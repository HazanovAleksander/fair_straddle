#!/usr/bin/env python3
import argparse
import getpass
import os
import select
import shutil
import sys
import termios
import time
import tty
from collections import deque
from dataclasses import dataclass
from datetime import datetime
from decimal import Decimal, InvalidOperation, ROUND_FLOOR
from threading import RLock

from pybit.unified_trading import HTTP, WebSocket

USE_COLOR = sys.stdout.isatty()
RESET = "\033[0m" if USE_COLOR else ""
COL = (
    {"b": "\033[1m", "d": "\033[2m", "r": "\033[31m", "g": "\033[32m",
     "y": "\033[33m", "c": "\033[36m", "o": "\033[38;5;208m", "rev": "\033[7m"}
    if USE_COLOR
    else {k: "" for k in ("b", "d", "r", "g", "y", "c", "o", "rev")}
)


def clr(code, text):
    return f"{COL[code]}{text}{RESET}"


BOLD_RED = "\033[1m\033[31m" if USE_COLOR else ""
TP_MULT = Decimal("1.2")
DOUBLE_SPACE_SEC = 0.3
CONSTRUCTIONS = ((0, "Стреддл"), (1, "Стренгл ±1"), (2, "Стренгл ±2"), (3, "Стренгл ±3"))
DESC_W = 30


@dataclass(frozen=True)
class Leg:
    symbol: str
    strike: int
    is_call: bool
    tick: Decimal
    min_price: Decimal
    qty_step: Decimal
    min_qty: Decimal
    max_qty: Decimal


class Series:
    def __init__(self, delivery_ms, legs):
        self.delivery_ms = delivery_ms
        self.expiry_ts = delivery_ms / 1000
        self.by_strike = {}
        for leg in legs:
            self.by_strike.setdefault(leg.strike, {})["C" if leg.is_call else "P"] = leg
        self.strikes = sorted(k for k, v in self.by_strike.items() if "C" in v and "P" in v)

    def label(self):
        return datetime.fromtimestamp(self.expiry_ts).strftime("%d%b%y %H:%M")


class State:
    def __init__(self):
        self.lock = RLock()
        self.tickers = {}
        self.index_price = None
        self.messages = deque(maxlen=8)
        self.orders = {}
        self.placed = False
        self.follow = False
        self.last_amend = {}
        self.assembled = False
        self.constr_idx = 0
        self.market_done = False

    def msg(self, kind, text):
        ts = datetime.now().strftime("%H:%M:%S")
        with self.lock:
            self.messages.append((ts, kind, text))


class Cfg:
    def __init__(self, base, qty, live, testnet, strikes):
        self.base = base
        self.qty = qty
        self.live = live
        self.testnet = testnet
        self.strikes = strikes
        self.qty_step = Decimal("0.01") if base == "BTC" else Decimal("0.1")


def dec(value):
    try:
        d = Decimal(str(value))
        return d if d > 0 else None
    except Exception:
        return None


def fmt_price(p, tick, group=True):
    if p is None:
        return "—"
    q = max(0, -tick.normalize().as_tuple().exponent)
    return f"{p:,.{q}f}" if group else f"{p:.{q}f}"


def fmt_qty(q, step):
    qn = max(0, -step.normalize().as_tuple().exponent)
    return f"{q:,.{qn}f}"


def fmt_dur(sec):
    sec = max(0, int(sec))
    d, rem = divmod(sec, 86400)
    h, rem = divmod(rem, 3600)
    m, s = divmod(rem, 60)
    return f"{d}д {h:02d}:{m:02d}:{s:02d}" if d else f"{h:02d}:{m:02d}:{s:02d}"


def fmt_iv(iv):
    return "—" if iv is None else f"{float(iv) * 100:.1f}%"


def fetch_instruments(http, base):
    out, cursor = [], None
    while True:
        r = http.get_instruments_info(category="option", baseCoin=base, limit=1000, cursor=cursor)
        if r.get("retCode") != 0:
            raise RuntimeError(f"instruments-info: {r.get('retMsg')}")
        res = r["result"]
        out += res.get("list", [])
        cursor = res.get("nextPageCursor")
        if not cursor:
            break
    return out


def build_all_series(instruments, now_ms):
    live = [i for i in instruments
            if i.get("status") == "Trading" and int(i.get("deliveryTime", 0)) > now_ms]
    if not live:
        raise RuntimeError("нет торгуемых серий в будущем")
    by_exp = {}
    for i in live:
        try:
            strike = int(i["symbol"].split("-")[2])
        except (ValueError, IndexError):
            continue
        pf = i.get("priceFilter", {})
        ls = i.get("lotSizeFilter", {})
        leg = Leg(
            symbol=i["symbol"],
            strike=strike,
            is_call=i.get("optionsType") == "Call",
            tick=Decimal(pf.get("tickSize", "5")),
            min_price=Decimal(pf.get("minPrice", "5")),
            qty_step=Decimal(ls.get("qtyStep", "0.01")),
            min_qty=Decimal(ls.get("minOrderQty", "0.01")),
            max_qty=Decimal(ls.get("maxOrderQty", "500")),
        )
        by_exp.setdefault(int(i["deliveryTime"]), []).append(leg)
    series_list = [Series(ms, legs) for ms, legs in sorted(by_exp.items())]
    series_list = [s for s in series_list if s.strikes]
    if not series_list:
        raise RuntimeError("нет серий с полными страйками")
    return series_list


FOUR_HOURS = 4 * 3600


def select_series(series_list, prompt=input):
    if len(series_list) == 1:
        return series_list[0]
    now = time.time()
    default = 2 if series_list[0].expiry_ts - now < FOUR_HOURS else 1
    labels = {1: "0day, ближайшая", 2: "1day, следующая"}
    print("Выберите серию:")
    for n, s in enumerate(series_list[:2], 1):
        print(f"  {n}) {s.label()}  ({labels[n]})   до экспирации {fmt_dur(s.expiry_ts - now)}")
    while True:
        raw = prompt(f"Ваш выбор [{default}]: ").strip()
        if raw == "":
            return series_list[default - 1]
        if raw in ("1", "2") and int(raw) <= len(series_list):
            return series_list[int(raw) - 1]
        print("  введите 1 или 2 (или Enter — по умолчанию)")


def on_ticker(state, msg):
    try:
        data = msg.get("data") or []
        if isinstance(data, dict):
            data = [data]
        with state.lock:
            for d in data:
                sym = d.get("symbol")
                if not sym:
                    continue
                state.tickers[sym] = {
                    "bid": dec(d.get("bidPrice")),
                    "bid_size": dec(d.get("bidSize")),
                    "ask": dec(d.get("askPrice")),
                    "ask_size": dec(d.get("askSize")),
                    "mark": dec(d.get("markPrice")),
                    "iv": dec(d.get("markPriceIv")),
                }
                idx = dec(d.get("indexPrice"))
                if idx:
                    state.index_price = idx
    except Exception as e:
        state.msg("err", f"ws tickers: {e!r}")


def on_order(state, msg):
    try:
        data = msg.get("data") or []
        if isinstance(data, dict):
            data = [data]
        for d in data:
            apply_order_update(state, d)
    except Exception as e:
        state.msg("err", f"ws order: {e!r}")


def apply_order_update(state, d):
    with state.lock:
        lid = d.get("orderLinkId")
        if lid not in state.orders:
            return
        o = state.orders[lid]
        o["symbol"] = d.get("symbol") or o.get("symbol")
        prev = o.get("status")
        o["status"] = d.get("orderStatus") or o.get("status")
        o["avg"] = d.get("avgPrice") or o.get("avg")
        o["filled"] = d.get("cumExecQty") or o.get("filled")
        o["reject"] = d.get("rejectReason") or ""
        st = o["status"]
        sym = o["symbol"]
        fill = f" {o['filled']} @ {o['avg']}" if o.get("filled") else ""
        if st != prev:
            if st == "Filled":
                state.msg("ok", f"{sym} исполнена{fill}")
            elif st == "PartiallyFilled":
                state.msg("info", f"{sym} частично исполнена{fill}")
            elif st in ("Cancelled", "PartiallyFilledCanceled"):
                state.msg("info", f"{sym} отменена (исполнено {o['filled'] or 0})")
            elif st == "Rejected":
                state.msg("err", f"{sym} отклонена: {o['reject']}")
        if st == "Filled" and not state.assembled and state.orders:
            tracked = [oo for oo in state.orders.values()
                       if oo.get("status") not in ("Cancelled", "PartiallyFilledCanceled", "Не найден")]
            if tracked and all(oo.get("status") == "Filled" for oo in tracked):
                state.assembled = True
                state.follow = False
                state.msg("ok", "конструкция собрана — следование выкл")


def atm_strike(series, index):
    return min(series.strikes, key=lambda s: abs(Decimal(s) - index))


def strangle_strikes(series, index, step):
    i = series.strikes.index(atm_strike(series, index))
    if i - step < 0 or i + step >= len(series.strikes):
        return None
    return series.strikes[i - step], series.strikes[i + step]


def construction_legs(series, index, step):
    atm = atm_strike(series, index)
    if step == 0:
        return series.by_strike[atm]["C"], series.by_strike[atm]["P"]
    sp = strangle_strikes(series, index, step)
    if sp is None:
        return None
    k_p, k_c = sp
    return series.by_strike[k_c]["C"], series.by_strike[k_p]["P"]


def limit_price(leg, t):
    ask = t.get("ask")
    if ask is None:
        return None, "нет аска"
    target = ask - leg.tick
    p = (target / leg.tick).to_integral_value(rounding=ROUND_FLOOR) * leg.tick
    if p < leg.min_price:
        p = leg.min_price
    if p >= ask:
        return None, f"нет цены без пересечения аска (аск {fmt_price(ask, leg.tick)})"
    return p, None


def do_place(cfg, state, series, http):
    with state.lock:
        index = state.index_price
        snap = dict(state.tickers)
        constr = state.constr_idx
        if state.placed:
            return
    if index is None:
        state.msg("err", "нет индексной цены — выставка отменена")
        return
    legs = construction_legs(series, index, CONSTRUCTIONS[constr][0])
    if legs is None:
        state.msg("err", f"{CONSTRUCTIONS[constr][1]}: плечи вне сетки страйков — выставка отменена")
        return
    plan = []
    for leg in legs:
        t = snap.get(leg.symbol)
        if not t:
            state.msg("err", f"нет данных по {leg.symbol} — выставка отменена")
            return
        p, err = limit_price(leg, t)
        if err:
            state.msg("err", f"{leg.symbol}: {err} — выставка отменена")
            return
        plan.append((leg, p, t))
    basket_mark = sum((t["mark"] for _, _, t in plan), Decimal(0))
    total = sum((p for _, p, _ in plan), Decimal(0))
    tick = plan[0][0].tick
    tag = "LIVE" if cfg.live else "DRY"
    base_lid = f"fs{int(time.time() * 1000)}"
    for suffix, (leg, p, _) in zip(("c", "p"), plan):
        state.msg("ok" if cfg.live else "info",
                  f"[{tag}] BUY {fmt_qty(cfg.qty, leg.qty_step)} {leg.symbol} лимит {fmt_price(p, tick)} (id {base_lid}{suffix})")
    state.msg("info", f"Σ лимит {fmt_price(total, tick)} против Σ марок {fmt_price(basket_mark, tick)}")
    with state.lock:
        for suffix, (leg, p, _) in zip(("c", "p"), plan):
            state.orders[f"{base_lid}{suffix}"] = {
                "symbol": leg.symbol, "tick": str(leg.tick),
                "price": fmt_price(p, tick), "price_d": str(p),
                "qty": fmt_qty(cfg.qty, leg.qty_step), "qty_d": str(cfg.qty),
                "type": "Limit",
                "status": "Отправлен…" if cfg.live else "DRY — не отправлен",
                "avg": "", "filled": "", "reject": "",
            }
        state.placed = True
    if not cfg.live:
        return
    for lid, (leg, p, _) in zip((f"{base_lid}c", f"{base_lid}p"), plan):
        try:
            http.place_order(
                category="option", symbol=leg.symbol, side="Buy", orderType="Limit",
                qty=str(cfg.qty), price=str(p), timeInForce="GTC", orderLinkId=lid)
        except Exception as e:
            state.msg("err", f"place {leg.symbol}: {e!r}")
            with state.lock:
                state.orders[lid]["status"] = "ОШИБКА"


TERMINAL_STATUSES = {"Filled", "Cancelled", "Rejected", "Deactivated",
                     "PartiallyFilledCanceled", "Не найден"}
GONE_MARKERS = ("order does not exist", "110001", "10001")
FOLLOW_COOLDOWN = 0.5
RECONCILE_PERIOD = 5.0


def order_gone(exc_text):
    lowered = exc_text.lower()
    return any(m.lower() in lowered for m in GONE_MARKERS)


def do_cancel_own(cfg, state, http):
    if not cfg.live:
        state.msg("err", "dry-run: отмена недоступна (нет ордеров на бирже)")
        return
    with state.lock:
        orders = {lid: dict(o) for lid, o in state.orders.items()}
    if not orders:
        state.msg("info", "нет ордеров приложения")
        return
    for lid, o in orders.items():
        if o.get("status") in TERMINAL_STATUSES:
            continue
        try:
            http.cancel_order(category="option", symbol=o["symbol"], orderLinkId=lid)
        except Exception as e:
            if order_gone(str(e)):
                state.msg("info", f"{lid}: уже не активен (исполнен или снят)")
                with state.lock:
                    state.orders[lid]["status"] = "Не найден"
            else:
                state.msg("err", f"cancel {lid}: {e!r}")
        else:
            state.msg("ok", f"{lid}: отменён ({o['symbol']})")
            with state.lock:
                state.orders[lid]["status"] = "Cancelled"


def place_market(cfg, state, http, items):
    tag = "LIVE" if cfg.live else "DRY"
    base_lid = f"fm{int(time.time() * 1000)}"
    placed = []
    for leg, qty in items:
        lid = f"{base_lid}{'c' if leg.is_call else 'p'}"
        placed.append((lid, leg, qty))
        state.msg("ok" if cfg.live else "info",
                  f"[{tag}] BUY {fmt_qty(qty, leg.qty_step)} {leg.symbol} по рынку (id {lid})")
    with state.lock:
        for lid, leg, qty in placed:
            state.orders[lid] = {
                "symbol": leg.symbol, "tick": str(leg.tick),
                "price": "", "price_d": "",
                "qty": fmt_qty(qty, leg.qty_step), "qty_d": str(qty),
                "type": "Market",
                "status": "Отправлен…" if cfg.live else "DRY — не отправлен",
                "avg": "", "filled": "", "reject": "",
            }
        state.placed = True
        state.market_done = True
        state.follow = False
    if not cfg.live:
        return
    for lid, leg, qty in placed:
        try:
            http.place_order(
                category="option", symbol=leg.symbol, side="Buy", orderType="Market",
                qty=str(qty), orderLinkId=lid)
        except Exception as e:
            state.msg("err", f"place market {leg.symbol}: {e!r}")
            with state.lock:
                state.orders[lid]["status"] = "ОШИБКА"


def do_market_entry(cfg, state, series, http):
    with state.lock:
        index = state.index_price
        constr = state.constr_idx
        if state.placed:
            return
    if index is None:
        state.msg("err", "нет индексной цены — выставка отменена")
        return
    legs = construction_legs(series, index, CONSTRUCTIONS[constr][0])
    if legs is None:
        state.msg("err", f"{CONSTRUCTIONS[constr][1]}: плечи вне сетки страйков — выставка отменена")
        return
    place_market(cfg, state, http, [(leg, cfg.qty) for leg in legs])


def do_market_replace(cfg, state, http, legs):
    with state.lock:
        market_done = state.market_done
        orders = {lid: dict(o) for lid, o in state.orders.items()}
    if market_done:
        state.msg("info", "рыночные ордера уже отправлены")
        return
    act = {lid: o for lid, o in orders.items() if o.get("status") not in TERMINAL_STATUSES}
    if not act:
        state.msg("info", "нет активных лимитных ордеров — конвертация невозможна")
        return
    items = []
    for lid, o in sorted(act.items()):
        leg = legs.get(o["symbol"])
        if leg is None:
            continue
        filled = dec(o.get("filled")) or Decimal(0)
        qty = (cfg.qty - filled) / leg.qty_step
        qty = qty.to_integral_value(rounding=ROUND_FLOOR) * leg.qty_step
        if qty > 0:
            items.append((leg, qty))
    if not cfg.live:
        with state.lock:
            for lid in act:
                state.orders[lid]["status"] = "Cancelled"
        state.msg("info", "[DRY] лимитные ордера заменены рыночными")
    else:
        failed = False
        for lid, o in sorted(act.items()):
            try:
                http.cancel_order(category="option", symbol=o["symbol"], orderLinkId=lid)
            except Exception as e:
                if order_gone(str(e)):
                    state.msg("info", f"{lid}: уже не активен (исполнен или снят)")
                    with state.lock:
                        state.orders[lid]["status"] = "Не найден"
                else:
                    state.msg("err", f"cancel {lid}: {e!r}")
                    failed = True
            else:
                with state.lock:
                    state.orders[lid]["status"] = "Cancelled"
        if failed:
            state.msg("err", "конвертация прервана: не все лимитные ордера отменены")
            return
    if not items:
        with state.lock:
            state.market_done = True
            state.follow = False
        state.msg("info", "лимитные ордера исполнены полностью — рынок не нужен")
        return
    place_market(cfg, state, http, items)


def active_orders(state):
    with state.lock:
        return {lid: dict(o) for lid, o in state.orders.items()
                if o.get("status") not in TERMINAL_STATUSES}


def active_limit_orders(state):
    with state.lock:
        return {lid: dict(o) for lid, o in state.orders.items()
                if o.get("status") not in TERMINAL_STATUSES
                and o.get("type", "Limit") == "Limit"}


def do_amend(cfg, state, http, lid, o, p):
    tick = Decimal(o["tick"])
    if not cfg.live:
        with state.lock:
            state.orders[lid]["price"] = fmt_price(p, tick)
            state.orders[lid]["price_d"] = str(p)
        state.msg("info", f"[DRY] {o['symbol']}: репрайс {o['price']} → {fmt_price(p, tick)}")
        return
    try:
        http.amend_order(category="option", symbol=o["symbol"], orderLinkId=lid, price=str(p))
    except Exception as e:
        if order_gone(str(e)):
            state.msg("info", f"{lid}: уже не активен (исполнен или снят)")
            with state.lock:
                state.orders[lid]["status"] = "Не найден"
        else:
            state.msg("err", f"amend {o['symbol']}: {e!r}")
        return
    with state.lock:
        state.orders[lid]["price"] = fmt_price(p, tick)
        state.orders[lid]["price_d"] = str(p)
    state.msg("info", f"{o['symbol']}: репрайс {o['price']} → {fmt_price(p, tick)}")


def do_follow_tick(cfg, state, http, legs):
    act = active_limit_orders(state)
    if not act:
        if state.follow:
            state.follow = False
            state.msg("info", "следование выкл: нет активных ордеров")
        return
    with state.lock:
        tickers = dict(state.tickers)
    now = time.monotonic()
    for lid, o in act.items():
        leg = legs.get(o["symbol"])
        t = tickers.get(o["symbol"])
        if leg is None or not t:
            continue
        p, err = limit_price(leg, t)
        if err:
            continue
        cur = dec(o.get("price_d"))
        if cur is not None and abs(p - cur) < leg.tick:
            continue
        if now - state.last_amend.get(lid, 0.0) < FOLLOW_COOLDOWN:
            continue
        state.last_amend[lid] = now
        do_amend(cfg, state, http, lid, o, p)


def do_update(cfg, state, http, legs):
    if not state.placed:
        state.msg("err", "конструкция не выставлена — сначала ПРОБЕЛ")
        return
    act = active_limit_orders(state)
    if not act:
        state.msg("info", "нет активных ордеров")
        return
    with state.lock:
        tickers = dict(state.tickers)
    for lid, o in act.items():
        leg = legs.get(o["symbol"])
        t = tickers.get(o["symbol"])
        if leg is None or not t:
            state.msg("err", f"{o['symbol']}: нет данных")
            continue
        p, err = limit_price(leg, t)
        if err:
            state.msg("err", f"{o['symbol']}: {err}")
            continue
        if dec(o.get("price_d")) == p:
            continue
        state.last_amend[lid] = time.monotonic()
        do_amend(cfg, state, http, lid, o, p)


def reconcile_orders(cfg, state, http):
    for lid, o in active_orders(state).items():
        try:
            r = http.get_open_orders(category="option", symbol=o["symbol"],
                                     orderLinkId=lid, openOnly=0)
        except Exception as e:
            state.msg("err", f"reconcile {lid}: {e!r}")
            continue
        if r.get("retCode") != 0:
            continue
        for d in r["result"].get("list", []):
            apply_order_update(state, d)


def seed_tickers(state, http, cfg, series):
    r = http.get_tickers(category="option", baseCoin=cfg.base)
    if r.get("retCode") != 0:
        raise RuntimeError(f"tickers: {r.get('retMsg')}")
    wanted = set()
    for s in series.by_strike.values():
        for leg in s.values():
            wanted.add(leg.symbol)
    with state.lock:
        for d in r["result"].get("list", []):
            sym = d.get("symbol")
            if sym not in wanted:
                continue
            state.tickers[sym] = {
                "bid": dec(d.get("bid1Price")),
                "bid_size": dec(d.get("bid1Size")),
                "ask": dec(d.get("ask1Price")),
                "ask_size": dec(d.get("ask1Size")),
                "mark": dec(d.get("markPrice")),
                "iv": dec(d.get("markIv")),
            }
            idx = dec(d.get("indexPrice"))
            if idx:
                state.index_price = idx


def pick_subscription_symbols(series, index, cap=380):
    strikes = sorted(series.strikes, key=lambda s: abs(Decimal(s) - index))
    syms = []
    for s in strikes:
        for kind in ("C", "P"):
            syms.append(series.by_strike[s][kind].symbol)
        if len(syms) >= cap:
            break
    return syms


class Term:
    def __init__(self):
        self.raw = sys.stdin.isatty()
        self.saved = None

    def __enter__(self):
        if self.raw:
            self.saved = termios.tcgetattr(sys.stdin.fileno())
            tty.setcbreak(sys.stdin.fileno())
        sys.stdout.write("\033[?25l")
        sys.stdout.flush()
        return self

    def __exit__(self, *exc):
        if self.saved is not None:
            termios.tcsetattr(sys.stdin.fileno(), termios.TCSADRAIN, self.saved)
        sys.stdout.write("\033[?25h\n")
        sys.stdout.flush()
        return False


def read_key(timeout):
    try:
        r, _, _ = select.select([sys.stdin], [], [], timeout)
        if not r:
            return None
        ch = os.read(sys.stdin.fileno(), 1)
        if not ch:
            time.sleep(timeout)
            return None
        if ch != b"\x1b":
            return ch.decode("utf-8", "ignore")
        r, _, _ = select.select([sys.stdin], [], [], 0.05)
        if not r:
            return "\x1b"
        ch2 = os.read(sys.stdin.fileno(), 1)
        if ch2 != b"[":
            return ch2.decode("utf-8", "ignore")
        r, _, _ = select.select([sys.stdin], [], [], 0.05)
        if not r:
            return "\x1b"
        ch3 = os.read(sys.stdin.fileno(), 1)
        return {"A": "up", "B": "down"}.get(ch3.decode("utf-8", "ignore"))
    except (OSError, ValueError):
        time.sleep(timeout)
        return None


def panel_cells(leg, t, show_sizes, show_iv, want_limit):
    tick = leg.tick
    w_px = 12 if show_sizes else 7

    def px_size(p, s):
        if p is None:
            return "—"
        txt = fmt_price(p, tick, group=False)
        if show_sizes and s is not None:
            txt += f"×{s:.1f}"
        return txt

    if t:
        bid = px_size(t["bid"], t["bid_size"])
        ask = px_size(t["ask"], t["ask_size"])
        mark = fmt_price(t["mark"], tick, group=False)
        iv = fmt_iv(t["iv"])
    else:
        bid = ask = mark = iv = "—"
    lim = None
    if want_limit and t:
        lim, _ = limit_price(leg, t)
    if not want_limit:
        lim_txt = ""
    elif lim is not None:
        lim_txt = fmt_price(lim, tick, group=False)
    else:
        lim_txt = "—"
    cells = [(f"{leg.strike}", 7), (bid, w_px), (ask, w_px), (mark, 7)]
    if show_iv:
        cells.append((iv, 6))
    cells.append((lim_txt, 7))
    return cells, lim is not None


def panel_row(leg, t, is_atm, show_sizes, show_iv):
    cells, ok = panel_cells(leg, t, show_sizes, show_iv, is_atm)
    if is_atm:
        parts = []
        for i, (txt, w) in enumerate(cells):
            padded = txt.rjust(w)
            if i == len(cells) - 1:
                parts.append(f"{BOLD_RED}{padded}{RESET}" if ok else clr("y", padded))
            else:
                parts.append(clr("rev", padded))
        return " ".join(parts)
    parts = [txt.rjust(w) for txt, w in cells]
    return " ".join(parts)


def panel_header(show_sizes, show_iv):
    w_px = 12 if show_sizes else 7
    cols = [("СТРАЙК", 7), ("БИД" + ("×Р" if show_sizes else ""), w_px),
            ("АСК" + ("×Р" if show_sizes else ""), w_px), ("МАРКА", 7)]
    if show_iv:
        cols.append(("IV", 6))
    cols.append(("ЛИМИТ", 7))
    return " ".join(t.rjust(w) for t, w in cols)


def construction_lines(cfg, series, tickers, index, step, selected):
    if step == 0:
        k = atm_strike(series, index)
        legs = (series.by_strike[k]["C"], series.by_strike[k]["P"])
        desc = f"Стреддл {k:,}"
        k_low = k_high = Decimal(k)
        note = "экспирация на страйке"
    else:
        sp = strangle_strikes(series, index, step)
        if sp is None:
            return []
        k_p, k_c = sp
        legs = (series.by_strike[k_c]["C"], series.by_strike[k_p]["P"])
        desc = f"Стренгл ±{step} P {k_p:,}/C {k_c:,}"
        k_low, k_high = Decimal(k_p), Decimal(k_c)
        note = "экспирация между страйками"
    sel = clr("c", "► ") if selected else "  "
    head = (clr("b", desc) if selected else desc) + " " * max(1, DESC_W - len(desc))
    ts = [tickers.get(leg.symbol) for leg in legs]
    if not all(t and t["ask"] is not None for t in ts):
        return ["", f"{sel}{head}" + clr("y", "стоимости и Short/Long: — (нет аска по плечам)")]
    market_cost = ts[0]["ask"] + ts[1]["ask"]
    tick = legs[0].tick
    lims = [limit_price(leg, t)[0] for leg, t in zip(legs, ts)]
    if all(p is not None for p in lims):
        lim_cost = lims[0] + lims[1]
        lim_txt = clr("b", fmt_price(lim_cost, tick))
    else:
        lim_cost = None
        lim_txt = "—"
    lines = ["", f"{sel}{head}рын. {clr('b', fmt_price(market_cost, tick))} / макс. лимит {lim_txt} USDT"]
    if lim_cost is None:
        lines.append(clr("y", "Short/Long и Макс. убыток: — (лимит без пересечения спреда невозможен)"))
        return lines
    target = lim_cost * TP_MULT
    lines.append(f"Short order (SELL {cfg.base}): {clr('o', f'{k_high + target:,.2f}')}   "
                 f"Long order (BUY {cfg.base}): {clr('o', f'{k_low - target:,.2f}')}   "
                 "фикс. +20% к лимитной стоимости")
    lines.append(f"Макс. убыток ({note}, 1 {cfg.base}): "
                 f"{BOLD_RED}{fmt_price(lim_cost, tick)}{RESET} USDT")
    return lines


def render(cfg, state, series):
    cols, lines = shutil.get_terminal_size((120, 40))
    show_sizes = cols >= 113
    show_iv = cols >= 93
    with state.lock:
        index = state.index_price
        tickers = dict(state.tickers)
        orders = {k: dict(v) for k, v in state.orders.items()}
        placed = state.placed
        follow = state.follow
        constr_idx = state.constr_idx
        messages = list(state.messages)
    L = []
    mode = (clr("r", clr("b", "LIVE")) if cfg.live else clr("y", clr("b", "DRY-RUN"))) + \
           (clr("d", "/TESTNET") if cfg.testnet else "")
    net = "testnet" if cfg.testnet else "mainnet"
    rem = fmt_dur(series.expiry_ts - time.time())
    contracts = int(cfg.qty / cfg.qty_step)
    L.append(f"{clr('b','FAIR STRADDLE')}  {mode}  {net}   "
             f"серия {clr('c', series.label())}  до экспирации {clr('b', rem)}")
    if index is None:
        L.append(f"База {cfg.base}   кол-во {clr('b', fmt_qty(cfg.qty, cfg.qty_step))} "
                 f"({contracts} контр.)   следование: "
                 f"{clr('g', 'ВКЛ') if follow else clr('d', 'выкл')}")
        L.append("")
        L.append(clr("y", "Ожидание данных…"))
    else:
        L.append(f"База {cfg.base}   кол-во {clr('b', fmt_qty(cfg.qty, cfg.qty_step))} "
                 f"({contracts} контр.)   Индекс: {clr('b', f'{index:,.2f}')}   "
                 f"ATM: {clr('b', f'{atm_strike(series, index):,}')}   следование: "
                 f"{clr('g', 'ВКЛ') if follow else clr('d', 'выкл')}")
        strike = atm_strike(series, index)
        i = series.strikes.index(strike)
        max_rows = max(3, min(2 * cfg.strikes + 1, lines - 22))
        half = min(cfg.strikes, (max_rows - 1) // 2)
        window = series.strikes[max(0, i - half):i + half + 1]
        sep = clr("d", "│")
        L.append("")
        L.append(clr("d", panel_header(show_sizes, show_iv)) + sep
                 + clr("d", panel_header(show_sizes, show_iv)))
        for s in window:
            cl = series.by_strike[s]["C"]
            pl = series.by_strike[s]["P"]
            L.append(panel_row(cl, tickers.get(cl.symbol), s == strike, show_sizes, show_iv)
                     + sep
                     + panel_row(pl, tickers.get(pl.symbol), s == strike, show_sizes, show_iv))
        for n, (step, _) in enumerate(CONSTRUCTIONS):
            L += construction_lines(cfg, series, tickers, index, step, n == constr_idx)
    if orders:
        L.append("")
        for lid, o in sorted(orders.items()):
            fill = f"  исп. {o.get('filled')} @ {o.get('avg')}" if o.get("filled") else ""
            rej = f"  {clr('r', o['reject'])}" if o.get("reject") else ""
            st = str(o.get("status", ""))
            if st in ("Cancelled", "Не найден"):
                stc = "d"
            elif st in ("Filled", "PartiallyFilled"):
                stc = "g"
            elif "ОШИБК" in st or st == "Rejected":
                stc = "r"
            else:
                stc = "y"
            L.append(f" {clr(stc, st)}  {o.get('symbol')}  BUY {o.get('qty')} @ {o.get('price') or 'рынок'}{fill}{rej}")
    if messages:
        L.append("")
        for ts, kind, text in messages[-2:]:
            color = {"err": "r", "ok": "g", "info": "d"}.get(kind, "d")
            L.append(f" {clr('d', ts)}  {clr(color, text)}")
    keys = "ESC — отменить ордера   q — выход"
    if placed:
        keys = "ПРОБЕЛ — лимит → рынок   f — следование ВКЛ/ВЫКЛ   u — обновить цены   " + keys
    else:
        keys = "↑/↓ — конструкция   ПРОБЕЛ — лимит (2× — рынок)   " + keys
    L.append("")
    L.append(clr("b", keys))
    out = "\r\n".join(line + "\033[K" for line in L)
    sys.stdout.write("\033[H" + out + "\033[J")
    sys.stdout.flush()


def parse_args():
    ap = argparse.ArgumentParser(
        description="Покупка ATM-стредла на ближайшей серии опционов ByBit (0DTE): "
                    "лимит по min(марка, аск−тик), не пересекая спред")
    ap.add_argument("base", choices=["BTC", "ETH"], help="базовый актив")
    ap.add_argument("qty", help="кол-во в монетах: BTC кратно 0.01, ETH кратно 0.1")
    ap.add_argument("--live", action="store_true", help="реальная отправка ордеров (по умолчанию dry-run)")
    ap.add_argument("--testnet", action="store_true", help="тестовая сеть")
    ap.add_argument("--strikes", type=int, default=3, help="полуокно страйков в таблице (по умолчанию 3)")
    return ap.parse_args()


def main():
    a = parse_args()
    try:
        qty = Decimal(a.qty)
    except InvalidOperation:
        sys.exit(f"Некорректное кол-во: {a.qty}")
    cfg = Cfg(a.base, qty, a.live, a.testnet, a.strikes)
    if cfg.qty <= 0 or cfg.qty % cfg.qty_step != 0:
        sys.exit(f"Кол-во должно быть кратно {cfg.qty_step} {cfg.base} (BTC: сотые, ETH: десятые)")
    cfg.qty = cfg.qty.quantize(cfg.qty_step)

    api_key = api_secret = None
    if a.live:
        print("Ключи API ByBit (Unified, права Trade):")
        api_key = input("  API key: ").strip()
        api_secret = getpass.getpass("  API secret: ").strip()
        if not (api_key and api_secret):
            sys.exit("Пустые ключи API — выход")

    state = State()
    print(f"Подключение к ByBit ({'testnet' if a.testnet else 'mainnet'})…", flush=True)
    http = HTTP(testnet=a.testnet, timeout=10,
                api_key=api_key or None, api_secret=api_secret or None)

    print("Загрузка инструментов…", flush=True)
    instruments = fetch_instruments(http, cfg.base)
    series_list = build_all_series(instruments, int(time.time() * 1000))
    series = select_series(series_list)
    print(f"Серия: {series.label()}  страйков: {len(series.strikes)}", flush=True)

    sample = series.by_strike[series.strikes[len(series.strikes) // 2]]["C"]
    if cfg.qty < sample.min_qty or cfg.qty > sample.max_qty or cfg.qty % sample.qty_step != 0:
        sys.exit(f"Кол-во вне лимитов серии: мин {sample.min_qty}, макс {sample.max_qty}, шаг {sample.qty_step}")

    print("Первичный снапшот рынка…", flush=True)
    seed_tickers(state, http, cfg, series)

    sub_syms = pick_subscription_symbols(series, state.index_price or Decimal(series.strikes[len(series.strikes) // 2]))
    print(f"Подписка WS tickers: {len(sub_syms)} символов…", flush=True)
    ws = WebSocket(testnet=a.testnet, channel_type="option")
    ws.ticker_stream(sub_syms, lambda m: on_ticker(state, m))

    if a.live:
        try:
            r = http.get_wallet_balance(accountType="UNIFIED", coin="USDT")
            if r.get("retCode") == 0:
                coins = r["result"]["list"][0].get("coin", [])
                if coins:
                    state.msg("info", f"Баланс USDT (UNIFIED): {coins[0].get('walletBalance', '?')}")
        except Exception as e:
            state.msg("err", f"баланс: {e!r}")
        priv = WebSocket(testnet=a.testnet, channel_type="private",
                         api_key=api_key, api_secret=api_secret)
        priv.order_stream(lambda m: on_order(state, m))

    legs = {leg.symbol: leg for s in series.by_strike.values() for leg in s.values()}
    with Term():
        last = 0.0
        last_reconcile = time.monotonic()
        pending_space = None
        while True:
            key = read_key(0.15)
            if key == " " and not state.placed:
                if pending_space is not None and \
                        time.monotonic() - pending_space < DOUBLE_SPACE_SEC:
                    pending_space = None
                    do_market_entry(cfg, state, series, http)
                else:
                    pending_space = time.monotonic()
            elif key == " ":
                do_market_replace(cfg, state, http, legs)
            elif key in ("up", "down"):
                if state.placed:
                    state.msg("info", "конструкция уже выбрана")
                else:
                    with state.lock:
                        state.constr_idx = (state.constr_idx +
                                            (1 if key == "down" else -1)) % len(CONSTRUCTIONS)
            elif key in ("f", "F"):
                if not state.placed:
                    state.msg("err", "конструкция не выставлена — сначала ПРОБЕЛ")
                elif active_orders(state):
                    state.follow = not state.follow
                    state.msg("info", "следование вкл" if state.follow else "следование выкл")
                else:
                    state.msg("err", "нет активных ордеров — следование недоступно")
            elif key in ("u", "U"):
                do_update(cfg, state, http, legs)
            elif key == "\x1b":
                pending_space = None
                if state.follow:
                    state.follow = False
                    state.msg("info", "следование выкл")
                do_cancel_own(cfg, state, http)
            elif key in ("q", "Q", "\x03"):
                break
            if pending_space is not None and not state.placed and \
                    time.monotonic() - pending_space >= DOUBLE_SPACE_SEC:
                pending_space = None
                do_place(cfg, state, series, http)
            if state.follow:
                do_follow_tick(cfg, state, http, legs)
            if cfg.live and time.monotonic() - last_reconcile >= RECONCILE_PERIOD:
                last_reconcile = time.monotonic()
                reconcile_orders(cfg, state, http)
            if time.time() - last >= 0.25:
                render(cfg, state, series)
                last = time.time()


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        pass

