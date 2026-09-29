# -*- coding: utf-8 -*-
"""
台股個股健診升級版 — Flask 後端
================================
安裝說明：
    pip install flask requests pandas

啟動方式：
    python app.py
    瀏覽器打開 http://127.0.0.1:5000

端點說明：
    /                — 前端頁面
    /api/data        — FinMind API 代理（保留原版）
    /api/stock       — 個股健診主端點（後端 pandas 計算 KD/MACD/布林/均線/評分）
    /api/news        — Google News RSS 抓取最新新聞
    /api/us_market   — 美股三大指數概況
    /api/sector_flow — 法人產業族群流向（含 1 小時 cache）
    /api/top_institutional — 法人（三大法人合計）個股買超/賣超排行 TOP10（含 1 小時 cache）
"""

from flask import Flask, render_template, request, jsonify
import requests
import time
import os
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo
from statistics import median
from html.parser import HTMLParser
import re
import importlib

class _LazyModule:
    """需要時才載入大型套件，降低 Gunicorn 啟動常駐記憶體。"""
    def __init__(self, module_name):
        self._module_name = module_name
        self._module = None
    def _load(self):
        if self._module is None:
            self._module = importlib.import_module(self._module_name)
        return self._module
    def __getattr__(self, name):
        return getattr(self._load(), name)

pd = _LazyModule("pandas")
import math
import json
import gc
import hashlib
import threading
from pathlib import Path

app = Flask(__name__)
# V2.9.3 資源治理：避免 JSON 回應輸出非必要空白，降低序列化與傳輸負擔。
app.config["JSON_AS_ASCII"] = False
app.config["MAX_CONTENT_LENGTH"] = int(os.environ.get("MAX_CONTENT_LENGTH", str(2 * 1024 * 1024)))
FINMIND_URL = "https://api.finmindtrade.com/api/v4/data"

# ===========================================================================
# V2.8.2 持股輸入體驗整合版標記
# ===========================================================================
SYSTEM_VERSION = "3.0.0"
MODEL_VERSION = "V3.0.0-core-baseline-frozen"
RELEASE_STAGE = "正式核心基準版"
CORE_RULESET_VERSION = "2026-09-29-FROZEN-1"


# 若在 Render 的 Environment Variables 裡設定 FINMIND_TOKEN，
# 就會帶上 Authorization header，使用個人配額而非匿名共用配額，
# 可大幅降低「查無資料」其實是配額用盡／IP 被暫時限制的機率。
FINMIND_TOKEN = os.environ.get("FINMIND_TOKEN", "").strip()

# ===========================================================================
# V2.4 資料快取＋API 配額保護
# ---------------------------------------------------------------------------
# 核心原則：同一組 FinMind 查詢只下載一次，後續回測優先讀本地快取。
# FinMind 一般配額以「時間窗」計算，因此這裡採 60 分鐘滾動計數，並保留
# 安全餘額，避免系統自己把官方配額打滿。可用環境變數調整。
# ===========================================================================
CACHE_DIR = Path(os.environ.get("STOCK_CACHE_DIR", ".cache_stock"))
CACHE_DIR.mkdir(parents=True, exist_ok=True)
FINMIND_CACHE_TTL = int(os.environ.get("FINMIND_CACHE_TTL", str(7 * 86400)))
QUOTA_WINDOW_SECONDS = 3600
# 官方常見上限約 300/600；預留 20 次安全空間，避免邊界誤差。
QUOTA_LIMIT_ANON = int(os.environ.get("FINMIND_SAFE_LIMIT_ANON", "280"))
QUOTA_LIMIT_TOKEN = int(os.environ.get("FINMIND_SAFE_LIMIT_TOKEN", "580"))
_QUOTA_FILE = CACHE_DIR / "finmind_quota.json"
_QUOTA_LOCK = threading.Lock()
_FINMIND_BLOCKED_UNTIL = 0.0

def _cache_key(params):
    payload = json.dumps(params, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()

def _cache_file(params):
    return CACHE_DIR / f"finmind_{_cache_key(params)}.json"

def _read_disk_cache(params, allow_stale=False):
    path = _cache_file(params)
    try:
        if not path.exists():
            return None
        expired = time.time() - path.stat().st_mtime > FINMIND_CACHE_TTL
        if expired and not allow_stale:
            return None
        with path.open("r", encoding="utf-8") as f:
            obj = json.load(f)
        if obj.get("ok"):
            return obj.get("data", [])
    except Exception:
        return None
    return None

def _write_disk_cache(params, data):
    path = _cache_file(params)
    tmp = path.with_suffix(".tmp")
    try:
        with tmp.open("w", encoding="utf-8") as f:
            json.dump({"ok": True, "saved_at": time.time(), "data": data}, f, ensure_ascii=False)
        tmp.replace(path)
    except Exception:
        try:
            tmp.unlink(missing_ok=True)
        except Exception:
            pass

def _load_quota_state():
    try:
        with _QUOTA_FILE.open("r", encoding="utf-8") as f:
            obj = json.load(f)
        now = time.time()
        calls = [float(x) for x in obj.get("calls", []) if now - float(x) < QUOTA_WINDOW_SECONDS]
        blocked_until = float(obj.get("blocked_until", 0) or 0)
        return calls, blocked_until
    except Exception:
        return [], 0.0

def _save_quota_state(calls, blocked_until=0.0):
    try:
        tmp = _QUOTA_FILE.with_suffix(".tmp")
        with tmp.open("w", encoding="utf-8") as f:
            json.dump({"calls": calls, "blocked_until": blocked_until}, f)
        tmp.replace(_QUOTA_FILE)
    except Exception:
        pass

def _load_quota_log():
    calls, _ = _load_quota_state()
    return calls

def _set_finmind_block(seconds=3600):
    global _FINMIND_BLOCKED_UNTIL
    until = time.time() + seconds
    _FINMIND_BLOCKED_UNTIL = max(_FINMIND_BLOCKED_UNTIL, until)
    with _QUOTA_LOCK:
        calls, file_until = _load_quota_state()
        _save_quota_state(calls, max(file_until, _FINMIND_BLOCKED_UNTIL))

def finmind_quota_status():
    calls, file_until = _load_quota_state()
    blocked_until = max(_FINMIND_BLOCKED_UNTIL, file_until)
    limit = QUOTA_LIMIT_TOKEN if FINMIND_TOKEN else QUOTA_LIMIT_ANON
    return {
        "window_seconds": QUOTA_WINDOW_SECONDS,
        "used": len(calls),
        "safe_limit": limit,
        "remaining_safe": max(0, limit - len(calls)),
        "has_token": bool(FINMIND_TOKEN),
        "provider_blocked": time.time() < blocked_until,
        "blocked_seconds": max(0, int(blocked_until - time.time())),
    }

def _quota_allows_request():
    now = time.time()
    with _QUOTA_LOCK:
        calls, file_until = _load_quota_state()
        blocked_until = max(_FINMIND_BLOCKED_UNTIL, file_until)
        if now < blocked_until:
            return False, len(calls), (QUOTA_LIMIT_TOKEN if FINMIND_TOKEN else QUOTA_LIMIT_ANON), "provider_blocked"
        limit = QUOTA_LIMIT_TOKEN if FINMIND_TOKEN else QUOTA_LIMIT_ANON
        if len(calls) >= limit:
            return False, len(calls), limit, "safe_limit"
        calls.append(now)
        _save_quota_state(calls, 0.0)
        return True, len(calls), limit, None


# ===========================================================================
# 交易成本設定（依使用者目前規格）
# ===========================================================================
# 證券交易稅：賣出市值 × 0.3%
# 券商手續費：買進／賣出市值 × 0.1425%（未計券商折讓）
# 台股 1 張 = 1,000 股；金額採無條件捨去到元。
TRADING_TAX_RATE = float(os.environ.get("STOCK_TRADING_TAX_RATE", "0.003"))
DAY_TRADE_TAX_RATE = float(os.environ.get("DAY_TRADE_TAX_RATE", "0.0015"))
BROKER_FEE_RATE = float(os.environ.get("BROKER_FEE_RATE", "0.001425"))
SHARES_PER_LOT = 1000


def calculate_trade_costs(price, lots, side, day_trade=False):
    """計算單筆台股交易成本。side: buy / sell；day_trade=True 時賣出稅率採現股當沖設定。"""
    if price is None or lots is None or float(lots) <= 0:
        return {"market_value": None, "fee": 0, "tax": 0, "total_cost": 0}
    market_value = math.floor(float(price) * float(lots) * SHARES_PER_LOT)
    fee = math.floor(market_value * BROKER_FEE_RATE)
    tax_rate = DAY_TRADE_TAX_RATE if day_trade else TRADING_TAX_RATE
    tax = math.floor(market_value * tax_rate) if side == "sell" else 0
    return {
        "market_value": market_value,
        "fee": fee,
        "tax": tax,
        "total_cost": fee + tax,
    }


def calculate_net_position_pnl(buy_price, current_price, lots):
    """
    以「實際買進總成本」與「現在全部賣出後可拿回金額」計算淨損益。
    損益率分母採原始買入總成本，與券商損益顯示邏輯一致。
    """
    if buy_price is None or current_price is None or lots is None or float(lots) <= 0:
        return None
    buy = calculate_trade_costs(buy_price, lots, "buy")
    sell = calculate_trade_costs(current_price, lots, "sell")
    original_cost = buy["market_value"] + buy["fee"]
    net_proceeds = sell["market_value"] - sell["fee"] - sell["tax"]
    pnl = net_proceeds - original_cost
    pnl_pct = pnl / original_cost * 100 if original_cost else None
    return {
        "lots": float(lots),
        "buy_market_value": buy["market_value"],
        "buy_fee": buy["fee"],
        "original_buy_cost": original_cost,
        "current_market_value": sell["market_value"],
        "sell_fee": sell["fee"],
        "sell_tax": sell["tax"],
        "sell_cost": sell["total_cost"],
        "net_proceeds": net_proceeds,
        "pnl_amount": round(pnl),
        "pnl_pct": round(pnl_pct, 3) if pnl_pct is not None else None,
        "gross_pnl_amount": round(sell["market_value"] - buy["market_value"]),
    }


def finmind_get(params, timeout=20):
    """
    V2.4.1 強化版 FinMind 請求入口：
    1) cache-first；2) 只有 cache miss 才計入配額；
    3) Provider 回傳 402 後立即全域熔斷 60 分鐘，禁止所有後續重試；
    4) 配額被保護時若存在舊快取，允許 stale cache 作為降級資料；
    5) 不再因同一個配額錯誤重複 fallback 請求。
    """
    cached = _read_disk_cache(params)
    if cached is not None:
        return cached, None

    allowed, used, limit, reason = _quota_allows_request()
    if not allowed:
        stale = _read_disk_cache(params, allow_stale=True)
        if stale is not None:
            return stale, "FinMind 暫停新增請求，已使用本地舊快取資料"
        if reason == "provider_blocked":
            return [], f"FinMind 配額已進入保護冷卻期，約剩 {_load_quota_state()[1] - time.time():.0f} 秒；禁止重試以避免再次耗盡配額"
        return [], (f"FinMind 配額保護已啟動：近 60 分鐘已使用 {used}/{limit} 次安全額度。"
                    "已停止新增 API 請求；已有本地快取仍可使用。")

    headers = {}
    if FINMIND_TOKEN:
        headers["Authorization"] = f"Bearer {FINMIND_TOKEN}"
    try:
        resp = requests.get(FINMIND_URL, params=params, headers=headers, timeout=timeout)
        j = resp.json()
    except Exception as e:
        return [], f"連線 FinMind 失敗: {e}"

    data = j.get("data", [])
    if data:
        _write_disk_cache(params, data)
    if not data and j.get("status") not in (200, None):
        status = j.get("status")
        msg = j.get("msg", "")
        if status == 402:
            _set_finmind_block(3600)
            stale = _read_disk_cache(params, allow_stale=True)
            if stale is not None:
                return stale, f"FinMind 配額已用盡，已切換舊快取並停止後續重試（{msg}）"
            return [], f"FinMind API 配額已用盡（{msg}）；系統已進入 60 分鐘熔斷，停止所有重試"
        if status == 403:
            _set_finmind_block(600)
            return [], f"FinMind API 暫時限制存取（{msg}）；系統已進入 10 分鐘保護"
        return [], f"FinMind API 錯誤（狀態碼 {status}）：{msg}"
    return data, None


def fetch_twse_t86(max_lookback_days=7):
    """
    從台灣證券交易所官方免費 OpenData 端點（T86 三大法人買賣超日報）
    取得「上市」全市場個股法人買賣超（無需 FinMind 帳號/配額，
    FinMind 該資料集全市場查詢屬付費 Sponsor 專屬功能，此為免費替代方案）。
    自動往回找最近一個有效交易日（跳過假日）。
    回傳 (rows, date_str) 或 ([], None)；rows 為 [{欄位: 值}, ...]。
    注意：僅涵蓋「上市」股票，不含「上櫃」。
    """
    for i in range(max_lookback_days):
        d = datetime.now() - timedelta(days=i)
        date_str = d.strftime("%Y%m%d")
        try:
            resp = requests.get(
                "https://www.twse.com.tw/rwd/zh/fund/T86",
                params={"date": date_str, "selectType": "ALL", "response": "json"},
                timeout=20,
            )
            j = resp.json()
        except Exception:
            continue
        if j.get("stat") == "OK" and j.get("data"):
            fields = j.get("fields", [])
            rows = [dict(zip(fields, row)) for row in j["data"]]
            return rows, d.strftime("%Y-%m-%d")
    return [], None


# ---------------------------------------------------------------------------
# 全域 cache（用於 /api/sector_flow，TTL 1 小時）
# ---------------------------------------------------------------------------
_sector_flow_cache = {"data": None, "ts": 0}
_SECTOR_FLOW_TTL = 3600  # 秒


# ===========================================================================
# /api/quota — API 配額保護狀態
# ===========================================================================
@app.route("/api/quota")
def get_quota_status():
    status = finmind_quota_status()
    try:
        cache_files = list(CACHE_DIR.glob("finmind_*.json"))
        status["cached_datasets"] = len(cache_files)
    except Exception:
        status["cached_datasets"] = None
    status["cache_ttl_hours"] = round(FINMIND_CACHE_TTL / 3600, 1)
    status["policy"] = "cache-first；cache miss 才消耗 API；達安全額度自動停止新增請求"
    return jsonify({"status": 200, **status})


# ===========================================================================
# 首頁
# ===========================================================================
@app.route("/")
def index():
    return render_template("index.html")


# ===========================================================================
# /api/data — FinMind 代理（保留原版架構）
# ===========================================================================
@app.route("/api/data")
def proxy_finmind():
    dataset = request.args.get("dataset")
    data_id = request.args.get("data_id")
    start_date = request.args.get("start_date")
    end_date = request.args.get("end_date")
    if not dataset:
        return jsonify({"status": 400, "msg": "缺少 dataset 參數", "data": []}), 400
    params = {"dataset": dataset}
    if data_id:
        params["data_id"] = data_id
    if start_date:
        params["start_date"] = start_date
    if end_date:
        params["end_date"] = end_date
    data, err = finmind_get(params, timeout=15)
    if err:
        return jsonify({"status": 429 if "配額" in err else 502, "msg": err, "data": []}), 429 if "配額" in err else 502
    return jsonify({"status": 200, "data": data})


# ===========================================================================
# calculate_indicators — pandas 後端計算技術指標
# KD(9,3,3) / MACD(12,26,9) / 布林通道 BB(20,2)
# BB 標準差使用 ddof=0（母體標準差），對齊看盤軟體慣例
# ===========================================================================
def calculate_indicators(df):
    """
    完全依照規格計算 KD(9,3,3)、MACD(12,26,9) 與布林通道 BB(20,2)
    布林通道標準差使用 ddof=0（母體標準差），與看盤軟體一致
    另計算策略訊號所需：KD(5,3,3) 短線指標、20日均量
    """
    if len(df) < 26:
        return df

    def calc_kd(low_col, high_col, close_col, window):
        low_n = low_col.rolling(window=window).min()
        high_n = high_col.rolling(window=window).max()
        rsv = ((close_col - low_n) / (high_n - low_n)) * 100
        rsv = rsv.fillna(50)
        k_vals, d_vals = [], []
        ck, cd = 50.0, 50.0
        for r in rsv:
            ck = ck * (2 / 3) + r * (1 / 3)
            cd = cd * (2 / 3) + ck * (1 / 3)
            k_vals.append(ck)
            d_vals.append(cd)
        return k_vals, d_vals

    # === 1. KD(9,3,3)：原有日線指標 ===
    df["K"], df["D"] = calc_kd(df["Low"], df["High"], df["Close"], 9)

    # === 1b. KD(5,3,3)：短線策略用 ===
    df["K5"], df["D5"] = calc_kd(df["Low"], df["High"], df["Close"], 5)

    # === 2. MACD(12,26,9) ===
    df["EMA12"] = df["Close"].ewm(span=12, adjust=False).mean()
    df["EMA26"] = df["Close"].ewm(span=26, adjust=False).mean()
    df["DIF"] = df["EMA12"] - df["EMA26"]
    df["DEA"] = df["DIF"].ewm(span=9, adjust=False).mean()
    df["MACD_Hist"] = (df["DIF"] - df["DEA"]) * 2

    # === 3. 布林通道 BB(20,2) — ddof=0 對齊看盤軟體 ===
    df["BB_Middle"] = df["Close"].rolling(window=20).mean()
    df["BB_Std"] = df["Close"].rolling(window=20).std(ddof=0)
    df["BB_Upper"] = df["BB_Middle"] + 2 * df["BB_Std"]
    df["BB_Lower"] = df["BB_Middle"] - 2 * df["BB_Std"]

    # === 4. 均線 ===
    df["MA5"] = df["Close"].rolling(window=5).mean()
    df["MA10"] = df["Close"].rolling(window=10).mean()
    df["MA20"] = df["Close"].rolling(window=20).mean()
    if len(df) >= 60:
        df["MA60"] = df["Close"].rolling(window=60).mean()
    else:
        df["MA60"] = None

    # === 5. 量能 ===
    df["Vol_MA5"] = df["Volume"].rolling(window=5).mean()
    df["Vol_MA20"] = df["Volume"].rolling(window=20).mean()

    # === 6. ATR14（真實波動幅度）— V2.1 動態停損／價格容忍度核心 ===
    prev_close_shift = df["Close"].shift(1)
    tr = pd.concat([
        df["High"] - df["Low"],
        (df["High"] - prev_close_shift).abs(),
        (df["Low"] - prev_close_shift).abs(),
    ], axis=1).max(axis=1)
    df["ATR14"] = tr.rolling(window=14).mean()

    return df


def calc_weekly_kd9(df):
    """
    將日線 resample 成週線（週五收），計算週 KD(9,3,3)。
    回傳最新兩週的 (K9, D9)，資料不足則回傳 None。
    """
    try:
        tmp = df[["Date", "Close", "High", "Low"]].copy()
        tmp["DateObj"] = pd.to_datetime(tmp["Date"])
        weekly = (
            tmp.set_index("DateObj")
            .resample("W-FRI")
            .agg({"Close": "last", "High": "max", "Low": "min"})
            .dropna()
        )
        if len(weekly) < 10:
            return None
        low_9 = weekly["Low"].rolling(window=9).min()
        high_9 = weekly["High"].rolling(window=9).max()
        rsv = ((weekly["Close"] - low_9) / (high_9 - low_9)) * 100
        rsv = rsv.fillna(50)
        k_vals, d_vals = [], []
        ck, cd = 50.0, 50.0
        for r in rsv:
            ck = ck * (2 / 3) + r * (1 / 3)
            cd = cd * (2 / 3) + ck * (1 / 3)
            k_vals.append(ck)
            d_vals.append(cd)
        weekly["K9"] = k_vals
        weekly["D9"] = d_vals
        weekly = weekly.dropna(subset=["K9", "D9"])
        if len(weekly) < 2:
            return None
        return {
            "K9": round(float(weekly["K9"].iloc[-1]), 2),
            "D9": round(float(weekly["D9"].iloc[-1]), 2),
            "K9_prev": round(float(weekly["K9"].iloc[-2]), 2),
        }
    except Exception:
        return None


# 簡易記憶體快取（用於降低 FinMind API 用量 — 同一支股票短時間內
# 重複查詢時不用重新打 API，直接吃快取，大幅減少每小時的請求數）
_revenue_cache = {}   # {stock_id: (ts, value)}
_revenue_raw_cache = {}  # {stock_id: (ts, rows)}
_per_stats_cache = {}  # {stock_id: (ts, value)}
_REVENUE_CACHE_TTL = 86400   # 24小時（月營收一個月才更新一次）
_PER_CACHE_TTL = 43200       # 12小時


def fetch_revenue_yoy(stock_id):
    """
    抓最近 14 個月營收，計算最新一筆的年增率 YoY(%)。
    抓不到資料時回傳 None。結果快取 24 小時。
    """
    now_ts = time.time()
    cached = _revenue_cache.get(stock_id)
    if cached and (now_ts - cached[0]) < _REVENUE_CACHE_TTL:
        return cached[1]
    try:
        end_date = datetime.now().strftime("%Y-%m-%d")
        start_date = (datetime.now() - timedelta(days=440)).strftime("%Y-%m-%d")
        data, _err = finmind_get({
            "dataset": "TaiwanStockMonthRevenue",
            "data_id": stock_id,
            "start_date": start_date,
            "end_date": end_date,
        }, timeout=15)
        if not data:
            result = None
        else:
            _revenue_raw_cache[stock_id] = (now_ts, data)
            data = sorted(data, key=lambda r: (r.get("revenue_year", 0), r.get("revenue_month", 0)))
            latest = data[-1]
            ly, lm = latest.get("revenue_year"), latest.get("revenue_month")
            same_month_last_year = None
            for r in data[:-1]:
                if r.get("revenue_year") == ly - 1 and r.get("revenue_month") == lm:
                    same_month_last_year = r
                    break
            if not same_month_last_year or not same_month_last_year.get("revenue"):
                result = None
            else:
                yoy = (latest["revenue"] - same_month_last_year["revenue"]) / same_month_last_year["revenue"] * 100
                result = round(float(yoy), 2)
    except Exception:
        result = None
    _revenue_cache[stock_id] = (now_ts, result)
    return result



# ===========================================================================
# 大盤環境引擎：以台灣加權指數 001 為基準，所有判斷只使用訊號日前已知資料
# ===========================================================================
_market_cache = {"data": None, "ts": 0}
_MARKET_CACHE_TTL = 86400

def fetch_market_environment(lookback_days=600):
    """取得加權指數歷史資料並建立每日市場環境。禁止使用未來資料。"""
    now_ts = time.time()
    if _market_cache["data"] is not None and now_ts - _market_cache["ts"] < _MARKET_CACHE_TTL:
        return _market_cache["data"], None

    end_date = datetime.now().strftime("%Y-%m-%d")
    start_date = (datetime.now() - timedelta(days=lookback_days)).strftime("%Y-%m-%d")
    raw, err = finmind_get({
        "dataset": "TaiwanStockPrice",
        "data_id": "TAIEX",
        "start_date": start_date,
        "end_date": end_date,
    }, timeout=30)
    if err or not raw:
        # 只有「查無資料」才允許 fallback；若是配額/權限錯誤，禁止再打一筆 API。
        quota_or_limit_error = err and any(x in str(err) for x in ["配額", "402", "限制存取", "熔斷", "冷卻"])
        if not quota_or_limit_error:
            raw, err = finmind_get({
                "dataset": "TaiwanStockPrice",
                "data_id": "001",
                "start_date": start_date,
                "end_date": end_date,
            }, timeout=30)
    if err or not raw:
        return {}, err or "查無加權指數資料"

    m = pd.DataFrame(raw)
    # 不同資料版本可能使用不同欄名
    def pick(*names):
        for n in names:
            if n in m.columns:
                return n
        return None
    close_col = pick("close", "Close", "收盤價")
    high_col = pick("max", "high", "High", "最高價")
    low_col = pick("min", "low", "Low", "最低價")
    open_col = pick("open", "Open", "開盤價")
    vol_col = pick("Trading_Volume", "volume", "Volume", "成交量")
    date_col = pick("date", "Date")
    if not close_col or not date_col:
        return {}, "加權指數資料欄位格式無法辨識"

    m["Close"] = pd.to_numeric(m[close_col], errors="coerce")
    m["High"] = pd.to_numeric(m[high_col], errors="coerce") if high_col else m["Close"]
    m["Low"] = pd.to_numeric(m[low_col], errors="coerce") if low_col else m["Close"]
    m["Open"] = pd.to_numeric(m[open_col], errors="coerce") if open_col else m["Close"]
    m["Volume"] = pd.to_numeric(m[vol_col], errors="coerce") if vol_col else 0
    m["Date"] = m[date_col].astype(str)
    m = m.dropna(subset=["Close"]).sort_values("Date").reset_index(drop=True)
    if len(m) < 65:
        return {}, "加權指數歷史資料不足"

    m["MA5"] = m["Close"].rolling(5).mean()
    m["MA20"] = m["Close"].rolling(20).mean()
    m["MA60"] = m["Close"].rolling(60).mean()
    m["Ret5"] = m["Close"].pct_change(5) * 100
    m["Ret20"] = m["Close"].pct_change(20) * 100
    m["VolMA20"] = m["Volume"].rolling(20).mean()
    m["VolRatio20"] = m["Volume"] / m["VolMA20"].replace(0, pd.NA)
    m["VolPrice"] = m["Ret5"] / m["VolRatio20"].replace(0, pd.NA)
    m["Volatility20"] = m["Close"].pct_change().rolling(20).std() * (252 ** 0.5) * 100

    env = {}
    for _, r in m.iterrows():
        date = str(r["Date"])[:10]
        vals = [r[x] for x in ["Close","MA5","MA20","MA60","Ret5","Ret20","VolRatio20","Volatility20"]]
        if any(pd.isna(x) for x in vals):
            continue
        score = 50.0
        score += 12 if r["Close"] > r["MA20"] else -12
        score += 12 if r["MA20"] > r["MA60"] else -12
        score += max(-10, min(10, float(r["Ret20"]) * 0.8))
        score += 6 if r["Ret5"] > 0 else -6
        # 大量上漲加分；大量下跌扣分
        if r["VolRatio20"] >= 1.3:
            score += 5 if r["Ret5"] > 0 else -5
        score = max(0, min(100, score))
        if score >= 85: regime = "強多頭"
        elif score >= 70: regime = "多頭"
        elif score >= 50: regime = "中性"
        elif score >= 30: regime = "空頭"
        else: regime = "強空頭"
        env[date] = {
            "score": round(score, 1),
            "regime": regime,
            "close": round(float(r["Close"]), 2),
            "ma20": round(float(r["MA20"]), 2),
            "ma60": round(float(r["MA60"]), 2),
            "ret5": round(float(r["Ret5"]), 2),
            "ret20": round(float(r["Ret20"]), 2),
            "vol_ratio20": round(float(r["VolRatio20"]), 2),
            "volatility20": round(float(r["Volatility20"]), 2),
        }
    _market_cache.update({"data": env, "ts": now_ts})
    return env, None

def backtest_short_strategy(stock_id, lookback_days=500, hold_days=5, backtest_lots=1, market_env=None):
    """
    短線策略歷史回測。
    除原始毛報酬外，同時計入買進手續費、賣出手續費與賣出證交稅，
    以固定 1 張（可調整）計算每筆訊號的「淨損益／淨報酬」。
    歷史資料只能驗證過去，不代表未來績效。
    """
    end_date = datetime.now().strftime("%Y-%m-%d")
    start_date = (datetime.now() - timedelta(days=lookback_days)).strftime("%Y-%m-%d")
    raw, err = finmind_get({
        "dataset": "TaiwanStockPrice",
        "data_id": stock_id,
        "start_date": start_date,
        "end_date": end_date,
    }, timeout=30)
    if err:
        return {"stock_id": stock_id, "error": err}
    if not raw:
        return {"stock_id": stock_id, "error": "查無股價資料"}

    df = pd.DataFrame(raw)
    try:
        df["Close"] = pd.to_numeric(df["close"], errors="coerce")
        df["High"] = pd.to_numeric(df["max"], errors="coerce")
        df["Low"] = pd.to_numeric(df["min"], errors="coerce")
        df["Open"] = pd.to_numeric(df["open"], errors="coerce")
        df["Volume"] = pd.to_numeric(df["Trading_Volume"], errors="coerce")
        df["Date"] = df["date"]
    except KeyError as e:
        return {"stock_id": stock_id, "error": f"欄位缺失: {e}"}
    df = df.dropna(subset=["Close"]).reset_index(drop=True)
    if len(df) < 40:
        return {"stock_id": stock_id, "error": "資料筆數不足"}

    df = calculate_indicators(df)
    df = df.where(pd.notnull(df), None)
    if market_env is None:
        market_env, _market_err = fetch_market_environment(lookback_days=lookback_days + 100)
    else:
        _market_err = None

    signals = []
    for i in range(1, len(df) - hold_days):
        prev = df.iloc[i - 1]
        cur = df.iloc[i]
        vals = (cur["K5"], cur["D5"], prev["K5"], prev["D5"], cur["MA5"], prev["MA5"],
                cur["Close"], cur["Volume"], cur["Vol_MA20"])
        if any(v is None for v in vals):
            continue
        kd5_cross_up = prev["K5"] <= prev["D5"] and cur["K5"] > cur["D5"] and cur["K5"] < 50
        ma5_up = cur["MA5"] >= prev["MA5"]
        price_above_ma5 = cur["Close"] > cur["MA5"]
        vol_ok = cur["Vol_MA20"] and cur["Volume"] > cur["Vol_MA20"]
        try:
            day_of_month = int(str(cur["Date"])[8:10])
        except Exception:
            day_of_month = 15
        not_hot = not (1 <= day_of_month <= 10)

        if kd5_cross_up and price_above_ma5 and ma5_up and vol_ok and not_hot:
            entry_price = float(cur["Close"])
            exit_price = float(df.iloc[i + hold_days]["Close"])
            gross_return_pct = (exit_price - entry_price) / entry_price * 100
            next_close = float(df.iloc[i + 1]["Close"]) if i + 1 < len(df) else None
            next_day_return_pct = ((next_close - entry_price) / entry_price * 100) if next_close is not None else None
            buy_cost = calculate_trade_costs(entry_price, backtest_lots, "buy")
            sell_cost = calculate_trade_costs(exit_price, backtest_lots, "sell")
            original_cost = buy_cost["market_value"] + buy_cost["fee"]
            net_proceeds = sell_cost["market_value"] - sell_cost["fee"] - sell_cost["tax"]
            net_pnl = net_proceeds - original_cost
            net_return_pct = net_pnl / original_cost * 100 if original_cost else 0
            me = market_env.get(str(cur["Date"])[:10], {}) if market_env else {}
            # 同期間大盤報酬，用來計算策略 alpha；只比較歷史已知的市場結果
            market_exit = None
            if market_env:
                exit_date = str(df.iloc[i + hold_days]["Date"])[:10]
                market_entry = me.get("close")
                market_exit = market_env.get(exit_date, {}).get("close")
            market_return_pct = ((market_exit - market_entry) / market_entry * 100) if market_entry and market_exit else None
            alpha_pct = (net_return_pct - market_return_pct) if market_return_pct is not None else None
            signals.append({
                "date": cur["Date"],
                "exit_date": df.iloc[i + hold_days]["Date"],
                "market_score": (market_env.get(str(cur["Date"])[:10], {}) or {}).get("score"),
                "market_regime": (market_env.get(str(cur["Date"])[:10], {}) or {}).get("regime", "未知"),
                "market_ret5_pct": (market_env.get(str(cur["Date"])[:10], {}) or {}).get("ret5"),
                "market_ret20_pct": (market_env.get(str(cur["Date"])[:10], {}) or {}).get("ret20"),
                "entry": entry_price,
                "exit": exit_price,
                "gross_return_pct": round(gross_return_pct, 3),
                "next_day_return_pct": round(next_day_return_pct, 3) if next_day_return_pct is not None else None,
                "next_day_direction_correct": bool(next_day_return_pct is not None and next_day_return_pct > 0),
                "net_return_pct": round(net_return_pct, 3),
                "net_pnl": round(net_pnl),
                "buy_fee": buy_cost["fee"],
                "sell_fee": sell_cost["fee"],
                "sell_tax": sell_cost["tax"],
                "total_cost": buy_cost["fee"] + sell_cost["fee"] + sell_cost["tax"],
                "market_return_pct": round(market_return_pct, 3) if market_return_pct is not None else None,
                "alpha_pct": round(alpha_pct, 3) if alpha_pct is not None else None,
            })

    if not signals:
        return {"stock_id": stock_id, "signal_count": 0, "win_rate": None,
                "avg_return": None, "net_avg_return": None, "signals": [], "_all_signals": []}

    wins_gross = sum(1 for s in signals if s["gross_return_pct"] > 0)
    wins_net = sum(1 for s in signals if s["net_return_pct"] > 0)
    net_values = [s["net_return_pct"] for s in signals]
    gross_values = [s["gross_return_pct"] for s in signals]
    next_day = [s["next_day_return_pct"] for s in signals if s.get("next_day_return_pct") is not None]
    direction_accuracy = (sum(1 for x in next_day if x > 0) / len(next_day) * 100) if next_day else None
    return {
        "stock_id": stock_id,
        "signal_count": len(signals),
        "win_rate": round(wins_net / len(signals) * 100, 1),
        "gross_win_rate": round(wins_gross / len(signals) * 100, 1),
        "direction_accuracy_1d": round(direction_accuracy, 1) if direction_accuracy is not None else None,
        "avg_next_day_return": round(sum(next_day) / len(next_day), 3) if next_day else None,
        "avg_return": round(sum(gross_values) / len(gross_values), 3),
        "net_avg_return": round(sum(net_values) / len(net_values), 3),
        "total_net_pnl": round(sum(s["net_pnl"] for s in signals)),
        "total_trading_cost": round(sum(s["total_cost"] for s in signals)),
        "total_buy_fee": round(sum(s["buy_fee"] for s in signals)),
        "total_sell_fee": round(sum(s["sell_fee"] for s in signals)),
        "total_sell_tax": round(sum(s["sell_tax"] for s in signals)),
        "signals": signals[-5:],
        "_all_signals": signals,
        "all_net_returns": net_values,
    }


def calculate_strategy_performance(results):
    """
    將各股票訊號合併成「整體策略績效」。
    每筆訊號以等權方式統計；另提供訊號序列的近似複利與最大回撤。
    注意：不同股票訊號可能重疊，因此複利曲線不是資金逐筆真實撮合結果。
    """
    valid = [r for r in results if r.get("signal_count", 0) > 0 and not r.get("error")]
    all_returns = [x for r in valid for x in r.get("all_net_returns", [])]
    all_gross = [x for r in valid for x in [s.get("gross_return_pct", 0) for s in r.get("signals", [])]]
    # signals 欄位只保留最近5筆，因此總體成本／損益以各股票累計欄位為準。
    total_signals = sum(r.get("signal_count", 0) for r in valid)
    total_net_pnl = sum(r.get("total_net_pnl", 0) for r in valid)
    total_cost = sum(r.get("total_trading_cost", 0) for r in valid)
    total_buy_fee = sum(r.get("total_buy_fee", 0) for r in valid)
    total_sell_fee = sum(r.get("total_sell_fee", 0) for r in valid)
    total_sell_tax = sum(r.get("total_sell_tax", 0) for r in valid)
    if not all_returns:
        return {"total_signals": 0, "net_win_rate": None, "avg_net_return": None}

    wins = sum(1 for x in all_returns if x > 0)
    avg_net = sum(all_returns) / len(all_returns)
    # 等權訊號的近似複利曲線；只作策略強弱比較，不作實際資金回測。
    equity = 1.0
    peak = 1.0
    max_dd = 0.0
    for ret in all_returns:
        equity *= (1 + ret / 100)
        peak = max(peak, equity)
        dd = (equity - peak) / peak * 100
        max_dd = min(max_dd, dd)
    gross_profit = sum(x for x in all_returns if x > 0)
    gross_loss = abs(sum(x for x in all_returns if x < 0))
    profit_factor = gross_profit / gross_loss if gross_loss else None

    # V2.7.6：方向準確度 + 風險調整報酬 + 時序穩定度（固定規則策略的Walk-forward式樣本外分段）
    all_signal_rows = sorted(
        [s for r in valid for s in r.get("_all_signals", [])],
        key=lambda x: str(x.get("date", ""))
    )
    next_day_values = [float(s["next_day_return_pct"]) for s in all_signal_rows if s.get("next_day_return_pct") is not None]
    direction_accuracy_1d = (sum(x > 0 for x in next_day_values) / len(next_day_values) * 100) if next_day_values else None
    avg_next_day_return = (sum(next_day_values) / len(next_day_values)) if next_day_values else None

    mean_ret = avg_net
    if len(all_returns) >= 2:
        variance = sum((x - mean_ret) ** 2 for x in all_returns) / (len(all_returns) - 1)
        std_ret = math.sqrt(variance)
        sharpe_signal = mean_ret / std_ret if std_ret > 0 else None
    else:
        sharpe_signal = None
    downside = [x for x in all_returns if x < 0]
    if downside:
        downside_dev = math.sqrt(sum(x*x for x in downside) / len(downside))
        sortino_signal = mean_ret / downside_dev if downside_dev > 0 else None
    else:
        sortino_signal = None

    wf_folds = []
    if len(all_signal_rows) >= 9:
        fold_size = max(3, len(all_signal_rows) // 3)
        starts = [0, fold_size, fold_size*2]
        for fi, st in enumerate(starts, start=1):
            en = len(all_signal_rows) if fi == 3 else min(len(all_signal_rows), st + fold_size)
            rows = all_signal_rows[st:en]
            if not rows: continue
            rets = [float(x.get("net_return_pct", 0)) for x in rows]
            nd = [float(x["next_day_return_pct"]) for x in rows if x.get("next_day_return_pct") is not None]
            wf_folds.append({
                "fold": fi,
                "start_date": rows[0].get("date"),
                "end_date": rows[-1].get("date"),
                "signals": len(rows),
                "net_win_rate": round(sum(x > 0 for x in rets) / len(rets) * 100, 1),
                "avg_net_return": round(sum(rets) / len(rets), 3),
                "direction_accuracy_1d": round(sum(x > 0 for x in nd) / len(nd) * 100, 1) if nd else None,
            })
    positive_folds = sum(1 for x in wf_folds if x.get("avg_net_return", 0) > 0)
    wf_stability = round(positive_folds / len(wf_folds) * 100, 1) if wf_folds else None

    # V2.7.7：近期失效偵測。只比較時間序列後段，不因單次波動立即判死刑。
    drift = {"status": "資料不足", "recent_signals": 0}
    if len(all_signal_rows) >= 20:
        recent = all_signal_rows[-min(20, max(8, len(all_signal_rows)//4)):]
        prior = all_signal_rows[:-len(recent)]
        rr = [float(x.get("net_return_pct", 0)) for x in recent]
        pr = [float(x.get("net_return_pct", 0)) for x in prior] if prior else []
        recent_win = sum(x > 0 for x in rr) / len(rr) * 100
        recent_avg = sum(rr) / len(rr)
        prior_win = (sum(x > 0 for x in pr) / len(pr) * 100) if pr else None
        prior_avg = (sum(pr) / len(pr)) if pr else None
        status = "正常"
        if recent_avg < 0 and prior_avg is not None and prior_avg > 0:
            status = "降級"
        elif prior_win is not None and recent_win < prior_win - 15:
            status = "警戒"
        drift = {
            "status": status,
            "recent_signals": len(rr),
            "recent_win_rate": round(recent_win, 1),
            "recent_avg_net_return": round(recent_avg, 3),
            "prior_win_rate": round(prior_win, 1) if prior_win is not None else None,
            "prior_avg_net_return": round(prior_avg, 3) if prior_avg is not None else None,
        }

    # 依「訊號當下」的大盤環境分組，驗證策略是否只在多頭有效。
    regime_stats = {}
    for regime in ["強多頭", "多頭", "中性", "空頭", "強空頭", "未知"]:
        rr = [s for r in valid for s in r.get("_all_signals", []) if s.get("market_regime", "未知") == regime]
        if not rr:
            continue
        rets = [float(s["net_return_pct"]) for s in rr]
        alphas = [float(s["alpha_pct"]) for s in rr if s.get("alpha_pct") is not None]
        regime_stats[regime] = {
            "signals": len(rr),
            "win_rate": round(sum(x > 0 for x in rets) / len(rets) * 100, 1),
            "avg_net_return": round(sum(rets) / len(rets), 3),
            "total_net_pnl": round(sum(float(s.get("net_pnl", 0)) for s in rr)),
            "avg_alpha": round(sum(alphas) / len(alphas), 3) if alphas else None,
        }

    return {
        "total_signals": total_signals,
        "stock_count": len(valid),
        "net_win_rate": round(wins / len(all_returns) * 100, 1),
        "avg_net_return": round(avg_net, 3),
        "approx_compound_return": round((equity - 1) * 100, 2),
        "max_drawdown": round(max_dd, 2),
        "profit_factor": round(profit_factor, 2) if profit_factor is not None else None,
        "direction_accuracy_1d": round(direction_accuracy_1d, 1) if direction_accuracy_1d is not None else None,
        "avg_next_day_return": round(avg_next_day_return, 3) if avg_next_day_return is not None else None,
        "sharpe_per_signal": round(sharpe_signal, 3) if sharpe_signal is not None else None,
        "sortino_per_signal": round(sortino_signal, 3) if sortino_signal is not None else None,
        "walk_forward_folds": wf_folds,
        "walk_forward_stability": wf_stability,
        "model_drift": drift,
        "regime_stats": regime_stats,
        "market_adjusted_win_rate": round(sum(1 for s in [x for r in valid for x in r.get("_all_signals", [])] if s.get("alpha_pct") is not None and s.get("alpha_pct") > 0) / max(1, sum(1 for r in valid for s in r.get("_all_signals", []) if s.get("alpha_pct") is not None)) * 100, 1),
        "total_net_pnl": round(total_net_pnl),
        "total_trading_cost": round(total_cost),
        "total_buy_fee": round(total_buy_fee),
        "total_sell_fee": round(total_sell_fee),
        "total_sell_tax": round(total_sell_tax),
        "fee_tax_rate": {"broker_fee": BROKER_FEE_RATE, "sell_tax": TRADING_TAX_RATE},
    }



def fetch_valuation(stock_id, current_price):
    """
    估值引擎（簡化版 P/E Band）：
    抓近 3 年 TaiwanStockPER（FinMind 免費資料集），取歷史本益比的
    最低／平均／最高，並用「目前股價 ÷ 最新本益比」反推近期 EPS
    （注意：免費資料無法取得分析師「預估EPS」，這裡以近期實際
    本益比反推的 EPS 作為替代，精準度不如真正的預估EPS，僅供參考）。

    回傳 dict 或 None（資料不足時）：
    {
        eps, pe_low, pe_avg, pe_high,
        reasonable_price, buy_ceiling, target_price,
        zone  # 低估 / 合理買入區 / 合理價 / 偏高估 / 高估
    }
    """
    try:
        now_ts = time.time()
        cached = _per_stats_cache.get(stock_id)
        if cached and (now_ts - cached[0]) < _PER_CACHE_TTL:
            cached_val = cached[1]
            if cached_val is None:
                return None
            if isinstance(cached_val, dict) and cached_val.get("_error"):
                return cached_val
            pe_low, pe_avg, pe_high, latest_per = cached_val
        else:
            end_date = datetime.now().strftime("%Y-%m-%d")
            start_date = (datetime.now() - timedelta(days=1500)).strftime("%Y-%m-%d")  # 約 4 年，加大範圍以取得足夠樣本
            data, _err = finmind_get({
                "dataset": "TaiwanStockPER",
                "data_id": stock_id,
                "start_date": start_date,
                "end_date": end_date,
            }, timeout=20)
            if not data:
                _per_stats_cache[stock_id] = (now_ts, None)
                return None

            data = sorted(data, key=lambda r: r.get("date", ""))
            total_records = len(data)
            pe_list = [r.get("PER") for r in data if r.get("PER") and r.get("PER") > 0]

            # 門檻放寬到 5 筆（原本 10 筆太嚴格，部分股票資料頻率較低就會被擋掉）
            if len(pe_list) < 5:
                if total_records > 0 and len(pe_list) == 0:
                    # 有資料但本益比全部是負值／0：代表這段期間持續虧損，
                    # 本益比估值法本來就不適用，這是合理限制而非資料不足
                    err = {"_error": True, "msg": "近期本益比多為負值（可能持續虧損），本益比估值法不適用於這檔股票"}
                else:
                    err = {"_error": True, "msg": f"本益比歷史樣本不足（僅 {len(pe_list)} 筆有效資料，需至少 5 筆）"}
                _per_stats_cache[stock_id] = (now_ts, err)
                return err

            latest_per = None
            for r in reversed(data):
                if r.get("PER") and r.get("PER") > 0:
                    latest_per = r["PER"]
                    break
            if not latest_per:
                err = {"_error": True, "msg": "查無最新本益比資料"}
                _per_stats_cache[stock_id] = (now_ts, err)
                return err

            pe_low = min(pe_list)
            pe_high = max(pe_list)
            pe_avg = sum(pe_list) / len(pe_list)
            _per_stats_cache[stock_id] = (now_ts, (pe_low, pe_avg, pe_high, latest_per))

        # 本益比歷史統計走快取，但 EPS／合理價格用「當下」股價現算，避免用到過期股價
        eps = current_price / latest_per

        reasonable_price = eps * pe_avg
        buy_ceiling = eps * pe_avg * 1.1
        target_price = eps * pe_high * 0.9

        if current_price < eps * pe_low * 1.05:
            zone = "低估／強力買入區"
        elif current_price <= buy_ceiling:
            zone = "合理買入區"
        elif current_price <= reasonable_price * 1.15:
            zone = "偏高估"
        else:
            zone = "高估區"

        return {
            "eps": round(eps, 2),
            "pe_low": round(pe_low, 1),
            "pe_avg": round(pe_avg, 1),
            "pe_high": round(pe_high, 1),
            "reasonable_price": round(reasonable_price, 1),
            "buy_ceiling": round(buy_ceiling, 1),
            "target_price": round(target_price, 1),
            "zone": zone,
        }
    except Exception:
        return None


def analyze_position(buy_price, share_count, strategy_pref, close, ma5, ma20, ma60,
                      recent_high5, volume, vol_ma5, short_sig, mid_sig, valuation,
                      atr14=None, support=None, resistance=None,
                      previous_low20=None, previous_high20=None,
                      volume_analysis=None, trend_score=50, no_trade_reasons=None,
                      kd_cross=None):
    """
    V2.1 持股價格即時分析。
    核心：輸入買入價後，建立「第一補倉／第二補倉／停損／第一停利／第二停利」
    價格階梯，再用量價、趨勢、KD、禁止交易條件決定是否允許執行。
    """
    if buy_price is None or buy_price <= 0:
        return None

    gross_profit_pct = round((close - buy_price) / buy_price * 100, 2) if close is not None else None
    lots_for_cost = (float(share_count) / SHARES_PER_LOT) if share_count is not None and float(share_count) > 0 else None
    net_costs = calculate_net_position_pnl(buy_price, close, lots_for_cost) if close is not None and lots_for_cost else None
    profit_pct = net_costs["pnl_pct"] if net_costs else gross_profit_pct
    profit_amount = net_costs["pnl_amount"] if net_costs else None

    plan = build_entry_price_plan(
        buy_price, atr14, support, resistance, previous_low20, previous_high20, strategy_pref
    )
    execution = evaluate_entry_price_plan(
        plan, close, volume_analysis or {}, trend_score, kd_cross, no_trade_reasons
    ) if plan else None

    status = "HOLD"
    status_label = "🟢 持有"
    reasons = []

    if no_trade_reasons:
        status = "STOP" if close is not None and plan and close <= plan["stop"] else "HOLD"
        status_label = "🔴 建議停損" if status == "STOP" else "⛔ 暫停補倉"
        reasons.extend(no_trade_reasons)

    if plan and close is not None and close <= plan["stop"]:
        status = "STOP"
        status_label = "🔴 建議停損"
        reasons.append("目前價格已跌破 V2.1 動態防守價")

    elif execution and execution["status"] in ("ADD1_READY", "ADD2_READY"):
        status = "ADD"
        status_label = "🔵 可評估補倉"
        reasons.append(execution["note"])

    else:
        # 接近第一／第二停利時，優先提示減碼，但不覆蓋停損。
        if plan and close is not None and close >= plan["target2"]:
            status = "REDUCE"
            status_label = "🟡 第二停利／減碼"
            reasons.append("價格已進入第二停利區，建議分批落袋並保留移動停利。")
        elif plan and close is not None and close >= plan["target1"]:
            status = "REDUCE"
            status_label = "🟡 第一停利／減碼"
            reasons.append("價格已進入第一停利區，建議部分減碼。")
        else:
            reasons.append(
                execution["note"] if execution else "持續觀察價格與量價條件。"
            )

    rr1 = plan.get("risk_reward_1") if plan else None
    rr2 = plan.get("risk_reward_2") if plan else None

    return {
        "profit_pct": profit_pct,
        "profit_amount": profit_amount,
        "gross_profit_pct": gross_profit_pct,
        "transaction_costs": net_costs,
        "share_count": int(round(float(share_count))) if share_count is not None else None,
        "status": status,
        "status_label": status_label,
        "add_action": (
            f"第一補倉：{plan['add1']['low']}～{plan['add1']['high']}；"
            f"第二補倉：{plan['add2']['low']}～{plan['add2']['high']}"
            if plan else "資料不足"
        ),
        "sell_action": (
            f"第一停利：{plan['target1']}；第二停利：{plan['target2']}"
            if plan else "資料不足"
        ),
        "stop_loss": plan["stop"] if plan else None,
        "take_profit": plan["target1"] if plan else None,
        "price_plan": plan,
        "execution": execution,
        "risk_reward": {
            "target1": rr1,
            "target2": rr2,
        },
        "recommendation": status_label + "：" + ("；".join(reasons) if reasons else "持續觀察"),
    }


def build_strategy_signals(latest, prev, weekly_kd, revenue_yoy, vol_ma20, day_of_month, df=None, entry_date=None):
    """
    依照短線（3~5天）與波段（2~3週）兩套策略計算買賣訊號與燈號。
    回傳 dict：{light, short:{action,reasons}, mid:{action,reasons}}

    entry_date（選填，格式 YYYY-MM-DD）：使用者進場日期。
    若提供，短線賣出/停損訊號會完全依規格判定：
        強制停損：收盤價 < 進場當天低點  或  收盤價 < 5MA
        短線利多結清：(日K_5>80 且已死叉)  或  持有天數 >= 5
    未提供則使用不需進場資訊的簡化版判斷。
    """
    def g(row, key):
        v = row[key] if row is not None else None
        return v

    close = g(latest, "Close")
    ma5 = g(latest, "MA5")
    ma20 = g(latest, "MA20")
    k5 = g(latest, "K5")
    d5 = g(latest, "D5")
    pk5 = g(prev, "K5")
    pd5 = g(prev, "D5")
    k9 = g(latest, "K")
    d9 = g(latest, "D")
    pk9 = g(prev, "K")
    pd9 = g(prev, "D")
    volume = g(latest, "Volume")
    revenue_hot_period = 1 <= day_of_month <= 10

    # --- 若提供進場日期，查出當天低點與持有天數 ---
    entry_low = None
    holding_days = None
    if entry_date and df is not None:
        match = df[df["Date"] == entry_date]
        if not match.empty:
            entry_low = float(match.iloc[0]["Low"])
            # 持有天數＝進場日到最新一筆資料之間的交易日數
            entry_idx = match.index[0]
            holding_days = int(len(df) - 1 - entry_idx)

    # ---------------- 短線（3~5天）：KD(5,3,3) ----------------
    short_reasons = []
    short_action = "觀望"
    if None not in (k5, d5, pk5, pd5, ma5, close, volume, vol_ma20):
        kd5_cross_up = pk5 <= pd5 and k5 > d5 and k5 < 50
        ma5_up = True  # 若無前一日 MA5 可比對則預設不擋
        if prev is not None and g(prev, "MA5") is not None:
            ma5_up = ma5 >= prev["MA5"]
        price_above_ma5 = close > ma5
        vol_ok = vol_ma20 and volume > vol_ma20
        not_hot = not revenue_hot_period
        if kd5_cross_up:
            short_reasons.append("5日KD低檔黃金交叉")
        if price_above_ma5 and ma5_up:
            short_reasons.append("站上5日均線且均線上揚")
        elif price_above_ma5:
            short_reasons.append("站上5日均線，但均線走平／下彎")
        if vol_ok:
            short_reasons.append("成交量放大（>20日均量）")
        if revenue_hot_period:
            short_reasons.append("目前為每月營收公佈期（1-10號），策略建議觀望")

        if kd5_cross_up and price_above_ma5 and ma5_up and vol_ok and not_hot:
            short_action = "買進訊號"
        elif entry_date and (entry_low is not None or holding_days is not None):
            # --- 完整規格：已提供進場資訊，精確判定停損/停利 ---
            forced_stop = (entry_low is not None and close < entry_low) or close < ma5
            take_profit = (k5 is not None and d5 is not None and k5 > 80 and k5 < d5) or \
                          (holding_days is not None and holding_days >= 5)
            if forced_stop:
                short_action = "強制停損"
                if entry_low is not None and close < entry_low:
                    short_reasons.append(f"跌破進場當天低點（{entry_low}）")
                if close < ma5:
                    short_reasons.append("跌破5日均線")
            elif take_profit:
                short_action = "短線利多結清"
                if k5 is not None and k5 > 80 and d5 is not None and k5 < d5:
                    short_reasons.append("5日KD高檔死叉（K>80且K<D）")
                if holding_days is not None and holding_days >= 5:
                    short_reasons.append(f"已持有 {holding_days} 天，達 3-5 天短線週期")
        elif (k5 is not None and d5 is not None and k5 < d5) or (close < ma5):
            short_action = "賣出／停損訊號"
            if k5 < d5:
                short_reasons.append("5日KD死亡交叉或偏空")
            if close < ma5:
                short_reasons.append("跌破5日均線")
    else:
        short_reasons.append("資料不足，無法判定短線訊號")

    # ---------------- 波段（2~3週）：週KD(9,3,3)＋日KD(9,3,3) ----------------
    mid_reasons = []
    mid_action = "觀望"
    week_up = None
    if weekly_kd:
        week_up = weekly_kd["K9"] > weekly_kd["D9"] and weekly_kd["K9"] > weekly_kd["K9_prev"]
        if weekly_kd["K9"] > weekly_kd["D9"]:
            mid_reasons.append("週KD偏多（K>D）")
        else:
            mid_reasons.append("週KD偏空（K<D）")
        mid_reasons.append("週K方向向上" if weekly_kd["K9"] > weekly_kd["K9_prev"] else "週K方向向下")
    else:
        mid_reasons.append("週線資料不足，無法判定大趨勢")

    if None not in (k9, d9, pk9, ma20, close):
        daily_gold_cross = pk9 is not None and pk9 <= (g(prev, "D") or 0) and k9 > d9 and k9 < 50
        above_ma20 = close > ma20
        if daily_gold_cross:
            mid_reasons.append("日KD低檔黃金交叉")
        mid_reasons.append("站上月線(20MA)" if above_ma20 else "跌破月線(20MA)")
        if revenue_yoy is not None:
            mid_reasons.append(f"最新營收年增率 {revenue_yoy:+.1f}%")
        # 完整規格為 (營收YoY>0) or (營收公佈後股價不跌反突破)；
        # 後者需精確比對公佈日期與股價反應，此處暫僅以 YoY>0 判定，
        # 未涵蓋「公佈後不跌反突破」這個 OR 分支
        rev_ok = (revenue_yoy is not None and revenue_yoy > 0)

        # 日KD 高檔死亡交叉：前一日 K>=D，今日 K<D，且今日 K 仍在高檔（>80）附近
        daily_dead_cross_high = (
            k9 is not None and d9 is not None and k9 < d9
            and pk9 is not None and pd9 is not None and pk9 >= pd9
            and (k9 > 80 or pk9 > 80)
        )

        if week_up and daily_gold_cross and above_ma20 and rev_ok:
            mid_action = "買進訊號"
        elif close < ma20:
            mid_action = "停損出場"
            mid_reasons.append("跌破波段生命線（月線20MA）")
        elif daily_dead_cross_high:
            mid_action = "獲利了結"
            mid_reasons.append("日KD高檔（>80）死亡交叉，動能減弱")
    else:
        mid_reasons.append("資料不足，無法判定波段訊號")

    # ---------------- 燈號 ----------------
    light = "gray"
    if week_up is True and k9 is not None and d9 is not None and k9 > d9 and ma20 is not None and close is not None and close > ma20:
        light = "green"
    elif k9 is not None and k9 > 80 and revenue_hot_period:
        light = "red"
    elif week_up is False:
        light = "gray"
    else:
        light = "neutral"

    return {
        "light": light,
        "short": {"action": short_action, "reasons": short_reasons},
        "mid": {"action": mid_action, "reasons": mid_reasons},
    }


# ===========================================================================
# V2.1 價格決策引擎（依規格收斂為 7 大模組，全部集中在本檔案，不拆 engine/）
# ===========================================================================

def _weighted_cluster(candidates):
    """
    候選價格聚集：candidates = [(name, value, weight), ...]（value 為 None 的自動剔除，
    剩餘權重自動正規化，符合規格「無效價格不能參與計算」）。
    回傳 (core_price, precision, tolerance_pct, component_list) 或 None（無有效候選時）。
    """
    valid = [(n, v, w) for n, v, w in candidates if v is not None]
    if not valid:
        return None
    total_w = sum(w for _, _, w in valid)
    if total_w <= 0:
        return None
    core = sum(v * w for _, v, w in valid) / total_w

    values = [v for _, v, _ in valid]
    mean_v = sum(values) / len(values)
    if len(values) > 1 and mean_v:
        variance = sum((v - mean_v) ** 2 for v in values) / len(values)
        disp_pct = (variance ** 0.5) / mean_v * 100
    else:
        disp_pct = 0.0

    if disp_pct < 1.0 and len(valid) >= 4:
        precision, tol = "A", 0.01
    elif disp_pct < 2.5 and len(valid) >= 2:
        precision, tol = "B", 0.015
    else:
        precision, tol = "C", 0.03

    components = [{"name": n, "value": round(v, 2)} for n, v, _ in valid]
    return round(core, 2), precision, tol, components


def calculate_support_cluster(close, ma20, bb_lower, previous_low5, previous_low20, atr14):
    """核心買點：支撐價格聚集（MA20 25% / BB下軌 15% / 前5日低 20% / 前20日低 15% / ATR支撐 15% + 量價成本10%省略，權重正規化補上）"""
    atr_support = (close - atr14 * 0.8) if (close is not None and atr14 is not None) else None
    candidates = [
        ("MA20", ma20, 0.25),
        ("布林下軌", bb_lower, 0.15),
        ("前5日低點", previous_low5, 0.20),
        ("前20日低點", previous_low20, 0.15),
        ("ATR支撐", atr_support, 0.15),
    ]
    result = _weighted_cluster(candidates)
    if not result:
        return None
    core, precision, tol, components = result
    return {
        "core": core,
        "zone_low": round(core * (1 - tol), 2),
        "zone_high": round(core * (1 + tol), 2),
        "precision": precision,
        "tolerance_pct": round(tol * 100, 2),
        "components": components,
    }


def calculate_resistance_cluster(close, ma20, bb_upper, previous_high5, previous_high20, atr14):
    """核心賣點／壓力：與支撐聚集同邏輯，換成壓力側候選價格"""
    atr_resistance = (close + atr14 * 0.8) if (close is not None and atr14 is not None) else None
    candidates = [
        ("MA20", ma20, 0.20),
        ("布林上軌", bb_upper, 0.20),
        ("前5日高點", previous_high5, 0.25),
        ("前20日高點", previous_high20, 0.20),
        ("ATR壓力", atr_resistance, 0.15),
    ]
    result = _weighted_cluster(candidates)
    if not result:
        return None
    core, precision, tol, components = result
    return {
        "core": core,
        "zone_low": round(core * (1 - tol), 2),
        "zone_high": round(core * (1 + tol), 2),
        "precision": precision,
        "tolerance_pct": round(tol * 100, 2),
        "components": components,
    }


def check_no_trade(ma20, ma20_prev, ma60, close, volume, vol_ma20, macd_hist, macd_hist_prev):
    """
    禁止交易高優先權判斷。任一成立即 NO_TRADE，即使分數再高也不能買。
    回傳 reasons list；空list代表沒有觸發禁止條件。
    """
    reasons = []
    if ma20 is not None and ma60 is not None and ma20_prev is not None:
        if ma20 < ma60 and ma20 < ma20_prev:
            reasons.append("趨勢空頭：MA20 < MA60 且 MA20 向下")
    if ma20 is not None and close is not None and vol_ma20 and volume is not None:
        if close < ma20 and volume > vol_ma20 * 1.3:
            reasons.append("放量跌破月線支撐")
    if macd_hist is not None and macd_hist_prev is not None:
        if macd_hist < macd_hist_prev and macd_hist < 0 and macd_hist_prev < 0:
            reasons.append("MACD 空頭擴張")
    return reasons


def calculate_buy_score(ma20, ma60, close, ma5, kd_cross, k, macd_improving,
                         pullback_support, vol_ok, inst_bullish=None, fund_ok=None):
    """純技術/量價買點分數，0~100。

    V2.9.6 起，籌碼與基本面不再塞進這個分數，避免在後續三核心融合時重複計分。
    inst_bullish / fund_ok 僅保留參數相容，不參與分數。
    """
    score = 0
    reasons = []
    if ma20 is not None and ma60 is not None and ma20 > ma60:
        score += 18; reasons.append("MA20>MA60（中期趨勢偏多）")
    if ma20 is not None and close is not None and close > ma20:
        score += 12; reasons.append("站上20日均線")
    if ma5 is not None and ma20 is not None and ma5 > ma20:
        score += 12; reasons.append("5MA>20MA（短線趨勢偏多）")
    if kd_cross == "黃金交叉":
        score += 8; reasons.append("KD黃金交叉")
    if k is not None and k < 80:
        score += 4
    if macd_improving:
        score += 12; reasons.append("MACD動能改善")
    if pullback_support:
        score += 16; reasons.append("價格回到有效支撐附近")
    if vol_ok:
        score += 18; reasons.append("量價條件通過")
    return int(_clamp(score, 0, 100)), reasons

def calculate_add_engine(close, ma20, ma20_prev, previous_high5, volume, vol_ma20,
                          ma5, macd_hist, macd_hist_prev, kd_dead_cross,
                          profit_pct, previous_high20, support_cluster):
    """
    補倉引擎：回踩補倉／突破補倉／趨勢加碼／禁止補倉，四選一（或都不符合）。
    """
    result = {"type": None, "core": None, "low": None, "high": None, "note": None, "reasons": []}

    # 禁止補倉：最高優先權
    if close is not None and ma20 is not None and vol_ma20 and volume is not None:
        if close < ma20 and volume > vol_ma20 * 1.3:
            result["type"] = "BLOCKED"
            result["reasons"].append("跌破月線且放量，禁止補倉")
            return result
    if ma20 is not None and ma20_prev is not None and macd_hist is not None and macd_hist_prev is not None:
        if ma20 < ma20_prev and macd_hist < macd_hist_prev and macd_hist < 0:
            result["type"] = "BLOCKED"
            result["reasons"].append("月線走弱且MACD空頭擴張，禁止補倉")
            return result

    # 回踩補倉：貼近月線、月線仍向上、沒有爆量殺跌、KD沒死叉
    if (close is not None and ma20 is not None and ma20 != 0 and ma20_prev is not None
            and not kd_dead_cross):
        dist_pct = abs(close - ma20) / ma20 * 100
        vol_not_crash = not (vol_ma20 and volume is not None and volume > vol_ma20 * 1.3 and close < ma20)
        if dist_pct <= 1.0 and ma20 >= ma20_prev and vol_not_crash:
            core = support_cluster["core"] if support_cluster else ma20
            result["type"] = "PULLBACK"
            result["core"] = core
            result["low"] = round(core * 0.99, 2)
            result["high"] = round(core * 1.01, 2)
            result["reasons"] = ["股價貼近月線（20MA）", "月線仍向上", "沒有爆量殺跌", "KD沒有死亡交叉"]
            return result

    # 突破補倉：站上前5日高點 + 爆量 + 短均在長均之上 + MACD非空頭擴張
    if (close is not None and previous_high5 is not None and vol_ma20 and volume is not None
            and ma5 is not None and ma20 is not None):
        macd_ok = not (macd_hist is not None and macd_hist_prev is not None
                        and macd_hist < macd_hist_prev and macd_hist < 0)
        if close > previous_high5 and volume > vol_ma20 * 1.3 and ma5 > ma20 and macd_ok:
            result["type"] = "BREAKOUT"
            result["core"] = round(previous_high5, 2)
            result["low"] = round(previous_high5 * 0.99, 2)
            result["high"] = round(previous_high5 * 1.01, 2)
            result["reasons"] = ["突破前5日高點", "成交量 > 20日均量的1.3倍", "5MA>20MA", "MACD非空頭擴張"]
            # 已經明顯偏離突破價，提醒不要追價
            if close > previous_high5 * 1.03:
                result["note"] = "⚠️ 目前股價已偏離突破補倉區，不建議追價"
            return result

    # 趨勢加碼：持倉獲利 + 突破20日高點 + 量能確認 + 5MA>20MA
    if (profit_pct is not None and profit_pct > 3 and close is not None
            and previous_high20 is not None and vol_ma20 and volume is not None
            and ma5 is not None and ma20 is not None):
        if close > previous_high20 and volume > vol_ma20 * 1.2 and ma5 > ma20:
            result["type"] = "TREND"
            result["core"] = round(close, 2)
            result["low"] = round(close * 0.99, 2)
            result["high"] = round(close * 1.01, 2)
            result["reasons"] = ["持倉獲利中", "突破20日高點", "量能確認", "5MA>20MA（趨勢仍向上）"]
            return result

    return result


def calculate_risk_engine(base_price, atr14, ma20, previous_low_ref, strategy_pref, close):
    """
    動態停損：候選價格取「策略對應的合理防守價」，短線較緊、波段較寬。
    base_price：成本價（有輸入買入價時）或現價（純即時判斷時）。
    """
    if atr14 is None or base_price is None:
        return None
    atr_mult = 1.2 if strategy_pref == "short" else 1.8
    s1 = base_price - atr14 * atr_mult
    candidates = [s1]
    # 結構防守只能採用「仍位於現價下方」的有效支撐；跌破後位於現價上方的均線/前低已是壓力，不能再當停損支撐。
    ceiling = float(close) if close is not None else float(base_price)
    if ma20 is not None:
        mstop = ma20 - atr14 * 0.3
        if mstop < ceiling: candidates.append(mstop)
    if previous_low_ref is not None:
        lstop = previous_low_ref - atr14 * 0.2
        if lstop < ceiling: candidates.append(lstop)
    stop_price = round(max(candidates), 2)  # 取現價下方較緊的有效防守價
    warning_price = round(stop_price * 1.01, 2)
    warning_triggered = close is not None and close <= warning_price
    return {
        "stop": stop_price,
        "warning": warning_price,
        "warning_triggered": bool(warning_triggered),
        "hit": (close is not None and close <= stop_price),
    }


def calculate_profit_engine(base_price, previous_high20, atr14, valuation, bb_upper, ma5, close_max_since_entry, strategy_pref="short"):
    """
    三級停利：第一停利／第二停利／移動停利。
    V2.9.5 起避免把遠端20日高點或估值價直接當成短線目標：
    先用 ATR 建立「可實現距離」，再與技術壓力／估值取較近的有效目標。
    """
    base = float(base_price) if base_price is not None else None
    atr = float(atr14) if atr14 is not None and atr14 > 0 else (base * 0.03 if base else None)
    if base is None or base <= 0:
        return {"target1": None, "target2": None, "trailing": None, "basis": "資料不足"}

    if strategy_pref == "mid":
        t1_mult, t2_mult = 1.8, 3.5
        horizon = "波段"
    else:
        t1_mult, t2_mult = 1.2, 2.2
        horizon = "短線"

    # 第一目標：最近可達壓力優先；ATR 距離作為上限保護，避免短線目標過遠。
    candidates_t1 = []
    if previous_high20 is not None and float(previous_high20) > base:
        candidates_t1.append(float(previous_high20))
    if bb_upper is not None and float(bb_upper) > base:
        candidates_t1.append(float(bb_upper))
    if atr is not None:
        candidates_t1.append(base + atr * t1_mult)
    target1 = round_to_tick(min(candidates_t1)) if candidates_t1 else None

    # 第二目標：仍須大於第一目標；估值價只作上方參考，不再用 max() 強迫拉到最遠。
    candidates_t2 = []
    if atr is not None:
        candidates_t2.append(base + atr * t2_mult)
    if previous_high20 is not None and atr is not None:
        candidates_t2.append(float(previous_high20) + atr * 0.5)
    if valuation and not valuation.get("_error") and valuation.get("target_price"):
        try:
            vt = float(valuation["target_price"])
            if vt > base:
                candidates_t2.append(vt)
        except Exception:
            pass
    if target1 is not None:
        valid_t2 = [x for x in candidates_t2 if x > target1]
        target2 = round_to_tick(min(valid_t2)) if valid_t2 else (round_to_tick(target1 + (atr or base*0.02)))
    else:
        target2 = round_to_tick(min(candidates_t2)) if candidates_t2 else None

    trailing = None
    if close_max_since_entry is not None:
        trail_pct = round(close_max_since_entry * 0.97, 2)
        trailing = max(trail_pct, ma5) if ma5 is not None else trail_pct
        trailing = round_to_tick(trailing)

    return {
        "target1": target1, "target2": target2, "trailing": trailing,
        "basis": f"{horizon}：技術壓力＋ATR可實現距離＋估值參考"
    }



def calculate_volume_metrics(current_volume, avg_volume_20, price_change_pct):
    """V2.1 統一量比與量價效率。主量比固定以20日均量為基準。"""
    if current_volume is None or avg_volume_20 is None or avg_volume_20 <= 0:
        return {
            "volume_ratio_20": None,
            "price_change_pct": price_change_pct,
            "efficiency": None,
            "status": "資料不足",
            "score": 50,
        }

    ratio = current_volume / avg_volume_20
    pct = float(price_change_pct or 0.0)

    # 效率：每 1 倍量比所換來的價格變化；只作相對評分，不視為預測報酬。
    efficiency = pct / ratio if ratio > 0 else 0.0

    if ratio >= 1.5 and pct >= 2.0:
        status, score = "放量上攻", 90
    elif ratio >= 1.2 and pct > 0.5:
        status, score = "量價偏多", 80
    elif ratio >= 1.5 and pct <= -1.0:
        status, score = "放量下跌", 25
    elif ratio >= 1.5 and abs(pct) < 0.5:
        status, score = "大量不漲", 40
    elif ratio < 0.7:
        status, score = "量能偏弱", 50
    else:
        status, score = "量價正常", 65

    return {
        "volume_ratio_20": round(ratio, 2),
        "price_change_pct": round(pct, 2),
        "efficiency": round(efficiency, 3),
        "status": status,
        "score": score,
    }


def calculate_risk_reward(entry_price, stop_price, target_price):
    """V2.1 風險報酬比。回傳 None 表示資料不足或報酬不為正。"""
    if entry_price is None or stop_price is None or target_price is None:
        return None
    risk = entry_price - stop_price
    reward = target_price - entry_price
    if risk <= 0 or reward <= 0:
        return None
    return {
        "risk": round(risk, 2),
        "reward": round(reward, 2),
        "ratio": round(reward / risk, 2),
        "label": f"1 : {round(reward / risk, 2)}",
    }


def build_entry_price_plan(entry_price, atr14, support, resistance, previous_low20,
                           previous_high20, strategy_pref="short"):
    """
    V2.1：使用者輸入買入價後建立價格階梯。
    補倉不是「跌到就買」，而是先產生候選價格，再由條件引擎決定是否允許執行。
    """
    if entry_price is None or entry_price <= 0:
        return None

    support_core = support.get("core") if support else None
    resistance_core = resistance.get("core") if resistance else None

    # 優先以 ATR + 支撐建立兩級補倉；避免固定百分比硬套所有股票。
    atr = float(atr14) if atr14 is not None and atr14 > 0 else entry_price * 0.03
    first_ref = support_core if support_core is not None else entry_price - atr * 0.8
    second_ref = previous_low20 if previous_low20 is not None else entry_price - atr * 1.6

    # 若支撐高於成本太多，第一補倉仍以成本下方的合理回撤為主。
    first_core = min(first_ref, entry_price - atr * 0.35)
    second_core = min(second_ref, first_core - atr * 0.5)

    zone_width = max(atr * 0.18, entry_price * 0.005)
    first_low = round(max(0.01, first_core - zone_width), 2)
    first_high = round(max(first_low, first_core + zone_width), 2)

    second_low = round(max(0.01, second_core - zone_width), 2)
    second_high = round(max(second_low, second_core + zone_width), 2)

    # 防守：支撐下方 + ATR；若結果高於第一補倉區，仍保留風險底線。
    support_stop = (support_core - atr * 0.35) if support_core is not None else None
    atr_stop = entry_price - atr * (1.2 if strategy_pref == "short" else 1.8)
    candidates = [x for x in (support_stop, atr_stop) if x is not None and x > 0]
    stop = round(max(candidates), 2) if candidates else round(entry_price * 0.95, 2)

    # 停利以壓力與20日高點為主，不用估值價直接覆蓋技術壓力。
    target1_candidates = [x for x in (resistance_core, previous_high20) if x is not None and x > entry_price]
    target1 = round(min(target1_candidates), 2) if target1_candidates else round(entry_price + atr * 1.5, 2)
    target2_candidates = [x for x in (previous_high20 + atr if previous_high20 else None,
                                      resistance_core + atr if resistance_core else None)]
    target2_candidates = [x for x in target2_candidates if x is not None and x > target1]
    target2 = round(max(target2_candidates), 2) if target2_candidates else round(max(target1 + atr, entry_price + atr * 2.5), 2)

    return {
        "entry": round(entry_price, 2),
        "add1": {"core": round(first_core, 2), "low": first_low, "high": first_high},
        "add2": {"core": round(second_core, 2), "low": second_low, "high": second_high},
        "stop": stop,
        "target1": target1,
        "target2": target2,
        "risk_reward_1": calculate_risk_reward(entry_price, stop, target1),
        "risk_reward_2": calculate_risk_reward(entry_price, stop, target2),
    }


def evaluate_entry_price_plan(plan, current_price, volume_analysis, trend_score,
                              kd_cross=None, no_trade_reasons=None):
    """V2.1：價格階梯的執行條件判斷。"""
    if not plan:
        return None

    blocked = list(no_trade_reasons or [])
    vp_score = volume_analysis.get("score", 50) if volume_analysis else 50

    # 第一層：任何高優先級風險成立，禁止補倉。
    if blocked or vp_score < 45 or trend_score < 45:
        status = "BLOCKED"
        note = "目前風險條件不足，禁止補倉，等待趨勢／量價修復。"
    else:
        status = "WAIT"
        note = "價格區間已建立；實際補倉仍需回到區間並確認止跌／量價條件。"

        if current_price is not None:
            a1 = plan["add1"]
            a2 = plan["add2"]
            if a1["low"] <= current_price <= a1["high"]:
                if vp_score >= 65 and trend_score >= 60 and kd_cross != "死亡交叉":
                    status = "ADD1_READY"
                    note = "進入第一補倉區，且量價／趨勢條件可評估執行。"
            elif a2["low"] <= current_price <= a2["high"]:
                if vp_score >= 65 and trend_score >= 55 and kd_cross != "死亡交叉":
                    status = "ADD2_READY"
                    note = "進入第二補倉區；僅在支撐有效且未出現放量破位時評估。"

    return {"status": status, "note": note}


def calculate_confidence(buy_score, vol_ok, trend_bullish, inst_bullish, no_trade_triggered):
    """訊號一致度，不是命中率。

    V2.9.6 起避免把同一技術訊號重複加權。技術買點分數、量價、趨勢只做一致性檢查；
    籌碼另由三核心模型融合，不在這裡再次加分。
    """
    tech = _clamp(float(buy_score or 0), 0, 100)
    checks = [
        1.0 if vol_ok else 0.0,
        1.0 if trend_bullish else 0.0,
        0.0 if no_trade_triggered else 1.0,
    ]
    agreement = sum(checks) / len(checks) * 100
    score = round(_clamp(0.65 * tech + 0.35 * agreement, 0, 100), 1)
    level = "強" if score >= 80 else "中高" if score >= 65 else "中" if score >= 50 else "低"
    return {"score": score, "level": level, "meaning": "技術/量價/風險訊號一致度，非預測準確率"}

def final_decision(no_trade_reasons, add_result, buy_score, position_status, stop_hit, stop_warning):
    """
    最終單一決策，依優先權：STOP > NO_TRADE > REDUCE > ADD > BUY > HOLD > WAIT
    position_status 是既有的 analyze_position 狀態（有輸入買入價時才有：STOP/REDUCE/ADD/HOLD）。
    """
    if stop_hit or position_status == "STOP":
        return "STOP", "🔴 建議停損"
    if no_trade_reasons:
        return "NO_TRADE", "⛔ 不建議交易"
    if position_status == "REDUCE":
        return "REDUCE", "🟡 建議減碼／停利"
    if add_result and add_result.get("type") in ("PULLBACK", "BREAKOUT", "TREND"):
        return "ADD", "🔵 可考慮補倉"
    if position_status == "ADD":
        return "ADD", "🔵 可考慮補倉"
    if position_status == "HOLD":
        return "HOLD", "🟢 持有"
    if buy_score >= 70:
        return "BUY", "🟢 建議買入" if buy_score >= 80 else "🟢 買入"
    if buy_score >= 60:
        return "WAIT", "🟡 等待"
    if buy_score >= 50:
        return "WAIT", "🟠 觀察"
    return "WAIT", "🔴 不建議買進"


def build_price_decision(latest, prev, df, strategy_pref="short"):
    """
    整合以上模組，產生完整的 V2.1 價格決策物件（不含使用者買入價相關的 position 部分，
    那個仍由 analyze_position 處理，這裡只算「即時、與個人成本無關」的市場決策）。
    """
    close = float(latest["Close"]) if latest["Close"] is not None else None
    ma5 = float(latest["MA5"]) if latest["MA5"] is not None else None
    ma20 = float(latest["MA20"]) if latest["MA20"] is not None else None
    ma60 = float(latest["MA60"]) if latest["MA60"] is not None else None
    ma20_prev = float(prev["MA20"]) if (prev is not None and prev["MA20"] is not None) else None
    bb_lower = float(latest["BB_Lower"]) if latest["BB_Lower"] is not None else None
    bb_upper = float(latest["BB_Upper"]) if latest["BB_Upper"] is not None else None
    atr14 = float(latest["ATR14"]) if latest["ATR14"] is not None else None
    volume = float(latest["Volume"]) if latest["Volume"] is not None else None
    vol_ma20 = float(latest["Vol_MA20"]) if latest["Vol_MA20"] is not None else None
    macd_hist = float(latest["MACD_Hist"]) if latest["MACD_Hist"] is not None else None
    macd_hist_prev = float(prev["MACD_Hist"]) if (prev is not None and prev["MACD_Hist"] is not None) else None
    k = float(latest["K"]) if latest["K"] is not None else None
    d = float(latest["D"]) if latest["D"] is not None else None
    pk = float(prev["K"]) if (prev is not None and prev["K"] is not None) else None
    pd_ = float(prev["D"]) if (prev is not None and prev["D"] is not None) else None

    # 前5日／前20日高低點 — 修正 Bug：不含「今天」自己
    previous_high5 = float(df["High"].iloc[-6:-1].max()) if len(df) >= 6 else None
    previous_low5 = float(df["Low"].iloc[-6:-1].min()) if len(df) >= 6 else None
    previous_high20 = float(df["High"].iloc[-21:-1].max()) if len(df) >= 21 else None
    previous_low20 = float(df["Low"].iloc[-21:-1].min()) if len(df) >= 21 else None

    support = calculate_support_cluster(close, ma20, bb_lower, previous_low5, previous_low20, atr14)
    resistance = calculate_resistance_cluster(close, ma20, bb_upper, previous_high5, previous_high20, atr14)

    no_trade_reasons = check_no_trade(ma20, ma20_prev, ma60, close, volume, vol_ma20, macd_hist, macd_hist_prev)

    kd_cross = None
    if pk is not None and pd_ is not None and k is not None and d is not None:
        if pk <= pd_ and k > d:
            kd_cross = "黃金交叉"
        elif pk >= pd_ and k < d:
            kd_cross = "死亡交叉"

    macd_improving = (macd_hist is not None and macd_hist_prev is not None and macd_hist > macd_hist_prev)
    pullback_support = (support is not None and close is not None
                         and support["zone_low"] <= close <= support["zone_high"] * 1.02)
    # V2.1：量比統一以20日均量為主，並加入量價效率
    prev_close = float(prev["Close"]) if (prev is not None and prev["Close"] is not None) else None
    price_change_pct = ((close - prev_close) / prev_close * 100) if (close is not None and prev_close) else 0.0
    volume_analysis = calculate_volume_metrics(volume, vol_ma20, price_change_pct)
    vol_ok = volume_analysis["volume_ratio_20"] is not None and 0.7 <= volume_analysis["volume_ratio_20"] <= 2.5

    buy_score, buy_reasons = calculate_buy_score(
        ma20, ma60, close, ma5, kd_cross, k, macd_improving,
        pullback_support, vol_ok, inst_bullish=None, fund_ok=None,
    )
    # V2.1：量價效率作為獨立校正，不重複計算單純成交量
    if volume_analysis["score"] >= 80:
        buy_score = min(100, buy_score + 8)
        buy_reasons.append(f"量價：{volume_analysis['status']}")
    elif volume_analysis["score"] <= 40:
        buy_score = max(0, buy_score - 8)
        buy_reasons.append(f"量價警示：{volume_analysis['status']}")

    kd_dead_cross = (kd_cross == "死亡交叉")
    add_result = calculate_add_engine(
        close, ma20, ma20_prev, previous_high5, volume, vol_ma20, ma5,
        macd_hist, macd_hist_prev, kd_dead_cross, None, previous_high20, support,
    )

    risk = calculate_risk_engine(close, atr14, ma20, previous_low5, strategy_pref, close)
    profit = calculate_profit_engine(close, previous_high20, atr14, None, bb_upper, ma5, close, strategy_pref=strategy_pref)

    trend_bullish = (ma20 is not None and ma60 is not None and ma20 > ma60)
    confidence = calculate_confidence(buy_score, vol_ok, trend_bullish, inst_bullish=False,
                                       no_trade_triggered=bool(no_trade_reasons))

    action, label = final_decision(
        no_trade_reasons, add_result, buy_score, position_status=None,
        stop_hit=(risk["hit"] if risk else False),
        stop_warning=(risk["warning_triggered"] if risk else False),
    )

    return {
        "action": action,
        "label": label,
        "score": buy_score,
        "confidence": confidence,
        "reasons": buy_reasons,
        "no_trade_reasons": no_trade_reasons,
        "price_decision": {
            "buy": support,
            "sell": resistance,
            "add": add_result,
            "risk": risk,
            "profit": profit,
        },
        "volume_analysis": volume_analysis,
        "volume_ratio_20": volume_analysis["volume_ratio_20"],
        "price_change_pct": volume_analysis["price_change_pct"],
        "volume_price_efficiency": volume_analysis["efficiency"],
        "volume_status": volume_analysis["status"],
        "_internal": {  # 給 position 分析重複使用，避免重算
            "previous_high5": previous_high5, "previous_low5": previous_low5,
            "previous_high20": previous_high20, "previous_low20": previous_low20,
            "atr14": atr14, "support": support, "resistance": resistance,
        },
    }




# ===========================================================================
# V2.7.16 投資人決策融合層
# ---------------------------------------------------------------------------
# 前台只拿「答案／價位／風險／失效條件」；技術細節留在後台。
# 注意：本層目前是規則型融合器，方向機率屬於「模型估計值」，不是統計保證。
# ===========================================================================
_STOCK_META_CACHE = {"ts": 0.0, "data": {}}


def fetch_stock_meta(stock_id):
    """低頻取得股票名稱／產業；結果記憶體快取24小時，FinMind磁碟快取仍會再保護配額。"""
    now = time.time()
    if now - _STOCK_META_CACHE.get("ts", 0) > 86400 or not _STOCK_META_CACHE.get("data"):
        rows, err = finmind_get({"dataset": "TaiwanStockInfo"}, timeout=20)
        if not err and rows:
            data = {}
            for r in rows:
                sid = str(r.get("stock_id") or "").strip()
                if sid:
                    data[sid] = {
                        "name": r.get("stock_name") or "",
                        "industry": r.get("industry_category") or "",
                        "market": r.get("type") or "",
                    }
            _STOCK_META_CACHE["ts"] = now
            _STOCK_META_CACHE["data"] = data
    return (_STOCK_META_CACHE.get("data") or {}).get(stock_id, {})


def _clamp(v, lo, hi):
    return max(lo, min(hi, v))


# ===========================================================================
# V2.7.18 三核心模型：基本面／技術面／籌碼面
# ---------------------------------------------------------------------------
# 基本面再拆為：商業品質(護城河代理)／財務品質／估值與預期差。
# 質化項目只做「代理分數」，且回傳 coverage / limitations，避免把推估當事實。
# ===========================================================================
_YF_FUND_CACHE = {}
_YF_FUND_TTL = 6 * 3600
_CHIP_MODEL_CACHE = {}
_CHIP_MODEL_TTL = 3600


def _num(v, default=None):
    try:
        if v is None or (isinstance(v, float) and math.isnan(v)):
            return default
        return float(v)
    except Exception:
        return default


def _pct100(v):
    """yfinance 多數比率為 0~1，轉百分點；已是百分數的大值則保留。"""
    x = _num(v)
    if x is None:
        return None
    return x * 100 if abs(x) <= 3 else x


def _score_linear(v, bad, good, reverse=False):
    if v is None:
        return None
    if good == bad:
        return 50.0
    x = (float(v) - bad) / (good - bad) * 100
    x = _clamp(x, 0, 100)
    return 100 - x if reverse else x


def _statement_value(df, labels, pos=0):
    try:
        if df is None or df.empty or len(df.columns) <= pos:
            return None
        for label in labels:
            if label in df.index:
                return _num(df.loc[label].iloc[pos])
    except Exception:
        pass
    return None


def _growth(cur, prev):
    cur, prev = _num(cur), _num(prev)
    if cur is None or prev in (None, 0):
        return None
    return (cur - prev) / abs(prev) * 100


def _yahoo_raw_value(obj, key, default=None):
    """Yahoo quoteSummary 欄位可能是 raw/fmt 物件，統一取 raw。"""
    try:
        v = (obj or {}).get(key, default)
        if isinstance(v, dict):
            return v.get("raw", default)
        return v
    except Exception:
        return default


def fetch_company_fundamentals(stock_id, meta=None):
    """
    V2.9.3 輕量公司資料來源：直接使用 Yahoo 公開 JSON，不載入 yfinance。
    目的：保留主要基本面／估值欄位，同時減少部署套件與執行記憶體。
    三表細項若來源未提供，交由 coverage/limitations 降級，不硬補資料。
    """
    now = time.time()
    cached = _YF_FUND_CACHE.get(stock_id)
    if cached and now - cached[0] < _YF_FUND_TTL:
        return cached[1]

    result = {"available": False, "source": "Yahoo Finance JSON", "limitations": []}
    market = str((meta or {}).get("market") or "")
    suffixes = [".TWO", ".TW"] if ("上櫃" in market or "OTC" in market.upper()) else [".TW", ".TWO"]
    modules = "assetProfile,financialData,defaultKeyStatistics,summaryDetail,price"

    for suffix in suffixes:
        symbol = str(stock_id) + suffix
        try:
            url = f"https://query1.finance.yahoo.com/v10/finance/quoteSummary/{symbol}"
            r = requests.get(url, params={"modules": modules}, headers={"User-Agent": "Mozilla/5.0"}, timeout=10)
            if r.status_code != 200:
                continue
            j = r.json()
            qr = (j.get("quoteSummary") or {}).get("result") or []
            if not qr:
                continue
            x = qr[0] or {}
            profile = x.get("assetProfile") or {}
            fin = x.get("financialData") or {}
            stat = x.get("defaultKeyStatistics") or {}
            detail = x.get("summaryDetail") or {}
            price = x.get("price") or {}

            revenue_growth = _pct100(_yahoo_raw_value(fin, "revenueGrowth"))
            earnings_growth = _pct100(_yahoo_raw_value(fin, "earningsGrowth"))
            gross_margin = _pct100(_yahoo_raw_value(fin, "grossMargins"))
            operating_margin = _pct100(_yahoo_raw_value(fin, "operatingMargins"))
            profit_margin = _pct100(_yahoo_raw_value(fin, "profitMargins"))
            roe = _pct100(_yahoo_raw_value(fin, "returnOnEquity"))
            current_ratio = _num(_yahoo_raw_value(fin, "currentRatio"))
            debt_to_equity = _num(_yahoo_raw_value(fin, "debtToEquity"))
            # Yahoo debtToEquity 常以百分比表示，近似轉成資產負債率代理；不冒充正式財報值。
            debt_ratio = None
            if debt_to_equity is not None and debt_to_equity >= 0:
                de = debt_to_equity / 100.0 if debt_to_equity > 3 else debt_to_equity
                debt_ratio = de / (1.0 + de) * 100 if de >= 0 else None

            fcf = _num(_yahoo_raw_value(fin, "freeCashflow"))
            ocf = _num(_yahoo_raw_value(fin, "operatingCashflow"))
            total_revenue = _num(_yahoo_raw_value(fin, "totalRevenue"))
            fcf_margin = (fcf / total_revenue * 100) if fcf is not None and total_revenue else None

            result.update({
                "available": True,
                "ticker": symbol,
                "name": _yahoo_raw_value(price, "longName") or _yahoo_raw_value(price, "shortName") or (meta or {}).get("name"),
                "sector": profile.get("sector"), "industry": profile.get("industry"),
                "business_summary": (profile.get("longBusinessSummary") or "")[:1200],
                "market_cap": _num(_yahoo_raw_value(price, "marketCap")),
                "revenue_growth": revenue_growth, "earnings_growth": earnings_growth,
                "gross_margin": gross_margin, "operating_margin": operating_margin,
                "profit_margin": profit_margin, "roe": roe,
                "free_cash_flow": fcf, "operating_cash_flow": ocf,
                "cfo_to_net_income": None, "fcf_margin": fcf_margin,
                "debt_ratio": debt_ratio, "current_ratio": current_ratio,
                "receivable_growth": None, "inventory_growth": None,
                "trailing_pe": _num(_yahoo_raw_value(detail, "trailingPE")),
                "forward_pe": _num(_yahoo_raw_value(detail, "forwardPE")),
                "price_to_book": _num(_yahoo_raw_value(stat, "priceToBook")),
                "dividend_yield": _pct100(_yahoo_raw_value(detail, "dividendYield")),
                "peg_ratio": _num(_yahoo_raw_value(stat, "pegRatio")),
                "target_mean_price": _num(_yahoo_raw_value(fin, "targetMeanPrice")),
                "analyst_count": int(_num(_yahoo_raw_value(fin, "numberOfAnalystOpinions"), 0) or 0),
                "recommendation_mean": _num(_yahoo_raw_value(fin, "recommendationMean")),
            })
            result["limitations"].append("輕量模式不常駐下載完整三表；應收／存貨與現金流品質細項缺值時由 coverage 自動降級")
            if not result.get("business_summary"):
                result["limitations"].append("公司商業模式文字資料不足")
            break
        except Exception as e:
            result["limitations"].append(str(e)[:120])

    if not result.get("available"):
        result["limitations"].append("Yahoo 輕量公司資料暫不可用")
    _YF_FUND_CACHE[stock_id] = (now, result)
    return result

def build_financial_quality_model(raw, revenue_yoy=None):
    """財務品質：只保留目前資料來源能穩定取得、且跨公司有解釋力的指標。

    不再為缺失的應收、存貨、CFO/淨利硬補中性分；金融業亦不套用一般產業的負債/流動比門檻。
    分數只依「實際有資料」項目加權，coverage 另外揭露。
    """
    rg = raw.get("revenue_growth") if raw else None
    if rg is None and revenue_yoy is not None:
        rg = float(revenue_yoy)
    eg = raw.get("earnings_growth") if raw else None
    gm = raw.get("gross_margin") if raw else None
    om = raw.get("operating_margin") if raw else None
    nm = raw.get("profit_margin") if raw else None
    roe = raw.get("roe") if raw else None
    fcfm = raw.get("fcf_margin") if raw else None
    debt = raw.get("debt_ratio") if raw else None
    cr = raw.get("current_ratio") if raw else None
    sector = str((raw or {}).get("sector") or "").lower()
    is_financial = any(k in sector for k in ("financial", "bank", "insurance"))

    # 名稱, 值, 單位, 分數, 權重。門檻只作跨產業保守基準，後續由產業相對模型替代。
    items = [
        ("營收成長", rg, "%", _score_linear(rg, -10, 25), 1.2),
        ("獲利成長", eg, "%", _score_linear(eg, -15, 30), 1.2),
        ("營業利益率", om, "%", _score_linear(om, 0, 20), 1.0),
        ("淨利率", nm, "%", _score_linear(nm, 0, 15), 0.8),
        ("ROE", roe, "%", _score_linear(roe, 3, 18), 1.2),
        ("自由現金流率", fcfm, "%", _score_linear(fcfm, -8, 12), 1.0),
    ]
    # 毛利率產業差異極大，只降為低權重輔助，不再當核心高權重。
    items.append(("毛利率（產業差異大）", gm, "%", _score_linear(gm, 5, 40), 0.4))
    if not is_financial:
        # 修正舊版反向錯誤：負債比越低越好；金融業不適用一般企業門檻。
        debt_score = None if debt is None else _clamp((75 - float(debt)) / 50 * 100, 0, 100)
        items.append(("負債比", debt, "%", debt_score, 0.8))
        items.append(("流動比率", cr, "x", _score_linear(cr, 0.8, 2.0), 0.6))

    out=[]; total=0.0; wsum=0.0; risks=[]; strengths=[]
    for name,val,unit,sc,w in items:
        state="資料不足" if sc is None else ("良好" if sc>=70 else "普通" if sc>=45 else "風險")
        out.append({"name":name,"value":round(val,2) if isinstance(val,(int,float)) else val,"unit":unit,
                    "score":round(sc,1) if sc is not None else None,"state":state})
        if sc is not None:
            total += sc*w; wsum += w
            if sc < 35: risks.append(name+"偏弱")
            elif sc >= 75: strengths.append(name+"良好")
    score = (total/wsum) if wsum else None
    coverage = sum(1 for _,_,_,sc,_ in items if sc is not None) / len(items) * 100 if items else 0
    label = "資料不足" if score is None else ("強健" if score>=75 else "偏強" if score>=62 else "中性" if score>=45 else "偏弱" if score>=30 else "高風險")
    note = "金融業不套用一般企業負債比/流動比門檻" if is_financial else "缺值不補分；毛利率僅低權重輔助"
    return {"score":round(score,1) if score is not None else None,"label":label,"coverage":round(coverage,1),"items":out,
            "strengths":strengths[:4],"risks":risks[:4],"note":note}

def build_business_quality_model(raw, financial):
    """商業模式只做描述，不再用『護城河代理分數』混入投資分數。

    沒有客戶集中度、轉換成本、競爭地位、管理品質等可靠資料時，硬算護城河分數會造成假精準。
    """
    summary=(raw.get("business_summary") or "") if raw else ""
    observations=[]
    if raw:
        if raw.get("gross_margin") is not None: observations.append("毛利率可作產品定價力線索，但需與同業比較")
        if raw.get("operating_margin") is not None: observations.append("營業利益率可觀察營運效率")
        if raw.get("roe") is not None: observations.append("ROE可觀察資本效率")
        if raw.get("fcf_margin") is not None: observations.append("自由現金流可觀察獲利含金量")
    return {"score":None,"label":"質化觀察","coverage":100 if summary else 40,"summary":summary[:360],
            "reasons":observations[:4],"risks":[],
            "limitations":["缺少可靠的客戶集中度、競爭優勢、轉換成本與管理品質資料，因此不把護城河量化成分數。"]}

def build_valuation_expectation_model(raw, valuation, current_price):
    """估值只採可解釋且有資料的項目，缺值不補分。

    歷史本益比比較為主；PB、成長/估值與分析師共識只在資料足夠時低權重加入。
    """
    pe = raw.get("trailing_pe") if raw else None
    pb = raw.get("price_to_book") if raw else None
    target = raw.get("target_mean_price") if raw else None
    analyst_count = int((raw or {}).get("analyst_count") or 0)
    growth = raw.get("earnings_growth") if raw else None
    hist_avg = _num((valuation or {}).get("pe_avg")) if valuation and not valuation.get("_error") else None
    components=[]; notes=[]; risks=[]

    if pe is not None and pe > 0 and hist_avg and hist_avg > 0:
        rel=(pe/hist_avg-1)*100
        sc=_clamp((40-rel)/65*100,0,100)  # 約低歷史25%=>高分；高40%=>低分
        components.append((sc,0.50)); notes.append(f"本益比相對歷史均值 {rel:+.1f}%")
    if pb is not None and pb > 0:
        sc=_clamp((6-float(pb))/5*100,0,100)
        components.append((sc,0.15))
    if growth is not None and growth > 0 and pe is not None and pe > 0:
        peg_proxy=pe/max(growth,1)
        sc=_clamp((2.5-peg_proxy)/1.7*100,0,100)
        components.append((sc,0.20)); notes.append(f"成長/估值代理 {peg_proxy:.2f}")
    consensus_upside=None
    if target and current_price and analyst_count >= 3:
        consensus_upside=(target/current_price-1)*100
        sc=_clamp((consensus_upside+15)/40*100,0,100)
        components.append((sc,0.15)); notes.append(f"{analyst_count}位分析師共識目標空間 {consensus_upside:+.1f}%")

    if components:
        w=sum(w for _,w in components); score=sum(sc*w for sc,w in components)/w
    else:
        score=None
    coverage=min(100, len(components)/4*100)
    if score is not None and score<40: risks.append("估值相對偏高")
    label="資料不足" if score is None else ("偏低估" if score>=72 else "合理偏低" if score>=60 else "合理" if score>=45 else "偏高估" if score>=30 else "高估風險")
    return {"score":round(score,1) if score is not None else None,"label":label,"pe":pe,"pb":pb,
            "historical_pe_avg":hist_avg,"consensus_target":target if analyst_count>=3 else None,
            "consensus_upside_pct":round(consensus_upside,1) if consensus_upside is not None else None,
            "analyst_count":analyst_count,"coverage":round(coverage,1),"notes":notes[:4],"risks":risks,
            "expectation_gap":None,"expectation_gap_label":"待可靠共識/修正資料"}

def build_fundamental_model(stock_id, meta, revenue_yoy, valuation, current_price):
    raw=fetch_company_fundamentals(stock_id,meta)
    financial=build_financial_quality_model(raw,revenue_yoy)
    business=build_business_quality_model(raw,financial)
    val=build_valuation_expectation_model(raw,valuation,current_price)
    # 只融合有可驗證數值的財務與估值；不再拿虛構中性總經/產業分數稀釋結果。
    parts=[]
    if financial.get("coverage",0) >= 25: parts.append((financial["score"],0.70))
    if val.get("coverage",0) >= 25: parts.append((val["score"],0.30))
    if parts:
        w=sum(x[1] for x in parts); composite=sum(x[0]*x[1] for x in parts)/w
    else:
        composite=None
    coverage=round((financial.get("coverage",0)*0.7 + val.get("coverage",0)*0.3),1)
    label="資料不足" if composite is None else ("偏強" if composite>=65 else "中性偏強" if composite>=55 else "中性" if composite>=45 else "偏弱")
    return {"score":round(composite,1) if composite is not None else None,"label":label,"coverage":coverage,
            "business":business,"financial":financial,"valuation_expectation":val,
            "macro":{"score":None,"label":"由市場層判斷","note":"不在公司基本面內硬塞固定50分。"},
            "industry":{"score":None,"label":"待產業相對模型","industry":(meta or {}).get("industry") or raw.get("industry"),
                        "note":"沒有同業比較資料時不虛構產業分數。"},
            "raw_source":raw.get("source"),"data_available":raw.get("available",False),"limitations":raw.get("limitations",[])}

def fetch_chip_model(stock_id):
    now=time.time(); c=_CHIP_MODEL_CACHE.get(stock_id)
    if c and now-c[0]<_CHIP_MODEL_TTL: return c[1]
    end=datetime.now().strftime("%Y-%m-%d"); start=(datetime.now()-timedelta(days=45)).strftime("%Y-%m-%d")
    inst, e1=finmind_get({"dataset":"TaiwanStockInstitutionalInvestorsBuySell","data_id":stock_id,"start_date":start,"end_date":end},timeout=20)
    margin, e2=finmind_get({"dataset":"TaiwanStockMarginPurchaseShortSale","data_id":stock_id,"start_date":start,"end_date":end},timeout=20)
    bydate={}
    for r in inst or []:
        d=r.get("date"); name=str(r.get("name") or "").lower(); net=_num(r.get("buy"),0)-_num(r.get("sell"),0)
        rec=bydate.setdefault(d,{"foreign":0,"trust":0,"dealer":0,"total":0})
        if "foreign" in name: rec["foreign"]+=net
        elif "investment" in name: rec["trust"]+=net
        elif "dealer" in name: rec["dealer"]+=net
        rec["total"]+=net
    dates=sorted(bydate)
    def sumlast(key,n): return sum(bydate[d][key] for d in dates[-n:]) if dates else 0
    def streak(key):
        if not dates:return 0
        sign=1 if bydate[dates[-1]][key]>0 else -1 if bydate[dates[-1]][key]<0 else 0
        if sign==0:return 0
        n=0
        for d in reversed(dates):
            v=bydate[d][key]
            if (v>0 and sign>0) or (v<0 and sign<0): n+=1
            else: break
        return n*sign
    latest_margin=(margin or [])[-1] if margin else {}
    old_margin=(margin or [])[-6] if len(margin or [])>=6 else ((margin or [None])[0] if margin else None)
    mb=_num(latest_margin.get("MarginPurchaseTodayBalance")) if latest_margin else None
    mbo=_num(old_margin.get("MarginPurchaseTodayBalance")) if old_margin else None
    margin_chg=(mb/mbo-1)*100 if mb is not None and mbo not in (None,0) else None
    factors=[]
    total5=sumlast("total",5); total20=sumlast("total",20); f5=sumlast("foreign",5); t5=sumlast("trust",5)
    fs=streak("foreign"); ts=streak("trust")
    # 沒有法人資料時，不再用 0 推導出五個「中性50」假分數。
    if dates:
        factors.append(65 if total5>0 else 35 if total5<0 else 50)
        factors.append(68 if f5>0 else 32 if f5<0 else 50)
        factors.append(72 if t5>0 else 30 if t5<0 else 50)
        factors.append(_clamp(50+fs*6,20,80))
        factors.append(_clamp(50+ts*7,20,85))
    if margin_chg is not None:
        factors.append(_clamp(55-margin_chg*2,25,75)) # 融資暴增視為較高風險
    score=sum(factors)/len(factors) if factors else None
    label="資料不足" if score is None else ("資金明顯偏多" if score>=68 else "籌碼偏多" if score>=58 else "中性" if score>=43 else "籌碼偏空" if score>=32 else "資金明顯偏空")
    coverage=round(len(factors)/7*100,1)
    out={"score":round(score,1) if score is not None else None,"label":label,"latest_date":dates[-1] if dates else None,
         "institutional":{"total_5d":round(total5/1000) if dates else None,"total_20d":round(total20/1000) if dates else None,"foreign_5d":round(f5/1000) if dates else None,"trust_5d":round(t5/1000) if dates else None,"foreign_streak":fs if dates else None,"trust_streak":ts if dates else None},
         "margin":{"balance":mb,"change_5d_pct":round(margin_chg,2) if margin_chg is not None else None},
         "large_holder":{"available":False,"note":"千張大戶/主力分點需穩定授權資料源；未取得時不納入分數，不以猜測補值。"},
         "coverage":coverage,"raw":{"inst":inst or [],"margin":margin or []},"errors":[x for x in [e1,e2] if x]}
    _CHIP_MODEL_CACHE[stock_id]=(now,out); return out


def build_technical_core_model(latest, decision, score_pct, kd_cross):
    """技術核心只用有實際資料的子項；缺值不補 50 分。"""
    components=[]
    trend=_num(score_pct)
    if trend is not None:
        components.append(("trend", trend, .45))

    va=((decision or {}).get("volume_analysis") or {})
    vp=_num(va.get("score")) if va.get("status") not in (None,"資料不足") else None
    if vp is not None:
        components.append(("volume", vp, .35))

    kd_component=None
    if kd_cross=="黃金交叉": kd_component=65
    elif kd_cross=="死亡交叉": kd_component=35
    elif kd_cross not in (None,"","無資料"): kd_component=50
    macd_h=_num(latest.get("MACD_Hist") if isinstance(latest,dict) else None)
    momentum=kd_component
    if momentum is None and macd_h is not None:
        momentum=58 if macd_h>0 else 42
    elif momentum is not None and macd_h is not None:
        momentum=_clamp(momentum + (8 if macd_h>0 else -8),0,100)
    if momentum is not None:
        components.append(("momentum", momentum, .20))

    if components:
        sw=sum(w for _,_,w in components)
        score=sum(v*w for _,v,w in components)/sw
    else:
        score=None
    coverage=round(sum(w for _,_,w in components)*100,1)
    label="資料不足" if score is None else ("多頭" if score>=68 else "偏多" if score>=58 else "中性" if score>=43 else "偏空" if score>=32 else "空頭")
    return {"score":round(score,1) if score is not None else None,"label":label,"coverage":coverage,
            "trend_score":round(trend,1) if trend is not None else None,
            "volume_price_score":round(vp,1) if vp is not None else None,
            "momentum_score":round(momentum,1) if momentum is not None else None,
            "kd":kd_cross,"volume_status":(decision or {}).get("volume_status")}

def build_three_core_model(fundamental, technical, chip, strategy_pref="short"):
    """三核心只融合資料覆蓋率達門檻的核心；至少兩核心才形成綜合判斷。"""
    fs=_num((fundamental or {}).get("score")); fc=_num((fundamental or {}).get("coverage"),0)
    ts=_num((technical or {}).get("score")); tc=_num((technical or {}).get("coverage"),0)
    cs=_num((chip or {}).get("score")); cc=_num((chip or {}).get("coverage"),0)
    if fc < 35: fs=None
    if tc < 50: ts=None
    if cc < 40: cs=None
    if strategy_pref=="mid": base={"fundamental":.40,"technical":.35,"chip":.25}
    else: base={"fundamental":.15,"technical":.50,"chip":.35}
    vals={"fundamental":fs,"technical":ts,"chip":cs}
    active={k:w for k,w in base.items() if vals.get(k) is not None}
    sw=sum(active.values())
    weights={k:(active.get(k,0)/sw if sw else 0) for k in base}
    available_count=sum(v is not None for v in vals.values())
    score=(sum(vals[k]*weights[k] for k in vals if vals[k] is not None) if available_count>=2 else None)
    all_three=available_count==3
    if score is None:
        label="資料不足"
    elif all_three and score>=67 and ts>=55 and cs>=50:
        label="三面共振偏多"
    elif score>=58:
        label="偏多"
    elif score>=43:
        label="中性"
    elif score>=33:
        label="偏空"
    elif all_three:
        label="三面共振偏空"
    else:
        label="偏空"
    conflicts=[]
    present=[v for v in (fs,ts,cs) if v is not None]
    if len(present)>=2 and max(present)-min(present)>=30: conflicts.append("基本／技術／籌碼分歧較大")
    return {"score":round(score,1) if score is not None else None,"label":label,"weights":weights,
            "fundamental":round(fs,1) if fs is not None else None,"technical":round(ts,1) if ts is not None else None,
            "chip":round(cs,1) if cs is not None else None,"conflicts":conflicts,"available_core_count":available_count,
            "coverage":{"fundamental":fc,"technical":tc,"chip":cc},
            "weight_note":"只融合覆蓋率達門檻的核心；基準權重待 Walk-forward 驗證後再調整"}

def apply_three_core_guard(v27, core):
    """三核心做風控修正；缺資料時不以中性50假裝通過。"""
    if not isinstance(v27,dict) or not isinstance(core,dict): return v27
    dec=v27.get("decision") or {}; cash=dec.get("cash") or {}; holder=dec.get("holder") or {}; risks=dec.setdefault("risks",[])
    if core.get("conflicts"):
        risks.extend([x for x in core["conflicts"] if x not in risks])
    tech=_num(core.get("technical")); chip=_num(core.get("chip")); fund=_num(core.get("fundamental")); total=_num(core.get("score"))
    if tech is None or chip is None:
        if cash.get("action")=="BUY": cash.update({"action":"WAIT","label":"等待"})
        risks.append("技術或籌碼資料覆蓋不足，暫不主動進場")
    elif tech<40 or chip<35:
        if cash.get("action")=="BUY": cash.update({"action":"WAIT","label":"等待"})
        risks.append("技術或籌碼未通過進場門檻")
    if fund is not None and fund<32:
        risks.append("公司基本面模型偏弱，中期風險升高")
    if total is None and holder.get("action")=="ADD":
        holder.update({"action":"HOLD","label":"續抱／停止加碼"}); risks.append("三核心資料不足，停止加碼")
    elif total is not None and total<42 and holder.get("action")=="ADD":
        holder.update({"action":"HOLD","label":"續抱／停止加碼"}); risks.append("三核心綜合未通過加碼門檻")
    dec["cash"]=cash; dec["holder"]=holder; dec["risks"]=list(dict.fromkeys(risks))[:6]; v27["decision"]=dec; v27["three_core"]=core
    return v27

def apply_v28_stability_gate(v28, core):
    """V2.8 正式上線門檻：主動進場/加碼必須同時通過資料、方向與三核心一致性。

    風控只會把積極動作降級，不會覆寫已觸發的停損/減碼等高優先決策。
    """
    if not isinstance(v28, dict):
        return v28
    dec = v28.get("decision") or {}
    cash = dec.get("cash") or {}
    holder = dec.get("holder") or {}
    direction = v28.get("direction") or {}
    dq = v28.get("data_quality") or {}
    risks = dec.setdefault("risks", [])

    dq_score = _num(dq.get("score"), 0)
    conf = _num(direction.get("confidence"), 0)
    up = _num(direction.get("up_probability"), 0)
    core_score = _num((core or {}).get("score"))
    tech = _num((core or {}).get("technical"))
    chip = _num((core or {}).get("chip"))

    gates = {
        "data_quality": dq_score >= 70,
        "direction_strength": conf >= 70,
        "upside_support": up >= 58,
        "three_core": core_score is not None and core_score >= 58,
        "technical": tech is not None and tech >= 55,
        "chip": chip is not None and chip >= 50,
    }
    passed = all(gates.values())

    if cash.get("action") == "BUY" and not passed:
        cash.update({"action": "WAIT", "label": "等待"})
        failed = [k for k, ok in gates.items() if not ok]
        name_map = {
            "data_quality": "資料品質",
            "direction_strength": "方向判斷強度",
            "upside_support": "偏多支持度",
            "three_core": "三核心綜合",
            "technical": "技術面",
            "chip": "籌碼面",
        }
        risks.append("V2.8 主動進場門檻未全部通過：" + "、".join(name_map[x] for x in failed))

    if holder.get("action") == "ADD" and not passed:
        holder.update({"action": "HOLD", "label": "續抱／停止加碼"})
        risks.append("V2.8 加碼門檻未全部通過")

    # 去重並限制前台風險訊息長度
    dec["risks"] = list(dict.fromkeys(risks))[:6]
    dec["cash"] = cash
    dec["holder"] = holder
    v28["decision"] = dec
    v28["stability_gate"] = {
        "passed": passed,
        "gates": gates,
        "release_stage": RELEASE_STAGE,
        "note": "主動進場/加碼需同時通過資料品質、方向判斷強度與三核心資料門檻；偏多支持度是內部規則量尺，不是機率。",
    }
    return v28


# ===========================================================================
# V2.8.1 台股制度／政策環境引擎（Taiwan Market Rule Engine）
# ---------------------------------------------------------------------------
# 核心原則：模型只能在臺灣市場制度允許的範圍內產生價格與交易建議。
# 主要官方依據（規則版本：2026-08-06）：
# - TWSE 營業細則第 3 條：集中市場交易時間原則 09:00~13:30
# - TWSE 營業細則第 62 條：股票申報買賣價格升降單位
# - TWSE 營業細則第 63 條：一般股票每日漲跌幅原則 ±10%；初次上市普通股特定情況前5日例外
# - TWSE 處置有價證券規則：處置期間可能分盤撮合、預收款券、暫停融資融券等
#
# 注意：除權息、初上市、恢復交易、變更交易方法、處置等「當日特殊狀態」
# 必須以交易所當日正式公告/開盤競價基準為準。若資料源未能自動驗證，系統會明確標記，
# 不會把「一般規則估算」偽裝成已確認的交易所資料。
# ===========================================================================
TWSE_RULE_VERSION = "2026-08-06"
TWSE_RULE_SOURCES = {
    "trading_hours": "TWSE Operating Rules Article 3",
    "tick_size": "TWSE Operating Rules Article 62",
    "price_limit": "TWSE Operating Rules Article 63",
    "disposition": "TWSE disposition securities rules / investor education",
}


_MARKET_HOLIDAY_CACHE = {"year": None, "holidays": set(), "ts": 0.0, "verified": False}


def _fetch_twse_market_holidays(year):
    """TWSE 官方休市日曆；抓取失敗時標記未驗證。"""
    now_ts = time.time()
    if (_MARKET_HOLIDAY_CACHE.get("year") == year and
            now_ts - _MARKET_HOLIDAY_CACHE.get("ts", 0) < 7 * 86400):
        return set(_MARKET_HOLIDAY_CACHE.get("holidays") or set()), bool(_MARKET_HOLIDAY_CACHE.get("verified"))
    holidays = set()
    verified = False
    try:
        roc_year = year - 1911
        r = requests.get(
            "https://www.twse.com.tw/rwd/zh/holidaySchedule/holidaySchedule",
            params={"response": "json", "queryYear": str(roc_year)},
            headers={"User-Agent": "Mozilla/5.0"}, timeout=8,
        )
        j = r.json() if r.status_code == 200 else {}
        for row in (j.get("data") or []):
            if not row:
                continue
            raw = str(row[0]).strip().replace("/", "-")
            candidates = []
            if "月" in raw and "日" in raw:
                try:
                    m = int(raw.split("月")[0].split()[-1])
                    d = int(raw.split("月")[1].split("日")[0])
                    candidates.append(f"{year:04d}-{m:02d}-{d:02d}")
                except Exception:
                    pass
            parts = [x for x in raw.replace("年", "-").replace("月", "-").replace("日", "").split("-") if x]
            try:
                if len(parts) >= 3:
                    yy, mm, dd = int(parts[-3]), int(parts[-2]), int(parts[-1])
                    if yy < 1911:
                        yy += 1911
                    candidates.append(f"{yy:04d}-{mm:02d}-{dd:02d}")
                elif len(parts) == 2:
                    candidates.append(f"{year:04d}-{int(parts[0]):02d}-{int(parts[1]):02d}")
            except Exception:
                pass
            holidays.update(candidates)
        verified = isinstance(j.get("data"), list)
    except Exception:
        verified = False
    _MARKET_HOLIDAY_CACHE.update({"year": year, "holidays": holidays, "ts": now_ts, "verified": verified})
    return holidays, verified


def _taipei_market_clock():
    try:
        from zoneinfo import ZoneInfo
        now = datetime.now(ZoneInfo("Asia/Taipei"))
    except Exception:
        now = datetime.now()
    hhmm = now.hour * 60 + now.minute
    weekday = now.weekday()
    holidays, holiday_verified = _fetch_twse_market_holidays(now.year)
    today = now.date().isoformat()
    if weekday >= 5:
        code, session = "CLOSED", "非交易日（週末）"
    elif holiday_verified and today in holidays:
        code, session = "CLOSED", "非交易日（TWSE休市）"
    elif hhmm < 8 * 60 + 30:
        code, session = "PRE_MARKET", "盤前"
    elif hhmm < 9 * 60:
        code, session = "ORDER_ENTRY", "一般交易委託時段（尚未撮合）"
    elif hhmm < 13 * 60 + 30:
        code, session = "REGULAR", "集中市場交易中"
    elif hhmm < 13 * 60 + 40:
        code, session = "POST_REGULAR_GAP", "一般交易已收盤／等待盤後零股"
    elif hhmm < 14 * 60:
        code, session = "ODD_LOT_AFTER_HOURS", "盤後零股委託時段"
    elif hhmm < 14 * 60 + 30:
        code, session = "AFTER_HOURS", "盤後定價＋盤後零股時段"
    else:
        code, session = "POST_CLOSE", "收盤後"
    return {
        "time": now.strftime("%Y-%m-%d %H:%M:%S"), "date": today,
        "session": session, "code": code, "weekday": weekday,
        "holiday_calendar_verified": holiday_verified,
        "is_trading_day": code != "CLOSED",
    }


def build_taiwan_market_rule_engine(reference_price, close, stock_id, meta=None, special_status=None,
                                    opening_reference=None, no_price_limit=False, official_limits=None):
    """建立台股硬規則校驗層。special_status 若無官方資料則保持『未自動驗證』。"""
    meta = meta or {}
    status = (special_status or "未自動驗證").strip()
    ref = opening_reference if opening_reference not in (None, "") else reference_price
    clock = _taipei_market_clock()

    if no_price_limit:
        limits = {"reference": round_to_tick(ref) if ref else None, "limit_up": None, "limit_down": None,
                  "estimated": False, "no_limit": True, "source": "special_rule"}
    elif official_limits and official_limits.get("available"):
        # 交易所即時欄位若已直接提供 u/w，優先採用，不自行重算。
        off_ref = official_limits.get("reference")
        if off_ref not in (None, ""):
            ref = float(off_ref)
        limits = {
            "reference": round_to_tick(ref) if ref else None,
            "limit_up": round_to_tick(official_limits.get("limit_up")) if official_limits.get("limit_up") is not None else None,
            "limit_down": round_to_tick(official_limits.get("limit_down")) if official_limits.get("limit_down") is not None else None,
            "estimated": False,
            "source": official_limits.get("source") or "TWSE MIS",
            "open": round_to_tick(official_limits.get("open")) if official_limits.get("open") is not None else None,
        }
        # 個別欄位缺失時才依官方參考價補算。
        calc = taiwan_daily_price_limits(ref) if ref else {}
        if limits["limit_up"] is None:
            limits["limit_up"] = calc.get("limit_up")
        if limits["limit_down"] is None:
            limits["limit_down"] = calc.get("limit_down")
    else:
        limits = taiwan_daily_price_limits(ref)
        limits["source"] = "historical_fallback"

    restrictions = []
    hard_block = False
    status_lower = status.lower()
    if any(k in status for k in ["停止交易", "終止上市", "暫停交易"]):
        hard_block = True
        restrictions.append("官方交易狀態限制：目前不得依一般股票規則產生主動進場建議")
    elif "處置" in status:
        restrictions.append("處置有價證券：撮合頻率、預收款券、融資融券等可能受限制")
    elif "注意" in status:
        restrictions.append("注意有價證券：交易異常風險提高，主動進場門檻上調")
    elif "變更交易方法" in status:
        restrictions.append("變更交易方法有價證券：交易方式與一般股票不同")

    special_unverified = status == "未自動驗證"
    notes = []
    if special_unverified:
        notes.append("注意／處置／變更交易方法／停止交易等特殊狀態尚未由官方資料源自動驗證")
    if official_limits and official_limits.get("available"):
        notes.append("當日漲跌停優先採用交易所即時參考價／漲跌停欄位；今日開盤成交價僅供顯示，不直接作為法定基準。")
    elif opening_reference is None:
        notes.append("交易所當日參考價未取得時，才以前一交易日收盤價估算；除權息、初上市等特殊交易日須以交易所基準為準。")
    notes.append("交易所休市日與臨時制度異動應以 TWSE/TPEx 最新公告為準")

    confidence = 100
    if special_unverified: confidence -= 15
    if not (official_limits and official_limits.get("available")) and opening_reference is None: confidence -= 10
    confidence = max(0, confidence)

    return {
        "rule_version": TWSE_RULE_VERSION,
        "market": meta.get("market") or "TWSE/TPEx待辨識",
        "security_status": status,
        "hard_block": hard_block,
        "restrictions": restrictions,
        "compliance_confidence": confidence,
        "session": clock,
        "tick_size_at_close": taiwan_tick_size(close) if close else None,
        "daily_limits": limits,
        "normal_rules": {
            "regular_session": "一般交易委託 08:30-13:30；撮合 09:00-13:30",
            "odd_lot_session": "盤中零股委託 09:00-13:30（09:10起撮合）；盤後零股 13:40-14:30（14:30撮合）",
            "after_hours_session": "盤後定價委託 14:00-14:30；14:30撮合",
            "daily_price_limit": "一般普通股以當市開盤競價基準 ±10% 為原則",
            "tick_rule": "股票升降單位：<10=0.01；10~<50=0.05；50~<100=0.1；100~<500=0.5；500~<1000=1；>=1000=5",
            "special_exceptions": "初次上市普通股（不含上櫃轉上市）前5個交易日無一般漲跌幅限制；除權息、減資恢復等依交易所當日開盤競價基準",
            "lot_rule": "一般股票整張 1,000 股；零股 1~999 股",
            "tax_rule": "一般股票賣出證交稅 0.3%；符合現股當沖規定之賣出稅率 0.15%（現行優惠至2027-12-31）",
            "broker_fee_rule": "券商手續費由券商訂定；系統預設基準 0.1425%，可用環境變數覆寫",
        },
        "notes": notes,
        "sources": TWSE_RULE_SOURCES,
    }


def build_policy_environment(meta=None, market_regime=None):
    """政策環境層：只在有可驗證政策事件時調整模型；沒有資料時維持中性，不硬猜。"""
    meta = meta or {}
    return {
        "score": 50,
        "label": "中性／待官方政策事件資料",
        "industry": meta.get("industry") or "",
        "market_regime": (market_regime or {}).get("label"),
        "principle": "政策先判斷影響產業與公司基本面，再檢查價格是否已反映；不得以『政府支持』直接等同股價必漲。",
        "verified_events": [],
        "data_status": "目前未在 /api/stock 內自動抓取官方政策事件，故不加分也不扣分",
        "source_priority": ["金管會", "臺灣證券交易所", "櫃買中心", "中央銀行", "經濟部", "財政部", "行政院/主管機關正式公告"],
    }


def apply_taiwan_market_rule_guard(v28, market_rules, policy_env=None):
    """把市場硬規則放在模型決策之上；政策環境只做可驗證事件的調整。"""
    if not v28 or v28.get("error"):
        return v28
    dec = v28.setdefault("decision", {})
    risks = list(dec.get("risks") or [])
    cash = dict(dec.get("cash") or {})
    holder = dict(dec.get("holder") or {})

    status = (market_rules or {}).get("security_status", "")
    hard_block = bool((market_rules or {}).get("hard_block"))
    if hard_block:
        cash.update({"action": "WAIT", "label": "等待／禁止主動進場"})
        dec["add_state"] = "停止加碼"
        risks.extend((market_rules or {}).get("restrictions") or [])
    elif "處置" in status or "變更交易方法" in status:
        cash.update({"action": "WAIT", "label": "等待／交易制度限制"})
        dec["add_state"] = "停止加碼"
        risks.extend((market_rules or {}).get("restrictions") or [])
    elif "注意" in status:
        # 注意股不等於禁止交易，但提高門檻；前台明確提醒。
        risks.extend((market_rules or {}).get("restrictions") or [])
        if cash.get("action") == "BUY":
            cash.update({"action": "WAIT", "label": "等待／注意股風險"})

    dec["cash"] = cash
    dec["holder"] = holder
    dec["risks"] = list(dict.fromkeys(risks))[:8]
    v28["decision"] = dec
    v28["market_rules"] = market_rules
    v28["policy_environment"] = policy_env or {}
    return v28


_TWSE_STATUS_CACHE = {"ts": 0.0, "data": {}}
_TWSE_STATUS_TTL = 900


def _row_stock_code(row):
    for k in ("Code", "證券代號", "股票代號", "SecuritiesCompanyCode"):
        v = row.get(k) if isinstance(row, dict) else None
        if v not in (None, ""):
            return str(v).strip()
    if isinstance(row, dict):
        for k, v in row.items():
            if ("代號" in str(k) or str(k).lower() == "code") and v not in (None, ""):
                return str(v).strip()
    return ""


def fetch_twse_special_status(stock_id, meta=None):
    """TWSE 官方 OpenAPI：注意／處置／暫停交易／變更交易方法。上櫃股仍標記待 TPEx 驗證。"""
    market = str((meta or {}).get("market") or "")
    if "上櫃" in market or "OTC" in market.upper():
        return {"status": "未自動驗證", "verified": False, "source": "TPEx待介接", "details": []}
    now_ts = time.time()
    if now_ts - _TWSE_STATUS_CACHE.get("ts", 0) > _TWSE_STATUS_TTL or not _TWSE_STATUS_CACHE.get("data"):
        datasets = {
            "注意": "https://openapi.twse.com.tw/v1/announcement/notice",
            "處置": "https://openapi.twse.com.tw/v1/announcement/punish",
            "停止交易": "https://openapi.twse.com.tw/v1/exchangeReport/TWTAWU",
            "變更交易方法": "https://openapi.twse.com.tw/v1/exchangeReport/TWT85U",
        }
        status_map = {}
        any_verified = False
        for label, url in datasets.items():
            try:
                r = requests.get(url, headers={"User-Agent": "Mozilla/5.0"}, timeout=6)
                rows = r.json() if r.status_code == 200 else []
                if isinstance(rows, list):
                    any_verified = True
                    for row in rows:
                        code = _row_stock_code(row)
                        if not code:
                            continue
                        status_map.setdefault(code, []).append({"label": label, "row": row})
            except Exception:
                continue
        _TWSE_STATUS_CACHE.update({"ts": now_ts, "data": status_map, "verified": any_verified})
    matches = (_TWSE_STATUS_CACHE.get("data") or {}).get(str(stock_id), [])
    labels = [m.get("label") for m in matches if m.get("label")]
    if "停止交易" in labels:
        status = "停止交易"
    elif "處置" in labels:
        status = "處置"
    elif "變更交易方法" in labels:
        status = "變更交易方法"
    elif "注意" in labels:
        status = "注意"
    else:
        status = "正常" if _TWSE_STATUS_CACHE.get("verified") else "未自動驗證"
    return {
        "status": status,
        "verified": bool(_TWSE_STATUS_CACHE.get("verified")),
        "source": "TWSE OpenAPI",
        "details": matches[:4],
    }


_TWSE_REALTIME_CACHE = {}
_TWSE_REALTIME_TTL = 20


def _twse_num(v):
    """TWSE MIS 即時欄位字串轉數字；'-' / 空值回傳 None。"""
    try:
        if v in (None, "", "-", "--"):
            return None
        return float(str(v).replace(",", "").strip())
    except Exception:
        return None


def fetch_twse_realtime_limits(stock_id, meta=None):
    """優先取得交易所即時個股的當日參考價／漲停／跌停。

    TWSE MIS 回傳欄位中：
      y = 參考價（一般日通常為前一日收盤；特殊交易日依交易所基準）
      u = 當日漲停價
      w = 當日跌停價
      o = 今日第一筆成交／開盤價（僅供顯示，不作漲跌停基準）

    目的：避免用 FinMind 歷史資料的「上一列收盤」誤當今天交易所基準。
    失敗時回傳 available=False，後續才使用歷史資料估算。
    """
    now = time.time()
    cached = _TWSE_REALTIME_CACHE.get(str(stock_id))
    if cached and now - cached[0] < _TWSE_REALTIME_TTL:
        return cached[1]

    market = str((meta or {}).get("market") or "")
    # 上櫃先試 otc；上市先試 tse；不確定則兩者都試。
    if "上櫃" in market or "OTC" in market.upper():
        prefixes = ["otc", "tse"]
    else:
        prefixes = ["tse", "otc"]

    result = {"available": False, "source": "TWSE MIS"}
    for prefix in prefixes:
        try:
            ex_ch = f"{prefix}_{stock_id}.tw"
            r = requests.get(
                "https://mis.twse.com.tw/stock/api/getStockInfo.jsp",
                params={"ex_ch": ex_ch, "json": "1", "delay": "0"},
                headers={
                    "User-Agent": "Mozilla/5.0",
                    "Referer": "https://mis.twse.com.tw/stock/fibest.jsp",
                },
                timeout=6,
            )
            if r.status_code != 200:
                continue
            j = r.json()
            rows = j.get("msgArray") or []
            if not rows:
                continue
            q = rows[0] or {}
            ref = _twse_num(q.get("y"))
            up = _twse_num(q.get("u"))
            down = _twse_num(q.get("w"))
            op = _twse_num(q.get("o"))
            last = _twse_num(q.get("z"))
            high = _twse_num(q.get("h"))
            low = _twse_num(q.get("l"))
            volume = _twse_num(q.get("v"))
            if ref is None and up is None and down is None and last is None:
                continue
            result = {
                "available": True,
                "source": "TWSE MIS",
                "market_channel": prefix,
                "reference": ref,
                "limit_up": up,
                "limit_down": down,
                "open": op,
                "last": last,
                "high": high,
                "low": low,
                "volume": volume,
                "name": q.get("n") or q.get("nf") or "",
                "time": q.get("t") or "",
                "date": q.get("d") or "",
            }
            break
        except Exception:
            continue

    _TWSE_REALTIME_CACHE[str(stock_id)] = (now, result)
    return result


_INTRADAY_CACHE = {}
_INTRADAY_CACHE_TTL = 300

def _safe_float(v):
    try:
        if v is None: return None
        x = float(v)
        return x if math.isfinite(x) else None
    except Exception:
        return None

def _yahoo_intraday_symbol(stock_id, meta=None):
    market = str((meta or {}).get("market") or "").upper()
    if "上櫃" in market or "OTC" in market:
        return [f"{stock_id}.TWO", f"{stock_id}.TW"]
    return [f"{stock_id}.TW", f"{stock_id}.TWO"]

def fetch_intraday_5m(stock_id, meta=None):
    """最近 5 個交易日的 5 分鐘價量；使用網站 JSON，不消耗 FinMind 配額。"""
    now = time.time(); key = str(stock_id)
    cached = _INTRADAY_CACHE.get(key)
    if cached and now - cached[0] < _INTRADAY_CACHE_TTL:
        return cached[1]
    result = {"available": False, "source": "Yahoo Finance 5m", "bars": []}
    for sym in _yahoo_intraday_symbol(stock_id, meta):
        try:
            r = requests.get(
                f"https://query1.finance.yahoo.com/v8/finance/chart/{sym}",
                params={"interval":"5m","range":"5d","includePrePost":"false","events":"div,splits"},
                headers={"User-Agent":"Mozilla/5.0"}, timeout=4)
            if r.status_code != 200: continue
            root = (((r.json() or {}).get("chart") or {}).get("result") or [])
            if not root: continue
            obj = root[0] or {}; ts = obj.get("timestamp") or []
            quote = ((((obj.get("indicators") or {}).get("quote") or [{}])[0]) or {})
            opens = quote.get("open") or []; highs = quote.get("high") or []; lows = quote.get("low") or []
            closes = quote.get("close") or []; vols = quote.get("volume") or []
            tz = ZoneInfo("Asia/Taipei"); bars = []
            for i, stamp in enumerate(ts):
                try:
                    dt = datetime.fromtimestamp(int(stamp), tz)
                    if dt.hour < 9 or dt.hour > 13: continue
                    o = _safe_float(opens[i] if i < len(opens) else None); c = _safe_float(closes[i] if i < len(closes) else None)
                    h = _safe_float(highs[i] if i < len(highs) else None); l = _safe_float(lows[i] if i < len(lows) else None)
                    v = _safe_float(vols[i] if i < len(vols) else None)
                    if c is None or v is None: continue
                    bars.append({"date":dt.strftime("%Y-%m-%d"),"time":dt.strftime("%H:%M"),"open":o,"high":h,"low":l,"close":c,"volume_shares":v})
                except Exception:
                    continue
            if bars:
                result = {"available": True, "source":"Yahoo Finance 5m", "symbol":sym, "bars":bars}
                break
        except Exception:
            continue
    _INTRADAY_CACHE[key] = (now, result)
    return result

def analyze_intraday_volume(stock_id, meta=None):
    """量在哪裡出現、是否比過去同時段異常、放量後價格是否有推進。"""
    raw = fetch_intraday_5m(stock_id, meta)
    if not raw.get("available"):
        return {"available":False,"source":raw.get("source"),"summary":"盤中 5 分鐘資料暫時無法取得"}
    bars = raw.get("bars") or []; dates = sorted({b["date"] for b in bars})
    if not dates: return {"available":False,"source":raw.get("source"),"summary":"盤中資料不足"}
    target = dates[-1]; today = [b for b in bars if b["date"] == target]; prior = [b for b in bars if b["date"] != target]
    if not today: return {"available":False,"source":raw.get("source"),"summary":"今日盤中資料不足"}
    byslot = {}
    for b in prior: byslot.setdefault(b["time"], []).append(float(b.get("volume_shares") or 0))
    today_vols = [float(b.get("volume_shares") or 0) for b in today]; med_today = median(today_vols) if today_vols else 0
    anomalies = []
    for b in today:
        hist = byslot.get(b["time"]) or []; baseline = median(hist) if hist else None
        ratio = float(b.get("volume_shares") or 0) / baseline if baseline and baseline > 0 else None
        op = b.get("open") or b.get("close"); cl = b.get("close"); pct = ((cl/op - 1) * 100) if op and cl else 0.0
        if ratio is not None and ratio >= 1.8 and float(b.get("volume_shares") or 0) >= med_today:
            if abs(pct) < 0.15: code, label = "HIGH_VOLUME_STALLED", "大量成交但價格推進有限"
            elif pct >= 0.25: code, label = "HIGH_VOLUME_UP", "放量上攻"
            elif pct <= -0.25: code, label = "HIGH_VOLUME_DOWN", "放量下壓"
            else: code, label = "HIGH_VOLUME_MIXED", "異常放量"
            anomalies.append({"time":b["time"],"volume_lots":round(float(b.get("volume_shares") or 0)/1000),"same_time_ratio":round(ratio,2),"price_change_pct":round(pct,2),"code":code,"label":label})
    anomalies = sorted(anomalies, key=lambda x:x.get("same_time_ratio") or 0, reverse=True)[:5]
    segments = [("開盤","09:00","09:30"),("上午","09:30","11:00"),("中場","11:00","12:30"),("尾盤","12:30","13:31")]
    total = sum(float(b.get("volume_shares") or 0) for b in today); segs=[]
    for name,start,end in segments:
        rows = [b for b in today if start <= b["time"] < end]; vol = sum(float(b.get("volume_shares") or 0) for b in rows)
        pct = None
        if rows:
            first = rows[0].get("open") or rows[0].get("close"); last = rows[-1].get("close")
            pct = ((last/first-1)*100) if first and last else None
        segs.append({"name":name,"volume_lots":round(vol/1000),"share_pct":round(vol/total*100,1) if total else None,"price_change_pct":round(pct,2) if pct is not None else None})
    concentration = max(segs, key=lambda x:x.get("share_pct") or 0) if segs else None
    stalls=[x for x in anomalies if x["code"]=="HIGH_VOLUME_STALLED"]; downs=[x for x in anomalies if x["code"]=="HIGH_VOLUME_DOWN"]; ups=[x for x in anomalies if x["code"]=="HIGH_VOLUME_UP"]
    if downs: impact, impact_code, note = "偏空警示", "RISK", "出現異常放量下壓，明日追價與加碼宜保守。"
    elif stalls: impact, impact_code, note = "追價保守", "CAUTION", "出現大量成交但價格推進有限，上方供給可能較重。"
    elif ups: impact, impact_code, note = "偏多確認", "POSITIVE", "出現相對同時段放量上攻，但仍需配合收盤位置與隔日市場環境。"
    else: impact, impact_code, note = "中性", "NEUTRAL", "未偵測到明顯的 5 分鐘異常量價時段。"
    return {"available":True,"source":raw.get("source"),"date":target,"interval":"5m","total_volume_lots":round(total/1000),"segments":segs,"volume_concentration":(concentration or {}).get("name"),"anomalies":anomalies,"impact":impact,"impact_code":impact_code,"note":note,"method":"最近5個交易日同一5分鐘時段中位數比較；異常量門檻 1.8 倍。"}

def apply_intraday_volume_guard(v27, intraday):
    """盤中量價是風控層：可降低積極動作，但不能單靠單一時段把等待升成買進。"""
    if not isinstance(v27, dict) or not isinstance(intraday, dict) or not intraday.get("available"): return v27
    dec=v27.get("decision") or {}; cash=dec.get("cash") or {}; risks=dec.setdefault("risks",[]); reasons=dec.setdefault("reasons",[])
    code=intraday.get("impact_code")
    if code in ("RISK","CAUTION"):
        if cash.get("action")=="BUY": cash.update({"action":"WAIT","label":"等待"})
        if dec.get("add_state")=="可評估加碼": dec["add_state"]="停止加碼"
        risks.append("盤中量價：" + str(intraday.get("impact") or "偏弱"))
    elif code=="POSITIVE": reasons.append("盤中量價：放量上攻確認")
    dec["cash"]=cash; dec["risks"]=list(dict.fromkeys(risks))[:6]; dec["reasons"]=list(dict.fromkeys(reasons))[:5]
    v27["decision"]=dec; v27["intraday_volume"]=intraday; return v27

class _SimpleTableParser(HTMLParser):
    def __init__(self): super().__init__(); self.rows=[]; self.row=None; self.cell=None
    def handle_starttag(self,tag,attrs):
        if tag=='tr': self.row=[]
        elif tag in ('td','th') and self.row is not None: self.cell=[]
    def handle_data(self,data):
        if self.cell is not None: self.cell.append(data)
    def handle_endtag(self,tag):
        if tag in ('td','th') and self.cell is not None:
            self.row.append(' '.join(''.join(self.cell).split())); self.cell=None
        elif tag=='tr' and self.row is not None:
            if self.row: self.rows.append(self.row)
            self.row=None

_TAIFEX_SENTIMENT_CACHE={"ts":0,"data":None}
def fetch_taifex_sentiment():
    """官方 Put/Call 比只作大盤情緒背景，不直接轉成個股買賣訊號。"""
    now=time.time()
    if _TAIFEX_SENTIMENT_CACHE.get("data") and now-_TAIFEX_SENTIMENT_CACHE.get("ts",0)<3600: return _TAIFEX_SENTIMENT_CACHE["data"]
    out={"available":False,"source":"TAIFEX","label":"資料不足"}
    try:
        r=requests.get('https://www.taifex.com.tw/cht/3/pcRatio',headers={"User-Agent":"Mozilla/5.0"},timeout=5)
        p=_SimpleTableParser(); p.feed(r.text); row=None
        for rr in p.rows:
            if rr and re.match(r'^\d{4}[/-]\d{1,2}[/-]\d{1,2}$',rr[0]) and len(rr)>=7: row=rr; break
        if row:
            nums=[_safe_float(str(x).replace(',','').replace('%','')) for x in row[1:7]]
            vr=nums[2] if len(nums)>2 else None; oi=nums[5] if len(nums)>5 else None
            label="避險交易偏高" if vr is not None and vr>=115 else ("買權交易相對活躍" if vr is not None and vr<=85 else "選擇權情緒中性")
            out={"available":True,"source":"TAIFEX Put/Call Ratio","date":row[0],"put_call_volume_ratio_pct":vr,"put_call_oi_ratio_pct":oi,"label":label,"note":"Put/Call 比只作大盤情緒輔助，不直接等同看多或看空個股。"}
    except Exception: pass
    _TAIFEX_SENTIMENT_CACHE.update({"ts":now,"data":out}); return out

@app.route('/api/taifex_sentiment')
def api_taifex_sentiment(): return jsonify({"status":200, **fetch_taifex_sentiment()})

@app.route('/api/intraday_volume')
def api_intraday_volume():
    sid=request.args.get('symbol','').strip()
    if not sid.isdigit(): return jsonify({"status":400,"msg":"請輸入數字股票代號"}),400
    return jsonify({"status":200, **analyze_intraday_volume(sid, fetch_stock_meta(sid))})

def taiwan_tick_size(price):
    """台股一般股票常用升降單位（ETF等商品可能另有規則；此處用於一般個股價位顯示）。"""
    p = float(price or 0)
    if p < 10: return 0.01
    if p < 50: return 0.05
    if p < 100: return 0.1
    if p < 500: return 0.5
    if p < 1000: return 1.0
    return 5.0


def round_to_tick(price):
    if price is None:
        return None
    tick = taiwan_tick_size(price)
    return round(round(float(price) / tick) * tick, 2)


def _floor_to_tick(price):
    """向下取到合法台股升降單位；用於漲停價，避免超過 +10%。"""
    if price is None:
        return None
    import math
    tick = taiwan_tick_size(price)
    return round(math.floor((float(price) + 1e-12) / tick) * tick, 2)


def _ceil_to_tick(price):
    """向上取到合法台股升降單位；用於跌停價，避免超過 -10%。"""
    if price is None:
        return None
    import math
    tick = taiwan_tick_size(price)
    return round(math.ceil((float(price) - 1e-12) / tick) * tick, 2)


def taiwan_daily_price_limits(reference_price):
    """
    一般台股個股每日漲跌幅 ±10%。
    reference_price 應優先使用交易所當日開盤競價基準；目前日線資料沒有獨立欄位時，
    一般交易日以最近一日收盤價作估算基準。除權息、初上市等特殊交易日需以交易所基準價為準。
    """
    if reference_price is None or float(reference_price) <= 0:
        return {"reference": None, "limit_up": None, "limit_down": None, "estimated": True}
    ref = float(reference_price)
    return {
        "reference": round_to_tick(ref),
        "limit_up": _floor_to_tick(ref * 1.10),
        "limit_down": _ceil_to_tick(ref * 0.90),
        "estimated": True,
    }


def _clip_price_to_limits(price, limits):
    if price is None:
        return None
    lo = (limits or {}).get("limit_down")
    hi = (limits or {}).get("limit_up")
    p = float(price)
    if lo is not None: p = max(p, float(lo))
    if hi is not None: p = min(p, float(hi))
    return round_to_tick(p)


def reconcile_v27_with_market_rules(v27, market_rules, live_quote=None):
    """以交易所當日官方價格限制重新校正作戰卡，避免舊基準殘留。"""
    if not isinstance(v27, dict) or v27.get("error"):
        return v27
    plan = v27.get("price_plan") or {}
    limits = dict((market_rules or {}).get("daily_limits") or {})
    if limits:
        for key in ("entry_zone", "add_zone"):
            z = plan.get(key) or {}
            if z.get("low") is not None:
                z["low"] = _clip_price_to_limits(z.get("low"), limits)
            if z.get("high") is not None:
                z["high"] = _clip_price_to_limits(z.get("high"), limits)
            plan[key] = z
        # 防守／停損屬當日可執行風控價，可受今日價格限制約束；
        # 第一／第二目標屬跨日策略目標，不得裁成今天漲停價。
        for key in ("defense", "stop_loss"):
            if plan.get(key) is not None:
                plan[key] = _clip_price_to_limits(plan.get(key), limits)
        plan["daily_limits"] = limits
        base = None
        if live_quote and live_quote.get("last") is not None:
            base = float(live_quote["last"])
        if base is not None and base > 0:
            vals = []
            for k in ("model_target_1", "model_target_2", "target_1", "target_2"):
                t = plan.get(k)
                if t is not None and float(t) > base:
                    vals.append((float(t) / base - 1) * 100)
            # 去重，避免相同目標重複影響範圍。
            vals = sorted(set(round(v, 6) for v in vals))
            model_remain = ({"low": round(min(vals), 1), "high": round(max(vals), 1)} if vals else None)
            plan["model_remaining_upside_pct"] = model_remain
            plan["remaining_upside_pct"] = model_remain
            if limits.get("limit_up") is not None and float(limits["limit_up"]) > base:
                plan["daily_legal_upside_pct"] = round((float(limits["limit_up"]) / base - 1) * 100, 1)
            else:
                plan["daily_legal_upside_pct"] = None
    v27["price_plan"] = plan
    v27["price_context"] = {
        "current_price": (live_quote or {}).get("last"),
        "open": (live_quote or {}).get("open"),
        "high": (live_quote or {}).get("high"),
        "low": (live_quote or {}).get("low"),
        "quote_time": (live_quote or {}).get("time"),
        "quote_date": (live_quote or {}).get("date"),
        "session": (market_rules or {}).get("session"),
        "source": (live_quote or {}).get("source"),
    }
    return v27


def classify_market_regime(close, ma20, ma60, atr14):
    if close is None:
        return {"code": "UNKNOWN", "label": "資料不足", "volatility": "未知"}
    atr_pct = (float(atr14) / float(close) * 100) if atr14 and close else None
    high_vol = atr_pct is not None and atr_pct >= 3.5
    if ma20 is not None and ma60 is not None:
        if close > ma20 > ma60:
            label = "多頭高波動" if high_vol else "多頭趨勢"
            code = "BULL_HIGH_VOL" if high_vol else "BULL"
        elif close < ma20 < ma60:
            label = "空頭高波動" if high_vol else "空頭趨勢"
            code = "BEAR_HIGH_VOL" if high_vol else "BEAR"
        else:
            label, code = "區間震盪", "RANGE"
    else:
        label, code = "區間震盪", "RANGE"
    return {
        "code": code,
        "label": label,
        "atr_pct": round(atr_pct, 2) if atr_pct is not None else None,
        "volatility": "高" if high_vol else "一般",
    }


def build_data_quality(df, latest, weekly_kd=None, revenue_yoy=None, valuation=None, meta=None):
    score = 0
    notes = []
    rows = len(df)
    if rows >= 250:
        score += 35
    elif rows >= 120:
        score += 25; notes.append("歷史資料未滿250個交易日")
    else:
        score += 15; notes.append("歷史樣本偏少")

    critical = [latest.get("Close"), latest.get("MA20"), latest.get("K"), latest.get("D"), latest.get("ATR14")]
    critical_ok = sum(x is not None and not pd.isna(x) for x in critical)
    score += round(25 * critical_ok / len(critical))
    if critical_ok < len(critical): notes.append("部分核心技術欄位缺失")

    if latest.get("Volume") is not None and latest.get("Vol_MA20") is not None:
        score += 15
    else:
        notes.append("成交量資料不足")
    if weekly_kd: score += 10
    else: notes.append("週期資料不足")
    if revenue_yoy is not None: score += 5
    if valuation and not valuation.get("_error"): score += 5
    if meta and meta.get("name"): score += 5

    score = int(_clamp(score, 0, 100))
    if score >= 85: grade, state = "A", "正常"
    elif score >= 70: grade, state = "B", "輕度降級"
    elif score >= 55: grade, state = "C", "嚴重降級"
    else: grade, state = "D", "禁止主動交易判斷"
    return {"score": score, "grade": grade, "state": state, "notes": notes[:4]}


def estimate_direction_v27(score_pct, volume_analysis, regime, kd_cross, macd_hist, macd_hist_prev, no_trade_reasons, data_quality):
    """規則融合的方向估計；三分類總和=100。之後可由Walk-forward校準層替換。"""
    edge = (float(score_pct or 50) - 50) * 0.55
    vscore = (volume_analysis or {}).get("score", 50)
    edge += (float(vscore) - 50) * 0.18
    rcode = (regime or {}).get("code")
    if rcode in ("BULL", "BULL_HIGH_VOL"): edge += 7
    elif rcode in ("BEAR", "BEAR_HIGH_VOL"): edge -= 7
    if kd_cross == "黃金交叉": edge += 4
    elif kd_cross == "死亡交叉": edge -= 4
    if macd_hist is not None and macd_hist_prev is not None:
        edge += 3 if macd_hist > macd_hist_prev else -3
    if no_trade_reasons: edge -= min(12, 4 * len(no_trade_reasons))

    # 資料品質愈低，機率往中性收斂，避免假性高信心。
    dq = float((data_quality or {}).get("score", 50))
    shrink = _clamp((dq - 45) / 55, 0.15, 1.0)
    edge *= shrink

    sideways = 24.0
    if abs(edge) < 8: sideways = 38.0
    elif abs(edge) < 15: sideways = 30.0
    if rcode == "RANGE": sideways += 7
    sideways = _clamp(sideways, 18, 52)
    directional = 100 - sideways
    up = directional / 2 + edge
    down = directional - up
    up = _clamp(up, 8, 84)
    down = _clamp(down, 8, 84)
    # 重新正規化
    total = up + down + sideways
    up, down, sideways = [round(x / total * 100, 1) for x in (up, down, sideways)]
    drift = round(100 - up - down - sideways, 1)
    sideways = round(sideways + drift, 1)

    if up >= 58: label = "偏多"
    elif down >= 58: label = "偏空"
    elif up >= down + 8: label = "震盪偏多"
    elif down >= up + 8: label = "震盪偏空"
    else: label = "震盪"

    # 目前尚未累積足夠 Walk-forward 樣本，三分類只能視為「方向權重」，
    # 不能包裝成統計機率。判斷強度同時考慮資料品質、因子一致性與方向優勢。
    consistency = 100 - min(45, abs(float(score_pct or 50) - float(vscore)))
    direction_edge = abs(up - down)
    edge_strength = _clamp(direction_edge * 3.0, 0, 100)
    signal_strength = int(_clamp(0.40 * dq + 0.35 * consistency + 0.25 * edge_strength, 0, 100))
    if signal_strength >= 80:
        strength_level = "強"
    elif signal_strength >= 65:
        strength_level = "中高"
    elif signal_strength >= 50:
        strength_level = "中"
    else:
        strength_level = "低"
    return {
        "label": label,
        # 新欄位：正式語意為規則融合權重。
        "up_weight": up,
        "sideways_weight": sideways,
        "down_weight": down,
        "signal_strength": signal_strength,
        "signal_strength_level": strength_level,
        # 相容既有決策層；名稱保留但前台不可稱為真實機率／準確率。
        "up_probability": up,
        "sideways_probability": sideways,
        "down_probability": down,
        "confidence": signal_strength,
        "probability_type": "規則融合權重（未校準機率）",
        "calibration_status": "待累積足夠 Walk-forward 樣本後才轉為統計校準機率",
    }


def build_v27_price_plan(close, decision, reference_price=None):
    pdx = (decision or {}).get("price_decision") or {}
    buy = pdx.get("buy") or {}
    add = pdx.get("add") or {}
    risk = pdx.get("risk") or {}
    profit = pdx.get("profit") or {}
    limits = taiwan_daily_price_limits(reference_price if reference_price is not None else close)
    entry_low = _clip_price_to_limits(buy.get("zone_low"), limits)
    entry_high = _clip_price_to_limits(buy.get("zone_high"), limits)
    add_low = _clip_price_to_limits(add.get("low"), limits)
    add_high = _clip_price_to_limits(add.get("high"), limits)
    stop = _clip_price_to_limits(risk.get("stop"), limits)
    defense = _clip_price_to_limits(risk.get("warning"), limits)
    # 目標價是跨交易日的策略目標，不應被「今天」的漲跌停價裁切。
    # 僅用台股升降單位做價格格式化；當日漲跌停另列為法定空間。
    raw_t1 = profit.get("target1")
    raw_t2 = profit.get("target2")
    t1 = round_to_tick(float(raw_t1)) if raw_t1 is not None else None
    t2 = round_to_tick(float(raw_t2)) if raw_t2 is not None else None
    remain1 = ((t1 / close - 1) * 100) if (close and t1 and t1 > close) else None
    remain2 = ((t2 / close - 1) * 100) if (close and t2 and t2 > close) else None
    positives = [x for x in (remain1, remain2) if x is not None and x > 0]
    model_remain = None
    if positives:
        model_remain = {"low": round(min(positives), 1), "high": round(max(positives), 1)}
    legal_upside = None
    if close and limits.get("limit_up") is not None and float(limits["limit_up"]) > close:
        legal_upside = round((float(limits["limit_up"]) / close - 1) * 100, 1)
    rr = calculate_risk_reward(close, stop, t1 or t2) if close and stop and (t1 or t2) else None
    return {
        "entry_zone": {"low": entry_low, "high": entry_high},
        "add_zone": {"low": add_low, "high": add_high, "type": add.get("type"), "note": add.get("note")},
        "defense": defense,
        "stop_loss": stop,
        "target_1": t1,
        "target_2": t2,
        "model_target_1": t1,
        "model_target_2": t2,
        "model_remaining_upside_pct": model_remain,
        "remaining_upside_pct": model_remain,
        "daily_legal_upside_pct": legal_upside,
        "upside_basis": "技術壓力／20日高點／ATR／估值參考；非漲停距離",
        "risk_reward": rr,
        "daily_limits": limits,
    }


def fuse_v27_decision(decision, position, direction, price_plan, data_quality, regime):
    no_trade = list((decision or {}).get("no_trade_reasons") or [])
    dq = (data_quality or {}).get("score", 0)
    # 空手策略
    action = (decision or {}).get("action") or "WAIT"
    if dq < 55:
        cash_action = "WAIT"; cash_label = "等待"
        no_trade.append("核心資料品質不足，禁止主動進場")
    elif no_trade:
        cash_action = "WAIT"; cash_label = "等待"
    elif action == "BUY" and direction.get("up_probability", 0) >= 55:
        cash_action = "BUY"; cash_label = "進場"
    else:
        cash_action = "WAIT"; cash_label = "等待"

    # 持股策略：有成本資料時沿用風險優先裁決；未輸入時只提供市場狀態，不假裝知道個人成本。
    if position:
        pa = position.get("final_action") or position.get("status") or "HOLD"
        pmap = {"STOP":"停損", "REDUCE":"減碼／停利", "HOLD":"續抱", "ADD":"加碼", "WAIT":"等待", "NO_TRADE":"停止加碼"}
        holder_action = pa
        holder_label = pmap.get(pa, "續抱")
    else:
        holder_action = "UNSET"
        holder_label = "請輸入持股成本"

    add_obj = ((decision or {}).get("price_decision") or {}).get("add") or {}
    add_allowed = dq >= 70 and not no_trade and add_obj.get("type") in ("PULLBACK", "BREAKOUT", "TREND")
    add_state = "可評估加碼" if add_allowed else "停止加碼"

    # 風險/理由/失效條件精簡成投資人可讀文案
    reasons = []
    if direction.get("label"): reasons.append("明日方向「%s」" % direction["label"])
    vstat = (decision or {}).get("volume_status")
    if vstat: reasons.append("量價：%s" % vstat)
    if regime and regime.get("label"): reasons.append("市場結構：%s" % regime["label"])
    reasons.extend(((decision or {}).get("reasons") or [])[:2])
    # 去重
    reasons = list(dict.fromkeys(reasons))[:4]

    risks = list(no_trade)
    if direction.get("confidence", 0) < 70: risks.append("目前模型判斷強度不足")
    if (data_quality or {}).get("state") != "正常": risks.append("資料品質為%s" % (data_quality or {}).get("state"))
    risks = list(dict.fromkeys(risks))[:4]

    invalidation = None
    if price_plan.get("stop_loss") is not None:
        invalidation = "跌破 %s 且無法快速收復，原判斷失效" % price_plan["stop_loss"]
    elif price_plan.get("defense") is not None:
        invalidation = "跌破防守位 %s 後重新評估" % price_plan["defense"]

    return {
        "cash": {"action": cash_action, "label": cash_label},
        "holder": {"action": holder_action, "label": holder_label},
        "add_state": add_state,
        "reasons": reasons,
        "risks": risks,
        "invalidation": invalidation,
    }


def build_v27_analysis(df, latest, prev, score_pct, decision, position, weekly_kd, revenue_yoy, valuation, meta, kd_cross):
    close = float(latest["Close"])
    ma20 = float(latest["MA20"]) if latest["MA20"] is not None else None
    ma60 = float(latest["MA60"]) if latest["MA60"] is not None else None
    atr14 = float(latest["ATR14"]) if latest["ATR14"] is not None else None
    regime = classify_market_regime(close, ma20, ma60, atr14)
    dq = build_data_quality(df, latest, weekly_kd, revenue_yoy, valuation, meta)
    direction = estimate_direction_v27(
        score_pct,
        (decision or {}).get("volume_analysis") or {},
        regime,
        kd_cross,
        float(latest["MACD_Hist"]) if latest["MACD_Hist"] is not None else None,
        float(prev["MACD_Hist"]) if prev is not None and prev["MACD_Hist"] is not None else None,
        (decision or {}).get("no_trade_reasons") or [],
        dq,
    )
    reference_price = float(prev["Close"]) if prev is not None and prev["Close"] is not None else close
    plan = build_v27_price_plan(close, decision, reference_price=reference_price)
    fused = fuse_v27_decision(decision, position, direction, plan, dq, regime)
    return {
        "system_version": SYSTEM_VERSION,
        "ruleset_version": CORE_RULESET_VERSION,
        "model_version": MODEL_VERSION,
        "release_stage": RELEASE_STAGE,
        "data_quality": dq,
        "market_regime": regime,
        "direction": direction,
        "price_plan": plan,
        "decision": fused,
        "front_end_principle": "前台給答案；後台負責運算",
    }


# ===========================================================================
# /api/stock — 個股健診主端點（後端計算技術指標）
# 從 FinMind 抓股價 → pandas 算指標 → 回傳 JSON
# ===========================================================================
@app.route("/api/stock")
def get_stock_data():
    stock_id = request.args.get("symbol", "").strip()
    if not stock_id:
        return jsonify({"status": 400, "msg": "缺少 symbol 參數"}), 400

    # 確保代號為純數字（台股）
    if not stock_id.isdigit():
        return jsonify({"status": 400, "msg": "請輸入數字股票代號"}), 400

    # --- Step 1: 股票名稱／產業低頻快取查詢 ---
    # V2.7.16：數字代號也必須顯示名稱，避免輸入錯股；TaiwanStockInfo 由快取保護配額。
    meta = fetch_stock_meta(stock_id)
    stock_name = meta.get("name", "")
    industry = meta.get("industry", "")

    # --- Step 2: 從 FinMind 抓股價（拉長區間以利週KD計算）---
    end_date = datetime.now().strftime("%Y-%m-%d")
    start_date = (datetime.now() - timedelta(days=260)).strftime("%Y-%m-%d")
    raw, err = finmind_get({
        "dataset": "TaiwanStockPrice",
        "data_id": stock_id,
        "start_date": start_date,
        "end_date": end_date,
    }, timeout=20)
    if err:
        return jsonify({"status": 502, "msg": err}), 502

    if not raw:
        return jsonify({"status": 404, "msg": "查無此股票代號的股價資料"}), 404

    # --- Step 3: 組 DataFrame 並計算指標 ---
    df = pd.DataFrame(raw)
    df["Close"] = pd.to_numeric(df["close"], errors="coerce")
    df["High"] = pd.to_numeric(df["max"], errors="coerce")
    df["Low"] = pd.to_numeric(df["min"], errors="coerce")
    df["Open"] = pd.to_numeric(df["open"], errors="coerce")
    df["Volume"] = pd.to_numeric(df["Trading_Volume"], errors="coerce")
    df["Date"] = df["date"]
    df = df.dropna(subset=["Close"])
    df = df.reset_index(drop=True)

    if len(df) < 26:
        return jsonify({"status": 422, "msg": f"股價資料不足（僅 {len(df)} 筆，需至少 26 筆）"}), 422

    df = calculate_indicators(df)

    # NaN → None
    df = df.where(pd.notnull(df), None)

    latest = df.iloc[-1]
    prev = df.iloc[-2] if len(df) >= 2 else None

    # --- 漲跌與漲跌幅（相對前一交易日收盤價）---
    prev_close = float(prev["Close"]) if prev is not None and prev["Close"] is not None else None
    price_change = None
    price_change_pct = None
    if prev_close is not None and prev_close != 0:
        price_change = round(float(latest["Close"]) - prev_close, 2)
        price_change_pct = round(price_change / prev_close * 100, 2)

    # --- KD 交叉判斷 ---
    kd_cross = ""
    if prev is not None and prev["K"] is not None and prev["D"] is not None:
        if prev["K"] <= prev["D"] and latest["K"] > latest["D"]:
            kd_cross = "黃金交叉"
        elif prev["K"] >= prev["D"] and latest["K"] < latest["D"]:
            kd_cross = "死亡交叉"
        elif latest["K"] > latest["D"]:
            kd_cross = "K>D 偏多"
        else:
            kd_cross = "K<D 偏空"

    # --- MACD 趨勢 ---
    macd_dir = "正（多頭）" if latest["MACD_Hist"] > 0 else "負（空頭）"
    macd_trend = ""
    if prev is not None and prev["MACD_Hist"] is not None:
        h, ph = latest["MACD_Hist"], prev["MACD_Hist"]
        if h > 0 and h > ph:
            macd_trend = "柱狀圖擴大，多頭增強"
        elif h > 0 and h < ph:
            macd_trend = "柱狀圖縮小，多頭減弱"
        elif h < 0 and h < ph:
            macd_trend = "柱狀圖擴大，空頭增強"
        else:
            macd_trend = "柱狀圖縮小，空頭減弱"

    # --- 布林位置 ---
    bb_pos = ""
    if latest["BB_Upper"] is not None and latest["BB_Lower"] is not None:
        rng = latest["BB_Upper"] - latest["BB_Lower"]
        pct = (latest["Close"] - latest["BB_Lower"]) / rng * 100 if rng > 0 else 50
        if pct > 80:
            bb_pos = "上軌附近（偏高）"
        elif pct < 20:
            bb_pos = "下軌附近（偏低）"
        elif pct > 50:
            bb_pos = "中上段"
        else:
            bb_pos = "中下段"

    # --- 近期高低點 ---
    recent_n = min(20, len(df))
    recent_high = float(df["High"].iloc[-recent_n:].max())
    recent_low = float(df["Low"].iloc[-recent_n:].min())

    # --- 買賣停損點 ---
    buy_low = latest["BB_Lower"] if latest["BB_Lower"] is not None else recent_low
    buy_high = latest["MA20"] if latest["MA20"] is not None else latest["Close"]
    sell_low = latest["BB_Upper"] if latest["BB_Upper"] is not None else recent_high
    sell_high = recent_high
    stop_loss = buy_low * 0.93

    # --- 量比 ---
    last_vol = float(latest["Volume"]) if latest["Volume"] is not None else 0
    avg_vol5 = float(latest["Vol_MA5"]) if latest["Vol_MA5"] is not None else 0
    avg_vol20 = float(latest["Vol_MA20"]) if latest["Vol_MA20"] is not None else 0
    vol_ratio = last_vol / avg_vol20 if avg_vol20 > 0 else 1.0

    # --- 技術面評分 ---
    # 設計說明：
    # 1) 均線排列(MA5/MA10/MA20)高度相關，合併成單一「趨勢」子分數，
    #    避免同一件事（多頭排列）被重複計分、稀釋其他獨立訊號的權重
    # 2) KD 加入「訊號新鮮度」（剛黃金/死亡交叉）作為動能加權
    # 3) 動態計算本次可達最大值 score_max，供百分比換算使用
    score = 0
    score_max = 0

    bull_count = 0
    ma_pairs_available = 0
    if latest["MA5"] is not None and latest["MA10"] is not None:
        ma_pairs_available += 1
        if latest["MA5"] > latest["MA10"]:
            bull_count += 1
    if latest["MA10"] is not None and latest["MA20"] is not None:
        ma_pairs_available += 1
        if latest["MA10"] > latest["MA20"]:
            bull_count += 1
    if latest["MA20"] is not None:
        ma_pairs_available += 1
        if latest["Close"] > latest["MA20"]:
            bull_count += 1
    if ma_pairs_available > 0:
        trend_score = round((2 * bull_count - ma_pairs_available) * (2.0 / ma_pairs_available))
        score += trend_score
        score_max += 2

    if latest["MA60"] is not None:
        score += 1 if latest["Close"] > latest["MA60"] else -1
        score_max += 1

    if latest["K"] is not None and latest["D"] is not None:
        score += 1 if latest["K"] > latest["D"] else -1
        score_max += 1
        if kd_cross == "黃金交叉":
            score += 1
        elif kd_cross == "死亡交叉":
            score -= 1
        score_max += 1
        if latest["K"] < 20:
            score += 1
        elif latest["K"] > 80:
            score -= 1
        score_max += 1

    if latest["MACD_Hist"] is not None:
        score += 1 if latest["MACD_Hist"] > 0 else -1
        score_max += 1

    if "偏低" in bb_pos:
        score += 1
        score_max += 1
    elif "偏高" in bb_pos:
        score -= 1
        score_max += 1
    else:
        score_max += 1

    if vol_ratio > 1.5:
        score += 1
        score_max += 1
    elif vol_ratio < 0.5:
        score -= 1
        score_max += 1
    else:
        score_max += 1

    score_pct = round((score + score_max) / (2 * score_max) * 100, 1) if score_max > 0 else 50.0

    # --- 策略訊號（短線3~5天 KD(5,3,3) ／ 波段2~3週 週KD(9,3,3)+日KD(9,3,3)+營收YoY）---
    try:
        weekly_kd = calc_weekly_kd9(df)
        revenue_yoy = fetch_revenue_yoy(stock_id)
        entry_date = request.args.get("entry_date", "").strip() or None
        strategy = build_strategy_signals(
            latest, prev, weekly_kd, revenue_yoy,
            float(latest["Vol_MA20"]) if latest["Vol_MA20"] is not None else None,
            datetime.now().day,
            df=df, entry_date=entry_date,
        )
    except Exception:
        weekly_kd = None
        revenue_yoy = None
        strategy = {
            "light": "neutral",
            "short": {"action": "觀望", "reasons": ["策略訊號計算發生錯誤"]},
            "mid": {"action": "觀望", "reasons": ["策略訊號計算發生錯誤"]},
        }

    # --- 估值引擎（階段1：合理價格 / 合理買入上限 / 目標價）---
    try:
        valuation = fetch_valuation(stock_id, float(latest["Close"]))
    except Exception:
        valuation = None

    # --- V2.7.18 基本面完整模型：商業模式/護城河代理 + 11指標財務品質 + 估值預期差 ---
    try:
        fundamental_model = build_fundamental_model(stock_id, meta, revenue_yoy, valuation, float(latest["Close"]))
    except Exception as e:
        fundamental_model = {"score": 50, "label": "資料不足", "error": str(e)[:120]}

    # --- V2.7.18 籌碼模型：法人連續性 + 5/20日資金 + 融資變化 ---
    try:
        chip_model = fetch_chip_model(stock_id)
    except Exception as e:
        chip_model = {"score": None, "label": "資料不足", "coverage": 0, "raw": {"inst": [], "margin": []}, "errors": [str(e)[:120]]}

    # --- V2.1 價格決策引擎（支撐/壓力聚集、核心買賣點±1%、禁止交易、補倉、動態停損停利、信心度）---
    strategy_pref = request.args.get("strategy_pref", "short").strip()
    if strategy_pref not in ("short", "mid"):
        strategy_pref = "short"
    try:
        decision = build_price_decision(latest, prev, df, strategy_pref=strategy_pref)
        if valuation and not valuation.get("_error"):
            # 有估值資料時，把估值目標價納入第二停利參考（重算一次 profit）
            atr14_v = float(latest["ATR14"]) if latest["ATR14"] is not None else None
            prev_high20_v = decision["_internal"]["previous_high20"]
            bb_upper_v = float(latest["BB_Upper"]) if latest["BB_Upper"] is not None else None
            ma5_v = float(latest["MA5"]) if latest["MA5"] is not None else None
            decision["price_decision"]["profit"] = calculate_profit_engine(
                float(latest["Close"]), prev_high20_v, atr14_v, valuation, bb_upper_v, ma5_v,
                float(latest["Close"]), strategy_pref=strategy_pref
            )
    except Exception:
        decision = None

    # --- 持股價格即時分析（選填，不存檔，當下輸入當下算）---
    # 用 Exception 而非只抓 ValueError/TypeError，確保這個選填功能萬一
    # 出現任何未預期錯誤，也只會讓「持股分析」這張卡片顯示不出來，
    # 不會讓整支 /api/stock 回應失敗、拖累其他所有卡片一起當機
    position = None
    buy_price_arg = request.args.get("buy_price", "").strip()
    if buy_price_arg:
        try:
            buy_price = float(buy_price_arg)
            # V2.8.2：前台以「總股數」傳入，後台統一以股數為主資料；
            # 舊版 shares(張數) 仍保留相容，避免既有呼叫失效。
            share_count_arg = request.args.get("share_count", "").strip()
            legacy_shares_arg = request.args.get("shares", "").strip()
            if share_count_arg:
                share_count = max(0.0, float(share_count_arg))
            elif legacy_shares_arg:
                share_count = max(0.0, float(legacy_shares_arg)) * SHARES_PER_LOT
            else:
                share_count = None
            recent_n5 = min(5, len(df))
            recent_high5 = float(df["High"].iloc[-recent_n5:].max())
            position = analyze_position(
                buy_price, share_count, strategy_pref,
                float(latest["Close"]),
                float(latest["MA5"]) if latest["MA5"] is not None else None,
                float(latest["MA20"]) if latest["MA20"] is not None else None,
                float(latest["MA60"]) if latest["MA60"] is not None else None,
                recent_high5,
                float(latest["Volume"]) if latest["Volume"] is not None else None,
                float(latest["Vol_MA5"]) if latest["Vol_MA5"] is not None else None,
                strategy["short"], strategy["mid"], valuation,
                atr14=float(latest["ATR14"]) if latest["ATR14"] is not None else None,
                support=decision["_internal"]["support"],
                resistance=decision["_internal"]["resistance"],
                previous_low20=decision["_internal"]["previous_low20"],
                previous_high20=decision["_internal"]["previous_high20"],
                volume_analysis=decision.get("volume_analysis"),
                trend_score=decision.get("score", 50),
                no_trade_reasons=decision.get("no_trade_reasons"),
                kd_cross=kd_cross,
            )
            # --- V2.1：用引擎的動態停損/補倉/停利取代原本的粗略估算，並用決策優先權重新裁決最終動作 ---
            if decision is not None:
                atr14_p = decision["_internal"]["atr14"]
                prev_low5_p = decision["_internal"]["previous_low5"]
                risk_v2 = calculate_risk_engine(
                    buy_price, atr14_p,
                    float(latest["MA20"]) if latest["MA20"] is not None else None,
                    prev_low5_p, strategy_pref, float(latest["Close"]),
                )
                position["risk_v2"] = risk_v2
                position["add_zone"] = decision["price_decision"]["add"]
                position["profit_v2"] = decision["price_decision"]["profit"]
                position["confidence"] = decision["confidence"]
                if risk_v2:
                    position["stop_loss"] = risk_v2["stop"]  # 用ATR動態停損覆蓋原本的簡易停損
                final_action, final_label = final_decision(
                    decision["no_trade_reasons"], decision["price_decision"]["add"],
                    decision["score"], position_status=position["status"],
                    stop_hit=(risk_v2["hit"] if risk_v2 else False),
                    stop_warning=(risk_v2["warning_triggered"] if risk_v2 else False),
                )
                position["final_action"] = final_action
                position["final_label"] = final_label
        except Exception:
            position = None

    # --- V2.8.0 正式穩定決策融合層：作戰卡只吃這一份輸出 ---
    official_limits = {}
    try:
        v27 = build_v27_analysis(
            df, latest, prev, score_pct, decision, position, weekly_kd, revenue_yoy, valuation, meta, kd_cross
        )
        technical_core = build_technical_core_model(latest, decision, score_pct, kd_cross)
        three_core = build_three_core_model(fundamental_model, technical_core, chip_model, strategy_pref)
        v27 = apply_three_core_guard(v27, three_core)
        v27 = apply_v28_stability_gate(v27, three_core)
        # V2.8.1：臺灣市場制度硬規則高於模型；政策層沒有可驗證事件時維持中性。
        reference_price_rule = float(prev["Close"]) if prev is not None and prev["Close"] is not None else float(latest["Close"])
        # V2.9.3：漲跌停不得直接用歷史資料上一列收盤當作今天基準。
        # 優先向交易所 MIS 取得當日參考價(y)與官方漲/跌停(u/w)；失敗才回退歷史估算。
        official_limits = fetch_twse_realtime_limits(stock_id, meta)
        special_info = fetch_twse_special_status(stock_id, meta)
        opening_reference_rule = official_limits.get("reference") if official_limits.get("available") else None
        market_rules = build_taiwan_market_rule_engine(
            reference_price_rule, float(latest["Close"]), stock_id, meta=meta,
            special_status=special_info.get("status"),
            opening_reference=opening_reference_rule, official_limits=official_limits
        )
        market_rules["special_status_verified"] = special_info.get("verified")
        market_rules["special_status_source"] = special_info.get("source")
        market_rules["special_status_details"] = special_info.get("details") or []
        policy_env = build_policy_environment(meta, v27.get("market_regime"))
        v27 = apply_taiwan_market_rule_guard(v27, market_rules, policy_env)
        v27 = reconcile_v27_with_market_rules(v27, market_rules, official_limits)
    except Exception as e:
        technical_core = {"score": score_pct, "label": "資料不足"}
        three_core = None
        market_rules = None
        policy_env = None
        v27 = {
            "system_version": SYSTEM_VERSION,
            "ruleset_version": CORE_RULESET_VERSION,
            "model_version": MODEL_VERSION,
            "error": "V2.8決策融合暫時無法計算",
            "detail": str(e)[:160],
        }

    # --- V2.9.8 盤中量價時段引擎：資料失敗時不補分、不阻斷主分析 ---
    try:
        intraday_volume = analyze_intraday_volume(stock_id, meta)
        v27 = apply_intraday_volume_guard(v27, intraday_volume)
    except Exception as e:
        intraday_volume = {"available": False, "summary": "盤中量價分析暫時無法取得", "error": str(e)[:80]}

    if decision is not None and "_internal" in decision:
        del decision["_internal"]  # 內部欄位，不需要回傳給前端

    result = {
        "status": 200,
        "system_version": SYSTEM_VERSION,
        "ruleset_version": CORE_RULESET_VERSION,
        "release_stage": RELEASE_STAGE,
        "model_version": MODEL_VERSION,
        "symbol": stock_id,
        "name": stock_name,
        "industry": industry,
        "date": latest["Date"],
        "close": round(float(latest["Close"]), 2),
        "current_price": (round(float(official_limits.get("last")), 2) if official_limits and official_limits.get("last") is not None else None),
        "current_open": (round(float(official_limits.get("open")), 2) if official_limits and official_limits.get("open") is not None else None),
        "current_high": (round(float(official_limits.get("high")), 2) if official_limits and official_limits.get("high") is not None else None),
        "current_low": (round(float(official_limits.get("low")), 2) if official_limits and official_limits.get("low") is not None else None),
        "market_session": ((market_rules or {}).get("session") if market_rules else None),
        "prev_close": round(prev_close, 2) if prev_close is not None else None,
        "change": price_change,
        "change_pct": price_change_pct,
        "ma": {
            "MA5": round(float(latest["MA5"]), 2) if latest["MA5"] is not None else None,
            "MA10": round(float(latest["MA10"]), 2) if latest["MA10"] is not None else None,
            "MA20": round(float(latest["MA20"]), 2) if latest["MA20"] is not None else None,
            "MA60": round(float(latest["MA60"]), 2) if latest["MA60"] is not None else None,
        },
        "kd": {
            "K": round(float(latest["K"]), 2),
            "D": round(float(latest["D"]), 2),
            "cross": kd_cross,
        },
        "macd": {
            "DIF": round(float(latest["DIF"]), 2),
            "DEA": round(float(latest["DEA"]), 2),
            "Hist": round(float(latest["MACD_Hist"]), 2),
            "dir": macd_dir,
            "trend": macd_trend,
        },
        "bb": {
            "Upper": round(float(latest["BB_Upper"]), 2) if latest["BB_Upper"] is not None else None,
            "Middle": round(float(latest["BB_Middle"]), 2) if latest["BB_Middle"] is not None else None,
            "Lower": round(float(latest["BB_Lower"]), 2) if latest["BB_Lower"] is not None else None,
            "pos": bb_pos,
        },
        "vol": {
            "last": last_vol,
            "avg5": avg_vol5,
            "avg20": avg_vol20,
            "ratio": round(vol_ratio, 2),
            "ratio_basis": "20日均量",
            "price_change_pct": round(price_change_pct or 0, 2),
            "efficiency": decision.get("volume_price_efficiency") if decision else None,
            "status": decision.get("volume_status") if decision else "資料不足",
        },
        "recent": {
            "high": recent_high,
            "low": recent_low,
        },
        "trade_points": {
            "buy_low": round(float(buy_low), 2),
            "buy_high": round(float(buy_high), 2),
            "sell_low": round(float(sell_low), 2),
            "sell_high": round(float(sell_high), 2),
            "stop_loss": round(float(stop_loss), 2),
        },
        "score": score,
        "score_max": score_max,
        "score_pct": score_pct,
        "strategy": strategy,
        "weekly_kd": weekly_kd,
        "revenue_yoy": revenue_yoy,
        "revenue_data": (_revenue_raw_cache.get(stock_id, (0, []))[1] if stock_id in _revenue_raw_cache else []),
        "valuation": valuation,
        "fundamental_model": fundamental_model,
        "technical_core": technical_core,
        "chip_model": chip_model,
        "three_core": three_core,
        "market_rules": (v27.get("market_rules") if isinstance(v27, dict) else market_rules),
        "policy_environment": (v27.get("policy_environment") if isinstance(v27, dict) else policy_env),
        "intraday_volume": intraday_volume,
        "decision": decision,
        "position": position,
        "v27": v27,
    }
    return jsonify(result)


# ===========================================================================
# /api/news — Google News RSS
# ===========================================================================
@app.route("/api/news")
def get_news():
    q = request.args.get("q", "").strip()
    if not q:
        return jsonify({"status": 400, "msg": "缺少查詢參數 q", "data": []}), 400

    rss_url = (
        f"https://news.google.com/rss/search?q={q}&hl=zh-TW&gl=TW&ceid=TW:zh-Hant"
    )
    try:
        resp = requests.get(rss_url, timeout=10)
        resp.encoding = "utf-8"
        root = ET.fromstring(resp.text)
        items = root.findall(".//item")
        news_list = []
        for item in items[:5]:
            title = item.findtext("title", default="")
            # Google News 的 link 是編碼連結，直接點會 400
            # 改用 <source url="..."> 取得原始新聞網站連結
            source_elem = item.find("source")
            source = source_elem.text if source_elem is not None else ""
            source_url = source_elem.get("url", "") if source_elem is not None else ""
            # 如果有 source_url 就用它，否則 fallback 到 Google News 連結
            link = source_url if source_url else item.findtext("link", default="")

            # 日期格式轉換：RSS 原始格式 "Mon, 07 Sep 2026 01:41:50 GMT"
            # 轉成 "2026/09/07 01:41" 數字格式
            pub_date_raw = item.findtext("pubDate", default="")
            pub_date = pub_date_raw  # fallback 用原始格式
            if pub_date_raw:
                try:
                    from email.utils import parsedate_to_datetime
                    dt = parsedate_to_datetime(pub_date_raw)
                    pub_date = dt.strftime("%Y/%m/%d %H:%M")
                except Exception:
                    pass

            news_list.append(
                {
                    "title": title,
                    "link": link,
                    "pubDate": pub_date,
                    "source": source,
                }
            )
        return jsonify({"status": 200, "data": news_list})
    except Exception as e:
        return jsonify({"status": 500, "msg": f"抓取新聞失敗: {e}", "data": []}), 500


# ===========================================================================
# /api/us_market — 美股三大指數
# ===========================================================================
@app.route("/api/us_market")
def get_us_market():
    symbols = {
        "^DJI": "道瓊工業指數",
        "^GSPC": "S&P 500",
        "^IXIC": "那斯達克綜合指數",
    }
    results = []

    # V2.9.3：直接使用 Yahoo JSON API，避免載入 yfinance。
    for sym, name in symbols.items():
        try:
            url = f"https://query1.finance.yahoo.com/v8/finance/chart/{sym}?interval=1d&range=5d"
            r = requests.get(
                url,
                headers={"User-Agent": "Mozilla/5.0"},
                timeout=10,
            )
            j = r.json()
            chart = j.get("chart", {})
            result = chart.get("result", [None])[0]
            if not result:
                continue
            indicators = result.get("indicators", {})
            quote = indicators.get("quote", [{}])[0]
            closes = quote.get("close", [])
            closes = [c for c in closes if c is not None]
            if len(closes) >= 2:
                close = closes[-1]
                prev_close = closes[-2]
                chg = close - prev_close
                chg_pct = (chg / prev_close) * 100 if prev_close else 0
                results.append(
                    {
                        "symbol": sym,
                        "name": name,
                        "close": round(close, 2),
                        "change": round(chg, 2),
                        "change_pct": round(chg_pct, 2),
                    }
                )
        except Exception:
            continue

    if not results:
        return jsonify({"status": 500, "msg": "無法取得美股資料", "data": []}), 500
    return jsonify({"status": 200, "data": results})


# ===========================================================================
# 全域 cache（用於 /api/backtest，TTL 24 小時 — 回測資料不需要即時）
# ===========================================================================
_backtest_cache = {}  # {cache_key: (ts, result)} — key 依所選股票組合區分
_BACKTEST_TTL = 86400  # 24 小時


# ===========================================================================
# /api/backtest — 短線策略歷史回測（5支代表性電子股，近~2年）
# ===========================================================================
@app.route("/api/backtest")
def get_backtest():
    # 支援自訂股票（最多5支，逗號分隔，例如 ?stocks=2330,2603,3037）
    # 沒有帶 stocks 參數時，沿用預設的 5 支代表性電子股
    default_stocks = ["2330", "2317", "2454", "2308", "2382"]
    stocks_arg = request.args.get("stocks", "").strip()
    if stocks_arg:
        requested = [s.strip() for s in stocks_arg.split(",") if s.strip()]
        # 只接受純數字股票代號，避免不合法輸入；最多5支，避免一次打太多API
        target_stocks = [s for s in requested if s.isdigit()][:5]
        if not target_stocks:
            return jsonify({"status": 400, "msg": "股票代號格式錯誤，請輸入數字代號並用逗號分隔（最多5支）"}), 400
    else:
        target_stocks = default_stocks

    lookback_days = 500
    hold_days = 5
    cache_key = "v24|" + ",".join(sorted(target_stocks)) + f"|{lookback_days}|{hold_days}"
    now_ts = time.time()
    cached = _backtest_cache.get(cache_key)
    if cached and (now_ts - cached[0]) < _BACKTEST_TTL:
        return jsonify({"status": 200, "cached": True, **cached[1]})

    market_env, market_err = fetch_market_environment(lookback_days=lookback_days + 100)
    results = []
    for sid in target_stocks:
        try:
            r = backtest_short_strategy(sid, lookback_days=lookback_days, hold_days=hold_days, market_env=market_env)
        except Exception as e:
            r = {"stock_id": sid, "error": str(e)}
        results.append(r)

    overall = calculate_strategy_performance(results)
    # 回傳前移除內部完整訊號，避免 API 負載過大；績效統計已在後端完成。
    for _r in results:
        _r.pop("_all_signals", None)
    result = {
        "period_days": lookback_days,
        "hold_days": hold_days,
        "backtest_lots": 1,
        "market_environment": {
            "benchmark": "台灣加權指數",
            "data_id": "001 / TAIEX",
            "available": bool(market_env),
            "error": market_err,
            "regime_method": "MA20/MA60 + 5/20日報酬 + 20日量價環境",
            "no_future_data": True
        },
        "cost_rules": {
            "broker_fee_rate": BROKER_FEE_RATE,
            "sell_tax_rate": TRADING_TAX_RATE,
            "fee_note": "買進／賣出皆計手續費；僅賣出計證交稅；未計券商折讓",
        },
        "stocks": results,
        "overall": overall,
    }

    _backtest_cache[cache_key] = (now_ts, result)
    return jsonify({"status": 200, "cached": False, **result})


# ===========================================================================
# /api/sector_flow — 法人產業族群流向（含 cache）
# ===========================================================================
@app.route("/api/sector_flow")
def get_sector_flow():
    now_ts = time.time()

    # 檢查 cache
    if (
        _sector_flow_cache["data"] is not None
        and (now_ts - _sector_flow_cache["ts"]) < _SECTOR_FLOW_TTL
    ):
        return jsonify({"status": 200, "cached": True, **_sector_flow_cache["data"]})

    # --- Step 1: 取得 TaiwanStockInfo（股票代號 → 產業別）---
    industry_map = {}  # {stock_id: industry_category}
    try:
        data, err = finmind_get({"dataset": "TaiwanStockInfo"}, timeout=30)
        if err:
            return jsonify({"status": 500, "msg": err}), 500
        for row in data:
            sid = row.get("stock_id", "")
            cat = row.get("industry_category", "")
            if sid and cat:
                industry_map[sid] = cat
    except Exception as e:
        return jsonify({"status": 500, "msg": f"取得 TaiwanStockInfo 失敗: {e}"}), 500

    if not industry_map:
        return jsonify({"status": 500, "msg": "無法取得產業別資料"}), 500

    # --- Step 2: 取得最近交易日的法人買賣超（改用 TWSE 官方免費 T86，涵蓋全市場）---
    t86_rows, latest_date = fetch_twse_t86()
    if not t86_rows:
        return jsonify({"status": 500, "msg": "無法取得 TWSE 法人買賣超資料（近期無交易日資料或連線失敗）"}), 500

    def _num(v):
        try:
            return int(str(v).replace(",", "").strip() or 0)
        except Exception:
            return 0

    # 統計各產業的外資 + 投信合計淨買超（股，非張）
    sector_net = {}  # {industry: net_buy}
    for row in t86_rows:
        sid = (row.get("證券代號") or "").strip()
        cat = industry_map.get(sid, "其他")
        foreign_net = _num(row.get("外陸資買賣超股數(不含外資自營商)")) + _num(row.get("外資自營商買賣超股數"))
        trust_net = _num(row.get("投信買賣超股數"))
        net = round((foreign_net + trust_net) / 1000)  # 股 → 張
        sector_net[cat] = sector_net.get(cat, 0) + net

    # 排序
    sorted_sectors = sorted(sector_net.items(), key=lambda x: x[1], reverse=True)
    top5_buy = [
        {"industry": s[0], "net": s[1]} for s in sorted_sectors[:5] if s[1] > 0
    ]
    top5_sell = [
        {"industry": s[0], "net": s[1]} for s in sorted_sectors[-5:] if s[1] < 0
    ]
    # 賣超排序（從最負開始）
    top5_sell = sorted(top5_sell, key=lambda x: x["net"])

    result = {
        "date": latest_date,
        "top5_buy": top5_buy,
        "top5_sell": top5_sell,
        "all_sectors": [
            {"industry": s[0], "net": s[1]} for s in sorted_sectors
        ],
    }

    # 寫入 cache
    _sector_flow_cache["data"] = result
    _sector_flow_cache["ts"] = now_ts

    return jsonify({"status": 200, "cached": False, **result})


# ===========================================================================
# 全域 cache（用於 /api/top_institutional，TTL 1 小時）
# ===========================================================================
_top_inst_cache = {"data": None, "ts": 0}
_TOP_INST_TTL = 3600  # 秒


# ===========================================================================
# /api/top_institutional — 法人（三大法人合計）個股買超/賣超排行 TOP10
# ===========================================================================
@app.route("/api/top_institutional")
def get_top_institutional():
    now_ts = time.time()

    # 檢查 cache
    if (
        _top_inst_cache["data"] is not None
        and (now_ts - _top_inst_cache["ts"]) < _TOP_INST_TTL
    ):
        return jsonify({"status": 200, "cached": True, **_top_inst_cache["data"]})

    # --- 取得最近交易日全市場法人買賣超（TWSE 官方免費 T86，涵蓋全部上市股票）---
    t86_rows, latest_date = fetch_twse_t86()
    if not t86_rows:
        return jsonify({"status": 500, "msg": "無法取得 TWSE 法人買賣超資料（近期無交易日資料或連線失敗）"}), 500

    def _num(v):
        try:
            return int(str(v).replace(",", "").strip() or 0)
        except Exception:
            return 0

    stock_rows = []
    for row in t86_rows:
        sid = (row.get("證券代號") or "").strip()
        name = (row.get("證券名稱") or "").strip()
        if not sid:
            continue
        net = round(_num(row.get("三大法人買賣超股數")) / 1000)  # 股 → 張
        stock_rows.append({"stock_id": sid, "name": name, "net": net})

    if not stock_rows:
        return jsonify({"status": 500, "msg": "查無最新交易日的法人買賣超資料"}), 500

    sorted_stocks = sorted(stock_rows, key=lambda x: x["net"], reverse=True)

    top10_buy = [s for s in sorted_stocks[:10] if s["net"] > 0]
    top10_sell = [s for s in sorted(sorted_stocks, key=lambda x: x["net"])[:10] if s["net"] < 0]

    result = {
        "date": latest_date,
        "top10_buy": top10_buy,
        "top10_sell": top10_sell,
    }

    # 寫入 cache
    _top_inst_cache["data"] = result
    _top_inst_cache["ts"] = now_ts

    return jsonify({"status": 200, "cached": False, **result})


# ===========================================================================
# V2.9.0 AI 自主分析小助手 / 自適應學習治理引擎
# ---------------------------------------------------------------------------
# 設計原則：
# 1. 台股為主體，美股只做輔助，不可反客為主。
# 2. 台股硬規則、資料品質、風險否決永遠高於學習模型。
# 3. L0 前六個月只學習、記錄、回測、產生候選參數，不得自動改正式核心。
# 4. 六個月到期只產生能力審查／權限申請建議，不自動升級。
# 5. 地緣政治、戰爭、政策事件採「可信度→傳導路徑→產業→是否已反映」流程，
#    不把單一新聞直接變成買賣訊號。
# 6. 每個交易日 06:30（Asia/Taipei）可由排程觸發正式晨報。
# ===========================================================================

import sqlite3
import smtplib
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from zoneinfo import ZoneInfo

AI_DB_PATH = Path(os.environ.get("AI_ASSISTANT_DB", "ai_assistant.sqlite3"))
AI_REPORT_HOUR = int(os.environ.get("AI_REPORT_HOUR", "6"))
AI_REPORT_MINUTE = int(os.environ.get("AI_REPORT_MINUTE", "30"))
AI_MIN_REVIEW_CALENDAR_DAYS = int(os.environ.get("AI_MIN_REVIEW_CALENDAR_DAYS", "180"))
AI_MIN_REVIEW_TRADING_DAYS = int(os.environ.get("AI_MIN_REVIEW_TRADING_DAYS", "100"))
AI_MIN_VALIDATED_SAMPLES = int(os.environ.get("AI_MIN_VALIDATED_SAMPLES", "60"))
AI_SCHEDULER_TOKEN = os.environ.get("AI_SCHEDULER_TOKEN", "").strip()
REPORT_EMAIL = os.environ.get("REPORT_EMAIL", "").strip()
SMTP_HOST = os.environ.get("SMTP_HOST", "smtp.gmail.com").strip()
SMTP_PORT = int(os.environ.get("SMTP_PORT", "587"))
SMTP_USER = os.environ.get("SMTP_USER", "").strip()
SMTP_PASSWORD = os.environ.get("SMTP_PASSWORD", "").strip()
ENABLE_INTERNAL_SCHEDULER = os.environ.get("ENABLE_INTERNAL_SCHEDULER", "0").strip() == "1"

_AI_DB_LOCK = threading.Lock()
_AI_RUN_LOCK = threading.Lock()
_AI_TWSE_CAL_CACHE = {"year": None, "holidays": set(), "ts": 0.0}
_AI_NEWS_CACHE = {"data": None, "ts": 0.0}
_AI_NEWS_TTL = 1800


def _ai_db():
    conn = sqlite3.connect(str(AI_DB_PATH), timeout=20)
    conn.row_factory = sqlite3.Row
    return conn


def _ai_init_db():
    with _AI_DB_LOCK:
        conn = _ai_db()
        try:
            conn.executescript("""
            CREATE TABLE IF NOT EXISTS assistant_meta (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL,
                updated_at TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS assistant_daily_reports (
                report_date TEXT PRIMARY KEY,
                generated_at TEXT NOT NULL,
                market_data_date TEXT,
                market_close REAL,
                prediction_direction TEXT,
                prediction_confidence REAL,
                permission_level TEXT NOT NULL,
                report_json TEXT NOT NULL,
                emailed_at TEXT
            );
            CREATE TABLE IF NOT EXISTS assistant_predictions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                signal_date TEXT NOT NULL,
                target_date TEXT NOT NULL,
                scope TEXT NOT NULL,
                subject TEXT NOT NULL,
                direction TEXT NOT NULL,
                confidence REAL,
                factors_json TEXT,
                base_close REAL,
                outcome_date TEXT,
                outcome_close REAL,
                outcome_return REAL,
                correct INTEGER,
                settled_at TEXT,
                UNIQUE(signal_date, target_date, scope, subject)
            );
            CREATE TABLE IF NOT EXISTS assistant_candidate_models (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                version TEXT UNIQUE NOT NULL,
                created_at TEXT NOT NULL,
                status TEXT NOT NULL,
                parameters_json TEXT NOT NULL,
                metrics_json TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS assistant_permission_history (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                created_at TEXT NOT NULL,
                from_level TEXT NOT NULL,
                requested_level TEXT NOT NULL,
                status TEXT NOT NULL,
                evidence_json TEXT NOT NULL,
                note TEXT
            );
            """)
            conn.commit()
        finally:
            conn.close()
    _ai_meta_setdefault("start_date", datetime.now(ZoneInfo("Asia/Taipei")).date().isoformat())
    _ai_meta_setdefault("permission_level", "L0")
    _ai_meta_setdefault("schema_version", "1")


def _ai_meta_get(key, default=None):
    conn = _ai_db()
    try:
        row = conn.execute("SELECT value FROM assistant_meta WHERE key=?", (key,)).fetchone()
        return row[0] if row else default
    finally:
        conn.close()


def _ai_meta_set(key, value):
    now = datetime.now(ZoneInfo("Asia/Taipei")).isoformat(timespec="seconds")
    with _AI_DB_LOCK:
        conn = _ai_db()
        try:
            conn.execute(
                "INSERT INTO assistant_meta(key,value,updated_at) VALUES(?,?,?) "
                "ON CONFLICT(key) DO UPDATE SET value=excluded.value, updated_at=excluded.updated_at",
                (key, str(value), now),
            )
            conn.commit()
        finally:
            conn.close()


def _ai_meta_setdefault(key, value):
    if _ai_meta_get(key) is None:
        _ai_meta_set(key, value)


def _ai_fetch_twse_holidays(year):
    """從 TWSE 公開休市日程取得日期；失敗時只退回週末判斷，不假裝已驗證。"""
    now = time.time()
    if _AI_TWSE_CAL_CACHE["year"] == year and now - _AI_TWSE_CAL_CACHE["ts"] < 7 * 86400:
        return _AI_TWSE_CAL_CACHE["holidays"], True
    holidays = set()
    verified = False
    try:
        roc_year = year - 1911
        url = "https://www.twse.com.tw/rwd/zh/holidaySchedule/holidaySchedule"
        r = requests.get(url, params={"response": "json", "queryYear": str(roc_year)},
                         headers={"User-Agent": "Mozilla/5.0"}, timeout=12)
        j = r.json()
        for row in j.get("data", []) or []:
            if not row:
                continue
            raw = str(row[0]).strip().replace("/", "-")
            # 常見格式 1月1日 / 01-01 / 115/01/01，做容錯解析。
            candidates = []
            if "月" in raw and "日" in raw:
                try:
                    m = int(raw.split("月")[0].split()[-1])
                    d = int(raw.split("月")[1].split("日")[0])
                    candidates.append(f"{year:04d}-{m:02d}-{d:02d}")
                except Exception:
                    pass
            parts = [x for x in raw.replace("年", "-").replace("月", "-").replace("日", "").split("-") if x]
            try:
                if len(parts) >= 3:
                    yy = int(parts[-3]); mm = int(parts[-2]); dd = int(parts[-1])
                    if yy < 1911: yy += 1911
                    candidates.append(f"{yy:04d}-{mm:02d}-{dd:02d}")
                elif len(parts) == 2:
                    candidates.append(f"{year:04d}-{int(parts[0]):02d}-{int(parts[1]):02d}")
            except Exception:
                pass
            holidays.update(candidates)
        verified = bool(j.get("data") is not None)
    except Exception:
        verified = False
    _AI_TWSE_CAL_CACHE.update({"year": year, "holidays": holidays, "ts": now})
    return holidays, verified


def ai_is_trading_day(day=None):
    day = day or datetime.now(ZoneInfo("Asia/Taipei")).date()
    if day.weekday() >= 5:
        return False, "週末"
    holidays, verified = _ai_fetch_twse_holidays(day.year)
    if day.isoformat() in holidays:
        return False, "TWSE 休市日"
    return True, "TWSE 日曆已驗證" if verified else "平日推定（休市日程暫未驗證）"


def _ai_latest_market_snapshot():
    env, err = fetch_market_environment(lookback_days=120)
    if err or not env:
        return {"available": False, "error": err or "大盤資料不足"}
    d = sorted(env.keys())[-1]
    x = dict(env[d])
    x.update({"available": True, "date": d})
    # 統一名稱供日報使用
    score = float(x.get("score") or 50)
    x["bias"] = "偏多" if score >= 60 else "偏空" if score <= 40 else "震盪"
    return x


def _ai_yahoo_history(symbol, days=7):
    """AI 晨報專用輕量行情抓取。

    Render Free 記憶體有限，這裡刻意不載入 yfinance/Ticker 物件，
    直接使用 Yahoo chart JSON，避免晨報一次分析多個海外商品時造成 OOM。
    """
    try:
        url = f"https://query1.finance.yahoo.com/v8/finance/chart/{symbol}"
        r = requests.get(
            url,
            params={"interval": "1d", "range": "10d"},
            headers={"User-Agent": "Mozilla/5.0"},
            timeout=8,
        )
        r.raise_for_status()
        j = r.json(); rr = (j.get("chart", {}).get("result") or [None])[0]
        closes = (((rr or {}).get("indicators") or {}).get("quote") or [{}])[0].get("close", [])
        closes = [float(v) for v in closes if v is not None]
        if len(closes) >= 2:
            return closes[-1], closes[-2], None
    except Exception as e:
        return None, None, str(e)
    return None, None, "資料不足"


def _ai_overseas_readiness():
    now_tw = datetime.now(ZoneInfo("Asia/Taipei"))
    now_ny = now_tw.astimezone(ZoneInfo("America/New_York"))
    wd = now_ny.weekday()
    minute = now_ny.hour * 60 + now_ny.minute
    if wd >= 5:
        level, label = 3, "主要資料完整"
        note = "美國週末；以上一正常交易日收盤資料為主。"
    elif 9 * 60 + 30 <= minute < 16 * 60:
        level, label = 1, "資料暫估"
        note = "美股正常盤交易中，目前海外資料尚未完成。"
    elif 16 * 60 <= minute < 20 * 60:
        level, label = 3, "主要資料完整"
        note = "美股正常盤已收盤；盤後交易仍可能變動，作為最後微調。"
    else:
        level, label = 3, "主要資料完整"
        note = "美股最近正常盤收盤資料可作為台股輔助依據。"
    return {"level": level, "label": label, "note": note,
            "taipei_time": now_tw.isoformat(timespec="minutes"),
            "new_york_time": now_ny.isoformat(timespec="minutes")}


def ai_fetch_us_context():
    symbols = {
        "^GSPC": ("S&P 500", 0.12),
        "^IXIC": ("NASDAQ", 0.18),
        "^SOX": ("費城半導體", 0.25),
        "TSM": ("台積電 ADR", 0.22),
        "UMC": ("聯電 ADR", 0.05),
        "^VIX": ("VIX", -0.10),
        "^TNX": ("美國10年債殖利率", -0.04),
        "DX-Y.NYB": ("美元指數", -0.04),
    }
    rows, raw_score, weight_sum = [], 0.0, 0.0
    for sym, (name, weight) in symbols.items():
        close, prev, err = _ai_yahoo_history(sym)
        if close is None or prev in (None, 0):
            rows.append({"symbol": sym, "name": name, "available": False, "error": err})
            continue
        pct = (close - prev) / prev * 100
        # 避免單日極端值讓輔助因子蓋過台股主體。
        contribution = max(-3.0, min(3.0, pct)) * weight
        raw_score += contribution
        weight_sum += abs(weight)
        rows.append({"symbol": sym, "name": name, "available": True,
                     "close": round(close, 3), "change_pct": round(pct, 2),
                     "contribution": round(contribution, 3)})
    normalized = raw_score / max(0.35, weight_sum)
    if normalized >= 0.35:
        impact = "正向"
    elif normalized <= -0.35:
        impact = "負向"
    else:
        impact = "中性"
    readiness = _ai_overseas_readiness()
    completeness = round(sum(1 for r in rows if r.get("available")) / max(1, len(rows)) * 100)
    return {"impact": impact, "score": round(normalized, 3), "items": rows,
            "data_completeness": completeness, "readiness": readiness,
            "principle": "美股只做台股方向的支持／削弱／抵銷，不單獨產生台股買賣結論。"}


def _ai_google_news_rss(query, limit=8):
    try:
        url = "https://news.google.com/rss/search"
        r = requests.get(url, params={"q": query, "hl": "zh-TW", "gl": "TW", "ceid": "TW:zh-Hant"},
                         headers={"User-Agent": "Mozilla/5.0"}, timeout=12)
        root = ET.fromstring(r.content)
        out = []
        for item in root.findall(".//item")[:limit]:
            source = item.find("source")
            out.append({
                "title": (item.findtext("title") or "").strip(),
                "link": (item.findtext("link") or "").strip(),
                "published": (item.findtext("pubDate") or "").strip(),
                "source": (source.text or "").strip() if source is not None else "",
            })
        return out
    except Exception:
        return []


def ai_fetch_geo_policy_watch():
    now = time.time()
    if _AI_NEWS_CACHE["data"] is not None and now - _AI_NEWS_CACHE["ts"] < _AI_NEWS_TTL:
        return _AI_NEWS_CACHE["data"]
    queries = [
        "台灣 地緣政治 台海 軍演 戰爭 制裁 封鎖",
        "台灣 半導體 AI 出口管制 關稅 政策",
        "台灣 金融 經濟 利率 匯率 產業政策",
    ]
    items, seen = [], set()
    for q in queries:
        for x in _ai_google_news_rss(q, 7):
            key = x.get("title")
            if key and key not in seen:
                seen.add(key); items.append(x)
    neg_kw = {"戰爭": 12, "封鎖": 14, "攻擊": 12, "制裁": 8, "軍演": 7, "衝突": 9,
              "出口管制": 7, "關稅": 5, "禁令": 8, "斷鏈": 8, "危機": 6}
    pos_kw = {"停火": -10, "協議": -5, "豁免": -6, "開放": -4, "補助": -3, "投資": -2}
    risk = 20.0
    tagged = []
    for x in items[:20]:
        title = x.get("title", "")
        delta, hits = 0, []
        for k, v in {**neg_kw, **pos_kw}.items():
            if k in title:
                delta += v; hits.append(k)
        if hits:
            tagged.append({**x, "keywords": hits, "risk_delta": delta})
            risk += max(-5, min(12, delta)) * 0.35
    risk = max(0, min(100, risk))
    label = "高" if risk >= 65 else "偏高" if risk >= 45 else "正常"
    result = {
        "risk_score": round(risk, 1), "risk_level": label,
        "events": tagged[:10],
        "rule": "事件先做可信度與傳導路徑判斷；單一新聞不得直接轉成買賣訊號。",
        "verification": "新聞聚合僅供事件雷達；重大事件在影響正式決策前仍須以政府／交易所／公司正式公告交叉驗證。",
    }
    _AI_NEWS_CACHE.update({"data": result, "ts": now})
    return result


def _ai_twse_industry_map():
    """優先用 TWSE OpenAPI 取得上市公司產業別；失敗就回空，不浪費 FinMind 配額。"""
    industry_names = {
        "01":"水泥工業","02":"食品工業","03":"塑膠工業","04":"紡織纖維","05":"電機機械",
        "06":"電器電纜","08":"玻璃陶瓷","09":"造紙工業","10":"鋼鐵工業","11":"橡膠工業",
        "12":"汽車工業","14":"建材營造","15":"航運業","16":"觀光餐旅","17":"金融保險",
        "18":"貿易百貨","20":"其他業","21":"化學工業","22":"生技醫療","23":"油電燃氣",
        "24":"半導體業","25":"電腦及週邊設備業","26":"光電業","27":"通信網路業",
        "28":"電子零組件業","29":"電子通路業","30":"資訊服務業","31":"其他電子業",
        "32":"文化創意業","33":"農業科技業","34":"電子商務業","35":"綠能環保","36":"數位雲端",
        "37":"運動休閒","38":"居家生活"
    }
    try:
        r = requests.get("https://openapi.twse.com.tw/v1/opendata/t187ap03_L",
                         headers={"User-Agent": "Mozilla/5.0"}, timeout=15)
        data = r.json()
        out = {}
        for row in data if isinstance(data, list) else []:
            sid = str(row.get("公司代號") or row.get("公司代碼") or "").strip()
            ind = str(row.get("產業別") or "").strip().zfill(2)
            if sid:
                out[sid] = industry_names.get(ind, ind or "其他")
        return out
    except Exception:
        return {}


def ai_build_sector_snapshot():
    rows, d = fetch_twse_t86(max_lookback_days=7)
    if not rows:
        return {"available": False, "date": d, "strong": [], "weak": [], "note": "法人產業資料不足"}
    imap = _ai_twse_industry_map()
    sums, counts = {}, {}
    def _n(v):
        try: return int(str(v).replace(",", "").strip() or 0)
        except Exception: return 0
    for row in rows:
        sid = str(row.get("證券代號") or "").strip()
        industry = imap.get(sid, "未分類")
        net = _n(row.get("三大法人買賣超股數")) / 1000.0
        sums[industry] = sums.get(industry, 0.0) + net
        counts[industry] = counts.get(industry, 0) + 1
    ranked = sorted([{"industry": k, "net_lots": round(v), "stocks": counts.get(k, 0)}
                     for k, v in sums.items() if k != "未分類"], key=lambda x: x["net_lots"], reverse=True)
    return {"available": bool(ranked), "date": d, "strong": ranked[:5], "weak": list(reversed(ranked[-5:])),
            "principle": "產業資金輪動優先於單一個股訊號；個股須與所屬產業相對強弱交叉判斷。"}


def _ai_settle_previous_predictions(latest_market):
    if not latest_market.get("available") or latest_market.get("close") is None:
        return 0
    latest_date = latest_market.get("date")
    latest_close = float(latest_market.get("close"))
    conn = _ai_db()
    settled = 0
    try:
        rows = conn.execute(
            "SELECT * FROM assistant_predictions WHERE settled_at IS NULL AND scope='MARKET' AND target_date<=? ORDER BY signal_date",
            (latest_date,),
        ).fetchall()
        for r in rows:
            base = r["base_close"]
            if not base: continue
            ret = (latest_close - float(base)) / float(base) * 100
            actual = "UP" if ret > 0.25 else "DOWN" if ret < -0.25 else "FLAT"
            correct = 1 if actual == r["direction"] else 0
            conn.execute(
                "UPDATE assistant_predictions SET outcome_date=?,outcome_close=?,outcome_return=?,correct=?,settled_at=? WHERE id=?",
                (latest_date, latest_close, round(ret, 4), correct,
                 datetime.now(ZoneInfo("Asia/Taipei")).isoformat(timespec="seconds"), r["id"]),
            )
            settled += 1
        conn.commit()
    finally:
        conn.close()
    return settled


def _ai_learning_stats():
    conn = _ai_db()
    try:
        reports = conn.execute("SELECT COUNT(*) FROM assistant_daily_reports").fetchone()[0]
        row = conn.execute("SELECT COUNT(*) n, SUM(CASE WHEN correct=1 THEN 1 ELSE 0 END) ok, AVG(confidence) conf FROM assistant_predictions WHERE settled_at IS NOT NULL").fetchone()
        n = int(row[0] or 0); ok = int(row[1] or 0)
        accuracy = round(ok / n * 100, 1) if n else None
        return {"trading_reports": reports, "validated_samples": n, "correct_samples": ok,
                "direction_accuracy": accuracy, "avg_confidence": round(float(row[2]),1) if row[2] is not None else None}
    finally:
        conn.close()


def ai_capability_review():
    start = _ai_meta_get("start_date")
    level = _ai_meta_get("permission_level", "L0")
    today = datetime.now(ZoneInfo("Asia/Taipei")).date()
    try: start_d = datetime.fromisoformat(start).date()
    except Exception: start_d = today
    calendar_days = (today - start_d).days
    st = _ai_learning_stats()
    time_ok = calendar_days >= AI_MIN_REVIEW_CALENDAR_DAYS
    trading_ok = st["trading_reports"] >= AI_MIN_REVIEW_TRADING_DAYS
    sample_ok = st["validated_samples"] >= AI_MIN_VALIDATED_SAMPLES
    accuracy = st.get("direction_accuracy")
    evidence_ok = accuracy is not None and accuracy >= 52.0
    eligible = bool(time_ok and trading_ok and sample_ok and evidence_ok)
    suggested = "L1" if level == "L0" and eligible else level
    reasons = []
    if not time_ok: reasons.append(f"尚未滿 {AI_MIN_REVIEW_CALENDAR_DAYS} 個日曆日")
    if not trading_ok: reasons.append(f"有效交易日報不足 {AI_MIN_REVIEW_TRADING_DAYS} 日")
    if not sample_ok: reasons.append(f"已驗證樣本不足 {AI_MIN_VALIDATED_SAMPLES} 筆")
    if not evidence_ok: reasons.append("目前方向命中率尚未達最低證據門檻，或樣本仍不足")
    if eligible: reasons.append("達到第一次權限審查最低門檻；仍須人工同意才可升級")
    return {
        "current_level": level, "suggested_level": suggested, "eligible_for_review": eligible,
        "start_date": start, "calendar_days": calendar_days, "stats": st,
        "checks": {"time": time_ok, "trading_days": trading_ok, "samples": sample_ok, "evidence": evidence_ok},
        "reasons": reasons,
        "governance": "AI 只有申請權，沒有自行升級權。台股硬規則、風險上限、資料品質否決、禁止未來資料永久鎖定。",
    }


def _ai_market_prediction(market, us, geo):
    # 台股自身 70%，美股輔助最多 20%，地緣政治／政策風險最多 10%。
    market_score = float(market.get("score") or 50)
    tw_component = (market_score - 50) / 50 * 0.70
    us_component = max(-1, min(1, float(us.get("score") or 0))) * 0.20
    geo_risk = float(geo.get("risk_score") or 20)
    geo_component = -max(0, (geo_risk - 35) / 65) * 0.10
    combined = tw_component + us_component + geo_component
    direction = "UP" if combined >= 0.10 else "DOWN" if combined <= -0.10 else "FLAT"
    label = {"UP":"偏多", "DOWN":"偏空", "FLAT":"震盪"}[direction]
    completeness = 0
    completeness += 55 if market.get("available") else 0
    completeness += min(25, float(us.get("data_completeness") or 0) * 0.25)
    completeness += 20 if geo.get("events") is not None else 0
    confidence = max(35, min(85, 45 + abs(combined) * 45)) * (completeness / 100)
    return {"direction": direction, "label": label, "confidence": round(confidence, 1),
            "combined_score": round(combined, 3), "data_completeness": round(completeness, 1),
            "explain": "台股自身結構為主；美股僅做輔助；重大地緣政治／政策風險可下修信心或觸發風險降級。"}


def _ai_create_candidate_model(stats):
    """L0 只建立候選紀錄，不會套用到正式模型。"""
    if stats.get("validated_samples", 0) < 20:
        return None
    version = "CAND-" + datetime.now(ZoneInfo("Asia/Taipei")).strftime("%Y%m%d")
    params = {
        "tw_market_weight": 0.70,
        "us_assist_max_weight": 0.20,
        "geo_policy_max_weight": 0.10,
        "note": "候選參數只供驗證；L0 不得自動套用正式模型。",
    }
    metrics = {"direction_accuracy": stats.get("direction_accuracy"), "validated_samples": stats.get("validated_samples")}
    conn = _ai_db()
    try:
        conn.execute(
            "INSERT OR IGNORE INTO assistant_candidate_models(version,created_at,status,parameters_json,metrics_json) VALUES(?,?,?,?,?)",
            (version, datetime.now(ZoneInfo("Asia/Taipei")).isoformat(timespec="seconds"), "CANDIDATE_ONLY",
             json.dumps(params, ensure_ascii=False), json.dumps(metrics, ensure_ascii=False)),
        )
        conn.commit()
    finally:
        conn.close()
    return {"version": version, "status": "CANDIDATE_ONLY", "parameters": params, "metrics": metrics}


def _ai_opportunity_module(level):
    if level == "L0":
        return {"enabled": False, "mode": "LOCKED", "message": "L0 學習觀察期不提供主動個股推薦。"}
    if level == "L1":
        return {"enabled": True, "mode": "WATCHLIST_ONLY", "message": "僅允許產生『值得關注』候選，不提供直接買進建議。"}
    if level == "L2":
        return {"enabled": True, "mode": "ENTRY_CONSIDERATION", "message": "通過治理門檻後可產生『可考慮進場／等待』，並強制附理由、失效條件與風險。"}
    return {"enabled": True, "mode": "ADVANCED", "message": "高度自適應候選發掘；硬規則與風險否決仍不可繞過。"}


def ai_build_daily_report(report_day=None, persist=True):
    _ai_init_db()
    now_tw = datetime.now(ZoneInfo("Asia/Taipei"))
    report_day = report_day or now_tw.date()
    is_td, cal_note = ai_is_trading_day(report_day)
    level = _ai_meta_get("permission_level", "L0")
    market = _ai_latest_market_snapshot()
    settled = _ai_settle_previous_predictions(market)
    gc.collect()
    us = ai_fetch_us_context()
    gc.collect()
    geo = ai_fetch_geo_policy_watch()
    gc.collect()
    sector = ai_build_sector_snapshot()
    gc.collect()
    pred = _ai_market_prediction(market, us, geo)
    stats = _ai_learning_stats()
    review = ai_capability_review()
    candidate = _ai_create_candidate_model(stats)

    strong_names = [x.get("industry") for x in sector.get("strong", [])[:3]]
    weak_names = [x.get("industry") for x in sector.get("weak", [])[:3]]
    risk_note = "地緣政治／政策風險正常"
    if geo.get("risk_level") in ("偏高", "高"):
        risk_note = f"地緣政治／政策風險{geo.get('risk_level')}，正式決策須提高風險門檻"

    report = {
        "schema_version": 1,
        "report_type": "AI自主分析小助手_每日台股市場觀察",
        "report_date": report_day.isoformat(),
        "generated_at": now_tw.isoformat(timespec="seconds"),
        "is_trading_day": is_td,
        "calendar_status": cal_note,
        "scope": {"primary": "台股", "secondary": "美股輔助"},
        "permission_level": level,
        "summary": {
            "taiwan_market": pred.get("label"),
            "confidence": pred.get("confidence"),
            "strong_industries": strong_names,
            "weak_industries": weak_names,
            "us_impact": us.get("impact"),
            "overseas_data": (us.get("readiness") or {}).get("label"),
            "geo_policy_risk": geo.get("risk_level"),
            "main_risk": risk_note,
            "assistant_note": "L0 只觀察與學習；單日日報不得直接修改正式模型。" if level == "L0" else "所有調整仍受模型治理與硬規則約束。",
        },
        # 先固定「規則層資料格式」，前台未來再用頁籤呈現；不把版面綁死在後端。
        "pages": {
            "market": {"title": "大盤", "market": market, "prediction": pred},
            "sector": {"title": "產業", **sector},
            "chip": {"title": "籌碼", "institutional_sector_flow": sector,
                     "rule": "籌碼只能與價格、產業與基本面交叉驗證，不以單日法人買賣超直接下結論。"},
            "technical": {"title": "技術面", "market_regime": market.get("regime"),
                          "ret5": market.get("ret5"), "ret20": market.get("ret20"),
                          "rule": "技術訊號需通過市場環境、資料品質與風險否決。"},
            "fundamental": {"title": "基本／估值", "rule": "營收、獲利、現金流、財務安全、估值與預期差共同判斷；股價低不等於便宜。"},
            "events": {"title": "事件／政策／地緣政治", **geo},
            "us": {"title": "美股輔助", **us},
            "learning": {"title": "AI 學習", "stats": stats, "settled_today": settled,
                         "capability_review": review, "candidate_model": candidate,
                         "opportunity_module": _ai_opportunity_module(level)},
        },
    }

    if persist and is_td:
        report_date = report_day.isoformat()
        market_date = market.get("date") if market.get("available") else None
        market_close = market.get("close") if market.get("available") else None
        with _AI_DB_LOCK:
            conn = _ai_db()
            try:
                conn.execute(
                    "INSERT INTO assistant_daily_reports(report_date,generated_at,market_data_date,market_close,prediction_direction,prediction_confidence,permission_level,report_json) "
                    "VALUES(?,?,?,?,?,?,?,?) ON CONFLICT(report_date) DO UPDATE SET generated_at=excluded.generated_at,market_data_date=excluded.market_data_date,market_close=excluded.market_close,prediction_direction=excluded.prediction_direction,prediction_confidence=excluded.prediction_confidence,permission_level=excluded.permission_level,report_json=excluded.report_json",
                    (report_date, report["generated_at"], market_date, market_close, pred["direction"], pred["confidence"], level, json.dumps(report, ensure_ascii=False)),
                )
                if market_close:
                    conn.execute(
                        "INSERT OR IGNORE INTO assistant_predictions(signal_date,target_date,scope,subject,direction,confidence,factors_json,base_close) VALUES(?,?,?,?,?,?,?,?)",
                        (report_date, report_date, "MARKET", "TAIEX", pred["direction"], pred["confidence"],
                         json.dumps({"market": market, "us": {"impact": us.get("impact"), "score": us.get("score")}, "geo": {"risk_score": geo.get("risk_score")}}, ensure_ascii=False),
                         market_close),
                    )
                conn.commit()
            finally:
                conn.close()
    return report


def ai_get_latest_report():
    _ai_init_db()
    conn = _ai_db()
    try:
        row = conn.execute("SELECT report_json, emailed_at FROM assistant_daily_reports ORDER BY report_date DESC LIMIT 1").fetchone()
        if not row: return None
        obj = json.loads(row["report_json"])
        obj["emailed_at"] = row["emailed_at"]
        return obj
    finally:
        conn.close()


def ai_report_html(report):
    s = report.get("summary", {})
    p = report.get("pages", {})
    def esc(v):
        import html
        return html.escape(str(v if v is not None else "—"))
    strong = "、".join(s.get("strong_industries") or []) or "資料整理中"
    weak = "、".join(s.get("weak_industries") or []) or "資料整理中"
    try:
        _strength_num = float(s.get("confidence"))
        strength_label = "高" if _strength_num >= 70 else ("中等" if _strength_num >= 50 else "低")
    except Exception:
        strength_label = "資料不足"
    events = (p.get("events") or {}).get("events") or []
    ev_html = "".join(f"<li>{esc(x.get('title'))} <small>({esc(x.get('source'))})</small></li>" for x in events[:6]) or "<li>目前無高優先事件</li>"
    return f"""<!doctype html><html><body style='font-family:-apple-system,BlinkMacSystemFont,Segoe UI,sans-serif;line-height:1.6;color:#222'>
    <h2>AI 小助手｜{esc(report.get('report_date'))} 台股晨報</h2>
    <table style='border-collapse:collapse;width:100%;max-width:720px'>
      <tr><td><b>台股整體</b></td><td>{esc(s.get('taiwan_market'))}</td></tr>
      <tr><td><b>判斷強度</b></td><td>{esc(strength_label)}</td></tr>
      <tr><td><b>強勢產業</b></td><td>{esc(strong)}</td></tr>
      <tr><td><b>弱勢產業</b></td><td>{esc(weak)}</td></tr>
      <tr><td><b>美股影響</b></td><td>{esc(s.get('us_impact'))}｜{esc(s.get('overseas_data'))}</td></tr>
      <tr><td><b>地緣政治／政策風險</b></td><td>{esc(s.get('geo_policy_risk'))}</td></tr>
      <tr><td><b>主要風險</b></td><td>{esc(s.get('main_risk'))}</td></tr>
      <tr><td><b>AI 權限</b></td><td>{esc(report.get('permission_level'))}</td></tr>
    </table>
    <h3>今日重要事件雷達</h3><ul>{ev_html}</ul>
    <p style='color:#666;font-size:13px'>台股為主體，美股僅做輔助。L0 期間報告只用於觀察、學習與驗證，不會自動修改正式核心交易規則。</p>
    </body></html>"""


def ai_send_report_email(report):
    if not REPORT_EMAIL:
        return {"sent": False, "reason": "未設定 REPORT_EMAIL"}
    if not SMTP_USER or not SMTP_PASSWORD:
        return {"sent": False, "reason": "未設定 SMTP_USER / SMTP_PASSWORD（Gmail 建議使用應用程式密碼）"}
    subject = f"台股 AI 小助手晨報｜{report.get('report_date')}｜{(report.get('summary') or {}).get('taiwan_market','')}"
    msg = MIMEMultipart("alternative")
    msg["Subject"] = subject; msg["From"] = SMTP_USER; msg["To"] = REPORT_EMAIL
    msg.attach(MIMEText("請使用支援 HTML 的郵件程式閱讀台股 AI 小助手晨報。", "plain", "utf-8"))
    msg.attach(MIMEText(ai_report_html(report), "html", "utf-8"))
    try:
        with smtplib.SMTP(SMTP_HOST, SMTP_PORT, timeout=20) as server:
            server.starttls(); server.login(SMTP_USER, SMTP_PASSWORD); server.sendmail(SMTP_USER, [REPORT_EMAIL], msg.as_string())
        with _AI_DB_LOCK:
            conn = _ai_db()
            try:
                conn.execute("UPDATE assistant_daily_reports SET emailed_at=? WHERE report_date=?",
                             (datetime.now(ZoneInfo("Asia/Taipei")).isoformat(timespec="seconds"), report.get("report_date")))
                conn.commit()
            finally: conn.close()
        return {"sent": True, "to": REPORT_EMAIL}
    except Exception as e:
        return {"sent": False, "reason": str(e)}


def ai_run_daily(force=False, send_email=True):
    with _AI_RUN_LOCK:
        now = datetime.now(ZoneInfo("Asia/Taipei"))
        is_td, note = ai_is_trading_day(now.date())
        if not is_td and not force:
            return {"ok": True, "skipped": True, "reason": note}
        report = ai_build_daily_report(now.date(), persist=True)
        mail = ai_send_report_email(report) if send_email else {"sent": False, "reason": "send_email=False"}
        review = ai_capability_review()
        return {"ok": True, "skipped": False, "report": report, "email": mail, "capability_review": review}


@app.route("/api/assistant/status")
def api_assistant_status():
    _ai_init_db()
    return jsonify({"status": 200, "version": SYSTEM_VERSION, "ruleset_version": CORE_RULESET_VERSION, "model_version": MODEL_VERSION,
                    "permission_level": _ai_meta_get("permission_level", "L0"),
                    "start_date": _ai_meta_get("start_date"),
                    "schedule": f"台灣交易日 {AI_REPORT_HOUR:02d}:{AI_REPORT_MINUTE:02d}",
                    "email_configured": bool(REPORT_EMAIL and SMTP_USER and SMTP_PASSWORD),
                    "learning": _ai_learning_stats(), "capability_review": ai_capability_review(),
                    "opportunity_module": _ai_opportunity_module(_ai_meta_get("permission_level", "L0"))})


@app.route("/api/assistant/report")
def api_assistant_report():
    """輕量唯讀端點：只讀已存在晨報，不在網頁請求中臨時計算完整晨報。

    Render Free 記憶體有限；若尚無晨報，前端顯示「尚未產生」，
    完整晨報只能由獨立排程流程建立。
    """
    latest = ai_get_latest_report()
    if latest is None:
        return jsonify({
            "status": 200,
            "data": None,
            "report_ready": False,
            "msg": "尚未產生晨報"
        })
    return jsonify({"status": 200, "data": latest, "report_ready": True})


@app.route("/api/assistant/review")
def api_assistant_review():
    return jsonify({"status": 200, "data": ai_capability_review()})


@app.route("/api/assistant/test_email", methods=["POST"])
def api_assistant_test_email():
    """輕量 SMTP 測試：只驗證寄信，不建立晨報、不抓市場資料。"""
    supplied = request.headers.get("X-Assistant-Token", "") or request.args.get("token", "")
    if AI_SCHEDULER_TOKEN:
        if supplied != AI_SCHEDULER_TOKEN:
            return jsonify({"status": 403, "msg": "排程驗證失敗"}), 403
    elif request.remote_addr not in ("127.0.0.1", "::1"):
        return jsonify({"status": 403, "msg": "雲端使用前請先設定 AI_SCHEDULER_TOKEN"}), 403

    if not REPORT_EMAIL:
        return jsonify({"status": 400, "sent": False, "msg": "未設定 REPORT_EMAIL"}), 400
    if not SMTP_USER or not SMTP_PASSWORD:
        return jsonify({"status": 400, "sent": False, "msg": "未設定 SMTP_USER / SMTP_PASSWORD"}), 400

    now = datetime.now(ZoneInfo("Asia/Taipei"))
    subject = f"台股分析系統｜測試信｜{now.strftime('%Y-%m-%d %H:%M:%S')}"
    body = (
        "這是一封 SMTP 連線測試信。\n\n"
        "若你收到這封信，代表 Render → Gmail SMTP 的登入與寄送流程正常。\n"
        "這次測試沒有執行 AI 晨報、沒有抓市場資料，也不會啟動大型模型運算。\n"
        f"系統版本：{SYSTEM_VERSION}\n"
        f"規則版本：{CORE_RULESET_VERSION}\n"
        f"測試時間：{now.strftime('%Y-%m-%d %H:%M:%S')}（台灣時間）\n"
    )
    msg = MIMEMultipart("alternative")
    msg["Subject"] = subject
    msg["From"] = SMTP_USER
    msg["To"] = REPORT_EMAIL
    msg.attach(MIMEText(body, "plain", "utf-8"))

    try:
        with smtplib.SMTP(SMTP_HOST, SMTP_PORT, timeout=20) as server:
            server.starttls()
            server.login(SMTP_USER, SMTP_PASSWORD)
            server.sendmail(SMTP_USER, [REPORT_EMAIL], msg.as_string())
        return jsonify({
            "status": 200,
            "sent": True,
            "msg": "測試信已送出",
            "to": REPORT_EMAIL,
            "tested_at": now.isoformat(timespec="seconds"),
            "version": SYSTEM_VERSION,
        })
    except Exception as e:
        return jsonify({
            "status": 500,
            "sent": False,
            "msg": "測試信寄送失敗",
            "reason": str(e),
        }), 500


@app.route("/api/assistant/run_daily", methods=["POST"])
def api_assistant_run_daily():
    # 對外排程端點必須設定 token；本機未設定 token 時只允許 loopback。
    supplied = request.headers.get("X-Assistant-Token", "") or request.args.get("token", "")
    if AI_SCHEDULER_TOKEN:
        if supplied != AI_SCHEDULER_TOKEN:
            return jsonify({"status": 403, "msg": "排程驗證失敗"}), 403
    elif request.remote_addr not in ("127.0.0.1", "::1"):
        return jsonify({"status": 403, "msg": "雲端使用前請先設定 AI_SCHEDULER_TOKEN"}), 403
    result = ai_run_daily(force=bool(request.args.get("force") == "1"), send_email=True)
    # 排程端點只回傳必要資訊，避免把整份大型 report JSON 再序列化一次，
    # 降低 Render Free 記憶體尖峰。完整報告可由 /api/assistant/report 讀取。
    report = result.pop("report", None) if isinstance(result, dict) else None
    compact = {"status": 200, **result}
    if isinstance(report, dict):
        compact["report_summary"] = {
            "report_date": report.get("report_date"),
            "permission_level": report.get("permission_level"),
            "summary": report.get("summary"),
        }
    gc.collect()
    return jsonify(compact)


def _ai_internal_scheduler_loop():
    """可選內建排程；雲端休眠型服務仍建議用平台 Cron 於 06:30 呼叫 run_daily。"""
    last_key = None
    while True:
        try:
            now = datetime.now(ZoneInfo("Asia/Taipei"))
            key = now.date().isoformat()
            if now.hour == AI_REPORT_HOUR and now.minute >= AI_REPORT_MINUTE and key != last_key:
                is_td, _ = ai_is_trading_day(now.date())
                if is_td:
                    ai_run_daily(force=False, send_email=True)
                last_key = key
        except Exception as e:
            print("[AI Assistant Scheduler]", e)
        time.sleep(30)


def _ai_maybe_start_scheduler():
    if ENABLE_INTERNAL_SCHEDULER:
        t = threading.Thread(target=_ai_internal_scheduler_loop, name="ai-assistant-scheduler", daemon=True)
        t.start()

# V2.9.3：資料庫採首次使用時初始化，避免 Gunicorn import 階段做磁碟 I/O。
_ai_maybe_start_scheduler()


# ===========================================================================
# Main
# ===========================================================================
if __name__ == "__main__":
    import os
    # 本機開發：預設 127.0.0.1:5000
    # 雲端部署（Render/Railway 等）：平台會用 PORT 環境變數指定 port，
    # 並需綁定 0.0.0.0 才能對外服務
    port = int(os.environ.get("PORT", 5000))
    host = "0.0.0.0" if os.environ.get("PORT") else "127.0.0.1"
    print(f"台股個股健診升級版 已啟動，請在瀏覽器打開 http://{host}:{port}")
    app.run(host=host, port=port, debug=False)
