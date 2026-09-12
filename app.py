# -*- coding: utf-8 -*-
"""
台股個股健診升級版 — Flask 後端
================================
安裝說明：
    pip install flask requests yfinance pandas

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
import pandas as pd
import math
import json
import hashlib
from pathlib import Path

app = Flask(__name__)
FINMIND_URL = "https://api.finmindtrade.com/api/v4/data"

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

def _cache_key(params):
    payload = json.dumps(params, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()

def _cache_file(params):
    return CACHE_DIR / f"finmind_{_cache_key(params)}.json"

def _read_disk_cache(params):
    path = _cache_file(params)
    try:
        if not path.exists() or time.time() - path.stat().st_mtime > FINMIND_CACHE_TTL:
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

def _load_quota_log():
    try:
        with _QUOTA_FILE.open("r", encoding="utf-8") as f:
            obj = json.load(f)
        calls = [float(x) for x in obj.get("calls", []) if time.time() - float(x) < QUOTA_WINDOW_SECONDS]
        return calls
    except Exception:
        return []

def _save_quota_log(calls):
    try:
        with _QUOTA_FILE.open("w", encoding="utf-8") as f:
            json.dump({"calls": calls}, f)
    except Exception:
        pass

def finmind_quota_status():
    calls = _load_quota_log()
    limit = QUOTA_LIMIT_TOKEN if FINMIND_TOKEN else QUOTA_LIMIT_ANON
    return {
        "window_seconds": QUOTA_WINDOW_SECONDS,
        "used": len(calls),
        "safe_limit": limit,
        "remaining_safe": max(0, limit - len(calls)),
        "has_token": bool(FINMIND_TOKEN),
    }

def _quota_allows_request():
    calls = _load_quota_log()
    limit = QUOTA_LIMIT_TOKEN if FINMIND_TOKEN else QUOTA_LIMIT_ANON
    if len(calls) >= limit:
        return False, len(calls), limit
    calls.append(time.time())
    _save_quota_log(calls)
    return True, len(calls), limit

# ===========================================================================
# 交易成本設定（依使用者目前規格）
# ===========================================================================
# 證券交易稅：賣出市值 × 0.3%
# 券商手續費：買進／賣出市值 × 0.1425%（未計券商折讓）
# 台股 1 張 = 1,000 股；金額採無條件捨去到元。
TRADING_TAX_RATE = 0.003
BROKER_FEE_RATE = 0.001425
SHARES_PER_LOT = 1000


def calculate_trade_costs(price, lots, side):
    """計算單筆台股交易成本。side: buy / sell。"""
    if price is None or lots is None or float(lots) <= 0:
        return {"market_value": None, "fee": 0, "tax": 0, "total_cost": 0}
    market_value = math.floor(float(price) * float(lots) * SHARES_PER_LOT)
    fee = math.floor(market_value * BROKER_FEE_RATE)
    tax = math.floor(market_value * TRADING_TAX_RATE) if side == "sell" else 0
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
    V2.4 統一 FinMind 請求入口：
    1) 先讀磁碟快取；2) 只有 cache miss 才消耗 API 配額；
    3) 滾動 60 分鐘達安全上限後自動停止新增請求；
    4) 成功資料落地，之後回測不再重複下載。
    回傳 (raw_data_list, error_msg or None)。
    """
    cached = _read_disk_cache(params)
    if cached is not None:
        return cached, None

    allowed, used, limit = _quota_allows_request()
    if not allowed:
        return [], (f"FinMind 配額保護已啟動：近 60 分鐘已使用 {used}/{limit} 次安全額度。"
                    "已停止新增 API 請求；已有本地快取仍可正常回測。")

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
            return [], f"FinMind API 配額已用盡（{msg}）；系統已停止重試，請稍後再試或設定 FINMIND_TOKEN"
        if status == 403:
            return [], f"FinMind API 暫時限制存取（{msg}），系統已停止重試"
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
        # FinMind 若以 001 表示加權指數，退回 001
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
    return {
        "stock_id": stock_id,
        "signal_count": len(signals),
        "win_rate": round(wins_net / len(signals) * 100, 1),
        "gross_win_rate": round(wins_gross / len(signals) * 100, 1),
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


def analyze_position(buy_price, shares, strategy_pref, close, ma5, ma20, ma60,
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
    net_costs = calculate_net_position_pnl(buy_price, close, shares) if close is not None and shares else None
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
                         pullback_support, vol_ok, inst_bullish, fund_ok):
    """買入訊號分數制，0~100。回傳 (score, reasons)"""
    score = 0
    reasons = []
    if ma20 is not None and ma60 is not None and ma20 > ma60:
        score += 15; reasons.append("MA20>MA60（多頭排列）")
    if ma20 is not None and close is not None and close > ma20:
        score += 10; reasons.append("站上月線(20MA)")
    if ma5 is not None and ma20 is not None and ma5 > ma20:
        score += 10; reasons.append("5MA>20MA")
    if kd_cross == "黃金交叉":
        score += 10; reasons.append("KD黃金交叉")
    if k is not None and k < 80:
        score += 5
    if macd_improving:
        score += 10; reasons.append("MACD轉強")
    if pullback_support:
        score += 15; reasons.append("股價回踩支撐")
    if vol_ok:
        score += 10; reasons.append("量能正常")
    if inst_bullish:
        score += 10; reasons.append("法人偏多")
    if fund_ok:
        score += 5; reasons.append("基本面合理")
    return score, reasons


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
    if ma20 is not None:
        candidates.append(ma20 - atr14 * 0.3)
    if previous_low_ref is not None:
        candidates.append(previous_low_ref - atr14 * 0.2)
    stop_price = round(max(candidates), 2)  # 取較保守（較高）的防守價，risk-first
    warning_price = round(stop_price * 1.01, 2)
    warning_triggered = close is not None and close <= warning_price
    return {
        "stop": stop_price,
        "warning": warning_price,
        "warning_triggered": bool(warning_triggered),
        "hit": (close is not None and close <= stop_price),
    }


def calculate_profit_engine(base_price, previous_high20, atr14, valuation, bb_upper, ma5, close_max_since_entry):
    """三級停利：第一停利／第二停利／移動停利"""
    candidates_t1 = []
    if previous_high20 is not None:
        candidates_t1.append(previous_high20)
    if bb_upper is not None:
        candidates_t1.append(bb_upper)
    target1 = round(min(candidates_t1), 2) if candidates_t1 else None

    candidates_t2 = []
    if previous_high20 is not None and atr14 is not None:
        candidates_t2.append(previous_high20 + atr14)
    if valuation and not valuation.get("_error") and valuation.get("target_price"):
        candidates_t2.append(valuation["target_price"])
    target2 = round(max(candidates_t2), 2) if candidates_t2 else None
    if target1 is not None and target2 is not None and target2 < target1:
        target2 = round(target1 * 1.05, 2)  # 確保第二停利 >= 第一停利

    trailing = None
    if close_max_since_entry is not None:
        trail_pct = round(close_max_since_entry * 0.97, 2)
        trailing = max(trail_pct, ma5) if ma5 is not None else trail_pct
        trailing = round(trailing, 2)

    return {"target1": target1, "target2": target2, "trailing": trailing}



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
    """
    簡化版信心度（依最新規格：技術趨勢／量價／價格位置／籌碼／風險，不做完整6大類權重）。
    0~100，越高代表各面向訊號越一致。
    """
    score = 0
    score += min(buy_score, 60) / 60 * 40  # 技術趨勢+價格位置（用買入分數當代理，佔40%）
    score += 20 if vol_ok else 5           # 量價 20%
    score += 20 if trend_bullish else 5    # 趨勢 20%
    score += 15 if inst_bullish else 8     # 籌碼 15%（無資料時給中性分）
    score += 5 if not no_trade_triggered else 0  # 風險 5%
    score = round(min(100, max(0, score)), 1)
    if score >= 80:
        level = "高"
    elif score >= 65:
        level = "中高"
    elif score >= 50:
        level = "中"
    else:
        level = "低"
    return {"score": score, "level": level}


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
    profit = calculate_profit_engine(close, previous_high20, atr14, None, bb_upper, ma5, close)

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

    # --- Step 1: 取得股票資訊（名稱、產業）---
    stock_name = ""
    industry = ""
    try:
        info_data, _err = finmind_get({"dataset": "TaiwanStockInfo", "data_id": stock_id}, timeout=15)
        if info_data:
            stock_name = info_data[0].get("stock_name", "")
            industry = info_data[0].get("industry_category", "")
    except Exception:
        pass

    # --- Step 2: 從 FinMind 抓股價（拉長區間以利週KD計算）---
    end_date = datetime.now().strftime("%Y-%m-%d")
    start_date = (datetime.now() - timedelta(days=400)).strftime("%Y-%m-%d")
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
                float(latest["Close"]), prev_high20_v, atr14_v, valuation, bb_upper_v, ma5_v, float(latest["Close"])
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
            shares_arg = request.args.get("shares", "").strip()
            shares = float(shares_arg) if shares_arg else None
            recent_n5 = min(5, len(df))
            recent_high5 = float(df["High"].iloc[-recent_n5:].max())
            position = analyze_position(
                buy_price, shares, strategy_pref,
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

    if decision is not None and "_internal" in decision:
        del decision["_internal"]  # 內部欄位，不需要回傳給前端

    result = {
        "status": 200,
        "symbol": stock_id,
        "name": stock_name,
        "industry": industry,
        "date": latest["Date"],
        "close": round(float(latest["Close"]), 2),
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
        "valuation": valuation,
        "decision": decision,
        "position": position,
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

    # --- 優先使用 yfinance ---
    try:
        import yfinance as yf  # type: ignore

        for sym, name in symbols.items():
            try:
                tk = yf.Ticker(sym)
                hist = tk.history(period="5d")
                if hist is not None and len(hist) >= 2:
                    close = float(hist["Close"].iloc[-1])
                    prev_close = float(hist["Close"].iloc[-2])
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
                pass  # 個別 symbol 失敗不中斷

        if len(results) == len(symbols):
            return jsonify({"status": 200, "data": results})
    except ImportError:
        pass  # yfinance 未安裝，改用 Yahoo JSON API

    # --- fallback: Yahoo Finance JSON API ---
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
