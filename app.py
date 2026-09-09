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

app = Flask(__name__)
FINMIND_URL = "https://api.finmindtrade.com/api/v4/data"

# 若在 Render 的 Environment Variables 裡設定 FINMIND_TOKEN，
# 就會帶上 Authorization header，使用個人配額而非匿名共用配額，
# 可大幅降低「查無資料」其實是配額用盡／IP 被暫時限制的機率。
FINMIND_TOKEN = os.environ.get("FINMIND_TOKEN", "").strip()


def finmind_get(params, timeout=20):
    """
    統一的 FinMind 請求入口。
    回傳 (raw_data_list, error_msg or None)。
    - 若有 FINMIND_TOKEN，自動帶 Authorization header（提升配額上限）
    - 若 FinMind 回傳非 200（如 402 配額用盡、403 IP 暫時限制），
      不再誤判為「查無資料」，而是把真正原因往上帶
    """
    headers = {}
    if FINMIND_TOKEN:
        headers["Authorization"] = f"Bearer {FINMIND_TOKEN}"
    try:
        resp = requests.get(FINMIND_URL, params=params, headers=headers, timeout=timeout)
        j = resp.json()
    except Exception as e:
        return [], f"連線 FinMind 失敗: {e}"

    data = j.get("data", [])
    if not data and j.get("status") not in (200, None):
        status = j.get("status")
        msg = j.get("msg", "")
        if status == 402:
            return [], f"FinMind API 配額已用盡（{msg}），請稍後再試，或設定 FINMIND_TOKEN 以取得個人配額"
        if status == 403:
            return [], f"FinMind API 暫時限制存取（{msg}），請等待約 30 分鐘後再試"
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
    try:
        headers = {"Authorization": f"Bearer {FINMIND_TOKEN}"} if FINMIND_TOKEN else {}
        resp = requests.get(FINMIND_URL, params=params, headers=headers, timeout=15)
        return jsonify(resp.json()), resp.status_code
    except requests.RequestException as e:
        return jsonify({"status": 500, "msg": f"連線 FinMind 失敗: {e}", "data": []}), 500


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


def fetch_revenue_yoy(stock_id):
    """
    抓最近 14 個月營收，計算最新一筆的年增率 YoY(%)。
    抓不到資料時回傳 None。
    """
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
            return None
        data = sorted(data, key=lambda r: (r.get("revenue_year", 0), r.get("revenue_month", 0)))
        latest = data[-1]
        ly, lm = latest.get("revenue_year"), latest.get("revenue_month")
        same_month_last_year = None
        for r in data[:-1]:
            if r.get("revenue_year") == ly - 1 and r.get("revenue_month") == lm:
                same_month_last_year = r
                break
        if not same_month_last_year or not same_month_last_year.get("revenue"):
            return None
        yoy = (latest["revenue"] - same_month_last_year["revenue"]) / same_month_last_year["revenue"] * 100
        return round(float(yoy), 2)
    except Exception:
        return None


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
        end_date = datetime.now().strftime("%Y-%m-%d")
        start_date = (datetime.now() - timedelta(days=1100)).strftime("%Y-%m-%d")  # 約 3 年
        data, _err = finmind_get({
            "dataset": "TaiwanStockPER",
            "data_id": stock_id,
            "start_date": start_date,
            "end_date": end_date,
        }, timeout=20)
        if not data:
            return None

        data = sorted(data, key=lambda r: r.get("date", ""))
        pe_list = [r.get("PER") for r in data if r.get("PER") and r.get("PER") > 0]
        if len(pe_list) < 10:
            return None

        latest_per = None
        for r in reversed(data):
            if r.get("PER") and r.get("PER") > 0:
                latest_per = r["PER"]
                break
        if not latest_per:
            return None

        eps = current_price / latest_per
        pe_low = min(pe_list)
        pe_high = max(pe_list)
        pe_avg = sum(pe_list) / len(pe_list)

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
                      recent_high5, volume, vol_ma5, short_sig, mid_sig, valuation):
    """
    持股價格即時分析（無需存檔，每次輸入當下計算）。
    依使用者輸入的買入價／張數／策略（short 或 mid），
    結合既有的短線／波段策略訊號與估值資料，給出：
    HOLD（持有）／ADD（可補倉）／REDUCE（停利／減碼）／STOP（建議停損）
    """
    profit_pct = round((close - buy_price) / buy_price * 100, 2) if buy_price else None
    sig = short_sig if strategy_pref == "short" else mid_sig
    action = sig["action"]

    status = "HOLD"
    status_label = "🟢 持有"
    add_action = "暫不補倉"
    sell_action = "尚未觸發"
    reasons = []

    stop_ref = ma5 if strategy_pref == "short" else ma20
    stop_loss = round(stop_ref, 2) if stop_ref is not None else None
    take_profit = None
    if valuation:
        take_profit = valuation["target_price"]
    elif recent_high5 is not None:
        take_profit = round(recent_high5 * 1.05, 2)

    if "停損" in action:
        status = "STOP"
        status_label = "🔴 建議停損"
        sell_action = "已觸發停損條件"
        reasons.append(sig["reasons"][0] if sig["reasons"] else "已跌破防守價位")
    elif "結清" in action or "了結" in action:
        status = "REDUCE"
        status_label = "🟡 停利／減碼"
        sell_action = "已達停利／過熱條件，建議分批減碼"
        reasons.extend(sig["reasons"])
    else:
        # 判斷是否符合補倉條件（賺錢狀態 + 突破近期高點 + 量能配合）
        breakout = (
            close is not None and recent_high5 is not None and close > recent_high5
            and volume is not None and vol_ma5 and volume > vol_ma5
        )
        profitable = profit_pct is not None and profit_pct > 0
        if action == "買進訊號" and profitable and breakout:
            status = "ADD"
            status_label = "🔵 可以考慮補倉"
            add_action = f"建議補倉區間：{round(close*0.99,1)}～{round(close*1.01,1)}"
            reasons.append("趨勢偏多、獲利中且突破近期高點並帶量")
        else:
            reasons.append("目前尚未突破關鍵壓力，不建議追價加碼" if not breakout else "訊號尚未同時滿足補倉條件")

    recommendation = status_label.split(" ", 1)[-1] + "：" + ("；".join(reasons) if reasons else "持續觀察")

    return {
        "profit_pct": profit_pct,
        "status": status,
        "status_label": status_label,
        "add_action": add_action,
        "sell_action": sell_action,
        "stop_loss": stop_loss,
        "take_profit": take_profit,
        "recommendation": recommendation,
    }



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
    vol_ratio = last_vol / avg_vol5 if avg_vol5 > 0 else 1.0

    # --- 技術面評分 ---
    score = 0
    if latest["MA5"] is not None and latest["MA10"] is not None:
        score += 1 if latest["MA5"] > latest["MA10"] else -1
    if latest["MA10"] is not None and latest["MA20"] is not None:
        score += 1 if latest["MA10"] > latest["MA20"] else -1
    if latest["MA20"] is not None:
        score += 1 if latest["Close"] > latest["MA20"] else -1
    if latest["MA60"] is not None:
        score += 1 if latest["Close"] > latest["MA60"] else -1
    if latest["K"] is not None and latest["D"] is not None:
        score += 1 if latest["K"] > latest["D"] else -1
        if latest["K"] < 20:
            score += 1
        elif latest["K"] > 80:
            score -= 1
    if latest["MACD_Hist"] is not None:
        score += 1 if latest["MACD_Hist"] > 0 else -1
    if "偏低" in bb_pos:
        score += 1
    elif "偏高" in bb_pos:
        score -= 1
    if vol_ratio > 1.5:
        score += 1
    elif vol_ratio < 0.5:
        score -= 1

    # --- 策略訊號（短線3~5天 KD(5,3,3) ／ 波段2~3週 週KD(9,3,3)+日KD(9,3,3)+營收YoY）---
    weekly_kd = calc_weekly_kd9(df)
    revenue_yoy = fetch_revenue_yoy(stock_id)
    entry_date = request.args.get("entry_date", "").strip() or None
    strategy = build_strategy_signals(
        latest, prev, weekly_kd, revenue_yoy,
        float(latest["Vol_MA20"]) if latest["Vol_MA20"] is not None else None,
        datetime.now().day,
        df=df, entry_date=entry_date,
    )

    # --- 估值引擎（階段1：合理價格 / 合理買入上限 / 目標價）---
    valuation = fetch_valuation(stock_id, float(latest["Close"]))

    # --- 持股價格即時分析（選填，不存檔，當下輸入當下算）---
    position = None
    buy_price_arg = request.args.get("buy_price", "").strip()
    if buy_price_arg:
        try:
            buy_price = float(buy_price_arg)
            shares_arg = request.args.get("shares", "").strip()
            shares = float(shares_arg) if shares_arg else None
            strategy_pref = request.args.get("strategy_pref", "short").strip()
            if strategy_pref not in ("short", "mid"):
                strategy_pref = "short"
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
            )
        except (ValueError, TypeError):
            position = None

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
            "ratio": round(vol_ratio, 2),
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
        "strategy": strategy,
        "valuation": valuation,
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
