import os
from datetime import datetime
from zoneinfo import ZoneInfo

import requests

from app import (
    ai_build_daily_report,
    ai_is_trading_day,
    ai_report_html,
    _send_email_via_resend,
)

REPORT_EMAIL = os.getenv("REPORT_EMAIL", "").strip()
AI_SCHEDULER_TOKEN = os.getenv("AI_SCHEDULER_TOKEN", "").strip()
REPORT_SYNC_URL = os.getenv(
    "REPORT_SYNC_URL",
    "https://hidkcole-1.onrender.com/api/assistant/import_report",
).strip()

if not REPORT_EMAIL:
    raise SystemExit("缺少 REPORT_EMAIL")

now = datetime.now(ZoneInfo("Asia/Taipei"))
is_td, note = ai_is_trading_day(now.date())

if not is_td:
    print(f"今日非台灣交易日，略過晨報：{note}")
    raise SystemExit(0)

print("開始建立正式台股晨報...")
report = ai_build_daily_report(now.date(), persist=False)

subject = (
    f"台股 AI 小助手晨報｜{report.get('report_date')}｜"
    f"{(report.get('summary') or {}).get('taiwan_market', '')}"
)

mail = _send_email_via_resend(
    subject=subject,
    html=ai_report_html(report),
    text="請使用支援 HTML 的郵件程式閱讀台股 AI 小助手晨報。",
)

if not mail.get("sent"):
    raise SystemExit(f"晨報寄送失敗：{mail}")

print("正式晨報寄送成功")

if AI_SCHEDULER_TOKEN and REPORT_SYNC_URL:
    try:
        resp = requests.post(
            REPORT_SYNC_URL,
            headers={"X-Assistant-Token": AI_SCHEDULER_TOKEN},
            json=report,
            timeout=30,
        )
        print("網站同步 HTTP:", resp.status_code)
        print("網站同步回應:", (resp.text or "")[:500])
        if resp.status_code >= 300:
            raise SystemExit(f"晨報已寄出，但網站同步失敗：HTTP {resp.status_code}")
    except requests.RequestException as e:
        raise SystemExit(f"晨報已寄出，但網站同步連線失敗：{e}")
else:
    print("未設定 AI_SCHEDULER_TOKEN，略過網站同步。")

print("06:30 正式晨報流程完成")
