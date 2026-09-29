import os
from datetime import datetime
from zoneinfo import ZoneInfo

from app import (
    ai_build_daily_report,
    ai_is_trading_day,
    ai_send_report_email,
    ai_log_run,
)

DATABASE_URL = os.getenv("DATABASE_URL", "").strip()
if not DATABASE_URL:
    raise SystemExit("缺少 DATABASE_URL；正式晨報禁止使用暫存 SQLite")

now = datetime.now(ZoneInfo("Asia/Taipei"))
is_td, note = ai_is_trading_day(now.date())

if not is_td:
    ai_log_run("daily_report", "skipped", now.date().isoformat(), note)
    print(f"今日非台灣交易日，略過晨報：{note}")
    raise SystemExit(0)

try:
    print("開始建立正式台股晨報（PostgreSQL 持久化）...")
    report = ai_build_daily_report(now.date(), persist=True)

    mail = ai_send_report_email(report)
    if not mail.get("sent"):
        ai_log_run("daily_report", "email_failed", report.get("report_date"), mail)
        raise SystemExit(f"晨報已建立，但寄送失敗：{mail}")

    ai_log_run(
        "daily_report",
        "success",
        report.get("report_date"),
        f"provider={mail.get('provider')}; id={mail.get('id')}",
    )
    print("正式晨報已寫入 PostgreSQL 並寄送成功")
except Exception as e:
    ai_log_run("daily_report", "failed", now.date().isoformat(), e)
    raise
