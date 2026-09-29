import os
from datetime import datetime
from zoneinfo import ZoneInfo

import requests


RESEND_API_KEY = os.getenv("RESEND_API_KEY", "").strip()
REPORT_EMAIL = os.getenv("REPORT_EMAIL", "").strip()

if not RESEND_API_KEY:
    raise SystemExit("缺少 RESEND_API_KEY")

if not REPORT_EMAIL:
    raise SystemExit("缺少 REPORT_EMAIL")


now = datetime.now(ZoneInfo("Asia/Taipei"))

subject = f"台股分析系統｜06:30 晨報排程測試｜{now:%Y-%m-%d}"

html = f"""
<h2>台股分析系統｜晨報排程測試成功</h2>

<p>GitHub Actions 已成功獨立執行晨報排程。</p>

<ul>
  <li>台灣時間：{now:%Y-%m-%d %H:%M:%S}</li>
  <li>執行環境：GitHub Actions</li>
  <li>寄信服務：Resend HTTPS API</li>
  <li>Render 主網站：未參與本次晨報運算</li>
</ul>

<p>這封信用來驗證：</p>

<p>
GitHub Actions → 晨報程式 → Resend → Gmail
</p>
"""

response = requests.post(
    "https://api.resend.com/emails",
    headers={
        "Authorization": f"Bearer {RESEND_API_KEY}",
        "Content-Type": "application/json",
    },
    json={
        "from": "台股分析系統 <onboarding@resend.dev>",
        "to": [REPORT_EMAIL],
        "subject": subject,
        "html": html,
    },
    timeout=30,
)

print("Resend HTTP:", response.status_code)
print("Resend 回應:", response.text)

if response.status_code >= 300:
    raise SystemExit(f"寄信失敗：HTTP {response.status_code}")

print("06:30 排程測試信寄送成功")
