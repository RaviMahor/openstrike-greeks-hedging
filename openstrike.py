import math
import os
import json
import socket
import threading
import sys
import select
import time
import fcntl
import tty
import termios
import hmac
import hashlib
import requests
import signal
import atexit
import re
from datetime import datetime, timedelta, timezone
from collections import deque, Counter
from concurrent.futures import ThreadPoolExecutor
from typing import Optional, TextIO
from requests.adapters import HTTPAdapter

def safe_float(val, default=0.0):
    """
    Converts a value to float safely. Returns the default value if conversion fails.
    """
    try:
        if val is None:
            return default
        return float(val)
    except (ValueError, TypeError):
        return default

def _abs_int_size(p):
    """
    Helper function to safely extract the absolute integer size of a position.
    """
    try:
        return abs(int(float(p.get("size", 0)))) if p else 0
    except (ValueError, TypeError):
        return 0

def is_valid_target_strike(t):
    if not isinstance(t, str):
        return False
    if t in ("highest", "highest_oi", "highest_volume", "second_highest", "third_highest", "atm", "vol_oi"):
        return True
    t_lower = t.lower()
    if re.match(r"^\d+(?:st|nd|rd|th)?_highest$", t_lower):
        return True
    if re.match(r"^rank_\d+$", t_lower):
        return True
    return False

def get_rank_index(t):
    if not isinstance(t, str):
        return None
    t_lower = t.lower()
    if t_lower in ("highest", "highest_oi", "1st_highest", "rank_1"):
        return 0
    if t_lower in ("second_highest", "2nd_highest", "rank_2"):
        return 1
    if t_lower in ("third_highest", "3rd_highest", "rank_3"):
        return 2
    m = re.match(r"^(\d+)(?:st|nd|rd|th)?_highest$", t_lower)
    if m:
        return int(m.group(1)) - 1
    m = re.match(r"^rank_(\d+)$", t_lower)
    if m:
        return int(m.group(1)) - 1
    return None

def _acquire_single_instance_lock():
    """
    Ensures that only a single instance of this trading bot runs.
    If an old instance exists, it sends SIGTERM to terminate it, then acquires a file lock.
    """
    base_name = os.path.splitext(os.path.basename(os.path.abspath(__file__)))[0]
    lock_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), f"{base_name}.lock")
    for attempt in range(2):
        f = open(lock_path, "w")
        try:
            fcntl.flock(f.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except (BlockingIOError, OSError):
            f.close()

            try:
                with open(lock_path, "r") as rf:
                    old_pid = int(rf.read().strip())
                if old_pid != os.getpid():
                    os.kill(old_pid, signal.SIGTERM)
                    time.sleep(2)
            except (ValueError, ProcessLookupError, PermissionError, FileNotFoundError):
                time.sleep(1)
            if attempt == 1:
                print("⚠️ Could not take over — old instance may still be exiting.", flush=True)
                sys.exit(1)
            continue
        f.write(str(os.getpid()))
        f.flush()
        return f

_SINGLE_INSTANCE_LOCK = _acquire_single_instance_lock()

_HTTP_SESSION = requests.Session()
_HTTP_ADAPTER = HTTPAdapter(pool_connections=24, pool_maxsize=24)
_HTTP_SESSION.mount("https://", _HTTP_ADAPTER)
_HTTP_SESSION.mount("http://", _HTTP_ADAPTER)


def _configure_requests_dual_stack():
    """Allow both IPv4 and IPv6 — whitelist both on Delta so whichever resolves first works."""
    try:
        import urllib3.util.connection as urllib3_connection

        def _allowed_gai_family():
            return socket.AF_UNSPEC          # let OS pick IPv4 or IPv6

        urllib3_connection.allowed_gai_family = _allowed_gai_family
    except Exception:
        pass


_configure_requests_dual_stack()


def _get_outbound_ips():
    """Return dict with 'ipv4' and/or 'ipv6' keys — whichever are reachable."""
    ips = {}
    try:
        r = http_get("https://api4.ipify.org", timeout=5)
        if r.status_code == 200:
            ips["ipv4"] = r.text.strip()
    except Exception:
        pass
    try:
        r = http_get("https://api6.ipify.org", timeout=5)
        if r.status_code == 200:
            v6 = r.text.strip()
            if ":" in v6:                     # only store if truly IPv6
                ips["ipv6"] = v6
    except Exception:
        pass
    return ips


def http_get(url, **kwargs):
    return _HTTP_SESSION.get(url, **kwargs)

def http_post(url, **kwargs):
    return _HTTP_SESSION.post(url, **kwargs)

_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
_SCRIPT_BASE = os.path.splitext(os.path.basename(os.path.abspath(__file__)))[0]
_SETTINGS_PATH = os.path.join(_SCRIPT_DIR, _SCRIPT_BASE + ".json")
_SECRETS_PATH = os.path.join(_SCRIPT_DIR, _SCRIPT_BASE + ".secrets.json")

TELEGRAM_BOT_TOKEN = ""
TELEGRAM_CHAT_ID = ""

def send_telegram(msg):
    if not TELEGRAM_BOT_TOKEN:
        return
    def _send():
        try:
            url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
            payload = {"chat_id": TELEGRAM_CHAT_ID, "text": msg}
            r = http_post(url, json=payload, timeout=5)
            if r.status_code != 200:
                print("❌ Telegram failed:", r.text, flush=True)
        except Exception as e:
            print("❌ Telegram failed:", e, flush=True)
    threading.Thread(target=_send, daemon=True).start()
SCRIPT_EXITED = False
def script_exit_alert(reason="Unknown"):
    global SCRIPT_EXITED
    if SCRIPT_EXITED:
            return
    SCRIPT_EXITED = True

    body = (
        f"⚠️ SCRIPT EXIT ALERT\n"
        f"Reason : {reason}\n"
        f"Time   : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
    )
    if reason == "Ctrl+C":
        body += "\n🛑 Positions unchanged (no auto square-off)."
    send_telegram(body)
atexit.register(lambda: script_exit_alert("Python process exited"))

LAST_401_TELEGRAM_AT = 0.0
_401_TELEGRAM_COOLDOWN_SEC = 120
_401_ALERT_SENT = False
_LAST_401_IP_HELP_KEY = ""
LAST_IP_WHITELIST_LOG_AT = 0.0
LAST_BLOCKED_IP = ""

def is_ip_whitelist_error(err):
    if not err:
        return False
    err_str = str(err).lower()
    if "ip_not_whitelisted" in err_str:
        return True
    try:
        if hasattr(err, "response") and err.response is not None:
            if err.response.status_code == 401 and "ip_not_whitelisted" in err.response.text:
                return True
    except Exception:
        pass
    return False

def _parse_api_client_ip(response_text):
    if not response_text:
        return ""
    try:
        data = json.loads(response_text)
        ctx = (data.get("error") or {}).get("context") or {}
        return str(ctx.get("client_ip") or "").strip()
    except Exception:
        m = re.search(r'"client_ip"\s*:\s*"([^"]+)"', response_text)
        return m.group(1).strip() if m else ""

def _log_ip_whitelist_help(client_ip, path, force_print=False):
    global _LAST_401_IP_HELP_KEY
    if not client_ip:
        return
    key = f"{client_ip}|{path}"
    if not force_print and key == _LAST_401_IP_HELP_KEY:
        return
    _LAST_401_IP_HELP_KEY = key
    print(
        f"\n🔐 IP WHITELIST — Delta blocked API calls from:\n"
        f"   {client_ip}\n"
        f"   Fix: Delta → API Keys → python → Whitelisted IP → paste the line above → Update IP Address\n"
        f"   Tip: Whitelist BOTH your IPv4 and IPv6 on Delta — bot uses whichever connects first.\n",
        flush=True,
    )

def _send_401_telegram_once(status_code, response_text, path, should_print_help=True):
    global LAST_401_TELEGRAM_AT, _401_ALERT_SENT
    client_ip = _parse_api_client_ip(response_text)
    if should_print_help:
        _log_ip_whitelist_help(client_ip, path, force_print=True)
    now = time.time()
    if now - LAST_401_TELEGRAM_AT < _401_TELEGRAM_COOLDOWN_SEC:
        return
    LAST_401_TELEGRAM_AT = now
    _401_ALERT_SENT = True
    err_short = (response_text[:250] if response_text else str(status_code))
    ip_line = f"Client IP : {client_ip}\n" if client_ip else ""
    send_telegram(
        f"🔴 API 401 ERROR\n\n"
        f"Code   : {status_code}\n"
        f"Path   : {path}\n"
        f"{ip_line}"
        f"Error  : {err_short}\n\n"
        f"⚠️ Whitelist the Client IP on Delta (API Keys → Update IP).\n"
        f"Time   : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
    )

def _send_401_cleared_telegram_once():
    global _401_ALERT_SENT
    if not _401_ALERT_SENT:
        return
    _401_ALERT_SENT = False
    send_telegram(
        f"🟢 API 401 ERROR CLEARED\n\n"
        f"Auth / IP issue resolved. API calls are working normally now.\n"
        f"Time : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
    )

def api_failure_alert(api_name, error):
    global API_DOWN
    if not HEALTH.get(api_name, True):
        return
    now = time.time()
    last_time = LAST_API_ALERT_TIME.get(api_name)

    err_str = str(error).lower()
    is_400_bad_request = "400" in err_str and ("bad request" in err_str or "client error" in err_str)
    if api_name in ("ORDERS", "POSITIONS", "SPOT", "WALLET") and not is_400_bad_request:
        API_DOWN = True

    if last_time and (now - last_time < API_ALERT_COOLDOWN):
        return

    LAST_API_ALERT_TIME[api_name] = now

    if HEALTH.get(api_name, True):
        HEALTH[api_name] = False
        API_LATENCY[api_name] = -1

        send_telegram(
            f"🔴 API DOWN ALERT\n\n"
            f"API   : {api_name}\n"
            f"Error : {str(error)[:200]}\n"
            f"Time  : {datetime.now().strftime('%H:%M:%S')}"
        )
def api_recovered(api_name):
    if not HEALTH[api_name]:
        HEALTH[api_name] = True
        API_LATENCY[api_name] = 0
        now = time.time()
        last_rec = LAST_RECOVERED_ALERT_TIME.get(api_name, 0)
        if now - last_rec >= API_RECOVERED_COOLDOWN:
            LAST_RECOVERED_ALERT_TIME[api_name] = now
            send_telegram(
                f"🟢 API RECOVERED\n"
                f"API  : {api_name}\n"
                f"Time : {datetime.now().strftime('%H:%M:%S')}"
            )

HEALTH = {
    "SPOT": True,
    "WALLET": True,
    "ORDERS": True,
    "POSITIONS": True,
}

LAST_API_ALERT_TIME = {
    "SPOT": 0.0,
    "WALLET": 0.0,
    "ORDERS": 0.0,
    "POSITIONS": 0.0,
}
LAST_RECOVERED_ALERT_TIME = {
    "SPOT": 0.0,
    "WALLET": 0.0,
    "ORDERS": 0.0,
    "POSITIONS": 0.0,
}
API_LATENCY = {
    "SPOT": 0,
    "WALLET": 0,
    "ORDERS": 0,
    "POSITIONS": 0,
}
def latency_status(latency_ms):
    if latency_ms < 0:
        return "🔴 DOWN"
    if latency_ms > 3000:
        return "🔴 CRITICAL"
    elif latency_ms > 2000:
        return "⚠️ WARNING"
    elif latency_ms >= 1000:
        return "🟡 SLOW"
    else:
        return "🟢 HEALTHY"

MAIN_ACCOUNT = {
    "account_name": "Main",
    "username": "Quantitative Trader",
    "email": "trader@example.com",
    "phone": "+1 0000000000"
}
ACCOUNT_NAME_EDIT_PENDING = False
USER_EDIT_PENDING = False
MARGIN_EDIT_PENDING = False

SYMBOL = "BTC"
INSTRUMENT_SWITCH_PENDING = False
INSTRUMENT_SWITCH_SQUARE_OFF_SENT = False
INSTRUMENT_SWITCH_BIAS_CHANGE_DETECTED = False
INSTRUMENT_SWITCH_BIAS_CHANGE_MSG = ""
LAST_BIAS_BTC = None
LAST_BIAS_ETH = None
CMD_FEEDBACK = ""
CMD_FEEDBACK_CLEAR_AT = 0.0
LAST_CMD_SHOWN = {"msg": "", "until": 0.0}
BASE_URL = "https://api.india.delta.exchange"

API_KEY = ""
API_SECRET = ""

REFRESH_SECONDS = 1

STRATEGY_MODE = "OPENSTRIKE"
STRATEGY_SWITCH_PENDING = False
PENDING_STRATEGY_MODE = ""
PENDING_TARGET_STRIKE = ""

ORDER_TYPE = "options"
ORDER_TYPES_CYCLE = ["options", "futures"]

OPENSTRIKE_TARGET_STRIKE = "highest_oi"

execution_status = "IDLE"

MARGIN_MODE = "cross"
MARGIN_MODES_CYCLE = ["isolated", "cross", "portfolio"]

MAX_USED_MARGIN_MULTIPLIER = 2.0

POSITION_SIZING_MODE = "max_loss"
MAX_LOSS_CAP_PCT = 0.10

def _position_sizing_mode_label():
    if POSITION_SIZING_MODE == "max_loss":
        return f"Max Loss {round(MAX_LOSS_CAP_PCT * 100)}%"
    elif POSITION_SIZING_MODE == "target_profit":
        return f"Target Profit {round(TARGET_PROFIT_PCT * 100)}%"
    return "Margin"

def _load_settings():
    defaults = {
        "strategy_switch_pending": False,
        "pending_strategy_mode": "",
        "pending_target_strike": "",
        "symbol": "BTC",
        "min_margin_pct": 0.10,
        "max_loss_cap_pct": 0.10,
        "account_name": "Main",
        "username": "Quantitative Trader",
        "email": "trader@example.com",
        "phone": "+1 0000000000",
        "margin_mode": "cross",
        "position_sizing_mode": "max_loss",
        "strategy_mode": "OPENSTRIKE",
        "order_type": "options",
        "user_auto_execution": True,
        "log_enabled": True,
        "api_key": os.getenv("DELTA_API_KEY", ""),
        "api_secret": os.getenv("DELTA_API_SECRET", ""),
        "telegram_bot_token": os.getenv("TELEGRAM_BOT_TOKEN", ""),
        "telegram_chat_id": os.getenv("TELEGRAM_CHAT_ID", ""),
        "openstrike_target_strike": "highest",
        "oi_chain_view": "both",
        "custom_hedges_count": 2,
        "target_profit_pct": 10.0,
        "openstrike_pending_missing_legs": {
            "call": {
                "symbol": "",
                "strike": 0.0,
                "reason": "",
                "since": 0.0,
                "fail_count": 0,
            },
            "put": {
                "symbol": "",
                "strike": 0.0,
                "reason": "",
                "since": 0.0,
                "fail_count": 0,
            }
        },
        "custom_base_threshold": 0.50,
        "custom_active_threshold": 0.75,
    }
    try:
        if os.path.isfile(_SECRETS_PATH):
            with open(_SECRETS_PATH) as f:
                secret_data = json.load(f)
            for k in ("api_key", "api_secret", "telegram_bot_token", "telegram_chat_id"):
                if k in secret_data and secret_data[k] is not None:
                    defaults[k] = str(secret_data[k]).strip()

        if not os.path.isfile(_SETTINGS_PATH):
            _legacy = os.path.join(_SCRIPT_DIR, "delta_settings.json")
            if os.path.isfile(_legacy):
                with open(_legacy) as f:
                    d = json.load(f)
                    for k in defaults:
                        if k in d:
                            defaults[k] = d[k]
                    defaults["min_margin_pct"] = max(0.01, min(1.0, float(defaults.get("min_margin_pct", 0.10))))
                    if defaults["margin_mode"] not in ("isolated", "cross", "portfolio"):
                        defaults["margin_mode"] = "cross"
                    if defaults["position_sizing_mode"] not in ("margin", "max_loss", "target_profit"):
                        defaults["position_sizing_mode"] = "max_loss"
                    if defaults["strategy_mode"] not in ("OPENSTRIKE", "STRADDLE"):
                        defaults["strategy_mode"] = "OPENSTRIKE"
                    val = str(defaults.get("order_type", "options")).strip().lower()
                    if val not in ("options", "futures"):
                        val = "options"
                    defaults["order_type"] = val
                    with open(_SETTINGS_PATH, "w") as out:
                        json.dump({k: defaults[k] for k in defaults}, out, indent=2)
                    return defaults
            with open(_SETTINGS_PATH, "w") as out:
                json.dump({k: defaults[k] for k in defaults}, out, indent=2)
            return defaults
        if os.path.isfile(_SETTINGS_PATH):
            with open(_SETTINGS_PATH) as f:
                d = json.load(f)
                for k in defaults:
                    if k in d:
                        defaults[k] = d[k]
                defaults["min_margin_pct"] = max(0.01, min(1.0, float(defaults.get("min_margin_pct", 0.10))))
                defaults["max_loss_cap_pct"] = max(0.01, min(1.0, float(defaults.get("max_loss_cap_pct", 0.10))))
                defaults["target_profit_pct"] = float(defaults.get("target_profit_pct", 10.0))
                if defaults["margin_mode"] not in ("isolated", "cross", "portfolio"):
                    defaults["margin_mode"] = "cross"
                if defaults["position_sizing_mode"] not in ("margin", "max_loss", "target_profit"):
                    defaults["position_sizing_mode"] = "max_loss"
                if defaults["strategy_mode"] not in ("OPENSTRIKE", "STRADDLE"):
                    defaults["strategy_mode"] = "OPENSTRIKE"
                val = str(defaults.get("order_type", "options")).strip().lower()
                if val not in ("options", "futures"):
                    val = "options"
                defaults["order_type"] = val
                if not is_valid_target_strike(defaults["openstrike_target_strike"]):
                    defaults["openstrike_target_strike"] = "highest_oi"
                elif defaults["openstrike_target_strike"] == "highest":
                    defaults["openstrike_target_strike"] = "highest_oi"
                if defaults["oi_chain_view"] not in ("both", "single"):
                    defaults["oi_chain_view"] = "both"
                if defaults["symbol"] not in ("BTC", "ETH"):
                    defaults["symbol"] = "BTC"
                defaults["strategy_switch_pending"] = bool(defaults.get("strategy_switch_pending", False))
                defaults["pending_strategy_mode"] = str(defaults.get("pending_strategy_mode", ""))
                defaults["pending_target_strike"] = str(defaults.get("pending_target_strike", ""))
                defaults["custom_hedges_count"] = 2
                
                defaults["custom_base_threshold"] = float(defaults.get("custom_base_threshold", 0.50))
                defaults["custom_active_threshold"] = float(defaults.get("custom_active_threshold", 0.75))
                defaults["last_cross_down_side"] = str(defaults.get("last_cross_down_side", "None")).strip()
                defaults["last_alerted_call_oppoi_step"] = d.get("last_alerted_call_oppoi_step", None)
                defaults["last_alerted_put_oppoi_step"] = d.get("last_alerted_put_oppoi_step", None)
                
                if "openstrike_pending_missing_legs" in d:
                    defaults["openstrike_pending_missing_legs"] = d["openstrike_pending_missing_legs"]
                elif "openstrike_pending_missing_leg" in d and isinstance(d["openstrike_pending_missing_leg"], dict):
                    old = d["openstrike_pending_missing_leg"]
                    leg = old.get("leg", "")
                    if leg in ("call", "put"):
                        defaults["openstrike_pending_missing_legs"][leg] = {
                            "symbol": str(old.get("symbol", "")),
                            "strike": safe_float(old.get("strike", 0.0)),
                            "reason": str(old.get("reason", "")),
                            "since": safe_float(old.get("since", 0.0)),
                            "fail_count": int(old.get("fail_count", 0)),
                        }
                
                if not isinstance(defaults.get("openstrike_pending_missing_legs"), dict):
                    defaults["openstrike_pending_missing_legs"] = {}
                for leg in ("call", "put"):
                    if leg not in defaults["openstrike_pending_missing_legs"] or not isinstance(defaults["openstrike_pending_missing_legs"][leg], dict):
                        defaults["openstrike_pending_missing_legs"][leg] = {
                            "symbol": "",
                            "strike": 0.0,
                            "reason": "",
                            "since": 0.0,
                            "fail_count": 0,
                        }
                    else:
                        leg_data = defaults["openstrike_pending_missing_legs"][leg]
                        if "fail_count" not in leg_data:
                            leg_data["fail_count"] = 0
    except Exception:
        pass
    return defaults
def _save_settings():
    try:
        d = {
            "strategy_switch_pending": STRATEGY_SWITCH_PENDING,
            "pending_strategy_mode": PENDING_STRATEGY_MODE,
            "pending_target_strike": PENDING_TARGET_STRIKE,
            "symbol": SYMBOL,
            "min_margin_pct": MIN_MARGIN_PCT,
            "max_loss_cap_pct": MAX_LOSS_CAP_PCT,
            "account_name": MAIN_ACCOUNT.get("account_name", "Main"),
            "username": MAIN_ACCOUNT.get("username", ""),
            "email": MAIN_ACCOUNT.get("email", ""),
            "phone": MAIN_ACCOUNT.get("phone", ""),
            "margin_mode": MARGIN_MODE.lower(),
            "position_sizing_mode": POSITION_SIZING_MODE,
            "strategy_mode": STRATEGY_MODE,
            "order_type": ORDER_TYPE,
            "user_auto_execution": USER_AUTO_EXECUTION,
            "log_enabled": LOG_ENABLED,
            "api_key": API_KEY,
            "api_secret": API_SECRET,
            "telegram_bot_token": TELEGRAM_BOT_TOKEN,
            "telegram_chat_id": TELEGRAM_CHAT_ID,
            "openstrike_target_strike": OPENSTRIKE_TARGET_STRIKE,
            "oi_chain_view": OI_CHAIN_VIEW,
            "custom_hedges_count": CUSTOM_HEDGES_COUNT,
            "target_profit_pct": TARGET_PROFIT_PCT * 100.0,
            "custom_base_threshold": CUSTOM_BASE_THRESHOLD,
            "custom_active_threshold": CUSTOM_ACTIVE_THRESHOLD,
            "last_cross_down_side": LAST_CROSS_DOWN_SIDE,
            "last_alerted_call_oppoi_step": globals().get("LAST_ALERTED_CALL_OPPOI_STEP", None),
            "last_alerted_put_oppoi_step": globals().get("LAST_ALERTED_PUT_OPPOI_STEP", None),
            "openstrike_pending_missing_legs": globals().get("OPENSTRIKE_PENDING_MISSING_LEGS", {
                "call": {
                    "symbol": "",
                    "strike": 0.0,
                    "reason": "",
                    "since": 0.0,
                    "fail_count": 0,
                },
                "put": {
                    "symbol": "",
                    "strike": 0.0,
                    "reason": "",
                    "since": 0.0,
                    "fail_count": 0,
                }
            }),
        }
        with open(_SETTINGS_PATH, "w") as f:
            json.dump(d, f, indent=2)
    except Exception as e:
        print("⚠️ Settings save fail:", e)

def _reset_settings_to_defaults():
    global SYMBOL, MIN_MARGIN_PCT, MAX_LOSS_CAP_PCT, MARGIN_MODE, POSITION_SIZING_MODE, STRATEGY_MODE, ORDER_TYPE, USER_AUTO_EXECUTION
    global TARGET_PROFIT_PCT
    global OPENSTRIKE_PENDING_MISSING_LEGS
    global CUSTOM_BASE_THRESHOLD, CUSTOM_ACTIVE_THRESHOLD, LAST_CROSS_DOWN_SIDE
    global LAST_ALERTED_CALL_OPPOI_STEP, LAST_ALERTED_PUT_OPPOI_STEP
    CUSTOM_BASE_THRESHOLD = 0.50
    CUSTOM_ACTIVE_THRESHOLD = 0.75
    LAST_CROSS_DOWN_SIDE = "None"
    LAST_ALERTED_CALL_OPPOI_STEP = None
    LAST_ALERTED_PUT_OPPOI_STEP = None
    SYMBOL = "BTC"
    STRATEGY_SWITCH_PENDING = False
    PENDING_STRATEGY_MODE = ""
    PENDING_TARGET_STRIKE = ""
    MIN_MARGIN_PCT = 0.10
    MAX_LOSS_CAP_PCT = 0.10
    TARGET_PROFIT_PCT = 0.10
    MAIN_ACCOUNT["account_name"] = "Main"
    MAIN_ACCOUNT["username"] = "Quantitative Trader"
    MAIN_ACCOUNT["email"] = "trader@example.com"
    MAIN_ACCOUNT["phone"] = "+1 0000000000"
    MARGIN_MODE = "cross"
    POSITION_SIZING_MODE = "target_profit"
    STRATEGY_MODE = "OPENSTRIKE"
    ORDER_TYPE = "options"
    USER_AUTO_EXECUTION = True
    global OPENSTRIKE_TARGET_STRIKE, OI_CHAIN_VIEW
    OPENSTRIKE_TARGET_STRIKE = "highest_oi"
    OI_CHAIN_VIEW = "both"
    OPENSTRIKE_PENDING_MISSING_LEGS = {
        "call": {
            "symbol": "",
            "strike": 0.0,
            "reason": "",
            "since": 0.0,
            "fail_count": 0,
        },
        "put": {
            "symbol": "",
            "strike": 0.0,
            "reason": "",
            "since": 0.0,
            "fail_count": 0,
        }
    }
    _save_settings()

_s = _load_settings()
SYMBOL = _s.get("symbol", "BTC")
STRATEGY_SWITCH_PENDING = _s.get("strategy_switch_pending", False)
PENDING_STRATEGY_MODE = _s.get("pending_strategy_mode", "")
PENDING_TARGET_STRIKE = _s.get("pending_target_strike", "")
MIN_MARGIN_PCT = _s["min_margin_pct"]
MAX_LOSS_CAP_PCT = _s.get("max_loss_cap_pct", 0.10)
TARGET_PROFIT_PCT = _s.get("target_profit_pct", 10.0) / 100.0
MAIN_ACCOUNT["account_name"] = _s["account_name"]
MAIN_ACCOUNT["username"] = _s["username"]
MAIN_ACCOUNT["email"] = _s["email"]
MAIN_ACCOUNT["phone"] = _s["phone"]
MARGIN_MODE = _s["margin_mode"]
POSITION_SIZING_MODE = _s["position_sizing_mode"]
if POSITION_SIZING_MODE == "target_profit":
    if "target_profit_pct" not in _s and MIN_MARGIN_PCT <= 0.05:
        TARGET_PROFIT_PCT = MIN_MARGIN_PCT
    MIN_MARGIN_PCT = 0.10
STRATEGY_MODE = _s["strategy_mode"]
ORDER_TYPE = str(_s.get("order_type", "options")).strip().lower()
if ORDER_TYPE == "futures" and POSITION_SIZING_MODE == "target_profit":
    POSITION_SIZING_MODE = "margin"
    MIN_MARGIN_PCT = 0.10
USER_AUTO_EXECUTION = _s["user_auto_execution"]
LOG_ENABLED = bool(_s.get("log_enabled", True))
OPENSTRIKE_TARGET_STRIKE = _s.get("openstrike_target_strike", "highest_oi")
if OPENSTRIKE_TARGET_STRIKE == "highest":
    OPENSTRIKE_TARGET_STRIKE = "highest_oi"
API_KEY = _s["api_key"]
API_SECRET = _s["api_secret"]
TELEGRAM_BOT_TOKEN = _s["telegram_bot_token"]
TELEGRAM_CHAT_ID = _s["telegram_chat_id"]
CUSTOM_HEDGES_COUNT = 2
CUSTOM_BASE_THRESHOLD = _s.get("custom_base_threshold", 0.50)
CUSTOM_ACTIVE_THRESHOLD = _s.get("custom_active_threshold", 0.75)
LAST_CROSS_DOWN_SIDE = _s.get("last_cross_down_side", "None")
LAST_ALERTED_CALL_OPPOI_STEP = _s.get("last_alerted_call_oppoi_step", None)
LAST_ALERTED_PUT_OPPOI_STEP = _s.get("last_alerted_put_oppoi_step", None)

HEDGE_DELTA_TARGET = 0.10
DELTA_THRESHOLD = 0.01
OI_DIFF_THRESHOLD_PCT = 10.0

OPENSTRIKE_CALL_DIFF_INFO = {"old_strike": None, "old_oi": None, "new_strike": None, "new_oi": None, "diff_pct": None, "action": "N/A"}
OPENSTRIKE_PUT_DIFF_INFO = {"old_strike": None, "old_oi": None, "new_strike": None, "new_oi": None, "diff_pct": None, "action": "N/A"}

EQUALITY_EVENT = False
LAST_ORDER_ERROR = ""

SYSTEM_EXECUTION_ALLOWED = True

EQUALITY_MANUAL_EXEC = False
EQUALITY_SUSPENDED = False
EQUALITY_SUSPENDED_UNTIL = 0
EQUALITY_TRIGGER_REASON = "NONE"
EXECUTION_ALLOWED = True
EQUALITY_WAIT_COUNT = 0
LAST_MARGIN_REDUCTION_TIME = 0.0
FORCE_UI_REFRESH = False
OI_CHAIN_VIEW = _s.get("oi_chain_view", "both")
UI_PRINT_LOCK = threading.RLock()
LAST_VISIBLE_UI_AT = time.time()
LAST_LIVE_UI_RENDER_AT = 0.0
LAST_HEARTBEAT_PRINT_AT = 0.0
LIVE_RENDER_COUNT = 0
LAST_MAIN_LOOP_STAGE = "startup"
STALL_HEARTBEAT_AFTER_SEC = 25.0
STALL_HEARTBEAT_EVERY_SEC = 10.0
LAST_FULL_SNAPSHOT_LOG_AT = 0.0
STALL_FULL_SNAPSHOT_EVERY_SEC = 30.0

LOW_BALANCE_USD = 5.0
LOW_FREE_USD = 0.25
PENDING_BIAS_REBALANCE = None
PENDING_BIAS_SINCE = 0.0
LOW_BALANCE_ALIGN_COOLDOWN_SEC = 60.0
LOW_BALANCE_ALIGN_LAST_TRY = 0.0

ORDER_FAILURE_COOLDOWN_UNTIL = 0.0
ORDER_FAILURE_COOLDOWN_SEC = 300

LEG_MODE = 1

MIN_POSITION_CONTRACTS = 1

MAIN_SYMBOL_OI_BY = "usd"

MARGIN_ENFORCEMENT_MODE = "SIGNAL"

ENFORCE_EQUALITY_JOB = True

KILL_SWITCH = False
_LAST_SIGINT_TIME = 0.0

def kill_switch(sig, frame):
    global _LAST_SIGINT_TIME
    now = time.time()
    if now - _LAST_SIGINT_TIME <= 3.0:
        print("\n🛑 SAFE EXIT (Ctrl+C x2)", flush=True)
        script_exit_alert("Ctrl+C")
        try:
            restore_tty()
        except:
            pass
        time.sleep(0.5)
        os._exit(0)
    _LAST_SIGINT_TIME = now
    print("\n⚠️  Ctrl+C pressed — press again within 3 seconds to exit.", flush=True)
signal.signal(signal.SIGINT, kill_switch)

def _sigterm_handler(sig, frame):
    print("\n🔴 SCRIPT KILLED (SIGTERM — terminal closed or new instance started)", flush=True)
    script_exit_alert("SIGTERM (terminal closed or duplicate launch)")
    try:
        restore_tty()
    except:
        pass
    time.sleep(0.5)
    os._exit(0)

def _sighup_handler(sig, frame):
    print("\n🔴 SCRIPT KILLED (SIGHUP — terminal disconnected)", flush=True)
    script_exit_alert("SIGHUP (terminal disconnected)")
    try:
        restore_tty()
    except:
        pass
    time.sleep(0.5)
    os._exit(0)

signal.signal(signal.SIGTERM, _sigterm_handler)
signal.signal(signal.SIGHUP, _sighup_handler)

def get_server_time():
    try:
        r = http_get(f"{BASE_URL}/v2/indices/t", timeout=5)
        return str(r.json()["result"]["timestamp"])
    except:
        return str(int(time.time()))

def sign(method, path, payload, ts):
    if not API_SECRET:
        raise RuntimeError(f"Missing api_secret in {_SETTINGS_PATH}")
    msg = method + ts + path + payload
    return hmac.new(API_SECRET.encode(), msg.encode(), hashlib.sha256).hexdigest()

def private_request(method, path, body=None, params=None):
    global LAST_IP_WHITELIST_LOG_AT, LAST_BLOCKED_IP
    import json
    if not API_KEY:
        raise RuntimeError(f"Missing api_key in {_SETTINGS_PATH}")
    json_body = json.dumps(body) if body else ""

    full_path = path
    if method == "GET" and params:
        query_string = "&".join([f"{k}={v}" for k, v in params.items()])
        full_path = f"{path}?{query_string}"

    ts = get_server_time()
    sig = sign(method, full_path, json_body, ts)

    headers = {
        "api-key": API_KEY,
        "timestamp": ts,
        "signature": sig,
        "Content-Type": "application/json"
    }

    url = BASE_URL + full_path
    if method == "GET":
        start = time.time()
        r = http_get(url, headers=headers, timeout=10)
        latency = int((time.time() - start) * 1000)

    else:
        start = time.time()
        r = http_post(url, headers=headers, data=json_body, timeout=10)
        latency = int((time.time() - start) * 1000)

    if r.status_code != 200:
        is_ip_wh = (r.status_code == 401 and "ip_not_whitelisted" in r.text)
        should_print = True
        if is_ip_wh:
            LAST_BLOCKED_IP = _parse_api_client_ip(r.text)
            now = time.time()
            if now - LAST_IP_WHITELIST_LOG_AT < 60.0:
                should_print = False
            else:
                LAST_IP_WHITELIST_LOG_AT = now

        if should_print:
            print(f"❌ API Error {r.status_code}: {r.text}")

        if r.status_code == 401:
            _send_401_telegram_once(r.status_code, r.text, path, should_print_help=should_print)
    else:
        _send_401_cleared_telegram_once()
        LAST_BLOCKED_IP = ""
    r.raise_for_status()
    return r.json()["result"]


def _startup_api_probe():
    """Verify wallet auth at boot; reset stale API_DOWN from a previous bad IP/session."""
    global API_DOWN, API_RECOVERY_COOLDOWN_UNTIL, HEALTH, API_LATENCY
    outbound = _get_outbound_ips()
    if outbound:
        ip_lines = []
        for label, addr in outbound.items():
            ip_lines.append(f"   {label.upper()}: {addr}")
        ip_block = "\n".join(ip_lines)
        print(
            f"\n🌐 Bot outbound IPs:\n{ip_block}\n"
            f"   Delta → API Keys → python → Whitelisted IP must include ALL addresses above.\n",
            flush=True,
        )
    try:
        start = time.time()
        private_request("GET", "/v2/wallet/balances")
        API_LATENCY["WALLET"] = int((time.time() - start) * 1000)
        for name in HEALTH:
            HEALTH[name] = True
            if API_LATENCY.get(name, 0) < 0:
                API_LATENCY[name] = 0
        API_DOWN = False
        API_RECOVERY_COOLDOWN_UNTIL = 0.0
        print("✅ Startup API probe: wallet authenticated (IP whitelist OK)\n", flush=True)
        return True
    except Exception as e:
        global LAST_BLOCKED_IP
        err_body = getattr(getattr(e, "response", None), "text", None) or str(e)
        client_ip = _parse_api_client_ip(err_body) if err_body else ""
        if not client_ip:
            client_ip = outbound.get("ipv4") or outbound.get("ipv6") or ""
        if client_ip:
            LAST_BLOCKED_IP = client_ip
        _log_ip_whitelist_help(client_ip, "/v2/wallet/balances")
        print("❌ Startup API probe failed — fix whitelist then restart.\n", flush=True)
        return False


def _bootstrap_dashboard_after_auth():
    """Paint one fresh dashboard so the terminal is not stuck on stale log snapshots."""
    global FIRST_UI_RENDER_DONE, API_DOWN, API_RECOVERY_COOLDOWN_UNTIL
    try:
        spot = get_spot()
        bal, blocked, upnl = wallet_usd()
        orders_api_health_check()
        positions_all = get_all_positions()
        spot_btc = spot if SYMBOL == "BTC" else get_spot("BTC")
        spot_eth = spot if SYMBOL == "ETH" else get_spot("ETH")
        _calc_upnl, _, position_count, position_details = calculate_upnl(
            positions_all, spot_btc=spot_btc, spot_eth=spot_eth
        )
        upnl = upnl if abs(upnl) > 0 else _calc_upnl
        used_pct_ui, heat_level, heat_bar = render_margin_heatmap(bal, blocked)
        used_pct_calc, margin_drift, drift_status, drift_icon, _ = calculate_margin_drift(
            bal, blocked, MIN_MARGIN_PCT
        )
        api_score, api_status, api_bar = render_api_health_bar()
        wallet_upnl_pct = (upnl / bal * 100) if bal > 0 else 0
        blocked_upnl_pct = (upnl / blocked * 100) if blocked > 0 else 0
        API_DOWN = False
        API_RECOVERY_COOLDOWN_UNTIL = 0.0
        render_terminal_ui(
            now=datetime.now(),
            spot=spot,
            decision="NO TRADE",
            source="LIVE — connected",
            bal=bal,
            blocked=blocked,
            upnl=upnl,
            wallet_upnl_pct=wallet_upnl_pct,
            blocked_upnl_pct=blocked_upnl_pct,
            used_pct_ui=used_pct_ui,
            heat_level=heat_level,
            heat_bar=heat_bar,
            delta=0,
            gamma=0,
            position_details=position_details,
            position_count=position_count,
            execution_status="CONNECTED — starting main loop",
            used_pct_calc=used_pct_calc,
            margin_drift=margin_drift,
            drift_status=drift_status,
            drift_icon=drift_icon,
            api_score=api_score,
            api_status=api_status,
            api_bar=api_bar,
            expiry_oi_list=[],
            expiry_oi_list_secondary=[],
            spot_secondary=None,
            symbol_secondary=None,
            symbol_primary=SYMBOL,
            all_expiry_max_pain_primary=None,
            all_expiry_max_pain_secondary=None,
            projected_profit=None,
            max_loss=None,
            position_delta_sum=None,
            position_gamma_sum=None,
            position_theta_sum=None,
            position_vega_sum=None,
            position_rho_sum=None,
            strike_order_ok=None,
            strike_order_msg=None,
            option_metrics=None,
            last_executed_signal=LAST_EXECUTED_SIGNAL,
            **build_price_change_ui_kwargs(
                symbol_primary=SYMBOL, spot_primary=spot, update_state=False
            ),
        )
        FIRST_UI_RENDER_DONE = True
        print("✅ Live dashboard painted (wallet/positions connected)\n", flush=True)
        return True
    except Exception as e:
        print(f"⚠️ Bootstrap dashboard skipped: {e}\n", flush=True)
        return False


def place_order(symbol, side, size, margin_mode=None, reason=None):
    """
    Places a market order on Delta Exchange.
    - symbol: Target contract symbol (options or futures perp).
    - side: "sell" or "buy".
    - size: Order quantity.
    - margin_mode: isolated, cross, or portfolio.
    - reason: Mandatory string explaining why the order is placed.
    """
    global ORDER_FAILURE_COOLDOWN_UNTIL, LAST_ORDER_ERROR
    LAST_ORDER_ERROR = ""
    
    if not USER_AUTO_EXECUTION:
        LAST_ORDER_ERROR = "AUTO_EXECUTION_OFF"
        return None
    if KILL_SWITCH:
        LAST_ORDER_ERROR = "KILL_SWITCH_ACTIVE"
        return None
    if size <= 0:
        LAST_ORDER_ERROR = "INVALID_SIZE"
        return None

    _open_reasons = ("NEW_POSITION", "ADD_MISSING_LEG", "LOW_BALANCE_BIAS_ALIGN", "BIAS_CHANGE_SHORT_SWAP", "BIAS_CHANGE_BUILD", "BIAS_CHANGE_LONG_ROLL", "NEW_POSITION_TOPUP")
    if reason and str(reason).strip() in _open_reasons and 0 < size < MIN_POSITION_CONTRACTS:
        size = MIN_POSITION_CONTRACTS

    _opening_reasons_ui_gate = (
        "NEW_POSITION", "ADD_MISSING_LEG", "LOW_BALANCE_BIAS_ALIGN",
        "BIAS_CHANGE_SHORT_SWAP", "BIAS_CHANGE_BUILD", "BIAS_CHANGE_LONG_ROLL",
        "NEW_POSITION_TOPUP", "EQUALITY", "MARGIN_ENFORCE", "MIN_1_POSITION_LOW_BALANCE",
        "OPENSTRIKE_ROLL_CALL", "OPENSTRIKE_ROLL_PUT",
    )
    if not FIRST_UI_RENDER_DONE and (not reason or str(reason).strip() in _opening_reasons_ui_gate):
        LAST_ORDER_ERROR = "FIRST_RENDER_NOT_DONE"
        return None

    _open_reasons_block = ("NEW_POSITION", "ADD_MISSING_LEG", "LOW_BALANCE_BIAS_ALIGN", "BIAS_CHANGE_SHORT_SWAP", "BIAS_CHANGE_BUILD", "BIAS_CHANGE_LONG_ROLL", "NEW_POSITION_TOPUP", "EQUALITY", "MARGIN_ENFORCE", "MIN_1_POSITION_LOW_BALANCE")
    if reason and str(reason).strip() in _open_reasons_block and time.time() < ORDER_FAILURE_COOLDOWN_UNTIL:
        LAST_ORDER_ERROR = "COOLDOWN_ACTIVE"
        return None
    if not reason or not str(reason).strip():
        send_telegram(
            f"⚠️ ORDER BLOCKED — No reason provided\n"
            f"Symbol: {symbol} Side: {side} Size: {size}\n"
            f"Rule: Order cannot be placed without a reason.\n"
            f"Time: {datetime.now().strftime('%H:%M:%S')}"
        )
        LAST_ORDER_ERROR = "MISSING_REASON"
        return None
    if margin_mode is None:
        margin_mode = MARGIN_MODE
    margin_mode = margin_mode.lower()
    if _is_symbol_expired(symbol):
        LAST_ORDER_ERROR = "CONTRACT_EXPIRED"
        return None
    body = {
        "product_symbol": symbol,
        "size": size,
        "side": side,
        "order_type": "market_order",
        "margin_mode": margin_mode
    }

    try:
        start = time.time()
        res = private_request("POST", "/v2/orders", body)

        latency = int((time.time() - start) * 1000)
        API_LATENCY["ORDERS"] = latency
        api_recovered("ORDERS")

        msg = (
            f"✅ ORDER PLACED\n"
            f"Symbol : {symbol}\n"
            f"Side   : {side.upper()}\n"
            f"Size   : {size}\n"
            f"Time   : {datetime.now().strftime('%H:%M:%S')}"
        )
        if reason:
            msg += f"\nReason : {reason}"
        send_telegram(msg)
        ORDER_FAILURE_COOLDOWN_UNTIL = 0.0

        return res

    except Exception as e:
        api_failure_alert("ORDERS", e)

        _open_reasons_cooldown = ("NEW_POSITION", "ADD_MISSING_LEG", "LOW_BALANCE_BIAS_ALIGN", "BIAS_CHANGE_SHORT_SWAP", "BIAS_CHANGE_BUILD", "BIAS_CHANGE_LONG_ROLL", "NEW_POSITION_TOPUP", "EQUALITY", "MARGIN_ENFORCE", "MIN_1_POSITION_LOW_BALANCE")
        if reason and str(reason).strip() in _open_reasons_cooldown:
            ORDER_FAILURE_COOLDOWN_UNTIL = time.time() + ORDER_FAILURE_COOLDOWN_SEC

        err_str = str(e).lower()
        err_msg = str(e)
        if hasattr(e, "response") and e.response is not None:
            try:
                err_msg = e.response.text
            except Exception:
                pass
        LAST_ORDER_ERROR = err_msg

        if (reason == "EQUALITY" and "400" in str(e) and
            ("insufficient_margin" in err_str or "invalid_contract" in err_str)):
            global EQUALITY_SUSPENDED, EQUALITY_SUSPENDED_UNTIL
            EQUALITY_SUSPENDED = True
            EQUALITY_SUSPENDED_UNTIL = time.time() + 600
            send_telegram(
                f"🛑 EQUALITY SUSPENDED (10 min)\n"
                f"Reason: {str(e)[:150]}\n"
                f"Equality job is suspended for 10 min to save funds.\n"
                f"Time: {datetime.now().strftime('%H:%M:%S')}"
            )

        send_telegram(
            f"❌ ORDER REJECTED\n"
            f"Symbol : {symbol}\n"
            f"Side   : {side.upper()}\n"
            f"Size   : {size}\n"
            f"Time   : {datetime.now().strftime('%H:%M:%S')}\n"
            f"Reason : {err_msg[:200]}"
        )

        return None

def orders_api_health_check():
    last_err = None
    for attempt in range(API_RETRY_COUNT):
        try:
            start = time.time()
            private_request("GET", "/v2/orders", params={"page_size": 1})
            latency = int((time.time() - start) * 1000)
            API_LATENCY["ORDERS"] = latency
            api_recovered("ORDERS")
            return True
        except Exception as e:
            last_err = e
            if attempt < API_RETRY_COUNT - 1:
                time.sleep(API_RETRY_DELAY_SEC)
    api_failure_alert("ORDERS", last_err)
    return False

def get_spot(symbol=None):
    """
    Fetches the current spot price for the given symbol (BTC or ETH).
    """
    sym = symbol if symbol is not None else SYMBOL
    last_err = None
    for attempt in range(API_RETRY_COUNT):
        try:
            start = time.time()
            r = http_get(
                f"{BASE_URL}/v2/tickers/{sym}USD",
                timeout=3
            )
            latency = int((time.time() - start) * 1000)
            API_LATENCY["SPOT"] = latency
            price = float(r.json()["result"]["mark_price"])
            api_recovered("SPOT")
            return price
        except Exception as e:
            last_err = e
            if attempt < API_RETRY_COUNT - 1:
                time.sleep(API_RETRY_DELAY_SEC)
    print("❌ SPOT FETCH FAILED (after retries):", last_err)
    api_failure_alert("SPOT", last_err)
    return 0

ALL_TICKERS_CACHE_SEC = 10.0
ALL_TICKERS_TOTAL_TIMEOUT_SEC = 12.0
LAST_ALL_TICKERS = None
LAST_ALL_TICKERS_AT = 0.0
LAST_ALL_TICKERS_FAILURE_AT = 0.0
ALL_TICKERS_FAILURE_COOLDOWN_SEC = 3.0
ALL_TICKERS_LOCK = threading.Lock()

STRADDLE_HISTORY = {}  # key: symbol, value: deque of (timestamp, price, oi)

def _update_straddle_history(tickers):
    global STRADDLE_HISTORY
    now = time.time()
    for t in tickers:
        sym = t.get("symbol", "")
        if sym.startswith("MV-"):
            price = safe_float(t.get("mark_price"))
            oi = safe_float(t.get("oi_value_usd"))
            if price > 0 or oi > 0:
                if sym not in STRADDLE_HISTORY:
                    STRADDLE_HISTORY[sym] = deque(maxlen=720)  # max 2 hours at 10s intervals
                STRADDLE_HISTORY[sym].append((now, price, oi))

def analyze_straddle_sentiment(symbol):
    global STRADDLE_HISTORY
    if symbol not in STRADDLE_HISTORY or len(STRADDLE_HISTORY[symbol]) < 2:
        return None
    history = STRADDLE_HISTORY[symbol]
    curr_time, curr_price, curr_oi = history[-1]
    
    # We look for a comparison point around 15 minutes ago
    target_time_ago = curr_time - 900
    comp_item = history[0]
    for item in reversed(history):
        if item[0] <= target_time_ago:
            comp_item = item
            break
            
    comp_time, comp_price, comp_oi = comp_item
    time_diff_min = (curr_time - comp_time) / 60.0
    if time_diff_min <= 0.1:  # Skip if difference is too small/recent
        return None
        
    price_change_pct = ((curr_price - comp_price) / comp_price * 100.0) if comp_price > 0 else 0.0
    oi_change_pct = ((curr_oi - comp_oi) / comp_oi * 100.0) if comp_oi > 0 else 0.0
    
    # Sentiment classification based on Price & OI Changes:
    # Price Up + OI Up -> Buy Straddle (Aggressive Buying)
    # Price Down + OI Up -> Short Straddle (Aggressive Selling/Writing)
    # Price Up + OI Down -> Short Covering
    # Price Down + OI Down -> Long Unwinding
    oi_threshold = 0.05
    price_threshold = 0.05
    
    if abs(oi_change_pct) < oi_threshold and abs(price_change_pct) < price_threshold:
        sentiment = "NEUTRAL"
        color_code = "\033[0m"
    elif price_change_pct >= 0 and oi_change_pct >= 0:
        sentiment = "BUY STRADDLE (Long Vol)"
        color_code = "\033[1;92m" # Green
    elif price_change_pct < 0 and oi_change_pct >= 0:
        sentiment = "SHORT STRADDLE (Short Vol)"
        color_code = "\033[1;91m" # Red
    elif price_change_pct >= 0 and oi_change_pct < 0:
        sentiment = "SHORT COVERING"
        color_code = "\033[1;93m" # Yellow
    else:
        sentiment = "LONG UNWINDING"
        color_code = "\033[1;95m" # Purple/Magenta
        
    return {
        "current_price": curr_price,
        "current_oi": curr_oi,
        "price_change_pct": price_change_pct,
        "oi_change_pct": oi_change_pct,
        "sentiment": sentiment,
        "color_code": color_code,
        "time_diff_min": time_diff_min
    }


def _fetch_json_with_total_timeout(url, connect_timeout=6.0, read_timeout=6.0, total_timeout=ALL_TICKERS_TOTAL_TIMEOUT_SEC):
    started = time.monotonic()
    with http_get(url, timeout=(connect_timeout, read_timeout), stream=True) as r:
        r.raise_for_status()
        chunks = []
        for chunk in r.iter_content(chunk_size=512 * 1024):
            if time.monotonic() - started > total_timeout:
                raise requests.Timeout(f"Total timeout {total_timeout:.0f}s exceeded for {url}")
            if chunk:
                chunks.append(chunk)
        if time.monotonic() - started > total_timeout:
            raise requests.Timeout(f"Total timeout {total_timeout:.0f}s exceeded for {url}")
    return json.loads(b"".join(chunks))

def fetch_all_tickers(refresh=False):
    """
    Fetches ticker info for all contracts from the Delta Exchange ticker API.
    """

    global LAST_ALL_TICKERS, LAST_ALL_TICKERS_AT, LAST_ALL_TICKERS_FAILURE_AT
    now_ts = time.time()
    if (
        not refresh
        and LAST_ALL_TICKERS is not None
        and (now_ts - LAST_ALL_TICKERS_AT) < ALL_TICKERS_CACHE_SEC
    ):
        return LAST_ALL_TICKERS
    if (
        LAST_ALL_TICKERS is None
        and (now_ts - LAST_ALL_TICKERS_FAILURE_AT) < ALL_TICKERS_FAILURE_COOLDOWN_SEC
    ):
        return []
    with ALL_TICKERS_LOCK:
        now_ts = time.time()
        if (
            not refresh
            and LAST_ALL_TICKERS is not None
            and (now_ts - LAST_ALL_TICKERS_AT) < ALL_TICKERS_CACHE_SEC
        ):
            return LAST_ALL_TICKERS
        if (
            LAST_ALL_TICKERS is None
            and (now_ts - LAST_ALL_TICKERS_FAILURE_AT) < ALL_TICKERS_FAILURE_COOLDOWN_SEC
        ):
            return []
        try:
            payload = _fetch_json_with_total_timeout(f"{BASE_URL}/v2/tickers")
            result = payload.get("result", [])
            LAST_ALL_TICKERS = result if isinstance(result, list) else []
            LAST_ALL_TICKERS_AT = time.time()
            LAST_ALL_TICKERS_FAILURE_AT = 0.0
            api_recovered("SPOT")
            _update_straddle_history(LAST_ALL_TICKERS)
            return LAST_ALL_TICKERS
        except Exception as e:
            LAST_ALL_TICKERS_FAILURE_AT = time.time()
            api_failure_alert("SPOT", e)
            return LAST_ALL_TICKERS or []

def _extract_symbol_spot_from_tickers(tickers, sym):
    target_symbol = f"{sym}USD"
    for t in tickers:
        if str(t.get("symbol") or "") != target_symbol:
            continue
        for key in ("spot_price", "mark_price", "close"):
            try:
                px = float(t.get(key, 0) or 0)
            except (ValueError, TypeError):
                px = 0.0
            if px > 0:
                return px
    for t in tickers:
        if t.get("contract_type") != "perpetual_futures":
            continue
        if str(t.get("underlying_asset_symbol") or "").upper() != sym:
            continue
        for key in ("spot_price", "mark_price", "close"):
            try:
                px = float(t.get(key, 0) or 0)
            except (ValueError, TypeError):
                px = 0.0
            if px > 0:
                return px
    return 0.0

def _quick_option_oi_totals_by_symbol(timeout=8):
    try:
        result = fetch_all_tickers(refresh=True)
        totals = {
            "BTC": {"usd": 0.0, "contracts": 0.0},
            "ETH": {"usd": 0.0, "contracts": 0.0},
        }
        for t in result:
            if t.get("contract_type") not in ("call_options", "put_options"):
                continue
            parts = str(t.get("symbol") or "").split("-")
            if len(parts) < 2:
                continue
            inst = parts[1].upper()
            if inst not in totals:
                continue
            try:
                totals[inst]["usd"] += float(t.get("oi_value_usd", 0) or 0)
            except (ValueError, TypeError):
                pass
            try:
                totals[inst]["contracts"] += float(t.get("oi", 0) or 0)
            except (ValueError, TypeError):
                pass
        return totals
    except Exception as e:
        api_failure_alert("SPOT", e)
        return None

def _pick_main_symbol_by_quick_oi(default_symbol=None, timeout=8):
    fallback = default_symbol if default_symbol in ("BTC", "ETH") else SYMBOL
    totals = _quick_option_oi_totals_by_symbol(timeout=timeout)
    if not totals:
        return fallback
    metric = "contracts" if MAIN_SYMBOL_OI_BY == "contracts" else "usd"
    total_oi_btc = float(totals.get("BTC", {}).get(metric, 0) or 0)
    total_oi_eth = float(totals.get("ETH", {}).get(metric, 0) or 0)
    return "BTC" if total_oi_btc >= total_oi_eth else "ETH"

def extract_expiry(symbol):
    try:
        return datetime.strptime(symbol.split("-")[-1], "%d%m%y")
    except:
        return None

def _is_symbol_expired(symbol):
    """Return True if the contract symbol has already expired (past 12:00 UTC on expiry day)."""
    if not symbol:
        return True
    exp = extract_expiry(symbol)
    if exp is None:
        return False          # perpetual / unknown format — not expired
    exact_expiry = datetime(exp.year, exp.month, exp.day, 12, 0, 0)
    return datetime.now(timezone.utc).replace(tzinfo=None) >= exact_expiry

def _norm_cdf(x):
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))

def estimate_iv_bs(spot, strike, expiry, mark, is_call, r=0.0):
    if spot <= 0 or strike <= 0 or mark <= 0:
        return None
    try:
        if hasattr(expiry, "date"):
            t = (expiry - datetime.now()).total_seconds() / (365.25 * 24 * 3600)
        else:
            t = (expiry - datetime.now()).total_seconds() / (365.25 * 24 * 3600)
    except Exception:
        return None
    if t <= 0:
        t = 1.0 / 365.0
    def bs_price(sig):
        if sig <= 0:
            return 0.0
        sqrt_t = math.sqrt(t)
        d1 = (math.log(spot / strike) + (r + 0.5 * sig * sig) * t) / (sig * sqrt_t)
        d2 = d1 - sig * sqrt_t
        if is_call:
            return spot * _norm_cdf(d1) - strike * math.exp(-r * t) * _norm_cdf(d2)
        else:
            return strike * math.exp(-r * t) * _norm_cdf(-d2) - spot * _norm_cdf(-d1)
    lo, hi = 0.01, 4.0
    for _ in range(50):
        mid = (lo + hi) * 0.5
        p = bs_price(mid)
        if abs(p - mark) < 0.01:
            return mid
        if p < mark:
            lo = mid
        else:
            hi = mid
    return round((lo + hi) * 0.5, 4)

def fetch_options(symbol=None, include_spot=False):
    """
    Fetches list of active option contracts and their current market data.
    """

    sym = symbol if symbol is not None else SYMBOL
    try:
        result = fetch_all_tickers(refresh=False)
        spot = _extract_symbol_spot_from_tickers(result, sym)
        if spot <= 0:
            spot = get_spot(sym)
        opts = []
        for t in result:
            if t.get("contract_type") not in ("call_options", "put_options"):
                continue
            if sym not in t.get("symbol", ""):
                continue
            expiry = extract_expiry(t["symbol"])
            if not expiry:
                continue
            try:
                exact_expiry = datetime(expiry.year, expiry.month, expiry.day, 12, 0, 0)
                if datetime.now(timezone.utc).replace(tzinfo=None) >= exact_expiry:
                    continue
            except Exception:
                pass

            greeks = t.get("greeks") or {}
            raw_delta = safe_float(greeks.get("delta"))
            raw_theta = safe_float(greeks.get("theta"))

            iv_val = (
                t.get("iv") or t.get("implied_volatility") or t.get("volatility")
                or greeks.get("iv") or greeks.get("implied_volatility")
            )
            if iv_val is not None:
                v = safe_float(iv_val)
                iv_val = v * 100 if v <= 1 else v
            else:
                strike = safe_float(t.get("strike_price"))
                mark = safe_float(t.get("mark_price"))
                is_call = t.get("contract_type") == "call_options"
                if spot > 0 and strike > 0 and mark > 0:
                    iv_dec = estimate_iv_bs(spot, strike, expiry, mark, is_call)
                    iv_val = round(iv_dec * 100, 2) if iv_dec is not None else None
                else:
                    iv_val = None
            vol = t.get("volume") or t.get("volume_24h") or t.get("turnover")
            vol = int(vol) if vol is not None else None
            opts.append({
                "symbol": t["symbol"],
                "type": "call" if t["contract_type"] == "call_options" else "put",
                "strike": safe_float(t.get("strike_price")),
                "expiry": expiry,
                "oi": safe_float(t.get("oi_value_usd")),
                "oi_contracts": safe_float(t.get("oi")),
                "delta": abs(raw_delta),
                "gamma": abs(safe_float(greeks.get("gamma"))),
                "theta": raw_theta,
                "vega": abs(safe_float(greeks.get("vega"))),
                "rho": safe_float(greeks.get("rho")),
                "mark_price": safe_float(t.get("mark_price")),
                "bid": safe_float((t.get("quotes") or {}).get("best_bid") or t.get("best_bid") or t.get("bid")),
                "ask": safe_float((t.get("quotes") or {}).get("best_ask") or t.get("best_ask") or t.get("ask")),
                "iv_pct": iv_val,
                "volume": vol,
            })

        return (opts, spot) if include_spot else opts

    except Exception as e:
        api_failure_alert("SPOT", e)
        return ([], 0.0) if include_spot else []

def get_option_metrics(opt, spot):
    if not opt or spot <= 0:
        return None
    strike = float(opt.get("strike", 0))
    is_call = (opt.get("type") or "").lower() == "call"
    mark = float(opt.get("mark_price", 0))
    if is_call:
        intrinsic = max(0.0, spot - strike)
    else:
        intrinsic = max(0.0, strike - spot)
    time_value = max(0.0, mark - intrinsic)
    expiry = opt.get("expiry")
    if hasattr(expiry, "date"):
        dte = (expiry.date() - datetime.now().date()).days
    else:
        try:
            dte = (expiry - datetime.now().date()).days
        except Exception:
            dte = None
    return {
        "ask": float(opt.get("ask", 0)),
        "bid": float(opt.get("bid", 0)),
        "theor": mark,
        "intrinsic": intrinsic,
        "time_value": time_value,
        "iv_pct": opt.get("iv_pct"),
        "volume": opt.get("volume"),
        "dte": dte,
        "delta": float(opt.get("delta", 0)),
        "gamma": float(opt.get("gamma", 0)),
        "vega": float(opt.get("vega", 0)),
        "theta": float(opt.get("theta", 0)),
        "rho": float(opt.get("rho", 0)),
        "symbol": opt.get("symbol", ""),
    }

def portfolio_theor_intrinsic_tv_iv(positions, opts_all, spot):
    try:
        tickers = fetch_all_tickers(refresh=False)
    except Exception:
        tickers = []
    by_sym = {t["symbol"]: t for t in tickers if t.get("symbol")}
    theor_usd = 0.0
    intrinsic_usd = 0.0
    iv_sum = 0.0
    iv_weight = 0.0
    for pos in positions:
        sym = pos.get("product_symbol", "")
        if not (sym.startswith("C-") or sym.startswith("P-") or sym.startswith("MV-")):
            continue
        try:
            size = float(pos.get("size", 0))
            if size == 0:
                continue
        except (ValueError, TypeError):
            continue
        opt = by_sym.get(sym)
        if not opt:
            continue
        mark = float(opt.get("mark_price", 0))

        strike = float(opt.get("strike_price") or opt.get("strike") or 0.0)
        if sym.startswith("MV-"):
            if strike > 0:
                intr = abs(spot - strike)
            else:
                intr = 0.0
        else:
            is_call = sym.startswith("C-")
            if is_call:
                intr = max(0.0, spot - strike)
            else:
                intr = max(0.0, strike - spot)

        mult = 0.001 if "BTC" in sym else (0.01 if "ETH" in sym else 0.001)
        theor_usd += mark * size * mult
        intrinsic_usd += intr * size * mult

        greeks = opt.get("greeks") or {}
        iv_raw = (
            opt.get("iv") or opt.get("implied_volatility") or opt.get("volatility")
            or greeks.get("iv") or greeks.get("implied_volatility")
            or (opt.get("quotes") or {}).get("mark_iv") or opt.get("mark_iv")
        )
        if iv_raw is not None:
            try:
                iv = float(iv_raw)
                if iv > 0:
                    if iv <= 1.0:
                        iv = iv * 100.0
                    iv_sum += iv * abs(size)
                    iv_weight += abs(size)
            except (ValueError, TypeError):
                pass

    time_value_usd = theor_usd - intrinsic_usd
    iv_avg = (iv_sum / iv_weight) if iv_weight > 0 else None
    return round(theor_usd, 2), round(intrinsic_usd, 2), round(time_value_usd, 2), round(iv_avg, 2) if iv_avg is not None else None

def split_expiries(opts):
    today = datetime.now().date()
    opts_future = []
    opts_orderable = []
    for o in opts:
        exp = o.get("expiry")
        if not exp:
            continue
        exp_date = exp.date() if hasattr(exp, "date") else exp
        if exp_date >= today:
            opts_future.append(o)
        if exp_date >= today:
            opts_orderable.append(o)
    if not opts_future:
        return [], [], []
    expiries = sorted(set(o["expiry"] for o in opts_future))

    orderable_expiries = sorted(set(o["expiry"] for o in opts_orderable)) if opts_orderable else []
    if orderable_expiries:
        near = [o for o in opts_orderable if o["expiry"] == orderable_expiries[0]]
        nxt  = [o for o in opts_orderable if len(orderable_expiries) > 1 and o["expiry"] == orderable_expiries[1]]
    else:
        near, nxt = [], []
    return near, nxt, opts_future

def get_spot_and_oi_for_symbol(sym):
    opts, spot = fetch_options(symbol=sym, include_spot=True)
    if spot <= 0:
        spot = get_spot(sym)
    total_contracts = sum(o.get("oi_contracts", 0) for o in opts)
    expiry_oi_list = []
    for exp in sorted(set(o["expiry"] for o in opts)):
        opts_exp = [o for o in opts if o["expiry"] == exp]
        c, p, pr = oi_pcr(opts_exp)
        mp = max_pain(opts_exp)
        expiry_oi_list.append((exp, c, p, pr, mp))
    if STRATEGY_MODE in ("OPENSTRIKE", "STRADDLE"):
        global OPENSTRIKE_CALL_OPT, OPENSTRIKE_PUT_OPT, OPENSTRIKE_TARGET_STRIKE
        global STRADDLE_TARGET_CONTRACT, STRADDLE_VOLUME_TARGET, STRADDLE_OI_TARGET

        calls = [o for o in opts if o.get("type") == "call"]
        puts = [o for o in opts if o.get("type") == "put"]

        calls_by_oi = sorted(calls, key=lambda x: float(x.get("oi", 0) or 0), reverse=True)
        puts_by_oi = sorted(puts, key=lambda x: float(x.get("oi", 0) or 0), reverse=True)

        calls_by_vol = sorted(calls, key=lambda x: float(x.get("volume") or x.get("turnover") or 0), reverse=True)
        puts_by_vol = sorted(puts, key=lambda x: float(x.get("volume") or x.get("turnover") or 0), reverse=True)

        target = OPENSTRIKE_TARGET_STRIKE
        rank_idx = get_rank_index(target)
        if rank_idx is not None:
            hc = calls_by_oi[min(rank_idx, len(calls_by_oi) - 1)] if calls_by_oi else None
            hp = puts_by_oi[min(rank_idx, len(puts_by_oi) - 1)] if puts_by_oi else None
        elif target == "highest_volume":
            hc = calls_by_vol[0] if calls_by_vol else None
            hp = puts_by_vol[0] if puts_by_vol else None
        elif target == "vol_oi":
            calls_by_vol_rank = {c["symbol"]: i for i, c in enumerate(calls_by_vol)}
            calls_by_oi_rank = {c["symbol"]: i for i, c in enumerate(calls_by_oi)}
            calls_fused = sorted(calls, key=lambda x: calls_by_vol_rank.get(x["symbol"], 999) + calls_by_oi_rank.get(x["symbol"], 999))
            hc = calls_fused[0] if calls_fused else None

            puts_by_vol_rank = {p["symbol"]: i for i, p in enumerate(puts_by_vol)}
            puts_by_oi_rank = {p["symbol"]: i for i, p in enumerate(puts_by_oi)}
            puts_fused = sorted(puts, key=lambda x: puts_by_vol_rank.get(x["symbol"], 999) + puts_by_oi_rank.get(x["symbol"], 999))
            hp = puts_fused[0] if puts_fused else None
        elif target == "atm":
            hc = select_atm_oi_option(calls, spot)
            hp = select_atm_oi_option(puts, spot)
        else:
            hc = calls_by_oi[0] if calls_by_oi else None
            hp = puts_by_oi[0] if puts_by_oi else None

        if sym == SYMBOL:
            OPENSTRIKE_CALL_OPT = hc
            OPENSTRIKE_PUT_OPT = hp

            try:
                tickers = fetch_all_tickers(refresh=False)
                mv_list = []
                prefix = f"MV-{SYMBOL}-"
                for t in tickers:
                    sym_name = t.get("symbol", "")
                    if sym_name.startswith(prefix):
                        mv_list.append({
                            "symbol": sym_name,
                            "price": safe_float(t.get("mark_price")),
                            "turnover": safe_float(t.get("turnover")),
                            "oi": safe_float(t.get("oi_value_usd")),
                        })

                if mv_list:
                    mv_by_vol = sorted(mv_list, key=lambda x: x["turnover"], reverse=True)
                    STRADDLE_VOLUME_TARGET = mv_by_vol[0] if mv_by_vol else None

                    mv_by_oi = sorted(mv_list, key=lambda x: x["oi"], reverse=True)
                    STRADDLE_OI_TARGET = mv_by_oi[0] if mv_by_oi else None

                    if OPENSTRIKE_TARGET_STRIKE == "highest_volume":
                        STRADDLE_TARGET_CONTRACT = STRADDLE_VOLUME_TARGET
                    elif OPENSTRIKE_TARGET_STRIKE == "vol_oi":
                        vol_ranks = {item["symbol"]: i for i, item in enumerate(mv_by_vol)}
                        oi_ranks = {item["symbol"]: i for i, item in enumerate(mv_by_oi)}
                        mv_fused = sorted(mv_list, key=lambda x: vol_ranks.get(x["symbol"], 999) + oi_ranks.get(x["symbol"], 999))
                        STRADDLE_TARGET_CONTRACT = mv_fused[0] if mv_fused else None
                    else:
                        STRADDLE_TARGET_CONTRACT = STRADDLE_OI_TARGET
                else:
                    STRADDLE_VOLUME_TARGET = None
                    STRADDLE_OI_TARGET = None
                    STRADDLE_TARGET_CONTRACT = None
            except Exception:
                STRADDLE_VOLUME_TARGET = None
                STRADDLE_OI_TARGET = None
                STRADDLE_TARGET_CONTRACT = None

        _hc_strike = float(hc.get("strike", 0)) if hc else None
        _hp_strike = float(hp.get("strike", 0)) if hp else None

        _all_strikes = sorted(set(float(o.get("strike", 0)) for o in opts if o.get("strike")), reverse=True)
        _atm_strike  = min(_all_strikes, key=lambda s: abs(s - spot)) if spot > 0 and _all_strikes else None

        def _best_at(strike, opt_type):
            cands = [o for o in opts if o.get("type") == opt_type and float(o.get("strike", 0)) == strike]
            return max(cands, key=lambda o: float(o.get("oi", 0) or 0), default=None) if cands else None

        straddle_strikes = set()
        for tgt in (STRADDLE_VOLUME_TARGET, STRADDLE_OI_TARGET):
            if tgt and tgt.get("symbol"):
                parts = tgt["symbol"].split("-")
                if len(parts) >= 3:
                    try:
                        straddle_strikes.add(float(parts[2]))
                    except ValueError:
                        pass

        if _atm_strike is not None:
            _upper_all = [s for s in _all_strikes if s > _atm_strike]
            _lower_all = [s for s in _all_strikes if s < _atm_strike]

            def _get_call_oi(strike):
                o = _best_at(strike, "call")
                return float(o.get("oi", 0)) if o else 0.0

            def _get_put_oi(strike):
                o = _best_at(strike, "put")
                return float(o.get("oi", 0)) if o else 0.0

            _atm_call_oi = _get_call_oi(_atm_strike)
            _atm_put_oi = _get_put_oi(_atm_strike)

            _upper_filtered = [s for s in _upper_all if _get_call_oi(s) >= _atm_call_oi]
            _lower_filtered = [s for s in _lower_all if _get_put_oi(s) >= _atm_put_oi]

            _upper_by_oi = sorted(_upper_filtered, key=lambda s: (_get_call_oi(s), s), reverse=True)
            _lower_by_oi = sorted(_lower_filtered, key=lambda s: (_get_put_oi(s), -s), reverse=True)

            # Show all available strikes passing the checkpoint
            _N = min(len(_upper_by_oi), len(_lower_by_oi))
            _upper_selected = set(_upper_by_oi[:_N])
            _lower_selected = set(_lower_by_oi[:_N])

            if _hc_strike:
                if _hc_strike > _atm_strike:
                    _upper_selected.add(_hc_strike)
                elif _hc_strike < _atm_strike:
                    _lower_selected.add(_hc_strike)
            if _hp_strike:
                if _hp_strike > _atm_strike:
                    _upper_selected.add(_hp_strike)
                elif _hp_strike < _atm_strike:
                    _lower_selected.add(_hp_strike)

            for s in straddle_strikes:
                if s > _atm_strike:
                    _upper_selected.add(s)
                elif s < _atm_strike:
                    _lower_selected.add(s)

            # Align both sides to have equal size by padding from remaining available strikes
            _final_N = max(len(_upper_selected), len(_lower_selected))
            while len(_upper_selected) < _final_N and len(_upper_selected) < len(_upper_by_oi):
                for s in _upper_by_oi:
                    if s not in _upper_selected:
                        _upper_selected.add(s)
                        break
            while len(_lower_selected) < _final_N and len(_lower_selected) < len(_lower_by_oi):
                for s in _lower_by_oi:
                    if s not in _lower_selected:
                        _lower_selected.add(s)
                        break

            # If still unequal due to list limits, truncate to equal sizes
            _final_N = min(len(_upper_selected), len(_lower_selected))
            _upper_sorted = sorted(_upper_selected, key=lambda s: (_get_call_oi(s), s), reverse=True)[:_final_N]
            _lower_sorted = sorted(_lower_selected, key=lambda s: (_get_put_oi(s), -s), reverse=False)
            # Re-align _lower_sorted size if it changed due to truncation
            _lower_sorted = sorted(_lower_sorted, key=lambda s: (_get_put_oi(s), -s), reverse=True)[:_final_N]
            # Convert _lower_sorted back to the desired output format (ascending by Put OI for table display)
            _lower_sorted = sorted(_lower_sorted, key=lambda s: (_get_put_oi(s), -s), reverse=False)

            _table_strikes = _upper_sorted + [_atm_strike] + _lower_sorted
        else:
            _table_strikes = []

        strike_table = []
        for _s in _table_strikes:
            _co = _best_at(_s, "call")
            _po = _best_at(_s, "put")
            strike_table.append({
                "strike":      _s,
                "call_oi":     float(_co.get("oi", 0)) if _co else 0.0,
                "put_oi":      float(_po.get("oi", 0)) if _po else 0.0,
                "call_expiry": _co.get("expiry") if _co else None,
                "put_expiry":  _po.get("expiry") if _po else None,
                "is_atm":      (_s == _atm_strike),
                "is_max_call": (_s == _hc_strike),
                "is_max_put":  (_s == _hp_strike),
                "is_straddle": (_s in straddle_strikes),
            })
        expiry_oi_list.append(("OPENSTRIKE_MSG", 0, 0, hc, hp, strike_table, [len(calls_by_oi), len(puts_by_oi)], spot))
    mp_all = max_pain(opts)
    return spot, expiry_oi_list, mp_all, total_contracts

def get_decision_for_symbol(sym):
    try:
        _, expiry_oi_list, _, _ = get_spot_and_oi_for_symbol(sym)
    except Exception:
        return ("NO TRADE", "NO OI")
    if not expiry_oi_list:
        return ("NO TRADE", "NO OI")
    el = sorted([i for i in expiry_oi_list if i[0] != "OPENSTRIKE_MSG"], key=lambda i: i[0])
    pcr_n = el[0][3] if len(el) >= 1 else 0
    pcr_x = el[1][3] if len(el) >= 2 else 0
    ca = sum(i[1] for i in el)
    pa = sum(i[2] for i in el)
    pcr_a = round(pa / ca, 2) if ca else 0
    max_oi_row = max(el, key=lambda i: (i[1] or 0) + (i[2] or 0)) if el else (None, 0, 0, 0, None)
    ca_max = max_oi_row[1] if len(max_oi_row) >= 2 else 0
    pa_max = max_oi_row[2] if len(max_oi_row) >= 3 else 0
    return decide(pcr_n, pcr_x, pcr_a, ca, pa, ca_max, pa_max)

def resolve_openstrike_order_opt(target_opt, all_opts):
    if target_opt is None or not all_opts:
        return None

    opt_type = target_opt.get("type", "").lower()
    target_strike = float(target_opt.get("strike", 0) or 0)
    target_expiry = target_opt.get("expiry")
    today = datetime.now().date()

    if all_opts:
        if target_expiry is not None:
            exact_match = [
                o for o in all_opts
                if o.get("type", "").lower() == opt_type
                and float(o.get("strike", 0) or 0) == target_strike
                and o.get("expiry") == target_expiry
            ]
            if exact_match:
                return exact_match[0]

        candidates = [
            o for o in all_opts
            if o.get("type", "").lower() == opt_type
            and float(o.get("strike", 0) or 0) == target_strike
            and hasattr(o.get("expiry"), "date")
            and o["expiry"].date() >= today
        ]
        if candidates:
            return min(candidates, key=lambda o: o["expiry"])

    # Don't fall back to an expired contract — return None so the bot
    # picks a fresh target on the next OI scan instead of retrying forever.
    target_sym = target_opt.get("symbol", "")
    if _is_symbol_expired(target_sym):
        return None
    return target_opt

def select_atm_option(opts, spot, side):
    filtered = [o for o in opts if o["type"] == side]
    if not filtered:
        return None

    atm = min(filtered, key=lambda o: abs(o["strike"] - spot))
    return atm

def select_atm_oi_option(opts, spot):
    if spot <= 0 or not opts:
        return None
    by_dist = sorted(opts, key=lambda o: abs(float(o.get("strike", 0)) - spot))
    cands = by_dist[:3]
    return max(cands, key=lambda o: float(o.get("oi", 0) or 0), default=None)

def select_delta_option(opts, side, target_delta=0.10):
    filtered = [o for o in opts if o["type"] == side]
    if not filtered:
        return None
    return min(filtered, key=lambda o: abs(o["delta"] - target_delta))

def oi_pcr(opts):
    call = sum(o["oi"] for o in opts if o["type"] == "call")
    put  = sum(o["oi"] for o in opts if o["type"] == "put")
    pcr = round(put / call, 2) if call else 0
    return call, put, pcr

def greek_avg(opts):
    if not opts:
        return 0,0,0,0
    avg = lambda k: sum(o[k] for o in opts) / len(opts)
    return avg("delta"), avg("gamma"), avg("theta"), avg("vega")

def fetch_options_for_symbol(sym):
    global SYMBOL
    orig = SYMBOL
    try:
        SYMBOL = sym
        return fetch_options() or []
    finally:
        SYMBOL = orig

def portfolio_greeks_sum(positions, opts_all):
    try:
        tickers = fetch_all_tickers(refresh=False)
    except Exception:
        tickers = []
    by_sym = {t["symbol"]: t for t in tickers if t.get("symbol")}
    sum_delta = sum_gamma = sum_theta = sum_vega = sum_rho = 0.0
    for pos in positions:
        sym = pos.get("product_symbol", "")
        if not (sym.startswith("C-") or sym.startswith("P-") or sym.startswith("MV-")):
            continue
        try:
            size = float(pos.get("size", 0))
            if size == 0:
                continue
        except (ValueError, TypeError):
            continue
        opt = by_sym.get(sym)
        if not opt:
            continue

        size_scaled = size
        greeks = opt.get("greeks") or {}

        if sym.startswith("MV-"):
            sum_delta += float(greeks.get("delta") or opt.get("delta") or 0.0) * size_scaled
            sum_gamma += float(greeks.get("gamma") or opt.get("gamma") or 0.0) * size_scaled
            sum_theta += float(greeks.get("theta") or opt.get("theta") or 0.0) * size_scaled
            sum_vega += float(greeks.get("vega") or opt.get("vega") or 0.0) * size_scaled
            sum_rho += float(greeks.get("rho") or opt.get("rho") or 0.0) * size_scaled
        else:
            d = float(greeks.get("delta") or opt.get("delta") or 0.0)
            is_call = sym.startswith("C-")
            signed_delta = abs(d) if is_call else -abs(d)

            sum_delta += signed_delta * size_scaled
            sum_gamma += float(greeks.get("gamma") or opt.get("gamma") or 0.0) * size_scaled
            sum_theta += float(greeks.get("theta") or opt.get("theta") or 0.0) * size_scaled
            sum_vega += float(greeks.get("vega") or opt.get("vega") or 0.0) * size_scaled
            sum_rho += float(greeks.get("rho") or opt.get("rho") or 0.0) * size_scaled

    if abs(sum_delta) < 1e-10: sum_delta = 0.0
    if abs(sum_gamma) < 1e-10: sum_gamma = 0.0
    if abs(sum_theta) < 1e-10: sum_theta = 0.0
    if abs(sum_vega) < 1e-10: sum_vega = 0.0
    if abs(sum_rho) < 1e-10: sum_rho = 0.0

    return round(sum_delta, 4), round(sum_gamma, 6), round(sum_theta, 4), round(sum_vega, 4), round(sum_rho, 4)

def max_pain(opts):
    strikes = sorted(set(o["strike"] for o in opts))
    pain = {}
    for s in strikes:
        loss = 0
        for o in opts:
            if o["type"] == "call":
                loss += max(0, s - o["strike"]) * o["oi"]
            else:
                loss += max(0, o["strike"] - s) * o["oi"]
        pain[s] = loss
    return min(pain, key=lambda s: pain[s]) if pain else None

def wallet_usd():
    last_err = None
    for attempt in range(API_RETRY_COUNT):
        try:
            start = time.time()
            data = private_request("GET", "/v2/wallet/balances")
            latency = int((time.time() - start) * 1000)
            API_LATENCY["WALLET"] = latency
            api_recovered("WALLET")
            for w in data:
                if w.get("asset_symbol") in ["USD", "USDT"]:
                    balance = float(w.get("balance", 0))
                    blocked = float(w.get("blocked_margin", 0))
                    upnl = float(w.get("unrealized_pnl", 0))
                    return balance, blocked, upnl
            return 0.0, 0.0, 0.0
        except Exception as e:
            last_err = e
            if attempt < API_RETRY_COUNT - 1:
                time.sleep(API_RETRY_DELAY_SEC)
    api_failure_alert("WALLET", last_err)
    return 0.0, 0.0, 0.0

def get_positions():
    """
    Fetches currently open positions from the Delta Exchange API.
    """
    global LAST_IP_WHITELIST_LOG_AT
    last_err = None
    for attempt in range(API_RETRY_COUNT):
        try:
            params = {"underlying_asset_symbol": SYMBOL}
            start = time.time()
            data = private_request("GET", "/v2/positions", params=params)
            latency = int((time.time() - start) * 1000)
            API_LATENCY["POSITIONS"] = latency
            api_recovered("POSITIONS")
            return data if isinstance(data, list) else []
        except Exception as e:
            last_err = e
            if attempt < API_RETRY_COUNT - 1:
                time.sleep(API_RETRY_DELAY_SEC)
    is_ip_wh = is_ip_whitelist_error(last_err)
    should_print = True
    if is_ip_wh:
        now = time.time()
        if now - LAST_IP_WHITELIST_LOG_AT < 60.0:
            should_print = False
        else:
            LAST_IP_WHITELIST_LOG_AT = now

    if should_print:
        print(f"❌ POSITIONS API ERROR (after {API_RETRY_COUNT} retries): {last_err}")
    api_failure_alert("POSITIONS", last_err)
    return []

def get_all_positions():
    def _fetch(sym):
        try:
            params = {"underlying_asset_symbol": sym}
            data = private_request("GET", "/v2/positions", params=params)
            return data if isinstance(data, list) else []
        except Exception:
            return []
    with ThreadPoolExecutor(max_workers=2) as ex:
        r_btc, r_eth = list(ex.map(_fetch, ["BTC", "ETH"]))
    return r_btc + r_eth

def calculate_upnl(positions, spot_btc=0.0, spot_eth=0.0):
    """
    Calculates the Unrealized Profit and Loss (UPNL) for all active positions.
    """

    total_upnl_usd = 0.0
    total_upnl_btc = 0.0
    position_count = 0
    position_details = []

    market_data = {}
    delta_map = {}
    try:
        for t in fetch_all_tickers(refresh=False):
            symbol = t.get("symbol")
            if symbol:
                market_data[symbol] = {
                    "mark_price": safe_float(t.get("mark_price")),
                    "bid": safe_float((t.get("quotes") or {}).get("best_bid") or t.get("best_bid") or t.get("bid")),
                    "ask": safe_float((t.get("quotes") or {}).get("best_ask") or t.get("best_ask") or t.get("ask")),
                }
                if t.get("contract_type") in ("call_options", "put_options"):
                    try:
                        greeks = t.get("greeks") or {}
                        raw_delta = greeks.get("delta", None)
                        if raw_delta is not None:
                            mag = abs(safe_float(raw_delta))
                            ct = str(t.get("contract_type") or "").lower()
                            signed_delta = -mag if ct == "put_options" else mag
                            delta_map[symbol] = signed_delta
                    except (ValueError, TypeError):
                        pass
    except Exception as e:
        print(f"❌ Failed to fetch market data for UPNL calculation: {e}")
        return 0.0, 0.0, 0, []

    for pos in positions:
        symbol = pos.get("product_symbol", "")

        is_option = symbol.startswith("C-") or symbol.startswith("P-")

        if is_option:
            found_upnl = False
            upnl_usd_value = 0.0

            upnl_fields = ["unrealized_pnl", "upnl", "unrealized_profit_loss", "pnl", "profit_loss",
                          "realized_pnl", "total_pnl", "mark_to_market", "mtm_pnl"]
            for field_name in upnl_fields:
                if field_name in pos and pos[field_name] is not None:
                    try:
                        upnl_usd_value = float(pos[field_name])
                        found_upnl = True
                        break
                    except (ValueError, TypeError):
                        pass

            if not found_upnl:
                entry_price = pos.get("entry_price") or pos.get("average_price")
                size = pos.get("size", 0)
                current_data = market_data.get(symbol)
                if current_data and entry_price and size:
                    try:
                        entry_price = float(entry_price)
                        size = float(size)
                        mark_price = current_data["mark_price"]

                        upnl_usd_value = (mark_price - entry_price) * size * 0.001
                        found_upnl = True
                    except (ValueError, TypeError):
                        pass

            if found_upnl:
                total_upnl_usd += upnl_usd_value
                total_upnl_btc += upnl_usd_value
                position_count += 1

                size = safe_float(pos.get("size"))
                direction = "LONG" if size > 0 else "SHORT"
                dir_letter = "L" if size > 0 else "S"
                option_type = "CALL" if symbol.startswith("C-") else "PUT"
                parts = symbol.split("-")
                instrument = parts[1] if len(parts) >= 2 else ""
                expiry_code = parts[-1] if len(parts) >= 4 else ""

                contract_id = f"{parts[0]}-{parts[2]}-{parts[3]}" if len(parts) >= 4 else symbol
                size_btc = abs(size) * 0.001
                try:
                    strike = safe_float(parts[2]) if len(parts) >= 3 else 0
                    entry = safe_float(pos.get("entry_price") or pos.get("average_price"))
                    if option_type == "CALL":
                        breakeven = strike + entry
                    else:
                        breakeven = strike - entry
                    breakeven = round(breakeven, 0) if strike else None
                except (ValueError, TypeError):
                    breakeven = None
                position_details.append({
                    "symbol": symbol,
                    "product_symbol": symbol,
                    "type": f"{direction} {option_type}",
                    "size": abs(size),
                    "size_btc": size_btc,
                    "contract_id": contract_id,
                    "dir_letter": dir_letter,
                    "upnl": upnl_usd_value,
                    "delta": delta_map.get(symbol),
                    "instrument": instrument,
                    "expiry": expiry_code,
                    "breakeven": breakeven,
                    "entry_price": pos.get("entry_price", 0),
                    "current_price": market_data.get(symbol, {}).get("mark_price", 0) if market_data.get(symbol) else 0
                })

        else:
            try:
                size = float(pos.get("size", 0))
                if size == 0:
                    continue
                entry_price = float(pos.get("entry_price") or pos.get("average_price") or 0)

                upnl_fut = 0.0
                found_fut = False
                for field_name in ["unrealized_pnl", "upnl", "unrealized_profit_loss", "pnl", "profit_loss"]:
                    if field_name in pos and pos[field_name] is not None:
                        try:
                            upnl_fut = float(pos[field_name])
                            found_fut = True
                            break
                        except (ValueError, TypeError):
                            pass
                if not found_fut:
                    mark_px = float(pos.get("mark_price") or pos.get("last_price") or 0)
                    if mark_px == 0 and market_data.get(symbol):
                        mark_px = market_data[symbol].get("mark_price") or 0.0
                    if mark_px == 0:
                        _inst = symbol.replace("USD", "").upper()
                        mark_px = spot_btc if _inst == "BTC" else (spot_eth if _inst == "ETH" else 0.0)
                    if mark_px > 0 and entry_price > 0:
                        upnl_fut = (mark_px - entry_price) * size * 0.001
                        found_fut = True
                total_upnl_usd += upnl_fut
                total_upnl_btc += upnl_fut
                position_count += 1
                direction = "LONG" if size > 0 else "SHORT"
                dir_letter = "L" if size > 0 else "S"
                mark_px_disp = mark_px if mark_px > 0 else float(pos.get("mark_price") or pos.get("last_price") or 0)
                position_details.append({
                    "symbol": symbol,
                    "product_symbol": symbol,
                    "type": f"{direction} FUTURES",
                    "size": abs(size),
                    "size_btc": abs(size) * 0.001,
                    "contract_id": symbol,
                    "dir_letter": dir_letter,
                    "upnl": upnl_fut,
                    "delta": None,
                    "instrument": symbol.replace("USD", ""),
                    "expiry": "PERP",
                    "breakeven": None,
                    "entry_price": entry_price,
                    "current_price": mark_px_disp,
                    "is_futures": True,
                })
            except (ValueError, TypeError):
                pass

    return total_upnl_usd, total_upnl_btc, position_count, position_details

def format_position_detail_for_ui(p):
    # This helper function formats a single position detail dictionary into a string.
    # IMPORTANT: Any changes made to the format here will automatically reflect in BOTH 
    # the terminal UI and the Telegram notifications (mirror reflection).
    color = "🟢" if p["upnl"] >= 0 else "🔴"
    dl = p.get("dir_letter", "L" if "LONG" in p["type"] else "S")
    inst = p.get("instrument", "BTC")
    if p.get("is_futures"):
        entry_p = float(p.get("entry_price") or 0)
        mark_p  = float(p.get("current_price") or 0)
        entry_s = f" Entry${entry_p:.0f}" if entry_p > 0 else ""
        mark_s  = f" Mark${mark_p:.0f}" if mark_p > 0 else ""
        left = f"{color} {dl} {p['contract_id']} x{int(p['size'])}{entry_s}{mark_s} PERP"
    else:
        cid = p.get("contract_id", "")
        sz_btc = p.get("size_btc", p["size"] * 0.001)
        d = p.get("delta", None)
        delta_s = f" Δ {d:.2f}" if d is not None else " Δ —"
        entry_p = float(p.get("entry_price") or 0)
        mark_p  = float(p.get("current_price") or 0)
        entry_s = f" Entry${entry_p:.1f}" if entry_p % 1 != 0 else f" Entry${entry_p:.0f}"
        mark_s  = f" Mark${mark_p:.1f}" if mark_p % 1 != 0 else f" Mark${mark_p:.0f}"
        left = f"{color} {dl} {cid} x{sz_btc:.3f} {inst}{delta_s} {entry_s}{mark_s}"
    return f"{left}  UPNL: ${p['upnl']:+.2f}"

def calculate_projected_profit(positions, spot_btc=None, spot_eth=None):
    if spot_btc is None:
        try:
            spot_btc = get_spot("BTC")
        except Exception:
            spot_btc = 0.0
    if spot_eth is None:
        try:
            spot_eth = get_spot("ETH")
        except Exception:
            spot_eth = 0.0
    mult = 0.001
    total = 0.0
    for pos in positions:
        symbol = pos.get("product_symbol", "")
        if not (symbol.startswith("C-") or symbol.startswith("P-") or symbol.startswith("MV-")):
            continue
        try:
            size = float(pos.get("size", 0))
            if size == 0:
                continue
            entry = float(pos.get("entry_price") or pos.get("average_price") or 0)
            parts = symbol.split("-")
            if len(parts) < 3:
                continue
            inst = parts[1] if len(parts) >= 2 else "BTC"
            strike = float(parts[2])
            spot = spot_btc if inst == "BTC" else spot_eth

            if symbol.startswith("MV-"):
                intrinsic = abs(spot - strike)
                total += (intrinsic - entry) * size * mult
            else:
                size_btc = abs(size) * mult
                if symbol.startswith("C-"):
                    intrinsic = max(0.0, spot - strike)
                    total += (intrinsic - entry) * size_btc * (1 if size > 0 else -1)
                else:
                    intrinsic = max(0.0, strike - spot)
                    total += (intrinsic - entry) * size_btc * (1 if size > 0 else -1)
        except (ValueError, TypeError):
            continue
    return total

def is_covered_under_10_percent_move(positions, spot_btc=None, spot_eth=None):
    if spot_btc is None:
        try:
            spot_btc = get_spot("BTC")
        except Exception:
            spot_btc = 0.0
    if spot_eth is None:
        try:
            spot_eth = get_spot("ETH")
        except Exception:
            spot_eth = 0.0

    has_any_options = False
    for pos in positions:
        symbol = pos.get("product_symbol", "")
        if symbol.startswith(("C-", "P-", "MV-")):
            has_any_options = True
            parts = symbol.split("-")
            inst = parts[1] if len(parts) >= 2 else "BTC"
            spot = spot_btc if inst == "BTC" else spot_eth
            if spot <= 0:
                continue
            _SCENARIO_MOVE_PCT = MAX_LOSS_CAP_PCT if (MAX_LOSS_CAP_PCT is not None and MAX_LOSS_CAP_PCT > 0) else 0.10
            S_min = spot * (1.0 - _SCENARIO_MOVE_PCT)
            S_max = spot * (1.0 + _SCENARIO_MOVE_PCT)
            try:
                strike = float(parts[2])
                if symbol.startswith("C-") and strike <= S_max:
                    return False
                elif symbol.startswith("P-") and strike >= S_min:
                    return False
                elif symbol.startswith("MV-"):
                    return False
            except Exception:
                pass
    return has_any_options


def calculate_max_loss(positions, spot_btc=None, spot_eth=None):
    if spot_btc is None:
        try:
            spot_btc = get_spot("BTC")
        except Exception:
            spot_btc = 0.0
    if spot_eth is None:
        try:
            spot_eth = get_spot("ETH")
        except Exception:
            spot_eth = 0.0
    mult = 0.001

    # Group positions by underlying instrument
    inst_positions = {"BTC": [], "ETH": []}
    for pos in positions:
        symbol = pos.get("product_symbol", "")
        if symbol.startswith(("C-", "P-", "MV-")):
            parts = symbol.split("-")
            inst = parts[1] if len(parts) >= 2 else "BTC"
        else:
            # Future
            clean = symbol.replace("USD", "").replace("-", "").upper()
            inst = "ETH" if "ETH" in clean else "BTC"
        if inst in inst_positions:
            inst_positions[inst].append(pos)

    total_max_loss = 0.0

    for inst, pos_list in inst_positions.items():
        if not pos_list:
            continue
        spot = spot_btc if inst == "BTC" else spot_eth
        if spot <= 0:
            continue

        _SCENARIO_MOVE_PCT = MAX_LOSS_CAP_PCT if (MAX_LOSS_CAP_PCT is not None and MAX_LOSS_CAP_PCT > 0) else 0.10

        # Collect candidate spot prices strictly within the stress movement range
        candidates = [
            0.0,
            spot,
            spot * (1.0 - _SCENARIO_MOVE_PCT),
            spot * (1.0 + _SCENARIO_MOVE_PCT),
            spot * (1.0 - _SCENARIO_MOVE_PCT * 2.0),
            spot * (1.0 + _SCENARIO_MOVE_PCT * 2.0),
            spot * 0.5,
            spot * 1.5,
            spot * 2.0,
            spot * 3.0,
        ]

        # Add strike prices that fall inside the stress interval
        for pos in pos_list:
            symbol = pos.get("product_symbol", "")
            if symbol.startswith(("C-", "P-", "MV-")):
                try:
                    parts = symbol.split("-")
                    if len(parts) >= 3:
                        strike = float(parts[2])
                        candidates.append(strike)
                except Exception:
                    pass

        # Evaluate net loss at each candidate spot price
        max_inst_loss = 0.0
        for S in set(candidates):
            if S < 0:
                continue
            inst_pnl = 0.0
            for pos in pos_list:
                symbol = pos.get("product_symbol", "")
                try:
                    size = float(pos.get("size", 0))
                    if size == 0:
                        continue
                    entry = float(pos.get("entry_price") or pos.get("average_price") or 0)
                    if symbol.startswith(("C-", "P-", "MV-")):
                        parts = symbol.split("-")
                        strike = float(parts[2])
                        if symbol.startswith("MV-"):
                            intrinsic = abs(S - strike)
                            inst_pnl += (intrinsic - entry) * size * mult
                        else:
                            size_btc = abs(size) * mult
                            if symbol.startswith("C-"):
                                intrinsic = max(0.0, S - strike)
                            else:
                                intrinsic = max(0.0, strike - S)
                            inst_pnl += (intrinsic - entry) * size_btc * (1 if size > 0 else -1)
                    else: # Future
                        size_btc = abs(size) * mult
                        if size > 0:
                            inst_pnl += (S - entry) * size_btc
                        else:
                            inst_pnl += (entry - S) * size_btc
                except Exception:
                    continue

            loss = -inst_pnl
            if loss > max_inst_loss:
                max_inst_loss = loss

        total_max_loss += max_inst_loss

    return round(total_max_loss, 2)
def square_off_position(symbol, size, reason="CLOSE_POSITION"):
    if size > 0:
        return place_order(symbol, "sell", abs(size), MARGIN_MODE.lower(), reason=reason)
    elif size < 0:
        return place_order(symbol, "buy", abs(size), MARGIN_MODE.lower(), reason=reason)
    return None

def decide(pcr_n, pcr_x, pcr_a, ca=0, pa=0, ca_max=0, pa_max=0):
    """
    OPENSTRIKE Decision Engine.
    Compares the Open Interest (OI) of the target CALL option and target PUT option.
    Note: Other parameters (pcr_n, pcr_x, etc.) are vestigial and kept for signature compatibility.
    """
    hc = OPENSTRIKE_CALL_OPT
    hp = OPENSTRIKE_PUT_OPT
    if hc is None and hp is None:
        return ("NO TRADE", "PRIMARY: OPENSTRIKE (no OI data)")
    c_oi = float(hc.get("oi", 0) or 0) if hc else 0
    p_oi = float(hp.get("oi", 0) or 0) if hp else 0
    c_strike = hc.get("strike") if hc else "?"
    p_strike = hp.get("strike") if hp else "?"
    if ORDER_TYPE == "futures":
        if c_oi > p_oi:
            return ("SELL CALL", f"PRIMARY: OPENSTRIKE (Call OI {_fmt_oi(c_oi)} > Put OI {_fmt_oi(p_oi)})")
        elif p_oi > c_oi:
            return ("SELL PUT", f"PRIMARY: OPENSTRIKE (Put OI {_fmt_oi(p_oi)} > Call OI {_fmt_oi(c_oi)})")
        else:
            return ("NO TRADE", "PRIMARY: OPENSTRIKE (Call OI = Put OI)")
    else:
        if c_oi > p_oi:
            return ("SELL CALL", f"PRIMARY: OPENSTRIKE (Call {c_strike} OI {_fmt_oi(c_oi)}, Put {p_strike} OI {_fmt_oi(p_oi)})")
        elif p_oi >= c_oi:
            return ("SELL PUT", f"PRIMARY: OPENSTRIKE (Put {p_strike} OI {_fmt_oi(p_oi)}, Call {c_strike} OI {_fmt_oi(c_oi)})")

    return "NO TRADE", "NO SIGNAL"

PREVIOUS_POSITIONS = []
POSITION_CHANGE_LOG = []
PENDING_NEW_POSITION_ALERT = False
LAST_EXPIRY_ROLL_TELEGRAM_AT = 0.0
CONSECUTIVE_ZERO_POSITION_CYCLES = 0
LAST_MAX_OI_EXPIRY_STR = None

OPENSTRIKE_CALL_OPT = None
OPENSTRIKE_PUT_OPT  = None
_saved_openstrike_pending_legs = _s.get("openstrike_pending_missing_legs", {})
if not isinstance(_saved_openstrike_pending_legs, dict):
    _saved_openstrike_pending_legs = {}
OPENSTRIKE_PENDING_MISSING_LEGS = {
    "call": {
        "symbol": str(_saved_openstrike_pending_legs.get("call", {}).get("symbol", "")),
        "strike": safe_float(_saved_openstrike_pending_legs.get("call", {}).get("strike", 0.0)),
        "reason": str(_saved_openstrike_pending_legs.get("call", {}).get("reason", "")),
        "since": safe_float(_saved_openstrike_pending_legs.get("call", {}).get("since", 0.0)),
        "fail_count": int(_saved_openstrike_pending_legs.get("call", {}).get("fail_count", 0)),
    },
    "put": {
        "symbol": str(_saved_openstrike_pending_legs.get("put", {}).get("symbol", "")),
        "strike": safe_float(_saved_openstrike_pending_legs.get("put", {}).get("strike", 0.0)),
        "reason": str(_saved_openstrike_pending_legs.get("put", {}).get("reason", "")),
        "since": safe_float(_saved_openstrike_pending_legs.get("put", {}).get("since", 0.0)),
        "fail_count": int(_saved_openstrike_pending_legs.get("put", {}).get("fail_count", 0)),
    }
}
# ── Auto-clear any saved pending legs whose contract has expired ──
for _leg_name in ("call", "put"):
    _pleg_sym = OPENSTRIKE_PENDING_MISSING_LEGS[_leg_name].get("symbol", "")
    if _pleg_sym and _is_symbol_expired(_pleg_sym):
        print(f"🗑️  Cleared expired pending {_leg_name} leg: {_pleg_sym}", flush=True)
        OPENSTRIKE_PENDING_MISSING_LEGS[_leg_name] = {
            "symbol": "", "strike": 0.0, "reason": "", "since": 0.0, "fail_count": 0,
        }
del _leg_name, _pleg_sym

STRADDLE_VOLUME_TARGET = None
STRADDLE_OI_TARGET = None
STARTUP_OPENSTRIKE_CLEANUP_DONE = False

def _get_current_cooldown(leg):
    leg_data = OPENSTRIKE_PENDING_MISSING_LEGS.get(leg, {})
    fc = leg_data.get("fail_count", 0)
    if fc <= 3:
        return 60.0
    elif fc <= 6:
        return 3600.0
    else:
        return 86400.0

def _fmt_duration(seconds):
    if seconds < 60:
        return f"{int(seconds)}s"
    elif seconds < 3600:
        return f"{int(seconds // 60)}m"
    elif seconds < 86400:
        return f"{int(seconds // 3600)}h {int((seconds % 3600) // 60)}m"
    else:
        return f"{int(seconds // 86400)}d {int((seconds % 86400) // 3600)}h"

def _openstrike_pending_same_target(leg, symbol):
    leg_data = OPENSTRIKE_PENDING_MISSING_LEGS.get(leg, {})
    pending_sym = leg_data.get("symbol", "")
    if not pending_sym:
        return False
    # Auto-clear if the pending symbol has expired — no point retrying it
    if _is_symbol_expired(pending_sym):
        _clear_openstrike_missing_leg_pending(leg)
        return False
    if pending_sym != symbol:
        _clear_openstrike_missing_leg_pending(leg)
        return False
    
    # Same target. Check if the dynamic cooldown has expired.
    since = leg_data.get("since", 0.0)
    cooldown = _get_current_cooldown(leg)
    if time.time() - since >= cooldown:
        return False # Cooldown expired, allow retry
    return True # Still in cooldown

def _pending_retry_status(leg_name, symbol):
    leg_data = OPENSTRIKE_PENDING_MISSING_LEGS.get(leg_name, {})
    since = leg_data.get("since", 0.0)
    cooldown = _get_current_cooldown(leg_name)
    rem = max(0.0, cooldown - (time.time() - since))
    rem_str = _fmt_duration(rem)
    return f"OPENSTRIKE: {leg_name.capitalize()} leg pending ({symbol}) — retry in {rem_str} or on strike change"

def _is_silent_guard_error():
    return LAST_ORDER_ERROR in (
        "AUTO_EXECUTION_OFF",
        "KILL_SWITCH_ACTIVE",
        "FIRST_RENDER_NOT_DONE",
        "COOLDOWN_ACTIVE",
        "INVALID_SIZE",
        "MISSING_REASON",
        "CONTRACT_EXPIRED",
    )

def _note_openstrike_missing_leg_pending(leg, opt, reason):
    global OPENSTRIKE_PENDING_MISSING_LEGS
    symbol = opt.get("symbol", "") if opt else ""
    if not symbol:
        return
    # Don't queue a retry for a contract that has already expired
    if _is_symbol_expired(symbol):
        _clear_openstrike_missing_leg_pending(leg)
        return
    
    leg_data = OPENSTRIKE_PENDING_MISSING_LEGS.get(leg, {})
    
    # Check if the target is exactly the same (ignoring cooldown)
    already_pending = (leg_data.get("symbol") == symbol)
    
    if already_pending:
        new_fail_count = leg_data.get("fail_count", 0) + 1
    else:
        new_fail_count = 1
        
    since = leg_data.get("since", 0.0)
    cooldown = _get_current_cooldown(leg)
    if already_pending and (time.time() - since < cooldown):
        return
        
    OPENSTRIKE_PENDING_MISSING_LEGS[leg] = {
        "symbol": symbol,
        "strike": float(opt.get("strike", 0) or 0),
        "reason": str(reason)[:180],
        "since": time.time(),
        "fail_count": new_fail_count,
    }
    _save_settings()
    
    if new_fail_count <= 3:
        action_msg = f"Same target: Will retry after 1 min cooldown (fail #{new_fail_count})."
    elif new_fail_count <= 6:
        action_msg = f"Same target: Will retry after 1 hour cooldown (fail #{new_fail_count})."
    else:
        action_msg = f"Same target: Will retry after 1 day cooldown (fail #{new_fail_count})."
        
    send_telegram(
        f"🟡 OPENSTRIKE MISSING LEG PENDING (Failure #{new_fail_count})\n"
        f"Leg    : {leg.upper()}\n"
        f"Symbol : {symbol}\n"
        f"Strike : {OPENSTRIKE_PENDING_MISSING_LEGS[leg]['strike']}\n"
        f"Reason : {str(reason)[:180]}\n"
        f"Action : {action_msg}\n"
        f"Time   : {datetime.now().strftime('%H:%M:%S')}"
    )

def _clear_openstrike_missing_leg_pending(leg=None):
    global OPENSTRIKE_PENDING_MISSING_LEGS
    if leg:
        leg_data = OPENSTRIKE_PENDING_MISSING_LEGS.get(leg, {})
        if not leg_data.get("symbol"):
            return
        OPENSTRIKE_PENDING_MISSING_LEGS[leg] = {
            "symbol": "",
            "strike": 0.0,
            "reason": "",
            "since": 0.0,
            "fail_count": 0,
        }
    else:
        OPENSTRIKE_PENDING_MISSING_LEGS = {
            "call": {
                "symbol": "",
                "strike": 0.0,
                "reason": "",
                "since": 0.0,
                "fail_count": 0,
            },
            "put": {
                "symbol": "",
                "strike": 0.0,
                "reason": "",
                "since": 0.0,
                "fail_count": 0,
            }
        }
    _save_settings()

last_orders = deque(maxlen=10)

def detect_position_changes(current_positions):
    global PREVIOUS_POSITIONS, POSITION_CHANGE_LOG

    changes = []
    current_symbols = {pos.get("product_symbol"): pos for pos in current_positions}
    previous_symbols = {pos.get("product_symbol"): pos for pos in PREVIOUS_POSITIONS}

    for symbol, prev_pos in previous_symbols.items():
        if symbol not in current_symbols:
            prev_size = float(prev_pos.get("size", 0))
            direction = "LONG" if prev_size > 0 else "SHORT"
            option_type = "CALL" if symbol.startswith("C-") else "PUT"
            changes.append(f"🔄 SQUARED OFF: {direction} {option_type} │ {symbol}")
            POSITION_CHANGE_LOG.append(f"[{datetime.now().strftime('%H:%M:%S')}] SQUARED OFF: {direction} {option_type} │ {symbol}")

    for symbol, curr_pos in current_symbols.items():
        if symbol not in previous_symbols:
            curr_size = float(curr_pos.get("size", 0))
            direction = "LONG" if curr_size > 0 else "SHORT"
            option_type = "CALL" if symbol.startswith("C-") else "PUT"
            changes.append(f"🆕 NEW POSITION: {direction} {option_type} │ {symbol}")
            POSITION_CHANGE_LOG.append(f"[{datetime.now().strftime('%H:%M:%S')}] NEW POSITION: {direction} {option_type} │ {symbol}")

    PREVIOUS_POSITIONS = current_positions.copy()

    return changes
def format_position_line_for_message(active_positions):
    n_legs = len(active_positions)
    if not n_legs:
        return "0 X"
    total_x = sum(abs(int(float(p.get("size", 0)))) for p in active_positions)
    per_leg = total_x // n_legs
    return f"{n_legs} legs, Total {total_x}x, each leg {per_leg}x qty"

def _get_strategy_subkey_label(mode, target):
    if not mode:
        return ""
    mode_upper = str(mode).upper()
    if mode_upper == "STRADDLE":
        if target == "highest_volume":
            return "sv Key - Volume"
        elif target == "highest_oi":
            return "so Key - OI"
        elif target == "vol_oi":
            return "sf Key - Vol+OI"
        return f"{target}"
    elif mode_upper == "OPENSTRIKE":
        if LAST_CROSS_DOWN_SIDE == "Call Strike":
            h_lbl = "10D Call Hedge" if CUSTOM_HEDGES_COUNT == 1 else "10D Hedges"
            return f"Custom - Put ATM + {h_lbl}"
        elif LAST_CROSS_DOWN_SIDE == "Put Strike":
            h_lbl = "10D Put Hedge" if CUSTOM_HEDGES_COUNT == 1 else "10D Hedges"
            return f"Custom - Call ATM + {h_lbl}"
        
        if target == "highest_oi":
            return "11 Key - 1st Highest OI"
        elif target == "second_highest":
            return "22 Key - 2nd Highest OI"
        elif target == "third_highest":
            return "33 Key - 3rd Highest OI"
        elif target == "4th_highest":
            return "44 Key - 4th Highest OI"
        elif target == "5th_highest":
            return "55 Key - 5th Highest OI"
        elif target == "atm":
            return "00 Key - ATM"
        if isinstance(target, str):
            t_lower = target.lower()
            if t_lower.startswith("rank_"):
                try:
                    num = int(t_lower.split("_")[1])
                    return f"{num}{num} Key - {num}th Highest OI"
                except Exception:
                    pass
            m = re.match(r"^(\d+)(?:st|nd|rd|th)?_highest$", t_lower)
            if m:
                num = int(m.group(1))
                return f"{num}{num} Key - {num}th Highest OI"
        return f"{target}"
    return ""

def _format_new_position_telegram_lines(active_positions, decision, symbol, expiry_display, bal, blocked, pos_line, strategy_mode="—", projected_profit=None, max_loss=None, position_details=None):
    sub_label = _get_strategy_subkey_label(strategy_mode, OPENSTRIKE_TARGET_STRIKE)
    strategy_lbl = f"{strategy_mode} ({sub_label})" if sub_label else strategy_mode

    if ORDER_TYPE == "futures":
        used_pct = (blocked / bal * 100) if bal > 0 else 0
        ts = datetime.now().strftime("%H:%M:%S")
        perp_sym = f"{symbol}USD"
        fut_pos = next((p for p in active_positions if p.get("product_symbol", "") == perp_sym), None)
        if not fut_pos:
            fut_pos = next(
                (p for p in active_positions
                 if not str(p.get("product_symbol", "")).startswith(("C-", "P-", "MV-"))),
                None,
            )
        size_val = float(fut_pos.get("size", 0)) if fut_pos else 0
        entry_px = float(fut_pos.get("entry_price") or fut_pos.get("average_price") or 0) if fut_pos else 0
        direction_label = "Long Futures" if size_val > 0 else "Short Futures"
        direction_icon  = "📈" if size_val > 0 else "📉"
        lines = [
            f"📋 Account  : {MAIN_ACCOUNT.get('account_name', 'Main')}",
            f"Reason   : NEW_POSITION ({decision})",
            f"Strategy : {strategy_lbl}",
            f"Bias     : {decision}",
            f"Sizing   : {_position_sizing_mode_label()}",
            f"Instrument : {perp_sym} | Perpetual",
            f"{direction_icon} Direction : {direction_label}",
            f"Size     : {abs(int(size_val))}x contracts",
            f"Entry    : ${entry_px:.2f}" if entry_px > 0 else "Entry    : —",
            f"Balance : ${bal:.2f} │ Used : ${blocked:.2f} ({used_pct:.1f}%)",
        ]
        if projected_profit is not None and max_loss is not None:
            proj_wallet_pct = (projected_profit / bal * 100) if bal > 0 else 0.0
            proj_wallet_pct_str = f"{proj_wallet_pct:+.4f}%" if 0 < abs(proj_wallet_pct) < 0.01 else f"{proj_wallet_pct:+.2f}%"
            proj_profit_str = f"${projected_profit:.4f}" if 0 < abs(projected_profit) < 0.01 else f"${projected_profit:.2f}"
            has_options = any(p.get("product_symbol", "").startswith(("C-", "P-", "MV-")) for p in active_positions)
            is_covered = is_covered_under_10_percent_move(active_positions)
            loss_wallet_pct = -(max_loss / bal * 100) if bal > 0 else 0.0
            loss_wallet_pct_str = f"{loss_wallet_pct:+.4f}%" if 0 < abs(loss_wallet_pct) < 0.01 else f"{loss_wallet_pct:+.2f}%"
            if is_covered and has_options:
                lines.append(f"Projected: {proj_profit_str} ({proj_wallet_pct_str})  │  Max Loss: ${max_loss:.2f} ({loss_wallet_pct_str}) (both leg covered under 10% movment)")
            else:
                lines.append(f"Projected: {proj_profit_str} ({proj_wallet_pct_str})  │  Max Loss: ${max_loss:.2f} ({loss_wallet_pct_str})")
        lines.append(f"Time : {ts}")
        return "\n".join(lines)

    short_put = short_call = long_put = long_call = None
    short_put_delta = short_call_delta = long_put_delta = long_call_delta = None

    delta_map = {}
    try:
        target_syms = {
            p.get("product_symbol")
            for p in active_positions
            if p and p.get("product_symbol")
        }
        if target_syms:
            opts = fetch_options(symbol=symbol) if symbol else fetch_options()
            for o in opts:
                s = o.get("symbol")
                if s in target_syms and o.get("delta") is not None:
                    delta_map[s] = abs(float(o.get("delta", 0) or 0))
    except Exception:
        delta_map = {}

    def _safe_signed_delta(p):
        if not p:
            return None
        try:
            sym_p = p.get("product_symbol", "") or ""
            d = p.get("delta", None)
            if d is not None:
                mag = abs(float(d))
                if sym_p.startswith("P-"):
                    return -mag
                return mag
        except (ValueError, TypeError):
            return None

        try:
            sym_p = p.get("product_symbol", "") or ""
            if sym_p and sym_p in delta_map:
                mag = delta_map[sym_p]
                if sym_p.startswith("P-"):
                    return -mag
                return mag
        except Exception:
            pass
        return None

    for p in active_positions:
        sym = p.get("product_symbol", "")
        size = float(p.get("size", 0))
        if sym.startswith("P-") and size < 0:
            short_put = sym
            short_put_delta = _safe_signed_delta(p)
        elif sym.startswith("C-") and size < 0:
            short_call = sym
            short_call_delta = _safe_signed_delta(p)
        elif sym.startswith("P-") and size > 0:
            long_put = sym
            long_put_delta = _safe_signed_delta(p)
        elif sym.startswith("C-") and size > 0:
            long_call = sym
            long_call_delta = _safe_signed_delta(p)

    exp_short = ""
    if expiry_display is not None:
        try:
            if hasattr(expiry_display, "strftime"):
                exp_short = expiry_display.strftime("%d-%b")
            else:
                exp_short = str(expiry_display)[:6] if len(str(expiry_display)) >= 6 else str(expiry_display)
        except Exception:
            exp_short = str(expiry_display)[:7] if expiry_display else ""
    if not exp_short and active_positions:
        ex = extract_expiry(active_positions[0].get("product_symbol", ""))
        if ex and hasattr(ex, "strftime"):
            exp_short = ex.strftime("%d-%b")
    leg_size = 0
    if active_positions:
        total_x = sum(abs(int(float(p.get("size", 0)))) for p in active_positions)
        n_legs = len(active_positions)
        leg_size = total_x // n_legs if n_legs else 0
    used_pct = (blocked / bal * 100) if bal > 0 else 0
    ts = datetime.now().strftime("%H:%M:%S")
    sub_label = _get_strategy_subkey_label(strategy_mode, OPENSTRIKE_TARGET_STRIKE)
    strategy_lbl = f"{strategy_mode} ({sub_label})" if sub_label else strategy_mode

    lines = [
        f"📋 Account  : {MAIN_ACCOUNT.get('account_name', 'Main')}",
        f"Reason   : NEW_POSITION ({decision})",
        f"Strategy : {strategy_lbl}",
        f"Bias     : {decision}",
        f"Sizing   : {_position_sizing_mode_label()}",
        f"Instrument : {symbol} | Exp {exp_short} | Leg size : {leg_size}x",
    ]

    position_details_lines = []
    if position_details is not None:
        for p in position_details:
            if not p.get("is_futures"):
                position_details_lines.append(format_position_detail_for_ui(p))
    else:
        for p in active_positions:
            sym = p.get("product_symbol", "")
            sz = float(p.get("size", 0))
            if not sym or sz == 0:
                continue
            
            upnl_val = 0.0
            for fld in ["unrealized_pnl", "upnl", "unrealized_profit_loss", "pnl", "profit_loss"]:
                if fld in p and p[fld] is not None:
                    try:
                        upnl_val = float(p[fld])
                        break
                    except:
                        pass
            
            color = "🟢" if upnl_val >= 0 else "🔴"
            dl = "L" if sz > 0 else "S"
            
            entry_p = float(p.get("entry_price") or p.get("average_price") or 0)
            mark_p = float(p.get("mark_price") or p.get("last_price") or 0)
            
            entry_s = f" Entry${entry_p:.1f}" if entry_p % 1 != 0 else f" Entry${entry_p:.0f}" if entry_p > 0 else ""
            mark_s = f" Mark${mark_p:.1f}" if mark_p % 1 != 0 else f" Mark${mark_p:.0f}" if mark_p > 0 else ""
            
            sz_btc = abs(sz) * 0.001
            left = f"{color} {dl} {sym} x{sz_btc:.3f} BTC{entry_s}{mark_s}"
            position_details_lines.append(f"{left} │ UPNL: ${upnl_val:+.2f}")

    if not position_details_lines:
        position_details_lines.append("No Active Positions")

    lines.extend(position_details_lines)
    lines.append(f"Balance : ${bal:.2f} │ Used : ${blocked:.2f} ({used_pct:.1f}%)")
    if projected_profit is not None and max_loss is not None:
        proj_wallet_pct = (projected_profit / bal * 100) if bal > 0 else 0.0
        proj_wallet_pct_str = f"{proj_wallet_pct:+.4f}%" if 0 < abs(proj_wallet_pct) < 0.01 else f"{proj_wallet_pct:+.2f}%"
        proj_profit_str = f"${projected_profit:.4f}" if 0 < abs(projected_profit) < 0.01 else f"${projected_profit:.2f}"
        has_options = any(p.get("product_symbol", "").startswith(("C-", "P-", "MV-")) for p in active_positions)
        is_covered = is_covered_under_10_percent_move(active_positions)
        loss_wallet_pct = -(max_loss / bal * 100) if bal > 0 else 0.0
        loss_wallet_pct_str = f"{loss_wallet_pct:+.4f}%" if 0 < abs(loss_wallet_pct) < 0.01 else f"{loss_wallet_pct:+.2f}%"
        if is_covered and has_options:
            lines.append(f"Projected: {proj_profit_str} ({proj_wallet_pct_str})  │  Max Loss: ${max_loss:.2f} ({loss_wallet_pct_str}) (both leg covered under 10% movment)")
        else:
            lines.append(f"Projected: {proj_profit_str} ({proj_wallet_pct_str})  │  Max Loss: ${max_loss:.2f} ({loss_wallet_pct_str})")
    
    lines.extend([
        f"Position : {pos_line}",
        f"Time : {ts}",
    ])
    return "\n".join(lines)

def identify_unknown_positions(current_positions, decision):
    if STRATEGY_MODE == "OPENSTRIKE" and ORDER_TYPE != "futures":
        return []
    unknown_positions = []

    for pos in current_positions:
        symbol = pos.get("product_symbol", "")
        size = float(pos.get("size", 0))
        if size == 0:
            continue

        is_call = symbol.startswith("C-")
        is_put  = symbol.startswith("P-")

        if decision == "SELL CALL":
            if is_put and size < 0:
                unknown_positions.append(pos)

        elif decision == "SELL PUT":
            if is_call and size < 0:
                unknown_positions.append(pos)

    return unknown_positions

def _strike_from_position(pos):
    if not pos:
        return None
    sym = pos.get("product_symbol", "")
    parts = sym.split("-")
    if len(parts) < 3:
        return None
    try:
        return float(parts[2])
    except (ValueError, TypeError):
        return None

def validate_three_leg_strike_order(decision, short_pos, long_leg_a, long_leg_b):
    if not (short_pos and long_leg_a and long_leg_b):
        return None, ""
    s_short = _strike_from_position(short_pos)
    s_a = _strike_from_position(long_leg_a)
    s_b = _strike_from_position(long_leg_b)
    if s_short is None or s_a is None or s_b is None:
        return None, ""
    if decision == "SELL CALL":
        ok = s_a < s_short < s_b
        msg = "Long put < Short call < Long call" if ok else "Strike order mismatch (SELL CALL)"
        return ok, msg
    if decision == "SELL PUT":
        ok = s_a < s_short < s_b
        msg = "Long put < Short put < Long call" if ok else "Strike order mismatch (SELL PUT)"
        return ok, msg
    return None, ""

def square_off_unknown_positions(unknown_positions):
    squared_off_count = 0

    for pos in unknown_positions:
        if KILL_SWITCH:
            return squared_off_count
        symbol = pos.get("product_symbol", "")
        size = float(pos.get("size", 0))

        if size != 0:
            print(f"🔄 Squaring off unknown position: {symbol} (size: {size})")
            res = square_off_position(symbol, size, reason="UNKNOWN_POSITION")
            if res:
                last_orders.append(
                    f"[{datetime.now().strftime('%H:%M:%S')}] SQUARE OFF UNKNOWN │ {symbol}"
                )

                squared_off_count += 1
            else:
                print(f"❌ Failed to square off: {symbol}")

    return squared_off_count

def square_off_current_instrument_for_switch(reason="INSTRUMENT_SWITCH"):
    if KILL_SWITCH:
        return 0
    try:
        positions = get_positions()
    except Exception:
        return 0
    count = 0
    for pos in positions:
        symbol = pos.get("product_symbol", "")
        size = float(pos.get("size", 0))
        if not symbol.startswith(("C-", "P-", "MV-")):
            continue
        if size == 0:
            continue
        print(f"🔄 Squaring off {symbol} (size: {size}) — reason: {reason}")
        res = square_off_position(symbol, size, reason=reason)
        if res:
            last_orders.append(
                f"[{datetime.now().strftime('%H:%M:%S')}] SQUARE OFF (switch) │ {symbol}"
            )
            count += 1
        else:
            print(f"❌ Failed to square off for switch: {symbol}")
    return count

API_ALERT_COOLDOWN = 300
API_RECOVERED_COOLDOWN = 300
API_DOWN = False

API_RECOVERY_COOLDOWN_SEC = 10
API_RECOVERY_COOLDOWN_UNTIL = 0.0
API_RETRY_COUNT = 3
API_RETRY_DELAY_SEC = 1.5
API_MIN_HEALTH_PCT = 25
LAST_EXECUTED_SIGNAL = None

NO_TRADE_ALERT_SENT_FOR_OLD_BIAS = None

def calc_position_size(balance, margin_pct, option_price):
    if balance <= 0 or option_price <= 0:
        return max(MIN_POSITION_CONTRACTS, 0)

    effective_pct = max(margin_pct, MIN_MARGIN_PCT)
    block_rate = 0.035

    if effective_pct >= 0.09 and effective_pct <= 0.11:
        block_per_leg = option_price * block_rate
        if block_per_leg <= 0:
            return 1
        size = (balance * 0.10 * 1.15) / (3 * block_per_leg)
        size = int(max(1, size))

        cap_size = (balance * 0.11) / (3 * block_per_leg)
        size = min(size, max(1, int(cap_size)))
        return size

    margin_scale = 1.0
    target_used_pct = effective_pct
    if effective_pct <= 0.02:
        margin_scale = 3.0
        target_used_pct = 0.015
    elif effective_pct >= 0.99:
        margin_scale = 2.0
        target_used_pct = 0.55
    elif effective_pct >= 0.005 and effective_pct < 0.09:
        margin_scale = 1.5
    capital_to_use = balance * max(effective_pct, target_used_pct) * margin_scale
    size = int(capital_to_use / option_price)
    if option_price > 0 and effective_pct <= 0.02:
        min_for_1pct = int((balance * 0.01) / (option_price * 0.06)) if (option_price * 0.06) > 0 else 0
        size = max(size, min_for_1pct)
    return max(size, 1)

def estimate_three_leg_max_loss_per_unit(decision, short_opt, long_call_opt, long_put_opt):
    if decision not in ("SELL CALL", "SELL PUT"):
        return 0.0

    if STRATEGY_MODE == "OPENSTRIKE" and not (short_opt and long_call_opt and long_put_opt):
        call_opt = short_opt
        put_opt = long_put_opt
        if not (call_opt and put_opt):
            return 0.0
        try:
            mult = 0.001
            call_strike = float(call_opt.get("strike_price") or call_opt.get("strike") or 0.0)
            call_entry = float(call_opt.get("mark_price", 0) or 0)
            put_strike = float(put_opt.get("strike_price") or put_opt.get("strike") or 0.0)
            put_entry = float(put_opt.get("mark_price", 0) or 0)

            spot_val = get_spot(SYMBOL)
            if spot_val <= 0:
                return 0.0

            stress_pct = MAX_LOSS_CAP_PCT if MAX_LOSS_CAP_PCT > 0 else 0.10

            spot_up = spot_val * (1.0 + stress_pct)
            spot_down = spot_val * (1.0 - stress_pct)

            total_premium = (call_entry + put_entry) * mult

            loss_up = max(0.0, spot_up - call_strike) * mult - total_premium

            loss_down = max(0.0, put_strike - spot_down) * mult - total_premium

            return round(max(loss_up, loss_down, 0.0), 6)
        except Exception:
            return 0.0

    if not (short_opt and long_call_opt and long_put_opt):
        return 0.0
    try:
        mult = 0.001 if SYMBOL == "BTC" else 0.01
        short_strike = float(short_opt.get("strike_price") or short_opt.get("strike") or 0.0)
        short_entry = float(short_opt.get("mark_price", 0) or 0)
        call_strike = float(long_call_opt.get("strike_price") or long_call_opt.get("strike") or 0.0)
        call_entry = float(long_call_opt.get("mark_price", 0) or 0)
        put_strike = float(long_put_opt.get("strike_price") or long_put_opt.get("strike") or 0.0)
        put_entry = float(long_put_opt.get("mark_price", 0) or 0)
    except (ValueError, TypeError):
        return 0.0
    if min(short_entry, call_entry, put_entry) <= 0:
        return 0.0
    if decision == "SELL PUT":
        put_spread_intrinsic = abs(short_strike - put_strike) * mult
        put_spread_net = (short_entry - put_entry) * mult
        loss = put_spread_intrinsic - put_spread_net + (call_entry * mult)
    else:
        call_spread_intrinsic = abs(call_strike - short_strike) * mult
        call_spread_net = (short_entry - call_entry) * mult
        loss = call_spread_intrinsic - call_spread_net + (put_entry * mult)
    return round(max(loss, 0.0), 6)

def calc_position_size_by_max_loss(balance, decision, short_opt, long_call_opt, long_put_opt, loss_pct=MAX_LOSS_CAP_PCT):
    if balance <= 0 or loss_pct <= 0:
        return 0
    per_set_loss = estimate_three_leg_max_loss_per_unit(decision, short_opt, long_call_opt, long_put_opt)
    if per_set_loss <= 0:
        return 0
    loss_budget = balance * loss_pct
    return max(int(loss_budget / per_set_loss), 0)

def calc_position_size_by_target_profit(balance, decision, short_opt, long_call_opt, long_put_opt, target_profit_pct):
    if balance <= 0 or target_profit_pct <= 0:
        return MIN_POSITION_CONTRACTS

    desired_profit_usd_min = balance * target_profit_pct
    mult = 0.001 if SYMBOL == "BTC" else 0.01

    if STRATEGY_MODE == "OPENSTRIKE" and not (short_opt and long_call_opt and long_put_opt):
        call_opt = short_opt
        put_opt = long_put_opt
        if not (call_opt or put_opt):
            return MIN_POSITION_CONTRACTS
        premium_c = float(call_opt.get("mark_price") or 0) if call_opt else 0.0
        premium_p = float(put_opt.get("mark_price") or 0) if put_opt else 0.0
        
        long_call_prem = float(long_call_opt.get("mark_price") or 0) if long_call_opt else 0.0
        net_prem = (premium_c + premium_p) - long_call_prem
        if net_prem <= 0:
            net_prem = max(0.01, premium_c + premium_p)
        net_premium_per_unit = net_prem * mult
    else:
        if not (short_opt and long_call_opt and long_put_opt):
            return MIN_POSITION_CONTRACTS
        short_entry = float(short_opt.get("average_price") or short_opt.get("entry_price") or short_opt.get("mark_price") or 0) or max(0.01, float(short_opt.get("strike_price") or short_opt.get("strike") or 1) * 0.005)
        call_entry = float(long_call_opt.get("mark_price") or 0) or max(0.01, float(long_call_opt.get("strike_price") or long_call_opt.get("strike") or 1) * 0.005)
        put_entry = float(long_put_opt.get("mark_price") or 0) or max(0.01, float(long_put_opt.get("strike_price") or long_put_opt.get("strike") or 1) * 0.005)
        net_premium_per_unit = (short_entry - call_entry - put_entry) * mult

    if net_premium_per_unit <= 0:
        return MIN_POSITION_CONTRACTS

    size = int(math.ceil(desired_profit_usd_min / net_premium_per_unit))

    strike_c = float(short_opt.get("strike_price") or short_opt.get("strike") or 0) if short_opt else 0
    mult_factor = 0.000011 if SYMBOL == "BTC" else 0.00011
    est_margin_per_contract = strike_c * mult_factor
    if est_margin_per_contract > 0:
        size_50_margin = int((balance * 0.50) / est_margin_per_contract)
        size = min(size, max(MIN_POSITION_CONTRACTS, size_50_margin))

    return max(size, MIN_POSITION_CONTRACTS)

def calc_futures_position_size_by_target_profit(balance, target_profit_pct, spot_price):
    if balance <= 0 or spot_price <= 0 or target_profit_pct <= 0:
        return 1
    desired_profit = balance * target_profit_pct
    target_move = spot_price * 0.05
    size = int(desired_profit / (target_move * 0.001))

    max_loss_pct = 2.0 * target_profit_pct
    max_loss_budget = balance * max_loss_pct
    adverse_move = spot_price * 0.10
    size_by_loss = int(max_loss_budget / (adverse_move * 0.001))

    size = min(size, size_by_loss)
    return max(size, 1)

def calc_futures_position_size(balance, margin_pct, spot_price):
    if balance <= 0 or spot_price <= 0 or margin_pct <= 0:
        return 1

    effective_margin = max(margin_pct, 0.05)
    multiplier = 0.001

    margin_available = balance * effective_margin

    size = int(margin_available / (spot_price * multiplier))

    return max(size, 1)

def calc_futures_position_size_by_max_loss(balance, decision, spot_price, loss_pct=MAX_LOSS_CAP_PCT):
    if balance <= 0 or spot_price <= 0 or loss_pct <= 0:
        return 1

    multiplier = 0.001

    loss_budget = balance * loss_pct

    spot_move = spot_price * loss_pct
    size_raw = loss_budget / (spot_move * multiplier) if spot_move > 0 else 0

    margin_safety_pct = min(0.99, max(0.01, 0.10 * MAX_USED_MARGIN_MULTIPLIER))
    size_safety = calc_futures_position_size(balance, margin_safety_pct, spot_price)

    size = min(int(size_raw), size_safety) if size_raw > 0 else 0

    return max(size, 1)

def create_or_manage_futures_position(symbol, decision, balance, spot_price):
    if not (decision and balance > 0 and spot_price > 0):
        return False, "Invalid parameters"

    try:
        positions = get_positions()
    except Exception as e:
        return False, f"Failed to fetch positions: {e}"

    perp_symbol = f"{symbol}USD"
    existing_futures_pos = None
    for pos in positions:
        if pos.get("product_symbol", "") == perp_symbol:
            existing_futures_pos = pos
            break

    if decision == "SELL CALL":
        desired_side = "sell"
        opposite_desc = "long"
        same_desc = "short"
        close_reason = "CLOSE_LONG_FOR_SHORT"
        success_msg = "Short futures"
    elif decision == "SELL PUT":
        desired_side = "buy"
        opposite_desc = "short"
        same_desc = "long"
        close_reason = "CLOSE_SHORT_FOR_PUT"
        success_msg = "Long futures"
    else:
        return False, f"Unknown decision: {decision}"

    if existing_futures_pos:
        current_size = float(existing_futures_pos.get("size", 0))
        if desired_side == "sell" and current_size < 0:
            return False, f"Futures already short {abs(current_size)}"
        if desired_side == "buy" and current_size > 0:
            return False, f"Futures already long {abs(current_size)}"

        if (desired_side == "sell" and current_size > 0) or (desired_side == "buy" and current_size < 0):
            res = square_off_position(perp_symbol, current_size, reason=close_reason)
            if not res:
                return False, f"Failed to close existing {opposite_desc} position"
            time.sleep(1)

    if POSITION_SIZING_MODE == "margin":
        size_dir = calc_futures_position_size(balance, MIN_MARGIN_PCT, spot_price)
    elif POSITION_SIZING_MODE == "target_profit":
        size_dir = calc_futures_position_size_by_target_profit(balance, MIN_MARGIN_PCT, spot_price)
    else:
        size_dir = calc_futures_position_size_by_max_loss(balance, decision, spot_price, MAX_LOSS_CAP_PCT)

    if size_dir <= 0:
        return False, "Position size too small (margin cap exceeded)"

    res = place_order(perp_symbol, desired_side, size_dir, MARGIN_MODE.lower(), reason="NEW_POSITION")
    if res:
        return True, f"{success_msg} {perp_symbol} x{size_dir} created"
    else:
        return False, f"Failed to place {same_desc} futures order"

    return False, f"Unknown decision: {decision}"

def render_margin_heatmap(balance, blocked):
    if balance <= 0:
        return "N/A", "⚪ UNKNOWN", ""

    used_pct = (blocked / balance) * 100

    if used_pct < 10:
        level = "🟢 SAFE"
        color_code = "\033[92m"
    elif used_pct < 15:
        level = "🟡 WARNING"
        color_code = "\033[93m"
    else:
        level = "🔴 DANGER"
        color_code = "\033[91m"

    filled = int(min(used_pct / 5, 20))
    reset = "\033[0m"
    bar = color_code + ("█" * filled) + reset + ("░" * (20 - filled))

    return round(used_pct, 2), level, bar

def calculate_margin_drift(balance, blocked, target_pct):
    if balance <= 0:
        return 0, 0, "UNKNOWN", "⚪", 0

    used_pct = (blocked / balance) * 100
    min_pct = target_pct * 100
    ceiling_pct = min_pct * 1.01
    drift_pct = round(used_pct - min_pct, 2)

    if used_pct < min_pct:
        status = "UNDER-EXPOSED"
        icon = "🟡"
    elif used_pct <= ceiling_pct:
        status = "ALIGNED"
        icon = "🟢"
    else:
        status = "OVER-EXPOSED"
        icon = "🔴"

    return round(used_pct, 2), drift_pct, status, icon, ceiling_pct

def render_api_health_bar():
    score = 0
    count = 0

    for api in ["SPOT", "WALLET", "ORDERS", "POSITIONS"]:
        latency = API_LATENCY.get(api, -1)
        healthy = HEALTH.get(api, False)

        if not healthy or latency < 0:
            api_score = 0
        elif latency < 1000:
            api_score = 100
        elif latency < 2000:
            api_score = 75
        elif latency < 3000:
            api_score = 50
        else:
            api_score = 15

        score += api_score
        count += 1

    avg = int(score / count) if count else 0

    if avg >= 80:
        status = "🟢 HEALTHY"
        color_code = "\033[92m"
    elif avg >= 50:
        status = "🟡 DEGRADED"
        color_code = "\033[93m"
    else:
        status = "🔴 UNSTABLE"
        color_code = "\033[91m"

    filled = int(avg / 5)
    filled = min(filled, 20)
    reset = "\033[0m"
    bar = color_code + ("█" * filled) + reset + ("░" * (20 - filled))

    return avg, status, bar
KEYBOARD_LISTENER_PAUSED = False
TTY_OLD_SETTINGS = None

def restore_tty():
    """
    Restores standard TTY terminal settings.
    """
    global TTY_OLD_SETTINGS
    if TTY_OLD_SETTINGS is not None:
        try:
            termios.tcsetattr(sys.stdin.fileno(), termios.TCSADRAIN, TTY_OLD_SETTINGS)
        except Exception:
            pass

def set_cbreak_tty():
    """
    Sets TTY terminal to cbreak mode to capture individual keypresses instantly.
    """
    if sys.stdin.isatty():
        try:
            tty.setcbreak(sys.stdin.fileno())
        except Exception:
            pass

def request_strategy_switch(target_mode, target_strike, key_label):
    """
    Requests strategy switch and applies target modes immediately.
    """
    global STRATEGY_MODE, OPENSTRIKE_TARGET_STRIKE
    global STRATEGY_SWITCH_PENDING, PENDING_STRATEGY_MODE, PENDING_TARGET_STRIKE
    global CMD_FEEDBACK, CMD_FEEDBACK_CLEAR_AT, LAST_CMD_SHOWN

    STRATEGY_MODE = target_mode
    OPENSTRIKE_TARGET_STRIKE = target_strike
    STRATEGY_SWITCH_PENDING = False
    PENDING_STRATEGY_MODE = ""
    PENDING_TARGET_STRIKE = ""
    
    # Leg jese hi change hua (by switching strategy / target), vese call/put pending hat jaye
    _clear_openstrike_missing_leg_pending()
    _save_settings()

    CMD_FEEDBACK = f"⌨️ [{key_label}] Mode → {target_mode}, Target → {target_strike}"
    CMD_FEEDBACK_CLEAR_AT = time.time() + 5
    LAST_CMD_SHOWN = {"msg": f"[{key_label}] Mode: {target_mode}, Target: {target_strike}", "until": time.time() + 30}
    send_telegram(
        f"⌨️ SHORTCUT [{key_label}]\n"
        f"Strategy Mode : {target_mode}\n"
        f"Target Strike : {target_strike}\n"
        f"Time : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
    )


def safe_input(prompt):
    global KEYBOARD_LISTENER_PAUSED
    KEYBOARD_LISTENER_PAUSED = True
    time.sleep(0.15)
    restore_tty()
    try:
        val = input(prompt)
    finally:
        set_cbreak_tty()
        KEYBOARD_LISTENER_PAUSED = False
    return val

def get_telegram_help_menu():
    global SYMBOL, MIN_MARGIN_PCT, MAX_LOSS_CAP_PCT, TARGET_PROFIT_PCT, MARGIN_MODE, POSITION_SIZING_MODE, ORDER_TYPE, USER_AUTO_EXECUTION
    global CUSTOM_BASE_THRESHOLD, CUSTOM_ACTIVE_THRESHOLD
    global OI_CHAIN_VIEW, LOG_ENABLED, OPENSTRIKE_TARGET_STRIKE, CUSTOM_HEDGES_COUNT
    global MAIN_ACCOUNT

    sizing_label = _position_sizing_mode_label()
    hedges_lbl = "1 Buy (Single)" if CUSTOM_HEDGES_COUNT == 1 else "2 Buys (Double)"
    order_type_lbl = "Options" if ORDER_TYPE.lower() == "options" else "Short Futures"

    menu = (
        "📋 *OPENSTRIKE BOT SHORTCUTS MENU:*\n\n"
        f"🔹 *ii* : Switch Instrument (Current: {SYMBOL})\n"
        f"🔹 *mm [val]* : Set target/loss % (Current target profit: {round(TARGET_PROFIT_PCT*100)}%) (e.g. `mm 25` or `/mm 25`)\n"
        f"🔹 *aa [val]* : Set Account Name (Current: {MAIN_ACCOUNT.get('account_name', 'Main')})\n"
        f"🔹 *uu [name, email, phone]* : Set User profile (e.g. `uu John, john@email.com, 123`)\n"
        f"🔹 *pp* : Cycle Margin Mode (Current: {MARGIN_MODE.capitalize()})\n"
        f"🔹 *kk* : Cycle Sizing (Current: {sizing_label})\n"
        f"🔹 *tt* : Cycle Order Type (Current: {order_type_lbl})\n"
        f"🔹 *xx* : Toggle Auto Exec (Current: {'ON' if USER_AUTO_EXECUTION else 'OFF'})\n"
        f"🔹 *ll* : Toggle Log File (Current: {'ON' if LOG_ENABLED else 'OFF'})\n"
        f"🔹 *oo* : Cycle OI Chain view (Current: {OI_CHAIN_VIEW.capitalize()})\n"
        f"🔹 *cc* : Cycle Custom Threshold (Current: {round(CUSTOM_BASE_THRESHOLD*100)}% / {round(CUSTOM_ACTIVE_THRESHOLD*100)}%)\n"
        "🔹 *rr* : Reset settings to script defaults\n"
        "🔹 *ss* : Restart script\n"
        "🔹 *qq* / *ctrl c* : Exit script\n"
        "🔹 *update* / *up* : Send live UI snapshot\n\n"
        "📊 *STRATEGY TARGETS:*\n"
        f"[11] - 1st highest OI strike {'(Active)' if OPENSTRIKE_TARGET_STRIKE == 'highest_oi' else ''}\n"
        f"[22] - 2nd highest OI strike {'(Active)' if OPENSTRIKE_TARGET_STRIKE == 'second_highest' else ''}\n"
        f"[33] - 3rd highest OI strike {'(Active)' if OPENSTRIKE_TARGET_STRIKE == 'third_highest' else ''}\n"
        f"[44] - 4th highest OI strike {'(Active)' if OPENSTRIKE_TARGET_STRIKE == '4th_highest' else ''}\n"
        f"[55] - 5th highest OI strike {'(Active)' if OPENSTRIKE_TARGET_STRIKE == '5th_highest' else ''}\n"
        f"[NN] - Nth highest OI strike (e.g. 88, 1010, etc.)\n"
        f"[00] - ATM strike {'(Active)' if OPENSTRIKE_TARGET_STRIKE == 'atm' else ''}\n"
        f"[sv] - STRADDLE -> highest_volume\n"
        f"[so] - STRADDLE -> highest_oi\n"
        f"[sf] - STRADDLE -> vol_oi\n\n"
        "💡 *Tip:* Send `/keys`, `/menu` or `/help` anytime to view this list."
    )
    return menu

def execute_shortcut_action(key, argument=None):
    """
    Executes a shortcut action either from local keyboard listener or from Telegram.
    """
    global EQUALITY_MANUAL_EXEC, EQUALITY_SUSPENDED, EQUALITY_SUSPENDED_UNTIL
    global ENFORCE_EQUALITY_JOB
    global EQUALITY_EVENT, EQUALITY_TRIGGER_REASON
    global STRATEGY_MODE, MIN_MARGIN_PCT, MAX_LOSS_CAP_PCT, TARGET_PROFIT_PCT, MARGIN_MODE, POSITION_SIZING_MODE, ORDER_TYPE, USER_AUTO_EXECUTION
    global CUSTOM_BASE_THRESHOLD, CUSTOM_ACTIVE_THRESHOLD
    global INSTRUMENT_SWITCH_PENDING, INSTRUMENT_SWITCH_SQUARE_OFF_SENT, INSTRUMENT_SWITCH_BIAS_CHANGE_DETECTED
    global STARTUP_OPENSTRIKE_CLEANUP_DONE
    global INSTRUMENT_SWITCH_BIAS_CHANGE_MSG, LAST_BIAS_BTC, LAST_BIAS_ETH, CMD_FEEDBACK, CMD_FEEDBACK_CLEAR_AT, LAST_CMD_SHOWN
    global OI_CHAIN_VIEW, LOG_ENABLED, OPENSTRIKE_TARGET_STRIKE, CUSTOM_HEDGES_COUNT
    global MARGIN_EDIT_PENDING, ACCOUNT_NAME_EDIT_PENDING, USER_EDIT_PENDING
    global MAIN_ACCOUNT

    key = key.strip().lower()

    is_repeating_num = False
    rep_num = None
    if key.isdigit() and len(key) % 2 == 0:
        half_len = len(key) // 2
        if key[:half_len] == key[half_len:]:
            is_repeating_num = True
            rep_num = int(key[:half_len])

    if key == "cc":
        if CUSTOM_BASE_THRESHOLD == 0.25 and CUSTOM_ACTIVE_THRESHOLD == 0.50:
            CUSTOM_BASE_THRESHOLD = 0.50
            CUSTOM_ACTIVE_THRESHOLD = 0.75
        elif CUSTOM_BASE_THRESHOLD == 0.50 and CUSTOM_ACTIVE_THRESHOLD == 0.75:
            CUSTOM_BASE_THRESHOLD = 0.75
            CUSTOM_ACTIVE_THRESHOLD = 1.00
        else:
            CUSTOM_BASE_THRESHOLD = 0.25
            CUSTOM_ACTIVE_THRESHOLD = 0.50
        _save_settings()
        CMD_FEEDBACK = f"✅ Custom threshold switched to {round(CUSTOM_BASE_THRESHOLD*100)}%/{round(CUSTOM_ACTIVE_THRESHOLD*100)}%"
        CMD_FEEDBACK_CLEAR_AT = time.time() + 5
        LAST_CMD_SHOWN = {"msg": f"[cc] Threshold: {round(CUSTOM_BASE_THRESHOLD*100)}%/{round(CUSTOM_ACTIVE_THRESHOLD*100)}%", "until": time.time() + 10}
        send_telegram(
            f"⌨️ CUSTOM THRESHOLD SWITCHED\n"
            f"Threshold: {round(CUSTOM_BASE_THRESHOLD*100)}% / {round(CUSTOM_ACTIVE_THRESHOLD*100)}%\n"
            f"Time: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
        )

    elif key == "mm":
        if argument is not None:
            try:
                pct = float(argument)
                if 0 < pct <= 100:
                    val_pct = max(0.01, min(1.0, pct / 100.0))
                    if POSITION_SIZING_MODE == "max_loss":
                        MAX_LOSS_CAP_PCT = val_pct
                        tg_header = "MAX LOSS UPDATED [m]"
                        tg_label = "Max loss"
                    elif POSITION_SIZING_MODE == "target_profit":
                        TARGET_PROFIT_PCT = val_pct
                        tg_header = "TARGET PROFIT UPDATED [m]"
                        tg_label = "Target profit"
                    else:
                        MIN_MARGIN_PCT = val_pct
                        tg_header = "MIN MARGIN UPDATED [m]"
                        tg_label = "Min margin"
                    _save_settings()
                    label = "100%" if val_pct >= 0.99 else f"{round(val_pct * 100)}%"
                    send_telegram(
                        f"⌨️ {tg_header}\n"
                        f"{tg_label} : {label}\n"
                        f"Time : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
                    )
                    CMD_FEEDBACK = f"✅ {tg_label} set to {label}"
                    CMD_FEEDBACK_CLEAR_AT = time.time() + 5
                else:
                    send_telegram("❌ Telegram Error: Enter 1 to 100 only for mm")
            except Exception as e:
                send_telegram(f"❌ Telegram Error parsing mm: {e}")
        else:
            MARGIN_EDIT_PENDING = True
            if POSITION_SIZING_MODE == "max_loss":
                label_raw = "max loss %"
            elif POSITION_SIZING_MODE == "target_profit":
                label_raw = "target profit %"
            else:
                label_raw = "min margin %"
            CMD_FEEDBACK = f"⌨️ [mm] Enter {label_raw} (1-100) in terminal"
            CMD_FEEDBACK_CLEAR_AT = time.time() + 8
            LAST_CMD_SHOWN = {"msg": f"[mm] {label_raw.capitalize()} — type 1 to 100 & Enter", "until": time.time() + 15}

    elif key == "ii":
        if INSTRUMENT_SWITCH_PENDING:
            INSTRUMENT_SWITCH_PENDING = False
            INSTRUMENT_SWITCH_SQUARE_OFF_SENT = False
            INSTRUMENT_SWITCH_BIAS_CHANGE_DETECTED = False
            INSTRUMENT_SWITCH_BIAS_CHANGE_MSG = ""
            LAST_BIAS_BTC = LAST_BIAS_ETH = None
            CMD_FEEDBACK = f"⌨️ [ii] Switch cancelled — staying on {SYMBOL}"
            CMD_FEEDBACK_CLEAR_AT = time.time() + 5
            LAST_CMD_SHOWN = {"msg": f"[ii] Switch cancelled — staying on {SYMBOL}", "until": time.time() + 10}
            send_telegram(
                f"⌨️ SHORTCUT [ii] (cancel)\n"
                f"Switch cancelled — staying on {SYMBOL}\n"
                f"Time : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
            )
        else:
            INSTRUMENT_SWITCH_PENDING = True
            INSTRUMENT_SWITCH_BIAS_CHANGE_DETECTED = False
            INSTRUMENT_SWITCH_SQUARE_OFF_SENT = False
            LAST_BIAS_BTC = None
            LAST_BIAS_ETH = None
            next_sym = "ETH" if SYMBOL == "BTC" else "BTC"
            CMD_FEEDBACK = f"⌨️ [ii] Switch → {next_sym} (wait for bias change in BTC/ETH)"
            CMD_FEEDBACK_CLEAR_AT = 0.0
            if next_sym == "ETH":
                LAST_CMD_SHOWN = {"msg": f"[ii] Switch → ETH when bias changes in BTC or ETH", "until": time.time() + 86400}
            else:
                LAST_CMD_SHOWN = {"msg": f"[ii] Switch → BTC when bias changes in BTC or ETH", "until": time.time() + 86400}
            send_telegram(
                f"⌨️ SHORTCUT [ii]\n"
                f"Instrument switch pending → {next_sym}\n"
                f"Waiting for bias change in either BTC or ETH; then close {SYMBOL} positions and switch.\n"
                f"Time : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
            )

    elif key == "xx":
        CMD_FEEDBACK = f"⌨️ [xx] Auto Execution {'ON' if not USER_AUTO_EXECUTION else 'OFF'}"
        CMD_FEEDBACK_CLEAR_AT = time.time() + 5
        LAST_CMD_SHOWN = {"msg": f"[xx] Auto Exec → {'ON' if not USER_AUTO_EXECUTION else 'OFF'}", "until": time.time() + 30}
        USER_AUTO_EXECUTION = not USER_AUTO_EXECUTION
        _save_settings()
        send_telegram(
            f"⌨️ SHORTCUT [xx]\n"
            f"Auto Execution : {'ON' if USER_AUTO_EXECUTION else 'OFF'}\n"
            f"Time : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
        )

    elif key == "aa":
        if argument is not None:
            new_val = argument.strip()
            if new_val:
                MAIN_ACCOUNT["account_name"] = new_val
                _save_settings()
                send_telegram(
                    f"⌨️ ACCOUNT NAME UPDATED\n"
                    f"Account : {new_val}\n"
                    f"Time    : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
                )
                CMD_FEEDBACK = f"✅ Account set to {new_val}"
                CMD_FEEDBACK_CLEAR_AT = time.time() + 5
        else:
            ACCOUNT_NAME_EDIT_PENDING = True
            CMD_FEEDBACK = "⌨️ [aa] Enter account name (main/sub) in terminal"
            CMD_FEEDBACK_CLEAR_AT = time.time() + 8
            LAST_CMD_SHOWN = {"msg": "[aa] Edit account name (main/sub) — type in terminal & Enter", "until": time.time() + 15}

    elif key == "uu":
        if argument is not None:
            parts = [p.strip() for p in argument.split(",", 2)]
            updated = False
            if len(parts) >= 1 and parts[0]:
                MAIN_ACCOUNT["username"] = parts[0]
                updated = True
            if len(parts) >= 2 and parts[1]:
                MAIN_ACCOUNT["email"] = parts[1]
                updated = True
            if len(parts) >= 3 and parts[2]:
                MAIN_ACCOUNT["phone"] = parts[2]
                updated = True
            if updated:
                _save_settings()
                send_telegram(
                    f"⌨️ USER UPDATED\n"
                    f"Name  : {MAIN_ACCOUNT['username']}\n"
                    f"Email : {MAIN_ACCOUNT['email']}\n"
                    f"Phone : {MAIN_ACCOUNT['phone']}\n"
                    f"Time  : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
                )
                CMD_FEEDBACK = "✅ User details updated"
                CMD_FEEDBACK_CLEAR_AT = time.time() + 5
        else:
            USER_EDIT_PENDING = True
            CMD_FEEDBACK = "⌨️ [uu] Enter User (name, email, phone) in terminal"
            CMD_FEEDBACK_CLEAR_AT = time.time() + 8
            LAST_CMD_SHOWN = {"msg": "[uu] Edit User — name, email, phone (3 prompts)", "until": time.time() + 15}

    elif key == "pp":
        current = MARGIN_MODE.lower()
        try:
            idx = (MARGIN_MODES_CYCLE.index(current) + 1) % len(MARGIN_MODES_CYCLE)
        except ValueError:
            idx = 0
        MARGIN_MODE = MARGIN_MODES_CYCLE[idx]
        _save_settings()
        mode_label = MARGIN_MODE.capitalize()
        CMD_FEEDBACK = f"⌨️ [pp] Margin mode → {mode_label}"
        CMD_FEEDBACK_CLEAR_AT = time.time() + 5
        LAST_CMD_SHOWN = {"msg": f"[pp] Margin mode → {mode_label}", "until": time.time() + 30}
        send_telegram(
            f"⌨️ SHORTCUT [pp]\n"
            f"Margin mode : {mode_label}\n"
            f"Time : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
        )

    elif key == "kk":
        current = POSITION_SIZING_MODE
        if ORDER_TYPE == "futures":
            allowed_modes = ["margin", "max_loss"]
        else:
            allowed_modes = ["margin", "max_loss", "target_profit"]
        try:
            idx = (allowed_modes.index(current) + 1) % len(allowed_modes)
        except ValueError:
            idx = 0
        POSITION_SIZING_MODE = allowed_modes[idx]
        _save_settings()
        mode_label = _position_sizing_mode_label()
        CMD_FEEDBACK = f"⌨️ [kk] Position sizing → {mode_label}"
        CMD_FEEDBACK_CLEAR_AT = time.time() + 5
        LAST_CMD_SHOWN = {"msg": f"[kk] Position sizing → {mode_label}", "until": time.time() + 30}
        send_telegram(
            f"⌨️ SHORTCUT [kk]\n"
            f"Position sizing : {mode_label}\n"
            f"Time : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
        )

    elif key == "tt":
        current = ORDER_TYPE
        try:
            idx = (ORDER_TYPES_CYCLE.index(current) + 1) % len(ORDER_TYPES_CYCLE)
        except ValueError:
            idx = 0
        ORDER_TYPE = ORDER_TYPES_CYCLE[idx]

        if ORDER_TYPE.lower() == "futures" and POSITION_SIZING_MODE == "target_profit":
            POSITION_SIZING_MODE = "margin"
            MIN_MARGIN_PCT = 0.10
        _save_settings()
        order_type_label = "Options" if ORDER_TYPE.lower() == "options" else "Short Futures"
        CMD_FEEDBACK = f"⌨️ [tt] Order type → {order_type_label}"
        CMD_FEEDBACK_CLEAR_AT = time.time() + 5
        LAST_CMD_SHOWN = {"msg": f"[tt] Order type → {order_type_label}", "until": time.time() + 30}
        send_telegram(
            f"⌨️ SHORTCUT [tt]\n"
            f"Order type : {order_type_label}\n"
            f"Time : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
        )

    elif key == "rr":
        _reset_settings_to_defaults()
        CMD_FEEDBACK = "⌨️ [rr] All settings reset to script defaults"
        CMD_FEEDBACK_CLEAR_AT = time.time() + 6
        LAST_CMD_SHOWN = {"msg": "[rr] Reset — margin 10%, Target Profit 10%, account Main, strategy OPENSTRIKE, order type Iron Fly, auto ON", "until": time.time() + 25}
        print("\n🔄 All settings reset to script defaults (margin 10%, Target Profit 10%, Main, OPENSTRIKE, Iron Fly, auto ON).")
        send_telegram(
            f"⌨️ SHORTCUT [rr] — RESET\n"
            f"All settings restored to script defaults.\n"
            f"Margin: 10% | Target Profit: 10% | Account: Main | Strategy: OPENSTRIKE | Order Type: Iron Fly | Auto: ON\n"
            f"Time : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
        )

    elif key == "ll":
        LOG_ENABLED = not LOG_ENABLED
        _save_settings()
        status = "ON" if LOG_ENABLED else "OFF"
        CMD_FEEDBACK = f"⌨️ [ll] Log file → {status}"
        CMD_FEEDBACK_CLEAR_AT = time.time() + 5
        LAST_CMD_SHOWN = {"msg": f"[ll] Log file → {status}", "until": time.time() + 30}
        print(f"\n📋 Log file: {status}", flush=True)
        send_telegram(
            f"⌨️ SHORTCUT [ll]\n"
            f"Log file : {status}\n"
            f"Time : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
        )

    elif key == "ss":
        try:
            restore_tty()
        except:
            pass
        print("\n🔄 RESTARTING SCRIPT ([ss])...", flush=True)
        send_telegram(
            f"🔄 SCRIPT RESTARTING (manual [ss])\n"
            f"Time : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
        )
        time.sleep(0.5)
        os.execv(sys.executable, [sys.executable] + sys.argv)

    elif key == "qq":
        try:
            restore_tty()
        except:
            pass
        print("\n🛑 SAFE EXIT ([qq])", flush=True)
        script_exit_alert("Manual quit (QQ)")
        time.sleep(0.5)
        os._exit(0)

    elif key == "oo":
        OI_CHAIN_VIEW = "single" if OI_CHAIN_VIEW == "both" else "both"
        _save_settings()
        _lbl = "Single (Primary only)" if OI_CHAIN_VIEW == "single" else "Both (BTC + ETH)"
        CMD_FEEDBACK = f"⌨️ [oo] OI Chain → {_lbl}"
        CMD_FEEDBACK_CLEAR_AT = time.time() + 5
        LAST_CMD_SHOWN = {"msg": f"[oo] OI Chain view → {_lbl}", "until": time.time() + 30}
        send_telegram(
            f"⌨️ SHORTCUT [oo]\n"
            f"OI Chain View : {_lbl}\n"
            f"Time : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
        )



    elif key == "00":
        request_strategy_switch("OPENSTRIKE", "atm", "00")
    elif key == "sv":
        request_strategy_switch("STRADDLE", "highest_volume", "sv")
    elif key == "so":
        request_strategy_switch("STRADDLE", "highest_oi", "so")
    elif key == "sf":
        request_strategy_switch("STRADDLE", "vol_oi", "sf")
    elif is_repeating_num and rep_num is not None:
        rank = rep_num
        if rank == 1:
            target_str = "highest_oi"
        elif rank == 2:
            target_str = "2nd_highest"
        elif rank == 3:
            target_str = "3rd_highest"
        elif rank == 4:
            target_str = "4th_highest"
        elif rank == 5:
            target_str = "5th_highest"
        elif rank == 6:
            target_str = "6th_highest"
        elif rank == 7:
            target_str = "7th_highest"
        elif rank == 8:
            target_str = "8th_highest"
        elif rank == 9:
            target_str = "9th_highest"
        else:
            target_str = f"{rank}th_highest"
        request_strategy_switch("OPENSTRIKE", target_str, key)

def keyboard_listener():
    """
    Listens to keyboard inputs in raw/cbreak terminal mode and triggers real-time setting adjustments.
    """
    global KEYBOARD_LISTENER_PAUSED
    fd = sys.stdin.fileno()
    set_cbreak_tty()

    while True:
        if KEYBOARD_LISTENER_PAUSED:
            time.sleep(0.1)
            continue
        if select.select([sys.stdin], [], [], 0.1)[0]:
            if KEYBOARD_LISTENER_PAUSED:
                continue
            try:
                raw = os.read(fd, 4096)
            except OSError:
                continue
            if not raw:
                continue

            if b"\x03" in raw:
                restore_tty()
                print("\n🛑 SAFE EXIT (Ctrl+C)", flush=True)
                script_exit_alert("Ctrl+C")
                sys.exit(0)
            typed = raw.decode("utf-8", errors="ignore").lower()
            typed = "".join(ch for ch in typed if ch not in "\r\n")
            if not typed:
                continue

            if not hasattr(keyboard_listener, "key_buffer"):
                keyboard_listener.key_buffer = ""
            keyboard_listener.key_buffer += typed

            double_letters = {"cc", "mm", "ii", "xx", "aa", "uu", "pp", "kk", "rr", "qq", "tt", "ll", "ss", "oo", "sv", "so", "sf"}
            key = None
            buf = keyboard_listener.key_buffer

            if len(buf) >= 2 and buf[:2] in double_letters:
                key = buf[:2]
                keyboard_listener.key_buffer = buf[2:]
            elif buf.isdigit():
                if len(buf) >= 2 and len(buf) % 2 == 0:
                    half = len(buf) // 2
                    if buf[:half] == buf[half:]:
                        key = buf
                        keyboard_listener.key_buffer = ""
                if len(buf) >= 6:
                    keyboard_listener.key_buffer = buf[-1]
            else:
                if len(buf) >= 2:
                    keyboard_listener.key_buffer = buf[-1]

            if not key:
                continue

            execute_shortcut_action(key)
if sys.stdin.isatty():
    try:
        TTY_OLD_SETTINGS = termios.tcgetattr(sys.stdin.fileno())
        atexit.register(restore_tty)
    except Exception:
        pass
    threading.Thread(target=keyboard_listener, daemon=True).start()
else:
    print("⚠️ Keyboard shortcuts disabled (not running in real terminal)")

def process_telegram_command(text):
    if not text:
        return
    text = text.strip()
    if text.startswith("/"):
        text = text[1:]

    parts = text.split(None, 1)
    cmd = parts[0].strip().lower()
    arg = parts[1].strip() if len(parts) > 1 else None

    if cmd in ("update", "up", "snapshot", "snap"):
        snap = get_latest_ui_snapshot()
        send_telegram_snapshot(snap)
        return

    ctrl_c_aliases = {
        "ctrl c", "ctrl+c", "ctrl-c", "ctrlc",
        "cntl c", "cntl+c", "cntl-c", "cntlc",
        "control c", "control+c", "control-c", "controlc"
    }
    if text.lower() in ctrl_c_aliases:
        execute_shortcut_action("qq")
        return

    if cmd in ("help", "h", "menu", "keys"):
        send_telegram(get_telegram_help_menu())
        return

    allowed_cmds = {
        "cc", "mm", "ii", "xx", "aa", "uu", "pp", "kk", "rr",
        "qq", "tt", "ll", "ss", "oo", "00", "sv", "so", "sf"
    }
    is_rep = False
    if cmd.isdigit() and len(cmd) % 2 == 0:
        half = len(cmd) // 2
        if cmd[:half] == cmd[half:]:
            is_rep = True

    if cmd in allowed_cmds or is_rep:
        if cmd in ("mm", "aa", "uu") and arg is None:
            if cmd == "mm":
                send_telegram("💡 *Usage:* Send `mm <value>` (e.g. `mm 25`) to update limit/margin percentage.")
            elif cmd == "aa":
                send_telegram("💡 *Usage:* Send `aa <name>` (e.g. `aa Sub`) to update account name.")
            elif cmd == "uu":
                send_telegram("💡 *Usage:* Send `uu <name, email, phone>` (e.g. `uu John, john@email.com, 123`) to update user details.")
            return
        execute_shortcut_action(cmd, argument=arg)
    else:
        # Match pattern like "mm50"
        for double_cmd in allowed_cmds:
            if text.lower().startswith(double_cmd) and len(text) > len(double_cmd):
                arg_val = text[len(double_cmd):].strip()
                execute_shortcut_action(double_cmd, argument=arg_val)
                return
        send_telegram(f"⚠️ Telegram Command not recognized: '{text}'. Send `/keys` or `/help` for menu.")

def telegram_polling_thread():
    global TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        print("⚠️ Telegram polling disabled: TELEGRAM_BOT_TOKEN or TELEGRAM_CHAT_ID not set.", flush=True)
        return
    offset = 0
    try:
        url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/getUpdates"
        r = http_get(url, params={"timeout": 0}, timeout=5)
        if r.status_code == 200:
            results = r.json().get("result", [])
            if results:
                offset = results[-1]["update_id"] + 1
    except Exception as e:
        print(f"⚠️ Telegram poll startup check failed: {e}", flush=True)

    while not SCRIPT_EXITED:
        if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
            time.sleep(2)
            continue
        try:
            url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/getUpdates"
            params = {"offset": offset, "timeout": 5}
            r = http_get(url, params=params, timeout=10)
            if r.status_code == 200:
                updates = r.json().get("result", [])
                for update in updates:
                    offset = update["update_id"] + 1
                    message = update.get("message") or update.get("channel_post")
                    if not message:
                        continue
                    chat = message.get("chat") or {}
                    chat_id = str(chat.get("id"))
                    if chat_id != str(TELEGRAM_CHAT_ID):
                        continue
                    text = message.get("text")
                    if text:
                        process_telegram_command(text.strip())
            else:
                time.sleep(2)
        except Exception as e:
            time.sleep(2)

# Start Telegram polling thread in background
threading.Thread(target=telegram_polling_thread, daemon=True).start()

if FORCE_UI_REFRESH:
    FORCE_UI_REFRESH = False

def _fmt_oi(v):
    if v >= 1e6:
        return f"{v/1e6:.2f}M"
    if v >= 1e3:
        return f"{v/1e3:.2f}K"
    return f"{v:.0f}"

def _is_near_atm(p):
    """Check if position delta is near ATM (0.49-0.51)"""
    try:
        d = abs(float(p.get("delta", 0) or 0))
    except (ValueError, TypeError):
        d = 0.0
    return 0.49 <= d <= 0.51

def _is_near_10d(p):
    """Check if position delta is near 10 delta (0.09-0.11)"""
    try:
        d = abs(float(p.get("delta", 0) or 0))
    except (ValueError, TypeError):
        d = 0.0
    return 0.09 <= d <= 0.11

def _fmt_opt_delta(opt, default_val):
    if not opt:
        return default_val
    d = opt.get("delta")
    if d is None:
        return default_val
    try:
        d_val = float(d)
        d_pct = round(d_val * 100.0, 1)
        if abs(d_pct - round(d_pct)) < 1e-5:
            return f"{int(round(d_pct))}D"
        return f"{d_pct}D"
    except (ValueError, TypeError):
        return default_val

def select_or_reuse_hedge(all_opts, target_expiry, option_type, existing_pos, short_opt=None, is_transitioning=False):
    """
    Reuse existing long position if it matches target expiry and strike side relative to short leg.
    - On transition from sell=sell to custom (is_transitioning=True): Select hedge targeting ~10% of sold leg premium.
    - Normally (is_transitioning=False): Select 10 Delta hedge (0.10 delta, Sell 50D / Buy 10D).
    Ensures strike ordering: Long Put strike < Short strike < Long Call strike (Center Strike Positioning).
    """
    short_strike = float(short_opt.get("strike_price") or short_opt.get("strike") or 0.0) if short_opt else 0.0
    short_premium = float(short_opt.get("mark_price", 0) or 0.0) if short_opt else 0.0

    if existing_pos:
        _exist_opt = next((o for o in all_opts if o.get("symbol") == existing_pos["product_symbol"]), None)
        if _exist_opt and _exist_opt.get("expiry") == target_expiry:
            _exist_strike = float(_exist_opt.get("strike_price") or _exist_opt.get("strike") or 0.0)
            if short_strike > 0:
                if option_type == "call" and _exist_strike > short_strike:
                    return _exist_opt
                elif option_type == "put" and _exist_strike < short_strike:
                    return _exist_opt
            else:
                return _exist_opt

    expiry_opts = [o for o in all_opts if o.get("expiry") == target_expiry]

    # Filter candidates based on strike direction relative to short leg (Center Strike Positioning)
    if short_strike > 0:
        if option_type == "call":
            candidates = [o for o in expiry_opts if o.get("type") == "call" and float(o.get("strike_price") or o.get("strike") or 0) > short_strike]
        else:
            candidates = [o for o in expiry_opts if o.get("type") == "put" and float(o.get("strike_price") or o.get("strike") or 0) < short_strike]
    else:
        candidates = [o for o in expiry_opts if o.get("type") == option_type]

    if not candidates:
        candidates = [o for o in expiry_opts if o.get("type") == option_type]

    if not candidates:
        return None

    # Transition rule: Target ~10% premium of sold leg when coming from sell=sell to custom
    if is_transitioning and short_premium > 0:
        target_prem = short_premium * 0.10
        best_cand = min(candidates, key=lambda o: abs(float(o.get("mark_price") or o.get("last_price") or 0) - target_prem))
        return best_cand

    # Normal rule: Select 10 Delta hedge (0.10 delta)
    return select_delta_option(candidates, option_type, 0.10)

def _build_analytics_telegram_summary(spot=None):
    """
    Builds a plain-text (no ANSI color codes) analytics summary for telegram messages.
    """
    global OPENSTRIKE_CALL_DIFF_INFO, OPENSTRIKE_PUT_DIFF_INFO
    global CUSTOM_BASE_THRESHOLD, CUSTOM_ACTIVE_THRESHOLD

    c_old = OPENSTRIKE_CALL_DIFF_INFO.get("old_strike")
    c_old_oi = OPENSTRIKE_CALL_DIFF_INFO.get("old_oi")
    c_new = OPENSTRIKE_CALL_DIFF_INFO.get("new_strike")
    c_new_oi = OPENSTRIKE_CALL_DIFF_INFO.get("new_oi")
    c_pct = OPENSTRIKE_CALL_DIFF_INFO.get("diff_pct")
    c_act = OPENSTRIKE_CALL_DIFF_INFO.get("action", "N/A")

    if isinstance(c_act, str):
        c_act = c_act.replace("\033[1;92m", "").replace("\033[0m", "")

    c_old_oi_str = f"({_fmt_oi(c_old_oi)})" if c_old_oi is not None else ""
    c_new_oi_str = f"({_fmt_oi(c_new_oi)})" if c_new_oi is not None else ""
    c_old_str = f"{int(c_old)}{c_old_oi_str}" if c_old is not None else "None"
    c_new_str = f"{int(c_new)}{c_new_oi_str}" if c_new is not None else "None"
    c_pct_str = f"{c_pct:.2f}%" if c_pct is not None else "N/A"

    p_old = OPENSTRIKE_PUT_DIFF_INFO.get("old_strike")
    p_old_oi = OPENSTRIKE_PUT_DIFF_INFO.get("old_oi")
    p_new = OPENSTRIKE_PUT_DIFF_INFO.get("new_strike")
    p_new_oi = OPENSTRIKE_PUT_DIFF_INFO.get("new_oi")
    p_pct = OPENSTRIKE_PUT_DIFF_INFO.get("diff_pct")
    p_act = OPENSTRIKE_PUT_DIFF_INFO.get("action", "N/A")

    if isinstance(p_act, str):
        p_act = p_act.replace("\033[1;92m", "").replace("\033[0m", "")

    p_old_oi_str = f"({_fmt_oi(p_old_oi)})" if p_old_oi is not None else ""
    p_new_oi_str = f"({_fmt_oi(p_new_oi)})" if p_new_oi is not None else ""
    p_old_str = f"{int(p_old)}{p_old_oi_str}" if p_old is not None else "None"
    p_new_str = f"{int(p_new)}{p_new_oi_str}" if p_new is not None else "None"
    p_pct_str = f"{p_pct:.2f}%" if p_pct is not None else "N/A"

    c_ratio = (c_new_oi / p_new_oi * 100.0) if p_new_oi and p_new_oi > 0.0 else 0.0
    p_ratio = (p_new_oi / c_new_oi * 100.0) if c_new_oi and c_new_oi > 0.0 else 0.0

    if CUSTOM_BASE_THRESHOLD == 0.25 and CUSTOM_ACTIVE_THRESHOLD == 0.50:
        custom_display = "Custom: [25% / 50% Active] │ 50% / 75% │ 75% / 100%"
    elif CUSTOM_BASE_THRESHOLD == 0.50 and CUSTOM_ACTIVE_THRESHOLD == 0.75:
        custom_display = "Custom: 25% / 50% │ [50% / 75% Active] │ 75% / 100%"
    else:
        custom_display = "Custom: 25% / 50% │ 50% / 75% │ [75% / 100% Active]"

    spot_str = f" [Spot: {spot:.0f}]" if spot is not None else ""
    summary = f"\n\n🎯 OPENSTRIKE — Analytics{spot_str}\n"
    summary += f"📊 LIMITS: Roll 10% (Active) │ {custom_display} [cc]\n"
    summary += f"  Call Strike : Old={c_old_str} │ New={c_new_str} │ Diff={c_pct_str} │ OppOI%={c_ratio:.1f}%\n  Action: {c_act}\n"
    summary += f"  Put Strike  : Old={p_old_str} │ New={p_new_str} │ Diff={p_pct_str} │ OppOI%={p_ratio:.1f}%\n  Action: {p_act}"
    return summary

def check_oppoi_25pct_change(c_oi, p_oi, side=None):
    global LAST_ALERTED_CALL_OPPOI_STEP, LAST_ALERTED_PUT_OPPOI_STEP, LAST_CROSS_DOWN_SIDE
    if c_oi <= 0 and p_oi <= 0:
        return
    c_ratio = (c_oi / p_oi * 100.0) if (p_oi and p_oi > 0) else 0.0
    p_ratio = (p_oi / c_oi * 100.0) if (c_oi and c_oi > 0) else 0.0

    c_step = int(c_ratio // 25) * 25
    p_step = int(p_ratio // 25) * 25

    if LAST_ALERTED_CALL_OPPOI_STEP is None or LAST_ALERTED_PUT_OPPOI_STEP is None:
        LAST_ALERTED_CALL_OPPOI_STEP = c_step
        LAST_ALERTED_PUT_OPPOI_STEP = p_step
        _save_settings()
        return

    target_side = side or LAST_CROSS_DOWN_SIDE
    if target_side == "None":
        if c_ratio < p_ratio:
            target_side = "Call Strike"
        elif p_ratio < c_ratio:
            target_side = "Put Strike"

    triggered = False
    reasons = []

    if target_side in ("Call Strike", "None") and c_step != LAST_ALERTED_CALL_OPPOI_STEP:
        old_step = LAST_ALERTED_CALL_OPPOI_STEP
        if c_step < old_step:
            crossed_lvl = old_step
            reasons.append(f"• Call OppOI%: *{c_ratio:.1f}%* (crossed {crossed_lvl}% level — dropped below {crossed_lvl}%)")
        else:
            crossed_lvl = c_step
            reasons.append(f"• Call OppOI%: *{c_ratio:.1f}%* (crossed {crossed_lvl}% level — rose above {crossed_lvl}%)")
        LAST_ALERTED_CALL_OPPOI_STEP = c_step
        triggered = True

    if target_side in ("Put Strike", "None") and p_step != LAST_ALERTED_PUT_OPPOI_STEP:
        old_step = LAST_ALERTED_PUT_OPPOI_STEP
        if p_step < old_step:
            crossed_lvl = old_step
            reasons.append(f"• Put OppOI%: *{p_ratio:.1f}%* (crossed {crossed_lvl}% level — dropped below {crossed_lvl}%)")
        else:
            crossed_lvl = p_step
            reasons.append(f"• Put OppOI%: *{p_ratio:.1f}%* (crossed {crossed_lvl}% level — rose above {crossed_lvl}%)")
        LAST_ALERTED_PUT_OPPOI_STEP = p_step
        triggered = True

    if triggered:
        _save_settings()
        msg = "📢 *OPENSTRIKE — 25% OppOI% Crossing Alert*\n" + "\n".join(reasons) + f"\n\n📊 *Current Ratios:* Call={c_ratio:.1f}% │ Put={p_ratio:.1f}%"
        try:
            send_telegram(msg)
        except Exception as e:
            print("⚠️ Error sending OppOI 25% alert:", e)

PRICE_CHANGE_ADV_THRESHOLD_PCT = 0.25
PRICE_CHANGE_BAR_WIDTH = 24
PRICE_CHANGE_CACHE_SEC = 2.0
LAST_PRICE_CHANGE_DISTRIBUTION = None
LAST_PRICE_CHANGE_DISTRIBUTION_AT = 0.0

def fetch_price_change_distribution(refresh=False):
    global LAST_PRICE_CHANGE_DISTRIBUTION, LAST_PRICE_CHANGE_DISTRIBUTION_AT
    now_ts = time.time()
    if (
        not refresh
        and LAST_PRICE_CHANGE_DISTRIBUTION is not None
        and (now_ts - LAST_PRICE_CHANGE_DISTRIBUTION_AT) < PRICE_CHANGE_CACHE_SEC
    ):
        return LAST_PRICE_CHANGE_DISTRIBUTION
    try:
        result = fetch_all_tickers(refresh=refresh)
        universe = 0
        advancers = 0
        threshold = PRICE_CHANGE_ADV_THRESHOLD_PCT
        for t in result:
            if t.get("contract_type") != "perpetual_futures":
                continue
            trading_status = str(t.get("product_trading_status") or "").lower()
            if trading_status and trading_status != "operational":
                continue
            raw_change = t.get("mark_change_24h")
            try:
                change_pct = float(raw_change) if raw_change is not None else None
            except (ValueError, TypeError):
                change_pct = None
            if change_pct is None:
                try:
                    open_px = float(t.get("open", 0) or 0)
                    mark_px = float(t.get("mark_price", 0) or 0)
                    if open_px <= 0 or mark_px <= 0:
                        continue
                    change_pct = ((mark_px - open_px) / open_px) * 100
                except (ValueError, TypeError, ZeroDivisionError):
                    continue
            universe += 1
            if change_pct > threshold:
                advancers += 1
        if universe > 0:
            LAST_PRICE_CHANGE_DISTRIBUTION = {
                "advancers": advancers,
                "decliners": max(universe - advancers, 0),
                "universe": universe,
                "threshold_pct": threshold,
                "basis": "mark_change_24h",
            }
            LAST_PRICE_CHANGE_DISTRIBUTION_AT = now_ts
    except Exception as e:
        api_failure_alert("SPOT", e)
    return LAST_PRICE_CHANGE_DISTRIBUTION

def _render_price_change_distribution_bar(dist):
    if not dist:
        return ""
    decliners = int(dist.get("decliners", 0) or 0)
    advancers = int(dist.get("advancers", 0) or 0)
    total = decliners + advancers
    if total <= 0:
        return ""
    red_blocks = int(round((decliners / total) * PRICE_CHANGE_BAR_WIDTH))
    red_blocks = max(0, min(PRICE_CHANGE_BAR_WIDTH, red_blocks))
    if decliners > 0 and red_blocks == 0:
        red_blocks = 1
    if advancers > 0 and red_blocks == PRICE_CHANGE_BAR_WIDTH:
        red_blocks -= 1
    green_blocks = PRICE_CHANGE_BAR_WIDTH - red_blocks
    red = "\033[91m"
    green = "\033[92m"
    reset = "\033[0m"
    return f"{red}{'█' * red_blocks}{reset}{green}{'█' * green_blocks}{reset}"

def build_price_change_ui_kwargs(
    symbol_primary=None,
    spot_primary=None,
    symbol_secondary=None,
    spot_secondary=None,
    update_state=False,
):
    dist = fetch_price_change_distribution(refresh=update_state)
    if not dist:
        return {
            "market_price_change_header": None,
            "market_price_change_bar": None,
            "market_price_change_counts": None,
        }
    universe = int(dist.get("universe", 0) or 0)
    advancers = int(dist.get("advancers", 0) or 0)
    decliners = int(dist.get("decliners", 0) or 0)
    threshold = float(dist.get("threshold_pct", PRICE_CHANGE_ADV_THRESHOLD_PCT) or PRICE_CHANGE_ADV_THRESHOLD_PCT)
    adv_pct = (advancers / universe * 100) if universe > 0 else 0
    dec_pct = (decliners / universe * 100) if universe > 0 else 0
    return {
        "market_price_change_header": f"📉 Price Change Dist: Perpetuals 24h mark (>{threshold:.2f}% = Advancers)",
        "market_price_change_bar": f"{_render_price_change_distribution_bar(dist)}  D {dec_pct:.1f}%  │  A {adv_pct:.1f}%",
        "market_price_change_counts": f"Decliners: {decliners}  │  Advancers: {advancers}  │  Universe: {universe}",
    }

def render_terminal_ui(
    # Renders the live terminal dashboard showing account stats, API health, Greeks, and active positions.
    now, spot, decision, source,
    bal, blocked, upnl,
    wallet_upnl_pct, blocked_upnl_pct,
    used_pct_ui, heat_level, heat_bar,
    delta, gamma,
    position_details, position_count,
    execution_status,
    used_pct_calc, margin_drift, drift_status, drift_icon,
    api_score, api_status, api_bar,
    expiry_oi_list=None,
    expiry_oi_list_secondary=None,
    spot_secondary=None,
    symbol_secondary=None,
    symbol_primary=None,
    all_expiry_max_pain_primary=None,
    all_expiry_max_pain_secondary=None,
    projected_profit=None,
    max_loss=None,
    position_delta_sum=None,
    position_gamma_sum=None,
    position_theta_sum=None,
    position_vega_sum=None,
    position_rho_sum=None,
    strike_order_ok=None,
    strike_order_msg=None,
    option_metrics=None,
    last_executed_signal=None,
    market_price_change_header=None,
    market_price_change_bar=None,
    market_price_change_counts=None,
):
    import os
    global CMD_FEEDBACK, CMD_FEEDBACK_CLEAR_AT, LAST_CMD_SHOWN
    global LAST_VISIBLE_UI_AT, LAST_LIVE_UI_RENDER_AT, LAST_HEARTBEAT_PRINT_AT, LIVE_RENDER_COUNT
    if CMD_FEEDBACK and CMD_FEEDBACK_CLEAR_AT > 0 and time.time() > CMD_FEEDBACK_CLEAR_AT:
        CMD_FEEDBACK = ""
        CMD_FEEDBACK_CLEAR_AT = 0.0
    with UI_PRINT_LOCK:
        now_ts = time.time()
        LAST_LIVE_UI_RENDER_AT = now_ts
        LAST_VISIBLE_UI_AT = now_ts
        LAST_HEARTBEAT_PRINT_AT = now_ts
        LIVE_RENDER_COUNT += 1
        live_clock = now.strftime("%H:%M:%S") if hasattr(now, "strftime") else str(now)

        print("\033[2J\033[H", end="", flush=True)
        print("\n" * 4)
        print("┌──────────────────────────────────────────────────────────────────────────────")
        print(f"│ 👤 User: {MAIN_ACCOUNT['username']}")
        print(f"│ 📧 Email: {MAIN_ACCOUNT['email']}")
        print(f"│ 📞 Phone: {MAIN_ACCOUNT['phone']}")
        print("│──────────────────────────────────────────────────────────────────────────────")
        print(f"│ ⏰ Time: {now}")
        if STRATEGY_MODE in ("OPENSTRIKE", "STRADDLE"):
            print(f"│ 🤖 Strat: {STRATEGY_MODE} - {OPENSTRIKE_TARGET_STRIKE}")
        else:
            print(f"│ 🤖 Strat: {STRATEGY_MODE}")

        print(f"│ 📡 Source: {source}")
        exec_on = "ON" if USER_AUTO_EXECUTION else "OFF"
        system_ok = "OK" if CAN_EXECUTE else "BLOCKED"
        log_on = "ON" if LOG_ENABLED else "OFF"
        print(f"│ ⚙️ Exec Status: {exec_on} │ {system_ok} │ Log: {log_on} │ {execution_status}")

        _bias_display = last_executed_signal if last_executed_signal is not None else decision
        print(f"│ 🎯 Bias: {_bias_display}")

        print("│")

        switch_next = "ETH" if SYMBOL == "BTC" else "BTC"
        _main_label = (symbol_primary or SYMBOL)
        print(f"│ 📌 Instrument: {_main_label} (Main)  │  💹 Spot {spot:.2f}")
        if INSTRUMENT_SWITCH_PENDING:
            print(f"│   ⏳ SWITCH PENDING → {switch_next} (on next signal)")
        if CMD_FEEDBACK:
            print(f"│   {CMD_FEEDBACK}")
        OI_CW = 11
        OI_PCR_W = 6
        el = expiry_oi_list or []
        openstrike_item = next((item for item in el if item[0] == "OPENSTRIKE_MSG"), None)
        normal_items = [item for item in el if item[0] != "OPENSTRIKE_MSG"]
        _strike_tbl_cnt = openstrike_item[5] if openstrike_item and len(openstrike_item) > 5 else []
        _final_N = (len(_strike_tbl_cnt) - 1) // 2 if _strike_tbl_cnt else 9
        if openstrike_item:
            print("│")
            _os_spot     = openstrike_item[7] if len(openstrike_item) > 7 else spot
            _strike_tbl  = openstrike_item[5] if len(openstrike_item) > 5 else []
            _counts      = openstrike_item[6] if len(openstrike_item) > 6 else []
            _calls_cnt   = _counts[0] if len(_counts) > 0 else 0
            _puts_cnt    = _counts[1] if len(_counts) > 1 else 0
            print(f"│ 🎯 OPENSTRIKE — Analytics  [Spot: {_os_spot:.0f}]  [Available Strikes: Calls={_calls_cnt}, Puts={_puts_cnt}]")

            # Strike Lock / Roll limits (10% Rule)
            c_old = OPENSTRIKE_CALL_DIFF_INFO.get("old_strike")
            c_old_oi = OPENSTRIKE_CALL_DIFF_INFO.get("old_oi")
            c_new = OPENSTRIKE_CALL_DIFF_INFO.get("new_strike")
            c_new_oi = OPENSTRIKE_CALL_DIFF_INFO.get("new_oi")
            c_pct = OPENSTRIKE_CALL_DIFF_INFO.get("diff_pct")
            c_act = OPENSTRIKE_CALL_DIFF_INFO.get("action", "N/A")

            c_old_oi_str = f"({_fmt_oi(c_old_oi)})" if c_old_oi is not None else ""
            c_new_oi_str = f"({_fmt_oi(c_new_oi)})" if c_new_oi is not None else ""
            c_old_str = f"{int(c_old)}{c_old_oi_str}" if c_old is not None else "None"
            c_new_str = f"{int(c_new)}{c_new_oi_str}" if c_new is not None else "None"
            c_pct_str = f"{c_pct:.2f}%" if c_pct is not None else "N/A"

            p_old = OPENSTRIKE_PUT_DIFF_INFO.get("old_strike")
            p_old_oi = OPENSTRIKE_PUT_DIFF_INFO.get("old_oi")
            p_new = OPENSTRIKE_PUT_DIFF_INFO.get("new_strike")
            p_new_oi = OPENSTRIKE_PUT_DIFF_INFO.get("new_oi")
            p_pct = OPENSTRIKE_PUT_DIFF_INFO.get("diff_pct")
            p_act = OPENSTRIKE_PUT_DIFF_INFO.get("action", "N/A")

            p_old_oi_str = f"({_fmt_oi(p_old_oi)})" if p_old_oi is not None else ""
            p_new_oi_str = f"({_fmt_oi(p_new_oi)})" if p_new_oi is not None else ""
            p_old_str = f"{int(p_old)}{p_old_oi_str}" if p_old is not None else "None"
            p_new_str = f"{int(p_new)}{p_new_oi_str}" if p_new is not None else "None"
            p_pct_str = f"{p_pct:.2f}%" if p_pct is not None else "N/A"
            c_ratio = (c_new_oi / p_new_oi * 100.0) if p_new_oi and p_new_oi > 0.0 else 0.0
            p_ratio = (p_new_oi / c_new_oi * 100.0) if c_new_oi and c_new_oi > 0.0 else 0.0

            if CUSTOM_BASE_THRESHOLD == 0.25 and CUSTOM_ACTIVE_THRESHOLD == 0.50:
                custom_display = "Custom: \033[1;92m[25% / 50% Active]\033[0m │ 50% / 75% │ 75% / 100%"
            elif CUSTOM_BASE_THRESHOLD == 0.50 and CUSTOM_ACTIVE_THRESHOLD == 0.75:
                custom_display = "Custom: 25% / 50% │ \033[1;92m[50% / 75% Active]\033[0m │ 75% / 100%"
            else:
                custom_display = "Custom: 25% / 50% │ 50% / 75% │ \033[1;92m[75% / 100% Active]\033[0m"

            print(f"│   📊 LIMITS: Roll 10% (Active) │ {custom_display} [cc]")
            print(f"│     Call Strike : Old={c_old_str:<14} │ New={c_new_str:<14} │ Diff={c_pct_str:<7} │ OppOI%={c_ratio:>5.1f}% │ Action: {c_act}")
            print(f"│     Put Strike  : Old={p_old_str:<14} │ New={p_new_str:<14} │ Diff={p_pct_str:<7} │ OppOI%={p_ratio:>5.1f}% │ Action: {p_act}")
            print("│   ──────────────────────────────────────────────────────────────────────────")

            _COI  = 10
            _STR  = 8
            _POI  = 10
            _SEP  = f"│   {'CALL OI':<{_COI}}  {'STRIKE':^{_STR}}  {'PUT OI':>{_POI}}"
            _LINE = f"│   {'─'*_COI}  {'─'*_STR}  {'─'*_POI}"
            print(_SEP)
            print(_LINE)

            c_opt = openstrike_item[3]
            p_opt = openstrike_item[4]
            c_info = ""
            p_info = ""
            target_label = OPENSTRIKE_TARGET_STRIKE
            if c_opt:
                c_exp = c_opt.get('expiry')
                c_exp_str = c_exp.strftime("%d-%b-%Y") if hasattr(c_exp, "strftime") else (str(c_exp) if c_exp else "?")
                c_info = f"  │  {target_label} Call: {c_opt.get('strike')}  OI: {_fmt_oi(c_opt.get('oi', 0)):>{OI_CW-3}}  │  Expiry: {c_exp_str}"
            if p_opt:
                p_exp = p_opt.get('expiry')
                p_exp_str = p_exp.strftime("%d-%b-%Y") if hasattr(p_exp, "strftime") else (str(p_exp) if p_exp else "?")
                p_info = f"  │  {target_label} Put:  {p_opt.get('strike')}  OI: {_fmt_oi(p_opt.get('oi', 0)):>{OI_CW-3}}  │  Expiry: {p_exp_str}"

            atm_info = ""
            if all_expiry_max_pain_primary is not None or normal_items:
                parts = []
                if all_expiry_max_pain_primary is not None:
                    parts.append(f"MaxPain: {int(all_expiry_max_pain_primary)}")
                if normal_items:
                    total_call = sum(i[1] for i in normal_items)
                    total_put = sum(i[2] for i in normal_items)
                    pcr_all = round(total_put / total_call, 2) if total_call else 0
                    parts.append(f"PCR: {pcr_all:.2f}")
                if parts:
                    atm_info = "  │  " + "  │  ".join(parts)

            for _row in _strike_tbl:
                _s   = _row['strike']
                _coi = _row['call_oi']
                _poi = _row['put_oi']
                _atm = _row.get('is_atm', False)
                _mc  = _row.get('is_max_call', False)
                _mp  = _row.get('is_max_put',  False)
                _is_straddle = _row.get('is_straddle', False)

                _c_tag = "★" if _mc else " "
                _p_tag = "★" if _mp else " "
                _c_str = f"{_c_tag}{_fmt_oi(_coi):>{_COI-1}}"
                _p_str = f"{_fmt_oi(_poi):>{_POI-1}}{_p_tag}"

                _s_str = f"{int(_s):^{_STR}}"
                if _is_straddle:
                    _s_str = f"\033[1;96m{_s_str}\033[0m"

                _side_text = ""
                if _mc:
                    _side_text = c_info
                elif _mp:
                    _side_text = p_info

                if _is_straddle:
                    _side_text += "  │  Straddle Target"

                if _atm:
                    print(f"│   {'═'*_COI}  {'═'*_STR}  {'═'*_POI}")
                    print(f"│   {_c_str}  {_s_str}  {_p_str} ◄ ATM{atm_info}{_side_text}")
                    print(f"│   {'═'*_COI}  {'═'*_STR}  {'═'*_POI}")
                else:
                    print(f"│   {_c_str}  {_s_str}  {_p_str}{_side_text}")
            if not _strike_tbl:
                if c_opt:
                    c_exp = c_opt.get('expiry')
                    c_exp_str = c_exp.strftime("%d-%b-%Y") if hasattr(c_exp, "strftime") else (str(c_exp) if c_exp else "?")
                    print(f"│   Highest Call Strike: {c_opt.get('strike'):<10} OI: {_fmt_oi(c_opt.get('oi', 0)):>{OI_CW}}  │  Expiry: {c_exp_str}")
                if p_opt:
                    p_exp = p_opt.get('expiry')
                    p_exp_str = p_exp.strftime("%d-%b-%Y") if hasattr(p_exp, "strftime") else (str(p_exp) if p_exp else "?")
                    print(f"│   Highest Put Strike:  {p_opt.get('strike'):<10} OI: {_fmt_oi(p_opt.get('oi', 0)):>{OI_CW}}  │  Expiry: {p_exp_str}")

        else:
            for item in normal_items:
                exp, call_oi, put_oi, pcr = item[0], item[1], item[2], item[3]
                mp = item[4] if len(item) > 4 else None
                exp_str = exp.strftime("%d-%b-%Y") if hasattr(exp, "strftime") else str(exp)
                mp_str = f"  │  MaxPain: {int(mp)}" if mp is not None else ""
                print(f"│   {exp_str:<12} : {_fmt_oi(call_oi):>{OI_CW}}  │  {_fmt_oi(put_oi):>{OI_CW}}  │  PCR {pcr:>{OI_PCR_W}.2f}{mp_str}")
            if normal_items:
                total_call = sum(i[1] for i in normal_items)
                total_put = sum(i[2] for i in normal_items)
                pcr_all = round(total_put / total_call, 2) if total_call else 0
                mp_primary_str = f"  │  MaxPain: {int(all_expiry_max_pain_primary)}" if all_expiry_max_pain_primary is not None else ""
                print(f"│   {'All Expiry':<12} : {_fmt_oi(total_call):>{OI_CW}}  │  {_fmt_oi(total_put):>{OI_CW}}  │  PCR {pcr_all:>{OI_PCR_W}.2f}{mp_primary_str}")

        try:
            tickers = fetch_all_tickers(refresh=False)
            straddles = []
            prefix = f"MV-{SYMBOL}-"
            for t in tickers:
                sym_name = t.get("symbol", "")
                if sym_name.startswith(prefix):
                    straddles.append({
                        "symbol": sym_name,
                        "price": safe_float(t.get("mark_price")),
                        "change": safe_float(t.get("ltp_change_24h")),
                        "turnover": safe_float(t.get("turnover")),
                        "oi": safe_float(t.get("oi_value_usd")),
                    })
            straddles.sort(key=lambda x: x["turnover"], reverse=True)
            if straddles:
                max_vol_sym = max(straddles, key=lambda x: x["turnover"])["symbol"]
                max_oi_sym = max(straddles, key=lambda x: x["oi"])["symbol"]
                straddles = [s for s in straddles if s["symbol"] in (max_vol_sym, max_oi_sym)]
                print("│")
                print("│ 🎯 Straddle (Move Options) — Sorted by 24h Vol")
                _SCO = 22
                _SPR = 10
                _SCH = 10
                _SVO = 10
                _SOI = 14
                print(f"│   {'Contract':<{_SCO}}  {'Last Price':>{_SPR}}  {'24h Chg.':>{_SCH}}  {'24h Vol.':>{_SVO}}  {'Open Interest':>{_SOI}}")
                print(f"│   {'─'*_SCO}  {'─'*_SPR}  {'─'*_SCH}  {'─'*_SVO}  {'─'*_SOI}")
                for s in straddles:
                    px = s["price"]
                    px_str = f"${px:.1f}" if px % 1 != 0 else f"${px:.0f}"
                    ch = s["change"]
                    ch_str = f"{ch:+.2f}%"
                    vol_str = _fmt_oi(s["turnover"])
                    oi_str = _fmt_oi(s["oi"])

                    tags = []
                    if s["symbol"] == max_vol_sym:
                        tags.append("Highest Vol")
                    if s["symbol"] == max_oi_sym:
                        tags.append("Highest OI")

                    tag_str = f" ◄ {' & '.join(tags)}" if tags else ""
                    print(f"│   {s['symbol']:<{_SCO}}  {px_str:>{_SPR}}  {ch_str:>{_SCH}}  {vol_str:>{_SVO}}  {oi_str:>{_SOI}}{tag_str}")
                    
                    analysis = analyze_straddle_sentiment(s["symbol"])
                    if analysis:
                        sent_str = f"{analysis['color_code']}{analysis['sentiment']}\033[0m"
                        p_ch_str = f"{analysis['price_change_pct']:+.2f}%"
                        o_ch_str = f"{analysis['oi_change_pct']:+.2f}%"
                        print(f"│      ↳ Sentiment ({int(analysis['time_diff_min'])}m change): {sent_str} (Price: {p_ch_str}, OI: {o_ch_str})")
        except Exception:
            pass

        sec_oi_list = expiry_oi_list_secondary or []
        sec_openstrike_item = next((item for item in sec_oi_list if item[0] == "OPENSTRIKE_MSG"), None)
        sec_normal_items = [item for item in sec_oi_list if item[0] != "OPENSTRIKE_MSG"]
        if OI_CHAIN_VIEW == "both" and symbol_secondary and spot_secondary is not None and sec_oi_list:
            print("│")
            print(f"│ 📌 Instrument: {symbol_secondary} (Secondary)  │  💹 Spot {spot_secondary:.2f}")
            if sec_openstrike_item:
                _sec_spot    = sec_openstrike_item[7] if len(sec_openstrike_item) > 7 else (spot_secondary or 0)
                _sec_tbl     = sec_openstrike_item[5] if len(sec_openstrike_item) > 5 else []

                sec_c_opt = sec_openstrike_item[3]
                sec_p_opt = sec_openstrike_item[4]
                sec_c_info = ""
                sec_p_info = ""
                if sec_c_opt:
                    sc_exp = sec_c_opt.get('expiry')
                    sc_exp_str = sc_exp.strftime("%d-%b-%Y") if hasattr(sc_exp, "strftime") else (str(sc_exp) if sc_exp else "?")
                    sec_c_info = f"  │  {target_label} Call: {sec_c_opt.get('strike')}  OI: {_fmt_oi(sec_c_opt.get('oi', 0)):>{OI_CW-3}}  │  Expiry: {sc_exp_str}"
                if sec_p_opt:
                    sp_exp = sec_p_opt.get('expiry')
                    sp_exp_str = sp_exp.strftime("%d-%b-%Y") if hasattr(sp_exp, "strftime") else (str(sp_exp) if sp_exp else "?")
                    sec_p_info = f"  │  {target_label} Put:  {sec_p_opt.get('strike')}  OI: {_fmt_oi(sec_p_opt.get('oi', 0)):>{OI_CW-3}}  │  Expiry: {sp_exp_str}"

                sec_atm_info = ""
                if all_expiry_max_pain_secondary is not None or sec_normal_items:
                    parts = []
                    if all_expiry_max_pain_secondary is not None:
                        parts.append(f"MaxPain: {int(all_expiry_max_pain_secondary)}")
                    if sec_normal_items:
                        total_call = sum(i[1] for i in sec_normal_items)
                        total_put = sum(i[2] for i in sec_normal_items)
                        pcr_all = round(total_put / total_call, 2) if total_call else 0
                        parts.append(f"PCR: {pcr_all:.2f}")
                    if parts:
                        sec_atm_info = "  │  " + "  │  ".join(parts)

                _COI  = 10
                _STR  = 8
                _POI  = 10
                print(f"│   {'CALL OI':<{_COI}}  {'STRIKE':^{_STR}}  {'PUT OI':>{_POI}}")
                print(f"│   {'─'*_COI}  {'─'*_STR}  {'─'*_POI}")
                for _row in _sec_tbl:
                    _s   = _row['strike']
                    _coi = _row['call_oi']
                    _poi = _row['put_oi']
                    _atm = _row.get('is_atm', False)
                    _mc  = _row.get('is_max_call', False)
                    _mp  = _row.get('is_max_put',  False)
                    _c_tag = "★" if _mc else " "
                    _p_tag = "★" if _mp else " "
                    _c_str = f"{_c_tag}{_fmt_oi(_coi):>{_COI-1}}"
                    _p_str = f"{_fmt_oi(_poi):>{_POI-1}}{_p_tag}"
                    _s_str = f"{int(_s):^{_STR}}"

                    _side_text = ""
                    if _mc:
                        _side_text = sec_c_info
                    elif _mp:
                        _side_text = sec_p_info

                    if _atm:
                        print(f"│   {'═'*_COI}  {'═'*_STR}  {'═'*_POI}")
                        print(f"│   {_c_str}  {_s_str}  {_p_str} ◄ ATM{sec_atm_info}{_side_text}")
                        print(f"│   {'═'*_COI}  {'═'*_STR}  {'═'*_POI}")
                    else:
                        print(f"│   {_c_str}  {_s_str}  {_p_str}{_side_text}")
                if not _sec_tbl:
                    if sec_c_opt:
                        c_exp = sec_c_opt.get('expiry')
                        c_exp_str = c_exp.strftime("%d-%b-%Y") if hasattr(c_exp, "strftime") else (str(c_exp) if c_exp else "?")
                        print(f"│   Highest Call Strike: {sec_c_opt.get('strike'):<10} OI: {_fmt_oi(sec_c_opt.get('oi', 0)):>{OI_CW}}  │  Expiry: {c_exp_str}")
                    if sec_p_opt:
                        p_exp = sec_p_opt.get('expiry')
                        p_exp_str = p_exp.strftime("%d-%b-%Y") if hasattr(p_exp, "strftime") else (str(p_exp) if p_exp else "?")
                        print(f"│   Highest Put Strike:  {sec_p_opt.get('strike'):<10} OI: {_fmt_oi(p_opt.get('oi', 0)):>{OI_CW}}  │  Expiry: {p_exp_str}")

            else:
                for item in sec_normal_items:
                    exp, call_oi, put_oi, pcr = item[0], item[1], item[2], item[3]
                    mp = item[4] if len(item) > 4 else None
                    exp_str = exp.strftime("%d-%b-%Y") if hasattr(exp, "strftime") else str(exp)
                    mp_str = f"  │  MaxPain: {int(mp)}" if mp is not None else ""
                    print(f"│   {exp_str:<12} : {_fmt_oi(call_oi):>{OI_CW}}  │  {_fmt_oi(put_oi):>{OI_CW}}  │  PCR {pcr:>{OI_PCR_W}.2f}{mp_str}")
                if sec_normal_items:
                    total_call = sum(i[1] for i in sec_normal_items)
                    total_put = sum(i[2] for i in sec_normal_items)
                    pcr_all = round(total_put / total_call, 2) if total_call else 0
                    mp_sec_str = f"  │  MaxPain: {int(all_expiry_max_pain_secondary)}" if all_expiry_max_pain_secondary is not None else ""
                    print(f"│   {'All Expiry':<12} : {_fmt_oi(total_call):>{OI_CW}}  │  {_fmt_oi(total_put):>{OI_CW}}  │  PCR {pcr_all:>{OI_PCR_W}.2f}{mp_sec_str}")

            try:
                tickers = fetch_all_tickers(refresh=False)
                straddles = []
                prefix = f"MV-{symbol_secondary}-"
                for t in tickers:
                    sym_name = t.get("symbol", "")
                    if sym_name.startswith(prefix):
                        straddles.append({
                            "symbol": sym_name,
                            "price": safe_float(t.get("mark_price")),
                            "change": safe_float(t.get("ltp_change_24h")),
                            "turnover": safe_float(t.get("turnover")),
                            "oi": safe_float(t.get("oi_value_usd")),
                        })
                straddles.sort(key=lambda x: x["turnover"], reverse=True)
                if straddles:
                    max_vol_sym = max(straddles, key=lambda x: x["turnover"])["symbol"]
                    max_oi_sym = max(straddles, key=lambda x: x["oi"])["symbol"]
                    straddles = [s for s in straddles if s["symbol"] in (max_vol_sym, max_oi_sym)]
                    print("│")
                    print("│ 🎯 Straddle (Move Options) — Sorted by 24h Vol")
                    _SCO = 22
                    _SPR = 10
                    _SCH = 10
                    _SVO = 10
                    _SOI = 14
                    print(f"│   {'Contract':<{_SCO}}  {'Last Price':>{_SPR}}  {'24h Chg.':>{_SCH}}  {'24h Vol.':>{_SVO}}  {'Open Interest':>{_SOI}}")
                    print(f"│   {'─'*_SCO}  {'─'*_SPR}  {'─'*_SCH}  {'─'*_SVO}  {'─'*_SOI}")
                    for s in straddles:
                        px = s["price"]
                        px_str = f"${px:.1f}" if px % 1 != 0 else f"${px:.0f}"
                        ch = s["change"]
                        ch_str = f"{ch:+.2f}%"
                        vol_str = _fmt_oi(s["turnover"])
                        oi_str = _fmt_oi(s["oi"])

                        tags = []
                        if s["symbol"] == max_vol_sym:
                            tags.append("Highest Vol")
                        if s["symbol"] == max_oi_sym:
                            tags.append("Highest OI")

                        tag_str = f" ◄ {' & '.join(tags)}" if tags else ""
                        print(f"│   {s['symbol']:<{_SCO}}  {px_str:>{_SPR}}  {ch_str:>{_SCH}}  {vol_str:>{_SVO}}  {oi_str:>{_SOI}}{tag_str}")
                        
                        analysis = analyze_straddle_sentiment(s["symbol"])
                        if analysis:
                            sent_str = f"{analysis['color_code']}{analysis['sentiment']}\033[0m"
                            p_ch_str = f"{analysis['price_change_pct']:+.2f}%"
                            o_ch_str = f"{analysis['oi_change_pct']:+.2f}%"
                            print(f"│      ↳ Sentiment ({int(analysis['time_diff_min'])}m change): {sent_str} (Price: {p_ch_str}, OI: {o_ch_str})")
            except Exception:
                pass
        if market_price_change_header or market_price_change_bar or market_price_change_counts:
            print("│")
            if market_price_change_header:
                print(f"│ {market_price_change_header}")
            if market_price_change_bar:
                print(f"│   {market_price_change_bar}")
            if market_price_change_counts:
                print(f"│   {market_price_change_counts}")
        print("│")

        API_W = 16
        print(f"│   {'🩺 API STATUS':<{API_W}}: Health + Latency")
        for api in ["SPOT", "WALLET", "ORDERS", "POSITIONS"]:
            latency = API_LATENCY.get(api, -1)
            if not HEALTH.get(api):
                print(f"│   {api:<{API_W}}: 🔴 DOWN ❌")
            else:
                print(f"│   {api:<{API_W}}: {latency_status(latency):<12} {latency} ms")
        print(f"│   🌐 API HEALTH: {api_bar} {api_score}%")

        print("│")

        if POSITION_SIZING_MODE == "max_loss":
            active_pct_label = "Max loss"
            active_pct = MAX_LOSS_CAP_PCT
        elif POSITION_SIZING_MODE == "target_profit":
            active_pct_label = "Target profit"
            active_pct = TARGET_PROFIT_PCT
        else:
            active_pct_label = "Min margin"
            active_pct = MIN_MARGIN_PCT

        if active_pct >= 0.99:
            pct_label = "100%"
        elif 0.09 <= active_pct <= 0.11:
            pct_label = "10%"
        elif 0.009 <= active_pct <= 0.011:
            pct_label = "1%"
        else:
            pct_label = f"{round(active_pct * 100)}%"
        print(f"│ 🎚️ {active_pct_label}: {pct_label} [mm]: set % (1-100)")
        print(f"│ 📏 Position sizing: {_position_sizing_mode_label()} [kk]")
        print(f"│ 📊 Used Bar: {heat_bar} {used_pct_ui}%")
        print(f"│ 📐 MARGIN DRIFT: {margin_drift:+.1f}%")
        print("│")
        print(f"│ 💰 Wallet Balance: ${bal:.2f}")
        wallet_upnl_str = f"│ UPNL %: {wallet_upnl_pct:+.2f}% {'🟢' if wallet_upnl_pct >= 0 else '🔴'}"
        if projected_profit is not None:
            proj_wallet_pct = (projected_profit / bal * 100) if bal > 0 else 0.0
            proj_wallet_pct_str = f"{proj_wallet_pct:+.4f}%" if 0 < abs(proj_wallet_pct) < 0.01 else f"{proj_wallet_pct:+.2f}%"
            wallet_upnl_str += f" (Proj: {proj_wallet_pct_str} {'🟢' if proj_wallet_pct >= 0 else '🔴'})"
        print(wallet_upnl_str)

        print(f"│ 🔒 Blocked Amount: ${blocked:.2f}")
        blocked_upnl_str = f"│ UPNL %: {blocked_upnl_pct:+.2f}% {'🟢' if blocked_upnl_pct >= 0 else '🔴'}"
        if projected_profit is not None:
            proj_blocked_pct = (projected_profit / blocked * 100) if blocked > 0 else 0.0
            proj_blocked_pct_str = f"{proj_blocked_pct:+.4f}%" if 0 < abs(proj_blocked_pct) < 0.01 else f"{proj_blocked_pct:+.2f}%"
            blocked_upnl_str += f" (Proj: {proj_blocked_pct_str} {'🟢' if proj_blocked_pct >= 0 else '🔴'})"
        print(blocked_upnl_str)

        print("│")
        pos_msg = f"{position_count}" if position_count > 0 else "0 (monitoring in background)"
        print(f"│ 📋 Account: {MAIN_ACCOUNT['account_name']} │ 🔄 Mode: {MARGIN_MODE.capitalize()} │ 📦 Positions: {pos_msg}")
        upnl_line = f"│ 💵 UPNL: ${upnl:+.2f}"
        if projected_profit is not None:
            proj_wallet_pct = (projected_profit / bal * 100) if bal > 0 else 0.0
            proj_wallet_pct_str = f"{proj_wallet_pct:+.4f}%" if 0 < abs(proj_wallet_pct) < 0.01 else f"{proj_wallet_pct:+.2f}%"
            proj_profit_str = f"${projected_profit:.4f}" if 0 < abs(projected_profit) < 0.01 else f"${projected_profit:.2f}"
            upnl_line += f"  │  Projected: {proj_profit_str} ({proj_wallet_pct_str})"
        if max_loss is not None:
            has_options = any(p.get("product_symbol", "").startswith(("C-", "P-", "MV-")) for p in position_details)
            is_covered = is_covered_under_10_percent_move(position_details, spot_btc, spot_eth)
            loss_wallet_pct = -(max_loss / bal * 100) if bal > 0 else 0.0
            loss_wallet_pct_str = f"{loss_wallet_pct:+.4f}%" if 0 < abs(loss_wallet_pct) < 0.01 else f"{loss_wallet_pct:+.2f}%"
            if is_covered and has_options:
                upnl_line += f"  │  Max Loss: ${max_loss:.2f} ({loss_wallet_pct_str}) (both leg covered under 10% movment)"
            else:
                upnl_line += f"  │  Max Loss: ${max_loss:.2f} ({loss_wallet_pct_str})"
        print(upnl_line)
        show_greeks_here = position_delta_sum is not None and position_gamma_sum is not None and position_theta_sum is not None and position_vega_sum is not None
        if show_greeks_here and not (option_metrics and option_metrics.get("is_combined")):
            rho_str = f"  │  ρ: {position_rho_sum:+.4f}" if position_rho_sum is not None else ""
            print(f"│   Δ: {position_delta_sum:+.4f}  │  Γ: {position_gamma_sum:+.6f}  │  Θ: {position_theta_sum:+.4f}  │  ν: {position_vega_sum:+.4f}{rho_str}")
        if option_metrics:
            om = option_metrics
            if om.get("is_combined") and position_details:
                theor = om.get("combined_theor") or 0.0
                intr = om.get("combined_intrinsic") or 0.0
                tv = om.get("combined_time_value") or 0.0
                iv = om.get("combined_iv_pct")
                print(f"│ 📈 Option Greeks : Theor {theor:.2f}  │  Intrinsic {intr:.2f}  │  Time value {tv:.2f}" + (f"  │  IV {iv:.2f}%" if iv is not None else "  │  IV —"))
                if position_delta_sum is not None and position_gamma_sum is not None and position_theta_sum is not None and position_vega_sum is not None:
                    rho_str = f"  │  ρ: {position_rho_sum:+.4f}" if position_rho_sum is not None else ""
                    print(f"│  Δ {position_delta_sum:+.4f}  │  Γ {position_gamma_sum:+.6f}  │  ν {position_vega_sum:+.4f}  │  Θ {position_theta_sum:+.4f}{rho_str}")
            else:
                ref_src = om.get("ref_label", "ref")
                ref_cid = om.get("ref_contract", "")
                ref_line = f"│ 📈 Option (ref): {ref_src}"
                if ref_cid:
                    ref_line += f"  →  {ref_cid}"
                print(ref_line)
                print(f"│   Ask {om['ask']:.2f}  │  Bid {om['bid']:.2f}  │  Theor {om['theor']:.2f}  │  Intrinsic {om['intrinsic']:.2f}  │  Time value {om['time_value']:.2f}")
                iv_s = f"{om['iv_pct']:.2f}%" if om.get('iv_pct') is not None else "-"
                vol_s = str(om['volume']) if om.get('volume') is not None else "-"
                dte_s = str(om['dte']) if om.get('dte') is not None else "-"
                print(f"│   IV% {iv_s}  │  Vol {vol_s}  │  DTE {dte_s}  │  Δ {om['delta']:.2f}  Γ {om['gamma']:.4f}  ν {om['vega']:.2f}  Θ {om['theta']:.2f}  ρ {om['rho']:.3f}")
        print("│")

        if position_details:
            icon = "✓" if strike_order_ok else "⚠"
            header = f"│ Position Details: {strike_order_msg} {icon}" if strike_order_msg else "│ Position Details:"
            print(header)
            for p in position_details:
                print(f"│   {format_position_detail_for_ui(p)}")

        print("│──────────────────────────────────────────────────────────────────────────────")

        if LAST_CMD_SHOWN.get("until", 0) > time.time() and LAST_CMD_SHOWN.get("msg"):
            print(f"│ 📌 Last command: {LAST_CMD_SHOWN['msg']}")
        _w = 74
        _gap = " " * 17
        print("│ ⌨️ SHORTCUTS: Telegram command keys /help or /keys or /menu" + _gap + "📊 STRATEGY:")

        ii_str = f"│   [ii] → Instrument (e.g. \033[1;92mBTC\033[0m / ETH)" if SYMBOL == "BTC" else f"│   [ii] → Instrument (e.g. BTC / \033[1;92mETH\033[0m)"
        if POSITION_SIZING_MODE == "max_loss":
            mm_str = f"│   [mm] → Max loss % (Current: \033[1;92m{round(MAX_LOSS_CAP_PCT * 100)}%\033[0m)"
        elif POSITION_SIZING_MODE == "target_profit":
            mm_str = f"│   [mm] → Target profit % (Current: \033[1;92m{round(TARGET_PROFIT_PCT * 100)}%\033[0m)"
        else:
            mm_str = f"│   [mm] → Min margin % (Current: \033[1;92m{round(MIN_MARGIN_PCT * 100)}%\033[0m)"
        acct_name = MAIN_ACCOUNT.get("account_name", "Main")
        if acct_name.lower() == "main":
            aa_str = f"│   [aa] → Account (e.g. \033[1;92mMain\033[0m / Sub)"
        else:
            aa_str = f"│   [aa] → Account (e.g. Main / \033[1;92mSub\033[0m)"
        uu_str = f"│   [uu] → User (Current: \033[1;92m{MAIN_ACCOUNT.get('username', '')}\033[0m)"

        pp_mode = MARGIN_MODE.lower()
        if pp_mode == "isolated":
            pp_str = f"│   [pp] → Margin (e.g. \033[1;92mIso\033[0m / Cross / Port)"
        elif pp_mode == "cross":
            pp_str = f"│   [pp] → Margin (e.g. Iso / \033[1;92mCross\033[0m / Port)"
        else:
            pp_str = f"│   [pp] → Margin (e.g. Iso / Cross / \033[1;92mPort\033[0m)"

        kk_mode = POSITION_SIZING_MODE.lower()
        if ORDER_TYPE.lower() == "futures":
            if kk_mode == "margin":
                kk_str = f"│   [kk] → Position sizing (\033[1;92mMargin\033[0m / Max Loss)"
            else:
                kk_str = f"│   [kk] → Position sizing (Margin / \033[1;92mMax Loss\033[0m)"
        else:
            if kk_mode == "margin":
                kk_str = f"│   [kk] → Position sizing (\033[1;92mMargin\033[0m / Max Loss / Target Profit)"
            elif kk_mode == "max_loss":
                kk_str = f"│   [kk] → Position sizing (Margin / \033[1;92mMax Loss\033[0m / Target Profit)"
            else:
                kk_str = f"│   [kk] → Position sizing (Margin / Max Loss / \033[1;92mTarget Profit\033[0m)"

        tt_type = ORDER_TYPE.lower()
        if "option" in tt_type:
            tt_str = f"│   [tt] → Order type (\033[1;92mOptions\033[0m / Futures)"
        else:
            tt_str = f"│   [tt] → Order type (Options / \033[1;92mFutures\033[0m)"

        xx_str = f"│   [xx] → Auto exec (e.g. \033[1;92mON\033[0m / OFF)" if USER_AUTO_EXECUTION else f"│   [xx] → Auto exec (e.g. ON / \033[1;91mOFF\033[0m)"
        ll_str = f"│   [ll] → Log file (ON / OFF) \033[1;92m[ON]\033[0m" if LOG_ENABLED else f"│   [ll] → Log file (ON / OFF) \033[1;91m[OFF]\033[0m"
        oo_str = f"│   [oo] → OI Chain (OI Chain View: \033[1;92m{OI_CHAIN_VIEW.capitalize()}\033[0m)"

        cc_str = f"│   [cc] → Custom Legs Threshold (Current: \033[1;92m{round(CUSTOM_BASE_THRESHOLD*100)}% / {round(CUSTOM_ACTIVE_THRESHOLD*100)}%\033[0m)"
        rr_str = "│   [rr] → Reset (margin 10%, Target Profit 10%, OPENSTRIKE, auto ON)"
        qq_str = "│   [qq] → Exit  │  [ss] → Restart  │  Ctrl+C → Exit"

        _left = [ii_str, mm_str, aa_str, uu_str, pp_str, kk_str, tt_str, xx_str, ll_str, oo_str, cc_str, rr_str, qq_str]

        sd_sv = "   [sv] → highest_volume"
        sd_so = "   [so] → highest_oi"
        sd_sf = "   [sf] → vol_oi"

        if STRATEGY_MODE == "STRADDLE":
            active_target = OPENSTRIKE_TARGET_STRIKE
            if active_target == "highest_volume":
                sd_sv = "   \033[1;92m[sv] → highest_volume\033[0m"
            elif active_target == "highest_oi":
                sd_so = "   \033[1;92m[so] → highest_oi\033[0m"
            elif active_target == "vol_oi":
                sd_sf = "   \033[1;92m[sf] → vol_oi\033[0m"

        _right = [
            " Active Strategy:",
            f"   Mode: \033[1;93m{STRATEGY_MODE}\033[0m",
            f"   Target: \033[1;96m{OPENSTRIKE_TARGET_STRIKE}\033[0m",
        ]

        if STRATEGY_SWITCH_PENDING:
            pending_key = ""
            if PENDING_STRATEGY_MODE == "OPENSTRIKE":
                rank_idx = get_rank_index(PENDING_TARGET_STRIKE)
                if rank_idx is not None:
                    pending_key = f"{rank_idx + 1}{rank_idx + 1}"
                elif PENDING_TARGET_STRIKE == "atm":
                    pending_key = "00"
            elif PENDING_STRATEGY_MODE == "STRADDLE":
                if PENDING_TARGET_STRIKE == "highest_volume":
                    pending_key = "sv"
                elif PENDING_TARGET_STRIKE == "highest_oi":
                    pending_key = "so"
                elif PENDING_TARGET_STRIKE == "vol_oi":
                    pending_key = "sf"
            key_label = f" [{pending_key}]" if pending_key else ""
            _right.append(f"   \033[1;91m⏳ PENDING → {PENDING_STRATEGY_MODE}{key_label}\033[0m")
        
        # Dynamically build _right_strikes based on _final_N
        _right_strikes = []
        active_target = OPENSTRIKE_TARGET_STRIKE
        active_rank_idx = get_rank_index(active_target)

        # Override active target and rank index if there are open positions matching any target rank
        if STRATEGY_MODE == "OPENSTRIKE" and position_details:
            opt_positions = [p for p in position_details if not p.get("is_futures") and (p.get("symbol", "").startswith("C-") or p.get("symbol", "").startswith("P-"))]
            if opt_positions:
                try:
                    opts = fetch_options(SYMBOL, include_spot=False)
                    calls = [o for o in opts if o.get("type") == "call"]
                    puts = [o for o in opts if o.get("type") == "put"]
                    calls_by_oi = sorted(calls, key=lambda x: float(x.get("oi", 0) or 0), reverse=True)
                    puts_by_oi = sorted(puts, key=lambda x: float(x.get("oi", 0) or 0), reverse=True)

                    atm_call = select_atm_oi_option(calls, spot)
                    atm_put = select_atm_oi_option(puts, spot)

                    detected_ranks = []
                    is_atm_detected = False
                    for pos in opt_positions:
                        pos_sym = pos.get("symbol")
                        if not pos_sym:
                            continue
                        if (pos_sym.startswith("C-") and atm_call and pos_sym == atm_call.get("symbol")) or \
                           (pos_sym.startswith("P-") and atm_put and pos_sym == atm_put.get("symbol")):
                            is_atm_detected = True
                            break
                        if pos_sym.startswith("C-"):
                            for idx, o in enumerate(calls_by_oi):
                                if o["symbol"] == pos_sym:
                                    detected_ranks.append(idx)
                                    break
                        elif pos_sym.startswith("P-"):
                            for idx, o in enumerate(puts_by_oi):
                                if o["symbol"] == pos_sym:
                                    detected_ranks.append(idx)
                                    break

                    if is_atm_detected:
                        active_target = "atm"
                        active_rank_idx = None
                    elif detected_ranks:
                        most_common_rank = Counter(detected_ranks).most_common(1)[0][0]
                        active_rank_idx = most_common_rank
                        if active_rank_idx == 0:
                            active_target = "highest_oi"
                        elif active_rank_idx == 1:
                            active_target = "2nd_highest"
                        elif active_rank_idx == 2:
                            active_target = "3rd_highest"
                        else:
                            active_target = f"{active_rank_idx + 1}th_highest"
                except Exception:
                    pass

        for rank_idx in range(_final_N):
            rank_num = rank_idx + 1
            rep_key = f"{rank_num}{rank_num}"
            if rank_num == 1:
                lbl = "highest_oi"
            elif rank_num == 2:
                lbl = "2nd_highest"
            elif rank_num == 3:
                lbl = "3rd_highest"
            else:
                lbl = f"{rank_num}th_highest"
            line_str = f"   [{rep_key}] → {lbl}"
            if STRATEGY_MODE == "OPENSTRIKE" and active_rank_idx == rank_idx:
                line_str = f"   \033[1;92m[{rep_key}] → {lbl}\033[0m"
            _right_strikes.append(line_str)

        atm_line = "   [00] → atm"
        if STRATEGY_MODE == "OPENSTRIKE" and active_target == "atm":
            atm_line = "   \033[1;92m[00] → atm\033[0m"
        _right_strikes.append(atm_line)

        _right.extend([
            "",
            " OPENSTRIKE Strategy:",
            f"   Current Target: \033[1;96m{active_target if STRATEGY_MODE == 'OPENSTRIKE' else '-'}\033[0m",
        ] + _right_strikes + [
            "",
            " STRADDLE Strategy:",
            f"   Current Target: \033[1;96m{OPENSTRIKE_TARGET_STRIKE if STRATEGY_MODE == 'STRADDLE' else '-'}\033[0m",
            sd_sv,
            sd_so,
            sd_sf,
        ])
        if STRATEGY_MODE == "STRADDLE" and STRADDLE_TARGET_CONTRACT:
            target_sym = STRADDLE_TARGET_CONTRACT.get("symbol")
            if target_sym:
                analysis = analyze_straddle_sentiment(target_sym)
                if analysis:
                    sent_val = f"{analysis['color_code']}{analysis['sentiment']}\033[0m"
                    p_ch = f"{analysis['price_change_pct']:+.2f}%"
                    o_ch = f"{analysis['oi_change_pct']:+.2f}%"
                    _right.extend([
                        "",
                        f"   Target: \033[1;97m{target_sym}\033[0m",
                        f"   Sentiment: {sent_val}",
                        f"   Chg({int(analysis['time_diff_min'])}m): P:{p_ch} OI:{o_ch}"
                    ])
        for i in range(max(len(_left), len(_right))):
            _l = _left[i] if i < len(_left) else "│"
            _r = _right[i] if i < len(_right) else ""
            _l_clean = re.sub(r'\033\[[0-9;]*m', '', _l)
            if len(_l_clean) < _w:
                _l_pad = _l + (" " * (_w - len(_l_clean)))
            else:
                _l_pad = _l
            print(_l_pad + "│ " + _r.rstrip())
        print("│")
        print(f"│ 📋 Last 10 Orders:")
        for o in list(last_orders):
            print(f"│   {o}")
        print("└──────────────────────────────────────────────────────────────────────────────")
        sys.stdout.flush()

CAN_EXECUTE = True
CAN_EXECUTE = (
    USER_AUTO_EXECUTION
    and not API_DOWN
    and not KILL_SWITCH
)
FIRST_UI_RENDER_DONE = False

OPEN_INTEREST_LOG_FILE = f"{_SCRIPT_BASE}.log"
LOG_RETENTION_HOURS = 24

def _stderr_write(message: str) -> None:
    err = sys.__stderr__ or sys.stderr
    if err is None:
        return
    try:
        err.write(message)
    except Exception:
        pass

class _TeeLog:
    """
    Standard STDOUT Tee implementation to write both to console and a log file.
    Magic methods (write, flush, reopen) are implicitly used by Python's sys.stdout redirection hook.
    """
    def __init__(self, log_path: str):
        self._stdout: TextIO = sys.stdout
        self._file: Optional[TextIO] = None
        self._log_path = log_path
        try:
            self._file = open(log_path, "a", encoding="utf-8")
        except Exception as e:
            _stderr_write(f"⚠️ Log file open fail: {log_path} — {e}\n")

    def reopen(self) -> None:
        if self._file:
            try:
                self._file.close()
            except Exception:
                pass
            self._file = None
        try:
            self._file = open(self._log_path, "a", encoding="utf-8")
        except Exception as e:
            _stderr_write(f"⚠️ Log reopen fail: {self._log_path} — {e}\n")

    def write(self, data: str) -> None:
        self._stdout.write(data)
        if self._file and LOG_ENABLED:
            try:
                self._file.write(data)
                self._file.flush()
            except Exception as e:
                _stderr_write(f"⚠️ Log write fail: {e}\n")

    def flush(self) -> None:
        self._stdout.flush()
        if self._file:
            try:
                self._file.flush()
            except Exception:
                pass

def _reopen_stdout_log() -> None:
    if isinstance(sys.stdout, _TeeLog):
        sys.stdout.reopen()

def _write_log_only(text: str) -> None:
    if not text:
        return
    if not LOG_ENABLED:
        return
    if not isinstance(sys.stdout, _TeeLog):
        return
    if not getattr(sys.stdout, "_file", None):
        return
    try:
        sys.stdout._file.write(text)
        if not text.endswith("\n"):
            sys.stdout._file.write("\n")
        sys.stdout._file.flush()
    except Exception as e:
        _stderr_write(f"⚠️ Log-only write fail: {e}\n")

_UI_SNAPSHOT_MAX_AGE_SEC = 600.0


def _ui_frame_timestamp(frame: str):
    m = re.search(r"│ ⏰ Time: (\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}(?:\.\d+)?)", frame)
    if not m:
        return None
    ts_str = m.group(1)
    try:
        if "." in ts_str:
            return datetime.strptime(ts_str[:26], "%Y-%m-%d %H:%M:%S.%f")
        return datetime.strptime(ts_str[:19], "%Y-%m-%d %H:%M:%S")
    except Exception:
        return None


def _load_last_ui_frame_from_log(log_path=None, max_bytes=768 * 1024, max_age_sec=_UI_SNAPSHOT_MAX_AGE_SEC):
    if log_path is None:
        log_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), OPEN_INTEREST_LOG_FILE)
    if not os.path.isfile(log_path):
        return ""
    try:
        size = os.path.getsize(log_path)
        if size <= 0:
            return ""
        with open(log_path, "rb") as f:
            if size > max_bytes:
                f.seek(size - max_bytes)
            data = f.read().decode("utf-8", errors="replace")
        fallback = ""
        search_end = len(data)
        while True:
            end = data.rfind("└", 0, search_end)
            if end == -1:
                break
            start = data.rfind("┌", 0, end)
            if start == -1:
                break
            end_line = data.find("\n", end)
            if end_line == -1:
                end_line = len(data)
            frame = data[start:end_line].rstrip() + "\n"
            if "│ 👤 User:" in frame:
                frame = frame.replace(
                    "│   [q]  → Exit (Ctrl+C to kill)",
                    "│   [q]  → Exit  │  [s]  → Restart  │  Ctrl+C → Exit",
                )
                if not fallback:
                    fallback = frame
                if "BOOTING..." not in frame:
                    frame_ts = _ui_frame_timestamp(frame)
                    if frame_ts is not None and (datetime.now() - frame_ts).total_seconds() > max_age_sec:
                        search_end = start
                        continue
                    return frame
            search_end = start
        if fallback:
            frame_ts = _ui_frame_timestamp(fallback)
            if frame_ts is not None and (datetime.now() - frame_ts).total_seconds() > max_age_sec:
                return ""
        return fallback
    except Exception:
        return ""

def get_latest_ui_snapshot():
    try:
        frame = _load_last_ui_frame_from_log(max_age_sec=3600.0)
        if not frame:
            return "No recent UI snapshot found."
        # Strip ANSI escape codes
        ansi_escape = re.compile(r'\x1b\[[0-9;]*[a-zA-Z]|\x1b\([a-zA-Z]')
        clean_frame = ansi_escape.sub('', frame)
        return clean_frame
    except Exception as e:
        return f"Error loading snapshot: {e}"

def send_telegram_snapshot(text):
    if not text:
        return
        
    # Replace the wide separators with the narrow ones for Telegram formatting
    text = text.replace("┌──────────────────────────────────────────────────────────────────────────────", "┌─────────────────────────────────")
    text = text.replace("│──────────────────────────────────────────────────────────────────────────────", "│──────────────────────────────────")
    text = text.replace("└──────────────────────────────────────────────────────────────────────────────", "└─────────────────────────────────")
    text = text.replace("│   ──────────  ────────  ──────────", "│   ─────────────────────────────────")
    text = text.replace("│   ──────────────────────────────────────────────────────────────────────────", "│   ─────────────────────────────────")
    text = text.replace("│   ──────────────────────  ──────────  ──────────  ──────────  ──────────────", "│   ──────────────────────  ──────────")
    
    top_border = "┌─────────────────────────────────"
    bottom_border = "└─────────────────────────────────"
    sep_line = "│──────────────────────────────────"
    
    # Check if the entire message fits in a single Telegram message
    full_msg = f"```\n{text}\n```"
    if len(full_msg) <= 4090:
        send_telegram(full_msg)
        return
        
    # Otherwise split into chunks, formatting each chunk as a complete box
    lines = text.split("\n")
    chunk = []
    chunk_len = 0
    
    for idx, line in enumerate(lines):
        line_len = len(line) + 1
        
        # If the chunk gets too large, send it and start a new one
        if chunk_len + line_len > 3800:
            if chunk:
                chunk_str = "\n".join(chunk)
                # Ensure it ends with bottom border
                if not chunk_str.rstrip().endswith(bottom_border):
                    chunk_str = chunk_str.rstrip()
                    if chunk_str.endswith(sep_line):
                        chunk_str = chunk_str[:-len(sep_line)] + bottom_border
                    else:
                        chunk_str = chunk_str + "\n" + bottom_border
                
                send_telegram(f"```\n{chunk_str}\n```")
                time.sleep(1.0) # Wait for the first message thread to submit to ensure correct ordering
                
            # Start new chunk with top border
            if line.startswith(top_border):
                chunk = [line]
            else:
                chunk = [top_border, line]
            chunk_len = sum(len(l) + 1 for l in chunk)
        else:
            chunk.append(line)
            chunk_len += line_len
            
    # Send remaining lines in the last chunk
    if chunk:
        chunk_str = "\n".join(chunk)
        if not chunk_str.rstrip().endswith(bottom_border):
            chunk_str = chunk_str.rstrip()
            if chunk_str.endswith(sep_line):
                chunk_str = chunk_str[:-len(sep_line)] + bottom_border
            else:
                chunk_str = chunk_str + "\n" + bottom_border
        send_telegram(f"```\n{chunk_str}\n```")

def _ui_stall_watchdog():
    global LAST_VISIBLE_UI_AT, LAST_HEARTBEAT_PRINT_AT, LAST_FULL_SNAPSHOT_LOG_AT
    while not KILL_SWITCH:
        try:
            now_ts = time.time()
            if (
                now_ts - LAST_VISIBLE_UI_AT >= STALL_HEARTBEAT_AFTER_SEC
                and now_ts - LAST_HEARTBEAT_PRINT_AT >= STALL_HEARTBEAT_EVERY_SEC
            ):
                live_age = (now_ts - LAST_LIVE_UI_RENDER_AT) if LAST_LIVE_UI_RENDER_AT > 0 else None
                if live_age is None or LIVE_RENDER_COUNT == 0:
                    live_msg = "first live UI pending"
                else:
                    live_msg = f"last live UI {live_age:.0f}s ago"
                if API_DOWN and live_age is not None and live_age > 120:
                    live_msg += " | API DOWN — fix IP whitelist (see log)"
                status_msg = execution_status if execution_status else "working"
                if now_ts - LAST_FULL_SNAPSHOT_LOG_AT >= STALL_FULL_SNAPSHOT_EVERY_SEC:
                    snapshot = ""
                    if (
                        LOG_ENABLED
                        and LIVE_RENDER_COUNT > 0
                        and live_age is not None
                        and live_age <= 60.0
                    ):
                        snapshot = _load_last_ui_frame_from_log()
                    if snapshot:
                        _write_log_only(snapshot)
                        _write_log_only(
                            f"⏳ UI snapshot replay | {live_msg} | stage: {LAST_MAIN_LOOP_STAGE} | status: {status_msg} | {datetime.now().strftime('%H:%M:%S')}"
                        )
                        with UI_PRINT_LOCK:
                            print("\033[2J\033[H", end="", flush=True)
                            print(snapshot, end="" if snapshot.endswith("\n") else "\n", flush=True)
                            print(
                                f"⏳ UI snapshot replay | {live_msg} | stage: {LAST_MAIN_LOOP_STAGE} | status: {status_msg} | {datetime.now().strftime('%H:%M:%S')}",
                                flush=True,
                            )
                            LAST_VISIBLE_UI_AT = time.time()
                            LAST_HEARTBEAT_PRINT_AT = LAST_VISIBLE_UI_AT
                        LAST_FULL_SNAPSHOT_LOG_AT = now_ts
                        continue
                with UI_PRINT_LOCK:
                    print(
                        f"\n⏳ Bot running... {live_msg} | stage: {LAST_MAIN_LOOP_STAGE} | status: {status_msg} | {datetime.now().strftime('%H:%M:%S')}",
                        flush=True,
                    )
                    LAST_VISIBLE_UI_AT = time.time()
                    LAST_HEARTBEAT_PRINT_AT = LAST_VISIBLE_UI_AT
        except Exception:
            pass
        time.sleep(1.0)

_tmp_log_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), OPEN_INTEREST_LOG_FILE)
_tl = _TeeLog(_tmp_log_path)
sys.stdout = _tl
if _tl._file:
    _stderr_write(f"📋 Log file: {_tmp_log_path}\n")
LOG_TRIM_INTERVAL_SEC = 1 * 3600
LAST_LOG_TRIM_AT = 0.0

def trim_log_to_last_24h(log_path=None, hours=24, fast_if_large=True):
    if log_path is None:
        log_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), OPEN_INTEREST_LOG_FILE)
    if not os.path.isfile(log_path):
        return
    frame_start_re = re.compile(r"^│ ⏰ Time: (\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}(?:\.\d+)?)")
    cutoff = datetime.now() - timedelta(hours=hours)

    def _parse_ts(m):
        try:
            ts_str = m.group(1)
            if "." in ts_str:
                return datetime.strptime(ts_str[:26], "%Y-%m-%d %H:%M:%S.%f")
            return datetime.strptime(ts_str[:19], "%Y-%m-%d %H:%M:%S")
        except Exception:
            return None

    try:
        _size_mb = os.path.getsize(log_path) / (1024 * 1024)
        if _size_mb > 15:
            first_kept_offset = None
            last_frame_offset = 0
            with open(log_path, "rb") as f:
                offset = 0
                for line in f:
                    start = offset
                    offset += len(line)
                    try:
                        s = line.decode("utf-8", errors="replace")
                    except Exception:
                        continue
                    m = frame_start_re.match(s.strip()) or frame_start_re.match(s)
                    if m:
                        ts = _parse_ts(m)
                        last_frame_offset = start
                        if ts is not None and ts >= cutoff and first_kept_offset is None:
                            first_kept_offset = start
            if first_kept_offset is None:
                first_kept_offset = last_frame_offset
            if first_kept_offset is None or first_kept_offset <= 0:
                return
            tmp_path = log_path + ".trim.tmp"
            with open(log_path, "rb") as fin:
                fin.seek(first_kept_offset)
                with open(tmp_path, "wb") as fout:
                    while True:
                        chunk = fin.read(2 * 1024 * 1024)
                        if not chunk:
                            break
                        fout.write(chunk)
            os.replace(tmp_path, log_path)
            _reopen_stdout_log()
            print(f"📋 Log trimmed to last {hours}h (stream): {log_path}", flush=True)
            return

        with open(log_path, "r", encoding="utf-8", errors="replace") as f:
            lines = f.readlines()
        if len(lines) < 10:
            return
        kept = []
        current = []
        prev_ts = None
        for line in lines:
            m = frame_start_re.match(line.strip()) or frame_start_re.match(line)
            if m:
                ts = _parse_ts(m)
                if current and prev_ts is not None and prev_ts >= cutoff:
                    kept.extend(current)
                current = [line]
                prev_ts = ts
            else:
                current.append(line)
        if current and prev_ts is not None and prev_ts >= cutoff:
            kept.extend(current)
        if len(kept) < len(lines):
            with open(log_path, "w", encoding="utf-8", newline="") as f:
                f.writelines(kept)
            _reopen_stdout_log()
            print(f"📋 Log trimmed to last {hours}h: {log_path}", flush=True)
    except Exception as e:
        print(f"⚠️ Log trim skipped: {e}", flush=True)

print("🚀 DELTA INDIA OPTIONS MASTER ENGINE STARTED", flush=True)
trim_log_to_last_24h(hours=LOG_RETENTION_HOURS)
LAST_LOG_TRIM_AT = time.time()
LAST_MAIN_LOOP_STAGE = "startup-restore"

try:
    all_pos = get_all_positions()
    btc_active = eth_active = 0
    for p in all_pos:
        sym = p.get("product_symbol", "")
        if not (sym.startswith("C-") or sym.startswith("P-")):
            continue
        if float(p.get("size", 0)) == 0:
            continue
        parts = sym.split("-")
        if len(parts) >= 2:
            inst = parts[1]
            if inst == "BTC":
                btc_active += 1
            elif inst == "ETH":
                eth_active += 1
    if eth_active > 0 and btc_active == 0:
        SYMBOL = "ETH"
        _save_settings()
        print(f"🔄 Restart: ETH positions detected → Instrument set to ETH (OI/Spot will show ETH)", flush=True)
    elif btc_active > 0 and eth_active == 0:
        SYMBOL = "BTC"
        _save_settings()
        print(f"🔄 Restart: BTC positions detected → Instrument set to BTC (OI/Spot will show BTC)", flush=True)
    elif btc_active > 0 and eth_active > 0:
        SYMBOL = "BTC" if btc_active >= eth_active else "ETH"
        _save_settings()
        print(f"🔄 Restart: Both have positions → Instrument set to {SYMBOL}", flush=True)
    else:
        def _bg_oi_pick():
            global SYMBOL, MAIN_SYMBOL_OI_BY
            try:
                picked = _pick_main_symbol_by_quick_oi(default_symbol=SYMBOL, timeout=8)
                SYMBOL = picked
                _save_settings()
                print(f"🔄 Restart: Position 0 → Instrument set to {SYMBOL} (higher OI, by {MAIN_SYMBOL_OI_BY})", flush=True)
            except Exception as oi_err:
                print(f"⚠️ Restart OI comparison skipped: {oi_err}", flush=True)
        threading.Thread(target=_bg_oi_pick, daemon=True).start()
except Exception as e:
    print(f"⚠️ Restart instrument detection skipped: {e}")
send_telegram(
    f"🚀 SCRIPT STARTED\n"
    f"Engine : Delta Options Bot\n"
    f"Time   : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
)
_STARTUP_API_OK = _startup_api_probe()
_SKIP_API_RECOVERY_FIRST_CYCLE = bool(_STARTUP_API_OK)
if _STARTUP_API_OK:
    _bootstrap_dashboard_after_auth()
_cached_ui = _load_last_ui_frame_from_log() if LOG_ENABLED and not _STARTUP_API_OK else ""
if _cached_ui:
    with UI_PRINT_LOCK:
        print("\033[2J\033[H", end="", flush=True)
        print(_cached_ui, end="" if _cached_ui.endswith("\n") else "\n", flush=True)
        LAST_VISIBLE_UI_AT = time.time()
threading.Thread(target=_ui_stall_watchdog, daemon=True).start()

while not KILL_SWITCH:
    try:
        while not KILL_SWITCH:
            LAST_MAIN_LOOP_STAGE = "cycle-start"
            SKIP_REST = False
            effective_min_margin = 0.50 if POSITION_SIZING_MODE == "target_profit" else MIN_MARGIN_PCT
            if KILL_SWITCH:
                break

            if time.time() - LAST_LOG_TRIM_AT >= LOG_TRIM_INTERVAL_SEC:
                trim_log_to_last_24h(hours=LOG_RETENTION_HOURS)
                LAST_LOG_TRIM_AT = time.time()

            if ACCOUNT_NAME_EDIT_PENDING:
                try:
                    new_val = safe_input("\n📋 Account name (main/sub): ").strip()
                    if new_val:
                        MAIN_ACCOUNT["account_name"] = new_val
                        _save_settings()
                        send_telegram(
                            f"⌨️ ACCOUNT NAME UPDATED\n"
                            f"Account : {new_val}\n"
                            f"Time    : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
                        )
                except (EOFError, KeyboardInterrupt):
                    pass
                ACCOUNT_NAME_EDIT_PENDING = False

            if USER_EDIT_PENDING:
                try:
                    new_name = safe_input("\n👤 User name: ").strip()
                    if new_name:
                        MAIN_ACCOUNT["username"] = new_name
                    new_email = safe_input("📧 Email: ").strip()
                    if new_email:
                        MAIN_ACCOUNT["email"] = new_email
                    new_phone = safe_input("📞 Phone: ").strip()
                    if new_phone:
                        MAIN_ACCOUNT["phone"] = new_phone
                    if new_name or new_email or new_phone:
                        _save_settings()
                        send_telegram(
                            f"⌨️ USER UPDATED\n"
                            f"Name  : {MAIN_ACCOUNT['username']}\n"
                            f"Email : {MAIN_ACCOUNT['email']}\n"
                            f"Phone : {MAIN_ACCOUNT['phone']}\n"
                            f"Time  : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
                        )
                except (EOFError, KeyboardInterrupt):
                    pass
                USER_EDIT_PENDING = False

            if MARGIN_EDIT_PENDING:
                if POSITION_SIZING_MODE == "max_loss":
                    prompt_label = "Max loss %"
                    tg_header = "MAX LOSS UPDATED [m]"
                    tg_label = "Max loss"
                elif POSITION_SIZING_MODE == "target_profit":
                    prompt_label = "Target profit %"
                    tg_header = "TARGET PROFIT UPDATED [m]"
                    tg_label = "Target profit"
                else:
                    prompt_label = "Min margin %"
                    tg_header = "MIN MARGIN UPDATED [m]"
                    tg_label = "Min margin"
                try:
                    raw = safe_input(f"\n🎚️ {prompt_label} (1-100): ").strip()
                    if raw:
                        pct = float(raw)
                        if 0 < pct <= 100:
                            val_pct = max(0.01, min(1.0, pct / 100.0))
                            if POSITION_SIZING_MODE == "max_loss":
                                MAX_LOSS_CAP_PCT = val_pct
                            elif POSITION_SIZING_MODE == "target_profit":
                                TARGET_PROFIT_PCT = val_pct
                            else:
                                MIN_MARGIN_PCT = val_pct
                            _save_settings()
                            label = "100%" if val_pct >= 0.99 else f"{round(val_pct * 100)}%"
                            send_telegram(
                                f"⌨️ {tg_header}\n"
                                f"{tg_label} : {label}\n"
                                f"Time : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
                            )
                            print(f"🎚️ {tg_label} → {label}")
                        else:
                            print("❌ Enter 1 to 100 only")
                except (EOFError, KeyboardInterrupt, ValueError):
                    pass
                MARGIN_EDIT_PENDING = False

            if INSTRUMENT_SWITCH_PENDING:
                new_sym = "ETH" if SYMBOL == "BTC" else "BTC"
                try:
                    current_positions = get_positions()
                except Exception:
                    current_positions = []
                has_active_positions = any(
                    p.get("product_symbol", "").startswith(("C-", "P-", "MV-")) and float(p.get("size", 0)) != 0
                    for p in current_positions
                )

                try:
                    decision_btc, _ = get_decision_for_symbol("BTC")
                    decision_eth, _ = get_decision_for_symbol("ETH")
                except Exception:
                    decision_btc = decision_eth = "NO TRADE"
                if LAST_BIAS_BTC is None:
                    LAST_BIAS_BTC = decision_btc
                    LAST_BIAS_ETH = decision_eth
                else:
                    if decision_btc != LAST_BIAS_BTC or decision_eth != LAST_BIAS_ETH:
                        INSTRUMENT_SWITCH_BIAS_CHANGE_DETECTED = True
                        which = []
                        if decision_btc != LAST_BIAS_BTC:
                            which.append(f"BTC {LAST_BIAS_BTC}→{decision_btc}")
                        if decision_eth != LAST_BIAS_ETH:
                            which.append(f"ETH {LAST_BIAS_ETH}→{decision_eth}")
                        INSTRUMENT_SWITCH_BIAS_CHANGE_MSG = "; ".join(which)
                    LAST_BIAS_BTC = decision_btc
                    LAST_BIAS_ETH = decision_eth
                if INSTRUMENT_SWITCH_BIAS_CHANGE_DETECTED and has_active_positions and USER_AUTO_EXECUTION:
                    if not INSTRUMENT_SWITCH_SQUARE_OFF_SENT:
                        n = square_off_current_instrument_for_switch()
                        INSTRUMENT_SWITCH_SQUARE_OFF_SENT = True
                        send_telegram(
                            f"🔄 [i] Bias change → closing {SYMBOL} positions for switch\n"
                            f"Change: {INSTRUMENT_SWITCH_BIAS_CHANGE_MSG or 'bias change'}\n"
                            f"Square-off sent: {n} leg(s). Switch to {new_sym} when positions = 0.\n"
                            f"Time : {datetime.now().strftime('%H:%M:%S')}"
                        )
                elif not has_active_positions:
                    INSTRUMENT_SWITCH_PENDING = False
                    INSTRUMENT_SWITCH_SQUARE_OFF_SENT = False
                    INSTRUMENT_SWITCH_BIAS_CHANGE_DETECTED = False
                    INSTRUMENT_SWITCH_BIAS_CHANGE_MSG = ""
                    LAST_BIAS_BTC = LAST_BIAS_ETH = None
                    SYMBOL = new_sym
                    _save_settings()
                    CMD_FEEDBACK = f"✅ [i] Switch instrument → {SYMBOL} (done)"
                    CMD_FEEDBACK_CLEAR_AT = time.time() + 5
                    LAST_CMD_SHOWN = {"msg": "", "until": 0.0}
                    LAST_EXECUTED_SIGNAL = None
                    send_telegram(
                        f"🔄 INSTRUMENT SWITCHED → {SYMBOL}\n"
                        f"Position was 0 — new position will be created on {SYMBOL} based on strategy.\n"
                        f"Time : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
                    )

            LAST_MAIN_LOOP_STAGE = "api-fetch"
            _api_timeout = 15
            _api_ex = None
            try:
                _api_ex = ThreadPoolExecutor(max_workers=5)
                f_spot = _api_ex.submit(get_spot)
                f_wallet = _api_ex.submit(wallet_usd)
                f_pos = _api_ex.submit(get_positions)
                f_all = _api_ex.submit(get_all_positions)
                f_orders = _api_ex.submit(orders_api_health_check)
                spot = f_spot.result(timeout=_api_timeout)
                bal, blocked, wallet_upnl = f_wallet.result(timeout=_api_timeout)
                positions = f_pos.result(timeout=_api_timeout)
                positions_all = f_all.result(timeout=_api_timeout)
                f_orders.result(timeout=_api_timeout)
            except Exception as _api_err:
                if _api_ex is not None:
                    _api_ex.shutdown(wait=False, cancel_futures=True)
                is_ip_wh = is_ip_whitelist_error(_api_err)
                should_print = True
                if is_ip_wh:
                    now = time.time()
                    if now - LAST_IP_WHITELIST_LOG_AT < 60.0:
                        should_print = False
                    else:
                        LAST_IP_WHITELIST_LOG_AT = now

                if should_print:
                    print(f"⚠️ API fetch timeout/error (retry next cycle): {repr(_api_err) or type(_api_err).__name__}", flush=True)
                # Skip slow synchronous retries in the exception handler to prevent main thread stall
                _bal, _blocked, _upnl = 0.0, 0.0, 0.0
                _pos_all, _pos_details, _pos_count = [], [], 0
                _spot_retry = 0.0
                _u, _hl, _hb = render_margin_heatmap(_bal, _blocked)
                _uc, _dr, _ds, _di, _ = calculate_margin_drift(_bal, _blocked, effective_min_margin)
                _as, _ast, _ab = render_api_health_bar()
                _err_short = (repr(_api_err) or type(_api_err).__name__)[:60] if _api_err else "Unknown"
                _price_change_ui_kwargs = build_price_change_ui_kwargs(
                    symbol_primary=SYMBOL,
                    spot_primary=_spot_retry,
                    update_state=True,
                )
                _src_msg = f"IP Blocked: {LAST_BLOCKED_IP}" if LAST_BLOCKED_IP else f"API Error ({_err_short})"
                _status_msg = f"IP Whitelist Blocked: {LAST_BLOCKED_IP}" if LAST_BLOCKED_IP else f"API Error — retry next cycle ({_err_short})"
                render_terminal_ui(
                    now=datetime.now(), spot=_spot_retry, decision="NO TRADE", source=_src_msg,
                    bal=_bal, blocked=_blocked, upnl=_upnl,
                    wallet_upnl_pct=(_upnl / _bal * 100) if _bal > 0 else 0,
                    blocked_upnl_pct=(_upnl / _blocked * 100) if _blocked > 0 else 0,
                    used_pct_ui=_u, heat_level=_hl, heat_bar=_hb,
                    delta=0, gamma=0,
                    position_details=_pos_details, position_count=_pos_count,
                    execution_status=_status_msg,
                    used_pct_calc=_uc, margin_drift=_dr, drift_status=_ds, drift_icon=_di,
                    api_score=_as, api_status=_ast, api_bar=_ab,
                    expiry_oi_list=[], expiry_oi_list_secondary=[],
                    spot_secondary=None, symbol_secondary=None, symbol_primary=SYMBOL,
                    all_expiry_max_pain_primary=None, all_expiry_max_pain_secondary=None,
                    projected_profit=None, max_loss=None,
                    position_delta_sum=None, position_gamma_sum=None, position_theta_sum=None,
                    position_vega_sum=None, position_rho_sum=None,
                    strike_order_ok=None, strike_order_msg=None, option_metrics=None,
                    last_executed_signal=LAST_EXECUTED_SIGNAL,
                    **_price_change_ui_kwargs
                )
                time.sleep(REFRESH_SECONDS)
                continue
            finally:
                if _api_ex is not None:
                    _api_ex.shutdown(wait=False, cancel_futures=True)
            _s_btc = spot if SYMBOL == "BTC" else 0.0
            _s_eth = spot if SYMBOL == "ETH" else 0.0
            _calc_upnl, _, position_count, position_details = calculate_upnl(positions_all, spot_btc=_s_btc, spot_eth=_s_eth)
            if STRATEGY_SWITCH_PENDING and position_count == 0:
                STRATEGY_MODE = PENDING_STRATEGY_MODE
                OPENSTRIKE_TARGET_STRIKE = PENDING_TARGET_STRIKE
                STRATEGY_SWITCH_PENDING = False
                PENDING_STRATEGY_MODE = ""
                PENDING_TARGET_STRIKE = ""
                _save_settings()
                send_telegram(
                    f"🔄 STRATEGY SWITCH COMPLETED\n"
                    f"Position reached 0. Switched strategy mode:\n"
                    f"Strategy Mode : {STRATEGY_MODE}\n"
                    f"Target Strike : {OPENSTRIKE_TARGET_STRIKE}\n"
                    f"Time : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
                )
            upnl = wallet_upnl if abs(wallet_upnl) > 0 else _calc_upnl

            if API_DOWN and all(HEALTH.values()):
                API_RECOVERY_COOLDOWN_UNTIL = time.time() + API_RECOVERY_COOLDOWN_SEC
                no_pos = not any(
                    (p.get("product_symbol") or "").startswith(("C-", "P-", "MV-")) and float(p.get("size", 0)) != 0
                    for p in positions_all
                )
                msg = (
                    "🟢 APIs RECOVERED — AUTO EXECUTION RESUMED\n"
                    f"Stabilizing for {API_RECOVERY_COOLDOWN_SEC}s before resuming.\n"
                )
                if no_pos:
                    msg += "No position → new position will be created based on strategy decision.\n"
                msg += f"Time: {datetime.now().strftime('%H:%M:%S')}"
                send_telegram(msg)
                API_DOWN = False

            api_score_early, _ast_early, _ab_early = render_api_health_bar()

            if api_score_early >= 50:
                API_RECOVERY_COOLDOWN_UNTIL = 0.0
            if (
                not _SKIP_API_RECOVERY_FIRST_CYCLE
                and (API_DOWN or time.time() < API_RECOVERY_COOLDOWN_UNTIL or api_score_early < API_MIN_HEALTH_PCT)
            ):
                has_any_option_pos = any(
                    (p.get("product_symbol") or "").startswith(("C-", "P-", "MV-")) and float(p.get("size", 0)) != 0
                    for p in positions
                )
                if not has_any_option_pos:
                    LAST_EXECUTED_SIGNAL = None
                _u, _hl, _hb = render_margin_heatmap(bal, blocked)
                _uc, _dr, _ds, _di, _ceiling = calculate_margin_drift(bal, blocked, effective_min_margin)
                _as, _ast, _ab = render_api_health_bar()

                _rec_oi_primary, _rec_oi_secondary = [], []
                _rec_spot_sec, _rec_sym_sec = None, None
                _rec_mp_primary, _rec_mp_secondary = None, None
                _rec_main = SYMBOL
                _rec_spot_primary = None
                _rec_ex = None
                try:
                    LAST_MAIN_LOOP_STAGE = "recovery-oi"
                    _rec_ex = ThreadPoolExecutor(max_workers=2)
                    _f_btc = _rec_ex.submit(get_spot_and_oi_for_symbol, "BTC")
                    _f_eth = _rec_ex.submit(get_spot_and_oi_for_symbol, "ETH")
                    _spot_btc, _oi_btc, _mp_btc, _tc_btc = _f_btc.result(timeout=12)
                    _spot_eth, _oi_eth, _mp_eth, _tc_eth = _f_eth.result(timeout=12)
                    if MAIN_SYMBOL_OI_BY == "contracts":
                        _tot_btc, _tot_eth = _tc_btc, _tc_eth
                    else:
                        _tot_btc = sum(i[1] + i[2] for i in (_oi_btc or []))
                        _tot_eth = sum(i[1] + i[2] for i in (_oi_eth or []))
                    _rec_main = "BTC" if _tot_btc >= _tot_eth else "ETH"
                    _rec_oi_primary = _oi_btc if _rec_main == "BTC" else _oi_eth
                    _rec_oi_secondary = _oi_eth if _rec_main == "BTC" else _oi_btc
                    _rec_spot_primary = _spot_btc if _rec_main == "BTC" else _spot_eth
                    _rec_spot_sec = _spot_eth if _rec_main == "BTC" else _spot_btc
                    _rec_sym_sec = "ETH" if _rec_main == "BTC" else "BTC"
                    _rec_mp_primary = _mp_btc if _rec_main == "BTC" else _mp_eth
                    _rec_mp_secondary = _mp_eth if _rec_main == "BTC" else _mp_btc
                except Exception:
                    pass
                finally:
                    if _rec_ex is not None:
                        _rec_ex.shutdown(wait=False, cancel_futures=True)
                _price_change_ui_kwargs = build_price_change_ui_kwargs(
                    symbol_primary=_rec_main,
                    spot_primary=_rec_spot_primary,
                    symbol_secondary=_rec_sym_sec,
                    spot_secondary=_rec_spot_sec,
                    update_state=True,
                )
                if LAST_BLOCKED_IP:
                    block_reason = f"IP Whitelist Blocked: {LAST_BLOCKED_IP}"
                    source_str = block_reason
                else:
                    block_reason = "API RECOVERING" if (API_DOWN or time.time() < API_RECOVERY_COOLDOWN_UNTIL) else f"API health {api_score_early}% < {API_MIN_HEALTH_PCT}%"
                    source_str = block_reason + "..."
                wallet_upnl_pct = (upnl / bal * 100) if bal > 0 else 0
                blocked_upnl_pct = (upnl / blocked * 100) if blocked > 0 else 0
                render_terminal_ui(
                    now=datetime.now(), spot=spot, decision="NO TRADE", source=source_str,
                    bal=bal, blocked=blocked, upnl=upnl,
                    wallet_upnl_pct=wallet_upnl_pct, blocked_upnl_pct=blocked_upnl_pct,
                    used_pct_ui=_u, heat_level=_hl, heat_bar=_hb,
                    delta=0, gamma=0,
                    position_details=position_details, position_count=position_count,
                    execution_status=f"{block_reason} (no new orders)",
                    used_pct_calc=_uc, margin_drift=_dr, drift_status=_ds, drift_icon=_di,
                    api_score=_as, api_status=_ast, api_bar=_ab,
                    expiry_oi_list=_rec_oi_primary or [], expiry_oi_list_secondary=_rec_oi_secondary or [],
                    spot_secondary=_rec_spot_sec, symbol_secondary=_rec_sym_sec, symbol_primary=_rec_main,
                    all_expiry_max_pain_primary=_rec_mp_primary, all_expiry_max_pain_secondary=_rec_mp_secondary,
                    projected_profit=None, max_loss=None,
                    position_delta_sum=None, position_gamma_sum=None, position_theta_sum=None,
                    position_vega_sum=None, position_rho_sum=None,
                    strike_order_ok=None, strike_order_msg=None, option_metrics=None,
                    last_executed_signal=LAST_EXECUTED_SIGNAL,
                    **_price_change_ui_kwargs
                )
                time.sleep(REFRESH_SECONDS)
                continue

            def _inst(pos):
                s = (pos.get("product_symbol") or "")
                return s.split("-")[1] if len(s.split("-")) >= 2 else ""
            btc_active = sum(1 for p in positions_all if (p.get("product_symbol") or "").startswith(("C-", "P-", "MV-")) and float(p.get("size", 0)) != 0 and _inst(p) == "BTC")
            eth_active = sum(1 for p in positions_all if (p.get("product_symbol") or "").startswith(("C-", "P-", "MV-")) and float(p.get("size", 0)) != 0 and _inst(p) == "ETH")
            manage_both = btc_active > 0 and eth_active > 0

            if STRATEGY_MODE == "OPENSTRIKE" and ORDER_TYPE != "futures" and USER_AUTO_EXECUTION:
                _other_sym = "ETH" if SYMBOL == "BTC" else "BTC"
                _other_positions = [
                    p for p in positions_all
                    if (p.get("product_symbol") or "").startswith(("C-", "P-", "MV-"))
                    and float(p.get("size", 0)) != 0
                    and _inst(p) == _other_sym
                ]
                if _other_positions:
                    for _op in _other_positions:
                        _op_sym = _op.get("product_symbol", "")
                        _op_size = float(_op.get("size", 0))
                        if _op_sym and _op_size != 0:
                            square_off_position(_op_sym, _op_size, reason="OPENSTRIKE_SECONDARY_CLEANUP")
                            send_telegram(
                                f"🔄 OPENSTRIKE: Secondary symbol position closed\n"
                                f"Symbol: {_op_sym}\n"
                                f"Size: {_op_size}\n"
                                f"Reason: OPENSTRIKE options mode — only primary ({SYMBOL}) is traded\n"
                                f"Time: {datetime.now().strftime('%H:%M:%S')}"
                            )
                    time.sleep(0.5)
                    positions_all = get_all_positions()
                    btc_active = sum(1 for p in positions_all if (p.get("product_symbol") or "").startswith(("C-", "P-", "MV-")) and float(p.get("size", 0)) != 0 and _inst(p) == "BTC")
                    eth_active = sum(1 for p in positions_all if (p.get("product_symbol") or "").startswith(("C-", "P-", "MV-")) and float(p.get("size", 0)) != 0 and _inst(p) == "ETH")
                    manage_both = btc_active > 0 and eth_active > 0

            now = datetime.now()
            wallet_upnl_pct = (upnl / bal * 100) if bal > 0 else 0
            blocked_upnl_pct = (upnl / blocked * 100) if blocked > 0 else 0

            used_pct_ui, heat_level, heat_bar = render_margin_heatmap(bal, blocked)
            api_score, api_status, api_bar = render_api_health_bar()

            _oi_ex = None
            try:
                LAST_MAIN_LOOP_STAGE = "oi-scan"
                _oi_ex = ThreadPoolExecutor(max_workers=2)
                _fb = _oi_ex.submit(get_spot_and_oi_for_symbol, "BTC")
                _fe = _oi_ex.submit(get_spot_and_oi_for_symbol, "ETH")
                spot_btc, oi_btc, mp_all_btc, tc_btc = _fb.result(timeout=12)
                spot_eth, oi_eth, mp_all_eth, tc_eth = _fe.result(timeout=12)
                if MAIN_SYMBOL_OI_BY == "contracts":
                    total_oi_btc, total_oi_eth = tc_btc, tc_eth
                else:
                    total_oi_btc = sum(i[1] + i[2] for i in (oi_btc or []))
                    total_oi_eth = sum(i[1] + i[2] for i in (oi_eth or []))
                main_sym = "BTC" if total_oi_btc >= total_oi_eth else "ETH"

                if btc_active > 0 and eth_active == 0:
                    SYMBOL = "BTC"
                elif eth_active > 0 and btc_active == 0:
                    SYMBOL = "ETH"
                else:
                    SYMBOL = main_sym
                spot = spot_btc if SYMBOL == "BTC" else spot_eth
                expiry_oi_list_primary = oi_btc if main_sym == "BTC" else oi_eth
                spot_primary_display = spot_btc if main_sym == "BTC" else spot_eth
                spot_secondary_oi = spot_eth if main_sym == "BTC" else spot_btc
                symbol_secondary_oi = "ETH" if main_sym == "BTC" else "BTC"
                expiry_oi_list_secondary_oi = oi_eth if main_sym == "BTC" else oi_btc
                all_expiry_mp_primary = mp_all_btc if main_sym == "BTC" else mp_all_eth
                all_expiry_mp_secondary = mp_all_eth if main_sym == "BTC" else mp_all_btc
            except Exception:
                main_sym = SYMBOL
                expiry_oi_list_primary = None
                spot = spot_primary_display = 0.0
                spot_secondary_oi = symbol_secondary_oi = expiry_oi_list_secondary_oi = None
                all_expiry_mp_primary = all_expiry_mp_secondary = None
                # Skip slow synchronous spot calls to prevent thread stall on timeout
                spot_btc = spot_eth = 0.0
            finally:
                if _oi_ex is not None:
                    _oi_ex.shutdown(wait=False, cancel_futures=True)
            price_change_ui_kwargs = build_price_change_ui_kwargs(
                symbol_primary=main_sym,
                spot_primary=spot_primary_display,
                symbol_secondary=symbol_secondary_oi,
                spot_secondary=spot_secondary_oi,
                update_state=True,
            )
            _opt_ex = None
            try:
                LAST_MAIN_LOOP_STAGE = "chain-fetch"
                _opt_ex = ThreadPoolExecutor(max_workers=1)
                opts = _opt_ex.submit(fetch_options).result(timeout=12)
            except Exception:
                opts = []
            finally:
                if _opt_ex is not None:
                    _opt_ex.shutdown(wait=False, cancel_futures=True)
            LAST_MAIN_LOOP_STAGE = "decision"
            near, nxt, all_opts = split_expiries(opts)

            _os_call_resolved = None
            _os_put_resolved = None

            OPENSTRIKE_CALL_DIFF_INFO = {"old_strike": None, "old_oi": None, "new_strike": None, "new_oi": None, "diff_pct": None, "action": "N/A"}
            OPENSTRIKE_PUT_DIFF_INFO = {"old_strike": None, "old_oi": None, "new_strike": None, "new_oi": None, "diff_pct": None, "action": "N/A"}

            c_meets_50 = True
            p_meets_50 = True
            custom_strategy_active = False
            custom_call_sell = None
            custom_put_sell = None
            custom_call_buy = None
            custom_put_buy = None

            if STRATEGY_MODE == "OPENSTRIKE" and ORDER_TYPE != "futures" and OPENSTRIKE_CALL_OPT is not None and OPENSTRIKE_PUT_OPT is not None:
                _os_call_resolved = resolve_openstrike_order_opt(OPENSTRIKE_CALL_OPT, all_opts)
                _os_put_resolved = resolve_openstrike_order_opt(OPENSTRIKE_PUT_OPT, all_opts)

                # Find active call/put short positions from positions
                temp_short_call = None
                temp_short_put = None
                for p in positions:
                    p_sym = p.get("product_symbol", "")
                    p_size = float(p.get("size", 0))
                    if p_sym.startswith("C-") and p_size < 0:
                        temp_short_call = p
                    elif p_sym.startswith("P-") and p_size < 0:
                        temp_short_put = p

                # Call Leg 10% Check (OI-based)
                if _os_call_resolved:
                    new_strike = float(_os_call_resolved.get("strike", 0) or 0)
                    new_oi = float(_os_call_resolved.get("oi", 0) or 0)
                    OPENSTRIKE_CALL_DIFF_INFO["new_strike"] = new_strike
                    OPENSTRIKE_CALL_DIFF_INFO["new_oi"] = new_oi
                    if temp_short_call:
                        old_strike = _strike_from_position(temp_short_call)
                        OPENSTRIKE_CALL_DIFF_INFO["old_strike"] = old_strike
                        # Find matching option in all_opts to get its OI
                        _old_call_opt = next((o for o in all_opts if o.get("symbol") == temp_short_call["product_symbol"]), None)
                        old_oi = float(_old_call_opt.get("oi", 0) or 0) if _old_call_opt else 0.0
                        OPENSTRIKE_CALL_DIFF_INFO["old_oi"] = old_oi

                        if old_strike and new_strike:
                            if new_strike == old_strike:
                                diff_pct = 0.0
                                OPENSTRIKE_CALL_DIFF_INFO["diff_pct"] = diff_pct
                                OPENSTRIKE_CALL_DIFF_INFO["action"] = "Keep Old (Same Strike)"
                            else:
                                if new_oi > 0:
                                    diff_pct = (new_oi - old_oi) / new_oi * 100.0
                                else:
                                    diff_pct = 0.0
                                OPENSTRIKE_CALL_DIFF_INFO["diff_pct"] = diff_pct
                                if abs(diff_pct) <= OI_DIFF_THRESHOLD_PCT:
                                    OPENSTRIKE_CALL_DIFF_INFO["action"] = f"Keep Old (|Diff| {abs(diff_pct):.2f}% <= {OI_DIFF_THRESHOLD_PCT}%)"
                                    if _old_call_opt:
                                        _os_call_resolved = _old_call_opt
                                    else:
                                        _os_call_resolved = {
                                            "symbol": temp_short_call["product_symbol"],
                                            "strike": old_strike,
                                            "type": "call",
                                            "expiry": extract_expiry(temp_short_call["product_symbol"])
                                        }
                                else:
                                    OPENSTRIKE_CALL_DIFF_INFO["action"] = f"Switch to New (|Diff| {abs(diff_pct):.2f}% > {OI_DIFF_THRESHOLD_PCT}%)"
                    else:
                        OPENSTRIKE_CALL_DIFF_INFO["action"] = "New Position"

                # Put Leg 10% Check (OI-based)
                if _os_put_resolved:
                    new_strike = float(_os_put_resolved.get("strike", 0) or 0)
                    new_oi = float(_os_put_resolved.get("oi", 0) or 0)
                    OPENSTRIKE_PUT_DIFF_INFO["new_strike"] = new_strike
                    OPENSTRIKE_PUT_DIFF_INFO["new_oi"] = new_oi
                    if temp_short_put:
                        old_strike = _strike_from_position(temp_short_put)
                        OPENSTRIKE_PUT_DIFF_INFO["old_strike"] = old_strike
                        # Find matching option in all_opts to get its OI
                        _old_put_opt = next((o for o in all_opts if o.get("symbol") == temp_short_put["product_symbol"]), None)
                        old_oi = float(_old_put_opt.get("oi", 0) or 0) if _old_put_opt else 0.0
                        OPENSTRIKE_PUT_DIFF_INFO["old_oi"] = old_oi

                        if old_strike and new_strike:
                            if new_strike == old_strike:
                                diff_pct = 0.0
                                OPENSTRIKE_PUT_DIFF_INFO["diff_pct"] = diff_pct
                                OPENSTRIKE_PUT_DIFF_INFO["action"] = "Keep Old (Same Strike)"
                            else:
                                if new_oi > 0:
                                    diff_pct = (new_oi - old_oi) / new_oi * 100.0
                                else:
                                    diff_pct = 0.0
                                OPENSTRIKE_PUT_DIFF_INFO["diff_pct"] = diff_pct
                                if abs(diff_pct) <= OI_DIFF_THRESHOLD_PCT:
                                    OPENSTRIKE_PUT_DIFF_INFO["action"] = f"Keep Old (|Diff| {abs(diff_pct):.2f}% <= {OI_DIFF_THRESHOLD_PCT}%)"
                                    if _old_put_opt:
                                        _os_put_resolved = _old_put_opt
                                    else:
                                        _os_put_resolved = {
                                            "symbol": temp_short_put["product_symbol"],
                                            "strike": old_strike,
                                            "type": "put",
                                            "expiry": extract_expiry(temp_short_put["product_symbol"])
                                        }
                                else:
                                    OPENSTRIKE_PUT_DIFF_INFO["action"] = f"Switch to New (|Diff| {abs(diff_pct):.2f}% > {OI_DIFF_THRESHOLD_PCT}%)"
                    else:
                        OPENSTRIKE_PUT_DIFF_INFO["action"] = "New Position"


                # Check active custom strategy legs to apply 75% hysteresis rule
                has_put_custom_legs = False
                existing_short_put = None
                existing_long_call = None
                existing_long_put = None
                for p in positions:
                    p_sym = p.get("product_symbol", "")
                    p_size = float(p.get("size", 0))
                    if p_size == 0:
                        continue
                    if p_sym.startswith("P-") and p_size < 0:
                        existing_short_put = p
                    elif p_sym.startswith("C-") and p_size > 0:
                        existing_long_call = p
                    elif p_sym.startswith("P-") and p_size > 0:
                        existing_long_put = p
                if CUSTOM_HEDGES_COUNT == 1:
                    if existing_short_put and existing_long_call:
                        has_put_custom_legs = True
                else:
                    if existing_short_put and existing_long_call and existing_long_put:
                        has_put_custom_legs = True

                has_call_custom_legs = False
                existing_short_call = None
                existing_long_call_val = None
                existing_long_put_val = None
                for p in positions:
                    p_sym = p.get("product_symbol", "")
                    p_size = float(p.get("size", 0))
                    if p_size == 0:
                        continue
                    if p_sym.startswith("C-") and p_size < 0:
                        existing_short_call = p
                    elif p_sym.startswith("C-") and p_size > 0:
                        existing_long_call_val = p
                    elif p_sym.startswith("P-") and p_size > 0:
                        existing_long_put_val = p
                if CUSTOM_HEDGES_COUNT == 1:
                    if existing_short_call and existing_long_put_val:
                        has_call_custom_legs = True
                else:
                    if existing_short_call and existing_long_call_val and existing_long_put_val:
                        has_call_custom_legs = True

                has_active_options_pos = any(
                    p.get("product_symbol", "").startswith(("C-", "P-", "MV-")) and float(p.get("size", 0)) != 0
                    for p in positions
                )
                if not has_active_options_pos:
                    c_threshold = CUSTOM_BASE_THRESHOLD
                    p_threshold = CUSTOM_BASE_THRESHOLD
                    if LAST_CROSS_DOWN_SIDE != "None":
                        LAST_CROSS_DOWN_SIDE = "None"
                        _save_settings()
                else:
                    c_threshold = CUSTOM_ACTIVE_THRESHOLD if (has_put_custom_legs or LAST_CROSS_DOWN_SIDE == "Call Strike") else CUSTOM_BASE_THRESHOLD
                    p_threshold = CUSTOM_ACTIVE_THRESHOLD if (has_call_custom_legs or LAST_CROSS_DOWN_SIDE == "Put Strike") else CUSTOM_BASE_THRESHOLD

                # 50% Rule check (with 75% hysteresis for active custom strategies)
                c_oi = float(OPENSTRIKE_CALL_OPT.get("oi", 0) or 0)
                p_oi = float(OPENSTRIKE_PUT_OPT.get("oi", 0) or 0)
                if c_oi > 0 or p_oi > 0:
                    check_oppoi_25pct_change(c_oi, p_oi)
                    c_meets_50 = (c_oi >= c_threshold * p_oi)
                    p_meets_50 = (p_oi >= p_threshold * c_oi)

                if not c_meets_50:
                    custom_strategy_active = True
                    was_in_custom = (LAST_CROSS_DOWN_SIDE == "Call Strike")
                    if LAST_CROSS_DOWN_SIDE != "Call Strike":
                        LAST_CROSS_DOWN_SIDE = "Call Strike"
                        _save_settings()
                    # Check if we already hold a Short Put + Long Call + Long Put
                    existing_short_put = None
                    existing_long_call = None
                    existing_long_put = None
                    for p in positions:
                        p_sym = p.get("product_symbol", "")
                        p_size = float(p.get("size", 0))
                        if p_size == 0:
                            continue
                        if p_sym.startswith("P-") and p_size < 0:
                            existing_short_put = p
                        elif p_sym.startswith("C-") and p_size > 0:
                            existing_long_call = p
                        elif p_sym.startswith("P-") and p_size > 0:
                            existing_long_put = p

                    custom_put_sell = None
                    target_expiry = None
                    if existing_short_put:
                        custom_put_sell = next((o for o in all_opts if o.get("symbol") == existing_short_put["product_symbol"]), None)
                        if custom_put_sell:
                            target_expiry = custom_put_sell.get("expiry")

                    if not custom_put_sell:
                        custom_put_sell = select_atm_option(near, spot, "put")
                        if custom_put_sell:
                            target_expiry = custom_put_sell.get("expiry")

                    _is_trans = not was_in_custom
                    if target_expiry:
                        custom_call_buy = select_or_reuse_hedge(all_opts, target_expiry, "call", existing_long_call, short_opt=custom_put_sell, is_transitioning=_is_trans)
                        if CUSTOM_HEDGES_COUNT == 1:
                            if existing_long_put:
                                custom_put_buy = select_or_reuse_hedge(all_opts, target_expiry, "put", existing_long_put, short_opt=custom_put_sell, is_transitioning=_is_trans)
                            else:
                                custom_put_buy = None
                        else:
                            custom_put_buy = select_or_reuse_hedge(all_opts, target_expiry, "put", existing_long_put, short_opt=custom_put_sell, is_transitioning=_is_trans)
                    else:
                        custom_call_buy = None
                        custom_put_buy = None

                    c_threshold_pct = int(c_threshold * 100)
                    _hedge_desc = "10% Premium Call Hedge" if _is_trans else "10D Call Hedge"
                    OPENSTRIKE_CALL_DIFF_INFO["action"] = f"Blocked (Call OI {_fmt_oi(c_oi)} < {c_threshold_pct}% of Put OI {_fmt_oi(p_oi)}). Running Put ATM + {_hedge_desc} Strategy"
                elif not p_meets_50:
                    custom_strategy_active = True
                    was_in_custom = (LAST_CROSS_DOWN_SIDE == "Put Strike")
                    if LAST_CROSS_DOWN_SIDE != "Put Strike":
                        LAST_CROSS_DOWN_SIDE = "Put Strike"
                        _save_settings()
                    # Check if we already hold a Short Call + Long Call + Long Put
                    existing_short_call = None
                    existing_long_call = None
                    existing_long_put = None
                    for p in positions:
                        p_sym = p.get("product_symbol", "")
                        p_size = float(p.get("size", 0))
                        if p_size == 0:
                            continue
                        if p_sym.startswith("C-") and p_size < 0:
                            existing_short_call = p
                        elif p_sym.startswith("C-") and p_size > 0:
                            existing_long_call = p
                        elif p_sym.startswith("P-") and p_size > 0:
                            existing_long_put = p

                    custom_call_sell = None
                    target_expiry = None
                    if existing_short_call:
                        custom_call_sell = next((o for o in all_opts if o.get("symbol") == existing_short_call["product_symbol"]), None)
                        if custom_call_sell:
                            target_expiry = custom_call_sell.get("expiry")

                    if not custom_call_sell:
                        custom_call_sell = select_atm_option(near, spot, "call")
                        if custom_call_sell:
                            target_expiry = custom_call_sell.get("expiry")

                    _is_trans = not was_in_custom
                    if target_expiry:
                        custom_put_buy = select_or_reuse_hedge(all_opts, target_expiry, "put", existing_long_put, short_opt=custom_call_sell, is_transitioning=_is_trans)
                        if CUSTOM_HEDGES_COUNT == 1:
                            if existing_long_call:
                                custom_call_buy = select_or_reuse_hedge(all_opts, target_expiry, "call", existing_long_call, short_opt=custom_call_sell, is_transitioning=_is_trans)
                            else:
                                custom_call_buy = None
                        else:
                            custom_call_buy = select_or_reuse_hedge(all_opts, target_expiry, "call", existing_long_call, short_opt=custom_call_sell, is_transitioning=_is_trans)
                    else:
                        custom_call_buy = None
                        custom_put_buy = None

                    p_threshold_pct = int(p_threshold * 100)
                    _hedge_desc = "10% Premium Put Hedge" if _is_trans else "10D Put Hedge"
                    OPENSTRIKE_PUT_DIFF_INFO["action"] = f"Blocked (Put OI {_fmt_oi(p_oi)} < {p_threshold_pct}% of Call OI {_fmt_oi(c_oi)}). Running Call ATM + {_hedge_desc} Strategy"
                else:
                    if LAST_CROSS_DOWN_SIDE != "None":
                        LAST_CROSS_DOWN_SIDE = "None"
                        _save_settings()


            if STRATEGY_SWITCH_PENDING:
                already_matching = False
                symbol_active_pos = [p for p in positions if float(p.get("size", 0)) != 0]
                active_symbols = {p.get("product_symbol") for p in symbol_active_pos}

                mv_list = []
                if PENDING_STRATEGY_MODE == "STRADDLE":
                    try:
                        tickers = fetch_all_tickers(refresh=False)
                        prefix = f"MV-{SYMBOL}-"
                        for t in tickers:
                            sym_name = t.get("symbol", "")
                            if sym_name.startswith(prefix):
                                mv_list.append({
                                    "symbol": sym_name,
                                    "turnover": safe_float(t.get("turnover")),
                                    "oi": safe_float(t.get("oi_value_usd")),
                                })
                        if mv_list:
                            if PENDING_TARGET_STRIKE == "highest_volume":
                                mv_list.sort(key=lambda x: x["turnover"], reverse=True)
                                target_mv_symbols = {mv_list[0]["symbol"]}
                            elif PENDING_TARGET_STRIKE == "vol_oi":
                                mv_by_vol = sorted(mv_list, key=lambda x: x["turnover"], reverse=True)
                                mv_by_oi = sorted(mv_list, key=lambda x: x["oi"], reverse=True)
                                target_mv_symbols = {mv_by_vol[0]["symbol"], mv_by_oi[0]["symbol"]}
                            else:
                                mv_list.sort(key=lambda x: x["oi"], reverse=True)
                                target_mv_symbols = {mv_list[0]["symbol"]}
                        else:
                            target_mv_symbols = set()
                    except Exception:
                        target_mv_symbols = set()

                    if target_mv_symbols and len(active_symbols) > 0 and active_symbols.issubset(target_mv_symbols):
                        already_matching = True

                elif PENDING_STRATEGY_MODE == "OPENSTRIKE":
                    if ORDER_TYPE == "futures":
                        if len(active_symbols) > 0 and all(not s.startswith(("C-", "P-", "MV-")) for s in active_symbols):
                            already_matching = True
                    else:
                        calls = [o for o in all_opts if o.get("type") == "call"]
                        puts = [o for o in all_opts if o.get("type") == "put"]

                        calls_by_oi = sorted(calls, key=lambda x: float(x.get("oi", 0) or 0), reverse=True)
                        puts_by_oi = sorted(puts, key=lambda x: float(x.get("oi", 0) or 0), reverse=True)

                        calls_by_vol = sorted(calls, key=lambda x: float(x.get("volume") or x.get("turnover") or 0), reverse=True)
                        puts_by_vol = sorted(puts, key=lambda x: float(x.get("volume") or x.get("turnover") or 0), reverse=True)

                        t_strike = PENDING_TARGET_STRIKE
                        rank_idx = get_rank_index(t_strike)
                        if rank_idx is not None:
                            hc_t = calls_by_oi[min(rank_idx, len(calls_by_oi) - 1)] if calls_by_oi else None
                            hp_t = puts_by_oi[min(rank_idx, len(puts_by_oi) - 1)] if puts_by_oi else None
                        elif t_strike == "highest_volume":
                            hc_t = calls_by_vol[0] if calls_by_vol else None
                            hp_t = puts_by_vol[0] if puts_by_vol else None
                        elif t_strike == "vol_oi":
                            calls_by_vol_rank = {c["symbol"]: i for i, c in enumerate(calls_by_vol)}
                            calls_by_oi_rank = {c["symbol"]: i for i, c in enumerate(calls_by_oi)}
                            calls_fused = sorted(calls, key=lambda x: calls_by_vol_rank.get(x["symbol"], 999) + calls_by_oi_rank.get(x["symbol"], 999))
                            hc_t = calls_fused[0] if calls_fused else None

                            puts_by_vol_rank = {p["symbol"]: i for i, p in enumerate(puts_by_vol)}
                            puts_by_oi_rank = {p["symbol"]: i for i, p in enumerate(puts_by_oi)}
                            puts_fused = sorted(puts, key=lambda x: puts_by_vol_rank.get(x["symbol"], 999) + puts_by_oi_rank.get(x["symbol"], 999))
                            hp_t = puts_fused[0] if puts_fused else None
                        elif t_strike == "atm":
                            hc_t = select_atm_oi_option(calls, spot)
                            hp_t = select_atm_oi_option(puts, spot)
                        else:
                            hc_t = hp_t = None

                        if hc_t or hp_t:
                            os_call_t = resolve_openstrike_order_opt(hc_t, all_opts)
                            os_put_t = resolve_openstrike_order_opt(hp_t, all_opts)
                            target_symbols = set()
                            if os_call_t:
                                target_symbols.add(os_call_t["symbol"])
                            if os_put_t:
                                target_symbols.add(os_put_t["symbol"])

                            if len(active_symbols) > 0 and active_symbols.issubset(target_symbols):
                                already_matching = True

                if already_matching:
                    STRATEGY_MODE = PENDING_STRATEGY_MODE
                    OPENSTRIKE_TARGET_STRIKE = PENDING_TARGET_STRIKE
                    STRATEGY_SWITCH_PENDING = False
                    PENDING_STRATEGY_MODE = ""
                    PENDING_TARGET_STRIKE = ""

                    if STRATEGY_MODE == "OPENSTRIKE" and ORDER_TYPE != "futures":
                        OPENSTRIKE_CALL_OPT = hc_t
                        OPENSTRIKE_PUT_OPT = hp_t
                    elif STRATEGY_MODE == "STRADDLE":
                        if mv_list:
                            mv_by_vol = sorted(mv_list, key=lambda x: x["turnover"], reverse=True)
                            STRADDLE_VOLUME_TARGET = mv_by_vol[0] if mv_by_vol else None
                            mv_by_oi = sorted(mv_list, key=lambda x: x["oi"], reverse=True)
                            STRADDLE_OI_TARGET = mv_by_oi[0] if mv_by_oi else None

                            if OPENSTRIKE_TARGET_STRIKE == "highest_volume":
                                STRADDLE_TARGET_CONTRACT = STRADDLE_VOLUME_TARGET
                            elif OPENSTRIKE_TARGET_STRIKE == "vol_oi":
                                vol_ranks = {item["symbol"]: i for i, item in enumerate(mv_by_vol)}
                                oi_ranks = {item["symbol"]: i for i, item in enumerate(mv_by_oi)}
                                mv_fused = sorted(mv_list, key=lambda x: vol_ranks.get(x["symbol"], 999) + oi_ranks.get(x["symbol"], 999))
                                STRADDLE_TARGET_CONTRACT = mv_fused[0] if mv_fused else None
                            else:
                                STRADDLE_TARGET_CONTRACT = STRADDLE_OI_TARGET

                    _save_settings()
                    send_telegram(
                        f"🔄 STRATEGY SWITCH COMPLETED (Matching Positions Detected)\n"
                        f"Active positions already match the pending target.\n"
                        f"Strategy Mode : {STRATEGY_MODE}\n"
                        f"Target Strike : {OPENSTRIKE_TARGET_STRIKE}\n"
                        f"Time : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
                    )

            cn, pn, pcr_n = oi_pcr(near)
            cx, px, pcr_x = oi_pcr(nxt)
            ca, pa, pcr_a = oi_pcr(all_opts)

            delta, gamma, theta, vega = greek_avg(near)
            mp = max_pain(near)

            if API_DOWN:
                try:
                    _upnl_now = upnl
                except NameError:
                    _upnl_now = 0
                wallet_upnl_pct = (_upnl_now / bal * 100) if bal > 0 else 0
                blocked_upnl_pct = (_upnl_now / blocked * 100) if blocked > 0 else 0
                _u, _hl, _hb = render_margin_heatmap(bal, blocked)
                _uc, _dr, _ds, _di, _ = calculate_margin_drift(bal, blocked, effective_min_margin)
                _as, _ast, _ab = render_api_health_bar()
                render_terminal_ui(
                    now=datetime.now(), spot=spot, decision="NO TRADE", source="API DOWN",
                    bal=bal, blocked=blocked, upnl=_upnl_now,
                    wallet_upnl_pct=wallet_upnl_pct, blocked_upnl_pct=blocked_upnl_pct,
                    used_pct_ui=_u, heat_level=_hl, heat_bar=_hb,
                    delta=delta, gamma=gamma,
                    position_details=position_details, position_count=position_count,
                    execution_status="API DOWN (no orders)",
                    used_pct_calc=_uc, margin_drift=_dr, drift_status=_ds, drift_icon=_di,
                    api_score=_as, api_status=_ast, api_bar=_ab,
                    expiry_oi_list=expiry_oi_list_primary or [], expiry_oi_list_secondary=expiry_oi_list_secondary_oi or [],
                    spot_secondary=spot_secondary_oi, symbol_secondary=symbol_secondary_oi, symbol_primary=main_sym,
                    all_expiry_max_pain_primary=all_expiry_mp_primary, all_expiry_max_pain_secondary=all_expiry_mp_secondary,
                    projected_profit=None, max_loss=None,
                    position_delta_sum=None, position_gamma_sum=None, position_theta_sum=None,
                    position_vega_sum=None, position_rho_sum=None,
                    strike_order_ok=None, strike_order_msg=None, option_metrics=None,
                    last_executed_signal=LAST_EXECUTED_SIGNAL,
                    **price_change_ui_kwargs
                )
                time.sleep(REFRESH_SECONDS)
                continue

            if (
                STRATEGY_MODE == "OPENSTRIKE"
                and not STARTUP_OPENSTRIKE_CLEANUP_DONE
                and not API_DOWN
                and not KILL_SWITCH
                and OPENSTRIKE_CALL_OPT is not None
                and OPENSTRIKE_PUT_OPT is not None
                and USER_AUTO_EXECUTION
            ):
                print("\n🧹 STARTUP: Running OPENSTRIKE target positions cleanup...", flush=True)
                os_call = _os_call_resolved
                os_put  = _os_put_resolved

                target_symbols = set()
                if ORDER_TYPE != "futures":
                    if custom_strategy_active:
                        for opt in [custom_call_sell, custom_put_sell, custom_call_buy, custom_put_buy]:
                            if opt:
                                target_symbols.add(opt["symbol"])
                    else:
                        if os_call:
                            target_symbols.add(os_call["symbol"])
                        if os_put:
                            target_symbols.add(os_put["symbol"])
                else:
                    target_symbols.add(f"{SYMBOL}USD")

                cleaned_any = False
                for p in positions_all:
                    p_sym = p.get("product_symbol", "")
                    p_size = float(p.get("size", 0))
                    if p_sym and p_size != 0:
                        is_opt_pos = p_sym.startswith(("C-", "P-", "MV-"))
                        should_close = False

                        if ORDER_TYPE != "futures":
                            if not is_opt_pos:
                                should_close = True
                            elif p_sym not in target_symbols:
                                should_close = True
                        else:
                            if is_opt_pos:
                                should_close = True
                            elif p_sym not in target_symbols:
                                should_close = True

                        if should_close:
                            print(f"🛑 STARTUP CLEANUP: Squaring off position {p_sym} (size: {p_size})", flush=True)
                            square_off_position(p_sym, p_size, reason="STARTUP_OPENSTRIKE_CLEANUP")
                            send_telegram(
                                f"🔄 STARTUP OPENSTRIKE CLEANUP\n"
                                f"Squared off: {p_sym}\n"
                                f"Size       : {p_size}\n"
                                f"Time       : {datetime.now().strftime('%H:%M:%S')}"
                            )
                            cleaned_any = True
                            time.sleep(0.5)

                if cleaned_any:
                    time.sleep(0.5)
                    positions_all = get_all_positions()
                    positions = get_positions()

                STARTUP_OPENSTRIKE_CLEANUP_DONE = True
                print("🧹 STARTUP: OPENSTRIKE target positions cleanup complete.\n", flush=True)

            has_active_position = any(
                p.get("product_symbol", "").startswith(("C-", "P-", "MV-"))
                and float(p.get("size", 0)) != 0
                for p in positions
            )

            if not has_active_position:
                execution_status = "NO POSITION → STRATEGY ENTRY ALLOWED"
            else:
                execution_status = "POSITION EXISTS → MANAGE ONLY"

            short_call_pos = short_put_pos = None
            long_call_pos = None
            long_put_pos  = None

            pos_upnl_usd, pos_upnl_btc, position_count, position_details = calculate_upnl(positions_all, spot_btc=spot_btc, spot_eth=spot_eth)
            active_positions = [
                p for p in positions
                if p.get("product_symbol", "").startswith(("C-", "P-", "MV-")) and float(p.get("size", 0)) != 0
            ]

            dominant_expiry_this_cycle = None
            if STRATEGY_MODE != "OPENSTRIKE" and len(active_positions) >= 1 and USER_AUTO_EXECUTION:
                exp_counts = Counter()
                for p in active_positions:
                    exp = extract_expiry(p.get("product_symbol", ""))
                    if exp is not None:
                        exp_counts[exp] += 1
                if len(exp_counts) > 1:
                    dominant_expiry = exp_counts.most_common(1)[0][0]
                    wrong_expiry_positions = [p for p in active_positions if extract_expiry(p.get("product_symbol", "")) != dominant_expiry]
                    for p in wrong_expiry_positions:
                        sym = p.get("product_symbol", "")
                        size = float(p.get("size", 0))
                        if sym and size != 0:
                            square_off_position(sym, size, reason="WRONG_EXPIRY")
                            send_telegram(
                                f"🔄 EXPIRY FIX: Squared off wrong-expiry leg\n"
                                f"Symbol: {sym}\n"
                                f"Size: {size}\n"
                                f"Dominant expiry kept: {dominant_expiry.strftime('%d-%b-%Y')}\n"
                                f"Time: {datetime.now().strftime('%H:%M:%S')}"
                            )
                    SKIP_REST = True
                    _uc, _dr, _ds, _di, _ = calculate_margin_drift(bal, blocked, effective_min_margin)
                    render_terminal_ui(
                        now=datetime.now(), spot=spot_primary_display, decision="NO TRADE", source="Expiry fix (squaring wrong-expiry)",
                        bal=bal, blocked=blocked, upnl=wallet_upnl,
                        wallet_upnl_pct=wallet_upnl_pct, blocked_upnl_pct=blocked_upnl_pct,
                        used_pct_ui=used_pct_ui, heat_level=heat_level, heat_bar=heat_bar,
                        delta=delta, gamma=gamma,
                        position_details=position_details, position_count=position_count,
                        execution_status="Expiry fix (squaring wrong-expiry legs)",
                        used_pct_calc=_uc, margin_drift=_dr, drift_status=_ds, drift_icon=_di,
                        api_score=api_score, api_status=api_status, api_bar=api_bar,
                        expiry_oi_list=expiry_oi_list_primary or [], expiry_oi_list_secondary=expiry_oi_list_secondary_oi or [],
                        spot_secondary=spot_secondary_oi, symbol_secondary=symbol_secondary_oi, symbol_primary=main_sym,
                        all_expiry_max_pain_primary=all_expiry_mp_primary, all_expiry_max_pain_secondary=all_expiry_mp_secondary,
                        projected_profit=None, max_loss=None,
                        position_delta_sum=None, position_gamma_sum=None, position_theta_sum=None,
                        position_vega_sum=None, position_rho_sum=None,
                        strike_order_ok=None, strike_order_msg=None, option_metrics=None,
                        last_executed_signal=LAST_EXECUTED_SIGNAL,
                        **price_change_ui_kwargs
                    )
                    FIRST_UI_RENDER_DONE = True
                    time.sleep(REFRESH_SECONDS)
                    continue
                if exp_counts:
                    dominant_expiry_this_cycle = exp_counts.most_common(1)[0][0]
                    exp_still_valid = any(o["expiry"] == dominant_expiry_this_cycle for o in all_opts)
                    if not exp_still_valid:
                        dominant_expiry_this_cycle = None

            execution_blocked = False
            if len(active_positions) > 3 and not (EQUALITY_EVENT or EQUALITY_MANUAL_EXEC):
                execution_blocked = True
                execution_status = "⚠️ Execution blocked — max 3 legs per instrument"

            has_short_call = has_long_put = has_short_put = has_long_call = False
            has_long_10d_call = has_long_10d_put = False
            has_any_long_call = False

            for pos in positions:
                symbol = pos.get("product_symbol", "")
                size = float(pos.get("size", 0))
                if size == 0:
                    continue
                delta_val = abs(float(pos.get("delta", 0))) if pos.get("delta") is not None else 0

                if symbol.startswith("C-"):
                    if size < 0:
                        short_call_pos = pos
                        has_short_call = True
                    else:
                        long_call_pos = pos
                        has_long_call = True
                        has_any_long_call = True
                        if abs(delta_val - HEDGE_DELTA_TARGET) <= DELTA_THRESHOLD:
                            has_long_10d_call = True

                elif symbol.startswith("P-"):
                    if size < 0:
                        short_put_pos = pos
                        has_short_put = True
                    else:
                        long_put_pos = pos
                        has_long_put = True
                        if abs(delta_val - HEDGE_DELTA_TARGET) <= DELTA_THRESHOLD:
                            has_long_10d_put = True
            if STRATEGY_MODE == "OPENSTRIKE" and ORDER_TYPE != "futures":
                if has_short_call:
                    _clear_openstrike_missing_leg_pending("call")
                if has_short_put:
                    _clear_openstrike_missing_leg_pending("put")
            if API_DOWN:
                execution_status = "PAUSED — API DOWN"
                time.sleep(REFRESH_SECONDS)
                SKIP_REST = True
            elif time.time() < API_RECOVERY_COOLDOWN_UNTIL:
                execution_status = f"STABILIZING — API just recovered (no orders for {API_RECOVERY_COOLDOWN_SEC}s)"
                time.sleep(REFRESH_SECONDS)
                SKIP_REST = True

            position_changes = detect_position_changes(positions)
            has_new_position = any("NEW POSITION" in c for c in position_changes)
            if has_new_position:
                PENDING_NEW_POSITION_ALERT = True

            positions_api_healthy = HEALTH.get("POSITIONS", True)
            _has_futures_pos = ORDER_TYPE == "futures" and any(
                p.get("product_symbol") == f"{SYMBOL}USD" and float(p.get("size", 0)) != 0
                for p in positions
            )
            if len(active_positions) == 0 and not _has_futures_pos and positions_api_healthy:
                CONSECUTIVE_ZERO_POSITION_CYCLES = CONSECUTIVE_ZERO_POSITION_CYCLES + 1
            else:
                CONSECUTIVE_ZERO_POSITION_CYCLES = 0
            if CONSECUTIVE_ZERO_POSITION_CYCLES >= 2:
                LAST_EXECUTED_SIGNAL = None

                if time.time() - LAST_EXPIRY_ROLL_TELEGRAM_AT > 60:
                    if USER_AUTO_EXECUTION and ORDER_TYPE != "futures":
                        send_telegram(
                            f"📅 EXPIRY ROLL: Positions 0 confirmed (2 cycles). Contract settled — new payoff in new near expiry.\n"
                            f"Time: {datetime.now().strftime('%H:%M:%S')}"
                            f"{_build_analytics_telegram_summary(spot)}"
                        )
                    LAST_EXPIRY_ROLL_TELEGRAM_AT = time.time()

            upnl = wallet_upnl if abs(wallet_upnl) > 0 else pos_upnl_usd
            wallet_upnl_pct = round((upnl / bal) * 100, 2) if bal > 0 else 0
            blocked_upnl_pct = round((upnl / blocked) * 100, 2) if blocked > 0 else 0

            max_oi_expiry_display = None
            if expiry_oi_list_primary and len(expiry_oi_list_primary) > 0:
                el = [i for i in expiry_oi_list_primary if i[0] != "OPENSTRIKE_MSG"]
                pcr_n = el[0][3] if len(el) >= 1 else 0
                pcr_x = el[1][3] if len(el) >= 2 else 0
                ca = sum(i[1] for i in el)
                pa = sum(i[2] for i in el)
                pcr_a = round(pa / ca, 2) if ca else 0
                max_oi_row = max(el, key=lambda i: (i[1] or 0) + (i[2] or 0)) if el else (None, 0, 0, 0, None)
                ca_max, pa_max = (max_oi_row[1], max_oi_row[2]) if len(max_oi_row) >= 3 else (0, 0)
                if max_oi_row and len(max_oi_row) > 0:
                    max_oi_expiry_display = max_oi_row[0]
                decision, source = decide(pcr_n, pcr_x, pcr_a, ca, pa, ca_max, pa_max)
            else:
                el = []
                for exp in sorted(set(o["expiry"] for o in all_opts)):
                    opts_exp = [o for o in all_opts if o["expiry"] == exp]
                    c, p, pr = oi_pcr(opts_exp)
                    mp = max_pain(opts_exp) if opts_exp else None
                    el.append((exp, c, p, pr, mp))
                pcr_n = el[0][3] if len(el) >= 1 else 0
                pcr_x = el[1][3] if len(el) >= 2 else 0
                ca = sum(i[1] for i in el)
                pa = sum(i[2] for i in el)
                pcr_a = round(pa / ca, 2) if ca else 0
                max_oi_row = max(el, key=lambda i: (i[1] or 0) + (i[2] or 0)) if el else (None, 0, 0, 0, None)
                ca_max, pa_max = (max_oi_row[1], max_oi_row[2]) if len(max_oi_row) >= 3 else (0, 0)
                if max_oi_row and len(max_oi_row) > 0:
                    max_oi_expiry_display = max_oi_row[0]
                decision, source = decide(pcr_n, pcr_x, pcr_a, ca, pa, ca_max, pa_max)

            # MAX_OPEN_INTEREST and other strategy checks are vestigial. Only OPENSTRIKE/STRADDLE are supported.
            LAST_MAX_OI_EXPIRY_STR = None

            # NEW_POSITION telegram is deferred to end of cycle (after sizing adjustments)
            # so that the reported leg size reflects the final target size, not the initial 1x.

            if LAST_EXECUTED_SIGNAL is None and has_active_position:
                if has_short_call:
                    LAST_EXECUTED_SIGNAL = "SELL CALL"
                elif has_short_put:
                    LAST_EXECUTED_SIGNAL = "SELL PUT"

            if LAST_EXECUTED_SIGNAL is None and ORDER_TYPE == "futures":
                _perp_sym_fr = f"{SYMBOL}USD"
                for _p_fr in positions:
                    if _p_fr.get("product_symbol") == _perp_sym_fr:
                        _fsize_fr = float(_p_fr.get("size", 0))
                        if _fsize_fr < 0:
                            LAST_EXECUTED_SIGNAL = "SELL CALL"
                        elif _fsize_fr > 0:
                            LAST_EXECUTED_SIGNAL = "SELL PUT"
                        break

            execution_decision = decision
            if (
                decision == "NO TRADE"
                and has_active_position
                and LAST_EXECUTED_SIGNAL in ("SELL CALL", "SELL PUT")
            ):
                execution_decision = LAST_EXECUTED_SIGNAL

            if len(active_positions) >= 3:
                execution_status = "EQUALITY SKIPPED — MAX LEGS"
                adjustments = []

            if execution_blocked:
                execution_status = "BLOCKED: MAX 3 LEGS (per instrument)"

            elif execution_status.startswith("WAITING"):
                pass

            else:
                execution_status = "AUTO EXEC READY"

            if SKIP_REST:
                execution_status = execution_status or "SKIPPED (SOFT)"
                SKIP_REST = False

            bias_changed = (
                LAST_EXECUTED_SIGNAL is not None
                and execution_decision != LAST_EXECUTED_SIGNAL
            )

            if PENDING_BIAS_REBALANCE in ("SELL CALL", "SELL PUT"):
                _bal_p, _blocked_p, _ = wallet_usd()
                _free_p = (_bal_p - _blocked_p) if _bal_p is not None else 0
                _low_balance_mode_p = (
                    (_bal_p is not None and _bal_p <= LOW_BALANCE_USD)
                    or (_free_p <= LOW_FREE_USD)
                )
                if not _low_balance_mode_p and decision == PENDING_BIAS_REBALANCE:
                    bias_changed = True

            if bias_changed and MARGIN_ENFORCEMENT_MODE == "SIGNAL":
                EQUALITY_EVENT = True
                EQUALITY_TRIGGER_REASON = "BIAS_CHANGE_MARGIN"
                used_pct = (blocked / bal * 100) if bal > 0 else 0
                pos_line = format_position_line_for_message(active_positions)

                should_send = True
                if decision == "NO TRADE":
                    if NO_TRADE_ALERT_SENT_FOR_OLD_BIAS == LAST_EXECUTED_SIGNAL:
                        should_send = False
                    else:
                        NO_TRADE_ALERT_SENT_FOR_OLD_BIAS = LAST_EXECUTED_SIGNAL
                else:
                    NO_TRADE_ALERT_SENT_FOR_OLD_BIAS = None
                if STRATEGY_MODE == "OPENSTRIKE":
                    strategy_line = f"Strategy: {STRATEGY_MODE}\n"
                    data_expiry_line = ""
                else:
                    strategy_line = f"Strategy: {STRATEGY_MODE}\n"
                    data_expiry_line = ""
                if should_send:
                    send_telegram(
                        f"🔄 BIAS CHANGE ALERT\n"
                        f"Time: {datetime.now().strftime('%H:%M:%S')}\n"
                        f"Old Bias: {LAST_EXECUTED_SIGNAL}\n"
                        f"New Bias: {decision}\n"
                        f"{strategy_line}"
                        f"{data_expiry_line}"
                        f"Spot: {spot:.2f}\n"
                        f"Balance: ${bal:.2f}\n"
                        f"Used: ${blocked:.2f} ({used_pct:.1f}%)\n"
                        f"Position: {pos_line}"
                        f"{_build_analytics_telegram_summary(spot)}"
                    )

                if not USER_AUTO_EXECUTION:
                    LAST_EXECUTED_SIGNAL = decision

                has_any_long_call = False
                has_long_10d_call = False
                has_long_10d_put = False

                if KILL_SWITCH:
                    break
                if bias_changed and decision != "NO TRADE" and USER_AUTO_EXECUTION:
                    unknown_positions = identify_unknown_positions(
                        positions,
                        decision
                    )

                    if unknown_positions and not KILL_SWITCH:
                        squared = square_off_unknown_positions(unknown_positions)
                        if squared > 0:
                            print("🛑 Square-off done — skipping execution this cycle")
                            SKIP_REST = True
                            _uc, _dr, _ds, _di, _ = calculate_margin_drift(bal, blocked, effective_min_margin)
                            render_terminal_ui(
                                now=datetime.now(), spot=spot, decision=decision, source=source,
                                bal=bal, blocked=blocked, upnl=upnl,
                                wallet_upnl_pct=wallet_upnl_pct, blocked_upnl_pct=blocked_upnl_pct,
                                used_pct_ui=used_pct_ui, heat_level=heat_level, heat_bar=heat_bar,
                                delta=delta, gamma=gamma,
                                position_details=position_details, position_count=position_count,
                                execution_status="Square-off done (unknown legs) — skipping execution this cycle",
                                used_pct_calc=_uc, margin_drift=_dr, drift_status=_ds, drift_icon=_di,
                                api_score=api_score, api_status=api_status, api_bar=api_bar,
                                expiry_oi_list=expiry_oi_list_primary or [], expiry_oi_list_secondary=expiry_oi_list_secondary_oi or [],
                                spot_secondary=spot_secondary_oi, symbol_secondary=symbol_secondary_oi, symbol_primary=main_sym,
                                all_expiry_max_pain_primary=all_expiry_mp_primary, all_expiry_max_pain_secondary=all_expiry_mp_secondary,
                                projected_profit=None, max_loss=None,
                                position_delta_sum=None, position_gamma_sum=None, position_theta_sum=None,
                                position_vega_sum=None, position_rho_sum=None,
                                strike_order_ok=None, strike_order_msg=None, option_metrics=None,
                                last_executed_signal=LAST_EXECUTED_SIGNAL,
                                **price_change_ui_kwargs
                            )
                            time.sleep(REFRESH_SECONDS)
                            continue

                if (
                    ORDER_TYPE != "futures"
                    and USER_AUTO_EXECUTION
                    and not API_DOWN
                    and not KILL_SWITCH
                ):
                    _perp_sym = f"{SYMBOL}USD"
                    _fut_pos = next(
                        (p for p in positions_all
                         if p.get("product_symbol", "") == _perp_sym
                         and float(p.get("size", 0)) != 0),
                        None
                    )
                    if _fut_pos:
                        square_off_position(_perp_sym, float(_fut_pos.get("size", 0)), reason="OPTIONS_MODE_SWITCH")
                        send_telegram(
                            f"🔄 OPTIONS MODE: Futures position closed\n"
                            f"Symbol : {_perp_sym}\n"
                            f"Size   : {abs(float(_fut_pos.get('size', 0))):.0f}x\n"
                            f"Next   : Options position will be built\n"
                            f"Time   : {datetime.now().strftime('%H:%M:%S')}"
                        )
                        LAST_EXECUTED_SIGNAL = None
                        SKIP_REST = True
                        continue

                if (
                    ORDER_TYPE == "futures"
                    and bias_changed
                    and decision in ("SELL CALL", "SELL PUT")
                    and USER_AUTO_EXECUTION
                    and not API_DOWN
                    and not KILL_SWITCH
                ):
                    _opts_to_close = [
                        p for p in positions_all
                        if p.get("product_symbol", "").startswith(("C-", "P-", "MV-"))
                        and float(p.get("size", 0)) != 0
                        and _inst(p) == SYMBOL
                    ]
                    if _opts_to_close:
                        for _p in _opts_to_close:
                            square_off_position(_p["product_symbol"], float(_p.get("size", 0)), reason="FUTURES_MODE_SWITCH")
                            time.sleep(0.3)
                        send_telegram(
                            f"🔄 FUTURES MODE: Options positions closed on bias change\n"
                            f"Bias : {LAST_EXECUTED_SIGNAL} → {decision}\n"
                            f"Closed : {len(_opts_to_close)} leg(s)\n"
                            f"Next : Futures position will open\n"
                            f"Time : {datetime.now().strftime('%H:%M:%S')}"
                        )
                        LAST_EXECUTED_SIGNAL = None
                        SKIP_REST = True
                        time.sleep(0.5)
                        continue

                    LAST_EXECUTED_SIGNAL = None

                if (
                    STRATEGY_MODE == "OPENSTRIKE"
                    and ORDER_TYPE != "futures"
                    and bias_changed
                    and decision in ("SELL CALL", "SELL PUT")
                    and USER_AUTO_EXECUTION
                ):
                    _c_oi = float(OPENSTRIKE_CALL_OPT.get("oi", 0) or 0) if OPENSTRIKE_CALL_OPT else 0
                    _p_oi = float(OPENSTRIKE_PUT_OPT.get("oi", 0) or 0) if OPENSTRIKE_PUT_OPT else 0
                    _dom = "Call" if _c_oi > _p_oi else "Put"
                    execution_status = f"OPENSTRIKE: OI side shifted → {_dom} dominant (positions unchanged)"
                    LAST_EXECUTED_SIGNAL = decision
                    send_telegram(
                        f"📊 OPENSTRIKE OI SHIFT DETECTED\n"
                        f"Dominant side: {_dom} (Call OI {_fmt_oi(_c_oi)} vs Put OI {_fmt_oi(_p_oi)})\n"
                        f"Action: NO position change — strangle remains open\n"
                        f"Time: {datetime.now().strftime('%H:%M:%S')}"
                        f"{_build_analytics_telegram_summary(spot)}"
                    )
                    SKIP_REST = True
                elif (
                    bias_changed
                    and decision in ("SELL CALL", "SELL PUT")
                    and USER_AUTO_EXECUTION
                    and not API_DOWN
                    and not KILL_SWITCH
                    and ORDER_TYPE != "futures"
                ):
                    _bal_lb, _blocked_lb, _ = wallet_usd()
                    _free_lb = (_bal_lb - _blocked_lb) if _bal_lb is not None else 0
                    _low_balance_mode = (
                        (_bal_lb is not None and _bal_lb <= LOW_BALANCE_USD)
                        or (_free_lb <= LOW_FREE_USD)
                    )
                    if _low_balance_mode:
                        PENDING_BIAS_REBALANCE = decision
                        if not PENDING_BIAS_SINCE:
                            PENDING_BIAS_SINCE = time.time()

                    _exp_leg = None
                    for _p in [short_call_pos, short_put_pos, long_call_pos, long_put_pos]:
                        if _p:
                            _exp_leg = extract_expiry(_p.get("product_symbol", ""))
                            break
                    _opts_exp = [o for o in all_opts if o["expiry"] == _exp_leg] if _exp_leg else (near or all_opts)

                    positions = get_positions()
                    if API_DOWN:
                        SKIP_REST = True
                        _uc, _dr, _ds, _di, _ = calculate_margin_drift(bal, blocked, effective_min_margin)
                        render_terminal_ui(
                            now=datetime.now(), spot=spot, decision=decision, source=source,
                            bal=bal, blocked=blocked, upnl=upnl,
                            wallet_upnl_pct=wallet_upnl_pct, blocked_upnl_pct=blocked_upnl_pct,
                            used_pct_ui=used_pct_ui, heat_level=heat_level, heat_bar=heat_bar,
                            delta=delta, gamma=gamma,
                            position_details=position_details, position_count=position_count,
                            execution_status="API DOWN (no orders)",
                            used_pct_calc=_uc, margin_drift=_dr, drift_status=_ds, drift_icon=_di,
                            api_score=api_score, api_status=api_status, api_bar=api_bar,
                            expiry_oi_list=expiry_oi_list_primary or [], expiry_oi_list_secondary=expiry_oi_list_secondary_oi or [],
                            spot_secondary=spot_secondary_oi, symbol_secondary=symbol_secondary_oi, symbol_primary=main_sym,
                            all_expiry_max_pain_primary=all_expiry_mp_primary, all_expiry_max_pain_secondary=all_expiry_mp_secondary,
                            projected_profit=None, max_loss=None,
                            position_delta_sum=None, position_gamma_sum=None, position_theta_sum=None,
                            position_vega_sum=None, position_rho_sum=None,
                            strike_order_ok=None, strike_order_msg=None, option_metrics=None,
                            last_executed_signal=LAST_EXECUTED_SIGNAL,
                            **price_change_ui_kwargs
                        )
                        time.sleep(REFRESH_SECONDS)
                        continue
                    short_call_pos = short_put_pos = None
                    long_call_pos = long_put_pos = None
                    for _pos in positions:
                        _sym = _pos.get("product_symbol", "")
                        try:
                            _sz = float(_pos.get("size", 0))
                        except (ValueError, TypeError):
                            _sz = 0
                        if _sz == 0:
                            continue
                        if _sym.startswith("C-") and _sz < 0:
                            short_call_pos = _pos
                        elif _sym.startswith("C-") and _sz > 0:
                            long_call_pos = _pos
                        elif _sym.startswith("P-") and _sz < 0:
                            short_put_pos = _pos
                        elif _sym.startswith("P-") and _sz > 0:
                            long_put_pos = _pos

                    def _is_10d(p):
                        try:
                            d = abs(float(p.get("delta", 0) or 0))
                        except (ValueError, TypeError):
                            d = 0
                        return abs(d - HEDGE_DELTA_TARGET) <= DELTA_THRESHOLD

                    def _delta_abs(p):
                        try:
                            return abs(float(p.get("delta", 0) or 0))
                        except (ValueError, TypeError):
                            return 0.0

                    short_calls = []
                    short_puts = []
                    long_calls = []
                    long_puts = []
                    for _pos in positions:
                        _sym = _pos.get("product_symbol", "")
                        try:
                            _sz = float(_pos.get("size", 0))
                        except (ValueError, TypeError):
                            _sz = 0
                        if _sz == 0:
                            continue
                        if _sym.startswith("C-") and _sz < 0:
                            short_calls.append(_pos)
                        elif _sym.startswith("C-") and _sz > 0:
                            long_calls.append(_pos)
                        elif _sym.startswith("P-") and _sz < 0:
                            short_puts.append(_pos)
                        elif _sym.startswith("P-") and _sz > 0:
                            long_puts.append(_pos)

                    def _pick_best_10d(cands):
                        if not cands:
                            return None

                        def key(p):
                            d = _delta_abs(p)
                            return (0 if d <= 0.15 else 1, abs(d - 0.10), -abs(float(p.get("size", 0) or 0)))
                        return min(cands, key=key)

                    keep_lc = _pick_best_10d(long_calls)
                    keep_lp = _pick_best_10d(long_puts)

                    keep_sc = max(short_calls, key=lambda p: abs(float(p.get("size", 0) or 0))) if short_calls else None
                    keep_sp = max(short_puts, key=lambda p: abs(float(p.get("size", 0) or 0))) if short_puts else None

                    to_close = []
                    if STRATEGY_MODE == "OPENSTRIKE" and ORDER_TYPE != "futures":
                        if custom_strategy_active:
                            # Keep only our custom target positions
                            custom_targets = set()
                            for opt in [custom_call_sell, custom_put_sell, custom_call_buy, custom_put_buy]:
                                if opt:
                                    custom_targets.add(opt["symbol"])
                            
                            all_active = short_calls + short_puts + long_calls + long_puts
                            for p in all_active:
                                if p.get("product_symbol") not in custom_targets:
                                    to_close.append(p)
                        else:
                            to_close.extend(long_calls)
                            to_close.extend(long_puts)

                            if len(short_calls) > 1:
                                to_close.extend([p for p in short_calls if keep_sc and p is not keep_sc])
                            if len(short_puts) > 1:
                                to_close.extend([p for p in short_puts if keep_sp and p is not keep_sp])
                    else:
                        if decision == "SELL CALL":
                            to_close.extend(short_puts)

                            to_close.extend([p for p in short_calls if keep_sc and p is not keep_sc])
                        elif decision == "SELL PUT":
                            to_close.extend(short_calls)

                            to_close.extend([p for p in short_puts if keep_sp and p is not keep_sp])

                        to_close.extend([p for p in long_calls if keep_lc and p is not keep_lc])
                        to_close.extend([p for p in long_puts if keep_lp and p is not keep_lp])

                    if to_close:
                        for p in to_close:
                            sym_p = p.get("product_symbol", "")
                            try:
                                sz_p = float(p.get("size", 0))
                            except (ValueError, TypeError):
                                sz_p = 0
                            if sym_p and sz_p != 0:
                                square_off_position(sym_p, sz_p, reason="BIAS_CHANGE_CLEAN_EXTRA_LEGS")
                                time.sleep(0.2)
                        time.sleep(0.8)

                        positions = get_positions()
                        if API_DOWN:
                            SKIP_REST = True
                            continue

                        short_call_pos = short_put_pos = None
                        long_call_pos = long_put_pos = None
                        for _pos in positions:
                            _sym = _pos.get("product_symbol", "")
                            try:
                                _sz = float(_pos.get("size", 0))
                            except (ValueError, TypeError):
                                _sz = 0
                            if _sz == 0:
                                continue
                            if _sym.startswith("C-") and _sz < 0:
                                short_call_pos = _pos
                            elif _sym.startswith("C-") and _sz > 0:
                                long_call_pos = _pos
                            elif _sym.startswith("P-") and _sz < 0:
                                short_put_pos = _pos
                            elif _sym.startswith("P-") and _sz > 0:
                                long_put_pos = _pos

                    if _low_balance_mode:
                        _now = time.time()
                        _can_try = (_now - LOW_BALANCE_ALIGN_LAST_TRY) >= LOW_BALANCE_ALIGN_COOLDOWN_SEC

                        positions = get_positions()
                        if API_DOWN:
                            SKIP_REST = True
                            continue
                        short_call_pos = short_put_pos = None
                        long_call_pos = long_put_pos = None
                        for _pos in positions:
                            _sym = _pos.get("product_symbol", "")
                            try:
                                _sz = float(_pos.get("size", 0))
                            except (ValueError, TypeError):
                                _sz = 0
                            if _sz == 0:
                                continue
                            if _sym.startswith("C-") and _sz < 0:
                                short_call_pos = _pos
                            elif _sym.startswith("C-") and _sz > 0:
                                long_call_pos = _pos
                            elif _sym.startswith("P-") and _sz < 0:
                                short_put_pos = _pos
                            elif _sym.startswith("P-") and _sz > 0:
                                long_put_pos = _pos

                        _target_size = max(_abs_int_size(short_call_pos), _abs_int_size(short_put_pos), _abs_int_size(long_call_pos), _abs_int_size(long_put_pos), 1)

                        if _can_try:
                            LOW_BALANCE_ALIGN_LAST_TRY = _now
                            if decision == "SELL CALL":
                                if short_put_pos:
                                    square_off_position(short_put_pos["product_symbol"], float(short_put_pos.get("size", 0)), reason="LOW_BALANCE_BIAS_ALIGN")
                                    time.sleep(0.4)

                                if not short_call_pos:
                                    atm_call = select_atm_option(_opts_exp, spot, "call")
                                    if atm_call:
                                        place_order(atm_call["symbol"], "sell", _target_size, MARGIN_MODE.lower(), reason="LOW_BALANCE_BIAS_ALIGN")
                                        time.sleep(0.4)
                            elif decision == "SELL PUT":
                                if short_call_pos:
                                    square_off_position(short_call_pos["product_symbol"], float(short_call_pos.get("size", 0)), reason="LOW_BALANCE_BIAS_ALIGN")
                                    time.sleep(0.4)
                                if not short_put_pos:
                                    atm_put = select_atm_option(_opts_exp, spot, "put")
                                    if atm_put:
                                        place_order(atm_put["symbol"], "sell", _target_size, MARGIN_MODE.lower(), reason="LOW_BALANCE_BIAS_ALIGN")
                                        time.sleep(0.4)

                        _tier_lb = LEG_MODE
                        if _tier_lb == 3:
                            if long_call_pos:
                                square_off_position(long_call_pos["product_symbol"], float(long_call_pos.get("size", 0)), reason="LOW_BAL_TIER3_SELL_ONLY")
                                time.sleep(0.4)
                            if long_put_pos:
                                square_off_position(long_put_pos["product_symbol"], float(long_put_pos.get("size", 0)), reason="LOW_BAL_TIER3_SELL_ONLY")
                                time.sleep(0.4)
                        elif _tier_lb == 2 and long_call_pos and long_put_pos:
                            if decision == "SELL CALL":
                                square_off_position(long_call_pos["product_symbol"], float(long_call_pos.get("size", 0)), reason="LOW_BAL_TIER2_SELL_LONG")
                                time.sleep(0.4)
                            else:
                                square_off_position(long_put_pos["product_symbol"], float(long_put_pos.get("size", 0)), reason="LOW_BAL_TIER2_SELL_LONG")
                                time.sleep(0.4)

                        execution_status = "LOW BALANCE — bias aligned best-effort (no hedge rolls/adds)"
                        SKIP_REST = True

                    _sz_sc = _abs_int_size(short_call_pos)
                    _sz_sp = _abs_int_size(short_put_pos)
                    _sz_lc = _abs_int_size(long_call_pos)
                    _sz_lp = _abs_int_size(long_put_pos)
                    _target_size = max(_sz_sc, _sz_sp, _sz_lc, _sz_lp, 1)
                    _bal2, _blocked2, _ = wallet_usd()
                    _tier_rebal = LEG_MODE

                    _used_pct_now = (_blocked2 / _bal2 * 100) if _bal2 > 0 else 0
                    _margin_ceiling = (effective_min_margin * 100) * 1.01
                    _ceiling_hard = _margin_ceiling + 1

                    _short_pos = short_call_pos if decision == "SELL CALL" else short_put_pos
                    if (
                        _used_pct_now >= _ceiling_hard
                        and long_call_pos
                        and long_put_pos
                        and _short_pos
                    ):
                        _base = min(_abs_int_size(long_call_pos), _abs_int_size(long_put_pos), _abs_int_size(_short_pos))
                        if _base > 1:
                            _new = max(1, int(_base * (_ceiling_hard / max(_used_pct_now, 0.0001))))
                            _close_each = max(0, _base - _new)
                            if _close_each > 0:
                                square_off_position(_short_pos["product_symbol"], -_close_each, reason="MARGIN_REDUCE_ON_BIAS_CHANGE")
                                square_off_position(long_call_pos["product_symbol"], +_close_each, reason="MARGIN_REDUCE_ON_BIAS_CHANGE")
                                square_off_position(long_put_pos["product_symbol"], +_close_each, reason="MARGIN_REDUCE_ON_BIAS_CHANGE")
                                time.sleep(0.8)

                                positions = get_positions()
                                if API_DOWN:
                                    SKIP_REST = True
                                    continue
                                short_call_pos = short_put_pos = None
                                long_call_pos = long_put_pos = None
                                for _pos in positions:
                                    _sym = _pos.get("product_symbol", "")
                                    try:
                                        _sz = float(_pos.get("size", 0))
                                    except (ValueError, TypeError):
                                        _sz = 0
                                    if _sz == 0:
                                        continue
                                    if _sym.startswith("C-") and _sz < 0:
                                        short_call_pos = _pos
                                    elif _sym.startswith("C-") and _sz > 0:
                                        long_call_pos = _pos
                                    elif _sym.startswith("P-") and _sz < 0:
                                        short_put_pos = _pos
                                    elif _sym.startswith("P-") and _sz > 0:
                                        long_put_pos = _pos
                                _target_size = max(_abs_int_size(short_call_pos), _abs_int_size(short_put_pos), _abs_int_size(long_call_pos), _abs_int_size(long_put_pos), 1)

                    if STRATEGY_MODE == "OPENSTRIKE" and ORDER_TYPE != "futures":
                        pass
                    elif _tier_rebal == 3:
                        if long_call_pos:
                            square_off_position(long_call_pos["product_symbol"], float(long_call_pos.get("size", 0)), reason="TIER3_BIAS_REBAL")
                            time.sleep(0.4)
                        if long_put_pos:
                            square_off_position(long_put_pos["product_symbol"], float(long_put_pos.get("size", 0)), reason="TIER3_BIAS_REBAL")
                            time.sleep(0.4)
                    elif _tier_rebal == 2:
                        if decision == "SELL CALL":
                            if long_call_pos:
                                square_off_position(long_call_pos["product_symbol"], float(long_call_pos.get("size", 0)), reason="TIER2_ONE_LONG")
                                time.sleep(0.4)
                            long_call_pos = None
                            if long_put_pos and not _is_10d(long_put_pos):
                                _sz = float(long_put_pos.get("size", 0))
                                if _sz != 0:
                                    square_off_position(long_put_pos["product_symbol"], _sz, reason="BIAS_CHANGE_LONG_ROLL")
                                    time.sleep(0.5)
                                put_10d = select_delta_option(_opts_exp, "put", 0.10)
                                if put_10d:
                                    place_order(put_10d["symbol"], "buy", _target_size, MARGIN_MODE.lower(), reason="BIAS_CHANGE_LONG_ROLL")
                                    time.sleep(0.5)
                            if not long_put_pos:
                                put_10d = select_delta_option(_opts_exp, "put", 0.10)
                                if put_10d:
                                    place_order(put_10d["symbol"], "buy", _target_size, MARGIN_MODE.lower(), reason="BIAS_CHANGE_BUILD")
                                    time.sleep(0.5)
                            elif _abs_int_size(long_put_pos) < _target_size:
                                diff = _target_size - _abs_int_size(long_put_pos)
                                if diff > 0:
                                    place_order(long_put_pos["product_symbol"], "buy", diff, MARGIN_MODE.lower(), reason="BIAS_CHANGE_BUILD")
                                    time.sleep(0.5)
                        else:
                            if long_put_pos:
                                square_off_position(long_put_pos["product_symbol"], float(long_put_pos.get("size", 0)), reason="TIER2_ONE_LONG")
                                time.sleep(0.4)
                            long_put_pos = None
                            if long_call_pos and not _is_10d(long_call_pos):
                                _sz = float(long_call_pos.get("size", 0))
                                if _sz != 0:
                                    square_off_position(long_call_pos["product_symbol"], _sz, reason="BIAS_CHANGE_LONG_ROLL")
                                    time.sleep(0.5)
                                call_10d = select_delta_option(_opts_exp, "call", 0.10)
                                if call_10d:
                                    place_order(call_10d["symbol"], "buy", _target_size, MARGIN_MODE.lower(), reason="BIAS_CHANGE_LONG_ROLL")
                                    time.sleep(0.5)
                            if not long_call_pos:
                                call_10d = select_delta_option(_opts_exp, "call", 0.10)
                                if call_10d:
                                    place_order(call_10d["symbol"], "buy", _target_size, MARGIN_MODE.lower(), reason="BIAS_CHANGE_BUILD")
                                    time.sleep(0.5)
                            elif _abs_int_size(long_call_pos) < _target_size:
                                diff = _target_size - _abs_int_size(long_call_pos)
                                if diff > 0:
                                    place_order(long_call_pos["product_symbol"], "buy", diff, MARGIN_MODE.lower(), reason="BIAS_CHANGE_BUILD")
                                    time.sleep(0.5)
                    else:
                        if long_call_pos and not _is_10d(long_call_pos):
                            _sz = float(long_call_pos.get("size", 0))
                            if _sz != 0:
                                square_off_position(long_call_pos["product_symbol"], _sz, reason="BIAS_CHANGE_LONG_ROLL")
                                time.sleep(0.5)
                            call_10d = select_delta_option(_opts_exp, "call", 0.10)
                            if call_10d:
                                place_order(call_10d["symbol"], "buy", _target_size, MARGIN_MODE.lower(), reason="BIAS_CHANGE_LONG_ROLL")
                                time.sleep(0.5)
                        if long_put_pos and not _is_10d(long_put_pos):
                            _sz = float(long_put_pos.get("size", 0))
                            if _sz != 0:
                                square_off_position(long_put_pos["product_symbol"], _sz, reason="BIAS_CHANGE_LONG_ROLL")
                                time.sleep(0.5)
                            put_10d = select_delta_option(_opts_exp, "put", 0.10)
                            if put_10d:
                                place_order(put_10d["symbol"], "buy", _target_size, MARGIN_MODE.lower(), reason="BIAS_CHANGE_LONG_ROLL")
                                time.sleep(0.5)

                    if (STRATEGY_MODE == "OPENSTRIKE" and ORDER_TYPE != "futures"):
                        pass
                    elif _tier_rebal == 1:
                        if not long_call_pos:
                            call_10d = select_delta_option(_opts_exp, "call", 0.10)
                            if call_10d:
                                place_order(call_10d["symbol"], "buy", _target_size, MARGIN_MODE.lower(), reason="BIAS_CHANGE_BUILD")
                                time.sleep(0.5)
                        elif _abs_int_size(long_call_pos) < _target_size:
                            diff = _target_size - _abs_int_size(long_call_pos)
                            if diff > 0:
                                place_order(long_call_pos["product_symbol"], "buy", diff, MARGIN_MODE.lower(), reason="BIAS_CHANGE_BUILD")
                                time.sleep(0.5)

                        if not long_put_pos:
                            put_10d = select_delta_option(_opts_exp, "put", 0.10)
                            if put_10d:
                                place_order(put_10d["symbol"], "buy", _target_size, MARGIN_MODE.lower(), reason="BIAS_CHANGE_BUILD")
                                time.sleep(0.5)
                        elif _abs_int_size(long_put_pos) < _target_size:
                            diff = _target_size - _abs_int_size(long_put_pos)
                            if diff > 0:
                                place_order(long_put_pos["product_symbol"], "buy", diff, MARGIN_MODE.lower(), reason="BIAS_CHANGE_BUILD")
                                time.sleep(0.5)

                    if decision == "SELL CALL":
                        if short_put_pos:
                            square_off_position(short_put_pos["product_symbol"], float(short_put_pos.get("size", 0)), reason="BIAS_CHANGE_SHORT_SWAP")
                            time.sleep(0.5)
                        if not short_call_pos:
                            atm_call = select_atm_option(_opts_exp, spot, "call")
                            if atm_call:
                                place_order(atm_call["symbol"], "sell", _target_size, MARGIN_MODE.lower(), reason="BIAS_CHANGE_SHORT_SWAP")
                                time.sleep(0.5)
                        elif _abs_int_size(short_call_pos) < _target_size:
                            diff = _target_size - _abs_int_size(short_call_pos)
                            if diff > 0:
                                place_order(short_call_pos["product_symbol"], "sell", diff, MARGIN_MODE.lower(), reason="BIAS_CHANGE_SHORT_SWAP")
                                time.sleep(0.5)
                    elif decision == "SELL PUT":
                        if short_call_pos:
                            square_off_position(short_call_pos["product_symbol"], float(short_call_pos.get("size", 0)), reason="BIAS_CHANGE_SHORT_SWAP")
                            time.sleep(0.5)
                        if not short_put_pos:
                            atm_put = select_atm_option(_opts_exp, spot, "put")
                            if atm_put:
                                place_order(atm_put["symbol"], "sell", _target_size, MARGIN_MODE.lower(), reason="BIAS_CHANGE_SHORT_SWAP")
                                time.sleep(0.5)
                        elif _abs_int_size(short_put_pos) < _target_size:
                            diff = _target_size - _abs_int_size(short_put_pos)
                            if diff > 0:
                                place_order(short_put_pos["product_symbol"], "sell", diff, MARGIN_MODE.lower(), reason="BIAS_CHANGE_SHORT_SWAP")
                                time.sleep(0.5)

                    LAST_EXECUTED_SIGNAL = decision
                    EQUALITY_EVENT = True
                    EQUALITY_TRIGGER_REASON = "BIAS_CHANGE_REBALANCE"
                    PENDING_BIAS_REBALANCE = None
                    PENDING_BIAS_SINCE = 0.0
                    SKIP_REST = True
                    continue

            if (
                STRATEGY_MODE == "STRADDLE"
                and not SKIP_REST
                and USER_AUTO_EXECUTION
                and not API_DOWN
                and not KILL_SWITCH
            ):
                targets = []
                if OPENSTRIKE_TARGET_STRIKE in ("highest_volume", "vol_oi") and STRADDLE_VOLUME_TARGET:
                    targets.append({"contract": STRADDLE_VOLUME_TARGET, "type": "vol"})
                if OPENSTRIKE_TARGET_STRIKE in ("highest_oi", "vol_oi") and STRADDLE_OI_TARGET:
                    if not any(t["contract"]["symbol"] == STRADDLE_OI_TARGET["symbol"] for t in targets):
                        targets.append({"contract": STRADDLE_OI_TARGET, "type": "oi"})

                if targets:
                    _target_symbols = {t["contract"]["symbol"] for t in targets}

                    _non_target_cleaned = False
                    for _pos in list(positions):
                        _p_sym = _pos.get("product_symbol", "")
                        _p_size = float(_pos.get("size", 0))
                        if not _p_sym or _p_size == 0:
                            continue

                        is_option_leg = _p_sym.startswith(("C-", "P-"))
                        is_wrong_mv = _p_sym.startswith("MV-") and _p_sym not in _target_symbols

                        # Skip expired contracts — already settled by the exchange
                        if (is_option_leg or is_wrong_mv) and _is_symbol_expired(_p_sym):
                            continue

                        if is_option_leg or is_wrong_mv:
                            square_off_position(_p_sym, _p_size, reason="STRADDLE_CLEANUP")
                            send_telegram(
                                f"🔄 STRADDLE: Non-target position closed\n"
                                f"Symbol: {_p_sym} (size {_p_size})\n"
                                f"Targets: {', '.join(sorted(_target_symbols))}\n"
                                f"Time: {datetime.now().strftime('%H:%M:%S')}"
                            )
                            _non_target_cleaned = True
                            time.sleep(0.4)

                    if _non_target_cleaned:
                        SKIP_REST = True
                        continue

                    for t in targets:
                        _target_sym = t["contract"]["symbol"]
                        _target_type = t["type"]

                        cur_straddle_pos = next((p for p in positions if p.get("product_symbol", "") == _target_sym), None)

                        if not cur_straddle_pos:
                            res = place_order(_target_sym, "sell", 1, MARGIN_MODE.lower(), reason=f"STRADDLE_NEW_{_target_type.upper()}")
                            if res:
                                send_telegram(
                                    f"📊 STRADDLE POSITION ADDED ({_target_type.upper()})\n"
                                    f"Symbol: {_target_sym}\n"
                                    f"Time: {datetime.now().strftime('%H:%M:%S')}"
                                )
                            time.sleep(0.3)

            if (
                STRATEGY_MODE == "OPENSTRIKE"
                and ORDER_TYPE != "futures"
                and not SKIP_REST
                and USER_AUTO_EXECUTION
                and not API_DOWN
                and not KILL_SWITCH
                and OPENSTRIKE_CALL_OPT is not None
                and OPENSTRIKE_PUT_OPT is not None
            ):
                _os_size = MIN_POSITION_CONTRACTS
                if bal > 0:
                    mult = 0.001 if SYMBOL == "BTC" else 0.01
                    mult_factor = 0.000011 if SYMBOL == "BTC" else 0.00011

                    cur_call_sz = abs(int(float(short_call_pos.get("size", 0)))) if short_call_pos else 0
                    cur_put_sz  = abs(int(float(short_put_pos.get("size", 0)))) if short_put_pos else 0
                    current_size = max(cur_call_sz, cur_put_sz)
                    actual_margin_per_contract = (blocked / current_size) if (current_size > 0 and blocked > 0) else None

                    if custom_strategy_active:
                        sell_opt = custom_put_sell if custom_put_sell else custom_call_sell
                        if sell_opt:
                            premium_sell = float(sell_opt.get("mark_price") or 0) or max(0.01, float(sell_opt.get("strike_price") or sell_opt.get("strike") or 1) * 0.005)
                            strike_sell = float(sell_opt.get("strike_price") or sell_opt.get("strike") or 0)

                            if POSITION_SIZING_MODE == "target_profit":
                                p_sell_c = float(custom_call_sell.get("mark_price") or 0) if custom_call_sell else 0.0
                                p_sell_p = float(custom_put_sell.get("mark_price") or 0) if custom_put_sell else 0.0
                                p_buy_c  = float(custom_call_buy.get("mark_price") or 0) if custom_call_buy else 0.0
                                p_buy_p  = float(custom_put_buy.get("mark_price") or 0) if custom_put_buy else 0.0

                                net_prem = (p_sell_c + p_sell_p) - (p_buy_c + p_buy_p)
                                if net_prem <= 0:
                                    net_prem = max(0.01, premium_sell * 0.8)
                                net_prem_per_unit = net_prem * mult

                                desired_profit = bal * TARGET_PROFIT_PCT
                                size_for_profit = int(math.ceil(desired_profit / net_prem_per_unit)) if net_prem_per_unit > 0 else MIN_POSITION_CONTRACTS

                                s_call_b = float(custom_call_buy.get("strike_price") or custom_call_buy.get("strike") or strike_sell) if custom_call_buy else strike_sell
                                s_put_b  = float(custom_put_buy.get("strike_price") or custom_put_buy.get("strike") or strike_sell) if custom_put_buy else strike_sell
                                spread_w = max(abs(strike_sell - s_call_b), abs(strike_sell - s_put_b))
                                spread_margin = spread_w * mult * 0.6

                                if actual_margin_per_contract and actual_margin_per_contract > 0:
                                    est_margin = actual_margin_per_contract
                                else:
                                    est_margin = max(0.20, spread_margin, strike_sell * mult_factor)

                                size_50_margin = int(round((bal * 0.50) / est_margin)) if est_margin > 0 else MIN_POSITION_CONTRACTS

                                _os_size = max(MIN_POSITION_CONTRACTS, min(size_for_profit, max(MIN_POSITION_CONTRACTS, size_50_margin)))
                            elif POSITION_SIZING_MODE == "margin":
                                if actual_margin_per_contract and actual_margin_per_contract > 0:
                                    _os_size = max(MIN_POSITION_CONTRACTS, int((bal * MIN_MARGIN_PCT) / actual_margin_per_contract))
                                else:
                                    _os_size = max(MIN_POSITION_CONTRACTS, calc_position_size(bal, MIN_MARGIN_PCT, premium_sell))
                            else:
                                _os_size = max(MIN_POSITION_CONTRACTS, calc_position_size_by_max_loss(bal, "SELL CALL", custom_call_sell, custom_call_buy, custom_put_sell, MAX_LOSS_CAP_PCT))
                    else:
                        _os_call_e = _os_call_resolved
                        _os_put_e  = _os_put_resolved
                        if _os_call_e and _os_put_e:
                            premium_c = float(_os_call_e.get("mark_price") or 0) or max(0.01, float(_os_call_e.get("strike_price") or _os_call_e.get("strike") or 1) * 0.005)
                            premium_p = float(_os_put_e.get("mark_price") or 0) or max(0.01, float(_os_put_e.get("strike_price") or _os_put_e.get("strike") or 1) * 0.005)
                            avg_prem  = max(0.01, (premium_c + premium_p) / 2)
                            strike_c = float(_os_call_e.get("strike_price") or _os_call_e.get("strike") or 0)
                            strike_p = float(_os_put_e.get("strike_price") or _os_put_e.get("strike") or 0)

                            if POSITION_SIZING_MODE == "margin":
                                if actual_margin_per_contract is not None and actual_margin_per_contract > 0:
                                    _os_size = max(MIN_POSITION_CONTRACTS, int((bal * MIN_MARGIN_PCT) / actual_margin_per_contract))
                                else:
                                    _os_size = max(MIN_POSITION_CONTRACTS, calc_position_size(bal, MIN_MARGIN_PCT, avg_prem))
                            elif POSITION_SIZING_MODE == "target_profit":
                                net_premium_per_unit = (premium_c + premium_p) * mult
                                if net_premium_per_unit > 0:
                                    desired_profit_usd_min = bal * TARGET_PROFIT_PCT
                                    size_for_profit = int(math.ceil(desired_profit_usd_min / net_premium_per_unit))
                                    if actual_margin_per_contract and actual_margin_per_contract > 0:
                                        size_50_margin = int((bal * 0.50) / actual_margin_per_contract)
                                    else:
                                        est_margin = max(1.0, (strike_c + strike_p) * mult_factor)
                                        size_50_margin = int((bal * 0.50) / est_margin)
                                    _os_size = max(MIN_POSITION_CONTRACTS, min(size_for_profit, max(MIN_POSITION_CONTRACTS, size_50_margin)))
                                else:
                                    _os_size = MIN_POSITION_CONTRACTS
                            else:
                                _os_size = max(MIN_POSITION_CONTRACTS, calc_position_size_by_max_loss(bal, "SELL CALL", _os_call_e, None, _os_put_e, MAX_LOSS_CAP_PCT))

                _os_call_strike = float(_os_call_resolved.get("strike", 0) or 0) if _os_call_resolved else 0
                _os_put_strike  = float(_os_put_resolved.get("strike", 0) or 0) if _os_put_resolved else 0

                _oi_call_strike = float(OPENSTRIKE_CALL_OPT.get("strike", 0) or 0)
                _oi_put_strike  = float(OPENSTRIKE_PUT_OPT.get("strike", 0) or 0)
                if _os_call_strike != _oi_call_strike:
                    _is_kept_old = short_call_pos and _os_call_strike == _strike_from_position(short_call_pos)
                    if not _is_kept_old:
                        execution_status = f"OPENSTRIKE: Call strike {_oi_call_strike} not in near expiry → using {_os_call_strike}"
                if _os_put_strike != _oi_put_strike:
                    _is_kept_old = short_put_pos and _os_put_strike == _strike_from_position(short_put_pos)
                    if not _is_kept_old:
                        execution_status = f"OPENSTRIKE: Put strike {_oi_put_strike} not in near expiry → using {_os_put_strike}"

                _os_target_symbols = set()
                sell_opt = None
                buy_call_opt = None
                buy_put_opt = None
                if custom_strategy_active:
                    sell_opt = custom_put_sell if custom_put_sell else custom_call_sell
                    buy_call_opt = custom_call_buy
                    buy_put_opt = custom_put_buy
                    for opt in [custom_call_sell, custom_put_sell, custom_call_buy, custom_put_buy]:
                        if opt:
                            _os_target_symbols.add(opt["symbol"])
                else:
                    if _os_call_resolved:
                        _os_target_symbols.add(_os_call_resolved["symbol"])
                    if _os_put_resolved:
                        _os_target_symbols.add(_os_put_resolved["symbol"])

                _non_target_cleaned = False
                for _pos in list(positions):
                    _p_sym = _pos.get("product_symbol", "")
                    _p_size = float(_pos.get("size", 0))
                    if not _p_sym or _p_size == 0:
                        continue

                    if not _p_sym.startswith(("C-", "P-", "MV-")):
                        continue

                    # Skip expired contracts — already settled by the exchange
                    if _is_symbol_expired(_p_sym):
                        continue

                    _wrong_direction = False
                    if _p_sym in _os_target_symbols:
                        if custom_strategy_active:
                            if sell_opt and _p_sym == sell_opt["symbol"] and _p_size > 0:
                                _wrong_direction = True
                            elif buy_call_opt and _p_sym == buy_call_opt["symbol"] and _p_size < 0:
                                _wrong_direction = True
                            elif buy_put_opt and _p_sym == buy_put_opt["symbol"] and _p_size < 0:
                                _wrong_direction = True
                        else:
                            if _os_call_resolved and _p_sym == _os_call_resolved["symbol"] and _p_size > 0:
                                _wrong_direction = True
                            elif _os_put_resolved and _p_sym == _os_put_resolved["symbol"] and _p_size > 0:
                                _wrong_direction = True

                    if _p_sym not in _os_target_symbols or _wrong_direction:
                        _reason = "OPENSTRIKE_WRONG_DIRECTION" if _wrong_direction else "OPENSTRIKE_CLEANUP"
                        square_off_position(_p_sym, _p_size, reason=_reason)
                        send_telegram(
                            f"🔄 OPENSTRIKE: {'Wrong direction' if _wrong_direction else 'Non-target'} position closed\n"
                            f"Symbol: {_p_sym} (size {_p_size})\n"
                            f"Target: {', '.join(sorted(_os_target_symbols)) if _os_target_symbols else 'None'}\n"
                            f"Time: {datetime.now().strftime('%H:%M:%S')}"
                        )
                        _non_target_cleaned = True
                        time.sleep(0.4)

                if _non_target_cleaned:
                    SKIP_REST = True
                    continue

                _roll_done = False

                if _os_call_resolved and not custom_strategy_active:
                    if short_call_pos:
                        _cur_call_sym = short_call_pos.get("product_symbol", "")
                        if _cur_call_sym != _os_call_resolved["symbol"]:
                            _sz = min(abs(int(float(short_call_pos.get("size", 0)))), _os_size)

                            square_off_position(_cur_call_sym, float(short_call_pos.get("size", 0)), reason="OPENSTRIKE_ROLL_CALL")
                            time.sleep(0.5)

                            res = place_order(_os_call_resolved["symbol"], "sell", max(_sz, 1), MARGIN_MODE.lower(), reason="OPENSTRIKE_ROLL_CALL")
                            if res:
                                _clear_openstrike_missing_leg_pending("call")
                                _roll_done = True
                                _note = "" if _os_call_strike == _oi_call_strike else f" (OI strike {_oi_call_strike} not in near expiry → nearest {_os_call_strike})"
                                send_telegram(
                                    f"🔄 OPENSTRIKE CALL ROLL\n"
                                    f"Old: {_cur_call_sym} → New: {_os_call_resolved['symbol']}{_note}\n"
                                    f"OI (reference): {_fmt_oi(OPENSTRIKE_CALL_OPT.get('oi', 0))}\n"
                                    f"Time: {datetime.now().strftime('%H:%M:%S')}"
                                )
                            else:
                                if not _is_silent_guard_error():
                                    execution_status = f"OPENSTRIKE: Call roll pending ({_os_call_resolved['symbol']}) — managing remaining leg"
                                    _note_openstrike_missing_leg_pending("call", _os_call_resolved, LAST_ORDER_ERROR or "roll order failed / margin used")
                            time.sleep(0.3)

                    else:
                        _sz_ref = min(abs(int(float(short_put_pos.get("size", 0)))), _os_size) if short_put_pos else _os_size
                        if _openstrike_pending_same_target("call", _os_call_resolved["symbol"]):
                            execution_status = _pending_retry_status("call", _os_call_resolved["symbol"])
                        else:
                            res = place_order(_os_call_resolved["symbol"], "sell", max(_sz_ref, 1), MARGIN_MODE.lower(), reason="OPENSTRIKE_ROLL_CALL")
                            if res:
                                _clear_openstrike_missing_leg_pending("call")
                                _roll_done = True
                                _note = "" if _os_call_strike == _oi_call_strike else f" (nearest to OI strike {_oi_call_strike})"
                                send_telegram(
                                    f"📊 OPENSTRIKE CALL LEG ADDED\n"
                                    f"Strike: {_os_call_strike}{_note} | OI (ref): {_fmt_oi(OPENSTRIKE_CALL_OPT.get('oi', 0))}\n"
                                    f"Time: {datetime.now().strftime('%H:%M:%S')}"
                                )
                            else:
                                if not _is_silent_guard_error():
                                    execution_status = f"OPENSTRIKE: Call leg pending ({_os_call_resolved['symbol']}) — managing single leg"
                                    _note_openstrike_missing_leg_pending("call", _os_call_resolved, LAST_ORDER_ERROR or "order failed / margin used")
                        time.sleep(0.3)

                if _os_put_resolved and not custom_strategy_active:
                    if short_put_pos:
                        _cur_put_sym = short_put_pos.get("product_symbol", "")
                        if _cur_put_sym != _os_put_resolved["symbol"]:
                            _sz = min(abs(int(float(short_put_pos.get("size", 0)))), _os_size)

                            square_off_position(short_put_pos["product_symbol"], float(short_put_pos.get("size", 0)), reason="OPENSTRIKE_ROLL_PUT")
                            time.sleep(0.5)

                            res = place_order(_os_put_resolved["symbol"], "sell", max(_sz, 1), MARGIN_MODE.lower(), reason="OPENSTRIKE_ROLL_PUT")
                            if res:
                                _clear_openstrike_missing_leg_pending("put")
                                _roll_done = True
                                _note = "" if _os_put_strike == _oi_put_strike else f" (OI strike {_oi_put_strike} not in near expiry → nearest {_os_put_strike})"
                                send_telegram(
                                    f"🔄 OPENSTRIKE PUT ROLL\n"
                                    f"Old: {_cur_put_sym} → New: {_os_put_resolved['symbol']}{_note}\n"
                                    f"OI (reference): {_fmt_oi(OPENSTRIKE_PUT_OPT.get('oi', 0))}\n"
                                    f"Time: {datetime.now().strftime('%H:%M:%S')}"
                                )
                            else:
                                if not _is_silent_guard_error():
                                    execution_status = f"OPENSTRIKE: Put roll pending ({_os_put_resolved['symbol']}) — managing remaining leg"
                                    _note_openstrike_missing_leg_pending("put", _os_put_resolved, LAST_ORDER_ERROR or "roll order failed / margin used")
                            time.sleep(0.3)

                    else:
                        _sz_ref = min(abs(int(float(short_call_pos.get("size", 0)))), _os_size) if short_call_pos else _os_size
                        if _openstrike_pending_same_target("put", _os_put_resolved["symbol"]):
                            execution_status = _pending_retry_status("put", _os_put_resolved["symbol"])
                        else:
                            res = place_order(_os_put_resolved["symbol"], "sell", max(_sz_ref, 1), MARGIN_MODE.lower(), reason="OPENSTRIKE_ROLL_PUT")
                            if res:
                                _clear_openstrike_missing_leg_pending("put")
                                _roll_done = True
                                _note = "" if _os_put_strike == _oi_put_strike else f" (nearest to OI strike {_oi_put_strike})"
                                send_telegram(
                                    f"📊 OPENSTRIKE PUT LEG ADDED\n"
                                    f"Strike: {_os_put_strike}{_note} | OI (ref): {_fmt_oi(OPENSTRIKE_PUT_OPT.get('oi', 0))}\n"
                                    f"Time: {datetime.now().strftime('%H:%M:%S')}"
                                )
                            else:
                                if not _is_silent_guard_error():
                                    execution_status = f"OPENSTRIKE: Put leg pending ({_os_put_resolved['symbol']}) — managing single leg"
                                    _note_openstrike_missing_leg_pending("put", _os_put_resolved, LAST_ORDER_ERROR or "order failed / margin used")
                        time.sleep(0.3)

                if _roll_done:
                    LAST_EXECUTED_SIGNAL = decision
                    EQUALITY_EVENT = True
                    EQUALITY_TRIGGER_REASON = "OPENSTRIKE_ROLL"
                    SKIP_REST = True
                    continue

            auto_roll = (
                LAST_EXECUTED_SIGNAL is not None
                and decision == LAST_EXECUTED_SIGNAL
                and near
                and nxt
            )
            if (
                LAST_EXECUTED_SIGNAL is not None
                and decision == LAST_EXECUTED_SIGNAL
                and decision != "NO TRADE"
                and near
            ):
                near_expiry_date = near[0]["expiry"]

                if auto_roll:
                    LAST_EXECUTED_SIGNAL = decision
                    expiry_reset = True
                    EQUALITY_EVENT = True
                    EQUALITY_TRIGGER_REASON = "EXPIRY_ROLL"
                    auto_roll = True
                    expiry_reset = True

            if bias_changed or not has_active_position:
                roll_opts = near if near else (nxt if nxt else [])
            elif dominant_expiry_this_cycle is not None:
                roll_opts = [o for o in all_opts if o["expiry"] == dominant_expiry_this_cycle]
                if not roll_opts:
                    roll_opts = nxt if auto_roll and nxt else (near if near else (nxt if nxt else []))
            else:
                roll_opts = near if near else (nxt if nxt else [])

            _is_openstrike_opts_mode = (STRATEGY_MODE == "OPENSTRIKE" and ORDER_TYPE != "futures")
            _openstrike_missing_short_leg = (
                _is_openstrike_opts_mode
                and ((has_short_call and not has_short_put) or (has_short_put and not has_short_call))
            )

            if not (USER_AUTO_EXECUTION and SYSTEM_EXECUTION_ALLOWED):
                execution_status = "PAUSED (AUTO EXEC OFF)"
                SKIP_REST = True

            _incomplete_2leg = (decision in ("SELL CALL", "SELL PUT") and
                ((1 if short_call_pos else 0) + (1 if long_call_pos else 0) + (1 if short_put_pos else 0) + (1 if long_put_pos else 0)) == 2)
            used_pct_now = (blocked / bal * 100) if bal > 0 else 0

            _sc_qty = abs(int(float(short_call_pos.get("size", 0)))) if short_call_pos else 0
            _sp_qty = abs(int(float(short_put_pos.get("size", 0)))) if short_put_pos else 0
            _is_min_1_1_position = (_is_openstrike_opts_mode and _sc_qty <= 1 and _sp_qty <= 1)

            if POSITION_SIZING_MODE == "target_profit":
                max_used_margin_pct = 0.60  # Hard cap: reduce at 60%; normal 40%, extended 50%, balancing up to 60%
            else:
                max_used_margin_pct = min(0.99, max(0.01, MIN_MARGIN_PCT * MAX_USED_MARGIN_MULTIPLIER))

            _fut_hard_cap_bypass = ORDER_TYPE == "futures" and bias_changed and decision in ("SELL CALL", "SELL PUT")
            if used_pct_now >= (max_used_margin_pct * 100) and not _fut_hard_cap_bypass and not _openstrike_missing_short_leg and not _is_min_1_1_position:
                execution_status = f"PAUSED: Used margin {used_pct_now:.1f}% >= {max_used_margin_pct*100:.0f}%" + (" (safety cap)" if POSITION_SIZING_MODE == "target_profit" else f" (safety cap = min×{MAX_USED_MARGIN_MULTIPLIER:.1f})")
                
                # Proportional position reduction logic (with 60-sec cool-down)
                if USER_AUTO_EXECUTION and not API_DOWN and (time.time() - LAST_MARGIN_REDUCTION_TIME >= 60.0):
                    # Target 50% margin (2% safety buffer below the 52% limit) to guarantee dropping below limit
                    target_pct = (max_used_margin_pct * 100) - 2.0
                    reduction_ratio = (used_pct_now - target_pct) / used_pct_now
                    
                    reduced_legs = []
                    if custom_strategy_active:
                        _c_sell = custom_put_sell if custom_put_sell else custom_call_sell
                        _c_call_b = custom_call_buy
                        _c_put_b = custom_put_buy
                        
                        total_sets_reduced = 0
                        while True:
                            # Re-check live wallet balance and margin
                            _b_chk, _blk_chk, _ = wallet_usd()
                            _u_pct_chk = (_blk_chk / _b_chk * 100) if (_b_chk and _b_chk > 0) else 0.0
                            
                            # Stop condition: Margin dropped below 60%
                            if _u_pct_chk < (max_used_margin_pct * 100):
                                break
                                
                            # Check remaining short leg size
                            _cur_pos_all = get_positions()
                            _cur_sz_c = 0
                            if _c_sell:
                                for p in _cur_pos_all:
                                    if p.get("product_symbol") == _c_sell["symbol"] and float(p.get("size", 0)) < 0:
                                        _cur_sz_c = abs(int(float(p.get("size", 0))))
                                        break
                                        
                            if _cur_sz_c <= 1:
                                break
                                
                            # Step-by-step reduction: 1 set (Sell leg + Buy Call + Buy Put)
                            if _c_sell:
                                place_order(_c_sell["symbol"], "buy", 1, MARGIN_MODE.lower(), reason="MARGIN_REDUCE_STEP_SELL")
                                time.sleep(0.3)
                            if _c_call_b:
                                place_order(_c_call_b["symbol"], "sell", 1, MARGIN_MODE.lower(), reason="MARGIN_REDUCE_STEP_CALL")
                                time.sleep(0.3)
                            if _c_put_b:
                                place_order(_c_put_b["symbol"], "sell", 1, MARGIN_MODE.lower(), reason="MARGIN_REDUCE_STEP_PUT")
                                time.sleep(0.3)
                                
                            total_sets_reduced += 1

                        if total_sets_reduced > 0:
                            _b_final, _blk_final, _ = wallet_usd()
                            _u_final = (_blk_final / _b_final * 100) if (_b_final and _b_final > 0) else 0.0
                            reduced_legs.append(f"Reduced {total_sets_reduced} sets (Sell + Buy Call + Buy Put) 1-by-1. Final Margin: {_u_final:.1f}%")
                    else:
                        for pos_leg in [short_call_pos, short_put_pos]:
                            if pos_leg:
                                curr_qty = abs(int(float(pos_leg.get("size", 0))))
                                if curr_qty > 0:
                                    qty_to_reduce = min(curr_qty, max(1, int(round(curr_qty * reduction_ratio))))
                                    if qty_to_reduce > 0:
                                        place_order(pos_leg["product_symbol"], "buy", qty_to_reduce, MARGIN_MODE.lower(), reason="MARGIN_REDUCTION")
                                        reduced_legs.append(f"{pos_leg['product_symbol']} x{qty_to_reduce} contracts")
                                        time.sleep(0.5)
                    
                    if reduced_legs:
                        LAST_MARGIN_REDUCTION_TIME = time.time()
                        msg = (
                            f"🚨 *MARGIN LIMIT BREACHED*\n\n"
                            f"Current Margin: {used_pct_now:.2f}% >= {max_used_margin_pct*100:.0f}%\n"
                            f"Proportionally scaling down positions to target {target_pct:.1f}% margin (2% safety buffer).\n\n"
                            f"Orders placed to buy back:\n" + "\n".join([f"🔹 {leg}" for leg in reduced_legs]) + "\n\n"
                            f"Time: {datetime.now().strftime('%H:%M:%S')}"
                        )
                        send_telegram(msg)
                
                SKIP_REST = True
            if POSITION_SIZING_MODE == "target_profit":
                margin_ceiling = 60.0  # Normal 40%, extended 50%, leg balancing up to 60%
                ceiling_hard = 61.0
            else:
                margin_ceiling = (effective_min_margin * 100) * 1.01
                ceiling_hard = margin_ceiling + 1

            _both_longs_10d = bool(long_call_pos and long_put_pos and has_long_10d_call and has_long_10d_put)
            _futures_bias_change = (ORDER_TYPE == "futures" and bias_changed)
            _allow_for_bias_change = bias_changed and (used_pct_now < ceiling_hard or _both_longs_10d or _futures_bias_change)
            if not _incomplete_2leg and not _allow_for_bias_change and not _openstrike_missing_short_leg and not _is_min_1_1_position and used_pct_now >= ceiling_hard and (decision != LAST_EXECUTED_SIGNAL or auto_roll or not has_active_position):
                execution_status = f"PAUSED: Margin {used_pct_now:.1f}% >= {ceiling_hard:.1f}%"
                SKIP_REST = True

            if _is_openstrike_opts_mode and not SKIP_REST and USER_AUTO_EXECUTION and not API_DOWN:
                if custom_strategy_active:
                    sell_opt = custom_put_sell if custom_put_sell else custom_call_sell
                    buy_call_opt = custom_call_buy
                    buy_put_opt = custom_put_buy

                    has_required_opts = False
                    if CUSTOM_HEDGES_COUNT == 1:
                        if custom_put_sell and buy_call_opt:
                            has_required_opts = True
                        elif custom_call_sell and buy_put_opt:
                            has_required_opts = True
                    else:
                        if sell_opt and buy_call_opt and buy_put_opt:
                            has_required_opts = True

                    if has_required_opts:
                        bal, blocked, _ = wallet_usd()
                        if bal > 0:
                            # _os_size is already calculated early

                            cur_sell_sz = 0
                            for p in positions:
                                if p.get("product_symbol") == sell_opt["symbol"] and float(p.get("size", 0)) < 0:
                                    cur_sell_sz = abs(int(float(p.get("size", 0))))
                                    break

                            cur_buy_call_sz = 0
                            if buy_call_opt:
                                for p in positions:
                                    if p.get("product_symbol") == buy_call_opt["symbol"] and float(p.get("size", 0)) > 0:
                                        cur_buy_call_sz = abs(int(float(p.get("size", 0))))
                                        break

                            cur_buy_put_sz = 0
                            if buy_put_opt:
                                for p in positions:
                                    if p.get("product_symbol") == buy_put_opt["symbol"] and float(p.get("size", 0)) > 0:
                                        cur_buy_put_sz = abs(int(float(p.get("size", 0))))
                                        break

                            # If position is already active, lock position size to hold stable until signal change (sell+sell) or emergency 60% margin breach
                            if cur_sell_sz > 0 or cur_buy_call_sz > 0 or cur_buy_put_sz > 0:
                                # Emergency reduction check if margin breaches 60% hard cap: 
                                # Step 1: Execute 1 test block (1-1-1) to measure margin drop per block on live exchange.
                                # Step 2: Re-check margin. If < 60%, stop immediately. If still >= 60%, calculate exact remaining blocks needed and execute in 1 single batch order.
                                if used_pct_now >= 60.0:
                                    _initial_margin_pct = used_pct_now
                                    _max_sz_before = max(cur_sell_sz, cur_buy_call_sz, cur_buy_put_sz)

                                    if _max_sz_before > 1:
                                        _blocks_squared_off = 0

                                        # Step 1: Execute 1 test block (1 contract per leg)
                                        if sell_opt and cur_sell_sz > 0:
                                            place_order(sell_opt["symbol"], "buy", 1, MARGIN_MODE.lower(), reason="CUSTOM_SCALE_DOWN_SELL")
                                            time.sleep(0.3)
                                        if buy_call_opt and cur_buy_call_sz > 0:
                                            place_order(buy_call_opt["symbol"], "sell", 1, MARGIN_MODE.lower(), reason="CUSTOM_SCALE_DOWN_CALL")
                                            time.sleep(0.3)
                                        if buy_put_opt and cur_buy_put_sz > 0:
                                            place_order(buy_put_opt["symbol"], "sell", 1, MARGIN_MODE.lower(), reason="CUSTOM_SCALE_DOWN_PUT")
                                            time.sleep(0.5)

                                        _blocks_squared_off += 1

                                        # Re-check live wallet balance and margin after 1 test block
                                        _b_chk, _blk_chk, _ = wallet_usd()
                                        _u_pct_chk = (_blk_chk / _b_chk * 100) if (_b_chk and _b_chk > 0) else 0.0

                                        # Step 2: If margin is STILL >= 60.0%, calculate exact additional blocks needed to bring margin under 60%
                                        if _u_pct_chk >= 60.0:
                                            margin_drop_per_block = _initial_margin_pct - _u_pct_chk
                                            if margin_drop_per_block > 0:
                                                margin_excess = _u_pct_chk - 59.0
                                                add_blocks_needed = math.ceil(margin_excess / margin_drop_per_block)
                                                max_add_blocks = _max_sz_before - 1 - 1
                                                blocks_to_exec = max(0, min(int(add_blocks_needed), max_add_blocks))

                                                if blocks_to_exec > 0:
                                                    if sell_opt and cur_sell_sz > 1:
                                                        place_order(sell_opt["symbol"], "buy", blocks_to_exec, MARGIN_MODE.lower(), reason="CUSTOM_SCALE_DOWN_SELL")
                                                        time.sleep(0.3)
                                                    if buy_call_opt and cur_buy_call_sz > 1:
                                                        place_order(buy_call_opt["symbol"], "sell", blocks_to_exec, MARGIN_MODE.lower(), reason="CUSTOM_SCALE_DOWN_CALL")
                                                        time.sleep(0.3)
                                                    if buy_put_opt and cur_buy_put_sz > 1:
                                                        place_order(buy_put_opt["symbol"], "sell", blocks_to_exec, MARGIN_MODE.lower(), reason="CUSTOM_SCALE_DOWN_PUT")
                                                        time.sleep(0.5)

                                                    _blocks_squared_off += blocks_to_exec

                                        if _blocks_squared_off > 0:
                                            _b_final, _blk_final, _ = wallet_usd()
                                            _u_final = (_blk_final / _b_final * 100) if (_b_final and _b_final > 0) else 0.0
                                            send_telegram(
                                                f"📉 OPENSTRIKE CUSTOM: Smart Emergency Scale-Down\n"
                                                f"Initial Margin: {_initial_margin_pct:.1f}% ➔ Final Margin: {_u_final:.1f}%\n"
                                                f"Total Squared off: {_blocks_squared_off} block(s) (1 test block + calculated batch)\n"
                                                f"Time: {datetime.now().strftime('%H:%M:%S')}"
                                            )
                                            SKIP_REST = True
                                            continue

                                # Normal active position holding state: LOCKED (renders live UI dashboard)
                                execution_status = f"OPENSTRIKE Custom: Position active ({max(cur_sell_sz, cur_buy_call_sz, cur_buy_put_sz)} contracts) — holding stable until sell+sell transition"
                                SKIP_REST = True

                            # Initial entry placement when 0 positions are open
                            _need_sell = (cur_sell_sz == 0)
                            _qty_sell = _os_size if _need_sell else 0

                            _need_buy_call = bool(buy_call_opt and cur_buy_call_sz == 0)
                            _qty_buy_call = _os_size if _need_buy_call else 0

                            _need_buy_put = bool(buy_put_opt and cur_buy_put_sz == 0)
                            _qty_buy_put = _os_size if _need_buy_put else 0

                            if _need_sell or _need_buy_call or _need_buy_put:
                                _executed_any = False
                                _is_put_atm = sell_opt["symbol"].startswith("P-") if sell_opt else False

                                # 1 Single Step Execution: Place Buy Hedges first for instant margin benefit, then Short ATM leg in 1 go
                                if buy_call_opt and _need_buy_call:
                                    if _is_put_atm or CUSTOM_HEDGES_COUNT == 2:
                                        _r = place_order(buy_call_opt["symbol"], "buy", _qty_buy_call, MARGIN_MODE.lower(), reason="CUSTOM_50_PCT_BUY_CALL")
                                        if _r:
                                            _executed_any = True

                                if buy_put_opt and _need_buy_put:
                                    if not _is_put_atm or CUSTOM_HEDGES_COUNT == 2:
                                        _r = place_order(buy_put_opt["symbol"], "buy", _qty_buy_put, MARGIN_MODE.lower(), reason="CUSTOM_50_PCT_BUY_PUT")
                                        if _r:
                                            _executed_any = True

                                if _need_sell:
                                    _r = place_order(sell_opt["symbol"], "sell", _qty_sell, MARGIN_MODE.lower(), reason="CUSTOM_50_PCT_SELL")
                                    if _r:
                                        _executed_any = True

                                if _executed_any:
                                    sell_delta_lbl = _fmt_opt_delta(sell_opt, "ATM")
                                    call_delta_lbl = _fmt_opt_delta(buy_call_opt, "10D")
                                    put_delta_lbl = _fmt_opt_delta(buy_put_opt, "10D")

                                    msg = "📊 OPENSTRIKE CUSTOM STRATEGY ADJUSTED/OPENED\n"
                                    msg += f"Sell ({sell_delta_lbl}): {sell_opt['symbol']} — Qty: {_qty_sell if _need_sell else 0} (Total: {cur_sell_sz + (_qty_sell if _need_sell else 0)})\n"
                                    if buy_call_opt:
                                        msg += f"Buy Call ({call_delta_lbl}): {buy_call_opt['symbol']} — Qty: {_qty_buy_call if _need_buy_call else 0} (Total: {cur_buy_call_sz + (_qty_buy_call if _need_buy_call else 0)})\n"
                                    if buy_put_opt:
                                        msg += f"Buy Put ({put_delta_lbl}): {buy_put_opt['symbol']} — Qty: {_qty_buy_put if _need_buy_put else 0} (Total: {cur_buy_put_sz + (_qty_buy_put if _need_buy_put else 0)})\n"
                                    msg += f"Balance: ${bal:.2f}\n"
                                    msg += f"Time: {datetime.now().strftime('%H:%M:%S')}"
                                    msg += _build_analytics_telegram_summary(spot)
                                    send_telegram(msg)
                                    SKIP_REST = True
                                    continue
                            else:
                                execution_status = "OPENSTRIKE Custom: All legs at target size — monitoring"
                                SKIP_REST = True
                    else:
                        execution_status = "OPENSTRIKE Custom: Options missing — waiting"
                        SKIP_REST = True
                elif OPENSTRIKE_CALL_OPT and OPENSTRIKE_PUT_OPT:
                    _os_call_e = _os_call_resolved
                    _os_put_e  = _os_put_resolved
                    if _os_call_e and _os_put_e:
                        bal, blocked, _ = wallet_usd()
                        if bal > 0:
                            # _os_size is already calculated early

                            cur_call_sz = abs(int(float(short_call_pos.get("size", 0)))) if short_call_pos else 0
                            cur_put_sz  = abs(int(float(short_put_pos.get("size", 0)))) if short_put_pos else 0

                            _need_call = False
                            _need_put  = False
                            _call_qty = 0
                            _put_qty  = 0

                            if not has_short_call:
                                _need_call = True
                                _call_qty = 1
                            elif cur_call_sz < _os_size:
                                _need_call = True
                                _call_qty = _os_size - cur_call_sz

                            if not has_short_put:
                                _need_put = True
                                _put_qty = 1
                            elif cur_put_sz < _os_size:
                                _need_put = True
                                _put_qty = _os_size - cur_put_sz

                            if _need_call or _need_put:
                                _os_any = False
                                if _need_call:
                                    _call_missing = not has_short_call
                                    if _call_missing and _openstrike_pending_same_target("call", _os_call_e["symbol"]):
                                        execution_status = _pending_retry_status("call", _os_call_e["symbol"])
                                    else:
                                        _r = place_order(_os_call_e["symbol"], "sell", _call_qty, MARGIN_MODE.lower(), reason="NEW_POSITION_TOPUP" if cur_call_sz > 0 else "NEW_POSITION")
                                        if _r:
                                            _clear_openstrike_missing_leg_pending("call")
                                            _os_any = True
                                            LAST_EXECUTED_SIGNAL = decision
                                            time.sleep(0.5)
                                        elif _call_missing:
                                            if not _is_silent_guard_error():
                                                execution_status = f"OPENSTRIKE: Call leg pending ({_os_call_e['symbol']}) — managing single leg"
                                                _note_openstrike_missing_leg_pending("call", _os_call_e, LAST_ORDER_ERROR or "order failed / margin used")
                                if _need_put:
                                    _put_missing = not has_short_put
                                    if _put_missing and _openstrike_pending_same_target("put", _os_put_e["symbol"]):
                                        execution_status = _pending_retry_status("put", _os_put_e["symbol"])
                                    else:
                                        _r = place_order(_os_put_e["symbol"], "sell", _put_qty, MARGIN_MODE.lower(), reason="NEW_POSITION_TOPUP" if cur_put_sz > 0 else "NEW_POSITION")
                                        if _r:
                                            _clear_openstrike_missing_leg_pending("put")
                                            _os_any = True
                                        elif _put_missing:
                                            if not _is_silent_guard_error():
                                                execution_status = f"OPENSTRIKE: Put leg pending ({_os_put_e['symbol']}) — managing single leg"
                                                _note_openstrike_missing_leg_pending("put", _os_put_e, LAST_ORDER_ERROR or "order failed / margin used")
                                if _os_any:
                                    send_telegram(
                                        f"📊 OPENSTRIKE SHORT STRANGLE ADJUSTED/OPENED\n"
                                        f"Sell Call: {_os_call_e.get('strike')} ({_os_call_e['symbol']}) — Qty added: {_call_qty if _need_call else 0} (Total: {max(_os_size, cur_call_sz)})\n"
                                        f"Sell Put:  {_os_put_e.get('strike')} ({_os_put_e['symbol']}) — Qty added: {_put_qty if _need_put else 0} (Total: {max(_os_size, cur_put_sz)})\n"
                                        f"Balance: ${bal:.2f}\n"
                                        f"Time: {datetime.now().strftime('%H:%M:%S')}"
                                        f"{_build_analytics_telegram_summary(spot)}"
                                    )
                                    SKIP_REST = True
                                    continue
                            else:
                                execution_status = "OPENSTRIKE: Both legs at target size — monitoring"
                                SKIP_REST = True
                else:
                    execution_status = "OPENSTRIKE: OI data missing — waiting"
                    SKIP_REST = True

            if not _is_openstrike_opts_mode:
                if execution_decision == "NO TRADE":
                    execution_status = "NO TRADE (Strategy)"
                    SKIP_REST = True

                if execution_decision == LAST_EXECUTED_SIGNAL and not auto_roll:
                    if ENFORCE_EQUALITY_JOB and not EQUALITY_EVENT:
                        if "SELL CALL" in execution_decision and short_call_pos and long_call_pos and long_put_pos:
                            sc, lc, lp = abs(short_call_pos["size"]), abs(long_call_pos["size"]), abs(long_put_pos["size"])
                            if not (sc == lc == lp):
                                EQUALITY_EVENT = True
                                EQUALITY_TRIGGER_REASON = "IMMEDIATE_DRIFT"
                        elif "SELL PUT" in execution_decision and short_put_pos and long_call_pos and long_put_pos:
                            sp, lc, lp = abs(short_put_pos["size"]), abs(long_call_pos["size"]), abs(long_put_pos["size"])
                            if not (sp == lc == lp):
                                EQUALITY_EVENT = True
                                EQUALITY_TRIGGER_REASON = "IMMEDIATE_DRIFT"

                        elif "SELL CALL" in execution_decision and short_call_pos and long_put_pos and not long_call_pos:
                            sc, lp = abs(float(short_call_pos["size"])), abs(float(long_put_pos["size"]))
                            if sc != lp:
                                EQUALITY_EVENT = True
                                EQUALITY_TRIGGER_REASON = "IMMEDIATE_DRIFT_2LEG"
                        elif "SELL PUT" in execution_decision and short_put_pos and long_call_pos and not long_put_pos:
                            sp, lc = abs(float(short_put_pos["size"])), abs(float(long_call_pos["size"]))
                            if sp != lc:
                                EQUALITY_EVENT = True
                                EQUALITY_TRIGGER_REASON = "IMMEDIATE_DRIFT_2LEG"
                    execution_status = "BIAS SAME (MONITORING)"
                    SKIP_REST = True

                if (execution_decision != LAST_EXECUTED_SIGNAL or auto_roll or not has_active_position) and execution_decision != "NO TRADE" and not SKIP_REST:
                    bal, blocked, _ = wallet_usd()
                    if bal <= 0:
                        execution_status = "PAUSED: Balance ≤ 0"
                        SKIP_REST = True
                    elif blocked < 0:
                        execution_status = "PAUSED: Invalid margin state"
                        SKIP_REST = True

            _would_run_s4 = not _is_openstrike_opts_mode and (execution_decision != LAST_EXECUTED_SIGNAL or auto_roll or not has_active_position) and execution_decision != "NO TRADE" and not SKIP_REST
            if _would_run_s4 and not bias_changed and time.time() < ORDER_FAILURE_COOLDOWN_UNTIL:
                execution_status = "Order fail cooldown — blocking new orders (will retry on bias change)"
                SKIP_REST = True
            if _would_run_s4 and (bias_changed or time.time() >= ORDER_FAILURE_COOLDOWN_UNTIL):
                execution_status = "AUTO EXECUTING"
                any_order_done = False

                if "SELL CALL" in execution_decision:
                    if ORDER_TYPE == "futures":
                        futures_created, futures_msg = create_or_manage_futures_position(SYMBOL, execution_decision, bal, spot)
                        if futures_created:
                            any_order_done = True
                            LAST_EXECUTED_SIGNAL = decision
                            execution_status = futures_msg
                            send_telegram(
                                f"📈 SHORT FUTURES OPENED (SELL CALL equiv.)\n"
                                f"Symbol   : {SYMBOL}\n"
                                f"Status   : {futures_msg}\n"
                                f"Balance  : ${bal:.2f}\n"
                                f"Time     : {datetime.now().strftime('%H:%M:%S')}"
                            )
                        else:
                            execution_status = f"Futures creation failed: {futures_msg}"

                elif "SELL PUT" in execution_decision:
                    if ORDER_TYPE == "futures":
                        futures_created, futures_msg = create_or_manage_futures_position(SYMBOL, execution_decision, bal, spot)
                        if futures_created:
                            any_order_done = True
                            LAST_EXECUTED_SIGNAL = decision
                            execution_status = futures_msg
                            send_telegram(
                                f"📉 LONG FUTURES OPENED (SELL PUT bias)\n"
                                f"Symbol   : {SYMBOL}\n"
                                f"Status   : {futures_msg}\n"
                                f"Balance  : ${bal:.2f}\n"
                                f"Time     : {datetime.now().strftime('%H:%M:%S')}"
                            )

            positions = get_positions()
            if API_DOWN:
                _u, _hl, _hb = render_margin_heatmap(bal, blocked)
                _uc, _dr, _ds, _di, _ = calculate_margin_drift(bal, blocked, effective_min_margin)
                _as, _ast, _ab = render_api_health_bar()
                expiry_list = expiry_oi_list_primary if (expiry_oi_list_primary and len(expiry_oi_list_primary) > 0) else []
                expiry_list_sec = expiry_oi_list_secondary_oi or []
                render_terminal_ui(
                    now=datetime.now(), spot=spot, decision=decision, source=source,
                    bal=bal, blocked=blocked, upnl=upnl,
                    wallet_upnl_pct=wallet_upnl_pct, blocked_upnl_pct=blocked_upnl_pct,
                    used_pct_ui=_u, heat_level=_hl, heat_bar=_hb,
                    delta=delta, gamma=gamma,
                    position_details=position_details, position_count=position_count,
                    execution_status="API DOWN (no orders)",
                    used_pct_calc=_uc, margin_drift=_dr, drift_status=_ds, drift_icon=_di,
                    api_score=_as, api_status=_ast, api_bar=_ab,
                    expiry_oi_list=expiry_list, expiry_oi_list_secondary=expiry_list_sec,
                    spot_secondary=spot_secondary_oi, symbol_secondary=symbol_secondary_oi, symbol_primary=main_sym,
                    all_expiry_max_pain_primary=all_expiry_mp_primary, all_expiry_max_pain_secondary=all_expiry_mp_secondary,
                    projected_profit=None, max_loss=None,
                    position_delta_sum=None, position_gamma_sum=None, position_theta_sum=None,
                    position_vega_sum=None, position_rho_sum=None,
                    strike_order_ok=None, strike_order_msg=None, option_metrics=None,
                    last_executed_signal=LAST_EXECUTED_SIGNAL,
                    **price_change_ui_kwargs
                )
                time.sleep(REFRESH_SECONDS)
                continue
            short_call_pos = short_put_pos = None
            long_call_pos = long_put_pos = None
            for pos in positions:
                sym = pos.get("product_symbol", "")
                size = float(pos.get("size", 0))
                if sym.startswith("C-") and size < 0:
                    short_call_pos = pos
                elif sym.startswith("C-") and size > 0:
                    long_call_pos = pos
                elif sym.startswith("P-") and size < 0:
                    short_put_pos = pos
                elif sym.startswith("P-") and size > 0:
                    long_put_pos = pos
            adjustments = []

            # Make positions equal logic: top up any smaller active legs to match max_sz without removing legs
            if USER_AUTO_EXECUTION and not API_DOWN and ORDER_TYPE != "futures":
                active_legs = []
                if short_call_pos:
                    sz = abs(int(float(short_call_pos.get("size", 0))))
                    if sz > 0:
                        active_legs.append(('short_call', short_call_pos, sz))
                if short_put_pos:
                    sz = abs(int(float(short_put_pos.get("size", 0))))
                    if sz > 0:
                        active_legs.append(('short_put', short_put_pos, sz))
                if long_call_pos:
                    sz = abs(int(float(long_call_pos.get("size", 0))))
                    if sz > 0:
                        active_legs.append(('long_call', long_call_pos, sz))
                if long_put_pos:
                    sz = abs(int(float(long_put_pos.get("size", 0))))
                    if sz > 0:
                        active_legs.append(('long_put', long_put_pos, sz))
                
                if len(active_legs) >= 2:
                    sizes = [leg[2] for leg in active_legs]
                    min_sz = min(sizes)
                    max_sz = max(sizes)
                    if max_sz > min_sz:
                        smaller_legs = [leg for leg in active_legs if leg[2] < max_sz]
                        if smaller_legs:
                            EQUALITY_TRIGGER_REASON = "MAKE_POSITIONS_EQUAL"
                            for leg in smaller_legs:
                                adjustments.append({
                                    "symbol": leg[1]["product_symbol"],
                                    "side": "buy" if float(leg[1]["size"]) > 0 else "sell",
                                    "size": max_sz - leg[2]
                                })
                            
                            if adjustments:
                                SKIP_REST = True
                                time.sleep(0.5)

            if EQUALITY_SUSPENDED and EQUALITY_SUSPENDED_UNTIL > 0 and time.time() > EQUALITY_SUSPENDED_UNTIL:
                EQUALITY_SUSPENDED = False
                EQUALITY_SUSPENDED_UNTIL = 0

            run_equality = (
                ENFORCE_EQUALITY_JOB
                and not EQUALITY_SUSPENDED
                and (EQUALITY_EVENT or EQUALITY_MANUAL_EXEC)
                and (STRATEGY_MODE == "OPENSTRIKE" and ORDER_TYPE != "futures")
                and USER_AUTO_EXECUTION
                and not custom_strategy_active
            )
            if not adjustments and not run_equality and ENFORCE_EQUALITY_JOB and not EQUALITY_SUSPENDED and (STRATEGY_MODE == "OPENSTRIKE" and ORDER_TYPE != "futures") and not custom_strategy_active:
                if short_call_pos and short_put_pos:
                    sc_sz = abs(int(float(short_call_pos.get("size", 0))))
                    sp_sz = abs(int(float(short_put_pos.get("size", 0))))
                    if sc_sz != sp_sz:
                        run_equality = True
                        EQUALITY_EVENT = True
                        EQUALITY_TRIGGER_REASON = "INSTANT_BALANCE_OPENSTRIKE"
            if run_equality and SYSTEM_EXECUTION_ALLOWED and not adjustments:
                if STRATEGY_MODE == "OPENSTRIKE" and ORDER_TYPE != "futures" and short_call_pos and short_put_pos:
                    sc_sz = abs(int(float(short_call_pos.get("size", 0))))
                    sp_sz = abs(int(float(short_put_pos.get("size", 0))))
                    target = min(sc_sz, sp_sz)
                    adjustments = []
                    if sc_sz > target:
                        adjustments.append({
                            "symbol": short_call_pos["product_symbol"],
                            "side": "buy",
                            "size": sc_sz - target
                        })
                    if sp_sz > target:
                        adjustments.append({
                            "symbol": short_put_pos["product_symbol"],
                            "side": "buy",
                            "size": sp_sz - target
                        })
                else:
                    execution_status = "EQUALITY PENDING (WAITING LEGS)"
                if adjustments:
                    FORCE_UI_REFRESH = True
                EQUALITY_WAIT_COUNT += 1
                if EQUALITY_WAIT_COUNT > 5 and not adjustments:
                    EQUALITY_EVENT = False
                    EQUALITY_MANUAL_EXEC = False
                    EQUALITY_TRIGGER_REASON = "ABORTED"
                    EQUALITY_WAIT_COUNT = 0
                if EQUALITY_WAIT_COUNT > 10:
                    EQUALITY_EVENT = False
                    EQUALITY_WAIT_COUNT = 0
                if adjustments:
                    time.sleep(0.5)
                    SKIP_REST = True

            if adjustments:
                print("\n⚖️ EQUALITY JOB RUNNING")
                print(f"Trigger Reason : {EQUALITY_TRIGGER_REASON}")

                _bal_eq, _blocked_eq, _ = wallet_usd()
                _free_eq = (_bal_eq - _blocked_eq) if _bal_eq is not None else 0
                has_sell = any(adj["side"] == "sell" for adj in adjustments)
                if has_sell and ((_bal_eq is not None and _bal_eq <= LOW_BALANCE_USD) or (_free_eq <= LOW_FREE_USD)):
                    execution_status = "EQUALITY SKIPPED — LOW BALANCE"
                    EQUALITY_EVENT = False
                    EQUALITY_MANUAL_EXEC = False
                    EQUALITY_TRIGGER_REASON = "NONE"
                    adjustments = []
                    FORCE_UI_REFRESH = True
                    SKIP_REST = True
                    continue
                for adj in adjustments:
                    place_order(
                        adj["symbol"],
                        adj["side"],
                        adj["size"],
                        MARGIN_MODE.lower(),
                        reason="EQUALITY"
                    )
                send_telegram(
                    "⚖️ EQUALITY ENFORCED\n"
                    f"Reason : {EQUALITY_TRIGGER_REASON}\n"
                    f"Time   : {datetime.now().strftime('%H:%M:%S')}"
                )
            if adjustments:
                EQUALITY_EVENT = False
                EQUALITY_MANUAL_EXEC = False
                EQUALITY_TRIGGER_REASON = "NONE"
                EQUALITY_WAIT_COUNT = 0
                FORCE_UI_REFRESH = True
            if EQUALITY_EVENT and not adjustments:
                EQUALITY_EVENT = False
                EQUALITY_MANUAL_EXEC = False
                EQUALITY_TRIGGER_REASON = "NONE"
                EQUALITY_WAIT_COUNT = 0
                FORCE_UI_REFRESH = True

            used_pct_calc, margin_drift, drift_status, drift_icon, margin_ceiling = calculate_margin_drift(
                bal, blocked, effective_min_margin
            )
            used_pct_ui, heat_level, heat_bar = render_margin_heatmap(bal, blocked)
            api_score, api_status, api_bar = render_api_health_bar()

            min_pct = effective_min_margin * 100
            ceiling_soft = margin_ceiling + 1
            EXECUTION_ALLOWED = (used_pct_calc < min_pct) or (used_pct_calc <= ceiling_soft)
            if not EXECUTION_ALLOWED:
                execution_status = f"PAUSED: Margin {used_pct_calc:.1f}% > {ceiling_soft:.1f}% (Ceiling+1%)"
            CAN_EXECUTE = (
                USER_AUTO_EXECUTION
                and not API_DOWN
                and not KILL_SWITCH
            )
            expiry_oi_list = []
            for exp in sorted(set(o["expiry"] for o in opts)):
                opts_exp = [o for o in opts if o["expiry"] == exp]
                c, p, pr = oi_pcr(opts_exp)
                mp = max_pain(opts_exp)
                expiry_oi_list.append((exp, c, p, pr, mp))
            all_mp_from_opts = max_pain(opts)

            spot_secondary = spot_secondary_oi
            oi_secondary = expiry_oi_list_secondary_oi
            symbol_secondary = symbol_secondary_oi
            _oi_primary = expiry_oi_list_primary if (expiry_oi_list_primary is not None and len(expiry_oi_list_primary or []) > 0) else expiry_oi_list
            _all_mp_primary = all_expiry_mp_primary if (expiry_oi_list_primary is not None and len(expiry_oi_list_primary or []) > 0) else all_mp_from_opts
            _spot_primary = spot_primary_display if spot_primary_display is not None else spot
            projected_profit = calculate_projected_profit(positions_all, spot_btc, spot_eth)
            max_loss = calculate_max_loss(positions_all, spot_btc, spot_eth)

            if ORDER_TYPE == "futures":
                _fp = next((p for p in positions_all
                            if not str(p.get("product_symbol","")).startswith(("C-","P-"))
                            and float(p.get("size", 0)) != 0), None)
                if _fp:
                    _fsize = float(_fp.get("size", 0))
                    _fentry = float(_fp.get("entry_price") or _fp.get("average_price") or 0)
                    _fspot = spot
                    if _fentry > 0 and _fspot > 0:
                        _abs = abs(_fsize)
                        if _fsize < 0:
                            projected_profit = round((_fentry - _fspot * (1 - MAX_LOSS_CAP_PCT)) * _abs * 0.001, 2)
                            max_loss        = round((_fspot * (1 + MAX_LOSS_CAP_PCT) - _fentry) * _abs * 0.001, 2)
                        else:
                            projected_profit = round((_fspot * (1 + MAX_LOSS_CAP_PCT) - _fentry) * _abs * 0.001, 2)
                            max_loss        = round((_fentry - _fspot * (1 - MAX_LOSS_CAP_PCT)) * _abs * 0.001, 2)
            opts_all = list(opts) if opts else []
            for sym in ["BTC", "ETH"]:
                if sym != SYMBOL and any(
                    (p.get("product_symbol") or "").startswith(("C-" + sym + "-", "P-" + sym + "-"))
                    and float(p.get("size", 0)) != 0
                    for p in positions_all
                ):
                    opts_all.extend(fetch_options_for_symbol(sym) or [])
            pos_delta, pos_gamma, pos_theta, pos_vega, pos_rho = portfolio_greeks_sum(positions_all, opts_all)
            strike_order_ok = None
            strike_order_msg = ""
            if execution_decision == "SELL CALL" and short_call_pos and long_call_pos and long_put_pos:
                strike_order_ok, strike_order_msg = validate_three_leg_strike_order(execution_decision, short_call_pos, long_put_pos, long_call_pos)
            elif execution_decision == "SELL PUT" and short_put_pos and long_call_pos and long_put_pos:
                strike_order_ok, strike_order_msg = validate_three_leg_strike_order(execution_decision, short_put_pos, long_put_pos, long_call_pos)

            if strike_order_ok is False and not (STRATEGY_MODE == "OPENSTRIKE" and ORDER_TYPE != "futures") and USER_AUTO_EXECUTION:
                legs_to_close = []
                if decision == "SELL CALL" and short_call_pos and long_call_pos and long_put_pos:
                    legs_to_close = [short_call_pos, long_call_pos, long_put_pos]
                elif decision == "SELL PUT" and short_put_pos and long_call_pos and long_put_pos:
                    legs_to_close = [short_put_pos, long_put_pos, long_call_pos]
                if legs_to_close:
                    for pos in legs_to_close:
                        sym = pos.get("product_symbol", "")
                        size = float(pos.get("size", 0))
                        if sym and size != 0:
                            square_off_position(sym, size, reason="STRIKE_ORDER_MISMATCH")
                            time.sleep(0.5)
                    send_telegram(
                        f"⚠️ STRIKE ORDER MISMATCH — ALL LEGS CLOSED\n"
                        f"Expected: {strike_order_msg}\n"
                        f"Position will be re-created as per current bias on next cycle.\n"
                        f"Time: {datetime.now().strftime('%H:%M:%S')}"
                    )
                    LAST_EXECUTED_SIGNAL = None
                    SKIP_REST = True
                    render_terminal_ui(
                        now=datetime.now(), spot=_spot_primary, decision=decision, source=source,
                        bal=bal, blocked=blocked, upnl=upnl,
                        projected_profit=projected_profit, max_loss=max_loss,
                        wallet_upnl_pct=wallet_upnl_pct, blocked_upnl_pct=blocked_upnl_pct,
                        used_pct_ui=used_pct_ui, heat_level=heat_level, heat_bar=heat_bar,
                        delta=delta, gamma=gamma,
                        position_details=position_details, position_count=position_count,
                        execution_status="Strike order mismatch — legs closed, will re-create next cycle",
                        used_pct_calc=used_pct_calc, margin_drift=margin_drift, drift_status=drift_status, drift_icon=drift_icon,
                        api_score=api_score, api_status=api_status, api_bar=api_bar,
                        expiry_oi_list=_oi_primary, expiry_oi_list_secondary=oi_secondary,
                        spot_secondary=spot_secondary, symbol_secondary=symbol_secondary, symbol_primary=main_sym,
                        all_expiry_max_pain_primary=_all_mp_primary, all_expiry_max_pain_secondary=all_expiry_mp_secondary,
                        position_delta_sum=pos_delta, position_gamma_sum=pos_gamma,
                        position_theta_sum=pos_theta, position_vega_sum=pos_vega, position_rho_sum=pos_rho,
                        strike_order_ok=strike_order_ok, strike_order_msg=strike_order_msg, option_metrics=None,
                        last_executed_signal=LAST_EXECUTED_SIGNAL,
                        **price_change_ui_kwargs
                    )
                    time.sleep(REFRESH_SECONDS)
                    continue

            option_metrics = None
            _fut_det = next((p for p in position_details if p.get("is_futures")), None) if position_details else None
            if ORDER_TYPE == "futures" and _fut_det:
                _is_short = _fut_det.get("dir_letter", "S") == "S"
                _atm_side = "call" if _is_short else "put"
                _atm_opt = None
                if opts:
                    _today = datetime.now().date()

                    _zero_dte = [o for o in opts if (o["expiry"].date() if hasattr(o["expiry"], "date") else o["expiry"]) == _today]
                    if _zero_dte:
                        _pool = _zero_dte
                        _dte_label = "0 DTE"
                    else:
                        _expiries = sorted(set(o["expiry"] for o in opts))
                        _pool = [o for o in opts if o["expiry"] == _expiries[0]] if _expiries else []
                        _dte_label = "near"
                    _atm_opt = select_atm_option(_pool, _spot_primary, _atm_side) if _pool else None
                if _atm_opt:
                    option_metrics = get_option_metrics(_atm_opt, _spot_primary)
                    if option_metrics:
                        _dir_label = "Short" if _is_short else "Long"
                        option_metrics["ref_label"] = f"ATM {_atm_side.upper()} [{_dte_label}] ({_dir_label} Futures)"
                        option_metrics["ref_contract"] = _atm_opt.get("symbol", "")

                    pos_delta = float(_atm_opt.get("delta", 0) or 0)
                    pos_gamma = float(_atm_opt.get("gamma", 0) or 0)
                    pos_theta = float(_atm_opt.get("theta", 0) or 0)
                    pos_vega  = float(_atm_opt.get("vega", 0) or 0)
                    pos_rho   = float(_atm_opt.get("rho", 0) or 0)
            elif position_details and len(position_details) >= 1:
                option_metrics = {"is_combined": True}
                pt, pi, ptv, piv = portfolio_theor_intrinsic_tv_iv(positions_all, opts_all, _spot_primary)
                option_metrics["combined_theor"] = pt
                option_metrics["combined_intrinsic"] = pi
                option_metrics["combined_time_value"] = ptv
                option_metrics["combined_iv_pct"] = piv
            else:
                ref_opt = None
                if opts:
                    expiries = sorted(set(o["expiry"] for o in opts))
                    near = [o for o in opts if o["expiry"] == expiries[0]] if expiries else []
                    ref_opt = select_atm_option(near, _spot_primary, "call") if near else None
                if ref_opt:
                    option_metrics = get_option_metrics(ref_opt, _spot_primary)
                    if option_metrics:
                        option_metrics["ref_label"] = "ATM near call (no active position)"
                        option_metrics["ref_contract"] = ref_opt.get("symbol", "")
            # --- Deferred NEW_POSITION telegram (after all sizing adjustments) ---
            if PENDING_NEW_POSITION_ALERT:
                _def_active = [
                    p for p in positions
                    if p.get("product_symbol", "").startswith(("C-", "P-", "MV-")) and float(p.get("size", 0)) != 0
                ]
                if _def_active:
                    _def_pos_line = format_position_line_for_message(_def_active)
                    _def_expiry = max_oi_expiry_display if max_oi_expiry_display else None
                    if not _def_expiry and _def_active:
                        _def_expiry = extract_expiry(_def_active[0].get("product_symbol", ""))
                    _def_positions_for_alert = positions_all if ORDER_TYPE == "futures" else _def_active
                    _def_proj = calculate_projected_profit(positions_all, spot_btc, spot_eth)
                    _def_max_loss = calculate_max_loss(positions_all, spot_btc, spot_eth)
                    if ORDER_TYPE == "futures":
                        _def_fp = next((p for p in positions_all
                                    if not str(p.get("product_symbol", "")).startswith(("C-", "P-", "MV-"))
                                    and float(p.get("size", 0)) != 0), None)
                        if _def_fp:
                            _def_fsize = float(_def_fp.get("size", 0))
                            _def_fentry = float(_def_fp.get("entry_price") or _def_fp.get("average_price") or 0)
                            _def_fspot = spot
                            if _def_fentry > 0 and _def_fspot > 0:
                                _def_abs = abs(_def_fsize)
                                if _def_fsize < 0:
                                    _def_proj = round((_def_fentry - _def_fspot * (1 - MAX_LOSS_CAP_PCT)) * _def_abs * 0.001, 2)
                                    _def_max_loss = round((_def_fspot * (1 + MAX_LOSS_CAP_PCT) - _def_fentry) * _def_abs * 0.001, 2)
                                else:
                                    _def_proj = round((_def_fspot * (1 + MAX_LOSS_CAP_PCT) - _def_fentry) * _def_abs * 0.001, 2)
                                    _def_max_loss = round((_def_fentry - _def_fspot * (1 - MAX_LOSS_CAP_PCT)) * _def_abs * 0.001, 2)
                    _def_msg = _format_new_position_telegram_lines(
                        _def_positions_for_alert, decision, SYMBOL, _def_expiry, bal, blocked, _def_pos_line,
                        strategy_mode=STRATEGY_MODE, projected_profit=_def_proj, max_loss=_def_max_loss,
                        position_details=position_details
                    )
                    send_telegram(_def_msg)
                PENDING_NEW_POSITION_ALERT = False

            render_terminal_ui(

                now=datetime.now(),
                spot=_spot_primary,
                decision=decision,
                source=source,
                bal=bal,
                blocked=blocked,
                upnl=upnl,
                projected_profit=projected_profit,
                max_loss=max_loss,
                wallet_upnl_pct=wallet_upnl_pct,
                blocked_upnl_pct=blocked_upnl_pct,
                used_pct_ui=used_pct_ui,
                heat_level=heat_level,
                heat_bar=heat_bar,
                delta=delta,
                gamma=gamma,
                position_details=position_details,
                position_count=position_count,
                execution_status=execution_status,
                used_pct_calc=used_pct_calc,
                margin_drift=margin_drift,
                drift_status=drift_status,
                drift_icon=drift_icon,
                api_score=api_score,
                api_status=api_status,
                api_bar=api_bar,
                expiry_oi_list=_oi_primary,
                expiry_oi_list_secondary=oi_secondary,
                spot_secondary=spot_secondary,
                symbol_secondary=symbol_secondary,
                symbol_primary=main_sym,
                all_expiry_max_pain_primary=_all_mp_primary,
                all_expiry_max_pain_secondary=all_expiry_mp_secondary,
                position_delta_sum=pos_delta,
                position_gamma_sum=pos_gamma,
                position_theta_sum=pos_theta,
                position_vega_sum=pos_vega,
                position_rho_sum=pos_rho,
                strike_order_ok=strike_order_ok,
                strike_order_msg=strike_order_msg,
                option_metrics=option_metrics,
                last_executed_signal=LAST_EXECUTED_SIGNAL,
                **price_change_ui_kwargs
            )
            FIRST_UI_RENDER_DONE = True
            LAST_MAIN_LOOP_STAGE = "sleep"
            if _SKIP_API_RECOVERY_FIRST_CYCLE:
                _SKIP_API_RECOVERY_FIRST_CYCLE = False
            time.sleep(REFRESH_SECONDS)

    except Exception as e:
        print(f"\n❌ ERROR: {e}", flush=True)
        send_telegram(
            f"💥 RUNTIME ERROR — AUTO-RESTART IN 10s\n"
            f"Error : {str(e)[:300]}\n"
            f"Time  : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
        )
        time.sleep(10)
        if KILL_SWITCH:
            break
        print("🔄 Restarting main loop...", flush=True)









