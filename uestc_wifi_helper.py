"""Command-line helper for logging into UESTC campus networks.

This module re-implements the original Pascal logic in Python without any GUI
requirements. It can be used as a CLI script or imported as a module.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import enum
import hashlib
import hmac
import math
import shutil
import struct
import sys
from pathlib import Path
from typing import Dict, Iterable, Tuple
from urllib.parse import quote

import json
from http.cookiejar import Cookie, CookieJar
from urllib.error import URLError
from urllib.parse import urlencode
from urllib.request import HTTPCookieProcessor, Request, build_opener

if sys.version_info >= (3, 11):  # Python 3.11+
    import tomllib  # type: ignore
else:  # pragma: no cover - fallback for older Pythons
    import tomli as tomllib  # type: ignore


CALLBACK_STRING = "jQuery112409729861590799633_1698107269291"
ALPHA = "LVoJPiCN2R8G90yg+hmFHuacZ1OWMnrsSTXkYpUq/3dlbfKwv6xztjI7DeBE45QA"
PAD = "="
NETWORK_OPERATORS: Dict[int, Tuple[int, str, str]] = {
    0: (3, "10.253.0.235", "dx"),
    1: (3, "10.253.0.235", "cmcc"),
    2: (1, "10.253.0.237", "dx-uestc"),
    3: (1, "10.253.0.237", "dx"),
}


class SimpleResponse:
    def __init__(self, status_code: int, text: str):
        self.status_code = status_code
        self.text = text


class SimpleSession:
    """A tiny HTTP client to avoid external dependencies."""

    def __init__(self):
        self.headers: dict[str, str] = {}
        self.cookies = CookieJar()
        self._opener = build_opener(HTTPCookieProcessor(self.cookies))

    def _build_request(self, url: str) -> Request:
        return Request(url, headers=self.headers)

    def _request(self, url: str, timeout: float) -> SimpleResponse:
        req = self._build_request(url)
        with self._opener.open(req, timeout=timeout) as resp:
            charset = resp.headers.get_content_charset() or "utf-8"
            body = resp.read().decode(charset, errors="replace")
            return SimpleResponse(resp.getcode(), body)

    def get(self, url: str, params: Dict[str, str | int] | None = None, timeout: float = 5) -> SimpleResponse:
        query = f"?{urlencode(params)}" if params else ""
        return self._request(url + query, timeout)


class NotConnectedException(RuntimeError):
    """Raised when the device cannot reach the portal host."""


class DeviceWithinScopeException(RuntimeError):
    """Raised when the device is outside the authentication scope."""


class IncorrectUsernameOrPasswordException(RuntimeError):
    """Raised when credentials are rejected by the portal."""


class CheckedStatus(enum.Enum):
    STILL_ONLINE = "StillOnline"
    DEVICE_WITHIN_SCOPE = "DeviceWithinScope"
    SUCCESSFULLY_LOGIN = "SuccessfullyLogin"


def _to_uint32_array(data: bytes, include_length: bool) -> list[int]:
    length = len(data)
    count = (length - 1) // 4 + (2 if include_length else 1)
    result = [0 for _ in range(count)]
    for i, byte in enumerate(data):
        result[i // 4] |= byte << (8 * (i % 4))
    if include_length:
        result[-1] = length
    return result


def _custom_base64(data: bytes) -> str:
    encoded = []
    i = 0
    imax = len(data) - len(data) % 3
    while i < imax:
        b10 = (data[i] << 16) | (data[i + 1] << 8) | data[i + 2]
        encoded.append(ALPHA[(b10 >> 18) & 63])
        encoded.append(ALPHA[(b10 >> 12) & 63])
        encoded.append(ALPHA[(b10 >> 6) & 63])
        encoded.append(ALPHA[b10 & 63])
        i += 3
    remainder = len(data) - imax
    if remainder:
        b10 = data[imax] << 16
        if remainder == 2:
            b10 |= data[imax + 1] << 8
        encoded.append(ALPHA[(b10 >> 18) & 63])
        encoded.append(ALPHA[(b10 >> 12) & 63])
        if remainder == 2:
            encoded.append(ALPHA[(b10 >> 6) & 63])
        else:
            encoded.append(PAD)
        encoded.append(PAD)
    return "".join(encoded)


def xencode(plain: str, key: str) -> str:
    """Port of the TEA + custom base64 algorithm used by the portal."""

    if not plain:
        raise ValueError("plain text is empty")

    v = _to_uint32_array(plain.encode("utf-8"), include_length=True)
    k = _to_uint32_array(key.encode("utf-8"), include_length=False)
    while len(k) < 4:
        k.append(0)

    n = len(v) - 1
    z = v[n]
    y = v[0]
    c = 0x9E3779B9
    q = int(math.floor(6 + 52 / len(v)))
    d = 0
    while q > 0:
        q -= 1
        d = (d + c) & 0xFFFFFFFF
        e = (d >> 2) & 3
        for p in range(n):
            y = v[p + 1]
            m = ((z >> 5) ^ (y << 2))
            m = (m + ((y >> 3) ^ (z << 4)) ^ (d ^ y)) & 0xFFFFFFFF
            m = (m + (k[(p & 3) ^ e] ^ z)) & 0xFFFFFFFF
            v[p] = (v[p] + m) & 0xFFFFFFFF
            z = v[p]
        y = v[0]
        m = ((z >> 5) ^ (y << 2))
        m = (m + ((y >> 3) ^ (z << 4)) ^ (d ^ y)) & 0xFFFFFFFF
        m = (m + (k[(n & 3) ^ e] ^ z)) & 0xFFFFFFFF
        v[n] = (v[n] + m) & 0xFFFFFFFF
        z = v[n]

    data_bytes = b"".join(struct.pack("<I", num & 0xFFFFFFFF) for num in v)
    return _custom_base64(data_bytes)


class UESTCWiFi:
    def __init__(self, username: str, password: str, network_operator: int):
        if network_operator not in NETWORK_OPERATORS:
            raise ValueError("Unknown network operator")

        ac_id, target_ip, operator_code = NETWORK_OPERATORS[network_operator]
        self._username = username
        self._password = password
        self._ac_id = ac_id
        self._target_ip = target_ip
        self._network_operator = operator_code
        self._session = SimpleSession()
        self._session.headers.update(
            {
                "Content-Type": "application/x-www-form-urlencoded",
                "User-Agent": (
                    "Mozilla/5.0 (Windows NT 10.0; WOW64) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/102.0.0.0 Safari/537.36"
                ),
                "Host": target_ip,
            }
        )
        self._session.headers["Cookie"] = "lang=zh-CN"

    @staticmethod
    def _parse_response(res: str) -> dict:
        prefix = f"{CALLBACK_STRING}("
        if not res.startswith(prefix) or not res.endswith(")"):
            raise RuntimeError("Unknown response format")
        json_str = res[len(prefix) : -1]
        return json.loads(json_str)

    def _check_connect(self) -> bool:
        try:
            resp = self._session.get(f"http://{self._target_ip}", timeout=5)
            return resp.status_code < 400
        except URLError:
            return False

    def _check_online(self) -> Tuple[bool, str]:
        timestamp = int(_dt.datetime.now().timestamp() * 1000)
        res = self._session.get(
            f"http://{self._target_ip}/cgi-bin/rad_user_info",
            params={
                "callback": CALLBACK_STRING,
                "_": timestamp,
            },
            timeout=5,
        )
        json_data = self._parse_response(res.text)
        error = json_data.get("error", "")
        if error == "ok":
            return True, json_data.get("online_ip", "")
        if error == "not_online_error":
            return False, json_data.get("client_ip", "")
        if error == "speed_limit_error":
            raise RuntimeError("Authentication requests are too frequent")
        raise RuntimeError("Unexpected response when checking online status")

    def _login(self, client_ip: str) -> None:
        timestamp = int(_dt.datetime.now().timestamp() * 1000)
        username = f"{self._username}@{self._network_operator}"
        res = self._session.get(
            f"http://{self._target_ip}/cgi-bin/get_challenge",
            params={
                "callback": CALLBACK_STRING,
                "username": username,
                "ip": client_ip,
                "_": timestamp,
            },
            timeout=5,
        )
        json_data = self._parse_response(res.text)
        if json_data.get("error", "") != "ok":
            raise RuntimeError(
                "Fetch challenge failed: " + json_data.get("error_msg", "")
            )
        token = json_data.get("challenge", "")
        if not token:
            raise RuntimeError("Challenge token is empty")

        payload = {
            "username": username,
            "password": self._password,
            "ip": client_ip,
            "acid": self._ac_id,
            "enc_ver": "srun_bx1",
        }
        json_str = json.dumps(payload, separators=(",", ":"))
        encoded_str = xencode(json_str, token)
        info = "{SRBX1}" + encoded_str
        password_md5 = hmac.new(
            token.encode(), self._password.encode(), hashlib.md5
        ).hexdigest()
        chksum_base = (
            token
            + username
            + token
            + password_md5
            + token
            + str(self._ac_id)
            + token
            + client_ip
            + token
            + "200"
            + token
            + "1"
            + token
            + info
        )
        chksum = hashlib.sha1(chksum_base.encode()).hexdigest()

        res = self._session.get(
            f"http://{self._target_ip}/cgi-bin/srun_portal",
            params={
                "callback": CALLBACK_STRING,
                "action": "login",
                "username": username,
                "password": f"%7BMD5%7D{password_md5}",
                "ac_id": self._ac_id,
                "ip": client_ip,
                "chksum": chksum,
                "info": quote(info, safe=""),
                "n": 200,
                "type": 1,
                "os": "Windows 10",
                "name": "Windows",
                "double_stack": 0,
                "_": int(_dt.datetime.now().timestamp() * 1000),
            },
            timeout=5,
        )
        json_data = self._parse_response(res.text)
        error = json_data.get("error", "")
        if error != "ok":
            error_msg = json_data.get("error_msg", "")
            if error_msg in (
                "INFO Error锛宔rr_code=2",
                "E2901: (Third party 1)bind_user2: ldap_bind error",
                "E2901: (Third party 1)ldap_first_entry error",
            ):
                raise IncorrectUsernameOrPasswordException(
                    "Incorrect username or password"
                )
            raise RuntimeError(
                f"Login failed: error: {error}, error_msg: {error_msg}"
            )

    def check(self) -> CheckedStatus:
        if not self._check_connect():
            raise NotConnectedException("Not connected to network cable or WiFi")
        online, online_ip = self._check_online()
        if online:
            return CheckedStatus.STILL_ONLINE
        try:
            self._login(online_ip)
            return CheckedStatus.SUCCESSFULLY_LOGIN
        except DeviceWithinScopeException:
            return CheckedStatus.DEVICE_WITHIN_SCOPE


def _timestamp() -> str:
    return _dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def check_once(wifi: UESTCWiFi, log_file_path: Path | None = None) -> str:
    time_str = _timestamp()
    try:
        status = wifi.check()
        if status is CheckedStatus.STILL_ONLINE:
            msg = f"{time_str} - INFO: 设备已在线"
        elif status is CheckedStatus.DEVICE_WITHIN_SCOPE:
            msg = f"{time_str} - INFO: 设备不在范围内"
        else:
            msg = f"{time_str} - INFO: 登录成功"
    except NotConnectedException:
        msg = f"{time_str} - ERROR: 未连接到网络"
    except IncorrectUsernameOrPasswordException:
        msg = f"{time_str} - ERROR: 用户名或密码错误"
    except Exception as exc:  # pragma: no cover - defensive
        msg = f"{time_str} - ERROR: 未知错误: {exc}"

    if log_file_path is not None:
        log_file_path.parent.mkdir(parents=True, exist_ok=True)
        with log_file_path.open("a", encoding="utf-8") as log_file:
            log_file.write(msg + "\n")
    else:
        print(msg)
    return msg


def _load_config(config_path: Path) -> dict:
    if not config_path.exists():
        template = Path(__file__).resolve().parent / "template.toml"
        if template.exists():
            config_path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(template, config_path)
        raise FileNotFoundError(
            f"Configuration file not found. A template has been placed at {config_path}."
        )
    with config_path.open("rb") as fp:
        return tomllib.load(fp)


def _resolve_credentials(args: argparse.Namespace) -> Tuple[str, str, int]:
    if args.username and args.password:
        return args.username, args.password, args.network_operator
    config_path = Path(args.config).expanduser()
    config = _load_config(config_path)
    try:
        username = config["username"]
        password = config["password"]
    except KeyError as exc:
        raise KeyError(f"Missing required field in config: {exc}")
    network_operator = int(config.get("network_operator", 0))
    if network_operator not in NETWORK_OPERATORS:
        raise ValueError("Unknown network operator in config")
    return username, password, network_operator


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="UESTC WiFi helper implemented in Python (CLI only)."
    )
    parser.add_argument("username", nargs="?", help="Portal username")
    parser.add_argument("password", nargs="?", help="Portal password")
    parser.add_argument(
        "network_operator",
        nargs="?",
        type=int,
        default=0,
        help="Network operator: 0 电信 (寝室), 1 移动 (寝室), 2 教研室, 3 教研室电信.",
    )
    parser.add_argument(
        "-l",
        "--log",
        action="store_true",
        help="Write results to ~/uestc_wifi.log instead of stdout",
    )
    parser.add_argument(
        "-c",
        "--config",
        default=str(Path.home() / "uestc_wifi.toml"),
        help="Path to config file (used when username/password are omitted)",
    )
    return parser.parse_args(argv)


def main(argv: Iterable[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        username, password, network_operator = _resolve_credentials(args)
    except Exception as exc:  # pragma: no cover - CLI input validation
        print(exc)
        return 1

    wifi = UESTCWiFi(username, password, network_operator)
    log_path = Path.home() / "uestc_wifi.log" if args.log else None
    check_once(wifi, log_path)
    return 0


if __name__ == "__main__":  # pragma: no cover - CLI entrypoint
    raise SystemExit(main())
