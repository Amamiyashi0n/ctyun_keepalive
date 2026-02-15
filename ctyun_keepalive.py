import asyncio
import base64
import hashlib
import json
import os
import random
import string
import sys
import time
import urllib.parse
import urllib.request
from dataclasses import dataclass
from datetime import datetime


def write_line(value):
    ts = datetime.now().strftime("%H:%M:%S.%f")[:-4]
    print(f"[{ts}] {value}", flush=True)


def compute_md5(value):
    return hashlib.md5(value.encode("utf-8")).hexdigest()


def compute_sha256(value):
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def generate_random_string(length):
    return "".join(random.choice(string.ascii_letters + string.digits) for _ in range(length))


def read_line(prompt):
    sys.stdout.write(prompt)
    sys.stdout.flush()
    return sys.stdin.readline().rstrip("\n")


@dataclass
class LoginInfo:
    userAccount: str
    bondedDevice: bool
    secretKey: str
    userId: int
    tenantId: int
    userName: str


@dataclass
class DesktopInfo:
    desktopId: int
    host: str
    port: str
    clinkLvsOutHost: str
    caCert: str
    clientCert: str
    clientKey: str
    token: str
    tenantMemberAccount: str

    def to_buffer(self, device_code):
        device_type = "60"
        header_size = 36
        total_size = header_size + len(self.token) + 1 + len(device_type) + 1 + len(device_code) + 1 + len(self.tenantMemberAccount) + 1
        buffer = bytearray(total_size)
        current_offset = header_size

        def write_uint32_le(value, offset):
            buffer[offset:offset + 4] = value.to_bytes(4, "little", signed=False)

        write_uint32_le(self.desktopId, 0)
        write_uint32_le(len(self.token) + 1, 4)
        write_uint32_le(current_offset, 8)
        current_offset += len(self.token) + 1

        write_uint32_le(len(device_type) + 1, 12)
        write_uint32_le(current_offset, 16)
        current_offset += len(device_type) + 1

        write_uint32_le(len(device_code) + 1, 20)
        write_uint32_le(current_offset, 24)
        current_offset += len(device_code) + 1

        write_uint32_le(len(self.tenantMemberAccount) + 1, 28)
        write_uint32_le(current_offset, 32)

        body_offset = header_size
        for s in [self.token, device_type, device_code, self.tenantMemberAccount]:
            data = s.encode("ascii")
            buffer[body_offset:body_offset + len(data)] = data
            body_offset += len(data)
            buffer[body_offset] = 0
            body_offset += 1

        return bytes(buffer)


@dataclass
class Desktop:
    desktopId: str
    desktopName: str
    desktopCode: str
    useStatusText: str
    desktopInfo: DesktopInfo | None = None


class SendInfo:
    def __init__(self, type_value, data=None):
        self.type = type_value
        self.data = data or b""

    @property
    def size(self):
        return len(self.data)

    def to_buffer(self, is_build_msg):
        msg_length = 8 if is_build_msg else 0
        data_length = len(self.data)
        size = msg_length + data_length
        buffer = bytearray(2 + 4 + msg_length + data_length)
        buffer[0:2] = self.type.to_bytes(2, "little", signed=False)
        buffer[2:6] = size.to_bytes(4, "little", signed=True)
        if is_build_msg:
            buffer[6:10] = data_length.to_bytes(4, "little", signed=False)
            buffer[10:14] = (8).to_bytes(4, "little", signed=False)
        if data_length:
            buffer[6 + msg_length:6 + msg_length + data_length] = self.data
        return bytes(buffer)

    @staticmethod
    def from_buffer(buffer):
        results = []
        if not buffer:
            return results
        offset = 0
        while offset + 6 <= len(buffer):
            type_value = int.from_bytes(buffer[offset:offset + 2], "little", signed=False)
            data_length = int.from_bytes(buffer[offset + 2:offset + 6], "little", signed=True)
            if data_length < 0 or offset + 6 + data_length > len(buffer):
                remaining = len(buffer) - offset
                if remaining > 0:
                    data = buffer[offset:offset + remaining]
                    results.append(SendInfo(type_value, data))
                break
            data = buffer[offset + 6:offset + 6 + data_length] if data_length > 0 else b""
            results.append(SendInfo(type_value, data))
            offset += 6 + data_length
            if offset + 6 > len(buffer) and offset < len(buffer):
                if all(b == 0 for b in buffer[offset:]):
                    offset = len(buffer)
                    break
        return results


class Encryption:
    def __init__(self):
        self.buffers = []
        self.auth_mechanism = 1

    def execute(self, key_bytes):
        self.resolve_inbound_data(key_bytes)
        n, e = self.get_public_key()
        encrypted = self.l(128, "", n, e)
        return self.to_buffer(encrypted)

    def resolve_inbound_data(self, data):
        self.buffers.append(data[16:])

    def get_public_key(self):
        n_source = self.buffers[0][32:32 + 129]
        n = int.from_bytes(n_source, "big", signed=False)
        e_source = self.buffers[0][163:166]
        e = (e_source[0] << 16) | (e_source[1] << 8) | e_source[2]
        return n, e

    def l(self, key_len, label, n, e):
        seed = os.urandom(20)
        h_len = 20
        db_len = key_len - h_len - 1
        db = bytearray(db_len)
        l_hash = hashlib.sha1(label.encode("utf-8")).digest()
        db[0:len(l_hash)] = l_hash
        db[db_len - 1 - len(label) - 1] = 1
        db_mask = self.mgf1(seed, db_len)
        for k in range(db_len):
            db[k] ^= db_mask[k]
        seed_mask = self.mgf1(db, h_len)
        seed = bytearray(seed)
        for k in range(h_len):
            seed[k] ^= seed_mask[k]
        em = bytearray(key_len)
        em[1:1 + h_len] = seed
        em[1 + h_len:] = db
        m = int.from_bytes(em, "big", signed=False)
        result_int = pow(m, e, n)
        result_bytes = result_int.to_bytes((result_int.bit_length() + 7) // 8 or 1, "big", signed=False)
        if len(result_bytes) == key_len:
            return result_bytes
        final = bytearray(key_len)
        final[key_len - len(result_bytes):] = result_bytes
        return bytes(final)

    def mgf1(self, seed, mask_len):
        mask = bytearray(mask_len)
        counter = 0
        offset = 0
        while offset < mask_len:
            c = counter.to_bytes(4, "big", signed=False)
            block = seed + c
            hash_bytes = hashlib.sha1(block).digest()
            copy_len = min(len(hash_bytes), mask_len - offset)
            mask[offset:offset + copy_len] = hash_bytes[:copy_len]
            offset += len(hash_bytes)
            counter += 1
        return bytes(mask)

    def to_buffer(self, buffer):
        result = bytearray(4 + len(buffer))
        result[0:4] = self.auth_mechanism.to_bytes(4, "little", signed=False)
        result[4:] = buffer
        return bytes(result)


class CtYunApi:
    orc_url = "https://orc.1999111.xyz/ocr"
    version = "103020001"
    device_type = "60"

    def __init__(self, device_code):
        self.device_code = device_code
        self.login_info = None
        self.base_headers = {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/137.0.0.0 Safari/537.36",
            "ctg-devicetype": self.device_type,
            "ctg-version": self.version,
            "ctg-devicecode": self.device_code,
            "referer": "https://pc.ctyun.cn/",
        }

    def login(self, user_phone, password):
        for i in range(1, 4):
            challenge = self.get_gen_challenge_data()
            if not challenge:
                continue
            captcha_code = self.get_captcha(self.get_login_captcha(user_phone))
            if not captcha_code:
                continue
            collection = [
                ("userAccount", user_phone),
                ("password", compute_sha256(password + challenge["challengeCode"])),
                ("sha256Password", compute_sha256(compute_sha256(password) + challenge["challengeCode"])),
                ("challengeId", challenge["challengeId"]),
                ("captchaCode", captcha_code),
            ]
            self.add_collection(collection)
            result = self.post_form("https://desk.ctyun.cn:8810/api/auth/client/login", collection)
            if result and result.get("code") == 0:
                data = result.get("data") or {}
                self.login_info = LoginInfo(
                    userAccount=data.get("userAccount") or "",
                    bondedDevice=data.get("bondedDevice", False),
                    secretKey=data.get("secretKey") or "",
                    userId=data.get("userId") or 0,
                    tenantId=data.get("tenantId") or 0,
                    userName=data.get("userName") or "",
                )
                return True
            msg = result.get("msg") if result else "unknown"
            write_line(f"重试{i}, Login Error:{msg}")
            if msg == "用户名或密码错误":
                return False
        return False

    def get_sms_code(self, user_phone):
        for i in range(3):
            captcha_code = self.get_captcha(self.get_sms_code_captcha())
            if captcha_code:
                result = self.get_json(f"https://desk.ctyun.cn:8810/api/cdserv/client/device/getSmsCode?mobilePhone={user_phone}&captchaCode={captcha_code}")
                if result and result.get("code") == 0:
                    return True
                msg = result.get("msg") if result else "unknown"
                write_line(f"重试{i}, GetSmsCode Error:{msg}")
        return False

    def binding_device(self, verification_code):
        url = f"https://desk.ctyun.cn:8810/api/cdserv/client/device/binding?verificationCode={verification_code}&deviceName=Chrome%E6%B5%8F%E8%A7%88%E5%99%A8&deviceCode={self.device_code}&deviceModel=Windows+NT+10.0%3B+Win64%3B+x64&sysVersion=Windows+NT+10.0%3B+Win64%3B+x64&appVersion=3.2.0&hostName=pc.ctyun.cn&deviceInfo=Win32"
        result = self.post_json(url, None)
        if result and result.get("code") == 0:
            return True
        msg = result.get("msg") if result else "unknown"
        write_line(f"BindingDevice Error:{msg}")
        return False

    def get_gen_challenge_data(self):
        result = self.post_json("https://desk.ctyun.cn:8810/api/auth/client/genChallengeData", {})
        if result and result.get("code") == 0:
            return result.get("data")
        msg = result.get("msg") if result else "unknown"
        write_line(f"GetGenChallengeDataAsync Error:{msg}")
        return None

    def get_login_captcha(self, user_phone):
        try:
            url = f"https://desk.ctyun.cn:8810/api/auth/client/captcha?height=36&width=85&userInfo={user_phone}&mode=auto&_t=1749139280909"
            return self.get_bytes(url, signed=False)
        except Exception as ex:
            write_line(f"登录验证码获取错误：{ex}")
            return None

    def get_sms_code_captcha(self):
        try:
            url = "https://desk.ctyun.cn:8810/api/auth/client/validateCode/captcha?width=120&height=40&_t=1766158569152"
            return self.get_bytes(url, signed=True)
        except Exception as ex:
            write_line(f"短信验证码获取错误：{ex}")
            return None

    def get_captcha(self, img_bytes):
        if not img_bytes:
            return ""
        try:
            write_line("正在识别验证码.")
            image_b64 = base64.b64encode(img_bytes).decode("utf-8")
            boundary = "----ctyun" + generate_random_string(16)
            body = []
            body.append(f"--{boundary}\r\n".encode("utf-8"))
            body.append(b'Content-Disposition: form-data; name="image"\r\n\r\n')
            body.append(image_b64.encode("utf-8"))
            body.append(f"\r\n--{boundary}--\r\n".encode("utf-8"))
            data = b"".join(body)
            headers = {
                "Content-Type": f"multipart/form-data; boundary={boundary}",
                "Content-Length": str(len(data)),
            }
            resp = self.request("POST", self.orc_url, data=data, headers=headers, signed=False)
            result = json.loads(resp.decode("utf-8"))
            write_line(f"识别结果：{resp.decode('utf-8')}")
            return result.get("data") or ""
        except Exception as ex:
            write_line(f"验证码识别错误：{ex}")
            return ""

    def get_client_list(self):
        try:
            payload = {"getCnt": 20, "desktopTypes": ["1", "2001", "2002", "2003"], "sortType": "createTimeV1"}
            result = self.post_json("https://desk.ctyun.cn:8810/api/desktop/client/pageDesktop", payload)
            data = result.get("data") if result else None
            if not data:
                return []
            desktops = []
            for d in data.get("desktopList", []):
                desktops.append(Desktop(
                    desktopId=d.get("desktopId"),
                    desktopName=d.get("desktopName"),
                    desktopCode=d.get("desktopCode"),
                    useStatusText=d.get("useStatusText"),
                ))
            return desktops
        except Exception as ex:
            write_line(f"获取设备信息错误。{ex}")
            return []

    def connect(self, desktop_id):
        collection = [
            ("objId", desktop_id),
            ("objType", "0"),
            ("osType", "15"),
            ("deviceId", self.device_type),
            ("vdCommand", ""),
            ("ipAddress", ""),
            ("macAddress", ""),
        ]
        self.add_collection(collection)
        result = self.post_form("https://desk.ctyun.cn:8810/api/desktop/client/connect", collection)
        return result

    def apply_signature(self, headers):
        if self.login_info:
            timestamp = str(int(time.time() * 1000))
            headers["ctg-userid"] = str(self.login_info.userId)
            headers["ctg-tenantid"] = str(self.login_info.tenantId)
            headers["ctg-timestamp"] = timestamp
            headers["ctg-requestid"] = timestamp
            signature_str = f"{self.device_type}{timestamp}{self.login_info.tenantId}{timestamp}{self.login_info.userId}{self.version}{self.login_info.secretKey}"
            headers["ctg-signaturestr"] = compute_md5(signature_str)

    def add_collection(self, collection):
        collection.append(("deviceCode", self.device_code))
        collection.append(("deviceName", "Chrome浏览器"))
        collection.append(("deviceType", self.device_type))
        collection.append(("deviceModel", "Windows NT 10.0; Win64; x64"))
        collection.append(("appVersion", "3.2.0"))
        collection.append(("sysVersion", "Windows NT 10.0; Win64; x64"))
        collection.append(("clientVersion", self.version))

    def request(self, method, url, data=None, headers=None, signed=True):
        merged_headers = dict(self.base_headers)
        if headers:
            merged_headers.update(headers)
        if signed:
            self.apply_signature(merged_headers)
        req = urllib.request.Request(url, data=data, headers=merged_headers, method=method)
        with urllib.request.urlopen(req, timeout=30) as resp:
            return resp.read()

    def post_json(self, url, payload):
        data = b""
        headers = {}
        if payload is not None:
            data = json.dumps(payload).encode("utf-8")
            headers["Content-Type"] = "application/json"
        try:
            resp = self.request("POST", url, data=data, headers=headers, signed=True)
            return json.loads(resp.decode("utf-8"))
        except Exception as ex:
            return {"code": -100, "msg": str(ex)}

    def post_form(self, url, collection):
        data = urllib.parse.urlencode(collection).encode("utf-8")
        headers = {"Content-Type": "application/x-www-form-urlencoded"}
        try:
            resp = self.request("POST", url, data=data, headers=headers, signed=True)
            return json.loads(resp.decode("utf-8"))
        except Exception as ex:
            return {"code": -100, "msg": str(ex)}

    def get_json(self, url):
        try:
            resp = self.request("GET", url, signed=True)
            return json.loads(resp.decode("utf-8"))
        except Exception as ex:
            return {"code": -100, "msg": str(ex)}

    def get_bytes(self, url, signed=True):
        return self.request("GET", url, signed=signed)


def resolve_credentials():
    if os.path.exists("/.dockerenv"):
        return os.getenv("APP_USER"), os.getenv("APP_PASSWORD"), os.getenv("DEVICECODE")
    if not os.path.exists("DeviceCode.txt"):
        with open("DeviceCode.txt", "w", encoding="utf-8") as f:
            f.write("web_" + generate_random_string(32))
    with open("DeviceCode.txt", "r", encoding="utf-8") as f:
        code = f.read().strip()
    user = read_line("账号: ")
    try:
        import getpass
        if sys.stdin.isatty():
            pwd = getpass.getpass("密码: ")
        else:
            pwd = read_line("密码: ")
    except Exception:
        pwd = read_line("密码: ")
    return user, pwd, code


async def receive_loop(ws, desktop, api):
    encryptor = Encryption()
    while True:
        message = await ws.recv()
        if isinstance(message, str):
            continue
        if message[:4] == b"REDQ":
            write_line(f"[{desktop.desktopCode}] -> 收到保活校验")
            response = encryptor.execute(message)
            await ws.send(response)
            write_line(f"[{desktop.desktopCode}] -> 发送保活响应成功")
        else:
            try:
                infos = SendInfo.from_buffer(message)
                for info in infos:
                    if info.type == 103:
                        user_json = json.dumps({
                            "type": 1,
                            "userName": api.login_info.userName,
                            "userInfo": "",
                            "userId": api.login_info.userId,
                        }, ensure_ascii=False)
                        payload = SendInfo(118, user_json.encode("utf-8")).to_buffer(True)
                        await ws.send(payload)
            except Exception as ex:
                write_line(str(ex))


async def keep_alive_worker(desktop, api, stop_event):
    initial_payload = base64.b64decode("UkVEUQIAAAACAAAAGgAAAAAAAAABAAEAAAABAAAAEgAAAAkAAAAECAAA")
    uri = f"wss://{desktop.desktopInfo.clinkLvsOutHost}/clinkProxy/{desktop.desktopId}/MAIN"
    try:
        import websockets
    except Exception as ex:
        write_line(f"缺少 websockets 依赖：{ex}")
        return
    while not stop_event.is_set():
        try:
            write_line(f"[{desktop.desktopCode}] === 新周期开始，尝试连接 ===")
            async with websockets.connect(
                uri,
                additional_headers={"Origin": "https://pc.ctyun.cn"},
                subprotocols=["binary"],
                ping_interval=None,
            ) as ws:
                connect_message = {
                    "type": 1,
                    "ssl": 1,
                    "host": desktop.desktopInfo.clinkLvsOutHost.split(":")[0],
                    "port": desktop.desktopInfo.clinkLvsOutHost.split(":")[1],
                    "ca": desktop.desktopInfo.caCert,
                    "cert": desktop.desktopInfo.clientCert,
                    "key": desktop.desktopInfo.clientKey,
                    "servername": f"{desktop.desktopInfo.host}:{desktop.desktopInfo.port}",
                    "oqs": 0,
                }
                await ws.send(json.dumps(connect_message))
                await asyncio.sleep(0.5)
                await ws.send(initial_payload)
                write_line(f"[{desktop.desktopCode}] 连接已就绪，保持 60 秒...")
                try:
                    await asyncio.wait_for(receive_loop(ws, desktop, api), timeout=60 * 60)
                except asyncio.TimeoutError:
                    write_line(f"[{desktop.desktopCode}] 60秒时间到，准备重连...")
        except Exception as ex:
            msg = str(ex)
            if "1005" in msg and "no status received" in msg:
                write_line(f"[{desktop.desktopCode}] 连接被对端关闭(1005)，不影响脚本使用，准备重连")
            else:
                write_line(f"[{desktop.desktopCode}] 异常: {ex}")
            await asyncio.sleep(5)


def parse_desktop_info(data):
    if not data:
        return None
    return DesktopInfo(
        desktopId=data.get("desktopId"),
        host=data.get("host"),
        port=data.get("port"),
        clinkLvsOutHost=data.get("clinkLvsOutHost"),
        caCert=data.get("caCert"),
        clientCert=data.get("clientCert"),
        clientKey=data.get("clientKey"),
        token=data.get("token"),
        tenantMemberAccount=data.get("tenantMemberAccount"),
    )


async def main():
    write_line("版本：v 1.0.0")
    user_phone, password, device_code = resolve_credentials()
    if not user_phone:
        return
    api = CtYunApi(device_code)
    if not api.login(user_phone, password):
        return
    if not api.login_info.bondedDevice:
        api.get_sms_code(user_phone)
        verification_code = read_line("短信验证码: ")
        if not api.binding_device(verification_code):
            return
    desktops = api.get_client_list()
    active_desktops = []
    for d in desktops:
        if d.useStatusText != "运行中":
            write_line(f"[{d.desktopCode}] [{d.useStatusText}]电脑未开机，正在开机，请在2分钟后重新运行软件")
        connect_result = api.connect(d.desktopId)
        if connect_result and connect_result.get("code") == 0:
            info = parse_desktop_info(connect_result.get("data", {}).get("desktopInfo"))
            if info:
                d.desktopInfo = info
                active_desktops.append(d)
        else:
            msg = connect_result.get("msg") if connect_result else "unknown"
            write_line(f"Connect Error: [{d.desktopId}] {msg}")
    if not active_desktops:
        return
    write_line("保活任务启动：每 60 秒强制重连一次。")
    stop_event = asyncio.Event()

    loop = asyncio.get_running_loop()
    for sig in ("SIGINT", "SIGTERM"):
        if hasattr(asyncio, "get_running_loop"):
            try:
                import signal
                loop.add_signal_handler(getattr(signal, sig), stop_event.set)
            except Exception:
                pass

    tasks = [keep_alive_worker(d, api, stop_event) for d in active_desktops]
    try:
        await asyncio.gather(*tasks)
    except asyncio.CancelledError:
        write_line("程序已停止。")


if __name__ == "__main__":
    if sys.version_info < (3, 10):
        write_line("需要 Python 3.10+")
        sys.exit(1)
    asyncio.run(main())
