import asyncio
import base64
import hashlib
import hmac
import json
import os
import random
import ssl
import string
import sys
import time
import urllib.parse
import urllib.request
import uuid
from dataclasses import dataclass
from datetime import datetime
from typing import Optional


def write_line(value):
    ts = datetime.now().strftime("%H:%M:%S.%f")[:-4]
    print(f"[{ts}] {value}", flush=True)


def compute_md5(value):
    return hashlib.md5(value.encode("utf-8")).hexdigest()


def compute_sha256(value):
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def get_system_fingerprint():
    node = uuid.getnode()
    mac_bytes = node.to_bytes(6, "big", signed=False)
    mac_address = ":".join(f"{b:02x}" for b in mac_bytes)
    return hashlib.sha256(mac_address.encode("utf-8")).hexdigest()


def generate_salt():
    return os.urandom(16).hex()


def derive_key(system_fingerprint, salt):
    material = f"{system_fingerprint}|{salt}".encode("utf-8")
    return hashlib.sha256(material).digest()


def rotl32(v, n):
    return ((v << n) & 0xffffffff) | (v >> (32 - n))


def quarter_round(a, b, c, d):
    a = (a + b) & 0xffffffff
    d ^= a
    d = rotl32(d, 16)
    c = (c + d) & 0xffffffff
    b ^= c
    b = rotl32(b, 12)
    a = (a + b) & 0xffffffff
    d ^= a
    d = rotl32(d, 8)
    c = (c + d) & 0xffffffff
    b ^= c
    b = rotl32(b, 7)
    return a, b, c, d


def chacha20_block(key, counter, nonce):
    state = [
        0x61707865,
        0x3320646e,
        0x79622d32,
        0x6b206574,
    ]
    for i in range(0, 32, 4):
        state.append(int.from_bytes(key[i:i + 4], "little", signed=False))
    state.append(counter & 0xffffffff)
    state.append(int.from_bytes(nonce[0:4], "little", signed=False))
    state.append(int.from_bytes(nonce[4:8], "little", signed=False))
    state.append(int.from_bytes(nonce[8:12], "little", signed=False))
    working = state[:]
    for _ in range(10):
        working[0], working[4], working[8], working[12] = quarter_round(working[0], working[4], working[8], working[12])
        working[1], working[5], working[9], working[13] = quarter_round(working[1], working[5], working[9], working[13])
        working[2], working[6], working[10], working[14] = quarter_round(working[2], working[6], working[10], working[14])
        working[3], working[7], working[11], working[15] = quarter_round(working[3], working[7], working[11], working[15])
        working[0], working[5], working[10], working[15] = quarter_round(working[0], working[5], working[10], working[15])
        working[1], working[6], working[11], working[12] = quarter_round(working[1], working[6], working[11], working[12])
        working[2], working[7], working[8], working[13] = quarter_round(working[2], working[7], working[8], working[13])
        working[3], working[4], working[9], working[14] = quarter_round(working[3], working[4], working[9], working[14])
    out = bytearray(64)
    for i in range(16):
        value = (working[i] + state[i]) & 0xffffffff
        out[i * 4:i * 4 + 4] = value.to_bytes(4, "little", signed=False)
    return bytes(out)


def chacha20_xor_keystream(src, key, nonce, counter):
    out = bytearray(len(src))
    offset = 0
    while offset < len(src):
        block = chacha20_block(key, counter, nonce)
        n = min(64, len(src) - offset)
        for i in range(n):
            out[offset + i] = src[offset + i] ^ block[i]
        offset += n
        counter = (counter + 1) & 0xffffffff
    return bytes(out)


def poly1305_sum(msg, key):
    r0 = key[0] | (key[1] << 8) | (key[2] << 16) | (key[3] << 24)
    r1 = (key[3] >> 2) | (key[4] << 6) | (key[5] << 14) | (key[6] << 22)
    r2 = (key[6] >> 4) | (key[7] << 4) | (key[8] << 12) | (key[9] << 20)
    r3 = (key[9] >> 6) | (key[10] << 2) | (key[11] << 10) | (key[12] << 18)
    r4 = (key[12] >> 8) | (key[13] << 0) | (key[14] << 8) | (key[15] << 16)
    r0 &= 0x3ffffff
    r1 &= 0x3ffff03
    r2 &= 0x3ffc0ff
    r3 &= 0x3f03fff
    r4 &= 0x00fffff
    s1 = r1 * 5
    s2 = r2 * 5
    s3 = r3 * 5
    s4 = r4 * 5
    h0 = h1 = h2 = h3 = h4 = 0
    offset = 0
    while offset < len(msg):
        block = bytearray(16)
        n = min(16, len(msg) - offset)
        block[:n] = msg[offset:offset + n]
        if n == 16:
            hibit = 1 << 24
        else:
            block[n] = 1
            hibit = 0
        t0 = block[0] | (block[1] << 8) | (block[2] << 16) | (block[3] << 24)
        t1 = (block[3] >> 2) | (block[4] << 6) | (block[5] << 14) | (block[6] << 22)
        t2 = (block[6] >> 4) | (block[7] << 4) | (block[8] << 12) | (block[9] << 20)
        t3 = (block[9] >> 6) | (block[10] << 2) | (block[11] << 10) | (block[12] << 18)
        t4 = (block[12] >> 8) | (block[13] << 0) | (block[14] << 8) | (block[15] << 16)
        h0 += t0 & 0x3ffffff
        h1 += t1 & 0x3ffffff
        h2 += t2 & 0x3ffffff
        h3 += t3 & 0x3ffffff
        h4 += (t4 & 0x3ffffff) + hibit
        d0 = h0 * r0 + h1 * s4 + h2 * s3 + h3 * s2 + h4 * s1
        d1 = h0 * r1 + h1 * r0 + h2 * s4 + h3 * s3 + h4 * s2
        d2 = h0 * r2 + h1 * r1 + h2 * r0 + h3 * s4 + h4 * s3
        d3 = h0 * r3 + h1 * r2 + h2 * r1 + h3 * r0 + h4 * s4
        d4 = h0 * r4 + h1 * r3 + h2 * r2 + h3 * r1 + h4 * r0
        h0 = d0 & 0x3ffffff
        d1 += d0 >> 26
        h1 = d1 & 0x3ffffff
        d2 += d1 >> 26
        h2 = d2 & 0x3ffffff
        d3 += d2 >> 26
        h3 = d3 & 0x3ffffff
        d4 += d3 >> 26
        h4 = d4 & 0x3ffffff
        h0 += (d4 >> 26) * 5
        h1 += h0 >> 26
        h0 &= 0x3ffffff
        offset += n
    h2 += h1 >> 26
    h1 &= 0x3ffffff
    h3 += h2 >> 26
    h2 &= 0x3ffffff
    h4 += h3 >> 26
    h3 &= 0x3ffffff
    h0 += (h4 >> 26) * 5
    h4 &= 0x3ffffff
    h1 += h0 >> 26
    h0 &= 0x3ffffff
    g0 = h0 + 5
    g1 = h1
    g2 = h2
    g3 = h3
    g4 = h4
    g1 += g0 >> 26
    g0 &= 0x3ffffff
    g2 += g1 >> 26
    g1 &= 0x3ffffff
    g3 += g2 >> 26
    g2 &= 0x3ffffff
    g4 += g3 >> 26
    g3 &= 0x3ffffff
    g4 -= 1 << 26
    if (g4 >> 63) == 0:
        h0, h1, h2, h3, h4 = g0, g1, g2, g3, g4
    f0 = (h0 | (h1 << 26)) & 0xffffffff
    f1 = ((h1 >> 6) | (h2 << 20)) & 0xffffffff
    f2 = ((h2 >> 12) | (h3 << 14)) & 0xffffffff
    f3 = ((h3 >> 18) | (h4 << 8)) & 0xffffffff
    s0 = int.from_bytes(key[16:20], "little", signed=False)
    s1k = int.from_bytes(key[20:24], "little", signed=False)
    s2k = int.from_bytes(key[24:28], "little", signed=False)
    s3k = int.from_bytes(key[28:32], "little", signed=False)
    f0 += s0
    f1 += s1k + (f0 >> 32)
    f0 &= 0xffffffff
    f2 += s2k + (f1 >> 32)
    f1 &= 0xffffffff
    f3 += s3k + (f2 >> 32)
    f2 &= 0xffffffff
    f3 &= 0xffffffff
    out = bytearray(16)
    out[0:4] = f0.to_bytes(4, "little", signed=False)
    out[4:8] = f1.to_bytes(4, "little", signed=False)
    out[8:12] = f2.to_bytes(4, "little", signed=False)
    out[12:16] = f3.to_bytes(4, "little", signed=False)
    return bytes(out)


def build_poly1305_data(aad, ciphertext):
    size = len(aad)
    if size % 16 != 0:
        size += 16 - (size % 16)
    size += len(ciphertext)
    if len(ciphertext) % 16 != 0:
        size += 16 - (len(ciphertext) % 16)
    size += 16
    out = bytearray()
    out += aad
    if len(aad) % 16 != 0:
        out += b"\x00" * (16 - (len(aad) % 16))
    out += ciphertext
    if len(ciphertext) % 16 != 0:
        out += b"\x00" * (16 - (len(ciphertext) % 16))
    out += len(aad).to_bytes(8, "little", signed=False)
    out += len(ciphertext).to_bytes(8, "little", signed=False)
    return bytes(out)


def chacha20poly1305_seal(key, nonce, plaintext):
    block0 = chacha20_block(key, 0, nonce)
    otk = block0[:32]
    ciphertext = chacha20_xor_keystream(plaintext, key, nonce, 1)
    mac_data = build_poly1305_data(b"", ciphertext)
    tag = poly1305_sum(mac_data, otk)
    return ciphertext + tag


def chacha20poly1305_open(key, nonce, ciphertext):
    if len(ciphertext) < 16:
        raise ValueError("invalid ciphertext")
    data = ciphertext[:-16]
    tag = ciphertext[-16:]
    block0 = chacha20_block(key, 0, nonce)
    otk = block0[:32]
    mac_data = build_poly1305_data(b"", data)
    expected = poly1305_sum(mac_data, otk)
    if not hmac.compare_digest(tag, expected):
        raise ValueError("invalid ciphertext")
    plaintext = chacha20_xor_keystream(data, key, nonce, 1)
    return plaintext


def encrypt_data(plaintext, key):
    nonce = os.urandom(12)
    ciphertext = chacha20poly1305_seal(key, nonce, plaintext.encode("utf-8"))
    return base64.b64encode(nonce + ciphertext).decode("utf-8")


def decrypt_data(ciphertext_b64, key):
    data = base64.b64decode(ciphertext_b64.encode("utf-8"))
    if len(data) < 12 + 16:
        raise ValueError("invalid ciphertext")
    nonce = data[:12]
    ciphertext = data[12:]
    plaintext = chacha20poly1305_open(key, nonce, ciphertext)
    return plaintext.decode("utf-8")


def generate_random_string(length):
    return "".join(random.choice(string.ascii_letters + string.digits) for _ in range(length))


def read_line(prompt):
    sys.stdout.write(prompt)
    sys.stdout.flush()
    return sys.stdin.readline().rstrip("\n")


initial_payload = base64.b64decode("UkVEUQIAAAACAAAAGgAAAAAAAAABAAEAAAABAAAAEgAAAAkAAAAECAAA")


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
    desktopInfo: Optional[DesktopInfo] = None


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


def has_send_info_type(buffer, target_type):
    if not buffer:
        return False
    offset = 0
    while offset + 6 <= len(buffer):
        type_value = int.from_bytes(buffer[offset:offset + 2], "little", signed=False)
        data_length = int.from_bytes(buffer[offset + 2:offset + 6], "little", signed=False)
        if data_length > 0x7fffffff:
            return False
        if offset + 6 + data_length > len(buffer):
            return False
        if type_value == target_type:
            return True
        offset += 6 + data_length
        if offset + 6 > len(buffer) and offset < len(buffer):
            if all(b == 0 for b in buffer[offset:]):
                return False
    return False


class WSConn:
    def __init__(self, reader, writer):
        self.reader = reader
        self.writer = writer

    async def send_text(self, text):
        await self._send_frame(0x1, text.encode("utf-8"))

    async def send_bytes(self, data):
        await self._send_frame(0x2, data)

    async def recv(self, timeout=None):
        while True:
            try:
                fin, opcode, payload = await self._read_frame(timeout)
            except asyncio.TimeoutError:
                return None
            if opcode == 0x8:
                await self.close()
                raise ConnectionError("websocket closed")
            if opcode == 0x9:
                await self._send_frame(0xA, payload)
                continue
            if opcode == 0xA:
                continue
            if opcode == 0x1:
                return payload.decode("utf-8", errors="ignore")
            if opcode == 0x2:
                return payload
            if opcode == 0x0 and fin:
                return payload

    async def close(self):
        try:
            self.writer.close()
            if hasattr(self.writer, "wait_closed"):
                await self.writer.wait_closed()
        except Exception:
            pass

    async def _read_exactly(self, n, timeout):
        if timeout is None:
            return await self.reader.readexactly(n)
        return await asyncio.wait_for(self.reader.readexactly(n), timeout)

    async def _read_frame(self, timeout):
        header = await self._read_exactly(2, timeout)
        b0 = header[0]
        b1 = header[1]
        fin = (b0 & 0x80) != 0
        opcode = b0 & 0x0f
        masked = (b1 & 0x80) != 0
        length = b1 & 0x7f
        if length == 126:
            ext = await self._read_exactly(2, timeout)
            length = int.from_bytes(ext, "big", signed=False)
        elif length == 127:
            ext = await self._read_exactly(8, timeout)
            length = int.from_bytes(ext, "big", signed=False)
        mask_key = b""
        if masked:
            mask_key = await self._read_exactly(4, timeout)
        payload = b""
        if length:
            payload = await self._read_exactly(length, timeout)
        if masked and payload:
            payload = bytes(b ^ mask_key[i % 4] for i, b in enumerate(payload))
        return fin, opcode, payload

    async def _send_frame(self, opcode, payload):
        fin_opcode = 0x80 | (opcode & 0x0f)
        length = len(payload)
        header = bytearray()
        header.append(fin_opcode)
        if length < 126:
            header.append(0x80 | length)
        elif length < (1 << 16):
            header.append(0x80 | 126)
            header.extend(length.to_bytes(2, "big", signed=False))
        else:
            header.append(0x80 | 127)
            header.extend(length.to_bytes(8, "big", signed=False))
        mask_key = os.urandom(4)
        masked_payload = bytes(b ^ mask_key[i % 4] for i, b in enumerate(payload))
        self.writer.write(bytes(header) + mask_key + masked_payload)
        await self.writer.drain()


async def ws_connect(uri, origin, subprotocol):
    parsed = urllib.parse.urlparse(uri)
    scheme = parsed.scheme.lower()
    host = parsed.hostname
    if not host:
        raise ValueError("invalid websocket uri")
    port = parsed.port
    if port is None:
        port = 443 if scheme == "wss" else 80
    path = parsed.path or "/"
    if parsed.query:
        path += "?" + parsed.query
    ssl_ctx = None
    if scheme == "wss":
        ssl_ctx = ssl.create_default_context()
    reader, writer = await asyncio.open_connection(host, port, ssl=ssl_ctx, server_hostname=host if ssl_ctx else None)
    key = base64.b64encode(os.urandom(16)).decode("ascii")
    request = [
        f"GET {path} HTTP/1.1",
        f"Host: {parsed.netloc}",
        "Upgrade: websocket",
        "Connection: Upgrade",
        f"Sec-WebSocket-Key: {key}",
        "Sec-WebSocket-Version: 13",
    ]
    if origin:
        request.append(f"Origin: {origin}")
    if subprotocol:
        request.append(f"Sec-WebSocket-Protocol: {subprotocol}")
    request.append("\r\n")
    writer.write("\r\n".join(request).encode("utf-8"))
    await writer.drain()
    status_code, headers = await _read_http_response(reader)
    if status_code != 101:
        writer.close()
        if hasattr(writer, "wait_closed"):
            await writer.wait_closed()
        raise ConnectionError(f"websocket handshake failed: {status_code}")
    accept = headers.get("sec-websocket-accept", "")
    expected = base64.b64encode(hashlib.sha1((key + "258EAFA5-E914-47DA-95CA-C5AB0DC85B11").encode("ascii")).digest()).decode("ascii")
    if accept != expected:
        writer.close()
        if hasattr(writer, "wait_closed"):
            await writer.wait_closed()
        raise ConnectionError("websocket handshake validation failed")
    return WSConn(reader, writer)


async def _read_http_response(reader):
    data = await reader.readuntil(b"\r\n\r\n")
    text = data.decode("iso-8859-1")
    lines = text.split("\r\n")
    status_line = lines[0].strip()
    parts = status_line.split(" ", 2)
    status_code = 0
    if len(parts) >= 2 and parts[1].isdigit():
        status_code = int(parts[1])
    headers = {}
    for line in lines[1:]:
        if not line:
            continue
        if ":" not in line:
            continue
        name, value = line.split(":", 1)
        headers[name.strip().lower()] = value.strip()
    return status_code, headers


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


def decode_first_account(accounts, system_fingerprint):
    if not accounts or not accounts.get("salt") or not accounts.get("accounts"):
        return None
    key = derive_key(system_fingerprint, accounts.get("salt"))
    for account in accounts.get("accounts", []):
        try:
            user = decrypt_data(account.get("user_account", ""), key)
            password = decrypt_data(account.get("password", ""), key)
            device_code = decrypt_data(account.get("device_code", ""), key)
            if user and device_code:
                return user, password, device_code
        except Exception:
            continue
    return None


def resolve_credentials():
    system_fingerprint = get_system_fingerprint()
    config_file = "config.json"
    while True:
        accounts = {}
        if os.path.exists(config_file):
            try:
                with open(config_file, "r", encoding="utf-8") as f:
                    accounts = json.load(f)
                result = decode_first_account(accounts, system_fingerprint)
                if result:
                    return result
                write_line("config.json 解码失败，进入手动录入")
            except Exception as ex:
                write_line(f"解析 config.json 失败: {ex}")
        salt = generate_salt()
        key = derive_key(system_fingerprint, salt)
        accounts = {"salt": salt, "accounts": []}
        while True:
            device_code = "web_" + generate_random_string(32)
            user = read_line("账号: ")
            pwd = read_line("密码: ")
            if not user or not pwd:
                write_line("账号或密码不能为空")
                continue
            try:
                encoded_user = encrypt_data(user, key)
                encoded_password = encrypt_data(pwd, key)
                encoded_device_code = encrypt_data(device_code, key)
            except Exception:
                write_line("配置加密失败")
                continue
            accounts["accounts"].append({
                "user_account": encoded_user,
                "password": encoded_password,
                "device_code": encoded_device_code,
            })
            continue_input = read_line("是否继续添加账户? (y/n): ")
            if continue_input.strip().lower() != "y":
                break
        if not accounts["accounts"]:
            continue
        try:
            with open(config_file, "w", encoding="utf-8") as f:
                json.dump(accounts, f, ensure_ascii=False, indent=2)
        except Exception:
            write_line("配置写入失败，重新录入")
            continue
        result = decode_first_account(accounts, system_fingerprint)
        if result:
            return result
        write_line("配置写入后解码失败，重新录入")


async def receive_loop(ws, desktop, encryptor, user_payload, stop_event):
    while not stop_event.is_set():
        message = await ws.recv(timeout=1.0)
        if message is None:
            continue
        if isinstance(message, str):
            continue
        if message[:4] == b"REDQ":
            write_line(f"[{desktop.desktopCode}] -> 收到保活校验")
            response = encryptor.execute(message)
            await ws.send_bytes(response)
            write_line(f"[{desktop.desktopCode}] -> 发送保活响应成功")
            continue
        if user_payload and has_send_info_type(message, 103):
            await ws.send_bytes(user_payload)


async def keep_alive_worker(desktop, api, user_payload, stop_event):
    clink_host = desktop.desktopInfo.clinkLvsOutHost or ""
    if clink_host:
        uri_host = clink_host
    else:
        uri_host = f"{desktop.desktopInfo.host}:{desktop.desktopInfo.port}"
    uri = f"wss://{uri_host}/clinkProxy/{desktop.desktopId}/MAIN"
    while not stop_event.is_set():
        try:
            write_line(f"[{desktop.desktopCode}] === 新周期开始，尝试连接 ===")
            ws = await ws_connect(uri, "https://pc.ctyun.cn", "binary")
            try:
                host = desktop.desktopInfo.host
                port = desktop.desktopInfo.port
                if clink_host:
                    if ":" in clink_host:
                        host, port = clink_host.split(":", 1)
                    else:
                        host = clink_host
                connect_message = {
                    "type": 1,
                    "ssl": 1,
                    "host": host,
                    "port": port,
                    "ca": desktop.desktopInfo.caCert,
                    "cert": desktop.desktopInfo.clientCert,
                    "key": desktop.desktopInfo.clientKey,
                    "servername": f"{desktop.desktopInfo.host}:{desktop.desktopInfo.port}",
                    "oqs": 0,
                }
                await ws.send_text(json.dumps(connect_message))
                await asyncio.sleep(0.5)
                await ws.send_bytes(initial_payload)
                write_line(f"[{desktop.desktopCode}] 连接已就绪，保持 60 秒...")
                try:
                    await asyncio.wait_for(receive_loop(ws, desktop, Encryption(), user_payload, stop_event), timeout=60)
                except asyncio.TimeoutError:
                    write_line(f"[{desktop.desktopCode}] 60秒时间到，准备重连...")
            finally:
                await ws.close()
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
    user_payload = b""
    if api.login_info:
        user_json = json.dumps({
            "type": 1,
            "userName": api.login_info.userName,
            "userInfo": "",
            "userId": api.login_info.userId,
        }, ensure_ascii=False)
        user_payload = SendInfo(118, user_json.encode("utf-8")).to_buffer(True)
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

    tasks = [keep_alive_worker(d, api, user_payload, stop_event) for d in active_desktops]
    try:
        await asyncio.gather(*tasks)
    except asyncio.CancelledError:
        write_line("程序已停止。")


if __name__ == "__main__":
    if sys.version_info < (3, 8):
        write_line("需要 Python 3.8+")
        sys.exit(1)
    asyncio.run(main())
