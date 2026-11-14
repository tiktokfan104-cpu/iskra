#!/usr/bin/env python3
"""Сервер мессенджера «Искра».

Только стандартная библиотека Python 3.8+, ничего устанавливать не нужно.
Вход по номеру телефона и паролю (без SMS), чаты, статус прочтения, индикатор набора.
Клиент (index.html) лежит рядом и отдаётся этим же сервером.

Запуск:  python server.py   (на Mac/Linux: python3 server.py)
Админы: в окне запущенного сервера введите  admin +380XXXXXXXXX
        (или, пока сервер остановлен:  python server.py admin +380XXXXXXXXX)
"""

import base64
import hashlib
import hmac
import json
import os
import re
import secrets
import socket
import sys
import threading
import time
import urllib.parse
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

BASE = Path(__file__).resolve().parent

# ---------- Настройки (переменные окружения) ----------
PORT = int(os.environ.get("PORT", "3000"))
# 127.0.0.1 = только этот компьютер. Для проверки с телефона в одной Wi-Fi сети
# можно задать HOST=0.0.0.0, но только в тестовом режиме и в доверенной сети.
HOST = os.environ.get("HOST", "127.0.0.1")
DATA_FILE = Path(os.environ.get("DATA_FILE", BASE / "data.json"))

# Админ-аккаунт: телефон и пароль задаются ТОЛЬКО переменными окружения.
# Номер никогда не хранится в коде. Пока ADMIN_PASSWORD не задан, вход в админку отключён.
ADMIN_PHONE_RAW = os.environ.get("ADMIN_PHONE", "")
ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD", "")
# Если сервер стоит за прокси хостинга (Render, Replit и т.п.), задайте TRUST_PROXY=1,
# чтобы лимиты считались по настоящему IP людей, а не по IP прокси.
# Локальный Cloudflare Tunnel определяется автоматически.
TRUST_PROXY = os.environ.get("TRUST_PROXY", "") == "1"
STARTED = time.time()

MIN_PASSWORD = 8
MAX_PASSWORD = 128
MAX_FAILS_PER_PHONE = 8    # неверных паролей на один номер за 15 минут
MAX_AUTH_PER_IP = 30       # попыток входа с одного IP за 10 минут
MAX_REG_PER_IP = 10        # регистраций с одного IP в час
MAX_TEXT = 4000
MAX_BODY = 48 * 1024
MAX_AVATAR = 30 * 1024     # размер фото профиля (JPEG), байт
TYPING_TTL = 4             # сколько секунд виден «печатает…»
RATE_LIMIT_PER_MIN = 300   # запросов к API в минуту с одного IP

lock = threading.RLock()

# ---------- Хранилище (JSON-файл) ----------
db = {"users": {}, "sessions": {}, "messages": [], "reads": {}, "contacts": {}, "blocks": {}, "seq": 0}
try:
    loaded = json.loads(DATA_FILE.read_text(encoding="utf-8"))
    db.update(loaded)
except (OSError, ValueError):
    pass  # первый запуск

by_id = {u["id"]: u for u in db["users"].values()}
by_username = {u["username"]: u for u in db["users"].values() if u.get("username")}
USERNAME_RE = re.compile(r"^[a-z][a-z0-9_]{2,23}$")
RESERVED_NAMES = {"admin", "administrator", "support", "iskra", "system", "root", "moderator"}


def save_db():
    with lock:
        tmp = DATA_FILE.with_name(DATA_FILE.name + ".tmp")
        tmp.write_text(json.dumps(db, ensure_ascii=False), encoding="utf-8")
        os.replace(tmp, DATA_FILE)


def sha(s):
    return hashlib.sha256(str(s).encode()).hexdigest()


def hash_password(password):
    salt = secrets.token_bytes(16)
    if hasattr(hashlib, "scrypt"):
        n, r, p = 2 ** 14, 8, 1
        dk = hashlib.scrypt(password.encode(), salt=salt, n=n, r=r, p=p, dklen=32)
        return f"scrypt${n}${r}${p}${salt.hex()}${dk.hex()}"
    iters = 400_000
    dk = hashlib.pbkdf2_hmac("sha256", password.encode(), salt, iters, 32)
    return f"pbkdf2${iters}${salt.hex()}${dk.hex()}"


def verify_password(password, stored):
    try:
        parts = str(stored or "").split("$")
        if parts[0] == "scrypt":
            _, n, r, p, salt, dk = parts
            calc = hashlib.scrypt(password.encode(), salt=bytes.fromhex(salt), n=int(n), r=int(r), p=int(p), dklen=len(dk) // 2)
        elif parts[0] == "pbkdf2":
            _, iters, salt, dk = parts
            calc = hashlib.pbkdf2_hmac("sha256", password.encode(), bytes.fromhex(salt), int(iters), len(dk) // 2)
        else:
            return False
        return hmac.compare_digest(calc.hex(), dk)
    except (ValueError, TypeError):
        return False


DUMMY_HASH = hash_password("iskra-dummy-password")  # чтобы вход несуществующего номера занимал столько же времени


def public_user(u):
    """То, что видят ДРУГИЕ люди. Номер телефона сюда не входит."""
    return {"id": u["id"], "name": u["name"], "username": u.get("username", ""), "avatarV": u.get("avatarV", "")}


def normalize_phone(raw):
    digits = "".join(ch for ch in str(raw or "") if ch.isdigit())
    if len(digits) < 10 or len(digits) > 15:
        return None
    return "+" + digits


ADMIN_PHONE = normalize_phone(ADMIN_PHONE_RAW)


def is_admin(u):
    """Админ: главный (ADMIN_PHONE из окружения) или тот, кому права выданы командой в терминале."""
    return (bool(ADMIN_PHONE) and u["phone"] == ADMIN_PHONE) or bool(u.get("admin"))


def self_user(u):
    """Профиль для самого пользователя: с флагом админа."""
    return {**public_user(u), "phone": u["phone"], "isAdmin": is_admin(u)}


# ---------- Состояние в памяти ----------
typing = {}      # (от кого, кому) -> время
hits = {}        # ip -> [время запроса, ...]
auth_hits = {}   # ip -> [время попытки входа/регистрации, ...]
reg_hits = {}    # ip -> [время регистрации, ...]
fails = {}       # phone -> [время неверного пароля, ...]
last_seen = {}   # id пользователя -> время последнего sync


def prune(d, now, window):
    """Чистит словарь «ключ -> список времён», чтобы он не рос бесконечно."""
    if len(d) > 5000:
        for k in [k for k, v in d.items() if not v or now - v[-1] > window]:
            del d[k]


class ApiError(Exception):
    def __init__(self, status, message, **extra):
        super().__init__(message)
        self.status = status
        self.message = message
        self.extra = extra


# ---------- Логика API ----------
def check_password_rules(password):
    if not isinstance(password, str) or len(password) < MIN_PASSWORD:
        raise ApiError(400, f"Пароль должен быть не короче {MIN_PASSWORD} символов.")
    if len(password) > MAX_PASSWORD:
        raise ApiError(400, "Пароль слишком длинный.")


def new_session(user):
    token = secrets.token_hex(32)
    db["sessions"][sha(token)] = user["id"]
    return token


def api_phone_status(body, ip):
    """Шаг 1 входа: человек ввёл номер. Новый номер -> экран «придумайте пароль», известный -> «введите пароль»."""
    phone = normalize_phone(body.get("phone"))
    if not phone:
        raise ApiError(400, "Неверный номер телефона")
    now = time.time()
    with lock:
        lst = [t for t in auth_hits.get(ip, []) if now - t < 600]
        if len(lst) >= MAX_AUTH_PER_IP:
            raise ApiError(429, "Слишком много попыток. Подождите несколько минут.")
        lst.append(now)
        auth_hits[ip] = lst
        prune(auth_hits, now, 600)
        exists = phone == ADMIN_PHONE or phone in db["users"]
    return {"exists": exists}


def api_register(body, ip):
    phone = normalize_phone(body.get("phone"))
    if not phone:
        raise ApiError(400, "Неверный номер телефона")
    name = str(body.get("name") or "").strip()[:60]
    if not name:
        raise ApiError(400, "Введите имя.")
    password = body.get("password")
    check_password_rules(password)
    now = time.time()
    with lock:
        lst = [t for t in reg_hits.get(ip, []) if now - t < 3600]
        if len(lst) >= MAX_REG_PER_IP:
            raise ApiError(429, "Слишком много регистраций с вашего адреса. Попробуйте позже.")
        lst.append(now)
        reg_hits[ip] = lst
        prune(reg_hits, now, 3600)
    pwhash = hash_password(password)  # тяжёлая операция: вне общей блокировки
    with lock:
        if phone == ADMIN_PHONE or phone in db["users"]:
            raise ApiError(409, "Этот номер уже зарегистрирован. Войдите с паролем.")
        user = {"id": secrets.token_hex(8), "phone": phone, "name": name, "pwhash": pwhash, "createdAt": int(now)}
        db["users"][phone] = user
        by_id[user["id"]] = user
        token = new_session(user)
        save_db()
    return {"token": token, "user": self_user(user)}


def api_login(body, ip):
    phone = normalize_phone(body.get("phone"))
    password = body.get("password")
    if not phone or not isinstance(password, str) or len(password) > MAX_PASSWORD:
        raise ApiError(400, "Неверный номер или пароль.")
    now = time.time()
    with lock:
        lst = [t for t in auth_hits.get(ip, []) if now - t < 600]
        if len(lst) >= MAX_AUTH_PER_IP:
            raise ApiError(429, "Слишком много попыток входа. Подождите несколько минут.")
        lst.append(now)
        auth_hits[ip] = lst
        prune(auth_hits, now, 600)
        recent = [t for t in fails.get(phone, []) if now - t < 900]
        fails[phone] = recent
        if len(recent) >= MAX_FAILS_PER_PHONE:
            raise ApiError(429, "Слишком много неверных паролей. Подождите 15 минут.")
        user = db["users"].get(phone)
        stored = user.get("pwhash") if user else None
    ok = verify_password(password, stored or DUMMY_HASH) and bool(stored)  # вне блокировки
    if not ok:
        with lock:
            fails.setdefault(phone, []).append(time.time())
            prune(fails, now, 900)
        raise ApiError(400, "Неверный номер или пароль.")
    with lock:
        if user.get("banned"):
            raise ApiError(403, "Аккаунт заблокирован")
        fails.pop(phone, None)
        token = new_session(user)
        save_db()
    return {"token": token, "user": self_user(user)}


def api_password(user, body, token):
    """Смена пароля. Старые аккаунты без пароля могут просто задать его (они уже вошли)."""
    new = body.get("new")
    check_password_rules(new)
    if user.get("pwhash"):
        old = body.get("old")
        if not isinstance(old, str) or not verify_password(old, user["pwhash"]):
            raise ApiError(400, "Текущий пароль неверный.")
    pwhash = hash_password(new)
    with lock:
        user["pwhash"] = pwhash
        keep = sha(token)
        for k in [k for k, v in db["sessions"].items() if v == user["id"] and k != keep]:
            del db["sessions"][k]  # остальные устройства выйдут
        save_db()
    return {"ok": True}


def ensure_admin():
    """Админ-аккаунт создаётся и защищается паролем из окружения, а не регистрацией:
    так никто не сможет занять номер администратора."""
    if not ADMIN_PHONE:
        return
    if not ADMIN_PASSWORD:
        print("ВНИМАНИЕ: ADMIN_PASSWORD не задан, вход в админ-аккаунт отключён.", flush=True)
        return
    check_password_rules(ADMIN_PASSWORD)
    pwhash = hash_password(ADMIN_PASSWORD)
    with lock:
        u = db["users"].get(ADMIN_PHONE)
        if not u:
            u = {"id": secrets.token_hex(8), "phone": ADMIN_PHONE, "name": "Администратор", "createdAt": int(time.time())}
            db["users"][ADMIN_PHONE] = u
            by_id[u["id"]] = u
        u["pwhash"] = pwhash
        u.pop("banned", None)
        save_db()


def api_sync(user, qs):
    try:
        after = int(qs.get("after", ["0"])[0] or 0)
    except ValueError:
        after = 0
    me = user["id"]
    now = time.time()
    with lock:
        fresh = []
        for m in reversed(db["messages"]):
            if m["seq"] <= after:
                break
            if m["from"] == me or m["to"] == me:
                fresh.append(m)
                if after == 0 and len(fresh) >= 1000:
                    break
        fresh.reverse()
        contact_ids = list(db["contacts"].get(me, []))
        users = [public_user(by_id[i]) for i in contact_ids if i in by_id]
        reads = {r: rd[me] for r, rd in db["reads"].items() if me in rd}
        my_reads = dict(db["reads"].get(me, {}))
        blocks = list(db["blocks"].get(me, []))
        for k in [k for k, t in typing.items() if now - t > TYPING_TTL]:
            del typing[k]
        typ = {frm: True for (frm, to) in typing if to == me}
        seq = db["seq"]
        last_seen[me] = now
    return {
        "user": self_user(user),
        "users": users,
        "contacts": contact_ids,
        "messages": fresh,
        "reads": reads,
        "myReads": my_reads,
        "typing": typ,
        "blocks": blocks,
        "seq": seq,
    }


def api_block(user, body):
    pid = str(body.get("id") or "")
    if pid not in by_id or pid == user["id"]:
        raise ApiError(404, "Пользователь не найден")
    with lock:
        lst = db["blocks"].setdefault(user["id"], [])
        if body.get("blocked"):
            if pid not in lst:
                lst.append(pid)
        elif pid in lst:
            lst.remove(pid)
        save_db()
    return {"ok": True}


def api_profile(user, body):
    with lock:
        name = user["name"]
        if "name" in body:
            name = str(body.get("name") or "").strip()[:60]
            if not name:
                raise ApiError(400, "Введите имя.")
        un = user.get("username", "")
        if "username" in body:
            un = str(body.get("username") or "").strip().lstrip("@").lower()
            if un:
                if not USERNAME_RE.match(un):
                    raise ApiError(400, "Имя пользователя: 3–24 символа, латинские буквы, цифры и _. Начинается с буквы.")
                if un in RESERVED_NAMES and not is_admin(user):
                    raise ApiError(400, "Это имя зарезервировано.")
                owner = by_username.get(un)
                if owner and owner["id"] != user["id"]:
                    raise ApiError(409, "Это имя уже занято.")
        avatar = user.get("avatar", "")
        if "avatar" in body:
            raw = str(body.get("avatar") or "")
            if raw:
                prefix = "data:image/jpeg;base64,"
                if not raw.startswith(prefix):
                    raise ApiError(400, "Нужна картинка JPEG.")
                try:
                    img = base64.b64decode(raw[len(prefix):], validate=True)
                except ValueError:
                    raise ApiError(400, "Не удалось прочитать картинку.")
                if len(img) > MAX_AVATAR or img[:3] != b"\xff\xd8\xff":
                    raise ApiError(400, "Картинка слишком большая или повреждена.")
            avatar = raw
        old = user.get("username", "")
        if old and old != un:
            by_username.pop(old, None)
        if un:
            user["username"] = un
            by_username[un] = user
        else:
            user.pop("username", None)
        user["name"] = name
        if avatar:
            user["avatar"] = avatar
            user["avatarV"] = sha(avatar)[:8]
        else:
            user.pop("avatar", None)
            user.pop("avatarV", None)
        save_db()
    return {"user": self_user(user)}


def api_add_contact(user, body):
    q = str(body.get("query") or "").strip().lstrip("@").lower()
    if not USERNAME_RE.match(q):
        raise ApiError(400, "Введите @имя пользователя (латиница, цифры и _).")
    with lock:
        peer = by_username.get(q)
        if not peer:
            raise ApiError(404, "Пользователя с таким @именем нет в Искре.")
        if peer["id"] == user["id"]:
            raise ApiError(400, "Это вы. Личные заметки уже есть в «Избранном».")
        lst = db["contacts"].setdefault(user["id"], [])
        if peer["id"] not in lst:
            lst.append(peer["id"])
            save_db()
    return {"user": public_user(peer)}


def add_message(frm, to, text):
    """Добавляет сообщение. Вызывать под lock, затем save_db()."""
    db["seq"] += 1
    msg = {
        "seq": db["seq"],
        "id": secrets.token_hex(8),
        "from": frm,
        "to": to,
        "text": text,
        "ts": int(time.time() * 1000),
    }
    db["messages"].append(msg)
    # Чтобы диалог появился у обоих.
    for owner, other in ((frm, to), (to, frm)):
        if owner != other:
            lst = db["contacts"].setdefault(owner, [])
            if other not in lst:
                lst.append(other)
    typing.pop((frm, to), None)
    return msg


def api_send(user, body):
    to = str(body.get("to") or "")
    text = str(body.get("text") or "").strip()[:MAX_TEXT]
    if not text:
        raise ApiError(400, "Пустое сообщение")
    with lock:
        if to not in by_id:
            raise ApiError(404, "Получатель не найден")
        if user["id"] in db["blocks"].get(to, []):
            raise ApiError(403, "Пользователь не принимает сообщения от вас.")
        if to in db["blocks"].get(user["id"], []):
            raise ApiError(403, "Вы заблокировали этого пользователя. Разблокируйте, чтобы писать.")
        msg = add_message(user["id"], to, text)
        save_db()
    return {"message": msg}


def api_read(user, body):
    peer = str(body.get("peer") or "")
    try:
        upto = int(body.get("upto") or 0)
    except (TypeError, ValueError):
        raise ApiError(400, "Неверные данные")
    with lock:
        if peer not in by_id:
            raise ApiError(404, "Пользователь не найден")
        rd = db["reads"].setdefault(user["id"], {})
        if upto > rd.get(peer, 0):
            rd[peer] = min(upto, db["seq"])
            save_db()
    return {"ok": True}


def api_typing(user, body):
    to = str(body.get("to") or "")
    with lock:
        if to in by_id and to != user["id"] and user["id"] not in db["blocks"].get(to, []):
            typing[(user["id"], to)] = time.time()
    return {"ok": True}


def api_logout(user, token):
    with lock:
        db["sessions"].pop(sha(token), None)
        save_db()
    return {"ok": True}


# ---------- Админ-панель ----------
def require_admin(user):
    if not is_admin(user):
        raise ApiError(404, "Не найдено")  # для остальных страницы как будто нет


def admin_target(body):
    """Пользователь, над которым действие. Себя трогать нельзя."""
    uid = str(body.get("id") or "")
    target = by_id.get(uid)
    if not target:
        raise ApiError(404, "Пользователь не найден")
    if is_admin(target):
        raise ApiError(400, "С собственным аккаунтом так нельзя")
    return target


def drop_sessions(uid):
    for k in [k for k, v in db["sessions"].items() if v == uid]:
        del db["sessions"][k]


def api_admin_overview(user):
    require_admin(user)
    now = time.time()
    with lock:
        msg_count, sess_count = {}, {}
        for m in db["messages"]:
            msg_count[m["from"]] = msg_count.get(m["from"], 0) + 1
        for uid in db["sessions"].values():
            sess_count[uid] = sess_count.get(uid, 0) + 1
        rows = []
        for u in db["users"].values():
            rows.append({
                **public_user(u),
                "phone": u["phone"],
                "createdAt": u.get("createdAt", 0),
                "banned": bool(u.get("banned")),
                "isAdmin": is_admin(u),
                "sent": msg_count.get(u["id"], 0),
                "sessions": sess_count.get(u["id"], 0),
                "online": now - last_seen.get(u["id"], 0) < 10,
            })
        rows.sort(key=lambda r: r["createdAt"], reverse=True)
        return {
            "users": rows,
            "messages": len(db["messages"]),
            "sessions": len(db["sessions"]),
            "banned": sum(1 for r in rows if r["banned"]),
            "online": sum(1 for r in rows if r["online"]),
            "devSms": False,
            "uptimeSec": int(now - STARTED),
        }


def api_admin_ban(user, body):
    require_admin(user)
    target = admin_target(body)
    with lock:
        target["banned"] = bool(body.get("banned"))
        if target["banned"]:
            drop_sessions(target["id"])
        save_db()
    return {"ok": True}


def api_admin_kick(user, body):
    require_admin(user)
    target = admin_target(body)
    with lock:
        drop_sessions(target["id"])
        save_db()
    return {"ok": True}


def api_admin_rename(user, body):
    require_admin(user)
    target = admin_target(body)
    name = str(body.get("name") or "").strip()[:60]
    if not name:
        raise ApiError(400, "Имя не может быть пустым")
    with lock:
        target["name"] = name
        save_db()
    return {"ok": True}


def api_admin_delete(user, body):
    require_admin(user)
    target = admin_target(body)
    uid = target["id"]
    with lock:
        drop_sessions(uid)
        db["messages"] = [m for m in db["messages"] if uid not in (m["from"], m["to"])]
        db["contacts"].pop(uid, None)
        for lst in db["contacts"].values():
            if uid in lst:
                lst.remove(uid)
        db["reads"].pop(uid, None)
        db["blocks"].pop(uid, None)
        for lst in db["blocks"].values():
            if uid in lst:
                lst.remove(uid)
        for rd in db["reads"].values():
            rd.pop(uid, None)
        db["users"].pop(target["phone"], None)
        by_id.pop(uid, None)
        by_username.pop(target.get("username", ""), None)
        last_seen.pop(uid, None)
        save_db()
    return {"ok": True}


def api_admin_broadcast(user, body):
    require_admin(user)
    text = str(body.get("text") or "").strip()[:MAX_TEXT]
    if not text:
        raise ApiError(400, "Пустое сообщение")
    with lock:
        targets = [u["id"] for u in db["users"].values() if not is_admin(u) and not u.get("banned")]
        for uid in targets:
            add_message(user["id"], uid, text)
        save_db()
    return {"sent": len(targets)}


# ---------- Команды из терминала ----------
HELP = (
    "Команды:\n"
    "  admin +380XXXXXXXXX    выдать админ-панель пользователю\n"
    "  unadmin +380XXXXXXXXX  забрать админ-панель\n"
    "  admins                 список админов\n"
    "  help                   эта подсказка"
)


def cmd_set_admin(raw, value):
    phone = normalize_phone(raw)
    if not phone:
        return "Неверный номер. Пример: admin +380671234567"
    with lock:
        u = db["users"].get(phone)
        if not u:
            return f"Пользователь {phone} не найден. Он должен сначала зарегистрироваться в Искре."
        if value:
            if is_admin(u):
                return f"{phone} ({u['name']}) уже админ."
            u["admin"] = True
            u.pop("banned", None)
            save_db()
            return f"Готово: {phone} ({u['name']}) теперь админ. Кнопка админ-панели появится у него в течение пары секунд."
        if phone == ADMIN_PHONE:
            return "Главного админа (ADMIN_PHONE) снять нельзя: он задан переменной окружения."
        if not u.get("admin"):
            return f"{phone} ({u['name']}) и так не админ."
        u.pop("admin", None)
        save_db()
        return f"Готово: у {phone} ({u['name']}) больше нет админ-панели."


def cmd_list_admins():
    with lock:
        rows = [f"  {u['phone']}  {u['name']}" + ("  (главный)" if u["phone"] == ADMIN_PHONE else "")
                for u in db["users"].values() if is_admin(u)]
    return "Админы:\n" + "\n".join(rows) if rows else "Админов пока нет."


def run_command(line):
    parts = line.strip().split(None, 1)
    if not parts:
        return ""
    name, arg = parts[0].lower(), (parts[1] if len(parts) > 1 else "")
    if name in ("admin", "grant-admin"):
        return cmd_set_admin(arg, True) if arg else "Укажите номер: admin +380671234567"
    if name in ("unadmin", "revoke-admin"):
        return cmd_set_admin(arg, False) if arg else "Укажите номер: unadmin +380671234567"
    if name in ("admins", "list-admins"):
        return cmd_list_admins()
    if name in ("help", "?"):
        return HELP
    return "Неизвестная команда. Введите help."


def console_loop():
    """Читает команды из терминала, пока работает сервер."""
    print(HELP, flush=True)
    while True:
        try:
            line = sys.stdin.readline()
        except (OSError, ValueError):
            return
        if not line:  # терминал закрыт
            return
        out = run_command(line)
        if out:
            print(out, flush=True)


def server_is_running():
    host = "127.0.0.1" if HOST in ("0.0.0.0", "") else HOST
    try:
        with socket.create_connection((host, PORT), timeout=0.5):
            return True
    except OSError:
        return False


# ---------- HTTP ----------
CSP = (
    "default-src 'self'; script-src 'self' 'unsafe-inline'; "
    "style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; "
    "font-src https://fonts.gstatic.com; img-src 'self' data:; connect-src 'self'; "
    "base-uri 'none'; form-action 'self'; frame-ancestors 'none'"
)


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "Iskra/1.0"
    timeout = 60  # не держать зависшие соединения вечно

    def log_message(self, fmt, *args):
        pass  # тише в консоли

    # --- вспомогательное ---
    def send_bytes(self, status, data, ctype, extra=None):
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        if not extra or "Cache-Control" not in extra:
            self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(data)

    def send_json(self, status, obj):
        self.send_bytes(status, json.dumps(obj, ensure_ascii=False).encode(), "application/json; charset=utf-8")

    def read_body(self):
        try:
            length = int(self.headers.get("Content-Length") or 0)
        except ValueError:
            raise ApiError(400, "Неверный запрос")
        if length > MAX_BODY:
            self.close_connection = True
            raise ApiError(413, "Слишком большой запрос")
        raw = self.rfile.read(length) if length else b"{}"
        try:
            data = json.loads(raw or b"{}")
        except ValueError:
            raise ApiError(400, "Неверный JSON")
        if not isinstance(data, dict):
            raise ApiError(400, "Неверный JSON")
        return data

    def token(self):
        h = self.headers.get("Authorization", "")
        return h[7:] if h.startswith("Bearer ") else ""

    def current_user(self):
        t = self.token()
        uid = t and db["sessions"].get(sha(t))
        user = uid and by_id.get(uid)
        if not user:
            raise ApiError(401, "Нужна авторизация")
        if user.get("banned"):
            raise ApiError(403, "Аккаунт заблокирован")
        return user

    def client_ip(self):
        peer = self.client_address[0]
        if TRUST_PROXY or peer in ("127.0.0.1", "::1"):
            cf = (self.headers.get("CF-Connecting-IP") or "").strip()
            if cf:
                return cf
            xff = (self.headers.get("X-Forwarded-For") or "").split(",")[-1].strip()
            if xff:
                return xff
        return peer

    def rate_limit(self):
        ip = self.client_ip()
        now = time.time()
        with lock:
            lst = [t for t in hits.get(ip, []) if now - t < 60]
            lst.append(now)
            hits[ip] = lst
            prune(hits, now, 60)
        if len(lst) > RATE_LIMIT_PER_MIN:
            raise ApiError(429, "Слишком много запросов")

    def dispatch(self, method):
        url = urllib.parse.urlsplit(self.path)
        path = url.path
        qs = urllib.parse.parse_qs(url.query)
        try:
            if method == "GET" and path in ("/", "/index.html"):
                html = (BASE / "index.html").read_bytes()
                return self.send_bytes(200, html, "text/html; charset=utf-8", {"Content-Security-Policy": CSP})
            if method == "GET" and path.startswith("/avatar/"):
                self.rate_limit()
                owner = by_id.get(path[len("/avatar/"):])
                av = owner.get("avatar") if owner else None
                if not av:
                    raise ApiError(404, "Не найдено")
                return self.send_bytes(200, base64.b64decode(av.split(",", 1)[1]), "image/jpeg",
                                       {"Cache-Control": "public, max-age=31536000, immutable"})
            if not path.startswith("/api/"):
                raise ApiError(404, "Не найдено")
            self.rate_limit()
            if method == "GET":
                if path == "/api/sync":
                    return self.send_json(200, api_sync(self.current_user(), qs))
                if path == "/api/me":
                    return self.send_json(200, self_user(self.current_user()))
                if path == "/api/admin/overview":
                    return self.send_json(200, api_admin_overview(self.current_user()))
            else:
                body = self.read_body()
                if path == "/api/phone-status":
                    return self.send_json(200, api_phone_status(body, self.client_ip()))
                if path == "/api/register":
                    return self.send_json(200, api_register(body, self.client_ip()))
                if path == "/api/login":
                    return self.send_json(200, api_login(body, self.client_ip()))
                user = self.current_user()
                if path == "/api/password":
                    return self.send_json(200, api_password(user, body, self.token()))
                if path == "/api/block":
                    return self.send_json(200, api_block(user, body))
                if path == "/api/profile":
                    return self.send_json(200, api_profile(user, body))
                if path == "/api/send":
                    return self.send_json(200, api_send(user, body))
                if path == "/api/read":
                    return self.send_json(200, api_read(user, body))
                if path == "/api/typing":
                    return self.send_json(200, api_typing(user, body))
                if path == "/api/contacts":
                    return self.send_json(200, api_add_contact(user, body))
                admin_routes = {
                    "/api/admin/ban": api_admin_ban,
                    "/api/admin/kick": api_admin_kick,
                    "/api/admin/rename": api_admin_rename,
                    "/api/admin/delete": api_admin_delete,
                    "/api/admin/broadcast": api_admin_broadcast,
                }
                if path in admin_routes:
                    return self.send_json(200, admin_routes[path](user, body))
                if path == "/api/logout":
                    return self.send_json(200, api_logout(user, self.token()))
            raise ApiError(404, "Не найдено")
        except ApiError as e:
            self.send_json(e.status, {"error": e.message, **e.extra})
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as e:  # непредвиденная ошибка
            print("Ошибка сервера:", repr(e), flush=True)
            try:
                self.send_json(500, {"error": "Ошибка сервера"})
            except OSError:
                pass

    def do_GET(self):
        self.dispatch("GET")

    def do_POST(self):
        self.dispatch("POST")


def main():
    # Разовая команда без запуска сервера: python server.py admin +380671234567
    if len(sys.argv) > 1:
        if server_is_running():
            print("Сервер сейчас запущен. Введите команду прямо в его окне терминала,\n"
                  "иначе при следующем сохранении сервер перезапишет изменения.")
            return
        print(run_command(" ".join(sys.argv[1:])))
        return
    if not (BASE / "index.html").exists():
        print("Рядом с server.py должен лежать index.html")
    ensure_admin()
    server = ThreadingHTTPServer((HOST, PORT), Handler)
    server.daemon_threads = True
    print(f"Искра запущена: http://localhost:{PORT}  (остановить: Ctrl+C)")
    if ADMIN_PHONE:
        print(f"Админ-панель доступна только аккаунту {ADMIN_PHONE}.")
    print("Вход по номеру и паролю, SMS не используются.")
    if sys.stdin and sys.stdin.isatty():
        threading.Thread(target=console_loop, daemon=True).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nОстановлено.")
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
