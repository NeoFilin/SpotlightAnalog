#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Spotlight PC — быстрый поиск файлов по всему компьютеру (аналог Spotlight).

Возможности:
    * Глобальная горячая клавиша Alt+Space (запасная: Ctrl+Alt+Space)
    * Фоновое индексирование выбранных папок/дисков в обычный текстовый файл
      data/index.txt — один абсолютный путь на строку
    * Мгновенный поиск по подстроке пути с ранжированием по имени файла
    * Enter — открыть, Ctrl+Enter — показать в Проводнике, Shift+Enter — папку
    * Настройки: папки для индексации, автозапуск, переиндексация
    * Без внешних зависимостей — только стандартная библиотека Python

Запуск:
    pyw spotlight_pc.py          (без окна консоли)
    py spotlight_pc.py           (с консолью, для отладки)
    py spotlight_pc.py --reindex (только перестроить индекс и выйти)
"""

from __future__ import annotations

import ctypes
import json
import os
import queue
import string
import subprocess
import sys
import threading
import time
import tkinter as tk
from array import array
from bisect import bisect_right
from ctypes import wintypes
from pathlib import Path
from tkinter import filedialog, messagebox

# ---------------------------------------------------------------------------
# Пути и константы
# ---------------------------------------------------------------------------

APP_DIR = Path(__file__).resolve().parent
DATA_DIR = Path(os.environ.get("SPOTLIGHT_DATA_DIR") or (APP_DIR / "data"))
INDEX_FILE = DATA_DIR / "index.txt"
META_FILE = DATA_DIR / "index_meta.json"
SETTINGS_FILE = DATA_DIR / "settings.json"

PLACEHOLDER = "Поиск файлов и папок…"
MAX_RESULTS = 8
WINDOW_WIDTH = 760

# Win32
MOD_ALT = 0x0001
MOD_CONTROL = 0x0002
MOD_NOREPEAT = 0x4000
VK_SPACE = 0x20
WM_HOTKEY = 0x0312
WM_QUIT = 0x0012
HOTKEY_ID = 0xB001
FILE_ATTRIBUTE_REPARSE_POINT = 0x0400
CREATE_NO_WINDOW = 0x08000000
ERROR_ALREADY_EXISTS = 183
DRIVE_FIXED = 3

# Оформление
BG = "#1f2023"
BORDER = "#3a3d43"
PANEL = "#27292e"
SELECT = "#2f3238"
TEXT = "#f1f1f1"
SUBTLE = "#8b9097"
ACCENT = "#4c8bf5"

EXCLUDED_DIR_NAMES = {
    "$recycle.bin", "system volume information", "recovery", "perflogs",
    "windows", "winsxs", "node_modules", "__pycache__", ".git", ".svn", ".hg",
    ".venv", "venv", ".tox", ".mypy_cache", ".pytest_cache", ".gradle", ".m2",
    ".npm", ".cache", "package cache",
}
EXCLUDED_FILES = {
    "pagefile.sys", "hiberfil.sys", "swapfile.sys",
    "ntuser.dat", "ntuser.dat.log1", "ntuser.dat.log2",
}


# ---------------------------------------------------------------------------
# Вспомогательные функции
# ---------------------------------------------------------------------------

def fmt_count(n: int) -> str:
    return f"{n:,}".replace(",", " ")


def shorten(text: str, limit: int, keep_tail: bool = False) -> str:
    if len(text) <= limit:
        return text
    if keep_tail:
        return "…" + text[-(limit - 1):]
    return text[: limit - 1] + "…"


def fixed_drives() -> list[str]:
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel32.GetDriveTypeW.argtypes = [wintypes.LPCWSTR]
    kernel32.GetDriveTypeW.restype = wintypes.UINT
    drives = []
    for letter in string.ascii_uppercase:
        root = f"{letter}:\\"
        try:
            if os.path.exists(root) and kernel32.GetDriveTypeW(root) == DRIVE_FIXED:
                drives.append(root)
        except OSError:
            pass
    return drives


def is_excluded_dir(name: str, path: str) -> bool:
    low = name.lower()
    if low in EXCLUDED_DIR_NAMES:
        return True
    if low in {"temp", "tmp"} and "\\appdata\\" in path.lower():
        return True
    return False


def iter_paths(root: str, cancel: threading.Event | None = None):
    """Обходит дерево каталогов и отдаёт пути файлов и папок.

    Не заходит в перехесты (ярлыки/точки монтирования), системные и мусорные
    каталоги; ошибки доступа молча пропускает.
    """
    stack = [root]
    while stack:
        if cancel is not None and cancel.is_set():
            return
        current = stack.pop()
        try:
            with os.scandir(current) as entries:
                for entry in entries:
                    if cancel is not None and cancel.is_set():
                        return
                    try:
                        if entry.is_dir(follow_symlinks=False):
                            attrs = entry.stat(follow_symlinks=False).st_file_attributes
                            if attrs & FILE_ATTRIBUTE_REPARSE_POINT:
                                continue
                            if is_excluded_dir(entry.name, entry.path):
                                continue
                            stack.append(entry.path)
                            yield entry.path
                        elif entry.is_file(follow_symlinks=False):
                            if entry.name.lower() in EXCLUDED_FILES:
                                continue
                            yield entry.path
                    except OSError:
                        continue
        except OSError:
            continue


WATCH_MAX_DEPTH = 3


def scan_tree(root, max_depth: int = WATCH_MAX_DEPTH):
    """Быстрый обход верхних уровней каталога — для авто-подхвата новых файлов."""
    stack = [(str(root), 0)]
    while stack:
        current, depth = stack.pop()
        try:
            with os.scandir(current) as entries:
                for entry in entries:
                    try:
                        if entry.is_dir(follow_symlinks=False):
                            attrs = entry.stat(follow_symlinks=False).st_file_attributes
                            if attrs & FILE_ATTRIBUTE_REPARSE_POINT:
                                continue
                            if is_excluded_dir(entry.name, entry.path):
                                continue
                            yield entry.path
                            if depth < max_depth:
                                stack.append((entry.path, depth + 1))
                        elif entry.is_file(follow_symlinks=False):
                            if entry.name.lower() in EXCLUDED_FILES:
                                continue
                            yield entry.path
                    except OSError:
                        continue
        except OSError:
            continue


def watch_folders() -> list[str]:
    """Папки, куда обычно попадают новые файлы."""
    override = os.environ.get("SPOTLIGHT_WATCH_DIRS")
    if override:
        return [p for p in override.split(os.pathsep) if p and os.path.isdir(p)]

    home = Path.home()
    candidates = [home / name for name in ("Downloads", "Desktop", "Documents", "Pictures")]
    onedrive = os.environ.get("OneDrive")
    if onedrive:
        candidates += [Path(onedrive) / name for name in ("Desktop", "Documents")]

    result: list[str] = []
    seen: set[str] = set()
    for path in candidates:
        try:
            if path.is_dir():
                key = str(path).lower()
                if key not in seen:
                    seen.add(key)
                    result.append(str(path))
        except OSError:
            continue
    return result


class NewFileWatcher(threading.Thread):
    """Периодически обходит папки и сообщает о новых путях."""

    def __init__(self, folders, known_lows, lock: threading.Lock,
                 on_new, stop_event: threading.Event, interval: float = 5.0) -> None:
        super().__init__(daemon=True)
        self.folders = list(folders)
        self.known = known_lows
        self.lock = lock
        self.on_new = on_new
        self.stop_event = stop_event
        self.interval = interval

    def run(self) -> None:
        while not self.stop_event.is_set():
            for folder in self.folders:
                if self.stop_event.is_set():
                    return
                if not os.path.isdir(folder):
                    continue
                for path in scan_tree(folder):
                    if self.stop_event.is_set():
                        return
                    low = path.lower()
                    with self.lock:
                        if low in self.known:
                            continue
                        self.known.add(low)
                    self.on_new(path)
            self.stop_event.wait(self.interval)


def build_index(roots, out_file, progress=None, cancel=None):
    """Строит индекс в out_file (атомарно через временный файл).

    Возвращает (количество путей, секунды) или None, если индексация отменена.
    """
    out_file = Path(out_file)
    out_file.parent.mkdir(parents=True, exist_ok=True)
    tmp = out_file.with_name(out_file.name + ".tmp")
    count = 0
    started = time.time()
    with open(tmp, "w", encoding="utf-8", errors="replace") as f:
        for root in roots:
            if cancel is not None and cancel.is_set():
                break
            for path in iter_paths(root, cancel):
                f.write(path)
                f.write("\n")
                count += 1
                if progress is not None and count % 1000 == 0:
                    progress(count)
    if cancel is not None and cancel.is_set():
        tmp.unlink(missing_ok=True)
        return None
    os.replace(tmp, out_file)
    return count, time.time() - started


def load_index() -> tuple[list[str], str, array]:
    """Загружает индекс: пути, общий блоб в нижнем регистре и смещения путей.

    Поиск подстроки идёт по одной большой строке на скорости C, а смещения
    позволяют мгновенно получить номер пути по позиции совпадения.
    """
    if not INDEX_FILE.exists():
        return [], "", array("Q")
    try:
        with open(INDEX_FILE, "r", encoding="utf-8", errors="replace") as f:
            paths = [line.rstrip("\r\n") for line in f]
    except OSError:
        return [], "", array("Q")
    lowered = [p.lower() for p in paths]
    blob = "\n".join(lowered)
    offsets = array("Q")
    pos = 0
    for low in lowered:
        offsets.append(pos)
        pos += len(low) + 1
    return paths, blob, offsets


def load_meta() -> dict:
    try:
        return json.loads(META_FILE.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}


def load_settings() -> dict:
    try:
        raw = json.loads(SETTINGS_FILE.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        raw = {}
    roots = [str(p) for p in raw.get("roots", []) if str(p).strip()]
    if not roots:
        roots = fixed_drives() or [str(Path.home())]
    return {
        "roots": roots,
        "autostart": bool(raw.get("autostart", False)),
        "auto_watch": bool(raw.get("auto_watch", True)),
    }


def save_json(path: Path, data: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    os.replace(tmp, path)


def search_paths(paths, blob: str, offsets: array, query: str,
                 limit: int = MAX_RESULTS, extra=()) -> list[str]:
    """Быстрый поиск по подстроке с ранжированием по имени файла.

    extra — пути, найденные авто-обновлением уже после построения индекса.
    """
    terms = query.lower().split()
    if not terms or (not paths and not extra):
        return []

    def score_for(low: str) -> int:
        name = low[low.rfind("\\") + 1:]
        if name.startswith(terms[0]):
            return 0
        if all(t in name for t in terms):
            return 1
        return 2

    found: list[tuple[int, int, str]] = []

    # Основной индекс: ищем самое короткое слово по общему блобу.
    if paths:
        term = min(terms, key=len)
        total = len(paths)
        start = 0
        while len(found) < 3000:
            pos = blob.find(term, start)
            if pos < 0:
                break
            index = bisect_right(offsets, pos) - 1
            if index < 0 or index >= total:
                break
            begin = offsets[index]
            end = offsets[index + 1] if index + 1 < total else len(blob)
            low = blob[begin:end]
            if all(t in low for t in terms):
                found.append((score_for(low), len(low), paths[index]))
            start = end + 1

    # Свежие файлы, добавленные после индексации.
    for path in extra:
        low = path.lower()
        if all(t in low for t in terms):
            found.append((score_for(low), len(low), path))

    found.sort(key=lambda entry: (entry[0], entry[1]))
    return [entry[2] for entry in found[:limit]]


# ---------------------------------------------------------------------------
# Глобальная горячая клавиша
# ---------------------------------------------------------------------------

class HotkeyListener(threading.Thread):
    def __init__(self, events: queue.Queue) -> None:
        super().__init__(daemon=True)
        self.events = events

    def run(self) -> None:
        user32 = ctypes.WinDLL("user32", use_last_error=True)
        msg = wintypes.MSG()
        # Создаём очередь сообщений у этого потока до регистрации.
        user32.PeekMessageW(ctypes.byref(msg), None, 0, 0, 0)

        combos = [
            (MOD_ALT | MOD_NOREPEAT, VK_SPACE, "Alt+Space"),
            (MOD_CONTROL | MOD_ALT | MOD_NOREPEAT, VK_SPACE, "Ctrl+Alt+Space"),
        ]
        chosen = None
        for mods, vk, label in combos:
            if user32.RegisterHotKey(None, HOTKEY_ID, mods, vk):
                chosen = label
                break
        self.events.put(("hotkey", chosen))
        if chosen is None:
            return

        while True:
            ret = user32.GetMessageW(ctypes.byref(msg), None, 0, 0)
            if ret <= 0:
                break
            if msg.message == WM_HOTKEY:
                self.events.put(("toggle", None))


# ---------------------------------------------------------------------------
# Приложение
# ---------------------------------------------------------------------------

class SpotlightApp:
    def __init__(self) -> None:
        self.settings = load_settings()
        if not SETTINGS_FILE.exists():
            try:
                save_json(SETTINGS_FILE, self.settings)
            except OSError:
                pass
        self._index_data = load_index()
        self._meta = load_meta()

        self.visible = False
        self.indexing = False
        self.index_progress = 0
        self._cancel = threading.Event()
        self._events: queue.Queue = queue.Queue()
        self._pending_search = None
        self._delta: list[str] = []
        self._delta_lock = threading.Lock()
        self._known_lows: set[str] = set()
        self._watch_lock = threading.Lock()
        self._watch_stop = threading.Event()
        self._watcher: NewFileWatcher | None = None
        self._unfocused_ticks = 0
        self._refresh_needed = False
        self._index_error = None
        self._status_message = ""
        self._message_until = 0.0
        self._selected = -1
        self._items: list[dict] = []
        self._rows: list[tuple[tk.Frame, list[tk.Widget]]] = []
        self._last_status = ""
        self._last_hint = ""
        self._last_stop_state = ""
        self.settings_win = None
        self.settings_open = False
        self._settings_roots: list[str] = []
        self._settings_autostart = None
        self._hotkey_label = ""
        self._placeholder_active = True

        self.root = tk.Tk()
        self.root.withdraw()
        self.root.title("Spotlight PC")
        self.root.overrideredirect(True)
        self.root.configure(bg=BORDER)
        self.root.attributes("-topmost", True)

        self._build_ui()
        self._bind_keys()
        self._apply_rounding()

        HotkeyListener(self._events).start()
        self._start_watcher()
        self.root.after(80, self._poll_events)
        self.root.after(150, self._tick)

        if not INDEX_FILE.exists():
            # Первый запуск: показываем окно и начинаем индексировать.
            self.root.after(400, self.show)
            self.root.after(700, self.reindex_current)

    # -- интерфейс ---------------------------------------------------------

    def _build_ui(self) -> None:
        outer = tk.Frame(self.root, bg=BORDER)
        outer.pack(fill="both", expand=True)
        self.inner = tk.Frame(outer, bg=BG)
        self.inner.pack(fill="both", expand=True, padx=1, pady=1)

        search = tk.Frame(self.inner, bg=BG)
        search.pack(fill="x", padx=18, pady=(14, 10))
        tk.Label(
            search, text="\U0001F50D", font=("Segoe UI Emoji", 16),
            bg=BG, fg=SUBTLE,
        ).pack(side="left", padx=(0, 8))
        self.entry = tk.Entry(
            search, font=("Segoe UI", 19), bg=BG, fg=TEXT,
            insertbackground=ACCENT, relief="flat", bd=0, highlightthickness=0,
        )
        self.entry.pack(side="left", fill="x", expand=True, ipady=2)
        self.entry.bind("<KeyPress>", self._on_keypress)
        self.entry.bind("<KeyRelease>", self._on_keyrelease)
        self.entry.bind("<<Paste>>", self._on_paste)

        tk.Frame(self.inner, bg="#33363c", height=1).pack(fill="x", padx=18)

        self.results = tk.Frame(self.inner, bg=BG)
        self.results.pack(fill="both", expand=True, padx=10, pady=8)

        footer = tk.Frame(self.inner, bg=BG)
        footer.pack(fill="x", padx=18, pady=(0, 12))
        self.hint = tk.Label(footer, text="", bg=BG, fg=SUBTLE, font=("Segoe UI", 9))
        self.hint.pack(side="left")
        self.status = tk.Label(footer, text="", bg=BG, fg=SUBTLE, font=("Segoe UI", 9))
        self.status.pack(side="right")

    def _bind_keys(self) -> None:
        self.root.bind("<Down>", lambda e: self._move_selection(1))
        self.root.bind("<Up>", lambda e: self._move_selection(-1))
        self.root.bind("<Return>", self._on_enter)
        self.root.bind("<KP_Enter>", self._on_enter)
        self.root.bind("<Escape>", lambda e: self.hide())
        self.root.bind("<Control-Return>", lambda e: self._activate_selected(reveal=True))
        self.root.bind("<Shift-Return>", lambda e: self._open_selected_folder())
        self.root.bind("<Control-a>", self._select_all)
        self.root.bind("<Control-A>", self._select_all)
        # Те же действия в русской раскладке (keysym кириллицы).
        self.root.bind("<Control-Cyrillic_ef>", self._select_all)   # Ctrl+Ф = A
        self.root.bind("<Control-Cyrillic_em>", self._paste)        # Ctrl+М = V
        self.root.bind("<Control-Cyrillic_es>", self._copy)         # Ctrl+С = C
        self.root.bind("<Control-Cyrillic_che>", self._cut)         # Ctrl+Ч = X
        self.root.bind("<Shift-Insert>", self._paste)
        self.root.bind("<Control-Insert>", self._copy)

    def _apply_rounding(self) -> None:
        try:
            user32 = ctypes.windll.user32
            dwmapi = ctypes.windll.dwmapi
            hwnd = user32.GetParent(self.root.winfo_id()) or self.root.winfo_id()
            pref = ctypes.c_int(2)  # DWMWCP_ROUND
            dwmapi.DwmSetWindowAttribute(
                hwnd, 33, ctypes.byref(pref), ctypes.sizeof(pref)
            )
        except Exception:
            pass

    def _window_geometry(self, height: int) -> str:
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        x = max(0, (sw - WINDOW_WIDTH) // 2)
        y = max(0, int(sh * 0.27))
        return f"{WINDOW_WIDTH}x{height}+{x}+{y}"

    def _fit_height(self) -> None:
        self.root.update_idletasks()
        height = min(620, max(120, self.inner.winfo_reqheight()))
        self.root.geometry(self._window_geometry(height))

    # -- показ / скрытие ---------------------------------------------------

    def show(self) -> None:
        self.visible = True
        self._unfocused_ticks = 0
        self._reset_query()
        self._fit_height()
        self.root.deiconify()
        self.root.attributes("-topmost", True)
        self.root.lift()
        self.root.after(10, self._focus_entry)

    def _focus_entry(self) -> None:
        try:
            self.root.focus_force()
            self.entry.focus_force()
            self.entry.icursor(0)
        except tk.TclError:
            pass

    def hide(self) -> None:
        self.visible = False
        self._cancel_pending_search()
        self.root.withdraw()

    def toggle(self) -> None:
        if self.settings_open:
            return
        if self.visible:
            self.hide()
        else:
            self.show()

    # -- поле поиска -------------------------------------------------------

    def _set_placeholder(self) -> None:
        self.entry.delete(0, "end")
        self.entry.insert(0, PLACEHOLDER)
        self.entry.configure(fg=SUBTLE)
        self._placeholder_active = True
        self.entry.icursor(0)

    def _clear_placeholder(self) -> None:
        if self._placeholder_active:
            self._placeholder_active = False
            self.entry.delete(0, "end")
            self.entry.configure(fg=TEXT)

    def _reset_query(self) -> None:
        self._set_placeholder()
        self._show_actions()

    def _on_keypress(self, event) -> None:
        # Ctrl+... по виртуальным кодам клавиш — работает в любой раскладке.
        if (event.state & 0x0004) and not (event.state & 0x0008):
            code = event.keycode
            if code == 86:      # V
                return self._paste()
            if code == 65:      # A
                return self._select_all()
            if code == 67:      # C
                return self._copy()
            if code == 88:      # X
                return self._cut()
        if self._placeholder_active:
            if event.keysym in ("BackSpace", "Delete"):
                return "break"
            if event.char and event.char.isprintable():
                self._clear_placeholder()
        return None

    def _on_paste(self, event=None) -> None:
        if self._placeholder_active:
            self._clear_placeholder()

    def _on_keyrelease(self, event) -> None:
        if event.keysym in (
            "Up", "Down", "Return", "KP_Enter", "Escape", "Control_L",
            "Control_R", "Shift_L", "Shift_R", "Alt_L", "Alt_R", "Tab",
        ):
            return
        self._schedule_search()

    def _schedule_search(self) -> None:
        self._cancel_pending_search()
        self._pending_search = self.root.after(120, self._do_search)

    def _cancel_pending_search(self) -> None:
        if self._pending_search is not None:
            try:
                self.root.after_cancel(self._pending_search)
            except (tk.TclError, ValueError):
                pass
            self._pending_search = None

    def _do_search(self) -> None:
        self._pending_search = None
        if self._placeholder_active:
            self._show_actions()
            return
        query = self.entry.get().strip()
        if not query:
            self._set_placeholder()
            self._show_actions()
            return
        paths, blob, offsets = self._index_data
        found = search_paths(paths, blob, offsets, query, extra=self._delta_snapshot())
        self._render_paths(found)

    def _select_all(self, event=None) -> str:
        self.entry.selection_range(0, "end")
        self.entry.icursor("end")
        return "break"

    def _paste(self, event=None) -> str:
        try:
            text = self.root.clipboard_get()
        except tk.TclError:
            return "break"
        self._clear_placeholder()
        text = text.replace("\r", " ").replace("\n", " ")
        if self.entry.selection_present():
            self.entry.delete("sel.first", "sel.last")
        self.entry.insert("insert", text)
        self._schedule_search()
        return "break"

    def _copy(self, event=None) -> str:
        try:
            text = self.entry.selection_get()
        except tk.TclError:
            return "break"
        self.root.clipboard_clear()
        self.root.clipboard_append(text)
        return "break"

    def _cut(self, event=None) -> str:
        try:
            text = self.entry.selection_get()
        except tk.TclError:
            return "break"
        self.root.clipboard_clear()
        self.root.clipboard_append(text)
        self.entry.delete("sel.first", "sel.last")
        self._schedule_search()
        return "break"

    # -- список результатов ------------------------------------------------

    def _actions(self) -> list[dict]:
        actions = []
        if self.indexing:
            actions.append({
                "type": "action", "icon": "⏹", "title": "Остановить индексацию",
                "subtitle": f"Уже проиндексировано: {fmt_count(self.index_progress)} путей",
                "action": self._stop_indexing,
            })
        actions.extend([
            {
                "type": "action", "icon": "⚙", "title": "Настройки индексации",
                "subtitle": "Папки и диски, автозапуск, статистика",
                "action": self.open_settings,
            },
            {
                "type": "action", "icon": "\U0001F504", "title": "Переиндексировать сейчас",
                "subtitle": "Обновить список путей на диске",
                "action": self.reindex_current,
            },
            {
                "type": "action", "icon": "\U0001F4C2", "title": "Открыть папку с индексом",
                "subtitle": str(DATA_DIR),
                "action": lambda: self._open_path(str(DATA_DIR)),
            },
            {
                "type": "action", "icon": "⏻", "title": "Выход",
                "subtitle": "Закрыть Spotlight PC",
                "action": self.quit,
            },
        ])
        return actions

    def _show_actions(self) -> None:
        self._render(self._actions(), select_first=False)

    def _render_paths(self, paths: list[str]) -> None:
        items = [{"type": "path", "path": p} for p in paths]
        self._render(items, select_first=True)

    def _render(self, items: list[dict], select_first: bool) -> None:
        for child in self.results.winfo_children():
            child.destroy()
        self._items = items
        self._rows = []
        self._selected = 0 if (items and select_first) else -1

        if not items:
            tk.Label(
                self.results, text="Ничего не найдено", font=("Segoe UI", 11),
                bg=BG, fg=SUBTLE,
            ).pack(pady=28)
        else:
            for index, item in enumerate(items):
                if item["type"] == "path":
                    path = item["path"]
                    title = os.path.basename(path) or path
                    subtitle = str(Path(path).parent)
                    try:
                        icon = "\U0001F4C1" if os.path.isdir(path) else "\U0001F4C4"
                    except OSError:
                        icon = "\U0001F4C4"
                else:
                    title = item["title"]
                    subtitle = item["subtitle"]
                    icon = item["icon"]
                row, widgets = self._make_row(
                    index, icon, shorten(title, 58),
                    shorten(subtitle, 92, keep_tail=True),
                )
                self._rows.append((row, widgets))

        self._paint_rows()
        self._fit_height()

    def _make_row(self, index: int, icon: str, title: str, subtitle: str):
        row = tk.Frame(self.results, bg=BG, cursor="hand2")
        row.pack(fill="x", pady=1)

        icon_lbl = tk.Label(
            row, text=icon, font=("Segoe UI Emoji", 14), bg=BG, fg=TEXT,
            width=3, anchor="center",
        )
        icon_lbl.pack(side="left", padx=(8, 4), pady=6)

        text_frame = tk.Frame(row, bg=BG)
        text_frame.pack(side="left", fill="x", expand=True, pady=4)
        title_lbl = tk.Label(
            text_frame, text=title, font=("Segoe UI", 11, "bold"),
            bg=BG, fg=TEXT, anchor="w",
        )
        title_lbl.pack(fill="x")
        sub_lbl = tk.Label(
            text_frame, text=subtitle, font=("Segoe UI", 8),
            bg=BG, fg=SUBTLE, anchor="w",
        )
        sub_lbl.pack(fill="x")

        widgets = [row, icon_lbl, text_frame, title_lbl, sub_lbl]
        for widget in widgets:
            widget.bind("<Enter>", lambda e, i=index: self._hover(i))
            widget.bind("<Button-1>", lambda e, i=index: self._click(i))
        return row, widgets

    def _paint_rows(self) -> None:
        for i, (_row, widgets) in enumerate(self._rows):
            color = SELECT if i == self._selected else BG
            for widget in widgets:
                widget.configure(bg=color)

    def _hover(self, index: int) -> None:
        if index != self._selected and 0 <= index < len(self._rows):
            self._selected = index
            self._paint_rows()

    def _click(self, index: int) -> None:
        self._selected = index
        self._paint_rows()
        self._activate_selected()

    def _move_selection(self, delta: int) -> str:
        if not self._items:
            return "break"
        if self._selected < 0:
            self._selected = 0 if delta > 0 else len(self._items) - 1
        else:
            self._selected = (self._selected + delta) % len(self._items)
        self._paint_rows()
        return "break"

    def _on_enter(self, event=None) -> str:
        if event is not None and (event.state & 0x0004):
            return "break"
        if self._pending_search is not None:
            self._cancel_pending_search()
            self._do_search()
        self._activate_selected()
        return "break"

    def _activate_selected(self, reveal: bool = False) -> None:
        if not (0 <= self._selected < len(self._items)):
            return
        item = self._items[self._selected]
        if item["type"] == "action":
            item["action"]()
            return
        path = item["path"]
        self.hide()
        if reveal:
            try:
                subprocess.Popen(
                    ["explorer", f"/select,{os.path.normpath(path)}"],
                    creationflags=CREATE_NO_WINDOW,
                )
            except OSError as exc:
                messagebox.showerror("Spotlight PC", f"Не удалось открыть:\n{path}\n\n{exc}")
            return
        self._open_path(path)

    def _open_selected_folder(self) -> str:
        if not (0 <= self._selected < len(self._items)):
            return "break"
        item = self._items[self._selected]
        if item["type"] == "path":
            path = item["path"]
            folder = path if os.path.isdir(path) else str(Path(path).parent)
            self.hide()
            self._open_path(folder)
        return "break"

    def _open_path(self, path: str) -> None:
        try:
            os.startfile(path)
        except OSError as exc:
            messagebox.showerror("Spotlight PC", f"Не удалось открыть:\n{path}\n\n{exc}")

    # -- индексирование ----------------------------------------------------

    def _start_watcher(self) -> None:
        if not self.settings.get("auto_watch", True):
            return
        folders = watch_folders()
        if not folders:
            return
        self._sync_known_lows(folders)
        self._watcher = NewFileWatcher(
            folders, self._known_lows, self._watch_lock,
            self._add_delta, self._watch_stop,
        )
        self._watcher.start()

    def _sync_known_lows(self, folders=None) -> None:
        """Запоминает, какие пути из наблюдаемых папок уже есть в индексе."""
        if folders is None:
            folders = self._watcher.folders if self._watcher else watch_folders()
        prefixes = tuple(f.lower().rstrip("\\") + "\\" for f in folders)
        known: set[str] = set()
        if prefixes:
            for path in self._index_data[0]:
                low = path.lower()
                if low.startswith(prefixes):
                    known.add(low)
        with self._watch_lock:
            self._known_lows.clear()
            self._known_lows.update(known)

    def _add_delta(self, path: str) -> None:
        with self._delta_lock:
            self._delta.append(path)
        if self.indexing:
            return
        try:
            with open(INDEX_FILE, "a", encoding="utf-8") as f:
                f.write(path)
                f.write("\n")
        except OSError:
            pass

    def _delta_snapshot(self) -> list[str]:
        with self._delta_lock:
            return list(self._delta)

    def _reset_watch_state(self) -> None:
        with self._delta_lock:
            self._delta.clear()
        self._sync_known_lows()

    def _apply_watch_setting(self) -> None:
        want = self.settings.get("auto_watch", True)
        if want and self._watcher is None:
            self._watch_stop = threading.Event()
            self._start_watcher()
        elif not want and self._watcher is not None:
            self._watch_stop.set()
            self._watcher = None

    def reindex_current(self) -> None:
        if self.indexing:
            self._set_message("Индексация уже идёт…")
            return
        self.start_index(self.settings["roots"])

    def start_index(self, roots: list[str]) -> None:
        roots = [str(r) for r in roots if str(r).strip()]
        if not roots:
            messagebox.showwarning("Spotlight PC", "Добавьте хотя бы одну папку или диск.")
            return
        if self.indexing:
            return
        self.indexing = True
        self.index_progress = 0
        self._cancel.clear()
        threading.Thread(target=self._index_worker, args=(roots,), daemon=True).start()

    def _stop_indexing(self) -> None:
        if self.indexing:
            self._cancel.set()
            self._set_message("Останавливаю индексацию…")

    def _index_worker(self, roots: list[str]) -> None:
        try:
            result = build_index(
                roots, INDEX_FILE,
                progress=self._on_index_progress,
                cancel=self._cancel,
            )
            if result is None:
                self._set_message("Индексация остановлена")
                return
            count, seconds = result
            save_json(META_FILE, {
                "built_at": time.time(),
                "count": count,
                "roots": roots,
                "duration_sec": round(seconds, 1),
            })
            self._meta = load_meta()
            self._index_data = load_index()
            self._reset_watch_state()
            self._refresh_needed = True
            self._set_message(
                f"Индекс готов: {fmt_count(count)} путей за {seconds:.1f} с"
            )
        except Exception as exc:  # noqa: BLE001 — показываем пользователю
            self._index_error = str(exc)
        finally:
            self.indexing = False

    def _on_index_progress(self, count: int) -> None:
        self.index_progress = count

    def _set_message(self, text: str, seconds: float = 6.0) -> None:
        self._status_message = text
        self._message_until = time.time() + seconds

    # -- статус и события --------------------------------------------------

    def _poll_events(self) -> None:
        try:
            while True:
                kind, value = self._events.get_nowait()
                if kind == "hotkey":
                    self._hotkey_label = value or ""
                    if value is None:
                        self.show()
                        messagebox.showwarning(
                            "Spotlight PC",
                            "Не удалось занять Alt+Space и Ctrl+Alt+Space.\n"
                            "Поиск можно открывать из этого окна.",
                        )
                elif kind == "toggle":
                    self.toggle()
        except queue.Empty:
            pass
        self.root.after(80, self._poll_events)

    def _tick(self) -> None:
        try:
            if self.visible and not self.settings_open:
                try:
                    focused = self.root.focus_get()
                except KeyError:
                    focused = None
                if focused is None:
                    self._unfocused_ticks += 1
                    if self._unfocused_ticks >= 4:
                        self.hide()
                else:
                    self._unfocused_ticks = 0

            if self._refresh_needed and not self.indexing:
                self._refresh_needed = False
                if self.visible:
                    self._do_search()
                self._update_settings_stats()

            if self.settings_win is not None:
                state = "normal" if self.indexing else "disabled"
                if state != self._last_stop_state:
                    try:
                        self.stop_button.configure(state=state)
                    except tk.TclError:
                        pass
                    self._last_stop_state = state

            if self._index_error:
                error, self._index_error = self._index_error, None
                messagebox.showerror("Spotlight PC", f"Ошибка индексации:\n{error}")

            self._update_status()
        finally:
            self.root.after(150, self._tick)

    def _update_status(self) -> None:
        hotkey = self._hotkey_label or "…"
        hint = (
            f"{hotkey} — поиск   ·   ↑↓ — выбор   ·   Enter — открыть   ·   "
            "Ctrl+Enter — в Проводнике   ·   Esc — скрыть"
        )
        if hint != self._last_hint:
            self.hint.configure(text=hint)
            self._last_hint = hint

        if self.indexing:
            status = f"Индексация… {fmt_count(self.index_progress)} путей"
        elif time.time() < self._message_until:
            status = self._status_message
        else:
            count = len(self._index_data[0]) + len(self._delta)
            status = f"Индекс: {fmt_count(count)} путей"
            built = self._meta.get("built_at")
            if built:
                status += " · " + time.strftime("%d.%m %H:%M", time.localtime(built))
        if status != self._last_status:
            self.status.configure(text=status)
            self._last_status = status

    # -- настройки ---------------------------------------------------------

    def open_settings(self) -> None:
        if self.settings_win is not None:
            try:
                self.settings_win.lift()
                self.settings_win.focus_force()
                return
            except tk.TclError:
                self.settings_win = None

        self.hide()
        self.settings_open = True
        self._settings_roots = list(self.settings["roots"])
        self._settings_autostart = tk.BooleanVar(value=self.settings["autostart"])
        self._settings_watch = tk.BooleanVar(value=self.settings.get("auto_watch", True))

        win = tk.Toplevel(self.root)
        win.title("Настройки — Spotlight PC")
        win.configure(bg=BG)
        win.geometry("640x545")
        win.resizable(False, False)
        self.settings_win = win
        win.protocol("WM_DELETE_WINDOW", self._close_settings)

        pad = {"padx": 20}
        tk.Label(
            win, text="Настройки Spotlight PC", font=("Segoe UI", 15, "bold"),
            bg=BG, fg=TEXT,
        ).pack(anchor="w", pady=(16, 2), **pad)
        tk.Label(
            win, text="Где искать файлы. Изменения вступят в силу после переиндексации.",
            font=("Segoe UI", 9), bg=BG, fg=SUBTLE,
        ).pack(anchor="w", pady=(0, 12), **pad)

        list_frame = tk.Frame(win, bg=BG)
        list_frame.pack(fill="both", expand=True, **pad)
        scroll = tk.Scrollbar(list_frame)
        scroll.pack(side="right", fill="y")
        self.roots_list = tk.Listbox(
            list_frame, height=8, bg=PANEL, fg=TEXT, selectbackground=ACCENT,
            selectforeground="#ffffff", relief="flat", bd=0,
            highlightthickness=0, font=("Consolas", 10),
            yscrollcommand=scroll.set,
        )
        self.roots_list.pack(side="left", fill="both", expand=True)
        scroll.configure(command=self.roots_list.yview)
        self._refresh_roots_list()

        buttons = tk.Frame(win, bg=BG)
        buttons.pack(fill="x", pady=(8, 0), **pad)
        self._button(buttons, "Добавить папку…", self._add_root).pack(side="left")
        self._button(buttons, "Удалить", self._remove_root).pack(side="left", padx=(8, 0))
        self._button(buttons, "Открыть индекс", self._open_index_file).pack(side="left", padx=(8, 0))

        self.settings_stats = tk.Label(
            win, text="", font=("Segoe UI", 9), bg=BG, fg=SUBTLE, justify="left",
        )
        self.settings_stats.pack(anchor="w", pady=(14, 6), **pad)
        self._update_settings_stats()

        tk.Checkbutton(
            win, text="Запускать при входе в Windows", variable=self._settings_autostart,
            bg=BG, fg=TEXT, activebackground=BG, activeforeground=TEXT,
            selectcolor=PANEL, highlightthickness=0, font=("Segoe UI", 10),
            anchor="w",
        ).pack(anchor="w", **pad)
        tk.Checkbutton(
            win, text="Подхватывать новые файлы (Загрузки, Рабочий стол, Документы)",
            variable=self._settings_watch,
            bg=BG, fg=TEXT, activebackground=BG, activeforeground=TEXT,
            selectcolor=PANEL, highlightthickness=0, font=("Segoe UI", 10),
            anchor="w",
        ).pack(anchor="w", pady=(6, 0), **pad)

        bottom = tk.Frame(win, bg=BG)
        bottom.pack(fill="x", pady=(18, 16), **pad)
        self._button(bottom, "Сохранить", self._save_settings).pack(side="right")
        self._button(bottom, "Переиндексировать", self._save_and_reindex,
                     primary=True).pack(side="right", padx=(0, 8))
        self.stop_button = self._button(bottom, "Остановить", self._stop_indexing)
        self.stop_button.pack(side="left")
        self._last_stop_state = ""

        win.update_idletasks()
        x = (win.winfo_screenwidth() - win.winfo_width()) // 2
        y = (win.winfo_screenheight() - win.winfo_height()) // 2 - 40
        win.geometry(f"+{max(0, x)}+{max(0, y)}")
        win.lift()
        win.focus_force()

    def _button(self, parent, text, command, primary: bool = False) -> tk.Button:
        bg = "#3b6fd4" if primary else PANEL
        active = "#4c82e6" if primary else SELECT
        return tk.Button(
            parent, text=text, command=command, bg=bg, fg=TEXT,
            activebackground=active, activeforeground=TEXT, relief="flat",
            bd=0, padx=14, pady=7, cursor="hand2", font=("Segoe UI", 10),
        )

    def _refresh_roots_list(self) -> None:
        self.roots_list.delete(0, "end")
        for root in self._settings_roots:
            self.roots_list.insert("end", root)

    def _add_root(self) -> None:
        folder = filedialog.askdirectory(
            parent=self.settings_win, title="Выберите папку или диск",
        )
        if not folder:
            return
        normalized = os.path.normpath(folder)
        if os.path.isdir(normalized) and normalized not in self._settings_roots:
            self._settings_roots.append(normalized)
            self._refresh_roots_list()

    def _remove_root(self) -> None:
        selection = self.roots_list.curselection()
        if selection:
            del self._settings_roots[selection[0]]
            self._refresh_roots_list()

    def _open_index_file(self) -> None:
        if INDEX_FILE.exists():
            self._open_path(str(INDEX_FILE))
        else:
            messagebox.showinfo("Spotlight PC", "Индекс ещё не построен.")

    def _update_settings_stats(self) -> None:
        if self.settings_win is None:
            return
        count = len(self._index_data[0]) + len(self._delta)
        built = self._meta.get("built_at")
        when = time.strftime("%d.%m.%Y %H:%M", time.localtime(built)) if built else "ещё не построен"
        self.settings_stats.configure(
            text=f"В индексе: {fmt_count(count)} путей\nОбновлён: {when}\n"
                 f"Файл: {INDEX_FILE}",
        )

    def _save_settings(self) -> bool:
        if not self._settings_roots:
            messagebox.showwarning("Spotlight PC", "Добавьте хотя бы одну папку или диск.")
            return False
        try:
            self.settings["roots"] = list(self._settings_roots)
            self.settings["autostart"] = bool(self._settings_autostart.get())
            self.settings["auto_watch"] = bool(self._settings_watch.get())
            save_json(SETTINGS_FILE, self.settings)
            self._apply_autostart(self.settings["autostart"])
            self._apply_watch_setting()
        except OSError as exc:
            messagebox.showerror("Spotlight PC", f"Не удалось сохранить настройки:\n{exc}")
            return False
        return True

    def _save_and_reindex(self) -> None:
        if not self._save_settings():
            return
        self._set_message("Запускаю индексацию…")
        self.start_index(self.settings["roots"])
        self._close_settings()

    def _close_settings(self) -> None:
        self.settings_open = False
        if self.settings_win is not None:
            try:
                self.settings_win.destroy()
            except tk.TclError:
                pass
            self.settings_win = None

    def _apply_autostart(self, enabled: bool) -> None:
        startup = (
            Path(os.environ.get("APPDATA", ""))
            / "Microsoft" / "Windows" / "Start Menu" / "Programs" / "Startup"
        )
        if not startup.is_dir():
            return
        lnk = startup / "Spotlight PC.lnk"
        if not enabled:
            try:
                lnk.unlink(missing_ok=True)
            except OSError:
                pass
            return

        pythonw = Path(sys.executable)
        if pythonw.name.lower() != "pythonw.exe":
            candidate = pythonw.with_name("pythonw.exe")
            if candidate.exists():
                pythonw = candidate
        script = Path(__file__).resolve()

        def q(value: Path | str) -> str:
            return str(value).replace("'", "''")

        command = (
            "$s = (New-Object -ComObject WScript.Shell).CreateShortcut('" + q(lnk) + "'); "
            "$s.TargetPath = '" + q(pythonw) + "'; "
            "$s.Arguments = '\"" + q(script) + "\"'; "
            "$s.WorkingDirectory = '" + q(script.parent) + "'; "
            "$s.Save()"
        )
        try:
            subprocess.run(
                ["powershell", "-NoProfile", "-NonInteractive", "-WindowStyle", "Hidden",
                 "-Command", command],
                creationflags=CREATE_NO_WINDOW, timeout=25, check=False,
            )
        except (OSError, subprocess.SubprocessError) as exc:
            messagebox.showwarning(
                "Spotlight PC", f"Не удалось добавить в автозапуск:\n{exc}",
            )

    # -- выход -------------------------------------------------------------

    def quit(self) -> None:
        self._watch_stop.set()
        try:
            self.root.destroy()
        except tk.TclError:
            pass

    def run(self) -> None:
        self.root.mainloop()


# ---------------------------------------------------------------------------
# Точка входа
# ---------------------------------------------------------------------------

def cli_reindex() -> int:
    settings = load_settings()
    roots = settings["roots"]
    print(f"Индексирую: {', '.join(roots)}")
    last = [0]

    def progress(count: int) -> None:
        if count - last[0] >= 20000:
            last[0] = count
            print(f"  {fmt_count(count)} путей…", flush=True)

    result = build_index(roots, INDEX_FILE, progress=progress)
    if result is None:
        print("Индексация отменена.")
        return 1
    count, seconds = result
    save_json(META_FILE, {
        "built_at": time.time(), "count": count, "roots": roots,
        "duration_sec": round(seconds, 1),
    })
    print(f"Готово: {fmt_count(count)} путей за {seconds:.1f} с")
    print(f"Индекс: {INDEX_FILE}")
    return 0


def main() -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except (AttributeError, ValueError):
        pass

    if "--reindex" in sys.argv:
        return cli_reindex()

    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel32.CreateMutexW.argtypes = [wintypes.LPVOID, wintypes.BOOL, wintypes.LPCWSTR]
    kernel32.CreateMutexW.restype = wintypes.HANDLE
    mutex = kernel32.CreateMutexW(None, False, "Local\\SpotlightPC_SingleInstance")
    if ctypes.get_last_error() == ERROR_ALREADY_EXISTS:
        ctypes.windll.user32.MessageBoxW(
            None, "Spotlight PC уже запущен.\nНажмите Alt+Space.", "Spotlight PC", 0x40,
        )
        return 0

    app = SpotlightApp()
    app.run()
    _ = mutex  # держим хэндл до конца работы процесса
    return 0


if __name__ == "__main__":
    sys.exit(main())
