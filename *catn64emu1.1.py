#!/usr/bin/env python3
"""CatN64Emu 1.1.0 — N64 ROM launcher inspired by Parallel Launcher.
© AC Kondo 1999–2026. RetroArch/libretro backend with portable runtime support.

1.1.0 — bug-fix release:
  * persistent, hashed ROM cache for ZIP archives (survives window close)
  * deep-copied, type-validated settings + atomic config writes
  * threaded library scan with generation tokens (no UI freeze, no stale results)
  * writable core-install fallback to the user config dir (read-only bundles OK)
  * settings dialog is cancel-safe and only commits on Save
  * on-screen geometry restore, safe shutdown, OS-aware argument splitting
"""
from __future__ import annotations

import copy
import hashlib
import html.parser
import io
import json
import os
import platform
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import tkinter as tk
import urllib.parse
import urllib.request
from pathlib import Path
from tkinter import filedialog, messagebox, ttk
from zipfile import BadZipFile, ZipFile

APP = 'CatN64Emu 1.1.0'
VERSION = '1.1.0'
CONFIG_DIR = Path.home() / '.catn64emu'
CONFIG_FILE = CONFIG_DIR / 'settings.json'
CACHE_DIR = CONFIG_DIR / 'cache'
CACHE_TTL = 7 * 24 * 60 * 60
MAX_ROM = 256 * 1024 * 1024
MAX_CORE = 90 * 1024 * 1024
EXTS = frozenset({'.z64', '.n64', '.v64'})
SCAN_EXTS = EXTS | {'.zip'}
GEO_RE = re.compile(r'^\d{2,5}x\d{2,5}(?:[+-]\d{1,5}){0,2}$')
DEFAULTS = {
    'rom_dirs': [],
    'emulator': '',
    'core': '',
    'extra_args': '',
    'geometry': '1120x740',
    'controller_profile': 'Auto (RetroArch)',
    'fullscreen': False,
    'theme': 'System',
}
BUNDLE_DIR = Path(__file__).resolve().parent / 'catn64emu_runtime'
CORE_NAMES = ('mupen64plus_next_libretro', 'parallel_n64_libretro', 'mupen64plus_libretro')
CORE_EXTS = ('.dylib', '.so', '.dll')
USER_AGENT = {'User-Agent': f'CatN64Emu/{VERSION}'}


# --------------------------------------------------------------------------- #
# Settings
# --------------------------------------------------------------------------- #
def _clean_settings(obj):
    cfg = copy.deepcopy(DEFAULTS)
    if not isinstance(obj, dict):
        return cfg
    dirs = obj.get('rom_dirs')
    if isinstance(dirs, list):
        seen, clean = set(), []
        for entry in dirs:
            if isinstance(entry, str) and entry.strip():
                key = os.path.normcase(os.path.abspath(entry.strip()))
                if key not in seen:
                    seen.add(key)
                    clean.append(entry.strip())
        cfg['rom_dirs'] = clean
    for key in ('emulator', 'core', 'extra_args', 'controller_profile', 'theme'):
        value = obj.get(key)
        if isinstance(value, str):
            cfg[key] = value
    if isinstance(obj.get('fullscreen'), bool):
        cfg['fullscreen'] = obj['fullscreen']
    geometry = obj.get('geometry')
    if isinstance(geometry, str) and GEO_RE.match(geometry.strip()):
        cfg['geometry'] = geometry.strip()
    return cfg


def load_settings():
    try:
        return _clean_settings(json.loads(CONFIG_FILE.read_text(encoding='utf-8')))
    except (OSError, ValueError):
        return copy.deepcopy(DEFAULTS)


def write_settings(cfg):
    CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    tmp = CONFIG_FILE.with_suffix('.json.partial')
    tmp.write_text(json.dumps(cfg, indent=2), encoding='utf-8')
    tmp.replace(CONFIG_FILE)


# --------------------------------------------------------------------------- #
# ROM headers and cache
# --------------------------------------------------------------------------- #
def read_header(path):
    try:
        with Path(path).open('rb') as handle:
            data = handle.read(0x40)
    except OSError:
        return None
    if len(data) < 0x40:
        return None
    magic = data[:4]
    if magic in (b'\x80\x37\x12\x40', b'\x80\x37\x12\x41'):
        raw = data
    elif magic == b'\x37\x80\x40\x12':
        raw = bytes(b for i in range(0, len(data) - 1, 2) for b in (data[i + 1], data[i]))
    elif magic == b'\x40\x12\x37\x80':
        raw = b''.join(data[i:i + 4][::-1] for i in range(0, len(data) - 3, 4))
    else:
        return None
    name = raw[0x20:0x34].decode('ascii', 'replace')
    name = ''.join(ch for ch in name if ch.isprintable()).strip('\x00 ').strip()
    return name or Path(path).stem


def cache_key(path):
    stat = path.stat()
    blob = f'{path.resolve()}|{stat.st_size}|{int(stat.st_mtime)}'.encode()
    return hashlib.sha1(blob).hexdigest()[:20]


def prune_cache(max_age=CACHE_TTL):
    cutoff = time.time() - max_age
    try:
        entries = list(CACHE_DIR.iterdir())
    except OSError:
        return
    for entry in entries:
        try:
            if entry.is_file() and entry.stat().st_mtime < cutoff:
                entry.unlink()
        except OSError:
            continue


def prepare_rom(path):
    """Return a launchable ROM path, extracting archives into the persistent cache."""
    if path.suffix.lower() != '.zip':
        if read_header(path) is None:
            raise ValueError(f'Unrecognized N64 ROM header: {path.name}')
        return path
    try:
        CACHE_DIR.mkdir(parents=True, exist_ok=True)
    except OSError as exc:
        raise ValueError(f'Cannot create cache directory: {exc}') from exc
    key = cache_key(path)
    for existing in CACHE_DIR.glob(key + '_*'):
        if existing.is_file() and read_header(existing):
            return existing
    try:
        with ZipFile(path) as archive:
            members = [i for i in archive.infolist()
                       if not i.is_dir() and Path(i.filename).suffix.lower() in EXTS]
            if not members:
                raise ValueError('ZIP archive contains no .z64, .n64, or .v64 ROM.')
            member = members[0]
            if member.file_size > MAX_ROM:
                raise ValueError('ROM exceeds 256 MB safety limit.')
            suffix = Path(member.filename).suffix.lower()
            target = CACHE_DIR / f'{key}_{suffix.lstrip(".")}'
            partial = target.with_suffix('.partial')
            with archive.open(member) as src, partial.open('wb') as dst:
                shutil.copyfileobj(src, dst)
            if read_header(partial) is None:
                partial.unlink(missing_ok=True)
                raise ValueError('Archive contains an unrecognized ROM.')
            partial.replace(target)
            return target
    except BadZipFile as exc:
        raise ValueError('Invalid ZIP archive.') from exc
    except OSError as exc:
        raise ValueError(f'Could not extract archive: {exc}') from exc


# --------------------------------------------------------------------------- #
# Backend discovery
# --------------------------------------------------------------------------- #
def discover_emulator():
    """Prefer a private RetroArch runtime, then a system RetroArch install."""
    candidates = [
        BUNDLE_DIR / 'retroarch',
        BUNDLE_DIR / 'retroarch.exe',
        BUNDLE_DIR / 'RetroArch.app' / 'Contents' / 'MacOS' / 'RetroArch',
        Path('/Applications/RetroArch.app/Contents/MacOS/RetroArch'),
        Path.home() / 'Applications/RetroArch.app/Contents/MacOS/RetroArch',
    ]
    for candidate in candidates:
        if candidate.is_file():
            return str(candidate)
    return shutil.which('retroarch') or ''


def discover_core(exe=''):
    """Find a libretro N64 core without requiring manual -L arguments."""
    roots = [
        BUNDLE_DIR / 'cores',
        CONFIG_DIR / 'cores',
        Path.home() / '.config/retroarch/cores',
        Path.home() / 'Library/Application Support/RetroArch/cores',
        Path('/Applications/RetroArch.app/Contents/Resources/cores'),
        Path('/Applications/RetroArch.app/Contents/MacOS/cores'),
        Path('/usr/lib/libretro'),
        Path('/usr/local/lib/libretro'),
        Path('/opt/homebrew/lib/libretro'),
    ]
    if exe:
        resolved = Path(exe).expanduser()
        if not resolved.is_file():
            found = shutil.which(exe)
            resolved = Path(found) if found else resolved
        if resolved.parent != Path('.'):
            roots += [resolved.parent / 'cores',
                      resolved.parent.parent / 'Resources' / 'cores',
                      resolved.parent.parent.parent / 'Resources' / 'cores']
    for root in roots:
        for name in CORE_NAMES:
            for ext in CORE_EXTS:
                candidate = root / (name + ext)
                if candidate.is_file():
                    return str(candidate)
    return ''


def discover_standalone():
    """Native N64 fallback; does not need a libretro core."""
    paths = [BUNDLE_DIR / 'mupen64plus',
             Path('/opt/homebrew/bin/mupen64plus'),
             Path('/usr/local/bin/mupen64plus'),
             Path('/usr/bin/mupen64plus')]
    found = shutil.which('mupen64plus')
    if found:
        paths.insert(0, Path(found))
    return str(next((p for p in paths if p.is_file()), ''))


def valid_retroarch(exe):
    if not exe:
        return False
    if Path(exe).expanduser().is_file():
        return True
    found = shutil.which(exe)
    return bool(found) and 'retroarch' in Path(found).name.lower()


def retroarch_core_available(exe, core):
    return valid_retroarch(exe) and bool(core) and Path(core).is_file()


def core_install_dir():
    """First writable core directory: bundle, then user config."""
    for candidate in (BUNDLE_DIR / 'cores', CONFIG_DIR / 'cores'):
        try:
            candidate.mkdir(parents=True, exist_ok=True)
            probe = candidate / '.catn64emu-write-test'
            probe.write_bytes(b'')
            probe.unlink()
            return candidate
        except OSError:
            continue
    raise RuntimeError('No writable directory is available for libretro cores.')


class _Links(html.parser.HTMLParser):
    def __init__(self):
        super().__init__()
        self.links = []

    def handle_starttag(self, tag, attrs):
        if tag == 'a':
            url = dict(attrs).get('href', '')
            if url:
                self.links.append(url)


def _official_core_indexes():
    """RetroArch's official buildbot; exact architecture matches only."""
    osname = platform.system()
    arch = platform.machine().lower()
    if osname == 'Darwin':
        if arch in ('arm64', 'aarch64'):
            return ['https://buildbot.libretro.com/nightly/apple/osx/arm64/latest/']
        return ['https://buildbot.libretro.com/nightly/apple/osx/x86_64/latest/']
    if osname == 'Windows':
        return (['https://buildbot.libretro.com/nightly/windows/x86_64/latest/']
                if arch in ('amd64', 'x86_64') else [])
    if osname == 'Linux' and arch in ('x86_64', 'amd64'):
        return ['https://buildbot.libretro.com/nightly/linux/x86_64/latest/']
    return []


def download_n64_core(progress=lambda msg: None):
    """Install an official, architecture-matched libretro core."""
    indexes = _official_core_indexes()
    if not indexes:
        raise RuntimeError('No official core index is configured for this OS/CPU.')
    last = 'No compatible N64 core archive was listed.'
    for base in indexes:
        progress('Checking official RetroArch buildbot...')
        try:
            with urllib.request.urlopen(urllib.request.Request(base, headers=USER_AGENT), timeout=20) as response:
                listing = response.read(2_000_000).decode('utf-8', 'replace')
            parser = _Links()
            parser.feed(listing)
            urls = [urllib.parse.unquote(u.split('?')[0]) for u in parser.links]
            for name in CORE_NAMES:
                wanted = {name + e for e in CORE_EXTS} | {name + e + '.zip' for e in CORE_EXTS}
                matches = [u for u in urls if Path(u).name.lower() in wanted]
                if not matches:
                    continue
                url = urllib.parse.urljoin(base, matches[0])
                progress('Downloading ' + Path(matches[0]).name + '...')
                with urllib.request.urlopen(urllib.request.Request(url, headers=USER_AGENT), timeout=90) as response:
                    payload = response.read(MAX_CORE + 1)
                if len(payload) > MAX_CORE:
                    raise RuntimeError('Core download exceeds the safety limit.')
                destination = core_install_dir()
                if Path(matches[0]).suffix in CORE_EXTS:
                    target = destination / Path(matches[0]).name
                    partial = target.with_suffix(target.suffix + '.partial')
                    partial.write_bytes(payload)
                    partial.replace(target)
                    progress('N64 core installed: ' + target.name)
                    return str(target)
                with ZipFile(io.BytesIO(payload)) as archive:
                    members = [m for m in archive.infolist()
                               if Path(m.filename).name.startswith(name)
                               and Path(m.filename).suffix in CORE_EXTS
                               and m.file_size < MAX_CORE]
                    if not members:
                        raise RuntimeError('Archive contains no recognized N64 libretro core.')
                    member = members[0]
                    target = destination / Path(member.filename).name
                    partial = target.with_suffix(target.suffix + '.partial')
                    with archive.open(member) as src, partial.open('wb') as dst:
                        shutil.copyfileobj(src, dst)
                    partial.replace(target)
                progress('N64 core installed: ' + target.name)
                return str(target)
        except Exception as exc:  # try the next index
            last = str(exc)
    raise RuntimeError('Could not install an official compatible N64 core. ' + last + '\n'
                       'Some platforms, including Apple Silicon, may not be listed on the '
                       'official buildbot; use the native backend instead.')


# --------------------------------------------------------------------------- #
# UI
# --------------------------------------------------------------------------- #
class Launcher(tk.Tk):
    def __init__(self):
        super().__init__()
        self.cfg = load_settings()
        self._closing = False
        self._busy = ''
        self._scan_token = 0
        self.title(f'{APP}  |  AC Kondo Solutions')
        self.minsize(760, 480)
        self._restore_geometry()
        self.configure(bg='#163b69')

        self.emulator = tk.StringVar(value=self.cfg['emulator'] or discover_emulator())
        self.extra_args = tk.StringVar(value=self.cfg['extra_args'])
        self.core = tk.StringVar(value=self.cfg['core'] or discover_core(self.emulator.get()))
        self.controller_profile = tk.StringVar(value=self.cfg['controller_profile'])
        self.fullscreen = tk.BooleanVar(value=self.cfg['fullscreen'])
        self.theme_choice = tk.StringVar(value=self.cfg['theme'])
        self.search = tk.StringVar()

        self.games = []
        self.visible = {}

        self._make_ui()
        self.apply_theme()
        self.search.trace_add('write', lambda *_: self.populate())
        self.bind('<F5>', lambda _: self.scan())
        self.bind('<Control-f>', lambda _: self._focus_search())
        self.protocol('WM_DELETE_WINDOW', self.close)
        self.scan()

    # -- window state -------------------------------------------------------
    def _restore_geometry(self):
        self.geometry(self.cfg['geometry'])
        try:
            self.update_idletasks()
            screen_w = self.winfo_screenwidth()
            screen_h = self.winfo_screenheight()
            width = min(self.winfo_width() or 1120, screen_w)
            height = min(self.winfo_height() or 740, screen_h)
            x, y = self.winfo_x(), self.winfo_y()
            if not (0 <= x < screen_w - 80 and 0 <= y < screen_h - 80):
                x = max(0, (screen_w - width) // 2)
                y = max(0, (screen_h - height) // 3)
            self.geometry(f'{width}x{height}+{x}+{y}')
        except tk.TclError:
            pass

    def _focus_search(self):
        self.search_entry.focus_set()
        self.search_entry.select_range(0, 'end')

    # -- layout -------------------------------------------------------------
    def _make_ui(self):
        bg, panel, navy, accent = '#edf2f8', '#ffffff', '#142e52', '#2b70c9'
        self.configure(bg=bg)
        style = ttk.Style(self)
        if 'clam' in style.theme_names():
            style.theme_use('clam')
        style.configure('Treeview', font=('Arial', 11), rowheight=32,
                        background='white', fieldbackground='white')
        style.configure('Treeview.Heading', font=('Arial', 10, 'bold'))
        style.map('Treeview', background=[('selected', '#d8e8ff')],
                  foreground=[('selected', '#102a50')])

        menu = tk.Menu(self)
        file_menu = tk.Menu(menu, tearoff=False)
        for label, command in (('Add ROM Folder…', self.add_folder),
                               ('Open ROM…', self.open_file),
                               ('Refresh Library', self.scan)):
            file_menu.add_command(label=label, command=command)
        file_menu.add_separator()
        file_menu.add_command(label='Exit', command=self.close)
        menu.add_cascade(label='File', menu=file_menu)
        self.file_menu = file_menu

        tools = tk.Menu(menu, tearoff=False)
        tools.add_command(label='RetroArch / Emulator Settings…', command=self.configure_emulator)
        tools.add_command(label='Auto-detect Backend', command=self.autodetect)
        tools.add_command(label='Download N64 Core', command=self.install_core)
        tools.add_command(label='Install Native Backend (macOS)', command=self.install_native_backend)
        tools.add_command(label='Controller Setup…', command=self.controller_setup)
        menu.add_cascade(label='Tools', menu=tools)
        self.tools_menu = tools

        appearance = tk.Menu(menu, tearoff=False)
        for choice in ('Light', 'Dark', 'System'):
            appearance.add_radiobutton(label=choice, variable=self.theme_choice,
                                       value=choice, command=self.change_theme)
        menu.add_cascade(label='Appearance', menu=appearance)
        self.appearance_menu = appearance

        help_menu = tk.Menu(menu, tearoff=False)
        help_menu.add_command(label='About', command=self._about)
        menu.add_cascade(label='Help', menu=help_menu)
        self.help_menu = help_menu
        self.menu_bar = menu
        self.config(menu=menu)

        header = tk.Frame(self, bg=navy, padx=22, pady=16)
        header.pack(fill='x')
        self.header_frame = header
        tk.Label(header, text='CATN64EMU 1.1', font=('Arial', 25, 'bold'),
                 fg='white', bg=navy).pack(side='left')
        tk.Label(header, text='N64 GAME LIBRARY  •  AC KONDO SOLUTIONS',
                 font=('Arial', 10, 'bold'), fg='#b8d9ff', bg=navy).pack(side='right')

        toolbar = tk.Frame(self, bg='#dfe9f5', padx=14, pady=10)
        toolbar.pack(fill='x')
        self.toolbar_frame = toolbar
        for text, command in (('＋ Add Games', self.add_folder),
                              ('Open ROM', self.open_file),
                              ('↻ Refresh', self.scan),
                              ('🎮 Controllers', self.controller_setup)):
            tk.Button(toolbar, text=text, command=command, padx=9).pack(side='left', padx=(0, 7))
        tk.Label(toolbar, text='Search', bg='#dfe9f5').pack(side='left', padx=(16, 6))
        self.search_entry = ttk.Entry(toolbar, textvariable=self.search)
        self.search_entry.pack(side='left', fill='x', expand=True)
        self.search_entry.bind('<Escape>', lambda _: self.search.set(''))

        body = tk.PanedWindow(self, orient='horizontal', bg=bg, sashwidth=5, bd=0)
        body.pack(fill='both', expand=True, padx=12, pady=12)
        self.body_frame = body

        sidebar = tk.Frame(body, bg=panel, width=195,
                           highlightbackground='#ccd9e9', highlightthickness=1)
        body.add(sidebar, minsize=160)
        tk.Label(sidebar, text='LIBRARY', bg=panel, fg=navy,
                 font=('Arial', 12, 'bold'), padx=15, pady=16).pack(anchor='w')
        for title, command in (('All Games', self.scan),
                               ('Add ROM Folder', self.add_folder),
                               ('Emulator Settings', self.configure_emulator),
                               ('Controller Setup', self.controller_setup)):
            tk.Button(sidebar, text=title, command=command, anchor='w', relief='flat',
                      bg=panel, fg=navy, padx=16, pady=10).pack(fill='x')

        center = tk.Frame(body, bg=panel, highlightbackground='#ccd9e9', highlightthickness=1)
        body.add(center, minsize=380)
        tk.Label(center, text='YOUR GAMES', bg=panel, fg=navy,
                 font=('Arial', 12, 'bold'), padx=15, pady=13).pack(anchor='w')
        list_wrap = tk.Frame(center, bg=panel)
        list_wrap.pack(fill='both', expand=True, padx=10, pady=(0, 10))
        self.tree = ttk.Treeview(list_wrap, columns=('game', 'type', 'location'),
                                 show='headings', selectmode='browse')
        for key, label, width, stretch in (('game', 'Game', 260, True),
                                           ('type', 'Format', 75, False),
                                           ('location', 'Location', 260, True)):
            self.tree.heading(key, text=label)
            self.tree.column(key, width=width, stretch=stretch)
        scroll = ttk.Scrollbar(list_wrap, orient='vertical', command=self.tree.yview)
        self.tree.configure(yscrollcommand=scroll.set)
        self.tree.pack(side='left', fill='both', expand=True)
        scroll.pack(side='right', fill='y')
        self.tree.bind('<Double-1>', self._on_double_click)
        self.tree.bind('<Return>', lambda _: self.launch_selected())
        self.tree.bind('<<TreeviewSelect>>', lambda _: self.update_details())

        details = tk.Frame(body, bg=panel, width=255,
                           highlightbackground='#ccd9e9', highlightthickness=1)
        body.add(details, minsize=210)
        tk.Label(details, text='GAME DETAILS', bg=panel, fg=navy,
                 font=('Arial', 12, 'bold'), pady=16).pack()
        self.detail = tk.StringVar(value='Select a ROM to view details.')
        tk.Label(details, textvariable=self.detail, wraplength=225, justify='left',
                 bg=panel, fg='#3b526e', padx=12, pady=20).pack(fill='x')
        tk.Label(details, text='Controller Profile', bg=panel, fg=navy,
                 font=('Arial', 10, 'bold')).pack(pady=(10, 4))
        self.profiles = ttk.Combobox(
            details, textvariable=self.controller_profile, state='readonly', width=23,
            values=['Auto (RetroArch)', 'Atari / Classic', 'NES / SNES',
                    'Nintendo Switch Pro', 'Xbox', 'PlayStation 3 / 4 / 5',
                    'Generic USB / Bluetooth'])
        self.profiles.pack(padx=12, fill='x')
        self.profiles.bind('<<ComboboxSelected>>', lambda _: self.save())
        ttk.Checkbutton(details, text='Start fullscreen', variable=self.fullscreen,
                        command=self.save).pack(pady=10)
        self.play_button = tk.Button(details, text='▶  PLAY GAME', command=self.launch_selected,
                                     bg=accent, fg='white', font=('Arial', 12, 'bold'),
                                     padx=18, pady=12)
        self.play_button.pack(fill='x', padx=12, pady=(14, 8))
        tk.Button(details, text='Controller Setup',
                  command=self.controller_setup).pack(fill='x', padx=12)

        bottom = tk.Frame(self, bg='#dfe9f5', padx=16, pady=9)
        bottom.pack(fill='x')
        self.bottom_frame = bottom
        self.status = tk.StringVar(value='Ready')
        self.status_label = tk.Label(bottom, textvariable=self.status, bg='#dfe9f5',
                                     fg='#324b66', anchor='w')
        self.status_label.pack(fill='x')

    def _about(self):
        messagebox.showinfo(
            APP,
            f'{APP} — Python N64 launcher\n© AC Kondo 1999–2026\n\n'
            'Parallel Launcher-inspired layout. Independent project, not an official port.\n'
            'Uses RetroArch/libretro or native Mupen64Plus.')

    def _on_double_click(self, event):
        if self.tree.identify_region(event.x, event.y) in ('heading', 'separator'):
            return
        if self.tree.identify_row(event.y):
            self.launch_selected()

    # -- theme --------------------------------------------------------------
    def system_is_dark(self):
        try:
            if sys.platform == 'darwin':
                result = subprocess.run(['defaults', 'read', '-g', 'AppleInterfaceStyle'],
                                        capture_output=True, text=True, timeout=2)
                return result.returncode == 0 and 'Dark' in result.stdout
            if sys.platform.startswith('win'):
                import winreg
                with winreg.OpenKey(
                        winreg.HKEY_CURRENT_USER,
                        r'Software\Microsoft\Windows\CurrentVersion\Themes\Personalize') as key:
                    return winreg.QueryValueEx(key, 'AppsUseLightTheme')[0] == 0
            return (os.environ.get('GTK_THEME', '').lower().endswith(':dark')
                    or os.environ.get('COLOR_SCHEME', '').lower() == 'dark')
        except (OSError, subprocess.TimeoutExpired, ValueError):
            return False

    def change_theme(self):
        self.apply_theme()
        self.save()

    def apply_theme(self):
        mode = self.theme_choice.get()
        dark = self.system_is_dark() if mode == 'System' else mode == 'Dark'
        c = ({'bg': '#151a24', 'panel': '#202838', 'header': '#101827',
              'toolbar': '#192333', 'fg': '#ecf2ff', 'muted': '#b1c1d8',
              'accent': '#397fe0', 'select': '#315887', 'border': '#384860',
              'input': '#111b2a', 'panel_alt': '#172130', 'link': '#66b5ff',
              'link_active': '#91caff'} if dark else
             {'bg': '#edf2f8', 'panel': '#ffffff', 'header': '#142e52',
              'toolbar': '#dfe9f5', 'fg': '#142e52', 'muted': '#3b526e',
              'accent': '#2b70c9', 'select': '#d8e8ff', 'border': '#ccd9e9',
              'input': '#ffffff', 'panel_alt': '#e8eff8', 'link': '#2b70c9',
              'link_active': '#1c4f92'})
        self.configure(bg=c['bg'])
        style = ttk.Style(self)
        if 'clam' in style.theme_names():
            style.theme_use('clam')
        style.configure('Treeview', background=c['input'], fieldbackground=c['input'],
                        foreground=c['fg'], rowheight=32, bordercolor=c['border'])
        style.configure('Treeview.Heading', background=c['toolbar'],
                        foreground=c['fg'], font=('Arial', 10, 'bold'))
        style.map('Treeview', background=[('selected', c['select'])],
                  foreground=[('selected', '#ffffff' if dark else c['header'])])
        style.configure('TFrame', background=c['panel'])
        style.configure('TLabel', background=c['panel'], foreground=c['fg'])
        style.configure('TButton', background=c['panel_alt'], foreground=c['link'],
                        padding=(10, 7), font=('Arial', 10, 'bold'))
        style.map('TButton',
                  background=[('pressed', c['select']), ('active', c['panel_alt']),
                              ('disabled', c['input'])],
                  foreground=[('pressed', c['header']), ('active', c['link_active']),
                              ('disabled', c['muted'])])
        style.configure('TCheckbutton', background=c['panel'], foreground=c['fg'])
        style.configure('TEntry', fieldbackground=c['input'], foreground=c['fg'])
        style.configure('TCombobox', fieldbackground=c['input'], foreground=c['fg'])
        style.map('TCombobox', fieldbackground=[('readonly', c['input'])],
                  foreground=[('readonly', c['fg'])])

        def repaint(widget):
            if isinstance(widget, tk.Menu):
                return
            if isinstance(widget, (tk.Toplevel, tk.Tk)):
                widget.configure(bg=c['bg'])
            elif isinstance(widget, tk.PanedWindow):
                widget.configure(bg=c['bg'])
            elif isinstance(widget, tk.Frame):
                if widget is getattr(self, 'header_frame', None):
                    paint = c['header']
                elif widget in (getattr(self, 'toolbar_frame', None),
                                getattr(self, 'bottom_frame', None)):
                    paint = c['toolbar']
                elif widget is getattr(self, 'body_frame', None):
                    paint = c['bg']
                else:
                    paint = c['panel']
                widget.configure(bg=paint)
                try:
                    if str(widget.cget('highlightthickness')) not in ('0', ''):
                        widget.configure(highlightbackground=c['border'])
                except tk.TclError:
                    pass
            elif isinstance(widget, tk.Label):
                try:
                    parent_bg = widget.master.cget('bg')
                except (tk.TclError, AttributeError):
                    parent_bg = c['panel']
                if parent_bg == c['header']:
                    widget.configure(bg=parent_bg, fg='#ffffff')
                elif widget is getattr(self, 'status_label', None):
                    widget.configure(bg=parent_bg, fg=c['muted'])
                else:
                    widget.configure(bg=parent_bg, fg=c['fg'])
            elif isinstance(widget, tk.Button):
                primary = widget is getattr(self, 'play_button', None)
                widget.configure(bg=c['accent'] if primary else c['panel_alt'],
                                 fg='#ffffff' if primary else c['link'],
                                 activebackground=c['select'] if primary else c['panel_alt'],
                                 activeforeground='#ffffff' if primary else c['link_active'],
                                 highlightbackground=c['border'], cursor='hand2')
            for child in widget.winfo_children():
                repaint(child)

        repaint(self)
        for menu in (getattr(self, 'file_menu', None), getattr(self, 'tools_menu', None),
                     getattr(self, 'help_menu', None), getattr(self, 'appearance_menu', None),
                     getattr(self, 'menu_bar', None)):
            try:
                menu.configure(bg=c['panel'], fg=c['fg'],
                               activebackground=c['select'], activeforeground=c['fg'])
            except (AttributeError, tk.TclError):
                pass

    # -- library ------------------------------------------------------------
    def add_folder(self):
        folder = filedialog.askdirectory(title='Choose N64 ROM folder')
        if not folder:
            return
        key = os.path.normcase(os.path.abspath(folder))
        if any(os.path.normcase(os.path.abspath(d)) == key for d in self.cfg['rom_dirs']):
            self.status.set('That folder is already in the library.')
            return
        self.cfg['rom_dirs'].append(folder)
        self.save()
        self.scan()

    def scan(self):
        self._scan_token += 1
        token = self._scan_token
        folders = list(self.cfg['rom_dirs'])
        if not folders:
            self.games = []
            self.populate()
            self.status.set('No ROM folders yet — use ＋ Add Games.')
            return
        self.status.set('Scanning library…')

        def work():
            found, seen = [], set()
            for folder in folders:
                root = Path(folder)
                if not root.is_dir():
                    continue
                try:
                    for path in root.rglob('*'):
                        if token != self._scan_token:
                            return
                        if not path.is_file() or path.suffix.lower() not in SCAN_EXTS:
                            continue
                        try:
                            key = str(path.resolve())
                        except OSError:
                            continue
                        if key in seen:
                            continue
                        seen.add(key)
                        name = read_header(path) if path.suffix.lower() in EXTS else path.stem
                        if name:
                            found.append((name, path))
                except (OSError, PermissionError):
                    continue
            found.sort(key=lambda item: item[0].casefold())
            try:
                self.after(0, lambda: self._finish_scan(token, found))
            except (RuntimeError, tk.TclError):
                pass

        threading.Thread(target=work, daemon=True).start()

    def _finish_scan(self, token, found):
        if token != self._scan_token:
            return
        self.games = found
        self.populate()

    def populate(self):
        if not hasattr(self, 'tree'):
            return
        self.tree.delete(*self.tree.get_children())
        self.visible.clear()
        query = self.search.get().strip().casefold()
        for name, path in self.games:
            if query and query not in (name + ' ' + path.name).casefold():
                continue
            item = self.tree.insert('', 'end',
                                    values=(name, path.suffix.upper().lstrip('.'), str(path)))
            self.visible[item] = path
        self.status.set(f'{len(self.visible)} games shown  •  {len(self.games)} total  •  '
                        'Double-click to launch')

    def update_details(self):
        path = self.selected_path()
        if not path:
            self.detail.set('Select a ROM to view details.')
            return
        self.detail.set(f'{path.stem}\n\nFormat: {path.suffix.upper().lstrip(".")}\n\n'
                        f'File: {path.name}\n\nDouble-click or press Play.')

    def selected_path(self):
        selection = self.tree.selection()
        return self.visible.get(selection[0]) if selection else None

    def open_file(self):
        chosen = filedialog.askopenfilename(
            title='Open Nintendo 64 ROM',
            filetypes=[('N64 ROMs and ZIPs', '*.z64 *.n64 *.v64 *.zip'), ('All files', '*.*')])
        if chosen:
            self.launch(Path(chosen))

    def launch_selected(self):
        path = self.selected_path()
        if not path:
            messagebox.showinfo(APP, 'Select a game, or click Open ROM.')
            return
        self.launch(path)

    # -- launching ----------------------------------------------------------
    def launch(self, path):
        exe = self.emulator.get().strip() or discover_emulator()
        configured = self.core.get().strip()
        core = configured if configured and Path(configured).is_file() else discover_core(exe)
        if core and core != configured:
            self.core.set(core)
            self.save()
        native = discover_standalone()

        if not retroarch_core_available(exe, core) and not native:
            if platform.system() == 'Darwin' and shutil.which('brew'):
                if messagebox.askyesno(
                        'Install native N64 backend?',
                        'No compatible RetroArch N64 core was found.\n\n'
                        'CatN64Emu can use native Mupen64Plus without a libretro core.\n'
                        'Install Mupen64Plus with Homebrew now?'):
                    self.install_native_backend(path)
            else:
                messagebox.showerror(
                    'N64 backend missing',
                    'No compatible N64 backend was found.\n\n'
                    'Install Mupen64Plus, or install RetroArch plus a matching N64 core.\n'
                    'CatN64Emu detects either backend automatically.')
            return

        try:
            rom = prepare_rom(path)
        except ValueError as exc:
            messagebox.showerror('Launch failed', str(exc))
            return

        try:
            if retroarch_core_available(exe, core):
                resolved = exe if Path(exe).is_file() else (shutil.which(exe) or exe)
                args = shlex.split(self.extra_args.get(), posix=(os.name != 'nt'))
                if self.fullscreen.get() and '--fullscreen' not in args:
                    args.append('--fullscreen')
                subprocess.Popen([resolved, '-L', core, *args, str(rom)],
                                 cwd=str(Path(resolved).resolve().parent))
                self.status.set('RetroArch launched: ' + path.name)
            else:
                resolved = native if Path(native).is_file() else (shutil.which(native) or native)
                subprocess.Popen([resolved, str(rom)], cwd=str(Path(resolved).resolve().parent))
                self.status.set('Native Mupen64Plus launched: ' + path.name)
        except (OSError, ValueError) as exc:
            messagebox.showerror('Launch failed', str(exc))

    # -- backends -----------------------------------------------------------
    def install_native_backend(self, pending_rom=None):
        brew = shutil.which('brew')
        if platform.system() != 'Darwin' or not brew:
            messagebox.showerror('Homebrew required',
                                 'Install Homebrew on macOS first, or install Mupen64Plus manually.')
            return
        if self._busy:
            self.status.set(self._busy + ' is already running…')
            return
        self._busy = 'Mupen64Plus install'
        self.status.set('Installing native Mupen64Plus using Homebrew...')

        def work():
            try:
                result = subprocess.run([brew, 'install', 'mupen64plus'],
                                        capture_output=True, text=True, timeout=900)
                if result.returncode:
                    raise RuntimeError((result.stderr or result.stdout)[-1600:]
                                       or 'Homebrew installation failed')
                installed = discover_standalone()
                if not installed:
                    raise RuntimeError('Homebrew finished but mupen64plus was not found.')

                def success():
                    self._busy = ''
                    self.status.set('Mupen64Plus installed: ' + installed)
                    if pending_rom:
                        self.launch(pending_rom)
                    else:
                        messagebox.showinfo('N64 backend installed',
                                            'Mupen64Plus is ready. Select a ROM to play.')
                self.after(0, success)
            except Exception as exc:
                def failure(message=str(exc)):
                    self._busy = ''
                    messagebox.showerror('Mupen64Plus installation failed', message)
                self.after(0, failure)

        threading.Thread(target=work, daemon=True).start()

    def install_core(self):
        if self._busy:
            self.status.set(self._busy + ' is already running…')
            return
        self._busy = 'N64 core download'
        self.status.set('Checking for an official N64 core...')

        def progress(message):
            self.after(0, lambda m=message: self.status.set(m))

        def work():
            try:
                installed = download_n64_core(progress)

                def done():
                    self._busy = ''
                    self.core.set(installed)
                    self.save()
                    messagebox.showinfo('N64 core installed',
                                        'Installed:\n' + installed +
                                        '\n\nYou can now launch games if RetroArch is installed.')
                self.after(0, done)
            except Exception as exc:
                def failure(message=str(exc)):
                    self._busy = ''
                    messagebox.showerror('Core installation failed', message)
                self.after(0, failure)

        threading.Thread(target=work, daemon=True).start()

    def autodetect(self):
        exe = discover_emulator()
        if exe:
            self.emulator.set(exe)
        core = discover_core(self.emulator.get())
        self.core.set(core)
        self.save()
        self.status.set(('RetroArch found' if exe else 'RetroArch not found')
                        + (' • N64 core found' if core else
                           (' • Native Mupen64Plus available' if discover_standalone()
                            else ' • N64 backend missing')))

    # -- dialogs ------------------------------------------------------------
    def _dialog(self, title, size):
        dialog = tk.Toplevel(self)
        dialog.title(title)
        dialog.geometry(size)
        dialog.transient(self)
        dialog.grab_set()
        dialog.bind('<Escape>', lambda _: close())
        dialog.protocol('WM_DELETE_WINDOW', close)

        def close():
            try:
                dialog.grab_release()
            except tk.TclError:
                pass
            dialog.destroy()

        dialog.close = close
        return dialog

    def configure_emulator(self):
        dialog = self._dialog('RetroArch + N64 Core Setup', '750x340')
        dialog.columnconfigure(1, weight=1)
        emulator = tk.StringVar(value=self.emulator.get())
        core = tk.StringVar(value=self.core.get())
        extra = tk.StringVar(value=self.extra_args.get())

        def browse_emulator():
            chosen = filedialog.askopenfilename(title='Choose RetroArch executable')
            if chosen:
                emulator.set(chosen)
                if not core.get():
                    core.set(discover_core(chosen))

        def browse_core():
            chosen = filedialog.askopenfilename(
                title='Choose N64 libretro core',
                filetypes=[('Libretro cores', '*.dylib *.so *.dll'), ('All files', '*.*')])
            if chosen:
                core.set(chosen)

        def commit():
            self.emulator.set(emulator.get().strip())
            self.core.set(core.get().strip())
            self.extra_args.set(extra.get().strip())
            self.save()
            dialog.close()

        tk.Label(dialog, text='RetroArch executable:').grid(row=0, column=0, padx=12, pady=12, sticky='w')
        ttk.Entry(dialog, textvariable=emulator).grid(row=0, column=1, sticky='ew', padx=5)
        tk.Button(dialog, text='Browse…', command=browse_emulator).grid(row=0, column=2, padx=12)
        tk.Label(dialog, text='N64 libretro core:').grid(row=1, column=0, padx=12, pady=12, sticky='w')
        ttk.Entry(dialog, textvariable=core).grid(row=1, column=1, sticky='ew', padx=5)
        tk.Button(dialog, text='Browse…', command=browse_core).grid(row=1, column=2, padx=12)
        tk.Label(dialog, text='Extra RetroArch arguments:').grid(row=2, column=0, padx=12, pady=8, sticky='w')
        ttk.Entry(dialog, textvariable=extra).grid(row=2, column=1, columnspan=2, sticky='ew', padx=5)
        info = ('Portable runtime: put RetroArch in catn64emu_runtime/ and your N64 core in\n'
                'catn64emu_runtime/cores/. The launcher auto-selects the core with -L.\n'
                'Alternatively install RetroArch and download Mupen64Plus-Next in its Online Updater.\n'
                'If RetroArch has no compatible core, CatN64Emu uses native Mupen64Plus.\n'
                'Install N64 Backend uses Homebrew on macOS (with your approval).')
        tk.Label(dialog, text=info, justify='left').grid(row=3, column=0, columnspan=3,
                                                         padx=12, pady=12, sticky='w')
        tk.Button(dialog, text='Install N64 Backend',
                  command=lambda: self.install_native_backend()).grid(row=4, column=0, padx=12, pady=8)
        tk.Button(dialog, text='Auto-detect',
                  command=self.autodetect).grid(row=4, column=1, sticky='e', pady=8)
        tk.Button(dialog, text='Save Settings', command=commit, padx=15).grid(row=4, column=2, padx=12, pady=8)

    def controller_setup(self):
        dialog = self._dialog('CatN64Emu — Controller Setup', '590x460')
        frame = ttk.Frame(dialog, padding=18)
        frame.pack(fill='both', expand=True)
        ttk.Label(frame, text='Bluetooth & USB Controllers',
                  font=('Arial', 16, 'bold')).pack(anchor='w', pady=(0, 10))
        text = ('CatN64Emu uses RetroArch controller autoconfiguration when the RetroArch '
                'backend is active.\n\n'
                '1. Pair your controller in macOS System Settings → Bluetooth (or your OS Bluetooth settings).\n'
                '2. Connect via USB if Bluetooth is unsupported.\n'
                '3. Open RetroArch → Settings → Input → RetroPad Binds / Port 1 Controls.\n'
                '4. Use Online Updater → Update Controller Profiles if necessary.\n\n'
                'Supported when drivers and profiles exist: DualSense (PS5), DualShock, Xbox, '
                'Switch Pro, and many generic Bluetooth/USB gamepads.\n\n'
                'Vintage Atari controllers generally need a USB/Bluetooth adapter that exposes '
                'standard gamepad input. Not every Atari device is plug-and-play.\n\n'
                'Note: Native Mupen64Plus controller mapping is configured separately using '
                'its input plugin.')
        ttk.Label(frame, text=text, wraplength=535, justify='left').pack(anchor='w')
        ttk.Button(frame, text='Open Bluetooth Settings',
                   command=self.open_bluetooth).pack(anchor='w', pady=(15, 5))
        ttk.Button(frame, text='Close', command=dialog.close).pack(anchor='e')

    def open_bluetooth(self):
        try:
            if sys.platform == 'darwin':
                subprocess.Popen(['open', 'x-apple.systempreferences:com.apple.BluetoothSettings'])
            elif sys.platform.startswith('win'):
                subprocess.Popen(['start', 'ms-settings:bluetooth'], shell=True)
            else:
                messagebox.showinfo('Bluetooth',
                                    'Open your system Bluetooth settings and pair your controller.')
        except OSError as exc:
            messagebox.showerror('Bluetooth settings', str(exc))

    # -- lifecycle ----------------------------------------------------------
    def save(self):
        self.cfg['emulator'] = self.emulator.get().strip()
        self.cfg['core'] = self.core.get().strip()
        self.cfg['extra_args'] = self.extra_args.get().strip()
        self.cfg['controller_profile'] = self.controller_profile.get()
        self.cfg['fullscreen'] = self.fullscreen.get()
        self.cfg['geometry'] = self.geometry()
        self.cfg['theme'] = self.theme_choice.get()
        try:
            write_settings(self.cfg)
        except OSError as exc:
            self.status.set('Could not save settings: ' + str(exc))

    def close(self):
        if self._closing:
            return
        self._closing = True
        self._scan_token += 1
        self.save()
        self.destroy()


def main():
    prune_cache()
    try:
        Launcher().mainloop()
    except tk.TclError as exc:
        print('Tkinter GUI unavailable:', exc, file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
