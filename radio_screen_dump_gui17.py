#!/usr/bin/env python3
"""
radio_screen_gui_full_rebuild.py

Rebuilt end-to-end script:
- Reads QuanshengDock UI packets (0xB5...) from serial @38400
- Renders screen in a scalable Tkinter canvas
- Shows BOTH cursor arrows (A/B VFO indication derived from active cursor row)
- On-screen keypad: sends REAL keycodes (no latch logic; FN is just '#')
- Keyboard controls (FIXED): uses event.keycode tracking so it doesn't "die" after first key
    * digits (top row + numpad) -> digit keys
    * '#' -> FN/# key
    * '*' -> SCAN
    * ESC -> EXIT
    * ENTER -> MENU
    * Up/Down arrows -> UP/DN
    * Spacebar -> PTT HOLD (press/release)
- Focus safety: clears stuck keys on focus-out and releases PTT

Install:
  pip install pyserial

Run:
  python3 radio_screen_gui_full_rebuild.py /dev/ttyUSB0
"""

import time
import argparse
import threading
import queue
import serial
from dataclasses import dataclass
from typing import Dict, Optional, Tuple

# --------------------------------------------------------------------------
# Protocol constants
# --------------------------------------------------------------------------
PKT_KEYPRESS  = 0x0801
PKT_GETSCREEN = 0x0803

DEFAULT_RELEASE_KEY = 19      # "key up"
DEFAULT_PTT_HOLD    = 16      # hold-to-TX (careful)

# XOR stream for AB/CD packets (matches QuanshengDock)
XOR_ARRAY = bytes([
    0x16, 0x6c, 0x14, 0xe6, 0x2e, 0x91, 0x0d, 0x40,
    0x21, 0x35, 0xd5, 0x40, 0x13, 0x03, 0xe9, 0x80
])

# Logical LCD size (dock UI coordinates)
LCD_W = 128
LCD_H = 64
ROW_H = 8  # pixels per row

# Your digit labels (visual only)
DIGIT_FUNCS = {
    "1": "BAND",
    "2": "A/B",
    "3": "VFO/MR",
    "4": "FC",
    "5": "NOAA",
    "6": "TX PWR",
    "7": "VOX",
    "8": "R",
    "9": "CALL",
    "0": "FM",
}

# Keycodes (confirmed from your Python + dock code)
KEYCODES: Dict[str, int] = {
    # digits: 32 + digit
    "0": 32, "1": 33, "2": 34, "3": 35, "4": 36,
    "5": 37, "6": 38, "7": 39, "8": 40, "9": 41,
    "MENU": 42,
    "UP":   43,
    "DN":   44,
    "EXIT": 45,
    "*":    46,   # SCAN
    "#":    47,   # FN/# (treated like normal key)
    "PTT_TAP": 48,
    "F2":   49,
    "F1":   50,
}

# --------------------------------------------------------------------------
# Low-level encode / send (matches QuanshengDock.Comms.SendCommand2)
# --------------------------------------------------------------------------
def crypt(b: int, i: int) -> int:
    return b ^ XOR_ARRAY[i & 0x0F]

def crc16_byte(byt: int, crc: int) -> int:
    crc ^= (byt << 8)
    for _ in range(8):
        crc <<= 1
        if crc > 0xFFFF:
            crc ^= 0x1021
            crc &= 0xFFFF
    return crc

def send_command(ser: serial.Serial, cmd: int, payload: bytes = b"") -> None:
    """
    Frame:
      AB CD [len:u16] [xor(payload(cmd+prmlen+payload)+crc16)] DC BA
    CRC16 is computed over plain bytes (cmd + prmLen + payload), then the CRC bytes are XOR'd too.
    """
    prm_len = len(payload)

    plain = bytearray()
    plain += cmd.to_bytes(2, "little")
    plain += prm_len.to_bytes(2, "little")
    plain += payload

    crc = 0
    for bb in plain:
        crc = crc16_byte(bb, crc)

    enc = bytearray()
    for i, bb in enumerate(plain):
        enc.append(crypt(bb, i))

    xor_i = len(plain)
    enc.append(crypt(crc & 0xFF, xor_i)); xor_i += 1
    enc.append(crypt((crc >> 8) & 0xFF, xor_i))

    enc_len_field = 4 + prm_len  # cmd(2)+prmlen(2)+payload

    frame = bytearray()
    frame += b"\xAB\xCD"
    frame += enc_len_field.to_bytes(2, "little")
    frame += enc
    frame += b"\xDC\xBA"

    ser.write(frame)
    ser.flush()

def send_keypress(ser: serial.Serial, keycode: int) -> None:
    send_command(ser, PKT_KEYPRESS, int(keycode).to_bytes(2, "little"))

def press_for_ms(ser: serial.Serial, keycode: int, release_key: Optional[int], down_ms: int) -> None:
    send_keypress(ser, keycode)
    if release_key is not None:
        time.sleep(max(0, down_ms) / 1000.0)
        send_keypress(ser, release_key)

def tap_key(ser: serial.Serial, keycode: int, release_key: Optional[int], down_ms: int = 60) -> None:
    press_for_ms(ser, keycode, release_key, down_ms)

# --------------------------------------------------------------------------
# UI packet parser (0xB5...)
# --------------------------------------------------------------------------
class Parser:
    IDLE, CD, LEN_LSB, LEN_MSB, DATA, CRC_LSB, CRC_MSB, DC, BA = range(9)
    UI_TYPE, UI_V1, UI_V2, UI_V3, UI_LEN, UI_DATA = range(9, 15)

    def __init__(self, on_ui_packet):
        self.stage = self.IDLE
        self.p_len = 0
        self.p_cnt = 0
        self.ui_type = 0
        self.v1 = 0
        self.v2 = 0
        self.v3 = 0
        self.ui_len = 0
        self.ui_buf = bytearray()
        self.ui_need = 0
        self.on_ui_packet = on_ui_packet

    def feed(self, b: int):
        s = self.stage

        if s == self.IDLE:
            if b == 0xAB:
                self.stage = self.CD
            elif b == 0xB5:
                self.stage = self.UI_TYPE
            return

        # AB CD framed packet: ignore content (we only care about 0xB5 UI packets)
        if s == self.CD:
            self.stage = self.LEN_LSB if b == 0xCD else self.IDLE
            return
        if s == self.LEN_LSB:
            self.p_len = b
            self.stage = self.LEN_MSB
            return
        if s == self.LEN_MSB:
            self.p_len |= (b << 8)
            self.p_cnt = 0
            self.stage = self.DATA
            return
        if s == self.DATA:
            self.p_cnt += 1
            if self.p_cnt >= self.p_len:
                self.stage = self.CRC_LSB
            return
        if s == self.CRC_LSB:
            self.stage = self.CRC_MSB
            return
        if s == self.CRC_MSB:
            self.stage = self.DC
            return
        if s == self.DC:
            self.stage = self.BA if b == 0xDC else self.IDLE
            return
        if s == self.BA:
            self.stage = self.IDLE
            return

        # UI packet
        if s == self.UI_TYPE:
            self.ui_type = b
            self.stage = self.UI_V1
            return
        if s == self.UI_V1:
            self.v1 = b
            self.stage = self.UI_V2
            return
        if s == self.UI_V2:
            self.v2 = b
            self.stage = self.UI_V3
            return
        if s == self.UI_V3:
            self.v3 = b
            self.stage = self.UI_LEN
            return
        if s == self.UI_LEN:
            self.ui_len = b
            self.ui_buf.clear()
            self.ui_need = 0 if self.ui_type == 6 else self.ui_len
            if self.ui_need == 0:
                self.on_ui_packet(self.ui_type, self.v1, self.v2, self.v3, self.ui_len, b"")
                self.stage = self.IDLE
            else:
                self.stage = self.UI_DATA
            return
        if s == self.UI_DATA:
            self.ui_buf.append(b)
            if len(self.ui_buf) >= self.ui_need:
                self.on_ui_packet(self.ui_type, self.v1, self.v2, self.v3, self.ui_len, bytes(self.ui_buf))
                self.stage = self.IDLE
            return

# --------------------------------------------------------------------------
# UI helpers
# --------------------------------------------------------------------------
def ui_unpack_xy(v1: int, v2: int) -> Tuple[int, int]:
    x = v1
    row = v2
    while x > 128:
        row += 1
        x -= 128
    return x, row

def decode_battery(lenb: int) -> Tuple[float, float]:
    volts = min(lenb * 0.04, 8.4)
    pct = lenb / 2.1
    return volts, pct

def looks_like_freq(s: str) -> bool:
    return ("." in s) and any(c.isdigit() for c in s)

# --------------------------------------------------------------------------
# Scalable LCD renderer
# --------------------------------------------------------------------------
@dataclass
class DrawTextCmd:
    x: int
    row: int
    scale: float
    text: str

class LCDView:
    def __init__(self, canvas, status_var, debug_grid=False):
        self.canvas = canvas
        self.status_var = status_var
        self.debug_grid = debug_grid

        self._px_scale = 4.0
        self._off_x = 0.0
        self._off_y = 0.0

        self.buffer: Dict[str, DrawTextCmd] = {}
        self._font_cache = {}

        import tkinter.font as tkfont
        self._tkfont = tkfont
        self.btn_font = tkfont.Font(family="DejaVu Sans Mono", size=11)

        self.canvas.bind("<Configure>", self._on_resize)

    def set_status(self, text: str) -> None:
        self.status_var.set(text)

    def _calc_scale(self, w: int, h: int) -> None:
        if w <= 1 or h <= 1:
            return
        scale = min(w / LCD_W, h / LCD_H)
        scale = max(1.0, scale)

        self._px_scale = scale
        self._off_x = (w - LCD_W * scale) / 2.0
        self._off_y = (h - LCD_H * scale) / 2.0

        self.btn_font.configure(size=int(max(10, round(11.0 * (scale / 4.0)))))
        self._font_cache.clear()

    def _on_resize(self, evt) -> None:
        self._calc_scale(evt.width, evt.height)
        self.redraw_all()

    def _px(self, x: float, y: float) -> Tuple[float, float]:
        return (self._off_x + x * self._px_scale, self._off_y + y * self._px_scale)

    def clear_lines(self, y1: int, y2: int) -> None:
        kill = [tag for tag, cmd in self.buffer.items() if y1 <= cmd.row <= y2]
        for tag in kill:
            self.buffer.pop(tag, None)
        for r in range(y1, y2 + 1):
            self.canvas.delete(f"row_{r}")

    def _font(self, size: int):
        f = self._font_cache.get(size)
        if f is None:
            f = self._tkfont.Font(family="DejaVu Sans Mono", size=size)
            self._font_cache[size] = f
        return f

    def draw_text(self, cmd: DrawTextCmd, tag_key: str) -> None:
        self.buffer[tag_key] = cmd
        self._draw_one(tag_key, cmd)

    def delete_tag(self, tag_key: str) -> None:
        self.buffer.pop(tag_key, None)
        self.canvas.delete(tag_key)

    def _draw_one(self, tag_key: str, cmd: DrawTextCmd) -> None:
        self.canvas.delete(tag_key)
        xpx, ypx = self._px(cmd.x, cmd.row * ROW_H)
        base = 10.0 * (self._px_scale / 4.0) * cmd.scale
        size = int(max(6, round(base)))
        font = self._font(size)

        self.canvas.create_text(
            xpx, ypx,
            text=cmd.text,
            fill="white",
            font=font,
            anchor="nw",
            tags=(f"row_{cmd.row}", tag_key)
        )

    def redraw_all(self) -> None:
        self.canvas.delete("all")
        if self.debug_grid:
            for r in range(0, 9):
                x0, y0 = self._px(0, r * ROW_H)
                x1, y1 = self._px(LCD_W, r * ROW_H)
                self.canvas.create_line(x0, y0, x1, y1, fill="#222")
        for tag, cmd in self.buffer.items():
            self._draw_one(tag, cmd)

# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description="Quansheng UI screen + keypad + keyboard (rebuild)")
    ap.add_argument("device", help="Serial device, e.g. /dev/ttyUSB0")
    ap.add_argument("--baud", type=int, default=38400)
    ap.add_argument("--debug-grid", action="store_true")
    ap.add_argument("--release", type=int, default=DEFAULT_RELEASE_KEY,
                    help="Release keycode (default 19). Use -1 to disable.")
    ap.add_argument("--ptt-hold", type=int, default=DEFAULT_PTT_HOLD,
                    help="PTT hold-down keycode (default 16). CAREFUL: can TX.")
    ap.add_argument("--keydown-ms", type=int, default=60,
                    help="Default key down time for taps (ms).")
    args = ap.parse_args()

    release_key: Optional[int] = None if args.release == -1 else args.release
    ptt_hold_key = int(args.ptt_hold)
    keydown_ms = max(10, int(args.keydown_ms))

    q_events: "queue.Queue[tuple]" = queue.Queue()

    def on_ui_packet(t: int, v1: int, v2: int, v3: int, data_len_byte: int, data: bytes):
        q_events.put((t, v1, v2, v3, data_len_byte, data))

    ser = serial.Serial(args.device, baudrate=args.baud, bytesize=8, parity="N", stopbits=1, timeout=0.2)
    print(f"Opened {args.device} @ {args.baud}. Ctrl+C to stop.")
    print("Keycodes: #/FN=47 (0x2F), digits 0..9=32..41.")

    # Nudge redraw
    try:
        press_for_ms(ser, 13, release_key, 50)
        time.sleep(0.05)
        send_command(ser, PKT_GETSCREEN, b"")
    except Exception as e:
        print(f"Warning: init poke failed: {e}")

    parser = Parser(on_ui_packet)
    stop_flag = threading.Event()
    send_lock = threading.Lock()

    def reader_thread():
        try:
            while not stop_flag.is_set():
                chunk = ser.read(4096)
                if not chunk:
                    continue
                for b in chunk:
                    parser.feed(b)
        except Exception as e:
            q_events.put(("__ERR__", str(e)))
        finally:
            try:
                ser.close()
            except Exception:
                pass

    threading.Thread(target=reader_thread, daemon=True).start()

    # ---------------- Tk UI ----------------
    import tkinter as tk

    root = tk.Tk()
    root.title("Radio Screen (Scalable) + Keypad + Keyboard")
    root.minsize(520, 420)

    root.grid_rowconfigure(1, weight=1)
    root.grid_columnconfigure(0, weight=1)

    status_var = tk.StringVar(value="(waiting...)")
    tk.Label(root, textvariable=status_var, anchor="w").grid(row=0, column=0, sticky="ew", padx=6, pady=(6, 2))

    canvas = tk.Canvas(root, bg="black", highlightthickness=0)
    canvas.grid(row=1, column=0, sticky="nsew", padx=6, pady=6)

    view = LCDView(canvas, status_var, debug_grid=args.debug_grid)

    # VFO derived from cursor rows
    vfo_state = {"which": "?"}
    cursor_rows: Dict[int, int] = {}
    last_cursor_row = {"row": None}

    def clear_cursor_rows(y1: int, y2: int) -> None:
        dead = [r for r in cursor_rows.keys() if y1 <= r <= y2]
        for r in dead:
            view.delete_tag(f"cursor_{r}")
            cursor_rows.pop(r, None)

    def derive_vfo_from_cursors() -> None:
        active_rows = [r for r, st in cursor_rows.items() if st != 0]
        if active_rows:
            r = active_rows[0]
        elif last_cursor_row["row"] is not None:
            r = last_cursor_row["row"]
        else:
            vfo_state["which"] = "?"
            return
        vfo_state["which"] = "A" if r < 4 else "B"

    def do_getscreen():
        with send_lock:
            send_command(ser, PKT_GETSCREEN, b"")

    def do_key(label: str, ms: int = None):
        if ms is None:
            ms = keydown_ms
        with send_lock:
            tap_key(ser, KEYCODES[label], release_key, down_ms=ms)

    def ptt_press():
        with send_lock:
            send_keypress(ser, ptt_hold_key)

    def ptt_release():
        if release_key is None:
            return
        with send_lock:
            send_keypress(ser, release_key)

    # ---------------- Keypad layout ----------------
    pad = tk.Frame(root)
    pad.grid(row=2, column=0, sticky="ew", padx=6, pady=(0, 6))
    pad.grid_columnconfigure(0, weight=1)
    pad.grid_columnconfigure(1, weight=1)

    topbar = tk.Frame(pad)
    topbar.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 6))
    topbar.grid_columnconfigure(0, weight=1)

    tk.Label(topbar, text="FN is just # (47). Press # then digit for function.", anchor="w").grid(row=0, column=0, sticky="w")
    tk.Button(topbar, text="GetScreen", command=do_getscreen, font=view.btn_font, takefocus=0).grid(row=0, column=1, sticky="e")

    kp = tk.Frame(pad)
    kp.grid(row=1, column=0, sticky="nsew")
    nav = tk.Frame(pad)
    nav.grid(row=1, column=1, sticky="nsew", padx=(10, 0))

    for r in range(4):
        kp.grid_rowconfigure(r, weight=1, uniform="kpr")
    for c in range(3):
        kp.grid_columnconfigure(c, weight=1, uniform="kpc")

    grid = [
        ["1","2","3"],
        ["4","5","6"],
        ["7","8","9"],
        ["*","0","#"],
    ]

    def label_text(k: str) -> str:
        if k.isdigit():
            return f"{k}\n{DIGIT_FUNCS.get(k,'')}"
        if k == "#":
            return "FN (#)"
        if k == "*":
            return "SCAN (*)"
        return k

    btns: Dict[str, "tk.Button"] = {}

    for r, row in enumerate(grid):
        for c, key in enumerate(row):
            b = tk.Button(
                kp,
                text=label_text(key),
                font=view.btn_font,
                takefocus=0,
                command=lambda K=key: do_key(K)
            )
            b.grid(row=r, column=c, sticky="nsew", padx=2, pady=2)
            btns[key] = b

    for i, key in enumerate(["UP", "DN", "MENU", "EXIT", "F1", "F2", "PTT_TAP"]):
        btxt = "PTT" if key == "PTT_TAP" else key
        b = tk.Button(
            nav,
            text=btxt,
            font=view.btn_font,
            takefocus=0,
            command=lambda K=key: do_key(K)
        )
        b.grid(row=i, column=0, sticky="ew", padx=2, pady=2)
        nav.grid_rowconfigure(i, weight=1)
        btns[key] = b

    ptt_hold_btn = tk.Button(nav, text="PTT HOLD (space)", font=view.btn_font, takefocus=0)
    ptt_hold_btn.grid(row=7, column=0, sticky="ew", padx=2, pady=(10, 2))
    nav.grid_rowconfigure(7, weight=1)
    ptt_hold_btn.bind("<ButtonPress-1>", lambda _e: ptt_press())
    ptt_hold_btn.bind("<ButtonRelease-1>", lambda _e: ptt_release())

    # Force focus into app so keyboard works reliably
    root.after(100, root.focus_force)

    # ---------------- Keyboard bindings (FIXED) ----------------
    down = set()

    def normalize_digit_key(event) -> Optional[str]:
        ks = event.keysym
        if ks.isdigit():
            return ks
        if ks.startswith("KP_") and ks[3:].isdigit():
            return ks[3:]
        return None

    def on_focus_out(_evt):
        down.clear()
        ptt_release()

    root.bind("<FocusOut>", on_focus_out)

    def keypress_handler(event):
        # robust anti-repeat: track by keycode
        if event.keycode in down:
            return
        down.add(event.keycode)

        d = normalize_digit_key(event)
        if d is not None and d in btns:
            btns[d].invoke()
            return

        if event.char == "#":
            btns["#"].invoke()
            return

        if event.char == "*" and "*" in btns:
            btns["*"].invoke()
            return

        if event.keysym == "Escape":
            btns["EXIT"].invoke()
            return

        if event.keysym in ("Return", "KP_Enter"):
            btns["MENU"].invoke()
            return

        if event.keysym == "space":
            ptt_press()
            return

        if event.keysym == "Up":
            btns["UP"].invoke()
            return

        if event.keysym == "Down":
            btns["DN"].invoke()
            return

    def keyrelease_handler(event):
        down.discard(event.keycode)
        if event.keysym == "space":
            ptt_release()

    root.bind_all("<KeyPress>", keypress_handler)
    root.bind_all("<KeyRelease>", keyrelease_handler)

    # ---------------- Screen processing ----------------
    last_freq_by_row: Dict[int, str] = {}

    def process_events():
        while True:
            try:
                evt = q_events.get_nowait()
            except queue.Empty:
                break

            if evt and evt[0] == "__ERR__":
                view.set_status(f"Serial reader error: {evt[1]}")
                continue

            ui_t, v1, v2, v3, lenb, data = evt

            if ui_t == 5:  # CLEAR
                view.clear_lines(v1, v2)
                clear_cursor_rows(v1, v2)
                continue

            if ui_t == 6:  # STATUS
                derive_vfo_from_cursors()
                volts, pct = decode_battery(lenb)
                view.set_status(
                    f"VFO={vfo_state['which']} | flags1=0x{v1:02X} flags2=0x{v2:02X} | "
                    f"bat≈{volts:.2f}V ({pct:.0f}%) | keydown={keydown_ms}ms"
                )
                continue

            if ui_t == 7:  # CURSOR
                row = int(v1)
                style = int(v2)
                cursor_rows[row] = style
                last_cursor_row["row"] = row
                glyph = "▻" if style == 0 else "➤"
                view.draw_text(DrawTextCmd(x=0, row=row, scale=1.0, text=glyph), tag_key=f"cursor_{row}")
                continue

            if ui_t in (0, 1, 2, 3):  # TEXT variants
                x, row = ui_unpack_xy(v1, v2)
                text = data.decode("ascii", errors="replace")

                # mimic QuanshengDock scaling rules
                if ui_t == 0:
                    scale = 1.5
                    row = row + 1
                elif ui_t == 3:
                    scale = 2.0
                    row = row + 1
                else:
                    scale = v3 / 6.0
                    row = row + 1

                if ui_t == 3 and looks_like_freq(text):
                    prev = last_freq_by_row.get(row)
                    if prev != text:
                        last_freq_by_row[row] = text
                        which = "TOP" if row <= 2 else "BOT"
                        print(f"FREQ {which}: {text} MHz")

                tag = f"cell_{ui_t}_{row}_{x}"
                view.draw_text(DrawTextCmd(x=x, row=row, scale=scale, text=text), tag_key=tag)

        root.after(20, process_events)

    root.after(20, process_events)

    def on_close():
        stop_flag.set()
        try:
            ser.close()
        except Exception:
            pass
        root.destroy()

    root.protocol("WM_DELETE_WINDOW", on_close)

    try:
        root.mainloop()
    finally:
        stop_flag.set()
        try:
            ser.close()
        except Exception:
            pass

if __name__ == "__main__":
    main()
