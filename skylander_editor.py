#!/usr/bin/env python3
"""
Skylanders Figure Editor
========================
Edit the stats in a Skylanders figure dump (.bin / .sky / .dmp, or a Flipper
Zero .nfc file): XP, gold, hero points, nickname, hat and skill bits.

    python3 skylander_editor.py [dump]        open the GUI (optionally with a file)
    python3 skylander_editor.py --info FILE   print what is in a dump
    python3 skylander_editor.py --convert SRC DST
                                              convert between .bin / .sky / .dmp / .nfc
                                              (the target format follows DST's extension)
    python3 skylander_editor.py --selftest    run the built-in checks

No third-party packages are needed (AES-128 is built in; pycryptodome is used
automatically if it happens to be installed).  The GUI needs tkinter:

    sudo apt install python3-tk

Format notes come from the community reverse-engineering of the figure data
(SkyReader and the "Skylander portal demystified" notes).  The XP / gold /
hero point / name / hat layout was documented for Spyro's Adventure; later
games reuse the same container, but ALWAYS EDIT A COPY of your dump first.
A .bak copy of the original is also made the first time you save over a file.

File formats: .bin, .sky and .dmp are all the same thing, a raw 1024-byte dump of
the figure (what the Dolphin emulated portal, SkyReader and most dumpers use), so
converting between them just means saving under another name.  A Flipper Zero .nfc
file wraps the same 1024 bytes in a text header.  Converting keeps the data exactly
as it is (encrypted stays encrypted).  Note: a raw dump only contains the sector
keys if the dumper wrote them into the sector trailers; a Flipper .nfc made from a
raw dump uses whatever trailers the dump holds.
"""
import hashlib
import json
import socket
import time
import os
import re
import shutil
import sys

APP = "Skylanders Figure Editor"

# ---------------------------------------------------------------------------
# AES-128 (ECB).  Pure-python fallback so the tool works with zero installs.
# ---------------------------------------------------------------------------
try:  # optional speed-up
    from Crypto.Cipher import AES as _PYCRYPTODOME_AES
except Exception:  # pragma: no cover
    _PYCRYPTODOME_AES = None


def _rotl8(x, n):
    return ((x << n) | (x >> (8 - n))) & 0xFF


def _build_sbox():
    sbox = [0] * 256
    p = q = 1
    while True:
        p = (p ^ ((p << 1) & 0xFF) ^ (0x1B if p & 0x80 else 0)) & 0xFF
        q ^= (q << 1) & 0xFF
        q ^= (q << 2) & 0xFF
        q ^= (q << 4) & 0xFF
        if q & 0x80:
            q ^= 0x09
        sbox[p] = q ^ _rotl8(q, 1) ^ _rotl8(q, 2) ^ _rotl8(q, 3) ^ _rotl8(q, 4) ^ 0x63
        if p == 1:
            break
    sbox[0] = 0x63
    return sbox


def _gmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a = ((a << 1) ^ (0x1B if a & 0x80 else 0)) & 0xFF
        b >>= 1
    return r


_SBOX = _build_sbox()
_INV_SBOX = [0] * 256
for _i, _v in enumerate(_SBOX):
    _INV_SBOX[_v] = _i
_MUL = {n: [_gmul(x, n) for x in range(256)] for n in (2, 3, 9, 11, 13, 14)}
_SR = [(i % 4) + 4 * (((i // 4) + (i % 4)) % 4) for i in range(16)]
_ISR = [(i % 4) + 4 * (((i // 4) - (i % 4)) % 4) for i in range(16)]


class _PyAES128:
    def __init__(self, key):
        w = [list(key[i:i + 4]) for i in range(0, 16, 4)]
        rcon = 1
        for i in range(4, 44):
            t = list(w[i - 1])
            if i % 4 == 0:
                t = [_SBOX[b] for b in t[1:] + t[:1]]
                t[0] ^= rcon
                rcon = _MUL[2][rcon]
            w.append([a ^ b for a, b in zip(w[i - 4], t)])
        self.rk = [sum(w[4 * r:4 * r + 4], []) for r in range(11)]

    def encrypt(self, block):
        rk, m2, m3 = self.rk, _MUL[2], _MUL[3]
        s = [a ^ b for a, b in zip(block, rk[0])]
        for r in range(1, 10):
            s = [_SBOX[s[j]] for j in _SR]
            out = []
            for c in range(0, 16, 4):
                a0, a1, a2, a3 = s[c:c + 4]
                out += [m2[a0] ^ m3[a1] ^ a2 ^ a3, a0 ^ m2[a1] ^ m3[a2] ^ a3,
                        a0 ^ a1 ^ m2[a2] ^ m3[a3], m3[a0] ^ a1 ^ a2 ^ m2[a3]]
            s = [a ^ b for a, b in zip(out, rk[r])]
        s = [_SBOX[s[j]] for j in _SR]
        return bytes(a ^ b for a, b in zip(s, rk[10]))

    def decrypt(self, block):
        rk, m9, m11, m13, m14 = self.rk, _MUL[9], _MUL[11], _MUL[13], _MUL[14]
        s = [a ^ b for a, b in zip(block, rk[10])]
        for r in range(9, 0, -1):
            s = [_INV_SBOX[s[j]] for j in _ISR]
            s = [a ^ b for a, b in zip(s, rk[r])]
            out = []
            for c in range(0, 16, 4):
                a0, a1, a2, a3 = s[c:c + 4]
                out += [m14[a0] ^ m11[a1] ^ m13[a2] ^ m9[a3], m9[a0] ^ m14[a1] ^ m11[a2] ^ m13[a3],
                        m13[a0] ^ m9[a1] ^ m14[a2] ^ m11[a3], m11[a0] ^ m13[a1] ^ m9[a2] ^ m14[a3]]
            s = out
        s = [_INV_SBOX[s[j]] for j in _ISR]
        return bytes(a ^ b for a, b in zip(s, rk[0]))


def aes_ecb_block(key, block, decrypt):
    if _PYCRYPTODOME_AES is not None:
        c = _PYCRYPTODOME_AES.new(key, _PYCRYPTODOME_AES.MODE_ECB)
        return c.decrypt(block) if decrypt else c.encrypt(block)
    c = _PyAES128(key)
    return c.decrypt(block) if decrypt else c.encrypt(block)


# ---------------------------------------------------------------------------
# Skylanders figure format
# ---------------------------------------------------------------------------
SIZE = 1024
HASH_CONST = b" Copyright (C) 2010 Activision. All Rights Reserved. "   # 0x35 bytes
AREA_BASE = (0x08, 0x24)          # header block of data area 0 / 1 (28 blocks each)
PLAIN_BLOCKS = (0x22, 0x3E)       # never encrypted (Imaginators checksum blocks) - see skyDecrypter.vb
R2 = 9                            # block (relative to the area header) holding the 2nd data region
                                  # (0x11 / 0x2D): own sequence byte, own CRC ("type 4"), XP overflow, hats
XP_A_MAX, XP_B_MAX, XP_MAX = 33000, 63500, 197500
HAT_MAX = 510
# XP needed to reach levels 1..20 (from the reference editor's level table)
LEVEL_XP = (0, 1000, 2200, 3800, 6000, 9000, 13000, 18200, 24800, 33000,
            43000, 55000, 69200, 85800, 96500, 113700, 132400, 152600, 174300, 197500)


def level_for_xp(xp):
    lvl = 1
    for i, need in enumerate(LEVEL_XP, 1):
        if xp >= need:
            lvl = i
    return lvl


def crypt_dump(data, decrypt):
    """AES-encrypt/decrypt every block from 0x08 on, except sector trailers and the two
    plaintext Imaginators blocks (0x22, 0x3E).  Key = MD5(blocks 0+1 | block index | HASH_CONST)."""
    out = bytearray(data)
    head = bytes(data[:32])
    for blk in range(8, 64):
        if blk % 4 == 3 or blk in PLAIN_BLOCKS:
            continue
        key = hashlib.md5(head + bytes([blk]) + HASH_CONST).digest()
        out[blk * 16:blk * 16 + 16] = aes_ecb_block(key, bytes(data[blk * 16:blk * 16 + 16]), decrypt)
    return bytes(out)


def crc16(data, crc=0xFFFF):
    """CRC-16/CCITT-FALSE (poly 0x1021, init 0xFFFF)."""
    for b in data:
        num2 = b << 8
        for _ in range(8):
            top = (crc ^ num2) & 0x8000
            crc = ((crc << 1) & 0xFFFF) ^ (0x1021 if top else 0)
            num2 = (num2 << 1) & 0xFFFF
    return crc


def crc_type0(d):
    return crc16(d[0:0x1E])


def crc_type1(d, area):
    b = AREA_BASE[area] * 16
    hdr = bytearray(d[b:b + 16])
    hdr[14], hdr[15] = 5, 0
    return crc16(hdr)


def crc_type23(d, area, kind):
    base = AREA_BASE[area]
    crc = 0xFFFF
    for r in (range(1, 5) if kind == 2 else range(5, 9)):
        if r % 4 == 3:
            continue
        crc = crc16(d[(base + r) * 16:(base + r + 1) * 16], crc)
    if kind == 3:
        for r in range(9, 28):
            if r % 4 != 3:
                crc = crc16(bytes(16), crc)
    return crc


def crc_type4(d, area, zero_last=False):
    """Checksum of the 2nd data region: block 0x11[2:16] + 0x12 + 0x14 + 0x15 (62 bytes, area 1:
    0x2D/0x2E/0x30/0x31), CRC16 xor 0xE953.  Stored at block 0x11 offset 0.
    The reference VB tool drops the very last byte (it is always 0 in practice); `zero_last`
    reproduces that, and FigureDump auto-detects which flavour a given file uses."""
    base = AREA_BASE[area] + R2
    buf = bytearray(d[base * 16 + 2:base * 16 + 16])
    for r in (1, 3, 4):
        buf += d[(base + r) * 16:(base + r + 1) * 16]
    if zero_last:
        buf[-1] = 0
    return crc16(bytes(buf)) ^ 0xE953


def area_blank(d, area):
    """True if the area's data blocks are all zero, i.e. the game never wrote it."""
    b = AREA_BASE[area]
    return not any(any(d[(b + r) * 16:(b + r + 1) * 16]) for r in range(28) if r % 4 != 3)


def zero_area(buf, area):
    b = AREA_BASE[area]
    for r in range(28):
        if r % 4 != 3:
            buf[(b + r) * 16:(b + r + 1) * 16] = bytes(16)


def region2_present(d, area):
    base = AREA_BASE[area] + R2
    return any(any(d[(base + r) * 16:(base + r + 1) * 16]) for r in (0, 1, 3, 4))


def _stored(d, blk, off):
    return d[blk * 16 + off] | (d[blk * 16 + off + 1] << 8)


def checksum_report(d, z4=False):
    """{(type, area): (stored, computed)}; type 0 is reported as (0, 0).
    Type 4 is only listed for areas whose 2nd region is in use."""
    rep = {(0, 0): (_stored(d, 1, 0x0E), crc_type0(d))}
    for a in (0, 1):
        if area_blank(d, a):                       # never written: no checksums to report
            continue
        b = AREA_BASE[a]
        rep[(1, a)] = (_stored(d, b, 0x0E), crc_type1(d, a))
        rep[(2, a)] = (_stored(d, b, 0x0C), crc_type23(d, a, 2))
        rep[(3, a)] = (_stored(d, b, 0x0A), crc_type23(d, a, 3))
        if region2_present(d, a):
            rep[(4, a)] = (_stored(d, b + R2, 0x00), crc_type4(d, a, z4))
    return rep


def valid_count(d):
    """Number of valid type 1-3 checksums (max 6); used to tell encrypted from decrypted dumps."""
    rep = checksum_report(d)
    return sum(1 for (t, _a), (s, c) in rep.items() if t in (1, 2, 3) and s == c)


def parse_nfc(text):
    """Read the 64 blocks out of a Flipper Zero MIFARE Classic 1K .nfc file."""
    blocks = {}
    for m in re.finditer(r"^Block\s+(\d+):[ \t]*([^\r\n]*)", text, re.M):
        toks = m.group(2).split()
        if len(toks) != 16 or any(not re.fullmatch(r"[0-9A-Fa-f]{2}", t) for t in toks):
            raise ValueError("Block %s in the .nfc file has unknown (??) bytes. "
                             "Read the figure with all keys found first." % m.group(1))
        blocks[int(m.group(1))] = bytes(int(t, 16) for t in toks)
    if any(i not in blocks for i in range(64)):
        raise ValueError("The .nfc file does not contain all 64 blocks of a MIFARE Classic 1K tag.")
    return b"".join(blocks[i] for i in range(64))


def render_nfc(text, data):
    def sub(m):
        n = int(m.group(2))
        if n >= 64:
            return m.group(0)
        return m.group(1) + " ".join("%02X" % b for b in data[n * 16:n * 16 + 16])
    return re.sub(r"^(Block\s+(\d+):[ \t]*)[^\r\n]*", sub, text, flags=re.M)


RAW_EXTS = (".bin", ".sky", ".dmp")
FORMAT_EXTS = RAW_EXTS + (".nfc",)


def format_for_path(path, default="bin"):
    """'nfc' or 'bin' (raw 1024-byte dump) from the file extension; `default` for anything else."""
    ext = os.path.splitext(path)[1].lower()
    if ext == ".nfc":
        return "nfc"
    if ext in RAW_EXTS:
        return "bin"
    return default


def new_nfc_text(data):
    """A complete Flipper Zero MIFARE Classic 1K .nfc file for a raw 1024-byte dump
    (used when converting a .bin/.sky/.dmp that has no .nfc header to reuse)."""
    if len(data) != SIZE:
        raise ValueError("Expected %d bytes of figure data." % SIZE)
    lines = ["Filetype: Flipper NFC device",
             "Version: 4",
             "# Device type can be ISO14443-3A, ISO14443-3B, ISO14443-4A, ISO14443-4B, ISO15693-3, "
             "FeliCa, NTAG/Ultralight, Mifare Classic, Mifare Plus, Mifare DESFire, SLIX, ST25TB, NTAG4xx",
             "Device type: Mifare Classic",
             "# UID is common for all formats",
             "UID: " + " ".join("%02X" % b for b in data[0:4]),
             "# ISO14443-3A specific data",
             "ATQA: 00 04",
             "SAK: 08",
             "# Mifare Classic specific data",
             "Mifare Classic type: 1K",
             "Data format version: 2",
             "# Mifare Classic blocks, '??' means unknown data"]
    lines += ["Block %d: %s" % (i, " ".join("%02X" % b for b in data[i * 16:i * 16 + 16])) for i in range(64)]
    return "\n".join(lines) + "\n"


class FigureDump:
    """A figure dump held decrypted in memory; re-encrypted when saved."""

    def __init__(self, plain, encrypted=True, fmt="bin", nfc_text=None, path=None):
        self.plain = bytearray(plain)
        self.encrypted = encrypted      # was the file's data area encrypted?
        self.fmt = fmt                  # 'bin' or 'nfc'
        self.nfc_text = nfc_text
        self.path = path
        self.dirty = False              # unsaved change that apply() does not cover (new character)
        self.blank = False              # True: figure was never used in a game, its data blocks are empty
        self.valid_found = valid_count(self.plain)
        self.z4 = self._detect_z4()

    def _detect_z4(self):
        """Does this figure's type-4 CRC cover the full 62 bytes (False) or zero the last one (True)?"""
        best = False
        for a in (0, 1):
            if not region2_present(self.plain, a):
                continue
            stored = _stored(self.plain, AREA_BASE[a] + R2, 0)
            if stored == crc_type4(self.plain, a, False):
                return False
            if stored == crc_type4(self.plain, a, True):
                best = True
        return best

    def report(self):
        return checksum_report(self.plain, self.z4)

    # -- loading / saving -------------------------------------------------
    @classmethod
    def load(cls, path):
        with open(path, "rb") as f:
            blob = f.read()
        fmt, text = "bin", None
        if blob.startswith(b"Filetype: Flipper NFC") or (path.lower().endswith(".nfc") and b"Block 0:" in blob):
            fmt, text = "nfc", blob.decode("utf-8", errors="replace")
            raw = parse_nfc(text)
        else:
            if len(blob) != SIZE:
                raise ValueError("Expected a %d-byte dump, but the file is %d bytes." % (SIZE, len(blob)))
            raw = blob
        if not any(any(raw[b * 16:b * 16 + 16]) for b in range(8, 64) if b % 4 != 3):
            fig = cls(raw, False, fmt, text, path)         # all-zero data blocks: nothing to decrypt
            fig.blank = True
            return fig
        dec = bytearray(crypt_dump(raw, decrypt=True))
        v_raw, v_dec = valid_count(raw), valid_count(dec)
        if v_raw > v_dec:
            return cls(raw, False, fmt, text, path)
        for a in (0, 1):
            if area_blank(raw, a):                 # unwritten area: decrypting zeros only makes noise
                zero_area(dec, a)
        return cls(dec, True, fmt, text, path)

    def to_bytes(self):
        if not self.encrypted:
            return bytes(self.plain)
        out = bytearray(crypt_dump(self.plain, decrypt=False))
        for a in (0, 1):
            if area_blank(self.plain, a):          # never encrypt an empty area into noise
                zero_area(out, a)
        return bytes(out)

    def save(self, path, fmt=None):
        """Write the figure.  The format follows the file extension (.nfc = Flipper Zero, .bin / .sky /
        .dmp = raw 1024-byte dump); any other extension keeps the format the figure was loaded in.
        Saving under a different format therefore converts the file."""
        fmt = fmt or format_for_path(path, self.fmt)
        data = self.to_bytes()
        if os.path.exists(path) and not os.path.exists(path + ".bak"):
            shutil.copy2(path, path + ".bak")
        if fmt == "nfc":
            text = render_nfc(self.nfc_text, data) if self.nfc_text else new_nfc_text(data)
            with open(path, "w", encoding="utf-8", newline="") as f:
                f.write(text)
            self.nfc_text = text
        else:
            with open(path, "wb") as f:
                f.write(data)
        self.fmt = fmt
        self.path = path

    # -- areas ------------------------------------------------------------
    # The figure holds two copies ("areas") of its save data and the game uses the newer one.
    # Each area has TWO independently sequenced regions: the header region (seq at header+9:
    # XP part A, gold, skills, hat part A, nickname, hero points) and the 2nd region (seq at
    # block 0x11/0x2D +2: XP parts B/C, hats B-D).  Which copy is newer can differ per region.
    @staticmethod
    def _newer(s0, s1):
        """Wrap-aware 8-bit sequence compare -> index of the newer area."""
        return 1 if ((s0 - s1) & 0xFF) >= 129 else 0

    def seq(self, area):
        return self.plain[AREA_BASE[area] * 16 + 9]

    def seq2(self, area):
        return self.plain[(AREA_BASE[area] + R2) * 16 + 2]

    def active_area(self):
        return self._newer(self.seq(0), self.seq(1))

    def active_area2(self):
        return self._newer(self.seq2(0), self.seq2(1))

    def has_region2(self):
        return region2_present(self.plain, 0) or region2_present(self.plain, 1)

    def _o(self, rel, off=0, area=None):
        a = self.active_area() if area is None else area
        return (AREA_BASE[a] + rel) * 16 + off

    def _o2(self, off, area=None):
        a = self.active_area2() if area is None else area
        return (AREA_BASE[a] + R2) * 16 + off

    def bad_checksums(self, area=None):
        a = self.active_area() if area is None else area
        rep = self.report()
        return [t for t in (1, 2, 3, 4) if (t, a) in rep and rep[(t, a)][0] != rep[(t, a)][1]]

    def fix_area(self, area):
        """Recompute the area's checksums in the game's order: 2, 3, 4 (if the 2nd region is in
        use), then 1 (type 1 covers the header block, which holds the type 2/3 values)."""
        p, b = self.plain, AREA_BASE[area] * 16
        for kind, off in ((2, 0x0C), (3, 0x0A)):
            c = crc_type23(p, area, kind)
            p[b + off], p[b + off + 1] = c & 0xFF, c >> 8
        if region2_present(p, area):
            c = crc_type4(p, area, self.z4)
            o = (AREA_BASE[area] + R2) * 16
            p[o], p[o + 1] = c & 0xFF, c >> 8
        c = crc_type1(p, area)
        p[b + 0x0E], p[b + 0x0F] = c & 0xFF, c >> 8

    def _area_blank(self, area):
        return area_blank(self.plain, area)

    def _live(self):
        """Areas the game has written (an empty area is never edited)."""
        return [a for a in (0, 1) if not area_blank(self.plain, a)]

    def fix_all(self):
        """Refresh the checksums of both areas (an area that was never written is left alone)."""
        for a in (0, 1):
            if not self._area_blank(a):
                self.fix_area(a)

    def init_region2(self):
        """A Spyro's-Adventure-only figure has an empty 2nd region.  Give it valid sequence numbers
        (1 and 2) the way the reference editor does, so larger XP / newer hats can be stored."""
        for a in self._live():
            for r in (0, 1, 3, 4):
                o = (AREA_BASE[a] + R2 + r) * 16
                self.plain[o:o + 16] = bytes(16)
            self.plain[(AREA_BASE[a] + R2) * 16 + 2] = a + 1

    # -- read-only info ---------------------------------------------------
    def uid(self):
        return " ".join("%02X" % b for b in self.plain[0:4])

    def set_identity(self, fid, var):
        """Turn this dump into another character: new figure ID + variant ID in block 1, plus the block-1
        checksum.  (The data encryption key is derived from blocks 0-1, so saving re-encrypts correctly.)"""
        if not (0 <= fid <= 0xFFFF and 0 <= var <= 0xFFFF):
            raise ValueError("Figure and variant IDs must fit in 16 bits.")
        self.plain[16:18] = fid.to_bytes(2, "little")
        self.plain[28:30] = var.to_bytes(2, "little")
        c = crc_type0(self.plain)
        self.plain[30], self.plain[31] = c & 0xFF, c >> 8
        self.dirty = True

    def figure_id(self):
        return self.plain[16] | (self.plain[17] << 8)

    def variant_id(self):
        return self.plain[16 + 12] | (self.plain[16 + 13] << 8)

    def platform_flags(self):
        return self.plain[self._o(1, 3)]

    # -- editable fields ----------------------------------------------------
    def _u16(self, o):
        return self.plain[o] | (self.plain[o + 1] << 8)

    def get_gold(self):
        return self._u16(self._o(0, 3))

    def get_hero_points(self):
        return self._u16(self._o(5, 0x0A))

    def get_skills(self):
        return self._u16(self._o(1, 0))

    def get_xp(self):
        """XP is split over three places: part A (header +0, up to 33,000), part B (2nd region +3,
        up to 63,500 more), part C (2nd region +8, 16 bit, plus a +65,536 flag at +10)."""
        xp = self._u16(self._o(0, 0))
        if self.has_region2():
            xp += self._u16(self._o2(3)) + self._u16(self._o2(8))
            if self.plain[self._o2(10)] == 1:
                xp += 65536
        return xp

    def get_hat(self):
        """Hat IDs live in one of four byte slots depending on their size."""
        h = self.plain[self._o(1, 4)]
        if h:
            return h
        if self.has_region2():
            for off in (5, 12):
                if self.plain[self._o2(off)]:
                    return self.plain[self._o2(off)]
            if self.plain[self._o2(14)]:
                return self.plain[self._o2(14)] + 255
        return 0

    def get_name(self):
        raw = bytes(self.plain[self._o(2):self._o(2) + 16] + self.plain[self._o(4):self._o(4) + 16])
        end = 32
        for i in range(0, 32, 2):
            if raw[i] == 0 and raw[i + 1] == 0:
                end = i
                break
        return raw[:end].decode("utf-16-le", errors="replace")

    def _put(self, o, data):
        self.plain[o:o + len(data)] = data

    def apply(self, xp, gold, hero_points, name, hat, skills):
        """Write the values into BOTH data areas (so it does not matter which copy the game reads).
        Only fields whose value actually changed are touched.  Returns True if anything changed.
        Call fix_all() afterwards to refresh the checksums."""
        enc = name.encode("utf-16-le")
        if len(name) > 14 or any(ord(c) > 0xFFFF for c in name) or len(enc) > 28:
            raise ValueError("Nickname must be at most 14 characters (no emoji).")
        if not 0 <= xp <= XP_MAX:
            raise ValueError("XP must be between 0 and %d." % XP_MAX)
        if not 0 <= hat <= HAT_MAX:
            raise ValueError("Hat ID must be between 0 and %d." % HAT_MAX)
        enc = enc.ljust(32, b"\0")
        before = bytes(self.plain)

        # fields that need the 2nd region must not be written into an uninitialised one
        if (xp > XP_A_MAX or hat >= 46) and not self.has_region2() and \
                (xp != self.get_xp() or hat != self.get_hat()):
            self.init_region2()

        # decide what changed BEFORE writing (the getters read from the active area)
        cur_name = bytes(self.plain[self._o(2):self._o(2) + 16] + self.plain[self._o(4):self._o(4) + 16])
        chg = {"gold": gold != self.get_gold(), "hp": hero_points != self.get_hero_points(),
               "skills": skills != self.get_skills(), "name": enc != cur_name,
               "xp": xp != self.get_xp(), "hat": hat != self.get_hat()}
        for a in self._live():
            if chg["gold"]:
                self._put(self._o(0, 3, a), gold.to_bytes(2, "little"))
            if chg["hp"]:
                self._put(self._o(5, 0x0A, a), hero_points.to_bytes(2, "little"))
            if chg["skills"]:
                self._put(self._o(1, 0, a), skills.to_bytes(2, "little"))
            if chg["name"]:
                self._put(self._o(2, 0, a), enc[:16])
                self._put(self._o(4, 0, a), enc[16:])
        if chg["xp"]:
            self._set_xp(xp)
        if chg["hat"]:
            self._set_hat(hat)
        return bytes(self.plain) != before

    def _set_xp(self, xp):
        if xp <= XP_A_MAX:
            parts = (xp, 0, 0, 0)
        elif xp <= XP_A_MAX + XP_B_MAX:
            parts = (XP_A_MAX, xp - XP_A_MAX, 0, 0)
        elif xp <= XP_A_MAX + XP_B_MAX + 65535:
            parts = (XP_A_MAX, XP_B_MAX, xp - XP_A_MAX - XP_B_MAX, 0)
        else:
            parts = (XP_A_MAX, XP_B_MAX, xp - (XP_A_MAX + XP_B_MAX + 65536), 1)
        pa, pb, pc, flag = parts
        r2 = self.has_region2()
        for a in self._live():
            self._put(self._o(0, 0, a), pa.to_bytes(2, "little"))
            if r2:
                self._put(self._o2(3, a), pb.to_bytes(2, "little"))
                self._put(self._o2(8, a), pc.to_bytes(2, "little") + bytes([flag]))

    def _set_hat(self, hat):
        slots = {"a": 0, "b": 0, "c": 0, "d": 0}
        if hat < 46:
            slots["a"] = hat
        elif hat < 97:
            slots["b"] = hat
        elif hat < 256:
            slots["c"] = hat
        else:
            slots["d"] = hat - 255
        r2 = self.has_region2()
        for a in self._live():
            self._put(self._o(1, 4, a), bytes([slots["a"]]))
            if r2:
                self._put(self._o2(5, a), bytes([slots["b"]]))
                self._put(self._o2(12, a), bytes([slots["c"]]))
                self._put(self._o2(14, a), bytes([slots["d"]]))

    def describe(self):
        if self.blank:
            return ("Save data     : NONE - this figure has never been used in a game (its data blocks are\n"
                    "                empty).  UID %s, figure ID %d, variant 0x%04X.\n"
                    "                Put it on the portal in a game once, then dump it again."
                    % (self.uid(), self.figure_id(), self.variant_id()))
        rep = self.report()
        bad = [("type %d, area %d" % (t, a)) for (t, a), (s, c) in rep.items() if s != c]
        lines = [
            "Format        : %s, data %s" % ("Flipper .nfc" if self.fmt == "nfc" else "raw 1 KB dump",
                                             "encrypted" if self.encrypted else "already decrypted"),
            "UID           : %s" % self.uid(),
            "Figure ID     : 0x%04X (%d)   variant 0x%04X" % (self.figure_id(), self.figure_id(), self.variant_id()),
            "Data areas    : A0 %s, A1 %s -> active A%d" % (
                *("empty" if self._area_blank(x) else "seq %d" % self.seq(x) for x in (0, 1)), self.active_area()),
            "Checksums     : %s" % ("all OK" if not bad else "BAD: " + ", ".join(bad)),
            "XP            : %d" % self.get_xp(),
            "Gold          : %d" % self.get_gold(),
            "Hero points   : %d" % self.get_hero_points(),
            "Nickname      : %r" % self.get_name(),
            "Hat ID        : %d" % self.get_hat(),
            "Skill bits    : 0x%04X" % self.get_skills(),
            "Platform flags: 0x%02X" % self.platform_flags(),
        ]
        return "\n".join(lines)

    def hexview(self):
        act = self.active_area()
        out = []
        for blk in range(64):
            row = self.plain[blk * 16:(blk + 1) * 16]
            note = ""
            if blk in AREA_BASE:
                a = AREA_BASE.index(blk)
                note = "  <- area %d header%s" % (a, " (ACTIVE)" if a == act else "")
            elif blk % 4 == 3:
                note = "  (sector trailer)"
            elif blk in PLAIN_BLOCKS:
                note = "  (never encrypted)"
            out.append("%02X: %s%s" % (blk, " ".join("%02X" % b for b in row), note))
        return "\n".join(out)


# ---------------------------------------------------------------------------
# GUI
# ---------------------------------------------------------------------------
try:
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox
    HAVE_TK = True
except Exception:  # pragma: no cover
    HAVE_TK = False

NOTES = """How it works
 - The 1 KB dump is 64 blocks of 16 bytes. Blocks 0-1 hold the UID / figure ID; every
   block from 0x08 on is AES-128 encrypted with a key derived from blocks 0-1 - EXCEPT
   the sector trailers and blocks 0x22 / 0x3E (Imaginators checksums), which are plain.
   This tool decrypts, edits, fixes the CRC16 checksums, then re-encrypts to the same
   format the file came in.
 - There are two data areas (headers at blocks 0x08 and 0x24); the game uses the one with
   the newer sequence number. Each area has two regions with their own sequence number and
   checksum: the header region and a 2nd region at block 0x11 / 0x2D (Trap Team and later).
   Edits are written into BOTH areas, sequence numbers are left alone, and every checksum
   (types 1, 2, 3 and 4) is recomputed.

Fields (offsets relative to the area header block)
 - XP      header +0x00 (16 bit, up to 33,000) + 2nd region +3 (16 bit, up to 63,500 more)
           + 2nd region +8 (16 bit) with a +65,536 flag at +10.  Max 197,500 (level 20).
 - Gold    header +0x03, 16-bit (max 65,000)
 - Hero pts  block +5, offset 0x0A (max 100)
 - Skills    block +1, offset 0x00 (16-bit; 0x0FFD / 0x0FFF = all skills, left / right)
 - Hat     one byte: block +1 off 4 (<46), 2nd region +5 (46-96), +12 (97-255), +14 (256+)
 - Nickname  blocks +2 and +4, UTF-16, <=14 chars

Offline use
 - Everything except downloading pictures works without internet: a built-in figure list
   (Spyro's Adventure, Giants, Trap Team traps/items) names the figure, fills the character
   picker and works in --info. The complete list is fetched once when you are online and
   cached in ~/.skylander_editor_figures.json.
 - Pictures are read from the skylander_images folder next to the script. To have them
   offline: press "All pictures..." in the toolbar (one picture per character, shared by all
   its variants), or use Change character... -> pick a game/type -> "Pictures for offline...",
   or drop image files onto the window.

Caveats
 - SuperChargers vehicles store their data differently and are not supported.
 - Layout was documented for Spyro's Adventure; later games use the same container,
   but check the result in-game on a copy of your dump.
 - Heroic-challenge flags are not editable here: sources disagree on their offset.
 - Your original is copied to <file>.bak the first time you save over it.
"""


# ---------------------------------------------------------------------------------------------
# Figure database (which character is this?) and pictures
# ---------------------------------------------------------------------------------------------
FIG_URL = ("https://gist.github.com/sleeyax/49c581bcffd042bc78d2e08490ab6594/raw/"
           "31c376f5183fc0e017d3a723b2a63b2b27460a69/figures.json")
FIG_CACHE = os.path.expanduser("~/.skylander_editor_figures.json")
IMG_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "skylander_images")
SERIES_NAMES = {"Spyros Adventure": "Spyro's Adventure", "Giants": "Giants", "SwapForce": "Swap Force",
                "TrapTeam": "Trap Team", "Superchargers": "SuperChargers", "Imaginators": "Imaginators"}
# Built-in fallback: the original Spyro's Adventure / Giants characters (figure ID -> name, element).
BASE_FIGURES = {
    0: ("Whirlwind", "Air"), 1: ("Sonic Boom", "Air"), 2: ("Warnado", "Air"), 3: ("Lightning Rod", "Air"),
    4: ("Bash", "Earth"), 5: ("Terrafin", "Earth"), 6: ("Dino-Rang", "Earth"), 7: ("Prism Break", "Earth"),
    8: ("Sunburn", "Fire"), 9: ("Eruptor", "Fire"), 10: ("Ignitor", "Fire"), 11: ("Flameslinger", "Fire"),
    12: ("Zap", "Water"), 13: ("Wham-Shell", "Water"), 14: ("Gill Grunt", "Water"), 15: ("Slam Bam", "Water"),
    16: ("Spyro", "Magic"), 17: ("Voodood", "Magic"), 18: ("Double Trouble", "Magic"),
    19: ("Trigger Happy", "Tech"), 20: ("Drobot", "Tech"), 21: ("Drill Sergeant", "Tech"), 22: ("Boomer", "Tech"),
    23: ("Wrecking Ball", "Magic"), 24: ("Camo", "Life"), 25: ("Zook", "Life"), 26: ("Stealth Elf", "Life"),
    27: ("Stump Smash", "Life"), 28: ("Dark Spyro", "Magic"), 29: ("Hex", "Undead"), 30: ("Chop Chop", "Undead"),
    31: ("Ghost Roaster", "Undead"), 32: ("Cynder", "Undead"),
    100: ("Jet-Vac", "Air"), 101: ("Swarm", "Air"), 102: ("Crusher", "Earth"), 103: ("Flashwing", "Earth"),
    104: ("Hot Head", "Fire"), 105: ("Hot Dog", "Fire"), 106: ("Chill", "Water"), 107: ("Thumpback", "Water"),
    108: ("Pop Fizz", "Magic"), 109: ("Ninjini", "Magic"), 110: ("Bouncer", "Tech"), 111: ("Sprocket", "Tech"),
    112: ("Tree Rex", "Life"), 113: ("Shroomboom", "Life"), 114: ("Eye-Brawl", "Undead"),
    115: ("Fright Rider", "Undead"),
}


# Built-in figure list (id | variant | game | element | name) so names, the character picker and the
# CLI work with no internet.  Covers Spyro's Adventure, Giants and the Trap Team traps / items / most
# Trap Masters; the complete list (Swap Force ... Imaginators) is added from the cache when downloaded.
BUILTIN_FIGURES = """0|0|S|A|Whirlwind
0|6145|G|A|Whirlwind (S2)
0|7170|G|A|Whirlwind (Polar)
0|10245|W|A|Whirlwind (Horn Blast)
0|14352|T|A|Whirlwind (Eon's Elite)
1|0|S|A|Sonic Boom
1|6145|G|A|Sonic Boom (S2)
1|6161|G|A|Sonic Boom (Glow In The Dark)
1|6163|G|A|Sonic Boom (Sparkle)
2|0|S|A|Warnado
2|8710|W|A|Warnado (Lightcore)
3|0|S|A|Lightning Rod
3|6145|G|A|Lightning Rod (S2)
4|0|S|E|Bash
4|6145|G|E|Bash (S2)
5|0|S|E|Terrafin
5|6145|G|E|Terrafin (S2)
5|10245|W|E|Terrafin (Knockout)
5|14352|T|E|Terrafin (Eon's Elite)
6|0|S|E|Dino-Rang
6|18448|C|E|Dino-Rang (Eon's Elite)
7|0|S|E|Prism Break
7|4614|G|E|Prism Break (Lightcore)
7|6145|G|E|Prism Break (S2)
7|10245|W|E|Prism Break (Hyper Beam)
8|0|S|F|Sunburn
9|0|S|F|Eruptor
9|4614|G|F|Eruptor (Lightcore)
9|6145|G|F|Eruptor (S2)
9|10245|W|F|Eruptor (Lava Barf)
9|11266|W|F|Eruptor (Volcanic)
9|14352|T|F|Eruptor (Eon's Elite)
10|0|S|F|Ignitor
10|6145|G|F|Ignitor (S2)
10|7171|G|F|Ignitor (Legendary)
11|0|S|F|Flameslinger
11|6145|G|F|Flameslinger (S2)
11|6146|G|F|Flameslinger (Golden)
12|0|S|W|Zap
12|6145|G|W|Zap (S2)
13|0|S|W|Wham-Shell
13|8710|W|W|Wham-Shell (Lightcore)
14|0|S|W|Gill Grunt
14|6145|G|W|Gill Grunt (S2)
14|6167|G|W|Gill Grunt (Metallic)
14|10245|W|W|Gill Grunt (Anchors Away)
14|14345|T|W|Gill Grunt (Tidal Wave)
14|14352|T|W|Gill Grunt (Eon's Elite)
15|0|S|W|Slam Bam
15|6145|G|W|Slam Bam (S2)
15|7171|G|W|Slam Bam (Legendary)
15|14352|C|W|Slam Bam (Eon's Elite)
16|0|S|M|Spyro
16|6145|G|M|Spyro (S2)
16|10245|W|M|Spyro (Mega Ram)
16|11266|W|M|Spyro (Dark Mega Ram)
16|14352|T|M|Spyro (Eon's Elite)
17|0|S|M|Voodood
17|14352|C|M|Voodood (Eon's Elite)
18|0|S|M|Double Trouble
18|6145|G|M|Double Trouble (S2)
18|7170|G|M|Double Trouble (Royal)
19|0|S|T|Trigger Happy
19|6145|G|T|Trigger Happy (S2)
19|10245|W|T|Trigger Happy (Big Bang)
19|11266|W|T|Trigger Happy (Springtime)
19|14352|T|T|Trigger Happy (Eon's Elite)
20|0|S|T|Drobot
20|4614|G|T|Drobot (Lightcore)
20|6145|G|T|Drobot (S2)
21|0|S|T|Drill Sergeant
21|6145|G|T|Drill Sergeant (S2)
22|0|S|T|Boomer
22|18448|C|T|Boomer (Eon's Elite)
23|0|S|M|Wrecking Ball
23|6145|G|M|Wrecking Ball (S2)
24|0|S|L|Camo
24|10245|W|L|Camo (Thorn Horn)
25|0|S|L|Zook
25|6145|G|L|Zook (S2)
25|14352|C|L|Zook (Eon's Elite)
26|0|S|L|Stealth Elf
26|6145|G|L|Stealth Elf (S2)
26|7171|G|L|Stealth Elf (Legendary)
26|10245|W|L|Stealth Elf (Ninja)
26|11266|W|L|Stealth Elf (Dark)
26|14352|T|L|Stealth Elf (Eon's Elite)
27|0|S|L|Stump Smash
27|6145|G|L|Stump Smash (S2)
28|0|S|M|Spyro (Dark)
29|0|S|U|Hex
29|4614|G|U|Hex (Lightcore)
29|6145|G|U|Hex (S2)
30|0|S|U|Chop Chop
30|6145|G|U|Chop Chop (S2)
30|10245|W|U|Chop Chop (Twin Blade)
30|10262|W|U|Chop Chop (Green Twin Blade)
30|14352|T|U|Chop Chop (Eon's Elite)
31|0|S|U|Ghost Roaster
31|18448|C|U|Ghost Roaster (Eon's Elite)
32|0|S|U|Cynder
32|6145|G|U|Cynder (S2)
32|6161|G|U|Cynder (Glow In The Dark)
32|10245|W|U|Cynder (Phantom)
32|12317|S|U|Cynder (Clear)
100|4096|G|A|Jet-Vac
100|4614|G|A|Jet-Vac (Lightcore)
100|5123|G|A|Jet-Vac (Legendary)
100|10245|W|A|Jet Vac (Turbo)
100|14341|T|A|Jet-Vac (Full Blast)
101|4614|G|A|Swarm (Giant)
102|4614|G|E|Crusher (Giant)
102|5634|G|E|Granite Crusher (Giant)
103|4096|G|E|Flashwing
103|5122|G|E|Flashwing (Jade)
103|8710|W|E|Flashwing (Lightcore)
104|4614|G|F|Hot Head (Giant)
104|4627|G|F|Hot Head (Sparkle)
105|4096|G|F|Hot Dog
105|5122|G|F|Hot Dog (Molten)
105|10245|W|F|Hot Dog (Fire Bone)
106|4096|G|W|Chill
106|4614|G|W|Chill (Lightcore)
106|5635|G|W|Chill (Legendary)
106|10245|W|W|Chill (Blizzard)
107|4614|G|W|Thumpback (Giant)
108|4096|G|M|Pop Fizz
108|4614|G|M|Pop Fizz (Lightcore)
108|5122|G|M|Pop Fizz (Punch)
108|10245|W|M|Pop Fizz (Super Gulp)
108|14341|T|M|Pop Fizz (Fizzy Frenzy)
108|15362|T|M|Pop Fizz (Love Potion)
109|4614|G|M|Ninjini (Giant)
109|5634|G|M|Ninjini (Scarlet) (Giant)
110|4614|G|T|Bouncer (Giant)
110|5635|G|T|Bouncer (Legendary) (Giant)
111|4096|G|T|Sprocket
111|10245|W|T|Sprocket (Heavy Duty)
111|10265|W|T|Sprocket (Heavy Metal)
112|4614|G|L|Tree Rex (Giant)
112|5634|G|L|Tree Rex (Gnarly) (Giant)
113|4096|G|L|Shroomboom
113|4614|G|L|Shroomboom (Lightcore)
113|14337|T|L|Shroomboom (Sure Shot)
114|4614|G|U|Eye-Brawl (Giant)
114|4629|G|U|Eye-Brawl (Pumpkin) (Giant)
115|4096|G|U|Fright Rider
115|4113|G|U|Fright Rider (Halloween)
115|6161|G|U|Fright Rider (Glow In The Dark)
200|8192|S|N|Item - Anvil Rain
201|8192|S|N|Item - Hidden Treasure
202|8192|S|N|Item - Healing Elixer
203|8192|S|N|Item - Ghost Pirate Swords
204|8192|S|N|Item - Time Twister Hourglass
205|8192|S|N|Item - Sky-Iron Shield
206|8192|S|N|Item - Winged Boots
207|8192|S|N|Item - Sparx Dragonfly
208|4614|G|N|Item - Dragonfire Cannon
208|5634|G|N|Item - Golden Dragonfire Cannon
209|4614|G|N|Item - Scorpion Striker Catapult
210|12289|T|M|Trap - Magic Log Holder
210|12296|T|M|Trap - Magic Skull
210|12299|T|M|Trap - Magic Axe
210|12302|T|M|Trap - Magic Hourglass
210|12306|T|M|Trap - Magic Totem
210|12309|T|M|Trap - Magic Rocket
211|12289|T|W|Trap - Water Tiki
211|12290|T|W|Trap - Water Log Holder
211|12294|T|W|Trap - Water Jughead
211|12295|T|W|Trap - Water Angel
211|12299|T|W|Trap - Water Axe
211|12310|T|W|Trap - Water Flying Helmet
211|13318|T|W|Trap - Water Jughead (Legendary)
212|12291|T|A|Trap - Air Toucan
212|12294|T|A|Trap - Air Jughead
212|12302|T|A|Trap - Air Hourglass
212|12304|T|A|Trap - Air Snake
212|12305|T|A|Trap - Air Screamer
212|12312|T|A|Trap - Air Sword
213|12292|T|U|Trap - Undead Orb
213|12296|T|U|Trap - Undead Skull
213|12299|T|U|Trap - Undead Axe
213|12300|T|U|Trap - Undead Hand
213|12304|T|U|Trap - Undead Snake
213|12311|T|U|Trap - Undead Captain's Hat
213|13316|T|U|Trap - Undead Orb (Legendary)
213|13320|T|U|Trap - Undead Skull (Legendary)
214|12289|T|T|Trap - Tech Tiki
214|12295|T|T|Trap - Tech Angel
214|12297|T|T|Trap - Tech Scepter
214|12300|T|T|Trap - Tech Hand
214|12310|T|T|Trap - Tech Flying Helmet
214|12314|T|T|Trap - Tech Handstand
215|12289|T|F|Trap - Fire Flower
215|12293|T|F|Trap - Fire Torch
215|12297|T|F|Trap - Fire Flower (NEW)
215|12305|T|F|Trap - Fire Screamer
215|12306|T|F|Trap - Fire Totem
215|12311|T|F|Trap - Fire Captain's Hat
215|12315|T|F|Trap - Fire Yawn
216|12291|T|E|Trap - Earth Toucan
216|12292|T|E|Trap - Earth Orb
216|12298|T|E|Trap - Earth Hammer
216|12302|T|E|Trap - Earth Hourglass
216|12306|T|E|Trap - Earth Totem
216|12314|T|E|Trap - Earth Handstand
217|12289|T|L|Trap - Life Toucan
217|12291|T|L|Trap - Life Toucan (NEW)
217|12293|T|L|Trap - Life Torch
217|12298|T|L|Trap - Life Hammer
217|12304|T|L|Trap - Life Snake
217|12312|T|L|Trap - Life Sword
217|12315|T|L|Trap - Life Yawn
218|12308|T|Dk|Trap - Dark Spider
218|12312|T|Dk|Trap - Dark Sword
218|12314|T|Dk|Trap - Dark Handstand
219|12303|T|Lt|Trap - Light Owl
219|12309|T|Lt|Trap - Light Rocket
219|12315|T|Lt|Trap - Light Yawn
220|12318|T|K|Trap - Kaos
220|13599|T|K|Trap - Kaos (Ultimate)
230|0|T|N|Item - Hand Of Fate
230|13315|T|N|Item - Hand Of Fate (Legendary)
231|0|T|N|Item - Piggy Bank
232|0|T|N|Item - Rocket Ram
233|0|T|N|Item - Tiki Speaky
235|20481|I|N|Item - Mystery Chest (Bronze)
235|20482|I|N|Item - Mystery Chest (Silver)
235|20483|I|N|Item - Mystery Chest (Gold)
235|20503|I|N|Item - Cursed Tiki Temple
235|20505|I|N|Item - Lost Imaginite Mines
300|0|S|N|Item - Dragon's Peak
301|8192|S|N|Item - Empire Of Ice
302|8192|S|N|Item - Pirate Ship
303|8192|S|N|Item - Darklight Crypt
304|8192|S|N|Item - Volcanic Vault
305|12288|T|N|Item - Mirror Of Mystery
306|12288|T|N|Item - Nightmare Express
307|12806|T|N|Item - Sunscraper Spire
308|12806|T|N|Item - Midnight Museum
310|20480|I|N|Item - Gryphon Park Observatory
311|20480|I|N|Item - Enchanted Elven Forest
404|0|S|E|Bash (Legendary)
416|0|S|M|Spyro (Legendary)
419|0|S|T|Trigger Happy (Legendary)
430|0|S|U|Chop Chop (Legendary)
450|12288|T|A|Gusto (Trap Master)
451|12288|T|A|Thunderbolt (Trap Master)
451|12317|T|A|Thunderbolt (Clear) (Trap Master)
452|12288|T|A|Fling Kong
453|12288|T|A|Blades
453|13315|T|A|Blades (Legendary)
454|12288|T|E|Wallop (Trap Master)
455|12288|T|E|Head Rush (Trap Master)
455|13314|T|E|Head Rush (Nitro)
456|12288|T|E|Fist Bump
457|12288|T|E|Rocky Roll
458|12288|T|F|Wildfire (Trap Master)
458|13314|T|F|Wildfire (Dark) (Trap Master)
459|12288|T|F|Kaboom (Trap Master)
460|12288|T|F|Trail Blazer
461|12288|T|F|Torch"""
_SER = {"S": "Spyros Adventure", "G": "Giants", "W": "SwapForce", "T": "TrapTeam", "C": "Superchargers",
        "I": "Imaginators"}
_EL = {"A": "Air", "E": "Earth", "F": "Fire", "W": "Water", "M": "Magic", "T": "Tech", "L": "Life",
       "U": "Undead", "Dk": "Dark", "Lt": "Light", "K": "Kaos", "N": "None"}


def builtin_entries():
    out = []
    for line in BUILTIN_FIGURES.strip().splitlines():
        fid, var, ser, el, name = line.split("|", 4)
        out.append({"Id": int(fid), "Variant": int(var), "Name": name, "Series": _SER[ser], "Element": _EL[el]})
    return out


# Giants figures use variant 0x1000 or 0x1206 depending on the character (needed for the offline list).
GIANTS_VARIANT = {100: 4096, 101: 4614, 102: 4614, 103: 4096, 104: 4614, 105: 4096, 106: 4096, 107: 4614,
                  108: 4096, 109: 4614, 110: 4614, 111: 4096, 112: 4614, 113: 4096, 114: 4614, 115: 4096}
GAMES = ("Spyro's Adventure", "Giants", "Swap Force", "Trap Team", "SuperChargers", "Imaginators")
KINDS = ("Character", "Item", "Trap", "Vehicle")


def figure_kind(name):
    n = name.lower()
    if n.startswith("item -"):
        return "Item"
    if n.startswith("trap -"):
        return "Trap"
    if n.startswith("vehicle"):
        return "Vehicle"
    return "Character"


def filter_entries(entries, game="", kind="", element="", text=""):
    """Empty string = no filter on that field."""
    t = text.strip().lower()
    return [e for e in entries
            if (not game or e["series"] == game) and (not kind or e["kind"] == kind)
            and (not element or e["element"] == element) and (not t or t in e["name"].lower())]


def entries_to_csv(entries):
    import csv
    import io
    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow(["Name", "Game", "Type", "Element", "Figure ID", "Variant ID", "Variant (hex)"])
    for e in entries:
        w.writerow([e["name"], e["series"], e["kind"], e["element"], e["id"], e["var"], "0x%04X" % e["var"]])
    return buf.getvalue()


class FigureDB:
    """(figure ID, variant ID) -> name / series / element."""

    def __init__(self, entries=()):
        self.full = False                  # True once the complete downloaded list is merged in
        self.exact = {}
        for e in entries:
            fid, var, name = int(e["Id"]), int(e["Variant"]), str(e["Name"])
            if fid == 6 and name.startswith("Hot Dog"):         # known typo in the source list
                fid = 105
            self.exact[(fid, var)] = (name, SERIES_NAMES.get(e.get("Series", ""), e.get("Series", "")),
                                      e.get("Element", ""))
        self.size = len(self.exact)

    @classmethod
    def from_json(cls, text):
        return cls(json.loads(text))

    def entries(self):
        """Every known figure as dicts (name, series, kind, element, id, var), sorted for display.
        Without the downloaded list this is the built-in set of Spyro's Adventure / Giants characters."""
        out = []
        if self.exact:
            for (fid, var), (name, series, el) in self.exact.items():
                out.append(dict(name=name, series=series, kind=figure_kind(name), element=el, id=fid, var=var))
        else:
            for fid, (name, el) in BASE_FIGURES.items():
                out.append(dict(name=name, series="Giants" if fid >= 100 else "Spyro's Adventure",
                                kind="Character", element=el, id=fid, var=GIANTS_VARIANT.get(fid, 0)))
        order = {g: i for i, g in enumerate(GAMES)}
        out.sort(key=lambda e: (order.get(e["series"], 99), e["kind"], e["name"].lower(), e["var"]))
        return out

    def lookup(self, fid, var):
        """-> dict(name, base, note, series, element, exact).  `base` is the plain character name
        (no "(S2)" etc.), used for picture lookups; `note` explains an unlisted variant."""
        hit = self.exact.get((fid, var))
        if hit:
            return dict(name=hit[0], base=_base_name(hit[0]), note="", series=hit[1], element=hit[2], exact=True)
        base = BASE_FIGURES.get(fid)
        if base:
            note = "" if var == 0 else "variant 0x%04X is not in the figure list" % var
            return dict(name=base[0], base=base[0], note=note, series="", element=base[1], exact=False)
        return dict(name="Unknown figure (ID %d, variant 0x%04X)" % (fid, var), base="", note="",
                    series="", element="", exact=False)


def _page_name(name):
    """Wiki page title for a figure: 'Item - Anvil Rain' -> 'Anvil Rain', 'Gill Grunt (S2)' -> 'Gill Grunt'."""
    return re.sub(r"^(Item|Trap)\s*-\s*", "", _base_name(name))


def _base_name(name):
    """'Gill Grunt (S2)' -> 'Gill Grunt'"""
    return re.sub(r"\s*\(.*?\)", "", name).strip() or name


def load_figure_db():
    """Built-in list, overlaid with the full downloaded list (cache) when there is one."""
    entries, full = builtin_entries(), False
    try:
        with open(FIG_CACHE, encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list) and len(data) >= 50:
            entries, full = entries + data, True
    except Exception:
        pass
    db = FigureDB(entries)
    db.full = full
    return db


def download_figure_db(timeout=6):
    """Fetch the full figure list once and cache it (Spyro's Adventure ... Imaginators)."""
    import urllib.request
    with urllib.request.urlopen(FIG_URL, timeout=timeout) as r:
        text = r.read().decode("utf-8")
    db = FigureDB.from_json(text)                      # validate before caching
    if db.size < 50:
        raise ValueError("figure list looks incomplete")
    with open(FIG_CACHE, "w", encoding="utf-8") as f:
        f.write(text)
    return db.size


def _safe(name):
    return re.sub(r"[^A-Za-z0-9._-]+", "_", name).strip("_")


_ONLINE = [0.0, False]


def is_online(force=False):
    """Quick check (cached for 20 s) so network features fail fast instead of hanging when offline."""
    now = time.time()
    if not force and now - _ONLINE[0] < 20:
        return _ONLINE[1]
    try:
        socket.create_connection(("skylanderswiki.com", 443), timeout=2).close()
        ok = True
    except OSError:
        ok = False
    _ONLINE[0], _ONLINE[1] = now, ok
    return ok


def picture_groups(entries):
    """One download job per distinct character - all of its variants share the wiki picture, which is
    saved once as <Character_Name>.png.  Returns [(save_stem, name, id, variant)] for characters that
    have no picture yet."""
    seen, out = set(), []
    for e in entries:
        if find_image(e["id"], e["var"], e["name"]) is not None:
            continue
        base = _base_name(e["name"])
        if base.lower() in seen:
            continue
        seen.add(base.lower())
        out.append((_safe(base), base, e["id"], e["var"]))
    return out


def prefetch_pictures(entries, state, fetch=None, delay=0.25):
    """Download the picture of every character in `entries` that has none yet (for offline use).
    `state` is updated as it goes: total / done / ok / fail / finished / error; set state['cancel']=True to stop."""
    fetch = fetch or fetch_image
    todo = picture_groups(entries)
    state.update(total=len(todo), done=0, ok=0, fail=0, finished=False, error="")
    if todo and fetch is fetch_image and not is_online(force=True):
        state.update(error="offline", finished=True)
        return
    for stem, name, fid, var in todo:
        if state.get("cancel"):
            break
        try:
            fetch(fid, var, name, save_stem=stem)
            state["ok"] += 1
        except Exception:
            state["fail"] += 1
        state["done"] += 1
        if delay:
            time.sleep(delay)
    state["finished"] = True


def find_image(fid, var, name, extra=()):
    """Look for a picture in ./skylander_images: <id>_<variant>.png, then <Name>.png (the figure's own
    name hints first, e.g. 'Pearl Sprocket'), then <id>.png."""
    base = _base_name(name)
    stems = ["%d_%d" % (fid, var)] + [_safe(x) for x in extra] + [_safe(name), _safe(base), str(fid)]
    for stem in stems:
        for ext in (".png", ".gif", ".jpg", ".jpeg", ".webp"):
            p = os.path.join(IMG_DIR, stem + ext)
            if os.path.isfile(p):
                return p
    return None


def og_image(html):
    """URL from the page's <meta property="og:image"> tag (either attribute order), or None."""
    m = re.search(r'<meta[^>]+property=["\']og:image["\'][^>]+content=["\']([^"\']+)', html) or \
        re.search(r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+property=["\']og:image', html)
    return m.group(1).replace("&amp;", "&") if m else None


_JUNK = re.compile(r"icon|logo|wordmark|banner|flag|element|button|badge|wiki\.|sprite|placeholder|commons|"
                   r"edit|arrow|star|coin|stat|ability|upgrade|path|gear|card", re.I)
_IMG_EXT = (".png", ".jpg", ".jpeg", ".webp", ".gif")


def page_image_urls(html, base, page_url):
    """Absolute URLs of the wiki page's pictures, best guess first.  The infobox picture is the first
    sizeable /images/ file whose name contains the character name."""
    from urllib.parse import urljoin
    want = re.sub(r"[^a-z0-9]", "", base.lower())
    found = []
    for pos, tag in enumerate(re.finditer(r"<img\b[^>]*>", html, re.I)):
        t = tag.group(0)
        attrs = dict((k.lower(), v) for k, v in re.findall(r'([\w:-]+)\s*=\s*["\']([^"\']*)["\']', t))
        src = attrs.get("data-src") or attrs.get("src") or ""
        if not src and attrs.get("srcset"):
            src = attrs["srcset"].split()[0]
        src = src.replace("&amp;", "&")
        low = src.lower().split("?")[0]
        if "/images/" not in low or not low.endswith(_IMG_EXT):
            continue
        fname = low.rsplit("/", 1)[-1]
        if _JUNK.search(fname) and want not in re.sub(r"[^a-z0-9]", "", fname):
            continue
        try:
            width = int(attrs.get("width", "0"))
        except ValueError:
            width = 0
        score = (10 if want and want in re.sub(r"[^a-z0-9]", "", fname + attrs.get("alt", "").lower()) else 0)
        score += 3 if width >= 150 else 0
        score -= 4 if 0 < width < 60 else 0
        found.append((-score, pos, urljoin(page_url, src)))
    out = []
    for _s, _p, url in sorted(found):
        out.append(url)
        m = re.match(r"(.*/images)/thumb/(.+?\.\w+)/[^/]+$", url)      # also try the full-size original
        if m:
            out.append(m.group(1) + "/" + m.group(2))
    return out


def _wiki_api_urls(base, timeout, req):
    """Core-MediaWiki fallback: list the page's files, then ask for a thumbnail URL of the best one."""
    import urllib.request
    import urllib.parse
    want = re.sub(r"[^a-z0-9]", "", base.lower())
    for api in ("https://skylanderswiki.com/api.php", "https://skylanderswiki.com/w/api.php"):
        try:
            q = urllib.parse.urlencode({"action": "parse", "page": base, "prop": "images", "format": "json"})
            data = json.loads(urllib.request.urlopen(urllib.request.Request(api + "?" + q, headers=req),
                                                     timeout=timeout).read().decode("utf-8"))
            files = [f for f in data.get("parse", {}).get("images", []) if f.lower().endswith(_IMG_EXT)]
            files.sort(key=lambda f: (want not in re.sub(r"[^a-z0-9]", "", f.lower()),
                                      bool(_JUNK.search(f))))
            out = []
            for f in files[:3]:
                q = urllib.parse.urlencode({"action": "query", "titles": "File:" + f, "prop": "imageinfo",
                                            "iiprop": "url", "iiurlwidth": 320, "format": "json"})
                info = json.loads(urllib.request.urlopen(urllib.request.Request(api + "?" + q, headers=req),
                                                         timeout=timeout).read().decode("utf-8"))
                for pg in info.get("query", {}).get("pages", {}).values():
                    for ii in pg.get("imageinfo", []):
                        out += [u for u in (ii.get("thumburl"), ii.get("url")) if u]
            if out:
                return out
        except Exception:
            continue
    return []


def fetch_image(fid, var, name, timeout=8, extra=(), save_stem=None):
    """Best-effort download of the character's wiki picture into ./skylander_images.  Tries the more
    specific names in `extra` first (e.g. 'Pearl Sprocket'), then `name`, then its base character name."""
    if not is_online():
        raise RuntimeError("offline - using only pictures from %s" % IMG_DIR)
    names, last = [], None
    for n in list(extra) + [name, _base_name(name)]:
        if n and n not in names:
            names.append(n)
    for n in names:
        try:
            return _fetch_one(fid, var, n, timeout, save_stem)
        except Exception as e:
            last = e
    raise last or RuntimeError("no picture found on the wiki page")


def _fetch_one(fid, var, name, timeout=8, save_stem=None):
    import urllib.request
    import urllib.parse
    base = _page_name(name).replace(" ", "_")
    page = "https://skylanderswiki.com/wiki/" + urllib.parse.quote(base)
    req = {"User-Agent": "Mozilla/5.0 (skylander_editor)", "Accept-Language": "en"}
    html = urllib.request.urlopen(urllib.request.Request(page, headers=req), timeout=timeout).read().decode(
        "utf-8", "replace")
    urls = []
    og = og_image(html)
    if og:
        urls.append(urllib.parse.urljoin(page, og))
    urls += page_image_urls(html, base.replace("_", " "), page)
    if not urls:
        urls = _wiki_api_urls(base, timeout, req)
    if not urls:
        raise RuntimeError("no picture found on the wiki page")
    last = None
    for url in urls[:6]:
        try:
            data = urllib.request.urlopen(urllib.request.Request(url, headers=req), timeout=timeout).read()
            return save_picture_bytes(fid, var, data, save_stem)
        except Exception as e:                      # try the next candidate
            last = e
    raise RuntimeError("download failed (%s)" % last)


def save_picture_bytes(fid, var, data, stem=None):
    """Store image bytes as skylander_images/<id>_<variant>.png (or .gif); non-PNG needs Pillow."""
    os.makedirs(IMG_DIR, exist_ok=True)
    stem = os.path.join(IMG_DIR, stem or "%d_%d" % (fid, var))
    for ext in (".png", ".gif", ".jpg", ".jpeg", ".webp"):          # replace any older picture
        if os.path.isfile(stem + ext):
            os.remove(stem + ext)
    if data[:8] == b"\x89PNG\r\n\x1a\n":
        out = stem + ".png"
        open(out, "wb").write(data)
    elif data[:3] == b"GIF":
        out = stem + ".gif"
        open(out, "wb").write(data)
    else:
        try:
            import io
            from PIL import Image
        except ImportError:
            raise RuntimeError("picture is not a PNG; install Pillow (pip install pillow) or use a PNG")
        out = stem + ".png"
        Image.open(io.BytesIO(data)).convert("RGBA").save(out, "PNG")
    return out


LIGHT = dict(bg="#f0f0f0", fg="#000000", field="#ffffff", btn="#e1e1e1", active="#d0d0d0",
             border="#adadad", select="#3399ff")
DARK = dict(bg="#1e1e1e", fg="#e6e6e6", field="#2b2b2b", btn="#3a3a3a", active="#4a4a4a",
            border="#555555", select="#264f78")
CONFIG = os.path.expanduser("~/.skylander_editor.json")


def _cfg():
    try:
        with open(CONFIG) as f:
            d = json.load(f)
        return d if isinstance(d, dict) else {}
    except Exception:
        return {}


def _cfg_set(**kw):
    d = _cfg()
    d.update(kw)
    try:
        with open(CONFIG, "w") as f:
            json.dump(d, f)
    except Exception:
        pass


def _load_dark():
    return bool(_cfg().get("dark", False))


def _save_dark(on):
    _cfg_set(dark=bool(on))


SAVE_TYPES = [("Raw dump (.bin)", "*.bin"), ("Raw dump (.sky)", "*.sky"), ("Raw dump (.dmp)", "*.dmp"),
              ("Flipper Zero (.nfc)", "*.nfc"), ("All files", "*.*")]


class Editor:
    def __init__(self, root, dnd=None):
        self.root = root
        self.dump = None
        root.title(APP)
        root.minsize(600, 640)
        self.v = {k: tk.StringVar() for k in ("xp", "gold", "hp", "name", "hat", "skills")}
        self.info = {k: tk.StringVar(value="-") for k in ("file", "format", "uid", "figure", "areas", "sums", "platform")}
        self.status = tk.StringVar(value="Open a figure dump to begin (Ctrl+O).")
        self.level = tk.StringVar(value="1")
        self.dark = tk.BooleanVar(value=_load_dark())
        self._texts = []
        self.fdb = load_figure_db()
        self.fig_name = tk.StringVar(value="No figure loaded")
        self.fig_sub = tk.StringVar(value="")
        self._photo = None
        self.auto = tk.BooleanVar(value=bool(_cfg().get("auto_pic", False)))
        self._pic_tried = set()          # figures we already failed to fetch a picture for (this session)
        self._pic_busy = None
        self._build()
        if dnd:
            root.drop_target_register(dnd)
            root.dnd_bind("<<Drop>>", self._on_drop)
            self.status.set("Open a figure dump, or just drop one onto this window.")
        else:
            self.status.set("Open a figure dump to begin (Ctrl+O).  Tip: pip install tkinterdnd2 "
                            "enables drag-and-drop.")
        if not self.fdb.full:
            self._start_db_download()
        self.v["xp"].trace_add("write", lambda *a: self._xp_to_level())
        self.apply_theme()
        root.bind("<Control-o>", lambda e: self.open_file())
        root.bind("<Control-s>", lambda e: self.save())

    def _build(self):
        bar = ttk.Frame(self.root, padding=(8, 8, 8, 4))
        bar.pack(fill="x")
        ttk.Button(bar, text="Open…", command=self.open_file).pack(side="left")
        ttk.Button(bar, text="Save", command=self.save).pack(side="left", padx=4)
        ttk.Button(bar, text="Save As…", command=self.save_as).pack(side="left")
        conv = ttk.Menubutton(bar, text="Convert to \u25be")
        menu = tk.Menu(conv, tearoff=False)
        for label, ext in ((".bin  (raw dump)", ".bin"), (".sky  (raw dump)", ".sky"),
                           (".dmp  (raw dump)", ".dmp"), (".nfc  (Flipper Zero)", ".nfc")):
            menu.add_command(label=label, command=lambda e=ext: self.convert(e))
        conv["menu"] = menu
        conv.pack(side="left", padx=4)
        ttk.Button(bar, text="All pictures…", command=self.download_all_pictures).pack(side="left", padx=(12, 0))
        ttk.Checkbutton(bar, text="Dark mode", variable=self.dark, command=self.apply_theme).pack(side="right")

        nb = ttk.Notebook(self.root)
        nb.pack(fill="both", expand=True, padx=8, pady=4)

        tab = ttk.Frame(nb, padding=10)
        nb.add(tab, text="Editor")
        fig = ttk.LabelFrame(tab, text="Figure", padding=8)
        fig.pack(fill="x")
        top = ttk.Frame(fig)
        top.pack(fill="x", pady=(0, 6))
        self.pic = ttk.Label(top, text="no\npicture", anchor="center", justify="center", width=14)
        self.pic.grid(row=0, column=0, rowspan=3, padx=(0, 12), sticky="n")
        ttk.Label(top, textvariable=self.fig_name, font=("TkDefaultFont", 16, "bold"),
                  wraplength=400, justify="left").grid(row=0, column=1, sticky="w")
        ttk.Label(top, textvariable=self.fig_sub).grid(row=1, column=1, sticky="w")
        picbar = ttk.Frame(top)
        picbar.grid(row=2, column=1, sticky="w", pady=4)
        self.btn_pic = ttk.Button(picbar, text="Get picture online", command=self.get_picture)
        self.btn_pic.pack(side="left")
        ttk.Checkbutton(picbar, text="Auto", variable=self.auto, command=self._auto_toggled).pack(
            side="left", padx=(8, 0))
        ttk.Button(picbar, text="Change character\u2026", command=self.change_character).pack(
            side="left", padx=(12, 0))
        details = ttk.Frame(fig)
        details.pack(fill="x")
        fig = details
        rows = (("File", "file"), ("Format", "format"), ("UID", "uid"), ("Figure ID", "figure"),
                ("Data areas", "areas"), ("Checksums", "sums"), ("Platform flags", "platform"))
        for i, (label, key) in enumerate(rows):
            ttk.Label(fig, text=label).grid(row=i, column=0, sticky="w")
            ttk.Label(fig, textvariable=self.info[key], wraplength=430, justify="left").grid(
                row=i, column=1, sticky="w", padx=10)

        st = ttk.LabelFrame(tab, text="Stats (active data area)", padding=8)
        st.pack(fill="x", pady=10)

        def spin(r, label, key, lo, hi, buttons=()):
            ttk.Label(st, text=label).grid(row=r, column=0, sticky="w", pady=3)
            ttk.Spinbox(st, from_=lo, to=hi, textvariable=self.v[key], width=12).grid(row=r, column=1, sticky="w", padx=8)
            for c, (text, val) in enumerate(buttons):
                ttk.Button(st, text=text, command=lambda k=key, x=val: self.v[k].set(x)).grid(row=r, column=2 + c, padx=2)

        ttk.Label(st, text="Level (1-20)").grid(row=0, column=0, sticky="w", pady=3)
        vcmd = (self.root.register(self._level_ok), "%P")
        lv = ttk.Spinbox(st, from_=1, to=20, textvariable=self.level, width=12, validate="key",
                         validatecommand=vcmd, command=self._level_commit)
        lv.grid(row=0, column=1, sticky="w", padx=8)
        lv.bind("<Return>", lambda e: self._level_commit())
        lv.bind("<FocusOut>", lambda e: self._level_commit())
        ttk.Label(st, text="sets XP to the start of that level").grid(row=0, column=2, columnspan=3, sticky="w")
        spin(1, "Experience (XP)", "xp", 0, XP_MAX, (("L10 = 33,000", "33000"), ("L20 = max", str(XP_MAX))))
        spin(2, "Gold", "gold", 0, 65000, (("Max", "65000"),))
        spin(3, "Hero points", "hp", 0, 100, (("Max", "100"),))
        spin(4, "Hat ID", "hat", 0, HAT_MAX)
        ttk.Label(st, text="Nickname").grid(row=5, column=0, sticky="w", pady=3)
        ttk.Entry(st, textvariable=self.v["name"], width=20).grid(row=5, column=1, sticky="w", padx=8)
        ttk.Label(st, text="max 14 chars").grid(row=5, column=2, sticky="w")
        ttk.Label(st, text="Skill bits (hex)").grid(row=6, column=0, sticky="w", pady=3)
        ttk.Entry(st, textvariable=self.v["skills"], width=12).grid(row=6, column=1, sticky="w", padx=8)
        ttk.Button(st, text="All – left", command=lambda: self.v["skills"].set("0FFD")).grid(row=6, column=2, padx=2)
        ttk.Button(st, text="All – right", command=lambda: self.v["skills"].set("0FFF")).grid(row=6, column=3, padx=2)

        actions = ttk.Frame(tab)
        actions.pack(fill="x", pady=(4, 0))
        ttk.Button(actions, text="Reset stats\u2026", command=self.reset_stats).pack(side="left")
        ttk.Button(actions, text="Apply && Save", command=self.save).pack(side="right")

        hexf = ttk.Frame(nb, padding=6)
        nb.add(hexf, text="Hex (decrypted)")
        self.hex = tk.Text(hexf, font="TkFixedFont", wrap="none", state="disabled", height=20)
        self._texts.append(self.hex)
        self.hex.pack(fill="both", expand=True)

        nf = ttk.Frame(nb, padding=6)
        nb.add(nf, text="Notes")
        t = tk.Text(nf, wrap="word", font="TkDefaultFont")
        t.insert("1.0", NOTES)
        t.configure(state="disabled")
        t.pack(fill="both", expand=True)
        self._texts.append(t)

        ttk.Label(self.root, textvariable=self.status, relief="sunken", anchor="w", padding=4).pack(fill="x", side="bottom")

    # -- which figure is it? ----------------------------------------------------
    def _start_db_download(self):
        """Fetch the full figure list in the background; the GUI thread polls for the result."""
        import threading
        self._db_result = []

        def work():
            try:
                self._db_result.append(download_figure_db())
            except Exception as e:                       # offline etc.: keep the built-in list
                self._db_result.append(e)
        threading.Thread(target=work, daemon=True).start()
        self.root.after(500, self._poll_db)

    def _poll_db(self):
        if not self._db_result:
            self.root.after(500, self._poll_db)
            return
        if isinstance(self._db_result[0], int):
            self.fdb = load_figure_db()
            self.status.set("Figure list downloaded (%d entries)." % self.fdb.size)
            if self.dump:
                self._show_figure()

    def _name_hints(self, info):
        """The file name (e.g. 'Pearl Sprocket.dump') is a better picture name than the base character
        when the figure list does not know this variant - but only if it mentions the character."""
        if info["exact"] or not self.dump or not self.dump.path:
            return ()
        stem = os.path.splitext(os.path.basename(self.dump.path))[0].strip()
        if info["base"] and info["base"].lower() in stem.lower() and stem.lower() != info["base"].lower():
            return (stem,)
        return ()

    def _figure_info(self):
        d = self.dump
        return d.figure_id(), d.variant_id(), self.fdb.lookup(d.figure_id(), d.variant_id())

    def _show_figure(self):
        if not self.dump:
            return
        fid, var, info = self._figure_info()
        hints = self._name_hints(info)
        self.fig_name.set(hints[0] if hints else info["name"])
        bits = [x for x in (info["series"], info["element"]) if x]
        bits.append("ID %d / variant 0x%04X" % (fid, var))
        if info["note"]:
            bits.append(info["note"] + (" - name taken from the file name" if hints else ""))
        self.fig_sub.set("  \u00b7  ".join(bits))
        path = find_image(fid, var, info["name"], hints)
        self._set_picture(path)
        if path is None and self.auto.get():
            self._auto_fetch(fid, var, info["name"], hints)

    def _set_picture(self, path):
        self._photo = None
        if path:
            img = None
            try:
                img = tk.PhotoImage(file=path)
            except Exception:
                try:
                    from PIL import Image, ImageTk
                    im = Image.open(path).convert("RGBA")
                    im.thumbnail((160, 160))
                    img = ImageTk.PhotoImage(im)
                except Exception:
                    img = None
            if img is not None:
                factor = max(1, -(-max(img.width(), img.height()) // 160))
                if factor > 1:
                    img = img.subsample(factor)
                self._photo = img
        if self._photo is not None:
            self.pic.configure(image=self._photo, text="")
        else:
            self.pic.configure(image="", text="no\npicture")

    def _auto_toggled(self):
        _cfg_set(auto_pic=bool(self.auto.get()))
        if self.auto.get() and self.dump:
            self._pic_tried.clear()
            self._show_figure()

    def _current_key(self):
        return (self.dump.figure_id(), self.dump.variant_id()) if self.dump else None

    def _auto_fetch(self, fid, var, name, hints=(), label="Auto: "):
        """Fetch the picture in a background thread so the window stays responsive."""
        import threading
        key = (fid, var)
        if self._pic_busy is not None:
            if not label:
                self.status.set("Still fetching another picture - try again in a moment.")
            return
        if key in self._pic_tried:
            return
        self._pic_busy = key
        self.status.set("%sfetching picture for %s ..." % (label, name))
        result = []

        def work():
            try:
                result.append(fetch_image(fid, var, name, extra=hints))
            except Exception as e:
                result.append(e)
        threading.Thread(target=work, daemon=True).start()
        self.root.after(300, lambda: self._poll_pic(key, name, result, label))

    def _poll_pic(self, key, name, result, label="Auto: "):
        if not result:
            self.root.after(300, lambda: self._poll_pic(key, name, result, label))
            return
        self._pic_busy = None
        r = result[0]
        here = self._current_key() == key
        if isinstance(r, Exception):
            self._pic_tried.add(key)
            if here:
                self.status.set("%sno picture for %s (%s). Drop an image onto the window to set one."
                                % (label, name, r))
        elif here:
            self._set_picture(r)
            self.status.set("%spicture for %s saved to %s" % (label, name, r))
        if not here and self.auto.get():          # another figure was opened meanwhile
            self._show_figure()

    _PIC_EXT = (".png", ".gif", ".jpg", ".jpeg", ".webp", ".bmp")

    def _on_drop(self, event):
        paths = self.root.tk.splitlist(event.data)
        if paths:
            p = paths[0]
            if p.lower().endswith(self._PIC_EXT):
                self.use_picture(p)
            else:
                self.open_file(p)
        return event.action

    def use_picture(self, path):
        """A dropped image becomes the picture for the figure that is currently open."""
        if not self.dump:
            self.status.set("Open a figure first, then drop the picture onto the window.")
            return
        fid, var, _info = self._figure_info()
        try:
            out = save_picture_bytes(fid, var, open(path, "rb").read())
        except Exception as e:
            self.status.set("Could not use that picture (%s)" % e)
            return
        self._set_picture(out)
        if self._photo is None:
            self.status.set("Saved %s but it cannot be displayed (PNG or GIF work out of the box; "
                            "others need Pillow)." % out)
        else:
            self.status.set("Picture set for this figure (saved to %s)." % out)

    def get_picture(self):
        if not self.dump:
            return
        fid, var, info = self._figure_info()
        self._pic_tried.discard((fid, var))
        self._auto_fetch(fid, var, info["name"], self._name_hints(info), label="")

    # -- reset / change character ----------------------------------------------
    def reset_stats(self):
        """Put the form back to a fresh figure's values.  Nothing is written until Apply & Save."""
        if not self.dump:
            messagebox.showinfo(APP, "Open a dump first.")
            return
        if not messagebox.askyesno(APP, "Reset this figure's progress?\n\nXP / level, gold, hero points, hat, "
                                        "nickname and skill choices go back to the values of a fresh figure.\n"
                                        "The character itself (and its UID) is NOT changed.\n\n"
                                        "Nothing is written until you press Apply && Save."):
            return
        for k, v in (("xp", "0"), ("gold", "0"), ("hp", "0"), ("hat", "0"), ("name", ""), ("skills", "0000")):
            self.v[k].set(v)
        self.status.set("Stats reset in the form - press Apply && Save to write them to the file.")

    def _refresh_identity(self):
        d = self.dump
        self.info["figure"].set("0x%04X (%d), variant 0x%04X" % (d.figure_id(), d.figure_id(), d.variant_id()))
        self._pic_tried.clear()
        self._show_figure()
        self.hex.configure(state="normal")
        self.hex.delete("1.0", "end")
        self.hex.insert("1.0", d.hexview())
        self.hex.configure(state="disabled")

    def change_character(self):
        """Dialog that asks which game / type / element, lists the matches, and applies the choice."""
        if not self.dump:
            messagebox.showinfo(APP, "Open a dump first.")
            return
        c = DARK if self.dark.get() else LIGHT
        entries = self.fdb.entries()
        dlg = tk.Toplevel(self.root)
        dlg.title("Change character")
        dlg.configure(bg=c["bg"])
        dlg.geometry("760x520")
        dlg.transient(self.root)
        elements = sorted({e["element"] for e in entries if e["element"] and e["element"] != "None"})
        games = [g for g in GAMES if any(e["series"] == g for e in entries)]
        kinds = [k for k in KINDS if any(e["kind"] == k for e in entries)]
        ALL = ("All games", "All types", "All elements")
        var_game, var_kind, var_el, var_txt = (tk.StringVar(value=ALL[0]), tk.StringVar(value=ALL[1]),
                                               tk.StringVar(value=ALL[2]), tk.StringVar())
        top = ttk.Frame(dlg, padding=(10, 10, 10, 4))
        top.pack(fill="x")
        for col, (label, var, values) in enumerate((("Which game?", var_game, (ALL[0],) + tuple(games)),
                                                    ("Character, item or trap?", var_kind, (ALL[1],) + tuple(kinds)),
                                                    ("Element?", var_el, (ALL[2],) + tuple(elements)))):
            ttk.Label(top, text=label).grid(row=0, column=col, sticky="w", padx=(0, 10))
            ttk.Combobox(top, textvariable=var, values=values, state="readonly", width=20).grid(
                row=1, column=col, padx=(0, 10), sticky="w")
        ttk.Label(top, text="Search name").grid(row=0, column=3, sticky="w")
        ttk.Entry(top, textvariable=var_txt, width=18).grid(row=1, column=3, sticky="w")

        if not self.fdb.full:
            ttk.Label(dlg, text="Showing the built-in list (Spyro's Adventure, Giants and most Trap Team items). "
                                "The complete list (Swap Force, SuperChargers, Imaginators ...) is downloaded "
                                "automatically the first time you are online.",
                      wraplength=720, justify="left").pack(fill="x", padx=10)
        cols = (("name", "Name", 260), ("series", "Game", 120), ("kind", "Type", 80),
                ("element", "Element", 70), ("id", "ID", 50), ("var", "Variant", 70))
        frame = ttk.Frame(dlg, padding=(10, 4))
        frame.pack(fill="both", expand=True)
        tree = ttk.Treeview(frame, columns=[k for k, _l, _w in cols], show="headings", selectmode="browse")
        for key, label, width in cols:
            tree.heading(key, text=label)
            tree.column(key, width=width, anchor="w")
        sb = ttk.Scrollbar(frame, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=sb.set)
        tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        count = tk.StringVar()
        ttk.Label(dlg, textvariable=count).pack(anchor="w", padx=10)
        shown = []

        def refill(*_):
            shown[:] = filter_entries(
                entries, "" if var_game.get() == ALL[0] else var_game.get(),
                "" if var_kind.get() == ALL[1] else var_kind.get(),
                "" if var_el.get() == ALL[2] else var_el.get(), var_txt.get())
            tree.delete(*tree.get_children())
            for i, e in enumerate(shown):
                tree.insert("", "end", iid=str(i), values=(e["name"], e["series"], e["kind"], e["element"],
                                                           e["id"], "0x%04X" % e["var"]))
            count.set("%d match%s" % (len(shown), "" if len(shown) == 1 else "es"))
        for v in (var_game, var_kind, var_el, var_txt):
            v.trace_add("write", refill)
        refill()

        def export():
            path = filedialog.asksaveasfilename(parent=dlg, title="Export list", defaultextension=".csv",
                                                initialfile="skylanders_figures.csv",
                                                filetypes=[("CSV", "*.csv"), ("All files", "*.*")])
            if path:
                with open(path, "w", encoding="utf-8", newline="") as f:
                    f.write(entries_to_csv(shown))
                self.status.set("Exported %d figures to %s" % (len(shown), path))

        def choose(_event=None):
            sel = tree.selection()
            if not sel:
                messagebox.showinfo(APP, "Select a character first.", parent=dlg)
                return
            e = shown[int(sel[0])]
            now = self.fdb.lookup(self.dump.figure_id(), self.dump.variant_id())["name"]
            if not messagebox.askyesno(
                    APP, "Change this figure from\n    %s\nto\n    %s  (%s, ID %d, variant 0x%04X)?\n\n"
                         "Only the figure's identity changes; its save data stays. Games may reject a "
                         "figure whose data does not fit the new character, so keep a backup (one is made "
                         "next to the file on first save)." % (now, e["name"], e["series"] or "?", e["id"],
                                                               e["var"]), parent=dlg):
                return
            self.dump.set_identity(e["id"], e["var"])
            dlg.destroy()
            self._refresh_identity()
            self.status.set("Changed to %s - press Apply && Save to write the file." % e["name"])
        tree.bind("<Double-1>", choose)
        btns = ttk.Frame(dlg, padding=10)
        btns.pack(fill="x")
        ttk.Button(btns, text="Export list\u2026", command=export).pack(side="left")
        ttk.Button(btns, text="Pictures for offline\u2026",
                   command=lambda: self._prefetch_dialog(dlg, list(shown))).pack(side="left", padx=6)
        ttk.Button(btns, text="Cancel", command=dlg.destroy).pack(side="right")
        ttk.Button(btns, text="Use selected", command=choose).pack(side="right", padx=6)

    def download_all_pictures(self):
        """Toolbar button: every character in the figure list."""
        self._prefetch_dialog(self.root, self.fdb.entries())

    def _prefetch_dialog(self, parent, items):
        """Download the pictures of the listed characters once, so they also show up offline."""
        import threading
        if not items:
            messagebox.showinfo(APP, "The list is empty - pick a game / type first.", parent=parent)
            return
        groups = picture_groups(items)
        if not groups:
            messagebox.showinfo(APP, "Every character in this list already has a picture saved locally.",
                                parent=parent)
            return
        note = "" if self.fdb.full else (
            "\n\nNote: only the built-in figure list is loaded (the complete list downloads when you are "
            "online), so characters from later games are not included yet.")
        if not messagebox.askyesno(
                APP, "Download pictures for offline use?\n\n%d characters have no picture yet (variants share "
                     "their character's picture). This asks skylanderswiki.com for each one - about %d "
                     "requests, a few minutes - and saves them to:\n%s%s"
                     % (len(groups), 2 * len(groups), IMG_DIR, note), parent=parent):
            return
        state = {}
        dlg = tk.Toplevel(parent)
        dlg.title("Downloading pictures")
        dlg.transient(parent)
        dlg.configure(bg=(DARK if self.dark.get() else LIGHT)["bg"])
        msg = tk.StringVar(value="Starting ...")
        ttk.Label(dlg, textvariable=msg, padding=12).pack()
        bar = ttk.Progressbar(dlg, length=360, mode="determinate")
        bar.pack(padx=12)
        btn = ttk.Button(dlg, text="Cancel", command=lambda: state.update(cancel=True))
        btn.pack(pady=12)

        def run():
            try:
                prefetch_pictures(items, state)
            except Exception as e:                    # never leave the dialog hanging on "Starting ..."
                state.update(error="failed: %s" % e, finished=True)
        threading.Thread(target=run, daemon=True).start()

        def poll():
            if state.get("error") == "offline":
                msg.set("You are offline - connect to the internet and try again.")
                btn.configure(text="Close", command=dlg.destroy)
                return
            if state.get("error"):
                msg.set("Download stopped: %s" % state["error"])
                btn.configure(text="Close", command=dlg.destroy)
                return
            total = max(state.get("total", 0), 1)
            bar.configure(maximum=total, value=state.get("done", 0))
            msg.set("%d / %d characters  (%d saved, %d without a picture)" % (
                state.get("done", 0), state.get("total", 0), state.get("ok", 0), state.get("fail", 0)))
            if state.get("finished"):
                msg.set(msg.get() + ("  - stopped" if state.get("cancel") else "  - finished"))
                btn.configure(text="Close", command=dlg.destroy)
                self._pic_tried.clear()
                if self.dump:
                    self._show_figure()
                return
            dlg.after(300, poll)
        dlg.after(300, poll)

    # -- level / theme -----------------------------------------------------
    @staticmethod
    def _level_ok(proposed):
        """Allow only an empty box or a whole number 1-20 while typing."""
        if proposed == "":
            return True
        return proposed.isdigit() and len(proposed) <= 2 and 1 <= int(proposed) <= 20

    def _level_commit(self):
        try:
            lvl = int(self.level.get())
        except ValueError:
            lvl = level_for_xp(self._xp_value())
        lvl = max(1, min(20, lvl))
        self.level.set(str(lvl))
        if lvl != level_for_xp(self._xp_value()):       # leave a custom XP inside this level alone
            self.v["xp"].set(str(LEVEL_XP[lvl - 1]))

    def _xp_value(self):
        try:
            return int(self.v["xp"].get().replace(",", "").strip())
        except ValueError:
            return 0

    def _xp_to_level(self):
        self.level.set(str(level_for_xp(self._xp_value())))

    def apply_theme(self):
        c = DARK if self.dark.get() else LIGHT
        _save_dark(self.dark.get())
        st = ttk.Style()
        st.theme_use("clam")
        st.configure(".", background=c["bg"], foreground=c["fg"], fieldbackground=c["field"],
                     bordercolor=c["border"], lightcolor=c["bg"], darkcolor=c["bg"],
                     troughcolor=c["field"], insertcolor=c["fg"])
        st.configure("TLabelframe", background=c["bg"], bordercolor=c["border"])
        st.configure("TLabelframe.Label", background=c["bg"], foreground=c["fg"])
        st.configure("TButton", background=c["btn"], foreground=c["fg"], bordercolor=c["border"])
        st.map("TButton", background=[("active", c["active"])])
        st.configure("TCheckbutton", background=c["bg"], foreground=c["fg"])
        st.map("TCheckbutton", background=[("active", c["bg"])])
        for w in ("TEntry", "TSpinbox"):
            st.configure(w, fieldbackground=c["field"], foreground=c["fg"], insertcolor=c["fg"],
                         bordercolor=c["border"])
        st.configure("TSpinbox", arrowcolor=c["fg"], background=c["btn"])
        st.map("TSpinbox", background=[("active", c["active"])])
        st.configure("TNotebook", background=c["bg"], bordercolor=c["border"])
        st.configure("TNotebook.Tab", background=c["btn"], foreground=c["fg"], padding=(10, 4))
        st.map("TNotebook.Tab", background=[("selected", c["bg"])], foreground=[("selected", c["fg"])])
        st.configure("Treeview", background=c["field"], fieldbackground=c["field"], foreground=c["fg"],
                     bordercolor=c["border"])
        st.configure("Treeview.Heading", background=c["btn"], foreground=c["fg"])
        st.map("Treeview", background=[("selected", c["select"])], foreground=[("selected", "#ffffff")])
        st.configure("TCombobox", fieldbackground=c["field"], background=c["btn"], foreground=c["fg"],
                     arrowcolor=c["fg"], selectbackground=c["field"], selectforeground=c["fg"])
        st.map("TCombobox", fieldbackground=[("readonly", c["field"])], foreground=[("readonly", c["fg"])])
        self.root.option_add("*TCombobox*Listbox.background", c["field"])
        self.root.option_add("*TCombobox*Listbox.foreground", c["fg"])
        self.root.option_add("*TCombobox*Listbox.selectBackground", c["select"])
        self.root.configure(bg=c["bg"])
        for t in self._texts:
            t.configure(bg=c["field"], fg=c["fg"], insertbackground=c["fg"],
                        selectbackground=c["select"], selectforeground="#ffffff")

    # -- actions -----------------------------------------------------------
    def open_file(self, path=None):
        path = path or filedialog.askopenfilename(
            title="Open Skylanders dump",
            filetypes=[("Figure dumps", "*.bin *.sky *.dmp *.nfc"), ("All files", "*.*")])
        if not path:
            return
        try:
            self.dump = FigureDump.load(path)
        except Exception as e:
            messagebox.showerror(APP, "Could not open file:\n%s" % e)
            return
        self.refresh()
        if self.dump.blank:
            messagebox.showinfo(APP, "This figure has no save data yet.\n\nIt has never been used in a game, "
                                     "so its data blocks are completely empty (no XP, gold, nickname or "
                                     "checksums to edit).\n\nPut it on the portal in a game once so the game "
                                     "writes its data, dump it again, and then open that dump here.")
        elif self.dump.valid_found == 0:
            messagebox.showwarning(APP, "No valid checksums were found in either data area. The figure may be "
                                        "blank, corrupt or from an unsupported game. Edit with care.")
        self.status.set("Opened %s" % os.path.basename(path))

    def refresh(self):
        d = self.dump
        rep = d.report()
        bad = ["type %d/A%d" % (t, a) for (t, a), (s, c) in rep.items() if s != c]
        self.info["file"].set(d.path or "-")
        self.info["format"].set(("Flipper .nfc" if d.fmt == "nfc" else "raw dump (.bin/.sky/.dmp)") + ", data " +
                                ("encrypted" if d.encrypted else "decrypted"))
        self.info["uid"].set(d.uid())
        self.info["figure"].set("0x%04X (%d), variant 0x%04X" % (d.figure_id(), d.figure_id(), d.variant_id()))
        self.info["areas"].set("A0 %s / A1 %s  ->  editing A%d" % (
            *("empty" if d._area_blank(x) else "seq %d" % d.seq(x) for x in (0, 1)), d.active_area()))
        self.info["sums"].set("all OK" if not bad else "bad: " + ", ".join(bad))
        self.info["platform"].set("0x%02X" % d.platform_flags())
        self._show_figure()
        self.v["xp"].set(str(d.get_xp()))
        self.v["gold"].set(str(d.get_gold()))
        self.v["hp"].set(str(d.get_hero_points()))
        self.v["hat"].set(str(d.get_hat()))
        self.v["name"].set(d.get_name())
        self.v["skills"].set("%04X" % d.get_skills())
        self.hex.configure(state="normal")
        self.hex.delete("1.0", "end")
        self.hex.insert("1.0", d.hexview())
        self.hex.configure(state="disabled")

    def _collect(self):
        def num(key, label, lo, hi, base=10):
            try:
                x = int(self.v[key].get().replace(",", "").strip(), base)
            except ValueError:
                raise ValueError("%s must be a number." % label)
            if not lo <= x <= hi:
                raise ValueError("%s must be between %d and %d." % (label, lo, hi))
            return x
        return (num("xp", "XP", 0, XP_MAX), num("gold", "Gold", 0, 65000),
                num("hp", "Hero points", 0, 100), self.v["name"].get(),
                num("hat", "Hat ID", 0, HAT_MAX), num("skills", "Skill bits", 0, 0xFFFF, 16))

    def save(self):
        self._save(self.dump.path if self.dump else None)

    def save_as(self):
        if not self.dump:
            return
        ext = ".nfc" if self.dump.fmt == "nfc" else ".bin"
        path = filedialog.asksaveasfilename(
            title="Save as (the extension picks the format: .bin .sky .dmp = raw, .nfc = Flipper)",
            defaultextension=ext, filetypes=SAVE_TYPES,
            initialfile=os.path.basename(self.dump.path or "figure" + ext))
        if path:
            self._save(path)

    def convert(self, ext):
        """Save a copy of the figure in another format (.bin / .sky / .dmp / .nfc).  Any edits currently
        in the form are applied, exactly as with Save As."""
        if not self.dump:
            messagebox.showinfo(APP, "Open a dump first.")
            return
        base = os.path.splitext(os.path.basename(self.dump.path or "figure"))[0]
        path = filedialog.asksaveasfilename(title="Convert to " + ext, defaultextension=ext,
                                            filetypes=SAVE_TYPES, initialfile=base + ext)
        if not path:
            return
        if self.dump.blank and not self.dump.dirty:     # nothing to edit, but it can still be converted
            try:
                self.dump.save(path)
            except Exception as e:
                messagebox.showerror(APP, str(e))
                return
            self.refresh()
            self.status.set("Converted to %s" % path)
            return
        self._save(path)

    def _save(self, path):
        if not self.dump:
            messagebox.showinfo(APP, "Open a dump first.")
            return
        if self.dump.blank and not self.dump.dirty:
            messagebox.showwarning(APP, "This figure has no save data yet (it was never used in a game), "
                                        "so there is nothing to edit. Use it in a game once, dump it again, "
                                        "then open that dump.")
            return
        if not path:
            return self.save_as()
        snapshot = bytes(self.dump.plain)
        try:
            values = self._collect()
            changed = False if self.dump.blank else self.dump.apply(*values)
            bad = self.dump.bad_checksums()
            if not changed and not bad and not self.dump.dirty and path == self.dump.path:
                self.status.set("No changes to save.")
                return
            if self.dump.valid_found == 0 and not messagebox.askyesno(
                    APP, "This dump had no valid checksums. Save anyway?"):
                self.dump.plain[:] = snapshot
                return
            self.dump.fix_all()
            self.dump.save(path)
            self.dump.dirty = False
        except Exception as e:
            self.dump.plain[:] = snapshot
            messagebox.showerror(APP, str(e))
            return
        self.refresh()
        self.status.set("Saved %s" % path)


def run_gui(path=None):
    if not HAVE_TK:
        sys.exit("tkinter is not installed.  On Linux Mint / Ubuntu run:  sudo apt install python3-tk")
    root, dnd = None, None
    try:                                           # optional: pip install tkinterdnd2
        from tkinterdnd2 import TkinterDnD, DND_FILES
        root, dnd = TkinterDnD.Tk(), DND_FILES
    except Exception:
        root = None
    if root is None:
        root = tk.Tk()
    ed = Editor(root, dnd)
    if path:
        ed.open_file(path)
    root.mainloop()


# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------
def _hexrow(s):
    return bytes.fromhex(s.replace(" ", ""))


def selftest():
    import tempfile
    # AES-128 FIPS-197 known answer
    key = bytes(range(16))
    pt = bytes.fromhex("00112233445566778899aabbccddeeff")
    ct = bytes.fromhex("69c4e0d86a7b0430d8cdb78070b4c55a")
    a = _PyAES128(key)
    assert a.encrypt(pt) == ct and a.decrypt(ct) == pt, "pure AES failed"
    if _PYCRYPTODOME_AES is not None:
        import os as _os
        for _ in range(20):
            k, b = _os.urandom(16), _os.urandom(16)
            assert _PyAES128(k).encrypt(b) == _PYCRYPTODOME_AES.new(k, _PYCRYPTODOME_AES.MODE_ECB).encrypt(b)
    assert len(HASH_CONST) == 0x35
    assert crc16(b"123456789") == 0x29B1, "crc16 failed"

    # Decrypted Gill Grunt dump published in the community notes (UID masked).
    plain = bytearray(SIZE)
    rows = {
        0x00: "01 02 03 04 CA 81 01 0F C3 85 14 91 55 50 10 11",
        0x01: "0E 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00",
        0x08: "00 00 00 00 00 6D 01 00 00 78 2E DF 3F 18 2C DD",
        0x09: "00 00 00 01 00 00 00 00 AF 2A BC 87 21 A8 63 9A",
        0x0D: "00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 01",
        0x24: "00 00 00 00 00 70 01 00 00 79 F8 ED 3F 18 C8 7A",
        0x25: "00 00 00 01 00 00 00 00 AF 2A BC 87 21 A8 63 9A",
        0x29: "35 14 16 0A DB 07 00 00 00 00 00 00 00 00 00 01",
        0x2A: "35 14 16 0A DB 07 00 00 00 00 00 00 00 00 00 00",
    }
    for blk, s in rows.items():
        plain[blk * 16:blk * 16 + 16] = _hexrow(s)
    for blk in range(3, 64, 4):
        plain[blk * 16 + 6:blk * 16 + 10] = bytes.fromhex("7F0F0869")
    rep = checksum_report(plain)
    for (t, ar), (s, c) in rep.items():
        if t:
            assert s == c, "checksum type %d area %d: stored %04X computed %04X" % (t, ar, s, c)
    print("ok: AES, CRC16 and the published real-figure checksums (types 1-3, both areas)")

    c = crc_type0(plain)
    plain[30], plain[31] = c & 0xFF, c >> 8

    # --- the two Imaginators blocks must be stored in the clear -------------------------------
    plain[0x22 * 16:0x23 * 16] = bytes(range(0xA0, 0xB0))
    plain[0x3E * 16:0x3F * 16] = bytes(range(0xC0, 0xD0))
    enc = crypt_dump(plain, decrypt=False)
    assert enc[0x22 * 16:0x23 * 16] == plain[0x22 * 16:0x23 * 16] and \
        enc[0x3E * 16:0x3F * 16] == plain[0x3E * 16:0x3F * 16], "blocks 0x22/0x3E must not be encrypted"
    assert enc != bytes(plain) and crypt_dump(enc, decrypt=True) == bytes(plain)

    # --- type 2/3/4 against a literal transcription of the reference VB (CRCcalculator.vb) ----
    import random
    rnd = random.Random(7)

    def vb_crc(d, sector, kind):
        o1, o2, o3, o4 = (128, 144, 208, 274) if sector == 1 else (576, 592, 656, 722)
        if kind == 2:
            buf, a_ = bytearray(48), 0
            for i in range(47):
                if i == 32:
                    a_ += 16
                buf[i] = d[o2 + a_]
                a_ += 1
            return crc16(bytes(buf))
        if kind == 3:
            buf, a_ = bytearray(272), 0
            for i in range(47):
                if i == 32:
                    a_ += 16
                buf[i] = d[o3 + a_]
                a_ += 1
            return crc16(bytes(buf))
        buf, a_ = bytearray(62), 0
        for i in range(61):
            if i == 30:
                a_ += 16
            buf[i] = d[o4 + a_]
            a_ += 1
        return crc16(bytes(buf)) ^ 0xE953

    for _ in range(25):
        r = bytearray(rnd.randrange(256) for _ in range(SIZE))
        for off in (207, 271, 351, 655, 719, 799):      # bytes the VB version leaves out (always 0)
            r[off] = 0
        r[(0x24 + 12) * 16 + 15] = 0
        for ar, sec in ((0, 1), (1, 2)):
            assert crc_type23(r, ar, 2) == vb_crc(r, sec, 2), "type 2 differs from reference"
            assert crc_type23(r, ar, 3) == vb_crc(r, sec, 3), "type 3 differs from reference"
            assert crc_type4(r, ar, True) == vb_crc(r, sec, 4), "type 4 differs from reference"
    print("ok: encrypted layout (0x22/0x3E in the clear) and type 2/3/4 checksums match the reference")

    # --- helpers for realistic figures ---------------------------------------------------------
    def make_figure(with_region2, seqs=(0x78, 0x79), seqs2=(1, 2)):
        p = bytearray(plain)
        p[0x08 * 16 + 9], p[0x24 * 16 + 9] = seqs
        if with_region2:
            for ar in (0, 1):
                o = (AREA_BASE[ar] + R2) * 16
                p[o + 2] = seqs2[ar]
                p[o + 3:o + 5] = (500).to_bytes(2, "little")          # something non-zero
        else:
            for ar in (0, 1):
                for r in (0, 1, 3, 4):
                    o = (AREA_BASE[ar] + R2 + r) * 16
                    p[o:o + 16] = bytes(16)
        d = FigureDump(p, True)
        d.fix_all()
        return d

    def write_dump(d, path):
        d.save(path)
        return FigureDump.load(path)

    with tempfile.TemporaryDirectory() as td:
        # raw encrypted .bin: load / edit / save / backup
        d = make_figure(True)
        p = os.path.join(td, "fig.bin")
        open(p, "wb").write(d.to_bytes())
        raw0 = open(p, "rb").read()
        d = FigureDump.load(p)
        assert d.encrypted and d.valid_found == 6 and not d.bad_checksums(0) and not d.bad_checksums(1)
        assert d.apply(33000, 65000, 100, "Gill", 7, 0x0FFD)
        d.fix_all()
        d.save(p)
        assert os.path.exists(p + ".bak") and open(p + ".bak", "rb").read() == raw0
        e = FigureDump.load(p)
        assert e.encrypted and e.valid_found == 6 and not e.bad_checksums(0) and not e.bad_checksums(1)
        assert (e.get_xp(), e.get_gold(), e.get_hero_points(), e.get_name(), e.get_hat(), e.get_skills()) == \
               (33000, 65000, 100, "Gill", 7, 0x0FFD)
        out = open(p, "rb").read()
        for blk in PLAIN_BLOCKS:                      # the bug: these used to get scrambled on save
            assert out[blk * 16:blk * 16 + 16] == raw0[blk * 16:blk * 16 + 16], "block %02X changed" % blk
        assert (e.seq(0), e.seq(1)) == (0x78, 0x79) and (e.seq2(0), e.seq2(1)) == (1, 2), "sequence numbers moved"
        for blk in range(3, 64, 4):
            assert out[blk * 16:blk * 16 + 16] == raw0[blk * 16:blk * 16 + 16], "trailer changed"
        for ar in (0, 1):                             # both areas carry the edit
            assert e.get_gold() == e._u16(e._o(0, 3, ar)) == 65000
        # decrypted .bin is detected too
        p2 = os.path.join(td, "dec.bin")
        open(p2, "wb").write(bytes(make_figure(True).plain))
        f = FigureDump.load(p2)
        assert not f.encrypted and f.valid_found == 6
        # Flipper .nfc round trip
        raw = make_figure(True).to_bytes()
        lines = ["Filetype: Flipper NFC device", "Version: 4", "UID: 01 02 03 04", "Mifare Classic type: 1K"]
        lines += ["Block %d: %s" % (i, " ".join("%02X" % b for b in raw[i * 16:i * 16 + 16])) for i in range(64)]
        p3 = os.path.join(td, "fig.nfc")
        open(p3, "w").write("\n".join(lines) + "\n")
        g = FigureDump.load(p3)
        assert g.fmt == "nfc" and g.encrypted and g.valid_found == 6
        g.apply(1234, 99, 5, "Test", 1, 0x0FFF)
        g.fix_all()
        g.save(p3)
        h = FigureDump.load(p3)
        assert (h.get_xp(), h.get_gold(), h.get_name()) == (1234, 99, "Test") and not h.bad_checksums()
        assert open(p3).read().startswith("Filetype: Flipper NFC device\nVersion: 4\nUID: 01 02 03 04")
        # conversion between .bin / .sky / .dmp / .nfc
        want = make_figure(True)
        want.apply(5000, 77, 3, "Conv", 4, 0x0FFF)
        want.fix_all()
        src = os.path.join(td, "src.bin")
        want.save(src)
        ref = open(src, "rb").read()
        assert len(ref) == SIZE
        for ext in (".sky", ".dmp"):                               # raw formats are byte-identical
            dst = os.path.join(td, "copy" + ext)
            FigureDump.load(src).save(dst)
            assert open(dst, "rb").read() == ref and FigureDump.load(dst).fmt == "bin"
        nfc_path = os.path.join(td, "conv.nfc")
        FigureDump.load(src).save(nfc_path)                        # raw -> Flipper (no header to reuse)
        txt = open(nfc_path).read()
        assert txt.startswith("Filetype: Flipper NFC device\nVersion: 4") and "UID: %s" % want.uid() in txt
        assert "Mifare Classic type: 1K" in txt and "ATQA: 00 04" in txt and "SAK: 08" in txt
        n2 = FigureDump.load(nfc_path)
        assert n2.fmt == "nfc" and n2.encrypted and n2.valid_found == 6 and n2.get_name() == "Conv"
        back = os.path.join(td, "back.sky")
        n2.save(back)                                              # Flipper -> raw .sky
        assert open(back, "rb").read() == ref and FigureDump.load(back).fmt == "bin"
        assert (format_for_path("a.NFC"), format_for_path("a.sky"), format_for_path("a.dmp"),
                format_for_path("a.txt", "nfc")) == ("nfc", "bin", "bin", "nfc")
        dec_nfc = os.path.join(td, "dec.nfc")                      # decrypted data stays decrypted when converted
        FigureDump.load(p2).save(dec_nfc)
        assert not FigureDump.load(dec_nfc).encrypted
        cli = os.path.join(td, "cli.sky")
        main(["x", "--convert", nfc_path, cli])
        assert open(cli, "rb").read() == ref
    print("ok: load / detect encrypted+decrypted / edit both areas / fix CRCs / save / backup / Flipper .nfc / convert")

    # --- XP and hat encodings across every threshold -------------------------------------------
    for xp in (0, 1, 32999, 33000, 33001, 96500, 96501, 162035, 162036, 162037, 197500):
        k = make_figure(True)
        k.apply(xp, 10, 0, "", 0, 0)
        k.fix_all()
        k2 = FigureDump(k.plain, True)
        assert k2.get_xp() == xp, "xp %d read back as %d" % (xp, k2.get_xp())
        assert not k2.bad_checksums(0) and not k2.bad_checksums(1), "bad checksum after xp %d" % xp
    for hat in (0, 1, 45, 46, 96, 97, 255, 256, 510):
        k = make_figure(True)
        k.apply(100, 10, 0, "", hat, 0)
        k.fix_all()
        assert FigureDump(k.plain, True).get_hat() == hat, "hat %d" % hat
        assert not k.bad_checksums(0) and not k.bad_checksums(1)
    k = make_figure(True)
    k.apply(5, 5, 0, "", 300, 0)                         # moving between hat slots clears the old one
    k.apply(5, 5, 0, "", 12, 0)
    assert k.get_hat() == 12 and k.plain[k._o2(14)] == 0
    try:
        k.apply(197501, 0, 0, "", 0, 0)
        raise AssertionError("XP above the cap was accepted")
    except ValueError:
        pass
    print("ok: XP (A/B/C split, 0 - 197,500) and hat (4 slots, 0 - 510) round-trip with valid checksums")

    # --- a Spyro's-Adventure-only figure: empty 2nd region ------------------------------------
    k = make_figure(False)
    assert not k.has_region2() and (4, 0) not in k.report()
    k.apply(20000, 300, 0, "Gill", 5, 0x0FFF)            # fits in the header region: leave region 2 alone
    k.fix_all()
    assert not k.has_region2() and not k.bad_checksums(0) and not k.bad_checksums(1)
    assert (k.get_xp(), k.get_hat(), k.get_gold()) == (20000, 5, 300)
    k.apply(150000, 300, 0, "Gill", 120, 0x0FFF)         # needs the 2nd region: it gets initialised
    k.fix_all()
    assert k.has_region2() and (k.seq2(0), k.seq2(1)) == (1, 2)
    k3 = FigureDump(k.plain, True)
    assert (k3.get_xp(), k3.get_hat()) == (150000, 120)
    assert not k3.bad_checksums(0) and not k3.bad_checksums(1) and (4, 0) in k3.report()
    print("ok: figures without a 2nd region are only upgraded when XP/hat need it")

    # --- the 2nd region may be 'newer' in the other area than the header region ----------------
    k = make_figure(True, seqs=(0x78, 0x79), seqs2=(5, 4))     # header: area 1 newer, region 2: area 0 newer
    assert k.active_area() == 1 and k.active_area2() == 0
    k.apply(80000, 10, 0, "", 50, 0)
    k.fix_all()
    k2 = FigureDump(k.plain, True)
    assert k2.get_xp() == 80000 and k2.get_hat() == 50
    assert FigureDump._newer(0x01, 0xFF) == 0 and FigureDump._newer(0xFF, 0x01) == 1   # wrap-around
    print("ok: per-region active-area selection, sequence wrap-around")

    # --- an untouched figure stays byte-identical -----------------------------------------------
    k = make_figure(True)
    before = bytes(k.plain)
    k.apply(k.get_xp(), k.get_gold(), k.get_hero_points(), k.get_name(), k.get_hat(), k.get_skills())
    k.fix_all()
    assert bytes(k.plain) == before
    assert LEVEL_XP[9] == XP_A_MAX and LEVEL_XP[19] == XP_MAX and len(LEVEL_XP) == 20
    assert [level_for_xp(x) for x in (0, 999, 1000, 32999, 33000, 197500)] == [1, 1, 2, 9, 10, 20]
    assert all(Editor._level_ok(x) for x in ("", "1", "9", "10", "20")) and \
        not any(Editor._level_ok(x) for x in ("0", "21", "99", "100", "-1", "a"))
    print("ok: level table and level-box validation (1-20 only)")
    sample = json.dumps([
        {"Id": 14, "Variant": 0, "Name": "Gill Grunt", "Series": "Spyros Adventure", "Element": "Water"},
        {"Id": 14, "Variant": 6145, "Name": "Gill Grunt (S2)", "Series": "Giants", "Element": "Water"},
        {"Id": 6, "Variant": 4096, "Name": "Hot Dog", "Series": "Giants", "Element": "Fire"},
        {"Id": 0, "Variant": 10245, "Name": "Whirlwind (Horn Blast)", "Series": "SwapForce", "Element": "Air"}])
    db = FigureDB.from_json(sample)
    assert db.lookup(14, 0)["name"] == "Gill Grunt" and db.lookup(14, 0)["series"] == "Spyro's Adventure"
    assert db.lookup(14, 6145)["name"] == "Gill Grunt (S2)" and db.lookup(0, 10245)["series"] == "Swap Force"
    assert db.lookup(105, 4096)["name"] == "Hot Dog"                 # typo in the source list is repaired
    assert db.lookup(14, 9999)["name"] == "Gill Grunt" and "0x270F" in db.lookup(14, 9999)["note"]
    assert db.lookup(14, 6145)["base"] == "Gill Grunt" and db.lookup(111, 0x1013)["base"] == "Sprocket"
    assert FigureDB().lookup(111, 0x1013)["name"] == "Sprocket" and FigureDB().lookup(111, 0)["note"] == ""
    assert FigureDB().lookup(14, 0)["name"] == "Gill Grunt" and FigureDB().lookup(14, 0)["exact"] is False
    assert FigureDB().lookup(9999, 1)["name"].startswith("Unknown figure (ID 9999")
    assert len(BASE_FIGURES) == 49 and BASE_FIGURES[105][0] == "Hot Dog"
    ff = make_figure(True)                                          # test figure is ID 14 (Gill Grunt)
    assert (ff.figure_id(), ff.variant_id()) == (14, 0)
    assert og_image('<meta property="og:image" content="https://x/y.png?a=1&amp;b=2">') == "https://x/y.png?a=1&b=2"
    assert og_image('<meta content="/img/z.jpg" property="og:image"/>') == "/img/z.jpg"
    assert og_image("<html></html>") is None
    with tempfile.TemporaryDirectory() as td:
        global IMG_DIR
        old, IMG_DIR = IMG_DIR, td
        try:
            assert find_image(14, 0, "Gill Grunt") is None
            open(os.path.join(td, "Gill_Grunt.png"), "wb").write(b"x")
            assert find_image(14, 6145, "Gill Grunt (S2)").endswith("Gill_Grunt.png")   # falls back to base name
            open(os.path.join(td, "14_6145.png"), "wb").write(b"x")
            assert find_image(14, 6145, "Gill Grunt (S2)").endswith("14_6145.png")      # exact variant wins
            open(os.path.join(td, "Pearl_Sprocket.png"), "wb").write(b"x")
            assert find_image(111, 0x1013, "Sprocket", ("Pearl Sprocket",)).endswith("Pearl_Sprocket.png")
            assert find_image(111, 0x1013, "Sprocket") is None
        finally:
            IMG_DIR = old
    wiki = ('<img alt="Skylanders Wiki" src="/images/b/bc/Wiki-wordmark.png" width="150">'
            '<img alt="Tech" src="/images/thumb/9/9a/Tech_icon.png/20px-Tech_icon.png" width="20">'
            '<img alt="Bouncer Giants.png" src="/images/thumb/1/1a/Bouncer_Giants.png/300px-Bouncer_Giants.png" '
            'width="300" height="300">'
            '<img alt="x" src="/images/thumb/2/2b/Bouncer_Swap.png/120px-Bouncer_Swap.png" width="120">'
            '<img src="/skins/logo.png">')
    urls = page_image_urls(wiki, "Bouncer", "https://skylanderswiki.com/wiki/Bouncer")
    assert urls[0] == "https://skylanderswiki.com/images/thumb/1/1a/Bouncer_Giants.png/300px-Bouncer_Giants.png"
    assert urls[1] == "https://skylanderswiki.com/images/1/1a/Bouncer_Giants.png"      # full-size fallback
    assert not any("icon" in u.lower() or "wordmark" in u.lower() or "logo" in u.lower() for u in urls)
    assert page_image_urls("<p>no images</p>", "Bouncer", "https://x/") == []
    png = b"\x89PNG\r\n\x1a\n" + b"0" * 20
    with tempfile.TemporaryDirectory() as td:
        old, IMG_DIR = IMG_DIR, td
        try:
            open(os.path.join(td, "14_0.gif"), "wb").write(b"GIF89a")
            out = save_picture_bytes(14, 0, png)
            assert out.endswith("14_0.png") and not os.path.exists(os.path.join(td, "14_0.gif"))
        finally:
            IMG_DIR = old
    with tempfile.TemporaryDirectory() as td:
        global CONFIG
        old_cfg, CONFIG = CONFIG, os.path.join(td, "cfg.json")
        try:
            assert _cfg() == {} and _load_dark() is False
            _save_dark(True)
            _cfg_set(auto_pic=True)
            assert _cfg() == {"dark": True, "auto_pic": True} and _load_dark() is True   # settings coexist
        finally:
            CONFIG = old_cfg
    fresh = bytearray(make_figure(True).to_bytes())              # a brand-new figure: UID + keys, no save data
    for b in range(8, 64):
        if b % 4 != 3:
            fresh[b * 16:b * 16 + 16] = bytes(16)
    with tempfile.TemporaryDirectory() as td:
        pb = os.path.join(td, "new.dump")
        open(pb, "wb").write(bytes(fresh))
        nb = FigureDump.load(pb)
        assert nb.blank and not nb.encrypted
        assert (nb.get_xp(), nb.get_gold(), nb.get_name(), nb.get_hat()) == (0, 0, "", 0)
        assert "NONE" in nb.describe() and (nb.figure_id(), nb.variant_id()) == (14, 0)
        assert not make_figure(True).blank
    half = bytearray(make_figure(True).to_bytes())              # like Ninjini/Thumpback: only area A1 was ever written
    for ar0 in range(8, 36):
        if ar0 % 4 != 3:
            half[ar0 * 16:ar0 * 16 + 16] = bytes(16)
    with tempfile.TemporaryDirectory() as td:
        ph = os.path.join(td, "half.dump")
        open(ph, "wb").write(bytes(half))
        h = FigureDump.load(ph)
        assert h.encrypted and not h.blank and h.active_area() == 1 and h._live() == [1]
        assert h.valid_found == 3 and not h.bad_checksums() and not any(
            s_ != c_ for (t_, _a), (s_, c_) in h.report().items())
        assert h.get_name() == "" and h.get_xp() == 500 and "empty" in h.describe()
        h.apply(40000, 123, 0, "Ninj", 50, 0x0FFF)
        h.fix_all()
        h.save(ph)
        out = open(ph, "rb").read()
        assert all(out[b_ * 16:b_ * 16 + 16] == bytes(16) for b_ in range(8, 36) if b_ % 4 != 3), \
            "the empty area must stay empty"
        h2 = FigureDump.load(ph)
        assert (h2.get_xp(), h2.get_gold(), h2.get_name(), h2.get_hat()) == (40000, 123, "Ninj", 50)
        assert h2.active_area() == 1 and h2._live() == [1] and not h2.bad_checksums()
    global _fetch_one
    real_fetch, tried = _fetch_one, []

    def fake_fetch(fid, var, name, timeout=8, save_stem=None):
        tried.append(name)
        if name != "Sprocket":
            raise RuntimeError("no picture found on the wiki page")
        return "/tmp/%d_%d.png" % (fid, var)
    _fetch_one = fake_fetch
    _ONLINE[:] = [time.time(), True]                                 # pretend to be online for this mock test
    try:
        assert fetch_image(111, 0x1013, "Sprocket", extra=("Pearl Sprocket",)) == "/tmp/111_4115.png"
        assert tried == ["Pearl Sprocket", "Sprocket"]               # specific name first, then the base
        tried.clear()
        try:
            fetch_image(5, 0, "Nobody (S2)")
            raise AssertionError("should have failed")
        except RuntimeError:
            pass
        assert tried == ["Nobody (S2)", "Nobody"]
    finally:
        _fetch_one = real_fetch
        _ONLINE[:] = [0.0, False]
    ents = FigureDB().entries()
    assert len(ents) == 49 and ents[0]["series"] == "Spyro's Adventure" and ents[-1]["series"] == "Giants"
    assert {(e["id"], e["var"]) for e in ents if e["name"] in ("Ninjini", "Thumpback", "Chill")} == \
        {(109, 4614), (107, 4614), (106, 4096)}                     # matches the dumps you tested with
    assert len(filter_entries(ents, game="Giants")) == 16 and len(filter_entries(ents, element="Tech")) == 6
    assert [e["name"] for e in filter_entries(ents, text="gill")] == ["Gill Grunt"]
    assert filter_entries(ents, game="Trap Team") == [] and len(filter_entries(ents)) == 49
    big = FigureDB.from_json(sample).entries()
    assert [figure_kind(n) for n in ("Item - Anvil Rain", "Trap - Water Axe", "Whirlwind", "Vehicle - Sky Slicer")] == \
        ["Item", "Trap", "Character", "Vehicle"] and len(big) == 4
    csv_text = entries_to_csv(filter_entries(ents, text="whirl"))
    assert csv_text.splitlines()[0].startswith("Name,Game,Type") and csv_text.splitlines()[1].startswith(
        "Whirlwind,Spyro's Adventure,Character,Air,0,0,0x0000")
    cf = make_figure(True)
    cf.apply(40000, 321, 7, "Keep", 9, 0x0FFD)
    cf.fix_all()
    cf.set_identity(109, 4614)                                      # Gill Grunt -> Ninjini (Giant)
    assert cf.dirty and (cf.figure_id(), cf.variant_id()) == (109, 4614)
    assert cf.report()[(0, 0)][0] == cf.report()[(0, 0)][1]         # block-1 checksum updated
    with tempfile.TemporaryDirectory() as td:
        pc = os.path.join(td, "changed.dump")
        cf.save(pc)
        c2 = FigureDump.load(pc)
        assert (c2.figure_id(), c2.variant_id()) == (109, 4614)
        assert c2.encrypted and c2.valid_found == 6 and not c2.bad_checksums(0) and not c2.bad_checksums(1)
        assert (c2.get_xp(), c2.get_gold(), c2.get_hero_points(), c2.get_name(), c2.get_hat()) == \
            (40000, 321, 7, "Keep", 9)                              # save data survives the re-encryption
        c2.apply(0, 0, 0, "", 0, 0)                                 # what "Reset stats" followed by Save does
        c2.fix_all()
        assert (c2.get_xp(), c2.get_gold(), c2.get_hero_points(), c2.get_name(), c2.get_hat(), c2.get_skills()) \
            == (0, 0, 0, "", 0, 0) and (c2.figure_id(), c2.variant_id()) == (109, 4614)
        assert not c2.bad_checksums(0) and not c2.bad_checksums(1)
    with tempfile.TemporaryDirectory() as td:
        global FIG_CACHE
        old_cache, FIG_CACHE = FIG_CACHE, os.path.join(td, "none.json")
        try:
            off = load_figure_db()                                   # no cache, no internet: built-in list only
            assert not off.full and off.size > 250
            assert off.lookup(106, 4096)["name"] == "Chill" and off.lookup(106, 4096)["exact"]
            assert off.lookup(109, 4614)["name"] == "Ninjini (Giant)" and off.lookup(111, 0x1013)["exact"] is False
            assert off.lookup(111, 0x1013)["base"] == "Sprocket"
            assert off.lookup(105, 4096)["name"] == "Hot Dog"        # Hot Dog sits under its real ID
            assert len(filter_entries(off.entries(), game="Trap Team", kind="Trap")) > 60
            assert len(filter_entries(off.entries(), game="Giants", kind="Character")) > 60
            assert all(e["kind"] == "Item" for e in filter_entries(off.entries(), kind="Item"))
            open(FIG_CACHE, "w").write(json.dumps([
                {"Id": 14, "Variant": 0, "Name": "Gill Grunt (cached)", "Series": "Spyros Adventure", "Element": "Water"}]
                + [{"Id": 900 + i, "Variant": 0, "Name": "X%d" % i, "Series": "Giants", "Element": "Air"}
                   for i in range(60)]))
            on = load_figure_db()                                    # cache layered over the built-in list
            assert on.full and on.lookup(14, 0)["name"] == "Gill Grunt (cached)" and on.lookup(106, 4096)["exact"]
            assert on.size == off.size + 60
        finally:
            FIG_CACHE = old_cache
    assert len(builtin_entries()) == len(BUILTIN_FIGURES.strip().splitlines()) and \
        len({(e["Id"], e["Variant"]) for e in builtin_entries()}) == len(builtin_entries())   # no duplicate keys
    with tempfile.TemporaryDirectory() as td:
        old, IMG_DIR = IMG_DIR, td
        try:
            fake_calls = []

            def fake(fid, var, name, save_stem=None):
                fake_calls.append(name)
                if name == "Gill Grunt":
                    raise RuntimeError("no picture")
                open(os.path.join(IMG_DIR, (save_stem or "%d_%d" % (fid, var)) + ".png"), "wb").write(b"x")
            items = filter_entries(off.entries(), text="Bash") + filter_entries(off.entries(), text="Gill")
            assert len(items) > 6                                    # many variants ...
            groups = picture_groups(items)
            assert [g[1] for g in groups] == ["Bash", "Gill Grunt"]  # ... but one download job per character
            st = {}
            prefetch_pictures(items, st, fetch=fake, delay=0)
            assert st["total"] == 2 and st["ok"] == 1 and st["fail"] == 1 and st["finished"] and st["done"] == 2
            assert find_image(4, 6145, "Bash (S2)").endswith("Bash.png")      # every Bash variant now has a picture
            assert find_image(4, 0, "Bash (Legendary)").endswith("Bash.png")
            fake_calls.clear()
            st2 = {}
            prefetch_pictures(items, st2, fetch=fake, delay=0)       # saved characters are skipped
            assert st2["total"] == 1 and fake_calls == ["Gill Grunt"]
            assert _page_name("Item - Anvil Rain") == "Anvil Rain" and _page_name("Gill Grunt (S2)") == "Gill Grunt"
            st3 = {"cancel": True}
            prefetch_pictures(filter_entries(off.entries(), text="Spyro"), st3, fetch=fake, delay=0)
            assert st3["done"] == 0 and st3["finished"]
        finally:
            IMG_DIR = old
    _ONLINE[:] = [time.time(), False]                                # simulate offline: fail fast, no hanging
    try:
        fetch_image(14, 0, "Gill Grunt")
        raise AssertionError("fetch_image must fail when offline")
    except RuntimeError as e:
        assert "offline" in str(e)
    st4 = {}
    prefetch_pictures([dict(id=14, var=999, name="Nobody", series="", kind="Character", element="")], st4)
    assert st4["error"] == "offline" and st4["finished"]             # offline: stops immediately
    _ONLINE[:] = [0.0, False]
    print("ok: figure lookup (id + variant -> name), fallback list, picture lookup, wiki image finder")
    print("All self-tests passed.")


def main(argv):
    if "--selftest" in argv:
        return selftest()
    if "--convert" in argv:
        i = argv.index("--convert")
        if len(argv) < i + 3:
            sys.exit("usage: skylander_editor.py --convert SRC DST   (DST ends in .bin, .sky, .dmp or .nfc)")
        src, dst = argv[i + 1], argv[i + 2]
        if os.path.splitext(dst)[1].lower() not in FORMAT_EXTS:
            sys.exit("The target must end in one of: " + ", ".join(FORMAT_EXTS))
        if os.path.abspath(src) == os.path.abspath(dst):
            sys.exit("Source and target are the same file.")
        _d = FigureDump.load(src)
        _from = "Flipper .nfc" if _d.fmt == "nfc" else "raw dump"
        _d.save(dst)
        print("Converted %s (%s) -> %s (%s)" % (src, _from, dst, "Flipper .nfc" if _d.fmt == "nfc" else "raw dump"))
        return
    if "--info" in argv:
        i = argv.index("--info")
        _d = FigureDump.load(argv[i + 1])
        _f = load_figure_db().lookup(_d.figure_id(), _d.variant_id())
        print("Character     : %s%s%s" % (_f["name"], "  (%s)" % _f["element"] if _f["element"] else "",
                                        "  - " + _f["note"] if _f["note"] else ""))
        print(_d.describe())
        return
    files = [a for a in argv[1:] if not a.startswith("-")]
    run_gui(files[0] if files else None)


if __name__ == "__main__":
    main(sys.argv)
