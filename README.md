# Skylanders Figure Editor

A zero-dependency Python tool with a built-in graphical interface (GUI) and command-line interface (CLI) to view and edit Skylanders toy figure dumps (`.bin`, `.sky`, `.dmp`, and Flipper Zero `.nfc` files).

## Features

- **Stats Editor**: Modify XP, Gold, Hero Points, Nickname, Hat ID, and Skill bits.
- **Multi-Format Support**: Open and save raw 1KB dumps (`.bin`, `.sky`, `.dmp`) or Flipper Zero MIFARE Classic 1K (`.nfc`) files[cite: 1].
- **Automatic Checksum Correction**: Automatically recalculates and fixes CRC16 checksums (types 1, 2, 3, and 4) across both data areas upon saving[cite: 1].
- **Character Database & Offline Art**: Built-in reference list for figures and optional offline/online wiki image downloading to display character portraits[cite: 1].
- **Zero Dependencies**: Pure-Python AES-128 implementation included as a fallback (uses `pycryptodome` if available)[cite: 1].

## Requirements

- Python 3.x
- `tkinter` (Standard on most Python installations; on Linux/Ubuntu/Mint: `sudo apt install python3-tk`)[cite: 1]
- Optional: `Pillow` for non-PNG image handling[cite: 1], `tkinterdnd2` for drag-and-drop support[cite: 1].

## Usage

Run the GUI by launching the script without arguments:
```bash
python3 skylander_editor.py