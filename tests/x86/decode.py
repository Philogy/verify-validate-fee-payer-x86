#!/usr/bin/env python3
"""Writes the decoder comparison file: candidate encodings and how
llvm-objdump decodes each.

    decode.py > decode.txt     # needs $AS (GNU as) and $OBJDUMP (llvm-objdump)

Candidates: every behaviour vector's bytes; those bytes with prefixes, REX
bytes and ModRM/SIB bytes changed; and every one-byte, `0f xx` and
`0f 38 xx` opcode with random operand bytes. Each candidate fills a 15-byte
window behind its own symbol, and llvm-objdump starts decoding afresh at
each symbol, so the first line of a window is that candidate alone.

Line format: `address | 15 bytes | length | text`; length 0 when llvm-objdump
finds no instruction.
"""
import os
import random
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
WINDOW = 15
BASE = 0x40000000
PREFIXES = [0x66, 0xF2, 0xF3, 0xF0, 0x67, 0x2E, 0x36, 0x3E, 0x26, 0x64, 0x65]


def vector_encodings():
    for f in sorted((HERE / "vectors").glob("*.txt")):
        for line in f.read_text().splitlines():
            if line and not line.startswith("#"):
                yield bytes.fromhex(line.split("|")[1].strip())


def split_prefixes(b):
    i = 0
    while i < len(b) and b[i] in PREFIXES:
        i += 1
    rex = i < len(b) and b[i] >> 4 == 4
    return b[:i], (b[i:i + 1] if rex else b""), b[i + (1 if rex else 0):]


def mutations(rng, b):
    legacy, rex, rest = split_prefixes(b)
    yield bytes([rng.choice(PREFIXES)]) + b
    yield legacy + bytes([0x40 | rng.randrange(16)]) + rest  # set or replace REX
    yield legacy + rest  # drop REX
    if rex:
        yield rex + legacy + rest  # REX before the legacy prefixes
        yield legacy + rex + rex + rest
    if len(rest) >= 2:
        opcode_len = 3 if rest[:2] == b"\x0f\x38" else 2 if rest[0] == 0x0F else 1
        if len(rest) > opcode_len:
            m = bytearray(rest)
            m[opcode_len] = rng.randrange(256)  # ModRM
            yield legacy + rex + bytes(m)
            if len(rest) > opcode_len + 1:
                m[opcode_len + 1] = rng.randrange(256)  # SIB or displacement
                yield legacy + rex + bytes(m)


def opcode_sweep(rng):
    for prefix in (b"", b"\x66", b"\xf2", b"\xf3", b"\x48", b"\x66\x48", b"\xf2\x48"):
        for m in (b"", b"\x0f", b"\x0f\x38"):
            for op in range(256):
                for _ in range(3):
                    yield prefix + m + bytes([op]) + rng.randbytes(WINDOW)


SIZES = {"byte": 8, "word": 16, "dword": 32, "qword": 64}
REGISTER_BITS = {**{r: 8 for r in "al cl dl bl ah ch dh bh spl bpl sil dil".split()},
                 **{r: 16 for r in "ax cx dx bx sp bp si di".split()},
                 **{r: 32 for r in "eax ecx edx ebx esp ebp esi edi".split()}}


def operand_bits(operand):
    m = re.match(r"(byte|word|dword|qword) ptr", operand)
    if m:
        return SIZES[m.group(1)]
    m = re.match(r"r\d+([bwd]?)$", operand)
    if m:
        return {"b": 8, "w": 16, "d": 32, "": 64}[m.group(1)]
    return REGISTER_BITS.get(operand, 64)


def normalise(text):
    """llvm-objdump's text in Print.lean's notation. Each rule is a choice of
    notation, not of meaning: the Lean `Address` does not record whether a SIB
    byte encoded "no index" (llvm: `riz`) or a scale of 1, and llvm-objdump
    versions differ in whether narrow immediates are printed signed."""
    text = re.sub(r" \+ (\d\*)?riz", "", text)
    text = text.replace("[1*", "[").replace("[rip]", "[rip + 0x0]")
    mnemonic, _, operands = text.partition(" ")
    ops = operands.split(", ") if operands else []
    if mnemonic in ("shl", "shr", "sar") and len(ops) == 1:
        ops.append("1")
    if len(ops) >= 2 and ops[-1].startswith("-0x"):
        if mnemonic == "movabs":
            ops[-1] = hex(int(ops[-1], 16) & ((1 << 64) - 1))
        elif mnemonic != "push" and operand_bits(ops[0]) < 64:
            ops[-1] = hex(int(ops[-1], 16) & ((1 << operand_bits(ops[0])) - 1))
    return mnemonic + (" " + ", ".join(ops) if ops else "")


def window(rng, b):
    b = b[:WINDOW]
    return b + rng.randbytes(WINDOW - len(b))


def disassemble(windows):
    assembler = os.environ.get("AS", "as")
    objdump = os.environ.get("OBJDUMP", "llvm-objdump")
    with tempfile.TemporaryDirectory() as tmp:
        s, o = Path(tmp) / "d.s", Path(tmp) / "d.o"
        lines = [".text"]
        for i, w in enumerate(windows):
            lines.append(f".type w{i}, @function\nw{i}:\n.byte " + ",".join(str(x) for x in w))
        s.write_text("\n".join(lines) + "\n")
        subprocess.run([assembler, "-o", str(o), str(s)], check=True)
        out = subprocess.run([objdump, "-d", "-M", "intel", f"--adjust-vma={BASE:#x}", str(o)],
                             check=True, capture_output=True, text=True).stdout
    first = {}
    current = None
    for line in out.splitlines():
        m = re.match(r"^([0-9a-f]+) <w(\d+)>:", line)
        if m:
            current = int(m.group(2))
            continue
        m = re.match(r"^ *([0-9a-f]+):((?: [0-9a-f]{2})+)\s*(.*)$", line)
        if m and current is not None and current not in first:
            first[current] = (int(m.group(1), 16), len(m.group(2).split()), m.group(3))
    return first


def main():
    rng = random.Random(20261009)
    candidates = []
    for b in vector_encodings():
        candidates.append(b)
        candidates.extend(mutations(rng, b))
    candidates.extend(opcode_sweep(rng))
    seen = set()
    windows = []
    for c in candidates:
        w = window(rng, c)
        if w not in seen:
            seen.add(w)
            windows.append(w)
    first = disassemble(windows)
    for i, w in enumerate(windows):
        address = BASE + WINDOW * i
        got_address, length, text = first.get(i, (None, 0, ""))
        if got_address is not None and got_address != address:
            sys.exit(f"window {i}: objdump started at {got_address:#x}, expected {address:#x}")
        text = re.sub(r"\s*#.*$", "", text)
        text = re.sub(r"\s*<[^>]*>", "", text)
        text = " ".join(text.split())
        if not text or "unknown" in text or "(bad)" in text:
            length, text = 0, "invalid"
        else:
            text = normalise(text)
        print(f"{address:#x} | {w.hex()} | {length} | {text}")


if __name__ == "__main__":
    main()
