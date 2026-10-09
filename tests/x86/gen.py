#!/usr/bin/env python3
"""Writes the behaviour test vectors, tests/x86/vectors/<group>.txt.

A vector is one line, `asm | bytes | field=value ...`: the instruction as
llvm-objdump prints it, its bytes, and the fields of the start state that
differ from layout.h. The bytes come from GNU as (`$AS`, default `as`), except
for encodings as does not choose, which are built from an assembled sibling.
Seeded, so a rerun writes the same files; CI checks that.
"""
import os
import random
import subprocess
import sys
import tempfile
from pathlib import Path

from undefined_flags import undefined

HERE = Path(__file__).resolve().parent
CODE_PAGE, DATA_PAGE, READ_ONLY_PAGE, STACK_PAGE = 0x40000000, 0x50000000, 0x50001000, 0x60000000
UNMAPPED = 0x50002000
DEFAULT_AT = 0x800

R64 = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi"] + [f"r{i}" for i in range(8, 16)]
R32 = ["eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi"] + [f"r{i}d" for i in range(8, 16)]
R16 = ["ax", "cx", "dx", "bx", "sp", "bp", "si", "di"] + [f"r{i}w" for i in range(8, 16)]
R8 = ["al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil"] + [f"r{i}b" for i in range(8, 16)]
HIGH = ["ah", "ch", "dh", "bh"]
NAMES = {8: R8, 16: R16, 32: R32, 64: R64}
PTR = {8: "byte", 16: "word", 32: "dword", 64: "qword", 128: "xmmword"}
CONDITIONS = ["o", "no", "b", "ae", "e", "ne", "be", "a", "s", "ns", "p", "np", "l", "ge", "le", "g"]
WIDTHS = [8, 16, 32, 64]


def mask(w):
    return (1 << w) - 1


def signed(v, w):
    v &= mask(w)
    return v - (1 << w) if v >> (w - 1) else v


def hexn(v):
    return f"0x{v:x}"


def signed_hex(v):
    return f"-0x{-v:x}" if v < 0 else f"0x{v:x}"


def imm(w, v):
    """An immediate of a w-bit operation, as llvm-objdump prints it."""
    return signed_hex(signed(v, 64)) if w == 64 else hexn(v & mask(w))


def le(v, n):
    return (v & mask(8 * n)).to_bytes(n, "little").hex()


class Vector:
    def __init__(self, asm, fields, source=None, patch=None, undef="", raw=None, rip_target=None):
        self.asm = asm  # what the decoder must print; may contain {rip}
        self.source = source or asm  # what GNU as assembles
        self.patch = patch  # bytes -> bytes, for encodings as does not choose
        self.raw = raw  # literal bytes (hex), when there is nothing to assemble
        self.fields = fields  # [(key, value)]
        self.undef = undef
        self.rip_target = rip_target
        self.bytes = None

    def at(self):
        return int(dict(self.fields).get("at", hexn(DEFAULT_AT)), 16)

    def rip_text(self, length):
        if self.rip_target is None:
            return ""
        d = signed(self.rip_target - (CODE_PAGE + self.at() + length), 64)
        return f" - 0x{-d:x}" if d < 0 else f" + 0x{d:x}"

    def line(self):
        asm = self.asm.replace("{rip}", self.rip_text(len(self.bytes) // 2))
        # as needs `1*` to encode an index without a base; llvm-objdump omits it.
        asm = asm.replace("[1*", "[")
        fields = list(self.fields) + ([("undef", self.undef)] if self.undef else [])
        return f"{asm} | {self.bytes} | " + " ".join(f"{k}={v}" for k, v in fields)


def assemble(sources):
    """Bytes (hex) of each instruction, assembled at once."""
    assembler = os.environ.get("AS", "as")
    with tempfile.TemporaryDirectory() as tmp:
        s, o = Path(tmp) / "v.s", Path(tmp) / "v.o"
        body = "".join(f"v{i}: {src}\n" for i, src in enumerate(sources))
        s.write_text(".intel_syntax noprefix\n.text\n" + body + "vend:\n")
        subprocess.run([assembler, "-o", str(o), str(s)], check=True)
        # Our own minimal ELF reader would be more code than nm + objcopy.
        prefix = assembler[: -len("as")] if assembler.endswith("as") else ""
        nm = subprocess.run([prefix + "nm", str(o)], check=True, capture_output=True, text=True).stdout
        addr = {}
        for line in nm.splitlines():
            value, _, name = line.split()
            addr[name] = int(value, 16)
        b = Path(tmp) / "v.bin"
        subprocess.run([prefix + "objcopy", "-O", "binary", "--only-section=.text", str(o), str(b)], check=True)
        text = b.read_bytes()
    names = [f"v{i}" for i in range(len(sources))] + ["vend"]
    return [text[addr[names[i]]:addr[names[i + 1]]].hex() for i in range(len(sources))]


def finish(vectors):
    """Fill in every vector's bytes. Rip-relative displacements depend on the
    instruction's length, so those are assembled twice."""
    def sources(vs, lengths):
        return [v.source.replace("{rip}", v.rip_text(lengths.get(id(v), 0))) for v in vs]

    todo = [v for v in vectors if v.raw is None]
    first = assemble(sources(todo, {}))
    lengths = {id(v): len(b) // 2 for v, b in zip(todo, first)}
    final = assemble(sources(todo, lengths))
    for v, b in zip(todo, final):
        if len(b) // 2 != lengths[id(v)]:
            sys.exit(f"length changed on reassembly: {v.source}")
        v.bytes = v.patch(bytes.fromhex(b)).hex() if v.patch else b
    for v in vectors:
        if v.raw is not None:
            v.bytes = v.raw


def with_rex_w(b):
    """Set REX.W, adding a REX byte after the legacy prefixes if there is none."""
    i = 0
    while b[i] in (0x66, 0xF2, 0xF3):
        i += 1
    if b[i] >> 4 == 4:
        return b[:i] + bytes([b[i] | 8]) + b[i + 1:]
    return b[:i] + b"\x48" + b[i:]


class Gen:
    def __init__(self, seed):
        self.rng = random.Random(seed)
        self.groups = {}

    def add(self, group, v):
        self.groups.setdefault(group, []).append(v)

    # Values

    def edge(self, w):
        top = 1 << (w - 1)
        return [0, 1, 2, mask(w), mask(w) - 1, top, top - 1, top + 1, 0x7F & mask(w), 0x80 & mask(w)]

    def value(self, w):
        r = self.rng.random()
        if r < 0.4:
            return self.rng.choice(self.edge(w))
        if r < 0.6:
            return self.rng.randrange(0, 256)
        return self.rng.getrandbits(w)

    def flags(self):
        return "".join(c for c in "CPAZSO" if self.rng.random() < 0.5) or "-"

    def with_low(self, w, v, high=False):
        """A random 64-bit register value whose low `w` bits (or bits 8-15) are `v`."""
        full = self.rng.getrandbits(64)
        if high:
            return (full & ~0xFF00) | ((v & 0xFF) << 8)
        return (full & ~mask(w)) | (v & mask(w))

    # Operands

    def pick(self, used, legacy=False, no_rsp=False):
        """An unused register index; `legacy`: no REX needed (for ah..bh)."""
        choices = [i for i in range(8 if legacy else 16) if i not in used and not (no_rsp and i == 4)]
        i = self.rng.choice(choices)
        used.add(i)
        return i

    def register(self, w, used, legacy=False, high_ok=False):
        """(name, index, is_high) of a w-bit register."""
        if w == 8 and high_ok and self.rng.random() < 0.3:
            free = [i for i in range(4) if i not in used]
            if free:
                i = self.rng.choice(free)
                used.add(i)
                return HIGH[i], i, True
        if w == 8 and legacy:
            i = self.pick(used, legacy=True)
            while i >= 4:  # spl..dil need a REX byte
                used.discard(i)
                used.add(100 + i)
                i = self.pick(used, legacy=True)
            return R8[i], i, False
        i = self.pick(used, legacy)
        return NAMES[w][i], i, False

    def address(self, used, target, shape=None, legacy=False):
        """An address operand (text inside `[...]`, fields) for `target`.
        Fields set the registers it uses; rip-relative text contains {rip}."""
        shape = shape or self.rng.choice(["b", "b", "b+i", "b+i", "i", "rip", "abs"])
        fields = []
        if shape == "rip":
            return "[rip{rip}]", fields, target
        if shape == "abs":
            return f"[{hexn(target)}]", fields, None
        disp = self.rng.choice([0, 0, self.rng.randrange(-128, 128), self.rng.randrange(-(1 << 31), 1 << 31)])
        scale = self.rng.choice([1, 2, 4, 8])
        if shape == "i":
            idx = self.pick(used, legacy, no_rsp=True)
            iv = (target - self.rng.randrange(-(1 << 20), 1 << 20)) // scale
            disp = target - iv * scale
            fields.append((R64[idx], hexn(iv)))
            return f"[{scale}*{R64[idx]}{self.disp(disp)}]", fields, None
        base = self.pick(used, legacy)
        terms = R64[base]
        offset = disp
        if shape == "b+i":
            idx = self.pick(used, legacy, no_rsp=True)
            iv = self.rng.choice([self.rng.randrange(0, 64), self.rng.getrandbits(64)])
            offset += iv * scale
            fields.append((R64[idx], hexn(iv)))
            terms += " + " + (R64[idx] if scale == 1 else f"{scale}*{R64[idx]}")
        fields.append((R64[base], hexn((target - offset) & mask(64))))
        return f"[{terms}{self.disp(disp)}]", fields, None

    @staticmethod
    def disp(d):
        return "" if d == 0 else (f" - 0x{-d:x}" if d < 0 else f" + 0x{d:x}")

    def memory(self, w, used, target=None, align=1, shape=None, legacy=False):
        """A w-bit memory operand at `target` (default: random in the data page).
        Returns (text, fields, target, rip_target)."""
        if target is None:
            target = DATA_PAGE + self.rng.randrange(0, 4096 - 16) // align * align
        a, fields, rip = self.address(used, target, shape, legacy)
        return f"{PTR[w]} ptr {a}", fields, target, rip


# Groups. Each method adds the vectors of one family of instruction forms.

ARITHMETIC = ["add", "or", "adc", "sbb", "and", "sub", "xor", "cmp", "test"]


def arithmetic(g):
    for op in ARITHMETIC:
        for w in WIDTHS:
            shapes = ["r,r", "r,r", "m,r", "r,imm", "r,imm", "m,imm", "acc,imm"]
            if op != "test":
                shapes += ["r,m", "r,r-load"]
            for shape in shapes:
                for _ in range(4):
                    one(g, "arithmetic", op, w, shape)
            # Same register on both sides: `xor eax, eax`, `sub rax, rax`.
            used = set()
            name, i, high = g.register(w, used, high_ok=True)
            v = g.value(w)
            g.add("arithmetic", Vector(f"{op} {name}, {name}", [(R64[i], hexn(g.with_low(w, v, high))),
                                                                 ("flags", g.flags())], undef=undefined(op)))


def one(g, group, op, w, shape):
    used = set()
    a, b = g.value(w), g.value(w)
    fields = [("flags", g.flags())]
    rip = None
    legacy = w == 8 and g.rng.random() < 0.4
    load = shape == "r,r-load"
    if shape in ("r,r", "r,r-load"):
        d, di, dh = g.register(w, used, legacy, high_ok=legacy)
        s, si, sh = g.register(w, used, legacy, high_ok=legacy)
        fields += [(R64[di], hexn(g.with_low(w, a, dh))), (R64[si], hexn(g.with_low(w, b, sh)))]
        text = f"{op} {d}, {s}"
    elif shape == "r,m":
        d, di, dh = g.register(w, used, legacy, high_ok=legacy)
        m, f, target, rip = g.memory(w, used, legacy=legacy)
        fields += [(R64[di], hexn(g.with_low(w, a, dh)))] + f + [("mem", f"{hexn(target)}:{le(b, w // 8)}")]
        text = f"{op} {d}, {m}"
    elif shape == "m,r":
        s, si, sh = g.register(w, used, legacy, high_ok=legacy)
        m, f, target, rip = g.memory(w, used, legacy=legacy)
        fields += [(R64[si], hexn(g.with_low(w, b, sh)))] + f + [("mem", f"{hexn(target)}:{le(a, w // 8)}")]
        text = f"{op} {m}, {s}"
    elif shape in ("r,imm", "acc,imm"):
        if shape == "acc,imm":
            d, di, dh = NAMES[w][0], 0, False
        else:
            d, di, dh = g.register(w, used, high_ok=True)
        b = g.immediate(w)
        fields += [(R64[di], hexn(g.with_low(w, a, dh)))]
        text = f"{op} {d}, {imm(w, b)}"
    else:  # m,imm
        m, f, target, rip = g.memory(w, used)
        b = g.immediate(w)
        fields += f + [("mem", f"{hexn(target)}:{le(a, w // 8)}")]
        text = f"{op} {m}, {imm(w, b)}"
    g.add(group, Vector(text, fields, source=("{load} " + text) if load else None,
                        undef=undefined(op), rip_target=rip))


def immediate(self, w):
    """An immediate for a w-bit operation, sign-extended to 64 bits as the
    encoding stores it (imm8 or imm32 for 64-bit operations)."""
    if w == 64:
        v = self.rng.choice([self.rng.randrange(-128, 128), self.rng.randrange(-(1 << 31), 1 << 31),
                             -1, 0, 1, 0x7FFFFFFF, -(1 << 31)])
        return v & mask(64)
    return self.rng.choice([self.rng.randrange(0, 128), self.value(w)])


Gen.immediate = immediate


def moves(g):
    for w in WIDTHS:
        for shape in ["r,r", "r,r-load", "r,m", "m,r", "r,imm", "m,imm"]:
            for _ in range(5):
                one(g, "move", "mov", w, shape)
    for _ in range(8):
        used = set()
        _, i, _ = g.register(64, used)
        v = g.rng.choice([g.rng.getrandbits(64), 1 << 63, mask(64), 0x100000000])
        g.add("move", Vector(f"movabs {R64[i]}, {hexn(v)}", [(R64[i], hexn(g.rng.getrandbits(64)))]))
    # movzx / movsx / movsxd
    for op in ["movzx", "movsx"]:
        for w, sw in [(16, 8), (32, 8), (64, 8), (32, 16), (64, 16)]:
            for src in ["r", "m"] * 4:
                extend(g, op, w, sw, src)
    for src in ["r", "m"] * 5:
        extend(g, "movsxd", 64, 32, src)
    # lea: any address, nothing read
    for w in [16, 32, 64]:
        for shape in ["b", "b+i", "i", "rip", "abs"] * 3:
            used = set()
            _, i, _ = g.register(w, used)
            target = g.rng.getrandbits(64) if shape in ("b", "b+i") else DATA_PAGE + g.rng.randrange(0, 4096)
            if shape == "abs":
                target = g.rng.randrange(0, 1 << 31)
            a, f, rip = g.address(used, target, shape)
            g.add("move", Vector(f"lea {NAMES[w][i]}, {a}", f + [(R64[i], hexn(g.rng.getrandbits(64)))],
                                 rip_target=rip))


def extend(g, op, w, sw, src):
    used = set()
    legacy = sw == 8 and g.rng.random() < 0.4
    d, di, _ = g.register(w, used, legacy)
    v = g.value(sw)
    fields = [(R64[di], hexn(g.rng.getrandbits(64)))]
    rip = None
    if src == "r":
        s, si, sh = g.register(sw, used, legacy, high_ok=legacy)
        fields.append((R64[si], hexn(g.with_low(sw, v, sh))))
    else:
        s, f, target, rip = g.memory(sw, used, legacy=legacy)
        fields += f + [("mem", f"{hexn(target)}:{le(v, sw // 8)}")]
    g.add("move", Vector(f"{op} {d}, {s}", fields, rip_target=rip))


def unary(g):
    for op in ["inc", "dec", "neg", "not"]:
        for w in WIDTHS:
            for dest in ["r", "r", "m"] * 3:
                used = set()
                v = g.value(w)
                fields = [("flags", g.flags())]
                rip = None
                if dest == "r":
                    d, di, dh = g.register(w, used, high_ok=True)
                    fields.append((R64[di], hexn(g.with_low(w, v, dh))))
                else:
                    d, f, target, rip = g.memory(w, used)
                    fields += f + [("mem", f"{hexn(target)}:{le(v, w // 8)}")]
                g.add("unary", Vector(f"{op} {d}", fields, rip_target=rip))


def multiply(g):
    for w in [16, 32, 64]:
        for shape in ["r,r", "r,m", "r,r,imm8", "r,m,imm8", "r,r,imm", "r,m,imm"] * 4:
            used = set()
            d, di, _ = g.register(w, used)
            a, b = g.value(w), g.value(w)
            fields = [(R64[di], hexn(g.with_low(w, a))), ("flags", g.flags())]
            rip = None
            if shape.startswith("r,r"):
                s, si, _ = g.register(w, used)
                fields.append((R64[si], hexn(g.with_low(w, b))))
            else:
                s, f, target, rip = g.memory(w, used)
                fields += f + [("mem", f"{hexn(target)}:{le(b, w // 8)}")]
            text = f"imul {d}, {s}"
            if shape.endswith("imm8"):
                text += ", " + imm(w, g.rng.randrange(-128, 128) & mask(64))
            elif shape.endswith("imm"):
                k = g.rng.choice([g.rng.randrange(-(1 << 31), 1 << 31), 0x7FFF, 0x10000, -0x8000])
                if w == 16:
                    k = g.rng.randrange(-0x8000, 0x8000)
                if -128 <= k < 128:
                    k += 0x1000
                text += ", " + imm(w, k & mask(64))
            g.add("multiply", Vector(text, fields, undef=undefined("imul"), rip_target=rip))


def shifts(g):
    for op in ["shl", "shr", "sar"]:
        for w in WIDTHS:
            for count in sorted({0, 1, 2, 3, 7, w - 1, w, w + 1, 31, 32, 33, 63, 64, 65, 255}):
                for form in ["imm", "cl", "one"]:
                    if form == "one" and count != 1:
                        continue
                    for dest in ["r", "m"]:
                        shift_vector(g, op, w, count, form, dest)


def shift_vector(g, op, w, count, form, dest):
    masked = count & (63 if w == 64 else 31)
    if masked == 0 and w == 32 and dest == "r":
        return  # the model leaves this unsupported (see Machine.lean, `shift`)
    if form == "imm" and count > 255:
        return
    used = {1} if form == "cl" else set()
    v = g.value(w)
    fields = [("flags", g.flags())]
    rip = None
    if dest == "r":
        d, di, dh = g.register(w, used, high_ok=form != "cl" or True)
        if dh and form == "cl" and di == 1:
            return
        fields.append((R64[di], hexn(g.with_low(w, v, dh))))
    else:
        d, f, target, rip = g.memory(w, used)
        fields += f + [("mem", f"{hexn(target)}:{le(v, w // 8)}")]
    patch = None
    source = None
    if form == "cl":
        fields.append(("rcx", hexn(g.with_low(8, count))))
        text = f"{op} {d}, cl"
    elif form == "one":
        text = f"{op} {d}, 1"
    elif count == 1:
        # as encodes a count of 1 as the shorter `d1` form; build `c1 ... 01`.
        text = f"{op} {d}, 0x1"
        source = f"{op} {d}, 0x2"
        patch = lambda b: b[:-1] + b"\x01"
    else:
        text = f"{op} {d}, {hexn(count)}"
    if op == "sar" and masked >= w:
        fields.append(("known", "sar-carry"))
    g.add("shift", Vector(text, fields, source=source, patch=patch,
                          undef=undefined(op, w, masked), rip_target=rip))


def flags_for_conditions(g):
    """Flag settings that make each condition both true and false."""
    picks = ["-", "C", "Z", "CZ", "S", "O", "SO", "ZSO", "P", "CPAZSO", "ZS", "ZO"]
    return picks + [g.flags() for _ in range(4)]


def conditionals(g):
    for c in CONDITIONS:
        for fl in flags_for_conditions(g):
            used = set()
            d, di, dh = g.register(8, used, high_ok=True)
            g.add("conditional", Vector(f"set{c} {d}", [(R64[di], hexn(g.rng.getrandbits(64))), ("flags", fl)]))
        for _ in range(3):
            used = set()
            m, f, target, rip = g.memory(8, used)
            g.add("conditional", Vector(f"set{c} {m}", f + [("flags", g.flags())], rip_target=rip))
        for w in [16, 32, 64]:
            for fl in g.rng.sample(flags_for_conditions(g), 6):
                used = set()
                d, di, _ = g.register(w, used)
                fields = [(R64[di], hexn(g.rng.getrandbits(64))), ("flags", fl)]
                rip = None
                if g.rng.random() < 0.6:
                    s, si, _ = g.register(w, used)
                    fields.append((R64[si], hexn(g.rng.getrandbits(64))))
                else:
                    s, f, target, rip = g.memory(w, used)
                    fields += f
                g.add("conditional", Vector(f"cmov{c} {d}, {s}", fields, rip_target=rip))
        # The source is read even when the move does not happen.
        used = set()
        s, f, _, _ = g.memory(64, used, target=UNMAPPED + 8, shape="b")
        g.add("conditional", Vector(f"cmov{c} rax, {s}", f + [("flags", g.flags())]))


def canonical(g):
    """A random address the CPU can jump to: bits 47-63 all equal."""
    v = g.rng.getrandbits(47)
    return v | (0xFFFF8 << 44) if g.rng.random() < 0.3 else v


def branch_target(offset, length, at=DEFAULT_AT):
    return (CODE_PAGE + at + length + offset) & mask(64)


def branches(g):
    for code, c in enumerate(CONDITIONS):
        for fl in g.rng.sample(flags_for_conditions(g), 5):
            d8 = g.rng.randrange(-128, 128)
            g.add("branch", Vector(f"j{c} {hexn(branch_target(d8, 2))}", [("flags", fl)],
                                   raw=f"{0x70 + code:02x}{le(d8, 1)}"))
            d32 = g.rng.randrange(-(1 << 31), 1 << 31)
            g.add("branch", Vector(f"j{c} {hexn(branch_target(d32, 6))}", [("flags", fl)],
                                   raw=f"0f{0x80 + code:02x}{le(d32, 4)}"))
    for _ in range(4):
        d8, d32 = g.rng.randrange(-128, 128), g.rng.randrange(-(1 << 31), 1 << 31)
        g.add("branch", Vector(f"jmp {hexn(branch_target(d8, 2))}", [], raw=f"eb{le(d8, 1)}"))
        g.add("branch", Vector(f"jmp {hexn(branch_target(d32, 5))}", [], raw=f"e9{le(d32, 4)}"))
        g.add("branch", Vector(f"call {hexn(branch_target(d32, 5))}", [], raw=f"e8{le(d32, 4)}"))
    for op in ["jmp", "call"]:
        for _ in range(6):
            used = {4}
            target = canonical(g)
            if g.rng.random() < 0.5:
                _, i, _ = g.register(64, used)
                g.add("branch", Vector(f"{op} {R64[i]}", [(R64[i], hexn(target))]))
            else:
                m, f, at, rip = g.memory(64, used)
                g.add("branch", Vector(f"{op} {m}", f + [("mem", f"{hexn(at)}:{le(target, 8)}")], rip_target=rip))
    # Every addressing mode of the indirect forms, rip-relative included.
    for op in ["jmp", "call"]:
        for shape in ["b", "b+i", "i", "rip", "abs"]:
            used = {4}
            m, f, at, rip = g.memory(64, used, shape=shape)
            g.add("branch", Vector(f"{op} {m}", f + [("mem", f"{hexn(at)}:{le(canonical(g), 8)}")], rip_target=rip))
    for _ in range(4):
        sp = STACK_PAGE + g.rng.randrange(0, 4088)
        g.add("branch", Vector("ret", [("rsp", hexn(sp)), ("mem", f"{hexn(sp)}:{le(canonical(g), 8)}")]))


def stack(g):
    for i in range(16):
        g.add("stack", Vector(f"push {R64[i]}", [(R64[i], hexn(g.rng.getrandbits(64)))] if i != 4 else []))
        if i != 4:
            g.add("stack", Vector(f"pop {R64[i]}", [("mem", f"{hexn(STACK_PAGE + 0x800)}:{le(g.rng.getrandbits(64), 8)}")]))
    g.add("stack", Vector("pop rsp", [("mem", f"{hexn(STACK_PAGE + 0x800)}:{le(g.rng.getrandbits(64), 8)}")]))
    for v in [0, 5, -1, 0x7F, -0x80, 0x80, 0x12345678, -0x80000000]:
        g.add("stack", Vector(f"push {signed_hex(v)}", []))
    for _ in range(4):
        used = {4}
        m, f, at, rip = g.memory(64, used)
        g.add("stack", Vector(f"push {m}", f, rip_target=rip))
        used = {4}
        m, f, at, rip = g.memory(64, used)
        g.add("stack", Vector(f"pop {m}", f, rip_target=rip))
    # Addressed through rsp: push reads before, pop writes after rsp moves.
    for off in [0, 8, 0x10]:
        g.add("stack", Vector(f"push qword ptr [rsp{Gen.disp(off)}]", []))
        g.add("stack", Vector(f"pop qword ptr [rsp{Gen.disp(off)}]", []))
    for op, w in [("cbw", 16), ("cwde", 32), ("cdqe", 64), ("cwd", 16), ("cdq", 32), ("cqo", 64)]:
        for v in [0, 0x7F, 0x80, 0x7FFF, 0x8000, 0x7FFFFFFF, 0x80000000, 1 << 63, mask(64)] + [
                g.rng.getrandbits(64) for _ in range(3)]:
            g.add("stack", Vector(op, [("rax", hexn(v)), ("rdx", hexn(g.rng.getrandbits(64)))]))
    g.add("stack", Vector("nop", [], raw="90"))
    g.add("stack", Vector("nop dword ptr [rax + rax]", []))
    g.add("stack", Vector("nop word ptr [rax + rax]", []))
    g.add("stack", Vector("nop eax", [], raw="0f1fc0"))
    # A nop's memory operand is not accessed.
    g.add("stack", Vector("nop dword ptr [rax]", [("rax", hexn(UNMAPPED))], raw="0f1f00"))
    g.add("stack", Vector("nop qword ptr [rax]", [("rax", hexn(UNMAPPED))], raw="480f1f00"))


# Floating point. Bit patterns of doubles.
F64_SPECIAL = [
    0x0000000000000000, 0x8000000000000000, 0x3FF0000000000000, 0xBFF0000000000000, 0x4000000000000000,
    0x3FE0000000000000, 0x4008000000000000, 0x3FF0000000000001, 0x0000000000000001, 0x800FFFFFFFFFFFFF,
    0x0010000000000000, 0x8010000000000000, 0x7FEFFFFFFFFFFFFF, 0xFFEFFFFFFFFFFFFF, 0x7FF0000000000000,
    0xFFF0000000000000, 0x7FF8000000000000, 0xFFF8000000000123, 0x7FF0000000000001, 0xFFF4000000000000,
    0x43E0000000000000, 0xC3E0000000000000, 0x43DFFFFFFFFFFFFF, 0x3CA0000000000000, 0x4330000000000000,
    0x45300000FFFFFFFF, 0x4530000000000000,
]


def f64_random(g):
    r = g.rng.random()
    if r < 0.3:
        return g.rng.choice(F64_SPECIAL)
    if r < 0.5:  # near the denormal range
        return (g.rng.getrandbits(1) << 63) | (g.rng.randrange(0, 40) << 52) | g.rng.getrandbits(52)
    if r < 0.6:  # near overflow
        return (g.rng.getrandbits(1) << 63) | (g.rng.randrange(2000, 2047) << 52) | g.rng.getrandbits(52)
    if r < 0.8:  # ordinary magnitudes
        return (g.rng.getrandbits(1) << 63) | (g.rng.randrange(1000, 1100) << 52) | g.rng.getrandbits(52)
    return g.rng.getrandbits(64)


def close_pair(g):
    """Operands whose sum or product needs careful rounding."""
    a = f64_random(g) & ~(0x7FF << 52) | (g.rng.randrange(1, 2046) << 52)
    e = (a >> 52) & 0x7FF
    b = (g.rng.getrandbits(1) << 63) | (max(1, min(2046, e + g.rng.randrange(-60, 3))) << 52)
    return a, b | g.rng.getrandbits(52)


def xmm_value(lo, hi):
    return f"0x{hi:016x}{lo:016x}"


def sse(g):
    used_fl = lambda: ("flags", g.flags())
    # 128-bit moves
    for op, aligned in [("movdqa", 1), ("movdqu", 0), ("movapd", 1), ("movupd", 0), ("movaps", 1), ("movups", 0)]:
        for _ in range(2):
            a, b = g.rng.randrange(16), g.rng.randrange(16)
            g.add("sse", Vector(f"{op} xmm{a}, xmm{b}", [(f"xmm{b}", xmm_value(g.rng.getrandbits(64), g.rng.getrandbits(64)))]))
        for store in [False, True]:
            for misaligned in [False, True]:
                used = set()
                align = 16
                target = DATA_PAGE + g.rng.randrange(0, 255) * 16 + (g.rng.randrange(1, 16) if misaligned else 0)
                m, f, _, rip = g.memory(128, used, target=target)
                x = g.rng.randrange(16)
                text = f"{op} {m}, xmm{x}" if store else f"{op} xmm{x}, {m}"
                g.add("sse", Vector(text, f, rip_target=rip))
    for op in ["movdqa", "movdqu", "movapd", "movupd", "movaps", "movups"]:
        for shape in ["b", "b+i", "i", "rip", "abs"]:
            used = set()
            m, f, _, rip = g.memory(128, used, target=DATA_PAGE + g.rng.randrange(0, 255) * 16, shape=shape)
            g.add("sse", Vector(f"{op} xmm{g.rng.randrange(16)}, {m}", f, rip_target=rip))
    # movd / movq between general registers and xmm
    for w, mn in [(32, "movd"), (64, "movq")]:
        for _ in range(3):
            used = set()
            _, i, _ = g.register(w, used)
            x = g.rng.randrange(16)
            g.add("sse", Vector(f"{mn} xmm{x}, {NAMES[w][i]}", [(R64[i], hexn(g.rng.getrandbits(64)))]))
            used = set()
            _, i, _ = g.register(w, used)
            g.add("sse", Vector(f"{mn} {NAMES[w][i]}, xmm{x}", []))
            for store in [False, True]:
                used = set()
                m, f, _, rip = g.memory(w, used)
                text = f"{mn} {m}, xmm{x}" if store else f"{mn} xmm{x}, {m}"
                src = text.replace("movq", "movd").replace("qword", "dword")
                g.add("sse", Vector(text, f, source=src if w == 64 else None,
                                    patch=with_rex_w if w == 64 else None, rip_target=rip))
    # movsd
    for _ in range(3):
        a, b = g.rng.randrange(16), g.rng.randrange(16)
        g.add("sse", Vector(f"movsd xmm{a}, xmm{b}", []))
        used = set()
        m, f, _, rip = g.memory(64, used)
        g.add("sse", Vector(f"movsd xmm{a}, {m}", f, rip_target=rip))
        used = set()
        m, f, _, rip = g.memory(64, used)
        g.add("sse", Vector(f"movsd {m}, xmm{a}", f, rip_target=rip))
    # bitwise, ptest, interleaves: register and aligned (and misaligned) memory sources
    ops = ["pand", "pandn", "por", "pxor", "andpd", "andnpd", "orpd", "xorpd", "andps", "andnps", "orps", "xorps",
           "ptest", "punpckldq", "punpcklqdq", "unpcklpd", "unpckhpd"]
    for op in ops:
        for src in ["xmm", "xmm", "xmm", "m", "m", "rip", "misaligned"]:
            d = g.rng.randrange(16)
            lo, hi = g.rng.getrandbits(64), g.rng.getrandbits(64)
            fields = [(f"xmm{d}", xmm_value(g.rng.getrandbits(64), g.rng.getrandbits(64))), used_fl()]
            rip = None
            if op == "ptest" and g.rng.random() < 0.5:
                # Make ZF or CF come out set.
                pick = g.rng.choice([(0, 0), (lo, hi), (~lo & mask(64), ~hi & mask(64))])
                fields[0] = (f"xmm{d}", xmm_value(*pick))
            if src == "xmm":
                s = g.rng.randrange(16)
                fields.append((f"xmm{s}", xmm_value(lo, hi)))
                text = f"{op} xmm{d}, xmm{s}"
            else:
                used = set()
                target = DATA_PAGE + g.rng.randrange(0, 255) * 16 + (8 if src == "misaligned" else 0)
                m, f, _, rip = g.memory(128, used, target=target, shape="rip" if src == "rip" else None)
                fields += f + [("mem", f"{hexn(target)}:{le(lo, 8)}{le(hi, 8)}")]
                text = f"{op} xmm{d}, {m}"
            g.add("sse", Vector(text, fields, rip_target=rip))


def floating(g):
    pairs = [(a, b) for a in F64_SPECIAL for b in F64_SPECIAL]
    for op in ["addsd", "subsd", "mulsd", "ucomisd"]:
        cases = pairs + [(f64_random(g), f64_random(g)) for _ in range(150)] + [close_pair(g) for _ in range(150)]
        for a, b in cases:
            float_vector(g, op, a, b, g.rng.getrandbits(64), g.rng.getrandbits(64))
    for op in ["addpd", "subpd", "mulpd"]:
        for _ in range(200):
            (a, b), (c, d) = g.rng.choice(pairs), (f64_random(g), f64_random(g))
            float_vector(g, op, a, b, c, d)
    for a in F64_SPECIAL + [f64_random(g) for _ in range(200)] + [
            0x43E0000000000000 + k for k in range(-3, 3)] + [0xC3E0000000000000 + k for k in range(-3, 3)]:
        float_vector(g, "cvttsd2si", a, None, 0, 0)
    # Sticky exception bits already set stay set; the control bits are the default.
    for op in ["addsd", "mulsd", "ucomisd", "cvttsd2si"]:
        float_vector(g, op, 0x3FF0000000000001, 0x3CA0000000000000, 0, 0, mxcsr=0x1FBF)


def float_vector(g, op, a, b, c, d, mxcsr=None):
    """`op` on lanes (a, c) of the destination and (b, d) of the source."""
    dx = g.rng.randrange(16)
    fields = [("flags", g.flags())]
    rip = None
    from_memory = g.rng.random() < 0.3
    if op == "cvttsd2si":
        used = set()
        _, ri, _ = g.register(64, used)
        if from_memory:
            m, f, target, rip = g.memory(64, used)
            fields += f + [("mem", f"{hexn(target)}:{le(a, 8)}")]
            text = f"cvttsd2si {R64[ri]}, {m}"
        else:
            fields.append((f"xmm{dx}", xmm_value(a, g.rng.getrandbits(64))))
            text = f"cvttsd2si {R64[ri]}, xmm{dx}"
    else:
        fields.append((f"xmm{dx}", xmm_value(a, c)))
        width = 128 if op.endswith("pd") else 64
        if from_memory:
            used = set()
            target = DATA_PAGE + g.rng.randrange(0, 255) * 16
            m, f, _, rip = g.memory(width, used, target=target)
            fields += f + [("mem", f"{hexn(target)}:{le(b, 8)}{le(d, 8) if width == 128 else ''}")]
            text = f"{op} xmm{dx}, {m}"
        else:
            sx = g.rng.choice([i for i in range(16) if i != dx])
            fields.append((f"xmm{sx}", xmm_value(b, d)))
            text = f"{op} xmm{dx}, xmm{sx}"
    if mxcsr is not None:
        fields.append(("mxcsr", hexn(mxcsr)))
    g.add("float", Vector(text, fields, rip_target=rip))


def faults(g):
    """Page faults, alignment faults and instruction fetch at a page end."""
    def add(text, fields, **kw):
        g.add("fault", Vector(text, fields, **kw))

    add("mov rax, qword ptr [rbx]", [("rbx", hexn(UNMAPPED))])
    add("mov rax, qword ptr [rbx]", [("rbx", hexn(READ_ONLY_PAGE + 0xFFC))])  # straddles into unmapped
    add("mov rax, qword ptr [rbx]", [("rbx", hexn(READ_ONLY_PAGE + 0xFF8))])  # last word of a mapping
    add("mov qword ptr [rbx], rax", [("rbx", hexn(READ_ONLY_PAGE))])  # read-only
    add("mov qword ptr [rbx], rax", [("rbx", hexn(DATA_PAGE + 0xFFC))])  # straddles into read-only
    add("mov dword ptr [rbx], eax", [("rbx", hexn(CODE_PAGE + 0x10))])  # code is not writable
    add("add qword ptr [rbx], rax", [("rbx", hexn(READ_ONLY_PAGE + 8))])  # read succeeds, write faults
    add("inc byte ptr [rbx]", [("rbx", hexn(READ_ONLY_PAGE + 8))])
    add("mov rax, qword ptr [rbx]", [("rbx", hexn(DATA_PAGE - 8))])  # below the first mapping
    add("mov rax, qword ptr [rbx + 8*rcx]", [("rbx", hexn(DATA_PAGE)), ("rcx", hexn((1 << 61) + 1))])  # wraps
    add("push rax", [("rsp", hexn(DATA_PAGE))])
    add("push rax", [("rsp", hexn(UNMAPPED + 8))])
    add("pop rax", [("rsp", hexn(UNMAPPED))])
    add("pop qword ptr [rbx]", [("rbx", hexn(READ_ONLY_PAGE))])  # rsp must not move
    add("ret", [("rsp", hexn(UNMAPPED))])
    add("call rax", [("rsp", hexn(READ_ONLY_PAGE + 0x100)), ("rax", hexn(DATA_PAGE))])
    add("call qword ptr [rbx]", [("rbx", hexn(UNMAPPED))])
    add("jmp qword ptr [rbx]", [("rbx", hexn(UNMAPPED))])
    add("movdqu xmm0, xmmword ptr [rbx]", [("rbx", hexn(READ_ONLY_PAGE + 0xFF8))])
    add("movdqu xmmword ptr [rbx], xmm0", [("rbx", hexn(DATA_PAGE + 0xFF8))])
    add("movdqa xmm0, xmmword ptr [rbx]", [("rbx", hexn(UNMAPPED + 8))])  # misaligned before unmapped
    add("movdqa xmm0, xmmword ptr [rbx]", [("rbx", hexn(UNMAPPED))])
    add("movsd qword ptr [rbx], xmm0", [("rbx", hexn(READ_ONLY_PAGE))])
    add("movq xmm0, qword ptr [rbx]", [("rbx", hexn(UNMAPPED))], source="movd xmm0, dword ptr [rbx]",
        patch=with_rex_w)
    add("cvttsd2si rax, qword ptr [rbx]", [("rbx", hexn(UNMAPPED))])
    add("ucomisd xmm0, qword ptr [rbx]", [("rbx", hexn(UNMAPPED))])
    add("setne byte ptr [rbx]", [("rbx", hexn(READ_ONLY_PAGE))])
    # Instruction fetch: ending exactly at the end of the code page, and running past it.
    add("mov rax, rbx", [("at", "0xffd")])
    add("mov rax, rbx", [("at", "0xffe")])
    add("mov rax, qword ptr [rip + 0x0]", [("at", "0xff9")])
    add("movabs rax, 0x1122334455667788", [("at", "0xff8")])
    add("jmp 0x40001000", [("at", "0xffb")], raw="e900000000")
    add("je 0x40001006", [("at", "0xffe"), ("flags", "Z")], raw="0f8402000000")
    # A non-canonical data address raises #GP on the CPU; the model has no notion
    # of canonical form. `known=` marks a deviation listed in tests/x86/README.md.
    # (Branches to such addresses are left out: Intel faults on the branch, AMD
    # on the fetch after it.)
    nc = 0x0000800000000000
    add("mov rax, qword ptr [rbx]", [("rbx", hexn(nc)), ("known", "noncanonical")])
    add("mov qword ptr [rbx], rax", [("rbx", hexn(nc + 0x1000)), ("known", "noncanonical")])
    # Undefined opcodes, which the decoder rejects too.
    add("ud2", [], raw="0f0b")
    add("lock mov rax, rbx", [], raw="f04889d8")


GROUPS = [arithmetic, moves, unary, multiply, shifts, conditionals, branches, stack, sse, floating, faults]


def main():
    g = Gen(seed=20261009)
    for group in GROUPS:
        group(g)
    everything = [v for vs in g.groups.values() for v in vs]
    finish(everything)
    out = HERE / "vectors"
    out.mkdir(exist_ok=True)
    for old in out.glob("*.txt"):
        old.unlink()
    for name, vs in g.groups.items():
        (out / f"{name}.txt").write_text("".join(v.line() + "\n" for v in vs))
    print(f"{len(everything)} vectors in {len(g.groups)} files", file=sys.stderr)


if __name__ == "__main__":
    main()
