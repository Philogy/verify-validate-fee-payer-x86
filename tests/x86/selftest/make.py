#!/usr/bin/env python3
"""Writes the harness self-test fixtures, tests/x86/selftest/<name>/.

Each fixture is real vectors with the CPU's committed outcomes and one
planted defect; `want.txt` says how many failures `x86-test selftest` must
report and what the report must say. `pass/` has no defect and must pass.
Rerun after the vectors or outcomes it draws from change.
"""
import re
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
X86 = HERE.parent


def lines(path):
    return [l for l in path.read_text().splitlines() if l.strip() and not l.startswith("#")]


def pairs(group):
    return list(zip(lines(X86 / "vectors" / f"{group}.txt"), lines(X86 / "expected" / f"{group}.txt")))


def find(group, vector=lambda v: True, outcome=lambda o: True):
    for v, o in pairs(group):
        if vector(v) and outcome(o):
            return v, o
    raise SystemExit(f"no vector in {group} matches")


ADD = find("arithmetic", lambda v: v.startswith("add rax, rcx") or v.startswith("add r"), lambda o: " flags=" in o and " ok " in o)
REGISTER = find("arithmetic", lambda v: v.startswith("sub "), lambda o: re.search(r" r[a-z0-9]+=0x", o))
MEMORY = find("arithmetic", lambda v: v.startswith("add qword ptr"), lambda o: " mem=" in o)
XMM = find("sse", lambda v: v.startswith("pxor xmm"), lambda o: " xmm" in o)
MXCSR = find("float", lambda v: v.startswith("addsd"), lambda o: " mxcsr=" in o)
BRANCH = find("branch", lambda v: v.startswith("jmp 0x"))
UNMAPPED = find("fault", outcome=lambda o: "pagefault unmapped" in o)
DENIED = find("fault", outcome=lambda o: "pagefault denied" in o)
GP = find("fault", outcome=lambda o: o.endswith("| gp"))
ILL = find("fault", outcome=lambda o: o.endswith("| ill"))
KNOWN = find("fault", lambda v: "known=" in v)

PASS = [ADD, REGISTER, MEMORY, XMM, MXCSR, BRANCH, UNMAPPED, DENIED, GP, ILL, KNOWN]


def replace_field(outcome, key, new):
    out, n = re.subn(rf"( {re.escape(key)}=)(\S+)", lambda m: m.group(1) + new(m.group(2)), outcome, count=1)
    assert n == 1, (outcome, key)
    return out


def flip_hex_digit(v):
    return v[:-1] + ("1" if v[-1] != "1" else "2")


def flip_flag(flags):
    i = next(i for i, c in enumerate(flags) if c != "?")
    return flags[:i] + ("-" if flags[i] != "-" else "CPAZSO"[i]) + flags[i + 1:]


# name: (vector lines, outcome lines, failures, text the report must contain)
FIXTURES = {
    "pass": ([v for v, _ in PASS], [o for _, o in PASS], 0, []),
    "flag": ([ADD[0]], [replace_field(ADD[1], "flags", flip_flag)], 1, ["MISMATCH t.txt"]),
    "register": ([REGISTER[0]], [re.sub(r"( r[a-z0-9]+=)(0x[0-9a-f]+)", lambda m: m.group(1) + flip_hex_digit(m.group(2)), REGISTER[1], count=1)], 1, ["MISMATCH"]),
    "memory": ([MEMORY[0]], [replace_field(MEMORY[1], "mem", flip_hex_digit)], 1, ["MISMATCH"]),
    "rip": ([BRANCH[0]], [replace_field(BRANCH[1], "rip", flip_hex_digit)], 1, ["MISMATCH"]),
    "xmm": ([XMM[0]], [re.sub(r"( xmm\d+=)(0x[0-9a-f]+)", lambda m: m.group(1) + flip_hex_digit(m.group(2)), XMM[1], count=1)], 1, ["MISMATCH"]),
    "mxcsr": ([MXCSR[0]], [replace_field(MXCSR[1], "mxcsr", flip_hex_digit)], 1, ["MISMATCH"]),
    "extra-change": ([ADD[0]], [ADD[1] + " r15=0x1"], 1, ["MISMATCH"]),
    "missing-change": ([MEMORY[0]], [re.sub(r" mem=\S+", "", MEMORY[1], count=1)], 1, ["MISMATCH"]),
    "kind": ([ADD[0]], [ADD[1].split("|")[0] + "| pagefault unmapped 0x50000000"], 1, ["MISMATCH"]),
    "fault-address": ([UNMAPPED[0]], [re.sub(r"(pagefault unmapped )(0x[0-9a-f]+)", lambda m: m.group(1) + flip_hex_digit(m.group(2)), UNMAPPED[1])], 1, ["MISMATCH"]),
    "denied-as-unmapped": ([DENIED[0]], [DENIED[1].replace("denied", "unmapped")], 1, ["MISMATCH"]),
    "fault-as-ok": ([GP[0]], [GP[1].replace("| gp", "| ok")], 1, ["MISMATCH"]),
    "known-model-agrees": ([KNOWN[0]], [KNOWN[1].split("|")[0] + "| " + re.search(r"known=\w+:(\S+)", KNOWN[0]).group(1).replace("_", " ")], 1, ["KNOWN", "CPU now gives 'pagefault unmapped'"]),
    "known-pin": ([re.sub(r"(known=\w+:\S*?)(0x[0-9a-f]+)", lambda m: m.group(1) + flip_hex_digit(m.group(2)), KNOWN[0])], [KNOWN[1]], 1, ["KNOWN", "not the pinned"]),
    "known-unpinned": ([re.sub(r"known=(\w+):\S+", r"known=\1", KNOWN[0])], [KNOWN[1]], 1, ["does not pin"]),
    "known-cpu": ([KNOWN[0]], [KNOWN[1].replace("| gp", "| ill")], 1, ["CPU now gives 'ill'"]),
    "known-undocumented": ([re.sub(r"known=\w+:", "known=whatever:", KNOWN[0])], [KNOWN[1]], 1, ["not a documented deviation"]),
    "truncated": ([v for v, _ in PASS], [o for _, o in PASS][:-1], 1, ["vectors but 10 expected outcomes"]),
    "extra-outcome": ([v for v, _ in PASS[:3]], [o for _, o in PASS[:4]], 1, ["vectors but 4 expected outcomes"]),
    "swapped": ([ADD[0], MEMORY[0]], [MEMORY[1], ADD[1]], 2, ["OUTCOME t.txt"]),
    "bad-value": ([re.sub(r" (r[a-z0-9]+)=0x[0-9a-f]+", r" \1=0xzz", ADD[0], count=1)], [ADD[1]], 1, ["bad value"]),
    "too-wide": ([re.sub(r" (r[a-z0-9]+)=0x[0-9a-f]+", r" \1=0x10000000000000000", ADD[0], count=1)], [ADD[1]], 1, ["does not fit in 64 bits"]),
    "bad-xmm": ([XMM[0] + " xmm16=0x1"], [XMM[1]], 1, ["bad register xmm16"]),
    "bad-flags": ([re.sub(r"flags=\S+", "flags=CX", ADD[0])], [ADD[1]], 1, ["bad flags"]),
    "unknown-field": ([ADD[0] + " foo=1"], [ADD[1]], 1, ["unknown field foo"]),
    "asm": ([ADD[0].replace("add ", "sub ", 1)], [ADD[1]], 1, ["ASM t.txt"]),
}


def main():
    for old in HERE.iterdir():
        if old.is_dir():
            shutil.rmtree(old)
    for name, (vectors, outcomes, failures, want) in FIXTURES.items():
        d = HERE / name
        (d / "vectors").mkdir(parents=True)
        (d / "expected").mkdir()
        (d / "vectors" / "t.txt").write_text("".join(v + "\n" for v in vectors))
        (d / "expected" / "t.txt").write_text("".join(o + "\n" for o in outcomes))
        (d / "want.txt").write_text("".join(l + "\n" for l in [f"failures={failures}"] + want))
    # Files out of step: outcomes without vectors, and vectors without outcomes.
    d = HERE / "orphan-outcomes"
    shutil.copytree(HERE / "pass", d)
    (d / "expected" / "u.txt").write_text(ADD[1] + "\n")
    (d / "want.txt").write_text("failures=1\nu.txt: outcomes without vectors\n")
    d = HERE / "missing-outcomes"
    shutil.copytree(HERE / "pass", d)
    (d / "vectors" / "u.txt").write_text(ADD[0] + "\n")
    (d / "want.txt").write_text("failures=1\nu.txt: no expected outcomes\n")
    print(f"{len(FIXTURES) + 2} fixtures")


if __name__ == "__main__":
    main()
