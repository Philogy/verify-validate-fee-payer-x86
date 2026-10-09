#!/usr/bin/env python3
"""Check that the code bytes in lean/ValidateFeePayer/Image.lean are the
bytes llvm-objdump disassembled (artifacts/validate_fee_payer.intel.s), and
that Disasm.lean is what disasm-to-lean.py makes of that disassembly.

Both files are committed outputs of one make-artifacts.sh run, and the
decoder check (listing_eq_objdump) compares the Lean decoder on Image.lean
with Disasm.lean; this ties them back to the same bytes.
"""
import re
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parent
image = (root / "lean" / "ValidateFeePayer" / "Image.lean").read_text()
listing = (root / "artifacts" / "validate_fee_payer.intel.s").read_text()

lean_code = {}
for m in re.finditer(r'name := "(\w+)"\s*address := (0x[0-9a-f]+)\s*contents := \.code ⟨#\[(.*?)\]⟩', image, re.S):
    lean_code[m.group(1)] = (int(m.group(2), 16), bytes(int(b, 16) for b in re.findall(r"0x[0-9a-f]{2}", m.group(3))))

objdump = {}
current = None
for line in listing.splitlines():
    header = re.match(r"^([0-9a-f]+) <(\w+)>:$", line)
    if header:
        current = header.group(2)
        objdump[current] = (int(header.group(1), 16), bytearray())
        continue
    m = re.match(r"^ +([0-9a-f]+): ([0-9a-f]{2}(?: [0-9a-f]{2})*) *\t", line)
    if m and current:
        start, code = objdump[current]
        if int(m.group(1), 16) != start + len(code):
            sys.exit(f"{current}: gap before {m.group(1)}")
        code += bytes.fromhex(m.group(2).replace(" ", ""))

problems = []
if set(lean_code) != set(objdump):
    problems.append(f"functions differ: Image.lean {sorted(lean_code)}, disassembly {sorted(objdump)}")
for name in sorted(set(lean_code) & set(objdump)):
    (a, x), (b, y) = lean_code[name], objdump[name]
    if a != b or x != bytes(y):
        problems.append(f"{name}: Image.lean {a:#x}+{len(x)} bytes, disassembly {b:#x}+{len(y)} bytes, equal: {x == bytes(y)}")
    else:
        print(f"{name}: {len(x)} bytes at {a:#x} agree")

subprocess.run([sys.executable, str(root / "disasm-to-lean.py")], check=True)
if subprocess.run(["git", "diff", "--exit-code", "--", "lean/ValidateFeePayer/Disasm.lean"], cwd=root).returncode:
    problems.append("Disasm.lean is not what disasm-to-lean.py makes of the disassembly")

for p in problems:
    print(p)
sys.exit(1 if problems or not lean_code else 0)
