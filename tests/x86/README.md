# Testing the x86 model

`lean/X86/` (decoder, `step`, `F64`) is trusted by the proof. Two checks
compare it with independent implementations; CI (`.github/workflows/x86-tests.yml`)
runs both on every push.

## Behaviour: the model against a CPU

| File | Role |
|---|---|
| `gen.py` | Writes `vectors/*.txt`: one instruction and start state per line. Seeded; CI checks a rerun is identical. |
| `layout.h` | The start state a vector overrides: four pages (code r-x, data rw-, read-only, stack), register and memory fill. `lean/X86Test/Harness.lean` repeats it. |
| `oracle.c` | Maps the pages in a child, sets the registers with ptrace, single-steps the instruction and prints what changed (`expected/*.txt`). |
| `lean/X86Test.lean` | `x86-test behaviour .`: one `step` per vector, printed the same way, compared line by line. |
| `selftest/` | Fixtures with one planted defect each (a wrong flag, register, memory byte, rip, xmm, MXCSR, outcome kind or fault address, a missing or extra outcome, a broken `known=`, a bad field value). `x86-test selftest selftest` requires the runner to reject each for its reason and to pass `pass/`. `make.py` draws them from the committed vectors and outcomes; CI checks a rerun is identical. |
| `lean/X86Test/FlagsAffected.lean` | The SDM's "Flags Affected" per instruction, written from the manual. Checked against the model on every vector that completes and, as a `#guard`, on register operands at every width and shift count. |
| `lean/X86Test/Refusals.lean` | `#guard`s for what no vector reaches: fetching from non-executable memory, the exits, reading an undefined flag, non-default MXCSR control bits, the 15-byte limit. |
| `rosetta/` | An optional local oracle for Apple silicon (below). |

A vector: `asm | bytes | field=value ...`. An outcome:
`bytes | ok|pagefault unmapped A|pagefault denied A|gp|ill field=value ...`,
listing only what changed. Flags print as `CPAZSO` letters and `-` for clear;
the model prints `?` for a flag it leaves undefined (`none`), which accepts
whatever the CPU holds: the model faults on reading such a flag, so its value
cannot affect a run the model completes.
MXCSR exception bits are compared although the machine does not keep them
(`Harness.floatExceptions` recomputes them from `F64`).

The runner also fails if a vector's `asm` is not what `Print.lean` prints for
its bytes; if a vector or outcome file has no partner or a different number
of lines, or an outcome is not for its vector's bytes; if a field does not
parse or does not fit (no value silently becomes 0); if the model's flags
after a completed step contradict the SDM table (a flag the SDM leaves
undefined must be `?`, a defined one must not, an unaffected one must keep its
value); and unless every form in the carved code and every `Instruction`
constructor has a vector that completes, every outcome kind (`ok`, both page
faults, `gp`, `ill`) has an agreeing vector, and every instruction of the
carved code has an agreeing vector with its exact bytes (`gen.py`, `carved`).

The model leaves undefined one flag the SDM defines: the carry of `sar` by at
least the width of an 8- or 16-bit operand (the SDM's exception names only
`shl` and `shr`). That is sound, as the model faults if it is read, and it is
listed in `FlagsAffected.lean` rather than accepted silently.

Known differences, `known=<reason>:<model outcome>` with spaces as `_`: the
model must give exactly that outcome and the CPU the kind listed for the
reason in `Harness.knownDeviations`, so a change on either side fails.

- `noncanonical`: a load or store at a non-canonical address raises #GP;
  the model has no canonical-address check and reports a page fault. Both
  stop the program.

Not compared: state the model omits (segment registers, FS/GS bases, x87/MMX,
AVX-512 masks, and YMM upper halves, which legacy SSE encodings leave
alone); `rflags` bits outside the six flags are printed if they change, so
an unexpected change fails.

The CPU is whatever GitHub's runner has (CI logs its CPUID), so one vendor
per run. Undefined flags are vendor-specific, which the `?` covers, but a
vendor difference in defined behaviour would only show on another runner.
CI also requires the runner's outcomes to match the committed `expected/` up
to undefined flags (`x86-test same`), so the committed copy, which local runs
and the self-test fixtures use, cannot drift. CI also checks that the code
bytes in `Image.lean` are the bytes llvm-objdump disassembled
(`check-carved.py`).

## Decoding: the decoder against llvm-objdump

`decode.py` writes candidates (every vector's bytes, mutations of their
prefixes, REX and ModRM/SIB bytes, and every opcode of the one-byte, `0f` and
`0f 38` maps with random operand bytes) with llvm-objdump's decoding;
`x86-test decode` requires every encoding the Lean decoder accepts to have
llvm's length and text, and that the decoder fetches no byte past the
instruction. Encodings the decoder rejects are listed by reason: it is
stricter than the CPU by design (see `Decode.lean`). `normalise` in
`decode.py` maps llvm's notation to `Print.lean`'s; each rule changes
notation only.

## Running locally

On Linux x86-64 (not under Rosetta or QEMU, whose fault and flag behaviour
is what is being tested):

```sh
cd lean && lake build x86-test && cd ../tests/x86
python3 gen.py
gcc -O2 -o oracle oracle.c
for f in vectors/*.txt; do ./oracle < $f > expected/$(basename $f); done
../../lean/.lake/build/bin/x86-test behaviour .
OBJDUMP=llvm-objdump python3 decode.py > decode.txt && ../../lean/.lake/build/bin/x86-test decode decode.txt
```

Elsewhere, the committed `expected/` stands in for the CPU: `x86-test
behaviour .` and `x86-test selftest selftest` work on any machine. `x86-test
model vectors/<file>` prints the model's outcomes alone. `gen.py` and
`decode.py` need GNU as (`AS=...`, e.g. `AS=x86_64-elf-as` from Homebrew's
`x86_64-elf-binutils`).

### Under Rosetta

`rosetta/run.sh` runs the vectors in Docker's `linux/amd64`, which on Apple
silicon is Rosetta, and compares the model with the outcomes
(`x86-test rosetta`). Rosetta does not support ptrace single-stepping, so
`rosetta/oracle_signals.c` installs the state from a signal handler and stops
at the `int3` fill after the instruction. It is a quick reference point, not
a replacement for CI's CPU: Rosetta does not keep AF (ignored), has no
alignment check on SSE operands, reports some permission faults as unmapped,
does not clear `ptest`'s P/S/O, and rejects `nop` with an operand; these are
counted and set aside, everything else must agree.
