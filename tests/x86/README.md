# Testing the x86 model

`lean/X86/` (decoder, `step`, `F64`) is trusted by the proof. Two checks
compare it with independent implementations; CI (`.github/workflows/x86-tests.yml`)
runs both on every push.

## Behaviour: the model against a CPU

| File | Role |
|---|---|
| `gen.py` | Writes `vectors/*.txt`: one instruction and start state per line. Seeded; CI checks a rerun is identical. |
| `layout.h` | The start state a vector overrides: four pages (code r-x, data rw-, read-only, stack), register and memory fill. `lean/X86Test/Harness.lean` repeats it. |
| `undefined_flags.py` | The flags the Intel SDM leaves undefined, per instruction, quoted from the SDM. |
| `oracle.c` | Maps the pages in a child, sets the registers with ptrace, single-steps the instruction and prints what changed (`expected/*.txt`). |
| `lean/X86Test.lean` | `x86-test behaviour .`: one `step` per vector, printed the same way, compared line by line. |

A vector: `asm | bytes | field=value ...`. An outcome:
`bytes | ok|pagefault unmapped A|pagefault denied A|gp|ill field=value ...`,
listing only what changed. Flags print as `CPAZSO` letters, `-` for clear and
`?` for undefined; the CPU's value of an undefined flag is never compared.
MXCSR exception bits are compared although the machine does not keep them
(`Harness.floatExceptions` recomputes them from `F64`).

The runner also fails if a vector's `asm` is not what `Print.lean` prints for
its bytes, if any form in the carved code or any `Instruction` constructor
has no vector that completes, or if a `known=` vector stops differing.

Known differences (`known=`):

- `noncanonical`: a load or store at a non-canonical address raises #GP;
  the model has no canonical-address check and reports a page fault. Both
  stop the program.

Not compared: state the model omits (segment registers, x87/MMX, YMM upper
halves); `rflags` bits outside the six flags are printed if they change, so
an unexpected change fails.

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
behaviour .` works on any machine. `x86-test model vectors/<file>` prints the
model's outcomes alone. `gen.py` and `decode.py` need GNU as (`AS=...`).
