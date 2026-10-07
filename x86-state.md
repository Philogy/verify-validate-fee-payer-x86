# x86-64 machine state for the model

The model has to hold every piece of state that the carved instructions
read or write. The test oracle steps one instruction on real hardware
(ptrace/gdb style), dumps the state, and compares it with one Lean `step`.
Any state the hardware changes but we leave out would make that comparison
fail, so this list is as long as the oracle needs it to be, not as short as
the proof needs it to be.

Instructions in `validate_fee_payer` (245 lines of disassembly): integer ALU
(`mov cmp test xor or and add sub inc imul sar sbb lea movzx setcc cmovcc`),
control flow (`jcc jmp call ret push pop`), and SSE2/SSE4.1 scalar/packed
double (`movq movdqu movapd pxor por ptest punpckldq unpckhpd subpd subsd
addsd mulsd xorpd ucomisd cvttsd2si`). No x87, AVX, string ops, division,
TLS or syscalls.

## State

| Component | Width | Notes |
|---|---|---|
| `rip` | 64 | Next instruction. Jumps/calls are relative (`rel32`), so the load base `B` matters only for data. |
| 16 GPRs `rax…r15` | 64 each | Includes `rsp`/`rbp`. Sub-register writes have different rules: 32-bit writes zero the upper 32 bits, 8/16-bit writes leave the rest unchanged. That is `step` semantics; the state is just 16 × `UInt64`. |
| RFLAGS status bits | 6 bits | `CF PF AF ZF SF OF`. All six are compared, including `AF`/`PF`, because every ALU op writes them. |
| RFLAGS `DF` | 1 bit | The ABI says it is 0 on entry. No carved instruction reads it; model it as a constant and check that it stays 0. |
| 16 XMM regs `xmm0…xmm15` | 128 each | Code only uses `xmm0–2`, but they are caller-saved, so model all 16. Legacy-SSE encodings leave YMM upper halves alone, so the YMM halves stay out of the model; the oracle can ignore them. |
| `MXCSR` | 32 | Read: rounding mode (`RC`), `FTZ`, `DAZ`, exception masks. Written: **sticky** exception flags `IE DE ZE OE UE PE`. `cvttsd2si` sets `IE` on out-of-range/NaN, and `mulsd`/`addsd`/`subsd` set `PE` when inexact. Default `0x1F80`: all masked, round-to-nearest. With all masks set, SSE never traps, so the result is just a value plus flags. |
| Memory | byte-addressed, 2^64 | Each address is either *unmapped* or *mapped* with its permissions (R/W/X). We only need: carved code (R/X), carved data and GOT (R), and stack (R/W). Everything else is unmapped, and an access there faults. |
| Outcome | sum type | `running`, `returned` (top-level `ret`), `called f` (leaves the carve, e.g. into `check_static_account_rent_state_transition` or the panic), `fault` (#PF/#GP/#UD). |

### Stack

There is no separate stack state. The stack is `rsp` plus ordinary memory.
What we have to model:

- **Mapped extent**: an interval `[lo, hi)` that holds the caller's frame,
  the return address, and enough room below `rsp` for this function
  (8 pushes + `sub rsp, 0x10` + the `call` return address, so
  about 0x60 bytes) plus the 128-byte red zone. Below `lo` is the guard page,
  so an access there faults.
- **Alignment**: SysV requires `rsp ≡ 0 (mod 16)` at the `call`.
  `movapd`/`movdqa` with a *memory* operand faults (#GP) if the operand is
  misaligned. Here `movapd` only moves between registers and `movdqu` is
  unaligned, but we should still model the check.
- **Return address**: the entry state has `[rsp] = return address`. A final
  `ret` pops it and is the `returned` outcome.

## Not modeled (fixed at user level, or never touched)

`CS DS ES SS` (flat in 64-bit), `FS/GS` base (no TLS access),
`TF IF IOPL AC ID…` and the other RFLAGS system bits, `CR*`, `DR*`, MSRs, the x87/MMX
stack and `FCW/FSW`, AVX/`k` masks, the CET shadow stack (off in Linux userspace).
The oracle should still check that these stay unchanged, which catches
an instruction that touches one unexpectedly.

## Things the per-instruction oracle has to handle

- **Undefined flags.** For example, `imul` leaves `SF ZF AF PF` undefined, and
  shifts by >1 leave `OF` undefined. Real CPUs output some deterministic,
  vendor-specific value. Choose one approach:
  (a) the model gives a "don't care" mask for each instruction and the
  comparison ignores those bits, or (b) the model says the value is arbitrary
  (∀ value), and proofs can't depend on it. (a) feeds into (b).
- **Memory diff.** A debugger can't dump 2^64 bytes. Compare the bytes in
  the mapped regions above, or have `step` return a write log (address,
  bytes) and compare that with a dump of those addresses before and after.
- **Faults.** Run each instruction in a sandbox with known mappings, and turn
  SIGSEGV/SIGBUS/SIGILL into the `fault` outcome. Then compare the outcome
  kind, not just the registers.
- **Load base.** Run the oracle at several bases `B` (PIE/ASLR) so that
  RIP-relative and GOT addressing get exercised.
- **CI runner CPU.** GitHub runners are mostly AMD EPYC or Intel Xeon. Log
  the CPUID so that a result about undefined flags can be traced to the vendor.
