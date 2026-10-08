# Comparing the model with hardware

The model (`lean/X86/`) is only as good as its agreement with a real CPU.
The plan is a CI job that checks every supported instruction form, the `F64`
operations included, one instruction at a time. Not built yet.

## Harness

For each instruction form in `X86/Instruction.lean`, and many random
encodings and states of it:

1. Map the instruction bytes and a few data pages in a child process, with
   the same permissions as the model's mappings, and set the registers,
   flags, XMM registers and MXCSR (default control bits).
2. Single-step it (ptrace), then dump the registers, flags, XMM registers
   and the mapped pages. Turn `SIGSEGV`/`SIGBUS` into a page fault and
   `SIGILL` into an undecodable instruction.
3. Run one `step` on the same state (exported via `lake exe`) and compare
   the outcome kind, then the state.

Run it at several load bases so rip-relative addressing is exercised, and log
the CPUID, since undefined-flag values are vendor-specific.

## What the comparison ignores, and why

- Flags the model reports as `none`: the SDM leaves them undefined, and the
  model makes reading one stop the run, so their hardware values cannot
  affect a run the model completes.
- MXCSR exception flags (bits 0–5): the model does not track them; no
  supported instruction reads them.
- YMM upper halves: legacy SSE encodings leave them alone.
- State the model omits (segment registers, FS/GS bases, x87/MMX, AVX-512
  masks, system flags). The harness should still check they are unchanged,
  which catches an instruction that touches one unexpectedly.
