import ValidateFeePayer.Memory

/-!
# The stack

The stack is not separate state: it is the stack pointer (x86: `rsp`) plus one read/write mapping of
the ordinary memory model. A stack overflow is therefore not a separate
mechanism either: a `push` or `call` below the mapping touches an unmapped
address and stops the machine with a page fault, as on Linux, where the
kernel then delivers `SIGSEGV` (and Rust's handler prints "stack overflow").

Where the stack is on Linux x86-64, and why its bounds are parameters:

- The main thread's stack starts just below the top of user space
  (`0x7ffffffff000` with 4-level paging), moved down by a random offset under
  ASLR. It grows down on demand, up to `RLIMIT_STACK` (8 MiB by default), and
  the kernel keeps `stack_guard_gap` (256 pages, 1 MiB) below it unmapped.
  Growth on demand is invisible to the program, so we take `low` to be the
  lowest address it may grow to.
- Other threads (the validator runs transactions on worker threads) get a
  fixed-size `mmap`ed stack (Rust's `std::thread` default is 2 MiB; thread
  pools set their own size) with a `PROT_NONE` guard page at its low end
  (glibc `pthread`).

Neither is at a fixed address, so a stack is an interval `[low, high)` given as
a parameter. What lies below `low` must be unmapped for an overflow to fault
(`GuardedBelow`); the image and the argument objects are elsewhere.

"Stack bytes free" is not an assumption baked into the model but a derived
quantity: `free low stackPointer = stackPointer - low`, the room between the stack pointer and the guard. A
specification that assumes, say, 96 bytes free at entry (the most the carved
code uses: five pushes, `sub rsp, 0x10`, the call into the callee, its three
pushes and the call into the panic) gets every push within the mapping from
that, and every deeper push is the fault above.
-/

namespace ValidateFeePayer

/-- A thread's stack: the read/write interval `[low, low + bytes.size)`. -/
structure Stack where
  low : UInt64
  bytes : ByteArray

namespace Stack

/-- One past the highest stack address, as a `Nat` so it cannot wrap. -/
def high (st : Stack) : Nat := st.low.toNat + st.bytes.size

def mapping (st : Stack) : Mapping := { base := st.low, bytes := st.bytes, permissions := .readWrite }

/-- Bytes between the stack pointer and the low end of the stack. -/
def free (low stackPointer : UInt64) : Nat := stackPointer.toNat - low.toNat

/-- The bytes up to `guard` below the stack are unmapped, so overflowing the
stack by up to that many bytes faults. Linux guarantees at least a page. -/
def GuardedBelow (st : Stack) (m : Memory) (guard : Nat) : Prop :=
  ∀ a : UInt64, st.low.toNat - guard ≤ a.toNat → a.toNat < st.low.toNat →
    ∀ mp ∈ m.mappings, ¬ mp.Contains a

end Stack

end ValidateFeePayer
