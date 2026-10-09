import X86.State

/-!
The parts of the System V x86-64 calling convention that do not depend on
the function's signature.
-/

namespace Abi.SysV

open X86

def argumentRegister : Fin 6 → Register
  | 0 => .rdi
  | 1 => .rsi
  | 2 => .rdx
  | 3 => .rcx
  | 4 => .r8
  | 5 => .r9

/-- The `i`-th integer argument passed in a register. -/
def argument (s : State) (i : Fin 6) : UInt64 := s.register (argumentRegister i)

/-- The address of the `i`-th 8-byte argument slot on the stack at entry,
above the return address. -/
def stackArgument (s : State) (i : Nat) : UInt64 := s.rsp + (8 + 8 * i).toUInt64

/-- A result too large for registers is written to memory at this address,
passed as a hidden first argument. -/
def indirectResult (s : State) : UInt64 := argument s 0

def calleeSaved : List Register := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- `s` is the state right after a `call` that will return to `returnAddress`.
The direction flag, which the convention also requires clear, is not
modelled: no supported instruction reads it. -/
structure Entry (s : State) (returnAddress : UInt64) : Prop where
  returnAddress : s.memory.Holds .bits64 s.rsp returnAddress
  -- `rsp ≡ 0 (mod 16)` before the `call`, which pushed 8 bytes.
  stackAligned : s.rsp % 16 = 8
  -- No flag is passed into a call, so the callee may not read one it did not write.
  rflags : s.rflags = .undefined

/-- `s'` is a return from the call entered in `s`. -/
structure Returned (s s' : State) : Prop where
  stackPopped : s'.rsp = s.rsp + 8
  calleeSavedKept : ∀ r ∈ calleeSaved, s'.register r = s.register r
  -- MXCSR's control bits are callee-saved; its status bits (0–5) are not.
  mxcsrKept : s'.mxcsr &&& ~~~0x3f = s.mxcsr &&& ~~~0x3f

/-- `s'` returns from a call entered in `s` with an indirect result, handing
its address back in `rax`. -/
def ReturnsIndirectly (s s' : State) : Prop :=
  s'.register .rax = indirectResult s

end Abi.SysV
