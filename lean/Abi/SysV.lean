import X86.State

/-!
The parts of the System V x86-64 calling convention that do not depend on
the function's signature.
-/

namespace Abi.SysV

open X86

def argumentRegister : Fin 6 → Register
  | 0 => .destinationIndex
  | 1 => .sourceIndex
  | 2 => .data
  | 3 => .counter
  | 4 => .r8
  | 5 => .r9

/-- The `i`-th integer argument passed in a register. -/
def argument (s : State) (i : Fin 6) : UInt64 := s.register (argumentRegister i)

/-- The address of the `i`-th 8-byte argument slot on the stack at entry,
above the return address. -/
def stackArgument (s : State) (i : Nat) : UInt64 := s.stackPointer + (8 + 8 * i).toUInt64

def calleeSaved : List Register := [.base, .framePointer, .r12, .r13, .r14, .r15]

/-- `s` is the state right after a `call` that will return to `returnAddress`.
The direction flag, which the convention also requires clear, is not
modelled: no supported instruction reads it. -/
structure Entry (s : State) (returnAddress : UInt64) : Prop where
  returnAddress : s.memory.Holds .bits64 s.stackPointer returnAddress
  -- `rsp ≡ 0 (mod 16)` before the `call`, which pushed 8 bytes.
  stackAligned : s.stackPointer % 16 = 8
  -- No flag is passed into a call, so the callee may not read one it did not write.
  flags : s.flags = .undefined

/-- `s'` is a return from the call entered in `s`. -/
structure Returned (s s' : State) : Prop where
  stackPopped : s'.stackPointer = s.stackPointer + 8
  calleeSavedKept : ∀ r ∈ calleeSaved, s'.register r = s.register r
  -- MXCSR's control bits are callee-saved; its status bits (0–5) are not.
  floatControlKept : s'.floatControl &&& ~~~0x3f = s.floatControl &&& ~~~0x3f

end Abi.SysV
