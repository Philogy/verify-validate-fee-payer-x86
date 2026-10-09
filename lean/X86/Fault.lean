import X86.Memory

namespace X86

inductive Flag where
  | carry | parity | auxiliaryCarry | zero | sign | overflow
  deriving DecidableEq, Repr

inductive DecodeError where
  | truncated
  | tooLong
  | unsupported (what : String)
  deriving DecidableEq, Repr

/-- Why an instruction could not complete. The instruction has no effect. -/
inductive Fault where
  | pageFault (f : PageFault)
  | undecodable (why : DecodeError)
  | misaligned (address : UInt64)
  /-- The CPU returns some vendor-specific value for an undefined flag, and
  the program may not rely on which. Faulting here instead of picking a
  value is sound: a run that ends without this fault never read an undefined
  flag, so it behaves the same whatever values the CPU holds there. -/
  | undefinedFlagRead (f : Flag)
  | unsupported (what : String)
  deriving DecidableEq, Repr

end X86
