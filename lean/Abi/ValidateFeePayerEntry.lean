import Abi.SysV

/-!
Where `validate_fee_payer`'s arguments are at its entry, as rustc laid them
out in this build. The Rust ABI is unstable, so this is what was observed,
not something the language promises: the 12-byte `Result<(), TransactionError>`
is returned through a hidden pointer passed first (and handed back in `rax`),
which moves every argument one register along, and the seventh, `relax`,
goes in the first stack slot.
-/

namespace Abi

open X86

/-- The argument locations. `payerIndex` is a `u16`: only the low 16 bits of
its register are the argument. `relax` is the address of a `bool`. -/
structure ValidateFeePayerEntry where
  result : UInt64
  account : UInt64
  payerIndex : UInt64
  errorMetrics : UInt64
  rent : UInt64
  fee : UInt64
  relax : UInt64

def ValidateFeePayerEntry.of (s : State) : ValidateFeePayerEntry where
  result := SysV.indirectResult s
  account := SysV.argument s 1
  payerIndex := SysV.argument s 2
  errorMetrics := SysV.argument s 3
  rent := SysV.argument s 4
  fee := SysV.argument s 5
  relax := SysV.stackArgument s 0

end Abi
