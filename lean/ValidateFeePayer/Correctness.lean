import ValidateFeePayer.Contract
import ValidateFeePayer.Proof.Correctness

/-!
The correctness theorem. Its statement lives here; the proof is in
`ValidateFeePayer/Proof/`.
-/

namespace ValidateFeePayer

open X86 Abi

/-- From any call into the loaded image whose footprint is in place and
which encodes the arguments, the machine code does what
`Spec.validateFeePayer` says: it panics exactly when the Rust function
panics, and otherwise returns with the result, the metrics and, on success,
the updated account encoded in memory. Either way nothing else in memory
changes. It never faults, jumps outside the code, or reads an undefined flag.

`heap` is where the account's pointers lead: `encoded` pins it down. -/
theorem validateFeePayer_correct (loadBase returnAddress : UInt64) (s : State) (heap : AccountHeap)
    (account : Spec.Account) (metrics : Spec.ErrorMetrics) (rent : Spec.Rent) (payerIndex : UInt16)
    (fee : UInt64) (relax : Bool)
    (called : Called loadBase returnAddress s)
    (abi : SysV.Entry s returnAddress)
    (footprint : Footprint loadBase s heap account.data.length)
    (encoded : Encoded s heap account metrics rent payerIndex fee relax)
    (integerThreshold : IntegerThreshold rent) :
    ∀ n ≥ fuel, match Spec.validateFeePayer account payerIndex rent fee relax metrics with
    | (.error (.panic _), _) =>
      ∃ s', run (exits loadBase returnAddress) n s = .panicked s' ∧ Frame s s'
    | (.error (.tx e), metrics') =>
      ∃ s', run (exits loadBase returnAddress) n s = .returned s' ∧ Post s heap metrics' (.error e) s'
    | (.ok account', metrics') =>
      ∃ s', run (exits loadBase returnAddress) n s = .returned s' ∧ Post s heap metrics' (.ok account') s' :=
  correct (.of loadBase returnAddress s heap payerIndex fee) account metrics rent relax s
    { ofState := rfl, called, abi, footprint, encoded, integerThreshold }

/-- info: 'ValidateFeePayer.validateFeePayer_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms validateFeePayer_correct

end ValidateFeePayer
