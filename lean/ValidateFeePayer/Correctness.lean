import ValidateFeePayer.Contract
import ValidateFeePayer.Proof.Correctness

/-!
The correctness theorem. Its statement lives here; the proof is in
`ValidateFeePayer/Proof/`.
-/

namespace ValidateFeePayer

open X86

/-- From any entry state that encodes the arguments, the machine code does
what `Spec.validateFeePayer` says: it panics exactly when the Rust function
panics, and otherwise returns with the result, the metrics and, on success,
the updated account encoded in memory. Either way nothing else in memory
changes. It never faults, jumps outside the code, or reads an undefined flag. -/
theorem validateFeePayer_correct (c : Call) (account : Spec.Account) (metrics : Spec.ErrorMetrics)
    (rent : Spec.Rent) (relax : Bool) (s : State) (pre : Pre c account metrics rent relax s) :
    ∀ n ≥ fuel, match Spec.validateFeePayer account c.payerIndex rent c.fee relax metrics with
    | (.error (.panic _), _) => ∃ s', run c.exits n s = .panicked s' ∧ c.Frame s s'
    | (.error (.tx e), metrics') => ∃ s', run c.exits n s = .returned s' ∧ Post c s metrics' (.error e) s'
    | (.ok account', metrics') => ∃ s', run c.exits n s = .returned s' ∧ Post c s metrics' (.ok account') s' :=
  correct c account metrics rent relax s pre

/-- info: 'ValidateFeePayer.validateFeePayer_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms validateFeePayer_correct

end ValidateFeePayer
