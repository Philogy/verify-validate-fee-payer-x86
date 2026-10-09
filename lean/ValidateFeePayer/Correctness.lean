import ValidateFeePayer.Contract
import ValidateFeePayer.Proof.Correctness

/-!
The correctness theorem. Its statement lives here; the proof is in
`ValidateFeePayer/Proof/`, reduced to the one symbolic-execution `sorry`.
-/

namespace ValidateFeePayer

open X86

/-- From any entry state that encodes the arguments, the machine code does
what `Spec.validateFeePayer` says: it panics exactly when the Rust function
panics, and otherwise returns with the result, the metrics and, on success,
the updated account encoded in memory and nothing else changed. It never faults, jumps
outside the code, or reads an undefined flag. -/
theorem validateFeePayer_correct (c : Call) (account : Spec.Account) (metrics : Spec.ErrorMetrics)
    (rent : Spec.Rent) (relax : Bool) (s : State) (pre : Pre c account metrics rent relax s) :
    match Spec.validateFeePayer account c.payerIndex rent c.fee relax with
    | .error (.panic _) => ∃ s', run c.exits fuel s = .panicked s'
    | .error (.tx e) => ∃ s', run c.exits fuel s = .returned s' ∧ Post c s metrics (.error e) s'
    | .ok account' => ∃ s', run c.exits fuel s = .returned s' ∧ Post c s metrics (.ok account') s' :=
  correct c account metrics rent relax s pre

end ValidateFeePayer
