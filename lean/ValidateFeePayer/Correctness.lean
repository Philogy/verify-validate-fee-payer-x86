import ValidateFeePayer.Contract

/-!
The correctness theorem. Its proof is the one `sorry` in the package.
-/

namespace ValidateFeePayer

open X86

/-- From any entry state that encodes the arguments, the machine code does
what `Spec.validateFeePayer` says: it panics exactly when the Rust function
panics, and otherwise returns with the result and the updated account and
metrics encoded in memory and nothing else changed. It never faults, jumps
outside the code, or reads an undefined flag. -/
theorem validateFeePayer_correct (c : Call) (account : Spec.Account) (metrics : Spec.ErrorMetrics)
    (rent : Spec.Rent) (relax : Bool) (s : State) (pre : Pre c account metrics rent relax s) :
    match Spec.validateFeePayer account c.payerIndex metrics rent c.fee relax with
    | none => ∃ s', run c.exits fuel s = .panicked s'
    | some (result, account', metrics') =>
      ∃ s', run c.exits fuel s = .returned s' ∧ Post c s result account' metrics' s' := by
  sorry

end ValidateFeePayer
