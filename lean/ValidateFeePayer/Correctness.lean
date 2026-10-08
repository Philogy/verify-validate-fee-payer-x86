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
theorem validateFeePayer_correct (c : Call) (refs : Spec.MutRefs) (rent : Spec.Rent) (relax : Bool)
    (s : State) (pre : Pre c refs rent relax s) :
    match (Spec.validateFeePayer c.payerIndex rent c.fee relax).run refs with
    | .error .maximumPermittedDataLengthExceeded => ∃ s', run c.exits fuel s = .panicked s'
    | .ok (result, refs') => ∃ s', run c.exits fuel s = .returned s' ∧ Post c s result refs' s' := by
  sorry

end ValidateFeePayer
