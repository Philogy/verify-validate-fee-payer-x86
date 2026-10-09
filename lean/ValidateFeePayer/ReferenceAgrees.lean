import ValidateFeePayer.Proof.Reference

/-!
`Spec.chargeFeePayer` checks rent with one condition where Agave computes
rent states and their transition; `Reference.chargeFeePayer` keeps Agave's
shape. They agree on every input, including which error or panic they hit.
The proof is in `ValidateFeePayer/Proof/Reference.lean`.
-/

namespace ValidateFeePayer

theorem chargeFeePayer_eq_reference (account : Spec.Account) (payerIndex : UInt16)
    (rent : Spec.Rent) (fee : UInt64) (relax : Bool) :
    Spec.chargeFeePayer account payerIndex rent fee relax =
      Reference.chargeFeePayer account payerIndex rent fee relax :=
  Reference.chargeFeePayer_eq' account payerIndex rent fee relax

/-- info: 'ValidateFeePayer.chargeFeePayer_eq_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms chargeFeePayer_eq_reference

end ValidateFeePayer
