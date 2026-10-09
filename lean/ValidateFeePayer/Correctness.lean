import ValidateFeePayer.Contract
import ValidateFeePayer.Proof.Correctness

/-!
The correctness theorem. Its statement lives here; the proof is in
`ValidateFeePayer/Proof/`.
-/

namespace ValidateFeePayer

/-- Call the image from any caller's state `s` that makes a valid call
(`Called`), whose memory has room for what the code touches (`Footprint`),
and whose argument locations hold the Rust values `account`, `metrics`,
`rent`, `payerIndex`, `fee` and `relax` (`Encoded`), with one of the integer
exemption thresholds. Then the machine code does what `Spec.validateFeePayer`
says on those values (`Behaves`): it panics exactly when the Rust function
panics, and otherwise returns with the result, the metrics and, on success,
the updated account encoded in memory. Either way nothing else in memory
changes. It never faults, jumps outside the code, or reads an undefined flag.

`heap` is where the account's pointers lead: `encoded` pins it down, as it
pins down every value from the bytes of `s`. -/
theorem validateFeePayer_correct (loadBase returnAddress : UInt64) (s : X86.State)
    (called : Called loadBase returnAddress s)
    (heap : AccountHeap) (account : Spec.Account) (metrics : Spec.ErrorMetrics) (rent : Spec.Rent)
    (payerIndex : UInt16) (fee : UInt64) (relax : Bool)
    (footprint : Footprint loadBase s heap account.data.length)
    (encoded : Encoded s heap account metrics rent payerIndex fee relax)
    (integerThreshold : IntegerThreshold rent) :
    Behaves loadBase s heap (Spec.validateFeePayer account payerIndex rent fee relax metrics)
      (invoke loadBase returnAddress s) :=
  invoke_behaves called footprint encoded integerThreshold

/-- With more fuel than `invoke` gives, the run is the same: it has stopped. -/
theorem validateFeePayer_more_fuel {loadBase returnAddress : UInt64} {s : X86.State} {heap : AccountHeap}
    {spec : Except Spec.Error Spec.Account × Spec.ErrorMetrics}
    (behaves : Behaves loadBase s heap spec (invoke loadBase returnAddress s)) (n : Nat) (hn : fuel ≤ n) :
    X86.run (exits loadBase returnAddress) n (enter loadBase s) = invoke loadBase returnAddress s :=
  run_of_behaves behaves hn

/-- info: 'ValidateFeePayer.validateFeePayer_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms validateFeePayer_correct

/-- info: 'ValidateFeePayer.validateFeePayer_more_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms validateFeePayer_more_fuel

end ValidateFeePayer
