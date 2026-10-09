import ValidateFeePayer.Contract
import ValidateFeePayer.Proof.Correctness

/-!
The correctness theorems. Their statements live here; the proofs are in
`ValidateFeePayer/Proof/`.

Both take the exemption threshold to be one of the two that
`Rent::minimum_balance` computes with integers. That is a limit of the
proof, not a precondition of the code: the `f64` path (the SSE blocks at
`0x27f369b` and `0x27f384b`) is not proved. `0x3ff0…` is `1.0` (SIMD-0194),
`0x4000…` is `2.0`.
-/

namespace ValidateFeePayer

/-- Any machine state `s` with the image loaded (`Loaded`), at a call into
it (`Called`), whose argument registers point at memory the code may use
(`Footprint`), runs without faulting: it panics, or it returns to the caller
with the stack popped and the callee-saved registers restored. Either way
memory outside the bytes the code may write is untouched. -/
theorem validateFeePayer_safe (loadBase returnAddress : UInt64) (s : X86.State)
    (loaded : Loaded loadBase s.memory)
    (called : Called loadBase returnAddress s)
    (heap : AccountHeap) (dataLength : Nat)
    (footprint : Footprint loadBase s heap dataLength)
    (integerThreshold : s.memory.read .bits64 (exemptionThresholdAddress s) ∈
      [.ok Spec.simd0194ExemptionThreshold, .ok Spec.currentExemptionThreshold]) :
    PanicsOrReturns returnAddress s (invoke loadBase returnAddress s) :=
  invoke_panicsOrReturns loaded called footprint integerThreshold

/-- If moreover the argument locations hold the Rust values `args`
(`Encoded`), the run does what `Spec.validateFeePayer` does on them
(`MatchesSpec`): it panics exactly when the Rust function panics, and
otherwise returns with the result, the metrics and, on success, the updated
account encoded in memory. -/
theorem validateFeePayer_correct (loadBase returnAddress : UInt64) (s : X86.State)
    (loaded : Loaded loadBase s.memory)
    (called : Called loadBase returnAddress s)
    (heap : AccountHeap) (args : Args)
    (footprint : Footprint loadBase s heap args.account.data.length)
    (integerThreshold : s.memory.read .bits64 (exemptionThresholdAddress s) ∈
      [.ok Spec.simd0194ExemptionThreshold, .ok Spec.currentExemptionThreshold])
    (encoded : Encoded s heap args) :
    PanicsOrReturns returnAddress s (invoke loadBase returnAddress s) ∧
      MatchesSpec s heap args.spec (invoke loadBase returnAddress s) :=
  invoke_matchesSpec loaded called footprint encoded integerThreshold

/-- With more fuel than `invoke` gives, the run is the same: it has stopped. -/
theorem validateFeePayer_more_fuel {loadBase returnAddress : UInt64} {s : X86.State}
    (safe : PanicsOrReturns returnAddress s (invoke loadBase returnAddress s)) (n : Nat) (hn : fuel ≤ n) :
    X86.run (exits loadBase returnAddress) n s = invoke loadBase returnAddress s :=
  run_of_panicsOrReturns safe hn

/-- info: 'ValidateFeePayer.validateFeePayer_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms validateFeePayer_safe

/-- info: 'ValidateFeePayer.validateFeePayer_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms validateFeePayer_correct

/-- info: 'ValidateFeePayer.validateFeePayer_more_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms validateFeePayer_more_fuel

end ValidateFeePayer
