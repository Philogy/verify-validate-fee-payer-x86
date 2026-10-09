import ValidateFeePayer.Proof.Run
import ValidateFeePayer.Proof.DecodeTable

/-! The simp set of one symbolic step, and `vstep`. -/

namespace ValidateFeePayer.Proof

open X86 Exec

@[vexec] theorem and_allOnes (x : UInt64) : x &&& 18446744073709551615 = x := by bv_decide

/-! The monad's plumbing as equations, not as definitions to unfold, and
proved by `Eq.trans rfl rfl` rather than `rfl` so that `simp` records them
as rewrites instead of definitional steps. The kernel has to re-derive every
definitional step when checking the proof, and its unfolding heuristics may
then unfold the rest of the instruction, down to an `if` on a symbolic
address, and evaluate something like `lb + 41891520` by recursion on the
literal. -/

section
variable {α β : Type}

/-- `bind` on the result of a run. -/
def andThen (r : Except Stop (α × State)) (k : α → State → Except Stop (β × State)) :
    Except Stop (β × State) :=
  match r with
  | .ok (a, s) => k a s
  | .error e => .error e

@[vexec] theorem andThen_ok (a : α) (s : State) (k : α → State → Except Stop (β × State)) :
    andThen (.ok (a, s)) k = k a s := Eq.trans rfl rfl

@[vexec] theorem run_bind (x : Exec α) (f : α → Exec β) (s : State) :
    (x >>= f).run s = andThen (x.run s) fun a s' => (f a).run s' := by
  change Except.bind (x s) _ = andThen (x s) _
  cases x s with
  | error e => rfl
  | ok p => rfl

@[vexec] theorem run_pure (a : α) (s : State) : (pure a : Exec α).run s = .ok (a, s) := Eq.trans rfl rfl

@[vexec] theorem run_get (s : State) : (get : Exec State).run s = .ok (s, s) := Eq.trans rfl rfl

@[vexec] theorem run_modify (f : State → State) (s : State) : (modify f : Exec Unit).run s = .ok ((), f s) := Eq.trans rfl rfl

@[vexec] theorem run_ite (c : Prop) [Decidable c] (x y : Exec α) (s : State) :
    (if c then x else y).run s = if c then x.run s else y.run s := by
  split <;> rfl

@[vexec] theorem run_liftPageFault (v : α) (s : State) :
    (liftPageFault (.ok v : Except PageFault α)).run s = .ok (v, s) := Eq.trans rfl rfl

end

attribute [vexec] execute arithmetic shift Exec.push Exec.pop readSource readOperand writeOperand
  readRegister writeRegister writeRegister64 store load effectiveAddress readFlag
  writeFlags holds Flags.get jumpBy jumpTo readVector writeVector vectorAddress readVector128
  writeVector128 readVector64 requireDefaultFloatControl OperandSize.mask OperandSize.width
  Nat.toUInt64_eq UInt64.reduceOfNat
  UInt64.add_assoc

end ValidateFeePayer.Proof
