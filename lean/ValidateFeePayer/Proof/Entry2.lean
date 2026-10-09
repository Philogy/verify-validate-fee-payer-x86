import ValidateFeePayer.Proof.Walk
import ValidateFeePayer.Proof.Entry

/-!
The entry state of `Pre`, as an explicit `State.mk … #v[…]` so the walk's
register lemmas fire. The six System V argument registers are their known
values; the rest are left as opaque `s.register …`.
-/

namespace ValidateFeePayer.Proof

open X86

theorem vector16_eta {α : Type} (v : Vector α 16) :
    v = #v[v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15]] := by
  apply Vector.ext
  intro i hi
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | n + 16, hi => exact absurd hi (by omega)

theorem entryAddress_eq (lb : UInt64) : entryAddress lb = lb + 0x27f3560 := rfl

/-- The entry state in explicit form. The argument registers hold their known
values; the others stay as `s.register …`, and memory and the vector/float
state stay as they are. -/
theorem entry_state {c : Call} {account metrics rent relax s} (pre : Pre c account metrics rent relax s) :
    s = State.mk (c.loadBase + 0x27f3560)
      #v[s.register .accumulator, c.errorMetrics, s.register .data, s.register .base,
         s.stackPointer, s.register .framePointer, c.account.account, c.result,
         c.rent, c.fee, s.register .r10, s.register .r11, s.register .r12, s.register .r13,
         s.register .r14, s.register .r15]
      .undefined s.vectorRegisters s.floatControl s.memory := by
  obtain ⟨ip, regs, flags, vr, fc, m⟩ := s
  have hip := pre.entered.atEntry
  have hflags := pre.abi.flags
  have h1 := pre.metricsRegister
  have h6 := pre.accountRegister
  have h7 := pre.resultRegister
  have h8 := pre.rentRegister
  have h9 := pre.feeRegister
  simp only [State.register, State.stackPointer, Register.index] at *
  rw [entryAddress_eq] at hip
  subst hip hflags
  rw [← h1, ← h6, ← h7, ← h8, ← h9]
  congr 1
  exact vector16_eta regs

end ValidateFeePayer.Proof
