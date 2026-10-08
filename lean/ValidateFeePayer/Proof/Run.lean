import ValidateFeePayer.Proof.Decode
import ValidateFeePayer.Proof.Memory
import ValidateFeePayer.Proof.Registers

/-!
`Finishes exits n s P`: from `s`, every run with at least `n` fuel stops in
the same outcome, and it satisfies `P`. Proofs walk the code one instruction
at a time with `Finishes.exec`.
-/

namespace ValidateFeePayer.Proof

open X86

def Finishes (exits : Exits) (n : Nat) (s : State) (P : Outcome → Prop) : Prop :=
  ∃ o, P o ∧ ∀ k, run exits (n + k) s = o

theorem Finishes.mono {exits : Exits} {n n' : Nat} {s : State} {P : Outcome → Prop}
    (h : Finishes exits n s P) (hn : n ≤ n') : Finishes exits n' s P := by
  obtain ⟨o, hP, hr⟩ := h
  exact ⟨o, hP, fun k => by rw [show n' + k = n + (n' - n + k) by omega]; exact hr _⟩

theorem Finishes.imp {exits : Exits} {n : Nat} {s : State} {P Q : Outcome → Prop}
    (h : Finishes exits n s P) (hPQ : ∀ o, P o → Q o) : Finishes exits n s Q := by
  obtain ⟨o, hP, hr⟩ := h
  exact ⟨o, hPQ o hP, hr⟩

theorem Finishes.run_eq {exits : Exits} {n fuel : Nat} {s : State} {P : Outcome → Prop}
    (h : Finishes exits n s P) (hn : n ≤ fuel) : P (run exits fuel s) := by
  obtain ⟨o, hP, hr⟩ := h
  rw [show fuel = n + (fuel - n) by omega, hr]; exact hP

theorem Finishes.returned {exits : Exits} {s : State} {P : Outcome → Prop}
    (h : s.instructionPointer = exits.returnAddress) (hP : P (.returned s)) : Finishes exits 1 s P :=
  ⟨_, hP, fun k => by rw [Nat.add_comm]; simp [run, step, h]⟩

theorem Finishes.panicked {exits : Exits} {s : State} {P : Outcome → Prop}
    (hr : s.instructionPointer ≠ exits.returnAddress) (h : s.instructionPointer = exits.panicAt)
    (hP : P (.panicked s)) : Finishes exits 1 s P :=
  ⟨_, hP, fun k => by rw [h] at hr; rw [Nat.add_comm]; simp [run, step, h, hr]⟩

theorem Finishes.running {exits : Exits} {n : Nat} {s s' : State} {P : Outcome → Prop}
    (hs : step exits s = .running s') (h : Finishes exits n s' P) : Finishes exits (n + 1) s P := by
  obtain ⟨o, hP, hr⟩ := h
  exact ⟨o, hP, fun k => by rw [show n + 1 + k = (n + k) + 1 by omega]; simp [run, hs, hr]⟩

/-- Control is in the carved code at `lb`, which neither exit points into. -/
structure CodeExits (lb : UInt64) (exits : Exits) : Prop where
  notReturn : ∀ x b, codeByte x = .ok b → lb + x ≠ exits.returnAddress
  notPanic : ∀ x b, codeByte x = .ok b → lb + x ≠ exits.panicAt

theorem step_code {lb : UInt64} {exits : Exits} {s : State} {A : UInt64} {i : Instruction} {n : Nat}
    (hx : CodeExits lb exits) (hc : CodeAt lb s.memory) (hip : s.instructionPointer = lb + A)
    (hdec : decodeWith codeByte A = .ok (i, n)) :
    step exits s = match (execute i).run { s with instructionPointer := lb + A + n.toUInt64 } with
      | .ok ((), s') => .running s'
      | .error why => .stopped why s := by
  have hf := decodeWith_fetched hdec
  obtain ⟨b, hb⟩ := hf 0 (by simp) (by
    obtain ⟨hlt, -⟩ := decodeWith_go_congr (g := codeByte) (a' := A) hdec; simpa using hlt)
  rw [show A + (0 : Nat).toUInt64 = A from UInt64.add_zero A] at hb
  have hdec' : decode s.memory (lb + A) = .ok (i, n) := by
    apply decodeWith_congr hdec
    intro j hj
    obtain ⟨b', hb'⟩ := hf j (by simp) hj
    rw [hb', UInt64.add_assoc]
    exact (hc _ _ hb').1
  simp only [step, hip, hx.notReturn A b hb, hx.notPanic A b hb, ↓reduceIte, (hc A b hb).1, hdec']
  rfl

theorem Finishes.exec {lb : UInt64} {exits : Exits} {s s' : State} {A : UInt64} {i : Instruction}
    {len n : Nat} {P : Outcome → Prop}
    (hx : CodeExits lb exits) (hc : CodeAt lb s.memory) (hip : s.instructionPointer = lb + A)
    (hdec : decodeWith codeByte A = .ok (i, len))
    (hexec : (execute i).run { s with instructionPointer := lb + A + len.toUInt64 } = .ok ((), s'))
    (h : Finishes exits n s' P) : Finishes exits (n + 1) s P :=
  Finishes.running (by rw [step_code hx hc hip hdec, hexec]) h

/-- `Finishes.exec` with the instruction's effect left in the goal for `simp`. -/
theorem Finishes.step {lb : UInt64} {exits : Exits} {s : State} {A : UInt64} {i : Instruction}
    {len n : Nat} {P : Outcome → Prop}
    (hx : CodeExits lb exits) (hc : CodeAt lb s.memory) (hip : s.instructionPointer = lb + A)
    (hdec : decodeWith codeByte A = .ok (i, len))
    (h : match (execute i).run { s with instructionPointer := lb + A + len.toUInt64 } with
      | .ok ((), s') => Finishes exits n s' P
      | .error _ => False) : Finishes exits (n + 1) s P := by
  split at h
  · rename_i s' hs; exact Finishes.exec hx hc hip hdec hs h
  · exact h.elim

/-- `Finishes.step` with the decoding also left in the goal, so `simp` can
look the instruction up in `decode_table`. -/
theorem Finishes.step' {lb : UInt64} {exits : Exits} {s : State} {A : UInt64} {n : Nat}
    {P : Outcome → Prop}
    (hx : CodeExits lb exits) (hc : CodeAt lb s.memory) (hip : s.instructionPointer = lb + A)
    (h : match decodeWith codeByte A with
      | .ok (i, len) =>
        match (execute i).run { s with instructionPointer := lb + A + len.toUInt64 } with
        | .ok ((), s') => Finishes exits n s' P
        | .error _ => False
      | .error _ => False) : Finishes exits (n + 1) s P := by
  split at h
  · rename_i i len hdec; exact Finishes.step hx hc hip hdec h
  · exact h.elim

/-- A store that is known to succeed. -/
def wr (m : Memory) (w : Width) (a v : UInt64) : Memory :=
  ⟨Memory.stores a (littleEndianBytes w.size v) 0 m.mappings⟩

theorem Stored.write_wr {m0 m : Memory} {ws : List (UInt64 × Nat)} {w : Width} {a v b : UInt64} {n : Nat}
    (h : Stored m0 m ws) {bs : List UInt8} (hw : m0.bytes .write b n = .ok bs)
    (hin : ∀ i < w.size, ∃ j < n, a + i.toUInt64 = b + j.toUInt64) :
    m.write w a v = .ok (wr m w a v) :=
  h.write_ok hw hin

end ValidateFeePayer.Proof
