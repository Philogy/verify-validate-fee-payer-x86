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
      | .error why => .faulted why s := by
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

/-- `r` succeeded with `i` and `len`, and `k` holds of them. A definition,
not a `match`: `simp` would try to reduce a `match` on `r` by evaluating it,
and so would the kernel when checking the result. -/
def DecodeThen (r : Except Fault (Instruction × Nat)) (k : Instruction → Nat → Prop) : Prop :=
  ∃ i len, r = .ok (i, len) ∧ k i len

/-- `r` succeeded with state `s'`, and `k s'` holds. -/
def ExecThen (r : Except Fault (Unit × State)) (k : State → Prop) : Prop :=
  ∃ s', r = .ok ((), s') ∧ k s'

theorem decodeThen_ok {i : Instruction} {len : Nat} {k : Instruction → Nat → Prop} :
    DecodeThen (.ok (i, len)) k = k i len :=
  propext ⟨fun ⟨_, _, h, hk⟩ => by cases h; exact hk, fun hk => ⟨_, _, rfl, hk⟩⟩

theorem execThen_ok {s : State} {k : State → Prop} : ExecThen (.ok ((), s)) k = k s :=
  propext ⟨fun ⟨_, h, hk⟩ => by cases h; exact hk, fun hk => ⟨_, rfl, hk⟩⟩

/-- One instruction: it decodes, executes, and the run finishes from there. -/
theorem Finishes.walk {lb : UInt64} {exits : Exits} {s : State} {A : UInt64} {n : Nat}
    {P : Outcome → Prop}
    (hx : CodeExits lb exits) (hc : CodeAt lb s.memory) (hip : s.instructionPointer = lb + A)
    (h : DecodeThen (decodeWith codeByte A) fun i len =>
      ExecThen ((execute i).run { s with instructionPointer := lb + A + len.toUInt64 }) fun s' =>
        Finishes exits n s' P) : Finishes exits (n + 1) s P := by
  obtain ⟨i, len, hdec, s', hexec, h⟩ := h
  exact Finishes.exec hx hc hip hdec hexec h

/-- A store that is known to succeed. -/
def wr (m : Memory) (w : Width) (a v : UInt64) : Memory :=
  ⟨Memory.stores a (littleEndianBytes w.size v) 0 m.mappings⟩

end ValidateFeePayer.Proof
