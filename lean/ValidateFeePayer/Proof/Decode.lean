import X86.Machine
import ValidateFeePayer.Code

/-!
`decode` reads only the bytes of the instruction it returns, so an
instruction decoded from the image at load base 0 (`codeByte`) decodes the
same from any memory that holds those bytes at the load base.
-/

namespace ValidateFeePayer.Proof

open X86

theorem decodeWith_go_congr {f g : UInt64 → Except PageFault UInt8} {a a' : UInt64} :
    ∀ {budget : Nat} {bytes : List UInt8} {i : Instruction} {n : Nat},
      decodeWith.go f a budget bytes = .ok (i, n) →
      bytes.length < n ∧
      ((∀ j, bytes.length ≤ j → j < n → g (a' + j.toUInt64) = f (a + j.toUInt64)) →
        decodeWith.go g a' budget bytes = .ok (i, n))
  | 0, _, _, _, h => by simp [decodeWith.go] at h
  | budget + 1, bytes, i, n, h => by
    simp only [decodeWith.go] at h ⊢
    cases hf : f (a + bytes.length.toUInt64) with
    | error e => simp [hf, bind, Except.bind, Except.mapError] at h
    | ok b =>
      simp only [hf, Except.mapError, bind, Except.bind] at h
      split at h
      · rename_i i' len hd
        split at h
        · cases h
          rename_i hlen
          refine ⟨by simp at hlen; omega, fun hg => ?_⟩
          rw [hg bytes.length (by omega) (by simp at hlen; omega), hf]
          simp only [Except.mapError, bind, Except.bind, hd, hlen, ↓reduceIte]
        · cases h
      · rename_i hd
        obtain ⟨hlt, hrec⟩ := decodeWith_go_congr h
        simp only [List.length_append, List.length_cons, List.length_nil] at hlt
        refine ⟨by omega, fun hg => ?_⟩
        rw [hg bytes.length (by omega) (by omega), hf]
        simp only [Except.mapError, bind, Except.bind, hd]
        exact hrec fun j h1 h2 => hg j (by simp at h1; omega) h2
      · cases h

theorem decodeWith_congr {f g : UInt64 → Except PageFault UInt8} {a a' : UInt64} {i : Instruction}
    {n : Nat} (h : decodeWith f a = .ok (i, n))
    (hg : ∀ j < n, g (a' + j.toUInt64) = f (a + j.toUInt64)) : decodeWith g a' = .ok (i, n) :=
  (decodeWith_go_congr h).2 fun j _ hj => hg j hj

/-- Every byte the decoder used was fetched successfully. -/
theorem decodeWith_fetched {f : UInt64 → Except PageFault UInt8} {a : UInt64} :
    ∀ {budget : Nat} {bytes : List UInt8} {i : Instruction} {n : Nat},
      decodeWith.go f a budget bytes = .ok (i, n) →
      ∀ j, bytes.length ≤ j → j < n → ∃ b, f (a + j.toUInt64) = .ok b
  | 0, _, _, _, h => by simp [decodeWith.go] at h
  | budget + 1, bytes, i, n, h => by
    simp only [decodeWith.go] at h
    cases hf : f (a + bytes.length.toUInt64) with
    | error e => simp [hf, bind, Except.bind, Except.mapError] at h
    | ok b =>
      simp only [hf, Except.mapError, bind, Except.bind] at h
      intro j h1 h2
      by_cases hj : j = bytes.length
      · subst hj; exact ⟨b, hf⟩
      split at h
      · split at h
        · cases h; rename_i hn _; simp only [List.length_append, List.length_cons, List.length_nil] at hn; omega
        · cases h
      · exact decodeWith_fetched h j (by simp; omega) h2
      · cases h

end ValidateFeePayer.Proof
