import ValidateFeePayer.Proof.Vexec
import ValidateFeePayer.Proof.Call

/-!
The entry state of `Pre` meets the hypotheses of the symbolic-execution
framework: control starts in the carved code, neither exit points into it,
and the image reads and fetches as in the binary.
-/

namespace ValidateFeePayer.Proof

open X86 Memory

theorem codeByte_in_regions {x : UInt64} {b : UInt8} (h : codeByte x = .ok b) :
    ∃ r ∈ Image.regions, r.Contains x := by
  obtain ⟨r, hr, bytes, hcode, hi, hle, -⟩ := codeByte_ok h
  refine ⟨r, List.mem_append_left _ hr, hle, ?_⟩
  simp only [Region.endAddress, Region.size, hcode, Contents.size]
  omega

theorem codeByte_block {lb : UInt64} (hBase : ValidLoadBase lb) {x : UInt64} {b : UInt8}
    (h : codeByte x = .ok b) : ∃ r ∈ Image.regions, (r.block lb).Contains (lb + x) := by
  obtain ⟨r, hr, bytes, hcode, hi, hle, -⟩ := codeByte_ok h
  have hreg : r ∈ Image.regions := List.mem_append_left _ hr
  refine ⟨r, hreg, ?_⟩
  have hsize : r.size = bytes.size := by simp [Region.size, hcode, Contents.size]
  have hat := Region.toNat_at hBase hreg (i := 0) (by omega)
  simp only [Nat.toUInt64_eq, UInt64.reduceOfNat, UInt64.add_zero, Nat.add_zero] at hat
  have hx : (lb + x).toNat = lb.toNat + x.toNat := by
    unfold ValidLoadBase at hBase
    have hle := List.all_eq_true.1 regions_within_reserved r hreg
    simp only [decide_eq_true_eq] at hle
    unfold Region.endAddress at hle
    have : Image.reservedEnd = 0x3a423d4 := rfl
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  unfold Abi.Block.Contains Abi.Block.endAddress Region.block
  simp only [hat, hx, hsize]
  omega

theorem codeExits_of_pre {c : Call} {account metrics rent relax s} (pre : Pre c account metrics rent relax s) :
    CodeExits c.loadBase c.exits where
  notReturn x b hx e := by
    obtain ⟨r, hr, hc⟩ := codeByte_block pre.loaded.validBase hx
    refine pre.called.returnOutsideImage r hr ?_
    have : c.returnAddress = c.exits.returnAddress := rfl
    rw [this, ← e]; exact hc
  notPanic x b hx e := by
    obtain ⟨r, hr, hc⟩ := codeByte_in_regions hx
    have := List.all_eq_true.1 panic_unmapped r hr
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
    have hxp : x = Image.panicEntry.off := by
      have he : c.loadBase + x = c.loadBase + Image.panicEntry.off := by
        simpa [Call.exits, exits, panicAddress, ImageOffset.at] using e
      exact (UInt64.add_right_inj c.loadBase).mp he
    exact absurd (hxp ▸ hc) this

theorem codeAt_of_pre {c : Call} {account metrics rent relax s} (pre : Pre c account metrics rent relax s) :
    CodeAt c.loadBase s.memory :=
  codeAt_of_loaded pre.loaded

theorem dataAt_of_pre {c : Call} {account metrics rent relax s} (pre : Pre c account metrics rent relax s) :
    DataAt c.loadBase s.memory :=
  dataAt_of_loaded pre.loaded

end ValidateFeePayer.Proof
