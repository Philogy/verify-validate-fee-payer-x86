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

theorem codeByte_mapped {lb : UInt64} (hBase : ValidLoadBase lb) {x : UInt64} {b : UInt8}
    (h : codeByte x = .ok b) : ∃ mp ∈ imageMappings lb, mp.Contains (lb + x) := by
  obtain ⟨r, hr, bytes, hcode, hi, hle, -⟩ := codeByte_ok h
  have hreg : r ∈ Image.regions := List.mem_append_left _ hr
  have hbytes : r.contents.bytesAt lb = bytes := by simp [hcode, Contents.bytesAt]
  obtain ⟨hbase, hend⟩ := Region.mapping_bounds hBase hreg (loadBase := lb)
  refine ⟨r.mapping lb, List.mem_map_of_mem hreg, ?_⟩
  have hs := Contents.size_bytesAt hbytes
  have hx : (lb + x).toNat = lb.toNat + x.toNat := by
    unfold ValidLoadBase at hBase
    have := List.all_eq_true.1 regions_within_reserved r hreg
    simp only [decide_eq_true_eq, Region.endAddress, Region.size, hcode, Contents.size] at this
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  unfold Mapping.Contains Mapping.endAddress
  simp only [Region.mapping, ImageOffset.at, hbytes] at hbase hend ⊢
  rw [hx]; omega

theorem codeExits_of_pre {c : Call} {account metrics rent relax s} (pre : Pre c account metrics rent relax s) :
    CodeExits c.loadBase c.exits where
  notReturn x b hx e := by
    obtain ⟨mp, hmp, hc⟩ := codeByte_mapped pre.entered.validBase hx
    refine pre.entered.returnOutsideImage mp hmp ?_
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
    CodeAt c.loadBase s.memory := by
  obtain ⟨rest, hrest, -⟩ := pre.entered.image
  rw [hrest]; exact codeAt_image pre.entered.validBase rest.mappings

theorem dataAt_of_pre {c : Call} {account metrics rent relax s} (pre : Pre c account metrics rent relax s) :
    DataAt c.loadBase s.memory := by
  obtain ⟨rest, hrest, -⟩ := pre.entered.image
  rw [hrest]; exact dataAt_image pre.entered.validBase rest.mappings

end ValidateFeePayer.Proof
