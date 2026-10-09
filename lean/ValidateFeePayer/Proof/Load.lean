import X86.MemoryFacts
import ValidateFeePayer.Checks
import ValidateFeePayer.Proof.Call

/-!
From the caller's memory to the entry state's: loading the image only adds
mappings inside the reserved span, which the caller left free, so every byte
the caller could access reads the same afterwards. The hypotheses about the
caller's state therefore hold of the entry state.
-/

namespace ValidateFeePayer.Proof

open X86 Memory

/-- Every access that succeeds in `m` succeeds in `m'` with the same byte. -/
def Extends (m m' : Memory) : Prop := ∀ acc a b, m.byte acc a = .ok b → m'.byte acc a = .ok b

theorem mapM_ok_of_ok {α β ε : Type} {f g : α → Except ε β} (hfg : ∀ x b, f x = .ok b → g x = .ok b) :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → l.mapM g = .ok r
  | [], _, h => h
  | y :: l, r, h => by
    simp only [List.mapM_cons] at h ⊢
    cases hy : f y with
    | error e => rw [hy] at h; cases h
    | ok b =>
      rw [hy] at h
      rw [hfg y b hy]
      cases hl : l.mapM f with
      | error e => rw [hl] at h; cases h
      | ok bs =>
        rw [hl] at h
        rw [mapM_ok_of_ok hfg hl]
        exact h

namespace Extends

variable {m m' : Memory} (h : Extends m m')
include h

theorem bytes {acc a n bs} (hb : m.bytes acc a n = .ok bs) : m'.bytes acc a n = .ok bs :=
  mapM_ok_of_ok (fun _ b => h acc _ b) hb

theorem holds {w a v} (hv : m.Holds w a v) : m'.Holds w a v := by
  unfold Memory.Holds Memory.read at *
  cases hb : m.bytes .read a w.byteCount with
  | error e => rw [hb] at hv; cases hv
  | ok bs => rw [h.bytes hb]; rw [hb] at hv; exact hv

theorem holdsBytes {a bs} (hv : m.HoldsBytes a bs) : m'.HoldsBytes a bs := h.bytes hv

theorem writable {a n} (hw : m.Writable a n) : m'.Writable a n := fun i hi =>
  let ⟨b, hb⟩ := hw i hi; ⟨b, h _ _ _ hb⟩

end Extends

theorem contains_of_go_ok {acc : Access} {a : UInt64} {b : UInt8} :
    ∀ {ms : List Mapping}, byte.go acc a ms = .ok b → ∃ mp ∈ ms, mp.Contains a
  | [], h => by simp [byte.go] at h
  | mp :: ms, h => by
    simp only [byte.go] at h
    by_cases hc : mp.Contains a
    · exact ⟨mp, List.mem_cons_self .., hc⟩
    · simp only [hc, ↓reduceDIte] at h
      obtain ⟨mp', hm, hc'⟩ := contains_of_go_ok h
      exact ⟨mp', List.mem_cons_of_mem _ hm, hc'⟩

theorem go_append_of_not_contains {acc : Access} {a : UInt64} :
    ∀ {ms : List Mapping} (rest : List Mapping), (∀ mp ∈ ms, ¬ mp.Contains a) →
      byte.go acc a (ms ++ rest) = byte.go acc a rest
  | [], _, _ => rfl
  | mp :: ms, rest, h => by
    simp only [List.cons_append, byte.go]
    simp only [h mp (List.mem_cons_self ..), ↓reduceDIte]
    exact go_append_of_not_contains rest fun mp' hm => h mp' (List.mem_cons_of_mem _ hm)

theorem reservedSpan_contains {lb : UInt64} (hBase : ValidLoadBase lb) {mp : Mapping}
    (hmp : mp ∈ imageMappings lb) {a : UInt64} (hc : mp.Contains a) : (reservedSpan lb).Contains a := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hmp
  obtain ⟨hbase, hend⟩ := Region.mapping_bounds hBase hr
  have hle := List.all_eq_true.1 regions_within_reserved r hr
  simp only [decide_eq_true_eq] at hle
  have h0 : Image.reservedStart.off.toNat = 0 := rfl
  have hstart : (Image.reservedStart.at lb).toNat = lb.toNat + Image.reservedStart.off.toNat := by
    simp only [ImageOffset.at, UInt64.toNat_add, h0, Nat.add_zero]
    exact Nat.mod_eq_of_lt lb.toNat_lt
  have : Image.reservedStart.off.toNat ≤ r.address.off.toNat := hle.1
  unfold Mapping.Contains at hc
  unfold Abi.Block.Contains Abi.Block.endAddress reservedSpan
  simp only [hstart]
  omega

/-- Loading the image keeps every access to the caller's memory as it was. -/
theorem extends_load {lb : UInt64} (hBase : ValidLoadBase lb) {m : Memory} (hfree : SpanFree lb m) :
    Extends m (load lb m) := by
  intro acc a b h
  obtain ⟨mp, hm, hc⟩ := contains_of_go_ok h
  have hout : ¬ (reservedSpan lb).Contains a := by
    have := hfree mp hm
    simp only [Abi.Block.Apart, Abi.Block.endAddress] at this
    unfold Mapping.Contains Mapping.endAddress at hc
    unfold Abi.Block.Contains Abi.Block.endAddress
    omega
  simp only [byte, load]
  rw [go_append_of_not_contains _ fun mp' hm' hc' => hout (reservedSpan_contains hBase hm' hc')]
  exact h

section Enter

variable {lb : UInt64} {s : State}

theorem enter_memory : (enter lb s).memory = load lb s.memory := by delta enter; exact Eq.refl _
theorem enter_instructionPointer : (enter lb s).rip = entryAddress lb := by delta enter; exact Eq.refl _
theorem enter_registers : (enter lb s).registers = s.registers := by delta enter; exact Eq.refl _
theorem enter_register (r : Register) : (enter lb s).register r = s.register r := by
  unfold State.register; rw [enter_registers]
theorem enter_stackPointer : (enter lb s).rsp = s.rsp := enter_register _
theorem enter_rflags : (enter lb s).rflags = s.rflags := by delta enter; exact Eq.refl _
theorem enter_floatControl : (enter lb s).mxcsr = s.mxcsr := by delta enter; exact Eq.refl _

theorem args_enter : args (enter lb s) = args s := by
  simp only [args, Abi.ValidateFeePayerEntry.of, Abi.SysV.indirectResult, Abi.SysV.argument,
    Abi.SysV.stackArgument, enter_register, enter_stackPointer]

theorem objects_enter {heap : AccountHeap} {n : Nat} : objects lb (enter lb s) heap n = objects lb s heap n := by
  simp only [objects, args_enter, enter_stackPointer]

theorem writes_enter : writes (enter lb s) = writes s := by
  simp only [writes, args_enter, enter_stackPointer]

theorem accountAt_enter {heap : AccountHeap} : accountAt (enter lb s) heap = accountAt s heap := by
  simp only [accountAt, args_enter]

end Enter

end ValidateFeePayer.Proof
