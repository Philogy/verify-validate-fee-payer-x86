import X86.Machine
import ValidateFeePayer.Proof.Attr

/-!
The register files as literal vectors, so that a symbolic run keeps one
term per register instead of a growing chain of `set`s.
-/

namespace ValidateFeePayer.Proof

open X86

variable {α : Type} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 x : α}


@[vexec] theorem register_accumulator {ip f vr fc m} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    (State.mk ip #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] f vr fc m).register .accumulator = a0 := rfl

@[vexec] theorem set_accumulator {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set (Register.accumulator.index : Nat) x h = #v[x, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem register_counter {ip f vr fc m} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    (State.mk ip #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] f vr fc m).register .counter = a1 := rfl

@[vexec] theorem set_counter {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set (Register.counter.index : Nat) x h = #v[a0, x, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem register_data {ip f vr fc m} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    (State.mk ip #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] f vr fc m).register .data = a2 := rfl

@[vexec] theorem set_data {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set (Register.data.index : Nat) x h = #v[a0, a1, x, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem register_base {ip f vr fc m} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    (State.mk ip #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] f vr fc m).register .base = a3 := rfl

@[vexec] theorem set_base {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set (Register.base.index : Nat) x h = #v[a0, a1, a2, x, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem register_stackPointer {ip f vr fc m} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    (State.mk ip #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] f vr fc m).register .stackPointer = a4 := rfl

@[vexec] theorem set_stackPointer {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set (Register.stackPointer.index : Nat) x h = #v[a0, a1, a2, a3, x, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem register_framePointer {ip f vr fc m} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    (State.mk ip #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] f vr fc m).register .framePointer = a5 := rfl

@[vexec] theorem set_framePointer {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set (Register.framePointer.index : Nat) x h = #v[a0, a1, a2, a3, a4, x, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem register_sourceIndex {ip f vr fc m} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    (State.mk ip #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] f vr fc m).register .sourceIndex = a6 := rfl

@[vexec] theorem set_sourceIndex {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set (Register.sourceIndex.index : Nat) x h = #v[a0, a1, a2, a3, a4, a5, x, a7, a8, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem register_destinationIndex {ip f vr fc m} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    (State.mk ip #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] f vr fc m).register .destinationIndex = a7 := rfl

@[vexec] theorem set_destinationIndex {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set (Register.destinationIndex.index : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, x, a8, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem register_r8 {ip f vr fc m} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    (State.mk ip #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] f vr fc m).register .r8 = a8 := rfl

@[vexec] theorem set_r8 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set (Register.r8.index : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, a7, x, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem register_r9 {ip f vr fc m} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    (State.mk ip #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] f vr fc m).register .r9 = a9 := rfl

@[vexec] theorem set_r9 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set (Register.r9.index : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, x, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem register_r10 {ip f vr fc m} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    (State.mk ip #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] f vr fc m).register .r10 = a10 := rfl

@[vexec] theorem set_r10 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set (Register.r10.index : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, x, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem register_r11 {ip f vr fc m} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    (State.mk ip #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] f vr fc m).register .r11 = a11 := rfl

@[vexec] theorem set_r11 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set (Register.r11.index : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, x, a12, a13, a14, a15] := rfl

@[vexec] theorem register_r12 {ip f vr fc m} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    (State.mk ip #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] f vr fc m).register .r12 = a12 := rfl

@[vexec] theorem set_r12 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set (Register.r12.index : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, x, a13, a14, a15] := rfl

@[vexec] theorem register_r13 {ip f vr fc m} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    (State.mk ip #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] f vr fc m).register .r13 = a13 := rfl

@[vexec] theorem set_r13 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set (Register.r13.index : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, x, a14, a15] := rfl

@[vexec] theorem register_r14 {ip f vr fc m} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    (State.mk ip #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] f vr fc m).register .r14 = a14 := rfl

@[vexec] theorem set_r14 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set (Register.r14.index : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, x, a15] := rfl

@[vexec] theorem register_r15 {ip f vr fc m} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    (State.mk ip #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] f vr fc m).register .r15 = a15 := rfl

@[vexec] theorem set_r15 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set (Register.r15.index : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, x] := rfl

@[vexec] theorem getElem_0 :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16)[(0 : Fin 16)] = a0 := rfl

@[vexec] theorem set_0 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set ((0 : Fin 16) : Nat) x h = #v[x, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem getElem_1 :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16)[(1 : Fin 16)] = a1 := rfl

@[vexec] theorem set_1 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set ((1 : Fin 16) : Nat) x h = #v[a0, x, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem getElem_2 :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16)[(2 : Fin 16)] = a2 := rfl

@[vexec] theorem set_2 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set ((2 : Fin 16) : Nat) x h = #v[a0, a1, x, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem getElem_3 :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16)[(3 : Fin 16)] = a3 := rfl

@[vexec] theorem set_3 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set ((3 : Fin 16) : Nat) x h = #v[a0, a1, a2, x, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem getElem_4 :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16)[(4 : Fin 16)] = a4 := rfl

@[vexec] theorem set_4 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set ((4 : Fin 16) : Nat) x h = #v[a0, a1, a2, a3, x, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem getElem_5 :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16)[(5 : Fin 16)] = a5 := rfl

@[vexec] theorem set_5 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set ((5 : Fin 16) : Nat) x h = #v[a0, a1, a2, a3, a4, x, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem getElem_6 :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16)[(6 : Fin 16)] = a6 := rfl

@[vexec] theorem set_6 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set ((6 : Fin 16) : Nat) x h = #v[a0, a1, a2, a3, a4, a5, x, a7, a8, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem getElem_7 :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16)[(7 : Fin 16)] = a7 := rfl

@[vexec] theorem set_7 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set ((7 : Fin 16) : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, x, a8, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem getElem_8 :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16)[(8 : Fin 16)] = a8 := rfl

@[vexec] theorem set_8 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set ((8 : Fin 16) : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, a7, x, a9, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem getElem_9 :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16)[(9 : Fin 16)] = a9 := rfl

@[vexec] theorem set_9 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set ((9 : Fin 16) : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, x, a10, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem getElem_10 :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16)[(10 : Fin 16)] = a10 := rfl

@[vexec] theorem set_10 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set ((10 : Fin 16) : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, x, a11, a12, a13, a14, a15] := rfl

@[vexec] theorem getElem_11 :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16)[(11 : Fin 16)] = a11 := rfl

@[vexec] theorem set_11 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set ((11 : Fin 16) : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, x, a12, a13, a14, a15] := rfl

@[vexec] theorem getElem_12 :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16)[(12 : Fin 16)] = a12 := rfl

@[vexec] theorem set_12 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set ((12 : Fin 16) : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, x, a13, a14, a15] := rfl

@[vexec] theorem getElem_13 :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16)[(13 : Fin 16)] = a13 := rfl

@[vexec] theorem set_13 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set ((13 : Fin 16) : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, x, a14, a15] := rfl

@[vexec] theorem getElem_14 :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16)[(14 : Fin 16)] = a14 := rfl

@[vexec] theorem set_14 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set ((14 : Fin 16) : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, x, a15] := rfl

@[vexec] theorem getElem_15 :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16)[(15 : Fin 16)] = a15 := rfl

@[vexec] theorem set_15 {h} :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16).set ((15 : Fin 16) : Nat) x h = #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, x] := rfl

end ValidateFeePayer.Proof
