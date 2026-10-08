import ValidateFeePayer.Proof.Run
import ValidateFeePayer.Proof.DecodeTable

/-! The simp set of one symbolic step, and `vstep`. -/

namespace ValidateFeePayer.Proof

open X86 Exec

@[vexec] theorem and_allOnes (x : UInt64) : x &&& 18446744073709551615 = x := by bv_decide

attribute [vexec] execute arithmetic shift Exec.push Exec.pop readSource readOperand writeOperand
  readRegister writeRegister writeRegister64 store load liftPageFault effectiveAddress readFlag
  writeFlags holds Flags.get jumpBy jumpTo readVector writeVector vectorAddress readVector128
  writeVector128 readVector64 requireDefaultFloatControl OperandSize.mask OperandSize.width
  StateT.run bind StateT.bind get getThe MonadStateOf.get StateT.get pure StateT.pure Except.pure
  Except.bind modify modifyGet MonadStateOf.modifyGet StateT.modifyGet throw throwThe
  MonadExceptOf.throw StateT.lift
  Nat.toUInt64_eq UInt64.reduceOfNat UInt64.reduceAdd UInt64.reduceSub UInt64.reduceMul
  UInt64.add_assoc

end ValidateFeePayer.Proof
