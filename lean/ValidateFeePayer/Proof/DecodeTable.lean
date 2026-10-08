import ValidateFeePayer.Code
import ValidateFeePayer.Proof.Attr

/-! Generated from `listing`: the instruction at each address, decoded from the image at load base 0. -/

namespace ValidateFeePayer.Proof

open X86

deriving instance DecidableEq for Except

@[decode_table] theorem decode_27f3560 :
    decodeWith codeByte 0x27f3560 = .ok (Instruction.push (Source.operand (RegisterOrMemory.register (Register.framePointer))), 1) := by
  decide +kernel

@[decode_table] theorem decode_27f3561 :
    decodeWith codeByte 0x27f3561 = .ok (Instruction.push (Source.operand (RegisterOrMemory.register (Register.r15))), 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3563 :
    decodeWith codeByte 0x27f3563 = .ok (Instruction.push (Source.operand (RegisterOrMemory.register (Register.r14))), 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3565 :
    decodeWith codeByte 0x27f3565 = .ok (Instruction.push (Source.operand (RegisterOrMemory.register (Register.r12))), 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3567 :
    decodeWith codeByte 0x27f3567 = .ok (Instruction.push (Source.operand (RegisterOrMemory.register (Register.base))), 1) := by
  decide +kernel

@[decode_table] theorem decode_27f3568 :
    decodeWith codeByte 0x27f3568 = .ok (Instruction.arithmetic (ArithmeticOp.subtract) (OperandSize.bits64) (RegisterOrMemory.register (Register.stackPointer)) (Source.immediate 16), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f356c :
    decodeWith codeByte 0x27f356c = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.accumulator)) (Source.operand (RegisterOrMemory.register (Register.sourceIndex))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f356f :
    decodeWith codeByte 0x27f356f = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.sourceIndex)) (Source.operand (RegisterOrMemory.memory (Address.baseIndex (some (Register.sourceIndex)) none 8))), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3573 :
    decodeWith codeByte 0x27f3573 = .ok (Instruction.arithmetic (ArithmeticOp.testBits) (OperandSize.bits64) (RegisterOrMemory.register (Register.sourceIndex)) (Source.operand (RegisterOrMemory.register (Register.sourceIndex))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3576 :
    decodeWith codeByte 0x27f3576 = .ok (Instruction.jumpIf (Condition.equal) 75, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3578 :
    decodeWith codeByte 0x27f3578 = .ok (Instruction.moveVector (VectorMove.integerUnaligned) (VectorOrMemory.register 0) (VectorOrMemory.memory (Address.relativeToNextInstruction 18446744073670744800)), 8) := by
  decide +kernel

@[decode_table] theorem decode_27f3580 :
    decodeWith codeByte 0x27f3580 = .ok (Instruction.moveVector (VectorMove.integerUnaligned) (VectorOrMemory.register 1) (VectorOrMemory.memory (Address.baseIndex (some (Register.accumulator)) none 16)), 5) := by
  decide +kernel

@[decode_table] theorem decode_27f3585 :
    decodeWith codeByte 0x27f3585 = .ok (Instruction.vectorBitwise (VectorBitwiseOp.xor) (VectorDomain.integer) 1 (VectorOrMemory.register 0), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3589 :
    decodeWith codeByte 0x27f3589 = .ok (Instruction.moveVector (VectorMove.integerUnaligned) (VectorOrMemory.register 0) (VectorOrMemory.memory (Address.baseIndex (some (Register.accumulator)) none 32)), 5) := by
  decide +kernel

@[decode_table] theorem decode_27f358e :
    decodeWith codeByte 0x27f358e = .ok (Instruction.moveVector (VectorMove.integerUnaligned) (VectorOrMemory.register 2) (VectorOrMemory.memory (Address.relativeToNextInstruction 18446744073670744794)), 8) := by
  decide +kernel

@[decode_table] theorem decode_27f3596 :
    decodeWith codeByte 0x27f3596 = .ok (Instruction.vectorBitwise (VectorBitwiseOp.xor) (VectorDomain.integer) 2 (VectorOrMemory.register 0), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f359a :
    decodeWith codeByte 0x27f359a = .ok (Instruction.vectorBitwise (VectorBitwiseOp.or) (VectorDomain.integer) 2 (VectorOrMemory.register 1), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f359e :
    decodeWith codeByte 0x27f359e = .ok (Instruction.testVectorBits 2 (VectorOrMemory.register 2), 5) := by
  decide +kernel

@[decode_table] theorem decode_27f35a3 :
    decodeWith codeByte 0x27f35a3 = .ok (Instruction.jumpIf (Condition.equal) 74, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f35a5 :
    decodeWith codeByte 0x27f35a5 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.accumulator)) (Source.operand (RegisterOrMemory.memory (Address.baseIndex (some (Register.counter)) none 88))), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f35a9 :
    decodeWith codeByte 0x27f35a9 = .ok (Instruction.increment (OperandSize.bits64) (RegisterOrMemory.register (Register.accumulator)), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f35ac :
    decodeWith codeByte 0x27f35ac = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.data)) (Source.immediate 18446744073709551615), 7) := by
  decide +kernel

@[decode_table] theorem decode_27f35b3 :
    decodeWith codeByte 0x27f35b3 = .ok (Instruction.moveIf (Condition.notEqual) (OperandSize.bits64) (Register.data) (RegisterOrMemory.register (Register.accumulator)), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f35b7 :
    decodeWith codeByte 0x27f35b7 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.memory (Address.baseIndex (some (Register.counter)) none 88)) (Source.operand (RegisterOrMemory.register (Register.data))), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f35bb :
    decodeWith codeByte 0x27f35bb = .ok (Instruction.move (OperandSize.bits32) (RegisterOrMemory.memory (Address.baseIndex (some (Register.destinationIndex)) none 0)) (Source.immediate 60), 6) := by
  decide +kernel

@[decode_table] theorem decode_27f35c1 :
    decodeWith codeByte 0x27f35c1 = .ok (Instruction.jump 28, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f35c3 :
    decodeWith codeByte 0x27f35c3 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.accumulator)) (Source.operand (RegisterOrMemory.memory (Address.baseIndex (some (Register.counter)) none 32))), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f35c7 :
    decodeWith codeByte 0x27f35c7 = .ok (Instruction.increment (OperandSize.bits64) (RegisterOrMemory.register (Register.accumulator)), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f35ca :
    decodeWith codeByte 0x27f35ca = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.data)) (Source.immediate 18446744073709551615), 7) := by
  decide +kernel

@[decode_table] theorem decode_27f35d1 :
    decodeWith codeByte 0x27f35d1 = .ok (Instruction.moveIf (Condition.notEqual) (OperandSize.bits64) (Register.data) (RegisterOrMemory.register (Register.accumulator)), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f35d5 :
    decodeWith codeByte 0x27f35d5 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.memory (Address.baseIndex (some (Register.counter)) none 32)) (Source.operand (RegisterOrMemory.register (Register.data))), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f35d9 :
    decodeWith codeByte 0x27f35d9 = .ok (Instruction.move (OperandSize.bits32) (RegisterOrMemory.memory (Address.baseIndex (some (Register.destinationIndex)) none 0)) (Source.immediate 57), 6) := by
  decide +kernel

@[decode_table] theorem decode_27f35df :
    decodeWith codeByte 0x27f35df = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.accumulator)) (Source.operand (RegisterOrMemory.register (Register.destinationIndex))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f35e2 :
    decodeWith codeByte 0x27f35e2 = .ok (Instruction.arithmetic (ArithmeticOp.add) (OperandSize.bits64) (RegisterOrMemory.register (Register.stackPointer)) (Source.immediate 16), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f35e6 :
    decodeWith codeByte 0x27f35e6 = .ok (Instruction.pop (RegisterOrMemory.register (Register.base)), 1) := by
  decide +kernel

@[decode_table] theorem decode_27f35e7 :
    decodeWith codeByte 0x27f35e7 = .ok (Instruction.pop (RegisterOrMemory.register (Register.r12)), 2) := by
  decide +kernel

@[decode_table] theorem decode_27f35e9 :
    decodeWith codeByte 0x27f35e9 = .ok (Instruction.pop (RegisterOrMemory.register (Register.r14)), 2) := by
  decide +kernel

@[decode_table] theorem decode_27f35eb :
    decodeWith codeByte 0x27f35eb = .ok (Instruction.pop (RegisterOrMemory.register (Register.r15)), 2) := by
  decide +kernel

@[decode_table] theorem decode_27f35ed :
    decodeWith codeByte 0x27f35ed = .ok (Instruction.pop (RegisterOrMemory.register (Register.framePointer)), 1) := by
  decide +kernel

@[decode_table] theorem decode_27f35ee :
    decodeWith codeByte 0x27f35ee = .ok (Instruction.returnToCaller, 1) := by
  decide +kernel

@[decode_table] theorem decode_27f35ef :
    decodeWith codeByte 0x27f35ef = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.base)) (Source.operand (RegisterOrMemory.memory (Address.baseIndex (some (Register.accumulator)) none 0))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f35f2 :
    decodeWith codeByte 0x27f35f2 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.r10)) (Source.operand (RegisterOrMemory.memory (Address.baseIndex (some (Register.base)) none 32))), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f35f6 :
    decodeWith codeByte 0x27f35f6 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.r11)) (Source.operand (RegisterOrMemory.register (Register.r10))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f35f9 :
    decodeWith codeByte 0x27f35f9 = .ok (Instruction.arithmetic (ArithmeticOp.testBits) (OperandSize.bits64) (RegisterOrMemory.register (Register.r10)) (Source.operand (RegisterOrMemory.register (Register.r10))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f35fc :
    decodeWith codeByte 0x27f35fc = .ok (Instruction.jumpIf (Condition.equal) 270, 6) := by
  decide +kernel

@[decode_table] theorem decode_27f3602 :
    decodeWith codeByte 0x27f3602 = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.r10)) (Source.immediate 80), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3606 :
    decodeWith codeByte 0x27f3606 = .ok (Instruction.jumpIf (Condition.notEqual) 18446744073709551517, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3608 :
    decodeWith codeByte 0x27f3608 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.r11)) (Source.operand (RegisterOrMemory.memory (Address.baseIndex (some (Register.base)) none 24))), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f360c :
    decodeWith codeByte 0x27f360c = .ok (Instruction.move (OperandSize.bits32) (RegisterOrMemory.register (Register.base)) (Source.operand (RegisterOrMemory.memory (Address.baseIndex (some (Register.r11)) none 0))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f360f :
    decodeWith codeByte 0x27f360f = .ok (Instruction.move (OperandSize.bits32) (RegisterOrMemory.register (Register.r11)) (Source.operand (RegisterOrMemory.memory (Address.baseIndex (some (Register.r11)) none 4))), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3613 :
    decodeWith codeByte 0x27f3613 = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits32) (RegisterOrMemory.register (Register.base)) (Source.immediate 1), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3616 :
    decodeWith codeByte 0x27f3616 = .ok (Instruction.jumpIf (Condition.equal) 4, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3618 :
    decodeWith codeByte 0x27f3618 = .ok (Instruction.arithmetic (ArithmeticOp.testBits) (OperandSize.bits32) (RegisterOrMemory.register (Register.base)) (Source.operand (RegisterOrMemory.register (Register.base))), 2) := by
  decide +kernel

@[decode_table] theorem decode_27f361a :
    decodeWith codeByte 0x27f361a = .ok (Instruction.jumpIf (Condition.notEqual) 18446744073709551497, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f361c :
    decodeWith codeByte 0x27f361c = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits32) (RegisterOrMemory.register (Register.r11)) (Source.immediate 1), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3620 :
    decodeWith codeByte 0x27f3620 = .ok (Instruction.jumpIf (Condition.notEqual) 18446744073709551491, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3622 :
    decodeWith codeByte 0x27f3622 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.r11)) (Source.operand (RegisterOrMemory.memory (Address.baseIndex (some (Register.r8)) none 0))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3625 :
    decodeWith codeByte 0x27f3625 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.base)) (Source.operand (RegisterOrMemory.memory (Address.baseIndex (some (Register.r8)) none 8))), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3629 :
    decodeWith codeByte 0x27f3629 = .ok (Instruction.moveImmediate64 (Register.r14) 4611686018427387904, 10) := by
  decide +kernel

@[decode_table] theorem decode_27f3633 :
    decodeWith codeByte 0x27f3633 = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.base)) (Source.operand (RegisterOrMemory.register (Register.r14))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3636 :
    decodeWith codeByte 0x27f3636 = .ok (Instruction.setIf (Condition.equal) (RegisterOrMemory.register (Register.framePointer)), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f363a :
    decodeWith codeByte 0x27f363a = .ok (Instruction.moveImmediate64 (Register.r15) 879598564933, 10) := by
  decide +kernel

@[decode_table] theorem decode_27f3644 :
    decodeWith codeByte 0x27f3644 = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.r11)) (Source.operand (RegisterOrMemory.register (Register.r15))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3647 :
    decodeWith codeByte 0x27f3647 = .ok (Instruction.jumpIf (Condition.above) 2, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3649 :
    decodeWith codeByte 0x27f3649 = .ok (Instruction.arithmetic (ArithmeticOp.xor) (OperandSize.bits32) (RegisterOrMemory.register (Register.framePointer)) (Source.operand (RegisterOrMemory.register (Register.framePointer))), 2) := by
  decide +kernel

@[decode_table] theorem decode_27f364b :
    decodeWith codeByte 0x27f364b = .ok (Instruction.arithmetic (ArithmeticOp.testBits) (OperandSize.bits8) (RegisterOrMemory.register (Register.framePointer)) (Source.operand (RegisterOrMemory.register (Register.framePointer))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f364e :
    decodeWith codeByte 0x27f364e = .ok (Instruction.jumpIf (Condition.notEqual) 291, 6) := by
  decide +kernel

@[decode_table] theorem decode_27f3654 :
    decodeWith codeByte 0x27f3654 = .ok (Instruction.moveImmediate64 (Register.r15) 4607182418800017408, 10) := by
  decide +kernel

@[decode_table] theorem decode_27f365e :
    decodeWith codeByte 0x27f365e = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.base)) (Source.operand (RegisterOrMemory.register (Register.r15))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3661 :
    decodeWith codeByte 0x27f3661 = .ok (Instruction.setIf (Condition.equal) (RegisterOrMemory.register (Register.framePointer)), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3665 :
    decodeWith codeByte 0x27f3665 = .ok (Instruction.moveImmediate64 (Register.r12) 1759197129867, 10) := by
  decide +kernel

@[decode_table] theorem decode_27f366f :
    decodeWith codeByte 0x27f366f = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.r11)) (Source.operand (RegisterOrMemory.register (Register.r12))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3672 :
    decodeWith codeByte 0x27f3672 = .ok (Instruction.jumpIf (Condition.above) 2, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3674 :
    decodeWith codeByte 0x27f3674 = .ok (Instruction.arithmetic (ArithmeticOp.xor) (OperandSize.bits32) (RegisterOrMemory.register (Register.framePointer)) (Source.operand (RegisterOrMemory.register (Register.framePointer))), 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3676 :
    decodeWith codeByte 0x27f3676 = .ok (Instruction.arithmetic (ArithmeticOp.testBits) (OperandSize.bits8) (RegisterOrMemory.register (Register.framePointer)) (Source.operand (RegisterOrMemory.register (Register.framePointer))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3679 :
    decodeWith codeByte 0x27f3679 = .ok (Instruction.jumpIf (Condition.notEqual) 248, 6) := by
  decide +kernel

@[decode_table] theorem decode_27f367f :
    decodeWith codeByte 0x27f367f = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.base)) (Source.operand (RegisterOrMemory.register (Register.r14))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3682 :
    decodeWith codeByte 0x27f3682 = .ok (Instruction.jumpIf (Condition.equal) 14, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3684 :
    decodeWith codeByte 0x27f3684 = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.base)) (Source.operand (RegisterOrMemory.register (Register.r15))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3687 :
    decodeWith codeByte 0x27f3687 = .ok (Instruction.jumpIf (Condition.notEqual) 18, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3689 :
    decodeWith codeByte 0x27f3689 = .ok (Instruction.multiplySigned (OperandSize.bits64) (Register.r11) (RegisterOrMemory.register (Register.r11)) (some 208), 7) := by
  decide +kernel

@[decode_table] theorem decode_27f3690 :
    decodeWith codeByte 0x27f3690 = .ok (Instruction.jump 126, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3692 :
    decodeWith codeByte 0x27f3692 = .ok (Instruction.multiplySigned (OperandSize.bits64) (Register.r11) (RegisterOrMemory.register (Register.r11)) (some 416), 7) := by
  decide +kernel

@[decode_table] theorem decode_27f3699 :
    decodeWith codeByte 0x27f3699 = .ok (Instruction.jump 117, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f369b :
    decodeWith codeByte 0x27f369b = .ok (Instruction.moveIntegerToVector (OperandSize.bits64) 0 (RegisterOrMemory.register (Register.base)), 5) := by
  decide +kernel

@[decode_table] theorem decode_27f36a0 :
    decodeWith codeByte 0x27f36a0 = .ok (Instruction.multiplySigned (OperandSize.bits64) (Register.r11) (RegisterOrMemory.register (Register.r11)) (some 208), 7) := by
  decide +kernel

@[decode_table] theorem decode_27f36a7 :
    decodeWith codeByte 0x27f36a7 = .ok (Instruction.moveIntegerToVector (OperandSize.bits64) 1 (RegisterOrMemory.register (Register.r11)), 5) := by
  decide +kernel

@[decode_table] theorem decode_27f36ac :
    decodeWith codeByte 0x27f36ac = .ok (Instruction.interleaveLow32 1 (VectorOrMemory.memory (Address.relativeToNextInstruction 18446744073670703228)), 8) := by
  decide +kernel

@[decode_table] theorem decode_27f36b4 :
    decodeWith codeByte 0x27f36b4 = .ok (Instruction.packedDouble (DoubleOp.subtract) 1 (VectorOrMemory.memory (Address.relativeToNextInstruction 18446744073670697700)), 8) := by
  decide +kernel

@[decode_table] theorem decode_27f36bc :
    decodeWith codeByte 0x27f36bc = .ok (Instruction.moveVector (VectorMove.doubleAligned) (VectorOrMemory.register 2) (VectorOrMemory.register 1), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f36c0 :
    decodeWith codeByte 0x27f36c0 = .ok (Instruction.interleaveHighDoubles 2 (VectorOrMemory.register 1), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f36c4 :
    decodeWith codeByte 0x27f36c4 = .ok (Instruction.scalarDouble (DoubleOp.add) 2 (VectorOrMemory.register 1), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f36c8 :
    decodeWith codeByte 0x27f36c8 = .ok (Instruction.scalarDouble (DoubleOp.multiply) 2 (VectorOrMemory.register 0), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f36cc :
    decodeWith codeByte 0x27f36cc = .ok (Instruction.truncateDoubleToInt64 (Register.r11) (VectorOrMemory.register 2), 5) := by
  decide +kernel

@[decode_table] theorem decode_27f36d1 :
    decodeWith codeByte 0x27f36d1 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.base)) (Source.operand (RegisterOrMemory.register (Register.r11))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f36d4 :
    decodeWith codeByte 0x27f36d4 = .ok (Instruction.shift (ShiftOp.rightArithmetic) (OperandSize.bits64) (RegisterOrMemory.register (Register.base)) (ShiftCount.immediate 63), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f36d8 :
    decodeWith codeByte 0x27f36d8 = .ok (Instruction.moveVector (VectorMove.doubleAligned) (VectorOrMemory.register 0) (VectorOrMemory.register 2), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f36dc :
    decodeWith codeByte 0x27f36dc = .ok (Instruction.scalarDouble (DoubleOp.subtract) 0 (VectorOrMemory.memory (Address.relativeToNextInstruction 18446744073670764612)), 8) := by
  decide +kernel

@[decode_table] theorem decode_27f36e4 :
    decodeWith codeByte 0x27f36e4 = .ok (Instruction.truncateDoubleToInt64 (Register.r14) (VectorOrMemory.register 0), 5) := by
  decide +kernel

@[decode_table] theorem decode_27f36e9 :
    decodeWith codeByte 0x27f36e9 = .ok (Instruction.arithmetic (ArithmeticOp.and) (OperandSize.bits64) (RegisterOrMemory.register (Register.r14)) (Source.operand (RegisterOrMemory.register (Register.base))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f36ec :
    decodeWith codeByte 0x27f36ec = .ok (Instruction.arithmetic (ArithmeticOp.or) (OperandSize.bits64) (RegisterOrMemory.register (Register.r14)) (Source.operand (RegisterOrMemory.register (Register.r11))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f36ef :
    decodeWith codeByte 0x27f36ef = .ok (Instruction.arithmetic (ArithmeticOp.xor) (OperandSize.bits32) (RegisterOrMemory.register (Register.base)) (Source.operand (RegisterOrMemory.register (Register.base))), 2) := by
  decide +kernel

@[decode_table] theorem decode_27f36f1 :
    decodeWith codeByte 0x27f36f1 = .ok (Instruction.vectorBitwise (VectorBitwiseOp.xor) (VectorDomain.double) 0 (VectorOrMemory.register 0), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f36f5 :
    decodeWith codeByte 0x27f36f5 = .ok (Instruction.compareDoubles 2 (VectorOrMemory.register 0), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f36f9 :
    decodeWith codeByte 0x27f36f9 = .ok (Instruction.moveIf (Condition.aboveOrEqual) (OperandSize.bits64) (Register.base) (RegisterOrMemory.register (Register.r14)), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f36fd :
    decodeWith codeByte 0x27f36fd = .ok (Instruction.compareDoubles 2 (VectorOrMemory.memory (Address.relativeToNextInstruction 18446744073670755443)), 8) := by
  decide +kernel

@[decode_table] theorem decode_27f3705 :
    decodeWith codeByte 0x27f3705 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.r11)) (Source.immediate 18446744073709551615), 7) := by
  decide +kernel

@[decode_table] theorem decode_27f370c :
    decodeWith codeByte 0x27f370c = .ok (Instruction.moveIf (Condition.belowOrEqual) (OperandSize.bits64) (Register.r11) (RegisterOrMemory.register (Register.base)), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3710 :
    decodeWith codeByte 0x27f3710 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.base)) (Source.operand (RegisterOrMemory.register (Register.sourceIndex))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3713 :
    decodeWith codeByte 0x27f3713 = .ok (Instruction.arithmetic (ArithmeticOp.subtract) (OperandSize.bits64) (RegisterOrMemory.register (Register.base)) (Source.operand (RegisterOrMemory.register (Register.r11))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3716 :
    decodeWith codeByte 0x27f3716 = .ok (Instruction.setIf (Condition.below) (RegisterOrMemory.register (Register.r11)), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f371a :
    decodeWith codeByte 0x27f371a = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.base)) (Source.operand (RegisterOrMemory.register (Register.r9))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f371d :
    decodeWith codeByte 0x27f371d = .ok (Instruction.setIf (Condition.below) (RegisterOrMemory.register (Register.base)), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3720 :
    decodeWith codeByte 0x27f3720 = .ok (Instruction.arithmetic (ArithmeticOp.or) (OperandSize.bits8) (RegisterOrMemory.register (Register.base)) (Source.operand (RegisterOrMemory.register (Register.r11))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3723 :
    decodeWith codeByte 0x27f3723 = .ok (Instruction.jumpIf (Condition.equal) 33, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3725 :
    decodeWith codeByte 0x27f3725 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.accumulator)) (Source.operand (RegisterOrMemory.memory (Address.baseIndex (some (Register.counter)) none 80))), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3729 :
    decodeWith codeByte 0x27f3729 = .ok (Instruction.increment (OperandSize.bits64) (RegisterOrMemory.register (Register.accumulator)), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f372c :
    decodeWith codeByte 0x27f372c = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.data)) (Source.immediate 18446744073709551615), 7) := by
  decide +kernel

@[decode_table] theorem decode_27f3733 :
    decodeWith codeByte 0x27f3733 = .ok (Instruction.moveIf (Condition.notEqual) (OperandSize.bits64) (Register.data) (RegisterOrMemory.register (Register.accumulator)), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3737 :
    decodeWith codeByte 0x27f3737 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.memory (Address.baseIndex (some (Register.counter)) none 80)) (Source.operand (RegisterOrMemory.register (Register.data))), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f373b :
    decodeWith codeByte 0x27f373b = .ok (Instruction.move (OperandSize.bits32) (RegisterOrMemory.memory (Address.baseIndex (some (Register.destinationIndex)) none 0)) (Source.immediate 59), 6) := by
  decide +kernel

@[decode_table] theorem decode_27f3741 :
    decodeWith codeByte 0x27f3741 = .ok (Instruction.jump 18446744073709551257, 5) := by
  decide +kernel

@[decode_table] theorem decode_27f3746 :
    decodeWith codeByte 0x27f3746 = .ok (Instruction.moveZeroExtend (OperandSize.bits32) (Register.r11) (OperandSize.bits8) (RegisterOrMemory.memory (Address.baseIndex (some (Register.stackPointer)) none 64)), 6) := by
  decide +kernel

@[decode_table] theorem decode_27f374c :
    decodeWith codeByte 0x27f374c = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.counter)) (Source.operand (RegisterOrMemory.register (Register.sourceIndex))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f374f :
    decodeWith codeByte 0x27f374f = .ok (Instruction.arithmetic (ArithmeticOp.subtract) (OperandSize.bits64) (RegisterOrMemory.register (Register.counter)) (Source.operand (RegisterOrMemory.register (Register.r9))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3752 :
    decodeWith codeByte 0x27f3752 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.memory (Address.baseIndex (some (Register.accumulator)) none 8)) (Source.operand (RegisterOrMemory.register (Register.counter))), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3756 :
    decodeWith codeByte 0x27f3756 = .ok (Instruction.moveZeroExtend (OperandSize.bits32) (Register.accumulator) (OperandSize.bits8) (RegisterOrMemory.register (Register.r11)), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f375a :
    decodeWith codeByte 0x27f375a = .ok (Instruction.move (OperandSize.bits32) (RegisterOrMemory.memory (Address.baseIndex (some (Register.stackPointer)) none 0)) (Source.operand (RegisterOrMemory.register (Register.accumulator))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f375d :
    decodeWith codeByte 0x27f375d = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.base)) (Source.operand (RegisterOrMemory.register (Register.destinationIndex))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3760 :
    decodeWith codeByte 0x27f3760 = .ok (Instruction.move (OperandSize.bits32) (RegisterOrMemory.register (Register.r9)) (Source.operand (RegisterOrMemory.register (Register.data))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3763 :
    decodeWith codeByte 0x27f3763 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.data)) (Source.operand (RegisterOrMemory.register (Register.counter))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3766 :
    decodeWith codeByte 0x27f3766 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.counter)) (Source.operand (RegisterOrMemory.register (Register.r10))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3769 :
    decodeWith codeByte 0x27f3769 = .ok (Instruction.call (RegisterOrMemory.memory (Address.relativeToNextInstruction 16783793)), 6) := by
  decide +kernel

@[decode_table] theorem decode_27f376f :
    decodeWith codeByte 0x27f376f = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.accumulator)) (Source.operand (RegisterOrMemory.register (Register.base))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3772 :
    decodeWith codeByte 0x27f3772 = .ok (Instruction.jump 18446744073709551211, 5) := by
  decide +kernel

@[decode_table] theorem decode_27f3777 :
    decodeWith codeByte 0x27f3777 = .ok (Instruction.loadAddress (OperandSize.bits64) (Register.destinationIndex) (Address.relativeToNextInstruction 18446744073674003870), 7) := by
  decide +kernel

@[decode_table] theorem decode_27f377e :
    decodeWith codeByte 0x27f377e = .ok (Instruction.loadAddress (OperandSize.bits64) (Register.data) (Address.relativeToNextInstruction 16146651), 7) := by
  decide +kernel

@[decode_table] theorem decode_27f3785 :
    decodeWith codeByte 0x27f3785 = .ok (Instruction.move (OperandSize.bits32) (RegisterOrMemory.register (Register.sourceIndex)) (Source.immediate 38), 5) := by
  decide +kernel

@[decode_table] theorem decode_27f378a :
    decodeWith codeByte 0x27f378a = .ok (Instruction.call (RegisterOrMemory.memory (Address.relativeToNextInstruction 16735208)), 6) := by
  decide +kernel

@[decode_table] theorem decode_27f3790 :
    decodeWith codeByte 0x27f3790 = .ok (Instruction.push (Source.operand (RegisterOrMemory.register (Register.r14))), 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3792 :
    decodeWith codeByte 0x27f3792 = .ok (Instruction.push (Source.operand (RegisterOrMemory.register (Register.base))), 1) := by
  decide +kernel

@[decode_table] theorem decode_27f3793 :
    decodeWith codeByte 0x27f3793 = .ok (Instruction.push (Source.operand (RegisterOrMemory.register (Register.accumulator))), 1) := by
  decide +kernel

@[decode_table] theorem decode_27f3794 :
    decodeWith codeByte 0x27f3794 = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.counter)) (Source.immediate 10485760), 7) := by
  decide +kernel

@[decode_table] theorem decode_27f379b :
    decodeWith codeByte 0x27f379b = .ok (Instruction.jumpIf (Condition.above) 370, 6) := by
  decide +kernel

@[decode_table] theorem decode_27f37a1 :
    decodeWith codeByte 0x27f37a1 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.accumulator)) (Source.operand (RegisterOrMemory.memory (Address.baseIndex (some (Register.r8)) none 0))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f37a4 :
    decodeWith codeByte 0x27f37a4 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.r8)) (Source.operand (RegisterOrMemory.memory (Address.baseIndex (some (Register.r8)) none 8))), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f37a8 :
    decodeWith codeByte 0x27f37a8 = .ok (Instruction.moveImmediate64 (Register.r10) 4611686018427387904, 10) := by
  decide +kernel

@[decode_table] theorem decode_27f37b2 :
    decodeWith codeByte 0x27f37b2 = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.r8)) (Source.operand (RegisterOrMemory.register (Register.r10))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f37b5 :
    decodeWith codeByte 0x27f37b5 = .ok (Instruction.setIf (Condition.equal) (RegisterOrMemory.register (Register.r11)), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f37b9 :
    decodeWith codeByte 0x27f37b9 = .ok (Instruction.moveImmediate64 (Register.base) 879598564933, 10) := by
  decide +kernel

@[decode_table] theorem decode_27f37c3 :
    decodeWith codeByte 0x27f37c3 = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.accumulator)) (Source.operand (RegisterOrMemory.register (Register.base))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f37c6 :
    decodeWith codeByte 0x27f37c6 = .ok (Instruction.jumpIf (Condition.above) 3, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f37c8 :
    decodeWith codeByte 0x27f37c8 = .ok (Instruction.arithmetic (ArithmeticOp.xor) (OperandSize.bits32) (RegisterOrMemory.register (Register.r11)) (Source.operand (RegisterOrMemory.register (Register.r11))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f37cb :
    decodeWith codeByte 0x27f37cb = .ok (Instruction.arithmetic (ArithmeticOp.testBits) (OperandSize.bits8) (RegisterOrMemory.register (Register.r11)) (Source.operand (RegisterOrMemory.register (Register.r11))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f37ce :
    decodeWith codeByte 0x27f37ce = .ok (Instruction.jumpIf (Condition.notEqual) 319, 6) := by
  decide +kernel

@[decode_table] theorem decode_27f37d4 :
    decodeWith codeByte 0x27f37d4 = .ok (Instruction.moveImmediate64 (Register.r11) 4607182418800017408, 10) := by
  decide +kernel

@[decode_table] theorem decode_27f37de :
    decodeWith codeByte 0x27f37de = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.r8)) (Source.operand (RegisterOrMemory.register (Register.r11))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f37e1 :
    decodeWith codeByte 0x27f37e1 = .ok (Instruction.setIf (Condition.equal) (RegisterOrMemory.register (Register.base)), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f37e4 :
    decodeWith codeByte 0x27f37e4 = .ok (Instruction.moveImmediate64 (Register.r14) 1759197129867, 10) := by
  decide +kernel

@[decode_table] theorem decode_27f37ee :
    decodeWith codeByte 0x27f37ee = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.accumulator)) (Source.operand (RegisterOrMemory.register (Register.r14))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f37f1 :
    decodeWith codeByte 0x27f37f1 = .ok (Instruction.jumpIf (Condition.above) 2, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f37f3 :
    decodeWith codeByte 0x27f37f3 = .ok (Instruction.arithmetic (ArithmeticOp.xor) (OperandSize.bits32) (RegisterOrMemory.register (Register.base)) (Source.operand (RegisterOrMemory.register (Register.base))), 2) := by
  decide +kernel

@[decode_table] theorem decode_27f37f5 :
    decodeWith codeByte 0x27f37f5 = .ok (Instruction.arithmetic (ArithmeticOp.testBits) (OperandSize.bits8) (RegisterOrMemory.register (Register.base)) (Source.operand (RegisterOrMemory.register (Register.base))), 2) := by
  decide +kernel

@[decode_table] theorem decode_27f37f7 :
    decodeWith codeByte 0x27f37f7 = .ok (Instruction.jumpIf (Condition.notEqual) 278, 6) := by
  decide +kernel

@[decode_table] theorem decode_27f37fd :
    decodeWith codeByte 0x27f37fd = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.r8)) (Source.operand (RegisterOrMemory.register (Register.r10))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3800 :
    decodeWith codeByte 0x27f3800 = .ok (Instruction.jumpIf (Condition.equal) 11, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3802 :
    decodeWith codeByte 0x27f3802 = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.r8)) (Source.operand (RegisterOrMemory.register (Register.r11))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3805 :
    decodeWith codeByte 0x27f3805 = .ok (Instruction.jumpIf (Condition.notEqual) 68, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3807 :
    decodeWith codeByte 0x27f3807 = .ok (Instruction.arithmetic (ArithmeticOp.subtract) (OperandSize.bits64) (RegisterOrMemory.register (Register.counter)) (Source.immediate 18446744073709551488), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f380b :
    decodeWith codeByte 0x27f380b = .ok (Instruction.jump 8, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f380d :
    decodeWith codeByte 0x27f380d = .ok (Instruction.loadAddress (OperandSize.bits64) (Register.counter) (Address.baseIndex none (some (Register.counter, 1)) 256), 8) := by
  decide +kernel

@[decode_table] theorem decode_27f3815 :
    decodeWith codeByte 0x27f3815 = .ok (Instruction.multiplySigned (OperandSize.bits64) (Register.accumulator) (RegisterOrMemory.register (Register.counter)) none, 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3819 :
    decodeWith codeByte 0x27f3819 = .ok (Instruction.moveZeroExtend (OperandSize.bits32) (Register.r8) (OperandSize.bits8) (RegisterOrMemory.memory (Address.baseIndex (some (Register.stackPointer)) none 32)), 6) := by
  decide +kernel

@[decode_table] theorem decode_27f381f :
    decodeWith codeByte 0x27f381f = .ok (Instruction.arithmetic (ArithmeticOp.testBits) (OperandSize.bits64) (RegisterOrMemory.register (Register.sourceIndex)) (Source.operand (RegisterOrMemory.register (Register.sourceIndex))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3822 :
    decodeWith codeByte 0x27f3822 = .ok (Instruction.jumpIf (Condition.equal) 168, 6) := by
  decide +kernel

@[decode_table] theorem decode_27f3828 :
    decodeWith codeByte 0x27f3828 = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.sourceIndex)) (Source.operand (RegisterOrMemory.register (Register.accumulator))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f382b :
    decodeWith codeByte 0x27f382b = .ok (Instruction.move (OperandSize.bits32) (RegisterOrMemory.register (Register.counter)) (Source.immediate 2), 5) := by
  decide +kernel

@[decode_table] theorem decode_27f3830 :
    decodeWith codeByte 0x27f3830 = .ok (Instruction.arithmetic (ArithmeticOp.subtractWithBorrow) (OperandSize.bits64) (RegisterOrMemory.register (Register.counter)) (Source.immediate 0), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3834 :
    decodeWith codeByte 0x27f3834 = .ok (Instruction.arithmetic (ArithmeticOp.testBits) (OperandSize.bits8) (RegisterOrMemory.register (Register.r8)) (Source.operand (RegisterOrMemory.register (Register.r8))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3837 :
    decodeWith codeByte 0x27f3837 = .ok (Instruction.jumpIf (Condition.equal) 176, 6) := by
  decide +kernel

@[decode_table] theorem decode_27f383d :
    decodeWith codeByte 0x27f383d = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.data)) (Source.operand (RegisterOrMemory.register (Register.sourceIndex))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3840 :
    decodeWith codeByte 0x27f3840 = .ok (Instruction.jumpIf (Condition.below) 143, 6) := by
  decide +kernel

@[decode_table] theorem decode_27f3846 :
    decodeWith codeByte 0x27f3846 = .ok (Instruction.jump 183, 5) := by
  decide +kernel

@[decode_table] theorem decode_27f384b :
    decodeWith codeByte 0x27f384b = .ok (Instruction.moveIntegerToVector (OperandSize.bits64) 0 (RegisterOrMemory.register (Register.r8)), 5) := by
  decide +kernel

@[decode_table] theorem decode_27f3850 :
    decodeWith codeByte 0x27f3850 = .ok (Instruction.arithmetic (ArithmeticOp.subtract) (OperandSize.bits64) (RegisterOrMemory.register (Register.counter)) (Source.immediate 18446744073709551488), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3854 :
    decodeWith codeByte 0x27f3854 = .ok (Instruction.multiplySigned (OperandSize.bits64) (Register.accumulator) (RegisterOrMemory.register (Register.counter)) none, 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3858 :
    decodeWith codeByte 0x27f3858 = .ok (Instruction.moveIntegerToVector (OperandSize.bits64) 1 (RegisterOrMemory.register (Register.accumulator)), 5) := by
  decide +kernel

@[decode_table] theorem decode_27f385d :
    decodeWith codeByte 0x27f385d = .ok (Instruction.interleaveLow32 1 (VectorOrMemory.memory (Address.relativeToNextInstruction 18446744073670702795)), 8) := by
  decide +kernel

@[decode_table] theorem decode_27f3865 :
    decodeWith codeByte 0x27f3865 = .ok (Instruction.packedDouble (DoubleOp.subtract) 1 (VectorOrMemory.memory (Address.relativeToNextInstruction 18446744073670697267)), 8) := by
  decide +kernel

@[decode_table] theorem decode_27f386d :
    decodeWith codeByte 0x27f386d = .ok (Instruction.moveVector (VectorMove.doubleAligned) (VectorOrMemory.register 2) (VectorOrMemory.register 1), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3871 :
    decodeWith codeByte 0x27f3871 = .ok (Instruction.interleaveHighDoubles 2 (VectorOrMemory.register 1), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3875 :
    decodeWith codeByte 0x27f3875 = .ok (Instruction.scalarDouble (DoubleOp.add) 2 (VectorOrMemory.register 1), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3879 :
    decodeWith codeByte 0x27f3879 = .ok (Instruction.scalarDouble (DoubleOp.multiply) 2 (VectorOrMemory.register 0), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f387d :
    decodeWith codeByte 0x27f387d = .ok (Instruction.truncateDoubleToInt64 (Register.accumulator) (VectorOrMemory.register 2), 5) := by
  decide +kernel

@[decode_table] theorem decode_27f3882 :
    decodeWith codeByte 0x27f3882 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.counter)) (Source.operand (RegisterOrMemory.register (Register.accumulator))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f3885 :
    decodeWith codeByte 0x27f3885 = .ok (Instruction.shift (ShiftOp.rightArithmetic) (OperandSize.bits64) (RegisterOrMemory.register (Register.counter)) (ShiftCount.immediate 63), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3889 :
    decodeWith codeByte 0x27f3889 = .ok (Instruction.moveVector (VectorMove.doubleAligned) (VectorOrMemory.register 0) (VectorOrMemory.register 2), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f388d :
    decodeWith codeByte 0x27f388d = .ok (Instruction.scalarDouble (DoubleOp.subtract) 0 (VectorOrMemory.memory (Address.relativeToNextInstruction 18446744073670764179)), 8) := by
  decide +kernel

@[decode_table] theorem decode_27f3895 :
    decodeWith codeByte 0x27f3895 = .ok (Instruction.truncateDoubleToInt64 (Register.r8) (VectorOrMemory.register 0), 5) := by
  decide +kernel

@[decode_table] theorem decode_27f389a :
    decodeWith codeByte 0x27f389a = .ok (Instruction.arithmetic (ArithmeticOp.and) (OperandSize.bits64) (RegisterOrMemory.register (Register.r8)) (Source.operand (RegisterOrMemory.register (Register.counter))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f389d :
    decodeWith codeByte 0x27f389d = .ok (Instruction.arithmetic (ArithmeticOp.or) (OperandSize.bits64) (RegisterOrMemory.register (Register.r8)) (Source.operand (RegisterOrMemory.register (Register.accumulator))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f38a0 :
    decodeWith codeByte 0x27f38a0 = .ok (Instruction.arithmetic (ArithmeticOp.xor) (OperandSize.bits32) (RegisterOrMemory.register (Register.counter)) (Source.operand (RegisterOrMemory.register (Register.counter))), 2) := by
  decide +kernel

@[decode_table] theorem decode_27f38a2 :
    decodeWith codeByte 0x27f38a2 = .ok (Instruction.vectorBitwise (VectorBitwiseOp.xor) (VectorDomain.double) 0 (VectorOrMemory.register 0), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f38a6 :
    decodeWith codeByte 0x27f38a6 = .ok (Instruction.compareDoubles 2 (VectorOrMemory.register 0), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f38aa :
    decodeWith codeByte 0x27f38aa = .ok (Instruction.moveIf (Condition.aboveOrEqual) (OperandSize.bits64) (Register.counter) (RegisterOrMemory.register (Register.r8)), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f38ae :
    decodeWith codeByte 0x27f38ae = .ok (Instruction.compareDoubles 2 (VectorOrMemory.memory (Address.relativeToNextInstruction 18446744073670755010)), 8) := by
  decide +kernel

@[decode_table] theorem decode_27f38b6 :
    decodeWith codeByte 0x27f38b6 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.accumulator)) (Source.immediate 18446744073709551615), 7) := by
  decide +kernel

@[decode_table] theorem decode_27f38bd :
    decodeWith codeByte 0x27f38bd = .ok (Instruction.moveIf (Condition.belowOrEqual) (OperandSize.bits64) (Register.accumulator) (RegisterOrMemory.register (Register.counter)), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f38c1 :
    decodeWith codeByte 0x27f38c1 = .ok (Instruction.moveZeroExtend (OperandSize.bits32) (Register.r8) (OperandSize.bits8) (RegisterOrMemory.memory (Address.baseIndex (some (Register.stackPointer)) none 32)), 6) := by
  decide +kernel

@[decode_table] theorem decode_27f38c7 :
    decodeWith codeByte 0x27f38c7 = .ok (Instruction.arithmetic (ArithmeticOp.testBits) (OperandSize.bits64) (RegisterOrMemory.register (Register.sourceIndex)) (Source.operand (RegisterOrMemory.register (Register.sourceIndex))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f38ca :
    decodeWith codeByte 0x27f38ca = .ok (Instruction.jumpIf (Condition.notEqual) 18446744073709551448, 6) := by
  decide +kernel

@[decode_table] theorem decode_27f38d0 :
    decodeWith codeByte 0x27f38d0 = .ok (Instruction.arithmetic (ArithmeticOp.testBits) (OperandSize.bits8) (RegisterOrMemory.register (Register.r8)) (Source.operand (RegisterOrMemory.register (Register.r8))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f38d3 :
    decodeWith codeByte 0x27f38d3 = .ok (Instruction.jumpIf (Condition.equal) 22, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f38d5 :
    decodeWith codeByte 0x27f38d5 = .ok (Instruction.arithmetic (ArithmeticOp.testBits) (OperandSize.bits64) (RegisterOrMemory.register (Register.data)) (Source.operand (RegisterOrMemory.register (Register.data))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f38d8 :
    decodeWith codeByte 0x27f38d8 = .ok (Instruction.jumpIf (Condition.equal) 40, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f38da :
    decodeWith codeByte 0x27f38da = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.data)) (Source.operand (RegisterOrMemory.register (Register.accumulator))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f38dd :
    decodeWith codeByte 0x27f38dd = .ok (Instruction.jumpIf (Condition.aboveOrEqual) 35, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f38df :
    decodeWith codeByte 0x27f38df = .ok (Instruction.move (OperandSize.bits32) (RegisterOrMemory.memory (Address.baseIndex (some (Register.destinationIndex)) none 0)) (Source.immediate 86), 6) := by
  decide +kernel

@[decode_table] theorem decode_27f38e5 :
    decodeWith codeByte 0x27f38e5 = .ok (Instruction.move (OperandSize.bits8) (RegisterOrMemory.memory (Address.baseIndex (some (Register.destinationIndex)) none 4)) (Source.operand (RegisterOrMemory.register (Register.r9))), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f38e9 :
    decodeWith codeByte 0x27f38e9 = .ok (Instruction.jump 29, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f38eb :
    decodeWith codeByte 0x27f38eb = .ok (Instruction.arithmetic (ArithmeticOp.xor) (OperandSize.bits32) (RegisterOrMemory.register (Register.counter)) (Source.operand (RegisterOrMemory.register (Register.counter))), 2) := by
  decide +kernel

@[decode_table] theorem decode_27f38ed :
    decodeWith codeByte 0x27f38ed = .ok (Instruction.arithmetic (ArithmeticOp.testBits) (OperandSize.bits64) (RegisterOrMemory.register (Register.data)) (Source.operand (RegisterOrMemory.register (Register.data))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f38f0 :
    decodeWith codeByte 0x27f38f0 = .ok (Instruction.jumpIf (Condition.equal) 16, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f38f2 :
    decodeWith codeByte 0x27f38f2 = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.data)) (Source.operand (RegisterOrMemory.register (Register.accumulator))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f38f5 :
    decodeWith codeByte 0x27f38f5 = .ok (Instruction.jumpIf (Condition.aboveOrEqual) 11, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f38f7 :
    decodeWith codeByte 0x27f38f7 = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.data)) (Source.operand (RegisterOrMemory.register (Register.sourceIndex))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f38fa :
    decodeWith codeByte 0x27f38fa = .ok (Instruction.jumpIf (Condition.above) 18446744073709551587, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f38fc :
    decodeWith codeByte 0x27f38fc = .ok (Instruction.arithmetic (ArithmeticOp.compare) (OperandSize.bits64) (RegisterOrMemory.register (Register.counter)) (Source.immediate 1), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f3900 :
    decodeWith codeByte 0x27f3900 = .ok (Instruction.jumpIf (Condition.notEqual) 18446744073709551581, 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3902 :
    decodeWith codeByte 0x27f3902 = .ok (Instruction.move (OperandSize.bits32) (RegisterOrMemory.memory (Address.baseIndex (some (Register.destinationIndex)) none 0)) (Source.immediate 18446744073709551615), 6) := by
  decide +kernel

@[decode_table] theorem decode_27f3908 :
    decodeWith codeByte 0x27f3908 = .ok (Instruction.move (OperandSize.bits64) (RegisterOrMemory.register (Register.accumulator)) (Source.operand (RegisterOrMemory.register (Register.destinationIndex))), 3) := by
  decide +kernel

@[decode_table] theorem decode_27f390b :
    decodeWith codeByte 0x27f390b = .ok (Instruction.arithmetic (ArithmeticOp.add) (OperandSize.bits64) (RegisterOrMemory.register (Register.stackPointer)) (Source.immediate 8), 4) := by
  decide +kernel

@[decode_table] theorem decode_27f390f :
    decodeWith codeByte 0x27f390f = .ok (Instruction.pop (RegisterOrMemory.register (Register.base)), 1) := by
  decide +kernel

@[decode_table] theorem decode_27f3910 :
    decodeWith codeByte 0x27f3910 = .ok (Instruction.pop (RegisterOrMemory.register (Register.r14)), 2) := by
  decide +kernel

@[decode_table] theorem decode_27f3912 :
    decodeWith codeByte 0x27f3912 = .ok (Instruction.returnToCaller, 1) := by
  decide +kernel

@[decode_table] theorem decode_27f3913 :
    decodeWith codeByte 0x27f3913 = .ok (Instruction.loadAddress (OperandSize.bits64) (Register.destinationIndex) (Address.relativeToNextInstruction 18446744073674003458), 7) := by
  decide +kernel

@[decode_table] theorem decode_27f391a :
    decodeWith codeByte 0x27f391a = .ok (Instruction.loadAddress (OperandSize.bits64) (Register.data) (Address.relativeToNextInstruction 16146239), 7) := by
  decide +kernel

@[decode_table] theorem decode_27f3921 :
    decodeWith codeByte 0x27f3921 = .ok (Instruction.move (OperandSize.bits32) (RegisterOrMemory.register (Register.sourceIndex)) (Source.immediate 38), 5) := by
  decide +kernel

@[decode_table] theorem decode_27f3926 :
    decodeWith codeByte 0x27f3926 = .ok (Instruction.call (RegisterOrMemory.memory (Address.relativeToNextInstruction 16734796)), 6) := by
  decide +kernel

end ValidateFeePayer.Proof
