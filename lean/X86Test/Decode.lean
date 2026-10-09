import X86.Decode

/-! Encodings the decoder must reject because the CPU ignores some of their bits. -/

namespace X86Test.Decode

open X86

def rejects (bytes : List UInt8) : Bool := (decodeBytes bytes).toOption.isNone

def accepts (bytes : List UInt8) : Bool := (decodeBytes bytes).toOption.isSome

-- `0x66` under REX.W: `add rax, rbx`, `mov rax, [rbx]`, `cmovne rax, rbx`, `imul rax, rbx`.
#guard accepts [0x48, 0x01, 0xd8] && rejects [0x66, 0x48, 0x01, 0xd8]
#guard accepts [0x48, 0x8b, 0x03] && rejects [0x66, 0x48, 0x8b, 0x03]
#guard accepts [0x48, 0x0f, 0x45, 0xc3] && rejects [0x66, 0x48, 0x0f, 0x45, 0xc3]
#guard accepts [0x48, 0x0f, 0xaf, 0xc3] && rejects [0x66, 0x48, 0x0f, 0xaf, 0xc3]
-- `0x66` alone still selects 16 bits.
#guard accepts [0x66, 0x01, 0xd8] && accepts [0x66, 0x0f, 0x45, 0xc3]
-- SSE forms where `0x66` is the mandatory prefix keep REX.W: `movq xmm0, rbx`.
#guard accepts [0x66, 0x48, 0x0f, 0x6e, 0xc3]
-- `66 90` is `xchg ax, ax`, which does nothing.
#guard accepts [0x90] && rejects [0x66, 0x90]

end X86Test.Decode
