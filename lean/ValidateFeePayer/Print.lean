import ValidateFeePayer.Decode

/-!
Intel-syntax text of a decoded instruction, in llvm-objdump's format, so
`Checks.lean` can compare the decoder with `Disasm.lean` operand for operand.
Only used for that check.
-/

namespace ValidateFeePayer.X86.Print

def hexDigits (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def hex (n : Nat) : String := "0x" ++ hexDigits n

def signedHex (v : Int) : String :=
  if v < 0 then "-" ++ hex v.natAbs else hex v.toNat

def reg64 : Reg → String
  | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rbx => "rbx"
  | .rsp => "rsp" | .rbp => "rbp" | .rsi => "rsi" | .rdi => "rdi"
  | r => "r" ++ toString r.toFin.val

def reg (sz : Size) (r : Reg) : String :=
  let i := r.toFin.val
  match sz with
  | .b64 => reg64 r
  | .b32 => if i < 8 then ["eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi"][i]! else reg64 r ++ "d"
  | .b8 => if i < 8 then ["al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil"][i]! else reg64 r ++ "b"

def xmm (x : Xmm) : String := "xmm" ++ toString x.val

def addr : Addr → String
  | .rip d => "[rip" ++ (if d < 0 then " - " ++ hex d.natAbs else " + " ++ hex d.toNat) ++ "]"
  | .sib base index d =>
    let terms := (base.map reg64).toList ++
      (index.map fun (r, s) => if s.val = 0 then reg64 r else toString (2 ^ s.val) ++ "*" ++ reg64 r).toList
    let body := " + ".intercalate terms
    let disp :=
      if d = 0 then ""
      else if terms.isEmpty then signedHex d
      else if d < 0 then " - " ++ hex d.natAbs else " + " ++ hex d.toNat
    "[" ++ body ++ disp ++ "]"

def ptr (bytes : Nat) (a : Addr) : String :=
  (match bytes with
   | 1 => "byte" | 2 => "word" | 4 => "dword" | 8 => "qword" | _ => "xmmword") ++ " ptr " ++ addr a

def bytesOf (sz : Size) : Nat := sz.bits / 8

def rm (sz : Size) : RM → String
  | .reg r => reg sz r
  | .mem a => ptr (bytesOf sz) a

def xrm (bytes : Nat) : XRM → String
  | .reg x => xmm x
  | .mem a => ptr bytes a

/-- llvm-objdump prints 64-bit immediates signed and narrower ones unsigned. -/
def imm (sz : Size) (v : UInt64) : String :=
  match sz with
  | .b64 => signedHex (if v.toNat < 2 ^ 63 then (v.toNat : Int) else v.toNat - 2 ^ 64)
  | _ => hex (v.toNat % 2 ^ sz.bits)

def src (sz : Size) : Src → String
  | .rm x => rm sz x
  | .imm v => imm sz v

def ops (l : List String) : String := ", ".intercalate l

/-- The text of `i`, which ends at `next` (for branch targets). -/
def instr (next : UInt64) (i : Instr) : String :=
  let target (rel : Int) := hex ((next.toNat + rel) % 2 ^ 64).toNat
  let body := match i with
    | .alu _ sz d s => ops [rm sz d, src sz s]
    | .mov sz d s => ops [rm sz d, src sz s]
    | .movabs d v => ops [reg64 d, hex v.toNat]
    | .movzx sz d s => ops [reg sz d, rm .b8 s]
    | .lea d a => ops [reg64 d, addr a]
    | .inc sz d => rm sz d
    | .imul d s none => ops [reg64 d, rm .b64 s]
    | .imul d s (some v) => ops [reg64 d, rm .b64 s, imm .b64 v]
    | .sar d c => ops [rm .b64 d, hex c.toNat]
    | .setcc _ d => rm .b8 d
    | .cmov _ sz d s => ops [reg sz d, rm sz s]
    | .push r | .pop r => reg64 r
    | .jcc _ rel | .jmp rel => target rel
    | .call t => rm .b64 t
    | .ret => ""
    | .movdqu d s | .movapd d s | .xbit _ d s | .ptest d s | .punpckldq d s
    | .unpckhpd d s | .subpd d s => ops [xmm d, xrm 16 s]
    | .movq d s => ops [xmm d, rm .b64 s]
    | .sd _ d s | .ucomisd d s => ops [xmm d, xrm 8 s]
    | .cvttsd2si d s => ops [reg64 d, xrm 8 s]
  if body.isEmpty then i.mnemonic else i.mnemonic ++ " " ++ body

def entry (e : Decoded) : UInt64 × Nat × String :=
  (e.addr, e.len, instr (e.addr + e.len.toUInt64) e.instr)

end ValidateFeePayer.X86.Print
