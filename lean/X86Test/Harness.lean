import X86.Machine
import X86.Print

/-!
The test-vector format shared with `tests/x86/oracle.c` and `tests/x86/gen.py`.
A vector is one line, `asm | bytes | field=value ...`, overriding a fixed
start state (`tests/x86/layout.h`). An outcome is one line,
`bytes | outcome field=value ...`, listing only what changed.
-/

namespace X86Test

open X86

def pageSize : Nat := 4096
def codePage : UInt64 := 0x40000000
def dataPage : UInt64 := 0x50000000
def readOnlyPage : UInt64 := 0x50001000
def stackPage : UInt64 := 0x60000000
def defaultAt : UInt64 := 0x800
def codeFill : UInt8 := 0xcc
def flagLetters : List Char := ['C', 'P', 'A', 'Z', 'S', 'O']
def flagOrder : List Flag := [.carry, .parity, .auxiliaryCarry, .zero, .sign, .overflow]

-- Unreachable from one step of a vector, so a step never ends in an exit.
def exits : Exits := { returnAddress := 0xdead0000, panicAt := 0xdead1000 }

def fillByte (address : UInt64) : UInt8 := ((address * 0x9e3779b97f4a7c15) >>> 56).toUInt8

def defaultRegister (i : Nat) : UInt64 :=
  if i = 4 then stackPage + 0x800 else 0x0101010101010101 * (i + 1).toUInt64

def defaultVector (i : Nat) : BitVec 128 :=
  (List.range 16).foldl (fun v _ => (v <<< 8) ||| BitVec.ofNat 128 (0xa0 + i)) 0

def pages : List (UInt64 × Permissions) :=
  [(codePage, .readExecute), (dataPage, .readWrite), (readOnlyPage, .readOnly), (stackPage, .readWrite)]

def page (m : Memory) (base : UInt64) (permissions : Permissions) : Memory :=
  let bytes := (List.range pageSize).map fun i =>
    if base = codePage then codeFill else fillByte (base + i.toUInt64)
  m.map base ⟨bytes.toArray⟩ permissions

/-- Write bytes regardless of permissions, as the oracle does before it protects the pages. -/
def poke (m : Memory) (address : UInt64) (bs : List UInt8) : Memory := Memory.stores address bs 0 m

/-- The same memory with one mapping per page: otherwise every lookup walks
back through each poke, and the memory diff looks up every byte. -/
def flatten (m : Memory) : Memory :=
  pages.foldl (init := .empty) fun acc (base, p) =>
    acc.map base ⟨(Array.range pageSize).map fun i => ((m.cell (base + i.toUInt64)).map (·.byte)).getD 0⟩ p

def hexValue (s : String) : Option Nat :=
  let s := if s.startsWith "0x" then s.drop 2 else s
  if s.isEmpty then none else
  s.foldl (fun acc c => acc.bind fun n =>
    if '0' ≤ c ∧ c ≤ '9' then some (16 * n + (c.toNat - '0'.toNat))
    else if 'a' ≤ c ∧ c ≤ 'f' then some (16 * n + (c.toNat - 'a'.toNat + 10))
    else none) (some 0)

def hexBytes (s : String) : Option (List UInt8) :=
  if s.length % 2 = 1 then none else
  (List.range (s.length / 2)).mapM fun i => (hexValue ((s.drop (2 * i)).take 2).toString).map (·.toUInt8)

def hexDigitsPadded (width : Nat) (n : Nat) : String :=
  let d := Print.hexDigits n
  String.ofList (List.replicate (width - d.length) '0') ++ d

def bytesHex (bs : List UInt8) : String := String.join (bs.map fun b => hexDigitsPadded 2 b.toNat)

def registerName (i : Nat) : String := Print.register64 (Register.ofIndex (Fin.ofNat 16 i))

structure Vector where
  asm : String
  bytes : List UInt8
  state : State
  /-- A documented way the model differs from the CPU on this vector. -/
  known : Option String

def initialState (bytes : List UInt8) (at_ : UInt64) : State :=
  let code := bytes.take (pageSize - at_.toNat)
  { rip := codePage + at_
    registers := Vector.ofFn fun i => defaultRegister i.val
    rflags := ⟨some false, some false, some false, some false, some false, some false⟩
    xmm := Vector.ofFn fun i => defaultVector i.val
    mxcsr := defaultMxcsr
    memory := poke (pages.foldl (fun m (b, p) => page m b p) .empty) (codePage + at_) code }

def flagsOf (letters : String) : List Flag :=
  (flagLetters.zip flagOrder).filterMap fun (c, f) => if letters.contains c then some f else none

def setFlag (fs : Flags) (f : Flag) (v : Option Bool) : Flags :=
  match f with
  | .carry => { fs with carry := v } | .parity => { fs with parity := v }
  | .auxiliaryCarry => { fs with auxiliaryCarry := v } | .zero => { fs with zero := v }
  | .sign => { fs with sign := v } | .overflow => { fs with overflow := v }

def applyField (s : State) (key value : String) : Except String State := do
  let num := (hexValue value).getD 0
  if let some i := (List.range 16).find? (registerName · == key) then
    return { s with registers := s.registers.set! i num.toUInt64 }
  if key.startsWith "xmm" then
    let some i := (key.drop 3).toNat? | throw s!"bad register {key}"
    return { s with xmm := s.xmm.set! i (BitVec.ofNat 128 num) }
  match key with
  | "at" => return { s with rip := codePage + num.toUInt64 }
  | "flags" =>
    let set := flagsOf value
    return { s with rflags := flagOrder.foldl (fun fs f => setFlag fs f (some (set.contains f))) s.rflags }
  | "mxcsr" => return { s with mxcsr := num.toUInt32 }
  | "known" => return s
  | "mem" =>
    let [address, bytes] := value.splitOn ":" | throw s!"bad mem {value}"
    let some a := hexValue address | throw s!"bad address {address}"
    let some bs := hexBytes bytes | throw s!"bad bytes {bytes}"
    return { s with memory := poke s.memory a.toUInt64 bs }
  | _ => throw s!"unknown field {key}"

def fields (s : String) : List (String × String) :=
  ((s.splitOn " ").filter (· ≠ "")).map fun f =>
    match f.splitOn "=" with
    | k :: v => (k, "=".intercalate v)
    | [] => (f, "")

def parseVector (line : String) : Except String Vector := do
  let [asm, hex, rest] := line.splitOn "|" | throw "expected 'asm | bytes | fields'"
  let some bytes := hexBytes hex.trimAscii.toString | throw s!"bad bytes {hex}"
  let fs := fields rest
  let at_ := ((fs.lookup "at").bind hexValue).getD defaultAt.toNat
  let state ← fs.foldlM (fun s (k, v) => applyField s k v) (initialState bytes at_.toUInt64)
  let state := { state with memory := flatten state.memory }
  return { asm := asm.trimAscii.toString, bytes, state, known := fs.lookup "known" }

def renderFlags (fs : Flags) : String :=
  String.ofList ((flagLetters.zip flagOrder).map fun (c, f) =>
    match fs.get f with | some true => c | some false => '-' | none => '?')

/-- An outcome line without its flags, and the flags after it. -/
def splitFlags (before : Flags) (line : String) : List String × List Char :=
  let tokens := line.splitOn " "
  let flags := (tokens.find? (·.startsWith "flags=")).map (·.drop 6 |>.toString)
  (tokens.filter (!·.startsWith "flags="), (flags.getD (renderFlags before)).toList)

/-- Whether the CPU's outcome is one the model allows: a flag the model
leaves undefined (`?`) allows any value, everything else must be equal. -/
def agrees (before : Flags) (model cpu : String) : Bool :=
  let (m, mFlags) := splitFlags before model
  let (c, cFlags) := splitFlags before cpu
  m == c && mFlags.length == cFlags.length && (mFlags.zip cFlags).all fun (a, b) => a == '?' || a == b

/-- Whether two CPUs' outcomes differ at most in flags the model leaves
undefined, which vendors and models set differently. -/
def sameModuloUndefined (before : Flags) (model cpu cpu' : String) : Bool :=
  let (_, mFlags) := splitFlags before model
  let (c, cFlags) := splitFlags before cpu
  let (c', cFlags') := splitFlags before cpu'
  c == c' && cFlags.length == cFlags'.length &&
    ((cFlags.zip cFlags').zipIdx).all fun ((a, b), i) => a == b || mFlags[i]? == some '?'

def hex (n : Nat) : String := "0x" ++ Print.hexDigits n

/-- Runs of changed bytes, as `mem=address:bytes`. -/
def memoryDiff (before after : Memory) : List String := Id.run do
  let mut out := #[]
  -- Only a writable page can change.
  for (base, _) in pages.filter (·.2.write) do
    let byteAt (m : Memory) (i : Nat) := ((m.cell (base + i.toUInt64)).map (·.byte)).getD 0
    let mut run : Option (Nat × Array UInt8) := none
    for i in [0:pageSize] do
      let a := byteAt after i
      if byteAt before i != a then
        run := some (match run with
          | some (start, bs) => (start, bs.push a)
          | none => (i, #[a]))
      else if let some (start, bs) := run then
        out := out.push s!"mem={hex (base.toNat + start)}:{bytesHex bs.toList}"
        run := none
    if let some (start, bs) := run then
      out := out.push s!"mem={hex (base.toNat + start)}:{bytesHex bs.toList}"
  return out.toList

/-- The fields of `after` that differ from `before`, in the oracle's order. -/
def diff (before after : State) (completed : Bool) (mxcsr : UInt32) : List String :=
  let rip := if completed || after.rip != before.rip
    then [s!"rip={hex after.rip.toNat}"] else []
  let registers := (List.range 16).filterMap fun i =>
    let v := after.registers[i]!
    if v != before.registers[i]! then some s!"{registerName i}={hex v.toNat}" else none
  let flags := if renderFlags after.rflags != renderFlags before.rflags
    then [s!"flags={renderFlags after.rflags}"] else []
  let vectors := (List.range 16).filterMap fun i =>
    let v := after.xmm[i]!
    if v != before.xmm[i]! then some s!"xmm{i}=0x{hexDigitsPadded 32 v.toNat}" else none
  let mxcsr := if mxcsr != before.mxcsr then [s!"mxcsr={hex mxcsr.toNat}"] else []
  rip ++ registers ++ flags ++ vectors ++ mxcsr ++ memoryDiff before.memory after.memory

open Exec in
/-- The MXCSR exception flags `i` raises. The machine does not keep them
(nothing reads them), but `F64` computes them, so they are compared too. -/
def floatExceptions : Instruction → Exec F64.Exceptions
  | .scalarDouble op d s => do return (op.eval (lowHalf (← readVector d)) (← readVector64 s)).2
  | .packedDouble op d s => do
    let a ← readVector d
    let b ← readVector128 true s
    return (op.eval (lowHalf a) (lowHalf b)).2.merge (op.eval (highHalf a) (highHalf b)).2
  | .compareDoubles d s => do return (F64.compareUnordered (lowHalf (← readVector d)) (← readVector64 s)).2
  | .truncateDoubleToInt64 _ s => do return (F64.truncateToInt64 (← readVector64 s)).2
  | _ => pure {}

def stickyExceptions (s : State) : UInt32 :=
  match decode s.memory s.rip with
  | .ok (i, length) =>
    match (floatExceptions i).run' { s with rip := s.rip + length.toUInt64 } with
    | .ok e => e.bits
    | .error _ => 0
  | .error _ => 0

/-- One `step`, rendered as the oracle renders the CPU's. The second
component explains an `ill` (the CPU only says `SIGILL`). -/
def outcome (v : Vector) : String × Option String :=
  let s := v.state
  let (kind, after, completed, why) := match step exits s with
    | .running s' => ("ok", s', true, none)
    | .faulted (.pageFault (.unmapped a _)) s' => (s!"pagefault unmapped {hex a.toNat}", s', false, none)
    | .faulted (.pageFault (.denied a _)) s' => (s!"pagefault denied {hex a.toNat}", s', false, none)
    | .faulted (.misaligned _) s' => ("gp", s', false, none)
    | .faulted (.undefinedFlagRead f) s' => (s!"undefined-flag-read {repr f}", s', false, none)
    | .faulted (.unsupported w) s' => (s!"unsupported {w}", s', false, none)
    | .faulted (.undecodable why) s' => ("ill", s', false, some (reprStr why))
    | .returned s' | .panicked s' => ("exit", s', false, none)
    | .badJump s' => (s!"badjump {hex s'.rip.toNat}", s', false, none)
  let mxcsr := if completed then after.mxcsr ||| stickyExceptions s else after.mxcsr
  (" ".intercalate ((bytesHex v.bytes ++ " |") :: kind :: diff s after completed mxcsr), why)

end X86Test
