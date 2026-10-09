import X86Test.Harness
import X86Test.Form
import X86Test.Decode
import ValidateFeePayer.Code

/-!
`lake exe x86-test behaviour <dir>`: runs every vector in `<dir>/vectors/*.txt`
through one `step` and compares with the CPU's outcome in
`<dir>/expected/*.txt`; checks that the instruction prints back as the vector's
assembly; and fails unless every form of the carved code and every
`Instruction` constructor has a vector that completes.

`lake exe x86-test decode <file>`: compares the decoder with llvm-objdump on
the encodings in `<file>` (`tests/x86/decode.py` writes it).
-/

open X86 X86Test

def readLines (path : System.FilePath) : IO (List String) := do
  return ((← IO.FS.readFile path).splitOn "\n").filter fun l => !l.trimAscii.isEmpty && !l.startsWith "#"

def printInstruction (bytes : List UInt8) (address : UInt64) : Except String String :=
  match decodeBytes bytes with
  | .ok (i, n) => .ok (Print.instruction (address + n.toUInt64) i)
  | .error e => .error (reprStr e)

def behaviour (dir : System.FilePath) : IO UInt32 := do
  let mut failures := 0
  let mut total := 0
  let mut known : Array String := #[]
  let mut completedForms : Std.HashMap String Nat := {}
  let mut constructors : Std.HashMap String Nat := {}
  let files := ((← (dir / "vectors").readDir).filter (·.fileName.endsWith ".txt")).qsort (·.fileName < ·.fileName)
  for file in files do
    let inputs ← readLines file.path
    let expected ← readLines (dir / "expected" / file.fileName)
    if inputs.length != expected.length then
      IO.println s!"{file.fileName}: {inputs.length} vectors but {expected.length} expected outcomes"
      failures := failures + 1
      continue
    for (line, want) in inputs.zip expected do
      total := total + 1
      match parseVector line with
      | .error e =>
        IO.println s!"{file.fileName}: {e}: {line}"
        failures := failures + 1
      | .ok v =>
        let (got, why) := outcome v
        if let some reason := v.known then
          if agrees v.state.flags got want then
            failures := failures + 1
            IO.println s!"KNOWN {file.fileName}: marked known={reason} but the model now agrees: {line}"
          else
            known := known.push s!"{reason}: {v.asm}\n    cpu:   {want}\n    model: {got}"
        else if !agrees v.state.flags got want then
          failures := failures + 1
          IO.println s!"MISMATCH {file.fileName}: {v.asm}\n  vector: {line}\n  cpu:    {want}\n  model:  {got}"
          if let some why := why then IO.println s!"  model rejected: {why}"
        let address := v.state.instructionPointer
        match printInstruction v.bytes address with
        | .ok text =>
          if v.asm != "-" && text != v.asm then
            failures := failures + 1
            IO.println s!"ASM {file.fileName}: vector says '{v.asm}', decoder prints '{text}'"
        | .error _ => pure ()
        if v.known.isNone && (want.splitOn " " |>.contains "ok") then
          if let .ok (i, _) := decodeBytes v.bytes then
            completedForms := completedForms.alter (form i) fun n => some (n.getD 0 + 1)
            constructors := constructors.alter (constructorName i) fun n => some (n.getD 0 + 1)
  IO.println s!"{total} vectors, {failures} failures, {known.size} known differences"
  for k in known do IO.println s!"  known {k}"

  -- Coverage gate.
  let listingForms := (ValidateFeePayer.listing.map (form ·.instruction)).eraseDups
  let missingForms := listingForms.filter (!completedForms.contains ·)
  let missingConstructors := instructionConstructors.filter (!constructors.contains ·)
  IO.println s!"\nforms in the carved code: {listingForms.length}, without a completed vector: {missingForms.length}"
  for f in listingForms.mergeSort (· ≤ ·) do
    IO.println s!"  {if completedForms.contains f then "    " else "MISS"} {(completedForms.getD f 0)}\t{f}"
  IO.println s!"Instruction constructors: {instructionConstructors.length}, without a completed vector: {missingConstructors.length}"
  for c in instructionConstructors do
    IO.println s!"  {if constructors.contains c then "    " else "MISS"} {(constructors.getD c 0)}\t{c}"
  IO.println s!"forms with a completed vector: {completedForms.size}"
  let ok := failures == 0 && missingForms.isEmpty && missingConstructors.isEmpty
  return if ok then 0 else 1

/-- A line of the decode file: `address | bytes | length | text`, from
llvm-objdump; length 0 means it found no instruction. -/
def decode (file : System.FilePath) : IO UInt32 := do
  let mut mismatches := 0
  let mut accepted := 0
  let mut total := 0
  let mut longest := 0
  let mut rejected : Std.HashMap String (Nat × String) := {}
  for line in ← readLines file do
    total := total + 1
    let [address, hex, length, text] := (line.splitOn "|").map (·.trimAscii.toString)
      | IO.println s!"bad line: {line}"; return 1
    let some address := hexValue address | IO.println s!"bad address: {line}"; return 1
    let some bytes := hexBytes hex | IO.println s!"bad bytes: {line}"; return 1
    let llvmLength := length.toNat!
    match decodeBytes bytes with
    | .ok (i, n) =>
      accepted := accepted + 1
      longest := max longest n
      let ours := Print.instruction (address.toUInt64 + n.toUInt64) i
      -- The decoder must also stop fetching at the instruction's end, and
      -- report a fault at the first byte it cannot fetch.
      let fetch (limit : Nat) (a : UInt64) : Except PageFault UInt8 :=
        if a.toNat - address < limit then .ok bytes[a.toNat - address]! else .error (.unmapped a .fetch)
      let exact := decodeWith (fetch n) address.toUInt64
      let short := decodeWith (fetch (n - 1)) address.toUInt64
      let shortOk := match short with
        | .error (.pageFault (.unmapped a _)) => a.toNat == address + n - 1
        | _ => false
      if n != llvmLength || ours != text || !(match exact with | .ok r => r == (i, n) | .error _ => false) || !shortOk then
        mismatches := mismatches + 1
        if mismatches ≤ 200 then
          IO.println s!"MISMATCH {hex}: llvm {llvmLength} '{text}', lean {n} '{ours}'{if shortOk then "" else " (fetch)"}"
    | .error e =>
      let key := reprStr e
      rejected := rejected.alter key fun
        | some (k, first) => some (k + 1, first)
        | none => some (1, s!"{hex} (llvm: {if llvmLength == 0 then "invalid" else text})")
  IO.println s!"{total} encodings: {accepted} decoded, all compared with llvm-objdump; {mismatches} mismatches; longest decoded: {longest} bytes"
  IO.println "rejected by the decoder (reason: count, first example):"
  for (reason, count, first) in rejected.toList.mergeSort (fun a b => a.2.1 ≥ b.2.1) do
    IO.println s!"  {reason}: {count}, {first}"
  return if mismatches == 0 then 0 else 1

/-- The model's outcome for each vector, in the oracle's format, so the two
can be compared with `diff` too. -/
def model (file : System.FilePath) : IO UInt32 := do
  for line in ← readLines file do
    match parseVector line with
    | .error e => IO.eprintln s!"{e}: {line}"; return 1
    | .ok v =>
      let (got, why) := outcome v
      let asm := match printInstruction v.bytes v.state.instructionPointer with
        | .ok text => if text == v.asm then "" else s!"   # prints '{text}'"
        | .error _ => ""
      IO.println (got ++ asm ++ (why.map ("   # " ++ ·)).getD "")
  return 0

def main : List String → IO UInt32
  | ["behaviour", dir] => behaviour dir
  | ["model", file] => model file
  | ["decode", file] => decode file
  | _ => do
    IO.eprintln "usage: x86-test behaviour <tests/x86> | x86-test decode <file>"
    return 2
