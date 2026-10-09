import X86Test.Harness
import X86Test.Form
import X86Test.Decode
import X86Test.FlagsAffected
import X86Test.Refusals
import ValidateFeePayer.Code

/-!
`lake exe x86-test behaviour <dir>`: runs every vector in `<dir>/vectors/*.txt`
through one `step` and compares with the CPU's outcome in
`<dir>/expected/*.txt`; checks that the instruction prints back as the vector's
assembly; and fails unless every form of the carved code and every
`Instruction` constructor has a vector that completes.

`lake exe x86-test decode <file>`: compares the decoder with llvm-objdump on
the encodings in `<file>` (`tests/x86/decode.py` writes it).

`lake exe x86-test same <dir> <other>`: compares two CPUs' outcomes up to the
flags the model leaves undefined.

`lake exe x86-test selftest <dir>`: requires the runner to reject each
fixture's planted defect (`tests/x86/selftest/`).
-/

open X86 X86Test

def readLines (path : System.FilePath) : IO (List String) := do
  return ((← IO.FS.readFile path).splitOn "\n").filter fun l => !l.trimAscii.isEmpty && !l.startsWith "#"

def printInstruction (bytes : List UInt8) (address : UInt64) : Except String String :=
  match decodeBytes bytes with
  | .ok (i, n) => .ok (Print.instruction (address + n.toUInt64) i)
  | .error e => .error (reprStr e)

/-- What comparing a directory of vectors with its outcomes found. -/
structure Report where
  failures : Nat := 0
  total : Nat := 0
  known : Array String := #[]
  completedForms : Std.HashMap String Nat := {}
  constructors : Std.HashMap String Nat := {}
  /-- Agreeing vectors per outcome kind, faults included. -/
  kinds : Std.HashMap String Nat := {}
  /-- Bytes of every vector that agrees. -/
  agreeingBytes : Std.HashSet (List UInt8) := {}
  perFile : Array (String × Nat) := #[]

/-- Every vector in `<dir>/vectors` against its outcome in `<dir>/expected`,
reporting each failure through `log`. `behaviour` and `selftest` share it, so
the self-test exercises the comparison CI relies on. -/
def compare (dir : System.FilePath) (log : String → IO Unit) : IO Report := do
  let mut r : Report := {}
  let txt (d : System.FilePath) : IO (Array String) := do
    if !(← d.pathExists) then return #[]
    return ((← d.readDir).filter (·.fileName.endsWith ".txt")).map (·.fileName) |>.qsort (· < ·)
  let files ← txt (dir / "vectors")
  for extra in (← txt (dir / "expected")).filter (!files.contains ·) do
    log s!"{extra}: outcomes without vectors"
    r := { r with failures := r.failures + 1 }
  if files.isEmpty then
    log s!"{dir}: no vectors"
    r := { r with failures := r.failures + 1 }
  for name in files do
    let inputs ← readLines (dir / "vectors" / name)
    let expectedPath := dir / "expected" / name
    if !(← expectedPath.pathExists) then
      log s!"{name}: no expected outcomes"
      r := { r with failures := r.failures + 1 }
      continue
    let expected ← readLines expectedPath
    r := { r with perFile := r.perFile.push (name, inputs.length) }
    if inputs.length != expected.length then
      log s!"{name}: {inputs.length} vectors but {expected.length} expected outcomes"
      r := { r with failures := r.failures + 1 }
      continue
    for (line, want) in inputs.zip expected do
      r := { r with total := r.total + 1 }
      match parseVector line with
      | .error e =>
        log s!"{name}: {e}: {line}"
        r := { r with failures := r.failures + 1 }
      | .ok v =>
        let (got, why) := outcome v
        let mut ok := true
        if !(want.startsWith (bytesHex v.bytes ++ " |")) then
          ok := false
          log s!"OUTCOME {name}: not the outcome of this vector's bytes\n  vector: {line}\n  cpu:    {want}"
        else if let some k := v.known then
          match checkKnown k got want with
          | .ok () => r := { r with known := r.known.push s!"{k}: {v.asm}\n    cpu:   {want}\n    model: {got}" }
          | .error e =>
            ok := false
            log s!"KNOWN {name}: {e}: {line}\n  cpu:    {want}\n  model:  {got}"
        else if !agrees v.state.rflags got want then
          ok := false
          log s!"MISMATCH {name}: {v.asm}\n  vector: {line}\n  cpu:    {want}\n  model:  {got}"
          if let some why := why then log s!"  model rejected: {why}"
        else
          for problem in sdmViolations v.state do
            ok := false
            log s!"FLAGS {name}: {v.asm}: {problem}\n  vector: {line}"
        match printInstruction v.bytes v.state.rip with
        | .ok text =>
          if v.asm != "-" && text != v.asm then
            ok := false
            log s!"ASM {name}: vector says '{v.asm}', decoder prints '{text}'"
        | .error _ => pure ()
        if !ok then
          r := { r with failures := r.failures + 1 }
        else if v.known.isNone then
          r := { r with kinds := r.kinds.alter (outcomeKind want) fun n => some (n.getD 0 + 1),
                        agreeingBytes := r.agreeingBytes.insert v.bytes }
          if outcomeKind want == "ok" then
            if let .ok (i, _) := decodeBytes v.bytes then
              r := { r with completedForms := r.completedForms.alter (form i) fun n => some (n.getD 0 + 1),
                            constructors := r.constructors.alter (constructorName i) fun n => some (n.getD 0 + 1) }
  return r

/-- Outcome kinds that must each have an agreeing vector, so the fault
vectors cannot drop out unnoticed. -/
def requiredKinds : List String := ["ok", "pagefault unmapped", "pagefault denied", "gp", "ill"]

def carvedBytes : List (List UInt8) :=
  ValidateFeePayer.listing.map fun d =>
    (List.range d.length).filterMap fun k => (ValidateFeePayer.codeByte (d.address + k.toUInt64)).toOption

/-- The coverage gate; prints what it checks and whether each part holds. -/
def gate (r : Report) (log : String → IO Unit := IO.println) : IO Bool := do
  let listingForms := (ValidateFeePayer.listing.map (form ·.instruction)).eraseDups
  let missingForms := listingForms.filter (!r.completedForms.contains ·)
  let missingConstructors := instructionConstructors.filter (!r.constructors.contains ·)
  let missingKinds := requiredKinds.filter (!r.kinds.contains ·)
  let carved := carvedBytes.eraseDups
  let missingCarved := carved.filter (!r.agreeingBytes.contains ·)
  log s!"\nvectors per file:"
  for (name, n) in r.perFile do log s!"  {n}\t{name}"
  log s!"\nforms in the carved code: {listingForms.length}, without a completed vector: {missingForms.length}"
  for f in listingForms.mergeSort (· ≤ ·) do
    log s!"  {if r.completedForms.contains f then "    " else "MISS"} {(r.completedForms.getD f 0)}\t{f}"
  log s!"Instruction constructors: {instructionConstructors.length}, without a completed vector: {missingConstructors.length}"
  for c in instructionConstructors do
    log s!"  {if r.constructors.contains c then "    " else "MISS"} {(r.constructors.getD c 0)}\t{c}"
  log s!"outcome kinds: {requiredKinds.length}, without an agreeing vector: {missingKinds.length}"
  for k in requiredKinds do
    log s!"  {if r.kinds.contains k then "    " else "MISS"} {(r.kinds.getD k 0)}\t{k}"
  log s!"carved instructions (distinct bytes): {carved.length}, without an agreeing vector of the same bytes: {missingCarved.length}"
  for b in missingCarved do log s!"  MISS {bytesHex b}"
  log s!"forms with a completed vector: {r.completedForms.size}"
  return missingForms.isEmpty && missingConstructors.isEmpty && missingKinds.isEmpty && missingCarved.isEmpty

def behaviour (dir : System.FilePath) : IO UInt32 := do
  let r ← compare dir IO.println
  IO.println s!"{r.total} vectors, {r.failures} failures, {r.known.size} known differences"
  for k in r.known do IO.println s!"  known {k}"
  let covered ← gate r
  return if r.failures == 0 && covered then 0 else 1

/-- Each fixture in `<dir>/<name>/` holds vectors and outcomes with one planted
defect, and `want.txt`: `failures=<n>`, then text the report must contain.
The runner must fail each fixture for that reason, pass `pass/`, and the
coverage gate must reject `pass/` (it covers only a few forms). A harness
that grows lenient fails here instead of passing the real vectors vacuously. -/
def selftest (dir : System.FilePath) : IO UInt32 := do
  let mut bad := 0
  let fixtures := ((← (← dir.readDir).filterM (·.path.isDir)).map (·.fileName)).qsort (· < ·)
  if !fixtures.contains "pass" then
    IO.println "no pass/ fixture"; bad := bad + 1
  for name in fixtures do
    let out ← IO.mkRef (#[] : Array String)
    let r ← compare (dir / name) fun l => out.modify (·.push l)
    let text := "\n".intercalate (← out.get).toList
    let want ← readLines (dir / name / "want.txt")
    let some n := (want.head?.bind (·.dropPrefix? "failures=")).bind (·.toString.toNat?)
      | IO.println s!"{name}: want.txt must start with failures=<n>"; bad := bad + 1; continue
    let missing := want.tail.filter (!text.contains ·)
    if r.failures != n || !missing.isEmpty then
      bad := bad + 1
      IO.println s!"FIXTURE {name}: {r.failures} failures (want {n}); missing from the report: {missing}\n{text}"
    else
      IO.println s!"ok {name}: {n} failures as planted"
    if name == "pass" then
      if ← gate r (fun _ => pure ()) then
        bad := bad + 1
        IO.println "FIXTURE pass: the coverage gate accepted a handful of vectors"
      else
        IO.println "ok pass: the coverage gate rejects it"
  IO.println s!"{fixtures.size} fixtures, {bad} not rejected as planted"
  return if bad == 0 then 0 else 1

/-- Compares the CPU outcomes in `<dir>/expected` with those in `other`, up to
flags the model leaves undefined. -/
def same (dir other : System.FilePath) : IO UInt32 := do
  let mut differences := 0
  let files := ((← (dir / "vectors").readDir).filter (·.fileName.endsWith ".txt")).qsort (·.fileName < ·.fileName)
  for file in files do
    let inputs ← readLines file.path
    let mine ← readLines (dir / "expected" / file.fileName)
    let theirs ← readLines (other / file.fileName)
    if inputs.length != mine.length || inputs.length != theirs.length then
      IO.println s!"{file.fileName}: different numbers of outcomes"
      differences := differences + 1
      continue
    for ((line, a), b) in (inputs.zip mine).zip theirs do
      let .ok v := parseVector line
        | differences := differences + 1
          IO.println s!"UNPARSED {file.fileName}: {line}"
          continue
      unless sameModuloUndefined v.state.rflags (outcome v).1 a b do
        differences := differences + 1
        IO.println s!"DIFFERENT {file.fileName}: {v.asm}\n  here:  {a}\n  other: {b}"
  IO.println s!"{differences} outcomes differ beyond flags the model leaves undefined"
  return if differences == 0 then 0 else 1

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
      let asm := match printInstruction v.bytes v.state.rip with
        | .ok text => if text == v.asm then "" else s!"   # prints '{text}'"
        | .error _ => ""
      IO.println (got ++ asm ++ (why.map ("   # " ++ ·)).getD "")
  return 0

def main : List String → IO UInt32
  | ["behaviour", dir] => behaviour dir
  | ["model", file] => model file
  | ["decode", file] => decode file
  | ["same", dir, other] => same dir other
  | ["selftest", dir] => selftest dir
  | _ => do
    IO.eprintln "usage: x86-test behaviour <tests/x86> | x86-test decode <file> | x86-test same <tests/x86> <expected dir> | x86-test selftest <fixtures dir>"
    return 2
