import ZigLean.Mem.ErrWidth

/-! L10: the model's side of `probe.zig` and `native.py`. For each configuration of a recorded
native observation (`native/<arch>-<os>-<version>.txt`), it recomputes from
`ZigLean/Mem/ErrWidth.lean` the lines the native run printed and compares them:

* whether the program compiles under `--error-limit` (it does iff 0 < limit and the compilation's
  error count is at most the limit; width 0 has no error value);
* the error integer's width (`errorLimitBits`), size and alignment (`errCodeSize`,
  `errCodeAlign`), also of `?E`;
* the byte images: a stored error is a nonzero code of `errCodeSize` bytes, distinct errors have
  distinct images, `null` is the zero code, `?E` shares the image of `E`;
* where `E!T` keeps its code and payload and its size and alignment (`errUnionOffsetsW`,
  `errUnionSizeW`) for seven payloads;
* `@errorFromInt`: code 0, every code above the compilation's error count and every integer too
  wide for the error integer panic, the codes 1..N do not (`errorFromIntW`, `errorCodeOfNat`)
  over the numbering the compiler printed, which is checked to be a table of that width
  (`ErrorTable.check`: unique names, at most `errCapacity` of them) whose `@intFromError` and
  `@errorFromInt` invert each other.

The compiler's numbering is a parameter, never predicted: the model compares everything else.
Tables above 1000 errors are not built (the uniqueness check is quadratic): their boundary lines
are the arithmetic of `errorFromIntW`, whose statement for every table is
`ZigLean.Mem.ErrWidthLemmas.errorFromIntW_zero` / `errorFromIntW_unused`.

    lake env lean --run tests/roadmap/error-width/Model.lean OBSERVED [EXPECTED_MISMATCHES]

A line only the model prints or only the native run prints is a mismatch. It must be listed in
EXPECTED_MISMATCHES (one `config | model: ... | native: ...` per line, written by this program
with `--print-mismatches`), or the run fails; a listed mismatch that no longer occurs also fails. -/

open Zig

private def domain : ErrorDomain := ⟨#["Bad", "Other", "Top"], by decide, by decide⟩
private def single : ErrorDomain := ⟨#["Bad"], by decide, by decide⟩

private def verdict {α : Type} (r : Result α) (show_ : α → String) : String :=
  match r.run with
  | some (.ok v) => show_ v
  | some (.error .panic) => "panic"
  | some (.error .overflow) => "panic"
  | _ => "undefined"

/-- Payloads of `probe.zig`: name, size, alignment. -/
private def payloads : List (String × Nat × Nat) :=
  [("void", 0, 1), ("u8", 1, 1), ("u16", 2, 2), ("u32", 4, 4), ("u64", 8, 8), ("a3u8", 3, 1),
   ("a2u16", 4, 2)]

private def flag (s : String) (b : Bool) : String := s!"enc {s} {if b then 1 else 0}"

/-- A configuration of the native file: header fields and the lines after it. -/
structure Cfg where
  name : String
  limit : Option Nat
  total : Nat
  status : String
  body : List String

private def parseHead (l : String) : Option Cfg :=
  match l.splitOn " " with
  | ["config", n, "limit", lim, "total", t, "compile", s] =>
    some ⟨n, if lim == "default" then none else lim.toNat?, t.toNat!, s, []⟩
  | ["config", n, "limit", lim, "total", t, "skipped"] =>
    some ⟨n, lim.toNat?, t.toNat!, "skipped", []⟩
  | _ => none

private def parseFile (text : String) : Nat × List Cfg := Id.run do
  let mut hidden := 0
  let mut cfgs : Array Cfg := #[]
  for l in (text.splitOn "\n").filter (· ≠ "") do
    if l.startsWith "meta hidden " then hidden := (l.drop 12).toNat!
    else if let some c := parseHead l then cfgs := cfgs.push c
    else if 0 < cfgs.size then
      cfgs := cfgs.modify (cfgs.size - 1) fun c => { c with body := c.body ++ [l] }
  return (hidden, cfgs.toList)

private def head (c : Cfg) (status : String) : String :=
  let lim := match c.limit with | none => "default" | some n => toString n
  if status == "skipped" then s!"config {c.name} limit {lim} total {c.total} skipped"
  else s!"config {c.name} limit {lim} total {c.total} compile {status}"

private def names (c : Cfg) : Array ErrName := Id.run do
  let mut out : Array (Nat × String) := #[]
  for l in c.body do
    match l.splitOn " " with
    | ["name", n, s] => out := out.push (n.toNat!, s)
    | _ => pure ()
  return (out.qsort (·.1 < ·.1)).map (·.2)

/-- The model's lines of one configuration. `observed` supplies the compiler's numbering. -/
private def expected (hidden : Nat) (c : Cfg) : List String :=
  let limit := c.limit.getD defaultErrorLimit
  let fits := 0 < limit && c.total ≤ limit
  if c.total < hidden + 1 then [head c "skipped"]
  else if !fits then [head c "fail"]
  else
    let bits := errorLimitBits limit
    let n := errCodeSize bits
    let a := errCodeAlign bits
    let isSingle := c.total == hidden + 1
    let d := if isSingle then single else domain
    let bytesOf (e : ErrName) := errBytesW bits (some e)
    let top := if isSingle then "Bad" else if c.total == hidden + 2 then "Other" else "Top"
    let es := (if isSingle then ["Bad"] else ["Bad", "Other"]) ++ (if top == "Top" then ["Top"] else [])
    let nonzero := es.all fun e => bytesOf e != errBytesW bits none
    let distinct := isSingle || bytesOf "Bad" != bytesOf "Other"
    let ownBytes := es.all fun e => (bytesOf e).size == n
    let optNull := (optionalErrorEncW bits d).encode none == errBytesW bits none &&
      (errBytesW bits none).all (fun b => b == .int 0)
    let optSome := es.all fun e => (optionalErrorEncW bits d).encode (some e) == bytesOf e &&
      (errorEncW bits d).encode e == bytesOf e
    let tbl := names c
    -- The printed codes of `Bad`, `Other` and the last error lie in 1..N, `Bad` and `Other` apart.
    let codesOk := match (c.body.find? (·.startsWith "code ")).map (·.splitOn " ") with
      | some ["code", "Bad", x, "Other", y, "top", z] =>
        [x, y, z].all (fun s => 1 ≤ s.toNat! && s.toNat! ≤ c.total) && (isSingle || x != y)
      | _ => false
    -- With a printed numbering (at most 1000 errors): unique, fits the width, inverse casts.
    let tableOk : Bool := match ErrorTable.check tbl bits with
      | .error _ => false
      | .ok t => (List.range tbl.size).all fun i =>
          verdict (intFromErrorW bits t tbl[i]!) (fun v => toString v.toNat) == toString (i + 1) &&
          verdict (errorFromIntW bits t (BitVec.ofNat bits (i + 1))) id == tbl[i]!
    -- `@errorFromInt` over the compilation's N errors: panic outside 1..N, in `Code` or not.
    let nerr := c.total
    let mkTable (k : Nat) : Option (ErrorTable) :=
      if k ≤ 1000 then
        (ErrorTable.check ((Array.range k).map toString) bits).toOption else none
    let castAt (x : Nat) : String :=
      match mkTable nerr with
      | some t => verdict (errorCodeOfNat bits x >>= fun v => errorFromIntW bits t v) (fun _ => "ok")
      | none => if 1 ≤ x ∧ x ≤ nerr ∧ x < 2 ^ bits then "ok" else "panic"
    let maxCode := 2 ^ bits - 1
    let tableLines := c.body.filter (·.startsWith "name ")
    [head c "ok",
     s!"enc size {n} {a}", s!"enc defined {n}", s!"enc anyerror {n} {a} {bits}",
     s!"enc optional {(optionalErrorEncW bits d).size} {(optionalErrorEncW bits d).align}",
     flag "nonzero" (nonzero && ownBytes), flag "distinct" distinct,
     flag "le_code" (ownBytes && codesOk && nerr ≤ errCapacity bits && (tbl.size ≤ 1000 → tableOk)),
     flag "null_zero" optNull, flag "some_eq_plain" optSome,
     flag "roundtrip" (nerr ≤ errCapacity bits && (tbl.size ≤ 1000 → tableOk))] ++
    (match c.body.find? (·.startsWith "code ") with | some l => [l] | none => []) ++
    payloads.map (fun (nm, ps, pa) =>
      let (eo, po) := errUnionOffsetsW bits ps pa
      s!"eu {nm} {ps} {pa} {errUnionSizeW bits ps pa} {Nat.max pa a} {eo} {if ps == 0 then "-" else toString po}") ++
    [s!"bound zero {castAt 0}", s!"bound count {nerr}",
     s!"bound above {nerr + 1} {castAt (nerr + 1)}",
     s!"bound max {maxCode} {castAt maxCode}", s!"bound over {maxCode + 1} {castAt (maxCode + 1)}"] ++
    tableLines

private def mismatches (hidden : Nat) (c : Cfg) : List String :=
  let model := expected hidden c
  let seen := head c c.status :: c.body
  -- The `code` line is the compiler's numbering: copied, then bounds-checked below.
  let modelOnly := model.filter (!seen.contains ·)
  let nativeOnly := seen.filter (!model.contains ·)
  let lines := modelOnly.map (s!"{c.name} | model: {·}") ++ nativeOnly.map (s!"{c.name} | native: {·}")
  match (model.zip seen).find? (fun (a, b) => a != b) with
  | some (a, b) => if lines.isEmpty then [s!"{c.name} | order differs: model {a} / native {b}"] else lines
  | none => lines

def main (args : List String) : IO UInt32 := do
  let printOnly := args.contains "--print-mismatches"
  let files := args.filter (· ≠ "--print-mismatches")
  let (path, expectFile) ← match files with
    | [p] => pure (p, none)
    | [p, e] => pure (p, some e)
    | _ => throw (IO.userError "usage: Model.lean [--print-mismatches] OBSERVED [EXPECTED_MISMATCHES]")
  let (hidden, cfgs) := parseFile (← IO.FS.readFile path)
  let got := cfgs.flatMap (mismatches hidden)
  if printOnly then
    got.forM IO.println
    return 0
  let want ← match expectFile with
    | some e => pure ((← IO.FS.readFile e).splitOn "\n" |>.filter (· ≠ ""))
    | none => pure []
  let unexpected := got.filter (!want.contains ·)
  let vanished := want.filter (!got.contains ·)
  unexpected.forM fun l => IO.eprintln s!"unexpected mismatch: {l}"
  vanished.forM fun l => IO.eprintln s!"expected mismatch no longer occurs: {l}"
  if unexpected.isEmpty && vanished.isEmpty then
    IO.println s!"error-width: {cfgs.length} configurations of {path} match the model \
      ({want.length} documented mismatches)"
    return 0
  return 1
