import Lean.Data.Json
import Proofs.Basic.Gen
import Proofs.Recursion.Gen
import Proofs.Options.Gen
import Proofs.Errors.Gen

/-!
# Differential-test Lean-side runner

Companion to `tests/diff/<ex>/harness.zig` (docs/generated-code.md names the functions per
example). Reads the same `tests/diff/<ex>/inputs/<fn>.jsonl` files
(tests/diff/gen_inputs.zig), calls the generated `<Ex>.<fn>`, and writes
`tests/diff/out/lean/<ex>/<fn>.jsonl`: one line per input, one of `{"ok": v}` /
`{"fail": "<error>"}` / `{"diverge": true}` (the `none` case of `Zig.Result` — non-termination).

`sum` and `totalWeightedTardiness` (basic) return `BitVec 64`; their `ok` value is quoted as a
decimal string for JS-safety, matching gen_inputs.zig / harness.zig's convention for wide
results. `isEven`/`isOdd` (recursion) return `Bool`, rendered as `0`/`1` — `renderBool` below,
matching common.zig's `renderPayload` on the Zig side.

Only basic and recursion are wired up here: the translator does not yet support options
(optionals) or errors (error unions), so `Proofs.Options.Gen`/`Proofs.Errors.Gen` don't exist —
see docs/generated-code.md's diff-test section.

This tool has no external user, only its own generator and this file as producer/consumer — a
parse failure here is a bug in one of the two, not bad data, so it fails loudly (`IO.userError`)
rather than skipping a line.

Run: `lake exe difftest` from `tests/diff/` (its own Lake package, see lakefile.toml), or via
`scripts/diff.sh` from the repo root.
-/

open Lean (Json)

namespace DiffTest

def orFail {α : Type} (r : Except String α) (ctx : String) : IO α :=
  match r with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{ctx}: {e}")

/-- Every Zig `uN`/`iN` param is a `BitVec N` (docs/generated-code.md); signedness only affects
which two's-complement value a JSON int denotes, not the Lean type. `BitVec.ofInt` wraps either
sign into that representation, so this one helper covers both. -/
def bv (n : Nat) (i : Int) : BitVec n := BitVec.ofInt n i

def getInt (j : Json) : IO Int := orFail j.getInt? "getInt"

def getArr (j : Json) : IO (Array Json) := orFail j.getArr? "getArr"

def getField (j : Json) (k : String) : IO Int := do
  let f ← orFail (j.getObjVal? k) s!"field {k}"
  getInt f

def jobOf (j : Json) : IO Basic.Job := do
  let duration ← getField j "duration"
  let due ← getField j "due"
  let weight ← getField j "weight"
  pure { duration := bv 32 duration, due := bv 32 due, weight := bv 8 weight }

/-- Render a `Zig.Result` outcome as one JSONL line. `wide`: quote the value (u64 results). -/
def render {n : Nat} (r : Zig.Result (BitVec n)) (wide : Bool) : String :=
  match r.run with
  | none => "{\"diverge\":true}"
  | some (.error e) => "{\"fail\":\"" ++ reprStr e ++ "\"}"
  | some (.ok v) =>
    if wide then "{\"ok\":\"" ++ toString v.toNat ++ "\"}" else "{\"ok\":" ++ toString v.toNat ++ "}"

/-- `Bool`-result variant of `render` (recursion's isEven/isOdd), matching common.zig's
`renderPayload`'s `0`/`1` encoding for `bool` on the Zig side. -/
def renderBool (r : Zig.Result Bool) : String :=
  match r.run with
  | none => "{\"diverge\":true}"
  | some (.error e) => "{\"fail\":\"" ++ reprStr e ++ "\"}"
  | some (.ok v) => if v then "{\"ok\":1}" else "{\"ok\":0}"

/-- The `ok` payload of an optional or error-union result, as common.zig's `renderPayload`
writes it: `null`, `{"err":"Name"}`, or the plain value. -/
def renderOk {α : Type} (r : Zig.Result α) (payload : α → String) : String :=
  match r.run with
  | none => "{\"diverge\":true}"
  | some (.error e) => "{\"fail\":\"" ++ reprStr e ++ "\"}"
  | some (.ok v) => "{\"ok\":" ++ payload v ++ "}"

def natStr {n : Nat} (v : BitVec n) (wide : Bool) : String :=
  if wide then "\"" ++ toString v.toNat ++ "\"" else toString v.toNat

def optStr {n : Nat} (v : Option (BitVec n)) (wide : Bool) : String :=
  match v with
  | none => "null"
  | some x => natStr x wide

def errStr {n : Nat} (v : Except Zig.ErrName (BitVec n)) : String :=
  match v with
  | .error name => "{\"err\":\"" ++ name ++ "\"}"
  | .ok x => natStr x false

/-- Read `tests/diff/<ex>/inputs/<name>.jsonl`, write `tests/diff/out/lean/<ex>/<name>.jsonl`:
`step` runs once per non-empty input line and returns the already-rendered output line. -/
def processFile (ex name : String) (step : Json → IO String) : IO Unit := do
  let inPath := "tests/diff/" ++ ex ++ "/inputs/" ++ name ++ ".jsonl"
  let outPath := "tests/diff/out/lean/" ++ ex ++ "/" ++ name ++ ".jsonl"
  let raw ← IO.FS.lines inPath
  IO.FS.withFile outPath .write fun h => do
    for line in raw do
      if line.trimAscii.isEmpty then continue
      let j ← orFail (Json.parse line) s!"{ex}.{name}: parse {line}"
      let out ← step j
      h.putStrLn out

def runScale : IO Unit :=
  processFile "basic" "scale" fun j => do
    let items ← getArr j
    let a ← getInt items[0]!
    let b ← getInt items[1]!
    pure (render (Basic.scale (bv 32 a) (bv 8 b)) false)

def runClampAdd : IO Unit :=
  processFile "basic" "clampAdd" fun j => do
    let items ← getArr j
    let a ← getInt items[0]!
    let b ← getInt items[1]!
    pure (render (Basic.clampAdd (bv 16 a) (bv 16 b)) false)

def runAbsDiff : IO Unit :=
  processFile "basic" "absDiff" fun j => do
    let items ← getArr j
    let a ← getInt items[0]!
    let b ← getInt items[1]!
    pure (render (Basic.absDiff (bv 32 a) (bv 32 b)) false)

def runTardiness : IO Unit :=
  processFile "basic" "tardiness" fun j => do
    let items ← getArr j
    let a ← getInt items[0]!
    let b ← getInt items[1]!
    pure (render (Basic.tardiness (bv 32 a) (bv 32 b)) false)

def runWeightedTardiness : IO Unit :=
  processFile "basic" "weightedTardiness" fun j => do
    let items ← getArr j
    let job ← jobOf items[0]!
    let start ← getInt items[1]!
    pure (render (Basic.weightedTardiness job (bv 32 start)) false)

def runSum : IO Unit :=
  processFile "basic" "sum" fun j => do
    let items ← getArr j
    let xsJson ← getArr items[0]!
    let xs ← xsJson.mapM fun v => return bv 32 (← getInt v)
    pure (render (Basic.sum xs) true)

def runTotalWeightedTardiness : IO Unit :=
  processFile "basic" "totalWeightedTardiness" fun j => do
    let items ← getArr j
    let jobsJson ← getArr items[0]!
    let jobs ← jobsJson.mapM jobOf
    pure (render (Basic.totalWeightedTardiness jobs) true)

def runClassify : IO Unit :=
  processFile "basic" "classify" fun j => do
    let items ← getArr j
    let x ← getInt items[0]!
    pure (render (Basic.classify (bv 8 x)) false)

def runGcd : IO Unit :=
  processFile "recursion" "gcd" fun j => do
    let items ← getArr j
    let a ← getInt items[0]!
    let b ← getInt items[1]!
    pure (render (Recursion.gcd (bv 32 a) (bv 32 b)) false)

def runIsEven : IO Unit :=
  processFile "recursion" "isEven" fun j => do
    let items ← getArr j
    let n ← getInt items[0]!
    pure (renderBool (Recursion.isEven (bv 32 n)))

def runIsOdd : IO Unit :=
  processFile "recursion" "isOdd" fun j => do
    let items ← getArr j
    let n ← getInt items[0]!
    pure (renderBool (Recursion.isOdd (bv 32 n)))

def runFact : IO Unit :=
  processFile "recursion" "fact" fun j => do
    let items ← getArr j
    let n ← getInt items[0]!
    pure (render (Recursion.fact (bv 32 n)) false)

/-- `(xs, x)` inputs of the options functions. -/
def xsAndX (j : Json) : IO (Array (BitVec 32) × BitVec 32) := do
  let items ← getArr j
  let xs ← (← getArr items[0]!).mapM fun v => return bv 32 (← getInt v)
  pure (xs, bv 32 (← getInt items[1]!))

def runFind : IO Unit :=
  processFile "options" "find" fun j => do
    let (xs, x) ← xsAndX j
    pure (renderOk (Options.find xs x) (optStr · true))

def runFindOr : IO Unit :=
  processFile "options" "findOr" fun j => do
    let (xs, x) ← xsAndX j
    pure (render (Options.findOr xs x) true)

def runFirstIndexPlusOne : IO Unit :=
  processFile "options" "firstIndexPlusOne" fun j => do
    let (xs, x) ← xsAndX j
    pure (render (Options.firstIndexPlusOne xs x) true)

def runParseDigit : IO Unit :=
  processFile "errors" "parseDigit" fun j => do
    let items ← getArr j
    let c ← getInt items[0]!
    pure (renderOk (Errors.parseDigit (bv 8 c)) errStr)

def runSumDigits : IO Unit :=
  processFile "errors" "sumDigits" fun j => do
    let items ← getArr j
    let s ← (← getArr items[0]!).mapM fun v => return bv 8 (← getInt v)
    pure (renderOk (Errors.sumDigits s) errStr)

def runDigitOrZero : IO Unit :=
  processFile "errors" "digitOrZero" fun j => do
    let items ← getArr j
    let c ← getInt items[0]!
    pure (render (Errors.digitOrZero (bv 8 c)) false)

end DiffTest

def main : IO Unit := do
  IO.FS.createDirAll "tests/diff/out/lean/basic"
  DiffTest.runScale
  DiffTest.runClampAdd
  DiffTest.runAbsDiff
  DiffTest.runTardiness
  DiffTest.runWeightedTardiness
  DiffTest.runSum
  DiffTest.runTotalWeightedTardiness
  DiffTest.runClassify

  IO.FS.createDirAll "tests/diff/out/lean/recursion"
  DiffTest.runGcd
  DiffTest.runIsEven
  DiffTest.runIsOdd
  DiffTest.runFact

  IO.FS.createDirAll "tests/diff/out/lean/options"
  DiffTest.runFind
  DiffTest.runFindOr
  DiffTest.runFirstIndexPlusOne

  IO.FS.createDirAll "tests/diff/out/lean/errors"
  DiffTest.runParseDigit
  DiffTest.runSumDigits
  DiffTest.runDigitOrZero
