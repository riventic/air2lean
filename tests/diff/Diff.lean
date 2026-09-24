import Lean.Data.Json
import Proofs.Basic.Gen

/-!
# Differential-test Lean-side runner

Companion to `tests/diff/harness.zig` (docs/generated-code.md names the 8 functions). Reads the
same `tests/diff/inputs/<fn>.jsonl` files (tests/diff/gen_inputs.zig), calls the generated
`Basic.<fn>`, and writes `tests/diff/out/lean/<fn>.jsonl`: one line per input, one of
`{"ok": v}` / `{"fail": "<error>"}` / `{"diverge": true}` (the `none` case of `Zig.Result` —
non-termination; none of these 8 functions recurse, so it should never actually appear).

`sum` and `totalWeightedTardiness` return `BitVec 64`; their `ok` value is quoted as a decimal
string for JS-safety, matching gen_inputs.zig / harness.zig's convention for wide results.

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

/-- Read `tests/diff/inputs/<name>.jsonl`, write `tests/diff/out/lean/<name>.jsonl`: `step` runs
once per non-empty input line and returns the already-rendered output line. -/
def processFile (name : String) (step : Json → IO String) : IO Unit := do
  let inPath := "tests/diff/inputs/" ++ name ++ ".jsonl"
  let outPath := "tests/diff/out/lean/" ++ name ++ ".jsonl"
  let raw ← IO.FS.lines inPath
  IO.FS.withFile outPath .write fun h => do
    for line in raw do
      if line.trimAscii.isEmpty then continue
      let j ← orFail (Json.parse line) s!"{name}: parse {line}"
      let out ← step j
      h.putStrLn out

def runScale : IO Unit :=
  processFile "scale" fun j => do
    let items ← getArr j
    let a ← getInt items[0]!
    let b ← getInt items[1]!
    pure (render (Basic.scale (bv 32 a) (bv 8 b)) false)

def runClampAdd : IO Unit :=
  processFile "clampAdd" fun j => do
    let items ← getArr j
    let a ← getInt items[0]!
    let b ← getInt items[1]!
    pure (render (Basic.clampAdd (bv 16 a) (bv 16 b)) false)

def runAbsDiff : IO Unit :=
  processFile "absDiff" fun j => do
    let items ← getArr j
    let a ← getInt items[0]!
    let b ← getInt items[1]!
    pure (render (Basic.absDiff (bv 32 a) (bv 32 b)) false)

def runTardiness : IO Unit :=
  processFile "tardiness" fun j => do
    let items ← getArr j
    let a ← getInt items[0]!
    let b ← getInt items[1]!
    pure (render (Basic.tardiness (bv 32 a) (bv 32 b)) false)

def runWeightedTardiness : IO Unit :=
  processFile "weightedTardiness" fun j => do
    let items ← getArr j
    let job ← jobOf items[0]!
    let start ← getInt items[1]!
    pure (render (Basic.weightedTardiness job (bv 32 start)) false)

def runSum : IO Unit :=
  processFile "sum" fun j => do
    let items ← getArr j
    let xsJson ← getArr items[0]!
    let xs ← xsJson.mapM fun v => return bv 32 (← getInt v)
    pure (render (Basic.sum xs) true)

def runTotalWeightedTardiness : IO Unit :=
  processFile "totalWeightedTardiness" fun j => do
    let items ← getArr j
    let jobsJson ← getArr items[0]!
    let jobs ← jobsJson.mapM jobOf
    pure (render (Basic.totalWeightedTardiness jobs) true)

def runClassify : IO Unit :=
  processFile "classify" fun j => do
    let items ← getArr j
    let x ← getInt items[0]!
    pure (render (Basic.classify (bv 8 x)) false)

end DiffTest

def main : IO Unit := do
  IO.FS.createDirAll "tests/diff/out/lean"
  DiffTest.runScale
  DiffTest.runClampAdd
  DiffTest.runAbsDiff
  DiffTest.runTardiness
  DiffTest.runWeightedTardiness
  DiffTest.runSum
  DiffTest.runTotalWeightedTardiness
  DiffTest.runClassify
