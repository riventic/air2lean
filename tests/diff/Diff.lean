import Lean.Data.Json
import Air2Lean.Air.Json
import Proofs.Basic.Gen
import Proofs.Recursion.Gen
import Proofs.Options.Gen
import Proofs.Errors.Gen
import Proofs.Floatops.Gen
import Proofs.Floatconv.Gen
import Proofs.Floats.Gen

/-!
# Differential-test Lean-side runner

Companion to `tests/diff/<ex>/harness.zig` (docs/generated-code.md names the functions per
example). Reads the same `tests/diff/<ex>/inputs/<fn>.jsonl` files
(tests/diff/gen_inputs.zig), calls the generated `<Ex>.<fn>`, and writes
`tests/diff/out/lean/<ex>/<fn>.jsonl`: one line per input, one of `{"ok": v}` /
`{"fail": "<error>"}` / `{"diverge": true}` (the `none` case of `Zig.Result` — non-termination).

A `u64`/`usize` `ok` value (`sum`, `totalWeightedTardiness`, the options functions) is quoted
as a decimal string for JS-safety, matching common.zig's `renderPayload`. `isEven`/`isOdd`
return `Bool`, rendered as `0`/`1`. An optional renders as `null` or its value, an error union
as `{"err":"Name"}` or its value. A float leaf (`floatops`, `floatconv`, `floats`) renders as
`"nan"` (any NaN) or `"0x"` + zero-padded lowercase hex of its bits (docs/floats.md); a
`[]const f64` argument (`dot`) is a JSON array of such tokens, and a `u64`/`i64`/`u128`
argument (the int-to-float conversions) is a quoted decimal string, the input-side mirror of
the `u64`/`usize` output-quoting rule above.

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

def getStr (j : Json) : IO String := orFail j.getStr? "getStr"

/-- A diff-protocol float argument: `"0x"` + hex bits, width from `fmt` (docs/floats.md). -/
def getFloat (fmt : Zig.FloatFmt) (j : Json) : IO (Zig.Float fmt) := do
  let s ← getStr j
  let bits ← orFail (Air2Lean.Raw.parseHexNat "diff" fmt.width s) s!"float hex {s}"
  pure (Zig.Float.ofBits (BitVec.ofNat fmt.width bits))

/-- A `u64`/`i64`/`u128` argument: quoted decimal (gen_inputs.zig's rule for any `>= 64`-bit
int argument), the input-side mirror of `natStr`'s `wide` output quoting below. -/
def getWideInt (j : Json) : IO Int := do
  let s ← getStr j
  match s.toInt? with
  | some n => pure n
  | none => throw (IO.userError s!"getWideInt: not an int: {s}")

def hexDigitChar (d : Nat) : Char :=
  if d < 10 then Char.ofNat (d + '0'.toNat) else Char.ofNat (d - 10 + 'a'.toNat)

/-- `n`'s value as exactly `digits` hex digits, most significant first, zero-padded. -/
def natToHex (n digits : Nat) : String :=
  let rec go (n k : Nat) (acc : List Char) : List Char :=
    match k with
    | 0 => acc
    | k + 1 => go (n / 16) k (hexDigitChar (n % 16) :: acc)
  String.ofList (go n digits [])

def getField (j : Json) (k : String) : IO Int := do
  let f ← orFail (j.getObjVal? k) s!"field {k}"
  getInt f

def jobOf (j : Json) : IO Basic.Job := do
  let duration ← getField j "duration"
  let due ← getField j "due"
  let weight ← getField j "weight"
  pure { duration := bv 32 duration, due := bv 32 due, weight := bv 8 weight }

/-- Render a `Zig.Result` outcome as one JSONL line; `payload` renders the `ok` value as
common.zig's `renderPayload` writes it. -/
def renderOk {α : Type} (r : Zig.Result α) (payload : α → String) : String :=
  match r.run with
  | none => "{\"diverge\":true}"
  | some (.error e) => "{\"fail\":\"" ++ reprStr e ++ "\"}"
  | some (.ok v) => "{\"ok\":" ++ payload v ++ "}"

/-- An integer value; `wide`: quoted (u64 results). -/
def natStr {n : Nat} (v : BitVec n) (wide : Bool) : String :=
  if wide then "\"" ++ toString v.toNat ++ "\"" else toString v.toNat

def render {n : Nat} (r : Zig.Result (BitVec n)) (wide : Bool) : String :=
  renderOk r (natStr · wide)

/-- A signed integer value (a Zig `iN` result, e.g. `toI32`'s `i32`): two's-complement decoding
of the `BitVec`, matching `renderPayload`'s `{d}` on a signed Zig int. -/
def renderSigned {n : Nat} (r : Zig.Result (BitVec n)) : String :=
  renderOk r fun v => toString v.toInt

/-- A `bool` as `0`/`1`. -/
def renderBool (r : Zig.Result Bool) : String :=
  renderOk r fun v => if v then "1" else "0"

def optStr {n : Nat} (v : Option (BitVec n)) (wide : Bool) : String :=
  match v with
  | none => "null"
  | some x => natStr x wide

def errStr {n : Nat} (v : Except Zig.ErrName (BitVec n)) (wide : Bool) : String :=
  match v with
  | .error name => "{\"err\":\"" ++ name ++ "\"}"
  | .ok x => natStr x wide

/-- A float leaf: `"nan"` (any NaN bit pattern) or `"0x"` + zero-padded lowercase hex of its
bits (docs/floats.md; common.zig's `renderPayload` mirrors this). -/
def floatStr {fmt : Zig.FloatFmt} (v : Zig.Float fmt) : String :=
  if v.isNaN then "\"nan\"" else "\"0x" ++ natToHex v.bits.toNat (fmt.width / 4) ++ "\""

/-- `?T` for a float `T`: `null` or the payload's own float rendering. -/
def optFloatStr {fmt : Zig.FloatFmt} (v : Option (Zig.Float fmt)) : String :=
  match v with
  | none => "null"
  | some x => floatStr x

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
    pure (renderOk (Errors.parseDigit (bv 8 c)) (errStr · false))

def runSumDigits : IO Unit :=
  processFile "errors" "sumDigits" fun j => do
    let items ← getArr j
    let s ← (← getArr items[0]!).mapM fun v => return bv 8 (← getInt v)
    pure (renderOk (Errors.sumDigits s) (errStr · false))

def runDigitOrZero : IO Unit :=
  processFile "errors" "digitOrZero" fun j => do
    let items ← getArr j
    let c ← getInt items[0]!
    pure (render (Errors.digitOrZero (bv 8 c)) false)

/-- `sel a b c` shared shape of `op16`/`op32`/`op64`/`op80`/`op128` (`examples/floatops`): a
`u8` opcode plus three same-format float operands (unused ones filled with `0`, gen_inputs.zig). -/
def runFloatOp (fmt : Zig.FloatFmt) (name : String)
    (f : BitVec 8 → Zig.Float fmt → Zig.Float fmt → Zig.Float fmt → Zig.Result (Zig.Float fmt)) :
    IO Unit :=
  processFile "floatops" name fun j => do
    let items ← getArr j
    let sel ← getInt items[0]!
    let a ← getFloat fmt items[1]!
    let b ← getFloat fmt items[2]!
    let c ← getFloat fmt items[3]!
    pure (renderOk (f (bv 8 sel) a b c) floatStr)

def runOp16 : IO Unit := runFloatOp .f16 "op16" Floatops.op16
def runOp32 : IO Unit := runFloatOp .f32 "op32" Floatops.op32
def runOp64 : IO Unit := runFloatOp .f64 "op64" Floatops.op64
def runOp80 : IO Unit := runFloatOp .f80 "op80" Floatops.op80
def runOp128 : IO Unit := runFloatOp .f128 "op128" Floatops.op128

def runCmp64 : IO Unit :=
  processFile "floatops" "cmp64" fun j => do
    let items ← getArr j
    let a ← getFloat .f64 items[0]!
    let b ← getFloat .f64 items[1]!
    pure (render (Floatops.cmp64 a b) false)

def runDivExact64 : IO Unit :=
  processFile "floatops" "divExact64" fun j => do
    let items ← getArr j
    let a ← getFloat .f64 items[0]!
    let b ← getFloat .f64 items[1]!
    pure (renderOk (Floatops.divExact64 a b) floatStr)

def runToI32 : IO Unit :=
  processFile "floatconv" "toI32" fun j => do
    let items ← getArr j
    let x ← getFloat .f64 items[0]!
    pure (renderSigned (Floatconv.toI32 x))

def runToU64 : IO Unit :=
  processFile "floatconv" "toU64" fun j => do
    let items ← getArr j
    let x ← getFloat .f32 items[0]!
    pure (render (Floatconv.toU64 x) true)

def runToByte : IO Unit :=
  processFile "floatconv" "toByte" fun j => do
    let items ← getArr j
    let x ← getFloat .f32 items[0]!
    pure (render (Floatconv.toByte x) false)

def runFromI64 : IO Unit :=
  processFile "floatconv" "fromI64" fun j => do
    let items ← getArr j
    let x ← getWideInt items[0]!
    pure (renderOk (Floatconv.fromI64 (bv 64 x)) floatStr)

def runFromU128 : IO Unit :=
  processFile "floatconv" "fromU128" fun j => do
    let items ← getArr j
    let x ← getWideInt items[0]!
    pure (renderOk (Floatconv.fromU128 (bv 128 x)) floatStr)

def runF64ToF16 : IO Unit :=
  processFile "floatconv" "f64ToF16" fun j => do
    let items ← getArr j
    let x ← getFloat .f64 items[0]!
    pure (renderOk (Floatconv.f64ToF16 x) floatStr)

def runF16ToF128 : IO Unit :=
  processFile "floatconv" "f16ToF128" fun j => do
    let items ← getArr j
    let x ← getFloat .f16 items[0]!
    pure (renderOk (Floatconv.f16ToF128 x) floatStr)

def runF80ToF64 : IO Unit :=
  processFile "floatconv" "f80ToF64" fun j => do
    let items ← getArr j
    let x ← getFloat .f80 items[0]!
    pure (renderOk (Floatconv.f80ToF64 x) floatStr)

def runBits32 : IO Unit :=
  processFile "floatconv" "bits32" fun j => do
    let items ← getArr j
    let x ← getFloat .f32 items[0]!
    pure (render (Floatconv.bits32 x) false)

def runOfBits64 : IO Unit :=
  processFile "floatconv" "ofBits64" fun j => do
    let items ← getArr j
    let x ← getWideInt items[0]!
    pure (renderOk (Floatconv.ofBits64 (bv 64 x)) floatStr)

def runLerp : IO Unit :=
  processFile "floats" "lerp" fun j => do
    let items ← getArr j
    let a ← getFloat .f64 items[0]!
    let b ← getFloat .f64 items[1]!
    let t ← getFloat .f64 items[2]!
    pure (renderOk (Floats.lerp a b t) floatStr)

def runClamp : IO Unit :=
  processFile "floats" "clamp" fun j => do
    let items ← getArr j
    let x ← getFloat .f32 items[0]!
    let lo ← getFloat .f32 items[1]!
    let hi ← getFloat .f32 items[2]!
    pure (renderOk (Floats.clamp x lo hi) floatStr)

def runIsNan : IO Unit :=
  processFile "floats" "isNan" fun j => do
    let items ← getArr j
    let x ← getFloat .f64 items[0]!
    pure (renderBool (Floats.isNan x))

def runHypot2 : IO Unit :=
  processFile "floats" "hypot2" fun j => do
    let items ← getArr j
    let a ← getFloat .f64 items[0]!
    let b ← getFloat .f64 items[1]!
    pure (renderOk (Floats.hypot2 a b) floatStr)

def runCelsius : IO Unit :=
  processFile "floats" "celsius" fun j => do
    let items ← getArr j
    let k ← getFloat .f32 items[0]!
    pure (renderOk (Floats.celsius k) optFloatStr)

def runDot : IO Unit :=
  processFile "floats" "dot" fun j => do
    let items ← getArr j
    let xs ← (← getArr items[0]!).mapM (getFloat .f64)
    let ys ← (← getArr items[1]!).mapM (getFloat .f64)
    pure (renderOk (Floats.dot xs ys) floatStr)

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

  IO.FS.createDirAll "tests/diff/out/lean/floatops"
  DiffTest.runOp16
  DiffTest.runOp32
  DiffTest.runOp64
  DiffTest.runOp80
  DiffTest.runOp128
  DiffTest.runCmp64
  DiffTest.runDivExact64

  IO.FS.createDirAll "tests/diff/out/lean/floatconv"
  DiffTest.runToI32
  DiffTest.runToU64
  DiffTest.runToByte
  DiffTest.runFromI64
  DiffTest.runFromU128
  DiffTest.runF64ToF16
  DiffTest.runF16ToF128
  DiffTest.runF80ToF64
  DiffTest.runBits32
  DiffTest.runOfBits64

  IO.FS.createDirAll "tests/diff/out/lean/floats"
  DiffTest.runLerp
  DiffTest.runClamp
  DiffTest.runIsNan
  DiffTest.runHypot2
  DiffTest.runCelsius
  DiffTest.runDot
