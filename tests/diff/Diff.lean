import Lean.Data.Json
import Air2Lean.Air.Json
import Proofs.Basic.Gen
import Proofs.Recursion.Gen
import Proofs.Options.Gen
import Proofs.Errors.Gen
import Proofs.Floatops.Gen
import Proofs.Floatconv.Gen
import Proofs.Floats.Gen
import Proofs.Variants.Gen
import Proofs.Pointers.Gen
import Proofs.Slices.Gen
import Proofs.Lists.Gen
import Proofs.Threads.Gen
import Proofs.Vectors.Gen
import Proofs.Asm.Gen
import Proofs.Layout.Gen

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

/-! ## Asm's diff-test-only implementation

`Proofs/Asm/Gen.lean`'s `Asm.airAsm_*` opaques carry no defining equation in the main pipeline —
M21's whole point is that a proof gets only what the caller states about one, no built-in
axiom. For the differential test to actually run, though, an executable needs real behaviour, the
same problem `ZigLean/Float/Libm.lean` solves for the transcendental ops. That file's
`@[implemented_by]` is attached inline, at the opaque's own declaration, in the same module — it
does not apply here: `Asm.airAsm_*` are auto-generated pipeline output, declared in
`Proofs/Asm/Gen.lean`, a module already imported by the time this file runs, and both
`@[implemented_by]` and `@[extern]` refuse to attach to a declaration from an imported module
(`Lean.throwAttrDeclInImportedModule`; the same `ParametricAttribute` machinery backs both).

`@[csimp]` does not have that restriction: it tags a fresh theorem (declared here, not imported)
stating `@f = @g`, and swaps `f` for `g` in compiled code only, never in the kernel or type theory
(its doc comment). The theorem needs a real proof term, and there is none — an asm opaque's whole
point is that no equation is derivable from the main pipeline alone — so this is the one place in
the repo that assumes rather than proves, via `sorry` (the unsound path `@[csimp]`'s own doc
comment names). Confined to this diff-test package, never `ZigLean`/`Proofs`
(`scripts/no-sorry.sh` checks only those two dirs), and load-bearing only for turning the archive's
real implementation into what the differential test runs against `examples/asm/asm.zig`'s inline
asm — not for anything the main pipeline emits or proves.

Raw `@[extern]` opaques into `tests/diff/asm/asm.zig`'s archive (docs/generated-code.md §Inline
asm), marshaled through `UInt32`/`UInt64` — everything here fits one register, unlike libm's
f80/f128 hi/lo split. -/

@[extern "air2lean_asm_bswap32"] private opaque asmBswap32 : UInt32 → UInt32
@[extern "air2lean_asm_popcnt64"] private opaque asmPopcnt64 : UInt64 → UInt64
@[extern "air2lean_asm_lzcnt64"] private opaque asmLzcnt64 : UInt64 → UInt64

private def airAsm_3500345798_impl (x : BitVec 32) : BitVec 32 :=
  (asmBswap32 (.ofBitVec x)).toBitVec

private def airAsm_3884223243_impl (x : BitVec 64) : BitVec 64 :=
  (asmLzcnt64 (.ofBitVec x)).toBitVec

private def airAsm_4040357768_impl (x : BitVec 64) : BitVec 64 :=
  (asmPopcnt64 (.ofBitVec x)).toBitVec

@[csimp] theorem airAsm_3500345798_eq : @Asm.airAsm_3500345798 = @airAsm_3500345798_impl := sorry
@[csimp] theorem airAsm_3884223243_eq : @Asm.airAsm_3884223243 = @airAsm_3884223243_impl := sorry
@[csimp] theorem airAsm_4040357768_eq : @Asm.airAsm_4040357768 = @airAsm_4040357768_impl := sorry

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

/-! ### vectors: every function takes/returns `@Vector(4, T)` (examples/vectors/vectors.zig) -/

/-- A `@Vector(4, α)` from 4 already-parsed lanes, lane 0 first (Zig's lane order; matches
`common.zig`'s `renderPayload` and `tests/diff/gen_inputs.zig`'s writer). -/
def vec4 {α : Type} (a b c d : α) : Zig.Vec α 4 := ⟨#v[a, b, c, d]⟩

/-- A `@Vector(4, uN/iN)` argument: a JSON array of 4 bare ints. -/
def intVecOf (n : Nat) (j : Json) : IO (Zig.Vec (BitVec n) 4) := do
  let items ← getArr j
  pure (vec4 (bv n (← getInt items[0]!)) (bv n (← getInt items[1]!))
    (bv n (← getInt items[2]!)) (bv n (← getInt items[3]!)))

/-- A `@Vector(4, fN)` argument: a JSON array of 4 float-hex strings. -/
def floatVecOf (fmt : Zig.FloatFmt) (j : Json) : IO (Zig.Vec (Zig.Float fmt) 4) := do
  let items ← getArr j
  pure (vec4 (← getFloat fmt items[0]!) (← getFloat fmt items[1]!)
    (← getFloat fmt items[2]!) (← getFloat fmt items[3]!))

/-- A `@Vector(4, uN/iN)` result: a JSON array of 4 ints, lane 0 first, matching
`common.zig`'s `renderPayload` `.vector` case. -/
def vecStr {n : Nat} (v : Zig.Vec (BitVec n) 4) : String :=
  "[" ++ ",".intercalate (v.lanes.toArray.toList.map (natStr · false)) ++ "]"

def renderVec {n : Nat} (r : Zig.Result (Zig.Vec (BitVec n) 4)) : String :=
  renderOk r vecStr

def runFDot : IO Unit :=
  processFile "vectors" "fDot" fun j => do
    let items ← getArr j
    let a ← floatVecOf .f32 items[0]!
    let b ← floatVecOf .f32 items[1]!
    pure (renderOk (Vectors.fDot a b) floatStr)

def runUDotWrap : IO Unit :=
  processFile "vectors" "uDotWrap" fun j => do
    let items ← getArr j
    let a ← intVecOf 32 items[0]!
    let b ← intVecOf 32 items[1]!
    pure (render (Vectors.uDotWrap a b) false)

def runSatAdd : IO Unit :=
  processFile "vectors" "satAdd" fun j => do
    let items ← getArr j
    let a ← intVecOf 32 items[0]!
    let b ← intVecOf 32 items[1]!
    pure (renderVec (Vectors.satAdd a b))

def runMaxLane : IO Unit :=
  processFile "vectors" "maxLane" fun j => do
    let items ← getArr j
    let v ← intVecOf 32 items[0]!
    pure (renderSigned (Vectors.maxLane v))

def runReverse : IO Unit :=
  processFile "vectors" "reverse" fun j => do
    let items ← getArr j
    let v ← intVecOf 32 items[0]!
    pure (renderVec (Vectors.reverse v))

def runCheckedAdd : IO Unit :=
  processFile "vectors" "checkedAdd" fun j => do
    let items ← getArr j
    let a ← intVecOf 32 items[0]!
    let b ← intVecOf 32 items[1]!
    pure (renderVec (Vectors.checkedAdd a b))

/-- A `@Vector(4, bool)` argument: a JSON array of 4 bools. -/
def boolVecOf (j : Json) : IO (Zig.Vec Bool 4) := do
  let items ← getArr j
  let b (x : Json) : IO Bool := match x with
    | .bool v => pure v
    | _ => throw (IO.userError s!"not a bool: {x.compress}")
  pure (vec4 (← b items[0]!) (← b items[1]!) (← b items[2]!) (← b items[3]!))

/-- The coverage functions (`examples/vectors/vectors.zig` after `checkedAdd`). -/
def runVectorCoverage : IO Unit := do
  let ex := "vectors"
  processFile ex "splatAdd" fun j => do
    let items ← getArr j
    pure (renderVec (Vectors.splatAdd (← intVecOf 32 items[0]!) (bv 32 (← getInt items[1]!))))
  processFile ex "pick" fun j => do
    let items ← getArr j
    pure (renderVec (Vectors.pick (← boolVecOf items[0]!) (← intVecOf 32 items[1]!)
      (← intVecOf 32 items[2]!)))
  processFile ex "interleave" fun j => do
    let items ← getArr j
    pure (renderVec (Vectors.interleave (← intVecOf 32 items[0]!) (← intVecOf 32 items[1]!)))
  processFile ex "andLanes" fun j => do
    pure (render (Vectors.andLanes (← intVecOf 32 (← getArr j)[0]!)) false)
  processFile ex "orLanes" fun j => do
    pure (render (Vectors.orLanes (← intVecOf 32 (← getArr j)[0]!)) false)
  processFile ex "xorLanes" fun j => do
    pure (render (Vectors.xorLanes (← intVecOf 32 (← getArr j)[0]!)) false)
  processFile ex "minLane" fun j => do
    pure (renderSigned (Vectors.minLane (← intVecOf 32 (← getArr j)[0]!)))
  processFile ex "uMinLane" fun j => do
    pure (render (Vectors.uMinLane (← intVecOf 32 (← getArr j)[0]!)) false)
  processFile ex "fMin" fun j => do
    pure (renderOk (Vectors.fMin (← floatVecOf .f32 (← getArr j)[0]!)) floatStr)
  processFile ex "fMax" fun j => do
    pure (renderOk (Vectors.fMax (← floatVecOf .f32 (← getArr j)[0]!)) floatStr)
  -- A memory function: run from `mem0`.
  processFile ex "twiceInMem" fun j => do
    pure (renderVec ((Vectors.twiceInMem (← intVecOf 32 (← getArr j)[0]!)).run' Vectors.mem0))

/-! ### variants: an enum is its tag value; a `Shape` is an object with its active field -/

def lightOf (j : Json) : IO Variants.Light := do
  match Variants.Light.ofInt? (← getInt j) with
  | some l => pure l
  | none => throw (IO.userError s!"not a Light: {j.compress}")

def prioOf (j : Json) : IO Variants.Prio := do
  match Variants.Prio.ofInt? (← getInt j) with
  | some p => pure p
  | none => throw (IO.userError s!"not a Prio: {j.compress}")

def shapeOf (j : Json) : IO Variants.Shape := do
  let size (k : String) : IO (BitVec 32) := do pure (bv 32 (← getField j k))
  if (j.getObjVal? "circle").isOk then return .circle (← size "circle")
  if (j.getObjVal? "square").isOk then return .square (← size "square")
  if (j.getObjVal? "empty").isOk then return .empty
  let r ← orFail (j.getObjVal? "rect") "shape"
  pure (.rect { w := bv 32 (← getField r "w"), h := bv 32 (← getField r "h") })

def shapeStr : Variants.Shape → String
  | .circle r => s!"\{\"circle\":{r.toNat}}"
  | .rect r => s!"\{\"rect\":\{\"w\":{r.w.toNat},\"h\":{r.h.toNat}}}"
  | .square a => s!"\{\"square\":{a.toNat}}"
  | .empty => "{\"empty\":null}"

def runVariants : IO Unit := do
  processFile "variants" "next" fun j => do
    let items ← getArr j
    pure (renderOk (Variants.next (← lightOf items[0]!)) (natStr ·.toBits false))
  processFile "variants" "advance" fun j => do
    let items ← getArr j
    let n ← getInt items[1]!
    pure (renderOk (Variants.advance (← lightOf items[0]!) (bv 32 n)) (natStr ·.toBits false))
  processFile "variants" "lightOf" fun j => do
    let items ← getArr j
    pure (renderOk (Variants.lightOf (bv 8 (← getInt items[0]!))) (natStr ·.toBits false))
  processFile "variants" "prioValue" fun j => do
    let items ← getArr j
    pure (renderSigned (Variants.prioValue (← prioOf items[0]!)))
  processFile "variants" "isUrgent" fun j => do
    let items ← getArr j
    pure (renderBool (Variants.isUrgent (← prioOf items[0]!)))
  processFile "variants" "severity" fun j => do
    let items ← getArr j
    pure (render (Variants.severity ⟨bv 8 (← getInt items[0]!)⟩) false)
  processFile "variants" "codeOf" fun j => do
    let items ← getArr j
    pure (renderOk (Variants.codeOf (bv 8 (← getInt items[0]!))) (natStr ·.toBits false))
  processFile "variants" "area" fun j => do
    let items ← getArr j
    pure (render (Variants.area (← shapeOf items[0]!)) true)
  processFile "variants" "totalArea" fun j => do
    let items ← getArr j
    let shapes ← (← getArr items[0]!).mapM shapeOf
    pure (render (Variants.totalArea shapes) true)
  processFile "variants" "scale" fun j => do
    let items ← getArr j
    let k ← getInt items[1]!
    pure (renderOk (Variants.scale (← shapeOf items[0]!) (bv 32 k)) shapeStr)
  processFile "variants" "radius" fun j => do
    let items ← getArr j
    pure (render (Variants.radius (← shapeOf items[0]!)) false)
  processFile "variants" "isRound" fun j => do
    let items ← getArr j
    pure (renderBool (Variants.isRound (← shapeOf items[0]!)))

/-! ### Memory: `{"bufs":[…],"args":[…]}` (docs/generated-code.md §Differential test)

The memory at the start is the example's `mem0`: its `g` globals are blocks `0 … g-1`. Input
buffer `i` is block `g + i`. -/

/-- One 16-byte aligned block per input buffer, after the globals of `m0`. The allocator did not
make it (`.stack`, not `.heap`): a free of it throws `.illegal`, as `TestAllocator` panics. -/
def memOf (m0 : Zig.Mem) (bufs : Array (Array (BitVec 8))) : IO Zig.Mem := do
  let act : Zig.MemM Unit := bufs.forM fun bytes => do
    let p ← Zig.alloc .stack bytes.size 16
    Zig.storeBytes p 1 (bytes.map .int)
  match (act.run m0).run with
  | some (.ok (_, m)) => pure m
  | _ => throw (IO.userError "memOf: cannot make the input buffers")

/-- A pointer argument `{"buf":i,"off":o}`, after `g` globals. -/
def ptrOf (g : Nat) (j : Json) : IO Zig.Ptr := do
  pure ⟨some (g + (← getField j "buf").toNat), ← getField j "off"⟩

/-- An optional pointer argument: `null` or a pointer. -/
def optPtrOf (g : Nat) (j : Json) : IO (Option Zig.Ptr) :=
  if j.isNull then pure none else some <$> ptrOf g j

/-- A slice argument `{"buf":i,"off":o,"len":n}`, after `g` globals. -/
def sliceOf (g : Nat) (j : Json) : IO Zig.Slice := do
  pure ⟨← ptrOf g j, bv 64 (← getField j "len")⟩

/-- A byte as two hex digits; `??` for an undefined byte (it matches any Zig byte, diff.sh). -/
def byteStr : Zig.Byte → String
  | .int x => natToHex x.toNat 2
  | .undef => "??"
  | .ptrFrag .. => "pp"

/-- A pointer result, the same as common.zig writes it: `{"buf":i,"off":o}` (with `"len":n` for
a slice) into the input buffers, else `{"bytes":"<hex>"}`, the `size` bytes at the pointer (a
global, or a heap block of the allocator). -/
def ptrStr (g : Nat) (m : Zig.Mem) (p : Zig.Ptr) (size : Nat) (len : Option Nat := none) :
    String :=
  let lenStr := match len with | some n => s!",\"len\":{n}" | none => ""
  match p.block with
  | some b =>
    if g ≤ b && (m.blocks[b]?.map (·.kind != .heap)).getD true then
      s!"\{\"buf\":{b - g},\"off\":{p.off}{lenStr}}"
    else
      let bytes := (m.blocks[b]?.map (·.bytes)).getD #[]
      let o := p.off.toNat
      "{\"bytes\":\"" ++ String.join ((bytes.extract o (o + size)).toList.map byteStr) ++ "\"}"
  -- An allocation of 0 bytes has no block (`Zig.zeroAllocPtr`).
  | none => if size = 0 then "{\"bytes\":\"\"}" else "\"outside the buffers\""

/-- A slice result of items of `size` bytes (`ptrStr`). -/
def sliceStr (g : Nat) (m : Zig.Mem) (size : Nat) (s : Zig.Slice) : String :=
  ptrStr g m s.ptr (size * s.len.toNat) (some s.len.toNat)

/-- `renderOk` for a function that uses memory: the result, then the bytes of the `n` input
buffers after the call (blocks `g` to `g + n - 1`). `heap`: then the number of live blocks of the
allocator, `,"live":<n>`. -/
def renderMem {α : Type} (g n : Nat) (r : Zig.Result (α × Zig.Mem)) (payload : Zig.Mem → α → String)
    (heap : Bool := false) : String :=
  match r.run with
  | none => "{\"diverge\":true}"
  | some (.error e) => "{\"fail\":\"" ++ reprStr e ++ "\"}"
  | some (.ok (v, m)) =>
    let bufs := (m.blocks.extract g (g + n)).toList.map fun blk =>
      "\"" ++ String.join (blk.bytes.toList.map byteStr) ++ "\""
    let live := if heap then s!",\"live\":{(m.blocks.filter fun b => b.kind == .heap && b.live).size}"
      else ""
    "{\"ok\":" ++ payload m v ++ ",\"bufs\":[" ++ ",".intercalate bufs ++ "]" ++ live ++ "}"

/-- Run `call` on each line of `tests/diff/<ex>/inputs/<name>.jsonl` of a function that uses
memory, from the memory `m0` of the example. `call` gets the number of globals. `heap`: the
function takes an allocator (`renderMem`). -/
def processMem {α : Type} (ex : String) (m0 : Zig.Mem) (name : String)
    (call : Nat → Array Json → IO (Zig.MemM α)) (payload : Zig.Mem → α → String)
    (heap : Bool := false) : IO Unit :=
  processFile ex name fun j => do
    let bufsJ ← getArr (← orFail (j.getObjVal? "bufs") "bufs")
    let bufs ← bufsJ.mapM fun b => do (← getArr b).mapM fun x => return bv 8 (← getInt x)
    let args ← getArr (← orFail (j.getObjVal? "args") "args")
    let g := m0.blocks.size
    pure (renderMem g bufs.size ((← call g args).run (← memOf m0 bufs)) payload heap)

def unitStr (_ : Zig.Mem) (_ : Unit) : String := "null"

def runPointers : IO Unit := do
  let ex := "pointers"
  let m0 := Pointers.mem0
  processMem ex m0 "swap" (fun g a => return Pointers.swap (← ptrOf g a[0]!) (← ptrOf g a[1]!)) unitStr
  processMem ex m0 "delay"
    (fun g a => return Pointers.delay (← ptrOf g a[0]!) (bv 32 (← getInt a[1]!))) unitStr
  processMem ex m0 "maxPtr" (fun g a => return Pointers.maxPtr (← optPtrOf g a[0]!) (← optPtrOf g a[1]!))
    fun m p => match p with | none => "null" | some p => ptrStr m0.blocks.size m p 4
  processMem ex m0 "dueOf" (fun g a => return Pointers.dueOf (← ptrOf g a[0]!)) fun m p => ptrStr m0.blocks.size m p 4
  processMem ex m0 "sumTo" (fun _ a => return Pointers.sumTo (bv 32 (← getInt a[0]!))) fun _ v => natStr v true
  processMem ex m0 "copyJob" (fun g a => return Pointers.copyJob (← ptrOf g a[0]!) (← ptrOf g a[1]!))
    unitStr
  processMem ex m0 "bumpOpt" (fun g a => return Pointers.bumpOpt (← ptrOf g a[0]!)) unitStr
  processMem ex m0 "setOpt" (fun g a => do
      let x ← if a[1]!.isNull then pure none else pure (some (bv 32 (← getInt a[1]!)))
      return Pointers.setOpt (← ptrOf g a[0]!) x) unitStr
  processMem ex m0 "same" (fun g a => return Pointers.same (← ptrOf g a[0]!) (← ptrOf g a[1]!))
    fun _ b => if b then "1" else "0"
  processMem ex m0 "setOptJob"
    (fun g a => return Pointers.setOptJob (← ptrOf g a[0]!) (bv 32 (← getInt a[1]!))) unitStr
  processMem ex m0 "addDown"
    (fun g a => return Pointers.addDown (← ptrOf g a[0]!) (bv 32 (← getInt a[1]!))) unitStr

/-- A pure function in the memory protocol (no buffers). -/
def pureMem {α : Type} (r : Zig.Result α) : Zig.MemM α := StateT.lift r

def runLayout : IO Unit := do
  let ex := "layout"
  let m0 := Layout.mem0
  let ptrRes (size : Nat) (m : Zig.Mem) (p : Zig.Ptr) := ptrStr m0.blocks.size m p size
  processMem ex m0 "addrEq" (fun g a => return Layout.addrEq (← ptrOf g a[0]!) (← ptrOf g a[1]!))
    fun _ b => if b then "1" else "0"
  processMem ex m0 "ptrRoundTrip" (fun g a => return Layout.ptrRoundTrip (← ptrOf g a[0]!))
    (ptrRes 4)
  processMem ex m0 "ptrFromAddr"
    (fun _ a => return Layout.ptrFromAddr (bv 64 (← getWideInt a[0]!))) (ptrRes 4)
  processMem ex m0 "asConst" (fun g a => return Layout.asConst (← ptrOf g a[0]!)) (ptrRes 4)
  processMem ex m0 "dropConst" (fun g a => return Layout.dropConst (← ptrOf g a[0]!)) (ptrRes 4)
  processMem ex m0 "asVolatile" (fun g a => return Layout.asVolatile (← ptrOf g a[0]!)) (ptrRes 4)
  processMem ex m0 "align4" (fun g a => return Layout.align4 (← ptrOf g a[0]!)) (ptrRes 4)
  processMem ex m0 "parentOfX" (fun g a => return Layout.parentOfX (← ptrOf g a[0]!)) (ptrRes 8)
  processMem ex m0 "parentOfY" (fun g a => return Layout.parentOfY (← ptrOf g a[0]!)) (ptrRes 8)
  -- `Flags` field by field from a byte (not `Zig.Packed.ofBits`, which is what the tests check).
  let flagsOf (b : Nat) : Layout.Flags :=
    { ready := b % 2 == 1, err := b / 2 % 2 == 1, mode := BitVec.ofNat 2 (b / 4), count := BitVec.ofNat 4 (b / 16) }
  let b01 (b : Bool) := if b then "1" else "0"
  let flagsStr (_ : Zig.Mem) (f : Layout.Flags) : String :=
    s!"\{\"ready\":{b01 f.ready},\"err\":{b01 f.err},\"mode\":{f.mode.toNat},\"count\":{f.count.toNat}}"
  processMem ex m0 "flagsToByte"
    (fun _ a => return pureMem (Layout.flagsToByte (flagsOf (← getInt a[0]!).toNat))) fun _ v => natStr v false
  processMem ex m0 "byteToFlags"
    (fun _ a => return pureMem (Layout.byteToFlags (bv 8 (← getInt a[0]!)))) flagsStr
  processMem ex m0 "setMode"
    (fun _ a => return pureMem (Layout.setMode (bv 8 (← getInt a[0]!)) (bv 2 (← getInt a[1]!))))
    fun _ v => natStr v false
  processMem ex m0 "incCount" (fun g a => return Layout.incCount (← ptrOf g a[0]!)) unitStr
  processMem ex m0 "isOk" (fun g a => return Layout.isOk (← ptrOf g a[0]!)) fun _ b => b01 b

def runSlices : IO Unit := do
  let ex := "slices"
  let m0 := Slices.mem0
  let u32 (_ : Zig.Mem) (v : BitVec 32) := natStr v false
  let bytes (m : Zig.Mem) (s : Zig.Slice) := sliceStr m0.blocks.size m 1 s
  processMem ex m0 "reverse" (fun g a => return Slices.reverse (← sliceOf g a[0]!)) unitStr
  processMem ex m0 "fill" (fun g a => return Slices.fill (← sliceOf g a[0]!) (bv 8 (← getInt a[1]!))) unitStr
  processMem ex m0 "clear" (fun g a => return Slices.clear (← sliceOf g a[0]!)) unitStr
  processMem ex m0 "copyWithin" (fun g a => return (Slices.copyWithin (← sliceOf g a[0]!)
    (bv 64 (← getInt a[1]!)) (bv 64 (← getInt a[2]!)) (bv 64 (← getInt a[3]!)))) unitStr
  processMem ex m0 "copy" (fun g a => return Slices.copy (← sliceOf g a[0]!) (← sliceOf g a[1]!)) unitStr
  processMem ex m0 "indexOfScalar" (fun _ a => return Slices.indexOfScalar (bv 8 (← getInt a[0]!)))
    fun _ v => optStr v true
  processMem ex m0 "factorial" (fun _ a => return pureMem (Slices.factorial (bv 64 (← getInt a[0]!))))
    fun _ v => natStr v false
  processMem ex m0 "bump" (fun _ _ => return Slices.bump) u32
  processMem ex m0 "sumZ" (fun g a => return Slices.sumZ (← ptrOf g a[0]!)) u32
  processMem ex m0 "subZ" (fun g a => return (Slices.subZ (← sliceOf g a[0]!)
    (bv 64 (← getInt a[1]!)) (bv 64 (← getInt a[2]!)))) bytes
  processMem ex m0 "sumMid" (fun g a => return Slices.sumMid (← sliceOf g a[0]!)) u32
  processMem ex m0 "total" (fun g a => return Slices.total (← ptrOf g a[0]!)) u32
  processMem ex m0 "at" (fun g a => return Slices.«at» (← ptrOf g a[0]!) (bv 64 (← getInt a[1]!))) u32
  processMem ex m0 "second" (fun g a => return Slices.second (← ptrOf g a[0]!)) u32
  processMem ex m0 "prevItem" (fun g a => return Slices.prevItem (← ptrOf g a[0]!)) u32
  processMem ex m0 "colorName" (fun _ a => do
      let c ← match (← getInt a[0]!) with
        | 0 => pure Slices.Color.red | 1 => pure .green | _ => pure .blue
      return Slices.colorName c) bytes
  processMem ex m0 "failName" (fun _ a => return Slices.failName (bv 8 (← getInt a[0]!))) bytes
  processMem ex m0 "bumpAt" (fun g a => return Slices.bumpAt (← ptrOf g a[0]!) (bv 64 (← getInt a[1]!)))
    fun _ v => natStr v false
  processMem ex m0 "localArr" (fun _ a => return Slices.localArr (bv 64 (← getInt a[0]!)))
    fun _ v => natStr v false
  processMem ex m0 "lenOr" (fun g a => do
      let s ← if a[0]!.isNull then pure none else some <$> sliceOf g a[0]!
      return Slices.lenOr s) fun _ v => natStr v true

/-- A function that takes an allocator: `args[0]` is the allocation that fails, `null` or its
number (`Zig.Mem.failAt`). -/
def withFailAt {α : Type} (fa : Json) (r : Zig.MemM α) : IO (Zig.MemM α) := do
  let f ← if fa.isNull then pure none else some <$> (Int.toNat <$> getInt fa)
  return (do modify fun m => { m with failAt := f }; r)

def runLists : IO Unit := do
  let ex := "lists"
  let m0 := Lists.mem0
  let a : Zig.Allocator := {}
  let wide (_ : Zig.Mem) (v : Except Zig.ErrName (BitVec 64)) := errStr v true
  let items (size : Nat) (m : Zig.Mem) : Except Zig.ErrName Zig.Slice → String
    | .error e => "{\"err\":\"" ++ e ++ "\"}"
    | .ok s => sliceStr m0.blocks.size m size s
  processMem ex m0 "sumRange"
    (fun _ x => do withFailAt x[0]! (Lists.sumRange a (bv 64 (← getInt x[1]!)))) wide (heap := true)
  processMem ex m0 "dupe" (fun g x => do withFailAt x[0]! (Lists.dupe a (← sliceOf g x[1]!)))
    (items 1) (heap := true)
  processMem ex m0 "evens" (fun g x => do withFailAt x[0]! (Lists.evens a (← sliceOf g x[1]!)))
    (items 4) (heap := true)
  processMem ex m0 "listSum" (fun g x => do withFailAt x[0]! (Lists.listSum a (← sliceOf g x[1]!)))
    wide (heap := true)

/-- `renderOk` for a `Zig.MemM` function with no buffer/allocator args (`examples/threads`): runs
it from a fresh `mem0`, then discards the final memory. A model rejection (`.illegal`, a
non-atomic race; `.nondet`, a non-commuting concurrent atomic op; `.illegal`, a thread that the
main thread did not join before the function returned) is the outer `Zig.Error`, the same as
`renderOk`'s (docs/std-models.md §Thread model). -/
def renderThread {α : Type} (m0 : Zig.Mem) (r : Zig.MemM α) (payload : α → String) : String :=
  let r := do let v ← r; Zig.Thread.checkJoinedByChild 0; pure v
  match (r.run m0).run with
  | none => "{\"diverge\":true}"
  | some (.error e) => "{\"fail\":\"" ++ reprStr e ++ "\"}"
  | some (.ok (v, _)) => "{\"ok\":" ++ payload v ++ "}"

def runParallelCounter : IO Unit :=
  processFile "threads" "parallelCounter" fun j => do
    let items ← getArr j
    let n ← getInt items[0]!
    pure (renderThread Threads.mem0 (Threads.parallelCounter (bv 32 n)) (errStr · false))

def runRace : IO Unit :=
  processFile "threads" "race" fun j => do
    let items ← getArr j
    let a ← getInt items[0]!
    let b ← getInt items[1]!
    pure (renderThread Threads.mem0 (Threads.race (bv 32 a) (bv 32 b)) (errStr · false))

def runXchgRace : IO Unit :=
  processFile "threads" "xchgRace" fun j => do
    let items ← getArr j
    let a ← getInt items[0]!
    let b ← getInt items[1]!
    pure (renderThread Threads.mem0 (Threads.xchgRace (bv 32 a) (bv 32 b)) (errStr · false))

-- Calls the opaque directly (`Asm.airAsm_*`), not the generated wrapper (`Asm.bswap32` etc.):
-- the wrapper's own body is compiled once, inside `Proofs/Asm/Gen.lean`, before this file's
-- `@[csimp]` swap exists to see -- `@[csimp]` only redirects references compiled after it, so a
-- call already baked into the wrapper stays on the opaque's own placeholder value (`Inhabited`'s
-- default; the `airAsm_*_eq` theorems above never fire there). A direct call from this file *is*
-- compiled after the swap, so it does. The wrapper itself is one-line pass-through boilerplate
-- (`let i1 ← pure (airAsm_* p0); pure (.ret i1)`) shared in shape with every other example's
-- generated code, already exercised by every other example's diff test -- calling the opaque
-- directly here still compares the real archive's behaviour against `examples/asm/asm.zig`'s
-- actual inline asm, which is the property this test exists to check.
def runBswap32 : IO Unit :=
  processFile "asm" "bswap32" fun j => do
    let items ← getArr j
    let x ← getInt items[0]!
    pure (render (pure (Asm.airAsm_3500345798 (bv 32 x)) : Zig.Result (BitVec 32)) false)

def runPopcnt64 : IO Unit :=
  processFile "asm" "popcnt64" fun j => do
    let items ← getArr j
    let x ← getWideInt items[0]!
    pure (render (pure (Asm.airAsm_4040357768 (bv 64 x)) : Zig.Result (BitVec 64)) true)

def runLzcnt64 : IO Unit :=
  processFile "asm" "lzcnt64" fun j => do
    let items ← getArr j
    let x ← getWideInt items[0]!
    pure (render (pure (Asm.airAsm_3884223243 (bv 64 x)) : Zig.Result (BitVec 64)) true)

end DiffTest

/-- Runs the examples named in `AIR2LEAN_EXAMPLES` (space-separated, the same variable as
`scripts/diff.sh`), or all of them if it is unset or empty. -/
def main : IO Unit := do
  let only := ((← IO.getEnv "AIR2LEAN_EXAMPLES").getD "").splitOn " " |>.filter (· != "")
  let run (ex : String) (tests : IO Unit) : IO Unit := do
    if only.isEmpty || only.contains ex then
      IO.FS.createDirAll s!"tests/diff/out/lean/{ex}"
      tests

  run "basic" do
    DiffTest.runScale
    DiffTest.runClampAdd
    DiffTest.runAbsDiff
    DiffTest.runTardiness
    DiffTest.runWeightedTardiness
    DiffTest.runSum
    DiffTest.runTotalWeightedTardiness
    DiffTest.runClassify

  run "recursion" do
    DiffTest.runGcd
    DiffTest.runIsEven
    DiffTest.runIsOdd
    DiffTest.runFact

  run "options" do
    DiffTest.runFind
    DiffTest.runFindOr
    DiffTest.runFirstIndexPlusOne

  run "errors" do
    DiffTest.runParseDigit
    DiffTest.runSumDigits
    DiffTest.runDigitOrZero

  run "floatops" do
    DiffTest.runOp16
    DiffTest.runOp32
    DiffTest.runOp64
    DiffTest.runOp80
    DiffTest.runOp128
    DiffTest.runCmp64
    DiffTest.runDivExact64

  run "floatconv" do
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

  run "variants" DiffTest.runVariants

  run "pointers" DiffTest.runPointers

  run "slices" DiffTest.runSlices

  run "lists" DiffTest.runLists

  run "threads" do
    DiffTest.runParallelCounter
    DiffTest.runRace
    DiffTest.runXchgRace

  run "floats" do
    DiffTest.runLerp
    DiffTest.runClamp
    DiffTest.runIsNan
    DiffTest.runHypot2
    DiffTest.runCelsius
    DiffTest.runDot

  run "vectors" do
    DiffTest.runFDot
    DiffTest.runUDotWrap
    DiffTest.runSatAdd
    DiffTest.runMaxLane
    DiffTest.runReverse
    DiffTest.runCheckedAdd
    DiffTest.runVectorCoverage

  run "asm" do
    DiffTest.runBswap32
    DiffTest.runPopcnt64
    DiffTest.runLzcnt64

  run "layout" DiffTest.runLayout

