import ZigLean.Float

/-!
# Float-model executable check

Two parts:

1. **Differential test** — for `f32`/`f64` (the two formats Lean core's own `Float32.Model`/
   `Float.Model` also implement), compare `Zig.Float`'s `add sub mul div sqrt lt le eq ofInt`
   against core's, over a curated edge-case bit array (pairwise) plus ~100k fixed-seed random
   bit patterns per op (`mkStdGen`, so a failing run reproduces).
2. **Hand-checked spot checks** — everything a differential test against core can't reach:
   ops core doesn't have (`min`/`max`'s Zig-specific zero tiebreak, `round`, `rem`, `mod`,
   `divTrunc`, `divFloor`, `fma`), NaN-producing results (unspecified sign/payload, so checked
   via `isNaN` only), and `f16`/`f80`/`f128` (formats core has no model for at all — this is the
   *only* ground truth for `f80`/`f128` `sqrt`, and for `fma`'s `f16`/`f80` double-rounding
   route). Expected values are copied verbatim from `tests/floatprobe/expected.txt` (a real
   run on the reference platform) or, for the `+0`/`-0` table, from `docs/floats.md`.

Exits 1 if anything disagrees; 0 otherwise.
-/

open Zig (FloatFmt)

/-! ## Hex helpers -/

private def hexDigit (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- Parse a plain (no `0x`) hex literal, e.g. one copied from `expected.txt`. -/
def parseHex (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + hexDigit c) 0

private def hexChar (n : Nat) : Char :=
  "0123456789abcdef".toList.getD n '?'

/-- Zero-padded lowercase hex, `width` digits. -/
def toHex (width n : Nat) : String :=
  String.ofList (((List.range width).reverse).map (fun i => hexChar ((n >>> (4 * i)) % 16)))

/-! ## Differential harness (f32 / f64 vs Lean core) -/

/-- Checked/diff counts for one named group, printed at the end. -/
structure Group where
  label : String
  checked : Nat
  diffs : Nat

def Group.report (g : Group) : IO Unit :=
  IO.println s!"{g.label}: {g.checked} checked, {g.diffs} diffs"

/-- Binary numeric op over raw bit patterns (`Nat`, format-erased — the caller's closures decode
and re-encode the actual float type). Pairwise over `edges`, then `randCount` random pairs in
`[0, bound]`, threading `gen` forward so the caller can chain more checks off the same stream. -/
def checkBinaryNumeric (label : String) (mine core : Nat → Nat → Nat) (edges : Array Nat)
    (bound randCount : Nat) (gen : StdGen) (hexW : Nat) : IO (Group × StdGen) := do
  let mut checked := 0
  let mut diffs := 0
  for a in edges do
    for b in edges do
      checked := checked + 1
      let m := mine a b
      let c := core a b
      unless m == c do
        diffs := diffs + 1
        if diffs ≤ 10 then
          IO.println
            s!"DIFF {label}(0x{toHex hexW a}, 0x{toHex hexW b}) mine=0x{toHex hexW m} core=0x{toHex hexW c}"
  let mut g := gen
  for _ in [0:randCount] do
    let (a, g1) := randNat g 0 bound
    let (b, g2) := randNat g1 0 bound
    g := g2
    checked := checked + 1
    let m := mine a b
    let c := core a b
    unless m == c do
      diffs := diffs + 1
      if diffs ≤ 10 then
        IO.println
          s!"DIFF {label}(0x{toHex hexW a}, 0x{toHex hexW b}) mine=0x{toHex hexW m} core=0x{toHex hexW c}"
  pure ({ label, checked, diffs }, g)

/-- Unary numeric op over raw bit patterns. -/
def checkUnaryNumeric (label : String) (mine core : Nat → Nat) (edges : Array Nat)
    (bound randCount : Nat) (gen : StdGen) (hexW : Nat) : IO (Group × StdGen) := do
  let mut checked := 0
  let mut diffs := 0
  for a in edges do
    checked := checked + 1
    let m := mine a
    let c := core a
    unless m == c do
      diffs := diffs + 1
      if diffs ≤ 10 then
        IO.println s!"DIFF {label}(0x{toHex hexW a}) mine=0x{toHex hexW m} core=0x{toHex hexW c}"
  let mut g := gen
  for _ in [0:randCount] do
    let (a, g1) := randNat g 0 bound
    g := g1
    checked := checked + 1
    let m := mine a
    let c := core a
    unless m == c do
      diffs := diffs + 1
      if diffs ≤ 10 then
        IO.println s!"DIFF {label}(0x{toHex hexW a}) mine=0x{toHex hexW m} core=0x{toHex hexW c}"
  pure ({ label, checked, diffs }, g)

/-- Binary predicate over raw bit patterns (`lt`/`le`/`eq`). -/
def checkBinaryBool (label : String) (mine core : Nat → Nat → Bool) (edges : Array Nat)
    (bound randCount : Nat) (gen : StdGen) (hexW : Nat) : IO (Group × StdGen) := do
  let mut checked := 0
  let mut diffs := 0
  for a in edges do
    for b in edges do
      checked := checked + 1
      let m := mine a b
      let c := core a b
      unless m == c do
        diffs := diffs + 1
        if diffs ≤ 10 then
          IO.println s!"DIFF {label}(0x{toHex hexW a}, 0x{toHex hexW b}) mine={m} core={c}"
  let mut g := gen
  for _ in [0:randCount] do
    let (a, g1) := randNat g 0 bound
    let (b, g2) := randNat g1 0 bound
    g := g2
    checked := checked + 1
    let m := mine a b
    let c := core a b
    unless m == c do
      diffs := diffs + 1
      if diffs ≤ 10 then
        IO.println s!"DIFF {label}(0x{toHex hexW a}, 0x{toHex hexW b}) mine={m} core={c}"
  pure ({ label, checked, diffs }, g)

/-! ### f32 wiring -/

def edgesF32 : Array Nat :=
  #[0, 0x80000000, 0x3f800000, 0xbf800000, 0x40000000, 0xc0000000, 0x3f000000, 0xbf000000,
    0x00000001, 0x80000001, 0x007fffff, 0x807fffff, 0x00800000, 0x80800000,
    0x7f7fffff, 0xff7fffff, 0x7f800000, 0xff800000, 0x7fc00000, 0xffc00000,
    0x7fa00000, 0x00400000]

def mineF32 (op : Zig.F32 → Zig.F32 → Zig.F32) (a b : Nat) : Nat :=
  (op ⟨.ofNat 32 a⟩ ⟨.ofNat 32 b⟩).bits.toNat

def coreF32 (op : Float32.Model → Float32.Model → Float32.Model) (a b : Nat) : Nat :=
  (op (Float32.Model.ofBits (UInt32.ofNat a)) (Float32.Model.ofBits (UInt32.ofNat b))).toBits.toNat

def mineF32Unary (op : Zig.F32 → Zig.F32) (a : Nat) : Nat :=
  (op ⟨.ofNat 32 a⟩).bits.toNat

def coreF32Unary (op : Float32.Model → Float32.Model) (a : Nat) : Nat :=
  (op (Float32.Model.ofBits (UInt32.ofNat a))).toBits.toNat

def mineF32Bool (op : Zig.F32 → Zig.F32 → Bool) (a b : Nat) : Bool :=
  op ⟨.ofNat 32 a⟩ ⟨.ofNat 32 b⟩

def coreF32Bool (op : Float32.Model → Float32.Model → Bool) (a b : Nat) : Bool :=
  op (Float32.Model.ofBits (UInt32.ofNat a)) (Float32.Model.ofBits (UInt32.ofNat b))

def edgesInt64 : Array Nat :=
  #[0, 1, 2, 3, 0xffffffffffffffff, 0x7fffffffffffffff, 0x8000000000000000,
    0x8000000000000001, 100, 1000000, 0xffffffff, 0x100000000, 0xfffffffe]

def mineF32OfIntSigned (raw : Nat) : Nat :=
  (Zig.Float.ofInt .f32 true (BitVec.ofNat 64 raw)).bits.toNat

def coreF32OfIntSigned (raw : Nat) : Nat :=
  (Float32.Model.ofInt (BitVec.ofNat 64 raw).toInt).toBits.toNat

def mineF32OfIntUnsigned (raw : Nat) : Nat :=
  (Zig.Float.ofInt .f32 false (BitVec.ofNat 64 raw)).bits.toNat

def coreF32OfIntUnsigned (raw : Nat) : Nat :=
  (Float32.Model.ofInt ((BitVec.ofNat 64 raw).toNat : Int)).toBits.toNat

/-! ### f64 wiring -/

def edgesF64 : Array Nat :=
  #[0, 0x8000000000000000, 0x3ff0000000000000, 0xbff0000000000000,
    0x4000000000000000, 0xc000000000000000, 0x3fe0000000000000, 0xbfe0000000000000,
    0x0000000000000001, 0x8000000000000001, 0x000fffffffffffff, 0x800fffffffffffff,
    0x0010000000000000, 0x8010000000000000, 0x7fefffffffffffff, 0xffefffffffffffff,
    0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000, 0xfff8000000000000,
    0x7ff4000000000000, 0x400921fb54442d18]

def mineF64 (op : Zig.F64 → Zig.F64 → Zig.F64) (a b : Nat) : Nat :=
  (op ⟨.ofNat 64 a⟩ ⟨.ofNat 64 b⟩).bits.toNat

def coreF64 (op : Float.Model → Float.Model → Float.Model) (a b : Nat) : Nat :=
  (op (Float.Model.ofBits (UInt64.ofNat a)) (Float.Model.ofBits (UInt64.ofNat b))).toBits.toNat

def mineF64Unary (op : Zig.F64 → Zig.F64) (a : Nat) : Nat :=
  (op ⟨.ofNat 64 a⟩).bits.toNat

def coreF64Unary (op : Float.Model → Float.Model) (a : Nat) : Nat :=
  (op (Float.Model.ofBits (UInt64.ofNat a))).toBits.toNat

def mineF64Bool (op : Zig.F64 → Zig.F64 → Bool) (a b : Nat) : Bool :=
  op ⟨.ofNat 64 a⟩ ⟨.ofNat 64 b⟩

def coreF64Bool (op : Float.Model → Float.Model → Bool) (a b : Nat) : Bool :=
  op (Float.Model.ofBits (UInt64.ofNat a)) (Float.Model.ofBits (UInt64.ofNat b))

def mineF64OfIntSigned (raw : Nat) : Nat :=
  (Zig.Float.ofInt .f64 true (BitVec.ofNat 64 raw)).bits.toNat

def coreF64OfIntSigned (raw : Nat) : Nat :=
  (Float.Model.ofInt (BitVec.ofNat 64 raw).toInt).toBits.toNat

def mineF64OfIntUnsigned (raw : Nat) : Nat :=
  (Zig.Float.ofInt .f64 false (BitVec.ofNat 64 raw)).bits.toNat

def coreF64OfIntUnsigned (raw : Nat) : Nat :=
  (Float.Model.ofInt ((BitVec.ofNat 64 raw).toNat : Int)).toBits.toNat

/-- Run the full `add sub mul div sqrt lt le eq ofInt(signed) ofInt(unsigned)` battery for one
of `f32`/`f64`, threading `gen` forward. `randCount` is per op (~100k per the task spec). -/
def runDiff32 (gen : StdGen) (randCount : Nat) : IO (Array Group × StdGen) := do
  let mut groups := #[]
  let mut g := gen
  let bound32 := 0xffffffff
  let bound64 := 0xffffffffffffffff
  let (r, g') ← checkBinaryNumeric "f32.add" (mineF32 Zig.Float.add) (coreF32 Float32.Model.add)
    edgesF32 bound32 randCount g 8
  groups := groups.push r; g := g'
  let (r, g') ← checkBinaryNumeric "f32.sub" (mineF32 Zig.Float.sub) (coreF32 Float32.Model.sub)
    edgesF32 bound32 randCount g 8
  groups := groups.push r; g := g'
  let (r, g') ← checkBinaryNumeric "f32.mul" (mineF32 Zig.Float.mul) (coreF32 Float32.Model.mul)
    edgesF32 bound32 randCount g 8
  groups := groups.push r; g := g'
  let (r, g') ← checkBinaryNumeric "f32.div" (mineF32 Zig.Float.div) (coreF32 Float32.Model.div)
    edgesF32 bound32 randCount g 8
  groups := groups.push r; g := g'
  let (r, g') ← checkUnaryNumeric "f32.sqrt" (mineF32Unary Zig.Float.sqrt)
    (coreF32Unary Float32.Model.sqrt) edgesF32 bound32 randCount g 8
  groups := groups.push r; g := g'
  let (r, g') ← checkBinaryBool "f32.lt" (mineF32Bool Zig.Float.lt) (coreF32Bool Float32.Model.lt)
    edgesF32 bound32 randCount g 8
  groups := groups.push r; g := g'
  let (r, g') ← checkBinaryBool "f32.le" (mineF32Bool Zig.Float.le) (coreF32Bool Float32.Model.le)
    edgesF32 bound32 randCount g 8
  groups := groups.push r; g := g'
  let (r, g') ← checkBinaryBool "f32.eq" (mineF32Bool Zig.Float.eq)
    (coreF32Bool Float32.Model.beq) edgesF32 bound32 randCount g 8
  groups := groups.push r; g := g'
  let (r, g') ← checkUnaryNumeric "f32.ofInt.signed" mineF32OfIntSigned coreF32OfIntSigned
    edgesInt64 bound64 randCount g 16
  groups := groups.push r; g := g'
  let (r, g') ← checkUnaryNumeric "f32.ofInt.unsigned" mineF32OfIntUnsigned coreF32OfIntUnsigned
    edgesInt64 bound64 randCount g 16
  groups := groups.push r; g := g'
  pure (groups, g)

def runDiff64 (gen : StdGen) (randCount : Nat) : IO (Array Group × StdGen) := do
  let mut groups := #[]
  let mut g := gen
  let bound64 := 0xffffffffffffffff
  let (r, g') ← checkBinaryNumeric "f64.add" (mineF64 Zig.Float.add) (coreF64 Float.Model.add)
    edgesF64 bound64 randCount g 16
  groups := groups.push r; g := g'
  let (r, g') ← checkBinaryNumeric "f64.sub" (mineF64 Zig.Float.sub) (coreF64 Float.Model.sub)
    edgesF64 bound64 randCount g 16
  groups := groups.push r; g := g'
  let (r, g') ← checkBinaryNumeric "f64.mul" (mineF64 Zig.Float.mul) (coreF64 Float.Model.mul)
    edgesF64 bound64 randCount g 16
  groups := groups.push r; g := g'
  let (r, g') ← checkBinaryNumeric "f64.div" (mineF64 Zig.Float.div) (coreF64 Float.Model.div)
    edgesF64 bound64 randCount g 16
  groups := groups.push r; g := g'
  let (r, g') ← checkUnaryNumeric "f64.sqrt" (mineF64Unary Zig.Float.sqrt)
    (coreF64Unary Float.Model.sqrt) edgesF64 bound64 randCount g 16
  groups := groups.push r; g := g'
  let (r, g') ← checkBinaryBool "f64.lt" (mineF64Bool Zig.Float.lt) (coreF64Bool Float.Model.lt)
    edgesF64 bound64 randCount g 16
  groups := groups.push r; g := g'
  let (r, g') ← checkBinaryBool "f64.le" (mineF64Bool Zig.Float.le) (coreF64Bool Float.Model.le)
    edgesF64 bound64 randCount g 16
  groups := groups.push r; g := g'
  let (r, g') ← checkBinaryBool "f64.eq" (mineF64Bool Zig.Float.eq) (coreF64Bool Float.Model.beq)
    edgesF64 bound64 randCount g 16
  groups := groups.push r; g := g'
  let (r, g') ← checkUnaryNumeric "f64.ofInt.signed" mineF64OfIntSigned coreF64OfIntSigned
    edgesInt64 bound64 randCount g 16
  groups := groups.push r; g := g'
  let (r, g') ← checkUnaryNumeric "f64.ofInt.unsigned" mineF64OfIntUnsigned coreF64OfIntUnsigned
    edgesInt64 bound64 randCount g 16
  groups := groups.push r; g := g'
  pure (groups, g)

/-! ## Hand-checked spot checks

Everything the f32/f64-vs-core differential test above can't reach: ops core has no model of
at all (`min`/`max`'s zero tiebreak, `round`, `rem`, `mod`, `divTrunc`, `divFloor`, `fma`), and
`f16`/`f80`/`f128` (formats core doesn't implement). Expected values are copied verbatim from
`tests/floatprobe/expected.txt`. -/

/-- One format's worth of expected hex bit patterns for the ops below, copied verbatim from
`tests/floatprobe/expected.txt`. -/
structure SpotExpected where
  minPZ_NZ : String
  minNZ_PZ : String
  maxPZ_NZ : String
  maxNZ_PZ : String
  round2_5 : String
  roundNeg2_5 : String
  round0_5 : String
  rem_neg1_3 : String
  mod_neg1_3 : String
  mod_1_neg3 : String
  mod_neg0_3 : String
  mod_neg3_3 : String
  rem_neg3_3 : String
  sqrt2 : String
  sqrt3 : String
  divTrunc_neg7_2 : String
  divFloor_neg7_2 : String
  mulAdd1 : String -- fma(1+eps, 1-eps, -1)
  mulAdd2 : String -- fma(3, 1/3, -1)

def expF16 : SpotExpected where
  minPZ_NZ := "8000"; minNZ_PZ := "8000"; maxPZ_NZ := "0000"; maxNZ_PZ := "0000"
  round2_5 := "4200"; roundNeg2_5 := "c200"; round0_5 := "3c00"
  rem_neg1_3 := "bc00"; mod_neg1_3 := "4000"; mod_1_neg3 := "3c00"
  mod_neg0_3 := "8000"; mod_neg3_3 := "0000"; rem_neg3_3 := "8000"
  sqrt2 := "3da8"; sqrt3 := "3eee"
  divTrunc_neg7_2 := "c200"; divFloor_neg7_2 := "c400"
  mulAdd1 := "8010"; mulAdd2 := "8c00"

def expF32 : SpotExpected where
  minPZ_NZ := "00000000"; minNZ_PZ := "00000000"; maxPZ_NZ := "00000000"; maxNZ_PZ := "00000000"
  round2_5 := "40400000"; roundNeg2_5 := "c0400000"; round0_5 := "3f800000"
  rem_neg1_3 := "bf800000"; mod_neg1_3 := "40000000"; mod_1_neg3 := "3f800000"
  mod_neg0_3 := "80000000"; mod_neg3_3 := "00000000"; rem_neg3_3 := "80000000"
  sqrt2 := "3fb504f3"; sqrt3 := "3fddb3d7"
  divTrunc_neg7_2 := "c0400000"; divFloor_neg7_2 := "c0800000"
  mulAdd1 := "a8800000"; mulAdd2 := "33000000"

def expF64 : SpotExpected where
  minPZ_NZ := "0000000000000000"; minNZ_PZ := "0000000000000000"
  maxPZ_NZ := "0000000000000000"; maxNZ_PZ := "0000000000000000"
  round2_5 := "4008000000000000"; roundNeg2_5 := "c008000000000000"
  round0_5 := "3ff0000000000000"
  rem_neg1_3 := "bff0000000000000"; mod_neg1_3 := "4000000000000000"
  mod_1_neg3 := "3ff0000000000000"
  mod_neg0_3 := "8000000000000000"; mod_neg3_3 := "0000000000000000"
  rem_neg3_3 := "8000000000000000"
  sqrt2 := "3ff6a09e667f3bcd"; sqrt3 := "3ffbb67ae8584caa"
  divTrunc_neg7_2 := "c008000000000000"; divFloor_neg7_2 := "c010000000000000"
  mulAdd1 := "b970000000000000"; mulAdd2 := "bc90000000000000"

def expF80 : SpotExpected where
  minPZ_NZ := "80000000000000000000"; minNZ_PZ := "80000000000000000000"
  maxPZ_NZ := "00000000000000000000"; maxNZ_PZ := "00000000000000000000"
  round2_5 := "4000c000000000000000"; roundNeg2_5 := "c000c000000000000000"
  round0_5 := "3fff8000000000000000"
  rem_neg1_3 := "bfff8000000000000000"; mod_neg1_3 := "40008000000000000000"
  mod_1_neg3 := "3fff8000000000000000"
  mod_neg0_3 := "80000000000000000000"; mod_neg3_3 := "00000000000000000000"
  rem_neg3_3 := "80000000000000000000"
  sqrt2 := "3fffb504f333f9de6484"; sqrt3 := "3fffddb3d742c265539e"
  divTrunc_neg7_2 := "c000c000000000000000"; divFloor_neg7_2 := "c0018000000000000000"
  mulAdd1 := "bf818000000000000000"; mulAdd2 := "3fbe8000000000000000"

def expF128 : SpotExpected where
  minPZ_NZ := "80000000000000000000000000000000"
  minNZ_PZ := "80000000000000000000000000000000"
  maxPZ_NZ := "00000000000000000000000000000000"
  maxNZ_PZ := "00000000000000000000000000000000"
  round2_5 := "40008000000000000000000000000000"
  roundNeg2_5 := "c0008000000000000000000000000000"
  round0_5 := "3fff0000000000000000000000000000"
  rem_neg1_3 := "bfff0000000000000000000000000000"
  mod_neg1_3 := "40000000000000000000000000000000"
  mod_1_neg3 := "3fff0000000000000000000000000000"
  mod_neg0_3 := "80000000000000000000000000000000"
  mod_neg3_3 := "00000000000000000000000000000000"
  rem_neg3_3 := "80000000000000000000000000000000"
  sqrt2 := "3fff6a09e667f3bcd000000000000000"
  sqrt3 := "3fffbb67ae8584caa000000000000000"
  divTrunc_neg7_2 := "c0008000000000000000000000000000"
  divFloor_neg7_2 := "c0010000000000000000000000000000"
  mulAdd1 := "bf1f0000000000000000000000000000"
  mulAdd2 := "bf8d0000000000000000000000000000"

/-- Every op-independent spot check for one format: the `+0`/`-0` min/max tiebreak table,
`round`/`rem`/`mod`/`divTrunc`/`divFloor`/`fma` against `expected.txt`, NaN-loses-to-number in
`min`/`max`, and the NaN-producing family (`0/0`, `inf - inf`, `sqrt(-1)`, `nan + 1`, `-nan`),
checked via `isNaN` only since Zig leaves a NaN's sign/payload unspecified. Returns
`(checked, diffs)`. -/
def runSpotChecks (fmt : FloatFmt) (label : String) (e : SpotExpected) : IO (Nat × Nat) := do
  -- `results` (not two `mut` counters via a nested closure): a closure defined inside a `do`
  -- block cannot mutate an outer `let mut` from Lean's own elaborator's point of view, so each
  -- check's `Bool` is instead pushed here and counted once at the end.
  let mut results : Array Bool := #[]
  let hw := fmt.width / 4
  let bits (x : Zig.Float fmt) : Nat := x.bits.toNat
  let eqHex (l : String) (got : Zig.Float fmt) (exp : String) : IO Bool := do
    let expected := parseHex exp
    unless bits got == expected do
      IO.println s!"SPOT FAIL {l}: got=0x{toHex hw (bits got)} expected=0x{exp}"
    pure (bits got == expected)
  let isNaNCheck (l : String) (got : Zig.Float fmt) : IO Bool := do
    unless got.isNaN do
      IO.println s!"SPOT FAIL {l}: expected isNaN, got=0x{toHex hw (bits got)}"
    pure got.isNaN
  let pz : Zig.Float fmt := Zig.Float.zero false
  let nz : Zig.Float fmt := Zig.Float.zero true
  let one : Zig.Float fmt := Zig.Float.roundRat fmt false 1
  let two : Zig.Float fmt := Zig.Float.roundRat fmt false 2
  let three : Zig.Float fmt := Zig.Float.roundRat fmt false 3
  let seven : Zig.Float fmt := Zig.Float.roundRat fmt false 7
  let half : Zig.Float fmt := Zig.Float.roundRat fmt false (1 / 2 : Rat)
  let twoHalf : Zig.Float fmt := Zig.Float.roundRat fmt false (5 / 2 : Rat)
  let nan : Zig.Float fmt := Zig.Float.nan
  let inf : Zig.Float fmt := Zig.Float.inf false
  let negOne := Zig.Float.neg one
  let negThree := Zig.Float.neg three
  let negSeven := Zig.Float.neg seven
  -- +0 / -0 min/max tiebreak table.
  results := results.push (←eqHex s!"{label}.min(+0,-0)" (Zig.Float.min pz nz) e.minPZ_NZ)
  results := results.push (←eqHex s!"{label}.min(-0,+0)" (Zig.Float.min nz pz) e.minNZ_PZ)
  results := results.push (←eqHex s!"{label}.max(+0,-0)" (Zig.Float.max pz nz) e.maxPZ_NZ)
  results := results.push (←eqHex s!"{label}.max(-0,+0)" (Zig.Float.max nz pz) e.maxNZ_PZ)
  -- min/max: NaN always loses to a number.
  results := results.push (←eqHex s!"{label}.min(nan,1)" (Zig.Float.min nan one) (toHex hw (bits one)))
  results := results.push (←eqHex s!"{label}.min(1,nan)" (Zig.Float.min one nan) (toHex hw (bits one)))
  results := results.push (←eqHex s!"{label}.max(nan,1)" (Zig.Float.max nan one) (toHex hw (bits one)))
  -- round, ties away from zero.
  results := results.push (←eqHex s!"{label}.round(2.5)" (Zig.Float.round twoHalf) e.round2_5)
  results := results.push (←eqHex s!"{label}.round(-2.5)" (Zig.Float.round (Zig.Float.neg twoHalf)) e.roundNeg2_5)
  results := results.push (←eqHex s!"{label}.round(0.5)" (Zig.Float.round half) e.round0_5)
  -- rem / mod.
  results := results.push (←eqHex s!"{label}.rem(-1,3)" (Zig.Float.rem negOne three) e.rem_neg1_3)
  results := results.push (←eqHex s!"{label}.mod(-1,3)" (Zig.Float.mod negOne three) e.mod_neg1_3)
  results := results.push (←eqHex s!"{label}.mod(1,-3)" (Zig.Float.mod one negThree) e.mod_1_neg3)
  results := results.push (←eqHex s!"{label}.mod(-0,3)" (Zig.Float.mod nz three) e.mod_neg0_3)
  results := results.push (←eqHex s!"{label}.mod(-3,3)" (Zig.Float.mod negThree three) e.mod_neg3_3)
  results := results.push (←eqHex s!"{label}.rem(-3,3)" (Zig.Float.rem negThree three) e.rem_neg3_3)
  -- sqrt: the only ground truth for f16/f80/f128.
  results := results.push (←eqHex s!"{label}.sqrt(2)" (Zig.Float.sqrt two) e.sqrt2)
  results := results.push (←eqHex s!"{label}.sqrt(3)" (Zig.Float.sqrt three) e.sqrt3)
  -- divTrunc / divFloor.
  results := results.push (←eqHex s!"{label}.divTrunc(-7,2)" (Zig.Float.divTrunc negSeven two) e.divTrunc_neg7_2)
  results := results.push (←eqHex s!"{label}.divFloor(-7,2)" (Zig.Float.divFloor negSeven two) e.divFloor_neg7_2)
  -- fma: the only ground truth at all (core has no model of it); these two probe the
  -- f16-via-f32 / f80-via-f128 double-rounding route specifically.
  let eps : Zig.Float fmt := Zig.Float.roundRat fmt false ((2 : Rat) ^ (1 - (fmt.prec : Int)))
  let onePlusE := Zig.Float.add one eps
  let oneMinusE := Zig.Float.sub one eps
  let oneThird := Zig.Float.div one three
  results := results.push (←eqHex s!"{label}.fma(1+eps,1-eps,-1)" (Zig.Float.fma onePlusE oneMinusE negOne)
    e.mulAdd1)
  results := results.push (←eqHex s!"{label}.fma(3,1/3,-1)" (Zig.Float.fma three oneThird negOne) e.mulAdd2)
  -- NaN-producing family: sign/payload is unspecified, so only `isNaN` is checked.
  results := results.push (←isNaNCheck s!"{label}.0/0" (Zig.Float.div pz pz))
  results := results.push (←isNaNCheck s!"{label}.inf-inf" (Zig.Float.sub inf inf))
  results := results.push (←isNaNCheck s!"{label}.sqrt(-1)" (Zig.Float.sqrt negOne))
  results := results.push (←isNaNCheck s!"{label}.nan+1" (Zig.Float.add nan one))
  results := results.push (←isNaNCheck s!"{label}.-nan" (Zig.Float.neg nan))
  pure (results.size, results.foldl (init := 0) (fun n b => if b then n else n + 1))

/-- `f80`'s unusual encodings (unnormal, pseudo-infinity, pseudo-NaN, pseudo-denormal — only
possible because `f80` stores its integer bit explicitly): `Float.classify`/`add`'s handling of
them, exercised as `x + 0.0` exactly as `tests/floatprobe/probe.zig` does. The first three
classify as NaN (sign/payload unspecified, so `isNaN`-only); the pseudo-denormal is a definite
finite value with an exact expected bit pattern. -/
def runF80EncodingChecks : IO (Nat × Nat) := do
  let mut checked := 0
  let mut fails := 0
  let nanCases : Array (String × Nat) :=
    #[("unnormal(e=1,i=0)", 0x00010000000000000001),
      ("pseudo-inf", 0x7fff0000000000000000),
      ("pseudo-nan", 0x7fff4000000000000000)]
  for (label, raw) in nanCases do
    checked := checked + 1
    let x : Zig.F80 := ⟨.ofNat 80 raw⟩
    let r := Zig.Float.add x (Zig.Float.zero false)
    unless r.isNaN do
      fails := fails + 1
      IO.println s!"SPOT FAIL f80.{label}: expected isNaN, got=0x{toHex 20 r.bits.toNat}"
  checked := checked + 2
  let pd : Zig.F80 := ⟨.ofNat 80 0x00008000000000000000⟩
  let pdr := Zig.Float.add pd (Zig.Float.zero false)
  let expected := parseHex "00018000000000000000"
  unless pdr.bits.toNat == expected do
    fails := fails + 1
    IO.println
      s!"SPOT FAIL f80.pseudo-denormal bits: got=0x{toHex 20 pdr.bits.toNat} expected=0x00018000000000000000"
  unless !pdr.isNaN do
    fails := fails + 1
    IO.println "SPOT FAIL f80.pseudo-denormal: expected not NaN"
  pure (checked, fails)

/-- `0.1 + 0.2 ≠ 0.3` in `f64`: `Float.roundRat` on the exact rationals `1/10`/`2/10`, added,
must land on the same bits as Lean core's `Float.Model.add` on the same values built via
`ofScientific` — both derive the value independently, so agreement is real evidence, not a
tautology. The well-known literal (`0x3fd3333333333334`) is logged for a human to eyeball but
not asserted, so a slip in transcribing it can't fail the suite. -/
def checkPoint1Plus0Point2 : IO Bool := do
  let a := Zig.Float.roundRat .f64 false (1 / 10 : Rat)
  let b := Zig.Float.roundRat .f64 false (2 / 10 : Rat)
  let mine := (Zig.Float.add a b).bits.toNat
  let core :=
    (Float.Model.add (Float.Model.ofScientific 1 (-1)) (Float.Model.ofScientific 2 (-1))).toBits.toNat
  IO.println
    s!"f64 0.1+0.2: mine=0x{toHex 16 mine} core=0x{toHex 16 core} (well-known value: 0x3fd3333333333334)"
  let ok := mine == core
  unless ok do IO.println "SPOT FAIL f64 0.1+0.2: mine ≠ core"
  pure ok

/-! ## Main -/

def main : IO Unit := do
  let seed := mkStdGen 42
  let randCount := 100000
  let (diffGroups32, seed) ← runDiff32 seed randCount
  let (diffGroups64, _seed) ← runDiff64 seed randCount
  for g in diffGroups32 do g.report
  for g in diffGroups64 do g.report
  let mut totalChecked := diffGroups32.foldl (init := 0) (fun n g => n + g.checked)
  let mut totalDiffs := diffGroups32.foldl (init := 0) (fun n g => n + g.diffs)
  totalChecked := totalChecked + diffGroups64.foldl (init := 0) (fun n g => n + g.checked)
  totalDiffs := totalDiffs + diffGroups64.foldl (init := 0) (fun n g => n + g.diffs)

  let (c1, f1) ← runSpotChecks .f16 "f16" expF16
  let (c2, f2) ← runSpotChecks .f32 "f32" expF32
  let (c3, f3) ← runSpotChecks .f64 "f64" expF64
  let (c4, f4) ← runSpotChecks .f80 "f80" expF80
  let (c5, f5) ← runSpotChecks .f128 "f128" expF128
  let (c6, f6) ← runF80EncodingChecks
  IO.println s!"spot checks: {c1 + c2 + c3 + c4 + c5 + c6} checked, {f1 + f2 + f3 + f4 + f5 + f6} diffs"
  totalChecked := totalChecked + c1 + c2 + c3 + c4 + c5 + c6
  totalDiffs := totalDiffs + f1 + f2 + f3 + f4 + f5 + f6

  let point1ok ← checkPoint1Plus0Point2
  totalChecked := totalChecked + 1
  totalDiffs := totalDiffs + (if point1ok then 0 else 1)

  IO.println s!"TOTAL: {totalChecked} checked, {totalDiffs} diffs"
  if totalDiffs > 0 then
    IO.println "FAILED"
    IO.Process.exit 1
  else
    IO.println "All checks passed."
