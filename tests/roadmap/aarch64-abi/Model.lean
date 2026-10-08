import ZigLean.VecMem
import ZigLean.Float.Allowed

/-! T04: the model's side of the two aarch64 profiles' recorded probe results
(`tests/roadmap/aarch64-abi/expected/<zig>/<triple>-<mode>.txt`, `docs/aarch64-abi.md`).

* Kernel-checked: for each profile, the recorded sizes and alignments of the probed integers,
  floats (incl. that profile's `c_longdouble`), vectors and atomic cells, and its atomic width
  limit, are the model's (`Zig.Enc`, `Zig.intSize`/`intAlign`, `Zig.packedVecLayout`)
  — `linuxGnu_layouts`, `macosNone_layouts`.
* Run time, `lake env lean --run tests/roadmap/aarch64-abi/Model.lean TRIPLE FILE`: FILE's layout
  lines must be exactly that profile's kernel-checked table (so the theorem is about that file),
  and each float/atomic result line must be allowed by the model (`Zig.Float.Allowed`: bit for
  bit, or any NaN for a NaN), except the declared divergences of that profile, which must
  diverge. A divergence is printed and never counted as a match. The vector byte images are
  L09's (`tests/roadmap/vector-layouts/Model.lean`). -/

open Zig

namespace T04

/-- A profile's recorded layouts. Integers: name, bits, size, align. Floats: name, format,
size, align. Vectors: name, lanes, lane bits, `bool` lanes, size, align. Atomic cells: name,
bits, size, align. -/
structure Recorded where
  ints : List (String × Nat × Nat × Nat)
  floats : List (String × FloatFmt × Nat × Nat)
  vectors : List (String × Nat × Nat × Bool × Nat × Nat)
  atomics : List (String × Nat × Nat × Nat)
  /-- The widest integer `@atomicRmw` accepts (`atomic-limit.zig` must be rejected). -/
  atomicMaxBits : Nat
  cacheLine : Nat
  deriving BEq, Repr

/-- The model's layout of each recorded row. An atomic cell is a plain integer cell: the
model's atomics need it naturally aligned (size = alignment), the premise of single-copy
atomicity on aarch64 (LDXP/STXP, CASP need 16-byte alignment for 128 bits). -/
def Recorded.consistent (r : Recorded) : Bool :=
  r.ints.all (fun (_, bits, size, align) =>
      Enc.size (BitVec bits) == size && Enc.align (BitVec bits) == align) &&
    r.floats.all (fun (_, fmt, size, align) =>
      Enc.size (Float fmt) == size && Enc.align (Float fmt) == align) &&
    r.vectors.all (fun (_, n, w, isBool, size, align) =>
      let l := if isBool then boolVecLayout n else packedVecLayout n w
      l == size && l == align) &&
    r.atomics.all (fun (_, bits, size, align) =>
      Enc.size (BitVec bits) == size && Enc.align (BitVec bits) == align && size == align &&
        bits ≤ r.atomicMaxBits)

/-- The rows both profiles share; only `c_longdouble` differs. -/
def common (longDouble : FloatFmt) (size : Nat) : Recorded where
  ints := [("u7", 7, 1, 1), ("i7", 7, 1, 1), ("u24", 24, 4, 4), ("i24", 24, 4, 4),
    ("u40", 40, 8, 8), ("i40", 40, 8, 8), ("u65", 65, 16, 16), ("u96", 96, 16, 16),
    ("u128", 128, 16, 16), ("i128", 128, 16, 16)]
  floats := [("f16", .f16, 2, 2), ("f32", .f32, 4, 4), ("f64", .f64, 8, 8), ("f80", .f80, 16, 16),
    ("f128", .f128, 16, 16), ("c_longdouble", longDouble, size, size)]
  vectors := [("u9x4", 4, 9, false, 8, 8), ("i9x2", 2, 9, false, 4, 4),
    ("u12x3", 3, 12, false, 8, 8), ("u4x4", 4, 4, false, 2, 2), ("u1x8", 8, 1, false, 1, 1),
    ("u24x2", 2, 24, false, 8, 8), ("u24x3", 3, 24, false, 16, 16),
    ("u40x2", 2, 40, false, 16, 16), ("f80x2", 2, 80, false, 32, 32),
    ("bool5", 5, 1, true, 1, 1), ("bool16", 16, 1, true, 2, 2), ("u8x3", 3, 8, false, 4, 4),
    ("u16x3", 3, 16, false, 8, 8), ("u32x3", 3, 32, false, 16, 16)]
  atomics := [("u8", 8, 1, 1), ("u16", 16, 2, 2), ("u24", 24, 4, 4), ("u32", 32, 4, 4),
    ("u40", 40, 8, 8), ("u64", 64, 8, 8), ("u128", 128, 16, 16)]
  atomicMaxBits := 128
  cacheLine := 128

/-- aarch64-linux-gnu, Zig 0.16.0, ReleaseSafe: `long double` is IEEE binary128. -/
def linuxGnu : Recorded := common .f128 16
/-- aarch64-macos-none, Zig 0.16.0, ReleaseSafe: `long double` is `double`. -/
def macosNone : Recorded := common .f64 8

theorem linuxGnu_layouts : linuxGnu.consistent = true := by decide
theorem macosNone_layouts : macosNone.consistent = true := by decide

/-- The probed vectors resolve to the bit-packed instances that `packedVecLayout` describes. -/
example : Enc.size (Vec (BitVec 24) 3) = 16 := rfl
example : Enc.size (Vec (Float .f80) 2) = 32 := rfl
example : Enc.size (Vec Bool 16) = 2 := rfl
/-- The two profiles differ in `c_longdouble` only; f80 and f128 have one layout on both. -/
example : Enc.size (Float .f80) = 16 ∧ Enc.align (Float .f80) = 16 := ⟨rfl, rfl⟩
example : linuxGnu.floats ≠ macosNone.floats := by decide

/-! ## Float and atomic results (run time) -/

def hexNat? (s : String) : Option Nat :=
  if s.isEmpty then none else s.toList.foldlM (init := 0) fun acc c =>
    if '0' ≤ c && c ≤ '9' then some (16 * acc + (c.toNat - '0'.toNat))
    else if 'a' ≤ c && c ≤ 'f' then some (16 * acc + (c.toNat - 'a'.toNat + 10))
    else none

/-- The model's result of one probe case. -/
inductive Out where
  | float (fmt : FloatFmt) (x : Float fmt)
  | nat (v : Nat)
  | bool (b : Bool)
  | unspecified

/-- `Float.Allowed` for a float; exact equality otherwise. -/
def Out.allows : Out → String → Bool
  | .float fmt x, s => match hexNat? s with
    | some r =>
      let y : Float fmt := ⟨BitVec.ofNat fmt.width r⟩
      decide (r < 2 ^ fmt.width) && (if x.isNaN then y.isNaN else x == y)
    | none => false
  | .nat v, s => hexNat? s == some v
  | .bool b, s => s == toString b
  | .unspecified, _ => false

def bitsF (fmt : FloatFmt) (n : Nat) : Float fmt := ⟨BitVec.ofNat fmt.width n⟩
/-- The bits below the exponent of a normal number with fraction `frac`: f80 stores the integer
bit. -/
def rest (fmt : FloatFmt) (frac : Nat) : Nat :=
  if fmt = .f80 then 2 ^ fmt.fracBits + frac else frac

/-- `probe.zig`'s `floatCases` and `probeF80`, in the model's default (`ieee`) semantics. -/
def floatCase (fmt : FloatFmt) (name : String) : Option Out :=
  let n (k : Nat) : Float fmt := Zig.Float.ofInt fmt false (BitVec.ofNat 8 k)
  let one := n 1
  let three := n 3
  let half := Zig.Float.div one (n 2)
  let zero : Float fmt := Zig.Float.zero false
  let tiny := bitsF fmt 1
  let minNormal := Zig.Float.pack fmt false 1 (rest fmt 0)
  let max := Zig.Float.pack fmt false (2 ^ fmt.expBits - 2) (rest fmt (2 ^ fmt.fracBits - 1))
  let eps := Zig.Float.pack fmt false (fmt.bias - fmt.fracBits) (rest fmt 0)
  let f := Out.float fmt
  let invalid : List (String × Nat) := [("unnormal(e=1,i=0)", 0x0001_0000000000000001),
    ("pseudo-inf", 0x7fff_0000000000000000), ("pseudo-nan", 0x7fff_4000000000000000),
    ("pseudo-denormal", 0x0000_8000000000000000)]
  match name with
  | "1/3" => f (Zig.Float.div one three)
  | "sqrt(2)" => f (Zig.Float.sqrt (n 2))
  | "0/0" => f (Zig.Float.div zero zero)
  | "nan+1" => f (Zig.Float.add Zig.Float.nan one)
  | "-nan" => f (Zig.Float.neg Zig.Float.nan)
  | "tiny*0.5" => f (Zig.Float.mul tiny half)
  | "tiny*1.5" => f (Zig.Float.mul tiny (Zig.Float.div three (n 2)))
  | "min_normal*0.5" => f (Zig.Float.mul minNormal half)
  | "min_normal-tiny" => f (Zig.Float.sub minNormal tiny)
  | "max*2" => f (Zig.Float.mul max (n 2))
  | "mulAdd(1+e,1-e,-1)" => f (Zig.Float.fma (Zig.Float.add one eps) (Zig.Float.sub one eps) (Zig.Float.neg one))
  | "f64(1/3)" => Out.float .f64 (Zig.Float.conv .f64 (Zig.Float.div one three))
  | "f64(tiny)" => Out.float .f64 (Zig.Float.conv .f64 tiny)
  | "of(f64.tiny)" => f (Zig.Float.conv fmt (bitsF .f64 1))
  | "of(u128.max)" => f (Zig.Float.ofInt fmt false (BitVec.allOnes 128))
  | "u64(1e19)" =>
    match (Zig.Float.toInt false 64 true (Zig.Float.ofInt fmt false (BitVec.ofNat 64 (10 ^ 19)))).run with
    | some (.ok v) => Out.nat v.toNat
    | _ => Out.unspecified
  | "isnan(0/0)" => Out.bool (Zig.Float.div zero zero).isNaN
  | _ =>
    if fmt ≠ .f80 then none else
    invalid.findSome? fun (enc, b) =>
      let x := bitsF .f80 b
      if name == enc ++ "+0" then some (Out.float .f80 (Zig.Float.add x (Zig.Float.zero false)))
      else if name == s!"isnan({enc})" then some (Out.bool (Zig.Float.ne x x))
      else none

/-- The sequential reading of the model's atomics (`ZigLean/Mem/Thread.lean`: `cmpxchgAt`
compares the `bits`-bit value, `atomicRmwAt` wraps) for `probe.zig`'s `atomic` sequence from
`max - 1`: cmpxchg succeeds, the second fails with `max`, fetch-add returns `max`, xchg
returns `max + 2` (wrapped), the load gives `0x5a`. The padding bytes are undefined in the
model, so the raw cell images are not compared. -/
def atomicCase (bits : Nat) (won lost added swapped loaded : String) : Bool :=
  let max := 2 ^ bits - 1
  won == "true" && hexNat? lost == some max && hexNat? added == some max &&
    hexNat? swapped == some ((max + 2) % 2 ^ bits) && hexNat? loaded == some 0x5a

/-- Results that differ from the model on that profile, with the reason. Each must diverge:
a listed case that matches fails the check (the list is stale). -/
def divergences : List (String × String) := [
  -- `unnormal+0` itself is allowed: the model classifies the unnormal it returns as a NaN.
  ("fop f80 isnan(unnormal(e=1,i=0))", "soft-float f80 (compiler_rt) treats an unnormal as a number, not NaN (the model and x87: NaN)"),
  ("fop f80 pseudo-denormal+0", "soft-float f80 keeps the pseudo-denormal encoding; the model (x87) normalizes it"),
  ("atomic u24 padff", "cmpxchg compares the 4-byte cell, padding byte included: it fails although the u24 values are equal"),
  ("atomic u40 padff", "cmpxchg compares the 8-byte cell, padding bytes included: it fails although the u40 values are equal")]

def intBits? (name : String) : Option Nat :=
  if name.startsWith "u" || name.startsWith "i" then (name.drop 1).toString.toNat? else none

def fmtOf? : String → Option FloatFmt
  | "f16" => some .f16 | "f32" => some .f32 | "f64" => some .f64
  | "f80" => some .f80 | "f128" => some .f128 | _ => none

/-- The layout table that the file's lines record, in `Recorded`'s shape (the vector shapes and
the `c_longdouble` format, which the lines do not carry, are taken from `ref`). -/
def parseLayouts (ref : Recorded) (lines : List (List String)) : Except String Recorded := do
  let nat (s : String) : Except String Nat := s.toNat?.elim (throw s!"not a number: {s}") pure
  let mut r : Recorded := ⟨[], [], [], [], 0, 0⟩
  for l in lines do
    match l with
    | "int" :: name :: size :: align :: bits :: _ =>
      unless intBits? name == bits.toNat? do throw s!"int {name}: {bits} bits"
      r := { r with ints := r.ints ++ [(name, ← nat bits, ← nat size, ← nat align)] }
    | "float" :: name :: size :: align :: _ =>
      let fmt ← match fmtOf? name, ref.floats.find? (·.1 == name) with
        | some fmt, _ => pure fmt
        | none, some (_, fmt, _) => pure fmt
        | none, none => throw s!"float {name}: unknown"
      r := { r with floats := r.floats ++ [(name, fmt, ← nat size, ← nat align)] }
    | "vector" :: name :: size :: align :: _ =>
      let some (_, n, w, b, _) := ref.vectors.find? (·.1 == name) | throw s!"vector {name}: unknown"
      r := { r with vectors := r.vectors ++ [(name, n, w, b, ← nat size, ← nat align)] }
    | "atomic" :: name :: size :: align :: "pad00" :: _ =>
      let some bits := intBits? name | throw s!"atomic {name}: not an integer"
      r := { r with atomics := r.atomics ++ [(name, bits, ← nat size, ← nat align)] }
    | ["limit", "atomic_u256", msg] =>
      match msg.splitOn "-bit" with
      | pre :: _ => r := { r with atomicMaxBits := ← nat ((pre.splitOn "expected_").getLast!) }
      | _ => throw "limit: unparsable"
    | ["sync", "cache_line", v] => r := { r with cacheLine := ← nat v }
    | _ => pure ()
  return r

def main (args : List String) : IO UInt32 := do
  let [triple, path] := args
    | IO.eprintln "usage: Model.lean aarch64-linux-gnu|aarch64-macos-none FILE"; return 2
  let some ref := (match triple with
      | "aarch64-linux-gnu" => some linuxGnu | "aarch64-macos-none" => some macosNone | _ => none)
    | IO.eprintln s!"aarch64-abi: no kernel-checked table for {triple}"; return 2
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (!·.isEmpty) |>.map
    (·.splitOn " " |>.filter (!·.isEmpty))
  let r ← match parseLayouts ref lines with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"aarch64-abi: {path}: {e}")
  unless r == ref do
    IO.eprintln s!"aarch64-abi: {path}: layout lines differ from the kernel-checked {triple} table:\n{repr r}"
    return 1
  let mut matched := 0
  let mut diverged : List String := []
  let mut bad : List String := []
  for l in lines do
    let (key, ok) ← match l with
      | ["fop", ty, name, obs] =>
        let some fmt := fmtOf? ty | pure (s!"fop {ty} {name}", false)
        let some out := floatCase fmt name | pure (s!"fop {ty} {name}", false)
        pure (s!"fop {ty} {name}", out.allows obs)
      | ["atomic", name, _, _, pad, _, won, lost, added, swapped, loaded, _] =>
        let some bits := intBits? name | pure (s!"atomic {name} {pad}", false)
        pure (s!"atomic {name} {pad}", atomicCase bits won lost added swapped loaded)
      -- A malformed result line is a failure, not a skipped case.
      | "fop" :: rest | "atomic" :: rest => pure (s!"malformed {" ".intercalate rest}", false)
      | _ => pure ("", true)
    if key.isEmpty then continue
    match divergences.lookup key, ok with
    | none, true => matched := matched + 1
    | some why, false => diverged := diverged ++ [s!"{key}: {why}"]
    | none, false => bad := bad ++ [s!"{key}: the recorded result is not allowed by the model"]
    | some _, true => bad := bad ++ [s!"{key}: declared divergence now matches (stale)"]
  let keys := lines.filterMap fun l => match l with
    | ["fop", ty, name, _] => some s!"fop {ty} {name}"
    | "atomic" :: name :: _ :: _ :: pad :: _ => some s!"atomic {name} {pad}"
    | _ => none
  for (key, _) in divergences do
    unless keys.contains key do bad := bad ++ [s!"{key}: declared divergence is not in the file"]
  for d in diverged do IO.println s!"divergence (not a match) {d}"
  for b in bad do IO.eprintln s!"aarch64-abi: {b}"
  unless bad.isEmpty do return 1
  IO.println s!"aarch64-abi: {triple}: {r.ints.length + r.floats.length + r.vectors.length + r.atomics.length} \
    layout rows equal the kernel-checked table; {matched} float/atomic results allowed by the model; \
    {diverged.length} declared divergences (not counted as matches)"
  return 0

end T04

def main (args : List String) : IO UInt32 := T04.main args
