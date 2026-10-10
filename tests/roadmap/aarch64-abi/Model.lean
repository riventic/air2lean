import ZigLean.VecMem
import ZigLean.Float.Allowed
import ZigLean.Mem.Thread

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
  L09's (`tests/roadmap/vector-layouts/Model.lean`).
* Synchronization rows: each `rmw` row is the model's `RmwOp.apply`; the `order` rows are the
  same for every ordering the compiler accepts; the `litmus` rows are the sequentially forced
  counts and zero forbidden outcomes; the `limit` rows are the rejected-program messages. The
  `atomic_ext` rows (bool, enum, pointer and float cells) are native observations only: the
  model has no such atomics. -/

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

/-! ### Zig 0.17.0 layouts

Zig 0.17.0 (LLVM 22) aligns `f80` to 8 bytes on both profiles, and `f128` on aarch64-macos (where
it is not `c_longdouble`); the bit-packed `f80x2` vector is 8-aligned, and its second lane is not
where `Vec.packedEnc` puts it. The model keeps 16 and the packed image. These rows are declared
divergences of the 0.17.0 files: the translator compares the layout of every type in memory with
the exporter's (`checkMemTy`), so it rejects these types in memory on 0.17.0 aarch64. -/

/-- The rows of a 0.17.0 file whose alignment is 8, not the model's 16. -/
def layoutDivergences017 (triple : String) : List String :=
  ["float f80", "vector f80x2"] ++ (if triple == "aarch64-macos-none" then ["float f128"] else [])

/-- The table that a file of `version` must record: the kernel-checked one, with the 0.17.0
divergent rows at alignment 8. -/
def Recorded.forVersion (r : Recorded) (version triple : String) : Recorded :=
  if version != "0.17.0" then r else
  let ds := layoutDivergences017 triple
  { r with
    floats := r.floats.map fun (n, f, s, a) => (n, f, s, if ds.contains s!"float {n}" then 8 else a)
    vectors := r.vectors.map fun (n, k, w, b, s, a) =>
      (n, k, w, b, s, if ds.contains s!"vector {n}" then 8 else a) }

/-- The model's `f80` and `f128` are 16-aligned, so each 0.17.0 row is a divergence. -/
example : Enc.align (Float .f80) = 16 ∧ Enc.align (Float .f128) = 16 := ⟨rfl, rfl⟩

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
def softF80Divergences : List (String × String) := [
  -- `unnormal+0` itself is allowed: the model classifies the unnormal it returns as a NaN.
  ("fop f80 isnan(unnormal(e=1,i=0))", "soft-float f80 (compiler_rt) treats an unnormal as a number, not NaN (the model and x87: NaN)"),
  ("fop f80 pseudo-denormal+0", "soft-float f80 keeps the pseudo-denormal encoding; the model (x87) normalizes it")]

/-- The padded-width atomics of Zig before 0.17.0 (0.17.0 agrees with the model on them). -/
def paddedDivergences : List (String × String) := [
  ("atomic u24 padff", "cmpxchg compares the 4-byte cell, padding byte included: it fails although the u24 values are equal"),
  ("atomic u40 padff", "cmpxchg compares the 8-byte cell, padding bytes included: it fails although the u40 values are equal"),
  ("rmw i24 Max e54321 2bcdef", "signed Max of a negative i24 cell and a positive operand keeps the negative cell: the native i24 Max is not the signed maximum (padded width)"),
  ("rmw i40 Max 8987654321 7890abcdef", "signed Max of a negative i40 cell and a positive operand keeps the negative cell: the native i40 Max is not the signed maximum (padded width)")]

/-- Zig before 0.16.0: the soft-float `@sqrt` of f80 and f128 on aarch64 is computed at f64
precision (`sqrt(2)` has 53 correct bits, the rest zero). 0.16.0 rounds correctly. -/
def divergences : List (String × String) := softF80Divergences ++ paddedDivergences

/-- Zig 0.17.0 compares only the value bits of a padded `cmpxchg` and computes the signed `Max`
of a padded width, as the model does, so only the soft-float `f80` rows diverge. -/
def divergencesIn (version : String) : List (String × String) :=
  if version == "0.17.0" then softF80Divergences
  else if version == "0.14.1" || version == "0.15.2" then divergences ++ [
    ("fop f80 sqrt(2)", "@sqrt of f80 is correct to f64 precision only (compiler_rt before 0.16.0)"),
    ("fop f128 sqrt(2)", "@sqrt of f128 is correct to f64 precision only (compiler_rt before 0.16.0)")]
  else divergences

/-! ## Synchronization rows (run time) -/

def rmwOp? : String → Option RmwOp
  | "Xchg" => some .xchg | "Add" => some .add | "Sub" => some .sub | "And" => some .and
  | "Nand" => some .nand | "Or" => some .or | "Xor" => some .xor | "Max" => some .max
  | "Min" => some .min | _ => none

/-- `rmw <type> <op> <cell> <operand> <returned> <final>`: the call returns the old cell and
leaves the model's `RmwOp.apply` of it (signed `Max`/`Min` for `iN`). -/
def rmwCase (bits : Nat) (signed : Bool) (op : RmwOp) (cell operand returned final : String) : Bool :=
  match hexNat? cell, hexNat? operand, hexNat? returned, hexNat? final with
  | some c, some v, some r, some f =>
    c < 2 ^ bits && v < 2 ^ bits && r == c &&
      f == (op.apply signed (BitVec.ofNat bits c) (BitVec.ofNat bits v)).toNat
  | _, _, _, _ => false

def splitOnce (c : Char) (s : String) : Option (String × String) :=
  match s.splitOn c.toString with
  | [a, b] => some (a, b)
  | _ => none

/-- `order <op> <ordering>:<result> ...`: the orderings that the compiler accepts, in order, and
a result independent of them (a store or load of 9, 7; adds from 9; cmpxchg from 14, each
consecutive and successful). -/
def orderCase (kind : String) (cells : List String) : Bool :=
  let pairs := cells.filterMap (splitOnce ':')
  pairs.length == cells.length &&
  match kind with
  | "load" => pairs == [("monotonic", "7"), ("acquire", "7"), ("seq_cst", "7")]
  | "store" => pairs == [("monotonic", "9"), ("release", "9"), ("seq_cst", "9")]
  | "rmw" => pairs == [("monotonic", "9"), ("acquire", "a"), ("release", "b"), ("acq_rel", "c"),
      ("seq_cst", "d")]
  | "cmpxchg" =>
    let names := ["monotonic/monotonic", "acquire/monotonic", "acquire/acquire",
      "release/monotonic", "release/acquire", "acq_rel/monotonic", "acq_rel/acquire",
      "seq_cst/monotonic", "seq_cst/acquire", "seq_cst/seq_cst"]
    pairs.map (·.1) == names &&
      (pairs.zipIdx.all fun ((_, v), i) => v == s!"{String.ofList (Nat.toDigits 16 (14 + i))},true")
  | _ => false

/-- Native observations of cell types the model's integer atomics do not cover. -/
def atomicExtRows : List (List String) := [
  ["bool", "1", "1", "false", "true", "true"], ["enum_u8", "1", "1", "red", "true", "green"],
  ["pointer", "8", "8", "true", "true", "5"],
  ["f32", "4", "4", "3fc00000", "40700000", "bf800000", "bfc00000"],
  ["f64", "8", "8", "3ff8000000000000", "400e000000000000", "bff0000000000000", "bff8000000000000"]]

/-- `litmus`: no forbidden outcome, and the counters the sequential model forces (four threads
adding `per_thread` each, wrapping at the cell width). -/
def litmusCase : List String → Bool
  | ["mp_release_acquire", "violations", "0", "rounds", _] => true
  | ["sb_seq_cst", "both_zero", "0", "unset", "0", "rounds", _] => true
  | ["counters", "u8", a, "u24", b, "u128", c, "cas_u64", d, "per_thread", n] =>
    match n.toNat? with
    | some n => a.toNat? == some (4 * n % 2 ^ 8) && b.toNat? == some (4 * n % 2 ^ 24) &&
        c.toNat? == some (4 * n) && d.toNat? == some (4 * n)
    | none => false
  | _ => false

/-- The program that the compiler must reject, and its first error (spaces as `_`). -/
def limitMessages : List (String × String) := [
  ("atomic_array", "expected_bool,_integer,_float,_enum,_packed_struct,_or_pointer_type;_found_'[2]u8'"),
  ("atomic_vector", "expected_bool,_integer,_float,_enum,_packed_struct,_or_pointer_type;_found_'@Vector(2,_u32)'"),
  ("bool_add", "@atomicRmw_with_bool_only_allowed_with_.Xchg"),
  ("cmpxchg_failure_release", "failure_atomic_ordering_must_not_be_release_or_acq_rel"),
  ("cmpxchg_failure_stronger", "failure_atomic_ordering_must_be_no_stricter_than_success"),
  ("float_and", "@atomicRmw_with_float_only_allowed_with_.Xchg,_.Add,_.Sub,_.Max,_and_.Min"),
  ("load_acq_rel", "@atomicLoad_atomic_ordering_must_not_be_release_or_acq_rel"),
  ("load_release", "@atomicLoad_atomic_ordering_must_not_be_release_or_acq_rel"),
  ("rmw_unordered", "@atomicRmw_atomic_ordering_must_not_be_unordered"),
  ("store_acq_rel", "@atomicStore_atomic_ordering_must_not_be_acquire_or_acq_rel"),
  ("store_acquire", "@atomicStore_atomic_ordering_must_not_be_acquire_or_acq_rel")]

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
  let version := lines.findSome? fun l => match l with | ["meta", "zig", v] => some v | _ => none
  let some version := version | IO.eprintln s!"aarch64-abi: {path}: no `meta zig` line"; return 1
  -- Every synchronization row the probe prints must be present (a missing row is not a pass).
  let required : List (String × Nat) := [("rmw", 110), ("order", 4), ("atomic_ext", 5),
    ("litmus", 3), ("limit", 1 + limitMessages.length)]
  for (kind, n) in required do
    let count := (lines.filter (·.headD "" == kind)).length
    unless count == n do
      IO.eprintln s!"aarch64-abi: {path}: {count} `{kind}` rows, expected {n}"
      return 1
  let r ← match parseLayouts ref lines with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"aarch64-abi: {path}: {e}")
  unless r == ref.forVersion version triple do
    IO.eprintln s!"aarch64-abi: {path}: layout lines differ from the kernel-checked {triple} table:\n{repr r}"
    return 1
  if version == "0.17.0" then
    for row in layoutDivergences017 triple do
      IO.println s!"divergence (not a match) {row}: 8-aligned in Zig 0.17.0, 16 in the model"
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
      | ["rmw", ty, opName, cell, operand, returned, final] =>
        let key := s!"rmw {ty} {opName} {cell} {operand}"
        match intBits? ty, rmwOp? opName with
        | some bits, some op => pure (key, rmwCase bits (ty.startsWith "i") op cell operand returned final)
        | _, _ => pure (key, false)
      | "order" :: kind :: cells => pure (s!"order {kind}", orderCase kind cells)
      | "atomic_ext" :: rest => pure (s!"atomic_ext {rest.headD ""}", atomicExtRows.contains rest)
      | "litmus" :: rest => pure (s!"litmus {rest.headD ""}", litmusCase rest)
      | ["limit", "atomic_u256", _] => pure ("", true)
      | ["limit", name, msg] => pure (s!"limit {name}", limitMessages.lookup name == some msg)
      | "fop" :: rest | "atomic" :: rest | "rmw" :: rest | "limit" :: rest => pure (s!"malformed {" ".intercalate rest}", false)
      | _ => pure ("", true)
    if key.isEmpty then continue
    match (divergencesIn version).lookup key, ok with
    | none, true => matched := matched + 1
    | some why, false => diverged := diverged ++ [s!"{key}: {why}"]
    | none, false => bad := bad ++ [s!"{key}: the recorded result is not allowed by the model"]
    | some _, true => bad := bad ++ [s!"{key}: declared divergence now matches (stale)"]
  let keys := lines.filterMap fun l => match l with
    | ["fop", ty, name, _] => some s!"fop {ty} {name}"
    | ["rmw", ty, op, cell, operand, _, _] => some s!"rmw {ty} {op} {cell} {operand}"
    | "atomic" :: name :: _ :: _ :: pad :: _ => some s!"atomic {name} {pad}"
    | _ => none
  for (key, _) in divergencesIn version do
    unless keys.contains key do bad := bad ++ [s!"{key}: declared divergence is not in the file"]
  for d in diverged do IO.println s!"divergence (not a match) {d}"
  for b in bad do IO.eprintln s!"aarch64-abi: {b}"
  unless bad.isEmpty do return 1
  IO.println s!"aarch64-abi: {triple} (Zig {version}): {r.ints.length + r.floats.length + r.vectors.length + r.atomics.length} \
    layout rows equal the kernel-checked table; {matched} float, atomic and synchronization results allowed by the model; \
    {diverged.length} declared divergences (not counted as matches)"
  return 0

end T04

def main (args : List String) : IO UInt32 := T04.main args
