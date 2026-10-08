import Air2Lean
import Air2Lean.Check
open Air2Lean

/-! L07 checker controls for `@bitCast` (`Air2Lean/Check.lean`): the representation cast and
the optional-pointer rules hold for Zig 0.14.1, 0.15.2 and 0.16.0 only (`memoryBitCastVersion`);
any other version (0.17.0 redefined `@bitCast`; `docs/bitcast-semantics.md` on its branch) or a
context without a version rejects them. Types without a guaranteed in-memory layout and
`@bitSizeOf` mismatches are rejected. The emitted text is pinned by `AggregateCasts/Gen.lean`.

    lake env lean --run tests/roadmap/aggregate-casts/Checker.lean -/

private def require (test : Bool) (why : String) : IO Unit :=
  unless test do throw (IO.userError why)

private def ptrLayout : Layout := {size := some 8, align := some 8, ptrAlign := some 4}

private def types : Array Ty := #[
  .int false 32, .int false 8, .array 4 1 false,                       -- 0..2: u32, u8, [4]u8
  .struct "S" "extern" #[("a", 1), ("b", 0)],                          -- 3: extern {u8, u32}
  .array 8 1 false, .int false 64,                                     -- 4..5: [8]u8, u64
  .tuple #[1, 0], .struct "A" "auto" #[("a", 1), ("b", 0)],            -- 6..7: tuple, auto
  .array 1 7 false,                                                    -- 8: [1]A
  .int false 24, .array 2 9 false, .int false 56,                      -- 9..11: u24, [2]u24, u56
  .ptr "one" false 0, .optional 12,                                    -- 12..13: *u32, ?*u32
  .ptr "c" false 0,                                                    -- 14: [*c]u32
  .union "U" "extern" none #[("a", 1), ("b", 0)],                      -- 15: extern union
  .array 4 1 true]                                                     -- 16: [4:0]u8

private def layouts : Array Layout := #[
  {size := some 4, align := some 4}, {size := some 1, align := some 1},
  {size := some 4, align := some 1},
  {size := some 8, align := some 4, offsets := #[0, 4]},
  {size := some 8, align := some 1}, {size := some 8, align := some 8},
  {size := some 8, align := some 4, offsets := #[0, 4]},
  {size := some 8, align := some 4, offsets := #[0, 4]},
  {size := some 8, align := some 4},
  {size := some 4, align := some 4}, {size := some 8, align := some 4},
  {size := some 8, align := some 8},
  ptrLayout, {size := some 8, align := some 8}, ptrLayout,
  {size := some 4, align := some 4}, {size := some 5, align := some 1, sentinel := true}]

private def cx (version : String) (src : TyId) : CheckCtx :=
  { fnName := "probe.f", types, layouts, instTys := #[(0, src)], places := #[],
    zigVersion := version }

private def result (version : String) (src dst : TyId) : Except String Nat :=
  checkOp (cx version src) 0 dst (.bitcast (.inst 0))

private def accepts (version : String) (src dst : TyId) : Bool := (result version src dst).isOk

private def rejects (version : String) (src dst : TyId) (marker : String) : Bool :=
  match result version src dst with
  | .error e => (e.splitOn marker).length > 1
  | .ok _ => false

def main : IO Unit := do
  let casts : List (TyId × TyId) :=
    [(2, 0), (0, 2), (4, 3), (3, 4), (3, 5), (10, 11), (11, 10), (15, 0), (0, 15),
     (13, 12), (13, 5), (5, 13)]
  for v in ["0.14.1", "0.15.2", "0.16.0"] do
    for (s, d) in casts do
      require (accepts v s d) s!"{v}: cast {s} → {d} is rejected: {result v s d}"
  -- Only ≤0.16 has these rules: 0.17.0 and a context without a version reject them.
  for v in ["0.17.0", ""] do
    for (s, d) in casts do
      require (!accepts v s d) s!"{repr v}: cast {s} → {d} is accepted"
  -- The pointer wrap (`*T → ?*T`) is the existing coercion, for every version.
  require (accepts "0.17.0" 12 13) "the optional wrap is rejected"
  let layoutMsg := "without a guaranteed in-memory layout"
  require (rejects "0.16.0" 4 6 "a type other than an integer") "[8]u8 → tuple is accepted"
  require (rejects "0.16.0" 7 4 "a type other than an integer") "auto struct → [8]u8 is accepted"
  require (rejects "0.16.0" 8 5 layoutMsg) "[1]auto → u64 is accepted"
  require (rejects "0.16.0" 10 5 "between types of 56 and 64 bits") "[2]u24 → u64 is accepted"
  require (rejects "0.16.0" 16 0 "an aggregate other than a packed") "[4:0]u8 → u32 is accepted"
  require (rejects "0.16.0" 13 0 "optional pointer") "?*u32 → u32 is accepted"
  require (rejects "0.16.0" 13 14 "optional pointer") "?*u32 → [*c]u32 is accepted"
  require (rejects "0.16.0" 14 13 "C/allowzero pointer") "[*c]u32 → ?*u32 is accepted"
  IO.println "aggregate-casts checker controls: ok"
