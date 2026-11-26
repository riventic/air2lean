import Air2Lean
import Air2Lean.Check
open Air2Lean

/-! L07 checker controls for `@bitCast` (`Air2Lean/Check.lean`): the representation cast
holds for Zig 0.14.1, 0.15.2 and 0.16.0 only (`ZigVersion.BitCast.memory`); 0.17.1 redefined
`@bitCast` (logical bit order, `docs/bitcast-semantics.md`), which admits only the equal-width
integer-array casts here. The optional-pointer rules (`@ptrCast`, `@intFromPtr`, `@ptrFromInt`: no
`@bitCast`s) hold for every version; a context without a version rejects all of them. Types without a guaranteed
in-memory layout, pointers
and optional pointers at any depth, and `@bitSizeOf` mismatches are rejected. The emitted text is pinned by `AggregateCasts/Gen.lean`.

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
  .array 4 1 true,                                                     -- 16: [4:0]u8
  .array 1 12 false, .struct "P" "extern" #[("p", 13)],                -- 17..18: [1]*u32, extern {?*u32}
  .int false 40, .array 1 6 false,                                     -- 19..20: u40, [1]tuple
  .void, .array 4 21 false, .int false 0,                              -- 21..23: void, [4]void, u0
  .vector 5 1,                                                         -- 24: @Vector(5, u8)
  .optional 1, .array 1 25 false,                                      -- 25..26: ?u8, [1]?u8
  .struct "AO" "auto" #[("o", 25)], .array 1 27 false,                 -- 27..28: auto {?u8}, [1]AO
  .int false 16,                                                       -- 29: u16
  .struct "AA" "auto" #[("a", 26)], .array 1 30 false]                 -- 30..31: auto {[1]?u8}, [1]AA

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
  {size := some 4, align := some 4}, {size := some 5, align := some 1, sentinel := true},
  {size := some 8, align := some 8}, {size := some 8, align := some 8, offsets := #[0]},
  {size := some 8, align := some 8}, {size := some 8, align := some 4},
  {size := some 0, align := some 1}, {size := some 0, align := some 1},
  {size := some 0, align := some 1},
  {size := some 8, align := some 8},
  {size := some 2, align := some 1}, {size := some 2, align := some 1},
  {size := some 2, align := some 1, offsets := #[0]}, {size := some 2, align := some 1},
  {size := some 2, align := some 2},
  {size := some 2, align := some 1, offsets := #[0]}, {size := some 2, align := some 1}]

/-- `backend`: the profile's code generator; the default is the legacy profile's (`unverified`). -/
private def cx (version : String) (src : TyId) (backend : String := "unverified") : CheckCtx :=
  { fnName := "probe.f", types, layouts, instTys := #[(0, src)], places := #[],
    dialect := (ZigVersion.ofString? version).map ({ version := ·, backend }) }

private def result (version : String) (src dst : TyId) (backend : String := "unverified") :
    Except String Nat :=
  checkOp (cx version src backend) 0 dst (.bitcast false (.inst 0))

private def accepts (version : String) (src dst : TyId) : Bool := (result version src dst).isOk

private def rejects (version : String) (src dst : TyId) (marker : String) : Bool :=
  match result version src dst with
  | .error e => (e.splitOn marker).length > 1
  | .ok _ => false

def main : IO Unit := do
  let casts : List (TyId × TyId) :=
    [(2, 0), (0, 2), (4, 3), (3, 4), (3, 5), (15, 0), (0, 15),
     (13, 12), (13, 5), (5, 13)]
  for v in ["0.14.1", "0.15.2", "0.16.0"] do
    for (s, d) in casts do
      require (accepts v s d) s!"{v}: cast {s} → {d} is rejected: {result v s d}"
    -- `[2]u24` ↔ `u56`: a padded integer is decoded with the backend's storage encoding, so the
    -- cast holds on a profile of the LLVM or the self-hosted x86_64 backend and is rejected on
    -- one that names no backend (the legacy profile; fail closed).
    for (s, d) in [(10, 11), (11, 10)] do
      for backend in [Target.llvmBackend, "stage2_x86_64"] do
        require (result v s d backend).isOk
          s!"{v} {backend}: cast {s} → {d} is rejected: {result v s d backend}"
      require (rejects v s d "of an integer with padding bits")
        s!"{v}: the padded cast {s} → {d} on a legacy profile: {result v s d}"
  -- A context without a version rejects them all. Only ≤0.16 has the representation casts:
  -- 0.17.1 takes the logical-bit-order path (`Air2Lean/BitCast.lean`, docs/bitcast-semantics.md),
  -- which admits `[4]u8` ↔ `u32` (equal logical bits) and rejects the rest (extern aggregates,
  -- `[2]u24` ↔ `u56` at 48 vs 56 logical bits). The three optional-pointer casts (`@ptrCast`,
  -- `@intFromPtr`, `@ptrFromInt`) are no `@bitCast`s and hold for every version.
  for (s, d) in casts ++ [(10, 11), (11, 10)] do
    require (!accepts "" s d) s!"\"\": cast {s} → {d} is accepted"
    let admitted := [(2, 0), (0, 2), (13, 12), (13, 5), (5, 13)].contains (s, d)
    require (accepts "0.17.1" s d == admitted)
      s!"\"0.17.1\": cast {s} → {d} is {if admitted then "rejected" else "accepted"}: {result "0.17.1" s d}"
  -- The pointer wrap (`*T → ?*T`) is the existing coercion, for every version.
  require (accepts "0.17.1" 12 13) "the optional wrap is rejected"
  let layoutMsg := "without a guaranteed in-memory layout"
  require (rejects "0.16.0" 4 6 "a type other than an integer") "[8]u8 → tuple is accepted"
  require (rejects "0.16.0" 7 4 "a type other than an integer") "auto struct → [8]u8 is accepted"
  require (rejects "0.16.0" 8 5 layoutMsg) "[1]auto → u64 is accepted"
  -- Pointer-bearing repr casts fail closed: pointer bytes are not integer bits in the model.
  for v in ["0.14.1", "0.15.2", "0.16.0"] do
    for (s, d) in [(17, 5), (5, 17), (18, 5), (5, 18), (17, 18)] do
      require (rejects v s d "involving a pointer") s!"{v}: pointer-bearing cast {s} → {d} is accepted"
  require (match result "0.16.0" 10 5 Target.llvmBackend with
      | .error e => (e.splitOn "between types of 56 and 64 bits").length > 1
      | .ok _ => false) "[2]u24 → u64 is accepted"
  -- Zig 0.14.1 and 0.15.2: an optional array item is decoded with the cast's flag rule
  -- (`Zig.Enc.optionRepr`); an optional in a field of an `auto` struct item (also as an item of
  -- an array field) is decoded by the struct's own encoding, and is rejected.
  for v in ["0.14.1", "0.15.2"] do
    require (accepts v 26 29 && accepts v 29 26) s!"{v}: [1]?u8 ↔ u16: {result v 26 29}"
    for a in [28, 31] do
      for (s, d) in [(a, 29), (29, a)] do
        require (rejects v s d "an optional in a field of a struct or union")
          s!"{v}: an optional in a field of an auto struct item, cast {s} → {d}: {result v s d}"
  require (rejects "0.16.0" 26 29 "involving an optional") "0.16.0: [1]?u8 → u16 is accepted"
  -- A sentinel-terminated array is one more item (`lenIncludingSentinel`): `[4:0]u8` has 40 bits
  -- up to 0.16. Zig 0.17 is rejected by name (docs/upstream/bitcast-sentinel-array.md), and so
  -- is a vector on the other side (up to 0.15.2 the LLVM lowering copies the items only).
  require (rejects "0.16.0" 16 0 "between types of 40 and 32 bits") "[4:0]u8 → u32 is accepted"
  for v in ["0.14.1", "0.15.2", "0.16.0"] do
    -- (`u40` has padding bits: on a profile that names its backend.)
    for (s, d) in [(16, 19), (19, 16)] do
      require (result v s d Target.llvmBackend).isOk
        s!"{v}: sentinel cast {s} → {d} is rejected: {result v s d Target.llvmBackend}"
      require (rejects v s d "of an integer with padding bits")
        s!"{v}: the padded sentinel cast {s} → {d} on a legacy profile: {result v s d}"
    require (rejects v 16 24 "a sentinel-terminated array and a vector")
      s!"{v}: [4:0]u8 → @Vector(5, u8) is accepted"
  for (s, d) in [(16, 19), (19, 16)] do
    require (rejects "0.17.1" s d "of a sentinel-terminated array (type 16)")
      s!"0.17.1: sentinel cast {s} → {d}: {result "0.17.1" s d}"
    require (!accepts "" s d) s!"\"\": sentinel cast {s} → {d} is accepted"
  -- An array of tuples compiles on 0.14.1 and 0.15.2 only; the memory model has no tuple layout.
  for v in ["0.14.1", "0.15.2", "0.16.0"] do
    require (rejects v 20 5 "involving a tuple (type 6") s!"{v}: [1]tuple → u64: {result v 20 5}"
    require (rejects v 5 20 "involving a tuple (type 6") s!"{v}: u64 → [1]tuple: {result v 5 20}"
  -- Zero-bit types: `[4]void` ↔ `u0` in every version, `void` itself from 0.17.
  for v in ["0.14.1", "0.15.2", "0.16.0", "0.17.1"] do
    require (accepts v 22 23) s!"{v}: [4]void → u0 is rejected: {result v 22 23}"
    require (accepts v 23 22) s!"{v}: u0 → [4]void is rejected: {result v 23 22}"
  require (accepts "0.17.1" 21 23 && accepts "0.17.1" 23 21 && accepts "0.17.1" 21 22)
    "0.17.1: a `void` cast is rejected"
  for v in ["0.14.1", "0.15.2", "0.16.0"] do
    require (rejects v 21 23 "to or from `void`") s!"{v}: void → u0: {result v 21 23}"
    require (rejects v 23 21 "to or from `void`") s!"{v}: u0 → void: {result v 23 21}"
  require (rejects "0.17.1" 22 0 "between types of 0 and 32 logical bits") "0.17.1: [4]void → u32 is accepted"
  require (rejects "0.16.0" 13 0 "optional pointer") "?*u32 → u32 is accepted"
  -- `?*T` ↔ `[*c]T` is L05's explicit null mapping (`docs/null-pointers.md`), for every version.
  for v in ["0.16.0", "0.17.1"] do
    require (accepts v 13 14) s!"{v}: ?*u32 → [*c]u32 is rejected: {result v 13 14}"
    require (accepts v 14 13) s!"{v}: [*c]u32 → ?*u32 is rejected: {result v 14 13}"
  IO.println "aggregate-casts checker controls: ok"
