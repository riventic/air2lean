import Air2Lean
import Air2Lean.Check
open Air2Lean

/-! Checker controls for pointers to opaque types (`Air2Lean/Check.lean`): `anyopaque` and a
declared `opaque {}` are one type kind (`Ty.opaque`). A single-item pointer to one is a value;
the type itself has no size, alignment or values, so every by-value use, every access through
the pointer and every pointer kind that needs the item size is rejected. Casts follow the
provenance rules of `*anyopaque`.

    lake env lean --run tests/roadmap/opaque-pointers/Checker.lean -/

private def require (test : Bool) (why : String) : IO Unit :=
  unless test do throw (IO.userError why)

private def ptrLayout (align : Nat) : Layout := {size := some 8, align := some 8, ptrAlign := some align}
private def optLayout : Layout := {size := some 8, align := some 8}

private def types : Array Ty := #[
  .int false 32, .opaque "m.Handle", .ptr "one" false 1, .optional 2,        -- 0..3: u32, Handle, *Handle, ?*Handle
  Ty.anyopaque, .ptr "one" false 4, .ptr "one" false 0,                      -- 4..6: anyopaque, *anyopaque, *u32
  .opaque "m.Other", .ptr "one" false 7, .ptr "one" true 1,                  -- 7..9: Other, *Other, *const Handle
  .ptr "many" false 1, .ptr "slice" false 1, .ptr "c" false 1,               -- 10..12: [*]Handle, []Handle, [*c]Handle
  .struct "m.Cell" "auto" #[("h", 2), ("o", 3)], .array 2 2 false,           -- 13..14: Cell, [2]*Handle
  .optional 1, .struct "m.Bad" "auto" #[("h", 1)], .array 2 1 false,         -- 15..17: ?Handle, Bad, [2]Handle
  .errorSet (some #["Bad"]), .errorUnion 18 0, .ptr "one" false 19,          -- 18..20: E, E!u32, *E!u32
  .void, .noreturn, .bool,                                                   -- 21..23
  .other "m.Handle", .ptr "one" false 24,                                    -- 24..25: an unmarked export's entry
  .optional 6, .optional 5, .int false 64]                                   -- 26..28: ?*u32, ?*anyopaque, usize

private def layouts : Array Layout := #[
  {size := some 4, align := some 4}, {}, ptrLayout 1, optLayout,
  {}, ptrLayout 1, ptrLayout 4,
  {}, ptrLayout 1, ptrLayout 1,
  ptrLayout 1, {size := some 16, align := some 8, ptrAlign := some 1}, ptrLayout 1,
  {size := some 16, align := some 8, offsets := #[0, 8]}, {size := some 16, align := some 8},
  {}, {}, {},
  {size := some 2, align := some 2}, {size := some 8, align := some 4}, ptrLayout 4,
  {size := some 0, align := some 1}, {}, {size := some 1, align := some 1},
  {}, ptrLayout 1,
  optLayout, optLayout, {size := some 8, align := some 8}]

private def tyOk (id : TyId) : Except String Unit := checkTy "probe.f" types layouts 0 id

private def cx (model : AllocatorModel) (src : TyId) : CheckCtx :=
  { fnName := "probe.f", types, layouts, instTys := #[(0, src)], places := #[],
    dialect := some (.ofVersion .v0_17_1), allocatorModel := model }

private def ptrCast (model : AllocatorModel) (src dst : TyId) : Except String Nat :=
  checkOp (cx model src) 0 dst (.bitcast false (.inst 0))

private def func (params : Array TyId) (ret : TyId) (body : Array Inst) : Func := {
  dialect := .ofVersion .v0_17_1
  name := "probe.f"
  types, layouts, params, ret, body, globals := #[] }

private def has (r : Except String α) (marker : String) : Bool :=
  match r with
  | .error e => (e.splitOn marker).length > 1
  | .ok _ => false

private def describe (r : Except String α) : String :=
  match r with
  | .error e => e
  | .ok _ => "accepted"

def main : IO Unit := do
  -- The pointer is a value: alone, optional, in a struct, in an array.
  for id in [2, 3, 5, 8, 9, 13, 14, 27] do
    require (tyOk id).isOk s!"type {id} is rejected: {describe (tyOk id)}"
  -- The opaque type itself and every pointer kind that needs its size.
  let noSize := "has no size, alignment or values"
  for id in [1, 4, 7, 10, 11, 12, 15, 16, 17] do
    require (has (tyOk id) noSize) s!"type {id}: {describe (tyOk id)}"
  -- An export that does not mark the opaque type (`other`) keeps the old rejection.
  for id in [24, 25] do
    require (has (tyOk id) "type 'm.Handle' is outside the subset (otherwise unsupported)")
      s!"unmarked type {id}: {describe (tyOk id)}"
  for model in [AllocatorModel.std, .translated] do
    -- To an opaque pointer from error-free typed storage, between opaque pointees, a
    -- qualifier change and the optional wrap.
    for (s, d) in [(6, 2), (6, 5), (2, 5), (5, 2), (2, 8), (8, 2), (2, 9), (9, 2), (2, 3), (26, 3),
        (3, 27), (27, 3)] do
      require (ptrCast model s d).isOk s!"cast {s} → {d} is rejected: {describe (ptrCast model s d)}"
    -- Erasing error storage: the bytes behind the handle would lose their symbolic errors.
    for d in [2, 5] do
      require (has (ptrCast model 20 d) "symbolic") s!"cast 20 → {d}: {describe (ptrCast model 20 d)}"
  -- Recovering a typed pointer: only the translated allocator model, and only error-free.
  for s in [2, 5] do
    require (has (ptrCast .std s 6) "unresolved or cyclic symbolic storage provenance")
      s!"std: cast {s} → 6: {describe (ptrCast .std s 6)}"
    require (ptrCast .translated s 6).isOk s!"translated: cast {s} → 6: {describe (ptrCast .translated s 6)}"
    for model in [AllocatorModel.std, .translated] do
      require (has (ptrCast model s 20) "symbolic") s!"cast {s} → 20: {describe (ptrCast model s 20)}"
  -- Zig rejects these at compile time; a hand-made AIR that has them is rejected all the same.
  let arg : Inst := { id := 0, ty := 2, op := .arg 0 }
  -- One instruction on the `*Handle` parameter, of result type `ty`.
  let one (ty : TyId) (op : Op) : Except String Unit :=
    check (func #[2] ty #[arg, { id := 1, ty, op }, { id := 2, ty := 22, op := .ret (.inst 1) }])
  let inMemory := "a value in memory is outside the subset"
  let noItems := "which has no items"
  let noItemSize := "type 1 has no size in the AIR file"
  let p : Val := .inst 0
  for (what, ty, op, marker) in [
      -- Accesses through the pointer: an opaque value, and a typed value at its address.
      ("load", 1, Op.load p, noSize), ("u32 load", 0, .load p, inMemory),
      ("u32 store", 21, .store p (.int 0 5), inMemory),
      ("atomic load", 0, .atomicLoad p .seqCst, inMemory),
      ("field pointer", 6, .fieldPtr p 0, inMemory),
      -- Arithmetic that needs the item size.
      ("pointer add", 2, .ptrAdd false p (.int 28 1), noItemSize),
      ("item pointer", 2, .elemPtr p (.int 28 1), noItemSize),
      ("item", 0, .ptrElemVal p (.int 28 0), noItems),
      ("memset", 21, .memset p (.int 0 1), noItems),
      ("slice", 11, .slice p (.int 28 1), noSize)] do
    require (has (one ty op) marker) s!"{what} through *Handle: {describe (one ty op)}"
  let byValue := func #[1] 21 #[{ id := 0, ty := 1, op := .arg 0 }, { id := 1, ty := 22, op := .ret .void }]
  require (has (check byValue) noSize) s!"by-value parameter: {describe (check byValue)}"
  let retValue := func #[2] 1 #[arg, { id := 1, ty := 22, op := .ret (.inst 0) }]
  require (has (check retValue) noSize) s!"opaque return type: {describe (check retValue)}"
  -- The pointer itself passes through a function.
  let passes := func #[2] 2 #[arg, { id := 1, ty := 22, op := .ret (.inst 0) }]
  require (check passes).isOk s!"*Handle → *Handle: {describe (check passes)}"
  IO.println "opaque pointer checker controls passed"
