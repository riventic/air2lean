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
  .optional 6, .optional 5, .int false 64,                                   -- 26..28: ?*u32, ?*anyopaque, usize
  .opaque "Io.AnyFuture" true, .ptr "one" false 29, .optional 30,            -- 29..31: a std opaque type, its pointers
  .int false 8, .ptr "slice" false 32,                                       -- 32..33: u8, []u8
  .allocator, .io, .thread, .future 0,                                       -- 34..37: the std model handles
  .ptr "one" false 34, .optional 33, .ptr "one" false 13,                    -- 38..40: *Allocator, ?[]u8, *Cell
  .tuple #[0, 23], .ptr "many" false 32, .optional 42]                       -- 41..43: tuple, [*]u8, ?[*]u8

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
  optLayout, optLayout, {size := some 8, align := some 8},
  {}, ptrLayout 1, optLayout,
  {size := some 1, align := some 1}, {size := some 16, align := some 8, ptrAlign := some 1},
  {size := some 16, align := some 8, offsets := #[0, 8]}, {size := some 16, align := some 8, offsets := #[0, 8]},
  {size := some 8, align := some 8, offsets := #[0]}, {size := some 16, align := some 8, offsets := #[0, 8]},
  ptrLayout 8, {size := some 16, align := some 8}, ptrLayout 8,
  {size := some 8, align := some 4, offsets := #[0, 4]}, ptrLayout 1, optLayout]

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
  -- An opaque type of the standard library: no value behind any pointer (the handle of a
  -- hand-written std model). Its presence in this table rejects nothing else here.
  for id in [29, 30, 31] do
    require (has (tyOk id) "opaque type 'Io.AnyFuture' is declared in the standard library")
      s!"std opaque type {id}: {describe (tyOk id)}"
  for model in [AllocatorModel.std, .translated] do
    for (s, d) in [(30, 6), (6, 30), (30, 5), (5, 30), (30, 2), (2, 30)] do
      require (!(ptrCast model s d).isOk) s!"std opaque cast {s} → {d} is accepted"
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
      ("atomic store", 21, .atomicStore p (.int 0 5) .seqCst, inMemory),
      ("atomic rmw", 0, .atomicRmw .add .seqCst p (.int 0 1), inMemory),
      ("cmpxchg", 0, .cmpxchg false p (.int 0 0) (.int 0 1) .seqCst .seqCst, inMemory),
      ("field pointer", 6, .fieldPtr p 0, inMemory),
      -- Arithmetic that needs the item size.
      ("pointer add", 2, .ptrAdd false p (.int 28 1), noItemSize),
      ("item pointer", 2, .elemPtr p (.int 28 1), noItemSize),
      ("item", 0, .ptrElemVal p (.int 28 0), noItems),
      ("memset", 21, .memset p (.int 0 1), noItems),
      ("slice", 11, .slice p (.int 28 1), noSize)] do
    require (has (one ty op) marker) s!"{what} through *Handle: {describe (one ty op)}"
  -- `@memcpy` needs items on both sides: a single-item pointer to an opaque type (declared or
  -- the primitive) or to a scalar has none, as destination and as source.
  let copy (dst src : TyId) : Except String Unit :=
    check (func #[dst, src] 21 #[{ id := 0, ty := dst, op := .arg 0 }, { id := 1, ty := src, op := .arg 1 },
      { id := 2, ty := 21, op := .memcpy false (.inst 0) (.inst 1) }, { id := 3, ty := 22, op := .ret .void }])
  require (copy 33 33).isOk s!"memcpy []u8 ← []u8: {describe (copy 33 33)}"
  for single in [2, 5, 6] do
    require (has (copy single 33) noItems) s!"memcpy {single} ← []u8: {describe (copy single 33)}"
    require (has (copy 33 single) noItems) s!"memcpy []u8 ← {single}: {describe (copy 33 single)}"
  let byValue := func #[1] 21 #[{ id := 0, ty := 1, op := .arg 0 }, { id := 1, ty := 22, op := .ret .void }]
  require (has (check byValue) noSize) s!"by-value parameter: {describe (check byValue)}"
  let retValue := func #[2] 1 #[arg, { id := 1, ty := 22, op := .ret (.inst 0) }]
  require (has (check retValue) noSize) s!"opaque return type: {describe (check retValue)}"
  -- The pointer itself passes through a function.
  let passes := func #[2] 2 #[arg, { id := 1, ty := 22, op := .ret (.inst 0) }]
  require (check passes).isOk s!"*Handle → *Handle: {describe (check passes)}"
  -- A field of a value (`valueFields?`): a struct, a union and a tuple have fields; a std model
  -- handle is one whole value. The emitter's projection or record would not type in Lean.
  let noFields := "which has no fields in the model"
  let outOfRange := "is out of range"
  -- One op on a value of type `src` (instruction 0), of result type `ty`.
  let onValue (src ty : TyId) (op : Op) : Except String Nat := checkOp (cx .std src) 0 ty op
  -- The same with instruction 0 a local that the model holds as a Lean value (a place).
  let onPlace (src ty : TyId) (op : Op) : Except String Nat :=
    checkOp { cx .std src with places := #[0] } 0 ty op
  for (handle, name) in [(34, "`std.mem.Allocator`"), (35, "`std.Io`"), (36, "`std.Thread`"),
      (37, "`std.Io.Future`")] do
    let read := onValue handle 5 (.structFieldVal (.inst 0) 0)
    require (has read noFields && has read name) s!"field of handle {handle}: {describe read}"
    let build := onValue 5 handle (.aggregateInit #[.inst 0, .inst 0])
    require (has build noFields && has build name) s!"literal of handle {handle}: {describe build}"
  -- Scalars and pointers have no fields either.
  for src in [0, 5, 33] do
    require (has (onValue src 0 (.structFieldVal (.inst 0) 0)) noFields)
      s!"field of type {src}: {describe (onValue src 0 (.structFieldVal (.inst 0) 0))}"
  require (has (onValue 5 0 (.aggregateInit #[.inst 0])) noFields) "a scalar literal is accepted"
  -- Controls: the fields of a struct and of a tuple, and their literals, in range.
  for (src, idx, ty) in [(13, 0, 2), (13, 1, 3), (41, 0, 0), (41, 1, 23)] do
    require (onValue src ty (.structFieldVal (.inst 0) idx)).isOk
      s!"field {idx} of type {src}: {describe (onValue src ty (.structFieldVal (.inst 0) idx))}"
  for src in [13, 41] do
    require (has (onValue src 0 (.structFieldVal (.inst 0) 2)) outOfRange)
      s!"field 2 of type {src}: {describe (onValue src 0 (.structFieldVal (.inst 0) 2))}"
    require (onValue 0 src (.aggregateInit #[.inst 0, .inst 0])).isOk s!"literal of type {src} is rejected"
    require (has (onValue 0 src (.aggregateInit #[.inst 0, .inst 0, .inst 0])) outOfRange)
      s!"literal of type {src} with three operands is accepted"
  require (onValue 2 14 (.aggregateInit #[.inst 0, .inst 0])).isOk "an array literal is rejected"
  -- A field pointer: into a local held as a value it is the value's field; into memory it is an
  -- address, also of a handle.
  require (has (onPlace 38 5 (.fieldPtr (.inst 0) 0)) noFields)
    s!"field pointer into a handle local: {describe (onPlace 38 5 (.fieldPtr (.inst 0) 0))}"
  require (onPlace 40 2 (.fieldPtr (.inst 0) 0)).isOk "field pointer into a struct local is rejected"
  require (has (onPlace 40 2 (.fieldPtr (.inst 0) 2)) outOfRange) "field 2 of a struct local is accepted"
  require (onValue 38 5 (.fieldPtr (.inst 0) 1)).isOk
    s!"field pointer into a handle in memory: {describe (onValue 38 5 (.fieldPtr (.inst 0) 1))}"
  -- A cast with a slice on one side only (hand-made: Zig casts the slice's `.ptr`): the model's
  -- slice is a pointer and a length, the other side is not.
  let oneSlice := "a cast between a slice (a pointer and a length) and a type that is not a slice"
  for model in [AllocatorModel.std, .translated] do
    for (s, d) in [(33, 5), (5, 33), (33, 6), (6, 33), (33, 42), (42, 33), (33, 28), (28, 33),
        (39, 43), (43, 39), (39, 27), (33, 43), (42, 39)] do
      require (has (ptrCast model s d) oneSlice) s!"cast {s} → {d}: {describe (ptrCast model s d)}"
    for (s, d) in [(33, 33), (33, 39), (42, 43)] do
      require (ptrCast model s d).isOk s!"cast {s} → {d} is rejected: {describe (ptrCast model s d)}"
  IO.println "opaque pointer checker controls passed"
