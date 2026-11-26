import Air2Lean.Sem

/-!
The interpreter's arms on concrete inputs (V01; the killing check of the `sem` mutants of
`mutations.py`, Q02).

Each check runs `Sem.execFunc` (one check `execBody` with a view) on a hand-built function of one
instruction kind and compares the outcome — a value, a panic or illegal-behaviour kind, or stuck —
with a literal that states Zig's meaning of that instruction on that input. The literals are
written out, never computed through `ZigLean`, so a check does not follow a changed arm. The
families: integer arithmetic in each overflow mode, division and remainder, bit and boolean
operations, comparisons of integers, booleans and pointers, casts, optionals and error unions,
constants, memory (blocks, register locals, fields, items of pointers and slices), control flow
and calls (the oracle, the panic handlers, the argument check, the frame's end).

`lean --run` prints one `check ok <name>` or `check FAILED <name>` line per check and fails when
any check failed. `mutations.py` requires each designated mutant of `Air2Lean/Sem.lean` to fail
the checks it names.
-/

namespace SemArms

open Air2Lean Air2Lean.Sem

/-- How a run ends. -/
inductive Outcome where
  | val (v : Value)
  | err (e : Zig.Error)
  | stuck
  deriving DecidableEq

structure Check where
  name : String
  run : Zig.MemM Value
  want : Outcome

def outcome (x : Zig.MemM Value) : Outcome :=
  match (x.run {}).run with
  | some (.ok (v, _)) => .val v
  | some (.error e) => .err e
  | none => .stuck

/-! ## The type table of every function here -/

def tU8 : TyId := 0
def tI8 : TyId := 1
def tBool : TyId := 2
def tVoid : TyId := 3
def tNoret : TyId := 4
def tU32 : TyId := 5
def tPU8 : TyId := 6
def tOpt : TyId := 7
def tSet : TyId := 8
def tEU : TyId := 9
def tU64 : TyId := 10
def tS : TyId := 11
def tPS : TyId := 12
def tMany : TyId := 13
def tSlice : TyId := 14
def tArr : TyId := 15
def tPArr : TyId := 16
def tPBool : TyId := 17
def tPPU8 : TyId := 18
def tPU32 : TyId := 19
def tManyU32 : TyId := 20
def tArr2 : TyId := 21
def tPArr2 : TyId := 22
def tArrZ : TyId := 23
def tPArrZ : TyId := 24

def types : Array Ty := #[
  .int false 8, .int true 8, .bool, .void, .noreturn, .int false 32,
  .ptr "one" false tU8, .optional tU8, .errorSet (some #["A", "B"]), .errorUnion tSet tU8,
  .int false 64, .struct "S" "extern" #[("a", tU8), ("b", tU8), ("c", tU32)],
  .ptr "one" false tS, .ptr "many" false tU8, .ptr "slice" false tU8, .array 4 tU8 false,
  .ptr "one" false tArr, .ptr "one" false tBool, .ptr "one" false tPU8, .ptr "one" false tU32,
  .ptr "many" false tU32, .array 2 tU8 false, .ptr "one" false tArr2, .array 2 tU8 true,
  .ptr "one" false tArrZ]

def ptrLayout (align : Nat) : Layout := { size := some 8, align := some 8, ptrAlign := some align }

def layouts : Array Layout := #[
  { size := some 1, align := some 1 }, { size := some 1, align := some 1 },
  { size := some 1, align := some 1 }, { size := some 0, align := some 1 }, {},
  { size := some 4, align := some 4 }, ptrLayout 1, { size := some 2, align := some 1 },
  { size := some 2, align := some 2 }, { size := some 4, align := some 2 },
  { size := some 8, align := some 8 }, { size := some 8, align := some 4, offsets := #[0, 1, 4] },
  ptrLayout 4, ptrLayout 1, { size := some 16, align := some 8, ptrAlign := some 1 },
  { size := some 4, align := some 1 }, ptrLayout 1, ptrLayout 1, ptrLayout 8, ptrLayout 4,
  ptrLayout 4, { size := some 2, align := some 1 }, ptrLayout 1, { size := some 3, align := some 1 },
  ptrLayout 1]

/-- A function `arms.f` with the given parameter types: its `arg` instructions `0, 1, …`, then
`body`. -/
def fn (params : Array TyId) (body : Array Inst) : Func :=
  { dialect := .ofVersion .v0_17_1, name := "arms.f", params, ret := tU8, types, layouts,
    globals := #[],
    body := (params.mapIdx fun k t => (⟨k, t, .arg k⟩ : Inst)) ++ body }

def ret (id : InstId) (v : Val) : Inst := ⟨id, tNoret, .ret v⟩

/-- `f(a, b) = op a b` at the result type `rt`. -/
def bin (pt rt : TyId) (op : Val → Val → Op) : Func :=
  fn #[pt, pt] #[⟨2, rt, op (.inst 0) (.inst 1)⟩, ret 3 (.inst 2)]

/-- `f(a) = op a` at the result type `rt`. -/
def un (pt rt : TyId) (op : Val → Op) : Func :=
  fn #[pt] #[⟨1, rt, op (.inst 0)⟩, ret 2 (.inst 1)]

def u8 (n : Nat) : Value := .int false 8 (BitVec.ofNat 8 n)
def i8 (n : Int) : Value := .int true 8 (BitVec.ofInt 8 n)
def u32 (n : Nat) : Value := .int false 32 (BitVec.ofNat 32 n)
def u64 (n : Nat) : Value := .int false 64 (BitVec.ofNat 64 n)
def cU8 (n : Int) : Val := .int tU8 n
def cIdx (n : Int) : Val := .int tU64 n

/-- The one direct callee: `arms.pair(a, b) = 16 a + b`, so the order of the arguments shows. -/
def oracle : Oracle := fun name vs =>
  match name, vs with
  | "arms.pair", [a, b] => pure (.int false 8 (a.toBV 8 * 16 + b.toBV 8))
  | _, _ => StateT.lift Sem.stuck

def exec (f : Func) (args : List Value) (prog : Prog := { funcs := #[] }) : Zig.MemM Value :=
  execFunc prog oracle f args

def good (name : String) (f : Func) (args : List Value) (v : Value) : Check :=
  ⟨name, exec f args, .val v⟩

def bad (name : String) (f : Func) (args : List Value) (e : Zig.Error) : Check :=
  ⟨name, exec f args, .err e⟩

def stuckOn (name : String) (f : Func) (args : List Value) : Check :=
  ⟨name, exec f args, .stuck⟩

/-! ## Arithmetic -/

def arith (op : ArithOp) (mode : Mode) (t : TyId := tU8) : Func := bin t t (.arith op mode)

def arithChecks : List Check := [
  good "arith.add.checked" (arith .add .checked) [u8 3, u8 4] (u8 7),
  bad "arith.add.checked.overflow" (arith .add .checked) [u8 200, u8 100] .overflow,
  good "arith.add.unchecked" (arith .add .unchecked) [u8 3, u8 4] (u8 7),
  bad "arith.add.unchecked.overflow" (arith .add .unchecked) [u8 200, u8 100] .illegal,
  good "arith.add.wrap" (arith .add .wrap) [u8 200, u8 100] (u8 44),
  good "arith.add.sat" (arith .add .sat) [u8 200, u8 100] (u8 255),
  good "arith.sub.checked" (arith .sub .checked) [u8 5, u8 3] (u8 2),
  bad "arith.sub.checked.overflow" (arith .sub .checked) [u8 3, u8 5] .overflow,
  good "arith.sub.unchecked" (arith .sub .unchecked) [u8 5, u8 3] (u8 2),
  bad "arith.sub.unchecked.overflow" (arith .sub .unchecked) [u8 3, u8 5] .illegal,
  good "arith.sub.wrap" (arith .sub .wrap) [u8 3, u8 5] (u8 254),
  good "arith.sub.sat" (arith .sub .sat) [u8 3, u8 5] (u8 0),
  good "arith.mul.checked" (arith .mul .checked) [u8 3, u8 5] (u8 15),
  bad "arith.mul.checked.overflow" (arith .mul .checked) [u8 20, u8 20] .overflow,
  good "arith.mul.unchecked" (arith .mul .unchecked) [u8 3, u8 5] (u8 15),
  bad "arith.mul.unchecked.overflow" (arith .mul .unchecked) [u8 20, u8 20] .illegal,
  good "arith.mul.wrap" (arith .mul .wrap) [u8 20, u8 20] (u8 144),
  good "arith.mul.sat" (arith .mul .sat) [u8 20, u8 20] (u8 255),
  -- The signedness is the type's: `100 + 100` overflows `i8` and `-1 + 1` does not.
  bad "arith.add.signed.overflow" (arith .add .checked tI8) [i8 100, i8 100] .overflow,
  good "arith.add.signed" (arith .add .checked tI8) [i8 (-1), i8 1] (i8 0),
  good "arith.add.signed.sat" (arith .add .sat tI8) [i8 100, i8 100] (i8 127),
  good "arith.sub.signed.sat" (arith .sub .sat tI8) [i8 (-100), i8 100] (i8 (-128)),
  -- An operand of another width than the instruction's type is ill-typed.
  stuckOn "arith.width" (fn #[tU32, tU32] #[⟨2, tU8, .arith .add .checked (.inst 0) (.inst 1)⟩,
    ret 3 (.inst 2)]) [u32 1, u32 2]]

def div (op : DivOp) (t : TyId := tI8) : Func := bin t t (.div op)

-- Sema checks the divisor, `minInt / -1` and an exact division's remainder in instructions
-- before the operation (the panic handlers of `callChecks`), so one that reaches it is illegal.
def divChecks : List Check := [
  good "div.trunc" (div .divTrunc) [i8 7, i8 2] (i8 3),
  good "div.trunc.neg" (div .divTrunc) [i8 (-7), i8 2] (i8 (-3)),
  bad "div.trunc.zero" (div .divTrunc) [i8 7, i8 0] .illegal,
  bad "div.trunc.overflow" (div .divTrunc) [i8 (-128), i8 (-1)] .illegal,
  good "div.trunc.unsigned" (div .divTrunc tU8) [u8 200, u8 3] (u8 66),
  good "div.floor" (div .divFloor) [i8 7, i8 2] (i8 3),
  good "div.floor.neg" (div .divFloor) [i8 (-7), i8 2] (i8 (-4)),
  good "div.exact" (div .divExact) [i8 6, i8 2] (i8 3),
  bad "div.exact.remainder" (div .divExact) [i8 7, i8 2] .illegal,
  good "div.rem" (div .rem) [i8 7, i8 2] (i8 1),
  good "div.rem.neg" (div .rem) [i8 (-7), i8 2] (i8 (-1)),
  bad "div.rem.zero" (div .rem) [i8 7, i8 0] .illegal,
  good "div.mod" (div .mod) [i8 7, i8 2] (i8 1),
  good "div.mod.neg" (div .mod) [i8 (-7), i8 2] (i8 1),
  good "div.ceil" (div .divCeil) [i8 7, i8 2] (i8 4),
  good "div.ceil.neg" (div .divCeil) [i8 (-7), i8 2] (i8 (-3)),
  good "minmax.max" (bin tU8 tU8 (.minMax true)) [u8 3, u8 5] (u8 5),
  good "minmax.min" (bin tU8 tU8 (.minMax false)) [u8 3, u8 5] (u8 3),
  good "minmax.max.signed" (bin tI8 tI8 (.minMax true)) [i8 (-1), i8 1] (i8 1),
  good "minmax.min.signed" (bin tI8 tI8 (.minMax false)) [i8 (-1), i8 1] (i8 (-1))]

def bitChecks : List Check := [
  good "bit.and" (bin tU8 tU8 (.bit .and)) [u8 12, u8 10] (u8 8),
  good "bit.or" (bin tU8 tU8 (.bit .or)) [u8 12, u8 10] (u8 14),
  good "bit.xor" (bin tU8 tU8 (.bit .xor)) [u8 12, u8 10] (u8 6),
  good "bit.and.bool" (bin tBool tBool (.bit .and)) [.bool true, .bool false] (.bool false),
  good "bit.and.bool.true" (bin tBool tBool (.bit .and)) [.bool true, .bool true] (.bool true),
  good "bit.or.bool" (bin tBool tBool (.bit .or)) [.bool true, .bool false] (.bool true),
  good "bit.or.bool.false" (bin tBool tBool (.bit .or)) [.bool false, .bool false] (.bool false),
  good "bit.xor.bool" (bin tBool tBool (.bit .xor)) [.bool true, .bool true] (.bool false),
  good "bit.xor.bool.true" (bin tBool tBool (.bit .xor)) [.bool true, .bool false] (.bool true),
  good "not.int" (un tU8 tU8 .not) [u8 15] (u8 240),
  good "not.bool" (un tBool tBool .not) [.bool true] (.bool false),
  good "bool.and" (bin tBool tBool .boolAnd) [.bool true, .bool false] (.bool false),
  good "bool.and.true" (bin tBool tBool .boolAnd) [.bool true, .bool true] (.bool true),
  good "bool.or" (bin tBool tBool .boolOr) [.bool true, .bool false] (.bool true),
  good "bool.or.false" (bin tBool tBool .boolOr) [.bool false, .bool false] (.bool false)]

/-! ## Comparisons -/

/-- `op` on `(3, 5)`, `(5, 5)` and `(5, 3)`. -/
def cmpRow (label : String) (op : CmpOp) (lt eq gt : Bool) : List Check := [
  good s!"cmp.{label}.less" (bin tU8 tBool (.cmp op)) [u8 3, u8 5] (.bool lt),
  good s!"cmp.{label}.equal" (bin tU8 tBool (.cmp op)) [u8 5, u8 5] (.bool eq),
  good s!"cmp.{label}.greater" (bin tU8 tBool (.cmp op)) [u8 5, u8 3] (.bool gt)]

/-- Four bytes `10, 20, 30, 40` in a block of their own; `k` gets the pointer to the first. -/
def withBytes (k : Zig.Ptr → Zig.MemM Value) : Zig.MemM Value := do
  let p ← Zig.allocStack 4 1
  Zig.store 1 p (10 : BitVec 8)
  Zig.store 1 (p.elem 1 1) (20 : BitVec 8)
  Zig.store 1 (p.elem 1 2) (30 : BitVec 8)
  Zig.store 1 (p.elem 1 3) (40 : BitVec 8)
  k p

/-- `op` on the pointers to items `a` and `b` of one block. -/
def ptrCmp (label : String) (op : CmpOp) (a b : Nat) (want : Bool) : Check :=
  ⟨s!"cmp.ptr.{label}", withBytes fun p =>
    exec (bin tMany tBool (.cmp op)) [.ptr (p.elem 1 (BitVec.ofNat 64 a)), .ptr (p.elem 1 (BitVec.ofNat 64 b))],
    .val (.bool want)⟩

def cmpChecks : List Check :=
  cmpRow "lt" .lt true false false ++ cmpRow "le" .le true true false ++
  cmpRow "gt" .gt false false true ++ cmpRow "ge" .ge false true true ++
  cmpRow "eq" .eq false true false ++ cmpRow "ne" .ne true false true ++ [
  good "cmp.lt.signed" (bin tI8 tBool (.cmp .lt)) [i8 (-1), i8 1] (.bool true),
  good "cmp.ge.signed" (bin tI8 tBool (.cmp .ge)) [i8 (-1), i8 1] (.bool false),
  good "cmp.bool.eq" (bin tBool tBool (.cmp .eq)) [.bool true, .bool true] (.bool true),
  good "cmp.bool.eq.differ" (bin tBool tBool (.cmp .eq)) [.bool true, .bool false] (.bool false),
  good "cmp.bool.ne" (bin tBool tBool (.cmp .ne)) [.bool true, .bool false] (.bool true),
  good "cmp.bool.ne.same" (bin tBool tBool (.cmp .ne)) [.bool true, .bool true] (.bool false),
  stuckOn "cmp.bool.lt" (bin tBool tBool (.cmp .lt)) [.bool false, .bool true],
  ptrCmp "eq.same" .eq 1 1 true, ptrCmp "eq.differ" .eq 1 2 false,
  ptrCmp "ne.same" .ne 1 1 false, ptrCmp "ne.differ" .ne 1 2 true,
  ptrCmp "lt.less" .lt 1 2 true, ptrCmp "lt.equal" .lt 1 1 false, ptrCmp "lt.greater" .lt 2 1 false,
  ptrCmp "le.less" .le 1 2 true, ptrCmp "le.equal" .le 1 1 true, ptrCmp "le.greater" .le 2 1 false,
  ptrCmp "gt.less" .gt 1 2 false, ptrCmp "gt.equal" .gt 1 1 false, ptrCmp "gt.greater" .gt 2 1 true,
  ptrCmp "ge.less" .ge 1 2 false, ptrCmp "ge.equal" .ge 1 1 true, ptrCmp "ge.greater" .ge 2 1 true]

/-! ## Casts, optionals, error unions, constants -/

def castChecks : List Check := [
  good "cast.int" (un tU32 tU8 (.intCast true)) [u32 200] (u8 200),
  bad "cast.int.overflow" (un tU32 tU8 (.intCast true)) [u32 300] .overflow,
  bad "cast.int.unsafe.overflow" (un tU32 tU8 (.intCast false)) [u32 300] .illegal,
  bad "cast.int.negative" (un tI8 tU8 (.intCast true)) [i8 (-1)] .overflow,
  bad "cast.int.to.signed" (un tU8 tI8 (.intCast true)) [u8 200] .overflow,
  bad "cast.int.negative.widen" (un tI8 tU32 (.intCast true)) [i8 (-1)] .overflow,
  good "cast.int.widen.signed" (un tI8 tU32 (.intCast true)) [i8 5] (u32 5),
  good "cast.trunc" (un tU32 tU8 .trunc) [u32 511] (u8 255),
  good "cast.trunc.signed" (un tU32 tI8 .trunc) [u32 384] (i8 (-128)),
  good "cast.bitcast" (un tU8 tI8 (.bitcast false)) [u8 200] (i8 (-56)),
  good "cast.bitcast.unsigned" (un tI8 tU8 (.bitcast false)) [i8 (-1)] (u8 255),
  stuckOn "cast.bitcast.width" (un tU32 tU8 (.bitcast false)) [u32 1]]

def optChecks : List Check := [
  good "opt.nonnull.some" (un tOpt tBool .isNonNull) [.optSome (u8 7)] (.bool true),
  good "opt.nonnull.none" (un tOpt tBool .isNonNull) [.optNone] (.bool false),
  good "opt.null.some" (un tOpt tBool .isNull) [.optSome (u8 7)] (.bool false),
  good "opt.null.none" (un tOpt tBool .isNull) [.optNone] (.bool true),
  good "opt.payload" (un tOpt tU8 .optPayload) [.optSome (u8 7)] (u8 7),
  bad "opt.payload.none" (un tOpt tU8 .optPayload) [.optNone] .illegal,
  good "opt.wrap" (un tU8 tOpt .wrapOptional) [u8 7] (.optSome (u8 7)),
  stuckOn "opt.wrap.type" (un tU8 tU8 .wrapOptional) [u8 7],
  good "err.iserr.ok" (un tEU tBool .isErr) [.errOk (u8 7)] (.bool false),
  good "err.iserr.err" (un tEU tBool .isErr) [.errErr "A"] (.bool true),
  good "err.isnonerr.ok" (un tEU tBool .isNonErr) [.errOk (u8 7)] (.bool true),
  good "err.isnonerr.err" (un tEU tBool .isNonErr) [.errErr "A"] (.bool false),
  good "err.payload" (un tEU tU8 .errPayload) [.errOk (u8 7)] (u8 7),
  bad "err.payload.err" (un tEU tU8 .errPayload) [.errErr "A"] .illegal,
  good "err.code" (un tEU tSet .errCode) [.errErr "A"] (.errName "A"),
  bad "err.code.ok" (un tEU tSet .errCode) [.errOk (u8 7)] .illegal,
  good "err.wrap.payload" (un tU8 tEU .wrapErrPayload) [u8 7] (.errOk (u8 7)),
  good "err.wrap.err" (un tSet tEU .wrapErr) [.errName "B"] (.errErr "B"),
  stuckOn "err.wrap.type" (un tU8 tU8 .wrapErrPayload) [u8 7]]

def constChecks : List Check := [
  good "const.int" (fn #[] #[ret 0 (cU8 200)]) [] (u8 200),
  good "const.int.negative" (fn #[] #[ret 0 (.int tI8 (-3))]) [] (i8 (-3)),
  good "const.bool" (fn #[] #[ret 0 (.bool true)]) [] (.bool true),
  good "const.void" (fn #[] #[ret 0 .void]) [] .void,
  good "const.opt.null" (fn #[] #[ret 0 (.optNull tOpt)]) [] .optNone,
  good "const.opt.some" (fn #[] #[ret 0 (.optSome tOpt (cU8 7))]) [] (.optSome (u8 7)),
  good "const.err" (fn #[] #[ret 0 (.err tSet "B")]) [] (.errName "B"),
  good "const.errunion.err" (fn #[] #[ret 0 (.errUnionErr tEU "B")]) [] (.errErr "B"),
  good "const.errunion.ok" (fn #[] #[ret 0 (.errUnionOk tEU (cU8 7))]) [] (.errOk (u8 7)),
  stuckOn "const.errunion.unknown" (fn #[] #[ret 0 (.errUnionErr tEU "Z")]) []]

/-! ## Memory -/

/-- A `u8` local that is a block (its pointer is cast, so its address is taken): instruction 2
is the pointer. -/
def blockLocal (rest : Array Inst) : Func :=
  fn #[tU8] (#[⟨1, tPU8, .alloc⟩, ⟨2, tPU8, .bitcast false (.inst 1)⟩] ++ rest)

/-- A `u8` register local: instruction 1 is its address. -/
def cellLocal (rest : Array Inst) : Func := fn #[tU8] (#[⟨1, tPU8, .alloc⟩] ++ rest)

def store (id : InstId) (p : InstId) (v : Val) : Inst := ⟨id, tVoid, .store (.inst p) v⟩
def load (id : InstId) (t : TyId) (p : InstId) : Inst := ⟨id, t, .load (.inst p)⟩

/-- The struct `S { a: u8, b: u8, c: u32 }` in a block: `b := 9`, `a := 5`, `c := 0x01020304`,
then the load of the field `read` at type `t` through a pointer of type `pt`. -/
def fields (read : Nat) (pt t : TyId) : Func :=
  fn #[] #[⟨0, tPS, .alloc⟩, ⟨1, tPU8, .fieldPtr (.inst 0) 1⟩, ⟨2, tPU8, .fieldPtr (.inst 0) 0⟩,
    ⟨3, tPU32, .fieldPtr (.inst 0) 2⟩, store 4 1 (cU8 9), store 5 2 (cU8 5),
    store 6 3 (.int tU32 16909060), ⟨7, pt, .fieldPtr (.inst 0) read⟩, load 8 t 7, ret 9 (.inst 8)]

/-- A function of one pointer or slice parameter of type `pt`, run on the four bytes. -/
def onBytes (name : String) (pt : TyId) (arg : Zig.Ptr → Value) (body : Array Inst) (want : Outcome) :
    Check :=
  ⟨name, withBytes fun p => exec (fn #[pt] body) [arg p], want⟩

def whole (p : Zig.Ptr) : Value := .slice ⟨p, 4⟩

/-- A function of one pointer parameter of type `pt`, run on the two `u32` items `0x11111111`
and `0x22222222` of a block of their own. -/
def onWords (name : String) (pt : TyId) (body : Array Inst) (want : Outcome) : Check :=
  ⟨name, do
    let p ← Zig.allocStack 8 4
    Zig.store 4 p (286331153 : BitVec 32)
    Zig.store 4 (p.elem 4 1) (572662306 : BitVec 32)
    exec (fn #[pt] body) [.ptr p], want⟩

/-- The frame of `f`: its return value is a pointer to its own block local. -/
def escaping : Func :=
  fn #[] #[⟨0, tPU8, .alloc⟩, ⟨1, tPU8, .bitcast false (.inst 0)⟩, store 2 1 (cU8 7), ret 3 (.inst 1)]

def memChecks : List Check := [
  good "mem.block" (blockLocal #[store 3 2 (.inst 0), load 4 tU8 2, ret 5 (.inst 4)]) [u8 7] (u8 7),
  bad "mem.block.undefined" (blockLocal #[load 3 tU8 2, ret 4 (.inst 3)]) [u8 7] .unspecified,
  good "mem.block.last.store" (blockLocal #[store 3 2 (.inst 0), store 4 2 (cU8 9), load 5 tU8 2,
    ret 6 (.inst 5)]) [u8 7] (u8 9),
  bad "mem.block.store.undef" (blockLocal #[store 3 2 (.inst 0), store 4 2 (.undef tU8),
    load 5 tU8 2, ret 6 (.inst 5)]) [u8 7] .unspecified,
  good "mem.block.bool" (fn #[tBool] #[⟨1, tPBool, .alloc⟩, ⟨2, tPBool, .bitcast false (.inst 1)⟩,
    store 3 2 (.inst 0), load 4 tBool 2, ret 5 (.inst 4)]) [.bool true] (.bool true),
  -- A pointer stored in a block and loaded again still points to the four bytes.
  onBytes "mem.block.ptr" tMany .ptr #[⟨1, tPPU8, .alloc⟩, ⟨2, tPPU8, .bitcast false (.inst 1)⟩,
    store 3 2 (.inst 0), load 4 tMany 2, ⟨5, tU8, .ptrElemVal (.inst 4) (cIdx 3)⟩, ret 6 (.inst 5)]
    (.val (u8 40)),
  good "mem.cell" (cellLocal #[store 2 1 (.inst 0), load 3 tU8 1, ret 4 (.inst 3)]) [u8 7] (u8 7),
  bad "mem.cell.undefined" (cellLocal #[load 2 tU8 1, ret 3 (.inst 2)]) [u8 7] .unspecified,
  good "mem.cell.last.store" (cellLocal #[store 2 1 (.inst 0), store 3 1 (cU8 9), load 4 tU8 1,
    ret 5 (.inst 4)]) [u8 7] (u8 9),
  bad "mem.cell.store.undef" (cellLocal #[store 2 1 (.inst 0), store 3 1 (.undef tU8), load 4 tU8 1,
    ret 5 (.inst 4)]) [u8 7] .unspecified,
  -- Two register locals are two cells.
  good "mem.cell.two" (fn #[tU8] #[⟨1, tPU8, .alloc⟩, ⟨2, tPU8, .alloc⟩, store 3 1 (.inst 0),
    store 4 2 (cU8 9), load 5 tU8 1, ret 6 (.inst 5)]) [u8 7] (u8 7),
  stuckOn "mem.cell.type" (cellLocal #[store 2 1 (.bool true), load 3 tU8 1, ret 4 (.inst 3)]) [u8 7],
  good "mem.field.a" (fields 0 tPU8 tU8) [] (u8 5),
  good "mem.field.b" (fields 1 tPU8 tU8) [] (u8 9),
  good "mem.field.c" (fields 2 tPU32 tU32) [] (u32 16909060),
  onBytes "mem.ptr.add" tMany .ptr #[⟨1, tMany, .ptrAdd false (.inst 0) (cIdx 2)⟩,
    load 2 tU8 1, ret 3 (.inst 2)] (.val (u8 30)),
  onBytes "mem.ptr.sub" tMany (fun p => .ptr (p.elem 1 3)) #[⟨1, tMany, .ptrAdd true (.inst 0) (cIdx 1)⟩,
    load 2 tU8 1, ret 3 (.inst 2)] (.val (u8 30)),
  onBytes "mem.ptr.add.outside" tMany .ptr #[⟨1, tMany, .ptrAdd false (.inst 0) (cIdx 9)⟩,
    ret 2 (cU8 0)] (.err .illegal),
  onBytes "mem.elem.ptr.slice" tSlice whole #[⟨1, tPU8, .elemPtr (.inst 0) (cIdx 2)⟩,
    load 2 tU8 1, ret 3 (.inst 2)] (.val (u8 30)),
  onBytes "mem.elem.ptr.slice.bounds" tSlice whole #[⟨1, tPU8, .elemPtr (.inst 0) (cIdx 4)⟩,
    ret 2 (cU8 0)] (.err .illegal),
  onBytes "mem.elem.ptr.array" tPArr .ptr #[⟨1, tPU8, .elemPtr (.inst 0) (cIdx 2)⟩,
    load 2 tU8 1, ret 3 (.inst 2)] (.val (u8 30)),
  -- The bound of a pointer to an array is the array's length (`*[2]u8` into the four bytes).
  onBytes "mem.elem.ptr.array.bounds" tPArr2 .ptr #[⟨1, tPU8, .elemPtr (.inst 0) (cIdx 2)⟩,
    ret 2 (cU8 0)] (.err .illegal),
  onWords "mem.elem.ptr.wide" tManyU32 #[⟨1, tPU32, .elemPtr (.inst 0) (cIdx 1)⟩,
    load 2 tU32 1, ret 3 (.inst 2)] (.val (u32 572662306)),
  onWords "mem.ptr.add.wide" tManyU32 #[⟨1, tManyU32, .ptrAdd false (.inst 0) (cIdx 1)⟩,
    load 2 tU32 1, ret 3 (.inst 2)] (.val (u32 572662306)),
  onWords "mem.elem.val.wide" tManyU32 #[⟨1, tU32, .ptrElemVal (.inst 0) (cIdx 1)⟩, ret 2 (.inst 1)]
    (.val (u32 572662306)),
  onBytes "mem.elem.val" tMany .ptr #[⟨1, tU8, .ptrElemVal (.inst 0) (cIdx 2)⟩, ret 2 (.inst 1)]
    (.val (u8 30)),
  onBytes "mem.elem.val.array.last" tPArr .ptr #[⟨1, tU8, .ptrElemVal (.inst 0) (cIdx 3)⟩,
    ret 2 (.inst 1)] (.val (u8 40)),
  onBytes "mem.elem.val.array.bounds" tPArr2 .ptr #[⟨1, tU8, .ptrElemVal (.inst 0) (cIdx 2)⟩,
    ret 2 (.inst 1)] (.err .illegal),
  -- `*[2:0]u8`: the sentinel is an item too, the one after it is not.
  onBytes "mem.elem.val.sentinel" tPArrZ .ptr #[⟨1, tU8, .ptrElemVal (.inst 0) (cIdx 2)⟩,
    ret 2 (.inst 1)] (.val (u8 30)),
  onBytes "mem.elem.val.sentinel.bounds" tPArrZ .ptr #[⟨1, tU8, .ptrElemVal (.inst 0) (cIdx 3)⟩,
    ret 2 (.inst 1)] (.err .illegal),
  onBytes "mem.slice.elem" tSlice whole #[⟨1, tU8, .sliceElemVal (.inst 0) (cIdx 2)⟩,
    ret 2 (.inst 1)] (.val (u8 30)),
  onBytes "mem.slice.elem.last" tSlice whole #[⟨1, tU8, .sliceElemVal (.inst 0) (cIdx 3)⟩,
    ret 2 (.inst 1)] (.val (u8 40)),
  onBytes "mem.slice.elem.bounds" tSlice whole #[⟨1, tU8, .sliceElemVal (.inst 0) (cIdx 4)⟩,
    ret 2 (.inst 1)] (.err .illegal),
  -- A shorter slice of the same bytes: the bound is the slice's length, not the block's.
  onBytes "mem.slice.elem.len" tSlice (fun p => .slice ⟨p, 2⟩)
    #[⟨1, tU8, .sliceElemVal (.inst 0) (cIdx 2)⟩, ret 2 (.inst 1)] (.err .illegal),
  onBytes "mem.slice.len" tSlice (fun p => .slice ⟨p, 3⟩) #[⟨1, tU64, .sliceLen (.inst 0)⟩,
    ret 2 (.inst 1)] (.val (u64 3)),
  onBytes "mem.slice.ptr" tSlice (fun p => .slice ⟨p.elem 1 1, 3⟩) #[⟨1, tMany, .slicePtr (.inst 0)⟩,
    load 2 tU8 1, ret 3 (.inst 2)] (.val (u8 20)),
  -- A length that is not `u64`, and a slice's pointer at a non-pointer type, are ill-typed.
  onBytes "mem.slice.len.type" tSlice whole #[⟨1, tU32, .sliceLen (.inst 0)⟩, ret 2 (.inst 1)] .stuck,
  onBytes "mem.slice.ptr.type" tSlice whole #[⟨1, tU64, .slicePtr (.inst 0)⟩, ret 2 (.inst 1)] .stuck,
  -- A viewed slice reads the view's items, not memory (`Ctx.view`, `Air2Lean.SemView`).
  ⟨"mem.slice.view", withBytes fun p => do
    let f := fn #[tSlice] #[⟨1, tU8, .sliceElemVal (.inst 0) (cIdx 2)⟩, ret 2 (.inst 1)]
    let view : InstId → Option (Array Value) := fun k => if k = 0 then some #[u8 1, u8 2, u8 3, u8 4] else none
    let (e, _) ← (execBody ⟨{ funcs := #[] }, f, [whole p], oracle, view⟩ f.body.toList (fun _ => none)).run {}
    match e with
    | .ret v => pure v
    | _ => StateT.lift Sem.stuck, .val (u8 3)⟩,
  -- The frame ends at the return: a pointer to a local of it is dangling afterwards.
  ⟨"mem.frame.freed", do
    match ← exec escaping [] with
    | .ptr p => do pure (.int false 8 (← Zig.load (BitVec 8) 1 p))
    | _ => StateT.lift Sem.stuck, .err .illegal⟩,
  -- Two block locals of one frame are distinct blocks.
  good "mem.frame.two" (fn #[] #[⟨0, tPU8, .alloc⟩, ⟨1, tPU8, .bitcast false (.inst 0)⟩,
    ⟨2, tPU8, .alloc⟩, ⟨3, tPU8, .bitcast false (.inst 2)⟩, store 4 1 (cU8 7), store 5 3 (cU8 9),
    load 6 tU8 1, ret 7 (.inst 6)]) [] (u8 7)]

/-! ## Control flow -/

/-- `switch (x) { 1 => 10, 2, 3 => 20, 5...7 => 30, else => 40 }`. -/
def switch : Func :=
  fn #[tU8] #[⟨1, tNoret, .switchBr (.inst 0) #[
      ⟨#[cU8 1], #[], #[ret 2 (cU8 10)]⟩, ⟨#[cU8 2, cU8 3], #[], #[ret 3 (cU8 20)]⟩,
      ⟨#[], #[(cU8 5, cU8 7)], #[ret 4 (cU8 30)]⟩] #[ret 5 (cU8 40)]⟩]

/-- `i = 0; while (i < n) i += 1; return i`, the counter a register local. -/
def count : Func :=
  fn #[tU8] #[⟨1, tPU8, .alloc⟩, store 2 1 (cU8 0), ⟨3, tNoret, .loop #[
    load 4 tU8 1, ⟨5, tBool, .cmp .lt (.inst 4) (.inst 0)⟩,
    ⟨6, tNoret, .condBr (.inst 5)
      #[⟨7, tU8, .arith .add .checked (.inst 4) (cU8 1)⟩, store 8 1 (.inst 7), ⟨9, tNoret, .«repeat» 3⟩]
      #[ret 10 (.inst 4)]⟩]⟩]

/-- `count` with a pointer parameter: the function uses memory, so its loop pays steps. -/
def countMem : Func := { count with params := #[tU8, tMany] }

/-- The steps a run of `f` in the program of `f` alone pays (`Mem.ticks`). -/
def ticks (f : Func) (args : List Value) : Zig.MemM Value := do
  let before := (← get).ticks
  let _ ← exec f args { funcs := #[f] }
  pure (u64 ((← get).ticks - before))

/-- `f(again, p) = if (again) f(again, p) else 7`: recursive, and it uses memory (`p`). -/
def recursive : Func :=
  fn #[tBool, tMany] #[⟨2, tNoret, .condBr (.inst 0)
    #[⟨3, tU8, .call (.func "arms.f" false none) #[.inst 0, .inst 1]⟩, ret 4 (.inst 3)]
    #[ret 5 (cU8 7)]⟩]

def tryFn : Func :=
  fn #[tEU] #[⟨1, tU8, .«try» (.inst 0) #[ret 2 (cU8 99)]⟩, ret 3 (.inst 1)]

def panicCall (member : String) : Func :=
  fn #[] #[⟨0, tNoret, .call (.func member true none) #[]⟩, ⟨1, tNoret, .unreach⟩]

def fullPanic (member : String) : String := "debug.FullPanic((function 'defaultPanic'))." ++ member

def flowChecks : List Check := [
  good "flow.arg.second" (fn #[tU8, tU8] #[ret 2 (.inst 1)]) [u8 3, u8 4] (u8 4),
  good "flow.block" (fn #[] #[⟨0, tU8, .block #[⟨1, tNoret, .br 0 (cU8 7)⟩]⟩, ret 2 (.inst 0)]) [] (u8 7),
  -- A `br` of the outer block from inside an inner one skips the rest of both.
  good "flow.block.outer" (fn #[] #[⟨0, tU8, .block #[
    ⟨1, tU8, .block #[⟨2, tNoret, .br 0 (cU8 5)⟩]⟩, ⟨3, tNoret, .br 0 (cU8 9)⟩]⟩, ret 4 (.inst 0)]) [] (u8 5),
  good "flow.cond.then" (fn #[tBool] #[⟨1, tNoret, .condBr (.inst 0) #[ret 2 (cU8 1)] #[ret 3 (cU8 2)]⟩])
    [.bool true] (u8 1),
  good "flow.cond.else" (fn #[tBool] #[⟨1, tNoret, .condBr (.inst 0) #[ret 2 (cU8 1)] #[ret 3 (cU8 2)]⟩])
    [.bool false] (u8 2),
  good "flow.switch.item" switch [u8 1] (u8 10),
  good "flow.switch.item.second" switch [u8 3] (u8 20),
  good "flow.switch.range.low" switch [u8 5] (u8 30),
  good "flow.switch.range.high" switch [u8 7] (u8 30),
  good "flow.switch.else" switch [u8 4] (u8 40),
  good "flow.switch.else.above" switch [u8 8] (u8 40),
  -- A range of a signed operand is compared signed: `-1` lies in `-2...2`.
  good "flow.switch.range.signed" (fn #[tI8] #[⟨1, tNoret, .switchBr (.inst 0)
    #[⟨#[], #[(.int tI8 (-2), .int tI8 2)], #[ret 2 (cU8 30)]⟩] #[ret 3 (cU8 40)]⟩]) [i8 (-1)] (u8 30),
  good "flow.loop" count [u8 5] (u8 5),
  good "flow.loop.zero" count [u8 0] (u8 0),
  -- A loop left by a `br` of an enclosing block.
  good "flow.loop.break" (fn #[] #[⟨0, tU8, .block #[⟨1, tNoret, .loop #[⟨2, tNoret, .br 0 (cU8 7)⟩]⟩]⟩,
    ret 3 (.inst 0)]) [] (u8 7),
  -- One step per run of the loop body of a function that uses memory, the last one included.
  ⟨"flow.loop.ticks", withBytes fun p => ticks countMem [u8 5, .ptr p], .val (u64 6)⟩,
  ⟨"flow.loop.ticks.pure", ticks count [u8 5], .val (u64 0)⟩,
  -- A recursive function that uses memory pays one step at its entry.
  ⟨"flow.entry.tick", withBytes fun p => ticks recursive [.bool false, .ptr p], .val (u64 1)⟩,
  ⟨"flow.entry.tick.pure", ticks count [u8 0], .val (u64 0)⟩,
  bad "flow.unreachable" (fn #[] #[⟨0, tNoret, .unreach⟩]) [] .unreachable,
  bad "flow.trap" (fn #[] #[⟨0, tNoret, .trap⟩]) [] .panic,
  good "flow.try.payload" tryFn [.errOk (u8 7)] (u8 7),
  good "flow.try.error" tryFn [.errErr "A"] (u8 99),
  good "flow.debug" (fn #[] #[⟨0, tVoid, .line 3⟩, ⟨1, tVoid, .dbg none none⟩, ret 2 (cU8 7)]) [] (u8 7),
  stuckOn "flow.fall.off" (fn #[] #[⟨0, tVoid, .line 3⟩]) [],
  stuckOn "flow.br.unbound" (fn #[] #[⟨0, tNoret, .br 9 (cU8 7)⟩]) []]

def callChecks : List Check := [
  good "call.args" (fn #[tU8, tU8] #[⟨2, tU8, .call (.func "arms.pair" false none) #[.inst 0, .inst 1]⟩,
    ret 3 (.inst 2)]) [u8 3, u8 4] (u8 52),
  bad "call.panic.default" (panicCall "debug.defaultPanic") [] .panic,
  bad "call.panic.overflow" (panicCall (fullPanic "integerOverflow")) [] .overflow,
  bad "call.panic.bounds" (panicCall (fullPanic "outOfBounds")) [] .outOfBounds,
  bad "call.panic.start" (panicCall (fullPanic "startGreaterThanEnd")) [] .outOfBounds,
  bad "call.panic.zero" (panicCall (fullPanic "divideByZero")) [] .divByZero,
  bad "call.panic.unreachable" (panicCall (fullPanic "reachedUnreachable")) [] .unreachable,
  bad "call.panic.null" (panicCall (fullPanic "unwrapNull")) [] .panic,
  stuckOn "call.unknown" (panicCall "arms.none") [],
  stuckOn "call.arg.type" (fn #[tU8] #[ret 1 (.inst 0)]) [.bool true],
  stuckOn "call.arg.signedness" (fn #[tU8] #[ret 1 (.inst 0)]) [i8 1],
  stuckOn "call.arg.count" (fn #[tU8] #[ret 1 (.inst 0)]) [u8 1, u8 2],
  stuckOn "call.arg.error.unknown" (fn #[tEU] #[ret 1 (cU8 0)]) [.errErr "Z"]]

def checks : List Check :=
  arithChecks ++ divChecks ++ bitChecks ++ cmpChecks ++ castChecks ++ optChecks ++ constChecks ++
  memChecks ++ flowChecks ++ callChecks

end SemArms

def main : IO Unit := do
  let mut failed := 0
  for check in SemArms.checks do
    if SemArms.outcome check.run = check.want then IO.println s!"check ok {check.name}"
    else
      failed := failed + 1
      IO.println s!"check FAILED {check.name}"
  IO.println s!"checks: {SemArms.checks.length}, failed: {failed}"
  if failed != 0 then throw (IO.userError s!"{failed} interpreter-arm checks failed")
