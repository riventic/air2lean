import Air2Lean.Air.Op
import Air2Lean.Emit
import Air2Lean.SemView
import Air2Lean.Reify

/-!
# AIR semantics certificates (`--air-certificate`)

For each function in the certificate fragment (`fragmentReason?`), writes a Lean file with

* the complete original canonical program as constructor terms (`Reify.func`), before
  selecting the certificate fragment;
* a theorem that `Air2Lean.Sem.execFunc` of that `Func` equals the generated definition
  (`docs/air-semantics.md`), proved by the kernel when the file is compiled.

The certificate is a separate file: the ordinary translation output does not change. Nothing
here is trusted for soundness except source quotation (the printed term must be the decoded `Func`;
`tests/roadmap/air-semantics` checks the round trip) and the choice of statement.
-/

namespace Air2Lean.Certificate

def bool (b : Bool) : String := if b then "true" else "false"

def int (v : Int) : String := s!"({v} : Int)"

def opt {α : Type} (f : α → String) : Option α → String
  | some a => s!"(some {f a})"
  | none => "none"

def arr {α : Type} (f : α → String) (xs : Array α) : String :=
  "#[" ++ ", ".intercalate (xs.toList.map f) ++ "]"

def str (s : String) : String := s.quote

def printTy : Ty → String
  | .int s b => s!"(.int {bool s} {b})"
  | .float b => s!"(.float {b})"
  | .bool => ".bool"
  | .void => ".void"
  | .noreturn => ".noreturn"
  | .ptr size c child => s!"(.ptr {str size} {bool c} {child})"
  | .array len c s => s!"(.array {len} {c} {bool s})"
  | .vector len c => s!"(.vector {len} {c})"
  | .optional c => s!"(.optional {c})"
  | .errorUnion s p => s!"(.errorUnion {s} {p})"
  | .errorSet names => s!"(.errorSet {opt (arr str) names})"
  | .struct n l fs => s!"(.struct {str n} {str l} {arr (fun (a, b) => s!"({str a}, {b})") fs})"
  | .enum n t e fs => s!"(.enum {str n} {t} {bool e} {arr (fun (a, b) => s!"({str a}, {int b})") fs})"
  | .union n l t fs =>
    s!"(.union {str n} {str l} {opt toString t} {arr (fun (a, b) => s!"({str a}, {b})") fs})"
  | .tuple fs => s!"(.tuple {arr toString fs})"
  | .allocator => ".allocator"
  | .thread => ".thread"
  | .io => ".io"
  | .future r => s!"(.future {r})"
  | .other n => s!"(.other {str n})"

partial def printVal : Val → String
  | .inst id => s!"(.inst {id})"
  | .int t v => s!"(.int {t} {int v})"
  | .float t b => s!"(.float {t} {b})"
  | .bool b => s!"(.bool {bool b})"
  | .void => ".void"
  | .undef t => s!"(.undef {t})"
  | .func n nr sp => s!"(.func {str n} {bool nr} {opt str sp})"
  | .optNull t => s!"(.optNull {t})"
  | .optSome t v => s!"(.optSome {t} {printVal v})"
  | .err t n => s!"(.err {t} {str n})"
  | .errUnionErr t n => s!"(.errUnionErr {t} {str n})"
  | .errUnionOk t v => s!"(.errUnionOk {t} {printVal v})"
  | .enumTag t v => s!"(.enumTag {t} {int v})"
  | .unionVal t i v => s!"(.unionVal {t} {i} {printVal v})"
  | .agg t es => s!"(.agg {t} {arr printVal es})"
  | .ptrConst t g o => s!"(.ptrConst {t} {g} {o})"
  | .ptrNull t => s!"(.ptrNull {t})"
  | .ptrOther t k => s!"(.ptrOther {t} {str k})"
  | .ptrInt t a => s!"(.ptrInt {t} {a})"
  | .sliceConst t p l => s!"(.sliceConst {t} {printVal p} {printVal l})"

def arithOp : ArithOp → String | .add => ".add" | .sub => ".sub" | .mul => ".mul"
def mode : Mode → String
  | .checked => ".checked" | .unchecked => ".unchecked" | .wrap => ".wrap" | .sat => ".sat"
def divOp : DivOp → String
  | .divTrunc => ".divTrunc" | .divFloor => ".divFloor" | .divExact => ".divExact"
  | .rem => ".rem" | .mod => ".mod" | .divCeil => ".divCeil"
def bitOp : BitOp → String | .and => ".and" | .or => ".or" | .xor => ".xor"
def cmpOp : CmpOp → String
  | .lt => ".lt" | .le => ".le" | .eq => ".eq" | .ne => ".ne" | .ge => ".ge" | .gt => ".gt"

mutual

/-- The fragment's instructions as Lean terms; `none` for any other instruction. -/
partial def printOp : Op → Option String
  | .arg i => some s!"(.arg {i})"
  | .arith o m a b => some s!"(.arith {arithOp o} {mode m} {printVal a} {printVal b})"
  | .div o a b => some s!"(.div {divOp o} {printVal a} {printVal b})"
  | .minMax mx a b => some s!"(.minMax {bool mx} {printVal a} {printVal b})"
  | .bit o a b => some s!"(.bit {bitOp o} {printVal a} {printVal b})"
  | .not a => some s!"(.not {printVal a})"
  | .cmp o a b => some s!"(.cmp {cmpOp o} {printVal a} {printVal b})"
  | .boolAnd a b => some s!"(.boolAnd {printVal a} {printVal b})"
  | .boolOr a b => some s!"(.boolOr {printVal a} {printVal b})"
  | .intCast s a => some s!"(.intCast {bool s} {printVal a})"
  | .trunc a => some s!"(.trunc {printVal a})"
  | .alloc => some ".alloc"
  | .load p => some s!"(.load {printVal p})"
  | .fieldPtr b idx => some s!"(.fieldPtr {printVal b} {idx})"
  | .bitcast s a => some s!"(.bitcast {bool s} {printVal a})"
  | .store p v => some s!"(.store {printVal p} {printVal v})"
  | .ptrAdd sub p n => some s!"(.ptrAdd {bool sub} {printVal p} {printVal n})"
  | .elemPtr p i => some s!"(.elemPtr {printVal p} {printVal i})"
  | .ptrElemVal p i => some s!"(.ptrElemVal {printVal p} {printVal i})"
  | .sliceElemVal sl i => some s!"(.sliceElemVal {printVal sl} {printVal i})"
  | .sliceLen sl => some s!"(.sliceLen {printVal sl})"
  | .slicePtr sl => some s!"(.slicePtr {printVal sl})"
  | .call c args => some s!"(.call {printVal c} {arr printVal args})"
  | .isNonNull a => some s!"(.isNonNull {printVal a})"
  | .isNull a => some s!"(.isNull {printVal a})"
  | .optPayload a => some s!"(.optPayload {printVal a})"
  | .wrapOptional a => some s!"(.wrapOptional {printVal a})"
  | .isErr a => some s!"(.isErr {printVal a})"
  | .isNonErr a => some s!"(.isNonErr {printVal a})"
  | .errPayload a => some s!"(.errPayload {printVal a})"
  | .errCode a => some s!"(.errCode {printVal a})"
  | .wrapErrPayload a => some s!"(.wrapErrPayload {printVal a})"
  | .wrapErr a => some s!"(.wrapErr {printVal a})"
  | .«try» v b => return s!"(.try {printVal v} {← printBody b})"
  | .block b => return s!"(.block {← printBody b})"
  | .loop b => return s!"(.loop {← printBody b})"
  | .br t v => some s!"(.br {t} {printVal v})"
  | .«repeat» t => some s!"(.repeat {t})"
  | .condBr c t e => return s!"(.condBr {printVal c} {← printBody t} {← printBody e})"
  | .switchBr v cs e => do
    let cases ← cs.mapM fun c => do
      let ranges := arr (fun (lo, hi) => s!"({printVal lo}, {printVal hi})") c.ranges
      pure s!"\{ items := {arr printVal c.items}, ranges := {ranges}, body := {← printBody c.body} }"
    return s!"(.switchBr {printVal v} {arr id cases} {← printBody e})"
  | .ret v => some s!"(.ret {printVal v})"
  | .unreach => some ".unreach"
  | .trap => some ".trap"
  | .line n => some s!"(.line {n})"
  | .dbg n v => some s!"(.dbg {opt str n} {opt printVal v})"
  | _ => none

partial def printBody (body : Array Inst) : Option String := do
  let insts ← body.mapM fun i => do pure s!"⟨{i.id}, {i.ty}, {← printOp i.op}⟩"
  pure ("#[" ++ ",\n    ".intercalate insts.toList ++ "]")

end

def printLayout (l : Layout) : String :=
  s!"\{ size := {opt toString l.size}, align := {opt toString l.align}, " ++
  s!"offsets := {arr toString l.offsets}, ptrAlign := {opt toString l.ptrAlign}, " ++
  s!"sentinel := {bool l.sentinel}, sentinelByte := {opt toString l.sentinelByte}, " ++
  s!"isVolatile := {bool l.isVolatile}, allowzero := {bool l.allowzero}, " ++
  s!"hostSize := {l.hostSize}, bitOffset := {l.bitOffset}, packedLanes := {bool l.packedLanes}, " ++
  s!"vectorIndex := {opt toString l.vectorIndex}, runtimeLane := {bool l.runtimeLane}, " ++
  s!"vectorIndexExported := {bool l.vectorIndexExported} }"

def printGlobal (g : Global) : String :=
  s!"\{ name := {opt str g.name}, ty := {g.ty}, isConst := {bool g.isConst}, " ++
  s!"threadlocal := {bool g.threadlocal}, isExtern := {bool g.isExtern}, init := {opt printVal g.init} }"

/-- Every field of the dialect, its enumerations by their full constructor names. -/
def printDialect (d : Dialect) : String :=
  s!"\{ version := {repr d.version}, arch := {str d.arch}, os := {str d.os}, ptrBytes := {d.ptrBytes}, " ++
  s!"endian := {repr d.endian}, errorSetBits := {d.errorSetBits}, backend := {str d.backend}, " ++
  s!"buildMode := {str d.buildMode}, noLibc := {bool d.noLibc} }"

/-- Constructor quotation of the whole decoded `Func`, including every source field and
operations outside the proof fragment. `none` denotes an unexpected quotation expression,
never an unsupported body replaced by `default`. -/
def printFunc (f : Func) : Option String := (Reify.func f).toOption


/-! ## The certificate fragment -/

/-- A parameter or return type of the fragment: its Lean type, its value encoding, and how
the oracle decodes argument `i`. -/
structure Scalar where
  lean : String
  /-- The `Sem.Value` of a Lean term of this type. -/
  enc : String → String
  dec : Nat → String
  /-- `valOk` inversion lemma, and the decoded argument of `v<i>`. -/
  inv : String
  decVar : Nat → String
  /-- `enc` ignores its argument (`void`): a lambda over the value binds `_`. -/
  ignoresValue : Bool := false
  /-- The decoding of a `Sem.Value` term (`Value.toBV`, …). -/
  decT : String → String := fun _ => "()"

/-- The binder of a lambda over a value of this type. -/
def Scalar.binder (sc : Scalar) : String := if sc.ignoresValue then "_" else "v"

/-- A plain slice of a 64-bit target: `Zig.Slice` (a 32-bit target's is `Zig.Slice32`, and
`Sem` reads a slice's length and indices as 64-bit). -/
def slice64 (f : Func) (t : TyId) : Bool := f.plainSlice t && ptrBytesOf f.layouts == 8

def scalar? (f : Func) (t : TyId) : Option Scalar :=
  match f.types[t]? with
  | some (.int s w) => some {
      lean := s!"BitVec {w}", enc := fun v => s!"(Value.int {bool s} {w} {v})",
      dec := fun i => s!"((args.getD {i} .void).toBV {w})",
      inv := "valOk_int", decVar := fun i => s!"(v{i}.toBV {w})",
      decT := fun t => s!"(Value.toBV {w} {t})" }
  | some .bool => some {
      lean := "Bool", enc := fun v => s!"(Value.bool {v})",
      dec := fun i => s!"((args.getD {i} .void).toBool)",
      inv := "valOk_bool", decVar := fun i => s!"v{i}.toBool",
      decT := fun t => s!"(Value.toBool {t})" }
  | some (.ptr ..) =>
    if f.plainPtr t then some {
      lean := "Zig.Ptr", enc := fun v => s!"(Value.ptr {v})",
      dec := fun i => s!"((args.getD {i} .void).toPtr)",
      inv := "valOk_ptr (hs := by decide)", decVar := fun i => s!"v{i}.toPtr",
      decT := fun t => s!"(Value.toPtr {t})" }
    -- A slice of a function in `Zig.MemM` (a pure function's `[]const T` is an `Array`;
    -- `localReason` excludes it).
    else if slice64 f t then some {
      lean := "Zig.Slice", enc := fun v => s!"(Value.slice {v})",
      dec := fun i => s!"((args.getD {i} .void).toSlice)",
      inv := "valOk_slice", decVar := fun i => s!"v{i}.toSlice",
      decT := fun t => s!"(Value.toSlice {t})" }
    else none
  | _ => none

def retScalar? (f : Func) (t : TyId) : Option Scalar :=
  -- The payload of an optional or error union: an integer or `bool` (`void` for `E!void`).
  let payload (c : TyId) : Option (String × String) :=
    match f.types[c]? with
    | some .void => some ("Unit", "(fun _ => Value.void)")
    | some (.ptr ..) => none
    | _ => (scalar? f c).map fun sc => (sc.lean, s!"(fun x => {sc.enc "x"})")
  -- A return value is never decoded (no `inv`): `dec` is a placeholder of the type.
  let wrap (ty enc dflt : String) (c : TyId) : Option Scalar := (payload c).map fun (lean, g) =>
    { lean := s!"{ty} ({lean})", enc := fun v => s!"({enc} {g} {v})", dec := fun _ => dflt, inv := "",
      decVar := fun _ => dflt }
  match f.types[t]? with
  | some .void => some {
      lean := "Unit", enc := fun _ => "Value.void", dec := fun _ => "()",
      inv := "valOk_void", decVar := fun _ => "()", ignoresValue := true }
  | some (.optional c) => wrap "Option" "Value.ofOpt" "none" c
  | some (.errorUnion _ c) => wrap "Except Zig.ErrName" "Value.ofExcept" "(.error \"\")" c
  | _ => scalar? f t

/-- A safety-panic handler of `Sem.panicOf?`'s literal table (not a generic instance). -/
def panicCallee? (name : String) : Option String :=
  if (name.splitOn "__anon_").length > 1 then none
  else match panicErrorFor? name with
    | some ".overflow" => some ".overflow"
    | some ".outOfBounds" => some ".outOfBounds"
    | some ".divByZero" => some ".divByZero"
    | some ".unreachable" => some ".unreachable"
    | some ".panic" => some ".panic"
    | _ => none

def isIntTy (f : Func) (t : TyId) : Bool :=
  match f.types[t]? with | some (.int ..) => true | _ => false

/-- A value type that memory holds in the fragment: an integer, `bool` or plain pointer. Not a
slice: `Sem.loadAs`/`storeAs` are stuck on one; only a register local's cell holds it. -/
def memValTy (f : Func) (t : TyId) : Bool := (scalar? f t).isSome && !f.plainSlice t

/-- A `[]const T` parameter of a function without memory, which the translator passes as an
`Array` that the caller read (`Zig.readSlice`): its index, its `arg` instruction, the item type
and its scalar (an integer or `bool`), the slice type's alignment and the caller's read alignment
(`FCtx.itemAlign`). The certificate runs the function with the items as a view (`Sem.execFuncV`,
docs/air-semantics.md §Pure-function slices). -/
structure ViewParam where
  idx : Nat
  arg : InstId
  sliceTy : TyId
  item : TyId
  sc : Scalar
  ptrAlign : Nat
  align : Nat

/-- The view parameters of `f`, or why a slice parameter cannot be one. -/
def viewParams (f : Func) : Except String (Array ViewParam) := do
  let mut out := #[]
  for (p, idx) in f.params.zipIdx do
    unless f.plainSlice p do continue
    unless slice64 f p do throw "a slice parameter of a 32-bit target"
    let some item := Sem.pointee? f p | throw "a slice parameter without an item type"
    let some sc := scalar? f item | throw "a slice parameter whose items are not integers or `bool`"
    unless memValTy f item && !(f.types[item]? matches some (.ptr ..)) do
      throw "a slice parameter whose items are not integers or `bool`"
    let some arg := f.body.find? (fun i => match i.op with | .arg j => j == idx | _ => false)
      | throw "a slice parameter without its `arg`"
    let some pa := Sem.ptrAlignOf f p | throw "a slice parameter without an alignment"
    let some (_, ia) := Sem.layoutOf f item | throw "a slice item without a layout"
    out := out.push { idx, arg := arg.id, sliceTy := p, item, sc, ptrAlign := pa, align := Nat.min pa ia }
  pure out

/-- An operand the certificate fragment reads: an instruction, an integer, `bool` or `void`, or an
optional or error-union constant of one (`Sem.constVal`). -/
def simpleVal (f : Func) : Val → Bool
  | .inst _ | .bool _ | .void => true
  | .err t n => Sem.errIn f t n
  | .errUnionErr t n => Sem.errUnionIn f t n
  | .int t _ => isIntTy f t
  | .optNull t => Sem.plainOpt f t
  | .optSome t v => Sem.plainOpt f t && (Sem.constVal f v).run.isSome
  | .errUnionOk t v => Sem.isErrorUnion f t && (Sem.constVal f v).run.isSome
  | _ => false

partial def allInsts (body : Array Inst) : Array Inst :=
  body.flatMap fun i => #[i] ++ match i.op with
    | .block b | .loop b => allInsts b
    | .condBr _ t e => allInsts t ++ allInsts e
    | .«try» _ b => allInsts b
    | .switchBr _ cs e => allInsts e ++ cs.flatMap (allInsts ·.body)
    | _ => #[]

/-- Why one instruction is outside the certificate fragment (nested bodies are checked by
`localReason`, which visits every instruction). -/
def instReason (f : Func) (tyOfInst : InstId → Option TyId) (regs : Array InstId) (i : Inst) :
    Except String Unit := do
  let vals (vs : List Val) : Except String Unit :=
    unless vs.all (simpleVal f) do throw s!"inst {i.id}: an operand outside the fragment"
  let intRes : Except String Unit :=
    unless isIntTy f i.ty do throw s!"inst {i.id}: a non-integer result"
  -- An operand whose type satisfies `ok`: an instruction, an integer or a `bool` constant.
  let typed (ok : TyId → Bool) : Val → Bool
    | .inst x => (tyOfInst x).any ok
    | .int t _ => ok t
    | .bool _ => true
    | _ => false
  -- A pointer operand: an instruction of a plain pointer type.
  let ptrOf (v : Val) : Option TyId := match v with
    | .inst x => (tyOfInst x).filter f.plainPtr
    | _ => none
  let ptrVal (v : Val) : Except String TyId := do
    let some t := ptrOf v | throw s!"inst {i.id}: an access through a pointer outside the fragment"
    pure t
  -- A slice operand: an instruction of a plain slice type.
  let sliceOf (v : Val) : Option TyId := match v with
    | .inst x => (tyOfInst x).filter (slice64 f)
    | _ => none
  let sliceVal (v : Val) : Except String Unit := do
    unless (sliceOf v).isSome do throw s!"inst {i.id}: a slice outside the fragment"
  -- 64-bit pointers: the translator's `Ptr.elem` (other widths use `Ptr.elemOf`).
  let ptr64 (_ : TyId) : Bool := ptrBytesOf f.layouts == 8
  -- A register local's cell holds any value of `scalar?`; memory only a `memValTy`.
  let isReg : Val → Bool
    | .inst x => regs.contains x
    | _ => false
  let cellTy (p : Val) (t : TyId) : Bool := memValTy f t || (isReg p && (scalar? f t).isSome)
  match i.op with
  | .arg _ | .line _ | .dbg .. | .unreach | .trap | .block _ => pure ()
  | .arith _ _ a b | .div _ a b | .minMax _ a b | .bit _ a b => do intRes; vals [a, b]
  | .cmp _ a b => do
    unless (!(a matches .bool _) && typed (isIntTy f) a) || ((ptrOf a).isSome && (ptrOf b).isSome) do
      throw s!"inst {i.id}: a comparison of non-integers"
    vals [a, b]
  | .load p => do
    let _ ← ptrVal p
    unless cellTy p i.ty do throw s!"inst {i.id}: a load of a type outside the fragment"
  | .store p v => do
    let _ ← ptrVal p
    vals [v]
    unless typed (cellTy p) v do throw s!"inst {i.id}: a store of a type outside the fragment"
  | .fieldPtr b idx => do
    let t ← ptrVal b
    unless f.plainPtr i.ty && (f.fieldOffset? t idx).isSome do
      throw s!"inst {i.id}: a field pointer outside the fragment"
  | .bitcast _ a => do
    -- A pointer `bitcast`, or `@bitCast` between integers of one width (`Sem.evalPure`).
    let width (t : TyId) : Option Nat := match f.types[t]? with | some (.int _ w) => some w | _ => none
    let intCast := match a with
      | .inst x => ((tyOfInst x).bind width).isSome && (tyOfInst x).bind width == width i.ty
      | _ => false
    unless intCast do
      let _ ← ptrVal a
      unless f.plainPtr i.ty do throw s!"inst {i.id}: a bitcast outside the fragment"
  | .ptrAdd _ p n | .elemPtr p n => do
    -- `slice_elem_ptr`: both sides check the index against the length (`Zig.checkIndex`).
    if (sliceOf p).isNone || i.op matches .ptrAdd .. then
      let _ ← ptrVal p
    vals [n]
    unless typed (isIntTy f) n && f.plainPtr i.ty && ptr64 i.ty do
      throw s!"inst {i.id}: pointer arithmetic outside the fragment"
  | .ptrElemVal p n => do
    let t ← ptrVal p
    vals [n]
    unless typed (isIntTy f) n && memValTy f i.ty && ptr64 t do throw s!"inst {i.id}: an item load outside the fragment"
  | .sliceElemVal sl n => do
    let _ ← sliceVal sl
    vals [n]
    unless typed (isIntTy f) n && memValTy f i.ty do throw s!"inst {i.id}: an item load outside the fragment"
  | .sliceLen sl => do
    let _ ← sliceVal sl
  | .slicePtr sl => do
    let _ ← sliceVal sl
    unless f.plainPtr i.ty do throw s!"inst {i.id}: a slice pointer outside the fragment"
  | .slice .. => throw s!"inst {i.id}: a slicing (the translator checks its bounds, which no AIR operation does)"
  -- Optionals (not pointer optionals) and error unions as values (`Sem.Value.optSome`, `errOk`, …).
  | .isNonNull a | .isNull a | .optPayload a => do
    vals [a]
    unless typed (Sem.plainOpt f) a do throw s!"inst {i.id}: an optional outside the fragment"
  | .wrapOptional a => do
    vals [a]
    unless Sem.plainOpt f i.ty do throw s!"inst {i.id}: an optional outside the fragment"
  | .isErr a | .isNonErr a | .errPayload a | .errCode a | .«try» a _ => do
    vals [a]
    unless typed (Sem.isErrorUnion f) a do throw s!"inst {i.id}: an error union outside the fragment"
  | .wrapErrPayload a | .wrapErr a => do
    vals [a]
    unless Sem.isErrorUnion f i.ty do throw s!"inst {i.id}: an error union outside the fragment"
  | .boolAnd a b | .boolOr a b => vals [a, b]
  | .not a => vals [a]
  | .intCast _ a | .trunc a => do intRes; vals [a]
  | .br _ v | .ret v => vals [v]
  | .call (.func _ _ none) args => vals args.toList
  | .call .. => throw s!"inst {i.id}: an indirect or spawn call"
  | .condBr c _ _ => vals [c]
  | .switchBr v cs _ => do
    match v with
    | .inst x =>
      unless (tyOfInst x).any (isIntTy f) do throw s!"inst {i.id}: a switch on a non-integer"
    | _ => throw s!"inst {i.id}: a switch on a constant"
    for c in cs do
      vals (c.items.toList ++ c.ranges.toList.flatMap fun (a, b) => [a, b])
      if c.items.isEmpty && c.ranges.isEmpty then throw s!"inst {i.id}: an empty switch case"
  | .loop _ | .«repeat» _ | .alloc => pure ()  -- checked with the function's shape (`localsReason`)
  | _ => throw s!"inst {i.id}: an instruction outside the fragment"

/-- The registers (`Sem.regAlloc`) of `f`, by id. -/
def registers (f : Func) : Array InstId :=
  ((allInsts f.body).filterMap fun i => if (i.op matches .alloc) && Sem.regAlloc f i.id then some i.id else none)
    |>.qsort (· < ·)

def callsIn (f : Func) : Array String :=
  (allInsts f.body).filterMap fun i => match i.op with
    | .call (.func n _ _) _ => some n
    | _ => none

/-- The local reason a function is outside the fragment, or its non-panic callees. -/
def localReason (f : Func) (mem : Bool) : Except String (Array String) := do
  for p in f.params do
    unless (scalar? f p).isSome do throw "a parameter that is not an integer, bool, plain pointer or slice"
  if !mem then
    let views ← viewParams f
    unless views.isEmpty do
      -- The view runs only where the function reads memory through its viewed slices (`roBody`).
      let keys := views.map (·.arg)
      let V : InstId → Option (Array Sem.Value) := fun k => if keys.contains k then some #[] else none
      let VT : InstId → TyId := fun k => ((views.find? (·.arg == k)).map (·.item)).getD 0
      unless Sem.roBody f V VT f.body.toList do
        -- The first instruction that `roInst` rejects names the cause.
        let bad := (allInsts f.body).find? (!Sem.roInst f V VT ·)
        throw <| match bad.map (·.op) with
          | some (.call ..) => "a function with a slice parameter that calls a function (a view function calls only panic handlers, `Sem.roBody`)"
          | some .alloc => "a function with a slice parameter and a local whose address is taken (`Sem.roBody`)"
          | _ => "a function with a slice parameter that reads memory other than through its items (`Sem.roBody`)"
  unless (retScalar? f f.ret).isSome do
    throw "a return type that is not an integer, bool, plain pointer or void, or an optional or error union of one"
  let insts := allInsts f.body
  let tys : Std.HashMap InstId TyId := insts.foldl (fun m i => m.insert i.id i.ty) {}
  let tyOfInst (x : InstId) := tys[x]?
  let regs := registers f
  for i in insts do instReason f tyOfInst regs i
  unless (printFunc f).isSome do throw "an instruction the certificate printer does not print"
  pure ((callsIn f).filter fun n => (panicCallee? n).isNone)

/-! ## Locals and loops -/

/-- The operands of an instruction (not its nested bodies or debug information): the classifier's
value and place operands (`Op.effects`), which covers every constructor. -/
def opVals (op : Op) : List Val := (op.effects.values ++ op.effects.places).toList

def instIdsOf (vs : List Val) : List InstId := vs.filterMap fun | .inst k => some k | _ => none

/-- Every loop with its enclosing blocks and loops, outer loops first. -/
partial def loopCtx (bs ls : List InstId) (body : Array Inst) :
    Array (Inst × Array Inst × List InstId × List InstId) :=
  body.flatMap fun i => match i.op with
    | .block b => loopCtx (i.id :: bs) ls b
    | .loop b => #[(i, b, bs, ls)] ++ loopCtx bs (i.id :: ls) b
    | .condBr _ t e => loopCtx bs ls t ++ loopCtx bs ls e
    | .switchBr _ cs e => cs.flatMap (loopCtx bs ls ·.body) ++ loopCtx bs ls e
    | .«try» _ b => loopCtx bs ls b
    | _ => #[]

/-- The registers a body reads or writes. -/
def cellsIn (regs : Array InstId) (body : Array Inst) : Array InstId :=
  ((allInsts body).toList.flatMap fun i => instIdsOf (opVals i.op)).eraseDups.filter regs.contains |>.toArray
    |>.qsort (· < ·)

/-- Why `f`'s locals or loops are outside the certificate fragment. `sh`: its emitted shape. -/
def localsReason (f : Func) (sh : CertShape) : Except String Unit := do
  let insts := allInsts f.body
  let tys : Std.HashMap InstId TyId := insts.foldl (fun m i => m.insert i.id i.ty) {}
  let allocs := insts.filterMap fun i => if i.op matches .alloc then some i.id else none
  let hasLoop := insts.any (·.op matches .loop _)
  if allocs.isEmpty && !hasLoop then return
  if sh.other then throw "a dispatch loop or a raw return"
  unless sh.byteLocals.isEmpty do throw "a byte local (`Zig.Bytes`)"
  unless Sem.wfBody [] [] f.body.toList do throw "a `br` or `repeat` that leaves no enclosing block or loop"
  let regs := registers f
  for a in allocs do
    if regs.contains a == sh.escaping.contains a then
      throw s!"inst {a}: a local that the translator and the semantics place differently"
  let top := f.body
  let escTop := top.filterMap fun i => if sh.escaping.contains i.id then some i.id else none
  unless escTop == sh.escaping do
    throw "an escaping local inside a nested body or out of the translator's order"
  -- The translator allocates every escaping local at entry: nothing before the last one may
  -- touch memory.
  if let some j := escTop.back? >>= fun e => top.findIdx? (·.id == e) then
    unless (top.extract 0 j).all (fun i => i.op matches .arg _ | .line _ | .dbg .. | .alloc) do
      throw "an escaping local allocated after an instruction with effects"
  -- The first top-level instruction that contains a loop.
  let firstLoop := top.findIdx? fun i => (allInsts #[i]).any (·.op matches .loop _)
  -- A register starts undefined; the translator's field starts at its default.
  for a in regs do
    let some j := top.findIdx? (·.id == a) | throw s!"inst {a}: a register local inside a nested body"
    let next := (top.extract (j + 1) top.size).find? fun i => !(i.op matches .line _ | .dbg ..)
    match (next.map (·.op) : Option Op) with
    | some (.store (.inst b) v) =>
      unless b == a && !(v matches .undef _) do throw s!"inst {a}: a register local read before it is set"
    | _ => throw s!"inst {a}: a register local read before it is set"
    unless ((tys[a]?).bind (Sem.pointee? f) |>.bind (scalar? f)).isSome do
      throw s!"inst {a}: a register local of a type outside the fragment"
    -- The loop lemmas map every register into the frame: it must be set before any loop.
    if firstLoop.any (· < j) then
      throw s!"inst {a}: a register local allocated after a loop"
  for (k, t) in sh.blockTys do
    if sh.brT.contains k && !(f.types[t]? matches some .void) && (scalar? f t).isNone then
      throw s!"inst {k}: a block value outside the fragment"
  -- An inner loop's generated state keeps the escaping locals' fields of the outer state, which
  -- the semantics' frame does not name.
  if !sh.escaping.isEmpty && (loopCtx [] [] f.body).any (fun (_, _, _, ls) => !ls.isEmpty) then
    throw "a nested loop in a function with escaping locals"
  for (l, caps) in sh.loops do
    let some li := insts.find? (·.id == l) | throw s!"inst {l}: a loop the translator does not name"
    let body := match li.op with | .loop b => b | _ => #[]
    let defined := (allInsts body).map (·.id)
    let free := ((allInsts body).toList.flatMap fun i => instIdsOf (opVals i.op)).eraseDups.filter (!defined.contains ·)
    for k in free do
      unless caps.any (·.1 == k) || regs.contains k do throw s!"inst {l}: a loop reads a value it does not capture"
    for (k, _) in caps do
      unless (tys[k]?.bind (scalar? f)).isSome do throw s!"inst {l}: a loop capture outside the fragment"

/-- A function without memory with a slice parameter: certified through a view of its items. -/
def isView (f : Func) (memFuncs : Array String) : Bool :=
  !memFuncs.contains f.name && f.params.any f.plainSlice

/-- Split the functions into the certificate fragment (closed under direct calls) and the
others, each with a reason. -/
def fragment (program : Program)
    (shapes : Array (String × CertShape)) : Array Func × Array (String × String) := Id.run do
  let funcs := program.funcs
  let memFuncs := program.memFuncs
  let concFuncs := program.concFuncs
  let mut out : Array (String × String) := #[]
  let mut cands : Array (Func × Array String) := #[]
  -- A recursive function in `Zig.MemM` charges its frame to the model's stack budget
  -- (`Zig.enterFrame`, STK-01), which the semantics does not have.
  let budgeted := if memFuncs.isEmpty then #[] else program.groups.flatMap fun (members, recursive) =>
    if recursive then (members.map (·.name)).filter memFuncs.contains else #[]
  for f in funcs do
    let reason : Except String (Array String) :=
      if concFuncs.contains f.name then .error "a concurrent function (`Zig.ConcM`)"
      else if budgeted.contains f.name then
        .error "a recursive function that uses memory (stack budget `Zig.enterFrame`, STK-01)"
      else match shapes.find? (·.1 == f.name) with
        -- Fail closed: without the emitter's shape, its locals and loops are unknown.
        | none => .error "no emitted certificate shape (`Emit.CertShape`)"
        | some (_, sh) =>
          localReason f (memFuncs.contains f.name) >>= fun cs => do
            localsReason f sh
            pure cs
    match reason with
    | .ok cs => cands := cands.push (f, cs)
    | .error e => out := out.push (f.name, e)
  -- A function with a viewed slice is certified at the call boundary only (no fixpoint equation,
  -- `execFunc_view`): its callers are outside until a caller's step relates the two.
  let views := (cands.filter fun (f, _) => isView f memFuncs).map (·.1.name)
  let mut changed := true
  while changed do
    changed := false
    let names := cands.map (·.1.name)
    let (keep, drop) := cands.partition fun (_, cs) => cs.all fun c => names.contains c && !views.contains c
    if !drop.isEmpty then
      changed := true
      for (f, cs) in drop do
        match cs.find? views.contains with
        | some v =>
          out := out.push (f.name, s!"calls `{v}`, whose slice parameter is certified at the call boundary only")
        | none =>
          let missing := ((cs.filter (!names.contains ·))[0]?).getD ""
          out := out.push (f.name, s!"calls `{missing}`, which is outside the fragment")
      cands := keep
  pure (cands.map (·.1), out)

/-! ## Emission -/

/-- Ordinary compiler facts, not a proof interface. Indices refer to the actual imported
induction theorem's telescope; names are retained for named application in the existing
certificate producer. The emitted certificate is still checked by Lean's kernel. -/
private structure CompiledBinder where
  index : Nat
  name : String
  binder : String

private structure CompiledApprox extends CompiledBinder where
  member : String

private structure CompiledIH extends CompiledApprox where
  approxIndex : Nat

private structure CompiledStep extends CompiledBinder where
  approxs : Array CompiledApprox
  ihs : Array CompiledIH

private structure CompiledMotive where
  member : String
  motive : CompiledBinder
  adm : CompiledBinder
  step : CompiledStep

private structure CompiledFixed extends CompiledBinder where
  groupIndex : Nat

private structure CompiledInduction where
  name : String
  target : String
  fixed : Array CompiledFixed
  members : Array CompiledMotive

private structure CompiledMember where
  name : String
  params : Array (String × String)
  fixed : Array (Option Nat)

private structure CompiledGroup where
  members : Array CompiledMember
  numFixed : Nat
  inductions : Array CompiledInduction

private def compiledName (ns : String) (decl : EmittedDecl) : String :=
  (((s!"{ns}.{decl.name}").splitOn ".").foldl
    (fun name part => Lean.Name.str name (plainName part)) Lean.Name.anonymous).toString

private def compiledBinder (j : Lean.Json) : Except String CompiledBinder := do
  let index ← j.getObjValAs? Nat "index"
  let name ← j.getObjValAs? String "name"
  let binder ← j.getObjValAs? String "binder"
  unless !name.isEmpty && #["default", "implicit", "strict_implicit", "inst_implicit"].contains binder do
    throw "invalid compiler binder name/kind"
  pure { index, name, binder }

private def compiledStep (j : Lean.Json) : Except String CompiledStep := do
  let b ← compiledBinder j
  let approxs ← (← j.getObjValAs? (Array Lean.Json) "approxs").mapM fun a => do
    let binder ← compiledBinder a
    let member ← a.getObjValAs? String "member"
    pure ({ toCompiledBinder := binder, member } : CompiledApprox)
  let ihs ← (← j.getObjValAs? (Array Lean.Json) "ihs").mapM fun h => do
    let binder ← compiledBinder h
    let member ← h.getObjValAs? String "member"
    let approxIndex ← h.getObjValAs? Nat "approx_index"
    let approx : CompiledApprox := { toCompiledBinder := binder, member }
    pure ({ toCompiledApprox := approx, approxIndex } : CompiledIH)
  let indices := approxs.map (·.index) ++ ihs.map (·.index)
  unless indices.toList == (List.range indices.size) do
    throw "compiler step binders are missing, duplicated or out of order"
  unless approxs.size == ihs.size &&
      (approxs.map (·.member)).toList.eraseDups.length == approxs.size &&
      (ihs.map (·.member)).toList.eraseDups.length == ihs.size do
    throw "compiler step has duplicate or unmatched retained members"
  for h in ihs do
    unless approxs.any (fun a => a.member == h.member && a.index == h.approxIndex) do
      throw "compiler induction hypothesis does not match its approximation"
  pure { toCompiledBinder := b, approxs, ihs }

private def compiledGroups (metadata : Lean.Json) : Except String (Array CompiledGroup) := do
  (← metadata.getObjValAs? (Array Lean.Json) "fixpoint_groups").mapM fun group => do
    let numFixed ← group.getObjValAs? Nat "num_fixed"
    let members ← (← group.getObjValAs? (Array Lean.Json) "members").mapM fun member => do
      let name ← member.getObjValAs? String "name"
      let params ← (← member.getObjValAs? (Array Lean.Json) "params").mapM fun p => do
        pure (← p.getObjValAs? String "name", ← p.getObjValAs? String "binder")
      let fixed ← member.getObjValAs? (Array (Option Nat)) "fixed"
      unless params.size == fixed.size && fixed.countP Option.isSome == numFixed do
        throw s!"compiler permutation has the wrong arity for {name}"
      for k in [:numFixed] do
        unless fixed.countP (· == some k) == 1 do
          throw s!"compiler permutation is not a bijection for {name}"
      unless fixed.all (fun k => k.all (· < numFixed)) do
        throw s!"compiler permutation has an out-of-range fixed index for {name}"
      pure { name, params, fixed : CompiledMember }
    let names := members.map (·.name)
    unless !members.isEmpty && names.toList.eraseDups.length == names.size do
      throw "compiler fixpoint group is empty or has duplicate members"
    let inductions ← (← group.getObjValAs? (Array Lean.Json) "inductions").mapM fun induction => do
      let name ← induction.getObjValAs? String "name"
      let target ← induction.getObjValAs? String "target"
      unless names.contains target do throw "compiler induction targets another group"
      let fixed ← (← induction.getObjValAs? (Array Lean.Json) "fixed").mapM fun f => do
        let binder ← compiledBinder f
        let groupIndex ← f.getObjValAs? Nat "group_index"
        pure ({ toCompiledBinder := binder, groupIndex } : CompiledFixed)
      unless (fixed.map (·.groupIndex)).toList == List.range numFixed do
        throw "compiler induction is missing or duplicates a fixed parameter"
      let roles ← (← induction.getObjValAs? (Array Lean.Json) "members").mapM fun m => do
        let member ← m.getObjValAs? String "name"
        let motive ← compiledBinder (← m.getObjVal? "motive")
        let adm ← compiledBinder (← m.getObjVal? "adm")
        let step ← compiledStep (← m.getObjVal? "step")
        pure ({ member, motive, adm, step } : CompiledMotive)
      unless roles.map (·.member) == names do throw "compiler motive membership/order disagrees with EqnInfo"
      let indices := fixed.map (·.index) ++ roles.flatMap (fun m => #[m.motive.index, m.adm.index, m.step.index])
      unless indices.toList.eraseDups.length == indices.size &&
          indices.all (· < indices.size) do
        throw "compiler induction outer binders are missing or duplicated"
      for role in roles do
        unless role.step.approxs.all (fun a => names.contains a.member) &&
            role.step.ihs.all (fun h => names.contains h.member) do
          throw "compiler step retains a member outside its group"
      pure { name, target, fixed, members := roles : CompiledInduction }
    unless (inductions.map (·.target)).toList.eraseDups.length == names.size &&
        inductions.size == names.size do
      throw "compiler group is missing or duplicates an induction theorem"
    pure { members, numFixed, inductions : CompiledGroup }

private def compiledGroupFor (groups : Array CompiledGroup) (ns : String)
    (group : DeclGroup) : Except String CompiledGroup := do
  let fullName := compiledName ns
  let expected := group.members.map fullName
  let candidates := groups.filter fun compiled => compiled.members.any (fun m => expected.contains m.name)
  unless candidates.size == 1 do throw "missing or ambiguous compiler fixpoint group for emitted declarations"
  let some compiled := candidates[0]?
    | throw "missing compiler fixpoint group for emitted declarations"
  unless compiled.members.size == expected.size && compiled.members.all (fun m => expected.contains m.name) do
    throw "compiler fixpoint members disagree with the actual emitted declaration group"
  for decl in group.members do
    let some member := compiled.members.find? (·.name == fullName decl)
      | throw "missing actual emitted declaration in compiler metadata"
    for (name, _) in decl.params do
      unless member.params.countP (fun (actual, binder) => actual == name && binder == "default") == 1 do
        throw s!"compiler parameters do not identify emitted parameter {fullName decl}.{name}"
  pure compiled

/-- One certified function's signature pieces. -/
structure Sig where
  ret : Scalar
  ps : Array (Nat × Scalar)
  binders : String
  encArgs : String
  argNames : String

def sig (f : Func) : Sig :=
  let blank : Scalar := { lean := "", enc := fun _ => "", dec := fun _ => "", inv := "", decVar := fun _ => "" }
  let ret := (retScalar? f f.ret).getD blank
  let ps := f.params.mapIdx fun i p => (i, (scalar? f p).getD ret)
  { ret, ps,
    binders := " ".intercalate (ps.toList.map fun (i, s) => s!"(p{i} : {s.lean})"),
    encArgs := ", ".intercalate (ps.toList.map fun (i, s) => s.enc s!"p{i}"),
    argNames := " ".intercalate (ps.toList.map fun (i, _) => s!"p{i}") }

/-- Tactic lines that turn a hypothesis `h : argsOk air f.params args` into concrete
`args = [enc v0, …]` (`argsOk_cons`/`valOk_*`), leaving the decoded `v<i>`. -/
def invertArgs (f : Func) (air : String) (indent : String) : Array String := Id.run do
  let paramList := "[" ++ ", ".intercalate (f.params.toList.map toString) ++ "]"
  let mut out := #[s!"{indent}replace h : argsOk {air} {paramList} args = true := h"]
  for (_, i) in f.params.zipIdx do
    out := out.push s!"{indent}obtain ⟨v{i}, args, rfl, h{i}, h⟩ := argsOk_cons h"
  out := out.push s!"{indent}obtain rfl := argsOk_nil h"
  for (p, i) in f.params.zipIdx do
    let inv := ((scalar? f p).map (·.inv)).getD "valOk_int"
    out := out ++ #[s!"{indent}replace h{i} : valOk {printTy (f.types[p]!)} v{i} = true := h{i}",
      s!"{indent}rw [{inv} h{i}]"]
  out

/-- How the certificate runs a function: in `Zig.MemM` (the generated code runs over the same
memory) or without memory (`Zig.M`), possibly with views of its slice parameters (`ViewParam`). -/
structure RunMode where
  mem : Bool
  views : Array ViewParam := #[]
  /-- The `Ctx.view` term of the run. -/
  view : String := "(fun _ => none)"

/-- Source and capture metadata of one extracted loop. Equality certificates and
completeness motives use the same capture, cell and enclosing-exit context. -/
structure LoopCertData where
  inst : Inst
  body : Array Inst
  blocks : List InstId
  parents : List InstId
  caps : Array (InstId × String)
  cells : Array InstId

private def loopCertDatum (sh : CertShape) (regs : Array InstId)
    (ctx : Inst × Array Inst × List InstId × List InstId) : LoopCertData :=
  let (inst, body, blocks, parents) := ctx
  { inst, body, blocks, parents,
    caps := ((sh.loops.find? (·.1 == inst.id)).map (·.2)).getD #[],
    cells := cellsIn regs body }

def loopCertData (f : Func) (sh : CertShape) (regs : Array InstId) : Array LoopCertData :=
  ((loopCtx [] [] f.body).reverse).map (loopCertDatum sh regs)

def loopTypes (f : Func) : Std.HashMap InstId TyId :=
  (allInsts f.body).foldl (fun m i => m.insert i.id i.ty) {}

def loopScalar (f : Func) (tys : Std.HashMap InstId TyId) (blank : Scalar) (k : InstId) : Scalar :=
  ((tys[k]?).bind (scalar? f)).getD blank

def loopCellScalar (f : Func) (tys : Std.HashMap InstId TyId) (blank : Scalar) (a : InstId) : Scalar :=
  ((tys[a]?).bind (Sem.pointee? f) |>.bind (scalar? f)).getD blank

def loopField (sh : CertShape) (a : InstId) : String :=
  ((sh.fields.find? (·.1 == a)).map (·.2)).getD s!"local{a}"

/-- Encode the actual generated locals into the arbitrary reference frame. No fresh
environment or frame replaces the caller's capture and cell hypotheses. -/
def loopFrame (sh : CertShape) (regs : Array InstId) (cellScalar : InstId → Scalar)
    (st locals : String) : String :=
  regs.foldl (init := st) fun acc a =>
    s!"(Frame.setCell {acc} {a} (some {(cellScalar a).enc s!"{locals}.{loopField sh a}"}))"

def loopState (sh : CertShape) (regs : Array InstId) (cellScalar : InstId → Scalar)
    (localsTy st : String) : String :=
  let fs := (regs.map fun a =>
      s!"{loopField sh a} := {(cellScalar a).decT s!"({st}.cell {a})"}") ++
    sh.escaping.map fun e => s!"{loopField sh e} := Value.toPtr (env.val {e})"
  if fs.isEmpty then s!"(default : {localsTy})"
  else "{ (default : " ++ localsTy ++ ") with " ++ ", ".intercalate fs.toList ++ " }"

/-- The loop machinery of a function with loops (`docs/air-semantics.md` §Loops): its AIR's field
lemmas, the exit encoding, and per loop (innermost first) the one-iteration lemma, the loop
commutation, the loop's exits and the rewrite used at the loop; then the step proof. -/
def loopCert (f : Func) (sh : CertShape) (ns gen air d : String) (calls : Bool)
    (calleeLemmas : List String) (rm : RunMode) : Array String × Array String := Id.run do
  let L := s!"{ns}.{sh.localsName}"
  let E := s!"{ns}.{sh.exitName}"
  let enc := s!"enc_{d}"
  let oracle := if calls then "gen" else "call"
  let callBinder := if calls then "" else "(call : Oracle) "
  let callArg := if calls then "" else "call "
  let stuckArg := if calls then "" else "(fun _ _ => StateT.lift stuck) "
  let ctx := s!"⟨program, {air}, args, {oracle}, {rm.view}⟩"
  -- The view items `a<i>` of every viewed parameter, and the slice `p<i>` with its size `h<i>` of
  -- those a loop captures (a loop's lemmas are stated for these names).
  let viewsOf (caps : Array (InstId × String)) := rm.views.filter fun v => caps.any (·.1 == v.arg)
  let binders (cvs : Array ViewParam) : String := String.join <|
    (rm.views.toList.map fun v => s!"(a{v.idx} : Array ({v.sc.lean})) ") ++
    cvs.toList.map fun v => s!"(p{v.idx} : Zig.Slice) (hs{v.idx} : a{v.idx}.size = p{v.idx}.len.toNat) "
  let argsOf (cvs : Array ViewParam) : String := String.join <|
    (rm.views.toList.map fun v => s!"a{v.idx} ") ++ cvs.toList.map fun v => s!"p{v.idx} hs{v.idx} "
  let tys := loopTypes f
  let blank := (sig f).ret
  let scalarOf := loopScalar f tys blank
  let viewOf (k : InstId) : Option ViewParam := rm.views.find? (·.arg == k)
  let regs := registers f
  let cellScalar := loopCellScalar f tys blank
  -- The frame of a generated state `t`: `st` with every register's cell, written in increasing
  -- id order (`Frame.setCell_comm`'s normal form). The escaping locals' pointers are in the
  -- environment, and a loop does not change the frame's blocks.
  let frameOf := loopFrame sh regs cellScalar
  -- The generated state of a frame and an environment.
  let stateOf := loopState sh regs cellScalar L
  let fieldLemmas := [s!"{air}_body", s!"{air}_types", s!"{air}_layouts", s!"{air}_params"]
  let mut out : Array String := #[
    s!"theorem {air}_body : {air}.body =\n  {(printBody f.body).getD "#[]"} := rfl",
    s!"theorem {air}_types : {air}.types = {arr printTy f.types} := rfl",
    s!"theorem {air}_layouts : {air}.layouts = {arr printLayout f.layouts} := rfl",
    s!"theorem {air}_params : {air}.params = {arr toString f.params} := rfl", "",
    s!"/-- The generated exits of `{f.name}` as AIR exits. -/",
    s!"def {enc} : {E} → Exit",
    (match retScalar? f f.ret with
      | some r => if r.ignoresValue then "  | .ret => .ret .void" else s!"  | .ret v => .ret {r.enc "v"}"
      | none => "  | .ret _ => .ret .void")]
  for k in sh.brT do
    let t := ((sh.blockTys.find? (·.1 == k)).map (·.2)).getD 0
    out := out.push (if f.types[t]? matches some Ty.void then s!"  | .br{k} => .br {k} .void"
      else s!"  | .br{k} v => .br {k} {((scalar? f t).getD blank).enc "v"}")
  for k in sh.repT do
    out := out.push s!"  | .rep{k} => .rep {k}"
  out := out.push ""
  let viewSet (cvs : Array ViewParam) := if rm.views.isEmpty then [] else
    [s!"view_{d}"] ++ cvs.toList.flatMap fun v => [s!"len_of_size hs{v.idx}", s!"hs{v.idx}"]
  let baseSet := fieldLemmas ++ ["air_sem", enc, s!"policy_{d}", s!"entry_{d}"] ++
    calleeLemmas ++ (if calls then ["gen"] else [])
  -- The tactic that closes a normalized step: equal binds, and after a loop a case split on its
  -- exit, restricted to the exits the loop has (`bind_congr_ok`).
  let close (loops : List (InstId × Nat × String)) (set : List String) : Array String :=
    let set := ", ".intercalate (set ++ ["Exit.again", "exitOk"])
    let pat := if rm.mem then "⟨⟨e, s⟩, m⟩" else "⟨e, s⟩"
    #["  all_goals repeat (first", "    | rfl"] ++
      (loops.toArray.map fun (n, nfree, va) =>
        s!"    | (refine bind_congr_ok _ _ (fun r hr => {d}_loop{n}_exits {va}{" ".intercalate (List.replicate nfree "_")} _ {if rm.mem then "_ " else ""}r hr) ?_\n" ++
        s!"       rintro {pat} ⟨h1, h2⟩\n" ++
        "       cases e <;> simp (config := { failIfUnchanged := false }) only [" ++ set ++ "] at h1 h2 ⊢)") ++
      #["    | (refine bind_congr fun _ => ?_))"]
  let ctxs := loopCertData f sh regs
  let mut done : Array (InstId × Nat × String) := #[]
  for info in ctxs do
    let n := info.inst.id
    let body := info.body
    let bs := info.blocks
    let ls := info.parents
    -- A captured view slice is its parameter's `p<i>`, and the generated loop gets its items `a<i>`.
    let caps := info.caps
    let ownCaps := caps.filter fun (k, _) => (viewOf k).isNone
    let cvs := viewsOf caps
    let vb := binders cvs
    let va := argsOf cvs
    let cells := info.cells
    let B := (printBody body).getD "#[]"
    let xs := caps.map fun (k, _) => match viewOf k with | some v => s!"a{v.idx}" | none => s!"x{k}"
    let xBinders := " ".intercalate (ownCaps.toList.map fun (k, _) => s!"(x{k} : {(scalarOf k).lean})")
    let capVal (val : InstId → String) (k : InstId) : String := match viewOf k with
      | some v => s!"(Value.slice p{v.idx})"
      | none => (scalarOf k).enc (val k)
    let hyps (val : InstId → String) := " ".intercalate
      ((caps.toList.map fun (k, _) => s!"(h{k} : env {k} = some ({tys[k]?.getD 0}, {capVal val k}))") ++
        cells.toList.map fun a => s!"(h{a} : env {a} = some ({tys[a]?.getD 0}, .cell {a}))")
    let hNames := " ".intercalate ((caps.toList.map fun (k, _) => s!"h{k}") ++ cells.toList.map fun a => s!"h{a}")
    let app (args : Array String) := s!"{gen}.loop{n}{String.join (args.toList.map (" " ++ ·))}"
    let again := s!"{gen}.again{n}"
    let F := frameOf
    -- Inner loops of this body: their rewrites and exits.
    let bodyIds := (allInsts body).map (·.id)
    let inner := done.filter fun (k, _) => bodyIds.contains k
    let innerSet := inner.toList.map fun (k, _) => s!"{d}_loop{k}"
    let bodySet := ", ".intercalate (baseSet ++ viewSet cvs ++ (caps.toList.map fun (k, _) => s!"h{k}") ++
      (cells.toList.map fun a => s!"h{a}") ++ innerSet ++ ["Env.val", "Frame.cell"])
    let ownXs := ownCaps.map fun (k, _) => s!"x{k}"
    let bodyRhs := if rm.mem then s!"((fun r => ({enc} r.1, {F "st" "r.2"})) <$> ({app xs}).run s).run m"
      else s!"(fun r => (({enc} r.1, {F "st" "r.2"}), m)) <$> ({app xs}).run s"
    out := out ++ #[
      s!"theorem {d}_loop{n}_body {callBinder}{vb}(args : List Value) (env : Env) (st : Frame) {xBinders}",
      s!"    {hyps (s!"x{·}")} (s : {L}) (m : Zig.Mem) :",
      s!"    ((execIteration {ctx} (Array.toList {B}) env).run {F "st" "s"}).run m =",
      s!"      {bodyRhs} := by",
      s!"  conv => rhs; rw [{gen}.loop{n}]",
      s!"  simp only [{bodySet}]"] ++
      close inner.toList (baseSet ++ viewSet cvs ++ innerSet ++ ["Env.val", "Frame.cell"]) ++ #[""]
    let bodyArgs := s!"{callArg}{va}args env st {" ".intercalate ownXs.toList} {hNames}"
    if rm.mem then
      out := out ++ #[
        s!"theorem {d}_loop{n}_comm {callBinder}{vb}(args : List Value) (env : Env) (st : Frame) {xBinders}",
        s!"    {hyps (s!"x{·}")} (s : {L}) :",
        s!"    (execLoop {ctx} {n} {B} env).run {F "st" "s"} =",
        s!"      mapRes {enc} (fun s : {L} => {F "st" "s"}) <$> (Zig.loop ({app xs}) {again}).run s := by",
        "  unfold execLoop",
        s!"  exact loop_comm _ _ (Exit.again {n}) {again} {enc} (fun s : {L} => {F "st" "s"})",
        s!"    (fun s => by funext m; exact {d}_loop{n}_body {bodyArgs} s m)",
        "    (by intro e; cases e <;> rfl) s", ""]
    else
      out := out ++ #[
        s!"theorem {d}_loop{n}_comm {callBinder}{vb}(args : List Value) (env : Env) (st : Frame) {xBinders}",
        s!"    {hyps (s!"x{·}")} (s : {L}) (m : Zig.Mem) :",
        s!"    ((execLoop {ctx} {n} {B} env).run {F "st" "s"}).run m =",
        s!"      (fun r => (mapRes {enc} (fun s : {L} => {F "st" "s"}) r, m)) <$> (Zig.loop ({app xs}) {again}).run s := by",
        "  unfold execLoop",
        s!"  exact loop_comm_pure _ _ (Exit.again {n}) {again} {enc} (fun s : {L} => {F "st" "s"})",
        s!"    (fun s m => {d}_loop{n}_body {bodyArgs} s m)",
        "    (by intro e; cases e <;> rfl) s m", ""]
    let canon := (caps.toList.map fun (k, _) => (k, capVal (s!"x{·}") k)) ++
      cells.toList.map fun a => (a, s!"(.cell {a})")
    let envTerm := canon.foldl (init := "(fun _ => none)") fun acc (k, v) =>
      s!"(Env.set {acc} {k} {tys[k]?.getD 0} {v})"
    let byEnv := " ".intercalate (List.replicate (caps.size + cells.size) "(by simp [env, Env.set])")
    let commArgs := s!"{stuckArg}{va}[] env " ++ "{} " ++ s!"{" ".intercalate ownXs.toList} {byEnv} s"
    let hrTy := if rm.mem then s!"(r : ({E} × {L}) × Zig.Mem)\n    (hr : (((Zig.loop ({app xs}) {again}).run s).run m).run = some (.ok r))"
      else s!"(r : {E} × {L})\n    (hr : ((Zig.loop ({app xs}) {again}).run s).run = some (.ok r))"
    let rr := if rm.mem then "r.1.1" else "r.1"
    out := out ++ #[
      s!"theorem {d}_loop{n}_exits {vb}{xBinders} (s : {L}){if rm.mem then " (m : Zig.Mem)" else ""} {hrTy} :",
      s!"    Exit.again {n} ({enc} {rr}) = false ∧ exitOk {bs} {ls} ({enc} {rr}) = true := by",
      s!"  let env : Env := {envTerm}"] ++
      (if rm.mem then #[
        s!"  exact ok_transfer (F := fun s : {L} => {F "({} : Frame)" "s"})",
        s!"    ({d}_loop{n}_comm {commArgs})",
        s!"    (execLoop_ok _ {n} _ env {bs} {ls} (by simp [wfBody, wfInst, wfCases])) m r hr", ""]
      else #[
        s!"  exact ok_transfer_pure (F := fun s : {L} => {F "({} : Frame)" "s"})",
        s!"    (fun m => {d}_loop{n}_comm {commArgs} m)",
        s!"    (execLoop_ok _ {n} _ env {bs} {ls} (by simp [wfBody, wfInst, wfCases])) r hr", ""])
    -- The rewrite at the loop: values decoded from the environment and the frame.
    let decOf (k : InstId) : String := match viewOf k with
      | some v => s!"a{v.idx}"
      | none => (scalarOf k).decT s!"(env.val {k})"
    let decs := caps.map fun (k, _) => decOf k
    let ownDecs := ownCaps.map fun (k, _) => (scalarOf k).decT s!"(env.val {k})"
    let sliceOf (v : ViewParam) := s!"(Value.toSlice (env.val {v.arg}))"
    let useBinders := String.join <|
      rm.views.toList.map fun v => s!"(a{v.idx} : Array ({v.sc.lean})) "
    let sizeHyps := String.join <|
      cvs.toList.map fun v => s!" (hs{v.idx} : a{v.idx}.size = {sliceOf v}.len.toNat)"
    let useViewArgs := String.join <|
      (rm.views.toList.map fun v => s!"a{v.idx} ") ++ cvs.toList.map fun v => s!"{sliceOf v} hs{v.idx} "
    let useHyps := " ".intercalate
      ((caps.toList.map fun (k, _) => match viewOf k with
        | some v => s!"(h{k} : env {k} = some ({tys[k]?.getD 0}, Value.slice {sliceOf v}))"
        | none => s!"(h{k} : env {k} = some ({tys[k]?.getD 0}, {(scalarOf k).enc ((scalarOf k).decT s!"(env.val {k})")}))") ++
        cells.toList.map fun a => s!"(h{a} : env {a} = some ({tys[a]?.getD 0}, .cell {a}))")
    let hst := regs.toList.map fun a =>
        s!"(hc{a} : st.cells {a} = some {(cellScalar a).enc ((cellScalar a).decT s!"(st.cell {a})")})"
    let eqs := regs.toList.map fun a => s!"Frame.setCell_eq _ _ _ hc{a}"
    let useArgs := s!"{callArg}{useViewArgs}args env st {" ".intercalate ownDecs.toList} {hNames} {stateOf "st"}"
    let rhs := if rm.mem then
        s!"      mapRes {enc} (fun s : {L} => {F "st" "s"}) <$>\n        (Zig.loop ({app decs}) {again}).run {stateOf "st"} := by"
      else
        s!"      StateT.lift (mapRes {enc} (fun s : {L} => {F "st" "s"}) <$>\n        (Zig.loop ({app decs}) {again}).run {stateOf "st"}) := by"
    out := out ++ #[
      s!"theorem {d}_loop{n} {callBinder}{useBinders}(args : List Value) (env : Env) (st : Frame) (B : Array Inst)",
      s!"    (hB : B = {B})",
      s!"    {useHyps}{sizeHyps}",
      s!"    {" ".intercalate hst} :",
      s!"    (execLoop {ctx} {n} B env).run st =",
      rhs,
      "  subst hB",
      s!"  have e : {F "st" (stateOf "st")} = st := by",
      "    dsimp only",
      s!"    rw [{", ".intercalate eqs}]",
      "  conv => lhs; rw [← e]"] ++
      (if rm.mem then #[s!"  exact {d}_loop{n}_comm {useArgs}", ""]
      else #["  apply StateT.ext; intro m",
        "  rw [lift_map_run]",
        s!"  exact {d}_loop{n}_comm {useArgs} m", ""])
    done := done.push (n, ownCaps.size, va)
  let top := done.filter fun (k, _) => (ctxs.find? (·.inst.id == k)).any (·.parents.isEmpty)
  let stepSet := ", ".intercalate (baseSet ++ viewSet rm.views ++ top.toList.map (fun (k, _) => s!"{d}_loop{k}") ++
    ["Env.val", "Frame.cell"])
  let proof := #[s!"  simp only [{stepSet}]"] ++ close top.toList (baseSet ++ viewSet rm.views ++ ["Env.val", "Frame.cell"])
  (out, proof)

/-- One actual executable declaration, with its original AIR and the existing loop capture
and frame metadata. A loop helper is a member in its own right, rather than a source function
silently removed from the compiler's induction clique. -/
private structure CompleteDecl where
  emitted : EmittedDecl
  source : Func
  shape : CertShape
  loop : Option LoopCertData
  compiler : CompiledMember
  /-- Explicit source/capture binders mapped into the compiler's original formal positions. -/
  positions : Array Nat
  /-- A state binder already exposed in the compiler's body arity. Otherwise `StateT.run`
  supplies the state after the recorded original formals. -/
  statePosition : Option Nat

private def completeDecl (frag : Array Func) (shapes : Array (String × CertShape))
    (ns : String) (emitted : EmittedDecl) (compiler : CompiledMember) : Except String CompleteDecl := do
  let some source := frag.find? (·.name == emitted.id.sourceName)
    | throw s!"actual proof clique contains an uncertified source: {emitted.id.sourceName}"
  let some (_, shape) := shapes.find? (·.1 == source.name)
    | throw s!"actual proof clique has no capture/frame metadata: {source.name}"
  unless compiler.name == compiledName ns emitted do throw "compiler/source declaration identity mismatch"
  let loop ← match emitted.id with
    | .function _ => pure none
    | .loop _ id => do
      let some ctx := ((loopCtx [] [] source.body).reverse).find? (fun (inst, _, _, _) => inst.id == id)
        | throw s!"actual helper has no existing loop metadata: {compiler.name}"
      let info := loopCertDatum shape (registers source) ctx
      unless info.caps.map (·.2) == emitted.params.map (·.1) do
        throw s!"actual helper capture order disagrees with its emitted signature: {compiler.name}"
      pure (some info)
  let positions ← emitted.params.mapM fun (name, _) => do
    let some index := compiler.params.findIdx? (fun (actual, binder) => actual == name && binder == "default")
      | throw s!"actual runtime/capture binder is absent from compiler formals: {compiler.name}.{name}"
    pure index
  let extras := (Array.range compiler.params.size).filter (!positions.contains ·)
  let statePosition ← match loop, extras.toList with
    | _, [] => pure none
    | some _, [index] => pure (some index)
    | _, _ => throw s!"unmapped formals in actual executable signature: {compiler.name}"
  pure { emitted, source, shape, loop, compiler, positions, statePosition }

private def CompleteDecl.stem (decl : CompleteDecl) : String :=
  let name := "_".intercalate (decl.emitted.name.splitOn "." |>.map plainName)
  let name := String.ofList (name.toList.map fun c => if c.isAlphanum then c else '_')
  (if decl.loop.isSome then "loop_" else "fn_") ++ name

private def CompleteDecl.values (decl : CompleteDecl) : Array String :=
  decl.emitted.params.mapIdx fun i _ => s!"a{i}"

private def CompleteDecl.binders (decl : CompleteDecl) : String :=
  " ".intercalate ((decl.emitted.params.mapIdx fun i (_, type) => s!"(a{i} : {type})").toList)

private def CompleteDecl.formalValue (decl : CompleteDecl) (index : Nat) : Except String String := do
  if let some i := decl.positions.idxOf? index then return s!"a{i}"
  if decl.statePosition == some index then return "s"
  throw s!"unmapped original compiler formal in {decl.compiler.name}"

private def CompleteDecl.guard (decl : CompleteDecl) (fixed : Array String) : Except String String := do
  let mut tests := #[]
  for index in [:decl.compiler.fixed.size] do
    if let some k := decl.compiler.fixed[index]! then
      let some value := fixed[k]? | throw "missing common compiler fixed parameter"
      tests := tests.push s!"{← decl.formalValue index} = {value}"
  pure (if tests.isEmpty then "True" else " ∧ ".intercalate tests.toList)

/-- Apply a compiler approximation to its actual varying formals. Fixed arguments are not
reintroduced into the partial approximation's type. The guard in the motive binds them to
the caller's fixed tuple before they may justify an arbitrary call-oracle argument. -/
private def CompleteDecl.approx (decl : CompleteDecl) (head : String) : Except String String := do
  let mut args := #[]
  for index in [:decl.compiler.fixed.size] do
    if decl.compiler.fixed[index]!.isNone then args := args.push (← decl.formalValue index)
  let app := head ++ String.join (args.toList.map (" " ++ ·))
  pure <| if decl.loop.isSome && decl.statePosition.isNone then s!"({app}).run s" else app

private def CompleteDecl.loopHyps (decl : CompleteDecl) : String :=
  match decl.loop with
  | none => ""
  | some info =>
    let tys := loopTypes decl.source
    let scalar := loopScalar decl.source tys (sig decl.source).ret
    " ".intercalate <|
      ((info.caps.mapIdx fun i (id, _) =>
        s!"(h{id} : env {id} = some ({tys[id]?.getD 0}, {(scalar id).enc s!"a{i}"}))").toList ++
        info.cells.toList.map fun id => s!"(h{id} : env {id} = some ({tys[id]?.getD 0}, .cell {id}))")

private def CompleteDecl.loopHypNameArray (decl : CompleteDecl) : Array String :=
  match decl.loop with
  | none => #[]
  | some info => (info.caps.map (fun (id, _) => s!"h{id}")) ++ info.cells.map (fun id => s!"h{id}")

private def CompleteDecl.loopHypNames (decl : CompleteDecl) : String :=
  " ".intercalate decl.loopHypNameArray.toList

private def CompleteDecl.extraBinders (decl : CompleteDecl) (ns : String) : String :=
  match decl.loop with
  | none => "(m : Zig.Mem)"
  | some _ => s!"(args : List Value) (env : Env) (st : Frame) {decl.loopHyps} " ++
      s!"(s : {ns}.{decl.shape.localsName}) (m : Zig.Mem)"

private def CompleteDecl.extraNameArray (decl : CompleteDecl) : Array String :=
  if decl.loop.isSome then #["args", "env", "st"] ++ decl.loopHypNameArray ++ #["s", "m"] else #["m"]

private def CompleteDecl.extraNames (decl : CompleteDecl) : String :=
  " ".intercalate decl.extraNameArray.toList

private def CompleteDecl.encodeResult (decl : CompleteDecl) (result d : String) : String :=
  match decl.loop with
  | none => s!"(fun {(sig decl.source).ret.binder} => ({(sig decl.source).ret.enc "v"}, m)) <$> {result}"
  | some _ =>
    let regs := registers decl.source
    let scalar := loopCellScalar decl.source (loopTypes decl.source) (sig decl.source).ret
    let frame := loopFrame decl.shape regs scalar "st" "r.2"
    s!"(fun r => ((enc_{d} r.1, {frame}), m)) <$> {result}"

private def CompleteDecl.left (decl : CompleteDecl) (head d : String) : Except String String := do
  pure (decl.encodeResult (← decl.approx head) d)

private def CompleteDecl.fullLeft (decl : CompleteDecl) (head d : String) : String :=
  let app := head ++ String.join (decl.values.toList.map (" " ++ ·))
  decl.encodeResult (if decl.loop.isSome then s!"({app}).run s" else app) d

private def CompleteDecl.right (decl : CompleteDecl) (air : String) : String :=
  match decl.loop with
  | none =>
    let encArgs := ", ".intercalate (((sig decl.source).ps.mapIdx fun i (_, scalar) => scalar.enc s!"a{i}").toList)
    s!"((runOn program table {str decl.source.name} [{encArgs}]).run m)"
  | some info =>
    let regs := registers decl.source
    let scalar := loopCellScalar decl.source (loopTypes decl.source) (sig decl.source).ret
    let frame := loopFrame decl.shape regs scalar "st" "s"
    s!"(((execIteration ⟨program, {air}, args, runOn program table, fun _ => none⟩ " ++
      s!"(Array.toList {(printBody info.body).getD "#[]"}) env).run {frame}).run m)"

private def CompleteDecl.motive (decl : CompleteDecl) (fixed : Array String)
    (ns air d : String) : Except String String := do
  pure (s!"fun g => ∀ {decl.binders} {decl.extraBinders ns}, {← decl.guard fixed} → " ++
    s!"Lean.Order.PartialOrder.rel ({← decl.left "g" d}) {decl.right air}")

private def CompleteDecl.fullStatement (decl : CompleteDecl) (head ns air d : String) : String :=
  s!"∀ {decl.binders} {decl.extraBinders ns}, Lean.Order.PartialOrder.rel " ++
    s!"({decl.fullLeft head d}) {decl.right air}"

private def CompleteDecl.intros (decl : CompleteDecl) : String :=
  " ".intercalate decl.values.toList ++ " " ++ decl.extraNames

/-- Reinsert the fixed tuple into the original declaration application, retaining the exact
compiler permutation. This is the same partial declaration that the compiler theorem's
conclusion supplies, expressed with ordinary lambdas rather than another proof interface. -/
private def CompleteDecl.partialTerm (decl : CompleteDecl) (fixed : Array String)
    (ns : String) : Except String String := do
  let mut binders := #[]
  let mut values := #[]
  for index in [:decl.compiler.params.size] do
    if let some k := decl.compiler.fixed[index]! then
      let some value := fixed[k]? | throw "missing partial declaration fixed parameter"
      values := values.push value
    else
      let type ← if let some i := decl.positions.idxOf? index then pure decl.emitted.params[i]!.2
        else if decl.statePosition == some index then pure s!"{ns}.{decl.shape.localsName}"
        else throw "unknown varying compiler formal"
      binders := binders.push s!"(v{index} : {type})"
      values := values.push s!"v{index}"
  let runtime := decl.positions.map (fun i => values[i]!)
  let app := s!"{ns}.{decl.emitted.name}" ++ String.join (runtime.toList.map (" " ++ ·))
  let app := match decl.statePosition with
    | some i => s!"({app}).run {values[i]!}"
    | none => app
  pure (if binders.isEmpty then app else s!"(fun {" ".intercalate binders.toList} => {app})")

private def CompleteDecl.admissibility (decl : CompleteDecl) : Except String (Array String) := do
  let names := decl.values ++ decl.extraNameArray ++ #["hfixed"]
  let mut lines := names.map fun name => s!"    apply Lean.Order.admissible_pi; intro {name}"
  -- Applying a known original formal is an existing generic continuous projection. It works
  -- for every helper capture count; the source-function arity gate is unchanged.
  for index in [:decl.compiler.params.size] do
    if decl.compiler.fixed[index]!.isNone then
      lines := lines.push s!"    apply Lean.Order.admissible_apply (x := {← decl.formalValue index})"
  if decl.loop.isSome && decl.statePosition.isNone then
    lines := lines.push "    apply Lean.Order.admissible_apply (x := s)"
  pure (lines.push "    exact adm_app0 _ _")

private def CompleteDecl.fixedIntro (decl : CompleteDecl) : Except String (Array String) := do
  let fixed := (Array.range decl.compiler.fixed.size).filter (fun i => decl.compiler.fixed[i]!.isSome)
  let intro := s!"    intro {decl.intros} hfixed"
  if fixed.isEmpty then return #[intro]
  let names := fixed.mapIdx (fun i _ => s!"hfixed{i}")
  let split := if names.size == 1 then s!"    have {names[0]!} := hfixed"
    else s!"    rcases hfixed with ⟨{", ".intercalate names.toList}⟩"
  let substitutions ← fixed.mapM fun index => do pure s!"    subst {← decl.formalValue index}"
  pure (#[intro, split] ++ substitutions)

private def CompleteDecl.boundAdapter (decl : CompleteDecl) (fixed : Array String)
    (approx ih ns air d : String) : Except String (Array String) := do
  let adapter := s!"b_{decl.stem}"
  let result ← decl.approx approx
  let guard ← decl.guard fixed
  let nativeRet := if decl.loop.isSome then s!"Zig.M {ns}.{decl.shape.localsName} {ns}.{decl.shape.exitName}"
    else s!"Zig.Result ({(sig decl.source).ret.lean})"
  let nativeTy := " → ".intercalate ((decl.emitted.params.map (·.2)).toList ++ [nativeRet])
  let state := if decl.loop.isSome then s!" (s : {ns}.{decl.shape.localsName})" else ""
  let args := " ".intercalate decl.values.toList
  let body := s!"if {guard} then {result} else stuck"
  let binders := decl.binders ++ state
  let body := if binders.trimAscii.toString.isEmpty then body else s!"fun {binders} => {body}"
  pure #[
    s!"    let {adapter} : {nativeTy} := {body}",
    s!"    have hb_{decl.stem} : {decl.fullStatement adapter ns air d} := by",
    s!"      intro {decl.intros}",
    s!"      by_cases hfixed : {guard}",
    s!"      · simpa only [{adapter}, hfixed, if_pos] using {ih} {args} {decl.extraNames} hfixed",
    s!"      · simp only [{adapter}, hfixed, if_neg]",
    "        exact Lean.Order.FlatOrder.rel.bot"]

/-- The existing loop-certificate producer's one-way closure, fed by a helper motive or a
previous helper completeness theorem. The same capture/frame/exit metadata used above for
exact certificates is retained here, including the arbitrary reference environment. -/
private def CompleteDecl.loopClosure (decl : CompleteDecl) (head hyp ns gen air d : String) :
    Except String (Array String) := do
  let some info := decl.loop | throw "loop closure requested for a source function"
  let n := info.inst.id
  let L := s!"{ns}.{decl.shape.localsName}"
  let E := s!"{ns}.{decl.shape.exitName}"
  let enc := s!"enc_{d}"
  let again := s!"{gen}.again{n}"
  let tys := loopTypes decl.source
  let regs := registers decl.source
  let scalar := loopScalar decl.source tys (sig decl.source).ret
  let cellScalar := loopCellScalar decl.source tys (sig decl.source).ret
  let frame := loopFrame decl.shape regs cellScalar
  let state := loopState decl.shape regs cellScalar L
  let B := (printBody info.body).getD "#[]"
  let ctx := s!"⟨program, {air}, args, runOn program table, fun _ => none⟩"
  let native := s!"Zig.loop ({head} {" ".intercalate decl.values.toList}) {again}"
  let loopLeft := decl.encodeResult s!"({native}).run s" d
  let loopRight := s!"(((execLoop {ctx} {n} {B} env).run {frame "st" "s"}).run m)"
  let comm := s!"lc_{decl.stem}"
  let exits := s!"lx_{decl.stem}"
  let use := s!"lu_{decl.stem}"
  let runtimeArgs := " ".intercalate decl.values.toList
  let mut lines := #[
    s!"    have {comm} : ∀ {decl.binders} {decl.extraBinders ns}, Lean.Order.PartialOrder.rel ({loopLeft}) {loopRight} := by",
    s!"      intro {decl.intros}",
    "      unfold execLoop",
    s!"      exact loop_comm_pure_le _ _ (Exit.again {n}) {again} {enc} (fun s : {L} => {frame "st" "s"})",
    s!"        (fun s m => {hyp} {runtimeArgs} args env st {decl.loopHypNames} s m)",
    "        (by intro e; cases e <;> rfl) s m"]
  let canon := (info.caps.mapIdx fun i (id, _) => (id, (scalar id).enc s!"a{i}")).toList ++
    info.cells.toList.map fun id => (id, s!"(.cell {id})")
  let envTerm := canon.foldl (init := "(fun _ => none)") fun env (id, value) =>
    s!"(Env.set {env} {id} {tys[id]?.getD 0} {value})"
  let byEnv := " ".intercalate (List.replicate canon.length "(by simp [env, Env.set])")
  let bs := toString info.blocks
  let ls := toString info.parents
  lines := lines ++ #[
    s!"    have {exits} {decl.binders} (s : {L}) (r : {E} × {L})",
    s!"        (hr : (({native}).run s).run = some (.ok r)) :",
    s!"        Exit.again {n} ({enc} r.1) = false ∧ exitOk {bs} {ls} ({enc} r.1) = true := by",
    s!"      let env : Env := {envTerm}",
    s!"      exact ok_transfer_pure_le (F := fun s : {L} => {frame "({} : Frame)" "s"})",
    s!"        (fun m => {comm} {runtimeArgs} [] env " ++ "{} " ++ s!"{byEnv} s m)",
    s!"        (execLoop_ok _ {n} _ env {bs} {ls} (by simp [wfBody, wfInst, wfCases])) r hr"]
  let decoded := info.caps.map fun (id, _) => (scalar id).decT s!"(env.val {id})"
  let captureHyps := (info.caps.toList.map fun (id, _) =>
      s!"(h{id} : env {id} = some ({tys[id]?.getD 0}, {(scalar id).enc ((scalar id).decT s!"(env.val {id})")}))") ++
    info.cells.toList.map fun id => s!"(h{id} : env {id} = some ({tys[id]?.getD 0}, .cell {id}))"
  let cellHyps := regs.toList.map fun id =>
    s!"(hc{id} : st.cells {id} = some {(cellScalar id).enc ((cellScalar id).decT s!"(st.cell {id})")})"
  let eqs := regs.toList.map fun id => s!"Frame.setCell_eq _ _ _ hc{id}"
  let native := s!"Zig.loop ({head} {" ".intercalate decoded.toList}) {again}"
  let left := decl.encodeResult s!"({native}).run {state "st"}" d
  lines := lines ++ #[
    s!"    have {use} (args : List Value) (env : Env) (st : Frame) (B : Array Inst) (hB : B = {B})",
    s!"        {" ".intercalate (captureHyps ++ cellHyps)} (m : Zig.Mem) :",
    s!"        Lean.Order.PartialOrder.rel ({left}) (((execLoop {ctx} {n} B env).run st).run m) := by",
    "      subst hB",
    s!"      have e : {frame "st" (state "st")} = st := by",
    "        dsimp only"] ++
      (if eqs.isEmpty then #["        rfl"] else #[s!"        rw [{", ".intercalate eqs}]"]) ++ #[
    "      conv => rhs; rw [← e]",
    s!"      exact {comm} {" ".intercalate decoded.toList} args env st {decl.loopHypNames} {state "st"} m"]
  pure lines

/-- The certificate of a function without memory with slice parameters (`isView`): its view
(`view_<d>`, the items of each slice parameter by its `arg` instruction), `<d>_view` (the run with
the view is the generated definition, by normalization) and `<d>_step` (from a memory in which the
caller read the items, the AIR semantics agrees with it up to read entries, `execFunc_view` and
`holds_of_readSlice`). -/
def viewCert (f : Func) (sh : CertShape) (ns gen air d : String) (calleeLemmas : List String) :
    Array String := Id.run do
  let views := (viewParams f).toOption.getD #[]
  let viewOf (i : Nat) := views.find? (·.idx == i)
  let s := sig f
  let items := " ".intercalate (views.toList.map fun v => s!"a{v.idx}")
  let viewTerm := s!"(view_{d} {items})"
  let enc (v : ViewParam) := s!"(fun x => {v.sc.enc "x"})"
  let mut out : Array String := #[
    s!"/-- The items of `{f.name}`'s slice parameters, by their `arg` instruction. -/",
    s!"def view_{d} {" ".intercalate (views.toList.map fun v => s!"(a{v.idx} : Array ({v.sc.lean}))")} : InstId → Option (Array Value) :=",
    "  fun k => " ++ String.join (views.toList.map fun v => s!"if k = {v.arg} then some (a{v.idx}.map {enc v}) else ") ++ "none", "",
    s!"/-- The item type of each viewed slice. -/",
    s!"def viewTy_{d} : InstId → TyId :=",
    "  fun k => " ++ String.join (views.toList.map fun v => s!"if k = {v.arg} then {v.item} else ") ++ "0", ""]
  -- Parameters: a viewed one is its slice `p<i>`, items `a<i>` and their count `h<i>`.
  let binders := " ".intercalate (s.ps.toList.map fun (i, sc) => match viewOf i with
    | some v => s!"(p{i} : Zig.Slice) (a{i} : Array ({v.sc.lean})) (hs{i} : a{i}.size = p{i}.len.toNat)"
    | none => s!"(p{i} : {sc.lean})")
  let encArgs := ", ".intercalate (s.ps.toList.map fun (i, sc) =>
    if (viewOf i).isSome then s!"Value.slice p{i}" else sc.enc s!"p{i}")
  let genArgs := " ".intercalate (s.ps.toList.map fun (i, _) => if (viewOf i).isSome then s!"a{i}" else s!"p{i}")
  let stmt := #[
    s!"/-- `{f.name}` run with the items of its slices as a view equals the generated definition. -/",
    s!"theorem {d}_view (call : Oracle) {binders} (m : Zig.Mem) :",
    s!"    (execFuncV program call {viewTerm} {air} [{encArgs}]).run m =",
    s!"      (fun {s.ret.binder} => ({s.ret.enc "v"}, m)) <$> {gen} {genArgs} := by",
    s!"  conv => rhs; rw [{gen}]"]
  let viewLemmas := ["execFuncV", s!"view_{d}", s!"policy_{d}", s!"entry_{d}"] ++
    views.toList.flatMap fun v => [s!"len_of_size hs{v.idx}", s!"hs{v.idx}"]
  if (allInsts f.body).any (·.op matches .loop _) then
    let (loopLines, stepProof) := loopCert f sh ns gen air d false (calleeLemmas ++ ["execFuncV"])
      { mem := false, views, view := viewTerm }
    out := out ++ loopLines ++ stmt ++ stepProof ++ #[""]
  else
    out := out ++ stmt ++
      #[s!"  simp only [{", ".intercalate ([air, "air_sem"] ++ calleeLemmas ++ viewLemmas)}]", ""]
  -- The step: the caller's materialization (`Zig.readSlice` from `m`) gives the view.
  let stepBinders := " ".intercalate (s.ps.toList.map fun (i, sc) => match viewOf i with
    | some _ => s!"(p{i} : Zig.Slice)"
    | none => s!"(p{i} : {sc.lean})")
  let reads := " ".intercalate (views.toList.map fun v =>
    s!"(a{v.idx} : Array ({v.sc.lean})) (m{v.idx} : Zig.Mem)\n    " ++
    s!"(r{v.idx} : ((Zig.readSlice ({v.sc.lean}) {v.align} p{v.idx}).run m).run = some (.ok (a{v.idx}, m{v.idx})))")
  let viewArgs := " ".intercalate (s.ps.toList.map fun (i, _) =>
    if (viewOf i).isSome then s!"p{i} a{i} hs{i}" else s!"p{i}")
  out := out ++ #[
    s!"/-- `{f.name}`, called with the items its caller read (`Zig.readSlice`, from `m`): the AIR",
    "semantics has the generated definition's values and errors, and its memory is `m` up to read",
    "entries of the running thread (`UpToReads`). -/",
    s!"theorem {d}_step (call : Oracle) {stepBinders} (m : Zig.Mem) (hwf : m.ClockWf)",
    s!"    {reads} :",
    s!"    RelR (fun p q => p.1 = q.1 ∧ UpToReads m p.2 ∧ q.2 = m)",
    s!"      ((execFunc program call {air} [{encArgs}]).run m)",
    s!"      ((fun {s.ret.binder} => ({s.ret.enc "v"}, m)) <$> {gen} {genArgs}) := by"]
  for v in views do
    out := out ++ #[
      s!"  obtain ⟨v{v.idx}, hs{v.idx}, -⟩ := holds_of_readSlice (f := {air}) (t := {v.item}) (a := {v.ptrAlign})",
      s!"    {enc v} r{v.idx} hwf (fun q al => by simp only [{air}, air_sem])",
      s!"    (fun size al h => by",
      s!"      simp only [{air}, air_sem, Option.some.injEq, Prod.mk.injEq] at h",
      "      obtain ⟨rfl, rfl⟩ := h",
      "      decide)"]
  out := out ++ #[
    s!"  rw [← {d}_view call {viewArgs} m]",
    s!"  refine execFunc_view program m {air} _ call {viewTerm} viewTy_{d}",
    s!"    (by simp only [roBody, roNested, roCases, roInst, argAt, {air}, air_sem, view_{d}, viewTy_{d},",
    "      List.find?_cons, List.find?_nil, cond_true, cond_false, Option.isSome_some])",
    s!"    ⟨by simp [Value.noPtr], ?_⟩ policy_{d}",
    "  intro k items idx t hk ha",
    s!"  simp only [view_{d}] at hk"]
  for v in views do
    out := out ++ #[
      "  split at hk",
      "  · cases hk",
      "    subst_vars",
      s!"    rw [show argAt {air} {v.arg} = some ({v.idx}, {v.sliceTy}) from rfl] at ha",
      "    cases ha",
      s!"    exact ⟨p{v.idx}, {v.ptrAlign}, rfl, rfl, v{v.idx}, by simp [Value.noPtr]⟩"]
  out := out ++ #["  all_goals cases hk", ""]
  out

/-- The certificate file for the complete original `program` and the actual emitted
declaration plan. Native effects/costs remain derived from `program`; declaration names,
capture shapes and executable proof cliques come from the same emitter's `parts`.
`genModule` defines these declarations in namespace `ns`. -/
def emit (program : Program) (ns : String) (parts : EmitParts)
    (genModule : String) (metadata : Lean.Json) : Except String String := do
  let compiled ← (compiledGroups metadata).mapError ("compiler fixpoint metadata: " ++ ·)
  unless compiled.size == parts.declGroups.countP (·.recursive) do
    throw "compiler fixpoint metadata has missing or unexpected executable cliques"
  for group in parts.declGroups do
    if group.recursive then discard <| compiledGroupFor compiled ns group
  let funcs := program.funcs
  let memFuncs := program.memFuncs
  let concFuncs := program.concFuncs
  let declNames := parts.declNames
  let shapes := parts.shapes
  let (frag, out) := fragment program shapes
  let leanDecl (n : String) : String := (declNames.find? (·.1 == n)).map (·.2) |>.getD n
  -- The stem of every certificate name derived from a function (`air_<d>`, `<d>_step`, …): the
  -- generated name without `«»` quoting, other characters as `_`, so a suffix keeps it valid.
  let declOf (n : String) : String :=
    String.ofList ((plainName (leanDecl n)).toList.map fun c => if c.isAlphanum then c else '_')
  let airName (f : Func) := s!"air_{declOf f.name}"
  let genName (f : Func) := s!"{ns}.{leanDecl f.name}"
  let names := frag.map (·.name)
  let calling (f : Func) := (callsIn f).any names.contains
  let isMem (f : Func) := memFuncs.contains f.name
  -- The generated definition applied to `args`, as the semantics' (value, memory) at `m`: a
  -- function in `Zig.MemM` runs on `m`; a pure one leaves `m`.
  -- `head`: the function term (default: the generated definition).
  let genRes (f : Func) (args : String) (head := genName f) : String :=
    let s := sig f
    if isMem f then s!"(fun r => ({s.ret.enc "r.1"}, r.2)) <$> ({head} {args}).run m"
    else s!"(fun {s.ret.binder} => ({s.ret.enc "v"}, m)) <$> {head} {args}"
  let mut lines : Array String := #[
    "-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.",
    (if frag.any (isView · memFuncs) then "import Air2Lean.SemView" else "import Air2Lean.Sem"),
    s!"import {genModule}", "",
    -- One simp set serves every function: an argument a function does not need is expected.
    "set_option linter.unusedSimpArgs false", "",
    s!"namespace {ns}.AirCert", "", "open Air2Lean Air2Lean.Sem", "",
    "/-! Certified: " ++ (if frag.isEmpty then "(none)" else ", ".intercalate (frag.toList.map (s!"`{·.name}`"))),
    "", "Outside the certificate fragment:", ""]
  for (n, r) in out do lines := lines.push s!"* `{n}`: {r}"
  if out.isEmpty then lines := lines.push "(none)"
  lines := lines ++ #["-/", ""]
  if frag.isEmpty then
    lines := lines.push s!"end {ns}.AirCert"
    return "\n".intercalate lines.toList ++ "\n"
  -- Reify the complete original input, including unsupported functions. Its graph and
  -- effects are never recomputed from the smaller certificate fragment.
  for f in funcs, index in [:funcs.size] do
    let source ← (Reify.func f).mapError (s!"source-program quotation for {f.name}: " ++ ·)
    lines := lines.push s!"def source_{index} : _root_.Air2Lean.Func :=\n{source}\n"
  let models ← Reify.models program.models
  let sources := (Array.range funcs.size).map fun index => s!"source_{index}"
  lines := lines.push s!"/-- The complete original translation input, before certificate selection. -/\ndef program : _root_.Air2Lean.Program := ⟨{arr id sources}, {models}⟩\n"
  for f in frag do
    let some index := funcs.findIdx? (·.name == f.name)
      | throw s!"certificate function {f.name} is absent from its original program"
    lines := lines.push s!"/-- The decoded canonical AIR of `{f.name}` in the original program. -/"
    lines := lines.push s!"def {airName f} : _root_.Air2Lean.Func := source_{index}\n"
    lines := lines.push s!"theorem lookup_{declOf f.name} : program.lookup {str f.name} = some {airName f} := rfl"
    lines := lines.push s!"theorem policy_{declOf f.name} : program.ticked {airName f}.name = {bool (program.ticked f.name)} := by decide +kernel"
    lines := lines.push s!"theorem entry_{declOf f.name} : program.entryTicked {airName f}.name = {bool (program.entryTicked f.name)} := by decide +kernel\n"
  -- Functions with a viewed slice parameter, and the program of the others.
  let views := frag.filter (isView · memFuncs)
  let frag := frag.filter (!isView · memFuncs)
  let callees := ((frag ++ views).flatMap callsIn).toList.eraseDups
  let mut panicLemmas : Array (String × String) := #[]
  for (n, k) in callees.toArray.zipIdx do
    let rhs := match panicCallee? n with | some e => s!"some {e}" | none => "none"
    lines := lines.push s!"theorem callee_{k} : panicOf? {str n} = {rhs} := rfl"
    panicLemmas := panicLemmas.push (n, s!"callee_{k}")
  lines := lines.push ""
  let calleeLemmasOf (f : Func) := (panicLemmas.filter fun (n, _) => (callsIn f).contains n).toList.map (·.2)
  for f in views do
    lines := lines ++ viewCert f ((shapes.find? (·.1 == f.name)).map (·.2) |>.getD default) ns (genName f)
      (airName f) (declOf f.name) (calleeLemmasOf f)
  unless views.isEmpty do
    lines := lines.push "/-- The functions certified through a view of their slices, by fully qualified name. -/"
    lines := lines.push ("def views : Table := [\n" ++
      ",\n".intercalate (views.toList.map fun f => s!"  {str f.name}") ++ "]\n")
  if frag.isEmpty then
    lines := lines.push s!"end {ns}.AirCert"
    return "\n".intercalate lines.toList ++ "\n"
  lines := lines.push "/-- The certified functions, by fully qualified name. -/"
  lines := lines.push ("def table : Table := [\n" ++
    ",\n".intercalate (frag.toList.map fun f => s!"  {str f.name}") ++ "]\n")
  lines := lines.push "/-- The generated definitions as a call oracle (arguments decoded by type). -/"
  lines := lines.push "def gen : Oracle"
  for f in frag do
    let s := sig f
    let args := s.ps.map fun (i, sc) => sc.dec i
    let app := s!"(fun {s.ret.binder} => {s.ret.enc "v"}) <$> {genName f} {" ".intercalate args.toList}"
    lines := lines.push s!"  | {str f.name}, args =>\n    {if isMem f then app else s!"StateT.lift ({app})"}"
  lines := lines.push "  | _, _ => StateT.lift stuck\n"
  let mut fixes : Array String := #[]
  for f in frag do
    let d := declOf f.name
    let s := sig f
    let calls := calling f
    let oracle := if calls then "gen" else "call"
    let callBinder := if calls then "" else "(call : Oracle) "
    let calleeLemmas := calleeLemmasOf f
    let simpSet := ", ".intercalate
      ([airName f, "air_sem", s!"policy_{d}", s!"entry_{d}"] ++
        calleeLemmas ++ (if calls then ["gen"] else []))
    let what := if calls then ", with the generated program answering its calls,"
      else " (under any call oracle)"
    let stmt := #[
      s!"/-- `{f.name}`: the AIR semantics of the decoded function{what} equals the generated definition. -/",
      s!"theorem {d}_step {callBinder}{s.binders} (m : Zig.Mem) :",
      s!"    (execFunc program {oracle} {airName f} [{s.encArgs}]).run m =",
      s!"      {genRes f s.argNames} := by",
      s!"  conv => rhs; rw [{genName f}]"]
    let sh := (shapes.find? (·.1 == f.name)).map (·.2) |>.getD default
    if (allInsts f.body).any (·.op matches .loop _) then
      let (loopLines, stepProof) := loopCert f sh ns (genName f) (airName f) d calls calleeLemmas
        { mem := isMem f }
      lines := lines ++ loopLines ++ stmt ++ stepProof ++ #[""]
    else
      lines := lines ++ stmt ++ #[s!"  simp only [{simpSet}]", ""]
    let fix := #[
      s!"theorem {d}_fix (args : List Value)",
      s!"    (h : argsOk {airName f} {airName f}.params.toList args = true) :",
      s!"    execFunc program gen {airName f} args = gen {str f.name} args := by"] ++
      invertArgs f (airName f) "  "
    let stepArgs := " ".intercalate (s.ps.toList.map fun (i, sc) => sc.decVar i)
    let fix := fix ++ #["  funext m",
      s!"  show (execFunc program gen {airName f} _).run m = (gen _ _).run m",
      s!"  rw [{d}_step {if calls then "" else "gen "}{stepArgs}]",
      "  simp only [gen, air_sem]", ""]
    lines := lines ++ fix
    fixes := fixes.push s!"(by intro f args hp ha; rw [lookup_{d}] at hp; cases hp; exact {d}_fix args ha)"
  lines := lines ++ #[
    "/-- The generated program satisfies every certified function's AIR equation. -/",
    "theorem gen_fixpoint : Fixpoint program gen table :=",
    s!"  ⟨{", ".intercalate (fixes.toList ++ ["trivial"])}⟩", "",
    "/-- The AIR semantics restricted to the certified names, using the complete original",
    "program's lookup and cost policy, is below the",
    "generated program: every terminating AIR behaviour is the generated definition's. -/",
    "theorem run_le_gen : Lean.Order.PartialOrder.rel (runOn program table) gen :=",
    "  run_le_of_table gen_fixpoint", ""]
  -- Exact agreement without calls: one unfolding of `run`.
  for f in frag do
    if calling f then continue
    let d := declOf f.name
    let s := sig f
    lines := lines ++ #[
      s!"/-- `{f.name}` makes no certified call: its AIR semantics equals the generated definition. -/",
      s!"theorem {d}_run {s.binders} (m : Zig.Mem) :",
      s!"    (runOn program table {str f.name} [{s.encArgs}]).run m =",
      s!"      {genRes f s.argNames} := by",
      s!"  rw [runOn_of_lookup (by decide) lookup_{d}]",
      s!"  exact {d}_step _ {s.argNames} m", "",
      s!"theorem {d}_complete {s.binders} (m : Zig.Mem) :",
      s!"    Lean.Order.PartialOrder.rel ({genRes f s.argNames})",
      s!"      ((runOn program table {str f.name} [{s.encArgs}]).run m) :=",
      s!"  rel_of_eq ({d}_run {s.argNames} m).symm", ""]
  -- Soundness is independent of the generated induction grouping.
  for f in frag.filter calling do
    let d := declOf f.name
    let s := sig f
    lines := lines ++ #[
      s!"/-- `{f.name}`: every terminating AIR run is the generated definition's. -/",
      s!"theorem {d}_sound {s.binders} (m : Zig.Mem) :",
      s!"    Lean.Order.PartialOrder.rel ((runOn program table {str f.name} [{s.encArgs}]).run m)",
      s!"      ({genRes f s.argNames}) := by",
      s!"  have h : Lean.Order.PartialOrder.rel ((runOn program table {str f.name} [{s.encArgs}]).run m)",
      s!"      ((gen {str f.name} [{s.encArgs}]).run m) := run_le_gen {str f.name} [{s.encArgs}] m",
      "  simp only [gen, air_sem] at h", "  exact h", ""]
  let completion (decl : CompleteDecl) := if decl.loop.isSome then
      s!"completeHelpers.{decl.emitted.name}_complete" else s!"{declOf decl.source.name}_complete"
  let ordinary (emitted : EmittedDecl) : CompiledMember :=
    { name := compiledName ns emitted, params := emitted.params.map (fun (name, _) => (name, "default")),
      fixed := Array.replicate emitted.params.size none }
  let mut complete : Array (CompleteDecl × String × String) := #[]
  let declarations := parts.declGroups.flatMap (·.members)
  for f in frag.filter (!calling ·) do
    let some emitted := declarations.find? (·.id == .function f.name)
      | throw s!"certified function has no actual emitted declaration: {f.name}"
    let decl ← completeDecl frag shapes ns emitted (ordinary emitted)
    complete := complete.push (decl, s!"{ns}.{emitted.name}", completion decl)
  for group in parts.declGroups do
    -- The fragment remains source-selected and call-closed, but an admitted proof clique is
    -- consumed whole. Helpers and members with no direct source call are never filtered out.
    unless group.members.any (fun decl => frag.any (fun f => f.name == decl.id.sourceName && calling f)) do
      continue
    let compiler? ← if group.recursive then pure (some (← compiledGroupFor compiled ns group)) else pure none
    let members ← match compiler? with
      | none => group.members.mapM fun decl => completeDecl frag shapes ns decl (ordinary decl)
      | some cg => cg.members.mapM fun member => do
        let some decl := group.members.find? (fun decl => compiledName ns decl == member.name)
          | throw "actual proof clique member disappeared"
        completeDecl frag shapes ns decl member
    let ids := members.map (·.emitted.id)
    let externals := (members.flatMap (·.emitted.refs)).filter (!ids.contains ·)
    -- Keep the existing unsupported memory/source-arity/callee boundaries. Capture count is
    -- not a new bound: helper admissibility uses the generic application rule above.
    if members.any (fun m => m.source.params.size > 4 || isMem m.source) ||
        !externals.all (fun id => complete.any (fun (decl, _, _) => decl.emitted.id == id)) then
      for member in members do
        if member.loop.isNone && calling member.source then
          lines := lines.push s!"-- `{member.source.name}`: no completeness theorem (arity, memory or callee outside this generator's scheme)."
      continue
    for target in members do
      if target.loop.isNone && !calling target.source then continue
      let d := declOf target.source.name
      let s := sig target.source
      let native := s!"{ns}.{target.emitted.name}"
      let targetArgs := if target.loop.isSome then target.values else s.ps.map (fun (i, _) => s!"p{i}")
      let targetExtra := target.extraNames
      let mut fixed := Array.replicate (compiler?.map (·.numFixed) |>.getD 0) ""
      let mut fixedBindings := #[]
      for index in [:target.compiler.fixed.size] do
        if let some k := target.compiler.fixed[index]! then
          let value ← if let some i := target.positions.idxOf? index then pure targetArgs[i]!
            else if target.statePosition == some index then pure "s" else throw "unmapped target fixed parameter"
          fixedBindings := fixedBindings.push s!"  let fixed{k} := {value}"
          fixed := fixed.set! k s!"fixed{k}"
      let motive ← target.motive fixed ns (airName target.source) d
      let partialTerm ← target.partialTerm fixed ns
      if target.loop.isSome then
        lines := lines ++ #[
          s!"/-- One generated helper iteration is below its canonical AIR iteration. -/",
          s!"private theorem {completion target} {target.binders} {target.extraBinders ns} :",
          s!"    Lean.Order.PartialOrder.rel ({target.fullLeft native d}) {target.right (airName target.source)} := by"]
      else
        lines := lines ++ #[
          s!"/-- `{target.source.name}`: the generated definition terminates only as the AIR does: it is below `run`. -/",
          s!"theorem {d}_complete {s.binders} (m : Zig.Mem) :",
          s!"    Lean.Order.PartialOrder.rel ({genRes target.source s.argNames})",
          s!"      ((runOn program table {str target.source.name} [{s.encArgs}]).run m) := by"]
      lines := lines ++ fixedBindings
      lines := lines.push s!"  have h_complete : ({motive}) ({partialTerm}) := by"
      let step (decl : CompleteDecl) (role? : Option CompiledStep) : Except String (Array String) := do
        let sd := declOf decl.source.name
        let mut out := #[]
        let mut available := complete.filter (fun (other, _, _) =>
          decl.emitted.refs.contains other.emitted.id && !ids.contains other.emitted.id)
        if let some role := role? then
          let binders := (role.approxs.map (fun a => s!"g_{a.index}")).toList ++
            (role.ihs.map (fun h => s!"hg_{h.approxIndex}")).toList
          unless binders.isEmpty do out := out.push s!"    intro {" ".intercalate binders}"
          for approx in role.approxs do
            let some member := members.find? (·.compiler.name == approx.member) | throw "unknown retained approximation"
            let ih := s!"hg_{approx.index}"
            let head := s!"g_{approx.index}"
            out := out ++ (← member.boundAdapter fixed head ih ns (airName member.source) (declOf member.source.name))
            available := available.push (member, s!"b_{member.stem}", s!"hb_{member.stem}")
        out := out ++ (← decl.fixedIntro)
        unless role?.isSome do out := out.push s!"    conv => lhs; rw [{ns}.{decl.emitted.name}]"
        if decl.loop.isNone then
          out := out.push s!"    rw [runOn_of_lookup (by decide) lookup_{sd}]"
        for (helper, head, hyp) in available do
          if helper.loop.isSome then
            out := out ++ (← helper.loopClosure head hyp ns (genName helper.source) (airName helper.source) (declOf helper.source.name))
        let definitions := ["air_sem", "-map_bind", airName decl.source, s!"policy_{sd}", s!"entry_{sd}"] ++
          calleeLemmasOf decl.source ++
          (if decl.loop.isSome || !decl.shape.loops.isEmpty then [s!"enc_{sd}"] else []) ++
          (available.toList.filterMap fun (member, head, _) => if head == s!"b_{member.stem}" then some head else none) ++
          ["Env.val", "Frame.cell"]
        let simpSet := ", ".intercalate definitions
        let simplify := s!"simp (config := \{ failIfUnchanged := false }) only [{simpSet}]"
        out := out ++ #[s!"    {simplify}", "    all_goals repeat (first", "      | exact Lean.Order.PartialOrder.rel_refl"]
        for (helper, _, _) in available do
          if let some info := helper.loop then
            let nproofs := info.caps.size + info.cells.size + (registers helper.source).size
            let proofs := " ".intercalate (List.replicate nproofs s!"(by first | assumption | rfl | simp only [{simpSet}])")
            let args := " ".intercalate (List.replicate helper.emitted.params.size "_")
            out := out.push <|
              s!"      | (refine map_bind_le_ok _ _ (lu_{helper.stem} _ _ _ _ rfl {proofs} _) _ " ++
              s!"(fun r hr => lx_{helper.stem} {args} _ r hr) ?_\n" ++
              "         rintro ⟨e, s⟩ ⟨h1, h2⟩\n" ++
              s!"         cases e <;> simp (config := \{ failIfUnchanged := false }) only [{simpSet}, Exit.again, exitOk] at h1 h2 ⊢)"
        for (callee, _, hyp) in available do
          if callee.loop.isNone then
            let args := " ".intercalate (List.replicate callee.emitted.params.size "_")
            out := out.push s!"      | exact {hyp} {args} _"
            let split := match callee.source.types[callee.source.ret]? with
              | some (.optional _) | some (.errorUnion ..) => s!"cases r <;> {simplify}"
              | _ => simplify
            out := out.push <|
              s!"      | (refine map_bind_le_ok _ _ ({hyp} {args} _) (fun _ => True) (by intro; trivial) ?_\n" ++
              s!"         intro r _\n         {split})"
        out := out ++ #[
          "      | (refine map_bind_le_ok _ _ Lean.Order.PartialOrder.rel_refl (fun _ => True) (by intro; trivial) ?_",
          s!"         intro r _; {simplify})",
          s!"      | (split <;> simp_all (config := \{ failIfUnchanged := false }) only [{simpSet}])",
          "      | (simp only [map_bind]; apply Lean.Order.MonoBind.bind_mono_right; intro)",
          "      | (apply Lean.Order.MonoBind.bind_mono_right; intro))"]
        pure out
      match compiler? with
      | none => lines := lines ++ (← step target none)
      | some cg =>
        let some induction := cg.inductions.find? (·.target == target.compiler.name)
          | throw "missing actual target induction theorem"
        let motiveArgs ← induction.members.mapM fun role => do
          let some member := members.find? (·.compiler.name == role.member) | throw "unknown compiler motive member"
          pure s!"({role.motive.name} := {← member.motive fixed ns (airName member.source) (declOf member.source.name)})"
        let fixedArgs := induction.fixed.map fun f => s!"({f.name} := {fixed[f.groupIndex]!})"
        lines := lines.push s!"    apply {induction.name} {" ".intercalate (fixedArgs ++ motiveArgs).toList}"
        let goals := ((induction.members.map fun role => (role.adm.index, role.member, false)) ++
          (induction.members.map fun role => (role.step.index, role.member, true))).qsort (fun a b => a.1 < b.1)
        for (_, memberName, isStep) in goals do
          let some member := members.find? (·.compiler.name == memberName) | throw "unknown actual induction goal"
          let some role := induction.members.find? (·.member == memberName) | throw "missing actual induction role"
          let body ← if isStep then step member (some role.step) else member.admissibility
          lines := lines.push "    ·"
          lines := lines ++ body.map ("  " ++ ·)
      lines := lines ++ #[s!"  exact h_complete {" ".intercalate targetArgs.toList} {targetExtra} (by simp)", ""]
    for member in members do
      complete := complete.push (member, s!"{ns}.{member.emitted.name}", completion member)
      if member.loop.isNone && calling member.source then
        let f := member.source
        let d := declOf f.name
        let s := sig f
        lines := lines ++ #[
          s!"/-- `{f.name}`: its AIR semantics equals the generated definition. -/",
          s!"theorem {d}_eq {s.binders} (m : Zig.Mem) :",
          s!"    (runOn program table {str f.name} [{s.encArgs}]).run m =",
          s!"      {genRes f s.argNames} :=",
          s!"  Lean.Order.PartialOrder.rel_antisymm ({d}_sound {s.argNames} m) ({d}_complete {s.argNames} m)", ""]
  lines := lines.push s!"end {ns}.AirCert"
  pure ("\n".intercalate lines.toList ++ "\n")

end Air2Lean.Certificate
