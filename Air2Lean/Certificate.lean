import Air2Lean.Air.Op
import Air2Lean.Emit
import Air2Lean.Sem

/-!
# AIR semantics certificates (`--air-certificate`)

For each function in the certificate fragment (`fragmentReason?`), writes a Lean file with

* the decoded, canonical `Func` the translator read, as a Lean term (`printFunc`);
* a theorem that `Air2Lean.Sem.execFunc` of that `Func` equals the generated definition
  (`docs/air-semantics.md`), proved by the kernel when the file is compiled.

The certificate is a separate file: the ordinary translation output does not change. Nothing
here is trusted for soundness except `printFunc` (the printed term must be the decoded `Func`;
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
  | .sliceConst t p l => s!"(.sliceConst {t} {printVal p} {printVal l})"

def arithOp : ArithOp → String | .add => ".add" | .sub => ".sub" | .mul => ".mul"
def mode : Mode → String | .checked => ".checked" | .wrap => ".wrap" | .sat => ".sat"
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
  | .intCast a => some s!"(.intCast {printVal a})"
  | .trunc a => some s!"(.trunc {printVal a})"
  | .alloc => some ".alloc"
  | .load p => some s!"(.load {printVal p})"
  | .fieldPtr b idx => some s!"(.fieldPtr {printVal b} {idx})"
  | .bitcast a => some s!"(.bitcast {printVal a})"
  | .store p v => some s!"(.store {printVal p} {printVal v})"
  | .ptrAdd sub p n => some s!"(.ptrAdd {bool sub} {printVal p} {printVal n})"
  | .elemPtr p i => some s!"(.elemPtr {printVal p} {printVal i})"
  | .ptrElemVal p i => some s!"(.ptrElemVal {printVal p} {printVal i})"
  | .sliceElemVal sl i => some s!"(.sliceElemVal {printVal sl} {printVal i})"
  | .sliceLen sl => some s!"(.sliceLen {printVal sl})"
  | .slicePtr sl => some s!"(.slicePtr {printVal sl})"
  | .call c args => some s!"(.call {printVal c} {arr printVal args})"
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

/-- The whole decoded `Func` as a Lean term, or `none` outside the printable fragment. -/
def printFunc (f : Func) : Option String := do
  let body ← printBody f.body
  pure <| "{ zigVersion := " ++ str f.zigVersion ++ ", name := " ++ str f.name ++
    ",\n  params := " ++ arr toString f.params ++ ", ret := " ++ toString f.ret ++
    ",\n  types := " ++ arr printTy f.types ++
    ",\n  layouts := " ++ arr printLayout f.layouts ++
    ",\n  globals := " ++ arr printGlobal f.globals ++
    ",\n  errorSetBits := " ++ toString f.errorSetBits ++
    ",\n  body := " ++ body ++ " }"


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
    else if Sem.plainSlice f t then some {
      lean := "Zig.Slice", enc := fun v => s!"(Value.slice {v})",
      dec := fun i => s!"((args.getD {i} .void).toSlice)",
      inv := "valOk_slice", decVar := fun i => s!"v{i}.toSlice",
      decT := fun t => s!"(Value.toSlice {t})" }
    else none
  | _ => none

def retScalar? (f : Func) (t : TyId) : Option Scalar :=
  match f.types[t]? with
  | some .void => some {
      lean := "Unit", enc := fun _ => "Value.void", dec := fun _ => "()",
      inv := "valOk_void", decVar := fun _ => "()", ignoresValue := true }
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

/-- A value type that memory holds in the fragment: an integer, `bool` or plain pointer. -/
def memValTy (f : Func) (t : TyId) : Bool := (scalar? f t).isSome

/-- An operand the certificate fragment reads: an instruction, an integer, `bool` or `void`. -/
def simpleVal (f : Func) : Val → Bool
  | .inst _ | .bool _ | .void => true
  | .int t _ => isIntTy f t
  | _ => false

partial def allInsts (body : Array Inst) : Array Inst :=
  body.flatMap fun i => #[i] ++ match i.op with
    | .block b | .loop b => allInsts b
    | .condBr _ t e => allInsts t ++ allInsts e
    | .switchBr _ cs e => allInsts e ++ cs.flatMap (allInsts ·.body)
    | _ => #[]

/-- Why one instruction is outside the certificate fragment (nested bodies are checked by
`localReason`, which visits every instruction). -/
def instReason (f : Func) (tyOfInst : InstId → Option TyId) (forLen : Array InstId) (i : Inst) :
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
    | .inst x => (tyOfInst x).filter (Sem.plainSlice f)
    | _ => none
  let sliceVal (v : Val) : Except String TyId := do
    let some t := sliceOf v | throw s!"inst {i.id}: a slice outside the fragment"
    pure t
  -- 64-bit pointers: the translator's `Ptr.elem` (other widths use `Ptr.elemOf`).
  let ptr64 (t : TyId) : Bool := (f.layouts[t]?.bind (·.size)) == some 8
  match i.op with
  | .arg _ | .line _ | .dbg .. | .unreach | .trap | .block _ => pure ()
  | .arith _ _ a b | .div _ a b | .minMax _ a b | .bit _ a b => do intRes; vals [a, b]
  | .cmp _ a b => do
    unless (!(a matches .bool _) && typed (isIntTy f) a) || ((ptrOf a).isSome && (ptrOf b).isSome) do
      throw s!"inst {i.id}: a comparison of non-integers"
    vals [a, b]
  | .load p => do
    let _ ← ptrVal p
    unless memValTy f i.ty do throw s!"inst {i.id}: a load of a type outside the fragment"
  | .store p v => do
    let _ ← ptrVal p
    vals [v]
    unless typed (memValTy f) v do throw s!"inst {i.id}: a store of a type outside the fragment"
  | .fieldPtr b idx => do
    let t ← ptrVal b
    unless f.plainPtr i.ty && (f.fieldOffset? t idx).isSome do
      throw s!"inst {i.id}: a field pointer outside the fragment"
  | .bitcast a => do
    let _ ← ptrVal a
    unless f.plainPtr i.ty do throw s!"inst {i.id}: a bitcast outside the fragment"
  | .ptrAdd _ p n | .elemPtr p n => do
    unless (sliceOf p).isSome do let _ ← ptrVal p
    vals [n]
    unless typed (isIntTy f) n && f.plainPtr i.ty && ptr64 i.ty do
      throw s!"inst {i.id}: pointer arithmetic outside the fragment"
  | .ptrElemVal p n => do
    let _ ← ptrVal p
    vals [n]
    unless typed (isIntTy f) n && memValTy f i.ty do throw s!"inst {i.id}: an item load outside the fragment"
  | .sliceElemVal sl n => do
    let _ ← sliceVal sl
    vals [n]
    unless typed (isIntTy f) n && memValTy f i.ty do throw s!"inst {i.id}: an item load outside the fragment"
  | .sliceLen sl => do
    let _ ← sliceVal sl
    if forLen.contains i.id then throw s!"inst {i.id}: a `for` length check (`Zig.forLen`, not an AIR operation)"
  | .slicePtr sl => do
    let _ ← sliceVal sl
    unless f.plainPtr i.ty do throw s!"inst {i.id}: a slice pointer outside the fragment"
  | .slice .. => throw s!"inst {i.id}: a slicing (the translator checks its bounds, which no AIR operation does)"
  | .boolAnd a b | .boolOr a b => vals [a, b]
  | .not a => vals [a]
  | .intCast a | .trunc a => do intRes; vals [a]
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

def callsIn (f : Func) : Array String :=
  (allInsts f.body).filterMap fun i => match i.op with
    | .call (.func n _ _) _ => some n
    | _ => none

/-- The local reason a function is outside the fragment, or its non-panic callees. -/
def localReason (f : Func) (mem : Bool) (forLen : Array InstId) : Except String (Array String) := do
  for p in f.params do
    unless (scalar? f p).isSome do throw "a parameter that is not an integer, bool, plain pointer or slice"
    if !mem && Sem.plainSlice f p then
      throw "a slice parameter of a function without memory (an `Array`; docs/air-semantics.md §Next fragments)"
  unless (retScalar? f f.ret).isSome do
    throw "a return type that is not an integer, bool, plain pointer or void"
  let insts := allInsts f.body
  let tys : Std.HashMap InstId TyId := insts.foldl (fun m i => m.insert i.id i.ty) {}
  let tyOfInst (x : InstId) := tys[x]?
  for i in insts do instReason f tyOfInst forLen i
  unless (printFunc f).isSome do throw "an instruction the certificate printer does not print"
  pure ((callsIn f).filter fun n => (panicCallee? n).isNone)

/-! ## Locals and loops -/

/-- The operands of a fragment instruction (not its nested bodies). -/
def opVals : Op → List Val
  | .arith _ _ a b | .div _ a b | .minMax _ a b | .bit _ a b | .cmp _ a b | .boolAnd a b
  | .boolOr a b | .store a b => [a, b]
  | .not a | .intCast a | .trunc a | .br _ a | .ret a | .bitcast a | .fieldPtr a _ | .load a
  | .condBr a _ _ => [a]
  | .call c args => c :: args.toList
  | .switchBr v cs _ =>
    v :: cs.toList.flatMap fun c => c.items.toList ++ c.ranges.toList.flatMap fun (a, b) => [a, b]
  | _ => []

def instIdsOf (vs : List Val) : List InstId := vs.filterMap fun | .inst k => some k | _ => none

/-- Every loop with its enclosing blocks and loops, outer loops first. -/
partial def loopCtx (bs ls : List InstId) (body : Array Inst) :
    Array (Inst × Array Inst × List InstId × List InstId) :=
  body.flatMap fun i => match i.op with
    | .block b => loopCtx (i.id :: bs) ls b
    | .loop b => #[(i, b, bs, ls)] ++ loopCtx bs (i.id :: ls) b
    | .condBr _ t e => loopCtx bs ls t ++ loopCtx bs ls e
    | .switchBr _ cs e => cs.flatMap (loopCtx bs ls ·.body) ++ loopCtx bs ls e
    | _ => #[]

/-- The registers (`Sem.regAlloc`) of `f`. -/
def registers (f : Func) : Array InstId :=
  (allInsts f.body).filterMap fun i => if (i.op matches .alloc) && Sem.regAlloc f i.id then some i.id else none

/-- The registers a body reads or writes. -/
def cellsIn (regs : Array InstId) (body : Array Inst) : Array InstId :=
  ((allInsts body).toList.flatMap fun i => instIdsOf (opVals i.op)).eraseDups.filter regs.contains |>.toArray
    |>.qsort (· < ·)

/-- The pointee type of an `alloc`. -/
def allocChild (f : Func) (a : InstId) : Option TyId :=
  ((allInsts f.body).find? (·.id == a)).bind fun i => Sem.pointee? f i.ty

/-- Why `f`'s locals or loops are outside the certificate fragment. `sh`: its emitted shape. -/
def localsReason (f : Func) (sh : CertShape) (mem : Bool) : Except String Unit := do
  let insts := allInsts f.body
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
  match top.findIdx? (·.id == escTop.back?.getD 0) with
  | some j =>
    unless (top.extract 0 j).all (fun i => i.op matches .arg _ | .line _ | .dbg .. | .alloc) do
      throw "an escaping local allocated after an instruction with effects"
  | none => pure ()
  -- A register starts undefined; the translator's field starts at its default.
  for a in regs do
    let some j := top.findIdx? (·.id == a) | throw s!"inst {a}: a register local inside a nested body"
    let next := (top.extract (j + 1) top.size).find? fun i => !(i.op matches .line _ | .dbg ..)
    match (next.map (·.op) : Option Op) with
    | some (.store (.inst b) v) =>
      unless b == a && !(v matches .undef _) do throw s!"inst {a}: a register local read before it is set"
    | _ => throw s!"inst {a}: a register local read before it is set"
    unless ((allocChild f a).bind (scalar? f)).isSome do
      throw s!"inst {a}: a register local of a type outside the fragment"
  for (k, t) in sh.blockTys do
    if sh.brT.contains k && !(f.types[t]? matches some .void) && (scalar? f t).isNone then
      throw s!"inst {k}: a block value outside the fragment"
  if hasLoop && !mem then throw "a loop in a function without memory (`Zig.M`)"
  -- An inner loop's generated state keeps the escaping locals' fields of the outer state, which
  -- the semantics' frame does not name.
  if !sh.escaping.isEmpty && (loopCtx [] [] f.body).any (fun (_, _, _, ls) => !ls.isEmpty) then
    throw "a nested loop in a function with escaping locals"
  let tys : Std.HashMap InstId TyId := insts.foldl (fun m i => m.insert i.id i.ty) {}
  for (l, caps) in sh.loops do
    let some li := insts.find? (·.id == l) | throw s!"inst {l}: a loop the translator does not name"
    let body := match li.op with | .loop b => b | _ => #[]
    let defined := (allInsts body).map (·.id)
    let free := ((allInsts body).toList.flatMap fun i => instIdsOf (opVals i.op)).eraseDups.filter (!defined.contains ·)
    for k in free do
      unless caps.any (·.1 == k) || regs.contains k do throw s!"inst {l}: a loop reads a value it does not capture"
    for (k, _) in caps do
      unless (tys[k]?.bind (scalar? f)).isSome do throw s!"inst {l}: a loop capture outside the fragment"

/-- Split the functions into the certificate fragment (closed under direct calls) and the
others, each with a reason. -/
def fragment (funcs : Array Func) (memFuncs concFuncs : Array String)
    (shapes : Array (String × CertShape)) : Array Func × Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  let mut cands : Array (Func × Array String) := #[]
  -- A recursive function in `Zig.MemM` charges its frame to the model's stack budget
  -- (`Zig.enterFrame`, STK-01), which the semantics does not have.
  let budgeted := if memFuncs.isEmpty then #[] else (callGroups funcs).flatMap fun (members, recursive) =>
    if recursive then (members.map (·.name)).filter memFuncs.contains else #[]
  for f in funcs do
    let reason := if concFuncs.contains f.name then .error "a concurrent function (`Zig.ConcM`)"
      else if budgeted.contains f.name then
        .error "a recursive function that uses memory (stack budget `Zig.enterFrame`, STK-01)"
      else
        let sh := (shapes.find? (·.1 == f.name)).map (·.2) |>.getD default
        localReason f (memFuncs.contains f.name) sh.forLen >>= fun cs => do
          localsReason f sh (memFuncs.contains f.name)
          pure cs
    match reason with
    | .ok cs => cands := cands.push (f, cs)
    | .error e => out := out.push (f.name, e)
  let mut changed := true
  while changed do
    changed := false
    let names := cands.map (·.1.name)
    let (keep, drop) := cands.partition fun (_, cs) => cs.all names.contains
    if !drop.isEmpty then
      changed := true
      for (f, cs) in drop do
        let missing := ((cs.filter (!names.contains ·))[0]?).getD ""
        out := out.push (f.name, s!"calls `{missing}`, which is outside the fragment")
      cands := keep
  pure (cands.map (·.1), out)

/-! ## Emission -/

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

/-- The loop machinery of a function with loops (`docs/air-semantics.md` §Loops): its AIR's field
lemmas, the exit encoding, and per loop (innermost first) the one-iteration lemma, the loop
commutation, the loop's exits and the rewrite used at the loop; then the step proof. -/
def loopCert (f : Func) (sh : CertShape) (ns gen air d : String) (calls : Bool)
    (calleeLemmas : List String) : Array String × Array String := Id.run do
  let L := s!"{ns}.{sh.localsName}"
  let E := s!"{ns}.{sh.exitName}"
  let enc := s!"enc_{d}"
  let oracle := if calls then "gen" else "call"
  let callBinder := if calls then "" else "(call : Oracle) "
  let callArg := if calls then "" else "call "
  let stuckArg := if calls then "" else "(fun _ _ => StateT.lift stuck) "
  let insts := allInsts f.body
  let tys : Std.HashMap InstId TyId := insts.foldl (fun m i => m.insert i.id i.ty) {}
  let blank := (sig f).ret
  let scalarOf (k : InstId) : Scalar := ((tys[k]?).bind (scalar? f)).getD blank
  let regs := registers f
  let fieldOf (a : InstId) : String := ((sh.fields.find? (·.1 == a)).map (·.2)).getD s!"local{a}"
  let cellScalar (a : InstId) : Scalar := ((allocChild f a).bind (scalar? f)).getD blank
  -- The frame of a generated state `t`: `st` with every register's cell, written in increasing
  -- id order (`Frame.setCell_comm`'s normal form). The escaping locals' pointers are in the
  -- environment, and a loop does not change the frame's blocks.
  let frameOf (st t : String) : String :=
    (regs.qsort (· < ·)).foldl (init := st) fun acc a =>
      s!"(Frame.setCell {acc} {a} (some {(cellScalar a).enc s!"{t}.{fieldOf a}"}))"
  -- The generated state of a frame and an environment.
  let stateOf (st : String) : String :=
    let fs := (regs.map fun a => s!"{fieldOf a} := {(cellScalar a).decT s!"({st}.cell {a})"}") ++
      sh.escaping.map fun e => s!"{fieldOf e} := Value.toPtr (env.val {e})"
    if fs.isEmpty then s!"(default : {L})"
    else "{ (default : " ++ L ++ ") with " ++ ", ".intercalate fs.toList ++ " }"
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
  let baseSet := fieldLemmas ++ ["air_sem", enc] ++ calleeLemmas ++ (if calls then ["gen"] else [])
  -- The tactic that closes a normalized step: equal binds, and after a loop a case split on its
  -- exit, restricted to the exits the loop has (`bind_congr_ok`).
  let close (loops : List (InstId × Nat)) (set : List String) : Array String :=
    let set := ", ".intercalate (set ++ ["Exit.again", "exitOk"])
    #["  all_goals repeat (first", "    | rfl"] ++
      (loops.toArray.map fun (n, nfree) =>
        s!"    | (refine bind_congr_ok _ _ (fun r hr => {d}_loop{n}_exits {" ".intercalate (List.replicate nfree "_")} _ _ r hr) ?_\n" ++
        "       rintro ⟨⟨e, s⟩, m⟩ ⟨h1, h2⟩\n" ++
        "       cases e <;> simp (config := { failIfUnchanged := false }) only [" ++ set ++ "] at h1 h2 ⊢)") ++
      #["    | (refine bind_congr fun _ => ?_))"]
  let ctxs := (loopCtx [] [] f.body).reverse
  let mut done : Array (InstId × Nat) := #[]
  for (li, body, bs, ls) in ctxs do
    let n := li.id
    let caps := ((sh.loops.find? (·.1 == n)).map (·.2)).getD #[]
    let cells := cellsIn regs body
    let B := (printBody body).getD "#[]"
    let xs := caps.map fun (k, _) => s!"x{k}"
    let xBinders := " ".intercalate (caps.toList.map fun (k, _) => s!"(x{k} : {(scalarOf k).lean})")
    let hyps (val : InstId → String) := " ".intercalate
      ((caps.toList.map fun (k, _) => s!"(h{k} : env {k} = some ({tys[k]?.getD 0}, {(scalarOf k).enc (val k)}))") ++
        cells.toList.map fun a => s!"(h{a} : env {a} = some ({tys[a]?.getD 0}, .cell {a}))")
    let hNames := " ".intercalate ((caps.toList.map fun (k, _) => s!"h{k}") ++ cells.toList.map fun a => s!"h{a}")
    let app (args : Array String) := s!"{gen}.loop{n}{String.join (args.toList.map (" " ++ ·))}"
    let again := s!"{gen}.again{n}"
    let F := frameOf
    -- Inner loops of this body: their rewrites and exits.
    let inner := done.filter fun (k, _) => (allInsts body).any (·.id == k)
    let innerSet := inner.toList.map fun (k, _) => s!"{d}_loop{k}"
    let bodySet := ", ".intercalate (baseSet ++ (caps.toList.map fun (k, _) => s!"h{k}") ++
      (cells.toList.map fun a => s!"h{a}") ++ innerSet ++ ["Env.val", "Frame.cell"])
    out := out ++ #[
      s!"theorem {d}_loop{n}_body {callBinder}(args : List Value) (env : Env) (st : Frame) {xBinders}",
      s!"    {hyps (s!"x{·}")} (s : {L}) (m : Zig.Mem) :",
      s!"    ((execBody ⟨{air}, args, {oracle}⟩ (Array.toList {B}) env).run {F "st" "s"}).run m =",
      s!"      ((fun r => ({enc} r.1, {F "st" "r.2"})) <$> ({app xs}).run s).run m := by",
      s!"  conv => rhs; rw [{gen}.loop{n}]",
      s!"  simp only [{bodySet}]"] ++
      close inner.toList (baseSet ++ innerSet ++ ["Env.val", "Frame.cell"]) ++ #["",
      s!"theorem {d}_loop{n}_comm {callBinder}(args : List Value) (env : Env) (st : Frame) {xBinders}",
      s!"    {hyps (s!"x{·}")} (s : {L}) :",
      s!"    (execLoop ⟨{air}, args, {oracle}⟩ {n} {B} env).run {F "st" "s"} =",
      s!"      mapRes {enc} (fun s : {L} => {F "st" "s"}) <$> (Zig.loop ({app xs}) {again}).run s := by",
      "  unfold execLoop",
      s!"  exact loop_comm _ _ (Exit.again {n}) {again} {enc} (fun s : {L} => {F "st" "s"})",
      s!"    (fun s => by funext m; exact {d}_loop{n}_body {callArg}args env st {" ".intercalate xs.toList} {hNames} s m)",
      "    (by intro e; cases e <;> rfl) s", ""]
    let canon := (caps.toList.map fun (k, _) => (k, (scalarOf k).enc s!"x{k}")) ++
      cells.toList.map fun a => (a, s!"(.cell {a})")
    let envTerm := canon.foldl (init := "(fun _ => none)") fun acc (k, v) =>
      s!"(Env.set {acc} {k} {tys[k]?.getD 0} {v})"
    let byEnv := " ".intercalate (List.replicate (caps.size + cells.size) "(by simp [env, Env.set])")
    out := out ++ #[
      s!"theorem {d}_loop{n}_exits {xBinders} (s : {L}) (m : Zig.Mem) (r : ({E} × {L}) × Zig.Mem)",
      s!"    (hr : (((Zig.loop ({app xs}) {again}).run s).run m).run = some (.ok r)) :",
      s!"    Exit.again {n} ({enc} r.1.1) = false ∧ exitOk {bs} {ls} ({enc} r.1.1) = true := by",
      s!"  let env : Env := {envTerm}",
      s!"  exact ok_transfer (F := fun s : {L} => {F "({} : Frame)" "s"})",
      s!"    ({d}_loop{n}_comm {stuckArg}[] env " ++ "{} " ++ s!"{" ".intercalate xs.toList} {byEnv} s)",
      s!"    (execLoop_ok _ {n} _ env {bs} {ls} (by simp [wfBody, wfInst, wfCases])) m r hr", ""]
    -- The rewrite at the loop: values decoded from the environment and the frame.
    let decs := caps.map fun (k, _) => (scalarOf k).decT s!"(env.val {k})"
    let hst := regs.toList.map fun a =>
        s!"(hc{a} : st.cells {a} = some {(cellScalar a).enc ((cellScalar a).decT s!"(st.cell {a})")})"
    let eqs := (regs.qsort (· < ·)).toList.map fun a => s!"Frame.setCell_eq _ _ _ hc{a}"
    out := out ++ #[
      s!"theorem {d}_loop{n} {callBinder}(args : List Value) (env : Env) (st : Frame) (B : Array Inst)",
      s!"    (hB : B = {B})",
      s!"    {hyps fun k => (scalarOf k).decT s!"(env.val {k})"}",
      s!"    {" ".intercalate hst} :",
      s!"    (execLoop ⟨{air}, args, {oracle}⟩ {n} B env).run st =",
      s!"      mapRes {enc} (fun s : {L} => {F "st" "s"}) <$>",
      s!"        (Zig.loop ({app decs}) {again}).run {stateOf "st"} := by",
      "  subst hB",
      s!"  have e : {F "st" (stateOf "st")} = st := by",
      "    dsimp only",
      s!"    rw [{", ".intercalate eqs}]",
      "  conv => lhs; rw [← e]",
      s!"  exact {d}_loop{n}_comm {callArg}args env st {" ".intercalate decs.toList} {hNames} {stateOf "st"}", ""]
    done := done.push (n, caps.size)
  let top := done.filter fun (k, _) => (ctxs.find? (·.1.id == k)).any fun (_, _, _, ls) => ls.isEmpty
  let stepSet := ", ".intercalate (baseSet ++ top.toList.map (fun (k, _) => s!"{d}_loop{k}") ++ ["Env.val", "Frame.cell"])
  let proof := #[s!"  simp only [{stepSet}]"] ++ close top.toList (baseSet ++ ["Env.val", "Frame.cell"])
  (out, proof)

/-- The certificate file for `funcs` (the translated program, emission order). `declNames`
maps each fully qualified name to its generated definition in namespace `ns`, which
`genModule` defines. `memFuncs`/`concFuncs`: the functions the translator emits in `Zig.MemM`
and `Zig.ConcM` (`memoryFunctions`, `concFunctions`). -/
def emit (funcs : Array Func) (ns : String) (declNames : Array (String × String))
    (genModule : String) (memFuncs concFuncs : Array String) (shapes : Array (String × CertShape) := #[]) :
    String := Id.run do
  let (frag, out) := fragment funcs memFuncs concFuncs shapes
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
    "import Air2Lean.Sem", s!"import {genModule}", "",
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
  for f in frag do
    lines := lines.push s!"/-- The decoded canonical AIR of `{f.name}`. -/"
    lines := lines.push s!"def {airName f} : Func :=\n{(printFunc f).getD "default"}\n"
  lines := lines.push "/-- The certified functions, by fully qualified name. -/"
  lines := lines.push ("def table : Table := [\n" ++
    ",\n".intercalate (frag.toList.map fun f => s!"  ({str f.name}, {airName f})") ++ "]\n")
  lines := lines.push "/-- The generated definitions as a call oracle (arguments decoded by type). -/"
  lines := lines.push "def gen : Oracle"
  for f in frag do
    let s := sig f
    let args := s.ps.map fun (i, sc) => sc.dec i
    let app := s!"(fun {s.ret.binder} => {s.ret.enc "v"}) <$> {genName f} {" ".intercalate args.toList}"
    lines := lines.push s!"  | {str f.name}, args =>\n    {if isMem f then app else s!"StateT.lift ({app})"}"
  lines := lines.push "  | _, _ => StateT.lift stuck\n"
  let callees := (frag.flatMap callsIn).toList.eraseDups
  let mut panicLemmas : Array (String × String) := #[]
  for (n, k) in callees.toArray.zipIdx do
    let rhs := match panicCallee? n with | some e => s!"some {e}" | none => "none"
    lines := lines.push s!"theorem callee_{k} : panicOf? {str n} = {rhs} := rfl"
    panicLemmas := panicLemmas.push (n, s!"callee_{k}")
  lines := lines.push ""
  let mut fixes : Array String := #[]
  for f in frag do
    let d := declOf f.name
    let s := sig f
    let calls := calling f
    let oracle := if calls then "gen" else "call"
    let callBinder := if calls then "" else "(call : Oracle) "
    let calleeLemmas := (panicLemmas.filter fun (n, _) => (callsIn f).contains n).toList.map (·.2)
    let simpSet := ", ".intercalate
      ([airName f, "air_sem"] ++ calleeLemmas ++ (if calls then ["gen"] else []))
    let what := if calls then ", with the generated program answering its calls,"
      else " (under any call oracle)"
    let stmt := #[
      s!"/-- `{f.name}`: the AIR semantics of the decoded function{what} equals the generated definition. -/",
      s!"theorem {d}_step {callBinder}{s.binders} (m : Zig.Mem) :",
      s!"    (execFunc {oracle} {airName f} [{s.encArgs}]).run m =",
      s!"      {genRes f s.argNames} := by",
      s!"  conv => rhs; rw [{genName f}]"]
    let sh := (shapes.find? (·.1 == f.name)).map (·.2) |>.getD default
    if (allInsts f.body).any (·.op matches .loop _) then
      let (loopLines, stepProof) := loopCert f sh ns (genName f) (airName f) d calls calleeLemmas
      lines := lines ++ loopLines ++ stmt ++ stepProof ++ #[""]
    else
      lines := lines ++ stmt ++ #[s!"  simp only [{simpSet}]", ""]
    let fix := #[
      s!"theorem {d}_fix (args : List Value)",
      s!"    (h : argsOk {airName f} {airName f}.params.toList args = true) :",
      s!"    execFunc gen {airName f} args = gen {str f.name} args := by"] ++
      invertArgs f (airName f) "  "
    let stepArgs := " ".intercalate (s.ps.toList.map fun (i, sc) => sc.decVar i)
    let fix := fix ++ #["  funext m",
      s!"  show (execFunc gen {airName f} _).run m = (gen _ _).run m",
      s!"  rw [{d}_step {if calls then "" else "gen "}{stepArgs}]",
      "  simp only [gen, air_sem]", ""]
    lines := lines ++ fix
    fixes := fixes.push s!"{d}_fix"
  lines := lines ++ #[
    "/-- The generated program satisfies every certified function's AIR equation. -/",
    "theorem gen_fixpoint : Fixpoint gen table :=",
    s!"  ⟨{", ".intercalate (fixes.toList ++ ["trivial"])}⟩", "",
    "/-- The AIR semantics of the certified program (`Sem.run`, the least fixpoint) is below the",
    "generated program: every terminating AIR behaviour is the generated definition's. -/",
    "theorem run_le_gen : Lean.Order.PartialOrder.rel (run (progOf table)) gen :=",
    "  run_le_of_table gen_fixpoint", ""]
  -- Exact agreement without calls: one unfolding of `run`.
  for f in frag do
    if calling f then continue
    let d := declOf f.name
    let s := sig f
    lines := lines ++ #[
      s!"/-- `{f.name}` makes no certified call: its AIR semantics equals the generated definition. -/",
      s!"theorem {d}_run {s.binders} (m : Zig.Mem) :",
      s!"    (run (progOf table) {str f.name} [{s.encArgs}]).run m =",
      s!"      {genRes f s.argNames} := by",
      "  rw [run_of_lookup (by rfl)]",
      s!"  exact {d}_step _ {s.argNames} m", "",
      s!"theorem {d}_complete {s.binders} (m : Zig.Mem) :",
      s!"    Lean.Order.PartialOrder.rel ({genRes f s.argNames})",
      s!"      ((run (progOf table) {str f.name} [{s.encArgs}]).run m) :=",
      s!"  rel_of_eq ({d}_run {s.argNames} m).symm", ""]
  -- With calls: soundness from the program fixpoint, completeness by fixpoint induction over
  -- the generated clique (or one unfolding, outside a clique), then equality.
  let motive (f : Func) : String :=
    let s := sig f
    s!"fun g => ∀ {s.argNames} m, Lean.Order.PartialOrder.rel ({genRes f s.argNames "g"}) " ++
      s!"((run (progOf table) {str f.name} [{s.encArgs}]).run m)"
  let mut complete : Array String := frag.filterMap fun f => if calling f then none else some f.name
  for (members, recursive) in callGroups frag do
    let calls := members.filter calling
    if calls.isEmpty then continue
    for f in calls do
      let d := declOf f.name
      let s := sig f
      lines := lines ++ #[
        s!"/-- `{f.name}`: every terminating AIR run is the generated definition's. -/",
        s!"theorem {d}_sound {s.binders} (m : Zig.Mem) :",
        s!"    Lean.Order.PartialOrder.rel ((run (progOf table) {str f.name} [{s.encArgs}]).run m)",
        s!"      ({genRes f s.argNames}) := by",
        s!"  have h : Lean.Order.PartialOrder.rel ((run (progOf table) {str f.name} [{s.encArgs}]).run m)",
        s!"      ((gen {str f.name} [{s.encArgs}]).run m) := run_le_gen {str f.name} [{s.encArgs}] m",
        "  simp only [gen, air_sem] at h",
        "  exact h", ""]
    -- Fail closed: arities without an admissibility lemma, or a callee without completeness.
    let externals := (members.flatMap callsIn).filter fun n => names.contains n && !members.any (·.name == n)
    if members.any (·.params.size > 4) || members.any isMem || !externals.all complete.contains then
      for f in calls do
        lines := lines.push s!"-- `{f.name}`: no completeness theorem (arity, memory or callee outside this generator's scheme)."
      continue
    for f in members do
      let d := declOf f.name
      -- The callee oracle: one argument per distinct certified callee.
      let callees := (callsIn f).toList.eraseDups.filter names.contains
      let calleeFuncs := callees.filterMap fun n => frag.find? (·.name == n)
      let gTy (c : Func) : String :=
        let cs := sig c
        " → ".intercalate (cs.ps.toList.map (·.2.lean) ++ [s!"Zig.Result ({cs.ret.lean})"])
      lines := lines.push s!"/-- `{f.name}`'s certified callees, answered by the given functions. -/"
      lines := lines.push s!"def calls_{d} {" ".intercalate (calleeFuncs.map fun c => s!"(g_{declOf c.name} : {gTy c})")} : Oracle"
      for c in calleeFuncs do
        let cs := sig c
        let args := cs.ps.map fun (i, sc) => sc.dec i
        lines := lines ++ #[s!"  | {str c.name}, args =>",
          s!"    if argsOk {airName c} {airName c}.params.toList args then",
          s!"      StateT.lift ((fun {cs.ret.binder} => {cs.ret.enc "v"}) <$> g_{declOf c.name} {" ".intercalate args.toList})",
          "    else StateT.lift stuck"]
      lines := lines.push "  | _, _ => StateT.lift stuck\n"
    -- One completeness theorem per member.
    let memberNames := members.map (·.name)
    for f in members do
      let d := declOf f.name
      let s := sig f
      let pre := #[
        s!"/-- `{f.name}`: the generated definition terminates only as the AIR does: it is below `run`. -/",
        s!"theorem {d}_complete {s.binders} (m : Zig.Mem) :",
        s!"    Lean.Order.PartialOrder.rel ({genRes f s.argNames})",
        s!"      ((run (progOf table) {str f.name} [{s.encArgs}]).run m) := by"]
      -- The step for member `g`, given the bound clique functions and hypotheses.
      let step (g : Func) (bound : Bool) (indent : String) : Array String := Id.run do
        let gs := sig g
        let gd := declOf g.name
        let callees := ((callsIn g).toList.eraseDups.filter names.contains).filterMap fun n => frag.find? (·.name == n)
        let fnOf (c : Func) := if bound && memberNames.contains c.name then s!"g_{declOf c.name}" else genName c
        let hypOf (c : Func) := if bound && memberNames.contains c.name then s!"hg_{declOf c.name}" else s!"{declOf c.name}_complete"
        let oracle := s!"(calls_{gd} {" ".intercalate (callees.map fnOf)})"
        let panics := ", ".intercalate (["air_sem", airName g, s!"calls_{gd}"] ++
          (callees.filter (·.name != g.name)).map airName ++
          (panicLemmas.filter fun (n, _) => (callsIn g).contains n).toList.map (·.2))
        let mut out := #[]
        if bound then
          let refs := members.filter fun c => callees.any (·.name == c.name)
          let binders := " ".intercalate (refs.toList.map fun c => s!"g_{declOf c.name} hg_{declOf c.name}")
          out := out.push s!"{indent}intro {binders} {gs.argNames} m"
        out := out ++ #[
          s!"{indent}rw [run_of_lookup (by rfl)]",
          s!"{indent}apply Lean.Order.PartialOrder.rel_trans (y := (execFunc {oracle} {airName g} [{gs.encArgs}]).run m)",
          s!"{indent}· apply rel_of_eq"]
        unless bound do out := out.push s!"{indent}  conv => lhs; rw [{genName g}]"
        out := out ++ #[
          s!"{indent}  simp only [{panics}]",
          s!"{indent}· apply execFunc_le",
          s!"{indent}  intro name args m'",
          s!"{indent}  show Lean.Order.PartialOrder.rel (({oracle} name args).run m') ((run (progOf table) name args).run m')",
          s!"{indent}  unfold calls_{gd}",
          s!"{indent}  split"]
        for c in callees do
          let cs := sig c
          out := out ++ #[s!"{indent}  · split", s!"{indent}    · rename_i h"] ++
            invertArgs c (airName c) s!"{indent}      " ++ #[
            s!"{indent}      have := {hypOf c} {" ".intercalate (cs.ps.toList.map fun (i, sc) => sc.decVar i)} m'",
            s!"{indent}      simp only [air_sem] at this ⊢",
            s!"{indent}      exact this",
            s!"{indent}    · exact Lean.Order.FlatOrder.rel.bot"]
        out := out.push s!"{indent}  · exact Lean.Order.FlatOrder.rel.bot"
        out
      if recursive then
        let motives := if members.size == 1 then s!"(motive := {motive f})"
          else " ".intercalate (members.toList.zipIdx.map fun (g, i) => s!"(motive_{i + 1} := {motive g})")
        let mut body := pre ++ #[s!"  revert {s.argNames} m", s!"  apply {genName f}.fixpoint_induct {motives}"]
        for g in members do
          let gs := sig g
          let intros := (gs.ps.toList.map fun (i, _) => s!"apply Lean.Order.admissible_pi; intro p{i}") ++
            ["apply Lean.Order.admissible_pi; intro m"]
          body := body.push s!"  · {"; ".intercalate intros}"
          body := body.push s!"    exact adm_app{gs.ps.size} _ {" ".intercalate (gs.ps.toList.map fun _ => "_")} _"
        for g in members do
          let st := step g true "    "
          body := body.push s!"  · {(st[0]!).trimLeft}"
          body := body ++ st.extract 1 st.size
        lines := lines ++ body ++ #[""]
      else
        lines := lines ++ pre ++ step f false "  " ++ #[""]
      complete := complete.push f.name
    for f in members do
      let d := declOf f.name
      let s := sig f
      lines := lines ++ #[
        s!"/-- `{f.name}`: its AIR semantics equals the generated definition. -/",
        s!"theorem {d}_eq {s.binders} (m : Zig.Mem) :",
        s!"    (run (progOf table) {str f.name} [{s.encArgs}]).run m =",
        s!"      {genRes f s.argNames} :=",
        s!"  Lean.Order.PartialOrder.rel_antisymm ({d}_sound {s.argNames} m) ({d}_complete {s.argNames} m)", ""]
  lines := lines.push s!"end {ns}.AirCert"
  pure ("\n".intercalate lines.toList ++ "\n")

end Air2Lean.Certificate
