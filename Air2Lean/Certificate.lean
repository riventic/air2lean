import Air2Lean.Air.Op
import Air2Lean.Emit

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

/-- A single or many pointer type whose accesses are ordinary: `Sem.plainPtr` (not a slice,
`volatile`, `allowzero` or a bit-pointer). -/
def plainPtrTy (f : Func) (t : TyId) : Bool :=
  match f.types[t]?, f.layouts[t]? with
  | some (.ptr size _ _), some l =>
    (size == "one" || size == "many") && !l.isVolatile && !l.allowzero && l.hostSize == 0
  | _, _ => false

def scalar? (f : Func) (t : TyId) : Option Scalar :=
  match f.types[t]? with
  | some (.int s w) => some {
      lean := s!"BitVec {w}", enc := fun v => s!"(Value.int {bool s} {w} {v})",
      dec := fun i => s!"((args.getD {i} .void).toBV {w})",
      inv := "valOk_int", decVar := fun i => s!"(v{i}.toBV {w})" }
  | some .bool => some {
      lean := "Bool", enc := fun v => s!"(Value.bool {v})",
      dec := fun i => s!"((args.getD {i} .void).toBool)",
      inv := "valOk_bool", decVar := fun i => s!"v{i}.toBool" }
  | some (.ptr ..) =>
    if plainPtrTy f t then some {
      lean := "Zig.Ptr", enc := fun v => s!"(Value.ptr {v})",
      dec := fun i => s!"((args.getD {i} .void).toPtr)",
      inv := "valOk_ptr", decVar := fun i => s!"v{i}.toPtr" }
    else none
  | _ => none

/-- The binder of a lambda over a value of this type: `_` if its encoding ignores the value. -/
def Scalar.binder (sc : Scalar) : String := if sc.enc "v" == sc.enc "w" then "_" else "v"

def retScalar? (f : Func) (t : TyId) : Option Scalar :=
  match f.types[t]? with
  | some .void => some {
      lean := "Unit", enc := fun _ => "Value.void", dec := fun _ => "()",
      inv := "valOk_void", decVar := fun _ => "()" }
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
def memValTy (f : Func) (t : TyId) : Bool :=
  isIntTy f t || plainPtrTy f t || match f.types[t]? with | some .bool => true | _ => false

/-- The offset of field `idx` of the non-`packed` struct a pointer of type `t` points to
(`Sem.fieldOffset?`). -/
def fieldOffset? (f : Func) (t : TyId) (idx : Nat) : Option Nat := do
  let .ptr _ _ s ← f.types[t]? | none
  let .struct _ layout _ ← f.types[s]? | none
  if layout == "packed" then none
  (← f.layouts[s]?).offsets[idx]?

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
def instReason (f : Func) (tyOfInst : InstId → Option TyId) (i : Inst) : Except String Unit := do
  let vals (vs : List Val) : Except String Unit :=
    unless vs.all (simpleVal f) do throw s!"inst {i.id}: an operand outside the fragment"
  let intRes : Except String Unit :=
    unless isIntTy f i.ty do throw s!"inst {i.id}: a non-integer result"
  -- A pointer operand: an instruction of a plain pointer type.
  let ptrOf (v : Val) : Option TyId := match v with
    | .inst x => (tyOfInst x).filter (plainPtrTy f)
    | _ => none
  let ptrVal (v : Val) : Except String TyId := do
    let some t := ptrOf v | throw s!"inst {i.id}: an access through a pointer outside the fragment"
    pure t
  match i.op with
  | .arg _ | .line _ | .dbg .. | .unreach | .trap | .block _ => pure ()
  | .arith _ _ a b | .div _ a b | .minMax _ a b | .bit _ a b => do intRes; vals [a, b]
  | .cmp _ a b => do
    let intOperand : Val → Bool
      | .inst x => (tyOfInst x).any (isIntTy f)
      | .int t _ => isIntTy f t
      | _ => false
    unless intOperand a || ((ptrOf a).isSome && (ptrOf b).isSome) do
      throw s!"inst {i.id}: a comparison of non-integers"
    vals [a, b]
  | .load p => do
    let _ ← ptrVal p
    unless memValTy f i.ty do throw s!"inst {i.id}: a load of a type outside the fragment"
  | .store p v => do
    let _ ← ptrVal p
    vals [v]
    let stored := match v with
      | .inst x => (tyOfInst x).any (memValTy f)
      | .int t _ => isIntTy f t
      | .bool _ => true
      | _ => false
    unless stored do throw s!"inst {i.id}: a store of a type outside the fragment"
  | .fieldPtr b idx => do
    let t ← ptrVal b
    unless plainPtrTy f i.ty && (fieldOffset? f t idx).isSome do
      throw s!"inst {i.id}: a field pointer outside the fragment"
  | .bitcast a => do
    let _ ← ptrVal a
    unless plainPtrTy f i.ty do throw s!"inst {i.id}: a bitcast outside the fragment"
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
  | .loop _ | .«repeat» _ => throw s!"inst {i.id}: a loop (semantics only; no certificate yet)"
  | .alloc => throw s!"inst {i.id}: a local (semantics only; no certificate yet)"
  | _ => throw s!"inst {i.id}: an instruction outside the fragment"

def callsIn (f : Func) : Array String :=
  (allInsts f.body).filterMap fun i => match i.op with
    | .call (.func n _ _) _ => some n
    | _ => none

/-- The local reason a function is outside the fragment, or its non-panic callees. -/
def localReason (f : Func) : Except String (Array String) := do
  for p in f.params do
    unless (scalar? f p).isSome do throw "a parameter that is not an integer, bool or plain pointer"
  unless (retScalar? f f.ret).isSome do
    throw "a return type that is not an integer, bool, plain pointer or void"
  let insts := allInsts f.body
  let tyOfInst (x : InstId) := (insts.find? (·.id == x)).map (·.ty)
  for i in insts do instReason f tyOfInst i
  unless (printFunc f).isSome do throw "an instruction the certificate printer does not print"
  pure ((callsIn f).filter fun n => (panicCallee? n).isNone)

/-- Split the functions into the certificate fragment (closed under direct calls) and the
others, each with a reason. -/
def fragment (funcs : Array Func) (memFuncs concFuncs : Array String) :
    Array Func × Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  let mut cands : Array (Func × Array String) := #[]
  -- A recursive function in `Zig.MemM` charges its frame to the model's stack budget
  -- (`Zig.enterFrame`, STK-01), which the semantics does not have.
  let budgeted := (callGroups funcs).flatMap fun (members, recursive) =>
    if recursive then (members.map (·.name)).filter memFuncs.contains else #[]
  for f in funcs do
    let reason := if concFuncs.contains f.name then .error "a concurrent function (`Zig.ConcM`)"
      else if budgeted.contains f.name then
        .error "a recursive function that uses memory (stack budget `Zig.enterFrame`, STK-01)"
      else localReason f
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

/-- The certificate file for `funcs` (the translated program, emission order). `declNames`
maps each fully qualified name to its generated definition in namespace `ns`, which
`genModule` defines. `memFuncs`/`concFuncs`: the functions the translator emits in `Zig.MemM`
and `Zig.ConcM` (`memoryFunctions`, `concFunctions`). -/
def emit (funcs : Array Func) (ns : String) (declNames : Array (String × String))
    (genModule : String) (memFuncs concFuncs : Array String) : String := Id.run do
  let (frag, out) := fragment funcs memFuncs concFuncs
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
  let genRes (f : Func) (args : String) : String :=
    let s := sig f
    if isMem f then s!"(fun r => ({s.ret.enc "r.1"}, r.2)) <$> ({genName f} {args}).run m"
    else s!"(fun {s.ret.binder} => ({s.ret.enc "v"}, m)) <$> {genName f} {args}"
  let mut lines : Array String := #[
    "-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.",
    "import Air2Lean.Sem", s!"import {genModule}", "",
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
    let simpSet := ", ".intercalate
      ([airName f, "air_sem"] ++ (panicLemmas.filter fun (n, _) => (callsIn f).contains n).toList.map (·.2) ++
        (if calls then ["gen"] else []))
    let what := if calls then ", with the generated program answering its calls,"
      else " (under any call oracle)"
    lines := lines ++ #[
      s!"/-- `{f.name}`: the AIR semantics of the decoded function{what} equals the generated definition. -/",
      s!"theorem {d}_step {callBinder}{s.binders} (m : Zig.Mem) :",
      s!"    (execFunc {oracle} {airName f} [{s.encArgs}]).run m =",
      s!"      {genRes f s.argNames} := by",
      s!"  conv => rhs; rw [{genName f}]",
      s!"  simp only [{simpSet}]", ""]
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
    s!"fun g => ∀ {s.argNames} m, Lean.Order.PartialOrder.rel ((fun {s.ret.binder} => ({s.ret.enc "v"}, m)) <$> g {s.argNames}) " ++
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
        s!"    Lean.Order.PartialOrder.rel ((fun {s.ret.binder} => ({s.ret.enc "v"}, m)) <$> {genName f} {s.argNames})",
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
        s!"      (fun {s.ret.binder} => ({s.ret.enc "v"}, m)) <$> {genName f} {s.argNames} :=",
        s!"  Lean.Order.PartialOrder.rel_antisymm ({d}_sound {s.argNames} m) ({d}_complete {s.argNames} m)", ""]
  lines := lines.push s!"end {ns}.AirCert"
  pure ("\n".intercalate lines.toList ++ "\n")

end Air2Lean.Certificate
