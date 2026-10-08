import Air2Lean.Air.Op

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

def int (v : Int) : String := if v < 0 then s!"({v} : Int)" else s!"({v} : Int)"

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
  | .rem => ".rem" | .mod => ".mod"
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

end Air2Lean.Certificate

namespace Air2Lean.Certificate

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

def scalar? : Ty → Option Scalar
  | .int s w => some { lean := s!"BitVec {w}", enc := fun v => s!"(Value.int {bool s} {w} {v})",
                       dec := fun i => s!"((args.getD {i} .void).toBV {w})",
                       inv := "valOk_int", decVar := fun i => s!"(v{i}.toBV {w})" }
  | .bool => some { lean := "Bool", enc := fun v => s!"(Value.bool {v})",
                    dec := fun i => s!"((args.getD {i} .void).toBool)",
                    inv := "valOk_bool", decVar := fun i => s!"v{i}.toBool" }
  | _ => none

def retScalar? : Ty → Option Scalar
  | .void => some { lean := "Unit", enc := fun _ => "Value.void", dec := fun _ => "()",
                    inv := "valOk_void", decVar := fun _ => "()" }
  | t => scalar? t

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
  match i.op with
  | .arg _ | .line _ | .dbg .. | .unreach | .trap | .block _ => pure ()
  | .arith _ _ a b | .div _ a b | .minMax _ a b | .bit _ a b => do intRes; vals [a, b]
  | .cmp _ a b => do
    let intOperand : Val → Bool
      | .inst x => (tyOfInst x).any (isIntTy f)
      | .int t _ => isIntTy f t
      | _ => false
    unless intOperand a do
      throw s!"inst {i.id}: a comparison of non-integers"
    vals [a, b]
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
  | .alloc | .load _ | .store .. =>
    throw s!"inst {i.id}: a local (semantics only; no certificate yet)"
  | _ => throw s!"inst {i.id}: an instruction outside the fragment"

def callsIn (f : Func) : Array String :=
  (allInsts f.body).filterMap fun i => match i.op with
    | .call (.func n _ _) _ => some n
    | _ => none

/-- The local reason a function is outside the fragment, or its non-panic callees. -/
def localReason (f : Func) : Except String (Array String) := do
  for p in f.params do
    unless (f.types[p]?.bind scalar?).isSome do throw "a parameter that is not an integer or bool"
  unless (f.types[f.ret]?.bind retScalar?).isSome do
    throw "a return type that is not an integer, bool or void"
  let insts := allInsts f.body
  let tyOfInst (x : InstId) := (insts.find? (·.id == x)).map (·.ty)
  for i in insts do instReason f tyOfInst i
  unless (printFunc f).isSome do throw "an instruction the certificate printer does not print"
  pure ((callsIn f).filter fun n => (panicCallee? n).isNone)

/-- Split the functions into the certificate fragment (closed under direct calls) and the
others, each with a reason. -/
def fragment (funcs : Array Func) : Array Func × Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  let mut cands : Array (Func × Array String) := #[]
  for f in funcs do
    match localReason f with
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
  let ret := (f.types[f.ret]?.bind retScalar?).getD blank
  let ps := f.params.mapIdx fun i p => (i, (f.types[p]?.bind scalar?).getD ret)
  { ret, ps,
    binders := " ".intercalate (ps.toList.map fun (i, s) => s!"(p{i} : {s.lean})"),
    encArgs := ", ".intercalate (ps.toList.map fun (i, s) => s.enc s!"p{i}"),
    argNames := " ".intercalate (ps.toList.map fun (i, _) => s!"p{i}") }

/-- The certificate file for `funcs` (the translated program, emission order). `declNames`
maps each fully qualified name to its generated definition in namespace `ns`, which
`genModule` defines. -/
def emit (funcs : Array Func) (ns : String) (declNames : Array (String × String))
    (genModule : String) : String := Id.run do
  let (frag, out) := fragment funcs
  let declOf (n : String) : String := (declNames.find? (·.1 == n)).map (·.2) |>.getD n
  let airName (f : Func) := s!"air_{declOf f.name}"
  let genName (f : Func) := s!"{ns}.{declOf f.name}"
  let names := frag.map (·.name)
  let calling (f : Func) := (callsIn f).any names.contains
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
    lines := lines.push s!"  | {str f.name}, args =>\n    StateT.lift ((fun v => {s.ret.enc "v"}) <$> {genName f} {" ".intercalate args.toList})"
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
      s!"      (fun v => ({s.ret.enc "v"}, m)) <$> {genName f} {s.argNames} := by",
      s!"  conv => rhs; rw [{genName f}]",
      s!"  simp only [{simpSet}]", ""]
    let paramList := "[" ++ ", ".intercalate (f.params.toList.map toString) ++ "]"
    let mut fix := #[
      s!"theorem {d}_fix (args : List Value)",
      s!"    (h : argsOk {airName f} {airName f}.params.toList args = true) :",
      s!"    execFunc gen {airName f} args = gen {str f.name} args := by",
      s!"  replace h : argsOk {airName f} {paramList} args = true := h"]
    for (i, _) in s.ps do
      fix := fix.push s!"  obtain ⟨v{i}, args, rfl, h{i}, h⟩ := argsOk_cons h"
    fix := fix.push "  obtain rfl := argsOk_nil h"
    for (i, sc) in s.ps do
      fix := fix ++ #[s!"  replace h{i} : valOk {printTy (f.types[f.params[i]!]!)} v{i} = true := h{i}",
        s!"  rw [{sc.inv} h{i}]"]
    let stepArgs := " ".intercalate (s.ps.toList.map fun (i, sc) => sc.decVar i)
    fix := fix ++ #["  funext m",
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
  for f in frag do
    unless calling f do continue
    let d := declOf f.name
    let s := sig f
    lines := lines ++ #[
      s!"/-- `{f.name}` calls certified functions: every terminating AIR run is the generated definition's. -/",
      s!"theorem {d}_sound {s.binders} (m : Zig.Mem) :",
      s!"    Lean.Order.PartialOrder.rel ((run (progOf table) {str f.name} [{s.encArgs}]).run m)",
      s!"      ((fun v => ({s.ret.enc "v"}, m)) <$> {genName f} {s.argNames}) := by",
      s!"  have h : Lean.Order.PartialOrder.rel ((run (progOf table) {str f.name} [{s.encArgs}]).run m)",
      s!"      ((gen {str f.name} [{s.encArgs}]).run m) := run_le_gen {str f.name} [{s.encArgs}] m",
      "  simp only [gen, air_sem] at h",
      "  exact h", ""]
  for f in frag do
    if calling f then continue
    let d := declOf f.name
    let s := sig f
    lines := lines ++ #[
      s!"/-- `{f.name}` makes no certified call: its AIR semantics equals the generated definition. -/",
      s!"theorem {d}_run {s.binders} (m : Zig.Mem) :",
      s!"    (run (progOf table) {str f.name} [{s.encArgs}]).run m =",
      s!"      (fun v => ({s.ret.enc "v"}, m)) <$> {genName f} {s.argNames} := by",
      "  rw [run_of_lookup (by rfl)]",
      s!"  exact {d}_step _ {s.argNames} m", ""]
  lines := lines.push s!"end {ns}.AirCert"
  pure ("\n".intercalate lines.toList ++ "\n")

end Air2Lean.Certificate
