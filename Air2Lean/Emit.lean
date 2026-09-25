import Air2Lean.Air.Op

/-!
# Emitter

`emit : Array Func → String → String → String` turns a list of already-checked functions into
one Lean source file: `import ZigLean`, one `namespace <ns>`, struct types once (deduplicated
by Zig name), then per function a generated `<Fn>Locals` structure (one field per `alloc`), a
generated `<Fn>Exit` inductive (`ret` / `br<targetId>` / `rep<targetId>`, one constructor per
distinct branch target reachable in the function), and the function itself as a
`Zig.M <Fn>Locals <Fn>Exit` do-block wrapped by a top-level `def` that unwraps `.ret`.

Assumes its input already passed `Check.lean`: it does not re-validate the subset, and reaches
for `throw .panic` / a `default`-typed placeholder at the handful of spots that are otherwise
statically impossible (an exit other than `.ret` leaving a function's outermost body, an
unresolved name).
-/

namespace Air2Lean

/-! ## Flatten: every instruction in a function, including nested bodies -/

mutual
partial def flattenInst (acc : Array Inst) (i : Inst) : Array Inst :=
  flattenOp (acc.push i) i.op

partial def flattenOp (acc : Array Inst) (op : Op) : Array Inst :=
  match op with
  | .block body => body.foldl flattenInst acc
  | .loop body => body.foldl flattenInst acc
  | .condBr _ t e => e.foldl flattenInst (t.foldl flattenInst acc)
  | .switchBr _ cases e =>
    let acc := cases.foldl (fun acc c => c.body.foldl flattenInst acc) acc
    e.foldl flattenInst acc
  | .«try» _ errBody => errBody.foldl flattenInst acc
  | _ => acc
end

def Func.allInsts (f : Func) : Array Inst := f.body.foldl flattenInst #[]

/-- Is `op` a terminator: the one instruction that ends its containing body (`docs/air-json.md`
/ `PLAN.md`)? A noreturn call counts (the `unreach` Sema emits right after it is dead code). -/
def isTerminating (op : Op) : Bool :=
  match op with
  | .br .. | .«repeat» .. | .ret .. | .unreach | .trap | .condBr .. | .switchBr .. => true
  | .call (.func _ noreturn) _ => noreturn
  | _ => false

/-! ## Name mangling (`docs/generated-code.md` §Names) -/

def leanKeywords : List String :=
  ["def", "theorem", "lemma", "structure", "inductive", "namespace", "import", "open", "match",
   "with", "do", "let", "fun", "if", "then", "else", "end", "mutual", "partial", "where",
   "deriving", "class", "instance", "abbrev", "variable", "variables", "section", "by", "sorry",
   "have", "show", "from", "this", "suffices", "calc", "for", "in", "return", "try", "catch",
   "finally", "unsafe", "noncomputable", "macro", "syntax", "elab", "axiom", "constant",
   "forall", "exists", "Type", "Prop", "Sort", "opaque", "attribute", "set_option", "universe",
   "extends", "renaming", "hiding"]

def mangleName (prefix_ : String) (raw : String) : String :=
  let stripped : String :=
    if prefix_.length > 0 && raw.startsWith prefix_ then (raw.drop prefix_.length).toString
    else raw
  let underscored := stripped.replace "." "_"
  if leanKeywords.contains underscored then s!"«{underscored}»" else underscored

def mangleField (raw : String) : String :=
  if leanKeywords.contains raw then s!"«{raw}»" else raw

/-! ## Types (`docs/generated-code.md` §Types) -/

/-- `TyId → Lean type` as source text. `structNames` maps a Zig struct name to its Lean name. -/
partial def emitTy (structNames : Array (String × String)) (types : Array Ty) (ty : Ty) :
    String :=
  match ty with
  | .int _ bits => s!"BitVec {bits}"
  | .bool => "Bool"
  | .void => "Unit"
  | .noreturn => "Unit"
  | .ptr "slice" true child => s!"Array ({emitTy structNames types types[child]!})"
  | .ptr _ _ child => emitTy structNames types types[child]!
  | .array _ child => s!"Array ({emitTy structNames types types[child]!})"
  | .optional child => s!"Option ({emitTy structNames types types[child]!})"
  | .errorUnion _set payload => s!"Except Zig.ErrName ({emitTy structNames types types[payload]!})"
  | .errorSet _ => "Zig.ErrName"
  | .struct name _ _ => (structNames.find? (·.1 == name)).map (·.2) |>.getD name
  | .tuple fields =>
    let parts := (fields.map (fun fid => emitTy structNames types types[fid]!)).toList
    if parts.isEmpty then "Unit" else String.intercalate " × " parts
  | .other name => name

/-! ## Struct registry: emit each distinct Zig struct once -/

structure StructInfo where
  zigName : String
  leanName : String
  fields : Array (String × TyId)
  srcTypes : Array Ty

def collectStructs (funcs : Array Func) (prefix_ : String) : Array StructInfo :=
  funcs.foldl (fun acc f =>
    f.types.foldl (fun acc ty =>
      match ty with
      | .struct name _ fields =>
        if acc.any (·.zigName == name) then acc
        else
          acc.push { zigName := name, leanName := mangleName prefix_ name, fields,
                     srcTypes := f.types }
      | _ => acc)
      acc)
    #[]

def emitStruct (structNames : Array (String × String)) (s : StructInfo) : String :=
  let fieldLines := (s.fields.map fun (fname, fty) =>
    s!"  {mangleField fname} : {emitTy structNames s.srcTypes s.srcTypes[fty]!}").toList
  String.intercalate "\n"
    ([s!"structure {s.leanName} where"] ++ fieldLines ++ ["  deriving Repr, Inhabited, DecidableEq"])

/-! ## Per-function static context -/

structure FCtx where
  types : Array Ty
  structNames : Array (String × String)
  funcNames : Array (String × String)
  /-- `alloc` inst id → its `<Fn>Locals` field name. -/
  allocFields : Array (InstId × String)
  /-- `block`/`loop` inst id → its declared `ty`. -/
  blockTys : Array (InstId × TyId)
  allInsts : Array Inst
  retTy : TyId
  /-- This function's own generated (mangled) name, for naming its extracted loop-body defs
  (`<fnName>.loop<k>`, see `emitLoopDef`). -/
  fnName : String
  /-- This function's generated `<Fn>Locals`/`<Fn>Exit` names, for ascribing nested do-blocks
  (see `FCtx.ascribedDo`). -/
  localsName : String
  exitName : String

def FCtx.tyOfId (fc : FCtx) (tid : TyId) : Ty := fc.types[tid]!
def FCtx.emitTyOf (fc : FCtx) (tid : TyId) : String :=
  emitTy fc.structNames fc.types (fc.tyOfId tid)
def FCtx.tyBits (fc : FCtx) (tid : TyId) : Nat := match fc.tyOfId tid with | .int _ b => b | _ => 0
def FCtx.tySigned (fc : FCtx) (tid : TyId) : Bool :=
  match fc.tyOfId tid with | .int s _ => s | _ => false

def FCtx.instTyId (fc : FCtx) (id : InstId) : TyId :=
  (fc.allInsts.find? (·.id == id)).map (·.ty) |>.getD 0

def FCtx.valTy (fc : FCtx) (v : Val) : Ty :=
  match v with
  | .inst id => fc.tyOfId (fc.instTyId id)
  | .int tid _ => fc.tyOfId tid
  | .bool _ => .bool
  | .void => .void
  | .func .. => .void
  | .undef tid | .optNull tid | .optSome tid _ | .err tid _ | .errUnionErr tid _
  | .errUnionOk tid _ => fc.tyOfId tid

def FCtx.valSigned (fc : FCtx) (v : Val) : Bool := match fc.valTy v with | .int s _ => s | _ => false

def FCtx.targetTy (fc : FCtx) (target : InstId) : Ty :=
  match fc.blockTys.find? (·.1 == target) with
  | some (_, t) => fc.tyOfId t
  | none => .void

def FCtx.resolveVal (fc : FCtx) (env : Array (InstId × String)) (v : Val) : String :=
  match v with
  | .inst id => (env.find? (·.1 == id)).map (·.2) |>.getD s!"(panic! \"air2lean: unbound inst {id}\")"
  | .int tid n =>
    let bits := fc.tyBits tid
    if n < 0 then s!"(-({(-n).toNat} : BitVec {bits}))" else s!"({n.toNat} : BitVec {bits})"
  | .bool b => if b then "true" else "false"
  | .void => "()"
  | .undef tid =>
    match fc.tyOfId tid with
    | .int _ b => s!"(0#{b})"
    | .bool => "false"
    | _ => "default"
  | .func name _ => (fc.funcNames.find? (·.1 == name)).map (·.2) |>.getD name
  | .optNull _ => "none"
  | .optSome _ v => s!"(some {fc.resolveVal env v})"
  | .err _ name => name.quote
  | .errUnionErr tid name => s!"(.error {name.quote} : {fc.emitTyOf tid})"
  | .errUnionOk tid p => s!"(.ok {fc.resolveVal env p} : {fc.emitTyOf tid})"

def FCtx.resolveCallee (fc : FCtx) (v : Val) : Bool × String :=
  match v with
  | .func name noreturn =>
    (noreturn, (fc.funcNames.find? (·.1 == name)).map (·.2) |>.getD name)
  | _ => (false, "panic! \"air2lean: indirect calls are outside the subset\"")


/-- The field name to project for `struct_field_val s index`: `s`'s own field name if `s` is a
struct, else a positional `1`/`2` (for example the pair `@addWithOverflow` returns). -/
def FCtx.structFieldName (fc : FCtx) (s : Val) (index : Nat) : String :=
  match fc.valTy s with
  | .struct _ _ fields => (fields[index]?).map (fun (n, _) => mangleField n) |>.getD s!"fld{index}"
  | _ => if index == 0 then "1" else "2"

def FCtx.structFieldNamesFor (_fc : FCtx) (ty : Ty) : Array String :=
  match ty with
  | .struct _ _ fields => fields.map (fun (n, _) => mangleField n)
  | _ => #[]

/-! ## `alloc` → `<Fn>Locals` field prepass -/

/-- `(allocId, fieldName, childTy)` for every `alloc` in the function: the field name is the
`dbg_var_ptr`-given name when one names that alloc, else `local<id>`. -/
def collectAllocs (types : Array Ty) (allInsts : Array Inst) : Array (InstId × String × TyId) :=
  let allocIds := allInsts.filterMap fun i => match i.op with | .alloc => some i.id | _ => none
  let names := allInsts.filterMap fun i => match i.op with
    | .dbg (some nm) (some (.inst aid)) => if allocIds.contains aid then some (aid, nm) else none
    | _ => none
  allocIds.map fun aid =>
    let nm := (names.find? (·.1 == aid)).map (·.2) |>.getD s!"local{aid}"
    let childTy := match allInsts.find? (·.id == aid) with
      | some i => match types[i.ty]! with
        | .ptr _ _ child => child
        | _ => i.ty
      | none => 0
    (aid, nm, childTy)

def emitLocalsStruct (structNames : Array (String × String)) (types : Array Ty)
    (localsName : String) (allocs : Array (InstId × String × TyId)) : String :=
  let lines := (allocs.map fun (_, nm, cty) =>
    s!"  {nm} : {emitTy structNames types types[cty]!}").toList
  String.intercalate "\n" ([s!"structure {localsName} where"] ++ lines ++ ["  deriving Inhabited"])

/-! ## `Exit` prepass and emission -/

def dedupIds (a : Array InstId) : Array InstId :=
  a.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

def blockLoopTys (allInsts : Array Inst) : Array (InstId × TyId) :=
  allInsts.filterMap fun i => match i.op with | .block _ | .loop _ => some (i.id, i.ty) | _ => none

def brTargets (allInsts : Array Inst) : Array InstId :=
  dedupIds (allInsts.filterMap fun i => match i.op with | .br t _ => some t | _ => none)

def repTargets (allInsts : Array Inst) : Array InstId :=
  dedupIds (allInsts.filterMap fun i => match i.op with | .«repeat» t => some t | _ => none)

def emitExitInductive (structNames : Array (String × String)) (types : Array Ty)
    (exitName : String) (retTy : TyId) (blTys : Array (InstId × TyId)) (brT repT : Array InstId) :
    String :=
  let retLine := match types[retTy]! with
    | .void => "  | ret"
    | rt => s!"  | ret (v : {emitTy structNames types rt})"
  let brLines := (brT.map fun k =>
    let kty := (blTys.find? (·.1 == k)).map (fun (_, t) => types[t]!) |>.getD .void
    match kty with
    | .void => s!"  | br{k}"
    | t => s!"  | br{k} (v : {emitTy structNames types t})").toList
  let repLines := (repT.map fun k => s!"  | rep{k}").toList
  String.intercalate "\n" ([s!"inductive {exitName} where", retLine] ++ brLines ++ repLines)

/-! ## Loop-body capture analysis

Every `loop` body becomes its own top-level def (`docs/generated-code.md` §Loops), so it needs
an explicit parameter for every SSA value it reads that is bound outside it. -/

/-- Every `Val` `op` resolves through `rv` at emission time (`emitSimple` / `emitTerminator` /
`emitSwitchChain` below) — i.e. every value referenced by name in the generated text. Does not
look inside a nested `block`/`loop`/`condBr`/`switchBr`'s own body: those instructions are
visited separately (`Func.allInsts` already flattens them in, see `FCtx.freeVarIds`). A
`load`/`store`'s pointer is excluded: it resolves to a `Locals` field name via `allocFields`,
never a captured identifier. A noreturn call's args are excluded: `emitSimple` drops the whole
call. -/
def FCtx.directVals (fc : FCtx) (op : Op) : Array Val :=
  match op with
  | .arg _ => #[]
  | .arith _ _ a b => #[a, b]
  | .div _ a b => #[a, b]
  | .minMax _ a b => #[a, b]
  | .withOverflow _ a b => #[a, b]
  | .bit _ a b => #[a, b]
  | .not a => #[a]
  | .neg a => #[a]
  | .shift _ a b => #[a, b]
  | .cmp _ a b => #[a, b]
  | .boolAnd a b => #[a, b]
  | .boolOr a b => #[a, b]
  | .intCast a => #[a]
  | .trunc a => #[a]
  | .bitcast a => #[a]
  | .isNull a => #[a]
  | .isNonNull a => #[a]
  | .optPayload a => #[a]
  | .wrapOptional a => #[a]
  | .isErr a => #[a]
  | .isNonErr a => #[a]
  | .errPayload a => #[a]
  | .errCode a => #[a]
  | .wrapErrPayload a => #[a]
  | .wrapErr a => #[a]
  | .alloc => #[]
  | .load _ => #[]
  | .store _ v => #[v]
  | .sliceLen s => #[s]
  | .sliceElemVal s i => #[s, i]
  | .structFieldVal s _ => #[s]
  | .aggregateInit elems => elems
  | .call callee args => match callee with | .func _ true => #[] | _ => args
  | .block _ => #[]
  | .loop _ => #[]
  | .br target v => match fc.targetTy target with | .void => #[] | _ => #[v]
  | .«repeat» _ => #[]
  | .condBr c _ _ => #[c]
  | .switchBr v cases _ =>
    #[v] ++ cases.foldl (fun acc c =>
      let acc := c.items.foldl Array.push acc
      c.ranges.foldl (fun acc (lo, hi) => (acc.push lo).push hi) acc) #[]
  | .«try» v _ => #[v]
  | .ret v => match fc.tyOfId fc.retTy with | .void => #[] | _ => #[v]
  | .unreach => #[]
  | .trap => #[]
  | .line _ => #[]
  | .dbg _ _ => #[]

/-- Ids referenced inside `body` (recursively) that are defined outside it: the free variables
of a loop body, i.e. what its extracted top-level def must take as parameters. -/
def FCtx.freeVarIds (fc : FCtx) (body : Array Inst) : Array InstId :=
  let bodyInsts := body.foldl flattenInst #[]
  let defined := bodyInsts.map (·.id)
  let used := dedupIds (bodyInsts.foldl (fun acc i =>
    (fc.directVals i.op).foldl
      (fun acc v => match v with | .inst id => acc.push id | _ => acc) acc)
    #[])
  used.filter (fun id => !defined.contains id)

/-- Some instruction of the function reads `id`. -/
def FCtx.isReferenced (fc : FCtx) (id : InstId) : Bool :=
  fc.allInsts.any fun i => (fc.directVals i.op).contains (.inst id)

/-- `id`'s parameter index if the instruction defining it is an `arg`, else `none`. -/
def FCtx.argIndexOf (fc : FCtx) (id : InstId) : Option Nat :=
  match fc.allInsts.find? (·.id == id) with
  | some i => match i.op with | .arg idx => some idx | _ => none
  | none => none

/-- The captured values a loop body needs from outside itself, as `(id, name, leanType)`,
ordered params first (by parameter index) then by id (`docs/generated-code.md` §Loops). The
name matches exactly what the body text already uses (`p<i>`/`i<id>`), so the extracted def's
parameter list needs no renaming of the body. -/
def FCtx.loopCaptures (fc : FCtx) (body : Array Inst) : Array (InstId × String × String) :=
  let free := fc.freeVarIds body
  let params := (free.filterMap fun id => (fc.argIndexOf id).map fun idx => (idx, id))
    |>.qsort (fun a b => decide (a.1 < b.1)) |>.map (·.2)
  let rest := (free.filter fun id => (fc.argIndexOf id).isNone)
    |>.qsort (fun a b => decide (a < b))
  (params ++ rest).map fun id =>
    let name := match fc.argIndexOf id with | some idx => s!"p{idx}" | none => s!"i{id}"
    (id, name, fc.emitTyOf (fc.instTyId id))

/-! ## Expression / statement emission -/

def indent (n : Nat) (s : String) : String :=
  let pad := String.ofList (List.replicate n ' ')
  String.intercalate "\n" ((s.splitOn "\n").map fun l => if l.isEmpty then l else pad ++ l)

/-- `indent`, but the first line is left untouched (for splicing right after `... ← `). -/
def indentTail (n : Nat) (s : String) : String :=
  match s.splitOn "\n" with
  | [] => s
  | first :: rest =>
    let pad := String.ofList (List.replicate n ' ')
    String.intercalate "\n" (first :: rest.map fun l => if l.isEmpty then l else pad ++ l)

def doBlock (body : String) : String := s!"(do\n{indent 2 body})"

/-- `doBlock`, ascribed with this function's `Zig.M <Locals> <Exit>` type. Needed at every
point a nested do-block is used as the *operand* of `match ←`/`Zig.loop` (a `.block`/`.loop`'s
own body): unlike a plain nested `if`/`match` living inside an already-typed do-block, that
operand position does not inherit the expected type from an outer ascription (confirmed by
elaboration failures when only the outermost per-function do-block was ascribed), so it needs
its own. -/
def FCtx.ascribedDo (fc : FCtx) (body : String) : String :=
  s!"({doBlock body} : Zig.M {fc.localsName} {fc.exitName})"

/-- AIR can compute a value that nothing reads (`catch 0` still unwraps the error code). The
effect stays; the `_` prefix stops Lean's unused-variable warning. -/
def bindLet (fc : FCtx) (env : Array (InstId × String)) (id : InstId) (expr : String) :
    Array (InstId × String) × String :=
  let name := if fc.isReferenced id then s!"i{id}" else s!"_i{id}"
  (env.push (id, name), s!"let {name} ← {expr}")

/-- A straight-line (non-terminator, non-`block`/`loop`) instruction: at most one output line. -/
def emitSimple (fc : FCtx) (env : Array (InstId × String)) (inst : Inst) :
    Array (InstId × String) × Option String :=
  let rv := fc.resolveVal env
  match inst.op with
  | .arg index => (env.push (inst.id, s!"p{index}"), none)
  | .arith op mode a b =>
    let sgn := if fc.valSigned a then "true" else "false"
    let expr := match op, mode with
      | .add, .checked => s!"Zig.add {sgn} {rv a} {rv b}"
      | .add, .wrap => s!"pure (Zig.addWrap {rv a} {rv b})"
      | .add, .sat => s!"pure (Zig.addSat {sgn} {rv a} {rv b})"
      | .sub, .checked => s!"Zig.sub {sgn} {rv a} {rv b}"
      | .sub, .wrap => s!"pure (Zig.subWrap {rv a} {rv b})"
      | .sub, .sat => s!"pure (Zig.subSat {sgn} {rv a} {rv b})"
      | .mul, .checked => s!"Zig.mul {sgn} {rv a} {rv b}"
      | .mul, .wrap => s!"pure (Zig.mulWrap {rv a} {rv b})"
      | .mul, .sat => s!"pure (Zig.mulSat {sgn} {rv a} {rv b})"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .div op a b =>
    let sgn := if fc.valSigned a then "true" else "false"
    let f := match op with
      | .divTrunc => "Zig.divTrunc" | .divFloor => "Zig.divFloor" | .divExact => "Zig.divExact"
      | .rem => "Zig.rem" | .mod => "Zig.mod"
    let (env, l) := bindLet fc env inst.id s!"{f} {sgn} {rv a} {rv b}"; (env, some l)
  | .minMax isMax a b =>
    let sgn := if fc.valSigned a then "true" else "false"
    let f := if isMax then "Zig.max" else "Zig.min"
    let (env, l) := bindLet fc env inst.id s!"pure ({f} {sgn} {rv a} {rv b})"; (env, some l)
  | .withOverflow op a b =>
    let sgn := if fc.valSigned a then "true" else "false"
    let f := match op with
      | .add => "Zig.addWithOverflow" | .sub => "Zig.subWithOverflow" | .mul => "Zig.mulWithOverflow"
    let (env, l) := bindLet fc env inst.id s!"pure ({f} {sgn} {rv a} {rv b})"; (env, some l)
  | .bit op a b =>
    let f := match op with | .and => "&&&" | .or => "|||" | .xor => "^^^"
    let (env, l) := bindLet fc env inst.id s!"pure ({rv a} {f} {rv b})"; (env, some l)
  | .not a =>
    let expr := match fc.valTy a with
      | .bool => s!"!{rv a}"
      | _ => s!"~~~{rv a}"
    let (env, l) := bindLet fc env inst.id s!"pure ({expr})"; (env, some l)
  | .neg a =>
    let (env, l) := bindLet fc env inst.id s!"Zig.neg {if fc.valSigned a then "true" else "false"} {rv a}"
    (env, some l)
  | .shift op a b =>
    let sgn := if fc.valSigned a then "true" else "false"
    let expr := match op with
      | .shl => s!"pure (Zig.shl {rv a} {rv b})"
      | .shr => s!"pure (Zig.shr {sgn} {rv a} {rv b})"
      | .shlSat => s!"pure (Zig.shlSat {sgn} {rv a} {rv b})"
      | .shlExact => s!"Zig.shlExact {sgn} {rv a} {rv b}"
      | .shrExact => s!"Zig.shrExact {sgn} {rv a} {rv b}"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .cmp op a b =>
    let sgn := if fc.valSigned a then "true" else "false"
    let expr := match op with
      | .lt => s!"Zig.lt {sgn} {rv a} {rv b}" | .le => s!"Zig.le {sgn} {rv a} {rv b}"
      | .gt => s!"Zig.gt {sgn} {rv a} {rv b}" | .ge => s!"Zig.ge {sgn} {rv a} {rv b}"
      | .eq => s!"{rv a} == {rv b}" | .ne => s!"{rv a} != {rv b}"
    let (env, l) := bindLet fc env inst.id s!"pure ({expr})"; (env, some l)
  | .boolAnd a b => let (env, l) := bindLet fc env inst.id s!"pure ({rv a} && {rv b})"; (env, some l)
  | .boolOr a b => let (env, l) := bindLet fc env inst.id s!"pure ({rv a} || {rv b})"; (env, some l)
  | .intCast a =>
    let s1 := if fc.valSigned a then "true" else "false"
    let s2 := if fc.tySigned inst.ty then "true" else "false"
    let m := fc.tyBits inst.ty
    let (env, l) := bindLet fc env inst.id s!"Zig.intCast {s1} {s2} {m} {rv a}"; (env, some l)
  | .trunc a =>
    let (env, l) := bindLet fc env inst.id s!"pure (Zig.trunc {fc.tyBits inst.ty} {rv a})"
    (env, some l)
  | .bitcast a => let (env, l) := bindLet fc env inst.id s!"pure ({rv a})"; (env, some l)
  | .isNull a => let (env, l) := bindLet fc env inst.id s!"pure (({rv a}).isNone)"; (env, some l)
  | .isNonNull a => let (env, l) := bindLet fc env inst.id s!"pure (({rv a}).isSome)"; (env, some l)
  | .optPayload a => let (env, l) := bindLet fc env inst.id s!"Zig.optPayload {rv a}"; (env, some l)
  | .wrapOptional a => let (env, l) := bindLet fc env inst.id s!"pure (some {rv a})"; (env, some l)
  | .isErr a => let (env, l) := bindLet fc env inst.id s!"pure (Zig.isErr {rv a})"; (env, some l)
  | .isNonErr a => let (env, l) := bindLet fc env inst.id s!"pure (Zig.isNonErr {rv a})"; (env, some l)
  | .errPayload a =>
    let (env, l) := bindLet fc env inst.id s!"Zig.call (Zig.unwrapPayload {rv a})"; (env, some l)
  | .errCode a =>
    let (env, l) := bindLet fc env inst.id s!"Zig.call (Zig.unwrapErr {rv a})"; (env, some l)
  | .wrapErrPayload a =>
    let ety := fc.emitTyOf inst.ty
    let (env, l) := bindLet fc env inst.id s!"pure ((.ok {rv a}) : {ety})"; (env, some l)
  | .wrapErr a =>
    let ety := fc.emitTyOf inst.ty
    let (env, l) := bindLet fc env inst.id s!"pure ((.error {rv a}) : {ety})"; (env, some l)
  | .alloc => (env, none)
  | .load ptr =>
    let field : String := match ptr with
      | .inst pid => (fc.allocFields.find? (·.1 == pid)).map (·.2) |>.getD "?"
      | _ => "?"
    let (env, l) := bindLet fc env inst.id s!"pure ((← get).{field})"; (env, some l)
  | .store ptr v =>
    let field : String := match ptr with
      | .inst pid => (fc.allocFields.find? (·.1 == pid)).map (·.2) |>.getD "?"
      | _ => "?"
    (env, some s!"modify (fun s => \{ s with {field} := {rv v} })")
  | .sliceLen s => let (env, l) := bindLet fc env inst.id s!"pure (Zig.len {rv s})"; (env, some l)
  | .sliceElemVal s i =>
    let (env, l) := bindLet fc env inst.id s!"Zig.call (Zig.index {rv s} {rv i})"; (env, some l)
  | .structFieldVal s index =>
    let fname := fc.structFieldName s index
    let (env, l) := bindLet fc env inst.id s!"pure (({rv s}).{fname})"; (env, some l)
  | .aggregateInit elems =>
    let sname := fc.emitTyOf inst.ty
    let fnames := fc.structFieldNamesFor (fc.tyOfId inst.ty)
    let assigns := ((fnames.zip elems).map fun (fn, e) => s!"{fn} := {rv e}").toList
    let (env, l) :=
      bindLet fc env inst.id s!"pure \{ {String.intercalate ", " assigns} : {sname} }"
    (env, some l)
  | .call callee args =>
    let (isNoreturn, cexpr) := fc.resolveCallee callee
    if isNoreturn then (env, none)
    else
      let argStrs := (args.map rv).toList
      let (env, l) := bindLet fc env inst.id s!"Zig.call ({cexpr} {String.intercalate " " argStrs})"
      (env, some l)
  | .line _ => (env, none)
  | .dbg _ _ => (env, none)
  | _ => (env, some s!"-- air2lean: unexpected op in straight-line position (inst {inst.id})")

mutual

/-- Translate an instruction sequence into a `Zig.M _ Exit` do-block body (as source text,
without the surrounding `do`). The last effective instruction (per `isTerminating`) becomes the
tail expression; anything the exporter placed after it (a defensive `unreach`) is dead and
dropped. -/
partial def emitStmts (fc : FCtx) (env : Array (InstId × String)) (insts : List Inst) : String :=
  match insts with
  | [] => "pure default"
  | inst :: rest =>
    if isTerminating inst.op then
      emitTerminator fc env inst
    else
      match inst.op with
      | .block body =>
        let inner := fc.ascribedDo (emitStmts fc env body.toList)
        match fc.targetTy inst.id with
        | .void =>
          let restStr := emitStmts fc env rest
          s!"match ← {inner} with\n| .br{inst.id} => {doBlock restStr}\n| e => pure e"
        | _ =>
          let vname := s!"v{inst.id}"
          let restStr := emitStmts fc (env.push (inst.id, vname)) rest
          s!"match ← {inner} with\n| .br{inst.id} {vname} => {doBlock restStr}\n| e => pure e"
      | .loop body =>
        -- A `loop` never falls through: the only way past it is a `br` to an *enclosing*
        -- block, so `rest` (anything after it in this same instruction array) is unreachable
        -- and dropped. The loop's own result (whatever exit its body converged to once
        -- `again` says stop) propagates as-is to whatever wraps this loop.
        --
        -- The body itself is not inlined: it was already emitted as its own top-level def
        -- (`emitLoopDef`, called from `emitOneFunction` before this function's own def), so a
        -- proof can name it. Call it with its captures instead.
        let caps := fc.loopCaptures body
        let args := String.intercalate " " ((caps.map fun (_, name, _) => name).toList)
        s!"Zig.loop ({fc.fnName}.loop{inst.id} {args}) {fc.fnName}.again{inst.id}"
      | .«try» v errBody =>
        let errStr := emitStmts fc env errBody.toList
        let vname := s!"v{inst.id}"
        let restStr := emitStmts fc (env.push (inst.id, vname)) rest
        s!"match {fc.resolveVal env v} with\n\
          | .error _ => {doBlock errStr}\n\
          | .ok {vname} => {doBlock restStr}"
      | _ =>
        let (env', lineOpt) := emitSimple fc env inst
        let restStr := emitStmts fc env' rest
        match lineOpt with
        | some line => s!"{line}\n{restStr}"
        | none => restStr

/-- The one instruction ending a body: `br`/`repeat`/`ret`/`unreach`/`trap`/`cond_br`/
`switch_br`/a noreturn call. -/
partial def emitTerminator (fc : FCtx) (env : Array (InstId × String)) (inst : Inst) : String :=
  let rv := fc.resolveVal env
  match inst.op with
  | .br target v =>
    match fc.targetTy target with
    | .void => s!"pure .br{target}"
    | _ => s!"pure (.br{target} {rv v})"
  | .«repeat» target => s!"pure .rep{target}"
  | .ret v =>
    match fc.tyOfId fc.retTy with
    | .void => "pure .ret"
    | _ => s!"pure (.ret {rv v})"
  | .unreach => "throw .unreachable"
  | .trap => "throw .panic"
  | .condBr c thenBody elseBody =>
    s!"if {rv c} then {doBlock (emitStmts fc env thenBody.toList)}\nelse \
      {doBlock (emitStmts fc env elseBody.toList)}"
  | .switchBr v cases elseBody => emitSwitchChain fc env v cases.toList elseBody
  | .call callee _ =>
    let (_, calleeName) := fc.resolveCallee callee
    match panicErrorFor? calleeName with
    | some ctor => s!"throw {ctor}"
    | none => s!"(panic! \"air2lean: unchecked noreturn callee {calleeName}\")"
  | _ => "pure default"

/-- `switch_br` as a chain of `if`/`else if` (a `BitVec` value has no numeral match pattern). -/
partial def emitSwitchChain (fc : FCtx) (env : Array (InstId × String)) (v : Val)
    (cases : List SwitchCase) (elseBody : Array Inst) : String :=
  match cases with
  | [] => emitStmts fc env elseBody.toList
  | c :: rest =>
    let sgn := if fc.valSigned v then "true" else "false"
    let rv := fc.resolveVal env
    let itemConds := (c.items.map fun it => s!"{rv v} == {rv it}").toList
    let rangeConds := (c.ranges.map fun (lo, hi) =>
      s!"(Zig.le {sgn} {rv lo} {rv v} && Zig.le {sgn} {rv v} {rv hi})").toList
    let cond := String.intercalate " || " (itemConds ++ rangeConds)
    s!"if {cond} then {doBlock (emitStmts fc env c.body.toList)}\nelse \
      {doBlock (emitSwitchChain fc env v rest elseBody)}"

end

/-- One `loop` instruction's body as its own top-level def, named `<fnName>.loop<id>` (so a
proof can refer to it — the point of extracting it at all), taking its captured values
(`FCtx.loopCaptures`) as explicit parameters with the same names the body text already uses. -/
def emitLoopDef (fc : FCtx) (loopInst : Inst) : String :=
  match loopInst.op with
  | .loop body =>
    let caps := fc.loopCaptures body
    let paramsStr := String.intercalate " "
      ((caps.map fun (_, name, ty) => s!"({name} : {ty})").toList)
    let initEnv := caps.map fun (id, name, _) => (id, name)
    let bodyStr := emitStmts fc initEnv body.toList
    String.intercalate "\n"
      [s!"def {fc.fnName}.loop{loopInst.id} {paramsStr} : Zig.M {fc.localsName} {fc.exitName} := do",
       indent 2 bodyStr]
  | _ => "" -- unreachable: `emitOneFunction` only calls this with a `.loop` instruction

-- `again` is named too: an inline `fun e => match …` gets a fresh matcher per elaboration,
-- so a proof could not restate it and `rw` with a `Zig.loop_spec` result would not match.
def emitAgainDef (fc : FCtx) (loopInst : Inst) : String :=
  String.intercalate "\n"
    [s!"def {fc.fnName}.again{loopInst.id} : {fc.exitName} → Bool",
     s!"  | .rep{loopInst.id} => true",
     "  | _ => false"]

/-! ## Per-function emission -/

def emitFunctionDef (fc : FCtx) (leanName localsName exitName : String) (paramTys : Array TyId)
    (retTy : TyId) (body : Array Inst) (hasNonRetExit : Bool) : String :=
  let paramsStr := String.intercalate " "
    ((paramTys.mapIdx fun i pt => s!"(p{i} : {fc.emitTyOf pt})").toList)
  let retStr := fc.emitTyOf retTy
  let bodyStr := emitStmts fc #[] body.toList
  -- The `M`-do-block's `σ`/`ε` never appear as a literal type anywhere inside it (`(← get)`,
  -- `.br<k>`, …), so without this ascription nothing pins them down for the elaborator.
  let ascribedBody := s!"({doBlock bodyStr} : Zig.M {localsName} {exitName})"
  let retArm := match fc.tyOfId retTy with
    | .void => "| .ret => pure ()"
    | _ => "| .ret v => pure v"
  -- `ret` is the only constructor when the function has no block/loop control flow at all
  -- (empty `brTargets`/`repTargets`): a wildcard arm after it is then unreachable, which Lean
  -- rejects as a "Redundant alternative" error rather than a warning, so it must be omitted.
  let matchLines :=
    [s!"  {retArm}"] ++ (if hasNonRetExit then ["  | _ => throw .panic"] else [])
  String.intercalate "\n"
    ([s!"def {leanName} {paramsStr} : Zig.Result ({retStr}) := do",
      s!"  let e ← {indentTail 2 ascribedBody}.run' (default : {localsName})",
      "  match e with"] ++ matchLines)

/-- One function's output in four parts: the `Locals`/`Exit` types, the `again<k>` defs, the
`loop<k>` defs (inner loop first), and the function def. `emit` joins them, and puts a
recursive group's loop and function defs into one `mutual` block. -/
structure FuncParts where
  types : List String
  agains : List String
  loops : List String
  defn : String

def emitOneFunction (f : Func) (structNames : Array (String × String))
    (funcNames : Array (String × String)) : FuncParts :=
  let allInsts := f.allInsts
  let leanName := (funcNames.find? (·.1 == f.name)).map (·.2) |>.getD f.name
  let allocs := collectAllocs f.types allInsts
  let blTys := blockLoopTys allInsts
  let brT := brTargets allInsts
  let repT := repTargets allInsts
  let localsName := s!"{leanName}Locals"
  let exitName := s!"{leanName}Exit"
  let fc : FCtx :=
    { types := f.types, structNames, funcNames,
      allocFields := allocs.map fun (i, n, _) => (i, n), blockTys := blTys, allInsts,
      retTy := f.ret, fnName := leanName, localsName, exitName }
  let localsStr := emitLocalsStruct structNames f.types localsName allocs
  let exitStr := emitExitInductive structNames f.types exitName f.ret blTys brT repT
  -- Every `loop` in the function, innermost first: `flattenInst`/`Func.allInsts` visits a node
  -- before its children (pre-order), so a parent loop always precedes a nested one; reversing
  -- flips that to child-before-parent, which is what "the inner loop's def is emitted before
  -- the outer one" needs (`docs/generated-code.md` §Loops).
  let loops := (allInsts.filter fun i => match i.op with | .loop _ => true | _ => false).reverse
  let hasNonRetExit := !brT.isEmpty || !repT.isEmpty
  { types := [localsStr, exitStr]
    agains := (loops.map (emitAgainDef fc)).toList
    loops := (loops.map (emitLoopDef fc)).toList
    defn := emitFunctionDef fc leanName localsName exitName f.params f.ret f.body hasNonRetExit }

/-! ## Call graph / emission order -/

def dedupNames (a : Array String) : Array String :=
  a.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

def calleesOf (allNames : Array String) (f : Func) : Array String :=
  dedupNames (f.allInsts.filterMap fun i => match i.op with
    | .call (.func nm _) _ => if allNames.contains nm then some nm else none
    | _ => none)

/-- DFS post-order over the call graph: a callee before its caller, except inside a cycle. -/
partial def topoVisit (funcs : Array Func) (allNames : Array String)
    (vo : Array String × Array Func) (name : String) : Array String × Array Func :=
  let (visited, order) := vo
  if visited.contains name then (visited, order)
  else
    let visited := visited.push name
    match funcs.find? (·.name == name) with
    | none => (visited, order)
    | some f =>
      let callees := calleesOf allNames f
      let (visited, order) := callees.foldl (topoVisit funcs allNames) (visited, order)
      (visited, order.push f)

def topoOrder (funcs : Array Func) : Array Func :=
  let allNames := funcs.map (·.name)
  (allNames.foldl (topoVisit funcs allNames) (#[], #[])).2

/-- Every function name reachable from `name` by one or more calls. -/
partial def reachable (funcs : Array Func) (allNames : Array String) (name : String) :
    Array String :=
  let rec go (seen : Array String) (todo : List String) : Array String :=
    match todo with
    | [] => seen
    | n :: rest =>
      let next := match funcs.find? (·.name == n) with
        | some f => (calleesOf allNames f).toList.filter (!seen.contains ·)
        | none => []
      go (seen ++ next.toArray) (rest ++ next)
  go #[] [name]

/-- The call-graph groups in emission order: a group is a set of functions that call each other
(a strongly connected component), and it comes after every group that it calls. The second
component is `true` if the group is recursive (more than one function, or a self-call). -/
def callGroups (funcs : Array Func) : Array (Array Func × Bool) :=
  let allNames := funcs.map (·.name)
  let reach := allNames.map fun n => (n, reachable funcs allNames n)
  let reaches (a b : String) : Bool :=
    ((reach.find? (·.1 == a)).map (·.2.contains b)).getD false
  let order := topoOrder funcs
  -- A group is complete at its last member in DFS post-order (the member where the DFS entered
  -- the group), and everything that the group calls is finished before that point.
  let (_, groups) := order.foldl (init := ((#[] : Array String), (#[] : Array (Array Func × Bool))))
    fun (done, groups) f =>
      let done := done.push f.name
      let members := order.filter fun g => g.name == f.name || (reaches f.name g.name && reaches g.name f.name)
      if members.all (done.contains ·.name) && !groups.any (·.1.any (·.name == f.name)) then
        (done, groups.push (members, members.size > 1 || reaches f.name f.name))
      else (done, groups)
  groups

/-! ## Top level -/

/-- `funcs → one Lean source file` importing `ZigLean`, namespaced under `ns`. `prefix_` is
stripped from every Zig name (function or struct) before mangling. -/
def emit (funcs : Array Func) (ns : String) (prefix_ : String) : String :=
  let structs := collectStructs funcs prefix_
  let structNames := structs.map fun s => (s.zigName, s.leanName)
  let funcNames := funcs.map fun f => (f.name, mangleName prefix_ f.name)
  let structsStr := (structs.map (emitStruct structNames)).toList
  let funcsStr := (callGroups funcs).toList.map fun (members, recursive) =>
    let parts := members.toList.map fun f => emitOneFunction f structNames funcNames
    if recursive then
      -- `partial_fixpoint` on every def of the group: the loop defs too, since a loop body can
      -- call a group member. Types and `again` defs do not recurse, so they come first.
      let fix (d : String) := s!"{d}\npartial_fixpoint"
      let defs := parts.flatMap fun p => (p.loops ++ [p.defn]).map fix
      String.intercalate "\n\n"
        (parts.flatMap (·.types) ++ parts.flatMap (·.agains) ++ ["mutual"] ++ defs ++ ["end"])
    else
      String.intercalate "\n\n" (parts.flatMap fun p => p.types ++ p.agains ++ p.loops ++ [p.defn])
  String.intercalate "\n\n"
    (["import ZigLean", s!"\nnamespace {ns}"] ++ structsStr ++ funcsStr ++ [s!"end {ns}"])

end Air2Lean
