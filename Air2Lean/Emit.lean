import Air2Lean.Check

/-!
# Emitter

`emit : Array Func → String → String → String` turns a list of already-checked functions into
one Lean source file: `import ZigLean`, one `namespace <ns>`, struct types once (deduplicated
by Zig name), `mem0` and the `@tagName`/`@errorName` defs if a function uses memory (§Globals),
then per function a generated `<Fn>Locals` structure (one field per `alloc`), a
generated `<Fn>Exit` inductive (`ret` / `br<targetId>` / `rep<targetId>`, one constructor per
distinct branch target reachable in the function), and the function itself as a
`Zig.M <Fn>Locals <Fn>Exit` do-block wrapped by a top-level `def` that unwraps `.ret`.

Assumes its input already passed `Check.lean`: it does not re-validate the subset, and reaches
for `throw .panic` / a `default`-typed placeholder at the handful of spots that are otherwise
statically impossible (an exit other than `.ret` leaving a function's outermost body, an
unresolved name).
-/

namespace Air2Lean

/-- Is `op` a terminator: the one instruction that ends its containing body (`docs/air-json.md`
/ `PLAN.md`)? A noreturn call counts (the `unreach` Sema emits right after it is dead code). -/
def isTerminating (op : Op) : Bool :=
  match op with
  | .br .. | .«repeat» .. | .ret .. | .unreach | .trap | .condBr .. | .switchBr .. => true
  | .retLoad _ => true
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
   "extends", "renaming", "hiding", "at"]

def mangleName (prefix_ : String) (raw : String) : String :=
  let stripped : String :=
    if prefix_.length > 0 && raw.startsWith prefix_ then (raw.drop prefix_.length).toString
    else raw
  let underscored := stripped.replace "." "_"
  if leanKeywords.contains underscored then s!"«{underscored}»" else underscored

def mangleField (raw : String) : String :=
  if leanKeywords.contains raw then s!"«{raw}»" else raw

/-! ## Types (`docs/generated-code.md` §Types) -/

/-- The `Zig.FN` format term for an `n`-bit float type (`ZigLean/Float/Format.lean`). `n` is
always one of `16 32 64 80 128` (`Check.lean`). -/
def floatFmtName (n : Nat) : String :=
  match n with
  | 16 => "Zig.F16" | 32 => "Zig.F32" | 64 => "Zig.F64" | 80 => "Zig.F80" | 128 => "Zig.F128"
  | _ => s!"Zig.Float .f{n}" -- unreachable: Check.lean restricts `n`

/-- `TyId → Lean type` as source text. `structNames` maps the Zig name of a struct, enum or
union to its Lean name. `pureSlice`: `ty` is the type of a value of a pure function, where a
`[]const T` is an `Array` (`docs/generated-code.md` §Memory); everywhere else a slice is a
`Zig.Slice`. -/
partial def emitTy (structNames : Array (String × String)) (types : Array Ty) (ty : Ty)
    (pureSlice : Bool := false) : String :=
  match ty with
  | .int _ bits => s!"BitVec {bits}"
  | .float bits => floatFmtName bits
  | .bool => "Bool"
  | .void => "Unit"
  | .noreturn => "Unit"
  | .ptr "slice" true child =>
    if pureSlice then s!"Array ({emitTy structNames types types[child]!})" else "Zig.Slice"
  | .ptr "slice" .. => "Zig.Slice"
  | .ptr .. => "Zig.Ptr"
  | .array len child => s!"Vector ({emitTy structNames types types[child]!}) {len}"
  | .optional child => s!"Option ({emitTy structNames types types[child]!})"
  | .errorUnion _set payload => s!"Except Zig.ErrName ({emitTy structNames types types[payload]!})"
  | .errorSet _ => "Zig.ErrName"
  | .struct name _ _ | .enum name .. | .union name .. =>
    (structNames.find? (·.1 == name)).map (·.2) |>.getD name
  | .tuple fields =>
    let parts := (fields.map (fun fid => emitTy structNames types types[fid]!)).toList
    if parts.isEmpty then "Unit" else String.intercalate " × " parts
  | .other name => name

/-! ## Named types: emit each distinct Zig struct, enum and union once -/

structure NamedType where
  zigName : String
  leanName : String
  ty : Ty
  srcTypes : Array Ty
  /-- `srcLayouts[i]` is the layout of `srcTypes[i]`. -/
  srcLayouts : Array Layout
  /-- The layout of `ty`. -/
  layout : Layout
  deriving Inhabited

/-- The Lean name of a named Zig type. The tag enum of `union(enum)` has the Zig name
`@typeInfo(U).@"union".tag_type.?`; its Lean name is `<U>Tag`. -/
def namedLeanName (prefix_ : String) (zigName : String) : String :=
  let pre := "@typeInfo("
  let post := ").@\"union\".tag_type.?"
  if zigName.startsWith pre && zigName.endsWith post then
    let u := ((zigName.drop pre.length).dropEnd post.length).toString
    mangleName prefix_ (u ++ "Tag")
  else mangleName prefix_ zigName

/-- The named types that `ty` refers to directly or through arrays, pointers, optionals, error
unions and tuples (not through another named type). -/
partial def namedDeps (types : Array Ty) (ty : Ty) : Array String :=
  let go (id : TyId) : Array String :=
    match types[id]? with
    | some t@(.struct name ..) | some t@(.enum name ..) | some t@(.union name ..) =>
      let _ := t; #[name]
    | some t => namedDeps types t
    | none => #[]
  match ty with
  | .struct _ _ fields | .union _ _ none fields => fields.flatMap (go ·.2)
  | .union _ _ (some tag) fields => go tag ++ fields.flatMap (go ·.2)
  | .enum .. => #[]
  | .ptr "slice" _ c | .array _ c | .optional c => go c
  | .errorUnion _ p => go p
  | .tuple fs => fs.flatMap go
  | _ => #[]

/-- Every named type of `funcs`, each after the named types its fields use. -/
def collectNamed (funcs : Array Func) (prefix_ : String) : Array NamedType := Id.run do
  let mut found : Array NamedType := #[]
  for f in funcs do
    for (ty, i) in f.types.zipIdx do
      match ty with
      | .struct name .. | .enum name .. | .union name .. =>
        let entry : NamedType := { zigName := name, leanName := namedLeanName prefix_ name, ty,
                                   srcTypes := f.types, srcLayouts := f.layouts,
                                   layout := f.layouts[i]?.getD {} }
        match found.findIdx? (·.zigName == name) with
        | none => found := found.push entry
        -- Another function's file can have the layout that this one does not.
        | some k =>
          if found[k]!.layout.size.isNone && entry.layout.size.isSome then
            found := found.set! k entry
      | _ => pure ()
  -- Depth-first: a type after its dependencies. Zig types cannot contain themselves by value,
  -- and `Check.lean` rejects a pointer inside a type; `open` still keeps a cycle finite.
  let mut done : Array String := #[]
  let mut «open» : Array String := #[]
  let mut order : Array NamedType := #[]
  let mut stack : List (String × Bool) := (found.toList.map (·.zigName, false)).reverse
  while !stack.isEmpty do
    match stack with
    | [] => pure ()
    | (n, expanded) :: rest =>
      stack := rest
      if done.contains n then continue
      let some info := found.find? (·.zigName == n) | continue
      if expanded then
        done := done.push n
        order := order.push info
      else if !«open».contains n then
        «open» := «open».push n
        stack := (namedDeps info.srcTypes info.ty).toList.map (·, false) ++ (n, true) :: stack
  return order

/-- An integer as a `BitVec` literal (a constant, or an enum's tag value). -/
def tagLit (bits : Nat) (v : Int) : String :=
  if v < 0 then s!"(-({(-v).toNat} : BitVec {bits}))" else s!"({v.toNat} : BitVec {bits})"

/-- The `Zig.Enc` instance of a struct or enum that can be in memory (`ZigLean/Mem/Enc.lean`):
the size, alignment and field offsets from the exporter. -/
def emitEnc (s : NamedType) : String :=
  let n := s.leanName
  let size := s.layout.size.getD 0
  let head := [s!"instance : Zig.Enc {n} where", s!"  size := {size}",
               s!"  align := {s.layout.align.getD 1}"]
  match s.ty with
  | .struct _ _ fields =>
    let parts := (fields.zip s.layout.offsets).toList.map fun ((f, _), o) =>
      s!"({o}, Zig.Enc.encode v.{mangleField f})"
    let decs := (fields.zip s.layout.offsets).toList.map fun ((f, _), o) =>
      s!"{mangleField f} := ← Zig.Enc.decodeAt bs {o}"
    String.intercalate "\n" (head ++
      [s!"  encode v := Zig.Enc.fields {size} [{String.intercalate ", " parts}]",
       s!"  decode bs := do pure \{ {String.intercalate ", " decs} }"])
  | .enum _ tag exhaustive _ =>
    let (signed, bits) := match s.srcTypes[tag]! with | .int sg b => (sg, b) | _ => (false, 0)
    let dec := if exhaustive then
        -- A tag value without a name is not a value of the enum: illegal behaviour.
        [s!"    match {n}.ofInt? (Zig.val {signed} b) with",
         "    | some v => pure v", "    | none => throw .illegal"]
      else ["    pure ⟨b⟩"]
    String.intercalate "\n" (head ++
      ["  encode v := Zig.Enc.encode v.toBits", "  decode bs := do",
       s!"    let b : BitVec {bits} ← Zig.Enc.decode bs"] ++ dec)
  | _ => ""

def emitNamedType (structNames : Array (String × String)) (s : NamedType) : String :=
  let tyStr (id : TyId) : String := emitTy structNames s.srcTypes s.srcTypes[id]!
  let n := s.leanName
  match s.ty with
  | .enum _ tag exhaustive fields =>
    let (signed, bits) := match s.srcTypes[tag]! with | .int sg b => (sg, b) | _ => (false, 0)
    let lo : Int := if signed then -(2 ^ (bits - 1)) else 0
    let hi : Int := if signed then 2 ^ (bits - 1) - 1 else 2 ^ bits - 1
    if exhaustive then
      let ctors := fields.toList.map fun (f, _) => s!"  | {mangleField f}"
      let toBits := fields.toList.map fun (f, v) => s!"  | .{mangleField f} => {tagLit bits v}"
      let ofInt := fields.foldr (fun (f, v) acc => s!"if v = {v} then some .{mangleField f} else {acc}") "none"
      String.intercalate "\n"
        ([s!"inductive {n} where"] ++ ctors ++ ["  deriving Repr, Inhabited, DecidableEq", "",
          s!"def {n}.toBits : {n} → BitVec {bits}"] ++ toBits ++ ["",
          s!"def {n}.ofInt? (v : Int) : Option {n} :=", s!"  {ofInt}", "",
          s!"def {n}.isNamed (_ : {n}) : Bool := true"])
    else
      let named := fields.toList.map fun (f, v) => s!"def {n}.{mangleField f} : {n} := ⟨{tagLit bits v}⟩"
      let isNamed := String.intercalate " || " (fields.toList.map fun (_, v) => s!"e.bits == {tagLit bits v}")
      String.intercalate "\n"
        ([s!"structure {n} where", s!"  bits : BitVec {bits}", "  deriving Repr, Inhabited, DecidableEq", ""]
          ++ named ++ ["",
          s!"def {n}.toBits (e : {n}) : BitVec {bits} := e.bits", "",
          s!"def {n}.ofInt? (v : Int) : Option {n} :=",
          s!"  if {lo} ≤ v ∧ v ≤ {hi} then some ⟨BitVec.ofInt {bits} v⟩ else none", "",
          s!"def {n}.isNamed (e : {n}) : Bool := {if isNamed.isEmpty then "false" else isNamed}"])
  | .union _ _ tag fields =>
    let tagName := match tag.bind (s.srcTypes[·]?) with
      | some t => emitTy structNames s.srcTypes t
      | none => "Unit"
    let isVoid (id : TyId) : Bool := s.srcTypes[id]! == .void
    let wild := if fields.size > 1 then ["  | _ => throw .panic"] else []
    let ctors := fields.toList.map fun (f, id) =>
      if isVoid id then s!"  | {mangleField f}" else s!"  | {mangleField f} (v : {tyStr id})"
    let tagArms := fields.toList.map fun (f, id) =>
      let pat := if isVoid id then s!".{mangleField f}" else s!".{mangleField f} _"
      s!"  | {pat} => .{mangleField f}"
    let perField := fields.toList.flatMap fun (f, id) =>
      let fm := mangleField f
      let (pat, val, pty) :=
        if isVoid id then (s!".{fm}", "()", "Unit") else (s!".{fm} v", "v", tyStr id)
      -- Another field is active: `f` becomes active, its payload `default` (Zig: undefined).
      let (keep, apply, fresh, applyFresh, g) :=
        if isVoid id then (s!".{fm}", s!".{fm}", s!".{fm}", s!".{fm}", "_g")
        else (s!".{fm} v", s!".{fm} (g v)", s!".{fm} default", s!".{fm} (g default)", "g")
      let multi (l : String) : List String := if fields.size > 1 then [l] else []
      ["", s!"def {n}.get_{f} : {n} → Zig.Result ({pty})", s!"  | {pat} => pure {val}"] ++ wild ++
      ["", s!"def {n}.modify_{f} ({g} : {pty} → {pty}) : {n} → {n}", s!"  | {pat} => {apply}"] ++
        multi s!"  | _ => {applyFresh}" ++
      ["", s!"def {n}.setTag_{f} : {n} → {n}", s!"  | {pat} => {keep}"] ++ multi s!"  | _ => {fresh}"
    String.intercalate "\n"
      ([s!"inductive {n} where"] ++ ctors ++ ["  deriving Repr, Inhabited, DecidableEq", "",
        s!"def {n}.tag : {n} → {tagName}"] ++ tagArms ++ perField)
  | .struct _ _ fields =>
    let fieldLines := (fields.map fun (fname, fty) => s!"  {mangleField fname} : {tyStr fty}").toList
    String.intercalate "\n"
      ([s!"structure {n} where"] ++ fieldLines ++ ["  deriving Repr, Inhabited, DecidableEq"])
  | _ => ""

/-- The named types reachable from `id` through struct fields, optionals and arrays, that the
memory model encodes (`modelLayout`). -/
partial def memNamed (types : Array Ty) (layouts : Array Layout) (acc : Array String) (id : TyId) :
    Array String :=
  if (modelLayout types layouts id).toOption.isNone then acc else
  match types[id]? with
  | some (.struct name _ fs) =>
    if acc.contains name then acc else fs.foldl (fun a (_, t) => memNamed types layouts a t) (acc.push name)
  | some (.enum name ..) => if acc.contains name then acc else acc.push name
  | some (.optional c) | some (.array _ c) => memNamed types layouts acc c
  | _ => acc

/-- The named types that get a `Zig.Enc` instance: those that a pointer of a function that uses
memory can point to, and the types of the globals. A pure function never has one, so v0 translations do not change. -/
def encTypeNames (funcs : Array Func) (memFuncs : Array String) : Array String :=
  funcs.foldl (init := #[]) fun acc f =>
    if !memFuncs.contains f.name then acc
    else
      let acc := f.globals.foldl (fun acc g => memNamed f.types f.layouts acc g.ty) acc
      f.types.foldl (init := acc) fun acc t => match t with
        | .ptr _ _ c => memNamed f.types f.layouts acc c
        | _ => acc

/-- A named type, and its `Zig.Enc` instance if it is in `encNames`. -/
def emitNamed (structNames : Array (String × String)) (encNames : Array String)
    (s : NamedType) : String :=
  let body := emitNamedType structNames s
  if encNames.contains s.zigName then s!"{body}\n\n{emitEnc s}" else body

/-! ## Float semantics mode (`--float-semantics`, `docs/floats.md` §Semantics) -/

/-- `ieee`: every float op is the model's own IEEE-correct result (`ZigLean/Float/Ops.lean`;
what a proof assumes). `compilerRt`: `f128` division and `@mulAdd` instead match the compiler_rt
routines the reference target (`x86_64-linux -mcpu=baseline`) actually calls, bit-exact
(`ZigLean/Float/CompilerRt.lean`) — opt-in per example (`examples/<ex>/translate.args`), since
most examples never reach the divergence and a proof should not have to know it exists. Groups C
(f80 invalid encodings) and D (f32/f64 mixed-sign-zero `@min`/`@max`) throw `.unspecified` in
both modes, unconditionally: `docs/floats.md` §f80 invalid encodings, §+0 and −0 in @min/@max. -/
inductive FloatSemantics where
  | ieee
  | compilerRt
  deriving DecidableEq, Repr

/-! ## Per-function static context -/

/-- One step from a local to a place inside it: a struct field, or the payload of a union
field. -/
inductive PathStep where
  | field (name : String)
  /-- `union`: the union's Lean name; `name`: the field's Zig name (`FCtx.unionField?`). -/
  | ufield (union : String) (name : String)
  deriving Inhabited

structure FCtx where
  types : Array Ty
  structNames : Array (String × String)
  funcNames : Array (String × String)
  /-- `alloc` inst id → its `<Fn>Locals` field name. -/
  allocFields : Array (InstId × String)
  /-- Place (pointer into a local) inst id → its `alloc` and the path from it (`FCtx.places`). -/
  places : Array (InstId × InstId × Array PathStep)
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
  /-- `--float-semantics` (default `ieee`), for `.div`/`.divFloat`/`.mulAdd` on a float operand. -/
  floatSemantics : FloatSemantics
  /-- The Zig version that wrote the AIR (`Func.zigVersion`), for the float ops whose result
  differs by version (`docs/floats.md` §Per-version differences). -/
  zigVersion : String
  /-- This function uses memory (`Air2Lean/Memory.lean`): it returns `Zig.MemM`, and its body
  runs in `Zig.MM`. -/
  mem : Bool
  /-- The names of the functions that use memory. -/
  memFuncs : Array String
  layouts : Array Layout
  /-- The `alloc`s whose address escapes: stack blocks, not places. -/
  escaping : Array InstId
  /-- The block of each global of `Func.globals`: its index in the program's globals
  (`emitGlobals`). -/
  globalIds : Array Nat := #[]

def FCtx.tyOfId (fc : FCtx) (tid : TyId) : Ty := fc.types[tid]!
def FCtx.emitTyOf (fc : FCtx) (tid : TyId) : String :=
  emitTy fc.structNames fc.types (fc.tyOfId tid) (pureSlice := !fc.mem)
def FCtx.tyBits (fc : FCtx) (tid : TyId) : Nat := match fc.tyOfId tid with | .int _ b => b | _ => 0
def FCtx.tySigned (fc : FCtx) (tid : TyId) : Bool :=
  match fc.tyOfId tid with | .int s _ => s | _ => false

def FCtx.instTyId (fc : FCtx) (id : InstId) : TyId :=
  (fc.allInsts.find? (·.id == id)).map (·.ty) |>.getD 0

def FCtx.valTy (fc : FCtx) (v : Val) : Ty :=
  match v with
  | .inst id => fc.tyOfId (fc.instTyId id)
  | .int tid _ => fc.tyOfId tid
  | .float tid _ => fc.tyOfId tid
  | .bool _ => .bool
  | .void => .void
  | .func .. => .void
  | .undef tid | .optNull tid | .optSome tid _ | .err tid _ | .errUnionErr tid _
  | .errUnionOk tid _ | .enumTag tid _ | .unionVal tid .. | .agg tid _ | .ptrConst tid ..
  | .ptrOther tid _ | .sliceConst tid .. => fc.tyOfId tid

/-- The type ID of `v`; `none` for a constant without a type. -/
def FCtx.valTyId? (fc : FCtx) (v : Val) : Option TyId :=
  match v with
  | .inst id => some (fc.instTyId id)
  | v => v.constTy?

def FCtx.valSigned (fc : FCtx) (v : Val) : Bool := match fc.valTy v with | .int s _ => s | _ => false

def FCtx.isFloatTy (fc : FCtx) (tid : TyId) : Bool :=
  match fc.tyOfId tid with | .float _ => true | _ => false

/-- Is `v`'s type a float? Dispatches the shared ops (`add`/`div`/`min`/`max`/`cmp`/`neg`/…)
between the int and float `ZigLean` functions. -/
def FCtx.isFloat (fc : FCtx) (v : Val) : Bool := match fc.valTy v with | .float _ => true | _ => false

/-- `"Rt"` in `compiler-rt` mode: the model ops that differ from IEEE on the reference target
(`Zig.Float.divRt`, `fmaRtChk`, …; `docs/floats.md` §`--float-semantics`). -/
def FCtx.rtSuffix (fc : FCtx) : String :=
  match fc.floatSemantics with | .ieee => "" | .compilerRt => "Rt"

/-- Before 0.16.0, compiler_rt rounded the `f128` square root through `f64` (`sqrt.zig`) and
flushed a subnormal `f128` quotient to zero (`divtf3.zig`). 0.16.0 rounds the square root
correctly, and rounds a subnormal quotient in its own way (`Float.divRt016`). -/
def FCtx.zigBefore016 (fc : FCtx) : Bool := fc.zigVersion == "0.14.1" || fc.zigVersion == "0.15.2"

/-- `rtSuffix` for the float divisions: `divRt` before 0.16.0, `divRt016` from 0.16.0. -/
def FCtx.divRtSuffix (fc : FCtx) : String :=
  if fc.rtSuffix == "" || fc.zigBefore016 then fc.rtSuffix else "Rt016"

/-- The `FloatFmt` term (`.f16` … `.f128`) for the type at `tid`, for the ops whose target format
is not otherwise inferable (`Zig.Float.conv`/`Zig.Float.ofInt`'s explicit `fmt` argument). -/
def FCtx.floatFmtTerm (fc : FCtx) (tid : TyId) : String :=
  match fc.tyOfId tid with
  | .float n => match n with
    | 16 => ".f16" | 32 => ".f32" | 64 => ".f64" | 80 => ".f80" | 128 => ".f128"
    | _ => ".f64" -- unreachable: Check.lean restricts `n`
  | _ => ".f64" -- unreachable: only called on a float-typed instruction result

def FCtx.targetTy (fc : FCtx) (target : InstId) : Ty :=
  match fc.blockTys.find? (·.1 == target) with
  | some (_, t) => fc.tyOfId t
  | none => .void

partial def FCtx.resolveVal (fc : FCtx) (env : Array (InstId × String)) (v : Val) : String :=
  match v with
  | .inst id => (env.find? (·.1 == id)).map (·.2) |>.getD s!"(panic! \"air2lean: unbound inst {id}\")"
  | .int tid n => tagLit (fc.tyBits tid) n
  | .float tid bits =>
    let n := match fc.tyOfId tid with | .float b => b | _ => 0
    s!"(Zig.Float.ofBits ({bits} : BitVec {n}) : {fc.emitTyOf tid})"
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
  | .enumTag tid v =>
    let e := fc.emitTyOf tid
    match fc.tyOfId tid with
    | .enum _ tag _ fields =>
      match fields.find? (·.2 == v) with
      | some (f, _) => s!"{e}.{mangleField f}"
      | none => s!"({e}.mk (BitVec.ofInt {fc.tyBits tag} ({v})))"
    | _ => "default" -- unreachable: `Json.lean` builds `enumTag` only for an enum type
  | .unionVal tid idx p =>
    let u := fc.emitTyOf tid
    match fc.tyOfId tid with
    | .union _ _ _ fields =>
      match fields[idx]? with
      | some (f, fty) =>
        if fc.tyOfId fty == .void then s!"{u}.{mangleField f}"
        else s!"({u}.{mangleField f} {fc.resolveVal env p})"
      | none => "default"
    | _ => "default" -- unreachable: `Json.lean` builds `unionVal` only for a union type
  | .agg tid elems =>
    let items (xs : Array Val) := ", ".intercalate (xs.map (fc.resolveVal env)).toList
    match fc.tyOfId tid with
    -- The sentinel is not an item of the value.
    | .array len _ => s!"(#v[{items (elems.extract 0 len)}] : {fc.emitTyOf tid})"
    | .struct _ _ fields =>
      let assigns := (fields.zip elems).toList.map fun ((f, _), e) =>
        s!"{mangleField f} := {fc.resolveVal env e}"
      s!"(\{ {", ".intercalate assigns} } : {fc.emitTyOf tid})"
    | .tuple _ => if elems.isEmpty then "()" else s!"({items elems})"
    | _ => "default" -- unreachable: the exporter writes `elems` only for these types
  | .ptrConst _ g off => s!"(⟨some {fc.globalIds[g]!}, {off}⟩ : Zig.Ptr)"
  | .ptrOther .. => "(panic! \"air2lean: a pointer constant without a global\")"
  | .sliceConst _ p len => s!"(⟨{fc.resolveVal env p}, {fc.resolveVal env len}⟩ : Zig.Slice)"

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

/-- The Lean type of `v`. -/
def FCtx.emitValTy (fc : FCtx) (v : Val) : String :=
  emitTy fc.structNames fc.types (fc.valTy v) (pureSlice := !fc.mem)

def isEnumTy (t : Ty) : Bool := match t with | .enum .. => true | _ => false

/-- `@enumFromInt`, `@intFromEnum` (an `intcast` or `bitcast` with an enum on one side), and
`@intCast` between integers. -/
def FCtx.enumIntCast (fc : FCtx) (a : Val) (dstId : TyId) (av : String) : String :=
  let dst := fc.tyOfId dstId
  match fc.valTy a, dst with
  | .enum _ tag _ _, .enum .. =>
    s!"Zig.enumOf ({fc.emitTyOf dstId}.ofInt? (Zig.val {fc.tySigned tag} ({fc.emitValTy a}.toBits {av})))"
  | _, .enum .. =>
    -- An unnamed value of an exhaustive enum: `invalidEnumValue` (`.panic`).
    s!"Zig.enumOf ({fc.emitTyOf dstId}.ofInt? (Zig.val {fc.valSigned a} {av}))"
  | .enum _ tag _ _, _ =>
    let bits := s!"({fc.emitValTy a}.toBits {av})"
    if fc.tyOfId tag == dst then s!"pure {bits}"
    else s!"Zig.intCast {fc.tySigned tag} {fc.tySigned dstId} {fc.tyBits dstId} {bits}"
  | _, _ => s!"Zig.intCast {fc.valSigned a} {fc.tySigned dstId} {fc.tyBits dstId} {av}"

/-- The Lean name of a union type, and its field `idx`: the Zig name (in accessor names
`get_f`, `modify_f`, `setTag_f`; `mangleField` for the constructor) and whether it has no
payload. -/
def FCtx.unionField? (fc : FCtx) (uty : Ty) (idx : Nat) : Option (String × String × Bool) :=
  match uty with
  | .union name _ _ fields =>
    let u := (fc.structNames.find? (·.1 == name)).map (·.2) |>.getD name
    (fields[idx]?).map fun (f, fty) => (u, f, fc.tyOfId fty == .void)
  | _ => none

/-- The field of union type `uty` whose tag has the value of the enum constant `tag`. -/
def FCtx.unionFieldOfTag? (fc : FCtx) (uty : Ty) (tag : Val) : Option (String × String × Bool) :=
  match uty, tag with
  | .union _ _ (some tagTy) fields, .enumTag _ v =>
    match fc.tyOfId tagTy with
    | .enum _ _ _ tagFields => do
      let (fname, _) ← tagFields.find? (·.2 == v)
      let idx ← fields.findIdx? (·.1 == fname)
      fc.unionField? uty idx
    | _ => none
  | _, _ => none

/-- The child type of a pointer-typed instruction. -/
def FCtx.pointee (fc : FCtx) (id : InstId) : Ty :=
  match fc.tyOfId (fc.instTyId id) with
  | .ptr _ _ c => fc.tyOfId c
  | t => t

/-- The child type of the pointer `v`. -/
def FCtx.pointeeOf (fc : FCtx) (v : Val) : Ty :=
  match fc.valTy v with
  | .ptr _ _ c => fc.tyOfId c
  | _ => .void

/-- Every place of the function (`Check.lean`): an `alloc` with the empty path, a field pointer
of a place with one more step, a `bitcast` of a place with the same path. -/
def FCtx.computePlaces (fc : FCtx) : Array (InstId × InstId × Array PathStep) :=
  fc.allInsts.foldl (init := #[]) fun acc i =>
    match i.op with
    | .alloc => if fc.escaping.contains i.id then acc else acc.push (i.id, i.id, #[])
    | .fieldPtr (.inst b) idx =>
      match acc.find? (·.1 == b) with
      | some (_, root, path) =>
        let base := fc.pointee b
        let step := match base with
          | .struct _ _ fields =>
            PathStep.field ((fields[idx]?).map (mangleField ·.1) |>.getD s!"fld{idx}")
          | .union .. =>
            match fc.unionField? base idx with
            | some (u, f, _) => .ufield u f
            | none => .field s!"fld{idx}"
          | _ => .field s!"fld{idx}"
        acc.push (i.id, root, path.push step)
      | none => acc
    | .sliceFieldPtr len (.inst b) =>
      match acc.find? (·.1 == b) with
      | some (_, root, path) => acc.push (i.id, root, path.push (.field (if len then "len" else "ptr")))
      | none => acc
    | .bitcast (.inst b) =>
      match acc.find? (·.1 == b) with
      | some (_, root, path) => acc.push (i.id, root, path)
      | none => acc
    | _ => acc

def FCtx.place? (fc : FCtx) (v : Val) : Option (String × Array PathStep) :=
  match v with
  | .inst id => do
    let (_, root, path) ← fc.places.find? (·.1 == id)
    let (_, field) ← fc.allocFields.find? (·.1 == root)
    pure (field, path)
  | _ => none

def FCtx.isPlace (fc : FCtx) (v : Val) : Bool := (fc.place? v).isSome

/-- The value at a place, as a term inside a `do` block. -/
def FCtx.loadPlace (fc : FCtx) (v : Val) : String :=
  match fc.place? v with
  | some (field, path) =>
    path.foldl (init := s!"(← get).{field}") fun e step =>
      match step with
      | .field f => s!"({e}).{f}"
      | .ufield u f => s!"(← {if fc.mem then "Zig.callR" else "Zig.call"} ({u}.get_{f} {e}))"
  | none => "(panic! \"air2lean: load through a pointer that is not a place\")"

/-- `base` with the value `old` at `path` replaced by `new old`. -/
def setPath (path : List PathStep) (new : String → String) (base : String) : String :=
  match path with
  | [] => new base
  | .field f :: rest => s!"\{ {base} with {f} := {setPath rest new s!"({base}).{f}"} }"
  | .ufield u f :: rest =>
    let inner := setPath rest new "x"
    let x := if inner == setPath rest new "y" then "_" else "x"
    s!"({u}.modify_{f} (fun {x} => {inner}) {base})"

/-- The statement that replaces the value `old` at a place by `new old`. -/
def FCtx.modifyPlace (fc : FCtx) (ptr : Val) (new : String → String) : String :=
  match fc.place? ptr with
  | some (field, path) =>
    s!"modify (fun s => \{ s with {field} := {setPath path.toList new s!"s.{field}"} })"
  | none => "(panic! \"air2lean: store through a pointer that is not a place\")"

/-- The statement that writes `v` to a place. -/
def FCtx.storePlace (fc : FCtx) (ptr : Val) (v : String) : String :=
  fc.modifyPlace ptr fun _ => v

/-! ## Memory (`docs/generated-code.md` §Memory) -/

/-- The body monad: `Zig.M` (pure) or `Zig.MM` (uses memory). -/
def FCtx.monad (fc : FCtx) : String := if fc.mem then "Zig.MM" else "Zig.M"

/-- A `Zig.Result` term called from the body. -/
def FCtx.liftR (fc : FCtx) (e : String) : String :=
  if fc.mem then s!"Zig.callR ({e})" else s!"Zig.call ({e})"

/-- The alignment of an access through the pointer `v`: its type's `align(N)`. -/
def FCtx.ptrAlign (fc : FCtx) (v : Val) : Nat :=
  ((fc.valTyId? v).bind fun t => fc.layouts[t]?.bind (·.ptrAlign)).getD 1

/-- The Lean type of the value that the pointer `v` points to. -/
def FCtx.pointeeTy (fc : FCtx) (v : Val) : String := emitTy fc.structNames fc.types (fc.pointeeOf v)

/-- The byte offset of field `idx` of the struct that the pointer `base` points to. -/
def FCtx.fieldOffset (fc : FCtx) (base : Val) (idx : Nat) : Nat :=
  match fc.valTy base with
  | .ptr _ _ c => (fc.layouts[c]?.bind (·.offsets[idx]?)).getD 0
  | _ => 0

/-- The item type of the slice, many-pointer or array pointer `v`. -/
def FCtx.itemTyId (fc : FCtx) (v : Val) : TyId :=
  ((fc.valTyId? v).bind (itemTy fc.types)).getD 0

/-- The size in bytes of the type `tid` (the exporter's `abi_size`). -/
def FCtx.sizeOf (fc : FCtx) (tid : TyId) : Nat := (fc.layouts[tid]?.bind (·.size)).getD 0

/-- The alignment of an access to an item of `v`: the pointer's `align(N)`, at most the item's own
alignment (item 1 of an `align(8)` pointer to `u32` is only 4-aligned). -/
def FCtx.itemAlign (fc : FCtx) (v : Val) : Nat :=
  Nat.min (fc.ptrAlign v) ((fc.layouts[fc.itemTyId v]?.bind (·.align)).getD 1)

/-- `v` is a slice (not a many-pointer or an array pointer). -/
def FCtx.isSlice (fc : FCtx) (v : Val) : Bool :=
  match fc.valTy v with | .ptr "slice" .. => true | _ => false

/-- The item pointer and the item count of the slice or array pointer `v`, as terms. -/
def FCtx.itemsOf (fc : FCtx) (v : Val) (rv : String) : String × String :=
  if fc.isSlice v then (s!"{rv}.ptr", s!"{rv}.len")
  else match fc.pointeeOf v with
    | .array len _ => (rv, s!"({len} : BitVec 64)")
    | _ => (rv, "(panic! \"air2lean: items of a pointer without a length\")")

/-- `v` is a pointer to memory: not a place. -/
def FCtx.isMemPtr (fc : FCtx) (v : Val) : Bool :=
  !fc.isPlace v && match fc.valTy v with | .ptr .. => true | _ => false

/-- A load through a pointer to memory. -/
def FCtx.loadMem (fc : FCtx) (ptr : Val) (p : String) : String :=
  s!"Zig.load ({fc.pointeeTy ptr}) {fc.ptrAlign ptr} {p}"

/-- A load of item `i` of the slice, many-pointer or array pointer `v`, whose item pointer is
`p`. -/
def FCtx.loadItem (fc : FCtx) (v : Val) (p i : String) : String :=
  let item := fc.itemTyId v
  s!"Zig.load ({emitTy fc.structNames fc.types (fc.tyOfId item)}) {fc.itemAlign v} \
    ({p}.elem {fc.sizeOf item} {i})"

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

/-- An escaping `alloc`'s field holds the pointer to its stack block. `mem`: the function uses
memory. -/
def emitLocalsStruct (structNames : Array (String × String)) (types : Array Ty)
    (localsName : String) (allocs : Array (InstId × String × TyId)) (escaping : Array InstId)
    (mem : Bool) : String :=
  let lines := (allocs.map fun (aid, nm, cty) =>
    if escaping.contains aid then s!"  {nm} : Zig.Ptr"
    else s!"  {nm} : {emitTy structNames types types[cty]! (pureSlice := !mem)}").toList
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
    (exitName : String) (retTy : TyId) (blTys : Array (InstId × TyId)) (brT repT : Array InstId)
    (mem : Bool) : String :=
  let retLine := match types[retTy]! with
    | .void => "  | ret"
    | rt => s!"  | ret (v : {emitTy structNames types rt (pureSlice := !mem)})"
  let brLines := (brT.map fun k =>
    let kty := (blTys.find? (·.1 == k)).map (fun (_, t) => types[t]!) |>.getD .void
    match kty with
    | .void => s!"  | br{k}"
    | t => s!"  | br{k} (v : {emitTy structNames types t (pureSlice := !mem)})").toList
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
  | .divFloat a b => #[a, b]
  | .minMax _ a b => #[a, b]
  | .withOverflow _ a b => #[a, b]
  | .bit _ a b => #[a, b]
  | .not a => #[a]
  | .neg a => #[a]
  | .abs a => #[a]
  | .shift _ a b => #[a, b]
  | .cmp _ a b => #[a, b]
  | .boolAnd a b => #[a, b]
  | .boolOr a b => #[a, b]
  | .intCast a => #[a]
  | .trunc a => #[a]
  | .bitcast a => if fc.isPlace a then #[] else #[a]
  | .floatRound _ a => #[a]
  | .sqrt a => #[a]
  | .libm _ a => #[a]
  | .mulAdd a b c => #[a, b, c]
  | .floatConv a => #[a]
  | .floatFromInt a => #[a]
  | .intFromFloat _ a => #[a]
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
  | .isNamedEnum a => #[a]
  | .unionTag a => #[a]
  | .unionInit _ a => #[a]
  | .alloc => #[]
  | .fieldPtr base _ => if fc.isMemPtr base then #[base] else #[]
  | .setUnionTag .. => #[]
  | .retLoad p | .load p => if fc.isMemPtr p then #[p] else #[]
  | .isNullPtr _ p | .optPayloadPtr _ p => #[p]
  | .store p v => (if fc.isMemPtr p then #[p] else #[]) ++ #[v]
  | .sliceFieldPtr _ p => if fc.isMemPtr p then #[p] else #[]
  | .ptrAdd _ a b | .elemPtr a b | .ptrElemVal a b | .arrayElemVal a b | .slice a b
  | .memset a b | .memcpy a b => #[a, b]
  | .slicePtr a | .arrayToSlice a | .tagName a | .errorName a => #[a]
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
  s!"({doBlock body} : {fc.monad} {fc.localsName} {fc.exitName})"

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
    -- A float operand always has `mode = .checked`: `Check.lean` rejects the other modes.
    let expr :=
      if fc.isFloat a then
        let f := match op with | .add => "Zig.Float.add" | .sub => "Zig.Float.sub" | .mul => "Zig.Float.mul"
        s!"pure ({f} {rv a} {rv b})"
      else
        let sgn := if fc.valSigned a then "true" else "false"
        match op, mode with
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
    let expr :=
      if fc.isFloat a then
        match op with
        | .divTrunc =>
          let f := s!"Zig.Float.divTrunc{fc.divRtSuffix}"
          s!"pure ({f} {rv a} {rv b})"
        | .divFloor =>
          let f := s!"Zig.Float.divFloor{fc.divRtSuffix}"
          s!"pure ({f} {rv a} {rv b})"
        | .divExact =>
          let f := s!"Zig.Float.div{fc.divRtSuffix}"
          s!"pure ({f} {rv a} {rv b})"
        -- Group C's guard applies in both modes, so `rem`/`mod` never switch on `floatSemantics`.
        | .rem => s!"Zig.Float.remChk {rv a} {rv b}"
        | .mod => s!"Zig.Float.modChk {rv a} {rv b}"
      else
        let sgn := if fc.valSigned a then "true" else "false"
        let f := match op with
          | .divTrunc => "Zig.divTrunc" | .divFloor => "Zig.divFloor" | .divExact => "Zig.divExact"
          | .rem => "Zig.rem" | .mod => "Zig.mod"
        s!"{f} {sgn} {rv a} {rv b}"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .divFloat a b =>
    -- `div_float` (plain `/` on floats): group A's guard, same mode dispatch as `.divExact`.
    let f := s!"Zig.Float.div{fc.divRtSuffix}"
    let (env, l) := bindLet fc env inst.id s!"pure ({f} {rv a} {rv b})"; (env, some l)
  | .minMax isMax a b =>
    let expr :=
      if fc.isFloat a then
        -- Group D's guard applies in both modes, so `min`/`max` never switch on `floatSemantics`.
        let f := if isMax then "Zig.Float.maxChk" else "Zig.Float.minChk"
        s!"{f} {rv a} {rv b}"
      else
        let sgn := if fc.valSigned a then "true" else "false"
        let f := if isMax then "Zig.max" else "Zig.min"
        s!"pure ({f} {sgn} {rv a} {rv b})"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
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
    if fc.isFloat a then
      let (env, l) := bindLet fc env inst.id s!"pure (Zig.Float.neg {rv a})"; (env, some l)
    else
      let (env, l) := bindLet fc env inst.id s!"Zig.neg {if fc.valSigned a then "true" else "false"} {rv a}"
      (env, some l)
  | .abs a => let (env, l) := bindLet fc env inst.id s!"pure (Zig.Float.abs {rv a})"; (env, some l)
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
    let expr :=
      if fc.isFloat a then
        match op with
        | .lt => s!"Zig.Float.lt {rv a} {rv b}" | .le => s!"Zig.Float.le {rv a} {rv b}"
        | .gt => s!"Zig.Float.gt {rv a} {rv b}" | .ge => s!"Zig.Float.ge {rv a} {rv b}"
        | .eq => s!"Zig.Float.eq {rv a} {rv b}" | .ne => s!"Zig.Float.ne {rv a} {rv b}"
      else
        let sgn := if fc.valSigned a then "true" else "false"
        match op with
        | .lt => s!"Zig.lt {sgn} {rv a} {rv b}" | .le => s!"Zig.le {sgn} {rv a} {rv b}"
        | .gt => s!"Zig.gt {sgn} {rv a} {rv b}" | .ge => s!"Zig.ge {sgn} {rv a} {rv b}"
        | .eq => s!"{rv a} == {rv b}" | .ne => s!"{rv a} != {rv b}"
    -- The order of two pointers is the order of their addresses (`Zig.ptrAddr`).
    let ptrOrder := match fc.valTy a, op with
      | .ptr .., .lt => some s!"Zig.ptrLt {rv a} {rv b}"
      | .ptr .., .le => some s!"Zig.ptrLe {rv a} {rv b}"
      | .ptr .., .gt => some s!"Zig.ptrLt {rv b} {rv a}"
      | .ptr .., .ge => some s!"Zig.ptrLe {rv b} {rv a}"
      | _, _ => none
    let expr := match ptrOrder with
      | some e => s!"Zig.callM ({e})"
      | none => s!"pure ({expr})"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .boolAnd a b => let (env, l) := bindLet fc env inst.id s!"pure ({rv a} && {rv b})"; (env, some l)
  | .boolOr a b => let (env, l) := bindLet fc env inst.id s!"pure ({rv a} || {rv b})"; (env, some l)
  | .intCast a =>
    let (env, l) := bindLet fc env inst.id (fc.enumIntCast a inst.ty (rv a)); (env, some l)
  | .trunc a =>
    let (env, l) := bindLet fc env inst.id s!"pure (Zig.trunc {fc.tyBits inst.ty} {rv a})"
    (env, some l)
  | .bitcast a =>
    if fc.isPlace a then (env, none) else
    if isEnumTy (fc.valTy a) || isEnumTy (fc.tyOfId inst.ty) then
      let (env, l) := bindLet fc env inst.id (fc.enumIntCast a inst.ty (rv a)); (env, some l)
    else
    let srcFloat := fc.isFloat a
    let dstFloat := fc.isFloatTy inst.ty
    let expr :=
      if srcFloat && !dstFloat then s!"Zig.Float.toBits? {rv a}"
      else if !srcFloat && dstFloat then s!"pure ((Zig.Float.ofBits {rv a}) : {fc.emitTyOf inst.ty})"
      else s!"pure ({rv a})"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .floatRound op a =>
    -- Group C's guard applies in both modes, so these never switch on `floatSemantics`.
    let f := match op with
      | .floor => "Zig.Float.floorChk" | .ceil => "Zig.Float.ceilChk"
      | .trunc => "Zig.Float.truncChk" | .round => "Zig.Float.roundChk"
    let (env, l) := bindLet fc env inst.id s!"{f} {rv a}"; (env, some l)
  | .sqrt a =>
    let f := if fc.zigBefore016 && fc.valTy a == .float 128 then "Zig.Float.sqrtF128ViaF64"
      else "Zig.Float.sqrt"
    let (env, l) := bindLet fc env inst.id s!"pure ({f} {rv a})"; (env, some l)
  | .libm op a =>
    let opName := match op with
      | .sin => ".sin" | .cos => ".cos" | .tan => ".tan" | .exp => ".exp"
      | .exp2 => ".exp2" | .log => ".log" | .log2 => ".log2" | .log10 => ".log10"
    let (env, l) := bindLet fc env inst.id s!"pure (Zig.Float.libm {opName} {rv a})"; (env, some l)
  | .mulAdd a b c =>
    -- Group C's guard applies in both modes; group B's dispatch picks `fma` vs `fmaRt` under it.
    let f := s!"Zig.Float.fma{fc.rtSuffix}Chk"
    let (env, l) := bindLet fc env inst.id s!"{f} {rv a} {rv b} {rv c}"; (env, some l)
  | .floatConv a =>
    let fmt := fc.floatFmtTerm inst.ty
    let (env, l) := bindLet fc env inst.id s!"pure (Zig.Float.conv {fmt} {rv a})"; (env, some l)
  | .floatFromInt a =>
    let fmt := fc.floatFmtTerm inst.ty
    let sgn := if fc.valSigned a then "true" else "false"
    let (env, l) := bindLet fc env inst.id s!"pure (Zig.Float.ofInt {fmt} {sgn} {rv a})"; (env, some l)
  | .intFromFloat safe a =>
    let sgn := if fc.tySigned inst.ty then "true" else "false"
    let n := fc.tyBits inst.ty
    let safeStr := if safe then "true" else "false"
    let (env, l) := bindLet fc env inst.id s!"Zig.Float.toInt {sgn} {n} {safeStr} {rv a}"
    (env, some l)
  | .isNull a => let (env, l) := bindLet fc env inst.id s!"pure (({rv a}).isNone)"; (env, some l)
  | .isNonNull a => let (env, l) := bindLet fc env inst.id s!"pure (({rv a}).isSome)"; (env, some l)
  | .optPayload a => let (env, l) := bindLet fc env inst.id s!"Zig.optPayload {rv a}"; (env, some l)
  | .wrapOptional a => let (env, l) := bindLet fc env inst.id s!"pure (some {rv a})"; (env, some l)
  | .isNullPtr isNull p =>
    -- `?*T`: the payload is the flag (null = address 0). `?T`: a flag byte after the payload.
    let some' := match fc.pointeeOf p with
      | .optional c => match fc.tyOfId c with
        | .ptr .. => s!"(·.isSome) <$> {fc.loadMem p (rv p)}"
        | ct => s!"Zig.optIsSome ({emitTy fc.structNames fc.types ct}) {rv p}"
      | _ => "(panic! \"air2lean: is_null_ptr of a non-optional\")"
    let expr := if isNull then s!"(!·) <$> {some'}" else some'
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .optPayloadPtr set p =>
    let expr := match set, fc.pointeeOf p with
      | true, .optional c =>
        match fc.tyOfId c with
        | .ptr .. => s!"pure {rv p}"
        | ct => s!"Zig.optSetSome ({emitTy fc.structNames fc.types ct}) {rv p}"
      | _, _ => s!"pure {rv p}"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .isErr a => let (env, l) := bindLet fc env inst.id s!"pure (Zig.isErr {rv a})"; (env, some l)
  | .isNonErr a => let (env, l) := bindLet fc env inst.id s!"pure (Zig.isNonErr {rv a})"; (env, some l)
  | .errPayload a =>
    let (env, l) := bindLet fc env inst.id (fc.liftR s!"Zig.unwrapPayload {rv a}"); (env, some l)
  | .errCode a =>
    let (env, l) := bindLet fc env inst.id (fc.liftR s!"Zig.unwrapErr {rv a}"); (env, some l)
  | .wrapErrPayload a =>
    let ety := fc.emitTyOf inst.ty
    let (env, l) := bindLet fc env inst.id s!"pure ((.ok {rv a}) : {ety})"; (env, some l)
  | .wrapErr a =>
    let ety := fc.emitTyOf inst.ty
    let (env, l) := bindLet fc env inst.id s!"pure ((.error {rv a}) : {ety})"; (env, some l)
  | .isNamedEnum a =>
    let (env, l) := bindLet fc env inst.id s!"pure ({fc.emitValTy a}.isNamed {rv a})"
    (env, some l)
  | .unionTag a =>
    let (env, l) := bindLet fc env inst.id s!"pure ({fc.emitValTy a}.tag {rv a})"
    (env, some l)
  | .unionInit idx a =>
    let expr := match fc.unionField? (fc.tyOfId inst.ty) idx with
      | some (u, f, true) => s!"pure {u}.{mangleField f}"
      | some (u, f, false) => s!"pure ({u}.{mangleField f} {rv a})"
      | none => "(panic! \"air2lean: union_init of a non-union type\")"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .alloc =>
    if fc.escaping.contains inst.id then
      -- The pointer to the local's stack block (made at function entry: `emitFunctionDef`).
      let field := (fc.allocFields.find? (·.1 == inst.id)).map (·.2) |>.getD s!"local{inst.id}"
      let (env, l) := bindLet fc env inst.id s!"pure (← get).{field}"; (env, some l)
    else (env, none)
  | .fieldPtr base idx =>
    if fc.isMemPtr base then
      let (env, l) := bindLet fc env inst.id s!"pure ({rv base}.add {fc.fieldOffset base idx})"
      (env, some l)
    else (env, none)
  | .setUnionTag ptr tag =>
    match fc.unionFieldOfTag? (fc.pointeeOf ptr) tag with
    | some (u, f, _) => (env, some (fc.modifyPlace ptr fun old => s!"({u}.setTag_{f} {old})"))
    | none => (env, some "(panic! \"air2lean: set_union_tag with an unknown tag\")")
  | .load ptr =>
    if fc.isMemPtr ptr then
      let (env, l) := bindLet fc env inst.id (fc.loadMem ptr (rv ptr)); (env, some l)
    else
      let (env, l) := bindLet fc env inst.id s!"pure ({fc.loadPlace ptr})"; (env, some l)
  | .store ptr v =>
    if fc.isMemPtr ptr then
      let (ty, align) := (fc.pointeeTy ptr, fc.ptrAlign ptr)
      match v with
      -- `undefined`: every byte of the value becomes undefined.
      | .undef _ => (env, some s!"Zig.storeUndef ({ty}) {align} {rv ptr}")
      | _ => (env, some s!"Zig.store (α := {ty}) {align} {rv ptr} {rv v}")
    else (env, some (fc.storePlace ptr (rv v)))
  | .sliceLen s =>
    let expr := if fc.mem then s!"pure {rv s}.len" else s!"pure (Zig.len {rv s})"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .sliceElemVal s i =>
    -- A pure function has the items (`Array`); a function that uses memory reads them.
    let expr := if fc.mem then s!"Zig.callM ({fc.loadItem s s!"{rv s}.ptr" (rv i)})"
      else fc.liftR s!"Zig.index {rv s} {rv i}"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .ptrAdd sub p n =>
    let size := fc.sizeOf ((ptrChild fc.types inst.ty).getD 0)
    let f := if sub then "elemSub" else "elem"
    let (env, l) := bindLet fc env inst.id s!"pure ({rv p}.{f} {size} {rv n})"; (env, some l)
  | .elemPtr p i =>
    let size := fc.sizeOf ((ptrChild fc.types inst.ty).getD 0)
    let base := if fc.isSlice p then s!"{rv p}.ptr" else rv p
    let (env, l) := bindLet fc env inst.id s!"pure ({base}.elem {size} {rv i})"; (env, some l)
  | .ptrElemVal p i =>
    let (env, l) := bindLet fc env inst.id s!"Zig.callM ({fc.loadItem p (rv p) (rv i)})"
    (env, some l)
  | .arrayElemVal a i =>
    let (env, l) := bindLet fc env inst.id (fc.liftR s!"Zig.vindex {rv a} {rv i}"); (env, some l)
  | .slice p len =>
    let (env, l) := bindLet fc env inst.id s!"pure (⟨{rv p}, {rv len}⟩ : Zig.Slice)"; (env, some l)
  | .slicePtr sl => let (env, l) := bindLet fc env inst.id s!"pure {rv sl}.ptr"; (env, some l)
  | .arrayToSlice p =>
    let (ptr, len) := fc.itemsOf p (rv p)
    let (env, l) := bindLet fc env inst.id s!"pure (⟨{ptr}, {len}⟩ : Zig.Slice)"; (env, some l)
  | .sliceFieldPtr len p =>
    if fc.isMemPtr p then
      let (env, l) := bindLet fc env inst.id s!"pure ({rv p}.add {if len then 8 else 0})"
      (env, some l)
    else (env, none)
  | .memset dst v =>
    let (ptr, n) := fc.itemsOf dst (rv dst)
    let item := emitTy fc.structNames fc.types (fc.tyOfId (fc.itemTyId dst))
    let v' := match v with | .undef _ => "none" | _ => s!"(some {rv v})"
    (env, some s!"Zig.callM (Zig.memset (α := {item}) {fc.ptrAlign dst} {ptr} {n} {v'})")
  | .memcpy dst src =>
    let (dptr, n) := fc.itemsOf dst (rv dst)
    let sptr := if fc.isSlice src then s!"{rv src}.ptr" else rv src
    let size := fc.sizeOf (fc.itemTyId dst)
    (env, some s!"Zig.callM (Zig.memmove {size} {fc.ptrAlign dst} {fc.ptrAlign src} {dptr} {sptr} {n})")
  | .tagName a =>
    let (env, l) := bindLet fc env inst.id (fc.liftR s!"{fc.emitValTy a}.tagName {rv a}")
    (env, some l)
  | .errorName a =>
    let (env, l) := bindLet fc env inst.id (fc.liftR s!"errorNameOf {rv a}"); (env, some l)
  | .structFieldVal s index =>
    match fc.unionField? (fc.valTy s) index with
    | some (u, f, _) =>
      let (env, l) := bindLet fc env inst.id (fc.liftR s!"{u}.get_{f} {rv s}"); (env, some l)
    | none =>
      let fname := fc.structFieldName s index
      let (env, l) := bindLet fc env inst.id s!"pure (({rv s}).{fname})"; (env, some l)
  | .aggregateInit elems =>
    match fc.tyOfId inst.ty with
    | .array .. =>
      let items := ", ".intercalate (elems.map rv).toList
      let (env, l) := bindLet fc env inst.id s!"pure (#v[{items}] : {fc.emitTyOf inst.ty})"
      (env, some l)
    | _ =>
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
      let memCallee := match callee with | .func name _ => fc.memFuncs.contains name | _ => false
      -- A pure callee gets the items of a `[]const T` argument (`Zig.readSlice`).
      let arg (a : Val) : String :=
        if fc.mem && !memCallee && fc.isSlice a then
          let item := emitTy fc.structNames fc.types (fc.tyOfId (fc.itemTyId a))
          s!"(← Zig.callM (Zig.readSlice ({item}) {fc.itemAlign a} {rv a}))"
        else rv a
      let term := s!"{cexpr} {String.intercalate " " (args.map arg).toList}"
      let expr := if memCallee then s!"Zig.callM ({term})" else fc.liftR term
      let (env, l) := bindLet fc env inst.id expr
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
  | .retLoad ptr =>
    match fc.tyOfId fc.retTy with
    | .void => "pure .ret"
    | _ =>
      if fc.isMemPtr ptr then s!"pure (.ret (← {fc.loadMem ptr (rv ptr)}))"
      else s!"pure (.ret {fc.loadPlace ptr})"
  | .unreach => "throw .unreachable"
  | .trap => "throw .panic"
  | .condBr c thenBody elseBody =>
    s!"if {rv c} then {doBlock (emitStmts fc env thenBody.toList)}\nelse \
      {doBlock (emitStmts fc env elseBody.toList)}"
  | .switchBr v cases elseBody =>
    match fc.valTy v with
    | .enum _ _ true fields =>
      -- Every name has a case: a `match` with one arm per case, no `else` arm (it is the
      -- `corruptSwitch` panic, which a valid enum value never reaches).
      let caseNames := cases.map fun c => c.items.filterMap fun it => match it with
        | .enumTag _ tv => (fields.find? (·.2 == tv)).map (mangleField ·.1)
        | _ => none
      let covered := caseNames.flatten
      if cases.all (·.ranges.isEmpty) && fields.all (fun (f, _) => covered.contains (mangleField f)) &&
          (cases.zip caseNames).all (fun (c, ns) => c.items.size == ns.size) then
        let arms := (cases.zip caseNames).toList.map fun (c, ns) =>
          let pats := String.intercalate " | " (ns.toList.map (s!".{·}"))
          s!"| {pats} => {doBlock (emitStmts fc env c.body.toList)}"
        s!"match {rv v} with\n{String.intercalate "\n" arms}"
      else emitSwitchChain fc env v cases.toList elseBody
    | _ => emitSwitchChain fc env v cases.toList elseBody
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
      [s!"def {fc.fnName}.loop{loopInst.id} {paramsStr} : {fc.monad} {fc.localsName} {fc.exitName} := do",
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

/-- An escaping `alloc`'s stack block: `(allocId, field, size, align)`. -/
def FCtx.stackBlocks (fc : FCtx) : Array (InstId × String × Nat × Nat) :=
  fc.escaping.map fun aid =>
    let field := (fc.allocFields.find? (·.1 == aid)).map (·.2) |>.getD s!"local{aid}"
    let child := match fc.tyOfId (fc.instTyId aid) with | .ptr _ _ c => c | _ => 0
    let l := fc.layouts[child]?.getD {}
    (aid, field, l.size.getD 0, l.align.getD 1)

def emitFunctionDef (fc : FCtx) (leanName localsName exitName : String) (paramTys : Array TyId)
    (retTy : TyId) (body : Array Inst) (hasNonRetExit : Bool) : String :=
  let paramsStr := String.intercalate " "
    ((paramTys.mapIdx fun i pt => s!"(p{i} : {fc.emitTyOf pt})").toList)
  let retStr := fc.emitTyOf retTy
  let bodyStr := emitStmts fc #[] body.toList
  -- The `M`-do-block's `σ`/`ε` never appear as a literal type anywhere inside it (`(← get)`,
  -- `.br<k>`, …), so without this ascription nothing pins them down for the elaborator.
  let ascribedBody := s!"({doBlock bodyStr} : {fc.monad} {localsName} {exitName})"
  -- Each escaping local's stack block lives from function entry to the return.
  let stack := fc.stackBlocks
  let allocLines := (stack.map fun (aid, _, size, align) =>
    s!"  let s{aid} ← Zig.allocStack {size} {align}").toList
  let init := if stack.isEmpty then s!"(default : {localsName})"
    else
      let sets := stack.map fun (aid, field, _, _) => s!"{field} := s{aid}"
      s!"\{ (default : {localsName}) with {String.intercalate ", " sets.toList} }"
  let freeLines := (stack.map fun (aid, _, _, _) => s!"  Zig.free s{aid}").toList
  let retArm := match fc.tyOfId retTy with
    | .void => "| .ret => pure ()"
    | _ => "| .ret v => pure v"
  -- `ret` is the only constructor when the function has no block/loop control flow at all
  -- (empty `brTargets`/`repTargets`): a wildcard arm after it is then unreachable, which Lean
  -- rejects as a "Redundant alternative" error rather than a warning, so it must be omitted.
  let matchLines :=
    [s!"  {retArm}"] ++ (if hasNonRetExit then ["  | _ => throw .panic"] else [])
  let resultTy := if fc.mem then "Zig.MemM" else "Zig.Result"
  String.intercalate "\n"
    ([s!"def {leanName} {paramsStr} : {resultTy} ({retStr}) := do"] ++ allocLines ++
     [s!"  let e ← {indentTail 2 ascribedBody}.run' {init}"] ++ freeLines ++
     ["  match e with"] ++ matchLines)

/-- One function's output in four parts: the `Locals`/`Exit` types, the `again<k>` defs, the
`loop<k>` defs (inner loop first), and the function def. `emit` joins them, and puts a
recursive group's loop and function defs into one `mutual` block. -/
structure FuncParts where
  types : List String
  agains : List String
  loops : List String
  defn : String

/-- The static context of `f`. `globalIds`: the block of each global of `f.globals`. -/
def mkFCtx (f : Func) (structNames : Array (String × String)) (funcNames : Array (String × String))
    (floatSemantics : FloatSemantics) (memFuncs : Array String) (globalIds : Array Nat) : FCtx :=
  let allInsts := f.allInsts
  let leanName := (funcNames.find? (·.1 == f.name)).map (·.2) |>.getD f.name
  -- `«at»` (a keyword) gives `atLocals`.
  let plain := (leanName.stripPrefix "«").stripSuffix "»"
  let allocs := collectAllocs f.types allInsts
  let fc : FCtx :=
    { types := f.types, structNames, funcNames,
      allocFields := allocs.map fun (i, n, _) => (i, n), blockTys := blockLoopTys allInsts,
      allInsts, retTy := f.ret, fnName := leanName, localsName := s!"{plain}Locals",
      exitName := s!"{plain}Exit", floatSemantics, zigVersion := f.zigVersion, places := #[],
      mem := memFuncs.contains f.name, memFuncs, layouts := f.layouts,
      escaping := escapingAllocs f, globalIds }
  { fc with places := fc.computePlaces }

def emitOneFunction (f : Func) (structNames : Array (String × String))
    (funcNames : Array (String × String)) (floatSemantics : FloatSemantics)
    (memFuncs : Array String) (globalIds : Array Nat) : FuncParts :=
  let fc := mkFCtx f structNames funcNames floatSemantics memFuncs globalIds
  let allInsts := fc.allInsts
  let leanName := fc.fnName
  let allocs := collectAllocs f.types allInsts
  let blTys := fc.blockTys
  let brT := brTargets allInsts
  let repT := repTargets allInsts
  let localsName := fc.localsName
  let exitName := fc.exitName
  let escaping := fc.escaping
  let localsStr := emitLocalsStruct structNames f.types localsName allocs escaping fc.mem
  let exitStr := emitExitInductive structNames f.types exitName f.ret blTys brT repT fc.mem
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

/-! ## Globals (`docs/generated-code.md` §Globals) -/

/-- One block of the memory at program start (`mem0`). -/
structure ProgGlobal where
  /-- What the block holds: a global's Zig name, `a constant`, or a tag name. -/
  label : String
  /-- The initial value as a term, and its Lean type. -/
  term : String
  ty : String
  align : Nat

/-- The initial value of global `g` of `fc`'s function, as a term and its Lean type. An array with
a sentinel is one item longer: the sentinel is its last item. -/
def FCtx.globalInit (fc : FCtx) (g : Global) : String × String :=
  let init := g.init.getD (.undef g.ty)
  match fc.tyOfId g.ty, init, (fc.layouts[g.ty]?.map (·.sentinel)).getD false with
  | .array _ c, .agg _ elems, true =>
    let t := s!"Vector ({emitTy fc.structNames fc.types (fc.tyOfId c)}) {elems.size}"
    (s!"(#v[{", ".intercalate (elems.map (fc.resolveVal #[])).toList}] : {t})", t)
  | _, _, _ => (fc.resolveVal #[] init, emitTy fc.structNames fc.types (fc.tyOfId g.ty))

/-- The globals of the program, and the block of each global of each function (by function
name). A named global is one block, shared by name. An unnamed constant (a string literal) with
the same type and value as another one shares its block. Named globals come first. -/
def collectGlobals (funcs : Array Func) (mkFc : Func → Array Nat → FCtx) :
    Array ProgGlobal × Array (String × Array Nat) := Id.run do
  let mut named : Array String := #[]
  for f in funcs do
    for g in f.globals do
      if let some n := g.name then
        if !named.contains n then named := named.push n
  let mut ids : Array (String × Array Nat) := funcs.map fun f =>
    (f.name, f.globals.map fun g => (g.name.bind named.idxOf?).getD 0)
  -- A constant can point to a constant after it in `Func.globals` (the exporter adds them in the
  -- order it finds them), so the last one comes first.
  let mut unnamed : Array (String × String) := #[]
  for (f, k) in funcs.zipIdx do
    for j in (List.range f.globals.size).reverse do
      let g := f.globals[j]!
      if g.name.isNone then
        let (term, ty) := (mkFc f ids[k]!.2).globalInit g
        let id := match unnamed.findIdx? (· == (term, ty)) with
          | some u => named.size + u
          | none => named.size + unnamed.size
        if id == named.size + unnamed.size then unnamed := unnamed.push (term, ty)
        ids := ids.set! k (f.name, ids[k]!.2.set! j id)
  let mut out : Array ProgGlobal := #[]
  for n in named do
    let some (f, k) := funcs.zipIdx.find? fun (f, _) => f.globals.any (·.name == some n)
      | continue
    let some g := f.globals.find? (·.name == some n) | continue
    let (term, ty) := (mkFc f ids[k]!.2).globalInit g
    out := out.push { label := n, term, ty, align := (f.layouts[g.ty]?.bind (·.align)).getD 1 }
  for (term, ty) in unnamed do
    -- The alignment of the value's type: its items for an array.
    out := out.push { label := "a constant", term, ty, align := 1 }
  return (out, ids)

/-- The alignment of each unnamed constant: the ABI alignment of its type. -/
def fixUnnamedAlign (funcs : Array Func) (ids : Array (String × Array Nat)) (gs : Array ProgGlobal) :
    Array ProgGlobal := Id.run do
  let mut gs := gs
  for f in funcs do
    let some (_, fid) := ids.find? (·.1 == f.name) | continue
    for (g, j) in f.globals.zipIdx do
      if g.name.isNone then
        let a := (f.layouts[g.ty]?.bind (·.align)).getD 1
        gs := gs.modify fid[j]! fun pg => { pg with align := a }
  return gs

/-- The enums whose tag names a function reads (`@tagName`), as `(Zig name, Lean name, fields)`. -/
def tagNameEnums (funcs : Array Func) (structNames : Array (String × String)) :
    Array (String × String × Array (String × Int) × Bool) := Id.run do
  let mut out := #[]
  for f in funcs do
    let insts := f.allInsts
    for i in insts do
      if let .tagName (.inst a) := i.op then
        let some ai := insts.find? (·.id == a) | continue
        if let some (.enum name _ exhaustive fields) := f.types[ai.ty]? then
          if !out.any (·.1 == name) then
            let lean := (structNames.find? (·.1 == name)).map (·.2) |>.getD name
            out := out.push (name, lean, fields, exhaustive)
  return out

/-- The error names of the program (the names of its error sets), if a function reads one
(`@errorName`). -/
def errorNames (funcs : Array Func) : Array String :=
  if !funcs.any (·.allInsts.any fun i => match i.op with | .errorName _ => true | _ => false) then #[]
  else
    let names := funcs.flatMap fun f => f.types.flatMap fun t => match t with
      | .errorSet (some ns) => ns
      | _ => #[]
    (names.foldl (fun acc n => if acc.contains n then acc else acc.push n) #[]).qsort (· < ·)

/-- `errorNameOf`: the name of each error of the program (`@errorName`), in the blocks from
`first` on. An error that no error set of the program names throws `.unspecified`. -/
def emitErrorNameOf (names : Array String) (first : Nat) : String :=
  let arms := names.toList.zipIdx.map fun (n, k) =>
    s!"  if e = {n.quote} then pure ⟨⟨some {first + k}, 0⟩, {n.toUTF8.size}⟩ else"
  String.intercalate "\n"
    (["def errorNameOf (e : Zig.ErrName) : Zig.Result Zig.Slice :="] ++ arms ++
      ["  throw .unspecified"])

/-- The name bytes of `s` with a 0 sentinel, as a term and its type. -/
def nameBytes (s : String) : String × String :=
  let bs := s.toUTF8.toList.map (s!"{·}")
  let t := s!"Vector (BitVec 8) {bs.length + 1}"
  (s!"(#v[{", ".intercalate (bs ++ ["0"])}] : {t})", t)

/-- `mem0`: the memory at program start, one block per global. -/
def emitMem0 (gs : Array ProgGlobal) : String :=
  let lines := gs.toList.zipIdx.map fun (g, k) =>
    s!"  -- {k}: {g.label}\n  (Zig.Enc.encode ({g.term} : {g.ty}), {g.align})"
  let body := if lines.isEmpty then "[]" else s!"[\n{",\n".intercalate lines}]"
  s!"/-- The memory at program start: block `k` is global `k`. -/\n\
    def mem0 : Zig.Mem := Zig.Mem.ofGlobals {body}"

/-- `<E>.tagName`: the name of each tag of `E` (`@tagName`), in the blocks from `first` on. -/
def emitTagName (lean : String) (fields : Array (String × Int)) (exhaustive : Bool) (bits : Nat)
    (first : Nat) : String :=
  let slice (k : Nat) (f : String) := s!"⟨⟨some {first + k}, 0⟩, {f.toUTF8.size}⟩"
  let head := s!"def {lean}.tagName (e : {lean}) : Zig.Result Zig.Slice :="
  if exhaustive then
    let arms := fields.toList.zipIdx.map fun ((f, _), k) => s!"  | .{mangleField f} => pure {slice k f}"
    String.intercalate "\n" ([head, "  match e with"] ++ arms)
  else
    -- A value without a name has no tag name: the AIR checks `is_named_enum_value` before.
    let arms := fields.toList.zipIdx.map fun ((f, v), k) =>
      s!"  if e.toBits == {tagLit bits v} then pure {slice k f} else"
    String.intercalate "\n" ([head] ++ arms ++ ["  throw .panic"])

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
stripped from every Zig name (function or struct) before mangling. `floatSemantics` selects
`--float-semantics` (default `ieee`). -/
def emit (funcs : Array Func) (ns : String) (prefix_ : String)
    (floatSemantics : FloatSemantics := .ieee) : String :=
  let structs := collectNamed funcs prefix_
  let structNames := structs.map fun s => (s.zigName, s.leanName)
  let funcNames := funcs.map fun f => (f.name, mangleName prefix_ f.name)
  let memFuncs := memoryFunctions funcs
  let structsStr := (structs.map (emitNamed structNames (encTypeNames funcs memFuncs))).toList
  let mkFc (f : Func) (ids : Array Nat) := mkFCtx f structNames funcNames floatSemantics memFuncs ids
  let (globals, ids) := collectGlobals funcs mkFc
  let globals := fixUnnamedAlign funcs ids globals
  -- The tag names are blocks after the globals.
  let (globals, tagDefs) := (tagNameEnums funcs structNames).foldl (init := (globals, #[]))
    fun (gs, defs) (_, lean, fields, exhaustive) =>
      let bits := match funcs.findSome? fun f => f.types.findSome? fun t => match t with
          | .enum n tag .. => if (structNames.find? (·.1 == n)).map (·.2) == some lean then
              (match f.types[tag]? with | some (.int _ b) => some b | _ => none) else none
          | _ => none with
        | some b => b
        | none => 0
      let d := emitTagName lean fields exhaustive bits gs.size
      let gs := fields.foldl (fun gs (f, _) =>
        let (term, ty) := nameBytes f
        gs.push { label := s!"the name of {lean}.{f}", term, ty, align := 1 }) gs
      (gs, defs.push d)
  let errNames := errorNames funcs
  let errDefs := if errNames.isEmpty then [] else [emitErrorNameOf errNames globals.size]
  let globals := errNames.foldl (fun gs n =>
    let (term, ty) := nameBytes n
    gs.push { label := s!"the name of error.{n}", term, ty, align := 1 }) globals
  let globalsStr := if memFuncs.isEmpty then [] else [emitMem0 globals] ++ tagDefs.toList ++ errDefs
  let idsOf (f : Func) := ((ids.find? (·.1 == f.name)).map (·.2)).getD #[]
  let funcsStr := (callGroups funcs).toList.map fun (members, recursive) =>
    let parts := members.toList.map fun f =>
      emitOneFunction f structNames funcNames floatSemantics memFuncs (idsOf f)
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
    (["import ZigLean", s!"\nnamespace {ns}"] ++ structsStr ++ globalsStr ++ funcsStr ++ [s!"end {ns}"])

end Air2Lean
