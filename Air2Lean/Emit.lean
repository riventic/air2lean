import Std.Data.HashSet
import Air2Lean.Check
import Air2Lean.ProofApi

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
  | .br .. | .switchDispatch .. | .«repeat» .. | .ret .. | .unreach | .trap | .condBr .. | .switchBr .. => true
  | .retLoad _ => true
  | .call (.func _ noreturn ..) _ => noreturn
  | _ => false

/-! ## Name mangling (`docs/generated-code.md` §Names) -/

/-- Identifier-shaped reserved tokens from the pinned Lean parser and core notation modules.
Contextual `nonReservedSymbol` words and the non-reserved leading words of tactic/attribute syntax are excluded. -/
def leanKeywords : List String :=
  ["def", "theorem", "lemma", "structure", "inductive", "namespace", "import", "open", "match", "matches",
   "with", "do", "let", "fun", "if", "then", "else", "end", "mutual", "partial", "where",
   "deriving", "class", "instance", "abbrev", "variable", "variables", "section", "by", "sorry",
   "have", "show", "from", "this", "suffices", "calc", "for", "in", "return", "try", "catch",
   "finally", "unsafe", "noncomputable", "macro", "syntax", "elab", "axiom", "constant",
   "forall", "exists", "Type", "Prop", "Sort", "opaque", "attribute", "set_option", "universe",
   "extends", "renaming", "hiding", "at", "private", "protected", "include", "omit",
   "export", "prelude", "initialize", "infix", "infixl", "infixr", "prefix", "postfix",
   "scoped", "local", "termination_by", "decreasing_by", "throw",
   "break", "continue", "unless", "mut", "repeat", "while", "until",
   "panic!", "unreachable!", "assert!", "debug_assert!", "termination_by?",
   "public", "meta", "nonrec", "example", "coinductive", "with_weak_namespace",
   "assert_not_exists", "assert_not_imported", "deprecated_syntax", "init_quot", "docs_to_verso",
   "deprecated_module", "unlock_limits", "builtin_initialize", "add_decl_doc", "register_tactic_tag",
   "tactic_extension", "recommended_spelling", "register_error_explanation", "notation", "macro_rules",
   "declare_syntax_cat", "elab_rules", "binder_predicate", "nomatch", "nofun", "leading_parser",
   "trailing_parser", "let_fun", "let_delayed", "let_tmp", "haveI", "letI", "partial_fixpoint",
   "coinductive_fixpoint", "inductive_fixpoint", "no_index", "inferInstanceAs", "dbg_trace", "idbg",
   "StateRefT", "show_term_elab", "match_expr", "let_expr", "throwNamedError", "throwNamedErrorAt",
   "logNamedError", "logNamedErrorAt", "logNamedWarning", "logNamedWarningAt", "register_parser_alias",
   "tactic_alt", "tactic_tag", "tactic_name", "nat_lit", "without_expected_type", "by_elab", "mod_cast",
   "include_str", "run_cmd", "run_elab", "run_meta", "seal", "unseal", "unif_hint",
   "max_prec", "eval_prec", "eval_prio", "s!", "f!", "println!", "show_term", "by?",
   "set_library_suggestions", "simproc", "dsimproc", "simproc_decl", "dsimproc_decl",
   "builtin_simproc", "builtin_dsimproc", "builtin_simproc_decl", "builtin_dsimproc_decl",
   "cbv_simproc", "cbv_simproc_decl", "builtin_cbv_simproc", "builtin_cbv_simproc_decl", "cbv_eval",
   "norm_cast_add_elim", "declare_simp_like_tactic", "register_try?_tactic", "grind_annotated",
   "grind_propagator", "builtin_grind_propagator", "declare_bitwise_uint_theorems",
   "declare_uint_theorems", "declare_bitwise_int_theorems", "declare_int_theorems",
   "register_sym_simp", "register_sym_dsimp"]

/-- Quote identifiers that Zig permits but Lean does not accept bare. -/
def mangleField (raw : String) : String :=
  let bare := match raw.toList with
    | [] => false
    | c :: cs => (c.isAlpha || c == '_') && cs.all fun c =>
        c.isAlphanum || c == '_' || c == '\'' || c == '?' || c == '!'
  if bare && raw != "_" && !leanKeywords.contains raw then raw
  else if !raw.isEmpty && !raw.toList.any (fun c => c == '«' || c == '»' || c == '\n' || c == '\r') then
    s!"«{raw}»"
  else
    "airName" ++ String.join (raw.toUTF8.toList.map fun b => s!"_{b.toNat}")

def plainName (name : String) : String :=
  ((name.dropPrefix "«").dropSuffix "»").toString

/-- Preserve the preferred spelling unless it is already occupied. -/
def freshName (raw : String) (used : Array String) : String := Id.run do
  let base := mangleField raw
  if !used.contains base then return base
  let mut k := 1
  while used.contains (mangleField s!"{raw}_air2lean{k}") do k := k + 1
  return mangleField s!"{raw}_air2lean{k}"

def mangleName (prefix_ : String) (raw : String) : String :=
  let stripped : String :=
    if prefix_.length > 0 && raw.startsWith prefix_ then (raw.drop prefix_.length).toString
    else raw
  -- A generic instance has its arguments in the name: `array_list.Aligned(u32,null)` gives
  -- `array_list_Aligned_u32_null`.
  let underscored := String.ofList (stripped.toList.filterMap fun c =>
    if c.isAlphanum || c == '_' then some c else if c == ')' then none else some '_')
  mangleField underscored

/-- Names Lean itself generates below a structure or inductive. -/
def typeCoreNames : Array String :=
  #["rec", "recOn", "casesOn", "below", "brecOn", "binductionOn", "noConfusion",
    "noConfusionType", "ctorIdx", "ctorElim", "ctorElimType", "sparseCasesOn"]

/-- Unqualified runtime names in the emitted source must not be shadowed by program defs. -/
def runtimeNames : Array String :=
  #["BitVec", "Bool", "Unit", "Vector", "Array", "Option", "Except", "StateT", "Int",
    "Nat", "String", "List", "Prod", "Repr", "Inhabited", "DecidableEq",
    "Zig", "default", "pure", "get", "modify", "discard", "id", "dispatchValue", "dispatchExit"]

def memberNames (ty : Ty) (reserved : Array String := #[]) : Array (String × String) := Id.run do
  let fields : Array String := match ty with
    | .struct _ _ fs | .union _ _ _ fs => fs.map (fun (p : String × TyId) => p.1)
    | .enum _ _ _ fs => fs.map (fun (p : String × Int) => p.1)
    | _ => #[]
  let mut used := typeCoreNames ++ runtimeNames ++ reserved
  if let .struct .. := ty then used := used.push "mk"
  let mut out := #[]
  for raw in fields do
    let name := freshName raw used
    used := used.push name
    out := out.push (raw, name)
  return out

/-- Capture the collision table once for every member emitted in the same type scope. -/
def memberLookup (ty : Ty) (reserved : Array String := #[]) : String → String :=
  let names := memberNames ty reserved
  fun raw => (names.find? (·.1 == raw)).map (·.2) |>.getD (mangleField raw)

def memberName (ty : Ty) (raw : String) (reserved : Array String := #[]) : String := memberLookup ty reserved raw

/-- Generated helpers share their type's namespace with source members. Allocate them after
those members, so a constructor named `toBits` or `get_a` keeps its source spelling. -/
def helperNames (ty : Ty) (reserved : Array String := #[]) : Array (String × String) := Id.run do
  let stems := match ty with
    | .enum _ _ exhaustive _ =>
      (if exhaustive then #[] else #["bits", "mk"]) ++ #["toBits", "ofInt?", "isNamed", "tagName"]
    | .union _ _ tag fs =>
      (if tag.isSome then #["tag"] else #[]) ++ fs.flatMap fun (p : String × TyId) =>
        #[s!"get_{p.1}", s!"modify_{p.1}"] ++ (if tag.isSome then #[s!"setTag_{p.1}"] else #[])
    | _ => #[]
  let mut used := typeCoreNames ++ runtimeNames ++ reserved ++ (memberNames ty reserved).map (·.2)
  let mut out := #[]
  for stem in stems do
    let name := freshName stem used
    used := used.push name
    out := out.push (stem, name)
  return out

def helperLookup (ty : Ty) (reserved : Array String := #[]) : String → String :=
  let names := helperNames ty reserved
  fun raw => (names.find? (·.1 == raw)).map (·.2) |>.getD (mangleField raw)

def helperName (ty : Ty) (raw : String) (reserved : Array String := #[]) : String := helperLookup ty reserved raw

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
  | .array len child s =>
    s!"Vector ({emitTy structNames types types[child]!}) {len + if s then 1 else 0}"
  | .vector len child => s!"Zig.Vec ({emitTy structNames types types[child]!}) {len}"
  | .optional child => s!"Option ({emitTy structNames types types[child]!})"
  | .errorUnion _set payload => s!"Except Zig.ErrName ({emitTy structNames types types[payload]!})"
  | .errorSet _ => "Zig.ErrName"
  | .struct name _ _ | .enum name .. | .union name .. =>
    (structNames.find? (·.1 == name)).map (·.2) |>.getD name
  | .tuple fields =>
    let parts := (fields.map (fun fid => emitTy structNames types types[fid]!)).toList
    if parts.isEmpty then "Unit" else String.intercalate " × " parts
  | .allocator => "Zig.Allocator"
  | .thread => "Zig.ThreadId"
  | .io => "Zig.Io"
  | .other name => name

/-- A finite declared name table, with checked capacity and uniqueness. These positions
are not ABI error ordinals; storage retains the shared symbolic `errFrag` identity. -/
def emitErrorDomain (names : Array String) : String :=
  s!"(⟨#[{String.intercalate ", " (names.toList.map String.quote)}], by decide, by decide⟩ : Zig.ErrorDomain)"

/-- An explicit type-indexed storage dictionary. No instance for `String` is registered.
Named aggregate dictionaries choose these recursively for their fields. -/
partial def emitStorageEnc (structNames : Array (String × String)) (types : Array Ty)
    (id : TyId) : Option String :=
  match types[id]? with
  | some (.errorSet (some names)) => some s!"Zig.errorEnc {emitErrorDomain names}"
  | some (.optional c) =>
    match types[c]? with
    | some (.errorSet (some names)) => some s!"Zig.optionalErrorEnc {emitErrorDomain names}"
    | _ => (emitStorageEnc structNames types c).map fun enc => s!"Zig.Enc.optionWith ({enc})"
  | some (.array n c sentinel) =>
    (emitStorageEnc structNames types c).map fun enc =>
      s!"Zig.Enc.vectorWith {n + if sentinel then 1 else 0} ({enc})"
  | some (.errorUnion set payload) =>
    let payloadEnc := emitStorageEnc structNames types payload
    let enc := payloadEnc.getD
      s!"(inferInstance : Zig.Enc ({emitTy structNames types types[payload]!}))"
    match types[set]? with
    | some (.errorSet (some names)) => some s!"Zig.errorUnionEnc {emitErrorDomain names} ({enc})"
    | _ => payloadEnc.map fun _ => s!"Zig.Enc.errorUnionWith ({enc})"
  | _ => none

/-- Bind a dictionary only around the storage operation that needs it. This preserves the
public semantic types (`ErrName`, `Option ErrName`, `Except ErrName`) and pure APIs. -/
def withStorageEnc (structNames : Array (String × String)) (types : Array Ty)
    (id : TyId) (expr : String) : String :=
  match emitStorageEnc structNames types id with
  | none => expr
  | some enc =>
    s!"(letI : Zig.Enc ({emitTy structNames types types[id]!}) := {enc}; {expr})"

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
  | .ptr "slice" _ c | .array _ c _ | .optional c => go c
  | .errorUnion _ p => go p
  | .tuple fs => fs.flatMap go
  | _ => #[]

/-- The types of `f` that its translation uses: those of the parameters, the result, each
instruction, each constant operand and each global, and every type that these name. A type that
is only in the file's type table is not used: `std.Thread`'s fields (its implementation, which
differs by host OS) are behind the model type `Zig.ThreadId`, which has no children. -/
def usedTys (f : Func) : Array Bool := Id.run do
  let insts := f.allInsts
  let consts := insts.flatMap fun i => (valueOperands i.op).filterMap Val.constTy?
  let mut used := Array.replicate f.types.size false
  let mut todo : List TyId :=
    (f.params ++ #[f.ret] ++ insts.map (·.ty) ++ consts ++ f.globals.map (·.ty)).toList
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | id :: rest =>
      todo := rest
      if used[id]?.getD true then continue
      used := used.set! id true
      todo := ((f.types[id]?.map childTys).getD #[]).toList ++ todo
  return used

/-- Every named type that `funcs` use (`usedTys`), each after the named types its fields use. -/
def collectNamed (funcs : Array Func) (prefix_ : String) : Array NamedType := Id.run do
  let mut found : Array NamedType := #[]
  for f in funcs do
    let used := usedTys f
    for (ty, i) in f.types.zipIdx do
      if !used[i]?.getD false then continue
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
  -- `found`'s own order follows the AIR type table, which the compiler does not dump in a
  -- stable order across runs; sort by name first so two types with no dependency on each
  -- other still come out in the same relative order every time.
  found := found.qsort (·.zigName < ·.zigName)
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

/-- The `Zig.Raw` (`extern`) or `Zig.PackedU` (`packed`) namespace of an `extern` or `packed`
union (`ZigLean/Union.lean`). -/
def rawUnionNs (layout : String) : String := if layout == "packed" then "Zig.PackedU" else "Zig.Raw"

/-- `union_init` of an `extern` or `packed` union `u` (`size` bytes) with the value `v` of the
field type `t`. -/
def rawUnionInit (u layout : String) (size : Nat) (v t : String) : String :=
  s!"(⟨{rawUnionNs layout}.init {size} ({v} : {t})⟩ : {u})"

/-- The `Zig.Enc` instance of a struct or enum that can be in memory (`ZigLean/Mem/Enc.lean`):
the size, alignment and field offsets from the exporter. -/
def emitEnc (structNames : Array (String × String)) (s : NamedType) : String :=
  let n := s.leanName
  let fm := memberLookup s.ty (structNames.map (·.2))
  let hn := helperLookup s.ty (structNames.map (·.2))
  let size := s.layout.size.getD 0
  let head := [s!"instance : Zig.Enc {n} where", s!"  size := {size}",
               s!"  align := {s.layout.align.getD 1}"]
  match s.ty with
  | .union _ _ none _ =>
    -- `extern`, `packed`: the bytes (`ZigLean/Union.lean`).
    String.intercalate "\n" (head ++
      ["  encode v := v.bytes.toArray", s!"  decode bs := pure ⟨Zig.Raw.ofArray {size} bs⟩"])
  | .union _ _ (some tag) fields =>
    -- The tag and the active field's payload at `unionOffsets` (M20).
    let (to, po) := (unionOffsets s.srcTypes s.srcLayouts tag (fields.map (·.2))).getD (0, 0)
    let tagTy := emitTy structNames s.srcTypes s.srcTypes[tag]!
    let isVoid (id : TyId) : Bool := s.srcTypes[id]! == .void
    let enc := fields.toList.map fun (f, id) =>
      if isVoid id then s!"    | .{fm f} => Zig.Enc.fields {size} [({to}, Zig.Enc.encode v.{hn "tag"})]"
      else s!"    | .{fm f} x => Zig.Enc.fields {size} [({to}, Zig.Enc.encode v.{hn "tag"}), ({po}, {withStorageEnc structNames s.srcTypes id "Zig.Enc.encode x"})]"
    let dec := fields.toList.map fun (f, id) =>
      if isVoid id then s!"    | .{fm f} => pure .{fm f}"
      else s!"    | .{fm f} => pure (.{fm f} (← {withStorageEnc structNames s.srcTypes id s!"Zig.Enc.decodeAt bs {po}"}))"
    String.intercalate "\n" (head ++ ["  encode v := match v with"] ++ enc ++
      ["  decode bs := do", s!"    let t : {tagTy} ← Zig.Enc.decodeAt bs {to}", "    match t with"] ++ dec)
  | .struct _ "packed" fields =>
    -- Its backing integer (`Zig.Packed`).
    let bits := fields.foldl (fun acc (_, t) => acc + (packedBits s.srcTypes t).getD 0) 0
    String.intercalate "\n" (head ++
      ["  encode v := Zig.Enc.encode (Zig.Packed.toBits v)", "  decode bs := do",
       s!"    let b : BitVec {bits} ← Zig.Enc.decode bs", "    Zig.Packed.ofBits? b"])
  | .struct _ _ fields =>
    let parts := (fields.zip s.layout.offsets).toList.map fun ((f, id), o) =>
      s!"({o}, {withStorageEnc structNames s.srcTypes id s!"Zig.Enc.encode v.{fm f}"})"
    let decs := (fields.zip s.layout.offsets).toList.map fun ((f, id), o) =>
      s!"{fm f} := ← {withStorageEnc structNames s.srcTypes id s!"Zig.Enc.decodeAt bs {o}"}"
    String.intercalate "\n" (head ++
      [s!"  encode v := Zig.Enc.fields {size} [{String.intercalate ", " parts}]",
       s!"  decode bs := do pure \{ {String.intercalate ", " decs} }"])
  | .enum _ tag exhaustive _ =>
    let (signed, bits) := match s.srcTypes[tag]! with | .int sg b => (sg, b) | _ => (false, 0)
    let dec := if exhaustive then
        -- A tag value without a name is not a value of the enum: illegal behaviour.
        [s!"    match {n}.{hn "ofInt?"} (Zig.val {signed} b) with",
         "    | some v => pure v", "    | none => throw .illegal"]
      else ["    pure ⟨b⟩"]
    String.intercalate "\n" (head ++
      [s!"  encode v := Zig.Enc.encode v.{hn "toBits"}", "  decode bs := do",
       s!"    let b : BitVec {bits} ← Zig.Enc.decode bs"] ++ dec)
  | _ => ""

def emitNamedType (structNames : Array (String × String)) (s : NamedType) : String :=
  let tyStr (id : TyId) : String := emitTy structNames s.srcTypes s.srcTypes[id]!
  let n := s.leanName
  let fm := memberLookup s.ty (structNames.map (·.2))
  let hn := helperLookup s.ty (structNames.map (·.2))
  match s.ty with
  | .enum _ tag exhaustive fields =>
    let (signed, bits) := match s.srcTypes[tag]! with | .int sg b => (sg, b) | _ => (false, 0)
    let lo : Int := if signed then -(2 ^ (bits - 1)) else 0
    let hi : Int := if signed then 2 ^ (bits - 1) - 1 else 2 ^ bits - 1
    if exhaustive then
      let ctors := fields.toList.map fun (f, _) => s!"  | {fm f}"
      let toBits := fields.toList.map fun (f, v) => s!"  | .{fm f} => {tagLit bits v}"
      -- `Option.none`: in the namespace of `{n}`, a field named `none` would be `{n}.none`.
      let ofInt := fields.foldr (fun (f, v) acc => s!"if v = {v} then Option.some .{fm f} else {acc}") "Option.none"
      String.intercalate "\n"
        ([s!"inductive {n} where"] ++ ctors ++ ["  deriving Repr, Inhabited, DecidableEq", "",
          s!"def {n}.{hn "toBits"} : {n} → BitVec {bits}"] ++ toBits ++ ["",
          s!"def {n}.{hn "ofInt?"} (v : Int) : Option {n} :=", s!"  {ofInt}", "",
          s!"def {n}.{hn "isNamed"} (_ : {n}) : Bool := true", "",
          -- A field of a packed struct (`ZigLean/Packed.lean`): a tag value without a name is
          -- not `valid`.
          s!"instance : Zig.Packed {n} {bits} where", s!"  toBits := {n}.{hn "toBits"}",
          s!"  ofBits b := ({n}.{hn "ofInt?"} (Zig.val {signed} b)).getD default",
          s!"  valid b := ({n}.{hn "ofInt?"} (Zig.val {signed} b)).isSome"])
    else
      let named := fields.toList.map fun (f, v) => s!"def {n}.{fm f} : {n} := ⟨{tagLit bits v}⟩"
      let isNamed := String.intercalate " || " (fields.toList.map fun (_, v) => s!"e.{hn "bits"} == {tagLit bits v}")
      String.intercalate "\n"
        ([s!"structure {n} where"] ++ (if hn "mk" == "mk" then [] else [s!"  {hn "mk"} ::"]) ++ [s!"  {hn "bits"} : BitVec {bits}", "  deriving Repr, Inhabited, DecidableEq", ""]
          ++ named ++ ["",
          s!"def {n}.{hn "toBits"} (e : {n}) : BitVec {bits} := e.{hn "bits"}", "",
          s!"def {n}.{hn "ofInt?"} (v : Int) : Option {n} :=",
          s!"  if {lo} ≤ v ∧ v ≤ {hi} then Option.some ⟨BitVec.ofInt {bits} v⟩ else Option.none", "",
          s!"def {n}.{hn "isNamed"} (e : {n}) : Bool := {if isNamed.isEmpty then "false" else isNamed}", "",
          s!"instance : Zig.Packed {n} {bits} where", s!"  toBits := {n}.{hn "toBits"}", "  ofBits b := ⟨b⟩"])
  | .union _ layout none fields =>
    -- `extern`, `packed`: the bytes; every field at byte 0 (`ZigLean/Union.lean`).
    let size := s.layout.size.getD 0
    let ns := rawUnionNs layout
    let perField := fields.toList.flatMap fun (f, id) =>
      let t := tyStr id
      ["", s!"def {n}.{hn s!"get_{f}"} (u : {n}) : Zig.Result ({t}) := {withStorageEnc structNames s.srcTypes id s!"{ns}.get ({t}) u.bytes"}", "",
       s!"def {n}.{hn s!"modify_{f}"} (g : {t} → {t}) (u : {n}) : {n} :=",
       s!"  {withStorageEnc structNames s.srcTypes id s!"⟨{ns}.set u.bytes (g (Zig.Raw.getD ({ns}.get ({t}) u.bytes)))⟩"}"]
    String.intercalate "\n"
      ([s!"structure {n} where", s!"  bytes : Vector Zig.Byte {size}",
        "  deriving Repr, Inhabited, DecidableEq"] ++ perField)
  | .union _ _ tag fields =>
    let tagName := match tag.bind (s.srcTypes[·]?) with
      | some t => emitTy structNames s.srcTypes t
      | none => "Unit"
    let isVoid (id : TyId) : Bool := s.srcTypes[id]! == .void
    let wild := if fields.size > 1 then ["  | _ => throw .panic"] else []
    let ctors := fields.toList.map fun (f, id) =>
      if isVoid id then s!"  | {fm f}" else s!"  | {fm f} (v : {tyStr id})"
    let tagArms := fields.toList.map fun (f, id) =>
      let pat := if isVoid id then s!".{fm f}" else s!".{fm f} _"
      s!"  | {pat} => .{fm f}"
    let perField := fields.toList.flatMap fun (f, id) =>
      let fm := fm f
      let (pat, val, pty) :=
        if isVoid id then (s!".{fm}", "()", "Unit") else (s!".{fm} v", "v", tyStr id)
      -- Another field is active: `f` becomes active, its payload `default` (Zig: undefined).
      let (keep, apply, fresh, applyFresh, g) :=
        if isVoid id then (s!".{fm}", s!".{fm}", s!".{fm}", s!".{fm}", "_g")
        else (s!".{fm} v", s!".{fm} (g v)", s!".{fm} default", s!".{fm} (g default)", "g")
      let multi (l : String) : List String := if fields.size > 1 then [l] else []
      ["", s!"def {n}.{hn s!"get_{f}"} : {n} → Zig.Result ({pty})", s!"  | {pat} => pure {val}"] ++ wild ++
      ["", s!"def {n}.{hn s!"modify_{f}"} ({g} : {pty} → {pty}) : {n} → {n}", s!"  | {pat} => {apply}"] ++
        multi s!"  | _ => {applyFresh}" ++
      ["", s!"def {n}.{hn s!"setTag_{f}"} : {n} → {n}", s!"  | {pat} => {keep}"] ++ multi s!"  | _ => {fresh}"
    String.intercalate "\n"
      ([s!"inductive {n} where"] ++ ctors ++ ["  deriving Repr, Inhabited, DecidableEq", "",
        s!"def {n}.{hn "tag"} : {n} → {tagName}"] ++ tagArms ++ perField)
  | .struct _ layout fields =>
    let fieldLines := (fields.map fun (fname, fty) => s!"  {fm fname} : {tyStr fty}").toList
    let decl := [s!"structure {n} where"] ++ fieldLines ++ ["  deriving Repr, Inhabited, DecidableEq"]
    if layout != "packed" then String.intercalate "\n" decl else
    -- `Zig.Packed`: field 0 in the lowest bits (`ZigLean/Packed.lean`).
    let bits := fields.foldl (fun acc (_, t) => acc + (packedBits s.srcTypes t).getD 0) 0
    let offs := (List.range fields.size).map (packedFieldBit s.srcTypes fields)
    let toBits := (fields.toList.zip offs).map fun ((f, _), o) =>
      s!"((Zig.Packed.toBits v.{fm f}).setWidth {bits} <<< {o})"
    let ofBits := (fields.toList.zip offs).map fun ((f, _), o) =>
      s!"{fm f} := Zig.Packed.get b {o}"
    -- `valid`: the fields that can hold bits that are not a value (an enum, in any depth).
    let valid := (fields.toList.zip offs).filterMap fun ((_, t), o) =>
      if packedHasEnum s.srcTypes t then some s!"Zig.Packed.validAt ({tyStr t}) b {o}" else none
    String.intercalate "\n" (decl ++ ["",
      s!"instance : Zig.Packed {n} {bits} where",
      s!"  toBits {if toBits.isEmpty then "_" else "v"} := {if toBits.isEmpty then "(0 : BitVec 0)" else String.intercalate " ||| " toBits}",
      s!"  ofBits {if ofBits.isEmpty then "_" else "b"} := \{ {String.intercalate ", " ofBits} }"] ++
      (if valid.isEmpty then [] else [s!"  valid b := {String.intercalate " && " valid}"]))
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
  | some (.union name _ tag fs) =>
    if acc.contains name then acc
    else (tag.toArray ++ fs.map (·.2)).foldl (memNamed types layouts) (acc.push name)
  | some (.optional c) | some (.array _ c _) => memNamed types layouts acc c
  | some (.errorUnion _ c) => memNamed types layouts acc c
  | _ => acc

/-- The named types that get a `Zig.Enc` instance: those that a pointer of a function that uses
memory can point to, the types of the globals, and every `extern` or `packed` union with its
field types. A v0 function never has one, so v0 translations do not change. -/
def encTypeNames (funcs : Array Func) (memFuncs : Array String) : Array String :=
  funcs.foldl (init := #[]) fun acc f =>
    -- An `extern` or `packed` union reads its fields with `Zig.Enc`, also in a pure function.
    let acc := f.types.zipIdx.foldl (init := acc) fun acc (t, id) => match t with
      | .union _ _ none _ => memNamed f.types f.layouts acc id
      | _ => acc
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
  if encNames.contains s.zigName then s!"{body}\n\n{emitEnc structNames s}" else body

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
  | ufield (union : String) (getName modifyName : String)
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
  /-- Branch targets, deduplicated in first-use order. -/
  brT : Array InstId
  /-- Ordinary repeat targets in first-use order; dispatch exits remain separate. -/
  repT : Array InstId
  /-- Actual emitted value uses across the entire function, including nested bodies.
  `none` preserves the scan fallback for bare public expression-emission contexts. -/
  instUses : Option (Std.HashSet InstId) := none
  /-- Membership of actual `br` targets, prepared once for normal and bare contexts.
  `none` lets a public bare `emitStmts` call prepare it before recursive emission. -/
  branchTargetSet : Option (Std.HashSet InstId) := none
  /-- Outward-terminal block certificates from one uniqueness-guarded body traversal.
  Bare contexts default to no certificate; recursive emission does not rescan bodies. -/
  outwardBlocks : Std.HashMap InstId Bool := {}
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
  spawnSemantics : SpawnSemantics := .available
  /-- Typed caller execution of each complete capture, including pure slice adapters. -/
  spawnFallbacks : Array (String × String) := #[]
  /-- First-match fallback lookup, prepared after assigning `spawnFallbacks`. Public callers
  changing that array must reset this cache to `none`; bare contexts retain array lookup. -/
  spawnFallbackMap : Option (Std.HashMap String String) := none
  /-- The Zig version that wrote the AIR (`Func.zigVersion`), for the float ops whose result
  differs by version (`docs/floats.md` §Per-version differences). -/
  zigVersion : String
  /-- This function uses memory (`Air2Lean/Memory.lean`): it returns `Zig.MemM`, and its body
  runs in `Zig.MM`. -/
  mem : Bool
  /-- The names of the functions that use memory. -/
  memFuncs : Array String
  /-- This function reaches a sync op (`Air2Lean/Memory.lean`'s `concFunctions`): it returns
  `Zig.ConcM Tgt`, and its body runs in `Zig.CM Tgt`. -/
  conc : Bool := false
  /-- The names of the concurrent functions. -/
  concFuncs : Array String := #[]
  layouts : Array Layout
  /-- The `alloc`s whose address escapes: stack blocks, not places. -/
  escaping : Array InstId
  /-- The block of each global of `Func.globals`: its index in the program's globals
  (`emitGlobals`). -/
  globalIds : Array Nat := #[]
  /-- The functions whose address the program takes (`fnRefs`), as `(function type name,
  function name, block)`: an indirect call compares its pointer with these blocks. -/
  fnBlocks : Array (String × String × Nat) := #[]

private def prepareSpawnFallbackMap (fallbacks : Array (String × String)) : Std.HashMap String String :=
  let empty : Std.HashMap String String := {}
  fallbacks.foldl (fun lookup (worker, body) =>
    if lookup.contains worker then lookup else lookup.insert worker body) empty

/-- Prepare the fallback lookup once, preserving the public array's first-match rule. -/
def FCtx.prepareSpawnFallbacks (fc : FCtx) : FCtx :=
  { fc with spawnFallbackMap := some (prepareSpawnFallbackMap fc.spawnFallbacks) }

def FCtx.spawnFallback (fc : FCtx) (worker : String) : String :=
  match fc.spawnFallbackMap with
  | some lookup => lookup[worker]?.getD ""
  | none => (fc.spawnFallbacks.find? (·.1 == worker)).map (·.2) |>.getD ""

def FCtx.memberLookup (fc : FCtx) (ty : Ty) : String → String :=
  Air2Lean.memberLookup ty (fc.structNames.map (·.2))
def FCtx.memberName (fc : FCtx) (ty : Ty) (raw : String) : String :=
  fc.memberLookup ty raw
def FCtx.helperName (fc : FCtx) (ty : Ty) (raw : String) : String :=
  Air2Lean.helperName ty raw (fc.structNames.map (·.2))

def FCtx.tyOfId (fc : FCtx) (tid : TyId) : Ty := fc.types[tid]!
def FCtx.emitTyOf (fc : FCtx) (tid : TyId) : String :=
  emitTy fc.structNames fc.types (fc.tyOfId tid) (pureSlice := !fc.mem)
def FCtx.storageExpr (fc : FCtx) (tid : TyId) (expr : String) : String :=
  withStorageEnc fc.structNames fc.types tid expr

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
  | .ptrNull tid | .ptrOther tid _ | .sliceConst tid .. => fc.tyOfId tid

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

def FCtx.isPtrTy (fc : FCtx) (tid : TyId) : Bool := match fc.tyOfId tid with | .ptr .. => true | _ => false

/-- Is `v`'s type a (non-optional) pointer? A `bitcast` to/from an int (`@intFromPtr`,
`@ptrFromInt`) picks this side by it (M20). -/
def FCtx.isPtr (fc : FCtx) (v : Val) : Bool := match fc.valTy v with | .ptr .. => true | _ => false

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
  | .int tid n =>
    match fc.tyOfId tid with
    | .struct _ "packed" _ =>
      let bits := (packedBits fc.types tid).getD 0
      s!"(Zig.Packed.ofBits {tagLit bits n} : {fc.emitTyOf tid})"
    | _ => tagLit (fc.tyBits tid) n
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
  | .func name .. => (fc.funcNames.find? (·.1 == name)).map (·.2) |>.getD name
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
      | some (f, _) => s!"{e}.{fc.memberName (fc.tyOfId tid) f}"
      | none => s!"({e}.{fc.helperName (fc.tyOfId tid) "mk"} (BitVec.ofInt {fc.tyBits tag} ({v})))"
    | _ => "default" -- unreachable: `Json.lean` builds `enumTag` only for an enum type
  | .unionVal tid idx p =>
    let u := fc.emitTyOf tid
    match fc.tyOfId tid with
    | .union _ layout none fields =>
      match fields[idx]? with
      | some (_, fty) =>
        fc.storageExpr fty (rawUnionInit u layout ((fc.layouts[tid]?.bind (·.size)).getD 0)
          (fc.resolveVal env p) (fc.emitTyOf fty))
      | none => "default"
    | .union _ _ _ fields =>
      match fields[idx]? with
      | some (f, fty) =>
        if fc.tyOfId fty == .void then s!"{u}.{fc.memberName (fc.tyOfId tid) f}"
        else s!"({u}.{fc.memberName (fc.tyOfId tid) f} {fc.resolveVal env p})"
      | none => "default"
    | _ => "default" -- unreachable: `Json.lean` builds `unionVal` only for a union type
  | .agg tid elems =>
    let items (xs : Array Val) := ", ".intercalate (xs.map (fc.resolveVal env)).toList
    match fc.tyOfId tid with
    -- A sentinel is the last item of the value (`Ty.array`).
    | .array len _ s =>
      s!"(#v[{items (elems.extract 0 (len + if s then 1 else 0))}] : {fc.emitTyOf tid})"
    -- A vector has no sentinel (`docs/air-json.md`'s `elems`).
    | .vector len _ => s!"((⟨#v[{items (elems.extract 0 len)}]⟩) : {fc.emitTyOf tid})"
    | .struct _ _ fields =>
      let fm := fc.memberLookup (fc.tyOfId tid)
      let assigns := (fields.zip elems).toList.map fun ((f, _), e) =>
        s!"{fm f} := {fc.resolveVal env e}"
      s!"(\{ {", ".intercalate assigns} } : {fc.emitTyOf tid})"
    | .tuple _ => if elems.isEmpty then "()" else s!"({items elems})"
    | _ => "default" -- unreachable: the exporter writes `elems` only for these types
  | .ptrConst _ g off => s!"(⟨some {fc.globalIds[g]!}, {off}⟩ : Zig.Ptr)"
  | .ptrNull _ => "Zig.Ptr.null"
  | .ptrOther .. => "(panic! \"air2lean: a pointer constant without a global\")"
  | .sliceConst _ p len => s!"(⟨{fc.resolveVal env p}, {fc.resolveVal env len}⟩ : Zig.Slice)"

def FCtx.resolveCallee (fc : FCtx) (v : Val) : Bool × String :=
  match v with
  | .func name noreturn .. =>
    (noreturn, (fc.funcNames.find? (·.1 == name)).map (·.2) |>.getD name)
  | _ => (false, "panic! \"air2lean: indirect calls are outside the subset\"")


/-- A right-associated tuple projection, empty for the single-field representation. -/
def tupleProjection (size index : Nat) : String :=
  String.join (List.replicate index ".2") ++ (if index + 1 < size then ".1" else "")

/-- The projection suffix for `struct_field_val s index`. -/
def FCtx.structFieldName (fc : FCtx) (s : Val) (index : Nat) : String :=
  match fc.valTy s with
  | .struct _ _ fields =>
    "." ++ ((fields[index]?).map (fun (n, _) => fc.memberName (fc.valTy s) n) |>.getD s!"fld{index}")
  | .tuple fields => tupleProjection fields.size index
  | _ => if index == 0 then ".1" else ".2"

def FCtx.structFieldNamesFor (fc : FCtx) (ty : Ty) : Array String :=
  match ty with
  | .struct _ _ fields =>
    let fm := fc.memberLookup ty
    fields.map (fun (n, _) => fm n)
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
    s!"Zig.enumOf ({fc.emitTyOf dstId}.{fc.helperName dst "ofInt?"} (Zig.val {fc.tySigned tag} ({fc.emitValTy a}.{fc.helperName (fc.valTy a) "toBits"} {av})))"
  | _, .enum .. =>
    -- An unnamed value of an exhaustive enum: `invalidEnumValue` (`.panic`).
    s!"Zig.enumOf ({fc.emitTyOf dstId}.{fc.helperName dst "ofInt?"} (Zig.val {fc.valSigned a} {av}))"
  | .enum _ tag _ _, _ =>
    let bits := s!"({fc.emitValTy a}.{fc.helperName (fc.valTy a) "toBits"} {av})"
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
of a place with one more step, a validated parent pointer with the terminal step removed,
a `bitcast` of a place with the same path. -/
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
            PathStep.field ((fields[idx]?).map (fc.memberName base ·.1) |>.getD s!"fld{idx}")
          | .union .. =>
            match fc.unionField? base idx with
            | some (u, f, _) => .ufield u (fc.helperName base s!"get_{f}") (fc.helperName base s!"modify_{f}")
            | none => .field s!"fld{idx}"
          | _ => .field s!"fld{idx}"
        acc.push (i.id, root, path.push step)
      | none => acc
    | .fieldParentPtr (.inst b) _ =>
      -- The checker proved the exact terminal struct field and result pointee type.
      match acc.find? (·.1 == b) with
      | some (_, root, path) => acc.push (i.id, root, path.pop)
      | none => acc
    | .sliceFieldPtr len (.inst b) =>
      match acc.find? (·.1 == b) with
      | some (_, root, path) => acc.push (i.id, root, path.push (.field (if len then "len" else "ptr")))
      | none => acc
    | .bitcast (.inst b) =>
      match acc.find? (·.1 == b) with
      | some (_, root, path) =>
        if samePointee fc.types (fc.instTyId b) i.ty then acc.push (i.id, root, path) else acc
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

/-- The body monad: `Zig.M` (pure) or `Zig.MM` (uses memory). -/
def FCtx.monad (fc : FCtx) : String :=
  if fc.conc then "Zig.CM Tgt" else if fc.mem then "Zig.MM" else "Zig.M"

/-- The lift of a call to a function that uses memory (`Zig.MemM`). -/
def FCtx.callMName (fc : FCtx) : String := if fc.conc then "Zig.callMC" else "Zig.callM"

/-- The lift of a call to a pure function (`Zig.Result`). -/
def FCtx.callRName (fc : FCtx) : String :=
  if fc.conc then "Zig.callRC" else if fc.mem then "Zig.callR" else "Zig.call"

/-- The call `term` of the function `name`, lifted to this function's monad. -/
def FCtx.callOf (fc : FCtx) (name term : String) (memCallee : Bool) : String :=
  if fc.concFuncs.contains name then s!"Zig.callC ({term})"
  else if memCallee then s!"{fc.callMName} ({term})"
  else s!"{fc.callRName} ({term})"

/-- A `Zig.Result` term called from the body. -/
def FCtx.liftR (fc : FCtx) (e : String) : String :=
  s!"{fc.callRName} ({e})"

/-- The value at a place, as a term inside a `do` block. -/
def FCtx.loadPlace (fc : FCtx) (v : Val) : String :=
  match fc.place? v with
  | some (field, path) =>
    path.foldl (init := s!"(← get).{field}") fun e step =>
      match step with
      | .field f => s!"({e}).{f}"
      | .ufield u g _ => s!"(← {fc.callRName} ({u}.{g} {e}))"
  | none => "(panic! \"air2lean: load through a pointer that is not a place\")"

/-- `base` with the value `old` at `path` replaced by `new old`. -/
def setPath (path : List PathStep) (new : String → String) (base : String) : String :=
  match path with
  | [] => new base
  | .field f :: rest => s!"\{ {base} with {f} := {setPath rest new s!"({base}).{f}"} }"
  | .ufield u _ m :: rest =>
    let inner := setPath rest new "x"
    let x := if inner == setPath rest new "y" then "_" else "x"
    s!"({u}.{m} (fun {x} => {inner}) {base})"

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

/-- The alignment of an access through the pointer `v`: its type's `align(N)`. -/
def FCtx.ptrAlign (fc : FCtx) (v : Val) : Nat :=
  ((fc.valTyId? v).bind fun t => fc.layouts[t]?.bind (·.ptrAlign)).getD 1

/-- The Lean term of an atomic ordering (`Zig.AtomicOrder`; `Check.lean` rejects `unordered`). -/
def orderTerm : AtomicOrder → String
  | .unordered | .monotonic => "Zig.AtomicOrder.relaxed"
  | .acquire => "Zig.AtomicOrder.acquire"
  | .release => "Zig.AtomicOrder.release"
  | .acqRel => "Zig.AtomicOrder.acqRel"
  | .seqCst => "Zig.AtomicOrder.seqCst"

/-- An atomic op through `ptr` on an enum, a `bool` or a packed struct: the typed op (`Zig.atomicLoadAs`, …, on
the value's `Zig.Packed` bits), not the integer op. -/
def FCtx.atomicTyped (fc : FCtx) (ptr : Val) : Bool :=
  match fc.pointeeOf ptr with
  | .enum .. | .bool | .struct _ "packed" _ => true
  | _ => false

/-- The Lean type of the value that the pointer `v` points to. -/
def FCtx.pointeeTy (fc : FCtx) (v : Val) : String := emitTy fc.structNames fc.types (fc.pointeeOf v)

/-- The byte offset of field `idx` of the struct that the pointer `base` points to. -/
def FCtx.fieldOffsetIn (fc : FCtx) (c : TyId) (idx : Nat) : Nat :=
  match fc.tyOfId c with
  -- A byte-aligned field of a packed struct that is a whole number of bytes: its pointer is
  -- not a bit-pointer.
  | .struct _ "packed" fields => packedFieldBit fc.types fields idx / 8
  -- Every field of a tagged union is its payload.
  | .union _ _ (some tag) fields =>
    ((unionOffsets fc.types fc.layouts tag (fields.map (·.2))).map (·.2)).getD 0
  -- Every field of an `extern` or `packed` union is at offset 0.
  | .union _ _ none _ => 0
  | _ => (fc.layouts[c]?.bind (·.offsets[idx]?)).getD 0

def FCtx.fieldOffset (fc : FCtx) (base : Val) (idx : Nat) : Nat :=
  match fc.valTy base with
  | .ptr _ _ c => fc.fieldOffsetIn c idx
  | _ => 0

/-- A bit-pointer type's host integer size in bytes; 0 for every other type. -/
def FCtx.hostSize (fc : FCtx) (ptrTy : TyId) : Nat := (fc.layouts[ptrTy]?.map (·.hostSize)).getD 0

/-- The byte offset of field `idx` of the struct that the pointer type `ptrTy` points to
(`field_parent_ptr`'s own result type, unlike `fieldOffset`'s operand type). -/
def FCtx.fieldOffsetOfPtrTy (fc : FCtx) (ptrTy : TyId) (idx : Nat) : Nat :=
  match fc.tyOfId ptrTy with
  | .ptr _ _ c => fc.fieldOffsetIn c idx
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
    | .array len .. | .vector len _ => (rv, s!"({len} : BitVec 64)")
    | _ => (rv, "(panic! \"air2lean: items of a pointer without a length\")")

/-- `v` is a pointer to memory: not a place. -/
def FCtx.isMemPtr (fc : FCtx) (v : Val) : Bool :=
  !fc.isPlace v && match fc.valTy v with | .ptr .. => true | _ => false

/-- Bind the exact pointee's dictionary at a memory boundary. -/
def FCtx.pointeeStorageExpr (fc : FCtx) (ptr : Val) (expr : String) : String :=
  match (fc.valTyId? ptr).bind (ptrChild fc.types) with
  | some tid => fc.storageExpr tid expr
  | none => expr

/-- A load through a pointer to memory. -/
def FCtx.loadMem (fc : FCtx) (ptr : Val) (p : String) : String :=
  match fc.valTyId? ptr with
  | some t =>
    if fc.hostSize t != 0 then
      s!"Zig.loadBits ({fc.pointeeTy ptr}) {fc.hostSize t} {fc.ptrAlign ptr} \
        {(fc.layouts[t]?.map (·.bitOffset)).getD 0} {p}"
    else fc.pointeeStorageExpr ptr s!"Zig.load ({fc.pointeeTy ptr}) {fc.ptrAlign ptr} {p}"
  | none => s!"Zig.load ({fc.pointeeTy ptr}) {fc.ptrAlign ptr} {p}"

/-- A call argument. A pure callee gets the items of a `[]const T` argument (`Zig.readSlice`). -/
def FCtx.callArg (fc : FCtx) (env : Array (InstId × String)) (memCallee : Bool) (a : Val) : String :=
  if fc.mem && !memCallee && fc.isSlice a then
    let item := emitTy fc.structNames fc.types (fc.tyOfId (fc.itemTyId a))
    s!"(← {fc.callMName} ({fc.storageExpr (fc.itemTyId a) s!"Zig.readSlice ({item}) {fc.itemAlign a} {fc.resolveVal env a}"}))"
  else fc.resolveVal env a

/-- A call to the allocator model (`ZigLean/Mem/Alloc.lean`), a `Zig.MemM` term. `ret`: the
call's result type. `args[0]` is the allocator. -/
def FCtx.allocCall (fc : FCtx) (env : Array (InstId × String)) (fn : AllocFn) (args : Array Val)
    (ret : TyId) : String :=
  let rv := fc.resolveVal env
  -- The pointer or slice in the result (`E!*T`, `E![]T`, `?[]T`).
  let p := match fc.tyOfId ret with | .errorUnion _ p | .optional p => p | _ => ret
  let size := fc.sizeOf ((ptrChild fc.types p).getD 0)
  let align := (fc.layouts[p]?.bind (·.ptrAlign)).getD 1
  -- The size of what the pointer or slice argument `args[1]` points to.
  let arg (i : Nat) : Val := args[i]?.getD .void
  let argSize := fc.sizeOf (((fc.valTyId? (arg 1)).bind (ptrChild fc.types)).getD 0)
  let a := rv (arg 0)
  match fn with
  | .create => s!"Zig.Allocator.create {a} {size} {align}"
  | .alloc | .alignedAlloc => s!"Zig.Allocator.alloc {a} {size} {align} {rv (arg 1)}"
  | .allocSentinel =>
    let sentinel := (fc.layouts[p]?.bind (·.sentinelByte)).getD 0
    s!"Zig.Allocator.allocSentinel {a} {rv (arg 1)} ({sentinel}#8)"
  | .dupe => s!"Zig.Allocator.dupe {a} {size} {align} {fc.ptrAlign (arg 1)} {rv (arg 1)}"
  | .destroy => s!"Zig.Allocator.destroy {a} {argSize} {rv (arg 1)}"
  | .free =>
    let sentinel := ((fc.valTyId? (arg 1)).bind (fc.layouts[·]?) |>.map (·.sentinel)).getD false
    s!"Zig.Allocator.{if sentinel then "freeSentinel" else "free"} {a} {argSize} {rv (arg 1)}"
  | .remap => s!"Zig.Allocator.remap {a} {argSize} {rv (arg 1)} {rv (arg 2)}"
  | .realloc => s!"Zig.Allocator.realloc {a} {rv (arg 1)} {rv (arg 2)}"

/-- A sync op of the thread model (`ZigLean/Conc/Call.lean`), a `Zig.CM Tgt` term. `.spawn`:
`callee`'s `spawnFn` (its `comptime_fn`) names the spawned function, a constructor of the
program's `Tgt` (`emitTgt`); `args[1]` is the complete by-value captured tuple. Zero
fields use `Unit`, one field keeps the historical scalar representation, and multiple
fields form a right-associated product. Dispatch applies each field in source order. `.join`: `args[0]` is the `Thread` handle. -/
def FCtx.threadCall (fc : FCtx) (env : Array (InstId × String)) (fn : ThreadFn) (callee : Val)
    (args : Array Val) : String :=
  let rv := fc.resolveVal env
  match fn with
  | .spawn =>
    let spawnFn := match callee with | .func _ _ sf => sf.getD "" | _ => ""
    let target := (fc.funcNames.find? (·.1 == spawnFn)).map (·.2) |>.getD spawnFn
    let op := if fc.spawnSemantics == .fallible then "spawnWithPolicyC .fallible" else "spawnC"
    s!"Zig.{op} (Tgt.{target} {rv (args[1]?.getD .void)})"
  | .join => s!"Zig.joinC {rv (args[0]?.getD .void)}"
  | .yield => "Zig.threadYieldC"
  | .spinLoopHint => "Zig.spinLoopHintC"
  -- `Io.futex*(io, ptr, value)` (the `comptime T` argument is not a runtime argument).
  | .futexWait => s!"Zig.futexWaitCancelableC {String.intercalate " " (args.toList.map rv)}"
  | .futexWaitU => s!"Zig.futexWaitC {String.intercalate " " (args.toList.map rv)}"
  | .futexWake => s!"Zig.futexWakeC {String.intercalate " " (args.toList.map rv)}"
  -- `Thread.Futex.wait(ptr, expect)`, `Thread.Futex.wake(ptr, max_waiters)`.
  | .threadFutexWait => s!"Zig.threadFutexWaitC {String.intercalate " " (args.toList.map rv)}"
  | .threadFutexWake => s!"Zig.threadFutexWakeC {String.intercalate " " (args.toList.map rv)}"
  -- `DarwinImpl.lock(self)`: `self` points to the `os_unfair_lock` (its only field).
  | .osLock => s!"Zig.osUnfairLockC {rv (args[0]?.getD .void)}"
  | .osUnlock => s!"Zig.osUnfairUnlockC {rv (args[0]?.getD .void)}"
  | .osTryLock => s!"Zig.osUnfairTryLockC {rv (args[0]?.getD .void)}"
  | .timerStart | .timerRead | .futexTimedWait => "Zig.callRC (throw Zig.Error.unspecified)"
  -- `Io.Group.async(g, io, args)` (the task is `callee`'s `spawnFn`, as for `.spawn`).
  | .groupAsync | .groupConcurrent =>
    let spawnFn := match callee with | .func _ _ sf => sf.getD "" | _ => ""
    let target := (fc.funcNames.find? (·.1 == spawnFn)).map (·.2) |>.getD spawnFn
    let capture := rv (args[2]?.getD .void)
    let op := if fn == .groupAsync then "groupAsyncC" else "groupConcurrentC"
    let op := if fc.spawnSemantics == .fallible then
      (if fn == .groupAsync then "groupAsyncWithPolicyC .fallible" else "groupConcurrentWithPolicyC .fallible")
      else op
    let fallback := if fc.spawnSemantics == .fallible && fn == .groupAsync then
      let body := fc.spawnFallback spawnFn
      s!" (({body}) {capture})"
      else ""
    s!"Zig.{op} {rv (args[0]?.getD .void)} {rv (args[1]?.getD .void)} \
      (Tgt.{target} {capture}){fallback}"
  | .groupAwait => s!"Zig.groupAwaitC {rv (args[0]?.getD .void)} {rv (args[1]?.getD .void)}"
  | .groupCancel => s!"Zig.groupCancelC {rv (args[0]?.getD .void)} {rv (args[1]?.getD .void)}"

/-- A load of item `i` of the slice, many-pointer or array pointer `v`, whose item pointer is
`p`. -/
def FCtx.loadItem (fc : FCtx) (v : Val) (p i : String) : String :=
  let item := fc.itemTyId v
  fc.storageExpr item s!"Zig.load ({emitTy fc.structNames fc.types (fc.tyOfId item)}) {fc.itemAlign v} \
    ({p}.elem {fc.sizeOf item} {i})"

/-! ## `alloc` → `<Fn>Locals` field prepass -/

/-- Typed per-loop selector state; unlike the original operand it changes on dispatch. -/
def dispatchFieldName (id : InstId) : String := s!"dispatchValue{id}"

def dispatchFieldNames (allInsts : Array Inst) : Array String :=
  allInsts.filterMap fun i => match i.op with
    | .loopSwitchBr .. => some (dispatchFieldName i.id) | _ => none

def FCtx.dispatchTys (fc : FCtx) : Array (InstId × Ty) :=
  fc.allInsts.filterMap fun i => match i.op with
    | .loopSwitchBr initial .. => some (i.id, fc.valTy initial) | _ => none

/-- `(allocId, fieldName, childTy)` for every `alloc` in the function: the field name is the
`dbg_var_ptr`-given name when one names that alloc, else `local<id>`. -/
def collectAllocs (types : Array Ty) (allInsts : Array Inst) (reserved : Array String := #[]) : Array (InstId × String × TyId) := Id.run do
  let allocIds := allInsts.filterMap fun i => match i.op with | .alloc => some i.id | _ => none
  let names := allInsts.filterMap fun i => match i.op with
    | .dbg (some nm) (some (.inst aid)) => if allocIds.contains aid then some (aid, nm) else none
    | _ => none
  let mut used := typeCoreNames.push "mk" ++ runtimeNames ++ reserved ++ dispatchFieldNames allInsts
  let mut out := #[]
  for aid in allocIds do
    let raw := (names.find? (·.1 == aid)).map (·.2) |>.getD s!"local{aid}"
    let nm := freshName raw used
    used := used.push nm
    let childTy := match allInsts.find? (·.id == aid) with
      | some i => match types[i.ty]! with
        | .ptr _ _ child => child
        | _ => i.ty
      | none => 0
    out := out.push (aid, nm, childTy)
  return out

/-- An escaping `alloc`'s field holds the pointer to its stack block. `mem`: the function uses
memory. -/
def emitLocalsStruct (structNames : Array (String × String)) (types : Array Ty)
    (localsName : String) (allocs : Array (InstId × String × TyId)) (escaping : Array InstId)
    (mem : Bool) (dispatches : Array (InstId × Ty) := #[]) : String :=
  let lines := (allocs.map fun (aid, nm, cty) =>
    if escaping.contains aid then s!"  {nm} : Zig.Ptr"
    else s!"  {nm} : {emitTy structNames types types[cty]! (pureSlice := !mem)}").toList
  String.intercalate "\n" ([s!"structure {localsName} where"] ++ lines ++
    (dispatches.map fun (id, ty) => s!"  {dispatchFieldName id} : {emitTy structNames types ty (pureSlice := !mem)}").toList ++
    ["  deriving Inhabited"])

/-! ## `Exit` prepass and emission -/

def dedupIds (a : Array InstId) : Array InstId :=
  a.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

def blockLoopTys (allInsts : Array Inst) : Array (InstId × TyId) :=
  allInsts.filterMap fun i => match i.op with | .block _ | .loop _ => some (i.id, i.ty) | _ => none

def brTargets (allInsts : Array Inst) : Array InstId :=
  dedupIds (allInsts.filterMap fun i => match i.op with | .br t _ => some t | _ => none)

/-- Prepare target membership once; recursive block emission reuses this context. -/
def FCtx.prepareBranchTargets (fc : FCtx) : FCtx :=
  match fc.branchTargetSet with
  | some _ => fc
  | none =>
    let empty : Std.HashSet InstId := {}
    let targets := fc.allInsts.foldl (init := empty) fun targets i =>
      match i.op with | .br target _ => targets.insert target | _ => targets
    { fc with branchTargetSet := some targets }

def repTargets (allInsts : Array Inst) : Array InstId :=
  dedupIds (allInsts.filterMap fun i => match i.op with | .«repeat» t => some t | _ => none)

def emitExitInductive (structNames : Array (String × String)) (types : Array Ty)
    (exitName : String) (retTy : TyId) (blTys : Array (InstId × TyId)) (brT repT : Array InstId)
    (mem : Bool) (dispatches : Array (InstId × Ty) := #[]) : String :=
  let retLine := match types[retTy]! with
    | .void => "  | ret"
    | rt => s!"  | ret (v : {emitTy structNames types rt (pureSlice := !mem)})"
  let brLines := (brT.map fun k =>
    let kty := (blTys.find? (·.1 == k)).map (fun (_, t) => types[t]!) |>.getD .void
    match kty with
    | .void => s!"  | br{k}"
    | t => s!"  | br{k} (v : {emitTy structNames types t (pureSlice := !mem)})").toList
  let repLines := (repT.map fun k => s!"  | rep{k}").toList
  String.intercalate "\n" ([s!"inductive {exitName} where", retLine] ++ brLines ++ repLines ++
    (dispatches.map fun (id, ty) => s!"  | dispatch{id} (v : {emitTy structNames types ty (pureSlice := !mem)})").toList)

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
  | .withOverflow _ a b | .shlWithOverflow a b => #[a, b]
  | .countBits _ a | .permuteBits _ a => #[a]
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
  | .splat a | .reduce _ a => #[a]
  | .select pred a b => #[pred, a, b]
  | .shuffle a b mask =>
    #[a] ++ (match b with | some v => #[v] | none => #[]) ++
      mask.filterMap fun l => match l with | .value v => some v | _ => none
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
  | .fieldParentPtr fieldPtr _ => if fc.isMemPtr fieldPtr then #[fieldPtr] else #[]
  | .setUnionTag p tag => if fc.isMemPtr p then #[p, tag] else #[]
  | .retLoad p | .load p => if fc.isMemPtr p then #[p] else #[]
  | .isNullPtr _ p | .optPayloadPtr _ p | .isErrPtr _ p | .errPayloadPtr _ p | .errCodePtr p => #[p]
  | .store p v => (if fc.isMemPtr p then #[p] else #[]) ++ #[v]
  | .atomicLoad p _ => if fc.isMemPtr p then #[p] else #[]
  | .atomicStore p v _ => (if fc.isMemPtr p then #[p] else #[]) ++ #[v]
  | .atomicRmw _ _ p v => (if fc.isMemPtr p then #[p] else #[]) ++ #[v]
  | .cmpxchg _ p expected new _ _ => (if fc.isMemPtr p then #[p] else #[]) ++ #[expected, new]
  | .sliceFieldPtr _ p => if fc.isMemPtr p then #[p] else #[]
  | .ptrAdd _ a b | .elemPtr a b | .ptrElemVal a b | .arrayElemVal a b | .slice a b
  | .memset a b | .memcpy a b => #[a, b]
  | .slicePtr a | .arrayToSlice a | .tagName a | .errorName a => #[a]
  | .sliceLen s => #[s]
  | .sliceElemVal s i => #[s, i]
  | .structFieldVal s _ => #[s]
  | .aggregateInit elems => elems
  | .call callee args => match callee with
    | .func _ true .. => #[]
    | .inst _ => #[callee] ++ args
    | _ => args
  | .block _ => #[]
  | .loop _ => #[]
  | .br target v => match fc.targetTy target with | .void => #[] | _ => #[v]
  | .switchDispatch _ v => #[v]
  | .«repeat» _ => #[]
  | .condBr c _ _ => #[c]
  | .switchBr v cases _ | .loopSwitchBr v cases _ =>
    #[v] ++ cases.foldl (fun acc c =>
      let acc := c.items.foldl Array.push acc
      c.ranges.foldl (fun acc (lo, hi) => (acc.push lo).push hi) acc) #[]
  | .«try» v _ | .tryPtr v _ => #[v]
  | .ret v => match fc.tyOfId fc.retTy with | .void => #[] | _ => #[v]
  | .unreach => #[]
  | .trap => #[]
  | .line _ => #[]
  | .dbg _ _ => #[]
  -- An lvalue output's `ref` is a pointer, used as `store`'s pointer.
  | .asm _ _ _ outputs inputs =>
    outputs.filterMap (fun o => o.ref.filter fc.isMemPtr) ++ inputs.filterMap (·.ref)

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

/-- Cache direct value uses from every instruction in the flattened function. Constant
aggregate SSA refs are rejected by Canon; debug-only refs do not read runtime values. -/
def FCtx.computeInstUses (fc : FCtx) : Std.HashSet InstId :=
  let empty : Std.HashSet InstId := {}
  fc.allInsts.foldl (init := empty) fun used i =>
    (fc.directVals i.op).foldl (init := used) fun used v =>
      match v with | .inst id => used.insert id | _ => used

/-- Prepare runtime-use membership once at the public statement-emission boundary. -/
def FCtx.prepareInstUses (fc : FCtx) : FCtx :=
  match fc.instUses with
  | some _ => fc
  | none => { fc with instUses := some fc.computeInstUses }

/-- Some instruction of the function reads `id`. Direct public scalar emission on a
bare context retains the original scan; statement emission prepares a shared cache. -/
def FCtx.isReferenced (fc : FCtx) (id : InstId) : Bool :=
  match fc.instUses with
  | some uses => uses.contains id
  | none => fc.allInsts.any fun i => (fc.directVals i.op).contains (.inst id)

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

/-- Case values and bodies determine captures; initialization reads the initial operand
at the caller. References to that original operand inside bodies remain ordinary captures. -/
def dispatchCaptureBody (i : Inst) : Array Inst :=
  match i.op with
  | .loopSwitchBr _ cases elseBody => #[{ i with op := .switchBr .void cases elseBody }]
  | _ => #[]

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

/-! ## Inline asm (M21) -/

/-- One distinct asm op across the whole program (`docs/generated-code.md` §asm): the generated
`opaque` def's name and `BitVec` widths. Two occurrences share a def when their source, ordered
constraint list (outputs then inputs) and operand widths all match — width is not part of the
brief's stated key (a hash of template and constraints), but two different-width asm exprs
sharing a name would give one of them the wrong `BitVec` width, so width is folded into the
identity here too. -/
structure AsmDef where
  name : String
  inputWidths : Array Nat
  /-- The width of each output, in output order. -/
  outputWidths : Array Nat
  deriving BEq

/-- The identity of an asm op: the source template, the ordered constraint list and the operand
widths. One output or none keeps the text of an `Option` width, so the names of those ops do not
change. -/
def asmKey (source : String) (constraints : Array String) (inputWidths : Array Nat)
    (outputWidths : Array Nat) : String :=
  let outs := match outputWidths.toList with
    | [] => "none"
    | [w] => s!"(some {w})"
    | ws => s!"{ws}"
  s!"{source}\u0001{"\u0001".intercalate constraints.toList}\u0001\
    {inputWidths.toList}\u0001{outs}"

/-- The generated Lean name of the `opaque` def for an asm op: `airAsm_<hash>`, `<hash>` a small
FNV-1a hash of the source template, the ordered constraint list and the operand widths. Not
Lean's own `hash`: this only needs to be stable within one generation run (the toolchain is
pinned), and a hand-rolled hash keeps that independent of a core implementation detail.
`collectAsmOps` removes duplicates by the full `asmKey`, not by this name: two different asm ops
with the same hash give two `opaque` defs of one name, a Lean build error, never one shared def. -/
def asmDefName (key : String) : String :=
  let h := key.foldl (init := (0x811c9dc5 : UInt32)) fun h c =>
    (h ^^^ c.val) * 0x01000193
  s!"airAsm_{h}"

/-- The bit width of `v`'s type within `f` (0 if it is not an integer): `Op.asm`'s operands, since
`Check.lean` accepts only register (so integer) operands. -/
def asmValBits (f : Func) (v : Val) : Nat :=
  let tyBits (tid : TyId) : Nat := match f.types[tid]? with | some (.int _ b) => b | _ => 0
  match v with
  | .inst id => ((f.allInsts.find? (·.id == id)).map fun i => tyBits i.ty).getD 0
  | v => (v.constTy?.map tyBits).getD 0

/-- The bit width of each output of an asm op: the result (no `ref`) has the instruction's type
`resTy`; an lvalue output has its pointer's child type. -/
def asmOutputWidths (types : Array Ty) (tyOf : Val → Option TyId) (resTy : TyId)
    (outputs : Array AsmOperand) : Array Nat :=
  let tyBits (tid : TyId) : Nat := match types[tid]? with | some (.int _ b) => b | _ => 0
  outputs.map fun o => match o.ref with
    | none => tyBits resTy
    | some r => ((tyOf r).bind fun p => match types[p]? with
        | some (.ptr _ _ c) => some (tyBits c)
        | _ => none).getD 0

/-- Every distinct asm op in `funcs`, in first-seen order (`asmKey` gives the identity). -/
def collectAsmOps (funcs : Array Func) : Array AsmDef := Id.run do
  let mut seen : Array String := #[]
  let mut defs : Array AsmDef := #[]
  for f in funcs do
    for i in f.allInsts do
      if i.op.isSpinHint then continue
      if let .asm source _ _ outputs inputs := i.op then
        let inputWidths := inputs.map fun o => asmValBits f o.ref.get!
        let tyOf (v : Val) : Option TyId := match v with
          | .inst id => (f.allInsts.find? (·.id == id)).map (·.ty)
          | v => v.constTy?
        let outputWidths := asmOutputWidths f.types tyOf i.ty outputs
        let constraints := outputs.map (·.constraint) ++ inputs.map (·.constraint)
        let key := asmKey source constraints inputWidths outputWidths
        if !seen.contains key then
          seen := seen.push key
          defs := defs.push { name := asmDefName key, inputWidths, outputWidths }
  return defs

/-- The `opaque` def for one distinct asm op: an uninterpreted function from its inputs' `BitVec`s
to its output's `BitVec` (`Unit` for no output; a tuple in output order for more than one). A proof can use only what the caller states
about it — no built-in axiom describes what any asm op computes (`Air2Lean/Air/Op.lean`'s `.asm`
doc comment). -/
def emitAsmDef (d : AsmDef) : String :=
  let params := (d.inputWidths.toList.zipIdx.map fun (w, k) => s!"(i{k} : BitVec {w})")
  let ret := if d.outputWidths.isEmpty then "Unit"
    else " × ".intercalate (d.outputWidths.toList.map fun w => s!"BitVec {w}")
  s!"opaque {d.name}{params.foldl (init := "") fun acc p => s!"{acc} {p}"} : {ret}"

/-- AIR can compute a value that nothing reads (`catch 0` still unwraps the error code). The
effect stays; the `_` prefix stops Lean's unused-variable warning. -/
def bindLet (fc : FCtx) (env : Array (InstId × String)) (id : InstId) (expr : String) :
    Array (InstId × String) × String :=
  let name := if fc.isReferenced id then s!"i{id}" else s!"_i{id}"
  (env.push (id, name), s!"let {name} ← {expr}")

/-- A straight-line (non-terminator, non-`block`/`loop`) instruction on scalars: at most one
output line. `emitSimple` lifts it to vectors. -/
def emitScalar (fc : FCtx) (env : Array (InstId × String)) (inst : Inst) :
    Array (InstId × String) × Option String :=
  let rv := fc.resolveVal env
  match inst.op with
  | .arg index => (env.push (inst.id, s!"p{index}"), none)
  | .arith op mode a b =>
    -- A float operand always has `mode = .checked`: `Check.lean` rejects the other modes.
    let expr :=
      match fc.tyOfId inst.ty with
      | .vector _ child =>
        -- Lane-wise: the same scalar function the non-vector case below calls, lifted by
        -- `Zig.Vec.map2`/`map2M` (`ZigLean/Vec.lean`).
        if fc.isFloatTy child then
          let f := match op with
            | .add => "Zig.Float.add" | .sub => "Zig.Float.sub" | .mul => s!"Zig.Float.mul{fc.rtSuffix}"
          s!"pure (Zig.Vec.map2 {f} {rv a} {rv b})"
        else
          let sgn := if fc.tySigned child then "true" else "false"
          match op, mode with
          | .add, .checked => s!"Zig.Vec.map2M (Zig.add {sgn}) {rv a} {rv b}"
          | .add, .wrap => s!"pure (Zig.Vec.map2 Zig.addWrap {rv a} {rv b})"
          | .add, .sat => s!"pure (Zig.Vec.map2 (Zig.addSat {sgn}) {rv a} {rv b})"
          | .sub, .checked => s!"Zig.Vec.map2M (Zig.sub {sgn}) {rv a} {rv b}"
          | .sub, .wrap => s!"pure (Zig.Vec.map2 Zig.subWrap {rv a} {rv b})"
          | .sub, .sat => s!"pure (Zig.Vec.map2 (Zig.subSat {sgn}) {rv a} {rv b})"
          | .mul, .checked => s!"Zig.Vec.map2M (Zig.mul {sgn}) {rv a} {rv b}"
          | .mul, .wrap => s!"pure (Zig.Vec.map2 Zig.mulWrap {rv a} {rv b})"
          | .mul, .sat => s!"pure (Zig.Vec.map2 (Zig.mulSat {sgn}) {rv a} {rv b})"
      | _ =>
        if fc.isFloat a then
          let f := match op with | .add => "Zig.Float.add" | .sub => "Zig.Float.sub" | .mul => s!"Zig.Float.mul{fc.rtSuffix}"
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
        | .rem => s!"Zig.Float.rem{fc.rtSuffix}Chk {rv a} {rv b}"
        | .mod => s!"Zig.Float.mod{fc.rtSuffix}Chk {rv a} {rv b}"
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
  | .shlWithOverflow a b =>
    let sgn := if fc.valSigned a then "true" else "false"
    let (env, l) := bindLet fc env inst.id s!"Zig.shlWithOverflow {sgn} {rv a} {rv b}"
    (env, some l)
  | .permuteBits op a =>
    let f := match op with
      | .byteSwap => "Zig.byteSwap" | .bitReverse => "Zig.bitReverse"
    let (env, l) := bindLet fc env inst.id s!"pure ({f} {rv a})"
    (env, some l)
  | .countBits op a =>
    let f := match op with
      | .clz => "Zig.clz" | .ctz => "Zig.ctz" | .popcount => "Zig.popcount"
    let (env, l) := bindLet fc env inst.id s!"pure ({f} {fc.tyBits inst.ty} {rv a})"
    (env, some l)
  | .splat a =>
    let (env, l) := bindLet fc env inst.id s!"pure (Zig.Vec.splat {rv a})"; (env, some l)
  | .select pred a b =>
    let (env, l) := bindLet fc env inst.id s!"pure (Zig.Vec.select {rv pred} {rv a} {rv b})"
    (env, some l)
  | .reduce op a =>
    -- The vector's element type dispatches to the same scalar function `.arith`'s int/float
    -- branches call. Zig's integer `.Add`/`.Mul` reduce wraps (`docs/floats.md` has no analogous
    -- note for ints: wrapping is safe because integer `+`/`*` stay associative under wraparound).
    let child := match fc.valTy a with | .vector _ c => c | _ => 0
    let expr :=
      if fc.isFloatTy child then
        match op with
        | .add => s!"pure (Zig.Vec.reduce Zig.Float.add {rv a})"
        | .mul => s!"pure (Zig.Vec.reduce Zig.Float.mul{fc.rtSuffix} {rv a})"
        | .min => s!"Zig.Vec.reduceM Zig.Float.minChk {rv a}"
        | .max => s!"Zig.Vec.reduceM Zig.Float.maxChk {rv a}"
        | .and | .or | .xor =>
          "(panic! \"air2lean: bitwise @reduce of a float vector\")"
      else if fc.tyOfId child == .bool then
        -- A `bool` vector: the safety checks of a vector op (`cmp_vector`, then `reduce .Or`).
        match op with
        | .and => s!"pure (Zig.Vec.reduce (· && ·) {rv a})"
        | .or => s!"pure (Zig.Vec.reduce (· || ·) {rv a})"
        | .xor => s!"pure (Zig.Vec.reduce (· ^^ ·) {rv a})"
        | _ => "(panic! \"air2lean: arithmetic @reduce of a bool vector\")"
      else
        let sgn := if fc.tySigned child then "true" else "false"
        match op with
        | .and => s!"pure (Zig.Vec.reduce (· &&& ·) {rv a})"
        | .or => s!"pure (Zig.Vec.reduce (· ||| ·) {rv a})"
        | .xor => s!"pure (Zig.Vec.reduce (· ^^^ ·) {rv a})"
        | .min => s!"pure (Zig.Vec.reduce (Zig.min {sgn}) {rv a})"
        | .max => s!"pure (Zig.Vec.reduce (Zig.max {sgn}) {rv a})"
        | .add => s!"pure (Zig.Vec.reduce Zig.addWrap {rv a})"
        | .mul => s!"pure (Zig.Vec.reduce Zig.mulWrap {rv a})"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .shuffle a b mask =>
    -- The mask is comptime-known: pick each lane directly into a `Zig.Vec` literal instead of a
    -- runtime shuffle function (`ZigLean/Vec.lean`).
    let laneText (lane : ShuffleLane) : String :=
      match lane with
      | .a idx => s!"{rv a}.lanes[{idx}]!"
      | .b idx =>
        match b with
        | some bv => s!"{rv bv}.lanes[{idx}]!"
        | none => "(panic! \"air2lean: shuffle mask reads 'b' with no second source\")"
      | .undef => "default"
      | .value v => rv v
    let items := ", ".intercalate (mask.map laneText).toList
    let (env, l) := bindLet fc env inst.id s!"pure ((⟨#v[{items}]⟩ : {fc.emitTyOf inst.ty}))"
    (env, some l)
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
  | .abs a =>
    let expr := if fc.isFloat a then s!"pure (Zig.Float.abs {rv a})"
      else s!"pure (Zig.absInt {if fc.valSigned a then "true" else "false"} {rv a})"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
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
    let nullableVal (v : Val) := (fc.valTyId? v |>.map (nullablePtrTy fc.types fc.layouts) |>.getD false)
    let nullable := nullableVal a || nullableVal b
    let expr := match ptrOrder, op with
      | some e, _ => s!"{fc.callMName} ({e})"
      | none, .eq => if nullable then s!"{fc.callMName} (Zig.ptrEqAddr {rv a} {rv b})" else s!"pure ({expr})"
      | none, .ne => if nullable then s!"{fc.callMName} (do pure (!(← Zig.ptrEqAddr {rv a} {rv b})))" else s!"pure ({expr})"
      | none, _ => s!"pure ({expr})"
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
    let isPacked (t : Ty) : Bool := match t with | .struct _ "packed" _ => true | _ => false
    let isPackedU (t : Ty) : Bool := match t with | .union _ "packed" none _ => true | _ => false
    if isPackedU (fc.valTy a) then
      -- A packed union to its backing integer: the bits of its bytes.
      let expr := s!"Zig.PackedU.get ({fc.emitTyOf inst.ty}) {rv a}.bytes"
      let (env, l) := bindLet fc env inst.id expr; (env, some l)
    else if isPackedU (fc.tyOfId inst.ty) then
      -- A backing integer to a packed union (0.16.0 `union_init`: every field has its width).
      let size := (fc.layouts[inst.ty]?.bind (·.size)).getD 0
      let u := fc.emitTyOf inst.ty
      let (env, l) := bindLet fc env inst.id
        s!"pure {rawUnionInit u "packed" size (rv a) (fc.emitValTy a)}"
      (env, some l)
    else if isPacked (fc.valTy a) then
      -- A packed struct to its backing integer.
      let (env, l) := bindLet fc env inst.id s!"pure (Zig.Packed.toBits {rv a})"; (env, some l)
    else if isPacked (fc.tyOfId inst.ty) then
      let expr := s!"Zig.Packed.ofBits? (α := {fc.emitTyOf inst.ty}) {rv a}"
      let (env, l) := bindLet fc env inst.id expr; (env, some l)
    else if fc.valTy a == .bool && fc.tyOfId inst.ty != .bool then
      -- `@intFromBool` (a `bitcast` `bool` → `u1`; `std.atomic.Value.bitSet`).
      let (env, l) := bindLet fc env inst.id
        s!"pure (if {rv a} then 1 else 0 : {fc.emitTyOf inst.ty})"
      (env, some l)
    else if fc.valTy a != .bool && fc.tyOfId inst.ty == .bool then
      let (env, l) := bindLet fc env inst.id s!"pure ({rv a} == 1)"
      (env, some l)
    else
    let srcPtr := fc.isPtr a
    let dstPtr := fc.isPtrTy inst.ty
    let isInt (t : Ty) : Bool := match t with | .int .. => true | _ => false
    if srcPtr && isInt (fc.tyOfId inst.ty) then
      -- `@intFromPtr`.
      let expr := s!"{fc.callMName} (do pure (BitVec.ofInt {fc.tyBits inst.ty} (← Zig.ptrAddr {rv a})))"
      let (env, l) := bindLet fc env inst.id expr; (env, some l)
    else if isInt (fc.valTy a) && dstPtr then
      -- `@ptrFromInt`.
      let fromAddr := if nullablePtrTy fc.types fc.layouts inst.ty then "Zig.ptrFromAddrNullable" else "Zig.ptrFromAddr"
      let expr := s!"{fc.callMName} ({fromAddr} ({rv a}).toNat)"
      let (env, l) := bindLet fc env inst.id expr; (env, some l)
    else if srcPtr && dstPtr &&
        (fc.valTyId? a |>.map (nullablePtrTy fc.types fc.layouts) |>.getD false) &&
        !(nullablePtrTy fc.types fc.layouts inst.ty) then
      let (env, l) := bindLet fc env inst.id s!"{fc.callMName} (Zig.ptrRequireNonNull {rv a})"
      (env, some l)
    else
    let srcFloat := fc.isFloat a
    let dstFloat := fc.isFloatTy inst.ty
    let expr :=
      if srcFloat && !dstFloat then s!"Zig.Float.toBits? {rv a}"
      else if !srcFloat && dstFloat then s!"pure ((Zig.Float.ofBits {rv a}) : {fc.emitTyOf inst.ty})"
      else s!"pure ({rv a})"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .floatRound op a =>
    -- Only f80's legacy extension changes rounding; vector lanes carry their scalar type here.
    let legacyRt := fc.zigBefore016 && fc.floatSemantics == .compilerRt &&
      fc.tyOfId inst.ty == .float 80
    let f := match op with
      | .floor => if legacyRt then "Zig.Float.floorRtLegacyChk" else "Zig.Float.floorChk"
      | .ceil => if legacyRt then "Zig.Float.ceilRtLegacyChk" else "Zig.Float.ceilChk"
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
    let (env, l) := bindLet fc env inst.id s!"Zig.Float.conv{fc.rtSuffix}Chk {fmt} {rv a}"
    (env, some l)
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
  | .isNull a =>
    let expr := if fc.isPtr a then s!"{fc.callMName} (Zig.ptrIsNull {rv a})" else s!"pure (({rv a}).isNone)"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .isNonNull a =>
    let expr := if fc.isPtr a then s!"{fc.callMName} (do pure (!(← Zig.ptrIsNull {rv a})))" else s!"pure (({rv a}).isSome)"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .optPayload a =>
    let expr := if fc.isPtr a then s!"{fc.callMName} (Zig.ptrRequireNonNull {rv a})" else s!"Zig.optPayload {rv a}"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .wrapOptional a => let (env, l) := bindLet fc env inst.id s!"pure (some {rv a})"; (env, some l)
  | .isNullPtr isNull p =>
    -- `?*T`: the payload is the flag (null = address 0). `?T`: a flag byte after the payload.
    let some' := match fc.pointeeOf p with
      | .optional c => match fc.tyOfId c with
        | .ptr .. => s!"(·.isSome) <$> {fc.loadMem p (rv p)}"
        | .errorSet (some names) => s!"Zig.optionalErrorIsSome {emitErrorDomain names} {fc.ptrAlign p} {rv p}"
        | ct => fc.storageExpr c s!"Zig.optIsSome ({emitTy fc.structNames fc.types ct}) {rv p}"
      | _ => "(panic! \"air2lean: is_null_ptr of a non-optional\")"
    let expr := if isNull then s!"(!·) <$> {some'}" else some'
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .optPayloadPtr set p =>
    let expr := match set, fc.pointeeOf p with
      | true, .optional c =>
        match fc.tyOfId c with
        | .ptr .. | .errorSet _ => s!"pure {rv p}"
        | ct => fc.storageExpr c s!"Zig.optSetSome ({emitTy fc.structNames fc.types ct}) {rv p}"
      | _, _ => s!"pure {rv p}"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .isErrPtr _ p | .errPayloadPtr _ p | .errCodePtr p =>
    -- `Zig.errIsErrAt` & co. (`ZigLean/Mem/Enc.lean`) take the payload type.
    let payload := match fc.pointeeOf p with
      | .errorUnion _ c => emitTy fc.structNames fc.types (fc.tyOfId c)
      | _ => "(panic! \"air2lean: an error-union pointer op on another type\")"
    let a := fc.ptrAlign p
    let domain := match fc.pointeeOf p with
      | .errorUnion set _ => match fc.tyOfId set with
        | .errorSet (some names) => some (emitErrorDomain names)
        | _ => none
      | _ => none
    let isErr := match domain with
      | some d => s!"Zig.finiteErrIsErrAt {d}"
      | none => "Zig.errIsErrAt"
    let code := match domain with
      | some d => s!"Zig.finiteErrCodeAt {d}"
      | none => "Zig.errCodeAt"
    let expr := match inst.op with
      | .isErrPtr true _ => s!"{isErr} ({payload}) {a} {rv p}"
      | .isErrPtr false _ => s!"(!·) <$> {isErr} ({payload}) {a} {rv p}"
      | .errPayloadPtr true _ => s!"Zig.errSetOk ({payload}) {a} {rv p}"
      | .errPayloadPtr false _ => s!"pure (Zig.errPayloadPtr ({payload}) {rv p})"
      | _ => s!"{code} ({payload}) {a} {rv p}"
    let expr := match fc.pointeeOf p with
      | .errorUnion _ child => fc.storageExpr child expr
      | _ => expr
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
    let (env, l) := bindLet fc env inst.id s!"pure ({fc.emitValTy a}.{fc.helperName (fc.valTy a) "isNamed"} {rv a})"
    (env, some l)
  | .unionTag a =>
    let (env, l) := bindLet fc env inst.id s!"pure ({fc.emitValTy a}.{fc.helperName (fc.valTy a) "tag"} {rv a})"
    (env, some l)
  | .unionInit idx a =>
    let expr := match fc.tyOfId inst.ty, fc.unionField? (fc.tyOfId inst.ty) idx with
      | .union _ layout none fields, some (u, _, _) =>
        let t := ((fields[idx]?).map fun (_, fty) => fc.emitTyOf fty).getD "Unit"
        let expr := s!"pure {rawUnionInit u layout ((fc.layouts[inst.ty]?.bind (·.size)).getD 0) (rv a) t}"
        match fields[idx]? with
        | some (_, fty) => fc.storageExpr fty expr
        | none => expr
      | _, some (u, f, true) => s!"pure {u}.{fc.memberName (fc.tyOfId inst.ty) f}"
      | _, some (u, f, false) => s!"pure ({u}.{fc.memberName (fc.tyOfId inst.ty) f} {rv a})"
      | _, none => "(panic! \"air2lean: union_init of a non-union type\")"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .alloc =>
    if fc.escaping.contains inst.id then
      -- The pointer to the local's stack block (made at function entry: `emitFunctionDef`).
      let field := (fc.allocFields.find? (·.1 == inst.id)).map (·.2) |>.getD s!"local{inst.id}"
      let (env, l) := bindLet fc env inst.id s!"pure (← get).{field}"; (env, some l)
    else (env, none)
  | .fieldPtr base idx =>
    if fc.isMemPtr base then
      -- A bit-pointer points to the host integer: the base's own address.
      let off := if fc.hostSize inst.ty != 0 then 0 else fc.fieldOffset base idx
      let (env, l) := bindLet fc env inst.id s!"pure ({rv base}.add {off})"
      (env, some l)
    else (env, none)
  | .fieldParentPtr fieldPtr idx =>
    if fc.isMemPtr fieldPtr then
      -- A bit-pointer points to the host integer: the parent's own address.
      let bitPtr := ((fc.valTyId? fieldPtr).map fc.hostSize).getD 0 != 0
      let off := if bitPtr then 0 else fc.fieldOffsetOfPtrTy inst.ty idx
      let (env, l) := bindLet fc env inst.id s!"pure ({rv fieldPtr}.add (-({off} : Int)))"
      (env, some l)
    else (env, none)
  | .setUnionTag ptr tag =>
    -- Old AIR retains a vestigial tag write for an extern or packed union with no tag.
    if let .union _ _ none _ := fc.pointeeOf ptr then (env, none) else
    if fc.isMemPtr ptr then
      -- Write the tag; the payload bytes stay (Zig).
      match fc.pointeeOf ptr with
      | .union _ _ (some tagTy) fields =>
        let to := ((unionOffsets fc.types fc.layouts tagTy (fields.map (·.2))).map (·.1)).getD 0
        let ty := emitTy fc.structNames fc.types (fc.tyOfId tagTy)
        let align := Nat.min (fc.ptrAlign ptr) ((fc.layouts[tagTy]?.bind (·.align)).getD 1)
        (env, some s!"Zig.store (α := {ty}) {align} ({rv ptr}.add {to}) {rv tag}")
      | _ => (env, some "(panic! \"air2lean: set_union_tag of a non-union\")")
    else
    match fc.unionFieldOfTag? (fc.pointeeOf ptr) tag with
    | some (u, f, _) => (env, some (fc.modifyPlace ptr fun old => s!"({u}.{fc.helperName (fc.pointeeOf ptr) s!"setTag_{f}"} {old})"))
    | none => (env, some "(panic! \"air2lean: set_union_tag with an unknown tag\")")
  | .load ptr =>
    if fc.isMemPtr ptr then
      if !fc.isReferenced inst.id then
        -- Keep the full access/read record, but do not decode a value with no runtime use.
        -- A bit-pointer reads its complete host, rather than only the field's byte width.
        let host := ((fc.valTyId? ptr).map fc.hostSize).getD 0
        let child := ((fc.valTyId? ptr).bind (ptrChild fc.types)).getD 0
        let size := if host != 0 then host else fc.sizeOf child
        (env, some s!"Zig.loadDiscardBytes {size} {fc.ptrAlign ptr} {rv ptr}")
      else
        let (env, l) := bindLet fc env inst.id (fc.loadMem ptr (rv ptr)); (env, some l)
    else
      let (env, l) := bindLet fc env inst.id s!"pure ({fc.loadPlace ptr})"; (env, some l)
  | .store ptr v =>
    if fc.isMemPtr ptr then
      let (ty, align) := (fc.pointeeTy ptr, fc.ptrAlign ptr)
      match v with
      -- `undefined`: every byte of the value becomes undefined.
      | .undef _ => (env, some (fc.pointeeStorageExpr ptr s!"Zig.storeUndef ({ty}) {align} {rv ptr}"))
      | _ =>
        let host := ((fc.valTyId? ptr).map fc.hostSize).getD 0
        if host != 0 then
          let bitOff := ((fc.valTyId? ptr).bind (fc.layouts[·]?) |>.map (·.bitOffset)).getD 0
          (env, some s!"Zig.storeBits (α := {ty}) {host} {align} {bitOff} {rv ptr} {rv v}")
        else (env, some (fc.pointeeStorageExpr ptr s!"Zig.store (α := {ty}) {align} {rv ptr} {rv v}"))
    else (env, some (fc.storePlace ptr (rv v)))
  -- An atomic op is a sync op: the oracle picks the message or the place, and another thread can
  -- run first (`ZigLean/Conc/Call.lean`).
  | .atomicLoad ptr order =>
    let bits := fc.tyBits inst.ty
    let o := orderTerm order
    let expr := if fc.atomicTyped ptr then s!"Zig.atomicLoadAsC ({fc.pointeeTy ptr}) {o} {fc.ptrAlign ptr} {rv ptr}"
      else s!"Zig.atomicLoadC (n := {bits}) {o} {fc.ptrAlign ptr} {rv ptr}"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .atomicStore ptr v order =>
    let f := if fc.atomicTyped ptr then "Zig.atomicStoreAsC" else "Zig.atomicStoreC"
    (env, some s!"{f} {orderTerm order} {fc.ptrAlign ptr} {rv ptr} {rv v}")
  | .atomicRmw op order ptr v =>
    -- `RmwOp`'s constructors have the same names in `Air2Lean.RmwOp` (parsed AIR) and
    -- `Zig.RmwOp` (the model, `ZigLean/Mem/Thread.lean`).
    let opName := match op with
      | .xchg => "xchg" | .add => "add" | .sub => "sub" | .and => "and" | .nand => "nand"
      | .or => "or" | .xor => "xor" | .max => "max" | .min => "min"
    let opTerm := s!"Zig.RmwOp.{opName}"
    let signed := if fc.tySigned inst.ty then "true" else "false"
    let o := orderTerm order
    let expr := if fc.atomicTyped ptr then s!"Zig.atomicRmwAsC {opTerm} {o} {fc.ptrAlign ptr} {rv ptr} {rv v}"
      else s!"Zig.atomicRmwC {opTerm} {signed} {o} {fc.ptrAlign ptr} {rv ptr} {rv v}"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .cmpxchg weak ptr expected new succ fail =>
    let f := if fc.atomicTyped ptr then
        if weak then "Zig.cmpxchgWeakAsC" else "Zig.cmpxchgAsC"
      else if weak then "Zig.cmpxchgWeakC" else "Zig.cmpxchgC"
    let expr := s!"{f} {orderTerm succ} {orderTerm fail} {fc.ptrAlign ptr} {rv ptr} {rv expected} {rv new}"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .sliceLen s =>
    let expr := if fc.mem then s!"pure {rv s}.len" else s!"pure (Zig.len {rv s})"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .sliceElemVal s i =>
    -- A pure function has the items (`Array`); a function that uses memory reads them.
    let expr := if fc.mem then s!"{fc.callMName} ({fc.loadItem s s!"{rv s}.ptr" (rv i)})"
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
    let (env, l) := bindLet fc env inst.id s!"{fc.callMName} ({fc.loadItem p (rv p) (rv i)})"
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
    (env, some s!"{fc.callMName} ({fc.storageExpr (fc.itemTyId dst) s!"Zig.memset (α := {item}) {fc.ptrAlign dst} {ptr} {n} {v'}"})")
  | .memcpy dst src =>
    -- The item count of the operand that has one (the AIR checks that both agree).
    let hasLen (v : Val) : Bool :=
      fc.isSlice v || match fc.pointeeOf v with | .array .. => true | _ => false
    let (dptr, n) := fc.itemsOf dst (rv dst)
    let n := if hasLen dst then n else (fc.itemsOf src (rv src)).2
    let sptr := if fc.isSlice src then s!"{rv src}.ptr" else rv src
    let size := fc.sizeOf (fc.itemTyId dst)
    (env, some s!"{fc.callMName} (Zig.memmove {size} {fc.ptrAlign dst} {fc.ptrAlign src} {dptr} {sptr} {n})")
  | .tagName a =>
    let (env, l) := bindLet fc env inst.id (fc.liftR s!"{fc.emitValTy a}.{fc.helperName (fc.valTy a) "tagName"} {rv a}")
    (env, some l)
  | .errorName a =>
    let (env, l) := bindLet fc env inst.id (fc.liftR s!"errorNameOf {rv a}"); (env, some l)
  | .structFieldVal s index =>
    match fc.unionField? (fc.valTy s) index with
    | some (u, f, _) =>
      let (env, l) := bindLet fc env inst.id (fc.liftR s!"{u}.{fc.helperName (fc.valTy s) s!"get_{f}"} {rv s}"); (env, some l)
    | none =>
      let fname := fc.structFieldName s index
      let (env, l) := bindLet fc env inst.id s!"pure (({rv s}){fname})"; (env, some l)
  | .aggregateInit elems =>
    match fc.tyOfId inst.ty with
    | .array .. =>
      let items := ", ".intercalate (elems.map rv).toList
      let (env, l) := bindLet fc env inst.id s!"pure (#v[{items}] : {fc.emitTyOf inst.ty})"
      (env, some l)
    | .tuple _ =>
      -- `Thread.spawn`'s `args` tuple (`docs/std-models.md` §Thread model) is the only source of
      -- a tuple-typed `aggregate_init` in the subset: positional, no field names.
      let items := ", ".intercalate (elems.map rv).toList
      let term := if elems.isEmpty then "()" else s!"({items})"
      let (env, l) := bindLet fc env inst.id s!"pure {term}"
      (env, some l)
    | .vector .. =>
      let items := ", ".intercalate (elems.map rv).toList
      let (env, l) := bindLet fc env inst.id s!"pure ((⟨#v[{items}]⟩ : {fc.emitTyOf inst.ty}))"
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
    let allocFn := match callee with | .func name .. => allocFn? name | _ => none
    let threadFn := match callee with | .func name .. => threadFn? name | _ => none
    if let some fn := allocFn then
      let (env, l) := bindLet fc env inst.id s!"{fc.callMName} ({fc.allocCall env fn args inst.ty})"
      (env, some l)
    else if let some fn := threadFn then
      let (env, l) := bindLet fc env inst.id (fc.threadCall env fn callee args)
      (env, some l)
    else if isNoreturn then (env, none)
    else if let .inst p := callee then
      -- An indirect call: the function whose block the pointer points to, at offset 0 (M20).
      let tn := match fc.tyOfId ((fc.valTyId? callee).getD 0) with
        | .ptr _ _ c => match fc.tyOfId c with | .other n => n | _ => ""
        | _ => ""
      let arms := (fc.fnBlocks.filter (·.1 == tn)).toList.map fun (_, nm, b) =>
        let lean := (fc.funcNames.find? (·.1 == nm)).map (·.2) |>.getD nm
        let memCallee := fc.memFuncs.contains nm
        let term := s!"{lean} {String.intercalate " " (args.map (fc.callArg env memCallee)).toList}"
        let call := fc.callOf nm term memCallee
        s!"if {rv (.inst p)} == (⟨some {b}, 0⟩ : Zig.Ptr) then {call} else "
      let (env, l) := bindLet fc env inst.id s!"({String.join arms}throw .illegal)"
      (env, some l)
    else
      let memCallee := match callee with | .func name .. => fc.memFuncs.contains name | _ => false
      let term := s!"{cexpr} {String.intercalate " " (args.map (fc.callArg env memCallee)).toList}"
      let expr := match callee with
        | .func name .. => fc.callOf name term memCallee
        | _ => fc.liftR term
      let (env, l) := bindLet fc env inst.id expr
      (env, some l)
  | .line _ => (env, none)
  | .dbg _ _ => (env, none)
  | .asm source _ _ outputs inputs =>
    if inst.op.isSpinHint then
      let (env, l) := bindLet fc env inst.id "Zig.spinLoopHintC"
      (env, some l)
    else
    -- Same identity as `collectAsmOps` (`asmKey`): this must name the very `opaque` def that
    -- pass emitted, or the call below resolves to nothing.
    let inputWidths := inputs.map fun i => match fc.valTy i.ref.get! with | .int _ b => b | _ => 0
    let outputWidths := asmOutputWidths fc.types fc.valTyId? inst.ty outputs
    let constraints := outputs.map (·.constraint) ++ inputs.map (·.constraint)
    let name := asmDefName (asmKey source constraints inputWidths outputWidths)
    let args := inputs.toList.map fun i => rv i.ref.get!
    let call := if args.isEmpty then name else s!"{name} {String.intercalate " " args}"
    if outputs.size ≤ 1 && outputs.all (·.ref.isNone) then
      let (env, l) := bindLet fc env inst.id s!"pure ({call})"
      (env, some l)
    else
      -- The tuple of the outputs; output `k` of `n` is `.2.….2.1` (`k` times `.2`), the last one
      -- without the `.1`. The result output binds the instruction; each lvalue output is a
      -- store through its pointer, as `store`.
      let t := s!"a{inst.id}"
      let n := outputs.size
      let proj (k : Nat) : String :=
        t ++ tupleProjection n k
      let (env, lines) := outputs.toList.zipIdx.foldl (init := (env, [s!"let {t} := {call}"]))
        fun (env, ls) (o, k) => match o.ref with
          | none =>
            let (env, l) := bindLet fc env inst.id s!"pure {proj k}"
            (env, ls ++ [l])
          | some ptr =>
            if fc.isMemPtr ptr then
              (env, ls ++ [s!"Zig.store (α := {fc.pointeeTy ptr}) {fc.ptrAlign ptr} {rv ptr} {proj k}"])
            else (env, ls ++ [fc.storePlace ptr (proj k)])
      (env, some ("\n".intercalate lines))
  | _ => (env, some s!"-- air2lean: unexpected op in straight-line position (inst {inst.id})")


/-- A lane-wise op on vectors: its operands, and the same op with other operands. `arith`,
`splat`, `select`, `reduce` and `shuffle` have their own vector cases in `emitScalar`. -/
def laneOp? : Op → Option (Array Val × (Array Val → Op))
  | .div o a b => some (#[a, b], fun v => .div o v[0]! v[1]!)
  | .divFloat a b => some (#[a, b], fun v => .divFloat v[0]! v[1]!)
  | .minMax m a b => some (#[a, b], fun v => .minMax m v[0]! v[1]!)
  | .withOverflow o a b => some (#[a, b], fun v => .withOverflow o v[0]! v[1]!)
  | .shlWithOverflow a b => some (#[a, b], fun v => .shlWithOverflow v[0]! v[1]!)
  | .countBits o a => some (#[a], fun v => .countBits o v[0]!)
  | .permuteBits o a => some (#[a], fun v => .permuteBits o v[0]!)
  | .bit o a b => some (#[a, b], fun v => .bit o v[0]! v[1]!)
  | .not a => some (#[a], fun v => .not v[0]!)
  | .neg a => some (#[a], fun v => .neg v[0]!)
  | .abs a => some (#[a], fun v => .abs v[0]!)
  | .shift o a b => some (#[a, b], fun v => .shift o v[0]! v[1]!)
  | .cmp o a b => some (#[a, b], fun v => .cmp o v[0]! v[1]!)
  | .boolAnd a b => some (#[a, b], fun v => .boolAnd v[0]! v[1]!)
  | .boolOr a b => some (#[a, b], fun v => .boolOr v[0]! v[1]!)
  | .intCast a => some (#[a], fun v => .intCast v[0]!)
  | .trunc a => some (#[a], fun v => .trunc v[0]!)
  | .floatRound o a => some (#[a], fun v => .floatRound o v[0]!)
  | .sqrt a => some (#[a], fun v => .sqrt v[0]!)
  | .libm o a => some (#[a], fun v => .libm o v[0]!)
  | .mulAdd a b c => some (#[a, b, c], fun v => .mulAdd v[0]! v[1]! v[2]!)
  | .floatConv a => some (#[a], fun v => .floatConv v[0]!)
  | .floatFromInt a => some (#[a], fun v => .floatFromInt v[0]!)
  | .intFromFloat safe a => some (#[a], fun v => .intFromFloat safe v[0]!)
  | _ => none

/-- A lane-wise op on vectors (`laneOp?`): the scalar op's expression (`emitScalar`) on lane
variables `x0`, `x1`, `x2`, in `Zig.Vec.mapM`/`map2M`/`map3M`. So each lane has the scalar
semantics, and the first lane that throws gives the error. `@addWithOverflow` gives a vector of
pairs: `Zig.Vec.unzip` makes the tuple of two vectors. `none` if `inst` is not such an op. -/
def emitLaneWise (fc : FCtx) (env : Array (InstId × String)) (inst : Inst) :
    Option (Array (InstId × String) × Option String) := do
  let (vals, rebuild) ← laneOp? inst.op
  let laneTy (t : TyId) : Option TyId := match fc.tyOfId t with | .vector _ c => some c | _ => none
  -- The result's lane type: a vector's child, or the tuple of the lane types (`withOverflow`).
  let (resTy, tupleTys) ← match fc.tyOfId inst.ty with
    | .vector _ c => some (c, none)
    | .tuple fs => do
      let cs ← fs.mapM laneTy
      some (0, some cs)
    | _ => none
  -- One fake instruction per operand: its lane type, bound to `x<k>`.
  let base := (fc.allInsts.foldl (fun m i => max m i.id) 0) + 1
  let mut fakes : Array Inst := #[]
  for k in [0:vals.size] do
    let t ← (fc.valTyId? vals[k]!).bind laneTy
    fakes := fakes.push { id := base + k, ty := t, op := .arg 0 }
  let fc' := { fc with allInsts := fc.allInsts ++ fakes }
  let env' := env ++ fakes.mapIdx fun k f => (f.id, s!"x{k}")
  -- `withOverflow`'s scalar result is the pair tuple; its type is only for the scalar emitter's
  -- signedness and width lookups, which read the operands.
  let scalarTy := match tupleTys with | some cs => cs[0]! | none => resTy
  let scalar : Inst := { id := inst.id, ty := scalarTy, op := rebuild (fakes.map (.inst ·.id)) }
  let (_, line?) := emitScalar fc' env' scalar
  let line ← line?
  let expr := (line.splitOn " ← ").drop 1 |> " ← ".intercalate
  let params := String.intercalate " " ((List.range vals.size).map (s!"x{·}"))
  let args := String.intercalate " " (vals.toList.map (fc.resolveVal env))
  let fn := match vals.size with | 1 => "Zig.Vec.mapM" | 2 => "Zig.Vec.map2M" | _ => "Zig.Vec.map3M"
  let lifted := s!"{fn} (fun {params} => {expr}) {args}"
  let lifted := if tupleTys.isSome then s!"(Zig.Vec.unzip <$> {lifted})" else lifted
  some (bindLet fc env inst.id lifted |> fun (e, l) => (e, some l))

/-- A straight-line (non-terminator, non-`block`/`loop`) instruction: at most one output line. -/
def emitSimple (fc : FCtx) (env : Array (InstId × String)) (inst : Inst) :
    Array (InstId × String) × Option String :=
  (emitLaneWise fc env inst).getD (emitScalar fc env inst)

mutual

/-- Translate an instruction sequence into a `Zig.M _ Exit` do-block body (as source text,
without the surrounding `do`). The last effective instruction (per `isTerminating`) becomes the
tail expression; anything the exporter placed after it (a defensive `unreach`) is dead and
dropped. -/
partial def emitStmts (fc : FCtx) (env : Array (InstId × String)) (insts : List Inst) : String :=
  let fc := fc.prepareInstUses.prepareBranchTargets
  match insts with
  | [] => "pure default"
  | inst :: rest =>
    if isTerminating inst.op then
      emitTerminator fc env inst
    else
      match inst.op with
      | .block body =>
        let inner := fc.ascribedDo (emitStmts fc env body.toList)
        -- Only discard a block's continuation when no branch targets it and either
        -- AIR declares it noreturn or every reachable body path exits outward.
        if !(fc.branchTargetSet.getD {}).contains inst.id &&
            (fc.targetTy inst.id == .noreturn || fc.outwardBlocks[inst.id]?.getD false) then
          inner
        else if !(fc.branchTargetSet.getD {}).contains inst.id then
          -- A nested loop can exit outward without a summary certificate. With no
          -- own-target branch there is no `br<id>` constructor or continuation to consume.
          inner
        else
          match fc.targetTy inst.id with
          | .void =>
            let restStr := emitStmts fc env rest
            s!"match ← {inner} with\n| .br{inst.id} => {doBlock restStr}\n| e => pure e"
          | _ =>
            -- `_v<id>` if nothing reads the block's result (Lean's unused-variable linter).
            let vname := if fc.isReferenced inst.id then s!"v{inst.id}" else s!"_v{inst.id}"
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
        -- The caller's name of each value: a `try` or `block` result is `v<id>` here.
        let args := String.intercalate " " ((caps.map fun (id, _, _) => fc.resolveVal env (.inst id)).toList)
        s!"Zig.loop ({fc.fnName}.loop{inst.id} {args}) {fc.fnName}.again{inst.id}"
      | .loopSwitchBr initial _ _ =>
        let caps := fc.loopCaptures (dispatchCaptureBody inst)
        let args := String.intercalate " " ((caps.map fun (id, _, _) => fc.resolveVal env (.inst id)).toList)
        s!"modify fun s => \{ s with {dispatchFieldName inst.id} := {fc.resolveVal env initial} }\nZig.loop ({fc.fnName}.loop{inst.id} {args}) {fc.fnName}.again{inst.id}"
      | .«try» v errBody =>
        let errStr := emitStmts fc env errBody.toList
        -- `try` on `!void`: nothing reads the payload.
        let vname := if fc.isReferenced inst.id then s!"v{inst.id}" else s!"_v{inst.id}"
        let restStr := emitStmts fc (env.push (inst.id, vname)) rest
        s!"match {fc.resolveVal env v} with\n\
          | .error _ => {doBlock errStr}\n\
          | .ok {vname} => {doBlock restStr}"
      | .tryPtr p errBody =>
        let payload := match fc.pointeeOf p with
          | .errorUnion _ c => emitTy fc.structNames fc.types (fc.tyOfId c)
          | _ => "(panic! \"air2lean: try_ptr of a non-error-union pointer\")"
        let errStr := emitStmts fc env errBody.toList
        let vname := if fc.isReferenced inst.id then s!"v{inst.id}" else s!"_v{inst.id}"
        let restStr := emitStmts fc (env.push (inst.id, vname)) rest
        let tryFn := match fc.pointeeOf p with
          | .errorUnion set _ => match fc.tyOfId set with
            | .errorSet (some names) => s!"Zig.finiteTryPayloadPtr {emitErrorDomain names}"
            | _ => "Zig.tryPayloadPtr"
          | _ => "Zig.tryPayloadPtr"
        let expr := s!"{tryFn} ({payload}) {fc.ptrAlign p} {fc.resolveVal env p}"
        let expr := match fc.pointeeOf p with
          | .errorUnion _ child => fc.storageExpr child expr
          | _ => expr
        s!"match ← {expr} with\n\
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
  | .switchDispatch target v => s!"pure (.dispatch{target} {rv v})"
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
  | .switchBr v cases elseBody => emitSwitch fc env v (rv v) cases elseBody
  | .call callee _ =>
    let (_, calleeName) := fc.resolveCallee callee
    match panicErrorFor? calleeName with
    | some ctor => s!"throw {ctor}"
    | none => s!"(panic! \"air2lean: unchecked noreturn callee {calleeName}\")"
  | _ => "pure default"

/-- Shared case selection, with loop-switch state supplied independently of SSA captures. -/
partial def emitSwitch (fc : FCtx) (env : Array (InstId × String)) (v : Val)
    (selector : String) (cases : Array SwitchCase) (elseBody : Array Inst) : String :=
  match fc.valTy v with
  | .enum _ _ true fields =>
    -- Every name has a case: a `match` with one arm per case, no `else` arm (it is the
    -- `corruptSwitch` panic, which a valid enum value never reaches).
    let fm := fc.memberLookup (fc.valTy v)
    let caseNames := cases.map fun c => c.items.filterMap fun it => match it with
      | .enumTag _ tv => (fields.find? (·.2 == tv)).map (fm ·.1)
      | _ => none
    let covered := caseNames.flatten
    if cases.all (·.ranges.isEmpty) && fields.all (fun (f, _) => covered.contains (fm f)) &&
        (cases.zip caseNames).all (fun (c, ns) => c.items.size == ns.size) then
      let arms := (cases.zip caseNames).toList.map fun (c, ns) =>
        let pats := String.intercalate " | " (ns.toList.map (s!".{·}"))
        s!"| {pats} => {doBlock (emitStmts fc env c.body.toList)}"
      s!"match {selector} with\n{String.intercalate "\n" arms}"
    else emitSwitchChain fc env v selector cases.toList elseBody
  | _ => emitSwitchChain fc env v selector cases.toList elseBody

/-- `switch_br` as a chain of `if`/`else if` (a `BitVec` value has no numeral match pattern). -/
partial def emitSwitchChain (fc : FCtx) (env : Array (InstId × String)) (v : Val)
    (selector : String) (cases : List SwitchCase) (elseBody : Array Inst) : String :=
  match cases with
  | [] => emitStmts fc env elseBody.toList
  | c :: rest =>
    let sgn := if fc.valSigned v then "true" else "false"
    let rv := fc.resolveVal env
    let itemConds := (c.items.map fun it => s!"{selector} == {rv it}").toList
    let rangeConds := (c.ranges.map fun (lo, hi) =>
      s!"(Zig.le {sgn} {rv lo} {selector} && Zig.le {sgn} {selector} {rv hi})").toList
    let cond := String.intercalate " || " (itemConds ++ rangeConds)
    s!"if {cond} then {doBlock (emitStmts fc env c.body.toList)}\nelse \
      {doBlock (emitSwitchChain fc env v selector rest elseBody)}"

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
  | .loopSwitchBr initial cases elseBody =>
    let caps := fc.loopCaptures (dispatchCaptureBody loopInst)
    let paramsStr := String.intercalate " "
      ((caps.map fun (_, name, ty) => s!"({name} : {ty})").toList)
    let initEnv := caps.map fun (id, name, _) => (id, name)
    let branch := fc.ascribedDo (emitSwitch fc initEnv initial "dispatchValue" cases elseBody)
    String.intercalate "\n"
      [s!"def {fc.fnName}.loop{loopInst.id} {paramsStr} : {fc.monad} {fc.localsName} {fc.exitName} := do",
       s!"  let dispatchValue := (← get).{dispatchFieldName loopInst.id}",
       s!"  let dispatchExit ← {indentTail 2 branch}",
       "  match dispatchExit with",
       s!"  | .dispatch{loopInst.id} dispatchValue => do",
       s!"    modify fun s => \{ s with {dispatchFieldName loopInst.id} := dispatchValue }",
       "    pure dispatchExit",
       "  | _ => pure dispatchExit"]
  | _ => "" -- unreachable: only loops and loop-switches have extracted bodies

-- `again` is named too: an inline `fun e => match …` gets a fresh matcher per elaboration,
-- so a proof could not restate it and `rw` with a `Zig.loop_spec` result would not match.
def emitAgainDef (fc : FCtx) (loopInst : Inst) : String :=
  let ownExit := match loopInst.op with
    | .loopSwitchBr .. => [s!"  | .dispatch{loopInst.id} _ => true"]
    | _ => if fc.repT.contains loopInst.id then
        [s!"  | .rep{loopInst.id} => true"] else []
  -- An ordinary loop can exit through an outer dispatch without ever repeating itself.
  -- Its own repeat constructor then does not exist, and every actual exit stops it.
  String.intercalate "\n"
    ([s!"def {fc.fnName}.again{loopInst.id} : {fc.exitName} → Bool"] ++ ownExit ++
     ["  | _ => false"])

/-! ## Per-function emission -/

/-- An escaping `alloc`'s stack block: `(allocId, field, size, align)`. -/
def FCtx.stackBlocks (fc : FCtx) : Array (InstId × String × Nat × Nat) :=
  fc.escaping.map fun aid =>
    let field := (fc.allocFields.find? (·.1 == aid)).map (·.2) |>.getD s!"local{aid}"
    let child := match fc.tyOfId (fc.instTyId aid) with | .ptr _ _ c => c | _ => 0
    let l := fc.layouts[child]?.getD {}
    (aid, field, l.size.getD 0, l.align.getD 1)

/-- Shared body text for a definition and its opt-in unfolding theorem. -/
def emitFunctionBody (fc : FCtx) (localsName exitName : String)
    (retTy : TyId) (body : Array Inst) (hasNonRetExit : Bool) : String :=
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
  String.intercalate "\n"
    (["do"] ++ allocLines ++
     [s!"  let e ← {indentTail 2 ascribedBody}.run' {init}"] ++ freeLines ++
     ["  match e with"] ++ matchLines)

def emitFunctionHeader (fc : FCtx) (leanName : String) (paramTys : Array TyId)
    (retTy : TyId) : String :=
  let paramsStr := String.intercalate " "
    ((paramTys.mapIdx fun i pt => s!"(p{i} : {fc.emitTyOf pt})").toList)
  let retStr := fc.emitTyOf retTy
  let resultTy := if fc.conc then "Zig.ConcM Tgt" else if fc.mem then "Zig.MemM" else "Zig.Result"
  s!"def {leanName} {paramsStr} : {resultTy} ({retStr}) := "

def emitFunctionDef (fc : FCtx) (leanName localsName exitName : String) (paramTys : Array TyId)
    (retTy : TyId) (body : Array Inst) (hasNonRetExit : Bool) : String :=
  emitFunctionHeader fc leanName paramTys retTy ++
    emitFunctionBody fc localsName exitName retTy body hasNonRetExit

/-- One function's output in four parts: the `Locals`/`Exit` types, the `again<k>` defs, the
`loop<k>` defs (inner loop first), and the function def. `emit` joins them, and puts a
recursive group's loop and function defs into one `mutual` block. -/
structure FuncParts where
  types : List String
  agains : List String
  loops : List String
  defn : String
  body : String

/-- The static context without block-emission membership, for global encoding. -/
private def mkFCtxUnprepared (f : Func) (structNames : Array (String × String)) (funcNames : Array (String × String))
    (floatSemantics : FloatSemantics) (memFuncs : Array String) (globalIds : Array Nat)
    (concFuncs : Array String := #[]) : FCtx :=
  let allInsts := f.allInsts
  let leanName := (funcNames.find? (·.1 == f.name)).map (·.2) |>.getD f.name
  -- `«at»` (a keyword) gives `atLocals`.
  let plain := plainName leanName
  let allocs := collectAllocs f.types allInsts (structNames.map (·.2))
  let fc : FCtx :=
    { types := f.types, structNames, funcNames,
      allocFields := allocs.map fun (i, n, _) => (i, n), blockTys := blockLoopTys allInsts,
      allInsts, brT := brTargets allInsts, repT := repTargets allInsts,
      retTy := f.ret, fnName := leanName, localsName := mangleField s!"{plain}Locals",
      exitName := mangleField s!"{plain}Exit", floatSemantics, zigVersion := f.zigVersion, places := #[],
      mem := memFuncs.contains f.name, memFuncs, layouts := f.layouts,
      conc := concFuncs.contains f.name, concFuncs,
      escaping := escapingAllocs f, globalIds }
  { fc with places := fc.computePlaces }

/-- The static context of `f`, prepared for block emission. `globalIds`: the block of
 each global of `f.globals`. Bare contexts are also prepared by `emitStmts`. -/
def mkFCtx (f : Func) (structNames : Array (String × String)) (funcNames : Array (String × String))
    (floatSemantics : FloatSemantics) (memFuncs : Array String) (globalIds : Array Nat)
    (concFuncs : Array String := #[]) : FCtx :=
  let fc := mkFCtxUnprepared f structNames funcNames floatSemantics memFuncs globalIds concFuncs
  { fc with outwardBlocks := (controlFlowSummaries f.body).outwardBlocks
  }.prepareInstUses.prepareBranchTargets

private def emitOneFunctionWithFallbackMap (f : Func)
    (spawnFallbackMap : Std.HashMap String String) (structNames : Array (String × String))
    (funcNames : Array (String × String)) (floatSemantics : FloatSemantics)
    (memFuncs : Array String) (globalIds : Array Nat) (fnBlocks : Array (String × String × Nat))
    (concFuncs : Array String := #[]) (spawnSemantics : SpawnSemantics := .available)
    (spawnFallbacks : Array (String × String) := #[]) : FuncParts :=
  let fc := mkFCtxUnprepared f structNames funcNames floatSemantics memFuncs globalIds concFuncs
  let fc := { fc with fnBlocks := fnBlocks, spawnSemantics := spawnSemantics, spawnFallbacks := spawnFallbacks, spawnFallbackMap := some spawnFallbackMap }.prepareInstUses
  let allInsts := fc.allInsts
  let leanName := fc.fnName
  let allocs := collectAllocs f.types allInsts (structNames.map (·.2))
  let blTys := fc.blockTys
  let brT := fc.brT
  -- Reuse the ordered constructor inventory for block-emission membership.
  let empty : Std.HashSet InstId := {}
  let fc := { fc with branchTargetSet := some (brT.foldl (fun targets id => targets.insert id) empty) }
  let repT := fc.repT
  let localsName := fc.localsName
  let exitName := fc.exitName
  let escaping := fc.escaping
  let localsStr := emitLocalsStruct structNames f.types localsName allocs escaping fc.mem fc.dispatchTys
  let exitStr := emitExitInductive structNames f.types exitName f.ret blTys brT repT fc.mem fc.dispatchTys
  -- Every `loop` in the function, innermost first: `flattenInst`/`Func.allInsts` visits a node
  -- before its children (pre-order), so a parent loop always precedes a nested one; reversing
  -- flips that to child-before-parent, which is what "the inner loop's def is emitted before
  -- the outer one" needs (`docs/generated-code.md` §Loops).
  let loops := (allInsts.filter fun i => match i.op with | .loop _ | .loopSwitchBr .. => true | _ => false).reverse
  let hasNonRetExit := !brT.isEmpty || !repT.isEmpty || !fc.dispatchTys.isEmpty
  let functionBody := emitFunctionBody fc localsName exitName f.ret f.body hasNonRetExit
  { types := [localsStr, exitStr]
    agains := (loops.map (emitAgainDef fc)).toList
    loops := (loops.map (emitLoopDef fc)).toList
    defn := emitFunctionHeader fc leanName f.params f.ret ++ functionBody
    body := functionBody }

/-- Optional stable scalar unfolding boundary. The equality exposes the actual emitted
body and is kernel checked with `rfl`; no replacement model or axiom is introduced. -/
def emitProofApi (f : Func) (mkFc : Unit → FCtx) (rhs : String) : Option String :=
  match proofApiFacts f with
  | none => none
  | some facts =>
    let fc := mkFc ()
    let base := proofApiName f.name
    let params := String.intercalate " " ((f.params.mapIdx fun i ty =>
      s!"(p{i} : {fc.emitTyOf ty})").toList)
    let arguments := String.intercalate " " ((Array.range f.params.size).map (fun i => s!"p{i}")).toList
    let record := Lean.Json.mkObj [("format", .str "air2lean-proof-api-v1"),
      ("source", .str f.name), ("definition", .str fc.fnName),
      ("model", .str (base ++ "_model")), ("unfold", .str (base ++ "_unfold")),
      ("facts", facts), ("source_map", proofApiSourceMap f)]
    some ("-- air2lean-proof-api: " ++ record.compress ++ "\n" ++
      s!"abbrev {base}_model := {fc.fnName}\n\n" ++
      s!"theorem {base}_unfold {params} : {base}_model {arguments} = ({rhs}) := rfl")

/-- Standalone function emission prepares its own first-match fallback lookup. Program
emission shares one prepared map across all functions. -/
def emitOneFunction (f : Func) (structNames : Array (String × String))
    (funcNames : Array (String × String)) (floatSemantics : FloatSemantics)
    (memFuncs : Array String) (globalIds : Array Nat) (fnBlocks : Array (String × String × Nat))
    (concFuncs : Array String := #[]) (spawnSemantics : SpawnSemantics := .available)
    (spawnFallbacks : Array (String × String) := #[]) : FuncParts :=
  emitOneFunctionWithFallbackMap f (prepareSpawnFallbackMap spawnFallbacks) structNames funcNames
    floatSemantics memFuncs globalIds fnBlocks concFuncs spawnSemantics spawnFallbacks

/-! ## Globals (`docs/generated-code.md` §Globals) -/

/-- One block of the memory at program start (`mem0`). -/
structure ProgGlobal where
  /-- What the block holds: a global's Zig name, `a constant`, or a tag name. -/
  label : String
  /-- The initial bytes, a term of type `Array Zig.Byte`. -/
  bytes : String
  align : Nat
  /-- A `var`: a writable block. Anything else is read-only (`Zig.BlockKind.constGlobal`). -/
  isVar : Bool := false

/-- The bytes of `term : ty`. -/
def encodeTerm (term ty : String) : String := s!"Zig.Enc.encode ({term} : {ty})"

/-- The initial bytes of global `g` of `fc`'s function. `undefined` is undefined bytes. -/
def FCtx.globalBytes (fc : FCtx) (g : Global) : String :=
  let ty := emitTy fc.structNames fc.types (fc.tyOfId g.ty)
  match g.init with
  -- A function: one byte, so that its pointer has a block (an indirect call, M20).
  | some (.func ..) => "#[.undef]"
  | some (.undef _) | none => fc.storageExpr g.ty s!"Array.replicate (Zig.Enc.size ({ty})) .undef"
  | some init => fc.storageExpr g.ty (encodeTerm (fc.resolveVal #[] init) ty)

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
  let mut unnamed : Array (String × Nat) := #[]
  for (f, k) in funcs.zipIdx do
    for j in (List.range f.globals.size).reverse do
      let g := f.globals[j]!
      if g.name.isNone then
        let bytes := (mkFc f ids[k]!.2).globalBytes g
        let id := match unnamed.findIdx? (·.1 == bytes) with
          | some u => named.size + u
          | none => named.size + unnamed.size
        if id == named.size + unnamed.size then
          unnamed := unnamed.push (bytes, (f.layouts[g.ty]?.bind (·.align)).getD 1)
        ids := ids.set! k (f.name, ids[k]!.2.set! j id)
  let mut out : Array ProgGlobal := #[]
  for n in named do
    let some (f, k) := funcs.zipIdx.find? fun (f, _) => f.globals.any (·.name == some n)
      | continue
    let some g := f.globals.find? (·.name == some n) | continue
    out := out.push { label := n, bytes := (mkFc f ids[k]!.2).globalBytes g,
                      align := (f.layouts[g.ty]?.bind (·.align)).getD 1, isVar := !g.isConst }
  for (bytes, align) in unnamed do
    out := out.push { label := "a constant", bytes, align }
  return (out, ids)

/-- The enums whose tag names a function reads (`@tagName`), as `(Zig name, Lean name, fields,
exhaustive, tag bits)`. -/
def tagNameEnums (funcs : Array Func) (structNames : Array (String × String)) :
    Array (String × String × Array (String × Int) × Bool × Nat) := Id.run do
  let mut out := #[]
  for f in funcs do
    let insts := f.allInsts
    for i in insts do
      if let .tagName a := i.op then
        let tid : Option TyId := match a with
          | .inst id => (insts.find? (fun (j : Inst) => j.id == id)).map Inst.ty
          | v => v.constTy?
        if let some (.enum name tag exhaustive fields) := tid.bind (f.types[·]?) then
          if !out.any (·.1 == name) then
            let lean := (structNames.find? (·.1 == name)).map (·.2) |>.getD name
            let bits := match f.types[tag]? with | some (.int _ b) => b | _ => 0
            out := out.push (name, lean, fields, exhaustive, bits)
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

/-- The bytes of the name `s` with a 0 sentinel. -/
def nameBytes (s : String) : String :=
  let bs := s.toUTF8.toList.map (s!"{·}")
  encodeTerm s!"#v[{", ".intercalate (bs ++ ["0"])}]" s!"Vector (BitVec 8) {bs.length + 1}"

/-- `mem0`: the memory at program start, one block per global. -/
def emitMem0 (gs : Array ProgGlobal) : String :=
  let lines := gs.toList.zipIdx.map fun (g, k) =>
    s!"  -- {k}: {g.label}\n  ({g.bytes}, {g.align}, {if g.isVar then ".global" else ".constGlobal"})"
  let body := if lines.isEmpty then "[]" else s!"[\n{",\n".intercalate lines}]"
  s!"/-- The memory at program start: block `k` is global `k`. -/\n\
    def mem0 : Zig.Mem := Zig.Mem.ofGlobals {body}"

/-- `<E>.tagName`: the name of each tag of `E` (`@tagName`), in the blocks from `first` on. -/
def emitTagName (lean : String) (fields : Array (String × Int)) (exhaustive : Bool) (bits : Nat)
    (first : Nat) (reserved : Array String := #[]) : String :=
  let ty := Ty.enum "" 0 exhaustive fields
  let fm := memberLookup ty reserved
  let hn := helperLookup ty reserved
  let slice (k : Nat) (f : String) := s!"⟨⟨some {first + k}, 0⟩, {f.toUTF8.size}⟩"
  let head := s!"def {lean}.{hn "tagName"} (e : {lean}) : Zig.Result Zig.Slice :="
  if exhaustive then
    let arms := fields.toList.zipIdx.map fun ((f, _), k) => s!"  | .{fm f} => pure {slice k f}"
    String.intercalate "\n" ([head, "  match e with"] ++ arms)
  else
    -- A value without a name has no tag name: the AIR checks `is_named_enum_value` before.
    let arms := fields.toList.zipIdx.map fun ((f, v), k) =>
      s!"  if e.{hn "toBits"} == {tagLit bits v} then pure {slice k f} else"
    String.intercalate "\n" ([head] ++ arms ++ ["  throw .panic"])

/-! ## Call graph / emission order -/

def dedupNames (a : Array String) : Array String :=
  a.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

def calleesOf (allNames : Array String) (refs : Array (String × String)) (f : Func) :
    Array String :=
  let direct := f.allInsts.filterMap fun i => match i.op with
    -- `spawnFn`: the function `Thread.spawn` runs, not `Thread.spawn` itself (which has no AIR
    -- and is not in `allNames`) — a spawned function must still be emitted before its spawner.
    | .call (.func nm _ (some spawnFn)) _ =>
      if allNames.contains spawnFn then some spawnFn
      else if allNames.contains nm then some nm else none
    | .call (.func nm ..) _ => if allNames.contains nm then some nm else none
    | _ => none
  dedupNames (direct ++ (f.indirectCallees refs).filter allNames.contains)

/-- DFS post-order over the call graph: a callee before its caller, except inside a cycle. -/
partial def topoVisit (funcs : Array Func) (allNames : Array String) (refs : Array (String × String))
    (vo : Array String × Array Func) (name : String) : Array String × Array Func :=
  let (visited, order) := vo
  if visited.contains name then (visited, order)
  else
    let visited := visited.push name
    match funcs.find? (·.name == name) with
    | none => (visited, order)
    | some f =>
      let callees := calleesOf allNames refs f
      let (visited, order) := callees.foldl (topoVisit funcs allNames refs) (visited, order)
      (visited, order.push f)

def topoOrder (funcs : Array Func) : Array Func :=
  let allNames := funcs.map (·.name)
  (allNames.foldl (topoVisit funcs allNames (fnRefs funcs)) (#[], #[])).2

/-- Every function name reachable from `name` by one or more calls. -/
partial def reachable (funcs : Array Func) (allNames : Array String) (refs : Array (String × String))
    (name : String) : Array String :=
  let rec go (seen : Array String) (todo : List String) : Array String :=
    match todo with
    | [] => seen
    | n :: rest =>
      let next := match funcs.find? (·.name == n) with
        | some f => (calleesOf allNames refs f).toList.filter (!seen.contains ·)
        | none => []
      go (seen ++ next.toArray) (rest ++ next)
  go #[] [name]

/-- The call-graph groups in emission order: a group is a set of functions that call each other
(a strongly connected component), and it comes after every group that it calls. The second
component is `true` if the group is recursive (more than one function, or a self-call). -/
def callGroups (funcs : Array Func) : Array (Array Func × Bool) :=
  let allNames := funcs.map (·.name)
  let reach := allNames.map fun n => (n, reachable funcs allNames (fnRefs funcs) n)
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

/-- Render one execution from a complete capture. Both dispatch and synchronous
fallback use this call, so their slice reads and memory/provenance treatment agree. -/
def emitCapturedCallWithStorage (name : String) (args : Array (String × Option (String × Nat × Option String)))
    (kind : Nat) : String :=
  let arg (i : Nat) := if args.size == 1 then "a" else s!"capture{i}"
  let itemName (i : Nat) := if args.size == 1 then "items" else s!"items{i}"
  let values := args.mapIdx fun i (_, adapter) =>
    match adapter with | none => arg i | some _ => itemName i
  let term := name ++ (if values.isEmpty then "" else " " ++ String.intercalate " " values.toList)
  let reads := args.toList.zipIdx |>.filterMap fun ((_, adapter), i) =>
    adapter.map fun (item, align, enc) =>
      let read := s!"Zig.readSlice ({item}) {align} {arg i}"
      let read := match enc with
        | none => read
        | some dictionary => s!"(letI : Zig.Enc ({item}) := {dictionary}; {read})"
      s!"          let {itemName i} ← {read}"
  match kind with
  | 2 => term
  | 1 => s!"Zig.ConcM.liftMem ({term})"
  | _ => if reads.isEmpty then s!"Zig.ConcM.liftMem (StateT.lift ({term}))" else
      "Zig.ConcM.liftMem (do\n" ++ String.intercalate "\n" reads ++ s!"\n          StateT.lift ({term}))"

def emitCapturedFallbackWithStorage (name : String) (args : Array (String × Option (String × Nat × Option String)))
    (kind : Nat) : String :=
  let binders := (List.range args.size).map fun i => s!"capture{i}"
  let unpack := if args.size > 1 then s!"let ({String.intercalate ", " binders}) := a; " else ""
  s!"fun a => (do {unpack}discard ({emitCapturedCallWithStorage name args kind}) : Zig.ConcM Tgt Unit)"

/-- Only async sites execute a caller fallback. Scan all sites before filtering the
ordered first-use descriptions: an earlier spawn/concurrent site can share the worker. -/
def emitSpawnFallbacksWithStorage (funcs : Array Func)
    (descriptions : Array (String × String × Array (String × Option (String × Nat × Option String)) × Nat)) :
    Array (String × String) :=
  let empty : Std.HashSet String := {}
  let workers := funcs.foldl (fun workers f => f.allInsts.foldl (fun workers i =>
    match i.op with
    | .call (.func name _ (some worker)) _ =>
      if threadFn? name == some .groupAsync then workers.insert worker else workers
    | _ => workers) workers) empty
  descriptions.filterMap fun (worker, name, args, kind) =>
    if workers.contains worker then some (worker, emitCapturedFallbackWithStorage name args kind) else none

/-- Ordinary capture adapters select their existing global dictionaries. -/
def captureStorageArgs (args : Array (String × Option (String × Nat))) :
    Array (String × Option (String × Nat × Option String)) :=
  args.map fun (ty, adapter) => (ty, adapter.map fun (item, align) => (item, align, none))

def emitCapturedCall (name : String) (args : Array (String × Option (String × Nat)))
    (kind : Nat) : String :=
  emitCapturedCallWithStorage name (captureStorageArgs args) kind

def emitCapturedFallback (name : String) (args : Array (String × Option (String × Nat)))
    (kind : Nat) : String :=
  emitCapturedFallbackWithStorage name (captureStorageArgs args) kind

def emitSpawnFallbacks (funcs : Array Func)
    (descriptions : Array (String × String × Array (String × Option (String × Nat)) × Nat)) :
    Array (String × String) :=
  emitSpawnFallbacksWithStorage funcs (descriptions.map fun (worker, name, args, kind) =>
    (worker, name, captureStorageArgs args, kind))

/-- A target retains the complete source tuple. Each dispatcher applies the fields in
source order, adapting every slice argument for a pure worker in the child thread. -/
def emitTgtWithStorage (_structNames : Array (String × String)) (extendedCapture : Bool)
    (targets : Array (String × Array (String × Option (String × Nat × Option String)) × Nat)) :
    List String × List String :=
  let ctors := targets.toList.map fun (n, args, _) =>
    let ty := if args.isEmpty then "Unit" else if args.size == 1 then args[0]!.1 else
      String.intercalate " × " (args.toList.map fun (ty, _) => s!"({ty})")
    s!"  | {n} (a : {ty})"
  let captureDoc := if extendedCapture then
    "/-- The spawn targets of the program; fields are captured by value. -/"
    else "/-- The spawn targets of the program. -/"
  let tgt := String.intercalate "\n" ([captureDoc,
    "inductive Tgt where"] ++ ctors)
  let obligation := "/-- The child protocol obligation for the complete captured tuple. Pointer\nidentities are copied; a proof must explicitly justify ownership transfer or sharing. -/\n" ++
    "abbrev Tgt.spawnInit {γ : Type} (P : Zig.Conc.Proto Tgt γ) (target : Tgt) (ghost : γ) : Prop :=\n  P.init target ghost"
  let arms := targets.toList.map fun (n, args, k) =>
    let arg (i : Nat) := if args.size == 1 then "a" else s!"capture{i}"
    let call := emitCapturedCallWithStorage n args k
    if args.size ≤ 1 then s!"  | .{n} a => discard ({call})" else
      let binders := (List.range args.size).map arg
      s!"  | .{n} a =>\n    let ({String.intercalate ", " binders}) := a\n    discard ({call})"
  let body := if arms.isEmpty then ["  fun t => nomatch t"] else arms
  let dispatch := String.intercalate "\n" (["/-- Runs a spawn target (`Zig.Sched.run`). -/",
    s!"def dispatch : Tgt → Zig.ConcM Tgt Unit{if arms.isEmpty then " :=" else ""}"] ++ body)
  ([tgt] ++ (if extendedCapture then [obligation] else []), [dispatch])

/-- Preserve the public helper for callers whose captures need ordinary dictionaries. -/
def emitTgt (structNames : Array (String × String)) (extendedCapture : Bool)
    (targets : Array (String × Array (String × Option (String × Nat)) × Nat)) :
    List String × List String :=
  emitTgtWithStorage structNames extendedCapture (targets.map fun (name, args, kind) =>
    (name, captureStorageArgs args, kind))


/-- Binders introduced by generated helpers and function bodies. Types and calls are rendered
unqualified, so their declarations must avoid these names even when the binder belongs to a
different declaration's body. Source field binders already avoid the allocated type names through
`memberNames` and `collectAllocs`. The indexed names follow this program's parameters and AIR
instruction IDs, including the unused-result spellings and extracted loop captures. -/
def generatedBinderNames (funcs : Array Func)
    (targets : Array (String × Func × Array TyId)) (extendedCapture : Bool) :
    Std.HashSet String := Id.run do
  let mut names : Std.HashSet String := {}
  for name in #["v", "e", "g", "_g", "u", "b", "bs", "t", "x", "y", "s", "a", "items", "x0", "x1", "x2"] do
    names := names.insert name
  for (_, _, fields) in targets do
    if fields.size > 1 then
      for k in [:fields.size] do names := names.insert s!"capture{k}"
  for f in funcs do
    for k in [:f.params.size] do
      names := names.insert s!"p{k}"
      if extendedCapture then names := names.insert s!"items{k}"
    for i in f.allInsts do
      for name in #[s!"i{i.id}", s!"_i{i.id}", s!"v{i.id}", s!"_v{i.id}", s!"a{i.id}", s!"s{i.id}"] do
        names := names.insert name
      if let .loopSwitchBr .. := i.op then
        names := names.insert (dispatchFieldName i.id)
  return names

/-- Allocate source declarations together with their generated names. The unambiguous
historical spelling stays unchanged; a collision gets a stable suffix. -/
def allocateDeclNames (structs : Array NamedType) (funcs : Array Func) (prefix_ : String)
    (fixed : Array String) (targets : Array (String × Func × Array TyId))
    (extendedCapture : Bool) : Array NamedType × Array (String × String) := Id.run do
  let preferred := structs.map (·.leanName) ++ funcs.map (mangleName prefix_ ·.name)
  let mut used := fixed
  let binders := generatedBinderNames funcs targets extendedCapture
  let mut named := #[]
  for s in structs do
    let base := plainName s.leanName
    -- Lean's anonymous instances capitalize the final type-name component.
    let occupied (name : String) : Array String :=
      #[name] ++ #["Repr", "Inhabited", "DecidableEq", "Enc", "Packed"].map
        (fun cls => mangleField s!"inst{cls}{(plainName name).capitalize}")
    let mut k := 0
    let mut name := mangleField base
    while binders.contains name || (occupied name).any used.contains ||
        (k != 0 && (occupied name).any preferred.contains) do
      k := k + 1
      name := mangleField s!"{base}_air2lean{k}"
    used := used ++ occupied name
    named := named.push { s with leanName := name }
  let targetNames := targets.map (·.1)
  let mut names := #[]
  for f in funcs do
    let base := plainName (mangleName prefix_ f.name)
    let occupied (name : String) : Array String :=
      let locals := s!"{plainName name}Locals"
      #[name, mangleField locals, mangleField s!"{plainName name}Exit",
        mangleField s!"instInhabited{locals.capitalize}"]
    let mut k := 0
    let mut name := mangleField base
    while binders.contains name || (occupied name).any used.contains ||
        (targetNames.contains f.name && typeCoreNames.contains name) ||
        (k != 0 && (occupied name).any preferred.contains) do
      k := k + 1
      name := mangleField s!"{base}_air2lean{k}"
    used := used ++ occupied name
    names := names.push (f.name, name)
  return (named, names)

/-- Emission needs only the first validated call for each registered symbol. Value-type
indexes are built lazily, at most once for each function with a selected call. The checker
continues to validate every matching site through its separate exhaustive index. -/
def firstModelCalls (models : Array ModelBinding) (funcs : Array Func) :
    Std.HashMap String ModelRegistry.CallSite := Id.run do
  let mut pending := models.foldl (fun names model => names.insert model.symbol) ({} : Std.HashSet String)
  let mut sites : Std.HashMap String ModelRegistry.CallSite := {}
  for (f, functionIndex) in funcs.zipIdx do
    if pending.isEmpty then break
    let insts := f.allInsts
    let mut values : Option ModelRegistry.ValueTypeIndex := none
    for i in insts do
      if let .call (.func name noreturn spawnFn) args := i.op then
        if pending.contains name then
          let index := match values with
            | some index => index
            | none => ModelRegistry.valueTypeIndex f.types insts
          values := some index
          let site : ModelRegistry.CallSite := {
            functionIndex := functionIndex
            function := f
            values := index
            args := args
            ret := i.ty
            noreturn := noreturn
            spawnFn := spawnFn
          }
          sites := sites.insert name site
          pending := pending.erase name
          if pending.isEmpty then break
  return sites

/-- Emit a typed implementation adapter plus a complete contract obligation. Imported
identifiers are rooted so generated names cannot shadow the user's definitions. -/
def emitModel (m : ModelBinding) (index : Nat) (site : ModelRegistry.CallSite)
    (structNames : Array (String × String)) : String := Id.run do
  let f := site.function
  let ret := site.ret
  -- Checked call sites use the same first-occurrence type resolver as registry validation.
  let ids : Array TyId := match ModelRegistry.argumentTypeIds site.values site.args with
    | .ok ids => ids
    | .error error => panic! s!"air2lean: unchecked model arguments: {error}"
  let tys : Array String := ids.map fun (id : TyId) => emitTy structNames f.types f.types[id]!
  let result := emitTy structNames f.types f.types[ret]!
  let argsTy := if tys.isEmpty then "Unit" else
    " × ".intercalate (tys.map fun ty => s!"({ty})").toList
  let names := (Array.range tys.size).map fun i => s!"p{i}"
  let binders := (tys.zip names).map fun (ty, name) => s!"({name} : {ty})"
  let tuple := if names.isEmpty then "()" else if names.size == 1 then names[0]!
    else s!"({", ".intercalate names.toList})"
  let base := s!"air2lean_model_{index}"
  let errors := "[" ++ ", ".intercalate (m.errors.map ("Zig.Error." ++ ·)).toList ++ "]"
  let termination := if m.termination == "partial" then "«partial»" else "total"
  let holds := s!"{base}_contract.Holds .{termination} {errors} .{m.effects} _root_.{m.implementation}"
  -- Right-associated argument tuple: parameter `i` of `n` is `.2` (i times) then `.1` unless last.
  let project (i : Nat) : String :=
    "args" ++ String.join (List.replicate i ".2") ++ (if i + 1 < tys.size then ".1" else "")
  let regions (indices : Array Nat) : String :=
    (if indices.isEmpty then "fun _ => [" else "fun args => [") ++
      ", ".intercalate (indices.map fun i => s!"Zig.External.Region.block {project i}").toList ++ "]"
  let (footprintDef, obligation) := match m.footprint with
    | some fp =>
      ([s!"def {base}_footprint : Zig.External.Footprint ({argsTy}) where\n" ++
          s!"  reads := {regions fp.reads}\n  writes := {regions fp.writes}"],
        s!"{holds} ∧ {base}_contract.Respects {base}_footprint")
    | none => ([], holds)
  let evidence := match m.proof with
    | some proof => s!"theorem {base}_evidence : {obligation} := _root_.{proof}"
    | none => s!"-- Explicit imported-model assumption; reported in air2lean-models.\naxiom {base}_evidence : {obligation}"
  return String.intercalate "\n\n" ([
    s!"def {base}_contract : Zig.External.Contract ({argsTy}) ({result}) := _root_.{m.contract}",
    s!"def {base} {" ".intercalate binders.toList} : Zig.MemM ({result}) := _root_.{m.implementation} {tuple}"] ++
    footprintDef ++ [evidence])

/-- `funcs → one Lean source file` importing `ZigLean`, namespaced under `ns`. `prefix_` is
stripped from every Zig name (function or struct) before mangling. `floatSemantics` selects
`--float-semantics` (default `ieee`). -/
def emit (funcs : Array Func) (ns : String) (prefix_ : String)
    (floatSemantics : FloatSemantics := .ieee) (models : Array ModelBinding := #[])
    (spawnSemantics : SpawnSemantics := .available) (proofApi : Bool := false) : String :=
  let memFuncs := memoryFunctions funcs (models.map (·.symbol))
  let concFuncs := concFunctions funcs
  let asmDefs := collectAsmOps funcs
  let hasErrorName := funcs.any (·.allInsts.any fun i => match i.op with | .errorName _ => true | _ => false)
  let targets := spawnTargets funcs
  let extendedCapture := targets.any fun (_, _, fields) => fields.size != 1
  let modelCalls := firstModelCalls models funcs
  let maxModelArgs := modelCalls.fold (fun count _ site => max count site.args.size) 0
  let modelBinders := (Array.range maxModelArgs).map fun i => s!"p{i}"
  let modelNames := models.zipIdx.flatMap fun (m, i) =>
    #[s!"air2lean_model_{i}", s!"air2lean_model_{i}_contract", s!"air2lean_model_{i}_evidence"] ++
      (if m.footprint.isSome then #[s!"air2lean_model_{i}_footprint"] else #[])
  let apiNames := if proofApi then funcs.flatMap (fun f =>
    if (proofApiFacts f).isSome then #[proofApiName f.name ++ "_model", proofApiName f.name ++ "_unfold"] else #[]) else #[]
  let fixed := runtimeNames ++ apiNames ++ modelNames ++ modelBinders ++
    (if memFuncs.isEmpty then #[] else #["mem0"]) ++
    (if concFuncs.isEmpty then #[] else #["Tgt", "dispatch"]) ++
    (if extendedCapture then #["spawnInit"] else #[]) ++
    (if hasErrorName then #["errorNameOf"] else #[]) ++ asmDefs.map (·.name)
  let (structs, ownFuncNames) := allocateDeclNames (collectNamed funcs prefix_) funcs prefix_ fixed targets extendedCapture
  let funcNames := ownFuncNames ++ models.mapIdx (fun i m => (m.symbol, s!"air2lean_model_{i}"))
  let structNames := structs.map fun s => (s.zigName, s.leanName)
  let structsStr := (structs.map (emitNamed structNames (encTypeNames funcs memFuncs))).toList
  let asmStr := asmDefs.toList.map emitAsmDef
  let modelStr := (models.mapIdx fun index model =>
    match modelCalls[model.symbol]? with
    | some site => emitModel model index site structNames
    | none => "").toList
  let mkFc (f : Func) (ids : Array Nat) := mkFCtxUnprepared f structNames funcNames floatSemantics memFuncs ids
  let (globals, ids) := collectGlobals funcs mkFc
  -- The tag names are blocks after the globals.
  let (globals, tagDefs) := (tagNameEnums funcs structNames).foldl (init := (globals, #[]))
    fun (gs, defs) (_, lean, fields, exhaustive, bits) =>
      let d := emitTagName lean fields exhaustive bits gs.size (structNames.map (·.2))
      let gs := fields.foldl (fun gs (f, _) =>
        gs.push { label := s!"the name of {lean}.{f}", bytes := nameBytes f, align := 1 }) gs
      (gs, defs.push d)
  let errNames := errorNames funcs
  let errDefs := if hasErrorName then [emitErrorNameOf errNames globals.size] else []
  let globals := errNames.foldl (fun gs n =>
    gs.push { label := s!"the name of error.{n}", bytes := nameBytes n, align := 1 }) globals
  let globalsStr := if memFuncs.isEmpty then [] else [emitMem0 globals] ++ tagDefs.toList ++ errDefs
  let idsOf (f : Func) := ((ids.find? (·.1 == f.name)).map (·.2)).getD #[]
  let fnBlocks := (fnRefs funcs).filterMap fun (tn, nm) =>
    (globals.findIdx? (·.label == nm)).map (tn, nm, ·)
  let leanOf (nm : String) := (funcNames.find? (·.1 == nm)).map (·.2) |>.getD nm
  let targetDescriptions := targets.map fun (nm, f, fields) =>
      let kind := if concFuncs.contains nm then 2 else if memFuncs.contains nm then 1 else 0
      -- The physical capture comes from the first call; conversion requirements
      -- belong to the worker contract and must also accept later weaker captures.
      let worker := (funcs.find? (·.name == nm)).getD f
      let args := fields.mapIdx fun index a =>
        let parameter := worker.params[index]!
        let adapter := if kind != 0 then none else match worker.types[parameter]! with
          | .ptr "slice" true child =>
            some (emitTy structNames worker.types worker.types[child]!,
              Nat.min ((worker.layouts[parameter]?.bind (·.ptrAlign)).getD 1)
                ((worker.layouts[child]?.bind (·.align)).getD 1),
              emitStorageEnc structNames worker.types child)
          | _ => none
        (emitTy structNames f.types f.types[a]!, adapter)
      (nm, leanOf nm, args, kind)
  let spawnFallbacks := if spawnSemantics == .fallible then
    emitSpawnFallbacksWithStorage funcs targetDescriptions
    else #[]
  let spawnFallbackMap := prepareSpawnFallbackMap spawnFallbacks
  let (tgtStr, dispatchStr) := if concFuncs.isEmpty then ([], []) else
    emitTgtWithStorage structNames extendedCapture (targetDescriptions.map fun (_, name, args, kind) => (name, args, kind))
  let funcsStr := (callGroups funcs).toList.map fun (members, recursive) =>
    let parts := members.toList.map fun f =>
      emitOneFunctionWithFallbackMap f spawnFallbackMap structNames funcNames floatSemantics memFuncs
        (idsOf f) fnBlocks concFuncs spawnSemantics spawnFallbacks
    if recursive then
      -- `partial_fixpoint` on every def of the group: the loop defs too, since a loop body can
      -- call a group member. Types and `again` defs do not recurse, so they come first.
      let fix (d : String) := s!"{d}\npartial_fixpoint"
      let defs := parts.flatMap fun p => (p.loops ++ [p.defn]).map fix
      String.intercalate "\n\n"
        (parts.flatMap (·.types) ++ parts.flatMap (·.agains) ++ ["mutual"] ++ defs ++ ["end"])
    else
      String.intercalate "\n\n" ((members.toList.zip parts).flatMap fun (f, p) =>
        p.types ++ p.agains ++ p.loops ++ [p.defn] ++
          (if proofApi then
            (emitProofApi f (fun _ => mkFCtxUnprepared f structNames funcNames floatSemantics memFuncs (idsOf f) concFuncs) p.body).toList
          else []))
  String.intercalate "\n\n"
    (["import ZigLean"] ++ (models.map (fun m => s!"import {m.importModule}")).toList ++
      (if spawnSemantics == .fallible then ["/- Thread assignment policy: fallible; all declared spawn errors and Io.Group caller fallback are modeled. -/"] else []) ++
      [s!"\nnamespace {ns}"] ++ structsStr ++ asmStr ++ modelStr ++ globalsStr ++ tgtStr ++
      funcsStr ++ dispatchStr ++ [s!"end {ns}"])

end Air2Lean
