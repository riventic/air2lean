import Std.Data.HashSet
import Air2Lean.Check
import Air2Lean.ProofApi
import Air2Lean.Device

/-!
# Emitter

`emit : Array Func → String → String → String` turns a list of already-checked functions into
one Lean source file: `import ZigLean`, one `namespace <ns>`, struct types once (deduplicated
by Zig name), `mem0` and the `@tagName`/`@errorName` defs if a function uses memory (§Globals),
then per function a generated `<Fn>Locals` structure (one field per `alloc`), a
generated `<Fn>Exit` inductive (`ret` / `br<targetId>` / `rep<targetId>`, one constructor per
distinct branch target reachable in the function), and the function itself as a
`Zig.M <Fn>Locals <Fn>Exit` do-block wrapped by a top-level `def` that unwraps `.ret`.

Assumes its input already passed `Check.lean`: it does not re-validate the subset. An arm that
`Check.lean` makes unreachable writes `placeholder`, never a term with a value: a `panic!` or a
`default` is a successful no-op in the logic (`docs/architecture-audit/memory-model.md`, MM-6).
`emitWithNamesChecked` (the CLI's entry point) rejects any output that contains one, and the
placeholder does not elaborate either. An exit other than `.ret` leaving a function's outermost
body is `throw .panic`.
-/

namespace Air2Lean

/-- The identifier of an emitter placeholder. It is bound nowhere, so generated Lean that still
contains one does not elaborate; `emitWithNamesChecked` rejects it before writing. -/
def placeholderMarker : String := "air2lean_emitter_placeholder"

/-- The term an emitter arm writes for input that `Check.lean` should have rejected (MM-6). -/
def placeholder (what : String) : String := s!"({placeholderMarker} {what.quote})"

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
      (if tag.isSome then #["tag"] else #[]) ++ (fs.flatMap fun (p : String × TyId) =>
        #[s!"get_{p.1}", s!"modify_{p.1}"] ++ (if tag.isSome then #[s!"setTag_{p.1}"] else #[])) ++
      -- A retagged payload (MM-13): its constructor and the writes that define it.
      (if tag.isSome && fs.size > 1 then fs.flatMap fun (p : String × TyId) =>
        #[s!"undef_{p.1}", s!"set_{p.1}", s!"setField_{p.1}"] else #[])
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

/-- Field `idx` of the tagged union `uty` gets an undefined payload when a retag activates it
(MM-13): the union has another field that can be active, and the payload has bits (not `void`,
not `noreturn`, not a struct without fields). `idx` is the AIR field index (`noreturn` fields
included). `some (some names)`: the payload is a struct with the Lean member `names`; it
becomes defined once each of them is written. `some none`: only a whole-payload write defines
it. -/
def unionFreshPayload (types : Array Ty) (uty : Ty) (idx : Nat) (reserved : Array String := #[]) :
    Option (Option (Array String)) :=
  match uty with
  | .union _ _ (some _) fields =>
    if (inhabitedFields types fields).size ≤ 1 then none else do
    let (_, id) ← fields[idx]?
    match types[id]? with
    | some .void | some .noreturn | none => none
    | some t@(.struct _ _ sfs) =>
      if sfs.isEmpty then none else some (some (sfs.map (memberName t ·.1 reserved)))
    | some _ => some none
  | _ => none

/-! ## Types (`docs/generated-code.md` §Types) -/

/-- The `Zig.FN` format term for an `n`-bit float type (`ZigLean/Float/Format.lean`). `n` is
always one of `16 32 64 80 128` (`Check.lean`). -/
def floatFmtName (n : Nat) : String :=
  match n with
  | 16 => "Zig.F16" | 32 => "Zig.F32" | 64 => "Zig.F64" | 80 => "Zig.F80" | 128 => "Zig.F128"
  | _ => s!"Zig.Float .f{n}" -- unreachable: Check.lean restricts `n`

/-- The Lean type of a slice for a profile with `ptrBits`-bit pointers. -/
def sliceTyName (ptrBits : Nat) : String :=
  if ptrBits == 64 then "Zig.Slice" else s!"Zig.Slice{ptrBits}"

/-- `TyId → Lean type` as source text. `structNames` maps the Zig name of a struct, enum or
union to its Lean name. `pureSlice`: `ty` is the type of a value of a pure function, where a
`[]const T` is an `Array` (`docs/generated-code.md` §Memory); everywhere else a slice is a
`Zig.Slice`, or `Zig.Slice32` for a 32-bit profile (`ptrBits`, `ZigLean/Mem/Width.lean`). -/
partial def emitTy (structNames : Array (String × String)) (types : Array Ty) (ty : Ty)
    (pureSlice : Bool := false) (ptrBits : Nat := 64) : String :=
  let emitTy (structNames : Array (String × String)) (types : Array Ty) (ty : Ty) :=
    emitTy structNames types ty (ptrBits := ptrBits)
  let slice := sliceTyName ptrBits
  match ty with
  | .int _ bits => s!"BitVec {bits}"
  | .float bits => floatFmtName bits
  | .bool => "Bool"
  | .void => "Unit"
  | .noreturn => "Unit"
  | .ptr "slice" true child =>
    if pureSlice then s!"Array ({emitTy structNames types types[child]!})" else slice
  | .ptr "slice" .. => slice
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
  | .future r => s!"Zig.Future ({emitTy structNames types types[r]!})"
  | .other name => name

/-- A finite declared name table, with checked capacity and uniqueness. These positions
are not ABI error ordinals; storage retains the shared symbolic `errFrag` identity. -/
def emitErrorDomain (names : Array String) : String :=
  s!"(⟨#[{String.intercalate ", " (names.toList.map String.quote)}], by decide, by decide⟩ : Zig.ErrorDomain)"

/-- The error-storage operation `name` of `ZigLean/Mem/Enc.lean` at the profile's
`error_set_bits`: the default 16 bits keeps the original 2-byte definitions (byte-identical
output); any other width selects the width-parameterized `<name>W bits` of
`ZigLean/Mem/ErrWidth.lean`. -/
def errOp (errBits : Nat) (name : String) : String :=
  if errBits == 16 then s!"Zig.{name}" else s!"Zig.{name}W {errBits}"

/-- An explicit type-indexed storage dictionary. No instance for `String` is registered.
Named aggregate dictionaries choose these recursively for their fields. At a non-default
error width every error union also gets an explicit dictionary, since the registered
`Enc (Except ErrName α)` instance is the 16-bit one. A C/allowzero pointer (`layouts` gives
allowzero) is stored with `Zig.nullablePtrEnc`: null is eight zero bytes (`Check.lean` rejects
an optional of one, which would need a separate flag). -/
partial def emitStorageEnc (structNames : Array (String × String)) (types : Array Ty)
    (errBits : Nat) (id : TyId) (layouts : Array Layout := #[]) (ptrBits : Nat := 64) :
    Option String :=
  let emitStorageEnc (structNames : Array (String × String)) (types : Array Ty) (errBits : Nat)
      (id : TyId) (layouts : Array Layout) :=
    emitStorageEnc structNames types errBits id layouts (ptrBits := ptrBits)
  match types[id]? with
  | some (.ptr ..) => if nullablePtrTy types layouts id then some "Zig.nullablePtrEnc" else none
  | some (.errorSet (some names)) => some s!"{errOp errBits "errorEnc"} {emitErrorDomain names}"
  | some (.optional c) =>
    match types[c]? with
    | some (.errorSet (some names)) => some s!"{errOp errBits "optionalErrorEnc"} {emitErrorDomain names}"
    | _ => (emitStorageEnc structNames types errBits c layouts).map fun enc => s!"Zig.Enc.optionWith ({enc})"
  | some (.array n c sentinel) =>
    (emitStorageEnc structNames types errBits c layouts).map fun enc =>
      s!"Zig.Enc.vectorWith {n + if sentinel then 1 else 0} ({enc})"
  | some (.errorUnion set payload) =>
    let payloadEnc := emitStorageEnc structNames types errBits payload layouts
    let enc := payloadEnc.getD
      s!"(inferInstance : Zig.Enc ({emitTy structNames types types[payload]! (ptrBits := ptrBits)}))"
    match types[set]? with
    | some (.errorSet (some names)) => some s!"{errOp errBits "errorUnionEnc"} {emitErrorDomain names} ({enc})"
    | _ =>
      if errBits == 16 then payloadEnc.map fun _ => s!"Zig.Enc.errorUnionWith ({enc})"
      else some s!"Zig.Enc.errorUnionWithW {errBits} ({enc})"
  | some (.future r) =>
    (emitStorageEnc structNames types errBits r layouts).map fun enc =>
      s!"@Zig.Future.instEnc ({emitTy structNames types types[r]! (ptrBits := ptrBits)}) ({enc})"
  | _ => none

/-- Bind a dictionary only around the storage operation that needs it. This preserves the
public semantic types (`ErrName`, `Option ErrName`, `Except ErrName`) and pure APIs. -/
def withStorageEnc (structNames : Array (String × String)) (types : Array Ty) (errBits : Nat)
    (id : TyId) (expr : String) (layouts : Array Layout := #[]) (ptrBits : Nat := 64) : String :=
  match emitStorageEnc structNames types errBits id layouts (ptrBits := ptrBits) with
  | none => expr
  | some enc =>
    s!"(letI : Zig.Enc ({emitTy structNames types types[id]! (ptrBits := ptrBits)}) := {enc}; {expr})"

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
  /-- The source function's `error_set_bits`. -/
  errBits : Nat := 16
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
  | .ptr "slice" _ c | .array _ c _ | .optional c | .future c => go c
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
                                   layout := f.layouts[i]?.getD {}, errBits := f.errorSetBits }
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
  let ptrBits := 8 * ptrBytesOf s.srcLayouts
  let emitTy (structNames : Array (String × String)) (types : Array Ty) (ty : Ty) :=
    emitTy structNames types ty (ptrBits := ptrBits)
  let withStorageEnc (structNames : Array (String × String)) (types : Array Ty) (errBits : Nat)
      (id : TyId) (expr : String) (layouts : Array Layout) :=
    withStorageEnc structNames types errBits id expr layouts (ptrBits := ptrBits)
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
    let (to, po) := (unionOffsets s.srcTypes s.srcLayouts tag (fields.map (·.2)) s.errBits).getD (0, 0)
    let tagTy := emitTy structNames s.srcTypes s.srcTypes[tag]!
    let isVoid (id : TyId) : Bool := s.srcTypes[id]! == .void
    let enc := (inhabitedFields s.srcTypes fields).toList.map fun (f, id) =>
      if isVoid id then s!"    | .{fm f} => Zig.Enc.fields {size} [({to}, Zig.Enc.encode v.{hn "tag"})]"
      else s!"    | .{fm f} x => Zig.Enc.fields {size} [({to}, Zig.Enc.encode v.{hn "tag"}), ({po}, {withStorageEnc structNames s.srcTypes s.errBits id "Zig.Enc.encode x" s.srcLayouts})]"
    -- A retagged payload that is not defined yet: its bytes are undefined (MM-13).
    let encUndef := (List.range fields.size).filterMap fun i =>
      (unionFreshPayload s.srcTypes s.ty i (structNames.map (·.2))).map fun _ =>
        s!"    | .{hn s!"undef_{fields[i]!.1}"} _ _ => Zig.Enc.fields {size} [({to}, Zig.Enc.encode v.{hn "tag"})]"
    -- The tag of a `noreturn` variant names no value: its bytes are illegal, like an enum tag
    -- without a name.
    let dec := fields.toList.map fun (f, id) =>
      if uninhabitedTy s.srcTypes id then s!"    | .{fm f} => throw .illegal"
      else if isVoid id then s!"    | .{fm f} => pure .{fm f}"
      else s!"    | .{fm f} => pure (.{fm f} (← {withStorageEnc structNames s.srcTypes s.errBits id s!"Zig.Enc.decodeAt bs {po}" s.srcLayouts}))"
    String.intercalate "\n" (head ++ ["  encode v := match v with"] ++ enc ++ encUndef ++
      ["  decode bs := do", s!"    let t : {tagTy} ← Zig.Enc.decodeAt bs {to}", "    match t with"] ++ dec)
  | .struct _ "packed" fields =>
    -- Its backing integer (`Zig.Packed`).
    let bits := fields.foldl (fun acc (_, t) => acc + (packedBits s.srcTypes t).getD 0) 0
    String.intercalate "\n" (head ++
      ["  encode v := Zig.Enc.encode (Zig.Packed.toBits v)", "  decode bs := do",
       s!"    let b : BitVec {bits} ← Zig.Enc.decode bs", "    Zig.Packed.ofBits? b"])
  | .struct _ _ fields =>
    let parts := (fields.zip s.layout.offsets).toList.map fun ((f, id), o) =>
      s!"({o}, {withStorageEnc structNames s.srcTypes s.errBits id s!"Zig.Enc.encode v.{fm f}" s.srcLayouts})"
    let decs := (fields.zip s.layout.offsets).toList.map fun ((f, id), o) =>
      s!"{fm f} := ← {withStorageEnc structNames s.srcTypes s.errBits id s!"Zig.Enc.decodeAt bs {o}" s.srcLayouts}"
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
  let ptrBits := 8 * ptrBytesOf s.srcLayouts
  let emitTy (structNames : Array (String × String)) (types : Array Ty) (ty : Ty) :=
    emitTy structNames types ty (ptrBits := ptrBits)
  let withStorageEnc (structNames : Array (String × String)) (types : Array Ty) (errBits : Nat)
      (id : TyId) (expr : String) (layouts : Array Layout) :=
    withStorageEnc structNames types errBits id expr layouts (ptrBits := ptrBits)
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
      ["", s!"def {n}.{hn s!"get_{f}"} (u : {n}) : Zig.Result ({t}) := {withStorageEnc structNames s.srcTypes s.errBits id s!"{ns}.get ({t}) u.bytes" s.srcLayouts}", "",
       s!"def {n}.{hn s!"modify_{f}"} (g : {t} → {t}) (u : {n}) : {n} :=",
       s!"  {withStorageEnc structNames s.srcTypes s.errBits id s!"⟨{ns}.set u.bytes (g (Zig.Raw.getD ({ns}.get ({t}) u.bytes)))⟩" s.srcLayouts}"]
    String.intercalate "\n"
      ([s!"structure {n} where", s!"  bytes : Vector Zig.Byte {size}",
        "  deriving Repr, Inhabited, DecidableEq"] ++ perField)
  | .union _ _ tag fields =>
    let tagName := match tag.bind (s.srcTypes[·]?) with
      | some t => emitTy structNames s.srcTypes t
      | none => "Unit"
    let isVoid (id : TyId) : Bool := s.srcTypes[id]! == .void
    -- A `noreturn` variant has no constructor and no accessors (`uninhabitedTy`).
    let airFields := fields
    let fields := inhabitedFields s.srcTypes fields
    let wild := if fields.size > 1 then ["  | _ => throw .panic"] else []
    -- A retag leaves a payload with bits undefined (MM-13): `undef_f v written` holds `f`'s
    -- payload while it is not defined, `v` with the struct fields `written` (`setField_f`).
    -- `unionFreshPayload` takes the AIR index of each inhabited field.
    let fresh := ((List.range airFields.size).filter fun i =>
        !uninhabitedTy s.srcTypes airFields[i]!.2).map fun i =>
      unionFreshPayload s.srcTypes s.ty i (structNames.map (·.2))
    let undefCtors := (fields.toList.zip fresh).filterMap fun ((f, id), fr) =>
      fr.map fun _ => s!"  | {hn s!"undef_{f}"} (v : {tyStr id}) (written : List String)"
    let ctors := fields.toList.map fun (f, id) =>
      if isVoid id then s!"  | {fm f}" else s!"  | {fm f} (v : {tyStr id})"
    let tagArms := (fields.toList.zip fresh).flatMap fun ((f, id), fr) =>
      let pat := if isVoid id then s!".{fm f}" else s!".{fm f} _"
      [s!"  | {pat} => .{fm f}"] ++ (fr.map fun _ => s!"  | .{hn s!"undef_{f}"} _ _ => .{fm f}").toList
    let perField := (fields.toList.zip fresh).flatMap fun ((f, id), fr) =>
      let fm := fm f
      let (pat, val, pty) :=
        if isVoid id then (s!".{fm}", "()", "Unit") else (s!".{fm} v", "v", tyStr id)
      match fr with
      | some names =>
        let u := s!".{hn s!"undef_{f}"}"
        let complete (v w : String) : String := match names with
          | some ns =>
            let lit := String.intercalate ", " (ns.toList.map fun k => s!"\"{k}\"")
            s!"if [{lit}].all ({w}).contains then .{fm} ({v}) else {u} ({v}) ({w})"
          | none => s!"{u} ({v}) ({w})"
        ["", s!"def {n}.{hn s!"get_{f}"} : {n} → Zig.Result ({pty})", s!"  | {pat} => pure {val}",
         s!"  | {u} _ _ => throw .unspecified"] ++ wild ++
        ["", s!"def {n}.{hn s!"modify_{f}"} (g : {pty} → {pty}) : {n} → {n}", s!"  | {pat} => .{fm} (g v)",
         s!"  | {u} v w => {u} (g v) w", s!"  | _ => {u} (g default) []"] ++
        ["", s!"def {n}.{hn s!"setTag_{f}"} : {n} → {n}", s!"  | {pat} => .{fm} v",
         s!"  | {u} v w => {u} v w", s!"  | _ => {u} default []"] ++
        ["", s!"def {n}.{hn s!"set_{f}"} (v : {pty}) (_ : {n}) : {n} := .{fm} v"] ++
        (if names.isSome then
          ["", s!"def {n}.{hn s!"setField_{f}"} (k : String) (g : {pty} → {pty}) : {n} → {n}",
           s!"  | {pat} => .{fm} (g v)", s!"  | {u} v w => {complete "g v" "k :: w"}",
           s!"  | _ => {complete "g default" "[k]"}"] else [])
      | none =>
      -- Void, or the only field: a retag keeps or makes the value.
      let (keep, apply, fresh, applyFresh, g) :=
        if isVoid id then (s!".{fm}", s!".{fm}", s!".{fm}", s!".{fm}", "_g")
        else (s!".{fm} v", s!".{fm} (g v)", s!".{fm} default", s!".{fm} (g default)", "g")
      let multi (l : String) : List String := if fields.size > 1 then [l] else []
      ["", s!"def {n}.{hn s!"get_{f}"} : {n} → Zig.Result ({pty})", s!"  | {pat} => pure {val}"] ++ wild ++
      ["", s!"def {n}.{hn s!"modify_{f}"} ({g} : {pty} → {pty}) : {n} → {n}", s!"  | {pat} => {apply}"] ++
        multi s!"  | _ => {applyFresh}" ++
      ["", s!"def {n}.{hn s!"setTag_{f}"} : {n} → {n}", s!"  | {pat} => {keep}"] ++ multi s!"  | _ => {fresh}"
    String.intercalate "\n"
      ([s!"inductive {n} where"] ++ ctors ++ undefCtors ++ ["  deriving Repr, Inhabited, DecidableEq", "",
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
partial def memNamed (types : Array Ty) (layouts : Array Layout) (errBits : Nat) (acc : Array String)
    (id : TyId) : Array String :=
  if (modelLayout types layouts id errBits).toOption.isNone then acc else
  match types[id]? with
  | some (.struct name _ fs) =>
    if acc.contains name then acc else fs.foldl (fun a (_, t) => memNamed types layouts errBits a t) (acc.push name)
  | some (.enum name ..) => if acc.contains name then acc else acc.push name
  | some (.union name _ tag fs) =>
    if acc.contains name then acc
    else (tag.toArray ++ fs.map (·.2)).foldl (memNamed types layouts errBits) (acc.push name)
  | some (.optional c) | some (.array _ c _) => memNamed types layouts errBits acc c
  | some (.errorUnion _ c) => memNamed types layouts errBits acc c
  | _ => acc

/-- The named types that get a `Zig.Enc` instance: those that a pointer of a function that uses
memory can point to, the types of the globals, and every `extern` or `packed` union with its
field types. A v0 function never has one, so v0 translations do not change. -/
def encTypeNames (funcs : Array Func) (memFuncs : Array String) : Array String :=
  funcs.foldl (init := #[]) fun acc f =>
    -- An `extern` or `packed` union reads its fields with `Zig.Enc`, also in a pure function.
    let acc := f.types.zipIdx.foldl (init := acc) fun acc (t, id) => match t with
      | .union _ _ none _ => memNamed f.types f.layouts f.errorSetBits acc id
      | _ => acc
    -- Instruction and operand types come from the checker's index (`Check.lean` `valTy?`).
    let operands := f.operandTypes
    -- A byte local (`Zig.Bytes T`) encodes its value, also in a pure function.
    let acc := (byteLocals f).foldl (init := acc) fun acc aid =>
      match operands.instructions[aid]?.bind (ptrChild f.types) with
      | some c => memNamed f.types f.layouts f.errorSetBits acc c
      | none => acc
    -- A Zig ≤0.16 representation `@bitCast` (`Zig.reprCast`) encodes and decodes both sides.
    let acc := operands.insts.foldl (init := acc) fun acc i => match i.op with
      | .bitcast a =>
        match operands.valTy? a with
        | some s =>
          if reprCastApplies f.zigVersion f.types s i.ty then
            memNamed f.types f.layouts f.errorSetBits
              (memNamed f.types f.layouts f.errorSetBits acc s) i.ty
          else acc
        | none => acc
      | _ => acc
    -- `mem0` (emitted when any function uses memory) encodes the globals of every function
    -- (`collectGlobals`), also of a pure one.
    let acc := if memFuncs.isEmpty then acc else
      f.globals.foldl (fun acc g => memNamed f.types f.layouts f.errorSetBits acc g.ty) acc
    if !memFuncs.contains f.name then acc
    else
      f.types.foldl (init := acc) fun acc t => match t with
        | .ptr _ _ c => memNamed f.types f.layouts f.errorSetBits acc c
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
(f80 invalid encodings), D (f32/f64 mixed-sign-zero `@min`/`@max`) and I (a signaling NaN in
`@min`/`@max`) throw `.unspecified` in both modes, unconditionally: `docs/floats.md` §f80
invalid encodings, §+0 and −0 in @min/@max. The profile's target (`FCtx.targetArch`) selects
the aarch64 rules (`FCtx.aarch64Floats`, `docs/floats.md` §Targets) in both modes. -/
inductive FloatSemantics where
  | ieee
  | compilerRt
  deriving DecidableEq, Repr

/-! ## Per-function static context -/

/-- One step from a local to a place inside it: a struct field, or the payload of a union
field. -/
inductive PathStep where
  | field (name : String)
  /-- `union`: the union's Lean name; `getName`/`modifyName`: the field's accessors
  (`FCtx.unionField?`). `fresh`: for a field whose payload a retag leaves undefined (MM-13), the
  helpers that write the whole payload (`set_f`) and one whole field of a struct payload
  (`setField_f`, `none` if the payload is not a struct). -/
  | ufield (union : String) (getName modifyName : String)
      (fresh : Option (String × Option String) := none)
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
  /-- The profile's `error_set_bits` (`Func.errorSetBits`), for error storage (`errOp`). -/
  errBits : Nat := 16
  /-- The profile is big endian (`Func.bigEndian`): bit-pointer accesses take `.big`. -/
  bigEndian : Bool := false
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
  /-- The byte locals (`Air2Lean/Memory.lean`'s `byteLocals`): `Locals` fields of type
  `Zig.Bytes T`, the bytes of a value with undefined parts. -/
  byteLocals : Array InstId := #[]
  /-- Each place of a byte local: `(place, alloc, byte offset)`. -/
  bytePlaces : Array (InstId × InstId × Nat) := #[]
  /-- The functions that return `Zig.Bytes T` (`rawFunctions`). -/
  rawFuncs : Array String := #[]
  /-- `Func.targetArch`: an asm op off the allowlist is a device event (`Op.isDeviceAsm`). -/
  targetArch : String := ""
  /-- The instructions whose value is `Zig.Bytes T` (`FCtx.computeRawInsts`). -/
  rawInsts : Array InstId := #[]
  /-- This function returns `Zig.Bytes T` (it is in `rawFuncs`). -/
  rawRet : Bool := false
  /-- The float `div_trunc`s that are the safety-checked lowering of `@divExact`
  (`exactFloatDivs`). -/
  exactFloatDivs : Array InstId := #[]
  /-- The sentinel slicings that a Sema check compares (`sentinelCheckedSlices`). -/
  sentinelChecked : Array InstId := #[]
  /-- This function is in a recursive call group (`callGroups`): its call depth is not bounded
  by the call graph, so a function that uses memory charges its frame to the stack budget
  (`Zig.enterFrame`, MM-5). -/
  recursive : Bool := false

/-- The `div_trunc`s that lower a float `@divExact` with safety on (`Sema.zirDivExact`):
`r = div_trunc(a, b)`, `f = floor(r)`, `ok = cmp_eq(r, f)` (for a vector, `reduce(And)` of a
`cmp_vector` `eq`), and a `cond_br` on `ok` whose `else` calls the `exactDivisionRemainder`
panic handler. Only a `floor` of a float reaches this shape, so `r` is a float division. That
check only catches a NaN quotient, so the emitter lowers `r` with `Zig.Float.divExactTrunc`,
which makes every other inexact quotient `.illegal` (`docs/illegal-behavior.md`). -/
def exactFloatDivs (insts : Array Inst) : Array InstId := Id.run do
  let byId : Std.HashMap InstId Inst := insts.foldl (fun m i => m.insert i.id i) {}
  let opOf (v : Val) : Option Op := match v with
    | .inst id => byId[id]?.map (·.op)
    | _ => none
  let isFloorOf (f : Val) (r : InstId) : Bool := match opOf f with
    | some (.floatRound .floor (.inst r')) => r' == r
    | _ => false
  -- The truncated quotient compared with its own floor.
  let checked (cmp : Val) : Option InstId := match opOf cmp with
    | some (.cmp .eq (.inst r) f) =>
      match opOf (.inst r) with
      | some (.div .divTrunc ..) => if isFloorOf f r then some r else none
      | _ => none
    | _ => none
  let callsExact (body : Array Inst) : Bool := body.any fun i => match i.op with
    | .call (.func name ..) _ => panicMember? name == some "exactDivisionRemainder"
    | _ => false
  let mut out := #[]
  for i in insts do
    if let .condBr c _ elseBody := i.op then
      if callsExact elseBody then
        let cmp := match opOf c with
          | some (.reduce .and v) => v
          | _ => c
        if let some r := checked cmp then
          out := out.push r
  return out

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

/-- The profile's pointer width in bits (`Layout.ptrBytes`): 64, or 32 for wasm32. -/
def FCtx.ptrBits (fc : FCtx) : Nat := 8 * ptrBytesOf fc.layouts

/-- The 64-bit runtime name `name`, or its width-parameterized form (`ZigLean/Mem/Width.lean`)
for another pointer width. -/
def FCtx.widthFn (fc : FCtx) (name wide : String) : String :=
  if fc.ptrBits == 64 then name else wide

/-- The `Zig.PtrWidth` term of the profile. -/
def FCtx.ptrWidthTerm (fc : FCtx) : String := if fc.ptrBits == 64 then ".w64" else ".w32"

def FCtx.tyOfId (fc : FCtx) (tid : TyId) : Ty := fc.types[tid]!
def FCtx.emitTyOf (fc : FCtx) (tid : TyId) : String :=
  emitTy (ptrBits := fc.ptrBits) fc.structNames fc.types (fc.tyOfId tid) (pureSlice := !fc.mem)
def FCtx.storageExpr (fc : FCtx) (tid : TyId) (expr : String) : String :=
  withStorageEnc (ptrBits := fc.ptrBits) fc.structNames fc.types fc.errBits tid expr fc.layouts

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

/-- The profile targets aarch64 (`docs/floats.md` §Targets): `f80` is soft-float
(`Zig.Float.softF80Chk`, and in `compiler-rt` mode `__divxf3`), and `@mulAdd` on `f16`/`f32`/`f64`
is the fused instruction. A legacy profile (empty `targetArch`) and x86_64 keep the reference
x86_64 rules. -/
def FCtx.aarch64Floats (fc : FCtx) : Bool := fc.targetArch == "aarch64"

/-- Is `v` an `f80` or a vector of `f80`? -/
def FCtx.isF80Val (fc : FCtx) (v : Val) : Bool :=
  match fc.valTy v with
  | .float 80 => true
  | .vector _ c => fc.tyOfId c == .float 80
  | _ => false

/-- The `f80` operands that an op reads through a compiler_rt soft-float routine on aarch64:
every float op except the sign-bit ops (`neg`, `abs`) and the bit reinterpretations. Empty off
aarch64. -/
def FCtx.softF80Reads (fc : FCtx) (op : Op) : Array Val :=
  if !fc.aarch64Floats then #[] else
  let vals := match op with
    | .arith _ _ a b | .div _ a b | .divFloat a b | .minMax _ a b | .cmp _ a b => #[a, b]
    | .floatRound _ a | .sqrt a | .libm _ a | .floatConv a | .intFromFloat _ a | .reduce _ a => #[a]
    | .mulAdd a b c => #[a, b, c]
    | _ => #[]
  vals.filter fc.isF80Val

/-- `divRtSuffix` for a division of `a`: aarch64 `f80` in `compiler-rt` mode is `__divxf3`
(`Zig.Float.divXf3`, all versions). -/
def FCtx.floatDivSuffix (fc : FCtx) (a : Val) : String :=
  if fc.aarch64Floats && fc.rtSuffix != "" && fc.valTy a == .float 80 then "Xf3"
  else fc.divRtSuffix

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

/-- The term of the operand `v`. An `undefined` operand is outside the subset
(`checkUndefOperands`) and resolves to a `placeholder`, except under `undefFill`: the value of a
store whose undefined bytes are written separately (`undefByteRanges`), or that no read observes
(`deadUndefStores`), where `undefined` is filler (`0`, `false`, `default`). -/
partial def FCtx.resolveVal (fc : FCtx) (env : Array (InstId × String)) (v : Val)
    (undefFill : Bool := false) : String :=
  let resolve (v : Val) := fc.resolveVal env v undefFill
  match v with
  | .inst id => (env.find? (·.1 == id)).map (·.2) |>.getD (placeholder s!"unbound inst {id}")
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
    if !undefFill then placeholder "an `undefined` operand" else
    match fc.tyOfId tid with
    | .int _ b => s!"(0#{b})"
    | .bool => "false"
    | _ => "default"
  | .func name .. => (fc.funcNames.find? (·.1 == name)).map (·.2) |>.getD name
  | .optNull _ => "none"
  | .optSome _ v => s!"(some {resolve v})"
  | .err _ name => name.quote
  | .errUnionErr tid name => s!"(.error {name.quote} : {fc.emitTyOf tid})"
  | .errUnionOk tid p => s!"(.ok {resolve p} : {fc.emitTyOf tid})"
  | .enumTag tid v =>
    let e := fc.emitTyOf tid
    match fc.tyOfId tid with
    | .enum _ tag _ fields =>
      match fields.find? (·.2 == v) with
      | some (f, _) => s!"{e}.{fc.memberName (fc.tyOfId tid) f}"
      | none => s!"({e}.{fc.helperName (fc.tyOfId tid) "mk"} (BitVec.ofInt {fc.tyBits tag} ({v})))"
    | _ => placeholder "an enum constant of another type"
  | .unionVal tid idx p =>
    let u := fc.emitTyOf tid
    match fc.tyOfId tid with
    | .union _ layout none fields =>
      match fields[idx]? with
      | some (_, fty) =>
        fc.storageExpr fty (rawUnionInit u layout ((fc.layouts[tid]?.bind (·.size)).getD 0)
          (resolve p) (fc.emitTyOf fty))
      | none => placeholder "a union constant with no such field"
    | .union _ _ _ fields =>
      match fields[idx]? with
      | some (f, fty) =>
        if fc.tyOfId fty == .void then s!"{u}.{fc.memberName (fc.tyOfId tid) f}"
        else s!"({u}.{fc.memberName (fc.tyOfId tid) f} {resolve p})"
      | none => placeholder "a union constant with no such field"
    | _ => placeholder "a union constant of another type"
  | .agg tid elems =>
    let items (xs : Array Val) := ", ".intercalate (xs.map resolve).toList
    match fc.tyOfId tid with
    -- A sentinel is the last item of the value (`Ty.array`).
    | .array len _ s =>
      s!"(#v[{items (elems.extract 0 (len + if s then 1 else 0))}] : {fc.emitTyOf tid})"
    -- A vector has no sentinel (`docs/air-json.md`'s `elems`).
    | .vector len _ => s!"((⟨#v[{items (elems.extract 0 len)}]⟩) : {fc.emitTyOf tid})"
    | .struct _ _ fields =>
      let fm := fc.memberLookup (fc.tyOfId tid)
      let assigns := (fields.zip elems).toList.map fun ((f, _), e) =>
        s!"{fm f} := {resolve e}"
      s!"(\{ {", ".intercalate assigns} } : {fc.emitTyOf tid})"
    | .tuple _ => if elems.isEmpty then "()" else s!"({items elems})"
    | _ => placeholder "an aggregate constant of another type"
  | .ptrConst _ g off => s!"(⟨some {fc.globalIds[g]!}, {off}⟩ : Zig.Ptr)"
  | .ptrNull _ => "Zig.Ptr.null"
  | .ptrOther .. => placeholder "a pointer constant without a global"
  | .sliceConst _ p len => s!"(⟨{fc.resolveVal env p}, {fc.resolveVal env len}⟩ : {sliceTyName fc.ptrBits})"

def FCtx.resolveCallee (fc : FCtx) (v : Val) : Bool × String :=
  match v with
  | .func name noreturn .. =>
    (noreturn, (fc.funcNames.find? (·.1 == name)).map (·.2) |>.getD name)
  | _ => (false, placeholder "an indirect call")


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
  emitTy (ptrBits := fc.ptrBits) fc.structNames fc.types (fc.valTy v) (pureSlice := !fc.mem)

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

/-- Zig 0.17's logical-order `@bitCast` (`Air2Lean/BitCast.lean`, `ZigLean/BitCast.lean`) of
`a` (Lean value `av`) to `dst`: the source's logical bits, then the destination made from them,
as a `Zig.Result`. `none` outside that path: ≤0.16 input, identical types, or no array, vector,
enum or `void` on either side (the existing `bitcast` rules then apply). An exhaustive enum
result checks the tag (`Zig.enumOf`: `invalidEnumValue`, the check of 0.17's `bit_cast_safe`). -/
def FCtx.logicalBitCastExpr? (fc : FCtx) (a : Val) (dst : TyId) (av : String) : Option String := do
  let src ← fc.valTyId? a
  unless logicalBitCastApplies fc.zigVersion fc.types src dst do none
  let (s, d) ← (logicalBitCastShapes fc.types src dst).toOption
  -- An enum and exactly its tag type (`@intFromEnum`, `@enumFromInt`-style): the ≤0.16 text
  -- (`enumIntCast`) is already this cast, so 0.16 and 0.17 translations stay identical.
  let tagOf (t : TyId) : Option Ty := match fc.tyOfId t with
    | .enum _ tag _ _ => some (fc.tyOfId tag) | _ => none
  if tagOf src == some (fc.tyOfId dst) || tagOf dst == some (fc.tyOfId src) then none
  let dstTy := fc.emitTyOf dst
  let toBits (v : String) : String := match s with
    | .int _ => s!"pure ({v})"
    | .bool => s!"pure (if {v} then 1#1 else 0#1)"
    | .float _ => s!"Zig.Float.toBits? ({v})"
    | .packed _ => s!"pure (Zig.Packed.toBits ({v}))"
    | .enum .. => s!"pure ({fc.emitTyOf src}.{fc.helperName (fc.tyOfId src) "toBits"} ({v}))"
    | .intLanes true .. => s!"pure (Zig.BitCast.ofLanes ({v}).lanes)"
    | .intLanes false .. => s!"pure (Zig.BitCast.ofLanes ({v}))"
    | .boolLanes true _ => s!"pure (Zig.BitCast.ofBools ({v}).lanes)"
    | .boolLanes false _ => s!"pure (Zig.BitCast.ofBools ({v}))"
  let fromBits (b : String) : String := match d with
    | .int _ => s!"pure ({b})"
    | .bool => s!"pure ({b} == 1#1)"
    | .float _ => s!"pure (Zig.Float.ofBits ({b}))"
    | .packed _ => s!"Zig.Packed.ofBits? (α := {dstTy}) ({b})"
    | .enum _ signed =>
      s!"Zig.enumOf ({dstTy}.{fc.helperName (fc.tyOfId dst) "ofInt?"} (Zig.val {signed} ({b})))"
    | .intLanes true n w => s!"pure ⟨Zig.BitCast.toLanes (n := {n}) (w := {w}) ({b})⟩"
    | .intLanes false n w => s!"pure (Zig.BitCast.toLanes (n := {n}) (w := {w}) ({b}))"
    | .boolLanes true _ => s!"pure ⟨Zig.BitCast.toBools ({b})⟩"
    | .boolLanes false _ => s!"pure (Zig.BitCast.toBools ({b}))"
  -- An integer side needs no conversion; otherwise compose through `BitVec (bits)`.
  let body := match s, d with
    | .int _, _ => fromBits av
    | _, .int _ => toBits av
    | _, _ => s!"(({toBits av} : Zig.Result (BitVec {s.bits})) >>= fun bits => {fromBits "bits"})"
  pure s!"({body} : Zig.Result ({dstTy}))"

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
    | .alloc =>
      if fc.escaping.contains i.id || fc.byteLocals.contains i.id then acc
      else acc.push (i.id, i.id, #[])
    | .fieldPtr (.inst b) idx =>
      match acc.find? (·.1 == b) with
      | some (_, root, path) =>
        let base := fc.pointee b
        let step := match base with
          | .struct _ _ fields =>
            PathStep.field ((fields[idx]?).map (fc.memberName base ·.1) |>.getD s!"fld{idx}")
          | .union .. =>
            match fc.unionField? base idx with
            | some (u, f, _) =>
              let fresh := (unionFreshPayload fc.types base idx (fc.structNames.map (·.2))).map fun structFields =>
                (fc.helperName base s!"set_{f}",
                 structFields.map fun _ => fc.helperName base s!"setField_{f}")
              .ufield u (fc.helperName base s!"get_{f}") (fc.helperName base s!"modify_{f}") fresh
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

/-- Every place of a byte local, with its byte offset: the `alloc` at 0, a field pointer at the
field's offset (`byteLocalOk` admits only these). -/
def FCtx.computeBytePlaces (fc : FCtx) : Array (InstId × InstId × Nat) :=
  fc.allInsts.foldl (init := #[]) fun acc i =>
    match i.op with
    | .alloc => if fc.byteLocals.contains i.id then acc.push (i.id, i.id, 0) else acc
    | .fieldPtr (.inst b) idx =>
      match acc.find? (·.1 == b) with
      | some (_, root, off) =>
        let base := (ptrChild fc.types (fc.instTyId b)).getD 0
        acc.push (i.id, root, off + (structFieldOffset? fc.types fc.layouts base idx).getD 0)
      | none => acc
    | _ => acc

/-- A place of a byte local: its `Locals` field and byte offset. -/
def FCtx.bytePlace? (fc : FCtx) (v : Val) : Option (String × Nat) :=
  match v with
  | .inst id => do
    let (_, root, off) ← fc.bytePlaces.find? (·.1 == id)
    let (_, field) ← fc.allocFields.find? (·.1 == root)
    pure (field, off)
  | _ => none

def FCtx.isBytePlace (fc : FCtx) (v : Val) : Bool := (fc.bytePlace? v).isSome

/-- The Lean type of the value of `id`: `Zig.Bytes T` for a raw instruction. -/
def FCtx.instLeanTy (fc : FCtx) (id : InstId) : String :=
  let t := fc.emitTyOf (fc.instTyId id)
  if fc.rawInsts.contains id then s!"Zig.Bytes ({t})" else t

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
      | .ufield u g _ _ => s!"(← {fc.callRName} ({u}.{g} {e}))"
  | none => placeholder "load through a pointer that is not a place"

/-- `base` with the value `old` at `path` replaced by `new old`. -/
def setPath (path : List PathStep) (new : String → String) (base : String) : String :=
  match path with
  | [] => new base
  | .field f :: rest => s!"\{ {base} with {f} := {setPath rest new s!"({base}).{f}"} }"
  | .ufield u _ m fresh :: rest =>
    let inner := setPath rest new "x"
    let whole := inner == setPath rest new "y"
    let modify := s!"({u}.{m} (fun {if whole then "_" else "x"} => {inner}) {base})"
    -- A write that defines the whole payload, or one whole field of a struct payload, of a
    -- union whose retag leaves the payload undefined (MM-13).
    match fresh, rest with
    | none, _ => modify
    | some (set, _), _ =>
      if whole then s!"({u}.{set} ({inner}) {base})" else
      match fresh, rest with
      | some (_, some setField), [.field k] =>
        if new "a" == new "b" then s!"({u}.{setField} \"{k}\" (fun x => {inner}) {base})" else modify
      | _, _ => modify

/-- The statement that replaces the value `old` at a place by `new old`. -/
def FCtx.modifyPlace (fc : FCtx) (ptr : Val) (new : String → String) : String :=
  match fc.place? ptr with
  | some (field, path) =>
    s!"modify (fun s => \{ s with {field} := {setPath path.toList new s!"s.{field}"} })"
  | none => placeholder "store through a pointer that is not a place"

/-- The statement that writes `v` to a place. -/
def FCtx.storePlace (fc : FCtx) (ptr : Val) (v : String) : String :=
  fc.modifyPlace ptr fun _ => v

/-! ## Memory (`docs/generated-code.md` §Memory) -/

/-- The alignment of an access through the pointer `v`: its type's `align(N)`. -/
def FCtx.ptrAlign (fc : FCtx) (v : Val) : Nat :=
  ((fc.valTyId? v).bind fun t => fc.layouts[t]?.bind (·.ptrAlign)).getD 1

/-- The op that defines `v`, if `v` is an instruction. -/
def FCtx.opOf? (fc : FCtx) (v : Val) : Option Op :=
  match v with
  | .inst id => (fc.allInsts.find? (·.id == id)).map (·.op)
  | _ => none

/-- The alignment of the pointer type `tid`, or of an optional pointer's child. -/
def FCtx.ptrAlignOf (fc : FCtx) (tid : TyId) : Nat :=
  let t := match fc.tyOfId tid with | .optional c => c | _ => tid
  (fc.layouts[t]?.bind (·.ptrAlign)).getD 1

/-- `Zig.checkAddr … >>= fun _ => ` for `@ptrFromInt` of `n` to the pointer type `tid` (empty
if no address can be illegal): the prefix of the conversion it guards. -/
def FCtx.checkAddr (fc : FCtx) (tid : TyId) (nonNull : Bool) (n : String) : String :=
  let align := fc.ptrAlignOf tid
  if align ≤ 1 && !nonNull then "" else
  s!"Zig.checkAddr {align} {nonNull} ({n}).toNat >>= fun _ => "

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

/-- An atomic op through `ptr` on a pointer (`*T`, `?*T`): the pointer op (`Zig.atomicLoadPtrC`,
…, `ZigLean/Conc/PtrAtomic.lean`), whose message keeps the pointer's block. -/
def FCtx.atomicPtr (fc : FCtx) (ptr : Val) : Bool :=
  match fc.valTy ptr with
  | .ptr _ _ c => atomicPtrPointee fc.types fc.layouts c
  | _ => false

/-- The Lean type of the value that the pointer `v` points to. -/
def FCtx.pointeeTy (fc : FCtx) (v : Val) : String := emitTy (ptrBits := fc.ptrBits) fc.structNames fc.types (fc.pointeeOf v)

/-- The byte offset of field `idx` of the struct that the pointer `base` points to. `baseBit`:
the bit offset of `base` if it is a bit-pointer (its address is its host's). -/
def FCtx.fieldOffsetIn (fc : FCtx) (c : TyId) (idx : Nat) (baseBit : Nat := 0) : Nat :=
  match fc.tyOfId c with
  -- A byte-aligned field of a packed struct that is a whole number of bytes: its pointer is
  -- not a bit-pointer, at its byte in the host (`Check.lean`'s `packedFieldPtr?`).
  | .struct _ "packed" fields => (baseBit + packedFieldBit fc.types fields idx) / 8
  -- Every field of a tagged union is its payload.
  | .union _ _ (some tag) fields =>
    ((unionOffsets fc.types fc.layouts tag (fields.map (·.2)) fc.errBits).map (·.2)).getD 0
  -- Every field of an `extern` or `packed` union is at offset 0.
  | .union _ _ none _ => 0
  | _ => (fc.layouts[c]?.bind (·.offsets[idx]?)).getD 0

/-- A bit-pointer type's host integer size in bytes; 0 for every other type. -/
def FCtx.hostSize (fc : FCtx) (ptrTy : TyId) : Nat := (fc.layouts[ptrTy]?.map (·.hostSize)).getD 0

/-- The bit-pointer access `name` (`ZigLean/Packed.lean`), or its byte-order form at `.big`
(`ZigLean/Endian.lean`) for a big-endian profile. -/
def FCtx.bitsFn (fc : FCtx) (name : String) : String :=
  if fc.bigEndian then s!"Zig.{name}Of .big" else s!"Zig.{name}"

/-- A bit-pointer type's bit offset in its host; 0 for every other type. -/
def FCtx.bitOffset (fc : FCtx) (ptrTy : TyId) : Nat := (fc.layouts[ptrTy]?.map (·.bitPtrOffset)).getD 0

def FCtx.fieldOffset (fc : FCtx) (base : Val) (idx : Nat) : Nat :=
  match fc.valTy base with
  | .ptr _ _ c => fc.fieldOffsetIn c idx (((fc.valTyId? base).map fc.bitOffset).getD 0)
  | _ => 0

/-- `ptrTy` is a lane pointer into a bit-packed vector (`Layout.laneBitPtr`). -/
def FCtx.laneBitPtr (fc : FCtx) (ptrTy : TyId) : Bool := laneBitPtrTy fc.layouts ptrTy

/-- The byte offset of field `idx` of the struct that the pointer type `ptrTy` points to
(`field_parent_ptr`'s own result type, unlike `fieldOffset`'s operand type). -/
def FCtx.fieldOffsetOfPtrTy (fc : FCtx) (ptrTy : TyId) (idx : Nat) : Nat :=
  match fc.tyOfId ptrTy with
  | .ptr _ _ c => fc.fieldOffsetIn c idx (fc.bitOffset ptrTy)
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
    | .array len .. | .vector len _ => (rv, s!"({len} : BitVec {fc.ptrBits})")
    | _ => (rv, placeholder "items of a pointer without a length")

/-- `v` is a pointer to memory: not a place. -/
def FCtx.isMemPtr (fc : FCtx) (v : Val) : Bool :=
  !fc.isPlace v && !fc.isBytePlace v && match fc.valTy v with | .ptr .. => true | _ => false

/-- `v`'s type is a C/allowzero pointer (address zero is a value). -/
def FCtx.nullableVal (fc : FCtx) (v : Val) : Bool :=
  (fc.valTyId? v |>.map (nullablePtrTy fc.types fc.layouts)).getD false

/-- `t` is an ordinary optional single/many pointer (`?*T`, `?[*]T`), `Option Zig.Ptr`. -/
def FCtx.isOptScalarPtr (fc : FCtx) (t : Ty) : Bool := optScalarPtr fc.types t

/-- A derived pointer: the projection `project` (a `Ptr → Ptr` term such as `·.add off`,
`·.elem size i`, `·.elemSub size i`) of the pointer `base`, whose term is `p`, with result type `result`. It is
`Zig.ptrProject` (`getelementptr inbounds`: `.illegal` unless base and result are in bounds of
the base's block; MM-3), and the base itself for a constant offset 0 (`zero`; no instruction
natively). From a C/allowzero base whose result the compiler types as a nonnullable pointer
(Zig ≤0.15 `struct_field_ptr`) it is `Zig.ptrProjectNonnull`: address zero is also illegal. -/
def FCtx.projectExpr (fc : FCtx) (base : Val) (result : TyId) (p project : String)
    (zero : Bool := false) : String :=
  if fc.nullableVal base && !nullablePtrTy fc.types fc.layouts result then
    s!"{fc.callMName} (Zig.ptrProjectNonnull {p} ({project}))"
  else if zero then s!"pure {p}"
  else s!"{fc.callMName} (Zig.ptrProject {p} ({project}))"

/-- Bind the exact pointee's dictionary at a memory boundary. -/
def FCtx.pointeeStorageExpr (fc : FCtx) (ptr : Val) (expr : String) : String :=
  match (fc.valTyId? ptr).bind (ptrChild fc.types) with
  | some tid => fc.storageExpr tid expr
  | none => expr

/-- `v` is a volatile pointer (L13: a device access with `--device-contract`). -/
def FCtx.isVolatileVal (fc : FCtx) (v : Val) : Bool :=
  (fc.valTyId? v |>.map (volatilePtrTy fc.types fc.layouts)).getD false

/-- The bit width of `ptr`'s integer pointee (a device register access). -/
def FCtx.pointeeBits (fc : FCtx) (ptr : Val) : Nat :=
  ((fc.valTyId? ptr).bind (ptrChild fc.types)).map fc.tyBits |>.getD 0

/-- A load through a pointer to memory. -/
def FCtx.loadMem (fc : FCtx) (ptr : Val) (p : String) : String :=
  match fc.valTyId? ptr with
  | some t =>
    if fc.hostSize t != 0 then
      let f := if fc.laneBitPtr t then "Zig.loadLane" else fc.bitsFn "loadBits"
      s!"{f} ({fc.pointeeTy ptr}) {fc.hostSize t} {fc.ptrAlign ptr} \
        {fc.bitOffset t} {p}"
    else fc.pointeeStorageExpr ptr s!"Zig.load ({fc.pointeeTy ptr}) {fc.ptrAlign ptr} {p}"
  | none => s!"Zig.load ({fc.pointeeTy ptr}) {fc.ptrAlign ptr} {p}"

/-- A use of the instruction `x` that takes its value as `Zig.Bytes T`: a `struct_field_val` of a
non-`packed` struct (`Zig.Bytes.get` decodes only the field), a store to memory (`Zig.storeBytes`)
or to a byte local (`Zig.Bytes.copy`) of the same type, a `ret` of a function that can return
`Zig.Bytes T` (`canRet`), and `dbg`. -/
def FCtx.rawUseOk (fc : FCtx) (canRet : Bool) (x : InstId) (u : Inst) : Bool :=
  let xty := fc.instTyId x
  match u.op with
  | .structFieldVal (.inst y) k => y == x && (structFieldOffset? fc.types fc.layouts xty k).isSome
  | .store p (.inst y) =>
    y == x && p != .inst x &&
      (fc.isBytePlace p || (fc.isMemPtr p && ((fc.valTyId? p).map fc.hostSize).getD 0 == 0)) &&
      ((fc.valTyId? p).bind (ptrChild fc.types)).any (fun c => fc.tyOfId c == fc.tyOfId xty)
  | .ret (.inst y) => canRet && y == x
  | .dbg .. => true
  | _ => false

/-- The instructions whose value is `Zig.Bytes T`, not decoded: a load of a whole byte local and a
call of a function in `rawFuncs`, if each of their uses is a `rawUseOk`. `canRet`: this function
can return `Zig.Bytes T` (`rawFunctions`). -/
def FCtx.computeRawInsts (fc : FCtx) (canRet : Bool) : Array InstId :=
  fc.allInsts.filterMap fun i =>
    let candidate := match i.op with
      | .load (.inst a) => fc.byteLocals.contains a
      | .call (.func name ..) _ => fc.rawFuncs.contains name
      | _ => false
    if candidate && fc.allInsts.all (fun u =>
        !(placeOperands u.op).contains (.inst i.id) || fc.rawUseOk canRet i.id u)
    then some i.id else none

/-- A call argument. A pure callee gets the items of a `[]const T` argument (`Zig.readSlice`). -/
def FCtx.callArg (fc : FCtx) (env : Array (InstId × String)) (memCallee : Bool) (a : Val) : String :=
  if fc.mem && !memCallee && fc.isSlice a then
    let item := emitTy (ptrBits := fc.ptrBits) fc.structNames fc.types (fc.tyOfId (fc.itemTyId a))
    s!"(← {fc.callMName} ({fc.storageExpr (fc.itemTyId a) s!"{fc.widthFn "Zig.readSlice" "Zig.readSliceOf"} ({item}) {fc.itemAlign a} {fc.resolveVal env a}"}))"
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
  -- `Check.lean` admits only create, alloc, alignedAlloc, destroy and free for a 32-bit profile.
  | .create =>
    if fc.ptrBits == 64 then s!"Zig.Allocator.create {a} {size} {align}"
    else s!"Zig.Allocator.createOf {fc.ptrWidthTerm} {a} {size} {align}"
  | .alloc | .alignedAlloc =>
    if fc.ptrBits == 64 then s!"Zig.Allocator.alloc {a} {size} {align} {rv (arg 1)}"
    else s!"Zig.Allocator.allocOf {fc.ptrWidthTerm} {a} {size} {align} {rv (arg 1)}"
  | .allocSentinel =>
    let sentinel := (fc.layouts[p]?.bind (·.sentinelByte)).getD 0
    s!"Zig.Allocator.allocSentinel {a} {rv (arg 1)} ({sentinel}#8)"
  | .dupe => s!"Zig.Allocator.dupe {a} {size} {align} {fc.ptrAlign (arg 1)} {rv (arg 1)}"
  | .destroy => s!"Zig.Allocator.destroy {a} {argSize} {rv (arg 1)}"
  | .free =>
    let sentinel := ((fc.valTyId? (arg 1)).bind (fc.layouts[·]?) |>.map (·.sentinel)).getD false
    s!"Zig.Allocator.{if sentinel then "freeSentinel" else fc.widthFn "free" "freeOf"} {a} {argSize} {rv (arg 1)}"
  | .remap => s!"Zig.Allocator.remap {a} {argSize} {rv (arg 1)} {rv (arg 2)}"
  | .realloc => s!"Zig.Allocator.realloc {a} {rv (arg 1)} {rv (arg 2)}"

/-- The `Tgt` constructor of the `Io.async` task of the worker with generated name `worker`. -/
def futureCtorName (worker : String) : String := s!"{worker}_future"

/-- The `spawnFallbacks` key of the caller's eager execution of an `Io.async` task. -/
def futureEagerKey (worker : String) : String := s!"future:{worker}"

/-- A sync op of the thread model (`ZigLean/Conc/Call.lean`), a `Zig.CM Tgt` term. `.spawn`:
`callee`'s `spawnFn` (its `comptime_fn`) names the spawned function, a constructor of the
program's `Tgt` (`emitTgt`); `args[1]` is the complete by-value captured tuple. Zero
fields use `Unit`, one field keeps the historical scalar representation, and multiple
fields form a right-associated product. Dispatch applies each field in source order. `.join`, `.detach`: `args[0]` is the `Thread` handle. -/
def FCtx.threadCall (fc : FCtx) (env : Array (InstId × String)) (fn : ThreadFn) (callee : Val)
    (args : Array Val) (ret : TyId := 0) : String :=
  let rv := fc.resolveVal env
  match fn with
  | .spawn =>
    let spawnFn := match callee with | .func _ _ sf => sf.getD "" | _ => ""
    let target := (fc.funcNames.find? (·.1 == spawnFn)).map (·.2) |>.getD spawnFn
    let op := if fc.spawnSemantics == .fallible then "spawnWithPolicyC .fallible" else "spawnC"
    s!"Zig.{op} (Tgt.{target} {rv (args[1]?.getD .void)})"
  | .join => s!"Zig.joinC {rv (args[0]?.getD .void)}"
  | .detach => s!"Zig.detachC {rv (args[0]?.getD .void)}"
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
  | .timerStart | .timerRead | .futexTimedWait => "Zig.callRC (throw Zig.Error.unsupportedTimer)"
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
  -- `Io.async(io, args)`: the task is `callee`'s `spawnFn`, its target `Tgt.<worker>_future`
  -- (`emitTgtWithStorage`); `ret` is the `Io.Future(T)` type (`docs/futures.md`).
  | .futureAsync =>
    let spawnFn := match callee with | .func _ _ sf => sf.getD "" | _ => ""
    let target := (fc.funcNames.find? (·.1 == spawnFn)).map (·.2) |>.getD spawnFn
    let capture := rv (args[1]?.getD .void)
    let result := match fc.tyOfId ret with | .future r => r | _ => ret
    let resultTy := fc.emitTyOf result
    let mk := s!"(fun futureSlot => Tgt.{futureCtorName target} futureSlot {capture})"
    let call := if fc.spawnSemantics == .fallible then
      s!"Zig.asyncWithPolicyC (α := {resultTy}) .fallible {mk} \
        (({fc.spawnFallback (futureEagerKey spawnFn)}) {capture})"
      else s!"Zig.asyncC (α := {resultTy}) {mk}"
    fc.storageExpr result call
  -- `Future(T).await(&f, io)`, `.cancel(&f, io)`: `ret` is `T`.
  | .futureAwait | .futureCancel =>
    let op := if fn == .futureAwait then "awaitC" else "cancelC"
    fc.storageExpr ret s!"Zig.{op} (α := {fc.emitTyOf ret}) {rv (args[1]?.getD .void)} \
      {rv (args[0]?.getD .void)}"
  | .checkCancel => s!"Zig.checkCancelC {rv (args[0]?.getD .void)}"

/-- A load of item `i` of the slice, many-pointer or array pointer `v`, whose item pointer is
`p`. -/
def FCtx.loadItem (fc : FCtx) (v : Val) (p i : String) : String :=
  let item := fc.itemTyId v
  -- L13 device mode: a volatile item read is one device event.
  if fc.isVolatileVal v then
    s!"Zig.vload {deviceDefName} {fc.tyBits item} {fc.itemAlign v} ({p}.{fc.widthFn "elem" "elemOf"} {fc.sizeOf item} {i})"
  else
  fc.storageExpr item s!"Zig.load ({emitTy (ptrBits := fc.ptrBits) fc.structNames fc.types (fc.tyOfId item)}) {fc.itemAlign v} \
    ({p}.{fc.widthFn "elem" "elemOf"} {fc.sizeOf item} {i})"

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
    (mem : Bool) (dispatches : Array (InstId × Ty) := #[]) (byteLocals : Array InstId := #[])
    (ptrBits : Nat := 64) : String :=
  let emitTy (structNames : Array (String × String)) (types : Array Ty) (ty : Ty) (pureSlice : Bool) :=
    emitTy structNames types ty pureSlice ptrBits
  let lines := (allocs.map fun (aid, nm, cty) =>
    if escaping.contains aid then s!"  {nm} : Zig.Ptr"
    else if byteLocals.contains aid then
      s!"  {nm} : Zig.Bytes ({emitTy structNames types types[cty]! (pureSlice := !mem)})"
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
    (mem : Bool) (dispatches : Array (InstId × Ty) := #[]) (rawRet : Bool := false)
    (ptrBits : Nat := 64) : String :=
  let emitTy (structNames : Array (String × String)) (types : Array Ty) (ty : Ty) (pureSlice : Bool) :=
    emitTy structNames types ty pureSlice ptrBits
  let retLine := match types[retTy]! with
    | .void => "  | ret"
    | rt =>
      let t := emitTy structNames types rt (pureSlice := !mem)
      s!"  | ret (v : {if rawRet then s!"Zig.Bytes ({t})" else t})"
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
  | .alloc | .runtimeNavPtr _ => #[]
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
  | .memset a b | .memcpy _ a b => #[a, b]
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

/-- A multi-operand `for` loop without safety: Sema still computes each operand's `slice_len`,
but only the loop's own length bounds the loop (`cmp_lt(bitcast(i), bitcast(bound))`). A
`slice_len` that nothing reads, followed by such a loop, is an operand whose length must equal
`bound` (`Zig.forLen`). With safety, Sema's `forLenMismatch` check reads every length. -/
def FCtx.forLenBound? (fc : FCtx) (id : InstId) : Option Val := do
  guard (!fc.isReferenced id)
  let after := fc.allInsts.filter (·.id > id)
  let cmp ← after.findSome? fun i => match i.op with
    | .cmp .lt (.inst idx) b => match fc.opOf? (.inst idx), b with
      | some (.bitcast _), .inst _ => match fc.opOf? b with
        | some (.bitcast bound) => some bound
        | _ => none
      -- A comptime-known first length (an array operand).
      | some (.bitcast _), .int .. => some b
      | _, _ => none
    | _ => none
  -- The bound must already be in scope at the `slice_len`.
  let inScope : Bool := match cmp with | .inst b => decide (b < id) | _ => true
  guard inScope
  pure cmp

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
    (id, name, fc.instLeanTy id)

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
  /-- The width of each read-write (`+r`, `+m`) output, in output order: the opaque's trailing
  parameters, the old values (A01). Empty for a register-only op. -/
  rwWidths : Array Nat := #[]
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
def asmHash (key : String) : UInt32 :=
  key.foldl (init := (0x811c9dc5 : UInt32)) fun h c => (h ^^^ c.val) * 0x01000193

def asmDefName (key : String) : String := s!"airAsm_{asmHash key}"

/-- The opaque's name for an op with these clobbers and outputs: `airAsmFx_<hash>` for an op under
the effect contract (`asmIsEffect`: a read-write or memory output, or a registry-approved
`"memory"` clobber; premise ASM-03), else `airAsm_<hash>` (register-only, ASM-01). Same hash. -/
def asmOpName (clobbers : Array String) (outputs : Array AsmOperand) (key : String) : String :=
  if asmIsEffect clobbers outputs then s!"airAsmFx_{asmHash key}" else asmDefName key

/-- The widths of the read-write outputs, in output order (`AsmDef.rwWidths`). -/
def asmRwWidths (outputs : Array AsmOperand) (outputWidths : Array Nat) : Array Nat :=
  (outputs.zip outputWidths).filterMap fun (o, w) => if o.isReadWrite then some w else none

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
      if i.op.isSpinHint || i.op.isDeviceAsm f.targetArch then continue
      if let .asm source _ clobbers outputs inputs := i.op then
        let inputWidths := inputs.map fun o => asmValBits f o.ref.get!
        let tyOf (v : Val) : Option TyId := match v with
          | .inst id => (f.allInsts.find? (·.id == id)).map (·.ty)
          | v => v.constTy?
        let outputWidths := asmOutputWidths f.types tyOf i.ty outputs
        let constraints := outputs.map (·.constraint) ++ inputs.map (·.constraint)
        let key := asmKey source constraints inputWidths outputWidths
        -- The key omits clobbers, so one key can name both forms (`asm volatile ("")` and the
        -- registry's `"memory"` barrier): deduplicate by name and key.
        let name := asmOpName clobbers outputs key
        if !seen.contains (name ++ "\u0002" ++ key) then
          seen := seen.push (name ++ "\u0002" ++ key)
          defs := defs.push { name, inputWidths, outputWidths,
                              rwWidths := asmRwWidths outputs outputWidths }
  return defs

/-- The `opaque` def for one distinct asm op: an uninterpreted function from its inputs' `BitVec`s
to its output's `BitVec` (`Unit` for no output; a tuple in output order for more than one). A proof can use only what the caller states
about it — no built-in axiom describes what any asm op computes (`Air2Lean/Air/Op.lean`'s `.asm`
doc comment). -/
def emitAsmDef (d : AsmDef) : String :=
  let params := ((d.inputWidths ++ d.rwWidths).toList.zipIdx.map fun (w, k) => s!"(i{k} : BitVec {w})")
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
output line. `emitSimple` lifts it to vectors; `emitScalarGuarded` adds the aarch64 `f80`
guard. -/
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
          if fc.exactFloatDivs.contains inst.id then
            -- `@divExact` with safety: an inexact non-NaN quotient is `.illegal`.
            s!"Zig.Float.divExactTrunc {rv a} {rv b} (Zig.Float.div{fc.floatDivSuffix a} {rv a} {rv b})"
          else
            let f := s!"Zig.Float.divTrunc{fc.floatDivSuffix a}"
            s!"pure ({f} {rv a} {rv b})"
        | .divFloor =>
          let f := s!"Zig.Float.divFloor{fc.floatDivSuffix a}"
          s!"pure ({f} {rv a} {rv b})"
        | .divCeil =>
          let f := s!"Zig.Float.divCeil{fc.floatDivSuffix a}"
          s!"pure ({f} {rv a} {rv b})"
        | .divExact =>
          -- `div_exact` (no safety): every inexact quotient, NaN included, is `.illegal`.
          s!"Zig.Float.divExactChk {rv a} {rv b} (Zig.Float.div{fc.floatDivSuffix a} {rv a} {rv b})"
        | .rem => s!"Zig.Float.rem{fc.rtSuffix}Chk {rv a} {rv b}"
        | .mod => s!"Zig.Float.mod{fc.rtSuffix}Chk {rv a} {rv b}"
      else
        let sgn := if fc.valSigned a then "true" else "false"
        let f := match op with
          | .divTrunc => "Zig.divTrunc" | .divFloor => "Zig.divFloor" | .divExact => "Zig.divExact"
          | .divCeil => "Zig.divCeil"
          | .rem => "Zig.rem" | .mod => "Zig.mod"
        s!"{f} {sgn} {rv a} {rv b}"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .divFloat a b =>
    -- `div_float` (plain `/` on floats): group A's guard, the same divide as `.divExact`.
    let f := s!"Zig.Float.div{fc.floatDivSuffix a}"
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
          placeholder "bitwise @reduce of a float vector"
      else if fc.tyOfId child == .bool then
        -- A `bool` vector: the safety checks of a vector op (`cmp_vector`, then `reduce .Or`).
        match op with
        | .and => s!"pure (Zig.Vec.reduce (· && ·) {rv a})"
        | .or => s!"pure (Zig.Vec.reduce (· || ·) {rv a})"
        | .xor => s!"pure (Zig.Vec.reduce (· ^^ ·) {rv a})"
        | _ => placeholder "arithmetic @reduce of a bool vector"
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
        | none => placeholder "shuffle mask reads 'b' with no second source"
      | .undef => placeholder "an `undefined` shuffle lane"
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
    -- The count of a width that is not a power of two can reach the width: illegal behaviour
    -- that only a safety check (rejected `shiftRhsTooBig`) would catch (`Zig.shiftCountOk`).
    let countChecked := match fc.valTy a, b with
      | .int _ w, .int _ k => k < w || k == 0
      | .int _ w, _ => w &&& (w - 1) == 0  -- a power of two (or `u0`)
      | _, _ => true
    let expr := match op with
      | .shl => if countChecked then s!"pure (Zig.shl {rv a} {rv b})" else s!"Zig.shlChk {rv a} {rv b}"
      | .shr =>
        if countChecked then s!"pure (Zig.shr {sgn} {rv a} {rv b})" else s!"Zig.shrChk {sgn} {rv a} {rv b}"
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
    -- `==` on pointers of every kind compares the addresses (`Zig.ptrEqAddr`, MM-4), also for
    -- optional pointers (`Zig.optPtrEqAddr`): two pointers with different provenance can have
    -- the same address.
    let addrPtr (t : Ty) := match t with
      | .ptr "slice" .. => false
      | .ptr .. => true
      | _ => false
    let optAddrPtr (t : Ty) := match t with | .optional c => addrPtr (fc.tyOfId c) | _ => false
    let eqFn := if addrPtr (fc.valTy a) || addrPtr (fc.valTy b) then some "Zig.ptrEqAddr"
      else if optAddrPtr (fc.valTy a) || optAddrPtr (fc.valTy b) then some "Zig.optPtrEqAddr"
      else none
    let expr := match ptrOrder, op, eqFn with
      | some e, _, _ => s!"{fc.callMName} ({e})"
      | none, .eq, some f => s!"{fc.callMName} ({f} {rv a} {rv b})"
      | none, .ne, some f => s!"{fc.callMName} (do pure (!(← {f} {rv a} {rv b})))"
      | none, _, _ => s!"pure ({expr})"
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
    if let some expr := fc.logicalBitCastExpr? a inst.ty (rv a) then
      let (env, l) := bindLet fc env inst.id expr; (env, some l)
    else
    if (fc.valTyId? a).any (reprCastApplies fc.zigVersion fc.types · inst.ty) then
      -- Zig ≤0.16 `@bitCast` of an array, `extern` struct or `extern` union: the memory bytes
      -- reinterpreted (`Zig.reprCast`, padding bytes undefined; `docs/aggregate-casts.md`).
      let (env, l) := bindLet fc env inst.id
        s!"Zig.reprCast ({fc.emitTyOf inst.ty}) ({rv a} : {fc.emitValTy a})"
      (env, some l)
    else
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
      let expr := if fc.ptrBits == 64 || fc.tyBits inst.ty != fc.ptrBits then
          s!"{fc.callMName} (do pure (BitVec.ofInt {fc.tyBits inst.ty} (← Zig.ptrAddr {rv a})))"
        -- The address must fit the target's address space (`Zig.ptrAddrOf`).
        else s!"{fc.callMName} (Zig.ptrAddrOf {fc.ptrWidthTerm} {rv a})"
      let (env, l) := bindLet fc env inst.id expr; (env, some l)
    else if isInt (fc.valTy a) && dstPtr then
      -- `@ptrFromInt`, after its own address check (`Zig.checkAddr`).
      let nullable := nullablePtrTy fc.types fc.layouts inst.ty
      let fromAddr := if nullable then "Zig.ptrFromAddrNullable" else "Zig.ptrFromAddr"
      let expr := s!"{fc.callMName} ({fc.checkAddr inst.ty (!nullable) (rv a)}{fromAddr} ({rv a}).toNat)"
      let (env, l) := bindLet fc env inst.id expr; (env, some l)
    else if srcPtr && fc.nullableVal a && fc.isOptScalarPtr (fc.tyOfId inst.ty) then
      -- A C/allowzero pointer to `?*T`: address zero is the explicit `none`.
      let (env, l) := bindLet fc env inst.id s!"{fc.callMName} (Zig.ptrToOptional {rv a})"
      (env, some l)
    else if dstPtr && nullablePtrTy fc.types fc.layouts inst.ty && fc.isOptScalarPtr (fc.valTy a) then
      -- `?*T` to a C/allowzero pointer: `none` is address zero.
      let (env, l) := bindLet fc env inst.id s!"pure (Zig.ptrOfOptional {rv a})"
      (env, some l)
    else
    let srcOptPtr := (fc.valTyId? a).any (optSinglePtrTy fc.types fc.layouts)
    if srcOptPtr && dstPtr then
      -- `?*T` → `*U`: unwrap, null throws (`ZigLean/Mem/Repr.lean`).
      let (env, l) := bindLet fc env inst.id s!"Zig.optPtrUnwrap {rv a}"
      (env, some l)
    else if srcOptPtr && isInt (fc.tyOfId inst.ty) then
      -- `@intFromPtr` of `?*T`: null is 0.
      let expr := s!"{fc.callMName} (do pure (BitVec.ofInt {fc.tyBits inst.ty} (← Zig.optPtrAddr {rv a})))"
      let (env, l) := bindLet fc env inst.id expr; (env, some l)
    else if isInt (fc.valTy a) && optSinglePtrTy fc.types fc.layouts inst.ty then
      -- `@ptrFromInt` to `?*T`: 0 is null.
      let expr := s!"{fc.callMName} ({fc.checkAddr inst.ty false (rv a)}Zig.optPtrFromAddr ({rv a}).toNat)"
      let (env, l) := bindLet fc env inst.id expr; (env, some l)
    else if srcPtr && dstPtr && fc.nullableVal a &&
        !(nullablePtrTy fc.types fc.layouts inst.ty) then
      let (env, l) := bindLet fc env inst.id s!"{fc.callMName} (Zig.ptrRequireNonNull {rv a})"
      (env, some l)
    else
    -- `@errorCast` to a set that lacks some source error checks its error itself.
    let narrowedTo : Option (Array String) := match fc.valTy a, fc.tyOfId inst.ty with
      | .errorSet src, .errorSet (some dst) => if src.any (·.all dst.contains) then none else some dst
      | _, _ => none
    if let some dst := narrowedTo then
      let names := ", ".intercalate (dst.toList.map fun n => (repr n).pretty)
      let (env, l) := bindLet fc env inst.id s!"Zig.errorIn [{names}] {rv a}"; (env, some l)
    else
    let srcFloat := fc.isFloat a
    let dstFloat := fc.isFloatTy inst.ty
    let expr :=
      if srcFloat && !dstFloat then s!"Zig.Float.toBits? {rv a}"
      else if !srcFloat && dstFloat then s!"pure ((Zig.Float.ofBits {rv a}) : {fc.emitTyOf inst.ty})"
      else if srcPtr && dstPtr && fc.isMemPtr a && fc.ptrAlignOf inst.ty > fc.ptrAlign a then
        -- `@alignCast` to a stricter alignment checks its pointer itself (`Zig.checkAlign`).
        s!"{fc.callMName} (Zig.checkAlign {fc.ptrAlignOf inst.ty} {rv a} >>= fun _ => pure {rv a})"
      else s!"pure ({rv a})"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .floatRound op a =>
    -- Only f80's legacy extension changes rounding; vector lanes carry their scalar type here.
    let legacyRt := fc.zigBefore016 && fc.floatSemantics == .compilerRt &&
      fc.tyOfId inst.ty == .float 80
    -- Zig 0.17.0's f80 `@trunc` keeps a pseudo-denormal whose f128 extension is zero.
    let trunc017 := fc.zigVersion == "0.17.0" && fc.floatSemantics == .compilerRt &&
      fc.tyOfId inst.ty == .float 80
    let f := match op with
      | .floor => if legacyRt then "Zig.Float.floorRtLegacyChk" else "Zig.Float.floorChk"
      | .ceil => if legacyRt then "Zig.Float.ceilRtLegacyChk" else "Zig.Float.ceilChk"
      | .trunc => if trunc017 then "Zig.Float.truncRt017Chk" else "Zig.Float.truncChk"
      | .round => "Zig.Float.roundChk"
    let (env, l) := bindLet fc env inst.id s!"{f} {rv a}"; (env, some l)
  | .sqrt a =>
    let f := if fc.zigBefore016 && fc.valTy a == .float 128 then "Zig.Float.sqrtF128ViaF64"
      else if fc.zigBefore016 && fc.aarch64Floats && fc.valTy a == .float 80 then
        "Zig.Float.sqrtF80ViaF64"
      else "Zig.Float.sqrt"
    let (env, l) := bindLet fc env inst.id s!"pure ({f} {rv a})"; (env, some l)
  | .libm op a =>
    let opName := match op with
      | .sin => ".sin" | .cos => ".cos" | .tan => ".tan" | .exp => ".exp"
      | .exp2 => ".exp2" | .log => ".log" | .log2 => ".log2" | .log10 => ".log10"
    let (env, l) := bindLet fc env inst.id s!"pure (Zig.Float.libm {opName} {rv a})"; (env, some l)
  | .mulAdd a b c =>
    -- Group C's guard applies in both modes; group B's dispatch picks `fma` vs `fmaRt` under it.
    -- aarch64: a fused instruction; its f80 operands are guarded by `softF80Chk` instead.
    let expr := if fc.aarch64Floats then s!"pure (Zig.Float.fma{fc.rtSuffix}Fused {rv a} {rv b} {rv c})"
      else s!"Zig.Float.fma{fc.rtSuffix}Chk {rv a} {rv b} {rv c}"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
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
        | .errorSet (some names) => s!"{errOp fc.errBits "optionalErrorIsSome"} {emitErrorDomain names} {fc.ptrAlign p} {rv p}"
        | ct => fc.storageExpr c s!"Zig.optIsSome ({emitTy (ptrBits := fc.ptrBits) fc.structNames fc.types ct}) {rv p}"
      | _ => placeholder "is_null_ptr of a non-optional"
    let expr := if isNull then s!"(!·) <$> {some'}" else some'
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .optPayloadPtr set p =>
    let expr := match set, fc.pointeeOf p with
      | true, .optional c =>
        match fc.tyOfId c with
        | .ptr .. | .errorSet _ => s!"pure {rv p}"
        | ct => fc.storageExpr c s!"Zig.optSetSome ({emitTy (ptrBits := fc.ptrBits) fc.structNames fc.types ct}) {rv p}"
      | _, _ => s!"pure {rv p}"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .isErrPtr _ p | .errPayloadPtr _ p | .errCodePtr p =>
    -- `Zig.errIsErrAt` & co. (`ZigLean/Mem/Enc.lean`) take the payload type.
    let payload := match fc.pointeeOf p with
      | .errorUnion _ c => emitTy (ptrBits := fc.ptrBits) fc.structNames fc.types (fc.tyOfId c)
      | _ => placeholder "an error-union pointer op on another type"
    let a := fc.ptrAlign p
    let domain := match fc.pointeeOf p with
      | .errorUnion set _ => match fc.tyOfId set with
        | .errorSet (some names) => some (emitErrorDomain names)
        | _ => none
      | _ => none
    let isErr := match domain with
      | some d => s!"{errOp fc.errBits "finiteErrIsErrAt"} {d}"
      | none => errOp fc.errBits "errIsErrAt"
    let code := match domain with
      | some d => s!"{errOp fc.errBits "finiteErrCodeAt"} {d}"
      | none => errOp fc.errBits "errCodeAt"
    let expr := match inst.op with
      | .isErrPtr true _ => s!"{isErr} ({payload}) {a} {rv p}"
      | .isErrPtr false _ => s!"(!·) <$> {isErr} ({payload}) {a} {rv p}"
      | .errPayloadPtr true _ => s!"{errOp fc.errBits "errSetOk"} ({payload}) {a} {rv p}"
      | .errPayloadPtr false _ =>
        fc.projectExpr p inst.ty (rv p) s!"{errOp fc.errBits "errPayloadPtr"} ({payload})"
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
      | _, none => placeholder "union_init of a non-union type"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .runtimeNavPtr g =>
    -- The current thread's instance of the `threadlocal` global whose key (the block of the
    -- main thread's instance) is `globalIds[g]` (§Thread-local storage).
    let (env, l) := bindLet fc env inst.id s!"Zig.tlsPtr {fc.globalIds[g]!}"; (env, some l)
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
      let (env, l) := bindLet fc env inst.id
        (fc.projectExpr base inst.ty (rv base) s!"·.add {off}" (zero := off == 0))
      (env, some l)
    else (env, none)
  | .fieldParentPtr fieldPtr idx =>
    if fc.isMemPtr fieldPtr then
      -- A bit-pointer points to the host integer: the parent's own address.
      let bitPtr := ((fc.valTyId? fieldPtr).map fc.hostSize).getD 0 != 0
      let off := if bitPtr then 0 else fc.fieldOffsetOfPtrTy inst.ty idx
      let q := fc.projectExpr fieldPtr inst.ty (rv fieldPtr) s!"·.add (-({off} : Int))" (zero := off == 0)
      -- A parent with no defined layout must be a live, aligned object at `q`
      -- (`Zig.checkParent`; `docs/illegal-behavior.md` row 40).
      let expr := match fc.pointeeOf (.inst inst.id) with
        | .struct _ "auto" _ =>
          let parent := (ptrChild fc.types inst.ty).getD 0
          let align := (fc.layouts[parent]?.bind (·.align)).getD 1
          s!"(do let q ← {q}; {fc.callMName} (Zig.checkParent {fc.sizeOf parent} {align} q >>= fun _ => pure q))"
        | _ => q
      let (env, l) := bindLet fc env inst.id expr
      (env, some l)
    else (env, none)
  | .setUnionTag ptr tag =>
    -- Old AIR retains a vestigial tag write for an extern or packed union with no tag.
    if let .union _ _ none _ := fc.pointeeOf ptr then (env, none) else
    if fc.isMemPtr ptr then
      -- Write the tag; the payload bytes stay (Zig).
      match fc.pointeeOf ptr with
      | .union _ _ (some tagTy) fields =>
        let to := ((unionOffsets fc.types fc.layouts tagTy (fields.map (·.2)) fc.errBits).map (·.1)).getD 0
        let ty := emitTy (ptrBits := fc.ptrBits) fc.structNames fc.types (fc.tyOfId tagTy)
        let align := Nat.min (fc.ptrAlign ptr) ((fc.layouts[tagTy]?.bind (·.align)).getD 1)
        (env, some s!"Zig.store (α := {ty}) {align} ({rv ptr}.add {to}) {rv tag}")
      | _ => (env, some (placeholder "set_union_tag of a non-union"))
    else
    match fc.unionFieldOfTag? (fc.pointeeOf ptr) tag with
    | some (u, f, _) => (env, some (fc.modifyPlace ptr fun old => s!"({u}.{fc.helperName (fc.pointeeOf ptr) s!"setTag_{f}"} {old})"))
    | none => (env, some (placeholder "set_union_tag with an unknown tag"))
  | .load ptr =>
    if let some (field, off) := fc.bytePlace? ptr then
      -- A byte local: a whole copy keeps its bytes, a typed read decodes only the bytes read.
      if fc.rawInsts.contains inst.id then
        let (env, l) := bindLet fc env inst.id s!"pure (← get).{field}"; (env, some l)
      else if !fc.isReferenced inst.id then (env, none)
      else
        let child := ((fc.valTyId? ptr).bind (ptrChild fc.types)).getD 0
        let (env, l) := bindLet fc env inst.id
          (fc.storageExpr child s!"Zig.Bytes.get ({fc.pointeeTy ptr}) (← get).{field} {off}")
        (env, some l)
    else if fc.isMemPtr ptr && fc.isVolatileVal ptr then
      -- L13 device mode (the checker admits it only with `--device-contract`): an event.
      let expr := s!"Zig.vload {deviceDefName} {fc.pointeeBits ptr} {fc.ptrAlign ptr} {rv ptr}"
      -- An unused read is still one event (`bindLet` names it `_iN`).
      let (env, l) := bindLet fc env inst.id expr; (env, some l)
    else if fc.isMemPtr ptr then
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
    let isRaw := match v with | .inst x => fc.rawInsts.contains x | _ => false
    if let some (field, off) := fc.bytePlace? ptr then
      let ty := fc.pointeeTy ptr
      let new := match v with
        | .undef _ => s!"Zig.Bytes.setUndef ({ty}) s.{field} {off}"
        | v => if isRaw then s!"Zig.Bytes.copy s.{field} {off} {rv v}"
          else s!"Zig.Bytes.set s.{field} {off} ({rv v} : {ty})"
      (env, some (fc.pointeeStorageExpr ptr s!"modify (fun s => \{ s with {field} := {new} })"))
    else if fc.isMemPtr ptr && fc.isVolatileVal ptr then
      (env, some s!"Zig.vstore {deviceDefName} {fc.pointeeBits ptr} {fc.ptrAlign ptr} {rv ptr} {rv v}")
    else if fc.isMemPtr ptr then
      let (ty, align) := (fc.pointeeTy ptr, fc.ptrAlign ptr)
      -- A copy of a value with undefined parts: its bytes (`rawUseOk`).
      if isRaw then (env, some s!"Zig.storeBytes {rv ptr} {align} {rv v}") else
      let ptrTy? := fc.valTyId? ptr
      let host := (ptrTy?.map fc.hostSize).getD 0
      let bitOff := (ptrTy?.map fc.bitOffset).getD 0
      match v with
      -- `undefined` through a bit-pointer: only the field's bits become undefined.
      | .undef _ =>
        if host != 0 then
          let bits := ((ptrTy?.bind (ptrChild fc.types)).bind (packedBits fc.types)).getD 0
          (env, some s!"{fc.bitsFn "storeUndefBits"} {bits} {host} {align} {bitOff} {rv ptr}")
        else
        -- `undefined`: every byte of the value becomes undefined.
        (env, some (fc.pointeeStorageExpr ptr s!"Zig.storeUndef ({ty}) {align} {rv ptr}"))
      -- Partly `undefined`: one store of the value's bytes, with the bytes of each `undefined`
      -- item or field undefined (`undefByteRanges`; `Check.lean` rejects any other shape).
      | v =>
        if v.hasNestedUndef then
          let ranges := (ptrTy?.bind (ptrChild fc.types)).bind
            (undefByteRanges fc.types fc.layouts · v)
          match ranges with
          | some ranges =>
            let bytes := ranges.foldl (init := s!"Zig.Enc.encode ({fc.resolveVal env v (undefFill := true)} : {ty})") fun acc (off, len) =>
              s!"(Zig.writeBytes ({acc}) {off} (Array.replicate {len} .undef))"
            (env, some (fc.pointeeStorageExpr ptr s!"Zig.storeBytes {rv ptr} {align} {bytes}"))
          | none => (env, some (placeholder "a store of a partly undefined value"))
        else
        if host != 0 then
          let f := if ptrTy?.any fc.laneBitPtr then "Zig.storeLane"
            else fc.bitsFn "storeBits"
          (env, some s!"{f} (α := {ty}) {host} {align} {bitOff} {rv ptr} {rv v}")
        else (env, some (fc.pointeeStorageExpr ptr s!"Zig.store (α := {ty}) {align} {rv ptr} {rv v}"))
    -- A wholly `undefined` value reaches a place only as a store no read observes
    -- (`deadUndefStores`; any other is a stack block or a byte local): filler.
    else (env, some (fc.storePlace ptr (fc.resolveVal env v (undefFill := v matches .undef _))))
  -- An atomic op is a sync op: the oracle picks the message or the place, and another thread can
  -- run first (`ZigLean/Conc/Call.lean`).
  | .atomicLoad ptr order =>
    let bits := fc.tyBits inst.ty
    let o := orderTerm order
    let expr := if fc.atomicPtr ptr then s!"Zig.atomicLoadPtrC ({fc.pointeeTy ptr}) {o} {fc.ptrAlign ptr} {rv ptr}"
      else if fc.atomicTyped ptr then s!"Zig.atomicLoadAsC ({fc.pointeeTy ptr}) {o} {fc.ptrAlign ptr} {rv ptr}"
      else s!"Zig.atomicLoadC (n := {bits}) {o} {fc.ptrAlign ptr} {rv ptr}"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .atomicStore ptr v order =>
    let f := if fc.atomicPtr ptr then s!"Zig.atomicStorePtrC (α := {fc.pointeeTy ptr})"
      else if fc.atomicTyped ptr then "Zig.atomicStoreAsC" else "Zig.atomicStoreC"
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
    -- `Check.lean` admits only `.Xchg` on a pointer.
    let expr := if fc.atomicPtr ptr then s!"Zig.atomicXchgPtrC (α := {fc.pointeeTy ptr}) {o} {fc.ptrAlign ptr} {rv ptr} {rv v}"
      else if fc.atomicTyped ptr then s!"Zig.atomicRmwAsC {opTerm} {o} {fc.ptrAlign ptr} {rv ptr} {rv v}"
      else s!"Zig.atomicRmwC {opTerm} {signed} {o} {fc.ptrAlign ptr} {rv ptr} {rv v}"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .cmpxchg weak ptr expected new succ fail =>
    let f := if fc.atomicPtr ptr then
        if weak then s!"Zig.cmpxchgWeakPtrC (α := {fc.pointeeTy ptr})" else s!"Zig.cmpxchgPtrC (α := {fc.pointeeTy ptr})"
      else if fc.atomicTyped ptr then
        if weak then "Zig.cmpxchgWeakAsC" else "Zig.cmpxchgAsC"
      else if weak then "Zig.cmpxchgWeakC" else "Zig.cmpxchgC"
    let expr := s!"{f} {orderTerm succ} {orderTerm fail} {fc.ptrAlign ptr} {rv ptr} {rv expected} {rv new}"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .sliceLen s =>
    let len := if fc.mem then s!"{rv s}.len"
      else s!"({fc.widthFn "Zig.len" s!"Zig.lenOf {fc.ptrBits}"} {rv s})"
    let expr := match fc.forLenBound? inst.id with
      | some bound => fc.liftR s!"Zig.forLen {len} {rv bound}"
      | none => s!"pure {len}"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .sliceElemVal s i =>
    -- A pure function has the items (`Array`); a function that uses memory reads them, after
    -- its own bounds check (`Zig.checkIndex`: `.illegal` where no Sema check precedes it).
    let sentinel := ((fc.valTyId? s).bind (fc.layouts[·]?)).any (·.sentinel)
    let check := if sentinel then "Zig.checkSentinelIndex" else "Zig.checkIndex"
    let expr := if fc.mem then
        s!"{fc.callMName} ({check} {rv s} {rv i} >>= fun _ => {fc.loadItem s s!"{rv s}.ptr" (rv i)})"
      else fc.liftR s!"{fc.widthFn "Zig.index" "Zig.indexOf"} {rv s} {rv i}"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .ptrAdd sub p n =>
    let size := fc.sizeOf ((ptrChild fc.types inst.ty).getD 0)
    let f := if sub then fc.widthFn "elemSub" "elemSubOf" else fc.widthFn "elem" "elemOf"
    let (env, l) := bindLet fc env inst.id
      (fc.projectExpr p inst.ty (rv p) s!"·.{f} {size} {rv n}" (zero := size == 0 || n matches .int _ 0))
    (env, some l)
  -- `&v[i]` of a bit-packed vector: the vector's address; the lane is in the type.
  | .elemPtr p i =>
    if fc.laneBitPtr inst.ty then
      let (env, l) := bindLet fc env inst.id s!"pure {rv p}"; (env, some l)
    else
    let size := fc.sizeOf ((ptrChild fc.types inst.ty).getD 0)
    let elem := fc.widthFn "elem" "elemOf"
    let base := if fc.isSlice p then s!"{rv p}.ptr" else rv p
    let expr := fc.projectExpr p inst.ty base s!"·.{elem} {size} {rv i}"
      (zero := size == 0 || i matches .int _ 0)
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .ptrElemVal p i =>
    let (env, l) := bindLet fc env inst.id s!"{fc.callMName} ({fc.loadItem p (rv p) (rv i)})"
    (env, some l)
  | .arrayElemVal a i =>
    -- A vector's lanes are a `Vector` (`Zig.Vec.lanes`).
    let items := match fc.valTy a with | .vector .. => s!"{rv a}.lanes" | _ => rv a
    let (env, l) := bindLet fc env inst.id (fc.liftR s!"{fc.widthFn "Zig.vindex" "Zig.vindexOf"} {items} {rv i}"); (env, some l)
  | .slice p len =>
    -- Each slicing checks its own bounds and sentinel (`docs/illegal-behavior.md` rows 5, 24):
    -- Sema lowers `x[start..end]` to `slice(ptr_add(base, start), end - start)`, where `base` is
    -- the `slice_ptr` of a slice or an array pointer cast to a many-pointer.
    let (base, start) := match fc.opOf? p with
      | some (.ptrAdd false b s) => (b, rv s)
      | _ => (p, "(0 : BitVec 64)")
    -- The source's item count, and whether a sentinel follows its items.
    let srcLen : Option (String × Bool) := match fc.opOf? base with
      | some (.slicePtr s) =>
        let sentinel := ((fc.valTyId? s).bind (fc.layouts[·]?)).any (·.sentinel)
        some (if s matches .inst _ then s!"{rv s}.len" else s!"({rv s}).len", sentinel)
      | some (.bitcast a) => match fc.pointeeOf a with
        | .array n _ sentinel => some (s!"({n} : BitVec 64)", sentinel)
        | _ => none
      | _ => none
    let resultSentinel := (fc.layouts[inst.ty]?).any (·.sentinel)
    -- A sentinel slicing reads the item at its end, which must be an item of the source unless
    -- the source's own sentinel is there.
    let checks := (srcLen.map fun (n, srcSentinel) =>
        let extra := if resultSentinel && !srcSentinel then 1 else 0
        [s!"Zig.checkSliceEnd {n} {start} {rv len} {extra}"]).getD [] ++
      -- Sema's own sentinel check comes after the slicing and panics first when present.
      (match ((fc.layouts[inst.ty]?).bind (·.sentinelByte)) with
        | some byte =>
          if fc.sentinelChecked.contains inst.id then []
          else [s!"Zig.checkSentinelByte {rv p} {rv len} ({byte} : BitVec 8)"]
        | none => [])
    let value := s!"(⟨{rv p}, {rv len}⟩ : {sliceTyName fc.ptrBits})"
    let expr := if checks.isEmpty then s!"pure {value}"
      else s!"{fc.callMName} ({" >>= fun _ => ".intercalate checks} >>= fun _ => pure {value})"
    let (env, l) := bindLet fc env inst.id expr; (env, some l)
  | .slicePtr sl => let (env, l) := bindLet fc env inst.id s!"pure {rv sl}.ptr"; (env, some l)
  | .arrayToSlice p =>
    let (ptr, len) := fc.itemsOf p (rv p)
    let (env, l) := bindLet fc env inst.id s!"pure (⟨{ptr}, {len}⟩ : {sliceTyName fc.ptrBits})"; (env, some l)
  | .sliceFieldPtr len p =>
    if fc.isMemPtr p then
      -- The length follows the pointer: `Zig.PtrWidth.bytes` (`ZigLean/Mem/Width.lean`).
      let (env, l) := bindLet fc env inst.id
        (fc.projectExpr p inst.ty (rv p) s!"·.add {fc.ptrBits / 8}" (zero := !len))
      (env, some l)
    else (env, none)
  | .memset dst v =>
    let (ptr, n) := fc.itemsOf dst (rv dst)
    let item := emitTy (ptrBits := fc.ptrBits) fc.structNames fc.types (fc.tyOfId (fc.itemTyId dst))
    let v' := match v with | .undef _ => "none" | _ => s!"(some {rv v})"
    (env, some s!"{fc.callMName} ({fc.storageExpr (fc.itemTyId dst) s!"{fc.widthFn "Zig.memset" "Zig.memsetOf"} (α := {item}) {fc.ptrAlign dst} {ptr} {n} {v'}"})")
  | .memcpy move dst src =>
    -- The item count of the operand that has one. `memcpy` also passes the source's count,
    -- which must agree (`Zig.memcpy` checks it and the overlap itself; with safety Sema
    -- checks it first, `copyLenMismatch`).
    let hasLen (v : Val) : Bool :=
      fc.isSlice v || match fc.pointeeOf v with | .array .. => true | _ => false
    let (dptr, dn) := fc.itemsOf dst (rv dst)
    let (_, sn) := fc.itemsOf src (rv src)
    let n := if hasLen dst then dn else sn
    -- Sema passes a slice source as its `slice_ptr`; its count is the slice's length.
    let slicePtrOf : Option Val := match src with
      | .inst id => match (fc.allInsts.find? (·.id == id)).map (·.op) with
        | some (Op.slicePtr sl) => some sl
        | _ => none
      | _ => none
    let lenOf (sl : Val) : String := match sl with
      | .inst _ => s!"{rv sl}.len"
      | _ => s!"({rv sl}).len"
    let m := if hasLen src then sn else (slicePtrOf.map lenOf).getD n
    let sptr := if fc.isSlice src then s!"{rv src}.ptr" else rv src
    let size := fc.sizeOf (fc.itemTyId dst)
    let args := s!"{size} {fc.ptrAlign dst} {fc.ptrAlign src} {dptr} {sptr} {n}"
    let call := if move then s!"{fc.widthFn "Zig.memmove" "Zig.memmoveOf"} {args}"
      else s!"{fc.widthFn "Zig.memcpy" "Zig.memcpyOf"} {args} {m}"
    (env, some s!"{fc.callMName} ({call})")
  | .tagName a =>
    let (env, l) := bindLet fc env inst.id (fc.liftR s!"{fc.emitValTy a}.{fc.helperName (fc.valTy a) "tagName"} {rv a}")
    (env, some l)
  | .errorName a =>
    let (env, l) := bindLet fc env inst.id (fc.liftR s!"errorNameOf {rv a}"); (env, some l)
  | .structFieldVal s index =>
    let rawField : Option (TyId × Nat) := match s with
      | .inst x =>
        if !fc.rawInsts.contains x then none else
        match fc.valTy s, structFieldOffset? fc.types fc.layouts (fc.instTyId x) index with
        | .struct _ _ fields, some off => (fields[index]?).map fun (_, t) => (t, off)
        | _, _ => none
      | _ => none
    if let some (fty, off) := rawField then
      -- A field of a value with undefined parts: decode only the field's bytes.
      let (env, l) := bindLet fc env inst.id
        (fc.storageExpr fty s!"Zig.Bytes.get ({fc.emitTyOf fty}) {rv s} {off}")
      (env, some l)
    else
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
      let (env, l) := bindLet fc env inst.id (fc.threadCall env fn callee args inst.ty)
      (env, some l)
    else if isNoreturn then (env, none)
    else if callee.isIndirectCallee then
      -- An indirect call: the function whose block the pointer points to, at offset 0 (M20).
      -- A constant address resolves through the same table of address-taken functions of
      -- the callee's type; any other address throws `.illegal` (L11).
      let tn := match fc.tyOfId ((fc.valTyId? callee).getD 0) with
        | .ptr _ _ c => match fc.tyOfId c with | .other n => n | _ => ""
        | _ => ""
      let arms := (fc.fnBlocks.filter (·.1 == tn)).toList.map fun (_, nm, b) =>
        let lean := (fc.funcNames.find? (·.1 == nm)).map (·.2) |>.getD nm
        let memCallee := fc.memFuncs.contains nm
        let term := s!"{lean} {String.intercalate " " (args.map (fc.callArg env memCallee)).toList}"
        let call := fc.callOf nm term memCallee
        s!"if {rv callee} == (⟨some {b}, 0⟩ : Zig.Ptr) then {call} else "
      let (env, l) := bindLet fc env inst.id s!"({String.join arms}throw .illegal)"
      (env, some l)
    else
      let memCallee := match callee with | .func name .. => fc.memFuncs.contains name | _ => false
      let term := s!"{cexpr} {String.intercalate " " (args.map (fc.callArg env memCallee)).toList}"
      let expr := match callee with
        | .func name .. => fc.callOf name term memCallee
        | _ => fc.liftR term
      -- A callee that returns `Zig.Bytes T`, whose value is read as a `T`: decode it.
      let expr := match callee with
        | .func name .. =>
          if fc.rawFuncs.contains name && !fc.rawInsts.contains inst.id then
            fc.storageExpr inst.ty s!"Zig.Bytes.get ({fc.emitTyOf inst.ty}) (← {expr}) 0"
          else expr
        | _ => expr
      let (env, l) := bindLet fc env inst.id expr
      (env, some l)
  | .line _ => (env, none)
  | .dbg _ _ => (env, none)
  | .asm source _ clobbers outputs inputs =>
    if inst.op.isSpinHint then
      let (env, l) := bindLet fc env inst.id "Zig.spinLoopHintC"
      (env, some l)
    else if inst.op.isDeviceAsm fc.targetArch then
      -- L13: a declared device asm (the checker admits no other): one `asm` trace event.
      let ins := "[" ++ ", ".intercalate (inputs.toList.map fun i => s!"({rv i.ref.get!}).toNat") ++ "]"
      let expr := if outputs.isEmpty then s!"Zig.vasmEffect {deviceDefName} {source.quote} {ins}"
        else s!"Zig.vasm {deviceDefName} {source.quote} {ins} {fc.tyBits inst.ty}"
      let (env, l) := bindLet fc env inst.id expr
      (env, some l)
    else
    -- Same identity as `collectAsmOps` (`asmKey`, `asmOpName`): this must name the very `opaque`
    -- def that pass emitted, or the call below resolves to nothing.
    let inputWidths := inputs.map fun i => match fc.valTy i.ref.get! with | .int _ b => b | _ => 0
    let outputWidths := asmOutputWidths fc.types fc.valTyId? inst.ty outputs
    let constraints := outputs.map (·.constraint) ++ inputs.map (·.constraint)
    let name := asmOpName clobbers outputs (asmKey source constraints inputWidths outputWidths)
    -- The effect contract (A01, `ZigLean/Asm.lean`): the old value of each read-write output is
    -- read before the call, in output order, and passed after the inputs.
    let rwOuts := outputs.toList.zipIdx.filter (·.1.isReadWrite)
    let rwName (k : Nat) : String := s!"a{inst.id}o{k}"
    let rwReads := rwOuts.filterMap fun (o, k) => o.ref.map fun ptr =>
      if fc.isMemPtr ptr then s!"let {rwName k} ← {fc.loadMem ptr (rv ptr)}"
      else s!"let {rwName k} ← pure ({fc.loadPlace ptr})"
    -- Two or more locations written through memory pointers: the aliasing guard.
    let memWrites := outputs.toList.filterMap fun o => o.ref.filter fc.isMemPtr
    let guard := if memWrites.length < 2 then [] else
      let locs := memWrites.map fun ptr =>
        s!"({rv ptr}, {fc.sizeOf (((fc.valTyId? ptr).bind (ptrChild fc.types)).getD 0)})"
      [s!"Zig.Asm.guard [{", ".intercalate locs}]"]
    let args := inputs.toList.map (fun i => rv i.ref.get!) ++ rwOuts.map (rwName ·.2)
    let call := if args.isEmpty then name else s!"{name} {String.intercalate " " args}"
    -- S7: an opaque is total, so the allowlist entry's fault condition guards it
    -- (`Zig.asmTrap`, `Zig.Error.trap`); an entry that never faults keeps `pure`. The checker
    -- admits no other asm here (`Op.isDeviceAsm`), so a missing entry or input index is an
    -- unknown identifier: the generated module does not build.
    let cond? : Option (Option String) := (inst.op.asmAllowEntry? fc.targetArch).bind fun e =>
      match e.fault with
      | .never => some none
      | f => (f.condition? args).map some
    let guarded := match cond? with
      | some none => s!"pure ({call})"
      | some (some c) => s!"Zig.asmTrap ({c}) ({call})"
      | none => "air2lean_asm_fault_unknown"
    if outputs.size ≤ 1 && outputs.all (·.ref.isNone) then
      let (env, l) := bindLet fc env inst.id guarded
      (env, some l)
    else
      -- The tuple of the outputs; output `k` of `n` is `.2.….2.1` (`k` times `.2`), the last one
      -- without the `.1`. The result output binds the instruction; each lvalue output is a
      -- store through its pointer, as `store`.
      let t := s!"a{inst.id}"
      let n := outputs.size
      let proj (k : Nat) : String :=
        t ++ tupleProjection n k
      let first := match cond? with
        | some none => s!"let {t} := {call}"
        | _ => s!"let {t} ← {guarded}"
      let (env, lines) := outputs.toList.zipIdx.foldl
        (init := (env, guard ++ rwReads ++ [first]))
        fun (env, ls) (o, k) => match o.ref with
          | none =>
            let (env, l) := bindLet fc env inst.id s!"pure {proj k}"
            (env, ls ++ [l])
          | some ptr =>
            if fc.isMemPtr ptr then
              (env, ls ++ [s!"Zig.store (α := {fc.pointeeTy ptr}) {fc.ptrAlign ptr} {rv ptr} {proj k}"])
            else (env, ls ++ [fc.storePlace ptr (proj k)])
      (env, some ("\n".intercalate lines))
  -- `emitStmts` and `emitTerminator` emit these (`Op.emitRoute`).
  | .block .. | .loop .. | .br .. | .«repeat» .. | .condBr .. | .switchBr .. | .loopSwitchBr ..
  | .switchDispatch .. | .«try» .. | .tryPtr .. | .ret .. | .retLoad .. | .unreach | .trap =>
    (env, some (placeholder s!"unexpected op in straight-line position (inst {inst.id})"))


/-- `emitScalar`; on aarch64 an op that reads `f80` operands (`FCtx.softF80Reads`) is wrapped
in `Zig.Float.softF80Chk`, over every lane of a vector. -/
def emitScalarGuarded (fc : FCtx) (env : Array (InstId × String)) (inst : Inst) :
    Array (InstId × String) × Option String :=
  let (env', line?) := emitScalar fc env inst
  let reads := fc.softF80Reads inst.op
  match line?, (line?.getD "").splitOn " ← " with
  | some _, binder :: rest@(_ :: _) =>
    if reads.isEmpty then (env', line?) else
    let rv := fc.resolveVal env
    let lanes := reads.toList.map fun v =>
      match fc.valTy v with | .vector .. => s!"({rv v}).lanes.toList" | _ => s!"[{rv v}]"
    let xs := if reads.all (fun v => match fc.valTy v with | .vector .. => false | _ => true)
      then s!"[{", ".intercalate (reads.toList.map rv)}]" else " ++ ".intercalate lanes
    (env', some s!"{binder} ← Zig.Float.softF80Chk {xs} ({" ← ".intercalate rest})")
  | _, _ => (env', line?)

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
  let (_, line?) := emitScalarGuarded fc' env' scalar
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
  (emitLaneWise fc env inst).getD (emitScalarGuarded fc env inst)

mutual

/-- Translate an instruction sequence into a `Zig.M _ Exit` do-block body (as source text,
without the surrounding `do`). The last effective instruction (per `isTerminating`) becomes the
tail expression; anything the exporter placed after it (a defensive `unreach`) is dead and
dropped. -/
partial def emitStmts (fc : FCtx) (env : Array (InstId × String)) (insts : List Inst) : String :=
  let fc := fc.prepareInstUses.prepareBranchTargets
  match insts with
  | [] => placeholder "a body without a terminator"
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
          | .errorUnion _ c => emitTy (ptrBits := fc.ptrBits) fc.structNames fc.types (fc.tyOfId c)
          | _ => placeholder "try_ptr of a non-error-union pointer"
        let errStr := emitStmts fc env errBody.toList
        let vname := if fc.isReferenced inst.id then s!"v{inst.id}" else s!"_v{inst.id}"
        let restStr := emitStmts fc (env.push (inst.id, vname)) rest
        let tryFn := match fc.pointeeOf p with
          | .errorUnion set _ => match fc.tyOfId set with
            | .errorSet (some names) => s!"{errOp fc.errBits "finiteTryPayloadPtr"} {emitErrorDomain names}"
            | _ => errOp fc.errBits "tryPayloadPtr"
          | _ => errOp fc.errBits "tryPayloadPtr"
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
    | _ =>
      -- A function that returns `Zig.Bytes T` returns the bytes of a value that has none
      -- undefined.
      let raw := match v with | .inst x => fc.rawInsts.contains x | _ => false
      if fc.rawRet && !raw then
        s!"pure (.ret {fc.storageExpr fc.retTy s!"(Zig.Enc.encode ({rv v} : {fc.emitTyOf fc.retTy}))"})"
      else s!"pure (.ret {rv v})"
  | .retLoad ptr =>
    match fc.tyOfId fc.retTy with
    | .void => "pure .ret"
    | _ =>
      let v := if fc.isMemPtr ptr then s!"(← {fc.loadMem ptr (rv ptr)})" else fc.loadPlace ptr
      if fc.rawRet then
        s!"pure (.ret {fc.storageExpr fc.retTy s!"(Zig.Enc.encode ({v} : {fc.emitTyOf fc.retTy}))"})"
      else s!"pure (.ret {v})"
  -- A bare `unreach` (no panic call before it, which would end the body first) is
  -- `unreachable` without a safety check: unchecked illegal behaviour.
  | .unreach => "throw .illegal"
  | .trap => "throw .panic"
  | .condBr c thenBody elseBody =>
    s!"if {rv c} then {doBlock (emitStmts fc env thenBody.toList)}\nelse \
      {doBlock (emitStmts fc env elseBody.toList)}"
  | .switchBr v cases elseBody => emitSwitch fc env v (rv v) cases elseBody
  | .call callee _ =>
    let (_, calleeName) := fc.resolveCallee callee
    match panicErrorFor? calleeName with
    | some ctor => s!"throw {ctor}"
    | none => placeholder s!"unchecked noreturn callee {calleeName}"
  | _ => placeholder "a terminator of another kind"

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

/-- The captured parameters `(id, name, type)` of a loop's extracted body def. -/
def FCtx.loopParams (fc : FCtx) (loopInst : Inst) : Array (InstId × String × String) :=
  match loopInst.op with
  | .loop body => fc.loopCaptures body
  | .loopSwitchBr .. => fc.loopCaptures (dispatchCaptureBody loopInst)
  | _ => #[]

/-- The text after `:= ` of a loop's extracted body def, starting with `do`. -/
def emitLoopBody (fc : FCtx) (loopInst : Inst) : String :=
  let initEnv := (fc.loopParams loopInst).map fun (id, name, _) => (id, name)
  match loopInst.op with
  | .loop body =>
    "do\n" ++ indent 2 (emitStmts fc initEnv body.toList)
  | .loopSwitchBr initial cases elseBody =>
    let branch := fc.ascribedDo (emitSwitch fc initEnv initial "dispatchValue" cases elseBody)
    String.intercalate "\n"
      ["do",
       s!"  let dispatchValue := (← get).{dispatchFieldName loopInst.id}",
       s!"  let dispatchExit ← {indentTail 2 branch}",
       "  match dispatchExit with",
       s!"  | .dispatch{loopInst.id} dispatchValue => do",
       s!"    modify fun s => \{ s with {dispatchFieldName loopInst.id} := dispatchValue }",
       "    pure dispatchExit",
       "  | _ => pure dispatchExit"]
  | _ => "" -- unreachable: only loops and loop-switches have extracted bodies

/-- One `loop` instruction's body as its own top-level def, named `<fnName>.loop<id>` (so a
proof can refer to it — the point of extracting it at all), taking its captured values
(`FCtx.loopCaptures`) as explicit parameters with the same names the body text already uses. -/
def emitLoopDef (fc : FCtx) (loopInst : Inst) : String :=
  match loopInst.op with
  | .loop _ | .loopSwitchBr .. =>
    let paramsStr := String.intercalate " "
      (((fc.loopParams loopInst).map fun (_, name, ty) => s!"({name} : {ty})").toList)
    s!"def {fc.fnName}.loop{loopInst.id} {paramsStr} : {fc.monad} {fc.localsName} {fc.exitName} := " ++
      emitLoopBody fc loopInst
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
    -- Zig guarantees the alignment of the `alloc`'s pointer type (`align(N)` or the child's ABI
    -- alignment), the only alignment the placement gives the block (MM-1).
    let align := (fc.layouts[fc.instTyId aid]?.bind (·.ptrAlign)).getD (l.align.getD 1)
    (aid, field, l.size.getD 0, align)

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
  -- A byte local starts with every byte undefined. Its size comes from the same storage
  -- dictionary as its `Bytes.get`/`set` (error width, nullable pointers).
  let byteSets := fc.byteLocals.map fun aid =>
    let field := (fc.allocFields.find? (·.1 == aid)).map (·.2) |>.getD s!"local{aid}"
    let child := (ptrChild fc.types (fc.instTyId aid)).getD 0
    s!"{field} := {fc.storageExpr child s!"Zig.Bytes.undef ({fc.emitTyOf child})"}"
  let sets := stack.map (fun (aid, field, _, _) => s!"{field} := s{aid}") ++ byteSets
  let init := if sets.isEmpty then s!"(default : {localsName})"
    else s!"\{ (default : {localsName}) with {String.intercalate ", " sets.toList} }"
  let freeLines := (stack.map fun (aid, _, _, _) => s!"  Zig.free s{aid}").toList
  -- A recursive function that uses memory charges its frame against the stack budget
  -- (`Zig.enterFrame`, MM-5): the bytes of its escaping locals, each rounded up to its
  -- alignment; `Zig.enterFrame` adds the fixed per-call part (`Zig.frameBase`).
  let (enterLines, leaveLines) := if fc.recursive && fc.mem && !fc.conc then
      let bytes := stack.foldl (fun acc (_, _, size, align) => acc + Zig.alignUp size align) 0
      ([s!"  Zig.enterFrame {bytes}"], [s!"  Zig.leaveFrame {bytes}"])
    else ([], [])
  let retArm := match fc.tyOfId retTy with
    | .void => "| .ret => pure ()"
    | _ => "| .ret v => pure v"
  -- `ret` is the only constructor when the function has no block/loop control flow at all
  -- (empty `brTargets`/`repTargets`): a wildcard arm after it is then unreachable, which Lean
  -- rejects as a "Redundant alternative" error rather than a warning, so it must be omitted.
  let matchLines :=
    [s!"  {retArm}"] ++ (if hasNonRetExit then ["  | _ => throw .panic"] else [])
  String.intercalate "\n"
    (["do"] ++ enterLines ++ allocLines ++
     [s!"  let e ← {indentTail 2 ascribedBody}.run' {init}"] ++ freeLines ++ leaveLines ++
     ["  match e with"] ++ matchLines)

/-- Whether a value of type `root` contains a `target` (`Ty.allocator`, `Ty.io`): the type itself,
or one reached through a pointer, array, vector, optional, error-union payload, struct, union or
tuple field. -/
def tyReaches (types : Array Ty) (target : Ty) (root : TyId) : Bool := Id.run do
  let mut seen : Std.HashSet TyId := {}
  let mut todo := #[root]
  while !todo.isEmpty do
    let id := todo.back!
    todo := todo.pop
    if seen.contains id then continue
    seen := seen.insert id
    match types[id]? with
    | some t =>
      if t == target then return true
      todo := todo ++ match t with
        | .ptr _ _ c | .array _ c _ | .vector _ c | .optional c | .errorUnion _ c => #[c]
        | .struct _ _ fs | .union _ _ _ fs => fs.map (·.2)
        | .tuple fs => fs
        | _ => #[]
    | none => pure ()
  return false

/-- The caller obligations of `f`'s signature (W1; `docs/premises.md` ALC-09, IOM-01): the
indices of the parameters that contain a `std.mem.Allocator` or a `std.Io`. The translation
replaces whatever allocator or Io a caller passes by the single std model, so a theorem about
`f` holds only for callers that pass one that behaves as that model. -/
def interfacePremises (f : Func) : Array (String × Array Nat) :=
  #[("ALC-09", Ty.allocator), ("IOM-01", Ty.io)].filterMap fun (premise, target) =>
    let params := (Array.range f.params.size).filter fun i => tyReaches f.types target f.params[i]!
    if params.isEmpty then none else some (premise, params)

/-- The `-- air2lean-premises:` marker line before a function's `def` (`scripts/premises.py`
derives the premise for every theorem that reaches the definition), or `""`. -/
def interfacePremiseMarker (f : Func) : String :=
  let premises := interfacePremises f
  if premises.isEmpty then "" else
    "-- air2lean-premises: " ++ (Lean.Json.mkObj (premises.toList.map fun (premise, params) =>
      (premise, Lean.toJson params))).compress ++ "\n"

def emitFunctionHeader (fc : FCtx) (leanName : String) (paramTys : Array TyId)
    (retTy : TyId) : String :=
  let paramsStr := String.intercalate " "
    ((paramTys.mapIdx fun i pt => s!"(p{i} : {fc.emitTyOf pt})").toList)
  let retStr := if fc.rawRet then s!"Zig.Bytes ({fc.emitTyOf retTy})" else fc.emitTyOf retTy
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
  /-- The prepared context, for `--proof-api` lemmas over the same text. -/
  ctx : FCtx

/-- The static context without block-emission membership, for global encoding. -/
private def mkFCtxUnprepared (f : Func) (structNames : Array (String × String)) (funcNames : Array (String × String))
    (floatSemantics : FloatSemantics) (memFuncs : Array String) (globalIds : Array Nat)
    (concFuncs : Array String := #[]) (rawFuncs : Array String := #[]) : FCtx :=
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
      exitName := mangleField s!"{plain}Exit", floatSemantics, errBits := f.errorSetBits, bigEndian := f.bigEndian,
      zigVersion := f.zigVersion, places := #[],
      mem := memFuncs.contains f.name, memFuncs, layouts := f.layouts,
      conc := concFuncs.contains f.name, concFuncs,
      escaping := escapingAllocs f, globalIds, byteLocals := byteLocals f, rawFuncs,
      rawRet := rawFuncs.contains f.name, targetArch := f.targetArch,
      exactFloatDivs := exactFloatDivs allInsts, sentinelChecked := sentinelCheckedSlices allInsts }
  let fc := { fc with places := fc.computePlaces, bytePlaces := fc.computeBytePlaces }
  { fc with rawInsts := fc.computeRawInsts fc.rawRet }

/-- The static context of `f`, prepared for block emission. `globalIds`: the block of
 each global of `f.globals`. Bare contexts are also prepared by `emitStmts`. -/
def mkFCtx (f : Func) (structNames : Array (String × String)) (funcNames : Array (String × String))
    (floatSemantics : FloatSemantics) (memFuncs : Array String) (globalIds : Array Nat)
    (concFuncs : Array String := #[]) (rawFuncs : Array String := #[]) : FCtx :=
  let fc := mkFCtxUnprepared f structNames funcNames floatSemantics memFuncs globalIds concFuncs
    rawFuncs
  { fc with outwardBlocks := (controlFlowSummaries f.body).outwardBlocks
  }.prepareInstUses.prepareBranchTargets

private def emitOneFunctionWithFallbackMap (f : Func)
    (spawnFallbackMap : Std.HashMap String String) (structNames : Array (String × String))
    (funcNames : Array (String × String)) (floatSemantics : FloatSemantics)
    (memFuncs : Array String) (globalIds : Array Nat) (fnBlocks : Array (String × String × Nat))
    (concFuncs : Array String := #[]) (spawnSemantics : SpawnSemantics := .available)
    (spawnFallbacks : Array (String × String) := #[]) (rawFuncs : Array String := #[])
    (recursive : Bool := false) : FuncParts :=
  let fc := mkFCtxUnprepared f structNames funcNames floatSemantics memFuncs globalIds concFuncs
    rawFuncs
  let fc := { fc with fnBlocks := fnBlocks, spawnSemantics := spawnSemantics, spawnFallbacks := spawnFallbacks, spawnFallbackMap := some spawnFallbackMap, recursive }.prepareInstUses
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
  let localsStr := emitLocalsStruct structNames f.types localsName allocs escaping fc.mem
    fc.dispatchTys fc.byteLocals fc.ptrBits
  let exitStr := emitExitInductive structNames f.types exitName f.ret blTys brT repT fc.mem
    fc.dispatchTys fc.rawRet fc.ptrBits
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
    defn := interfacePremiseMarker f ++ emitFunctionHeader fc leanName f.params f.ret ++ functionBody
    body := functionBody
    ctx := fc }

/-- `--proof-api` lemmas of one emitted function (`docs/generated-code.md`): a model
abbreviation and its unfolding lemma, and per loop (pre-order index `k`) body/again
abbreviations, the body's unfolding lemma and the `Zig.loop` step lemma. Every equality
exposes the actual emitted text and is kernel checked: by `rfl`, or by the definition's
equation lemma for a `partial_fixpoint` (recursive) group. No axiom is introduced. Names come
from the source identity and the loop index (`proofLemmaIndex`), never from AIR IDs. -/
def emitProofApi (f : Func) (p : FuncParts) (recursive : Bool) : String :=
  let fc := p.ctx
  let base := proofApiName f.name
  let binders (xs : Array (String × String)) :=
    String.join (xs.toList.map fun (name, ty) => s!" ({name} : {ty})")
  let applied (head : String) (xs : Array (String × String)) :=
    head ++ String.join (xs.toList.map fun (name, _) => s!" {name}")
  let proof (defn : String) (xs : Array (String × String)) :=
    if recursive then applied s!"{defn}.eq_def" xs else "rfl"
  let params := f.params.mapIdx fun i ty => (s!"p{i}", fc.emitTyOf ty)
  let record := Lean.Json.mkObj ([("format", .str "air2lean-proof-lemmas-v1"),
    ("source", .str f.name), ("definition", .str fc.fnName)] ++ proofLemmaFields f)
  let scalar := match proofApiFacts f with
    | none => []
    | some facts =>
      let v1 := Lean.Json.mkObj [("format", .str "air2lean-proof-api-v1"),
        ("source", .str f.name), ("definition", .str fc.fnName),
        ("model", .str (base ++ "_model")), ("unfold", .str (base ++ "_unfold")),
        ("facts", facts), ("source_map", proofApiSourceMap f)]
      ["-- air2lean-proof-api: " ++ v1.compress]
  let function := String.intercalate "\n" (scalar ++
    ["-- air2lean-proof-lemmas: " ++ record.compress, s!"abbrev {base}_model := {fc.fnName}", "",
     s!"theorem {base}_unfold{binders params} : {applied (base ++ "_model") params} = ({p.body}) :=",
     s!"  {proof fc.fnName params}"])
  let monad := s!"{fc.monad} {fc.localsName} {fc.exitName}"
  let loops := (proofLoops f).toList.zipIdx.map fun (inst, k) =>
    let (body, again, bodyUnfold, step) := proofLoopNames base k
    let defn := s!"{fc.fnName}.loop{inst.id}"
    let caps := (fc.loopParams inst).map fun (_, name, ty) => (name, ty)
    let call := applied body caps
    String.intercalate "\n\n" [
      s!"abbrev {body} := {defn}",
      s!"abbrev {again} := {fc.fnName}.again{inst.id}",
      s!"theorem {bodyUnfold}{binders caps} : {call} = ({emitLoopBody fc inst}) :=\n  {proof defn caps}",
      s!"theorem {step}{binders caps} :\n    (Zig.loop ({call}) {again} : {monad}) =\n" ++
        s!"      ({call} >>= fun e => if {again} e then Zig.loop ({call}) {again} else pure e : {monad}) :=\n" ++
        "  Zig.loop.eq_1 _ _"]
  String.intercalate "\n\n" (function :: loops)

/-- Standalone function emission prepares its own first-match fallback lookup. Program
emission shares one prepared map across all functions. -/
def emitOneFunction (f : Func) (structNames : Array (String × String))
    (funcNames : Array (String × String)) (floatSemantics : FloatSemantics)
    (memFuncs : Array String) (globalIds : Array Nat) (fnBlocks : Array (String × String × Nat))
    (concFuncs : Array String := #[]) (spawnSemantics : SpawnSemantics := .available)
    (spawnFallbacks : Array (String × String) := #[]) (rawFuncs : Array String := #[]) :
    FuncParts :=
  emitOneFunctionWithFallbackMap f (prepareSpawnFallbackMap spawnFallbacks) structNames funcNames
    floatSemantics memFuncs globalIds fnBlocks concFuncs spawnSemantics spawnFallbacks rawFuncs

/-- The functions that return `Zig.Bytes T`: those with a `ret` of a raw instruction
(`FCtx.computeRawInsts`), up to a fixpoint (a call of one is raw too). A function whose address
is taken or that a thread runs keeps its type. `mk f raw`: `f`'s context with `rawFuncs := raw`. -/
partial def rawFunctions (funcs : Array Func) (mk : Func → Array String → FCtx) : Array String :=
  -- A raw value starts at a byte local.
  if funcs.all (byteLocals · |>.isEmpty) then #[] else
  let excluded := (spawnTargets funcs).map (·.1) ++ (futureTargets funcs).map (·.1) ++
    (fnRefs funcs).map (·.2)
  let rec go (raw : Array String) : Array String :=
    let next := funcs.filterMap fun f =>
      if raw.contains f.name || excluded.contains f.name then none else
      let fc := mk f raw
      let insts := fc.computeRawInsts true
      if fc.allInsts.any (fun i => match i.op with
          | .ret (.inst x) => insts.contains x
          | _ => false) then some f.name else none
    if next.isEmpty then raw else go (raw ++ next)
  go #[]

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
  /-- An `extern` global: its `ExternInit` field and Lean type; `bytes` encode that field. -/
  externField : Option (String × String) := none
  /-- A `threadlocal` global: the block is the main thread's instance, and its index is the
  global's TLS key (§Thread-local storage). -/
  tls : Bool := false

/-- The structure of the explicit external initial state that `mem0` takes (§Globals). -/
def externInitName : String := "ExternInit"

/-- The name reserved for the initial bytes of the `threadlocal` globals, only if there is one. -/
def tlsReservedNames (funcs : Array Func) : Array String :=
  if funcs.any (·.globals.any (·.threadlocal)) then #["tlsInit"] else #[]

/-- Program names reserved for explicit external initial state, only if a global is `extern`. -/
def externReservedNames (funcs : Array Func) : Array String :=
  if funcs.any (·.globals.any (·.isExtern)) then #[externInitName] else #[]

/-- The bytes of `term : ty`. -/
def encodeTerm (term ty : String) : String := s!"Zig.Enc.encode ({term} : {ty})"

/-- The initial bytes of global `g` of `fc`'s function. `undefined` is undefined bytes. An
`extern` global (`externField = some field`) is the encoding of `ext.field`, never a default. -/
def FCtx.globalBytes (fc : FCtx) (g : Global) (externField : Option String := none) : String :=
  let ty := emitTy (ptrBits := fc.ptrBits) fc.structNames fc.types (fc.tyOfId g.ty)
  if let some field := externField then fc.storageExpr g.ty (encodeTerm s!"ext.{field}" ty) else
  match g.init with
  -- A function: one byte, so that its pointer has a block (an indirect call, M20).
  | some (.func ..) => "#[.undef]"
  | some (.undef _) | none => fc.storageExpr g.ty s!"Array.replicate (Zig.Enc.size ({ty})) .undef"
  | some init => fc.storageExpr g.ty (encodeTerm (fc.resolveVal #[] init) ty)

/-- Every pointer constant in `v`, at any depth, whose pointer type's alignment `a` (`ptr_align`)
is known and divides its offset: its global and `a`. Zig guarantees `(addr + off) % a = 0`, so
then `addr % a = 0`: `a` is a true lower bound on the global's address alignment. -/
partial def Val.ptrConstAligns (layouts : Array Layout) (v : Val) : Array (Nat × Nat) :=
  match v with
  | .ptrConst ty g off => match layouts[ty]?.bind (·.ptrAlign) with
    | some a => if 0 < a && off % a == 0 then #[(g, a)] else #[]
    | none => #[]
  | .agg _ vs => vs.flatMap (Val.ptrConstAligns layouts)
  | .optSome _ v | .errUnionOk _ v | .unionVal _ _ v => Val.ptrConstAligns layouts v
  | .sliceConst _ p n => Val.ptrConstAligns layouts p ++ Val.ptrConstAligns layouts n
  | _ => #[]

/-- The globals of the program, and the block of each global of each function (by function
name). A named global is one block, shared by name. An unnamed constant (a string literal) with
the same type and value as another one shares its block. Named globals come first. An `extern`
global gets an `ExternInit` field named after it (`prefix_` stripped), in block order. -/
def collectGlobals (funcs : Array Func) (mkFc : Func → Array Nat → FCtx) (prefix_ : String := "") :
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
  let mut fields : Array String := typeCoreNames.push "mk"
  for n in named do
    let some (f, k) := funcs.zipIdx.find? fun (f, _) => f.globals.any (·.name == some n)
      | continue
    let some g := f.globals.find? (·.name == some n) | continue
    let fc := mkFc f ids[k]!.2
    let externField := if g.isExtern then
      some (freshName (plainName (mangleName prefix_ n)) fields) else none
    if let some field := externField then fields := fields.push field
    out := out.push { label := n, bytes := fc.globalBytes g externField,
                      align := (f.layouts[g.ty]?.bind (·.align)).getD 1, isVar := !g.isConst,
                      externField := externField.map (·, emitTy (ptrBits := fc.ptrBits) fc.structNames fc.types (fc.tyOfId g.ty)),
                      tls := g.threadlocal }
  for (bytes, align) in unnamed do
    out := out.push { label := "a constant", bytes, align }
  -- The block's alignment is what Zig guarantees for the global's address (MM-1): its declared
  -- alignment, which the export does not record. Each pointer constant into it at an offset its
  -- alignment divides is a true lower bound (`Val.ptrConstAligns`); the largest one caps the
  -- type's ABI alignment (`&g` of an `align(1)` global is `*align(1) T`). The smallest one is not
  -- a bound: `&g.a : *u8` or a coercion to `*align(1) T` of an aligned global claims less.
  let mut bound : Array Nat := out.map fun _ => 0
  for (f, k) in funcs.zipIdx do
    let vals := f.allInsts.flatMap (placeOperands ·.op) ++ f.globals.filterMap (·.init)
    for (g, a) in vals.flatMap (Val.ptrConstAligns f.layouts) do
      if let some id := ids[k]!.2[g]? then
        if id < bound.size then bound := bound.set! id (Nat.max bound[id]! a)
  for (b, id) in bound.zipIdx do
    if let some pg := out[id]? then
      if 0 < b && b < pg.align then out := out.set! id { pg with align := b }
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

/-- `mem0 σ`: the memory at program start, one block per global, at the addresses that the
placement `σ` gives them (`Zig.Placement`, MM-1). A theorem from `mem0 σ` holds for every `σ`,
so it cannot depend on where a block is. With an `extern` global, `mem0` also takes the explicit
external initial state `ext : ExternInit`, one field per `extern` global in block order: a proof
from `mem0 σ ext` states its assumptions about external storage on `ext`. -/
def emitMem0 (gs : Array ProgGlobal) : String :=
  let kind (g : ProgGlobal) := if g.isVar then ".global" else ".constGlobal"
  let lines := gs.toList.zipIdx.map fun (g, k) =>
    let source := match g.externField with
      | some (field, _) => s!" (extern: initial value `ext.{field}`)"
      | none => if g.tls then " (threadlocal: the main thread's instance)" else ""
    s!"  -- {k}: {g.label}{source}\n  ({g.bytes}, {g.align}, {kind g})"
  let body := if lines.isEmpty then "[]" else s!"[\n{",\n".intercalate lines}]"
  let keys := gs.toList.zipIdx.filterMap fun (g, k) => if g.tls then some s!"{k}" else none
  let body := if keys.isEmpty then s!"Zig.Mem.ofGlobals σ {body}" else
    s!"(Zig.Mem.ofGlobals σ {body}).mainTls #[{", ".intercalate keys}]"
  let tlsDoc := if keys.isEmpty then "" else
    " The main thread's instance of a `threadlocal` global is its block (its TLS key)."
  let tlsInit := if keys.isEmpty then "" else
    let items := gs.toList.zipIdx.filterMap fun (g, k) =>
      if g.tls then some s!"  -- {g.label}\n  ({k}, {g.bytes}, {g.align})" else none
    s!"\n\n/-- The `threadlocal` globals: key, initial bytes and alignment. A spawned thread \
      makes its own instance of each from these (`Zig.ConcM.tlsThread`). -/\n\
      def tlsInit : List (Zig.BlockId × Array Zig.Byte × Nat) := [\n{",\n".intercalate items}]"
  let externs := gs.toList.zipIdx.filterMap fun (g, k) => g.externField.map fun (field, ty) =>
    let access := if g.isVar then "`var`, writable" else "`const`, read-only"
    s!"  /-- Block {k}: `{g.label}` ({access}). -/\n  {field} : {ty}"
  if externs.isEmpty then
    s!"/-- The memory at program start under the placement `σ`: block `k` is global `k`.{tlsDoc} -/\n\
      def mem0 (σ : Zig.Placement) : Zig.Mem := {body}{tlsInit}"
  else
    s!"/-- External initial state: the initial value of each `extern` global, which this program \
      does not define. Fields follow block (initialization) order. Contract: the external \
      definition holds a valid encoding of the field's type before the program starts; any \
      other assumption about external storage is a hypothesis on this value. -/\n\
      structure {externInitName} where\n{"\n".intercalate externs}\n\n\
      /-- The memory at program start under the placement `σ`: block `k` is global `k`. Blocks \
      are added in order; an `extern` block holds its `ext` field, never a default.{tlsDoc} -/\n\
      def mem0 (σ : Zig.Placement) (ext : {externInitName}) : Zig.Mem := {body}{tlsInit}"

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
    -- A value without a name has no tag name: illegal behaviour, which with safety the AIR
    -- checks before (`is_named_enum_value`).
    let arms := fields.toList.zipIdx.map fun ((f, v), k) =>
      s!"  if e.{hn "toBits"} == {tagLit bits v} then pure {slice k f} else"
    String.intercalate "\n" ([head] ++ arms ++ ["  throw .illegal"])

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

/-- Bind a multi-field capture `a` to the `capture<i>` names of `emitCapturedCallWithStorage`. -/
def emitCaptureUnpack (size : Nat) : String :=
  let binders := (List.range size).map fun i => s!"capture{i}"
  if size > 1 then s!"let ({String.intercalate ", " binders}) := a; " else ""

def emitCapturedFallbackWithStorage (name : String) (args : Array (String × Option (String × Nat × Option String)))
    (kind : Nat) : String :=
  s!"fun a => (do {emitCaptureUnpack args.size}discard ({emitCapturedCallWithStorage name args kind}) : Zig.ConcM Tgt Unit)"

/-- The caller's eager execution of an `Io.async` task (fallible policy): the complete
capture, the worker's result. -/
def emitFutureEager (name : String) (args : Array (String × Option (String × Nat × Option String)))
    (kind : Nat) : String :=
  s!"fun a => (do {emitCaptureUnpack args.size}{emitCapturedCallWithStorage name args kind})"

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

/-- Whether a value of type `id` holds no pointer identity. Opaque runtime handles
(allocators, `Io`, threads) and unknown types count as holding one. -/
def pointerFree (types : Array Ty) (id : TyId) (fuel : Nat := types.size + 1) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    match types[id]? with
    | some (.int ..) | some (.float _) | some .bool | some .void | some .noreturn
    | some (.errorSet _) | some (.enum ..) => true
    | some (.array _ c _) | some (.vector _ c) | some (.optional c) => pointerFree types c fuel
    | some (.errorUnion s p) => pointerFree types s fuel && pointerFree types p fuel
    | some (.struct _ _ fs) | some (.union _ _ _ fs) => fs.all fun (_, c) => pointerFree types c fuel
    | some (.tuple fs) => fs.all fun c => pointerFree types c fuel
    | _ => false

/-- The `Zig.Conc.Capture` constructor of a captured field (`ZigLean/Conc/Capture.lean`). -/
inductive CaptureClass where
  | value | ptr | slice | other
  deriving BEq, Inhabited

def captureClass (types : Array Ty) (id : TyId) : CaptureClass :=
  match types[id]? with
  | some (.ptr "slice" ..) => .slice
  | some (.ptr ..) => .ptr
  | _ => if pointerFree types id then .value else .other

/-- `Tgt.captures`: every captured field in source order, as a `Zig.Conc.Capture`. The
ownership obligation over it is `Zig.Conc.Capture.grant` (`ZigLean/Conc/Transfer.lean`). -/
def emitTgtCaptures (targets : Array (String × Array CaptureClass))
    (futures : Array (String × Array CaptureClass) := #[]) : String :=
  let arm (lead : String) (n : String) (classes : Array CaptureClass) :=
    let binder (i : Nat) := if classes.size == 1 then "a" else s!"capture{i}"
    let parts := classes.toList.zipIdx.map fun (c, i) =>
      if c == .ptr || c == .slice then binder i else "_"
    let pattern := match parts with
      | [] => "_"
      | [p] => p
      | _ => s!"({String.intercalate ", " parts})"
    let items := classes.toList.zipIdx.map fun (c, i) => match c with
      | .value => ".value"
      | .ptr => s!".ptr {binder i}"
      | .slice => s!".slice {binder i}"
      | .other => ".other"
    s!"  | .{n}{lead} {pattern} => [{String.intercalate ", " items}]"
  -- A future target's runtime record is not a capture: the task owns its result cells.
  let arms := targets.toList.map (fun (n, classes) => arm "" n classes) ++
    futures.toList.map fun (n, classes) => arm " _" (futureCtorName n) classes
  let body := if arms.isEmpty then ["  fun t => nomatch t"] else arms
  String.intercalate "\n" (["/-- Each captured field in source order. A value is copied and carries no ownership;",
    "a pointer or slice copies only its identity, so a spawn proof must hand over or share its",
    "region (`Zig.Conc.Capture.grant`). An `other` field's obligation cannot be discharged. -/",
    s!"def Tgt.captures : Tgt → List Zig.Conc.Capture{if arms.isEmpty then " :=" else ""}"] ++ body)

/-- A target retains the complete source tuple. Each dispatcher applies the fields in
source order, adapting every slice argument for a pure worker in the child thread.
`captureClasses` (by target index) classifies the fields for `Tgt.captures`; a missing entry
classifies every field as `other`. -/
def emitTgtWithStorage (_structNames : Array (String × String)) (extendedCapture : Bool)
    (targets : Array (String × Array (String × Option (String × Nat × Option String)) × Nat))
    (captureClasses : Array (Array CaptureClass) := #[]) (tls : Bool := false)
    (futures : Array (String × Array (String × Option (String × Nat × Option String)) × Nat ×
      String × Array CaptureClass) := #[]) :
    List String × List String :=
  let tupleTy (args : Array (String × Option (String × Nat × Option String))) :=
    if args.isEmpty then "Unit" else if args.size == 1 then args[0]!.1 else
      String.intercalate " × " (args.toList.map fun (ty, _) => s!"({ty})")
  let ctors := targets.toList.map (fun (n, args, _) => s!"  | {n} (a : {tupleTy args})") ++
    futures.toList.map fun (n, args, _) =>
      s!"  | {futureCtorName n} (futureSlot : Zig.Ptr) (a : {tupleTy args})"
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
    -- With `threadlocal` globals the thread makes and frees its own instances around the target.
    let run := if tls then s!"Zig.ConcM.tlsThread tlsInit (discard ({call}))" else s!"discard ({call})"
    if args.size ≤ 1 then s!"  | .{n} a => {run}" else
      let binders := (List.range args.size).map arg
      s!"  | .{n} a =>\n    let ({String.intercalate ", " binders}) := a\n    {run}"
  -- An `Io.async` task runs the worker and writes its result into its runtime record; with
  -- `threadlocal` globals it is a thread with its own instances, as a spawn target is.
  let futureArms := futures.toList.map fun (n, args, k, complete, _) =>
    let arg (i : Nat) := if args.size == 1 then "a" else s!"capture{i}"
    let call := emitCapturedCallWithStorage n args k
    let run := s!"do\n      let futureResult ← {call}\n      Zig.ConcM.liftMem ({complete})"
    let run := if tls then s!"Zig.ConcM.tlsThread tlsInit {run}" else run
    if args.size ≤ 1 then s!"  | .{futureCtorName n} futureSlot a => {run}" else
      let binders := (List.range args.size).map arg
      s!"  | .{futureCtorName n} futureSlot a =>\n    let ({String.intercalate ", " binders}) := a\n    {run}"
  let arms := arms ++ futureArms
  let body := if arms.isEmpty then ["  fun t => nomatch t"] else arms
  let dispatch := String.intercalate "\n" (["/-- Runs a spawn target (`Zig.Sched.run`). -/",
    s!"def dispatch : Tgt → Zig.ConcM Tgt Unit{if arms.isEmpty then " :=" else ""}"] ++ body)
  let captures := emitTgtCaptures (targets.mapIdx fun i (n, args, _) =>
    (n, captureClasses[i]?.getD (args.map fun _ => .other)))
    (futures.map fun (n, _, _, _, classes) => (n, classes))
  ([tgt] ++ (if extendedCapture then [obligation, captures] else []), [dispatch])

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
  for name in #["v", "e", "g", "_g", "u", "b", "bs", "t", "x", "y", "s", "a", "items", "x0", "x1", "x2",
      "futureSlot", "futureResult"] do
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
  let ids : Array TyId ← match ModelRegistry.argumentTypeIds site.values site.args with
    | .ok ids => pure ids
    | .error error => return placeholder s!"unchecked model arguments: {error}"
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

/-- A 32-bit profile opens the 4-byte `Enc` instances of `Ptr`, `?*T` and `std.mem.Allocator`
(`ZigLean/Mem/Width.lean`); a 64-bit program keeps the global ones. -/
def wasm32Open (funcs : Array Func) : List String :=
  if funcs.any (fun f => ptrBytesOf f.layouts == 4) then ["open scoped Zig.Wasm32"] else []

/-- Runtime names of the 64-bit model that a 32-bit translation must not contain: each has a
width-parameterized form (`ZigLean/Mem/Width.lean`). `Main` refuses such an output. -/
def width64Names : List String :=
  ["Zig.readSlice ", "Zig.memset ", "Zig.memmove ", "Zig.len ", "Zig.index ", "Zig.vindex ",
   "Zig.ptrAddr ", "Zig.Allocator.alloc ", "Zig.Allocator.create ", "Zig.Allocator.free ",
   "Zig.Allocator.freeSentinel ", ".elem ", ".elemSub ",
   -- The unchecked-illegal-behaviour checks exist for the 64-bit model only: a 32-bit program
   -- that needs one is refused, not translated without the check.
   "Zig.memcpy ", "Zig.checkIndex ", "Zig.checkSentinelIndex ", "Zig.checkSliceEnd ",
   "Zig.checkSentinelByte ", "Zig.forLen ", "Zig.checkAddr ", "Zig.checkAlign ", "Zig.checkParent "]

/-- `Zig.Slice` as a whole identifier (not `Zig.Slice32`/`Zig.SliceOf`), or a name of
`width64Names`, in a 32-bit translation's source. -/
def width64Leak (src : String) : Option String :=
  let parts := src.splitOn "Zig.Slice"
  let wholeSlice := parts.drop 1 |>.any fun rest =>
    match rest.toList.head? with
    | some c => !(c.isAlphanum || c == '_')
    | none => true
  if wholeSlice then some "Zig.Slice" else width64Names.find? fun n => (src.splitOn n).length > 1

/-- One emitted program in the pieces that `emitWithNames` concatenates. `groups` are the
call groups (`callGroups`) in emission order: each group's member source names, the source
names of the functions it references outside itself (`calleesOf`), and its declarations. -/
structure EmitParts where
  /-- `import` lines and the spawn-policy comment, before `namespace`. -/
  header : List String
  /-- Scoped instances every module opens right after its `namespace` (`wasm32Open`). -/
  opens : List String := []
  /-- Types, inline assembly, models, globals and `Tgt`: everything the functions share. -/
  preamble : List String
  groups : Array (Array String × Array String × String)
  /-- `dispatch`, which references the spawn targets. -/
  dispatch : List String
  /-- Source names of the functions `dispatch` references. -/
  dispatchTargets : Array String
  /-- Each function's declaration name. -/
  declNames : Array (String × String)

/-- The pieces of `funcs → one Lean source file` importing `ZigLean` (`EmitParts.render`).
`prefix_` is stripped from every Zig name (function or struct) before mangling.
`floatSemantics` selects `--float-semantics` (default `ieee`). -/
def emitParts (funcs : Array Func) (prefix_ : String)
    (floatSemantics : FloatSemantics := .ieee) (models : Array ModelBinding := #[])
    (spawnSemantics : SpawnSemantics := .available) (proofApi : Bool := false)
    (device : Option DeviceContract := none) : EmitParts :=
  let memFuncs := memoryFunctions funcs (models.map (·.symbol))
  let concFuncs := concFunctions funcs
  let asmDefs := collectAsmOps funcs
  let hasErrorName := funcs.any (·.allInsts.any fun i => match i.op with | .errorName _ => true | _ => false)
  let targets := spawnTargets funcs
  let futures := futureTargets funcs
  let extendedCapture := targets.any (fun (_, _, fields) => fields.size != 1) || !futures.isEmpty
  let modelCalls := firstModelCalls models funcs
  let maxModelArgs := modelCalls.fold (fun count _ site => max count site.args.size) 0
  let modelBinders := (Array.range maxModelArgs).map fun i => s!"p{i}"
  let modelNames := models.zipIdx.flatMap fun (m, i) =>
    #[s!"air2lean_model_{i}", s!"air2lean_model_{i}_contract", s!"air2lean_model_{i}_evidence"] ++
      (if m.footprint.isSome then #[s!"air2lean_model_{i}_footprint"] else #[])
  let apiNames := if proofApi then funcs.flatMap proofLemmaNames else #[]
  let fixed := runtimeNames ++ apiNames ++ modelNames ++ modelBinders ++
    (if memFuncs.isEmpty then #[] else #["mem0"] ++ externReservedNames funcs ++ tlsReservedNames funcs) ++
    (if concFuncs.isEmpty then #[] else #["Tgt", "dispatch"]) ++
    (if extendedCapture then #["spawnInit", "captures"] else #[]) ++
    (if hasErrorName then #["errorNameOf"] else #[]) ++ asmDefs.map (·.name) ++
    (if device.isSome then #[deviceDefName] else #[])
  let (structs, ownFuncNames) := allocateDeclNames (collectNamed funcs prefix_) funcs prefix_ fixed
    (targets ++ futures.map fun (nm, f, fields, _) => (nm, f, fields)) extendedCapture
  let funcNames := ownFuncNames ++ models.mapIdx (fun i m => (m.symbol, s!"air2lean_model_{i}"))
  let structNames := structs.map fun s => (s.zigName, s.leanName)
  let structsStr := (structs.map (emitNamed structNames (encTypeNames funcs memFuncs))).toList
  let asmStr := asmDefs.toList.map emitAsmDef
  let modelStr := (models.mapIdx fun index model =>
    match modelCalls[model.symbol]? with
    | some site => emitModel model index site structNames
    | none => "").toList
  let mkFc (f : Func) (ids : Array Nat) := mkFCtxUnprepared f structNames funcNames floatSemantics memFuncs ids
  let rawFuncs := rawFunctions funcs fun f raw =>
    mkFCtxUnprepared f structNames funcNames floatSemantics memFuncs #[] concFuncs raw
  let (globals, ids) := collectGlobals funcs mkFc prefix_
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
  let describe (nm : String) (f : Func) (fields : Array TyId) :=
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
              emitStorageEnc structNames worker.types worker.errorSetBits child worker.layouts)
          | _ => none
        (emitTy structNames f.types f.types[a]!, adapter)
      (nm, leanOf nm, args, kind)
  let targetDescriptions := targets.map fun (nm, f, fields) => describe nm f fields
  -- `Io.async` tasks: the description, the result write and the capture classes.
  let futureDescriptions := futures.map fun (nm, f, fields, r) =>
    let (_, name, args, kind) := describe nm f fields
    let complete := withStorageEnc structNames f.types f.errorSetBits r
      "Zig.Future.complete futureSlot futureResult" f.layouts
    (nm, name, args, kind, complete, fields.map (captureClass f.types))
  let spawnFallbacks := if spawnSemantics == .fallible then
    emitSpawnFallbacksWithStorage funcs targetDescriptions ++
      futureDescriptions.map fun (nm, name, args, kind, _, _) =>
        (futureEagerKey nm, emitFutureEager name args kind)
    else #[]
  let spawnFallbackMap := prepareSpawnFallbackMap spawnFallbacks
  let (tgtStr, dispatchStr) := if concFuncs.isEmpty then ([], []) else
    emitTgtWithStorage structNames extendedCapture (targetDescriptions.map fun (_, name, args, kind) => (name, args, kind))
      (targets.map fun (_, f, fields) => fields.map (captureClass f.types)) (globals.any (·.tls))
      (futureDescriptions.map fun (_, name, args, kind, complete, classes) =>
        (name, args, kind, complete, classes))
  let allNames := funcs.map (·.name)
  let refs := fnRefs funcs
  let groups := (callGroups funcs).map fun (members, recursive) =>
    let names := members.map (·.name)
    let callees := dedupNames (members.flatMap (calleesOf allNames refs)) |>.filter (!names.contains ·)
    let parts := members.toList.map fun f =>
      emitOneFunctionWithFallbackMap f spawnFallbackMap structNames funcNames floatSemantics memFuncs
        (idsOf f) fnBlocks concFuncs spawnSemantics spawnFallbacks rawFuncs recursive
    let text := if recursive then
      -- `partial_fixpoint` on every def of the group: the loop defs too, since a loop body can
      -- call a group member. Types and `again` defs do not recurse, so they come first.
      let fix (d : String) := s!"{d}\npartial_fixpoint"
      let defs := parts.flatMap fun p => (p.loops ++ [p.defn]).map fix
      String.intercalate "\n\n"
        (parts.flatMap (·.types) ++ parts.flatMap (·.agains) ++ ["mutual"] ++ defs ++ ["end"] ++
          (if proofApi then (members.toList.zip parts).map fun (f, p) => emitProofApi f p true
           else []))
    else
      String.intercalate "\n\n" ((members.toList.zip parts).flatMap fun (f, p) =>
        p.types ++ p.agains ++ p.loops ++ [p.defn] ++
          (if proofApi then [emitProofApi f p false] else []))
    (names, callees, text)
  { header := ["import ZigLean"] ++ (models.map (fun m => s!"import {m.importModule}")).toList ++
      (if spawnSemantics == .fallible then ["/- Thread assignment policy: fallible; all declared spawn errors and Io.Group caller fallback are modeled. -/"] else [])
    -- A big-endian profile: the big-endian encodings (`ZigLean/Endian.lean`, T03).
    opens := wasm32Open funcs ++ (if funcs.any (·.bigEndian) then ["open scoped Zig.BigEndian"] else [])
    preamble := structsStr ++ asmStr ++ modelStr ++ (device.map DeviceContract.emitDef).toList ++
      globalsStr ++ tgtStr
    groups
    dispatch := dispatchStr
    -- The spawn targets and the `Io.async` tasks: `dispatch` calls each by name.
    dispatchTargets := if dispatchStr.isEmpty then #[] else
      targets.map (·.1) ++ futures.map (·.1)
    declNames := ownFuncNames }

/-- The single-file output: every part in order under one `namespace`. -/
def EmitParts.render (p : EmitParts) (ns : String) : String :=
  String.intercalate "\n\n" (p.header ++ [s!"\nnamespace {ns}"] ++ p.opens ++ p.preamble ++
    (p.groups.map (·.2.2)).toList ++ p.dispatch ++ [s!"end {ns}"])

/-- `funcs → one Lean source file` (`emitParts`). Also returns each function's declaration name. -/
def emitWithNames (funcs : Array Func) (ns : String) (prefix_ : String)
    (floatSemantics : FloatSemantics := .ieee) (models : Array ModelBinding := #[])
    (spawnSemantics : SpawnSemantics := .available) (proofApi : Bool := false)
    (device : Option DeviceContract := none) :
    String × Array (String × String) :=
  let p := emitParts funcs prefix_ floatSemantics models spawnSemantics proofApi device
  (p.render ns, p.declNames)

/-- The kinds of the placeholders in the generated source `src`, deduplicated, in order. -/
def placeholdersIn (src : String) : Array String :=
  ((src.splitOn s!"{placeholderMarker} \"").drop 1).foldl (init := #[]) fun acc part =>
    let what := (part.splitOn "\"").head!
    if acc.contains what then acc else acc.push what

/-- `emitWithNames`, failing closed: output that contains a `placeholder` (an arm the checker
did not exclude) is a translation error, never a Lean term that succeeds (MM-6). -/
def emitWithNamesChecked (funcs : Array Func) (ns : String) (prefix_ : String)
    (floatSemantics : FloatSemantics := .ieee) (models : Array ModelBinding := #[])
    (spawnSemantics : SpawnSemantics := .available) (proofApi : Bool := false) :
    Except String (String × Array (String × String)) := do
  let out := emitWithNames funcs ns prefix_ floatSemantics models spawnSemantics proofApi
  let kinds := placeholdersIn out.1
  unless kinds.isEmpty do
    throw s!"EMITTER_PLACEHOLDER: the input reached emitter arms that the checker should \
      exclude ({"; ".intercalate (kinds.extract 0 8).toList}); nothing was written. This is a \
      translator bug: please report the AIR input."
  pure out

/-- `emitWithNames`'s Lean source only. -/
def emit (funcs : Array Func) (ns : String) (prefix_ : String)
    (floatSemantics : FloatSemantics := .ieee) (models : Array ModelBinding := #[])
    (spawnSemantics : SpawnSemantics := .available) (proofApi : Bool := false) : String :=
  (emitWithNames funcs ns prefix_ floatSemantics models spawnSemantics proofApi).1

end Air2Lean
