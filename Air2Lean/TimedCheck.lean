import Air2Lean.Emit

/-! Strict preflight for the isolated acyclic timed emitter. This is not an ordinary
translator option and does not alter default missing-callee/no-clock rejection. -/
namespace Air2Lean.Timed

def selected (name : String) : Bool :=
  name == "Io.Clock.now" || (name.splitOn "__anon_").head! == "Io.futexWaitTimeout"

private def require (ok : Bool) (message : String) : Except String Unit :=
  unless ok do throw s!"selected timed emission: {message}"

private def abi (f : Func) (id size align : Nat) (offsets : Array Nat := #[]) : Except String Unit := do
  let some l := f.layouts[id]? | throw "selected timed emission: missing layout"
  require (l.size == some size && l.align == some align && l.offsets == offsets)
    s!"{f.name}: incompatible timed ABI at type {id}"

/-- Follow field types, not local type IDs; names and the whole selected shape agree. -/
private partial def shape (f : Func) (id : TyId) (kind : String) : Except String Unit := do
  let some ty := f.types[id]? | throw "selected timed emission: unknown selected type"
  match kind, ty with
  | "Clock", .enum "Io.Clock" tag true fields =>
    require (f.types[tag]? == some (.int false 3) && fields ==
      #[("real", 0), ("awake", 1), ("boot", 2), ("cpu_process", 3), ("cpu_thread", 4)]) "Clock tags"
    abi f id 1 1
  | "Timestamp", .struct "Io.Timestamp" "auto" fields
  | "Duration", .struct "Io.Duration" "auto" fields =>
    require (fields.size == 1 && fields[0]!.1 == "nanoseconds" &&
      f.types[fields[0]!.2]? == some (.int true 96)) "signed i96 raw value"
    abi f id 16 16 #[0]
  | "Clock.Timestamp", .struct "Io.Clock.Timestamp" "auto" fields
  | "Clock.Duration", .struct "Io.Clock.Duration" "auto" fields =>
    require (fields.size == 2 && fields.map (·.1) == #["raw", "clock"]) "clock wrapper fields"
    shape f fields[0]!.2 (if kind == "Clock.Timestamp" then "Timestamp" else "Duration")
    shape f fields[1]!.2 "Clock"
    abi f id 32 16 #[0, 16]
  | "Timeout", .union "Io.Timeout" "auto" (some tag) fields =>
    require (fields.size == 3 && fields.map (·.1) == #["none", "duration", "deadline"] &&
      f.types[fields[0]!.2]? == some .void) "Timeout fields"
    let some (.enum _ tagInt true tags) := f.types[tag]? | throw "selected timed emission: Timeout tag"
    require (f.types[tagInt]? == some (.int false 2) && tags ==
      #[("none", 0), ("duration", 1), ("deadline", 2)]) "Timeout tag values"
    abi f tag 1 1
    shape f fields[1]!.2 "Clock.Duration"
    shape f fields[2]!.2 "Clock.Timestamp"
    abi f id 48 16
  | _, _ => throw s!"selected timed emission: {f.name}: incompatible {kind} type"

private def callSignature (f : Func) (i : Inst) (name : String) (args : Array Val) : Except String Unit := do
  let index := f.operandTypes
  let arg (k : Nat) : Except String TyId :=
    match args[k]?.bind index.valTy? with
    | some id => pure id
    | none => throw "selected timed emission: missing argument type"
  if name == "Io.Clock.now" then
    require (args.size == 2) "Clock.now arity"
    shape f (← arg 0) "Clock"
    require (f.types[← arg 1]? == some .io) "Clock.now Io"
    shape f i.ty "Timestamp"
  else
    require (args.size == 4) "futexWaitTimeout arity"
    require (f.types[← arg 0]? == some .io && f.types[← arg 2]? == some (.int false 32)) "wait Io/u32"
    let pointer ← arg 1
    let some (.ptr "one" true child) := f.types[pointer]? | throw "selected timed emission: wait pointer"
    let some l := f.layouts[pointer]? | throw "selected timed emission: pointer layout"
    require (f.types[child]? == some (.int false 32) && l.ptrAlign == some 4 &&
      !l.isVolatile && !l.allowzero && !l.sentinel && l.hostSize == 0 && l.bitOffset == 0) "wait pointer representation"
    abi f pointer 8 8
    shape f (← arg 3) "Timeout"
    let some (.errorUnion errors payload) := f.types[i.ty]? | throw "selected timed emission: wait result"
    require (f.types[errors]? == some (.errorSet (some #["Canceled"])) &&
      f.types[payload]? == some .void) "wait error{Canceled}!void result"

/-- Deliberately small opcode inventory. All other operations fail before lowering. -/
def admitted : Op → Bool
  | .arg _ | .dbg .. | .line _ | .alloc | .store .. | .load _ | .bitcast _ | .fieldPtr ..
  | .aggregateInit _ | .unionInit .. | .structFieldVal .. | .errCode _ | .errPayload _ | .wrapErr _
  | .wrapErrPayload _ | .ret _ | .«try» .. | .call (.func _ false none) _ => true
  | _ => false

def preflight (funcs : Array Func) (profiles : Array BuildProfile) : Except String (Array String) := do
  require (!funcs.isEmpty && funcs.size == profiles.size) "function/profile count"
  let profile ← BuildProfile.checkProgram profiles (some BuildProfile.currentName)
  let dialect? := (Dialect.ofProfile profile).toOption
  require (profile.schema == 12 && dialect?.any (·.version == .v0_16_0) &&
    profile.targetTriple == "x86_64-linux.5.10...6.19-musl" && profile.backend == "stage2_llvm" &&
    profile.buildMode == "ReleaseSafe" && profile.cpu == "x86_64" && profile.errorTracing == some false)
    "outside retained source profile"
  let names := funcs.map (·.name)
  let mut selectedNames := #[]
  for f in funcs do
    require (dialect?.any (·.version == f.dialect.version)) "function/profile Zig version mismatch"
    check f
    -- A byte local (`Zig.Bytes T`) is outside the timed subset.
    require (byteLocals f).isEmpty s!"{f.name}: a local with undefined parts"
    for i in f.allInsts do
      require (admitted i.op) s!"{f.name}: inst {i.id}: unsupported timed opcode/control flow"
      if let .structFieldVal value field := i.op then
        let some (.struct _ "auto" fields) :=
          (f.operandTypes.valTy? value).bind (f.types[·]?)
          | throw "selected timed emission: projection requires an ordinary auto struct"
        let some (_, child) := fields[field]?
          | throw "selected timed emission: projection field is out of bounds"
        require (compatibleType f f child i.ty) "projection result type differs from field"
      if let .call (.func name false none) args := i.op then
        if selected name then
          require (!names.contains name) "selected std symbol shadowed by AIR body"
          callSignature f i name args
          unless selectedNames.contains name do selectedNames := selectedNames.push name
        else require (names.contains name) s!"{f.name}: unselected callee {name}"
  for (_, recursive) in callGroups funcs do require (!recursive) "recursive call graph"
  require (!selectedNames.isEmpty) "no selected clock/wait calls"
  checkProgram funcs #[] (some profile) selectedNames
  return selectedNames

end Air2Lean.Timed
