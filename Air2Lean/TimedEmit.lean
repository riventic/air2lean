import Air2Lean.TimedCheck
import Air2Lean.Air.Normalize
import Air2Lean.Air.Anon

/-! Isolated acyclic timed entry point. Named types/encodings/globals and scalar
instructions are emitted by the ordinary shared emitter; generated body effects and
selected calls use an explicit Program path. No ordinary CLI behavior changes. -/
namespace Air2Lean.Timed

private def selectTimeout (fc : FCtx) (id : TyId) (value : String) : String :=
  let ty := fc.tyOfId id
  let fields := match ty with | .union _ _ _ fields => fields | _ => #[]
  let arm (index : Nat) (kind : String) :=
    let wrapper := fc.tyOfId fields[index]!.2
    let inner := match wrapper with | .struct _ _ fs => fs | _ => #[]
    let rawTy := fc.tyOfId inner[0]!.2
    let clockTy := fc.tyOfId inner[1]!.2
    let ctor := fc.memberName ty fields[index]!.1
    let raw := fc.memberName wrapper "raw"
    let clock := fc.memberName wrapper "clock"
    let nanos := fc.memberName rawTy "nanoseconds"
    let awake := fc.memberName clockTy "awake"
    s!"| .{ctor} d => if d.{clock} == .{awake} then \
      (Zig.TimedCall.checkedNanoseconds d.{raw}.{nanos}).map Zig.Time.Timeout.{kind} else none"
  s!"(match {value} with\n| .{fc.memberName ty "none"} => none\n{arm 1 "duration"}\n{arm 2 "deadline"})"

private def callExpr (fc : FCtx) (env : Array (InstId × String)) (i : Inst)
    (name : String) (args : Array Val) : String :=
  let rv := fc.resolveVal env
  if name == "Io.Clock.now" then
    let clockTy := fc.valTy args[0]!
    let timestampTy := fc.tyOfId i.ty
    s!"Zig.TimedBody.observeClock ({rv args[0]!} == .{fc.memberName clockTy "awake"}) \
      (fun bits => (\{ {fc.memberName timestampTy "nanoseconds"} := bits } : {fc.emitTyOf i.ty}))"
  else if selected name then
    let timeoutId := (fc.valTyId? args[3]!).getD 0
    s!"Zig.TimedBody.waitTimeout {rv args[1]!} {rv args[2]!} \
      {selectTimeout fc timeoutId (rv args[3]!)}"
  else
    let lean := (fc.funcNames.find? (·.1 == name)).map (·.2) |>.getD name
    s!"{lean} {String.intercalate " " (args.toList.map rv)}"

/-- One ordinary scalar operation executes in its original MM semantics. Lift its
whole action, including locals, instead of rewriting emitted expression text. -/
private def scalar (fc : FCtx) (env : Array (InstId × String)) (i : Inst) :
    Array (InstId × String) × Option String :=
  let (nextEnv, line) := emitSimple fc env i
  match line with
  | none => (nextEnv, none)
  | some line =>
    match nextEnv.find? (·.1 == i.id) with
    | some (_, name) =>
      let body := doBlock s!"{line}\npure {name}"
      (nextEnv, some s!"let {name} ← Zig.TimedBody.callBody ({body} : Zig.MM {fc.localsName} ({fc.emitTyOf i.ty}))")
    | none =>
      let body := doBlock s!"{line}\npure ()"
      (nextEnv, some s!"Zig.TimedBody.callBody ({body} : Zig.MM {fc.localsName} Unit)")

private partial def statements (fc : FCtx) (env : Array (InstId × String)) : List Inst → String
  | [] => "Zig.TimedBody.fail .panic"
  | i :: rest =>
    match i.op with
    | .ret value =>
      if fc.tyOfId fc.retTy == .void then "pure .ret"
      else s!"pure (.ret {fc.resolveVal env value})"
    | .«try» value errors =>
      let name := if fc.isReferenced i.id then s!"v{i.id}" else s!"_v{i.id}"
      s!"match {fc.resolveVal env value} with\n\
        | .error _ => {doBlock (statements fc env errors.toList)}\n\
        | .ok {name} => {doBlock (statements fc (env.push (i.id, name)) rest)}"
    | .call (.func name false none) args =>
      let bound := if fc.isReferenced i.id then s!"i{i.id}" else s!"_i{i.id}"
      s!"let {bound} ← Zig.TimedBody.callProgram ({callExpr fc env i name args})\n\
        {statements fc (env.push (i.id, bound)) rest}"
    | _ =>
      let (nextEnv, line) := scalar fc env i
      let tail := statements fc nextEnv rest
      match line with | none => tail | some line => s!"{line}\n{tail}"

private def functionDef (fc : FCtx) (f : Func) : String :=
  let params := String.intercalate " "
    ((f.params.mapIdx fun k id => s!"(p{k} : {fc.emitTyOf id})").toList)
  let stack := fc.stackBlocks
  let allocs := stack.toList.map fun (id, _, size, align) =>
    s!"  let s{id} ← Zig.TimedSched.Program.liftMem (Zig.allocStack {size} {align})"
  let initial := if stack.isEmpty then s!"(default : {fc.localsName})" else
    let fields := stack.toList.map fun (id, field, _, _) => s!"{field} := s{id}"
    s!"\{ (default : {fc.localsName}) with {String.intercalate ", " fields} }"
  let action := s!"({doBlock (statements fc #[] f.body.toList)} : Zig.TimedBody.TM {fc.localsName} {fc.exitName})"
  let frees := stack.toList.map fun (id, _, _, _) =>
    s!"  Zig.TimedSched.Program.liftMem (Zig.free s{id})"
  let ret := if fc.tyOfId f.ret == .void then "  | .ret => pure ()" else "  | .ret value => pure value"
  String.intercalate "\n"
    ([s!"def {fc.fnName} {params} : Zig.TimedSched.Program ({fc.emitTyOf f.ret}) := do"] ++
      allocs ++ [s!"  let exit ← {indentTail 2 action}.run' {initial}"] ++ frees ++ ["  match exit with", ret])

private def emitChecked (funcs : Array Func) (ns prefix_ : String) : String := Id.run do
  let names := funcs.map (·.name)
  let (named, functions) := allocateDeclNames (collectNamed funcs prefix_) funcs prefix_
    (runtimeNames ++ #["mem0"]) #[] false
  let structNames := named.map fun n => (n.zigName, n.leanName)
  let mk (f : Func) (ids : Array Nat) := mkFCtx f structNames functions .ieee names ids
  let (globals, globalIds) := collectGlobals funcs mk
  let types := named.toList.map (emitNamed structNames (encTypeNames funcs names))
  let mut output := ["import ZigLean", "import ZigLean.Conc.TimedBody", s!"namespace {ns}"] ++
    types ++ [emitMem0 globals]
  for f in topoOrder funcs do
    let ids := (globalIds.find? (·.1 == f.name)).map (·.2) |>.getD #[]
    let fc := mk f ids
    let allocs := collectAllocs f.types fc.allInsts (structNames.map (·.2))
    output := output ++
      [emitLocalsStruct structNames f.types fc.localsName allocs fc.escaping true,
       emitExitInductive structNames f.types fc.exitName f.ret #[] #[] #[] true,
       functionDef fc f]
  return String.intercalate "\n\n" (output ++ [s!"end {ns}"])

/-- Explicit selected-source entry point; callers must supply parsed metadata for every
AIR body. Validation runs before any output. Default Main.processRaw/emit are unchanged. -/
def emitSelected (funcs : Array Func) (profiles : Array BuildProfile) (ns prefix_ : String) :
    Except String String := do
  unless (ns.splitOn ".").all (fun part => !part.isEmpty && mangleField part == part) do
    throw "selected timed emission: invalid namespace"
  let _ ← preflight funcs profiles
  let profile ← BuildProfile.checkProgram profiles
  let metadata := Lean.Json.mkObj [("profile", profile.toJson), ("timed_emission", .str "acyclic-unqualified")]
  return s!"-- air2lean-build: {metadata.compress}\n" ++ emitChecked funcs ns prefix_

/-- Parse and normalize the actual compiler AIR together, retaining metadata. No
handwritten replacement of the generated declarations is part of this path. -/
def translateSelected (contents : Array String) (ns prefix_ : String) : Except String String := do
  let raw ← (Anon.renumberAll contents).mapM Raw.parseFile
  let funcs ← raw.mapM normalize
  emitSelected funcs (raw.map (·.profile)) ns prefix_

end Air2Lean.Timed
