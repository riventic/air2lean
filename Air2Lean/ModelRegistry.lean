import Std.Data.HashMap
import Std.Data.HashSet
import Air2Lean.Memory
import Air2Lean.Air.Profile
import Lean.Data.Json
import Air2Lean.Air.StrictJson

/-! Exact direct-call project bindings. Built-in std models live in the single typed table of
`Air2Lean/StdModels.lean`; a project binding cannot reuse one of its qualified names.
The registry supplies identifiers, never executable Lean source fragments. A generated typed
alias and contract obligation are checked by Lean after translation. -/
namespace Air2Lean
open Lean (Json)

/-- Declared memory footprint: zero-based indices of pointer/slice parameters whose blocks a
call may read (`reads`) or read and write (`writes`). -/
structure ModelFootprint where
  reads : Array Nat
  writes : Array Nat
  deriving BEq, Repr

structure ModelBinding where
  symbol : String
  profile : BuildProfile
  params : Array Json
  ret : Json
  importModule : String
  implementation : String
  contract : String
  proof : Option String
  termination : String
  errors : Array String
  effects : String
  dependencies : Array String
  /-- `none`: no declared footprint; only the contract's own `access`/`frame` apply. -/
  footprint : Option ModelFootprint := none

instance : Inhabited ModelBinding := ⟨{
  symbol := "", profile := {name := "", schema := 0, zigVersion := ""},
  params := #[], ret := .null, importModule := "", implementation := "", contract := "",
  proof := none, termination := "", errors := #[], effects := "", dependencies := #[] }⟩

namespace ModelRegistry
private def require {α : Type} (v : Option α) (message : String) : Except String α :=
  match v with | some value => pure value | none => throw message
private def field (j : Json) (k : String) : Except String Json := j.getObjVal? k
private def str (j : Json) (k : String) : Except String String := do
  let s ← (← field j k).getStr?
  unless !s.isEmpty do throw s!"model registry: '{k}' must not be empty"
  pure s
private def strings (j : Json) (k : String) : Except String (Array String) := do
  (← (← field j k).getArr?).mapM Json.getStr?

private def identifier (s : String) : Bool :=
  (s.splitOn ".").all fun part => !part.isEmpty &&
    (part.toList.head?.map fun c => c.isAlpha || c == '_').getD false &&
    part.toList.all (fun c => c.isAlphanum || c == '_' || c == '\'')

private def keys (j : Json) (allowed : List String) : Except String Unit := do
  for (k, _) in (← j.getObj?).toArray do
    unless allowed.contains k do throw s!"model registry: unsupported field '{k}'"

/-- Bounds apply to expanded schema-1 JSON, including repeated DAG edges. -/
def maxShapeNodes : Nat := 65536
def maxShapeBytes : Nat := 1048576
def maxShapeDepth : Nat := 256
/-- Two containers per type node plus room for registry/profile envelopes. -/
def maxJsonDepth : Nat := 2 * maxShapeDepth + 16

private structure Shape where
  json : Json
  nodes : Nat
  bytes : Nat
  height : Nat
  deriving Inhabited

private structure ShapeState where
  done : Std.HashMap TyId Shape := {}
  active : Std.HashSet TyId := {}
  deriving Inhabited

private partial def jsonNodes : Json → Nat
  | .arr values => 1 + values.foldl (fun n value => n + jsonNodes value) 0
  | .obj fields => 1 + fields.toArray.foldl (fun n (_, value) => n + jsonNodes value) 0
  | _ => 1

private def withinBudget (nodes bytes : Nat) : Except String Unit := do
  unless nodes ≤ maxShapeNodes && bytes ≤ maxShapeBytes do
    throw s!"model registry: expanded signature budget exceeded (limit {maxShapeNodes} JSON nodes, {maxShapeBytes} UTF-8 bytes)"

private def shapeHead (t : Ty) : Ty := match t with
  | .ptr s c _ => .ptr s c 0
  | .array n _ s => .array n 0 s
  | .vector n _ => .vector n 0
  | .optional _ => .optional 0
  | .errorUnion _ _ => .errorUnion 0 0
  | .struct n s fs => .struct n s (fs.map fun (n, _) => (n, 0))
  | .enum n _ e fs => .enum n 0 e fs
  | .union n s tag fs => .union n s (tag.map fun _ => 0) (fs.map fun (n, _) => (n, 0))
  | .tuple fs => .tuple (fs.map fun _ => 0)
  | t => t

private def shapeJson (t : Ty) (l : Layout) (children : Array Json) : Json :=
  Json.mkObj [("type", .str (reprStr (shapeHead t))), ("children", .arr children),
    ("layout", Json.mkObj ([("size", Lean.toJson l.size), ("align", Lean.toJson l.align),
      ("offsets", Lean.toJson l.offsets), ("pointer_align", Lean.toJson l.ptrAlign),
      ("sentinel", .bool l.sentinel), ("volatile", .bool l.isVolatile),
      ("allowzero", .bool l.allowzero), ("host_size", Lean.toJson l.hostSize),
      ("bit_offset", Lean.toJson l.bitOffset)] ++
      l.sentinelByte.toList.map (fun byte => ("sentinel_byte", Lean.toJson byte))))]

private partial def shapeGo (types : Array Ty) (layouts : Array Layout) (id : TyId) :
    StateT ShapeState (Except String) Shape := do
  let state : ShapeState ← get
  if let some cached := state.done[id]? then
    if state.active.size + cached.height > maxShapeDepth then
      throw s!"model registry: signature nesting exceeds {maxShapeDepth} type nodes"
    return cached
  if state.active.contains id then
    throw "model registry: recursive signature is outside the extension API"
  if state.active.size ≥ maxShapeDepth then
    throw s!"model registry: signature nesting exceeds {maxShapeDepth} type nodes"
  let some t := types[id]? | throw s!"model registry: unknown type {id}"
  modify fun state => {state with active := state.active.insert id}
  let children ← (childTys t).mapM (shapeGo types layouts)
  let height := 1 + children.foldl (fun h child => max h child.height) 0
  if height > maxShapeDepth then
    throw s!"model registry: signature nesting exceeds {maxShapeDepth} type nodes"
  let l := layouts[id]?.getD {}
  let base := shapeJson t l #[]
  let nodes := jsonNodes base + children.foldl (fun n child => n + child.nodes) 0
  let bytes := base.compress.utf8ByteSize +
    children.foldl (fun n child => n + child.bytes) 0 + (children.size - 1)
  -- Check costs before attaching repeated child JSON; never serialize an oversized DAG.
  match withinBudget nodes bytes with
  | .error error => throw error
  | .ok () => pure ()
  let shape : Shape := {
    json := base.setObjVal! "children" (.arr (children.map (·.json)))
    nodes := nodes
    bytes := bytes
    height := height
  }
  modify fun state => {state with done := state.done.insert id shape, active := state.active.erase id}
  return shape

/-- Completed memoization avoids retraversing shared types. Expanded-node/byte accounting
also bounds serialization/equality: memoization alone cannot bound expanded schema-1 JSON. -/
private def typeShapesWith (types : Array Ty) (layouts : Array Layout) (roots : Array TyId)
    (state : ShapeState := {}) : Except String (Array Json × ShapeState) := do
  let action : StateT ShapeState (Except String) (Array Json) := do
    let mut shapes : Array Json := #[]
    let mut nodes := 0
    let mut bytes := 0
    for root in roots do
      let shape ← shapeGo types layouts root
      nodes := nodes + shape.nodes
      bytes := bytes + shape.bytes
      match withinBudget nodes bytes with
      | .error error => throw error
      | .ok () => pure ()
      shapes := shapes.push shape.json
    return shapes
  action.run state

def typeShapes (types : Array Ty) (layouts : Array Layout) (roots : Array TyId) : Except String (Array Json) := do
  pure (← typeShapesWith types layouts roots).1

def typeShape (types : Array Ty) (layouts : Array Layout) (id : TyId) : Except String Json := do
  pure (← typeShapes types layouts #[id])[0]!

/-- Registry/template inputs are bounded before the existing recursive subset checks.
This is an explicit extension limit, not a general scalability fix for unregistered AIR. -/
private def preflightShapes (types : Array Ty) (layouts : Array Layout) : Except String ShapeState := do
  pure (← typeShapesWith types layouts (Array.range types.size)).2

def preflight (types : Array Ty) (layouts : Array Layout) : Except String Unit := do
  let _ ← preflightShapes types layouts
  pure ()

structure ValueTypeIndex where
  instructions : Std.HashMap InstId TyId := {}
  boolType : Option TyId := none
  voidType : Option TyId := none

def valueTypeIndex (types : Array Ty) (insts : Array Inst) : ValueTypeIndex := Id.run do
  let mut instructions : Std.HashMap InstId TyId := {}
  for i in insts do
    unless instructions.contains i.id do instructions := instructions.insert i.id i.ty
  return {
    instructions := instructions
    boolType := types.findIdx? (· == Ty.bool)
    voidType := types.findIdx? (· == Ty.void)
  }

/-- Shared by the checker and emitter. First instruction occurrence retains the old lookup
semantics; diagnostics remain the same for missing or untyped arguments. -/
def argumentTypeIds (index : ValueTypeIndex) (args : Array Val) : Except String (Array TyId) :=
  args.mapM fun arg => match arg with
    | .inst id => require index.instructions[id]? "model registry: missing argument instruction"
    | .bool _ => require index.boolType "model registry: missing bool type"
    | .void => require index.voidType "model registry: missing void type"
    | v => require v.constTy? "model registry: untyped/function-valued argument is unsupported"

private def signatureWithShapes (f : Func) (index : ValueTypeIndex) (args : Array Val) (ret : TyId)
    (state : ShapeState := {}) :
    Except String (Array Json × Json) := do
  let ids ← argumentTypeIds index args
  let (shapes, _) ← typeShapesWith f.types f.layouts (ids.push ret) state
  pure (shapes.extract 0 ids.size, shapes[ids.size]!)

def signatureWith (f : Func) (index : ValueTypeIndex) (args : Array Val) (ret : TyId) :
    Except String (Array Json × Json) :=
  signatureWithShapes f index args ret

def signature (f : Func) (args : Array Val) (ret : TyId) : Except String (Array Json × Json) :=
  signatureWith f (valueTypeIndex f.types f.allInsts) args ret

structure CallSite where
  functionIndex : Nat := 0
  function : Func
  values : ValueTypeIndex
  args : Array Val
  ret : TyId
  noreturn : Bool
  spawnFn : Option String

/-- Prepend into lists, then reverse each bucket once to retain traversal order. -/
def callIndex (funcs : Array Func) : Std.HashMap String (Array CallSite) := Id.run do
  let mut calls : Std.HashMap String (List CallSite) := {}
  for (f, functionIndex) in funcs.zipIdx do
    let insts := f.allInsts
    let values := valueTypeIndex f.types insts
    for i in insts do
      if let .call (.func name noreturn spawnFn) args := i.op then
        let site : CallSite := {
          functionIndex := functionIndex
          function := f
          values := values
          args := args
          ret := i.ty
          noreturn := noreturn
          spawnFn := spawnFn
        }
        calls := calls.insert name (site :: calls.getD name [])
  return calls.fold (fun buckets name sites => buckets.insert name sites.reverse.toArray)
    ({} : Std.HashMap String (Array CallSite))

/-- Profile uses the same parser and equality policy as AIR. Legacy bindings must explicitly
select legacy metadata; there is no implicit default or wildcard. -/
def parse (contents : String) : Except String (Array ModelBinding) := do
  let j ← StrictJson.parse contents maxJsonDepth
  keys j ["schema", "models"]
  unless (← (← field j "schema").getNat?) == 1 do throw "unsupported model registry schema"
  (← (← field j "models").getArr?).mapM fun m => do
    keys m ["symbol", "profile", "signature", "import", "implementation", "contract", "trust",
      "proof", "termination", "errors", "effects", "dependencies", "footprint"]
    let symbol ← str m "symbol"
    let p ← field m "profile"
    let schema ← (← field p "schema").getNat?
    let version ← str p "zig_version"
    let facts := (← p.getObj?).toArray.filter fun (k, _) => k != "schema"
    let raw := Json.mkObj <| [("zig_version", .str version)] ++
      (if schema < 12 then [] else [("profile", Json.mkObj facts.toList)])
    let profile ← BuildProfile.parse raw schema version
    unless profile.toJson == p do throw "model registry: profile must be the complete normalized profile record"
    let sig ← field m "signature"
    keys sig ["params", "return"]
    let params ← (← field sig "params").getArr?
    let ret ← field sig "return"
    let importModule ← str m "import"
    let implementation ← str m "implementation"
    let contract ← str m "contract"
    for name in #[importModule, implementation, contract] do
      unless identifier name do throw s!"model registry: invalid Lean identifier '{name}'"
    let trust ← str m "trust"
    let proof ← match trust with
      | "proved" =>
        let name ← str m "proof"
        unless identifier name do throw "model registry: invalid proof identifier"
        pure (some name)
      | "assumed" =>
        if (m.getObjVal? "proof").isOk then throw "model registry: assumed binding cannot carry proof"
        pure none
      | _ => throw "model registry: trust must be 'proved' or 'assumed'"
    let termination ← str m "termination"
    unless ["total", "partial"].contains termination do throw "model registry: unsupported termination"
    let effects ← str m "effects"
    unless ["preserves", "tracked"].contains effects do throw "model registry: unsupported effects"
    let errors ← strings m "errors"
    for e in errors do
      unless ["overflow", "outOfBounds", "divByZero", "unreachable", "panic", "unspecified",
        "illegal", "deadlock", "unsupportedTimer"].contains e do throw s!"model registry: unknown safety error '{e}'"
    let dependencies ← strings m "dependencies"
    unless dependencies.all (fun s => !s.isEmpty) do throw "model registry: empty semantic dependency"
    let footprint ← match m.getObjVal? "footprint" with
      | .error _ => pure none
      | .ok fp => do
        keys fp ["reads", "writes"]
        let indices (k : String) : Except String (Array Nat) := do
          let values ← (← (← field fp k).getArr?).mapM Json.getNat?
          for (index, position) in values.zipIdx do
            unless index < params.size do
              throw s!"model registry: footprint {k} index {index} is not a parameter"
            if (values.extract 0 position).contains index then
              throw s!"model registry: duplicate footprint {k} index {index}"
          pure values
        let reads ← indices "reads"
        let writes ← indices "writes"
        if reads.any writes.contains then
          throw "model registry: footprint index listed as both read and write"
        if effects == "preserves" && !(reads.isEmpty && writes.isEmpty) then
          throw "model registry: preserves binding cannot declare footprint accesses"
        pure (some {reads, writes : ModelFootprint})
    pure {
      symbol := symbol
      profile := profile
      params := params
      ret := ret
      importModule := importModule
      implementation := implementation
      contract := contract
      proof := proof
      termination := termination
      effects := effects
      errors := errors
      dependencies := dependencies
      footprint := footprint
    }

/-- Each semantic dependency names another binding, a modelled built-in std model qualified
for the binding's Zig version, or a project Lean declaration. Dependencies are unique, and
those between bindings are acyclic. This checks the declared inventory, not an inferred
proof-dependency closure. -/
def checkDependencies (models : Array ModelBinding) : Except String Unit := do
  let bindings := models.foldl (fun index m => index.insert m.symbol m) ({} : Std.HashMap String ModelBinding)
  for m in models do
    let mut seen : Std.HashSet String := {}
    for d in m.dependencies do
      if seen.contains d then throw s!"model '{m.symbol}': duplicate semantic dependency '{d}'"
      seen := seen.insert d
      if bindings.contains d then continue
      match anyStdModel? d with
      | some std =>
        if let .rejected reason := std.kind then
          throw s!"model '{m.symbol}': semantic dependency '{d}' is outside the subset: {reason}"
        unless std.qualifies m.profile.zigVersion do
          throw s!"model '{m.symbol}': semantic dependency '{d}' is not qualified for Zig {m.profile.zigVersion}"
      | none =>
        unless identifier d do
          throw s!"model '{m.symbol}': semantic dependency '{d}' is not a binding, built-in std model or Lean identifier"
  -- Binding-to-binding edges: reject any cycle, including a self-dependency.
  for m in models do
    let mut frontier := m.dependencies.filter bindings.contains
    let mut reached : Std.HashSet String := {}
    while !frontier.isEmpty do
      let d := frontier.back!
      frontier := frontier.pop
      if d == m.symbol then throw s!"model '{m.symbol}': cyclic semantic dependency"
      unless reached.contains d do
        reached := reached.insert d
        frontier := frontier ++ ((bindings[d]?.map (·.dependencies)).getD #[]).filter bindings.contains

/-- All registry entries must bind an actual direct call and cannot override AIR/built-ins.
Function pointers and concurrent clients remain outside this selected extension fragment. -/
def check (models : Array ModelBinding) (profile : BuildProfile) (funcs : Array Func) :
    Except String Unit := do
  if models.isEmpty then return
  unless profile.pointerBits == 64 do
    throw "model registry: external models are qualified for the 64-bit pointer model only"
  unless funcs.all (·.zigVersion == profile.zigVersion) do
    throw "model registry: function Zig version differs from checked profile"
  let completedShapes ← funcs.mapM fun f => preflightShapes f.types f.layouts
  let calls := callIndex funcs
  let functionNames := funcs.foldl (fun names f => names.insert f.name) ({} : Std.HashSet String)
  let addressTaken := (fnRefs funcs).foldl (fun names reference => names.insert reference.2) ({} : Std.HashSet String)
  let mut seen : Std.HashSet String := {}
  for m in models do
    if seen.contains m.symbol then throw s!"duplicate model symbol '{m.symbol}'"
    seen := seen.insert m.symbol
    unless m.profile == profile do throw s!"model '{m.symbol}': exact profile/version mismatch"
    -- Any mode's row: a project binding never shadows a built-in model, the OS boundary included.
    if functionNames.contains m.symbol || (anyStdModel? m.symbol).isSome then
      throw s!"model '{m.symbol}' conflicts with translated AIR or a built-in model"
    if addressTaken.contains m.symbol then
      throw s!"model '{m.symbol}': address-taken/indirect bindings are outside the extension API"
    let sites := calls.getD m.symbol #[]
    if sites.isEmpty then throw s!"model '{m.symbol}' has no supported direct call"
    for site in sites do
      unless !site.noreturn && site.spawnFn.isNone do
        throw s!"model '{m.symbol}': noreturn/comptime-worker calls are outside the extension API"
      let (params, ret) ← signatureWithShapes site.function site.values site.args site.ret
        completedShapes[site.functionIndex]!
      unless params == m.params && ret == m.ret do
        throw s!"{site.function.name}: model '{m.symbol}' has incompatible signature/layout"
      let ids ← argumentTypeIds site.values site.args
      let types := site.function.types
      let layouts := site.function.layouts
      if let some fp := m.footprint then
        for index in fp.reads ++ fp.writes do
          unless (match types[ids[index]!]? with | some (.ptr ..) => true | _ => false) do
            throw s!"model '{m.symbol}': footprint parameter {index} is not a pointer or slice"
      -- L13: a volatile parameter is a device effect. Its explicit contract is a write
      -- footprint (a read may change device state); no nested volatile capability.
      for (id, index) in ids.zipIdx do
        let nested := match types[id]? with
          | some (.ptr _ _ child) => containsVolatilePtr types layouts child
          | _ => containsVolatilePtr types layouts id
        if nested then
          throw s!"model '{m.symbol}': parameter {index} has a nested volatile pointer (VOLATILE_ACCESS; only a direct volatile pointer parameter can carry a device contract)"
        if volatilePtrTy types layouts id &&
            !((m.footprint.map (·.writes.contains index)).getD false) then
          throw s!"model '{m.symbol}': volatile pointer parameter {index} must be listed in footprint.writes (VOLATILE_ACCESS: a device access is an observable effect, not a pure repeatable read)"
  checkDependencies models
  unless (concFunctions funcs).isEmpty do
    throw "external model bindings currently require a sequential program"

/-- Authoring template: missing implementation/contract/policy fields intentionally make
this invalid as a registry until the project supplies and reviews its own declarations. -/
def template (profile : BuildProfile) (funcs : Array Func) : Except String Json := do
  let mut names : Array String := #[]
  let mut entries : Array Json := #[]
  for f in funcs do
    let insts := f.allInsts
    let values := valueTypeIndex f.types insts
    for i in insts do
      if let .call (.func name false none) args := i.op then
        unless names.contains name || funcs.any (·.name == name) || (anyStdModel? name).isSome do
          names := names.push name
          let (params, ret) ← signatureWith f values args i.ty
          entries := entries.push <| Json.mkObj [("symbol", .str name),
            ("profile", profile.toJson),
            ("signature", Json.mkObj [("params", .arr params), ("return", ret)])]
  pure <| Json.mkObj [("schema", Lean.toJson (1 : Nat)), ("models", .arr entries)]

/-- Report trust separately from the qualified runtime semantics. No proved label is evidence
until the generated obligation has passed Lean kernel checking. -/
def report (models : Array ModelBinding) : Json :=
  Json.mkObj [("schema", Lean.toJson (1 : Nat)),
    ("qualification", .str "selected-sequential-direct-MemM-models"),
    ("bindings", .arr <| models.map fun m => Json.mkObj [
      ("symbol", .str m.symbol), ("profile", m.profile.toJson),
      ("signature", Json.mkObj [("params", .arr m.params), ("return", m.ret)]),
      ("implementation", .str m.implementation), ("contract", .str m.contract),
      ("trust", .str (if m.proof.isSome then "proved-obligation" else "assumed")),
      ("proof", Lean.toJson m.proof), ("termination", .str m.termination),
      ("errors", Lean.toJson m.errors), ("effects", .str m.effects),
      ("dependencies", Lean.toJson m.dependencies),
      ("footprint", match m.footprint with
        | some fp => Json.mkObj [("reads", Lean.toJson fp.reads), ("writes", Lean.toJson fp.writes)]
        | none => .null)]),
    ("assumptions", Lean.toJson <| (models.filter (·.proof.isNone)).map (·.symbol))]
end ModelRegistry
end Air2Lean
