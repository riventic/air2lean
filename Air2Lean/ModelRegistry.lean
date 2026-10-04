import Air2Lean.Memory
import Air2Lean.Air.Profile
import Lean.Data.Json

/-! Exact direct-call bindings, separate from the historical built-in recognition tables.
The registry supplies identifiers, never executable Lean source fragments. A generated typed
alias and contract obligation are checked by Lean after translation. -/
namespace Air2Lean
open Lean (Json)

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

/-- Signature shapes include all layout flags and recursive child types, independent of IDs.
Recursive signatures are deliberately outside this first extension API. -/
def typeShape (types : Array Ty) (layouts : Array Layout) (id : TyId) : Except String Json :=
  let rec go (fuel : Nat) (id : TyId) : Except String Json := do
    match fuel with
    | 0 => throw "model registry: recursive signature is outside the extension API"
    | fuel + 1 =>
      let some t := types[id]? | throw s!"model registry: unknown type {id}"
      let l := layouts[id]?.getD {}
      let children ← (childTys t).mapM (go fuel)
      -- Replace child IDs with a fixed ID in the head: the child shapes carry their identity.
      let head : Ty := match t with
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
      pure <| Json.mkObj [("type", .str (reprStr head)), ("children", .arr children),
        ("layout", Json.mkObj [("size", Lean.toJson l.size), ("align", Lean.toJson l.align),
          ("offsets", Lean.toJson l.offsets), ("pointer_align", Lean.toJson l.ptrAlign),
          ("sentinel", .bool l.sentinel), ("volatile", .bool l.isVolatile),
          ("allowzero", .bool l.allowzero), ("host_size", Lean.toJson l.hostSize),
          ("bit_offset", Lean.toJson l.bitOffset)])]
  go (types.size + 1) id

/-- Emit these shapes from a checked call site when authoring a manifest binding. -/
def signature (f : Func) (args : Array Val) (ret : TyId) :
    Except String (Array Json × Json) := do
  let types ← args.mapM fun arg => do
    let id ← match arg with
      | .inst id => require ((f.allInsts.find? (·.id == id)).map (·.ty)) "model registry: missing argument instruction"
      | .bool _ => require (f.types.findIdx? (· == .bool)) "model registry: missing bool type"
      | .void => require (f.types.findIdx? (· == .void)) "model registry: missing void type"
      | v => require v.constTy? "model registry: untyped/function-valued argument is unsupported"
    typeShape f.types f.layouts id
  pure (types, ← typeShape f.types f.layouts ret)

/-- Profile uses the same parser and equality policy as AIR. Legacy bindings must explicitly
select legacy metadata; there is no implicit default or wildcard. -/
def parse (contents : String) : Except String (Array ModelBinding) := do
  let j ← Json.parse contents
  keys j ["schema", "models"]
  unless (← (← field j "schema").getNat?) == 1 do throw "unsupported model registry schema"
  (← (← field j "models").getArr?).mapM fun m => do
    keys m ["symbol", "profile", "signature", "import", "implementation", "contract", "trust",
      "proof", "termination", "errors", "effects", "dependencies"]
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
        "illegal", "deadlock"].contains e do throw s!"model registry: unknown safety error '{e}'"
    let dependencies ← strings m "dependencies"
    unless dependencies.all (fun s => !s.isEmpty) do throw "model registry: empty semantic dependency"
    pure { symbol := symbol, profile := profile, params := params, ret := ret,
      importModule := importModule, implementation := implementation, contract := contract,
      proof := proof, termination := termination, effects := effects, errors := errors,
      dependencies := dependencies }

/-- All registry entries must bind an actual direct call and cannot override AIR/built-ins.
Function pointers and concurrent clients remain outside this selected extension fragment. -/
def check (models : Array ModelBinding) (profile : BuildProfile) (funcs : Array Func) :
    Except String Unit := do
  unless models.isEmpty || funcs.all (·.zigVersion == profile.zigVersion) do
    throw "model registry: function Zig version differs from checked profile"
  let mut seen : Array String := #[]
  for m in models do
    if seen.contains m.symbol then throw s!"duplicate model symbol '{m.symbol}'"
    seen := seen.push m.symbol
    unless m.profile == profile do throw s!"model '{m.symbol}': exact profile/version mismatch"
    if funcs.any (·.name == m.symbol) || (allocFn? m.symbol).isSome ||
        (threadFn? m.symbol).isSome || (rejectedThreadFn? m.symbol).isSome then
      throw s!"model '{m.symbol}' conflicts with translated AIR or a built-in model"
    if (fnRefs funcs).any (·.2 == m.symbol) then
      throw s!"model '{m.symbol}': address-taken/indirect bindings are outside the extension API"
    let mut used := false
    for f in funcs do
      for i in f.allInsts do
        if let .call (.func name noreturn spawnFn) args := i.op then
          if name == m.symbol then
            unless !noreturn && spawnFn.isNone do
              throw s!"model '{name}': noreturn/comptime-worker calls are outside the extension API"
            used := true
            let (params, ret) ← signature f args i.ty
            unless params == m.params && ret == m.ret do
              throw s!"{f.name}: model '{name}' has incompatible signature/layout"
    unless used do throw s!"model '{m.symbol}' has no supported direct call"
  unless models.isEmpty || (concFunctions funcs).isEmpty do
    throw "external model bindings currently require a sequential program"

/-- Authoring template: missing implementation/contract/policy fields intentionally make
this invalid as a registry until the project supplies and reviews its own declarations. -/
def template (profile : BuildProfile) (funcs : Array Func) : Except String Json := do
  let mut names : Array String := #[]
  let mut entries : Array Json := #[]
  for f in funcs do
    for i in f.allInsts do
      if let .call (.func name false none) args := i.op then
        unless names.contains name || funcs.any (·.name == name) || (allocFn? name).isSome ||
            (threadFn? name).isSome || (rejectedThreadFn? name).isSome do
          names := names.push name
          let (params, ret) ← signature f args i.ty
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
      ("dependencies", Lean.toJson m.dependencies)]),
    ("assumptions", Lean.toJson <| (models.filter (·.proof.isNone)).map (·.symbol))]
end ModelRegistry
end Air2Lean
