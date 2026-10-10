import Lean.Data.Json
import Std.Data.HashMap

/-!
# Module identity

A fully qualified Zig name (`util.helper`) is a path inside one module: a root `util.zig` and a
dependency module's `util.zig` both declare `util.helper`, and a user `Thread.zig` declares
`Thread.spawn` like the standard library (`docs/air-json.md` §Identity). The exporter writes the
module next to every identity: the function's own `module`, a function reference's `module` and
`comptime_fn_module`, and the `module` of a named type or global.

Before parsing, `rewrite` replaces each identity by its key (`key`); every later lookup (callee
resolution, shared types and globals, std models, special std types, Lean names) uses the key:

* `std`: the name itself. Only the std module can name a std model or special std type.
* `root`: the name itself (the historical spelling), unless its first component is a std
  namespace that the translator interprets by name (`stdNamespaces`): then `root:<name>`, which
  no std model or special type matches.
* any other module `m`: `m:<name>`.

`checkProgram` rejects a key that two different (module, name) pairs share (for example a root
and a std function with the same name), and a program that mixes files with and without
module identity. An export without a top-level `module` is legacy: its names are its keys, and no
module tells them apart.

**Generic instances.** The compiler names an instance `<generic>__anon_<n>`, with a number that
depends on the compilation. The exporter writes the instance's content-addressed
`instance_key` next to its name (`instance_key`, `comptime_fn_instance_key`; `docs/air-json.md`
§Instances). Before this rewrite, `Anon.renumberAnon` renames each keyed instance to
`<generic>__anon_<the key's first 12 hex digits>` (`instanceSuffix`), the same in every program that
uses the instance. The identity of an instance is (module, generic name, instance key): its record
carries the key, `rewrite` checks that the name is the key's name, and `checkProgram` that no two
keys share one name. An instance without a key (a legacy export, or an argument without a stable
identity) keeps a number (`Anon.lean`).
-/

namespace Air2Lean.Identity

open Lean (Json)

/-- One identity in an AIR file: its key and the (module, name) pair it stands for. `module`
is `none` in a legacy export. -/
structure Record where
  key : String
  module : Option String
  name : String
  /-- A generic instance's content-addressed key (`instance_key`), if the export has one. -/
  instanceKey : Option String := none
  deriving BEq, Repr, Inhabited

/-- The hex digits of an instance key in an instance's name. -/
def instanceDigits : Nat := 12

/-- The suffix of the name of the instance with `instanceKey`: `<generic>__anon_<digits>`. -/
def instanceSuffix (instanceKey : String) : String :=
  "__anon_" ++ (instanceKey.take instanceDigits).toString

/-- An `instance_key`: 64 lower-case hex digits (a SHA-256). -/
def validInstanceKey (k : String) : Bool :=
  k.length == 64 && k.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- The std namespaces whose names the translator interprets (`StdModels.lean`, the special
types of `Json.parseTy`, the panic handlers of `Op.panicErrorFor?`, the receiver and clock
types of `Check.lean` and `TimedCheck.lean`). -/
def stdNamespaces : Array String := #["mem", "Thread", "Io", "atomic", "time", "debug"]

/-- The key of `name` in `module` (`none`: a legacy export). -/
def key (module : Option String) (name : String) : String :=
  match module with
  | none | some "std" => name
  | some "root" =>
    if stdNamespaces.contains ((name.splitOn ".").headD name) then "root:" ++ name else name
  | some m => m ++ ":" ++ name

/-- The module of a file's function: its `module`; `none` for a legacy export without it. -/
def fileModule (j : Json) : Except String (Option String) := do
  let .ok m := j.getObjVal? "module" | pure none
  let .str module := m | throw "'module' must be a string"
  if module.isEmpty then throw "'module' must not be empty"
  pure (some module)

/-- The key of the file's own function, for emission order: its name if the file cannot be
read (parsing reports that). -/
def fileKey (j : Json) : String :=
  let name := (j.getObjValAs? String "name").toOption.getD ""
  key ((fileModule j).toOption.join) name

private abbrev M := StateT (Array Record) (Except String)

/-- The instance key in field `field` of `j`, for the identity `name`: a valid key, and `name`
ends with its `instanceSuffix` (`Anon.renumberAnon` names a keyed instance so). -/
private def instanceOf (what name : String) (j : Json) (field : String) : M (Option String) := do
  let .ok v := j.getObjVal? field | return none
  let .str k := v | throw s!"{what} '{name}': '{field}' must be a string"
  unless validInstanceKey k do
    throw s!"{what} '{name}': '{field}' must be 64 lower-case hex digits"
  unless name.endsWith (instanceSuffix k) do
    throw s!"{what} '{name}': its '{field}' names another instance (two instances with one compiler name, or a name that is not an instance's)"
  pure (some k)

/-- `j` with the identity in `nameKey` replaced by its key, given the module in `moduleKey`.
An export with module identity names the module of every identity; a legacy export none. -/
private def qualify (legacy : Bool) (what : String) (j : Json) (nameKey moduleKey : String)
    (instanceField : Option String := none) : M Json := do
  let .ok (.str name) := j.getObjVal? nameKey | return j
  let module ← match j.getObjVal? moduleKey, legacy with
    | .error _, true => pure none
    | .error _, false => throw s!"{what} '{name}': missing '{moduleKey}' (an export with a top-level module names the module of every identity)"
    | .ok _, true => throw s!"{what} '{name}': '{moduleKey}' in an export without a top-level module"
    | .ok (.str m), false =>
      if m.isEmpty then throw s!"{what} '{name}': '{moduleKey}' must not be empty" else pure (some m)
    | .ok _, false => throw s!"{what} '{name}': '{moduleKey}' must be a string"
  let k := key module name
  modify (·.push { key := k, module, name, instanceKey := ← match instanceField with
    | some field => instanceOf what name j field
    | none => pure none })
  pure (j.setObjVal! nameKey (.str k))

/-- `j` with every function reference (`func`, `comptime_fn`) at any depth replaced by its key. -/
private partial def refs (legacy : Bool) (j : Json) : M Json := do
  match j with
  | .arr vs => .arr <$> vs.mapM (refs legacy)
  | .obj fields =>
    let mut out : Json := Json.mkObj []
    for (k, v) in fields.toArray do
      out := out.setObjVal! k (← refs legacy v)
    if (out.getObjVal? "func").toOption.isSome then
      out ← qualify legacy "function reference" out "func" "module" "instance_key"
      out ← qualify legacy "spawned function" out "comptime_fn" "comptime_fn_module"
        "comptime_fn_instance_key"
    pure out
  | j => pure j

private def mapArray (j : Json) (k : String) (f : Json → M Json) : M Json := do
  let .ok (.arr vs) := j.getObjVal? k | return j
  pure (j.setObjVal! k (.arr (← vs.mapM f)))

/-- One AIR file with every identity replaced by its key, and its identity records (the
file's own function first). -/
def rewrite (j : Json) : Except String (Json × Array Record) := do
  let module ← fileModule j
  let legacy := module.isNone
  let go : M Json := do
    let .ok (.str name) := j.getObjVal? "name" | return j
    let own := key module name
    modify (·.push { key := own, module, name, instanceKey := ← instanceOf "function" name j "instance_key" })
    let mut j := j.setObjVal! "name" (.str own)
    j ← mapArray j "types" fun t =>
      match (t.getObjValAs? String "k").toOption with
      | some "struct" | some "enum" | some "union" => qualify legacy "type" t "name" "module"
      | _ => pure t
    j ← mapArray j "globals" fun g => do refs legacy (← qualify legacy "global" g "name" "module")
    mapArray j "body" (refs legacy)
  go.run #[]

/-- `j` with `f` applied to the module of every identity that `rewrite` reads: the file's own
`module`, a named type's or global's `module`, and a function reference's `module` and
`comptime_fn_module`. -/
partial def mapModulesM {m : Type → Type} [Monad m] (f : String → m String) (j : Json) : m Json := do
  let setModule (j : Json) (k : String) : m Json := do
    let .ok (.str module) := j.getObjVal? k | return j
    pure (j.setObjVal! k (.str (← f module)))
  let rec refs (j : Json) : m Json := do
    match j with
    | .arr vs => .arr <$> vs.mapM refs
    | .obj fields =>
      let mut out : Json := Json.mkObj []
      for (k, v) in fields.toArray do
        out := out.setObjVal! k (← refs v)
      if (out.getObjVal? "func").toOption.isSome then
        out ← setModule out "module"
        out ← setModule out "comptime_fn_module"
      pure out
    | j => pure j
  let mapArray (j : Json) (k : String) (g : Json → m Json) : m Json := do
    let .ok (.arr vs) := j.getObjVal? k | return j
    pure (j.setObjVal! k (.arr (← vs.mapM g)))
  let mut j ← setModule j "module"
  j ← mapArray j "types" fun t =>
    match (t.getObjValAs? String "k").toOption with
    | some "struct" | some "enum" | some "union" => setModule t "module"
    | _ => pure t
  j ← mapArray j "globals" fun g => do refs (← setModule g "module")
  mapArray j "body" refs

/-- The (module, name) of a record, for messages. -/
def Record.describe (r : Record) : String :=
  let suffix := match r.instanceKey with
    | some k => s!" (instance {k})"
    | none => ""
  match r.module with
  | some m => s!"'{r.name}' of module '{m}'{suffix}"
  | none => s!"'{r.name}' (no module){suffix}"

/-- One program's identities (`records[i]`: file `i`'s records, its own function first): every
key stands for one (module, name), and all files have module identity or none has. -/
def checkProgram (records : Array (Array Record)) : Except String Unit := do
  let files := records.filterMap (·[0]?)
  if files.any (·.module.isSome) then
    if let some legacy := files.find? (·.module.isNone) then
      throw s!"{legacy.name}: AIR without module identity (an older exporter) cannot be combined with AIR that names modules; export the whole program with one compiler"
  let mut seen : Std.HashMap String Record := {}
  for r in records.flatten do
    match seen[r.key]? with
    | none => seen := seen.insert r.key r
    | some previous =>
      unless previous.module == r.module && previous.name == r.name &&
          previous.instanceKey == r.instanceKey do
        throw s!"identity '{r.key}' names both {previous.describe} and {r.describe}; rename one of them (docs/air-json.md §Identity)"

end Air2Lean.Identity
