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
* `root`: the name itself (the historical spelling), unless it starts with a namespace of
  `lib/std` (`stdNamespaces`, the complete list): then `root:<name>`, which no std model or
  special type matches. A std identity outside that list is rejected (`checkedKey`), so a bare
  key in a std namespace is always std's.
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

/-- Every top-level namespace of `lib/std` (its files and directories) in every supported Zig
version (0.14.1, 0.15.2, 0.16.0, 0.17.0). A std name starts with one of them, so a `root` name
that starts with one gets the key `root:<name>`, and no std model, OS primitive, special std type
or panic handler, whichever namespace it is in, can match a root name. The list is complete, not
the namespaces some lookup happens to use: `rewrite` rejects a std identity in any other
namespace (`namespaceOf`), and `tests/roadmap/models/test_std_sources.py` compares it with the
`lib/std` of each Zig version present. -/
def stdNamespaces : Array String := #[
  "BitStack", "Build", "DoublyLinkedList", "Io", "Progress", "Random", "RingBuffer",
  "SemanticVersion", "SinglyLinkedList", "Target", "Thread", "Uri", "array_hash_map",
  "array_list", "ascii", "atomic", "base64", "bit_set", "bounded_array", "buf_map", "buf_set",
  "builtin", "c", "coff", "compress", "crypto", "debug", "deque", "dwarf", "dynamic_library",
  "elf", "enums", "fifo", "fmt", "fs", "gpu", "hash", "hash_map", "heap", "http", "io", "json",
  "lang", "leb128", "linked_list", "log", "macho", "math", "mem", "meta", "multi_array_list",
  "net", "once", "os", "pdb", "pie", "posix", "priority_dequeue", "priority_queue", "process",
  "segmented_list", "simd", "sort", "spirv", "start", "static_string_map", "std", "tar",
  "testing", "time", "treap", "tz", "unicode", "valgrind", "wasm", "zig", "zip", "zon"]

/-- The namespace a fully qualified name starts with: its first identifier, inside any
`@typeInfo(` (a type such as `@typeInfo(Io.Terminal.Mode).@"union".tag_type.?`). -/
partial def namespaceOf (name : String) : String :=
  if name.startsWith "@typeInfo(" then namespaceOf (name.drop "@typeInfo(".length).toString
  else String.ofList (name.toList.takeWhile fun c => c.isAlphanum || c == '_')

/-- The key of `name` in `module` (`none`: a legacy export). -/
def key (module : Option String) (name : String) : String :=
  match module with
  | none | some "std" => name
  | some "root" => if stdNamespaces.contains (namespaceOf name) then "root:" ++ name else name
  | some m => m ++ ":" ++ name

/-- The module name the exporter gives a standard library whose sources are not the reviewed
`lib/std` of the pinned release (`zig-patch/air-json/identity.zig` `modified_std`): an edited
copy through `--zig-lib-dir`, or `-Mstd=`. -/
def modifiedStd : String := "std@modified"

/-- `key`, failing closed on a std identity outside `stdNamespaces` (a namespace of a new Zig
version that the list misses would let a root file of that name share std's keys) and on an
unreviewed standard library (`modifiedStd`): the std models, special types and panic handlers
are reviewed against the pinned sources only (soundness audit 2026-10-14, F1). -/
def checkedKey (module : Option String) (name : String) : Except String String := do
  if module == some modifiedStd then
    throw s!"'{name}' is from a standard library whose sources are not the reviewed lib/std of this Zig release (an edited --zig-lib-dir or -Mstd): the std models are reviewed against the pinned sources only; export with the unmodified std (docs/air-json.md §Identity)"
  if module == some "std" && !stdNamespaces.contains (namespaceOf name) then
    throw s!"std identity '{name}' is in namespace '{namespaceOf name}', which is not a known lib/std namespace; add it to Identity.stdNamespaces (docs/air-json.md §Identity)"
  pure (key module name)

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
  let k ← checkedKey module name
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
    let own ← checkedKey module name
    modify (·.push { key := own, module, name, instanceKey := ← instanceOf "function" name j "instance_key" })
    let mut j := j.setObjVal! "name" (.str own)
    j ← mapArray j "types" fun t =>
      match (t.getObjValAs? String "k").toOption with
      | some "struct" | some "enum" | some "union" => qualify legacy "type" t "name" "module"
      | _ => pure t
    j ← mapArray j "globals" fun g => do refs legacy (← qualify legacy "global" g "name" "module")
    mapArray j "body" (refs legacy)
  go.run #[]

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
