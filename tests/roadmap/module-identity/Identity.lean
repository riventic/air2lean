import Air2Lean.Air.Identity
import Air2Lean.Air.Json
import Air2Lean.Check

/-! Module identity keys and program checks (docs/air-json.md §Identity), without a compiler:
`lake env lean tests/roadmap/module-identity/Identity.lean`. -/

open Air2Lean

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def failsWith (r : Except String α) (fragment : String) : Bool :=
  match r with
  | .error e => (e.splitOn fragment).length > 1
  | .ok _ => false

private def json (s : String) : Lean.Json := (Lean.Json.parse s).toOption.get!

private def keysOf (s : String) : Except String (Array String) := do
  let (_, records) ← Identity.rewrite (json s)
  pure (records.map (·.key))

#eval show IO Unit from do
  -- Keys: std and ordinary root names are unchanged; root names in a std namespace and other
  -- modules are qualified; a legacy export keeps its names.
  require (Identity.key (some "std") "Thread.spawn" == "Thread.spawn") "std key"
  require (Identity.key (some "root") "util.helper" == "util.helper") "root key"
  require (Identity.key (some "root") "Thread.spawn" == "root:Thread.spawn") "root std-namespace key"
  require (Identity.key (some "root") "Thread" == "root:Thread") "root Thread type key"
  require (Identity.key (some "root") "atomic.spinLoopHint" == "root:atomic.spinLoopHint") "root atomic key"
  require (Identity.key (some "root") "atomics.x" == "atomics.x") "a longer component is not a std namespace"
  require (Identity.key (some "other") "util.helper" == "other:util.helper") "dependency key"
  require (Identity.key none "Thread.spawn" == "Thread.spawn") "legacy key"
  -- Every lib/std namespace, not only those some lookup uses (soundness audit 2026-10-14 S2: a
  -- user `posix.zig` bound the OS model `posix.mmap`; 0.17.0 adds `lang` and `spirv`).
  for ns in #["posix", "heap", "lang", "spirv", "os", "c"] do
    require (Identity.key (some "root") s!"{ns}.f" == s!"root:{ns}.f") s!"root {ns} key"
  require (Identity.namespaceOf "@typeInfo(Io.Terminal.Mode).@\"union\".tag_type.?" == "Io")
    "namespace inside @typeInfo"
  require (Identity.namespaceOf "Io.Future(u32).await" == "Io") "namespace of a generic method"
  -- A std identity outside the known namespaces fails closed: a root file of that name would
  -- otherwise share std's keys.
  require (failsWith (Identity.checkedKey (some "std") "frobnicate.f") "not a known lib/std namespace")
    "std identity in an unknown namespace accepted"
  require (failsWith (keysOf "{\"name\": \"main.f\", \"module\": \"root\", \"body\": [{\"func\": \"frobnicate.f\", \"module\": \"std\"}]}")
    "not a known lib/std namespace") "std callee in an unknown namespace accepted"
  require (Identity.checkedKey (some "root") "frobnicate.f" == .ok "frobnicate.f") "root key checked"
  -- A standard library other than the reviewed sources (soundness audit 2026-10-14 F1): the
  -- exporter names it `std@modified`, and any identity of it is rejected.
  require (failsWith (Identity.checkedKey (some Identity.modifiedStd) "mem.Allocator.create")
    "not the reviewed lib/std") "a modified std identity accepted"
  require (failsWith (keysOf "{\"name\": \"main.f\", \"module\": \"root\", \"body\": [{\"func\": \"mem.Allocator.create\", \"module\": \"std@modified\"}]}")
    "not the reviewed lib/std") "a modified std callee accepted"
  -- Every identity of an export with a top-level module is rewritten.
  let file := "{\"name\": \"main.entry\", \"module\": \"root\", \"body\": [{\"callee\": " ++
    "{\"func\": \"Thread.spawn__anon_1\", \"module\": \"std\", \"comptime_fn\": \"Thread.run\", " ++
    "\"comptime_fn_module\": \"root\"}}], \"types\": [{\"k\": \"struct\", \"name\": \"Thread\", " ++
    "\"module\": \"root\"}, {\"k\": \"other\", \"name\": \"fn () void\"}], \"globals\": " ++
    "[{\"name\": \"g\", \"module\": \"other\", \"init\": {\"func\": \"f\", \"module\": \"other\"}}]}"
  require (keysOf file == .ok #["main.entry", "root:Thread", "other:g", "other:f",
    "Thread.spawn__anon_1", "root:Thread.run"]) s!"rewrite keys: {repr (keysOf file)}"
  -- An identified export names the module of every identity; a legacy one of none.
  require (failsWith (keysOf "{\"name\": \"f\", \"module\": \"root\", \"body\": [{\"func\": \"g\"}]}")
    "missing 'module'") "missing callee module accepted"
  require (failsWith (keysOf "{\"name\": \"f\", \"body\": [{\"func\": \"g\", \"module\": \"root\"}]}")
    "without a top-level module") "module in a legacy export accepted"
  require (failsWith (keysOf "{\"name\": \"f\", \"module\": \"\"}") "must not be empty")
    "empty module accepted"
  -- Program checks: one (module, name) per key; no mixing of identified and legacy files.
  let r (key name : String) (module : Option String) : Identity.Record := { key, module, name }
  require (Identity.checkProgram #[#[r "f" "f" (some "root")], #[r "g" "g" (some "std"), r "f" "f" (some "root")]] == .ok ())
    "consistent program rejected"
  require (failsWith (Identity.checkProgram #[#[r "f" "f" (some "root")], #[r "f" "f" (some "std")]])
    "names both") "root/std name collision accepted"
  require (failsWith (Identity.checkProgram #[#[r "f" "f" (some "root")], #[r "g" "g" none]])
    "cannot be combined") "legacy and identified files mixed"
  require (Identity.checkProgram #[#[r "f" "f" none], #[r "g" "g" none]] == .ok ()) "legacy program rejected"
  -- The parser: a root `Thread` struct is a struct, a std one the model handle type.
  let ty (module : String) := s!"\{\"k\": \"struct\", \"name\": \"Thread\", \"module\": \"{module}\", " ++
    "\"layout\": \"auto\", \"fields\": [{\"name\": \"id\", \"ty\": 0}]}"
  let rawTypes (module : String) : Except String (Array Ty) := do
    let (j, _) ← Identity.rewrite (json s!"\{\"name\": \"f\", \"module\": \"root\", \"types\": [{ty module}]}")
    (← (← j.getObjVal? "types").getArr?).mapM Raw.parseTy
  require (match rawTypes "root" with | .ok #[.struct "root:Thread" ..] => true | _ => false) "root Thread type"
  require (match rawTypes "std" with | .ok #[.thread] => true | _ => false) "std Thread type"
  IO.println "module identity unit checks passed"
