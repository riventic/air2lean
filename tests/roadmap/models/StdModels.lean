import Air2Lean
import Air2Lean.Check

/-! E04: the single built-in std model table, same-name rejection and semantic dependency
checks. Run with `lake env lean --run tests/roadmap/models/StdModels.lean`. -/
open Air2Lean Lean
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (e : Except String α) : IO α :=
  match e with | .ok a => pure a | .error error => throw (IO.userError error)
private def expectError {α : Type} (result : Except String α) (part : String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"expected error containing {part}")
  | .error message => require (decide ((message.splitOn part).length > 1)) message

private def allocFns : Array AllocFn :=
  #[.create, .destroy, .alloc, .alignedAlloc, .allocSentinel, .free, .dupe, .remap, .realloc]
private def threadFns : Array ThreadFn :=
  #[.spawn, .join, .detach, .yield, .spinLoopHint, .futexWait, .futexWaitU, .futexWake,
    .threadFutexWait, .threadFutexWake, .osLock, .osUnlock, .osTryLock,
    .timerStart, .timerRead, .futexTimedWait,
    .groupAsync, .groupConcurrent, .groupAwait, .groupCancel,
    .futureAsync, .futureAwait, .futureCancel, .checkCancel]

/-- A call of `callee` with the single `u8` argument of `f`, returning `u8`. -/
private def caller (f : Func) (name callee : String) : Func :=
  { f with name, body := #[{id := 0, ty := 0, op := .arg 0},
    {id := 1, ty := 0, op := .call (.func callee false none) #[.inst 0]},
    {id := 2, ty := 1, op := .ret (.inst 1)}] }

def main : IO Unit := do
  -- One table: unique qualified names, every typed model reachable, dependencies declared.
  let symbols := stdModels.map (·.symbol)
  require (symbols.size == (symbols.foldl (fun s n => s.insert n) ({} : Std.HashSet String)).size)
    "duplicate std model symbol"
  for fn in allocFns do
    require (stdModels.any (·.kind == StdModelKind.alloc fn)) s!"allocator model without a table row: {repr fn}"
  for fn in threadFns do
    require (stdModels.any (·.kind == StdModelKind.thread fn)) s!"thread model without a table row: {repr fn}"
  for m in stdModels do
    match m.kind with
    | .rejected _ => require (m.dependencies.isEmpty && m.zigVersions.isEmpty) s!"{m.symbol}: rejected row with semantics"
    | _ =>
      require (!m.dependencies.isEmpty && m.dependencies.all (·.startsWith "Zig."))
        s!"{m.symbol}: modelled row without ZigLean dependencies"
      -- W2: every modelled row lists its reviewed versions; no row is "every version".
      require (!m.reviewed.isEmpty) s!"{m.symbol}: modelled row without reviewed Zig versions"
      require (m.zigVersions.toList.eraseDups.length == m.zigVersions.size) s!"{m.symbol}: duplicate reviewed version"
      require (m.reviewed.all fun r => r.sha256.length == 64 && !r.file.isEmpty) s!"{m.symbol}: malformed std review"
    -- A Zig version qualifies exactly when the row has a reviewed std source for it (the 0.17.0
    -- audit, docs/std-models.md); an unreviewed release is never qualified.
    require (m.qualifies "0.17.0" == m.reviewed.any (·.zigVersion == "0.17.0"))
      s!"{m.symbol}: 0.17.0 qualification without its reviewed std source"
    require (!m.qualifies "0.18.0") s!"{m.symbol}: qualified for unreviewed Zig 0.18.0"
    -- The typed projections agree with the row in its `--allocator-model`, including
    -- anonymous instances; the row is absent in the other mode.
    for mode in #[AllocatorModel.std, .translated] do
      for name in #[m.symbol, m.symbol ++ "__anon_7"] do
        if m.activeIn mode then
          require ((stdModel? name mode).map (·.symbol) == some m.symbol) s!"{name}: lookup"
          require (modelledStdFn name mode == !(rejectedThreadFn? name).isSome) s!"{name}: disposition"
          require ((allocFn? name mode).isSome || (threadFn? name).isSome || (osFn? name mode).isSome ||
            (rejectedThreadFn? name).isSome) s!"{name}: projection"
        else
          require ((stdModel? name mode).isNone && !modelledStdFn name mode) s!"{name}: inactive row"
  -- Allocator rows are std-only, OS rows translated-only (`docs/allocator-model.md`).
  require (stdModels.all fun m => match m.kind with
    | .alloc _ => m.allocatorModel == some .std
    | .os _ => m.allocatorModel == some .translated && m.zigVersions == #["0.16.0"]
    | _ => m.allocatorModel.isNone) "allocator-model row scopes"
  require ((allocFn? "mem.Allocator.alloc__anon_3" .translated).isNone) "translated allocator wrappers"
  require (osFn? "posix.mmap" .translated == some .mmap && (osFn? "posix.mmap").isNone) "OS projection"
  require ((stdModel? "mem.Allocator.dupeSentinel__anon_1").isNone) "prefix is not a model name"
  require ((stdModel? "project.mem.Allocator.create").isNone) "qualified names are exact"
  require (allocFn? "mem.Allocator.create__anon_3" == some .create) "allocator projection"
  require (threadFn? "Thread.Futex.timedWait" == some .futexTimedWait) "clock projection"
  require ((rejectedThreadFn? "Io.futexWaitTimeout").isSome) "rejection projection"
  require (threadFn? "Thread.detach" == some .detach) "detach projection"
  -- C05: cancelable APIs outside the cancelation model are rejected with their reason; the
  -- modelled cancelation points stay models.
  for name in #["Io.recancel", "Io.swapCancelProtection", "Io.sleep",
      "Io.operate", "Io.Batch.awaitAsync", "Io.Batch.cancel"] do
    require ((rejectedThreadFn? name).isSome) s!"{name}: cancelable API not rejected"
  for name in #["Io.futexWait", "Io.Group.cancel", "Io.Group.await", "Io.checkCancel"] do
    require (modelledStdFn name) s!"{name}: cancelation point not modelled"
  -- C08: methods of instantiated generic types name their generic method.
  require (threadFn? "Io.Future(u32).await" == some .futureAwait) "Future(T).await projection"
  require (threadFn? "Io.Future(error{Canceled}!u32).cancel" == some .futureCancel) "Future(E!T).cancel projection"
  require (threadFn? "Io.Future(foo(bar).Baz).await" == some .futureAwait) "nested type argument"
  require (threadFn? "Io.async__anon_582" == some .futureAsync) "Io.async projection"
  require ((rejectedThreadFn? "Io.Select(union).async__anon_9").isSome) "Select rejection"
  require ((rejectedThreadFn? "Io.concurrent__anon_3").isSome) "Io.concurrent rejection"
  require ((stdModel? "Io.Futurex(u32).await").isNone) "generic prefix is exact"
  require ((stdModel? "Io.async").map (·.zigVersions) == some #["0.16.0"]) "futures are 0.16.0 only"

  let raw ← get <| Raw.parseFile (← IO.FS.readFile "tests/roadmap/models/client.json")
  let f ← get <| normalize raw
  -- A std name called with an incompatible runtime signature is rejected.
  expectError (checkProgram #[caller f "client" "mem.Allocator.create__anon_3"])
    "model callee 'mem.Allocator.create__anon_3' has an incompatible allocator argument signature"
  expectError (checkProgram #[caller f "client" "Thread.join"]) "has an incompatible Thread/void signature"
  -- Version qualification is table data, checked before the typed signature.
  expectError (checkProgram #[{ caller f "client" "mem.Allocator.allocSentinel__anon_1" with zigVersion := "0.15.2" }])
    "mem.Allocator.allocSentinel qualified Zig 0.16.0"
  -- A row qualifies exactly its reviewed versions: a newer Zig is listed per row.
  let qualifies (symbol version : String) : Bool := ((stdModel? symbol).map (·.qualifies version)).getD false
  for v in #["0.14.1", "0.15.2", "0.16.0"] do
    require (qualifies "mem.Allocator.dupe" v) s!"{v}: base qualification"
  -- `std.Thread.Futex` is removed in 0.16.0: reviewed for 0.14.1 and 0.15.2 only.
  for v in #["0.14.1", "0.15.2"] do
    require (qualifies "Thread.Futex.wait" v) s!"{v}: Thread.Futex qualification"
  require (!qualifies "Thread.Futex.wait" "0.16.0") "Thread.Futex.wait: not qualified for 0.16.0"
  for symbol in #["mem.Allocator.dupe", "mem.Allocator.allocSentinel", "Thread.spawn", "Io.futexWait",
      "Io.Group.await"] do
    require (qualifies symbol "0.17.0") s!"{symbol}: audited for 0.17.0"
  for symbol in #["Thread.Futex.wait", "time.Timer.read"] do
    require (!qualifies symbol "0.17.0") s!"{symbol}: not qualified for 0.17.0"
  -- A rejection row qualifies no version; it is rejected in every version.
  require (!qualifies "Io.futexWaitTimeout" "0.17.0" && (rejectedThreadFn? "Io.futexWaitTimeout").isSome)
    "a rejection holds in every version"
  -- C07 detach and the C08 future API are audited for 0.16.0 only.
  for symbol in #["Thread.detach", "Io.async", "Io.checkCancel"] do
    require (!qualifies symbol "0.17.0") s!"{symbol}: not qualified for 0.17.0"
  expectError (checkProgram #[{ caller f "client" "Thread.Futex.wait" with zigVersion := "0.17.0" }])
    "Thread.Futex.wait qualified Zig 0.14.1, 0.15.2"
  expectError (checkProgram #[{ caller f "client" "mem.Allocator.realloc__anon_1" with zigVersion := "0.15.2" }])
    "mem.Allocator.realloc qualified Zig 0.16.0"
  expectError (checkProgram #[{ caller f "client" "Thread.detach" with zigVersion := "0.15.2" }])
    "Thread.detach qualified Zig 0.16.0"
  expectError (checkProgram #[caller f "client" "Thread.detach"]) "has an incompatible Thread/void signature"
  expectError (checkProgram #[{ caller f "client" "Io.Future(u8).await" with zigVersion := "0.15.2" }])
    "Io.Future.await qualified Zig 0.16.0"
  expectError (checkProgram #[caller f "client" "Io.concurrent__anon_1"])
    "Io.concurrent is not a qualified async API"
  -- An empty review list qualifies nothing (it never means "every audited version").
  require (!({ symbol := "mem.Allocator.create", kind := .alloc .create } : StdModel).qualifies "0.16.0")
    "empty review list qualified a version"
  expectError (checkProgram #[{ caller f "client" "Thread.Futex.wait" with zigVersion := "0.16.0" }])
    "no reviewed std source for Zig 0.16.0"
  expectError (checkProgram #[caller f "client" "Thread.spinLoopHint"]) "is not a std declaration"
  -- A translated function cannot reuse a built-in std model name.
  for name in #["Thread.join", "Thread.spawn__anon_4", "Thread.detach", "mem.Allocator.free__anon_9"] do
    expectError (checkProgram #[f, { f with name }]) s!"{name}: translated function conflicts with built-in std model"

  let template ← get <| ModelRegistry.template raw.profile #[f]
  let entry := ((template.getObjValD "models").getArr?.toOption.getD #[])[0]!
  let entry := (← get entry.getObj?).toArray.toList ++ [
    ("import", Json.str "tests.roadmap.models.Model"), ("implementation", .str "RegistryExample.identity"),
    ("contract", .str "RegistryExample.contract"), ("trust", .str "assumed"),
    ("termination", .str "total"), ("errors", .arr #[]), ("effects", .str "preserves"),
    ("dependencies", .arr #[])]
  let models ← get <| ModelRegistry.parse (Json.mkObj [("schema", toJson (1 : Nat)),
    ("models", .arr #[Json.mkObj entry])]).compress
  let model := models[0]!
  let _ ← get <| ModelRegistry.check models raw.profile #[f]
  -- The template never offers a built-in std name, and a binding cannot claim one.
  require ((ModelRegistry.template raw.profile #[caller f "client" "Thread.join"]).toOption.map
    (·.getObjValD "models") == some (.arr #[])) "template offered a built-in std model"
  for symbol in #["mem.Allocator.create", "Thread.detach", "Io.Group.async"] do
    expectError (ModelRegistry.check #[{ model with symbol }] raw.profile #[caller f "client" symbol])
      s!"model '{symbol}' conflicts with translated AIR or a built-in model"
  -- W4: a project binding in a std namespace is an OS primitive or rejected.
  for symbol in #["fmt.format", "heap.PageAllocator.alloc", "mem.Allocator.resize", "Io.Threaded.async",
      "posix.read", "array_list.Aligned(u8,null).append__anon_3"] do
    expectError (ModelRegistry.check #[{ model with symbol }] raw.profile #[caller f "client" symbol])
      s!"model '{symbol}' hand-models std code"
  for symbol in #["os.linux.read", "posix.mmap"] do
    require (projectStdBinding? symbol).isNone s!"{symbol}: OS primitive refused"
    let _ ← get <| ModelRegistry.check #[{ model with symbol }] raw.profile #[caller f "client" symbol]
  -- A user module's names never trigger the std rule (the registry example binds `project.*`).
  for symbol in #["project.identity", "lists.helper", "client.posix.read", "mempool.alloc"] do
    require (projectStdBinding? symbol).isNone s!"{symbol}: user-module name refused as std"
  -- Module identity (B1) decides: a user root module named like a std namespace is user code, a
  -- std-module callee is std code whatever its name. Without module identity (legacy export) the
  -- std namespace match refuses it (fail closed).
  require (projectStdBinding? "posix.helper").isSome "std namespace match without module identity"
  require (projectStdBinding? "posix.helper" (some "root")).isNone "root-module posix.helper refused as std"
  require (projectStdBinding? "fmt.format" (some "std")).isSome "std-module fmt.format accepted"
  require (projectStdBinding? "mempool.alloc" (some "std")).isSome "std module decides, not the name"
  let rootPosix : Func := { caller f "client" "posix.helper" with
    identities := #[{ key := "client", module := some "root", name := "client" },
                    { key := "posix.helper", module := some "root", name := "posix.helper" }] }
  let _ ← get <| ModelRegistry.check #[{ model with symbol := "posix.helper" }] raw.profile #[rootPosix]
  let stdPosix : Func := { rootPosix with
    identities := #[{ key := "client", module := some "root", name := "client" },
                    { key := "posix.helper", module := some "std", name := "posix.helper" }] }
  expectError (ModelRegistry.check #[{ model with symbol := "posix.helper" }] raw.profile #[stdPosix])
    "model 'posix.helper' hand-models std code"
  require ((ModelRegistry.template raw.profile #[caller f "client" "fmt.format"]).toOption.map
    (·.getObjValD "models") == some (.arr #[])) "template offered a std function"
  -- Same-name project binding with an incompatible second call site.
  let wide : Func := { caller f "wide" "project.identity" with
    types := #[.int false 16, .noreturn], layouts := #[{size := some 2, align := some 2}, {}] }
  expectError (ModelRegistry.check models raw.profile #[f, wide])
    "wide: model 'project.identity' has incompatible signature/layout"

  -- Semantic dependencies: bindings, qualified std models or Lean identifiers; acyclic.
  let other : ModelBinding := { model with symbol := "project.other", dependencies := #["project.identity"] }
  let deps (ds : Array String) : ModelBinding := { model with dependencies := ds }
  let _ ← get <| ModelRegistry.checkDependencies
    #[deps #["mem.Allocator.create", "mem.Allocator.allocSentinel", "RegistryExample.identity"], other]
  let _ ← get <| ModelRegistry.checkDependencies #[deps #["project.other"]]
  expectError (ModelRegistry.checkDependencies #[deps #["Zig.x", "Zig.x"]]) "duplicate semantic dependency 'Zig.x'"
  expectError (ModelRegistry.checkDependencies #[deps #["Io.futexWaitTimeout"]])
    "semantic dependency 'Io.futexWaitTimeout' is outside the subset"
  let legacy := { deps #["mem.Allocator.allocSentinel"] with profile := { model.profile with zigVersion := "0.15.2" } }
  expectError (ModelRegistry.checkDependencies #[legacy])
    "semantic dependency 'mem.Allocator.allocSentinel' is not qualified for Zig 0.15.2"
  expectError (ModelRegistry.checkDependencies #[deps #["not a name"]])
    "is not a binding, built-in std model or Lean identifier"
  expectError (ModelRegistry.checkDependencies #[deps #["project.identity"]]) "cyclic semantic dependency"
  expectError (ModelRegistry.checkDependencies #[deps #["project.other"], other]) "cyclic semantic dependency"
  -- The registry check applies them end to end.
  expectError (ModelRegistry.check #[deps #["Io.futexWaitTimeout"]] raw.profile #[f]) "outside the subset"
  IO.println s!"std model registry tests passed ({stdModels.size} rows)"
