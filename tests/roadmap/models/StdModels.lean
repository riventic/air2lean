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
  #[.spawn, .join, .detach, .futexWait, .futexWaitU, .futexWake,
    .threadFutexWait, .threadFutexWake, .osLock, .osUnlock, .osTryLock,
    .groupAsync, .groupConcurrent, .groupAwait, .groupCancel,
    .futureAsync, .futureAwait, .futureCancel, .checkCancel]

/-- `f` as a function of Zig `version`. -/
private def atVersion (version : ZigVersion) (f : Func) : Func :=
  { f with dialect := { f.dialect with version } }

/-- A call of `callee` with the single `u8` argument of `f`, returning `u8`. -/
private def caller (f : Func) (name callee : String) : Func :=
  { f with name, body := #[{id := 0, ty := 0, op := .arg 0},
    {id := 1, ty := 0, op := .call (.func callee false none) #[.inst 0]},
    {id := 2, ty := 1, op := .ret (.inst 1)}] }

def main : IO Unit := do
  -- One table: unique qualified names, every typed model reachable, dependencies declared.
  let symbols := stdModels.map (·.symbol)
  -- Every name a std lookup matches is in a lib/std namespace, so a root name it could match
  -- has the key `root:<name>` (`Identity.key`, soundness audit 2026-10-14 S2). An extern callee
  -- (`extern:<symbol>`) is a linker identity, which no function name can take.
  for name in symbols ++ osPrimitiveBindings ++ ownerCheckedUnlocks do
    require ((externSymbol? name).isSome || Identity.stdNamespaces.contains (Identity.namespaceOf name))
      s!"{name}: not in a lib/std namespace (Identity.stdNamespaces)"
  require (symbols.size == (symbols.foldl (fun s n => s.insert n) ({} : Std.HashSet String)).size)
    "duplicate std model symbol"
  for fn in allocFns do
    require (stdModels.any (·.kind == StdModelKind.alloc fn)) s!"allocator model without a table row: {repr fn}"
  for fn in threadFns do
    require (stdModels.any (·.kind == StdModelKind.thread fn)) s!"thread model without a table row: {repr fn}"
  for m in stdModels do
    match m.kind with
    | .rejected _ =>
      require (m.dependencies.isEmpty && m.zigVersions.isEmpty && m.premise.isNone)
        s!"{m.symbol}: rejected row with semantics"
    | kind =>
      require (!m.dependencies.isEmpty && m.dependencies.all (·.startsWith "Zig."))
        s!"{m.symbol}: modelled row without ZigLean dependencies"
      -- Every model names its premise: an OS premise (`OS*-<nn>`, docs/premises.md) for an OS
      -- primitive, a transitional STD-<nn> (a hand model of std code, docs/std-models.md
      -- §Retiring the hand models) otherwise.
      let osRow := match kind with | .os _ => true | _ => false
      let family : String := if osRow then "OS" else "STD-"
      require ((m.premise.getD "").startsWith family)
        s!"{m.symbol}: modelled row without its premise"
      -- W2: every modelled row lists its reviewed versions; no row is "every version".
      require (!m.reviewed.isEmpty) s!"{m.symbol}: modelled row without reviewed Zig versions"
      require (m.zigVersions.toList.eraseDups.length == m.zigVersions.size) s!"{m.symbol}: duplicate reviewed version"
      require (m.reviewed.all fun r => r.sha256.length == 64 && !r.file.isEmpty) s!"{m.symbol}: malformed std review"
    -- A Zig version qualifies exactly when the row has a reviewed std source for it (the 0.17.0
    -- audit, docs/std-models.md); an unreviewed release is never qualified.
    for v in ZigVersion.all do
      require (m.qualifies v == m.reviewed.any (·.zigVersion == v))
        s!"{m.symbol}: {v} qualification without its reviewed std source"
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
    -- The page-mapping rows are translated-allocator-only; the other OS rows are active in
    -- every mode (their std callers, `Thread.yield`, are translated in both).
    | .os .mmap | .os .munmap | .os .mremap =>
      m.allocatorModel == some .translated && m.zigVersions == #[.v0_16_0]
    | _ => m.allocatorModel.isNone) "allocator-model row scopes"
  require ((allocFn? "mem.Allocator.alloc__anon_3" .translated).isNone) "translated allocator wrappers"
  require (osFn? "posix.mmap" .translated == some .mmap && (osFn? "posix.mmap").isNone) "OS projection"
  require (osFn? "os.linux.sched_yield" == some .schedYield && osFn? "extern:sched_yield" == some .cSchedYield)
    "OSY-01 projection in every allocator model"
  -- `Thread.yield` has no model: it is translated from std down to `sched_yield` (OSY-01).
  require (stdModel? "Thread.yield").isNone "Thread.yield is translated"
  require ((stdModel? "mem.Allocator.dupeSentinel__anon_1").isNone) "prefix is not a model name"
  require ((stdModel? "project.mem.Allocator.create").isNone) "qualified names are exact"
  require (allocFn? "mem.Allocator.create__anon_3" == some .create) "allocator projection"
  -- `time.Timer` and `Thread.Futex.timedWait` have no model: they are translated from std down
  -- to `clock_gettime` (OSK-01) and the timed futex wait (OSF-01).
  for name in #["time.Timer.start", "time.Timer.read", "Thread.Futex.timedWait"] do
    require (stdModel? name).isNone s!"{name} is translated"
  require (osFn? "os.linux.clock_gettime" == some .clockGettime &&
    osFn? "extern:clock_gettime" == some .cClockGettime) "OSK-01 projection"
  require ((stdModels.filter fun m => match m.kind with
      | .os fn => fn.env | _ => false).map (·.premise) == #[some "OSK-01", some "OSK-01"])
    "the environment rows are the clocks"
  require (osFn? "os.linux.futex_4arg" == some .futex4 && osFn? "extern:__ulock_wait2" == some .ulockWait2)
    "OSF-01 projection"
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
  require ((stdModel? "Io.async").map (·.zigVersions) == some #[.v0_16_0]) "futures are 0.16.0 only"

  let raw ← get <| Raw.parseFile (← IO.FS.readFile "tests/roadmap/models/client.json")
  let f ← get <| normalize raw
  -- A std name called with an incompatible runtime signature is rejected.
  expectError (checkProgram #[caller f "client" "mem.Allocator.create__anon_3"])
    "model callee 'mem.Allocator.create__anon_3' has an incompatible allocator argument signature"
  expectError (checkProgram #[caller f "client" "Thread.join"]) "has an incompatible Thread/void signature"
  -- Version qualification is table data, checked before the typed signature.
  expectError (checkProgram #[atVersion .v0_15_2 (caller f "client" "mem.Allocator.allocSentinel__anon_1")])
    "mem.Allocator.allocSentinel qualified Zig 0.16.0"
  -- A row qualifies exactly its reviewed versions: a newer Zig is listed per row.
  let qualifies (symbol : String) (version : ZigVersion) : Bool :=
    ((stdModel? symbol).map (·.qualifies version)).getD false
  for v in [ZigVersion.v0_14_1, .v0_15_2, .v0_16_0] do
    require (qualifies "mem.Allocator.dupe" v) s!"{v}: base qualification"
  -- `std.Thread.Futex` is removed in 0.16.0: reviewed for 0.14.1 and 0.15.2 only.
  for v in [ZigVersion.v0_14_1, .v0_15_2] do
    require (qualifies "Thread.Futex.wait" v) s!"{v}: Thread.Futex qualification"
  require (!qualifies "Thread.Futex.wait" .v0_16_0) "Thread.Futex.wait: not qualified for 0.16.0"
  for symbol in #["mem.Allocator.dupe", "mem.Allocator.allocSentinel", "Thread.spawn", "Io.futexWait",
      "Io.Group.await"] do
    require (qualifies symbol .v0_17_0) s!"{symbol}: audited for 0.17.0"
  for symbol in #["Thread.Futex.wait", "Thread.Futex.wake"] do
    require (!qualifies symbol .v0_17_0) s!"{symbol}: not qualified for 0.17.0"
  -- An OS row with an environment (`OsFn.env`) checks its signature like any OS row, and every
  -- function that reaches it, and only those, takes the OS environment (`envFunctions`).
  expectError (checkProgram #[caller f "client" "os.linux.clock_gettime"]) "has an incompatible"
  let clockUser := caller f "clockUser" "os.linux.clock_gettime"
  let clockCaller := caller f "clockCaller" "clockUser"
  let other := caller f "other" "os.linux.sched_yield"
  require (envFunctions #[clockUser, clockCaller, other] == #["clockUser", "clockCaller"])
    "envFunctions: the callers of an environment row, transitively"
  require (envFunctions #[other] == #[]) "envFunctions: sched_yield takes no environment"
  -- A rejection row qualifies no version; it is rejected in every version.
  require (!qualifies "Io.futexWaitTimeout" .v0_17_0 && (rejectedThreadFn? "Io.futexWaitTimeout").isSome)
    "a rejection holds in every version"
  -- C07 detach and the C08 future API are audited for 0.16.0 only.
  for symbol in #["Thread.detach", "Io.async", "Io.checkCancel"] do
    require (!qualifies symbol .v0_17_0) s!"{symbol}: not qualified for 0.17.0"
  expectError (checkProgram #[atVersion .v0_17_0 (caller f "client" "Thread.Futex.wait")])
    "Thread.Futex.wait qualified Zig 0.14.1, 0.15.2"
  expectError (checkProgram #[atVersion .v0_15_2 (caller f "client" "mem.Allocator.realloc__anon_1")])
    "mem.Allocator.realloc qualified Zig 0.16.0"
  expectError (checkProgram #[atVersion .v0_15_2 (caller f "client" "Thread.detach")])
    "Thread.detach qualified Zig 0.16.0"
  expectError (checkProgram #[caller f "client" "Thread.detach"]) "has an incompatible Thread/void signature"
  expectError (checkProgram #[atVersion .v0_15_2 (caller f "client" "Io.Future(u8).await")])
    "Io.Future.await qualified Zig 0.16.0"
  expectError (checkProgram #[caller f "client" "Io.concurrent__anon_1"])
    "Io.concurrent is not a qualified async API"
  -- An empty review list qualifies nothing (it never means "every audited version").
  require (!({ symbol := "mem.Allocator.create", kind := .alloc .create } : StdModel).qualifies .v0_16_0)
    "empty review list qualified a version"
  expectError (checkProgram #[atVersion .v0_16_0 (caller f "client" "Thread.Futex.wait")])
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
  let _ ← get <| ModelRegistry.check #[{ model with symbol := "os.linux.read" }] raw.profile
    #[caller f "client" "os.linux.read"]
  -- `posix.mmap` is the built-in OS boundary of `--allocator-model translated` (OSM-01): a
  -- project binding never shadows it, in either mode.
  expectError (ModelRegistry.check #[{ model with symbol := "posix.mmap" }] raw.profile
    #[caller f "client" "posix.mmap"]) "model 'posix.mmap' conflicts with translated AIR or a built-in model"
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
  let rootPosix : Func := { caller f "client" "root:posix.helper" with
    identities := #[{ key := "client", module := some "root", name := "client" },
                    { key := "root:posix.helper", module := some "root", name := "posix.helper" }] }
  require (Identity.key (some "root") "posix.helper" == "root:posix.helper") "root posix key"
  let _ ← get <| ModelRegistry.check #[{ model with symbol := "root:posix.helper" }] raw.profile #[rootPosix]
  let stdPosix : Func := { caller f "client" "posix.helper" with
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
