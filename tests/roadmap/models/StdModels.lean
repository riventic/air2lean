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
private def atVersion (version : ZigVersion) (f : Func) : Func :=
  { f with dialect := { f.dialect with version } }

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
    -- The typed projections agree with the row, including anonymous instances.
    for name in #[m.symbol, m.symbol ++ "__anon_7"] do
      require ((stdModel? name).map (·.symbol) == some m.symbol) s!"{name}: lookup"
      require (modelledStdFn name == !(rejectedThreadFn? name).isSome) s!"{name}: disposition"
      require ((allocFn? name).isSome || (threadFn? name).isSome || (rejectedThreadFn? name).isSome) s!"{name}: projection"
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
  -- A row without versions covers only `baseZigVersions`: a newer Zig is listed per row.
  let qualifies (symbol : String) (version : ZigVersion) : Bool :=
    ((stdModel? symbol).map (·.qualifies version)).getD false
  for v in baseZigVersions do
    require (qualifies "Thread.Futex.wait" v && qualifies "mem.Allocator.dupe" v) s!"{v}: base qualification"
  for symbol in #["mem.Allocator.dupe", "mem.Allocator.allocSentinel", "Thread.spawn", "Io.futexWait",
      "Io.Group.await"] do
    require (qualifies symbol .v0_17_0) s!"{symbol}: audited for 0.17.0"
  for symbol in #["Thread.Futex.wait", "time.Timer.read"] do
    require (!qualifies symbol .v0_17_0) s!"{symbol}: not qualified for 0.17.0"
  require (qualifies "Io.futexWaitTimeout" .v0_17_0) "a rejection holds in every version"
  -- C07 detach and the C08 future API are audited for 0.16.0 only.
  for symbol in #["Thread.detach", "Io.async", "Io.checkCancel"] do
    require (!qualifies symbol .v0_17_0) s!"{symbol}: not qualified for 0.17.0"
  expectError (checkProgram #[atVersion .v0_17_0 (caller f "client" "Thread.Futex.wait")])
    "Thread.Futex.wait qualified Zig 0.14.1, 0.15.2, 0.16.0"
  expectError (checkProgram #[atVersion .v0_15_2 (caller f "client" "mem.Allocator.realloc__anon_1")])
    "mem.Allocator.realloc qualified Zig 0.16.0"
  expectError (checkProgram #[atVersion .v0_15_2 (caller f "client" "Thread.detach")])
    "Thread.detach qualified Zig 0.16.0"
  expectError (checkProgram #[caller f "client" "Thread.detach"]) "has an incompatible Thread/void signature"
  expectError (checkProgram #[atVersion .v0_15_2 (caller f "client" "Io.Future(u8).await")])
    "Io.Future.await qualified Zig 0.16.0"
  expectError (checkProgram #[caller f "client" "Io.concurrent__anon_1"])
    "Io.concurrent is not a qualified async API"
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
