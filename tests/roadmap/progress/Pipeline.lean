import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

open Air2Lean

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def fixture (name : String) (op : Op) (ret : TyId := 0) : Func :=
  { dialect := .ofVersion .v0_16_0, targetOs := "linux", name, params := #[], ret,
    types := #[.void, .errorSet (some #["SystemCannotYield"]), .errorUnion 1 0,
      .noreturn, .int false 8, .errorSet (some #["Other"]), .errorUnion 5 0, .int false 64],
    layouts := Array.replicate 8 {}, globals := #[],
    body := #[{ id := 0, ty := ret, op }, { id := 1, ty := 3, op := .ret (.inst 0) }] }

private def accepted (f : Func) : IO Unit := do
  match check f >>= fun _ => checkProgram #[f] with
  | .ok () => pure ()
  | .error e => throw (IO.userError e)

private def rejected (f : Func) (part : String) : IO Unit := do
  match check f >>= fun _ => checkProgram #[f] with
  | .ok () => throw (IO.userError s!"{f.name}: invalid progress signature accepted")
  | .error e => require ((e.splitOn part).length > 1) s!"wrong rejection: {e}"

def main (args : List String) : IO Unit := do
  let output := args.headD "/tmp/air2lean-progress-pipeline.lean"
  for version in ZigVersion.all do
    let spin := { (fixture "spin" (.asm "pause" true #[] #[] #[])) with dialect := .ofVersion version }
    -- `isb` is the aarch64 spin hint only (Air2Lean/AsmAllowlist.lean).
    let arm := { (fixture "armSpin" (.asm "isb" true #[] #[] #[])) with
      dialect := { version, arch := "aarch64" } }
    -- `Thread.yield` is translated from std; its OS call is the OSY-01 row (`os.linux.sched_yield`).
    let yielding := { (fixture "yielding" (.call (.func "os.linux.sched_yield" false none) #[]) 7) with
      dialect := .ofVersion version }
    accepted spin
    accepted arm
    accepted yielding
    require ((memoryFunctions #[spin, arm, yielding]).size == 3) "hints must use memory"
    require ((concFunctions #[spin, arm, yielding]).size == 3) "hints must use the scheduler"
    require ((collectAsmOps #[spin, arm]).isEmpty) "audited hints must not become opaque asm"
  -- `Thread.yield` has no model: without its AIR it fails closed.
  rejected (fixture "yieldNoAir" (.call (.func "Thread.yield" false none) #[]) 2) "no AIR"
  rejected (fixture "badYieldVoid" (.call (.func "os.linux.sched_yield" false none) #[])) "() usize"
  rejected (fixture "badYieldArgs" (.call (.func "os.linux.sched_yield" false none) #[.void]) 7) "() usize"
  rejected (fixture "badYieldLibc" (.call (.func "extern:sched_yield" false none) #[]) 7) "macOS libc"
  rejected (fixture "badSpinType" (.asm "pause" true #[] #[] #[]) 4) "must return void"
  -- `atomic.spinLoopHint` is `inline` (its instruction is the hint above), so it has no model:
  -- a call of it without its AIR fails closed (docs/std-models.md §Retiring the hand models).
  rejected (fixture "spinCall" (.call (.func "atomic.spinLoopHint" false none) #[])) "no AIR"
  rejected (fixture "badNoreturn" (.call (.func "os.linux.sched_yield" true none) #[]) 7) "noreturn"
  rejected (fixture "badClobber" (.asm "pause" true #["memory"] #[] #[])) "memory"
  for source in ["pause; ud2", "yield", "or 27, 27, 27", "pause(#1)"] do
    let f := fixture "opaqueHint" (.asm source true #[] #[] #[])
    require (!f.syncLocally) "non-audited asm must not become a modeled hint"
    -- L13: asm off the reviewed allowlist is rejected, not a repeatable opaque.
    rejected f "allowlist"
  require (!(Op.asm "pause" false #[] #[] #[]).isSpinHint) "nonvolatile asm is not a hint"
  require (!(Op.asm "pause" true #["cc"] #[] #[]).isSpinHint) "clobbered asm is not a hint"
  let fs := #[fixture "spin" (.asm "pause" true #[] #[] #[]),
    fixture "yielding" (.call (.func "os.linux.sched_yield" false none) #[]) 7]
  IO.FS.writeFile output (emit fs "ProgressPipeline" "" .ieee)
  if let some directory := (args.drop 1).head? then
    for version in ZigVersion.all do
      let versioned := fs.map fun f => { f with dialect := .ofVersion version }
      IO.FS.writeFile (System.FilePath.mk directory / s!"ProgressPipeline-{version}.lean")
        (emit versioned "ProgressPipeline" "" .ieee)
  IO.println "Progress pipeline regressions passed"
