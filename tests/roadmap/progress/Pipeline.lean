import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

open Air2Lean

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def fixture (name : String) (op : Op) (ret : TyId := 0) : Func :=
  { zigVersion := "0.16.0", name, params := #[], ret,
    types := #[.void, .errorSet (some #["SystemCannotYield"]), .errorUnion 1 0,
      .noreturn, .int false 8, .errorSet (some #["Other"]), .errorUnion 5 0],
    layouts := Array.replicate 7 {}, globals := #[],
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
  for version in supportedVersions do
    let spin := { (fixture "spin" (.asm "pause" true #[] #[] #[])) with zigVersion := version }
    let arm := { (fixture "armSpin" (.asm "isb" true #[] #[] #[])) with zigVersion := version }
    let yielding := { (fixture "yielding" (.call (.func "Thread.yield" false none) #[]) 2) with zigVersion := version }
    accepted spin
    accepted arm
    accepted yielding
    require ((memoryFunctions #[spin, arm, yielding]).size == 3) "hints must use memory"
    require ((concFunctions #[spin, arm, yielding]).size == 3) "hints must use the scheduler"
    require ((collectAsmOps #[spin, arm]).isEmpty) "audited hints must not become opaque asm"
  rejected (fixture "badYieldVoid" (.call (.func "Thread.yield" false none) #[])) "error union"
  rejected (fixture "badYieldError" (.call (.func "Thread.yield" false none) #[]) 6) "SystemCannotYield"
  rejected (fixture "badYieldArgs" (.call (.func "Thread.yield" false none) #[.void]) 2) "not 0"
  rejected (fixture "badSpinType" (.asm "pause" true #[] #[] #[]) 4) "must return void"
  rejected (fixture "badSpinCall" (.call (.func "atomic.spinLoopHint" false none) #[]) 4) "must return void"
  rejected (fixture "badNoreturn" (.call (.func "Thread.yield" true none) #[]) 2) "noreturn"
  rejected (fixture "badClobber" (.asm "pause" true #["memory"] #[] #[])) "memory"
  for source in ["pause; ud2", "yield", "or 27, 27, 27", "pause(#1)"] do
    let f := fixture "opaqueHint" (.asm source true #[] #[] #[])
    require (!f.syncLocally) "non-audited asm must not become a modeled hint"
    require ((collectAsmOps #[f]).size == 1) "non-audited asm must stay opaque"
  require (!(Op.asm "pause" false #[] #[] #[]).isSpinHint) "nonvolatile asm is not a hint"
  require (!(Op.asm "pause" true #["cc"] #[] #[]).isSpinHint) "clobbered asm is not a hint"
  let fs := #[fixture "spin" (.asm "pause" true #[] #[] #[]),
    fixture "yielding" (.call (.func "Thread.yield" false none) #[]) 2]
  IO.FS.writeFile output (emit fs "ProgressPipeline" "" .ieee)
  if let some directory := (args.drop 1).head? then
    for version in supportedVersions do
      let versioned := fs.map fun f => { f with zigVersion := version }
      IO.FS.writeFile (System.FilePath.mk directory / s!"ProgressPipeline-{version}.lean")
        (emit versioned "ProgressPipeline" "" .ieee)
  IO.println "Progress pipeline regressions passed"
