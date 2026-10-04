import ZigLean.Conc.Progress

open Zig

-- The qualification runner replaces this exact line in an isolated mutant artifact.
private def hint : ConcM Unit Unit := spinLoopHint

def main : IO Unit := do
  let (_, trace) := Sched.runTrace (fun _ => pure ()) 10 (fun _ => 0) hint {}
  unless trace = #[1] do
    throw (IO.userError "spin scheduler participation lost")
  IO.println "Spin scheduler participation checked"
