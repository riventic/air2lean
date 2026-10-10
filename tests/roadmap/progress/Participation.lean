import ZigLean.Conc.Progress

open Zig

-- The qualification runner replaces this exact line in an isolated mutant artifact.
private def hint : ConcM Unit Unit := spinLoopHint

def main : IO UInt32 := do
  let (_, trace) := Sched.runTrace ⟨.any, .available⟩ (fun _ => pure ()) 10 (fun _ => 0) hint {}
  if trace != #[1] then
    IO.eprintln "C03_ASSERTION: spin scheduler participation lost"
    return 85
  IO.println "Spin scheduler participation checked"
  pure 0
