/-!
The assurance extractor's driver as a Lake-built artifact (scripts/assumptions.py
`lake_extraction`). A generated driver module imports this file and runs
`#eval Air2Lean.AssuranceRun.run "<extractor>" #[<arguments>]`: the compiled extractor
(`tools/AssuranceMain.lean`) runs as its own process on the lookup path Lake gave this build, and
its report line, printed here, is the driver's message, which Lake stores in its build log. A
failed extractor fails the driver's build. This file imports only `Init`, so the driver's process
holds little besides the extractor.
-/

namespace Air2Lean.AssuranceRun

/-- Run the extractor `exe` with `args` and print its report; fail when it fails. -/
def run (exe : String) (args : Array String) : IO Unit := do
  let out ← IO.Process.output { cmd := exe, args }
  if out.exitCode != 0 then
    throw <| IO.userError s!"assurance extractor exited {out.exitCode}:\n{out.stderr}"
  IO.print out.stdout

end Air2Lean.AssuranceRun
