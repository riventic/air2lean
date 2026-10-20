import Lean

/-!
A module's kernel replay as a Lake-built artifact (scripts/assumptions.py `lake_kernel_replay`).

A generated receipt module imports the module `M` it is about and this file, and runs
`run_meta Air2Lean.KernelReplay.run `M`. The toolchain's independent `leanchecker` re-checks
every declaration of `M` against the oleans on the lookup path Lake gave this build, and the
helper logs one line with the result. Lake elaborates the receipt module again exactly when its
trace changes. That trace covers the receipt's text, which names the checker and the installed
runtime, and the trace of `M`, which covers `M`'s olean and every module below it. Otherwise
Lake replays the stored log. So a module is re-checked once per change of itself or of anything
it imports, not once per audit. A failed check is logged like a passing one (the build itself
succeeds), so it is replayed as a failure until an input changes.
-/

open Lean Meta

namespace Air2Lean.KernelReplay

/-- The marker of a receipt line: `AIR2LEAN_KERNEL_REPLAY:` and a JSON object. -/
def marker : String := "AIR2LEAN_KERNEL_REPLAY:"

/-- Run the toolchain's `leanchecker` on `module` and log its receipt line. -/
def run (module : Name) : MetaM Unit := do
  let checker := (← findSysroot) / "bin" / "leanchecker"
  let out ← IO.Process.output { cmd := checker.toString, args := #[module.toString] }
  let text := out.stdout ++ out.stderr
  let receipt := Json.mkObj [("module", toJson module.toString),
    ("status", toJson (if out.exitCode == 0 then "pass" else "fail")),
    ("exit_code", toJson out.exitCode.toNat),
    ("output", toJson (if out.exitCode == 0 then "" else text.takeRight 2000))]
  logInfo (marker ++ receipt.compress)

end Air2Lean.KernelReplay
