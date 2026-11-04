/-!
A module's kernel replay as a Lake-built artifact (scripts/assumptions.py `lake_kernel_replay`).

A generated receipt module imports this file and runs `#eval Air2Lean.KernelReplay.run "M"` for
the module `M` it is about, which it does not import (importing `M` would run `M`'s `initialize`
code in the receipt's process). The toolchain's independent `leanchecker` re-checks every
declaration of `M` against the oleans on the lookup path Lake gave this build, and the helper
prints one line with the result, which `#eval` logs as the receipt's message. Lake elaborates
the receipt module again exactly when its trace changes. That trace covers the receipt's text,
which names the checker and the installed runtime, and `M`'s olean and dependency trace, which
the receipt's library `needs` (every module below `M`). Otherwise Lake replays the stored log.
So a module is re-checked once per change of itself or of anything it imports, not once per
audit. A failed check is logged like a passing one (the build itself succeeds), so it is
replayed as a failure until an input changes. A checker that did not finish (it could not start,
a signal ended it: exit code 128 + signal, e.g. 137 for a SIGKILL under memory pressure, or its
runtime panicked, e.g. out of memory) decided nothing about `M`: the receipt's build fails instead, so Lake stores no receipt, the
audit fails, and the next build checks `M` again.

This file imports only `Init`: the receipt's process then holds little besides its checker
(importing `Lean` would add about 1.3 GB to every replay running at once).
-/

namespace Air2Lean.KernelReplay

/-- The marker of a receipt line: `AIR2LEAN_KERNEL_REPLAY:` and a JSON object. -/
def marker : String := "AIR2LEAN_KERNEL_REPLAY:"

/-- `s` as a JSON string on one line (RFC 8259: `"` and `\` escaped, control characters and the
line separators U+0085, U+2028 and U+2029, which a reader may split lines on, as `\uXXXX`). -/
def jsonString (s : String) : String :=
  let hex (n : Nat) : String := (Nat.toDigits 16 (0x10000 + n)).drop 1 |> String.ofList
  let body := s.foldl (init := "") fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else if c.toNat < 0x20 || c.toNat == 0x85 || c.toNat == 0x2028 || c.toNat == 0x2029 then
      acc ++ "\\u" ++ hex c.toNat
    else acc.push c
  "\"" ++ body ++ "\""

/-- The toolchain's `leanchecker`: under `LEAN_SYSROOT` (which Lake sets, and which
scripts/assumptions.py hashes the checker under), else beside the running `lean`. -/
def checker : IO System.FilePath := do
  match ← IO.getEnv "LEAN_SYSROOT" with
  | some root => return System.FilePath.mk root / "bin" / "leanchecker"
  | none => return (← IO.appDir) / "leanchecker"

/-- Run the toolchain's `leanchecker` on `module` and print its receipt line; fail when the
checker did not finish: a signal ended it, or the runtime panicked (`INTERNAL PANIC`, such as
running out of memory, exits with code 1 but decides nothing about `module`). -/
def run (module : String) : IO Unit := do
  -- One worker: `leanchecker M` checks `M` and every module `M.*` below it, each in a task of its
  -- own with its own imported environment, so its peak grows with its worker count (a cold
  -- `leanchecker ZigLean` with 16 workers took 25 GB). The receipts' parallelism is Lake's
  -- (scripts/assumptions.py `replay_jobs`), not the checker's.
  let out ← IO.Process.output { cmd := (← checker).toString, args := #[module],
                                env := #[("LEAN_NUM_THREADS", some "1")] }
  let text := out.stdout ++ out.stderr
  let pass := out.exitCode == 0
  let tail := if pass then "" else (text.takeEnd 2000).toString
  if out.exitCode ≥ 128 || (!pass && text.contains "INTERNAL PANIC:") then
    throw <| IO.userError s!"leanchecker {module} did not finish (exit code {out.exitCode}):\n{tail}"
  -- Key order does not matter to the reader (scripts/assumptions.py parses the JSON).
  IO.println <| marker ++ "{\"exit_code\":" ++ toString out.exitCode.toNat ++ ",\"module\":" ++
    jsonString module ++ ",\"output\":" ++ jsonString tail ++
    ",\"status\":" ++ jsonString (if pass then "pass" else "fail") ++ "}"

end Air2Lean.KernelReplay
