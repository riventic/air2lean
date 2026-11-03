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
or a signal ended it: exit code 128 + signal, e.g. 137 for a SIGKILL under memory pressure)
decided nothing about `M`: the receipt's build fails instead, so Lake stores no receipt, the
audit fails, and the next build checks `M` again.

This file imports only `Init`: the receipt's process then holds little besides its checker
(importing `Lean` would add about 1.3 GB to every replay running at once).
-/

namespace Air2Lean.KernelReplay

/-- The marker of a receipt line: `AIR2LEAN_KERNEL_REPLAY:` and a JSON object. -/
def marker : String := "AIR2LEAN_KERNEL_REPLAY:"

/-- `s` as a JSON string (RFC 8259: `"` and `\` escaped, control characters as `\u00XX`). -/
def jsonString (s : String) : String :=
  let hex (n : Nat) : Char := "0123456789abcdef".toList[n % 16]!
  let body := s.foldl (init := "") fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else if c.toNat < 0x20 then acc ++ "\\u00" ++ (hex (c.toNat / 16)).toString ++ (hex c.toNat).toString
    else acc.push c
  "\"" ++ body ++ "\""

/-- Run the toolchain's `leanchecker` (beside the running `lean`) on `module` and print its
receipt line; fail when the checker did not finish. -/
def run (module : String) : IO Unit := do
  let checker := (← IO.appDir) / "leanchecker"
  let out ← IO.Process.output { cmd := checker.toString, args := #[module] }
  let text := out.stdout ++ out.stderr
  let tail := String.ofList (text.toList.drop (text.length - 2000))
  if out.exitCode ≥ 128 then
    throw <| IO.userError s!"leanchecker {module} did not finish (exit code {out.exitCode}):\n{tail}"
  let pass := out.exitCode == 0
  IO.println <| marker ++ "{\"exit_code\":" ++ toString out.exitCode.toNat ++ ",\"module\":" ++
    jsonString module ++ ",\"output\":" ++ jsonString (if pass then "" else tail) ++
    ",\"status\":" ++ jsonString (if pass then "pass" else "fail") ++ "}"

end Air2Lean.KernelReplay
