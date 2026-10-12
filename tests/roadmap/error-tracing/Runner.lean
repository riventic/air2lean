
-- Appended to the error-tracing translation by check.sh: the native `main`'s lines.
private def observed (x : Zig.MemM α) : IO α :=
  match (x.run {}).run with
  | some (.ok (v, _)) => pure v
  | some (.error e) => throw (IO.userError s!"unexpected modeled error: {reprStr e}")
  | none => throw (IO.userError "unexpected modeled divergence")

def main : IO Unit := do
  for x in ([0, 1, 5] : List Nat) do
    IO.println s!"traced {x} {(← observed (ErrorTracing.error_tracing_traced (BitVec.ofNat 64 x))).toNat}"
    IO.println s!"handledTwice {x} {(← observed (ErrorTracing.error_tracing_handledTwice (BitVec.ofNat 64 x))).toNat}"
