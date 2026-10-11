
-- Appended to the fresh AuditIo Gen.lean. Runs each probe under 2^10 binary schedules and a
-- few constant ones (fuel 400, default `available` spawn policy) and prints the distinct
-- outcomes.
private def render : Zig.Result (BitVec 32 × Zig.Mem) → String
  | some (.ok (v, _)) => toString v.toNat
  | some (.error e) => s!"error:{repr e}"
  | none => "no-result"

private def outcomes (main : Zig.ConcM AuditIo.Tgt (BitVec 32)) : Array String := Id.run do
  let mut seen : Array String := #[]
  let oracles : List (Nat → Nat) :=
    (List.range 1024).map (fun k i => (k >>> (i % 10)) % 2) ++
    [fun _ => 0, fun _ => 1, fun _ => 2, fun i => i]
  for o in oracles do
    let r := render (Zig.Sched.run AuditIo.dispatch 400 o main AuditIo.mem0).run
    unless seen.contains r do seen := seen.push r
  return seen

def main : IO Unit := do
  for r in outcomes (AuditIo.cancelProbe {}) do IO.println s!"cancelProbe={r}"
  for r in outcomes (AuditIo.handoffProbe {}) do IO.println s!"handoffProbe={r}"
