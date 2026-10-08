-- Appended to the fresh `MemModel` translation of memmodel.zig (check.sh). Prints what the
-- model gives for each counterexample, from the generated program-start memory `mem0`.
private def report (name : String) (x : Zig.MemM α) (f : α → String) : IO Unit :=
  match (x.run MemModel.mem0).run with
  | some (.ok (v, _)) => IO.println s!"{name} {f v}"
  | some (.error e) => IO.println s!"{name} error {reprStr e}"
  | none => IO.println s!"{name} diverges"

def main : IO Unit := do
  report "addrOfLocal" MemModel.addrOfLocal (toString ·.toNat)
  report "eqVsAddr" MemModel.eqVsAddr (toString ·.toNat)
  report "crossOrder" MemModel.crossOrder (fun b => if b then "1" else "0")
  report "crossDistance" MemModel.crossDistance (toString ·.toNat)
  report "overAlign" MemModel.overAlign (toString ·.toNat)
