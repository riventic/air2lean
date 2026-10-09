-- Appended to the fresh `OobPtr` translation of oob_ptr.zig (check.sh). Runs under the
-- harness's concrete placement (`Zig.Placement.fresh`).
private def okBool (x : Zig.MemM Bool) : String :=
  match (x.run' (OobPtr.mem0 .fresh)).run with
  | some (.ok v) => if v then "1" else "0"
  | some (.error e) => s!"error {reprStr e}"
  | none => "diverges"

def main : IO Unit := do
  let big : BitVec 64 := BitVec.ofNat 64 (2 ^ 63)
  IO.println s!"oobCompare(1) {okBool (OobPtr.oobCompare 1)}"
  IO.println s!"oobCompare(2^63) {okBool (OobPtr.oobCompare big)}"
  IO.println s!"oobPtrCompare(2^63) {okBool (OobPtr.oobPtrCompare big)}"
