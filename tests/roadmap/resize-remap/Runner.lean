
-- Append to the fresh, receipt-bound RemapProbe Gen.lean after the normal import.
private def checkSource (mode : Zig.ByteRemapMode) (expected : Nat) : IO Unit := do
  let m : Zig.Mem := { RemapProbe.mem0 .fresh with allocPolicy := { maxBytes := 16, byteRemap := mode } }
  match ((RemapProbe.exercise {}).run m).run with
  | some (.ok (.ok value, final)) =>
    unless value.toNat == expected && final.blocks.all (fun b => !b.live) do
      throw (IO.userError "actual generated remap client returned wrong bytes/frame/outcome or leaked")
    IO.println s!"{expected}"
  | _ => throw (IO.userError "actual generated remap client errored or had no result")

def main : IO Unit := do
  checkSource .inPlace 101
  checkSource .move 201
  checkSource .fail 301
