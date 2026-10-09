-- Appended to the fresh `MemModel` translation of memmodel.zig (check.sh). Prints what the
-- model gives for each fixture from the generated program-start memory `mem0 σ`, under the
-- harness's concrete placement (`Zig.Placement.fresh`) and under placements that put the
-- fixture's stack blocks where a native build can put them (MM-1): `adjacent` places block 1
-- right after block 0 (as the native frame does for two `[8]u8` locals), `misaligned` places
-- block 0 at an address that is not 4096-aligned, `high` moves block 0 up.
def placeAt (as : List (Nat × Nat)) : Zig.Placement := ⟨fun b => (as.find? (·.1 == b)).map (·.2)⟩

private def report (name : String) (σ : Zig.Placement) (x : Zig.MemM α) (f : α → String) :
    IO Unit :=
  match (x.run (MemModel.mem0 σ)).run with
  | some (.ok (v, _)) => IO.println s!"{name} {f v}"
  | some (.error e) => IO.println s!"{name} error {reprStr e}"
  | none => IO.println s!"{name} diverges"

def main : IO Unit := do
  let fresh := Zig.Placement.fresh
  report "addrOfLocal" fresh MemModel.addrOfLocal (toString ·.toNat)
  report "addrOfLocal@high" (placeAt [(0, 1 <<< 40)]) MemModel.addrOfLocal (toString ·.toNat)
  report "eqVsAddr" fresh MemModel.eqVsAddr (toString ·.toNat)
  report "eqVsAddr@adjacent" (placeAt [(0, 8192), (1, 8196)]) MemModel.eqVsAddr (toString ·.toNat)
  report "crossOrder" fresh MemModel.crossOrder (fun b => if b then "1" else "0")
  report "crossOrder@swapped" (placeAt [(0, 8192), (1, 4096)]) MemModel.crossOrder
    (fun b => if b then "1" else "0")
  report "crossDistance" fresh MemModel.crossDistance (toString ·.toNat)
  report "crossDistance@adjacent" (placeAt [(0, 8192), (1, 8200)]) MemModel.crossDistance
    (toString ·.toNat)
  report "overAlign" fresh MemModel.overAlign (toString ·.toNat)
  report "overAlign@misaligned" (placeAt [(0, 4097)]) MemModel.overAlign (toString ·.toNat)
