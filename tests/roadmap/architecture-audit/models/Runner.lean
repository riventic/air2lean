
-- Appended to the fresh AuditAlloc Gen.lean. Runs both probes under a spread of allocation
-- policies (default, every byte-remap mode, first attempt failing) and prints one line each.
private def policies : List (String × Zig.AllocPolicy) :=
  [("default", {}),
   ("inPlace", { byteRemap := .inPlace }),
   ("move", { byteRemap := .move }),
   ("fail0", { failures := [0] })]

private def render {α : Type} [ToString α] : Zig.Result (Except Zig.ErrName α × Zig.Mem) → String
  | some (.ok (.ok v, _)) => toString v
  | some (.ok (.error e, _)) => s!"error.{e}"
  | some (.error e) => s!"illegal:{repr e}"
  | none => "diverges"

def main : IO Unit := do
  for (name, p) in policies do
    let m : Zig.Mem := { AuditAlloc.mem0 with allocPolicy := p }
    IO.println s!"aliasProbe[{name}]={render (((AuditAlloc.aliasProbe {}).run m).run.map (·.map fun (r, s) => (r.map (·.toNat), s)))}"
    IO.println s!"remapProbe[{name}]={render (((AuditAlloc.remapProbe {}).run m).run.map (·.map fun (r, s) => (r.map (·.toNat), s)))}"
