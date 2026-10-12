import VectorFields.Gen
import Show

/-! `vector_fields.zig` (Zig 0.14.1, 0.15.2): kernel-checked results, then `main` prints the lines
of `native.zig`'s cases. -/

open Zig VectorFields PackedCastsShow

def result {α : Type} (f : MemM α) : Option (Except Error α) :=
  ((f.run (mem0 .fresh)).run).map (·.map Prod.fst)

theorem setVector_ok : result (setVector 1 2 3) = some (.ok 0x321a) := by decide +kernel
theorem lane1_ok : (lane1 0x321A#16).run = some (.ok 2) := by decide +kernel
theorem laneSum_ok : result (laneSum 0x321A#16) = some (.ok 6) := by decide +kernel

def main : IO Unit := do
  let m := mem0 .fresh
  lineM "setVector" m (setVector 1 2 3)
  line "lane1" (lane1 0x321A#16)
  lineM "laneSum" m (laneSum 0x321A#16)
