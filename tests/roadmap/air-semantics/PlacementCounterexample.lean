import ZigLean.Mem

/-! Why a register local is not a memory block related by a memory extension
(docs/air-semantics.md §Locals).

The placement proposes an address by block id (SEM-07) and its fallback `Mem.top` lies past
every block. An extra block (a promoted local kept in memory) shifts the id of every later
block, so the address a later `alloc` gets, and so a value, can differ from the same memory.
Run from the repository root: `lake env lean tests/roadmap/air-semantics/PlacementCounterexample.lean`.
-/

open Zig

/-- One global block (id 0, 4 bytes at 8192); the placement puts block 1 high and block 2 low. -/
def m0 : Mem :=
  { blocks := #[{ bytes := Array.replicate 4 .undef, align := 4, kind := .global, live := true, addr := 8192 }],
    place := { propose := fun b => if b = 1 then some 65536 else if b = 2 then some 16 else none } }

/-- A local kept as a block before the escaping local `q`. -/
def withExtraBlock : MemM Bool := do
  let _x ← allocStack 4 4
  let q ← allocStack 4 4
  ptrLt q ⟨some 0, 0⟩

/-- The local promoted: only `q` is a block. -/
def promoted : MemM Bool := do
  let q ← allocStack 4 4
  ptrLt q ⟨some 0, 0⟩

theorem withExtraBlock_lt : (withExtraBlock.run' m0).run = some (.ok true) := by decide +kernel

theorem promoted_lt : (promoted.run' m0).run = some (.ok false) := by decide +kernel
