import ZigLean.Mem.Reuse
import ZigLean.Sep.Full.AutoAll

/-! The M05 acceptance theorems (`docs/address-reuse.md`), checked by the kernel. `check.sh`
rejects `sorryAx`. -/

open Zig Zig.Full

-- (a) Lifetime safety from provenance: after a free, any number of allocations at any
-- addresses (also the freed block's) leave the stale pointer dangling.
example {m : Mem} {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (hd : blk.live = false) (allocs : List (BlockKind × Nat × Nat)) (off : Int) (n a : Nat) :
    (allocs.foldl (fun m (k, s, al) => m.afterAlloc k s al) m).access ⟨some b, off⟩ n a =
      throw .illegal :=
  access_stale hb hd allocs off n a

-- (b) No double free, whatever block now has the address.
example {m : Mem} {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (hd : blk.live = false) (off : Int) : (free ⟨some b, off⟩).run m = throw .illegal :=
  free_stale hb hd off

-- (c) Every triple (frame rule included) holds under every placement and provenance mode:
-- total triples return, partial triples keep their postcondition.
example {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} (ht : FTotalTriple P c Q) {m : Mem}
    {r rF : Res} (hh : Holds m r rF) (hp : P r) (hs : m.FSeq) (σ : Placement) (pm : ProvenanceMode) :
    ∃ v m' r', c.run (m.withPlacement σ pm) = pure (v, m') ∧ Holds m' r' rF ∧ Q v r' ∧ m'.FSeq :=
  ht.withPlacement hh hp hs σ pm

example {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} (ht : FTriple P c Q) {m : Mem}
    {r rF : Res} (hh : Holds m r rF) (hp : P r) (hs : m.FSeq) (σ : Placement) (pm : ProvenanceMode) :
    match (c.run (m.withPlacement σ pm)).run with
    | none => True
    | some (.error e) => e = .stackOverflow
    | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FSeq :=
  ht.withPlacement hh hp hs σ pm

-- (c') The same for a client walked by `fsym` from the library's `alloc` and `free` rules:
-- `reuseRun`'s allocate, free, allocate again (the shape whose second block takes the first
-- block's address under `reuseFirst`) keeps any frame `R`, under every placement.
def reuseCycle : MemM Unit := do
  let p ← alloc .heap 8 8
  free p
  let q ← alloc .heap 8 8
  free q

theorem reuseCycle_spec (R : FAssn) : FTriple R reuseCycle (fun _ => R) := by
  unfold reuseCycle
  fsym

example (R : FAssn) {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : R r) (hs : m.FSeq)
    (σ : Placement) (pm : ProvenanceMode) :
    match (reuseCycle.run (m.withPlacement σ pm)).run with
    | none => True
    | some (.error e) => e = .stackOverflow
    | some (.ok (_, m')) => ∃ r', Holds m' r' rF ∧ R r' ∧ m'.FSeq :=
  (reuseCycle_spec R).withPlacement hh hp hs σ pm

-- (d) A new block's address range is clear of every live block under every placement (and
-- nothing about order or gaps).
example (m : Mem) (size align : Nat) {l : Loc} {c : Cell} (hc : m.heap l = some c) :
    size = 0 ∨ c.addr + c.size ≤ m.newAddr size align ∨ m.newAddr size align + size ≤ c.addr :=
  Mem.newAddr_clear m size align hc

-- (e) Reuse happens; the naive address argument is false under the default provenance mode.
example : runValue reuseRun (({} : Mem).withPlacement reuseFirst) = some (.ok (4096, 4096, some 1)) :=
  reuse_witness
example : runValue staleIntRun (({} : Mem).withPlacement reuseFirst) ≠ some (.ok 7#64) := by
  rw [stale_int_strict]; decide

#print axioms Zig.Mem.newAddr_clear
#print axioms Zig.afterAlloc_old
#print axioms Zig.alloc_new_id
#print axioms Zig.access_stale
#print axioms Zig.free_stale
#print axioms Zig.Full.Holds.withPlacement
#print axioms Zig.Full.FTriple.withPlacement
#print axioms Zig.Full.FTotalTriple.withPlacement
#print axioms Zig.Full.FTriple.alloc
#print axioms Zig.Full.FTotalTriple.rawAlloc
#print axioms Zig.Full.FTotalTriple.free
#print axioms reuseCycle_spec
#print axioms Zig.reuse_witness
#print axioms Zig.fresh_witness
#print axioms Zig.reuse_stale_load
#print axioms Zig.stale_int_strict
#print axioms Zig.stale_int_roundTrip
#print axioms Zig.stale_int_eq
#print axioms Zig.stale_int_liveBlock
#print axioms Zig.stale_int_fresh
