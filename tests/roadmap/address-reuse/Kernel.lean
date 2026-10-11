import ZigLean.Sep.AddrReuse

/-! The M05 acceptance theorems (`docs/address-reuse.md`), checked by the kernel. `check.sh`
rejects `sorryAx`. -/

open Zig

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

-- (c) Every triple (frame rule included) holds under every placement and provenance mode.
example {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn} (ht : TotalTriple P c Q) {m : Mem}
    {hP hF : Heap} (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq)
    (σ : Placement) (pm : ProvenanceMode) :
    ∃ v m' hQ, c.run (m.withPlacement σ pm) = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
      m'.heap = hQ ∪ hF ∧ Q v hQ ∧ m'.Seq :=
  ht.withPlacement hd hm hp hs σ pm

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
#print axioms Zig.Mem.Seq.alloc
#print axioms Zig.alloc_run
#print axioms Zig.rawAlloc_run
#print axioms Zig.afterAlloc_old
#print axioms Zig.alloc_new_id
#print axioms Zig.access_stale
#print axioms Zig.free_stale
#print axioms Zig.rawFree_stale
#print axioms Zig.Triple.withPlacement
#print axioms Zig.TotalTriple.withPlacement
#print axioms Zig.reuse_witness
#print axioms Zig.fresh_witness
#print axioms Zig.reuse_stale_load
#print axioms Zig.stale_int_strict
#print axioms Zig.stale_int_roundTrip
#print axioms Zig.stale_int_eq
#print axioms Zig.stale_int_liveBlock
#print axioms Zig.stale_int_fresh
