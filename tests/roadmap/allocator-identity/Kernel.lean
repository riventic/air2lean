import ZigLean.Sep.ArenaClient

/-! The M01 acceptance theorems, checked by the kernel. `check.sh` rejects `sorryAx`. -/

open Zig

-- (a) Cross-allocator frees are illegal, for every allocator pair.
example (r : AllocRef) {m : Mem} {size : Nat} {s : Slice} {b : BlockId} {blk : Block}
    (hn : size * s.len.toNat ≠ 0) (hpb : s.ptr.block = some b)
    (hblk : m.blocks[b]? = some blk) (hk : blk.kind ≠ r.kind) :
    (r.free size s).run m = throw .illegal :=
  r.free_foreign hn hpb hblk hk

-- (b) A reset invalidates exactly the allocator's blocks.
example (m : Mem) (a : AllocId) : (m.resetOwned a).heap = m.heap.dropOwned a :=
  Mem.heap_resetOwned m a

-- (c) The production-style client.
example (reqs : List (List (Array (BitVec 8)))) (hn : ∀ req ∈ reqs, ∀ f ∈ req, f.size < 2 ^ 64)
    (m : Mem) (hst : m.Seq) (hfresh : ∀ l c, m.heap l = some c → c.kind ≠ .owned m.allocators.size) :
    ∃ rs m', (session reqs).run m = pure (rs, m') ∧ Outcomes rs reqs ∧ m'.heap = m.heap ∧
      m'.Seq :=
  session_restores reqs hn m hst hfresh

#print axioms Zig.AllocRef.free_foreign
#print axioms Zig.AllocRef.destroy_foreign
#print axioms Zig.AllocRef.remap_foreign
#print axioms Zig.Mem.heap_resetOwned
#print axioms Zig.Mem.resetOwned_other
#print axioms Zig.Mem.resetOwned_access_own
#print axioms Zig.Mem.resetOwned_access_other
#print axioms Zig.Owned.reset_spec
#print axioms Zig.Arena.deinit_spec
#print axioms Zig.ownedRawAlloc_fixedBuffer_run
#print axioms Zig.handleRequest_spec
#print axioms Zig.session_spec
#print axioms Zig.session_restores
