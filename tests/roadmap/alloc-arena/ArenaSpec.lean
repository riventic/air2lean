import AllocArena.ArenaLinux
import AllocArena.Core
import AllocArena.Reset
import ZigLean.Sep.Full.AutoAll

/-!
# The translated `ArenaAllocator`'s `free`, `resize` and `remap` against `FAllocSpec`

`free_spec`, `resize_spec`, `remap_spec`: the entries of the translated `std.heap.ArenaAllocator`
(Zig 0.16.0, x86_64-linux, `AllocArena/ArenaLinux.lean`) meet `FAllocSpec`'s contracts for the
arena invariant `inv CI γ e ctx` below, read in the caller's thread (`CTriple`, `Sched.soloRun`),
from the generated code only. No model of the arena is used. `alloc` is not here: the stock arena
does not meet `FAllocSpec`'s `alloc` field for any child (O-E, O-B in `docs/alloc-arena.md`).

**The invariant** `own CI γ e ctx` (for a child allocator `CI : Child`: its invariant, context
pointer `CI.cctx` and vtable `CI.vtp` with entries `CI.fns`; ghost name `γ`, epoch `e`):

* the arena struct at `ctx`: the child allocator (16 bytes `CI.bytes`: `cctx` and `vtp`, not read
  here) and the child's vtable as persistent knowledge (`vtR`), `used_list` and `free_list` as
  pointer-valued atomic words (`aptsE`);
* the ghost authority `gauthP γ e M CI.tag`: the grant map `M` of epoch `e`, grant id ↦ region
  and lent fraction (`docs/sep-full-state.md` §Ghost state), under the child's tag;
* the first node of `used_list`, if any (`FirstPart`): its header words (`size` and `end_index`
  owned words with any atomic tag constraint, `wpts`: the child grants the node as a plain
  region, `HeaderTagCX.lean`; `next` plain), the unused tail of its buffer (from `end_index` on), the child's token
  for the node and the part of the node's extent share that the arena keeps; the other used nodes
  (`rest`, a list of node records `NodeV`) and the free list (`Chain`): headers, tokens and
  shares, the free nodes with their whole buffers;
* the child's state `CI.own`, the junk `JunkAt jh` (bytes that frees which were not the last
  allocation, shrinks and padding leaked back; the arena never touches them until `reset`), one
  receipt per grant together with the grant's fee (`LedgerRcpts`, `ledgerRcpt`: the reset ledger,
  `ZigLean/Sep/Full/ResetLedger.lean`, of which the arena is an instance, `Core.ledger`) and the shares that frees
  gave back (`Pool`).

With no first node, `M` is empty. Every byte of a used node's buffer is in the junk's heap `jh`,
in a grant, or in the first node's unused tail (`OV.Cov`), which `reset` needs to give each node
back whole. Every grant lies in the block of a used node, with that node's
address and kind labels, at a nonnegative offset past that node's header (`GrantOk`). A token for the slice `(p, n)` with
cell labels `A`, `K` is `gfrag γ e i (p, n, q, A, K, φ)` for some grant id `i`, with the fraction `q`
of the grant's extent share (tagged `(γ, e)`) and the fee `φ`: it names exactly that region, so a token of the
current epoch shows `M i = some (p, n, q, A, K, φ)` (`gfrag_mem`), hence a first node: **O-A is excluded by ghost state**, not by a premise, and a `free` of a slice
that this arena did not grant has no token: a permission violation. A token of an older epoch
(after `reset`) is stale: it belongs to `inv … e'` for `e' < e`, whose `own` needs the authority
of epoch `e'`, which no longer exists.

**`free`** loads the first node, compares `buf + end_index` with the slice's end by address
(`ptrEqAddr`), and on a match moves `end_index` back by a strong `cmpxchg`. The comparison is
decided by the blocks and offsets (O-F, `last_dec`): the node and the slice reach their ends by
their extent shares (`Holds.pshareW`), and two live blocks share no byte address
(`Mem.LiveDisjoint.addr_ne`); a slice of the node's block that ends at `buf + end_index` carries
the node's labels (`last_labels`) and lies past the header, which the arena owns (`lo_of`). On a match the slice's bytes rejoin the tail; otherwise (a grant that is not the last
one) they become junk. Either way the grant's share goes back against its receipt into the pool
and the grant is retired (`ledger_return`).

**`resize`** meets the refined contract (`FAllocSpec.resize`, `docs/sep-full-state.md`
§`FAllocSpec` refined): the client gives the token, a part `q'` of the grant's share and only the
bytes a shrink releases. It has the same prefix. A slice that is not the first node's last one only
shrinks (the released bytes become junk); the last one moves `end_index` back (a shrink: the
released bytes rejoin the tail) or forward into the tail when it has room (`Node.loadBuf` reads
the `size` word: `FTriple.atomicLoadAs`, `toInt_ofBits`): the client gets the new bytes with its
labels, and its part of the share is re-lent at the new end against a split receipt
(`ledger_regrow_rcpt`: `brcpt_split`, `EUpd.returnTw`, `EUpd.lendT`, `EUpd.rjoin`). A successful
resize re-points the grant at the new length (`Upd.reassign`; `ledger_shrink`, `ledger_regrow`).
**`remap`** is `resize` (the whole-region form, `FAllocInv.resize_granted_of`) and returns
`memory.ptr`.

**The fee** (`FAllocInv.fee`, `docs/sep-full-state.md` §The fee of a grant) is `epFee γ e φ`, a
nonzero part `φ` of the epoch token `epTok γ e`. `alloc` takes it, the state keeps it with the
grant's receipt, and `free` (and the ghost `grant_return`, which gives a grant back without
running code) gives it back. So a client that holds the whole token `epTok γ e 1` next to `own`
has no outstanding grant (`own_epTok_empty`; `granted_epTok_false`): what a `reset` that gives
the nodes back to the child needs (`ArenaObstruction.not_reset_own`: a `reset` from `own` alone
is unsound).

**`reset`'s ghost part** (`AllocArena/Reset.lean`, `reset_release`): from `own` and the whole epoch
token, the ledger at epoch `e + 1` with that epoch's whole token and both lists as lists of whole
nodes (`Released`), which the code gives back to the child or keeps.

**O-E** (`ArenaObstruction.oob_free_illegal`): the invariant keeps `end_index` within the first
node's buffer (`OV.Facts`: `24 + ei ≤ sz`). A failed `alloc` leaves it past the buffer, so the reachable
states this specification covers end at the first failed `alloc`.
-/

namespace AllocArena.ArenaSpec

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocArena.Core AllocArena.ArenaLinux

arena_spec_statements

/-! ## `deinit` and `reset`

The child enters through `CAllocSpec` of the allocator that the arena's vtable selects among the
module's allocators (`tables`, `CVTable.dispatch`). Each loop is `CTriple.loop` with its invariant;
the bodies and the entries are walked by `fsym`. Workarounds for engine gaps (fsym-engine ledger,
arena rows): the loop posts are `match`es on the exit (a generated `again` test is not decided),
an exit's state is named by an equation of the result, the head stores of `free_all` are a rule
proved by `fsym` without the struct's region, and a node list's empty cases close by
`contradiction`. -/

/-- The alignment argument of the generated entries, from its log2. -/
def al (k : Nat) : mem_Alignment := ⟨BitVec.ofNat 6 k⟩

/-- The module's allocators (`std.heap.page_allocator`, `ArenaAllocator`, `FixedBufferAllocator`):
the entries that an indirect call through the child's vtable can reach. -/
def tables : AllocTables Tgt where
  alloc := [(⟨some 3, 0⟩, fun a => heap_PageAllocator_alloc a.1 a.2.1 (al a.2.2.1) a.2.2.2),
    (⟨some 8, 0⟩, fun a => heap_ArenaAllocator_alloc a.1 a.2.1 (al a.2.2.1) a.2.2.2),
    (⟨some 12, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_alloc a.1 a.2.1 (al a.2.2.1) a.2.2.2))]
  resize := [(⟨some 4, 0⟩, fun a => ConcM.liftMem (heap_PageAllocator_resize a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2)),
    (⟨some 9, 0⟩, fun a => heap_ArenaAllocator_resize a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2),
    (⟨some 13, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_resize a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2))]
  remap := [(⟨some 5, 0⟩, fun a => ConcM.liftMem (heap_PageAllocator_remap a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2)),
    (⟨some 10, 0⟩, fun a => heap_ArenaAllocator_remap a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2),
    (⟨some 14, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_remap a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2))]
  free := [(⟨some 6, 0⟩, fun a => ConcM.liftMem (heap_PageAllocator_free a.1 a.2.1 (al a.2.2.1) a.2.2.2)),
    (⟨some 11, 0⟩, fun a => heap_ArenaAllocator_free a.1 a.2.1 (al a.2.2.1) a.2.2.2),
    (⟨some 15, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_free a.1 a.2.1 (al a.2.2.1) a.2.2.2))]

/-- The child allocator read back from its bytes in the arena struct. -/
theorem child_decode (CI : Child) : Enc.decode CI.bytes = pure (⟨CI.cctx, CI.vtp⟩ : mem_Allocator) := by
  simp only [Enc.decode, Child.decodeAt0, Child.decodeAt8]; rfl

/-- `free_all`'s store of the empty list heads into the two atomic words. -/
theorem reset_heads (ctx : Ptr) (a b : Option Ptr) :
    FTotalTriple (aptsE (ctx.add 16) a ⋆ aptsE (ctx.add 24) b)
      (store 8 (ctx.add 16) ({ used_list := none, free_list := none } : heap_ArenaAllocator_State))
      (fun _ => aptsE (ctx.add 16) (none : Option Ptr) ⋆ aptsE (ctx.add 24) (none : Option Ptr)) := by
  fsym

set_option maxHeartbeats 2000000 in
/-- `countListCapacity`'s loop over a list from `it`, by induction on the list (the loop unfolded
once, `Full.loop_run`). Workaround (fsym-engine ledger row #54): the statement is generic over
the loop's `MonoBind` instance, a proof that `fsym`'s keyed unification compares by its head
(the generated function's `_proof_1` against this statement's own). -/
theorem count_loop (CI : Child) (free : Bool)
    [hm : Lean.Order.MonoBind (MM heap_ArenaAllocator_countListCapacityLocals)] :
    ∀ (ns : List NodeV) (it : Option Ptr) (c : BitVec 64),
      FTotalTriple (⟪c.toNat + capOf ns < 2 ^ 64⟫ ⋆ Chain CI free ns it)
        ((@Zig.loop _ _ _ hm _ heap_ArenaAllocator_countListCapacity.loop6
          heap_ArenaAllocator_countListCapacity.again6).run ⟨c, it⟩)
        (fun r => FAssn.ex fun c' : BitVec 64 =>
          ⟪r = (.br5, ⟨c', none⟩) ∧ c'.toNat = c.toNat + capOf ns⟫ ⋆ Chain CI free ns it)
  | [], none, c => by
    rw [Full.loop_run]
    conv in StateT.run heap_ArenaAllocator_countListCapacity.loop6 _ =>
      rw [heap_ArenaAllocator_countListCapacity.loop6]
    fsym [heap_ArenaAllocator_countListCapacity.again6.eq_def]
  | nd :: ns, some N, c => by
    rw [Full.loop_run]
    conv in StateT.run heap_ArenaAllocator_countListCapacity.loop6 _ =>
      rw [heap_ArenaAllocator_countListCapacity.loop6]
    fsym [heap_ArenaAllocator_countListCapacity.again6.eq_def, toInt_step, @count_loop CI free]
  | [], some _, _ | _ :: _, none, _ => by
    rw [Full.loop_run]
    conv in StateT.run heap_ArenaAllocator_countListCapacity.loop6 _ =>
      rw [heap_ArenaAllocator_countListCapacity.loop6]
    fsym
    all_goals contradiction

/-- **`countListCapacity`** of a list of whole nodes: the sum of their buffer sizes, which fits in
a word because the list owns its bytes (`chain_capOf_lt`), so the checked `+` never overflows. -/
theorem count_spec (CI : Child) (ns : List NodeV) (x : Option Ptr) :
    FTotalTriple (Chain CI true ns x) (heap_ArenaAllocator_countListCapacity x)
      (fun c => ⟪c.toNat = capOf ns⟫ ⋆ Chain CI true ns x) :=
  MemFacts.pre FLogic.total (chain_capOf_lt CI ns x) fun _ => by
    unfold heap_ArenaAllocator_countListCapacity
    fsym [@count_loop CI true]

section Deinit

variable (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)

/-- The inner loop's invariant: the list from `it` (`FreeList`, its nodes opened). -/
def Inv19 (l : BitVec 64) (s : heap_ArenaAllocator_deinitLocals) : FAssn :=
  FAssn.ex fun ns : List NodeV => ⟪s.local1 = l⟫ ⋆
    (Chain CI true (ns.map NodeV.full) s.it ⋆ FreeCl CI ns ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList))

/-- After one run of the inner loop's body. -/
def Post19 (l : BitVec 64) : heap_ArenaAllocator_deinitExit × heap_ArenaAllocator_deinitLocals → FAssn
  | (.rep19, s) => Inv19 CI l s
  | (e, s) => ⟪(e, s) = (.br18, ⟨l, none⟩)⟫ ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList)

include h in
set_option maxHeartbeats 2000000 in
/-- One node given back to the child (`free` through the vtable; the refund joins the
reservoir). -/
theorem loop19_step (st : heap_ArenaAllocator_State) (l : BitVec 64) (s : heap_ArenaAllocator_deinitLocals) :
    CTriple (Tgt := Tgt) (Inv19 CI l s) ((heap_ArenaAllocator_deinit.loop19 ⟨⟨CI.cctx, CI.vtp⟩, st⟩).run s)
      (Post19 CI l) := by
  refine CTriple.ex fun ns => ?_
  rcases s with ⟨l', it⟩
  unfold heap_ArenaAllocator_deinit.loop19
  cases ns <;> cases it <;> simp only [List.map_cons, List.map_nil] <;>
    fsym [CAllocSpec.free h, toInt_step, Child.cown_refund]
  all_goals contradiction

include h in
theorem loop19_ct (st : heap_ArenaAllocator_State) (l : BitVec 64) (s : heap_ArenaAllocator_deinitLocals) :
    CTriple (Tgt := Tgt) (Inv19 CI l s)
      ((Zig.loop (heap_ArenaAllocator_deinit.loop19 ⟨⟨CI.cctx, CI.vtp⟩, st⟩)
        heap_ArenaAllocator_deinit.again19).run s)
      (fun r => ⟪r = (.br18, ⟨l, none⟩)⟫ ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList)) :=
  CTriple.loop (Inv19 CI l) _ (fun s => (loop19_step CI h st l s).post fun r _ hr => by
    rcases r with ⟨e, s'⟩; cases e <;> exact hr) s

/-- The lists that `deinit` has not given back yet, from index `k` of `[used_list, free_list]`. -/
def Lists9 (used fl : Option Ptr) (k : BitVec 64) : FAssn :=
  if k = 0 then FreeList CI used ⋆ FreeList CI fl else if k = 1 then FreeList CI fl else emp

/-- The outer loop's invariant. -/
def Inv9 (used fl : Option Ptr) (s : heap_ArenaAllocator_deinitLocals) : FAssn :=
  ⟪s.local1.toNat ≤ 2⟫ ⋆ (Lists9 CI used fl s.local1 ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList))

/-- After one run of the outer loop's body. -/
def Post9 (used fl : Option Ptr) :
    heap_ArenaAllocator_deinitExit × heap_ArenaAllocator_deinitLocals → FAssn
  | (.rep9, s) => Inv9 CI used fl s
  | (e, s) => FAssn.ex fun s' => ⟪(e, s) = (.br8, s')⟫ ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList)

include h in
set_option maxHeartbeats 2000000 in
theorem loop9_step (used fl : Option Ptr) (s : heap_ArenaAllocator_deinitLocals) :
    CTriple (Tgt := Tgt) (Inv9 CI used fl s)
      ((heap_ArenaAllocator_deinit.loop9 ⟨⟨CI.cctx, CI.vtp⟩, ⟨used, fl⟩⟩ #v[used, fl]).run s)
      (Post9 CI used fl) := by
  rcases s with ⟨l, it⟩
  unfold heap_ArenaAllocator_deinit.loop9
  obtain rfl | rfl | hl : l = 0 ∨ l = 1 ∨ 2 ≤ l.toNat := by bv_omega
  all_goals fsym [loop19_ct CI h, vindex_step]

include h in
theorem loop9_ct (used fl : Option Ptr) (s : heap_ArenaAllocator_deinitLocals) :
    CTriple (Tgt := Tgt) (Inv9 CI used fl s)
      ((Zig.loop (heap_ArenaAllocator_deinit.loop9 ⟨⟨CI.cctx, CI.vtp⟩, ⟨used, fl⟩⟩ #v[used, fl])
        heap_ArenaAllocator_deinit.again9).run s)
      (fun r => FAssn.ex fun s' => ⟪r = (.br8, s')⟫ ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList)) :=
  CTriple.loop (Inv9 CI used fl) _ (fun s => (loop9_step CI h used fl s).post fun r _ hr => by
    rcases r with ⟨e, s'⟩; cases e <;> exact hr) s

include h in
set_option maxHeartbeats 2000000 in
/-- **`deinit` gives every node of both lists back to the child** (the child's `free` through its
vtable, `CAllocSpec`), and each node's fee back into the reservoir (`Child.cown_refund`). -/
theorem deinit_ct (used fl : Option Ptr) :
    CTriple (Tgt := Tgt) (FreeList CI used ⋆ FreeList CI fl ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList))
      (heap_ArenaAllocator_deinit ⟨⟨CI.cctx, CI.vtp⟩, ⟨used, fl⟩⟩)
      (fun _ => CI.cown ⋆ vtR CI.vtp CI.fns.toList) := by
  unfold heap_ArenaAllocator_deinit
  fsym [loop9_ct CI h]

end Deinit

section Reset

attribute [local fsym_atom] own

set_option maxHeartbeats 2000000 in
/-- `reset(.free_all)` from the released arena (`reset_release`): `deinit` gives both lists back
to the child, the list heads become empty, and the arena has no node at epoch `e + 1`
(`own_empty`). -/
theorem reset_free_all_ct (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)
    (γ e : Nat) (ctx : Ptr) :
    CTriple (Tgt := Tgt) (Released CI γ e ctx) (heap_ArenaAllocator_reset ctx .free_all)
      (fun r => ⟪r = true⟫ ⋆ (own CI γ (e + 1) ctx ⋆ epTok γ (e + 1) Frac.one)) := by
  have hd := child_decode CI
  unfold heap_ArenaAllocator_reset
  fsym [deinit_ct CI h, own_empty, reset_heads, heap_ArenaAllocator_ResetMode.tag.eq_def]

/-- **`reset(.free_all)` meets the reset contract**: from the arena's state at epoch `e` and the
whole epoch token (no grant outstanding), the arena's state at epoch `e + 1` and that epoch's
whole token; every node is back with the child. -/
theorem reset_free_all_spec (CI : Child)
    (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv) (γ e : Nat) (ctx : Ptr) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ epTok γ e Frac.one) (heap_ArenaAllocator_reset ctx .free_all)
      (fun r => ⟪r = true⟫ ⋆ ((inv CI γ (e + 1) ctx).own ⋆ epTok γ (e + 1) Frac.one)) :=
  CTriple.eupd (reset_release CI γ e ctx) (reset_free_all_ct CI h γ e ctx)

end Reset

end AllocArena.ArenaSpec

#print axioms AllocArena.ArenaSpec.free_spec
#print axioms AllocArena.ArenaSpec.resize_spec
#print axioms AllocArena.ArenaSpec.remap_spec
#print axioms AllocArena.Core.grant_return
#print axioms AllocArena.Core.own_epTok_empty
#print axioms AllocArena.Core.granted_epTok_false
#print axioms AllocArena.Core.reset_release
#print axioms AllocArena.Core.chain_sizes_le
#print axioms AllocArena.ArenaSpec.deinit_ct
#print axioms AllocArena.ArenaSpec.reset_free_all_spec
#print axioms AllocArena.ArenaSpec.count_spec
