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
nodes (`Released`), which the code gives back to the child or keeps. **`reset`** meets the reset
contract in every mode (`reset_spec`, §`reset`'s retaining modes): `free_all` gives every node
back, `retain_capacity` and `retain_with_limit` keep at most one node of each list, resized,
reallocated or given back, which become the arena at epoch `e + 1` (`own_kept`).

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
the bodies and the entries are walked by `fsym`. -/

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

set_option maxHeartbeats 2000000 in
/-- `countListCapacity`'s loop over a list from `it`, by induction on the list (the loop unfolded
once, `Full.loop_run`). -/
theorem count_loop (CI : Child) (free : Bool) :
    ∀ (ns : List NodeV) (it : Option Ptr) (c : BitVec 64),
      FTotalTriple (⟪c.toNat + capOf ns < 2 ^ 64⟫ ⋆ Chain CI free ns it)
        ((Zig.loop heap_ArenaAllocator_countListCapacity.loop6
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
    fsym [heap_ArenaAllocator_countListCapacity.again6.eq_def, toInt_step, count_loop CI free]
  | [], some _, _ | _ :: _, none, _ => by
    rw [Full.loop_run]
    conv in StateT.run heap_ArenaAllocator_countListCapacity.loop6 _ =>
      rw [heap_ArenaAllocator_countListCapacity.loop6]
    fsym

/-- **`countListCapacity`** of a list of whole nodes: the sum of their buffer sizes, which with a
header fits in `2 ^ 63` because the list owns its bytes (`chain_capOf_le`), so the checked `+`
never overflows. -/
theorem count_spec (CI : Child) (ns : List NodeV) (x : Option Ptr) :
    FTotalTriple (Chain CI true ns x) (heap_ArenaAllocator_countListCapacity x)
      (fun c => ⟪c.toNat = capOf ns ∧ capOf ns + 24 ≤ 2 ^ 63⟫ ⋆ Chain CI true ns x) :=
  MemFacts.pre FLogic.total (chain_capOf_le CI ns x) fun _ => by
    unfold heap_ArenaAllocator_countListCapacity
    fsym [count_loop CI true]

section Deinit

variable (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)

/-- The inner loop's invariant: the list from `it` (`FreeList`, its nodes opened). -/
def Inv19 (l : BitVec 64) (s : heap_ArenaAllocator_deinitLocals) : FAssn :=
  FAssn.ex fun ns : List NodeV => ⟪s.local1 = l⟫ ⋆
    (Chain CI true (ns.map NodeV.full) s.it ⋆ FreeCl CI ns ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList))

/-- The inner loop's exit. -/
def Exit19 (l : BitVec 64) (r : heap_ArenaAllocator_deinitExit × heap_ArenaAllocator_deinitLocals) :
    FAssn :=
  ⟪r = (.br18, ⟨l, none⟩)⟫ ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList)

include h in
set_option maxHeartbeats 2000000 in
/-- One node given back to the child (`free` through the vtable; the refund joins the
reservoir). -/
theorem loop19_step (st : heap_ArenaAllocator_State) (l : BitVec 64) (s : heap_ArenaAllocator_deinitLocals) :
    CTriple (Tgt := Tgt) (Inv19 CI l s) ((heap_ArenaAllocator_deinit.loop19 ⟨⟨CI.cctx, CI.vtp⟩, st⟩).run s)
      (fun r => if heap_ArenaAllocator_deinit.again19 r.1 then Inv19 CI l r.2 else Exit19 CI l r) := by
  refine CTriple.ex fun ns => ?_
  rcases s with ⟨l', it⟩
  unfold heap_ArenaAllocator_deinit.loop19
  cases ns <;> cases it <;> simp only [List.map_cons, List.map_nil] <;>
    fsym [CAllocSpec.free h, toInt_step, Child.cown_refund]

include h in
theorem loop19_ct (st : heap_ArenaAllocator_State) (l : BitVec 64) (s : heap_ArenaAllocator_deinitLocals) :
    CTriple (Tgt := Tgt) (Inv19 CI l s)
      ((Zig.loop (heap_ArenaAllocator_deinit.loop19 ⟨⟨CI.cctx, CI.vtp⟩, st⟩)
        heap_ArenaAllocator_deinit.again19).run s)
      (Exit19 CI l) :=
  CTriple.loop (Inv19 CI l) _ (loop19_step CI h st l) s

/-- The lists that `deinit` has not given back yet, from index `k` of `[used_list, free_list]`. -/
def Lists9 (used fl : Option Ptr) (k : BitVec 64) : FAssn :=
  if k = 0 then FreeList CI used ⋆ FreeList CI fl else if k = 1 then FreeList CI fl else emp

/-- The outer loop's invariant. -/
def Inv9 (used fl : Option Ptr) (s : heap_ArenaAllocator_deinitLocals) : FAssn :=
  ⟪s.local1.toNat ≤ 2⟫ ⋆ (Lists9 CI used fl s.local1 ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList))

/-- The outer loop's exit. -/
def Exit9 (r : heap_ArenaAllocator_deinitExit × heap_ArenaAllocator_deinitLocals) : FAssn :=
  FAssn.ex fun s' => ⟪r = (.br8, s')⟫ ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList)

include h in
set_option maxHeartbeats 2000000 in
theorem loop9_step (used fl : Option Ptr) (s : heap_ArenaAllocator_deinitLocals) :
    CTriple (Tgt := Tgt) (Inv9 CI used fl s)
      ((heap_ArenaAllocator_deinit.loop9 ⟨⟨CI.cctx, CI.vtp⟩, ⟨used, fl⟩⟩ #v[used, fl]).run s)
      (fun r => if heap_ArenaAllocator_deinit.again9 r.1 then Inv9 CI used fl r.2 else Exit9 CI r) := by
  rcases s with ⟨l, it⟩
  unfold heap_ArenaAllocator_deinit.loop9
  obtain rfl | rfl | hl : l = 0 ∨ l = 1 ∨ 2 ≤ l.toNat := by bv_omega
  all_goals fsym [loop19_ct CI h]

include h in
theorem loop9_ct (used fl : Option Ptr) (s : heap_ArenaAllocator_deinitLocals) :
    CTriple (Tgt := Tgt) (Inv9 CI used fl s)
      ((Zig.loop (heap_ArenaAllocator_deinit.loop9 ⟨⟨CI.cctx, CI.vtp⟩, ⟨used, fl⟩⟩ #v[used, fl])
        heap_ArenaAllocator_deinit.again9).run s)
      (Exit9 CI) :=
  CTriple.loop (Inv9 CI used fl) _ (loop9_step CI h used fl) s

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

/-! ## `reset`'s retaining modes

`retain_capacity` and `retain_with_limit` sum each list's buffer sizes (`count_spec`), then
`loop66` handles the two lists in turn: `loop78` gives every node of a list back to the child but
the last one, which the arena keeps (`Kept`, `Core.Reset`), resized to the list's share of the
limit (`std.mem.alignBackward(24 + limit, 2)` bytes): given back if that is just the header, kept
as it is if it has that size, else shrunk or grown in place by the child (`resize_shrink`,
`resize_grow`), else replaced by a new node of that size (`alloc_fits`; the old one back,
`node_free`), else kept as it is (the result `ok` false). The child takes every request up to
`2 ^ 63` bytes (`FAllocInv.FitsUpTo`, the hypothesis `hfit`): a kept node holds at most a list's
buffer sizes and a header (`chain_capOf_le`). The kept nodes are the arena at the next epoch
(`own_kept`). Workarounds for engine gaps (fsym-engine ledger, arena rows): the arena struct's child
bytes are a variable with their decoding (`Cm`, row #55); the cases of a list are split before
`fsym` and a node's `next` bytes generalized with their decoding (`loop78_step`, row #55); a loop
rule per head value with a constructor exit (`loop78_some`, `loop78_none`, row #56); the word store
rules first (row #57); a loop rule from its start state (`loop78_ct`, row #59); the child's `free`
and `resize` of a node as rules over the node's atoms (`node_free`, `resize_shrink`, `resize_grow`,
rows #60, #61). -/

/-- `std.mem.alignBackward(x, 2)`: `x` rounded down to even. A step rule for `fsym` (the generated
helper's mask arithmetic, `docs/proof-automation.md` §Debugging). -/
theorem alignBack2_step (x : BitVec 64) :
    FTotalTriple emp (StateT.lift (mem_alignBackward__anon_f056e98f6fd2 x 2))
      (fun r => ⟪r.toNat = x.toNat - x.toNat % 2⟫) := by
  have e : mem_alignBackward__anon_f056e98f6fd2 x 2 =
      pure (x &&& ~~~(BitVec.ofNat 64 (2 ^ 1) - BitVec.ofNat 64 1)) := rfl
  rw [e]
  exact FTotalTriple.of_run fun m r rF hh hp hs =>
    ⟨_, m, r, rfl, hh, ⟨Auto.and_not_lowMask x 1, hp⟩, hs⟩

/-- The packed `size` word of a node from its bits. -/
theorem size_toBits_ofBits (w : BitVec 64) :
    Packed.toBits (Packed.ofBits w : heap_ArenaAllocator_Node_Size) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Packed.toBits, Packed.ofBits, Packed.get, bit0_get, BitVec.shiftLeft_zero,
    BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb']
  rcases i with _ | i
  · cases h : w.getLsbD 0 <;> simp
  · simp [show i < 63 by omega, hi, Nat.add_comm 1 i]
    intro; omega

/-- A store of a node's `size` word from its bits (`wpts_storePacked`, `size_toBits_ofBits`). -/
theorem size_store (p : Ptr) (v : BitVec 64) (x : Nat) :
    FTotalTriple (wpts p v)
      (Zig.store 8 p (Packed.ofBits (BitVec.ofNat 64 x) : heap_ArenaAllocator_Node_Size))
      (fun _ => wpts p (BitVec.ofNat 64 x)) := by
  have := FTotalTriple.wpts_storePacked (p := p) (v := v) (al := 8)
    (Packed.ofBits (BitVec.ofNat 64 x) : heap_ArenaAllocator_Node_Size) rfl (by decide)
  rwa [size_toBits_ofBits] at this

/-- A store of a node's `size` word from its bits over a new node's first 8 bytes
(`region_store_wpts`). -/
theorem region_store_size (p : Ptr) {A S : Nat} {K : BlockKind} {a : Nat} (x : Nat)
    (hA : (A + p.off.toNat) % 8 = 0) :
    FTotalTriple (FAssn.ex fun bs : Array Byte => ⟪bs.size = 8⟫ ⋆ up (regionIn p A S K a bs))
      (Zig.store 8 p (Packed.ofBits (BitVec.ofNat 64 x) : heap_ArenaAllocator_Node_Size))
      (fun _ => wpts p (BitVec.ofNat 64 x)) := by
  have e : Zig.store 8 p (Packed.ofBits (BitVec.ofNat 64 x) : heap_ArenaAllocator_Node_Size) =
      Zig.store 8 p (BitVec.ofNat 64 x) := by
    show Zig.storeBytes p 8 (Enc.encode (Packed.toBits
        (Packed.ofBits (BitVec.ofNat 64 x) : heap_ArenaAllocator_Node_Size))) =
      Zig.storeBytes p 8 (Enc.encode (BitVec.ofNat 64 x))
    rw [size_toBits_ofBits]
  rw [e]; exact FTotalTriple.region_store_wpts _ hA

/-- `Node.Size.fromInt` of an even size of at least the header: its bits. A step rule for `fsym`. -/
theorem fromInt_step (x : BitVec 64) (h24 : 24 ≤ x.toNat) (he : x.toNat % 2 = 0) :
    FTotalTriple emp (StateT.lift (heap_ArenaAllocator_Node_Size_fromInt x))
      (fun r => ⟪r = Packed.ofBits (BitVec.ofNat 64 x.toNat)⟫) := by
  have e : heap_ArenaAllocator_Node_Size_fromInt x = pure (Packed.ofBits (BitVec.ofNat 64 x.toNat)) := by
    have h0 : (Packed.ofBits x : heap_ArenaAllocator_Node_Size).resizing = false := by
      show (BitVec.extractLsb' 0 1 x == 1#1) = false
      rw [bit0_get]
      simp [BitVec.getLsbD, Nat.testBit_zero, he]
    have h24' : Zig.ge false x (24 : BitVec 64) = true := by
      simp only [Zig.ge, Ops.le_eq, decide_eq_true_eq]; simpa using h24
    have hv : Packed.valid (α := heap_ArenaAllocator_Node_Size) x = true := rfl
    unfold heap_ArenaAllocator_Node_Size_fromInt
    simp only [Packed.ofBits?, hv, pure_bind, h24', ↓reduceIte, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
    generalize (Packed.ofBits x : heap_ArenaAllocator_Node_Size) = v at h0 ⊢
    obtain ⟨res, rest⟩ := v
    simp only at h0
    subst h0
    rfl
  rw [e]
  exact FTotalTriple.of_run fun m r rF hh hp hs => ⟨_, m, r, rfl, hh, ⟨rfl, hp⟩, hs⟩

section Retain

attribute [local fsym_arith] encode_nxt_size
attribute [local fsym_facts] MemFacts.region_end

variable (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)
  (hfit : CI.FitsUpTo (2 ^ 63) 3) (ctx : Ptr) (Ac Sc : Nat) (Kc : BlockKind) (cb : Array Byte)

/-- `loop78`'s invariant: the head word `p`, and the list from `it`; `it` is empty only if the
list was. -/
def Inv78 (p : Ptr) (x0 : Option Ptr) (s : heap_ArenaAllocator_resetLocals) : FAssn :=
  FAssn.ex fun ns : List NodeV => ⟪s.it = none → x0 = none⟫ ⋆
    (aptsE p x0 ⋆ Chain CI true (ns.map NodeV.full) s.it ⋆ FreeCl CI ns ⋆ Cm CI ctx Ac Sc Kc cb)

/-- `loop78`'s exits: the list's last node, or an empty list. -/
def Exit78 (p : Ptr) (x0 : Option Ptr) :
    heap_ArenaAllocator_resetExit × heap_ArenaAllocator_resetLocals → FAssn
  | (.br77 N, _) => aptsE p x0 ⋆ Last CI N ⋆ Cm CI ctx Ac Sc Kc cb
  | (.br68, _) => ⟪x0 = none⟫ ⋆ (aptsE p x0 ⋆ Cm CI ctx Ac Sc Kc cb)
  | _ => ⟪False⟫

attribute [local fsym_atom] Chain FreeCl in
include h in
set_option maxHeartbeats 2000000 in
/-- One run of `loop78`'s body: the list's last node is kept (`br77`); any other node goes back to
the child (`free` through the vtable; the refund joins the reservoir). The cases of the list are
split before `fsym` (`chain_one`, `chain_full_cons2`), so the node's `next` is known when it is
loaded (fsym-engine ledger row #55). -/
theorem loop78_step (hd : Enc.decode cb = pure (⟨CI.cctx, CI.vtp⟩ : mem_Allocator)) (hcs : cb.size = 16)
    (p : Ptr) (x0 : Option Ptr) (s : heap_ArenaAllocator_resetLocals) :
    CTriple (Tgt := Tgt) (Inv78 CI ctx Ac Sc Kc cb p x0 s) ((heap_ArenaAllocator_reset.loop78 ctx).run s)
      (fun r => if heap_ArenaAllocator_reset.again78 r.1 then Inv78 CI ctx Ac Sc Kc cb p x0 r.2
        else Exit78 CI ctx Ac Sc Kc cb p x0 r) := by
  refine CTriple.ex fun ns => ?_
  rcases s with ⟨ok, l, it⟩
  unfold heap_ArenaAllocator_reset.loop78
  refine CTriple.lift fun hx => ?_
  rcases ns with _ | ⟨nd, _ | ⟨nd2, ns⟩⟩ <;> cases it
  · have hx0 := hx rfl
    simp only [List.map_nil, Chain, FreeCl]
    fsym
  · exact CTriple.facts (φ := False)
      (fun _ _ _ _ hp _ => by obtain ⟨_, _, -, -, -, _, _, -, -, h1, -⟩ := hp; exact h1.1) False.elim
  · exact CTriple.facts (φ := False)
      (fun _ _ _ _ hp _ => by obtain ⟨_, _, -, -, -, _, _, -, -, h1, -⟩ := hp; exact h1.1) False.elim
  · simp only [List.map_cons, List.map_nil, chain_one, FreeCl]
    fsym [node_free h, toInt_step, Child.cown_refund]
  · exact CTriple.facts (φ := False)
      (fun _ _ _ _ hp _ => by obtain ⟨_, _, -, -, -, _, _, -, -, h1, -⟩ := hp; exact h1.1) False.elim
  · rw [chain_full_cons2, FreeCl.eq_2]
    generalize hbs : (Enc.encode (some nd2.N) : Array Byte) = bs
    have hdec : Enc.decode bs = pure (some nd2.N) := by rw [← hbs]; exact LawfulEnc.decode_encode _
    have hsz : bs.size = 8 := by rw [← hbs]; exact encode_nxt_size _
    clear hbs
    fsym [node_free h, toInt_step, Child.cown_refund]
    exact fun h => nomatch h

include h in
/-- **`loop78`** gives every node of a list back to the child but the last (`CTriple.loop`,
`Inv78`), from the list's head word `p` holding `x` and the list of whole nodes from `x`. A rule
from the loop's start state (fsym-engine ledger row #59). -/
theorem loop78_ct (hd : Enc.decode cb = pure (⟨CI.cctx, CI.vtp⟩ : mem_Allocator)) (hcs : cb.size = 16)
    (p : Ptr) (x : Option Ptr) (ok : Bool) (l : BitVec 64) :
    CTriple (Tgt := Tgt) (aptsE p x ⋆ FreeList CI x ⋆ Cm CI ctx Ac Sc Kc cb)
      ((Zig.loop (heap_ArenaAllocator_reset.loop78 ctx) heap_ArenaAllocator_reset.again78).run ⟨ok, l, x⟩)
      (fun r => FAssn.ex fun e => FAssn.ex fun s' => ⟪r = (e, s')⟫ ⋆ Exit78 CI ctx Ac Sc Kc cb p x (e, s')) := by
  refine CTriple.pre ((CTriple.loop (Inv78 CI ctx Ac Sc Kc cb p x) (Exit78 CI ctx Ac Sc Kc cb p x)
    (loop78_step CI h ctx Ac Sc Kc cb hd hcs p x) ⟨ok, l, x⟩).post fun r r' h =>
      ⟨r.1, r.2, sep_lift.mpr ⟨rfl, h⟩⟩) fun r hr => ?_
  obtain ⟨r₁, r₂, hd', he, h1, h2⟩ := hr
  obtain ⟨ns, h2⟩ := sep_ex.mp h2
  refine ⟨ns, sep_lift.mpr ⟨id, ?_⟩⟩
  show (aptsE p x ⋆ Chain CI true (ns.map NodeV.full) x ⋆ FreeCl CI ns ⋆ Cm CI ctx Ac Sc Kc cb) r
  have h3 : (aptsE p x ⋆ ((Chain CI true (ns.map NodeV.full) x ⋆ FreeCl CI ns) ⋆
    Cm CI ctx Ac Sc Kc cb)) r := ⟨r₁, r₂, hd', he, h1, h2⟩
  exact of_eq (by ac_rfl) h3

include h in
/-- `loop78` over a nonempty list: it exits at the last node (`br77`), the others given back. A
rule per head value, so the exit is a constructor (fsym-engine ledger row #56). -/
theorem loop78_some (hd : Enc.decode cb = pure (⟨CI.cctx, CI.vtp⟩ : mem_Allocator)) (hcs : cb.size = 16)
    (p N0 : Ptr) (ok : Bool) (l : BitVec 64) :
    CTriple (Tgt := Tgt) (aptsE p (some N0) ⋆ FreeList CI (some N0) ⋆ Cm CI ctx Ac Sc Kc cb)
      ((Zig.loop (heap_ArenaAllocator_reset.loop78 ctx) heap_ArenaAllocator_reset.again78).run ⟨ok, l, some N0⟩)
      (fun r => FAssn.ex fun N => FAssn.ex fun s' => ⟪r = (.br77 N, s')⟫ ⋆
        (aptsE p (some N0) ⋆ Last CI N ⋆ Cm CI ctx Ac Sc Kc cb)) :=
  (loop78_ct CI h ctx Ac Sc Kc cb hd hcs p (some N0) ok l).post fun r r' hr => by
    obtain ⟨e, s', h0⟩ := hr
    obtain ⟨rfl, h1⟩ := sep_lift.mp h0
    cases e with
    | br77 N => exact ⟨N, s', sep_lift.mpr ⟨rfl, h1⟩⟩
    | br68 => exact absurd (sep_lift.mp h1).1 (by simp)
    | _ => exact h1.1.elim

/-- `loop78` over an empty list: it exits at once (`br68`). -/
theorem loop78_none (p : Ptr) (ok : Bool) (l : BitVec 64) :
    CTriple (Tgt := Tgt) (aptsE p (none : Option Ptr) ⋆ FreeList CI none ⋆ Cm CI ctx Ac Sc Kc cb)
      ((Zig.loop (heap_ArenaAllocator_reset.loop78 ctx) heap_ArenaAllocator_reset.again78).run ⟨ok, l, none⟩)
      (fun r => FAssn.ex fun s' => ⟪r = (.br68, s')⟫ ⋆ (aptsE p (none : Option Ptr) ⋆ Cm CI ctx Ac Sc Kc cb)) := by
  refine CTriple.pre (P := ⟪(⟨ok, l, none⟩ : heap_ArenaAllocator_resetLocals).it = none⟫ ⋆
    (aptsE p (none : Option Ptr) ⋆ Cm CI ctx Ac Sc Kc cb))
    (CTriple.loop (body := heap_ArenaAllocator_reset.loop78 ctx) (again := heap_ArenaAllocator_reset.again78)
      (fun s : heap_ArenaAllocator_resetLocals => ⟪s.it = none⟫ ⋆
        (aptsE p (none : Option Ptr) ⋆ Cm CI ctx Ac Sc Kc cb))
      (fun r => FAssn.ex fun s' => ⟪r = (heap_ArenaAllocator_resetExit.br68, s')⟫ ⋆
        (aptsE p (none : Option Ptr) ⋆ Cm CI ctx Ac Sc Kc cb))
      (fun s => ?_) _)
    fun r hr => ?_
  · rcases s with ⟨ok', l', it⟩
    unfold heap_ArenaAllocator_reset.loop78
    refine CTriple.lift fun hit => ?_
    subst hit
    fsym
  · rw [freeList_none] at hr
    exact sep_lift.mpr ⟨rfl, of_eq (by simp only [Full.emp_sep_eq]) hr⟩

/-- `loop66`'s invariant: the lists before index `local55` are handled. -/
def Inv66 (pu pf : Ptr) (xu xf : Option Ptr) (s : heap_ArenaAllocator_resetLocals) : FAssn :=
  ⟪s.local55.toNat ≤ 2⟫ ⋆ (Lst CI (decide (0 < s.local55.toNat)) pu xu ⋆
    Lst CI (decide (1 < s.local55.toNat)) pf xf ⋆ Cm CI ctx Ac Sc Kc cb)

/-- `loop66`'s exit: both lists handled. -/
def Exit66 (pu pf : Ptr) (r : heap_ArenaAllocator_resetExit × heap_ArenaAllocator_resetLocals) : FAssn :=
  FAssn.ex fun s' => ⟪r = (.br65, s')⟫ ⋆ (KeptAt CI pu ⋆ KeptAt CI pf ⋆ Cm CI ctx Ac Sc Kc cb)

include h hfit in
set_option maxHeartbeats 4000000 in
/-- One run of `loop66`'s body: the list at index `local55` is handled (`loop78`, then its last
node kept, resized, reallocated or given back; module section doc). -/
theorem loop66_step (hd : Enc.decode cb = pure (⟨CI.cctx, CI.vtp⟩ : mem_Allocator)) (hcs : cb.size = 16)
    (pu pf : Ptr) (xu xf : Option Ptr) (v0 v1 : BitVec 64) (hv0 : v0.toNat + 24 ≤ 2 ^ 63)
    (hv1 : v1.toNat + 24 ≤ 2 ^ 63) (s : heap_ArenaAllocator_resetLocals) :
    CTriple (Tgt := Tgt) (Inv66 CI ctx Ac Sc Kc cb pu pf xu xf s)
      ((heap_ArenaAllocator_reset.loop66 ctx #v[pu, pf] #v[v0, v1]).run s)
      (fun r => if heap_ArenaAllocator_reset.again66 r.1 then Inv66 CI ctx Ac Sc Kc cb pu pf xu xf r.2
        else Exit66 CI ctx Ac Sc Kc cb pu pf r) := by
  rcases s with ⟨ok, l, it⟩
  unfold heap_ArenaAllocator_reset.loop66
  obtain rfl | rfl | hl : l = 0 ∨ l = 1 ∨ 2 ≤ l.toNat := by bv_omega
  · cases xu with
    | none => fsym [loop78_none CI ctx Ac Sc Kc cb]
    | some N0 =>
      fsym [loop78_some CI h ctx Ac Sc Kc cb hd hcs, @FTotalTriple.aptsE_store, @FTotalTriple.wpts_store,
        toInt_step, alignBack2_step, fromInt_step, size_store, region_store_size,
        FTotalTriple.region_store_wpts, FTotalTriple.region_storeAll, node_free h,
        resize_shrink h hfit, resize_grow h hfit, alloc_fits h hfit, Child.cown_refund]
  · cases xf with
    | none => fsym [loop78_none CI ctx Ac Sc Kc cb]
    | some N0 =>
      fsym [loop78_some CI h ctx Ac Sc Kc cb hd hcs, @FTotalTriple.aptsE_store, @FTotalTriple.wpts_store,
        toInt_step, alignBack2_step, fromInt_step, size_store, region_store_size,
        FTotalTriple.region_store_wpts, FTotalTriple.region_storeAll, node_free h,
        resize_shrink h hfit, resize_grow h hfit, alloc_fits h hfit, Child.cown_refund]
  · fsym

include h hfit in
/-- **`loop66`** keeps at most one node of each list (`CTriple.loop`, `Inv66`), from the two head
words holding `xu`, `xf` and the lists of whole nodes from them. -/
theorem loop66_ct (hd : Enc.decode cb = pure (⟨CI.cctx, CI.vtp⟩ : mem_Allocator)) (hcs : cb.size = 16)
    (pu pf : Ptr) (xu xf : Option Ptr) (v0 v1 : BitVec 64) (hv0 : v0.toNat + 24 ≤ 2 ^ 63)
    (hv1 : v1.toNat + 24 ≤ 2 ^ 63) (ok : Bool) (it : Option Ptr) :
    CTriple (Tgt := Tgt) (aptsE pu xu ⋆ FreeList CI xu ⋆ aptsE pf xf ⋆ FreeList CI xf ⋆
        Cm CI ctx Ac Sc Kc cb)
      ((Zig.loop (heap_ArenaAllocator_reset.loop66 ctx #v[pu, pf] #v[v0, v1])
        heap_ArenaAllocator_reset.again66).run ⟨ok, 0, it⟩)
      (Exit66 CI ctx Ac Sc Kc cb pu pf) := by
  refine CTriple.pre (CTriple.loop (Inv66 CI ctx Ac Sc Kc cb pu pf xu xf) (Exit66 CI ctx Ac Sc Kc cb pu pf)
    (loop66_step CI h hfit ctx Ac Sc Kc cb hd hcs pu pf xu xf v0 v1 hv0 hv1) ⟨ok, 0, it⟩) fun r hr => ?_
  simp only [Inv66, Lst]
  exact sep_lift.mpr ⟨by decide, of_eq (by simp; ac_rfl) hr⟩

end Retain

section Reset

set_option maxHeartbeats 4000000 in
/-- `reset` from the released arena (`reset_release`), every mode: `free_all` (and
`retain_with_limit` of `0`) gives both lists back to the child (`deinit_ct`) and leaves no node
(`own_empty`); the retaining modes keep at most one node of each list (`loop66_ct`, `own_kept`). -/
theorem reset_ct (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)
    (hfit : CI.FitsUpTo (2 ^ 63) 3) (γ e : Nat) (ctx : Ptr) (mode : heap_ArenaAllocator_ResetMode)
    (hmode : ∀ v w, mode ≠ .undef_retain_with_limit v w) :
    CTriple (Tgt := Tgt) (Released CI γ e ctx) (heap_ArenaAllocator_reset ctx mode)
      (fun r => ⟪mode = .free_all → r = true⟫ ⋆ (own CI γ (e + 1) ctx ⋆ epTok γ (e + 1) Frac.one)) := by
  have hd := child_decode CI
  have hcs := Child.bytes_size CI
  unfold heap_ArenaAllocator_reset
  cases mode with
  | free_all =>
    refine (show CTriple (Tgt := Tgt) _ _
        (fun r => ⟪r = true⟫ ⋆ (own CI γ (e + 1) ctx ⋆ epTok γ (e + 1) Frac.one)) by
      fsym [deinit_ct CI h, own_empty]).post fun r r' hr => ?_
    exact sep_lift.mpr ⟨fun _ => (sep_lift.mp hr).1, (sep_lift.mp hr).2⟩
  | retain_capacity =>
    refine (show CTriple (Tgt := Tgt) _ _ (fun _ => own CI γ (e + 1) ctx ⋆ epTok γ (e + 1) Frac.one) by
      fsym [count_spec, loop66_ct CI h hfit ctx, own_kept]).post fun r r' hr => ?_
    exact sep_lift.mpr ⟨(fun h => nomatch h), hr⟩
  | retain_with_limit l =>
    refine (show CTriple (Tgt := Tgt) _ _ (fun _ => own CI γ (e + 1) ctx ⋆ epTok γ (e + 1) Frac.one) by
      fsym [deinit_ct CI h, own_empty, count_spec, loop66_ct CI h hfit ctx, own_kept]).post
      fun r r' hr => ?_
    exact sep_lift.mpr ⟨(fun h => nomatch h), hr⟩
  | undef_retain_with_limit v w => exact absurd rfl (hmode v w)

/-- **`reset` meets the reset contract in every mode**: from the arena's state at epoch `e` and the
whole epoch token (no grant outstanding), the arena's state at epoch `e + 1` and that epoch's whole
token. `free_all` gives every node back to the child (and returns `true`); `retain_capacity` and
`retain_with_limit` keep at most one node of each list for the next epoch. For a child that takes
every request up to `2 ^ 63` bytes (`hfit`) and a mode with a defined limit (`hmode`: an
`undefined` limit is read, `.unspecified`). -/
theorem reset_spec (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)
    (hfit : CI.FitsUpTo (2 ^ 63) 3) (γ e : Nat) (ctx : Ptr) (mode : heap_ArenaAllocator_ResetMode)
    (hmode : ∀ v w, mode ≠ .undef_retain_with_limit v w) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ epTok γ e Frac.one) (heap_ArenaAllocator_reset ctx mode)
      (fun r => ⟪mode = .free_all → r = true⟫ ⋆ ((inv CI γ (e + 1) ctx).own ⋆ epTok γ (e + 1) Frac.one)) :=
  CTriple.eupd (reset_release CI γ e ctx) (reset_ct CI h hfit γ e ctx mode hmode)

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
#print axioms AllocArena.ArenaSpec.count_spec
#print axioms AllocArena.Core.own_kept
#print axioms AllocArena.ArenaSpec.reset_spec
