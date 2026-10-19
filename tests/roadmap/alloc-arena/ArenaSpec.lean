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
  atomic words, `wpts`: the thread rules of the atomic ops take them, `Core.Header`; `next`
  plain), the unused tail of its buffer (from `end_index` on), the child's token
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

**The proofs** are the invariant, `fsym` and the updates at the returns (`fsym [u]`,
`docs/proof-automation.md`): `fsym` walks each entry's generated code from `own` with the
library's rules, and each return is closed by the update of its branch (`Core.free_last_upd`, …).
The invariant supplies the facts about a grant that its token does not carry (`Core.grant_facts`,
`Core.grant_first`, `Core.grant_live`).

**`free`** loads the first node, compares `buf + end_index` with the slice's end by address
(`ptrEqAddr`), and on a match moves `end_index` back by a strong `cmpxchg`. The comparison is
decided by the blocks and offsets (O-F, the library rule `ptrEqAddr_live`): the node and the slice
reach their ends by their extent shares, both blocks are live below the pointers (owned bytes: the
node's `next` word, and for the slice the `next` word of the node it lies past, `grant_live`), and
two live blocks share no byte address (`Mem.LiveDisjoint.addr_ne`); a slice of the node's block
that ends at `buf + end_index` carries the node's labels and lies past the header, which the arena
owns. On a match the slice's bytes rejoin the tail; otherwise (a grant that is not the last
one) they become junk. Either way the grant's share goes back against its receipt into the pool
and the grant is retired (`ledger_return`).

**`resize`** meets the refined contract (`FAllocSpec.resize`, `docs/sep-full-state.md`
§`FAllocSpec` refined): the client gives the token, a part `q'` of the grant's share and only the
bytes a shrink releases. It has the same prefix. A slice that is not the first node's last one only
shrinks (the released bytes become junk); the last one moves `end_index` back (a shrink: the
released bytes rejoin the tail) or forward into the tail when it has room (`Node.loadBuf` reads
the `size` word: `FTTriple.atomicLoadAs`; `fsym` reads the packed `Node.Size` through its
`Packed` instance): the client gets the new bytes with its
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

**`reset`'s retaining modes** (`reset_retain_capacity_spec`, `reset_retain_with_limit_spec`)
meet the same contract as `free_all`: from `Released`, each list gives every node back to the
child but its last one, which it keeps, resized to its share of the limit in place, replaced by a
new node from the child, or as it is (`loop78_ct`, `loop66_ct`); the kept nodes, whole and empty,
are the arena at epoch `e + 1` (`own_kept`). The child takes every request up to `2 ^ 63` bytes
(`FAllocInv.FitsUpTo`).

**O-E** (`ArenaObstruction.oob_free_illegal`): the invariant keeps `end_index` within the first
node's buffer (`OV.Facts`: `24 + ei ≤ sz`). A failed `alloc` leaves it past the buffer, so the reachable
states this specification covers end at the first failed `alloc`.
-/

namespace AllocArena.ArenaSpec

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocArena.Core AllocArena.ArenaLinux

/-! ## `free`, `resize` and `remap` -/

set_option maxHeartbeats 2000000 in
/-- `free`'s run, case by case (module doc). -/
theorem free_ct (CI : Child) (γ e : Nat) (ctx s : _) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k φ bs)
      (heap_ArenaAllocator_free ctx s ⟨BitVec.ofNat 6 k⟩ ra)
      (fun _ => (inv CI γ e ctx).own ⋆ (inv CI γ e ctx).fee φ) := by
  unfold heap_ArenaAllocator_free
  fsym [free_other_upd, free_last_upd]

/-- **`free` meets `FAllocSpec`'s `free` field** for the arena invariant at every epoch, every
child `CI` (`Child`), and every depth of the one-thread reading (`Sched.soloRun`). -/
theorem free_spec (CI : Child) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (ra : BitVec 64) (φ : Frac) (bs : Array Byte) (hlen : s.len.toNat = bs.size)
    (hpos : 0 < bs.size) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k φ bs)
      (Sched.soloRun fuel (heap_ArenaAllocator_free ctx s ⟨BitVec.ofNat 6 k⟩ ra))
      (fun _ => (inv CI γ e ctx).own ⋆ (inv CI γ e ctx).fee φ) :=
  (free_ct CI γ e ctx s k ra φ bs hlen hpos).toSolo fuel

set_option maxHeartbeats 10000000 in
/-- `resize`'s run, case by case, against the refined contract (`FAllocSpec.resize`): from the
token, the client's part `q'` of the grant's share and the bytes a shrink releases. A slice that
is not the first node's last one only shrinks (the released bytes become junk); the last one moves
`end_index` (shrink, or growth into the tail when it fits: the client gets the new bytes, its part
of the share is re-lent at the new end). A successful resize re-points the grant at the new
length (`Upd.reassign`). The updates take the released bytes' length, labels and bytes from the
statement. The workaround for engine ledger rows #64 and #return-bool-split: `n` against `len` is split before
the walk (the released bytes' `if`, and the returned `n <= len`). -/
theorem resize_ct (CI : Child) (γ e : Nat) (ctx s : _) (k : Nat) (n ra : BitVec 64)
    (A S : Nat) (K : BlockKind) (q q' φ : Frac) (tl : Array Byte) (hpos : 0 < s.len.toNat)
    (hn : 0 < n.toNat) (hq : q'.val ≤ q.val) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ ((inv CI γ e ctx).held s.ptr s.len.toNat k A S K q q' φ ⋆
        (inv CI γ e ctx).relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (heap_ArenaAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((inv CI γ e ctx).rresizePost s.ptr k s.len.toNat n.toNat A S K q q' φ tl) := by
  unfold heap_ArenaAllocator_resize
  rcases Nat.lt_trichotomy n.toNat s.len.toNat with hc | hc | hc <;>
  fsym [resize_other_upd (S := S) (k := k) (n := n.toNat) (tl := tl),
    resize_shrink_upd (S := S) (k := k) (n := n.toNat) (tl := tl),
    resize_grow_upd (S := S) (k := k) (n := n.toNat) (tl := tl),
    resize_false_upd (S := S) (k := k) (n := n.toNat) (tl := tl)]

/-- The whole-region `resize` (`FAllocInv.resize_granted_of`). -/
theorem resize_granted_ct (CI : Child) (γ e : Nat) (ctx s : _) (k : Nat) (n ra : BitVec 64)
    (φ : Frac) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size)
    (hn : 0 < n.toNat) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k φ bs)
      (heap_ArenaAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((inv CI γ e ctx).resizePost s.ptr k φ bs n.toNat) :=
  (inv CI γ e ctx).resize_granted_gen (T := CTriple) (fun h hp => CTriple.pre h hp)
    (fun h => CTriple.frame h) (fun h => CTriple.ex h) (fun h hu => CTriple.eupd_post h hu)
    (fun A S K q q' tl h1 _ => resize_ct CI γ e ctx s k n ra A S K q q' φ tl (by omega) hn h1) hlen

/-- `remap` is `resize`, and returns `memory.ptr` when it succeeds. -/
theorem remap_ct (CI : Child) (γ e : Nat) (ctx s : _) (k : Nat) (n ra : BitVec 64)
    (φ : Frac) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size)
    (hn : 0 < n.toNat) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k φ bs)
      (heap_ArenaAllocator_remap ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((inv CI γ e ctx).remapPost s.ptr k φ bs n.toNat) := by
  unfold heap_ArenaAllocator_remap
  fsym [resize_granted_ct CI γ e ctx s k n ra φ bs hlen hpos hn]

/-- **`resize` meets `FAllocSpec`'s refined `resize` field** for the arena invariant at every
epoch, every child `CI`, and every depth of the one-thread reading. -/
theorem resize_spec (CI : Child) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (n ra : BitVec 64) (A S : Nat) (K : BlockKind) (q q' φ : Frac) (tl : Array Byte)
    (hpos : 0 < s.len.toNat) (hn : 0 < n.toNat) (hq : q'.val ≤ q.val) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ ((inv CI γ e ctx).held s.ptr s.len.toNat k A S K q q' φ ⋆
        (inv CI γ e ctx).relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (Sched.soloRun fuel (heap_ArenaAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra))
      ((inv CI γ e ctx).rresizePost s.ptr k s.len.toNat n.toNat A S K q q' φ tl) :=
  (resize_ct CI γ e ctx s k n ra A S K q q' φ tl hpos hn hq).toSolo fuel

/-- **`remap` meets `FAllocSpec`'s `remap` field.** -/
theorem remap_spec (CI : Child) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (n ra : BitVec 64) (φ : Frac) (bs : Array Byte) (hlen : s.len.toNat = bs.size)
    (hpos : 0 < bs.size) (hn : 0 < n.toNat) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k φ bs)
      (Sched.soloRun fuel (heap_ArenaAllocator_remap ctx s ⟨BitVec.ofNat 6 k⟩ n ra))
      ((inv CI γ e ctx).remapPost s.ptr k φ bs n.toNat) :=
  (remap_ct CI γ e ctx s k n ra φ bs hlen hpos hn).toSolo fuel

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
once, `Full.loop_run`), in the caller's thread (`reset` runs it). -/
theorem count_loop (CI : Child) (free : Bool) :
    ∀ (ns : List NodeV) (it : Option Ptr) (c : BitVec 64),
      FTTotalTriple (⟪c.toNat + capOf ns < 2 ^ 64⟫ ⋆ Chain CI free ns it)
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
    fsym [heap_ArenaAllocator_countListCapacity.again6.eq_def, count_loop CI free]
  | [], some _, _ | _ :: _, none, _ => by
    rw [Full.loop_run]
    conv in StateT.run heap_ArenaAllocator_countListCapacity.loop6 _ =>
      rw [heap_ArenaAllocator_countListCapacity.loop6]
    fsym

/-- **`countListCapacity`** of a list of whole nodes: the sum of their buffer sizes, which with a
header fits in `2 ^ 63` because the list owns its bytes (`chain_capOf_le`), so the checked `+`
never overflows. In the caller's thread. -/
theorem count_spec (CI : Child) (ns : List NodeV) (x : Option Ptr) :
    FTTotalTriple (Chain CI true ns x) (heap_ArenaAllocator_countListCapacity x)
      (fun c => ⟪c.toNat = capOf ns ∧ capOf ns + 24 ≤ 2 ^ 63⟫ ⋆ Chain CI true ns x) :=
  FTTotalTriple.eupd (chain_capOf_le CI ns x).eupd <| FTTotalTriple.lift fun _ => by
    unfold heap_ArenaAllocator_countListCapacity
    fsym [count_loop CI true]

/-- **`countListCapacity`** of the free list `FreeList CI x`: the sum fits with a header in
`2 ^ 63` (`count_spec`). -/
theorem count_free (CI : Child) (x : Option Ptr) :
    FTTotalTriple (FreeList CI x) (heap_ArenaAllocator_countListCapacity x)
      (fun c => ⟪c.toNat + 24 ≤ 2 ^ 63⟫ ⋆ FreeList CI x) := by
  fsym [count_spec CI]

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
    fsym [CAllocSpec.free' h, Child.cown_refund]

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

`retain_capacity` and `retain_with_limit` sum each list's buffer sizes (`count_free`), then
`loop66` handles the two lists in turn: `loop78` gives every node of a list back to the child but
the last one, which the arena keeps (`Last`, `AllocArena/Reset.lean`), resized to the list's share
of the limit (`std.mem.alignBackward(24 + limit, 2)` bytes): given back if that is just the header,
kept as it is if it has that size, else shrunk or grown in place by the child
(`CAllocSpec.resize_shrink`, `CAllocSpec.resize_grow`), else replaced by a new node of that size
(`CAllocSpec.alloc_upTo`, the old one given back; the new node's header words are stored over the
granted bytes: `region_storePacked_wpts`, `region_store_wpts`, `region_storeAll`), else kept as
it is (the result `ok` false). Each kept node is a whole node with `end_index` `0` and no next node
(`Kept`); the walk folds it from the node's parts, whatever path made it. The child takes every
request up to `2 ^ 63` bytes (`FAllocInv.FitsUpTo`, the hypothesis `hfit`): a kept node holds at
most a list's buffer sizes and a header (`count_free`). The kept nodes are the arena at the next
epoch (`own_kept`). -/

section Retain

variable (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)
  (ctx : Ptr) (Ac Sc : Nat) (Kc : BlockKind)

/-- `loop78`'s invariant: the head word `p`, and the list from `it`; `it` is empty only if the
list was. -/
def Inv78 (p : Ptr) (x0 : Option Ptr) (s : heap_ArenaAllocator_resetLocals) : FAssn :=
  FAssn.ex fun ns : List NodeV => ⟪s.it = none → x0 = none⟫ ⋆
    (aptsE p x0 ⋆ Chain CI true (ns.map NodeV.full) s.it ⋆ FreeCl CI ns ⋆ Cm CI ctx Ac Sc Kc)

/-- `loop78`'s exits: the list's last node, or an empty list. -/
def Exit78 (p : Ptr) (x0 : Option Ptr) :
    heap_ArenaAllocator_resetExit × heap_ArenaAllocator_resetLocals → FAssn
  | (.br77 N, _) => aptsE p x0 ⋆ Last CI N ⋆ Cm CI ctx Ac Sc Kc
  | (.br68, _) => ⟪x0 = none⟫ ⋆ (aptsE p x0 ⋆ Cm CI ctx Ac Sc Kc)
  | _ => ⟪False⟫

attribute [local fsym_atom] Chain FreeCl in
include h in
/-- One run of `loop78`'s body: the list's last node is kept (`br77`); any other node goes back to
the child (`free` through the vtable; the refund joins the reservoir). The list's cases are split
before `fsym`: its first node, and the rest as a chain (`fsym_atom`), which the invariant names
again at the next node (ledger #chain-case-unfold). -/
theorem loop78_step (p : Ptr) (x0 : Option Ptr) (s : heap_ArenaAllocator_resetLocals) :
    CTriple (Tgt := Tgt) (Inv78 CI ctx Ac Sc Kc p x0 s) ((heap_ArenaAllocator_reset.loop78 ctx).run s)
      (fun r => if heap_ArenaAllocator_reset.again78 r.1 then Inv78 CI ctx Ac Sc Kc p x0 r.2
        else Exit78 CI ctx Ac Sc Kc p x0 r) := by
  have hd := child_decode CI
  refine CTriple.ex fun ns => ?_
  rcases s with ⟨ok, l, it⟩
  unfold heap_ArenaAllocator_reset.loop78
  rcases ns with _ | ⟨nd, _ | ⟨nd2, ns⟩⟩ <;> cases it
  · simp only [List.map_nil, Chain, FreeCl]
    fsym
  · simp only [List.map_nil, Chain]
    fsym
  · simp only [List.map_cons, List.map_nil, Chain]
    fsym
  · rw [List.map_cons, List.map_nil, chain_one, FreeCl.eq_2, FreeCl.eq_1]
    fsym [CAllocSpec.free' h, Child.cown_refund]
  · simp only [List.map_cons, Chain]
    fsym
  · rw [chain_full_cons2, FreeCl.eq_2]
    fsym [CAllocSpec.free' h, Child.cown_refund]

include h in
/-- **`loop78`** gives every node of a list back to the child but the last (`CTriple.loop`,
`Inv78`), from the list's head word `p` holding `x` and the list of whole nodes from `x`. A rule
from the loop's start state, where the invariant's implication holds (ledger #59). -/
theorem loop78_ct (p : Ptr) (x : Option Ptr) (ok : Bool) (l : BitVec 64) :
    CTriple (Tgt := Tgt) (aptsE p x ⋆ FreeList CI x ⋆ Cm CI ctx Ac Sc Kc)
      ((Zig.loop (heap_ArenaAllocator_reset.loop78 ctx) heap_ArenaAllocator_reset.again78).run ⟨ok, l, x⟩)
      (fun r => FAssn.ex fun e => FAssn.ex fun s' => ⟪r = (e, s')⟫ ⋆ Exit78 CI ctx Ac Sc Kc p x (e, s')) := by
  refine CTriple.pre ((CTriple.loop (Inv78 CI ctx Ac Sc Kc p x) (Exit78 CI ctx Ac Sc Kc p x)
    (loop78_step CI h ctx Ac Sc Kc p x) ⟨ok, l, x⟩).post fun r r' h =>
      ⟨r.1, r.2, sep_lift.mpr ⟨rfl, h⟩⟩) fun r hr => ?_
  obtain ⟨r₁, r₂, hd', he, h1, h2⟩ := hr
  obtain ⟨ns, h2⟩ := sep_ex.mp h2
  refine ⟨ns, sep_lift.mpr ⟨id, ?_⟩⟩
  show (aptsE p x ⋆ Chain CI true (ns.map NodeV.full) x ⋆ FreeCl CI ns ⋆ Cm CI ctx Ac Sc Kc) r
  have h3 : (aptsE p x ⋆ ((Chain CI true (ns.map NodeV.full) x ⋆ FreeCl CI ns) ⋆
    Cm CI ctx Ac Sc Kc)) r := ⟨r₁, r₂, hd', he, h1, h2⟩
  exact of_eq (by ac_rfl) h3

attribute [local fsym_facts] MemFacts.region_end

/-- `loop66`'s invariant: the lists before index `local55` are handled (`Lst`). -/
def Inv66 (pu pf : Ptr) (xu xf : Option Ptr) (s : heap_ArenaAllocator_resetLocals) : FAssn :=
  ⟪s.local55.toNat ≤ 2⟫ ⋆ (Lst CI (decide (0 < s.local55.toNat)) pu xu ⋆
    Lst CI (decide (1 < s.local55.toNat)) pf xf ⋆ Cm CI ctx Ac Sc Kc)

/-- `loop66`'s exit: both lists handled. -/
def Exit66 (pu pf : Ptr) (r : heap_ArenaAllocator_resetExit × heap_ArenaAllocator_resetLocals) : FAssn :=
  FAssn.ex fun s' => ⟪r = (.br65, s')⟫ ⋆ (KeptAt CI pu ⋆ KeptAt CI pf ⋆ Cm CI ctx Ac Sc Kc)

include h in
set_option maxHeartbeats 12000000 in
/-- One run of `loop66`'s body for the first list (`limits[0]`, `v0`). The limit is split before
the walk: a node of just a header (`v0 < 2`, the node goes back) or a kept node (ledger
#undecided-eq-branch-cost). -/
theorem loop66_c0 (hfit : CI.FitsUpTo (2 ^ 63) 3) (pu pf : Ptr) (xu xf : Option Ptr)
    (v0 v1 : BitVec 64) (hv0 : v0.toNat + 24 ≤ 2 ^ 63) (ok : Bool) (it : Option Ptr) :
    CTriple (Tgt := Tgt) (Inv66 CI ctx Ac Sc Kc pu pf xu xf ⟨ok, 0, it⟩)
      ((heap_ArenaAllocator_reset.loop66 ctx #v[pu, pf] #v[v0, v1]).run ⟨ok, 0, it⟩)
      (fun r => if heap_ArenaAllocator_reset.again66 r.1 then Inv66 CI ctx Ac Sc Kc pu pf xu xf r.2
        else Exit66 CI ctx Ac Sc Kc pu pf r) := by
  have hd := child_decode CI
  unfold heap_ArenaAllocator_reset.loop66
  by_cases hsm : v0.toNat < 2 <;>
    fsym [loop78_ct CI h ctx Ac Sc Kc, CAllocSpec.free' h, CAllocSpec.alloc_upTo h hfit,
      CAllocSpec.resize_shrink h hfit, CAllocSpec.resize_grow h hfit, Child.cown_refund,
      FTotalTriple.region_storePacked_wpts, FTotalTriple.region_store_wpts,
      FTotalTriple.region_storeAll]

include h in
set_option maxHeartbeats 12000000 in
/-- One run of `loop66`'s body for the second list (`limits[1]`, `v1`), as `loop66_c0`. -/
theorem loop66_c1 (hfit : CI.FitsUpTo (2 ^ 63) 3) (pu pf : Ptr) (xu xf : Option Ptr)
    (v0 v1 : BitVec 64) (hv1 : v1.toNat + 24 ≤ 2 ^ 63) (ok : Bool) (it : Option Ptr) :
    CTriple (Tgt := Tgt) (Inv66 CI ctx Ac Sc Kc pu pf xu xf ⟨ok, 1, it⟩)
      ((heap_ArenaAllocator_reset.loop66 ctx #v[pu, pf] #v[v0, v1]).run ⟨ok, 1, it⟩)
      (fun r => if heap_ArenaAllocator_reset.again66 r.1 then Inv66 CI ctx Ac Sc Kc pu pf xu xf r.2
        else Exit66 CI ctx Ac Sc Kc pu pf r) := by
  have hd := child_decode CI
  unfold heap_ArenaAllocator_reset.loop66
  by_cases hsm : v1.toNat < 2 <;>
    fsym [loop78_ct CI h ctx Ac Sc Kc, CAllocSpec.free' h, CAllocSpec.alloc_upTo h hfit,
      CAllocSpec.resize_shrink h hfit, CAllocSpec.resize_grow h hfit, Child.cown_refund,
      FTotalTriple.region_storePacked_wpts, FTotalTriple.region_store_wpts,
      FTotalTriple.region_storeAll]

include h in
/-- One run of `loop66`'s body, for every list index: the first list (`loop66_c0`), the second
(`loop66_c1`), or past both (`br65`). -/
theorem loop66_step (hfit : CI.FitsUpTo (2 ^ 63) 3) (pu pf : Ptr) (xu xf : Option Ptr)
    (v0 v1 : BitVec 64) (hv0 : v0.toNat + 24 ≤ 2 ^ 63) (hv1 : v1.toNat + 24 ≤ 2 ^ 63)
    (s : heap_ArenaAllocator_resetLocals) :
    CTriple (Tgt := Tgt) (Inv66 CI ctx Ac Sc Kc pu pf xu xf s)
      ((heap_ArenaAllocator_reset.loop66 ctx #v[pu, pf] #v[v0, v1]).run s)
      (fun r => if heap_ArenaAllocator_reset.again66 r.1 then Inv66 CI ctx Ac Sc Kc pu pf xu xf r.2
        else Exit66 CI ctx Ac Sc Kc pu pf r) := by
  rcases s with ⟨ok, l, it⟩
  obtain rfl | rfl | hl : l = 0 ∨ l = 1 ∨ 2 ≤ l.toNat := by bv_omega
  · exact loop66_c0 CI h ctx Ac Sc Kc hfit pu pf xu xf v0 v1 hv0 ok it
  · exact loop66_c1 CI h ctx Ac Sc Kc hfit pu pf xu xf v0 v1 hv1 ok it
  · unfold heap_ArenaAllocator_reset.loop66
    fsym

include h in
/-- **`loop66`** handles both lists in turn (`CTriple.loop`, `Inv66`): each list's nodes go back to
the child but the one it keeps (`KeptAt`). -/
theorem loop66_ct (hfit : CI.FitsUpTo (2 ^ 63) 3) (pu pf : Ptr) (xu xf : Option Ptr)
    (v0 v1 : BitVec 64) (hv0 : v0.toNat + 24 ≤ 2 ^ 63) (hv1 : v1.toNat + 24 ≤ 2 ^ 63) (ok : Bool)
    (it : Option Ptr) :
    CTriple (Tgt := Tgt) (Inv66 CI ctx Ac Sc Kc pu pf xu xf ⟨ok, 0, it⟩)
      ((Zig.loop (heap_ArenaAllocator_reset.loop66 ctx #v[pu, pf] #v[v0, v1])
        heap_ArenaAllocator_reset.again66).run ⟨ok, 0, it⟩)
      (Exit66 CI ctx Ac Sc Kc pu pf) :=
  CTriple.loop (Inv66 CI ctx Ac Sc Kc pu pf xu xf) _
    (loop66_step CI h ctx Ac Sc Kc hfit pu pf xu xf v0 v1 hv0 hv1) _

end Retain

section Reset

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
  fsym [deinit_ct CI h, own_empty]

/-- **`reset(.free_all)` meets the reset contract**: from the arena's state at epoch `e` and the
whole epoch token (no grant outstanding), the arena's state at epoch `e + 1` and that epoch's
whole token; every node is back with the child. -/
theorem reset_free_all_spec (CI : Child)
    (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv) (γ e : Nat) (ctx : Ptr) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ epTok γ e Frac.one) (heap_ArenaAllocator_reset ctx .free_all)
      (fun r => ⟪r = true⟫ ⋆ ((inv CI γ (e + 1) ctx).own ⋆ epTok γ (e + 1) Frac.one)) :=
  CTriple.eupd (reset_release CI γ e ctx) (reset_free_all_ct CI h γ e ctx)

/-- **(M01) `reset(.free_all)` ends exactly the arena's allocations.** Every resource `F` of the
caller (another allocator's grants and state, stack and global buffers, other threads' shares)
is kept unchanged, and no grant of the arena survives: the precondition has the whole epoch
token, which no client holds next to a grant (`granted_epTok_false`), and a token names its epoch
(`inv`'s `tok`), so one of epoch `e` is no token of the arena at epoch `e + 1`, whose `free`,
`resize` and `remap` take only tokens of their own epoch (`granted_in_node`). -/
theorem reset_free_all_frame (CI : Child)
    (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv) (γ e : Nat) (ctx : Ptr)
    (F : FAssn) :
    CTriple (Tgt := Tgt) (((inv CI γ e ctx).own ⋆ epTok γ e Frac.one) ⋆ F)
      (heap_ArenaAllocator_reset ctx .free_all)
      (fun r => (⟪r = true⟫ ⋆ ((inv CI γ (e + 1) ctx).own ⋆ epTok γ (e + 1) Frac.one)) ⋆ F) :=
  (reset_free_all_spec CI h γ e ctx).frame

end Reset

/-! ### `reset`'s retaining modes

The lists stay `FreeList` atoms at this level (`fsym_atom`): `count_free` and `loop66_ct` name each
list by its head word (ledger #final-match-greedy). -/

section ResetRetain

variable (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)
  (hfit : CI.FitsUpTo (2 ^ 63) 3)

attribute [local fsym_atom] FreeList in
include h hfit in
/-- `reset(.retain_capacity)` from the released arena (`reset_release`): each list keeps one node
(`loop66_ct`), which become the arena at epoch `e + 1` (`own_kept`). -/
theorem reset_retain_capacity_ct (γ e : Nat) (ctx : Ptr) :
    CTriple (Tgt := Tgt) (Released CI γ e ctx) (heap_ArenaAllocator_reset ctx .retain_capacity)
      (fun _ => own CI γ (e + 1) ctx ⋆ epTok γ (e + 1) Frac.one) := by
  have hd := child_decode CI
  unfold heap_ArenaAllocator_reset
  fsym [count_free CI, loop66_ct CI h ctx, own_kept]

attribute [local fsym_atom] FreeList in
include h hfit in
/-- `reset(.retain_with_limit l)` from the released arena: as `retain_capacity` with the limit
`l` (a limit of `0` is `free_all`'s path: `deinit`, `own_empty`). -/
theorem reset_retain_with_limit_ct (γ e : Nat) (ctx : Ptr) (l : BitVec 64) :
    CTriple (Tgt := Tgt) (Released CI γ e ctx) (heap_ArenaAllocator_reset ctx (.retain_with_limit l))
      (fun _ => own CI γ (e + 1) ctx ⋆ epTok γ (e + 1) Frac.one) := by
  have hd := child_decode CI
  unfold heap_ArenaAllocator_reset
  fsym [count_free CI, loop66_ct CI h ctx, own_kept, deinit_ct CI h, own_empty]

include h hfit in
/-- **`reset(.retain_capacity)` meets the reset contract** (`reset_free_all_spec`): from the
arena's state at epoch `e` and the whole epoch token, the arena's state at epoch `e + 1` and that
epoch's whole token; every node is back with the child but the one each list keeps, which the
arena owns whole at epoch `e + 1`. The result (`false` when the child had no room for a kept
node) is a capacity hint, not part of the contract. For every child that takes requests up to
`2 ^ 63` bytes (`hfit`). -/
theorem reset_retain_capacity_spec (γ e : Nat) (ctx : Ptr) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ epTok γ e Frac.one)
      (heap_ArenaAllocator_reset ctx .retain_capacity)
      (fun _ => (inv CI γ (e + 1) ctx).own ⋆ epTok γ (e + 1) Frac.one) :=
  CTriple.eupd (reset_release CI γ e ctx) (reset_retain_capacity_ct CI h hfit γ e ctx)

include h hfit in
/-- **`reset(.retain_with_limit l)` meets the reset contract**, for every limit `l`
(`reset_retain_capacity_spec`). -/
theorem reset_retain_with_limit_spec (γ e : Nat) (ctx : Ptr) (l : BitVec 64) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ epTok γ e Frac.one)
      (heap_ArenaAllocator_reset ctx (.retain_with_limit l))
      (fun _ => (inv CI γ (e + 1) ctx).own ⋆ epTok γ (e + 1) Frac.one) :=
  CTriple.eupd (reset_release CI γ e ctx) (reset_retain_with_limit_ct CI h hfit γ e ctx l)

end ResetRetain

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
#print axioms AllocArena.Core.granted_in_node
#print axioms AllocArena.ArenaSpec.reset_free_all_frame
#print axioms AllocArena.ArenaSpec.loop78_ct
#print axioms AllocArena.ArenaSpec.reset_retain_capacity_spec
#print axioms AllocArena.ArenaSpec.reset_retain_with_limit_spec
