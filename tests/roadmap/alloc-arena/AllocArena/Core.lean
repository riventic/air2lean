import ZigLean.Sep.AllocSpec.Region
import ZigLean.Sep.AllocSpec.Ops
import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Conc
import ZigLean.Sep.Full.Dispatch
import ZigLean.Sep.Full.AtomicRules
import ZigLean.Sep.Full.Ghost
import ZigLean.Sep.Full.Pinned
import ZigLean.Sep.Full.Reclaim
import ZigLean.Range

/-!
# The translated `ArenaAllocator`: the shared layer of its specification

Everything the proofs of the arena's entries need that does not depend on the generated module:
the invariant (`own`, `inv`), the variables of a precondition (`OV`, `FV`), ownership and run
lemmas, the resource updates that end each branch (ghost ledger, extent shares and receipts,
`free_last_upd` … `resize_false_of`; stated over the invariant, not the code), and the **proof
tactics** of the entries (`arena_free`, `arena_resize`, `arena_remap`,
`arena_loadBuf`, `arena_toInt`; `arena_free_checked`, `arena_resize_checked` for the patched
arena's bounds check). Each generated module (`AllocArena/ArenaLinux.lean`,
`ArenaFixedLinux.lean`, …) has its own spawn-target type `Tgt` and its own copies of the std
types, so no generated term of one is a term of another. The specification files
(`ArenaSpec.lean`, `ArenaSpecMacos.lean`: the stock arena on x86_64-linux and aarch64-macos,
`ArenaSpecFixed.lean`: the patched one) state the theorems for
their module and prove them with these tactics, which are elaborated against that module's code
(their identifiers resolve there: `hygiene false`). Nothing here mentions a generated definition.
The invariant and the proof are documented in `ArenaSpec.lean` and `docs/alloc-arena.md`.
-/

namespace AllocArena.Core

open Zig Zig.Region Zig.Full Zig.Full.FAssn

/-! ## Owned cells (`Owns` and its lemmas: `ZigLean/Sep/Full/Reclaim.lean`) -/

/-- Two regions held separately in one block do not overlap. -/
theorem region_apart {p q : Ptr} {b : BlockId} {A S A₂ S₂ : Nat} {K K₂ : BlockKind} {a a₂ : Nat}
    {bs bs₂ : Array Byte} {r : Res} (hp : p.block = some b) (hq : q.block = some b)
    (hn : 0 < bs.size) (hn₂ : 0 < bs₂.size)
    (h : (up (regionIn p A S K a bs) ⋆ up (regionIn q A₂ S₂ K₂ a₂ bs₂)) r) :
    p.off.toNat + bs.size ≤ q.off.toNat ∨ q.off.toNat + bs₂.size ≤ p.off.toNat := by
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := h
  refine Classical.byContradiction fun hc => ?_
  obtain ⟨x, hx1, hx2⟩ : ∃ x, (p.off.toNat ≤ x ∧ x < p.off.toNat + bs.size) ∧
      (q.off.toNat ≤ x ∧ x < q.off.toNat + bs₂.size) :=
    ⟨Nat.max p.off.toNat q.off.toNat, by simp only [Nat.max_def]; split <;> omega,
      by simp only [Nat.max_def]; split <;> omega⟩
  obtain ⟨f1, e1, -⟩ := Owns.region (a := a) (A := A) (S := S) (K := K) hp
    (i := x - p.off.toNat) (by omega) r₁ h1
  obtain ⟨f2, e2, -⟩ := Owns.region (a := a₂) (A := A₂) (S := S₂) (K := K₂) hq
    (i := x - q.off.toNat) (by omega) r₂ h2
  rw [show p.off.toNat + (x - p.off.toNat) = x by omega] at e1
  rw [show q.off.toNat + (x - q.off.toNat) = x by omega] at e2
  rcases hd (b, x) with e | e <;> simp_all

/-! ## The child allocator

The arena struct holds its child allocator (`std.mem.Allocator`: the context pointer and the
vtable pointer). `alloc` and `reset` call the child through it, so the invariant fixes which
allocator that is: the child's invariant, its context `cctx`, and its vtable `vtp` with the entries
`fns` (persistent knowledge of a `const` global, `vtR`). A specification that calls the child
takes the child's `CAllocSpec` for the implementation those entries select
(`CVTable.dispatch`, `docs/alloc-arena.md`). -/

/-- The arena's child allocator: its invariant, the context and vtable pointers that the arena
struct holds, and the vtable's entries. -/
structure Child extends FAllocInv where
  cctx : Ptr
  vtp : Ptr
  fns : VTableFns

/-- The child allocator's bytes in the arena struct (the generated `std.mem.Allocator` encoding:
`ptr` at 0, `vtable` at 8). -/
def Child.bytes (CI : Child) : Array Byte :=
  Enc.fields 16 [(0, Enc.encode CI.cctx), (8, Enc.encode CI.vtp)]

@[simp] theorem Child.bytes_size (CI : Child) : CI.bytes.size = 16 := by
  have h1 : (Enc.encode CI.cctx).size = 8 := LawfulEnc.size_encode _
  have h2 : (Enc.encode CI.vtp).size = 8 := LawfulEnc.size_encode _
  simp only [Child.bytes, Enc.fields, List.foldl, writeBytes, Array.size_append, Array.size_extract,
    Array.size_replicate, h1, h2]
  omega

/-! ## The invariant -/

/-- The pure facts of a node at `N` of `sz` bytes in a block at address `A`. -/
structure NodeFacts (N : Ptr) (A sz : Nat) : Prop where
  off0 : 0 ≤ N.off
  al : (A + N.off.toNat) % 8 = 0
  hdr : 24 ≤ sz
  even : sz % 2 = 0
  small : N.off.toNat + sz < 2 ^ 63

/-- A node of the arena: its pointer, the address, size and kind labels of its cells, its size,
the fraction `qn` that the child lent with it, and the part `qh` of the node's extent share that
the arena keeps. -/
structure NodeV where
  N : Ptr
  A : Nat
  S : Nat
  K : BlockKind
  sz : Nat
  qn : Frac
  qh : Frac

/-- The header of a node, the child's token for it (the child lent the fraction `qn` with it)
and the part `qh` of the node's extent share that the arena keeps (the rest is lent to the
node's grants, or back in the pool): the `size` word (atomic; even, so its `resizing` bit is
clear), the `end_index` word (atomic) and the `next` pointer. The share is tagged like the
child's grants (`CI.tag`). -/
def Header (CI : Child) (N : Ptr) (A S : Nat) (K : BlockKind) (sz : Nat) (ei : BitVec 64)
    (nxt : Option Ptr) (qn qh : Frac) : FAssn :=
  apts N (BitVec.ofNat 64 sz) ⋆ apts (N.add 8) ei ⋆
    up (regionIn (N.add 16) A S K 8 (Enc.encode nxt)) ⋆
    (CI.tok N sz 3 A S K qn ⋆ pshare N qh (N.off.toNat + sz) CI.tag)

/-- The nodes `ns` as a `next`-linked chain from `N'`: headers, tokens and shares, and for the
free list (`free = true`) the whole buffer. -/
def Chain (CI : Child) (free : Bool) : List NodeV → Option Ptr → FAssn
  | [], none => FAssn.emp
  | nd :: ns, some N' =>
    FAssn.ex fun ei : BitVec 64 => FAssn.ex fun nxt : Option Ptr => FAssn.ex fun buf : Array Byte =>
      ⟪nd.N = N' ∧ NodeFacts nd.N nd.A nd.sz ∧ buf.size = (if free then nd.sz - 24 else 0)⟫ ⋆
        (Header CI nd.N nd.A nd.S nd.K nd.sz ei nxt nd.qn nd.qh ⋆
          up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf) ⋆ Chain CI free ns nxt)
  | _, _ => ⟪False⟫

/-- The used nodes after the first. -/
def UsedRest (CI : Child) (ns : List NodeV) (nxt : Option Ptr) : FAssn := Chain CI false ns nxt

/-! ### Byte-range claims of the nodes (decision O1, `docs/alloc-arena.md`)

The child gives each node with the claim on its whole region, tagged like its grants (`CI.tag`).
A used node keeps the claim on its header and lends the claim on its buffer as the arena's claim
of epoch `e` (`EUpd.plendC`), keeping the receipt (`NodeCl`); a reset revokes the receipts
(`EUpd.prevokeC`) and gives the child back the claim on the whole node. The first node holds the
lent claim on its unused tail (`TailCl`); each grant gets the claim on its bytes out of it, and a
`free` or shrink of the last grant joins it back. A free-list node holds its whole claim. -/

/-- The claims a used node keeps: its header's (tagged `CI.tag`) and the receipt for its buffer's,
lent as the arena's claim of epoch `e`. -/
def NodeCl (CI : Child) (γ e : Nat) (N : Ptr) (sz : Nat) : FAssn :=
  pclaim N N.off.toNat (N.off.toNat + 24) CI.tag ⋆ pcrcpt N (N.off.toNat + 24) (N.off.toNat + sz) γ e

/-- The first node's claim on its unused tail `[24 + ei, sz)`, of the arena's epoch `e`. -/
def TailCl (γ e : Nat) (N : Ptr) (ei sz : Nat) : FAssn :=
  pclaim N (N.off.toNat + 24 + ei) (N.off.toNat + sz) (some (γ, e))

/-- **A claim right before the tail joins it** (`pclaim_split`; read backwards, the tail's claim
splits off a claim at its front). -/
theorem tailCl_join {γ e : Nat} {p N : Ptr} {lo hi ei ei' sz : Nat} (hb : p.block = N.block)
    (h1 : lo = N.off.toNat + 24 + ei') (h2 : hi = N.off.toNat + 24 + ei) (h3 : ei' ≤ ei)
    (h4 : 24 + ei ≤ sz) :
    (pclaim p lo hi (some (γ, e)) ⋆ TailCl γ e N ei sz) = TailCl γ e N ei' sz := by
  subst h1 h2; rw [pclaim_rebase hb]; exact pclaim_split (by omega) (by omega)

/-- The claims of the used nodes after the first. -/
def RestCl (CI : Child) (γ e : Nat) : List NodeV → FAssn
  | [] => FAssn.emp
  | nd :: ns => NodeCl CI γ e nd.N nd.sz ⋆ RestCl CI γ e ns

/-- The claims of free-list nodes: each whole node, tagged `CI.tag`. -/
def FreeCl (CI : Child) : List NodeV → FAssn
  | [] => FAssn.emp
  | nd :: ns => pclaim nd.N nd.N.off.toNat (nd.N.off.toNat + nd.sz) CI.tag ⋆ FreeCl CI ns

/-- The free list: nodes with no grants, so the arena keeps their whole share (`qh = qn`) and
their whole claim. -/
def FreeList (CI : Child) (fl : Option Ptr) : FAssn :=
  FAssn.ex fun ns => ⟪∀ nd ∈ ns, nd.qh = nd.qn⟫ ⋆ (Chain CI true ns fl ⋆ FreeCl CI ns)

theorem encode_nxt_size (nxt : Option Ptr) : (Enc.encode nxt).size = 8 := LawfulEnc.size_encode nxt

/-- The `next` word of every node of a chain is owned, with the node's labels. -/
theorem chain_owns {CI : Child} {free : Bool} {b : BlockId} {nd : NodeV}
    (hb : nd.N.block = some b) :
    ∀ {ns : List NodeV} {nxt : Option Ptr}, nd ∈ ns →
      Owns b ((nd.N.add 16).off.toNat + 0) nd.A nd.K (Chain CI free ns nxt)
  | [], _, h => absurd h List.not_mem_nil
  | _ :: _, none, _ => fun _ hr => hr.1.elim
  | nd' :: ns, some N', h => fun r hr => by
    obtain ⟨ei, nx, buf, hr⟩ := hr
    rcases List.mem_cons.mp h with rfl | hm
    · exact Owns.within (X := up (regionIn (nd.N.add 16) nd.A nd.S nd.K 8 (Enc.encode nx)))
        (Owns.region (a := 8) (by simpa [Ptr.add] using hb) (by rw [encode_nxt_size]; omega))
        (by within) r hr
    · exact Owns.within (X := Chain CI free ns nx) (chain_owns hb hm) (by within) r hr

/-- The receipt the arena keeps for a grant `(p, n, q, A, K)` of epoch `e` (`EUpd.lendT`): the
fraction `q` of the extent of `p`'s block, at some bound (a share given back against it is
weakened to that bound first, `EUpd.returnTw`). -/
def rcptOf (γ e : Nat) : Option GRegion → FAssn
  | none => FAssn.emp
  | some (p, _, q, _, _) => FAssn.ex fun b => FAssn.ex fun k => ⟪p.block = some b⟫ ⋆ brcpt b q k γ e

/-- One receipt per grant of the map (decision 1 of step 4, `docs/alloc-arena.md`). -/
def Rcpts (γ e : Nat) (M : GMap) : FAssn :=
  FAssn.ex fun N => ⟪∀ i, N ≤ i → M i = none⟫ ⋆ sepN N (fun i => rcptOf γ e (M i))

/-- Shares (tagged `t`) that frees gave back, `n` pieces `f j = (block, fraction, bound)`: they
belong to the blocks of the arena's nodes and go back to the child with the nodes. -/
def Pool (t : STag) (n : Nat) (f : Nat → BlockId × Frac × Nat) : FAssn :=
  sepN n (fun j => bshare (f j).1 (f j).2.1 (f j).2.2 t)

/-- The pool pieces with one more piece `x` at index `n`. -/
def poolPush (n : Nat) (f : Nat → BlockId × Frac × Nat) (x : BlockId × Frac × Nat) :
    Nat → BlockId × Frac × Nat := fun j => if j = n then x else f j

theorem rcpts_pick {γ e i : Nat} {M : GMap} {g : GRegion} {r : Res} (hM : M i = some g)
    (h : Rcpts γ e M r) : (rcptOf γ e (some g) ⋆ Rcpts γ e (M.set i none)) r := by
  obtain ⟨N, h⟩ := h
  obtain ⟨hN, h⟩ := sep_lift.mp h
  have hi : i < N := Nat.lt_of_not_le fun hle => by rw [hN i hle] at hM; cases hM
  rw [sepN_pick hi] at h
  simp only [hM] at h
  refine sep_mono_right (fun r h => ⟨N, sep_lift.mpr ⟨fun j hj => ?_, ?_⟩⟩) h
  · by_cases hji : j = i
    · subst hji; simp
    · rw [GMap.set_ne _ _ hji]; exact hN j hj
  · refine of_eq (sepN_congr fun j _ => ?_) h
    by_cases hji : j = i
    · subst hji; simp [rcptOf]
    · simp [hji, GMap.set_ne _ _ hji]

theorem rcpts_put {γ e i : Nat} {M : GMap} {v : Option GRegion} {r : Res} (hM : M i = none)
    (h : (rcptOf γ e v ⋆ Rcpts γ e M) r) : Rcpts γ e (M.set i v) r := by
  obtain ⟨N, h⟩ := sep_exR h
  obtain ⟨hN, h⟩ := sep_lift.mp (of_eq (sep_left_comm_eq _ _ _) h)
  refine ⟨N + i + 1, sep_lift.mpr ⟨fun j hj => ?_, ?_⟩⟩
  · rw [GMap.set_ne _ _ (by omega)]; exact hN j (by omega)
  · rw [sepN_pick (i := i) (by omega)]
    simp only [GMap.set_same]
    have e1 : (sepN (N + i + 1) fun j => if j = i then emp else rcptOf γ e ((M.set i v) j)) =
        sepN (N + i + 1) fun j => rcptOf γ e (M j) := sepN_congr fun j _ => by
      by_cases hji : j = i
      · subst hji; simp [hM, rcptOf]
      · simp [hji, GMap.set_ne _ _ hji]
    have e2 : (sepN (N + i + 1) fun j => rcptOf γ e (M j)) = sepN N fun j => rcptOf γ e (M j) :=
      sepN_extend (by omega) fun j hj _ => by rw [hN j hj]; rfl
    rw [e1, e2]; exact h

theorem pool_add {t : STag} {b : BlockId} {q : Frac} {k : Nat} {n : Nat}
    {f : Nat → BlockId × Frac × Nat} {r : Res}
    (h : (bshare b q k t ⋆ Pool t n f) r) : Pool t (n + 1) (poolPush n f (b, q, k)) r := by
  simp only [Pool, sepN, poolPush, if_pos rfl]
  exact of_eq (congrArg _ (sepN_congr fun j hj => by simp [Nat.ne_of_lt hj])) h

/-- The arena's variables: the struct's labels (`Ac`, `Sc`, `Kc`; its first 16 bytes are the
child allocator's, `Child.bytes`), the lists' heads, the grant map `M` (no grant at an id `≥ mN`), the first node (`nxt`, `A`, `S`, `K`,
`sz`, `ei`, `tail`, the token's fraction `qn` and the kept share `qh`; unused without one), the
used nodes after it (`rest`), the pool (`pn` pieces `pf`) and the junk's heap `jh`. -/
structure OV where
  Ac : Nat
  Sc : Nat
  Kc : BlockKind
  first : Option Ptr
  fl : Option Ptr
  M : GMap
  nxt : Option Ptr
  A : Nat
  S : Nat
  K : BlockKind
  sz : Nat
  ei : Nat
  tail : Array Byte
  qn : Frac
  qh : Frac
  rest : List NodeV
  mN : Nat
  pn : Nat
  pf : Nat → BlockId × Frac × Nat
  jh : Heap

/-- The first node at `N`, as a node. -/
def OV.node (w : OV) (N : Ptr) : NodeV := ⟨N, w.A, w.S, w.K, w.sz, w.qn, w.qh⟩

/-- The used nodes. -/
def OV.nodes (w : OV) : List NodeV :=
  match w.first with
  | none => []
  | some N => w.node N :: w.rest

/-- A grant lies in a block of one of the nodes `ns`, with that node's address label and a kind
label of the same normal form (a node that its child grows in place may get another kind label,
`FAllocInv.rresizePost`), at a nonnegative offset. -/
def GrantOk (ns : List NodeV) : GRegion → Prop
  | (p, _, _, A, K) => 0 ≤ p.off ∧ ∃ nd ∈ ns, p.block = nd.N.block ∧ A = nd.A ∧ K.norm = nd.K.norm

/-- A grant's length does not matter to `GrantOk`. -/
theorem GrantOk.len {ns : List NodeV} {p : Ptr} {n n' : Nat} {q : Frac} {A : Nat} {K : BlockKind}
    (h : GrantOk ns (p, n, q, A, K)) : GrantOk ns (p, n', q, A, K) := h

/-- The facts of the first node: none means no grant. -/
def OV.FirstFacts (w : OV) : Prop :=
  match w.first with
    | none => w.M = GMap.empty ∧ w.rest = [] ∧ w.nxt = none
    | some N => NodeFacts N w.A w.sz ∧ 24 + w.ei ≤ w.sz ∧ w.tail.size = w.sz - 24 - w.ei

/-! ### Fraction accounting per block

The child lent each used node's share `qn` with the node; the arena keeps the part `qh` and lent
the rest to its grants, or got it back into the pool. Per block (several nodes may lie in one
block of the child, e.g. a `FixedBufferAllocator`'s buffer): the nodes' lent parts
`Σ (qn - qh)` are the pool's pieces and the grants' fractions on that block. A reset revokes the
grants' receipts and joins everything back into each node's `qn`. -/

/-- `Σ (qn - qh)` over the nodes of `ns` in block `b`. -/
def ndLent (b : BlockId) : List NodeV → Rat
  | [] => 0
  | nd :: ns => (if nd.N.block = some b then nd.qn.val - nd.qh.val else 0) + ndLent b ns

/-- The pool's fractions on block `b`. -/
def poolOn (b : BlockId) (n : Nat) (f : Nat → BlockId × Frac × Nat) : Rat :=
  esum (fun j => if (f j).1 = b then (f j).2.1.val else 0) n

/-- A grant's fraction on block `b`. -/
def grantOn (b : BlockId) : Option GRegion → Rat
  | some (p, _, q, _, _) => if p.block = some b then q.val else 0
  | none => 0

/-- The grants' fractions on block `b` (ids below `N`). -/
def grantsOn (b : BlockId) (M : GMap) (N : Nat) : Rat := esum (fun i => grantOn b (M i)) N

/-! ### Coverage of the nodes' buffers

`reset` gives every used node back to the child, whose `free` takes the node's whole region. The
arena holds a node's buffer in pieces: the bytes that frees and shrinks leaked and the padding of
`alloc` are junk, the outstanding grants' bytes are the clients', and the first node's unused tail
is the arena's. So the junk is exactly a heap `jh` (`JunkAt`, `ZigLean/Sep/Full/Reclaim.lean`), and
every byte of a used node's buffer is in `jh`, in a grant, or in the first node's tail (`OV.Cov`).
A reset with no outstanding grant turns the junk of each buffer back into a region
(`EUpd.junkRegion`). -/

/-- Byte `x` of block `b` lies in the buffer of the node `nd`. -/
abbrev InNode (nd : NodeV) (b : BlockId) (x : Nat) : Prop :=
  nd.N.block = some b ∧ nd.N.off.toNat + 24 ≤ x ∧ x < nd.N.off.toNat + nd.sz

/-- Byte `x` of block `b` lies in the grant `g`. -/
def GrantHas (b : BlockId) (x : Nat) : Option GRegion → Prop
  | some (p, n, _, _, _) => p.block = some b ∧ p.off.toNat ≤ x ∧ x < p.off.toNat + n
  | none => False

/-- Byte `x` of block `b` lies in the first node's unused tail. -/
def OV.InTail (w : OV) (b : BlockId) (x : Nat) : Prop :=
  ∃ N, w.first = some N ∧ N.block = some b ∧ N.off.toNat + 24 + w.ei ≤ x ∧ x < N.off.toNat + w.sz

/-- Where a byte of a used node's buffer is: junk, a grant's, or the first node's tail. -/
def OV.Avail (w : OV) (b : BlockId) (x : Nat) : Prop :=
  w.jh (b, x) ≠ none ∨ (∃ i, GrantHas b x (w.M i)) ∨ w.InTail b x

/-- A byte of the first node's unused tail is available. -/
theorem OV.avail_tail {w : OV} {N : Ptr} {b : BlockId} {x : Nat} (hf : w.first = some N)
    (hb : N.block = some b) (h1 : N.off.toNat + 24 + w.ei ≤ x) (h2 : x < N.off.toNat + w.sz) :
    w.Avail b x := by
  unfold OV.Avail OV.InTail; exact Or.inr (Or.inr ⟨N, hf, hb, h1, h2⟩)

/-- A byte of the tail of the first node `N`. -/
theorem OV.InTail.of_first {w : OV} {N : Ptr} {b : BlockId} {x : Nat} (hf : w.first = some N)
    (h : w.InTail b x) : N.block = some b ∧ N.off.toNat + 24 + w.ei ≤ x ∧ x < N.off.toNat + w.sz := by
  obtain ⟨N', hf', hb, h1, h2⟩ := h
  rw [hf] at hf'; cases hf'; exact ⟨hb, h1, h2⟩

/-- The re-pointed grant `i` has the bytes of its new region. -/
theorem GrantHas.set {M : GMap} {i : Nat} {p : Ptr} {n : Nat} {q : Frac} {A : Nat} {K : BlockKind}
    {b : BlockId} {x : Nat} (hb : p.block = some b) (h1 : p.off.toNat ≤ x) (h2 : x < p.off.toNat + n) :
    GrantHas b x (M.set i (some (p, n, q, A, K)) i) := by
  rw [GMap.set_same]; exact ⟨hb, h1, h2⟩

/-- **Coverage**: every byte of every used node's buffer is available (`OV.Avail`). -/
def OV.Cov (w : OV) : Prop := ∀ nd ∈ w.nodes, ∀ b x, InNode nd b x → w.Avail b x

/-- The facts of the arena's variables. -/
def OV.Facts (w : OV) : Prop :=
  (∀ i, w.mN ≤ i → w.M i = none) ∧ w.FirstFacts ∧
    (∀ i g, w.M i = some g → GrantOk w.nodes g) ∧
    (∀ b, ndLent b w.nodes = poolOn b w.pn w.pf + grantsOn b w.M w.mN) ∧
    (∀ nd ∈ w.nodes, nd.qh.val ≤ nd.qn.val) ∧ w.Cov

/-- **Coverage after an update**: the old available bytes stay available, and each byte of a used
node's buffer lies in an old node's buffer or is available. -/
theorem OV.Cov.step {w w' : OV} (hc : w.Cov) (hav : ∀ b x, w.Avail b x → w'.Avail b x)
    (hn : ∀ nd ∈ w'.nodes, ∀ b x, InNode nd b x → (∃ nd' ∈ w.nodes, InNode nd' b x) ∨ w'.Avail b x) :
    w'.Cov := fun nd hnd b x hx => by
  rcases hn nd hnd b x hx with ⟨nd', hnd', hx'⟩ | h
  · exact hav b x (hc nd' hnd' b x hx')
  · exact h

/-- **Availability after an update** that may change the grant `i`, grow the junk and move the
tail: the junk's bytes stay, the other grants stay, and the bytes of grant `i` and of the old tail
are available. -/
theorem OV.avail_step {w w' : OV} {i : Nat} (hjh : ∀ l, w.jh l ≠ none → w'.jh l ≠ none)
    (hM : ∀ j, j ≠ i → w'.M j = w.M j) (hgi : ∀ b x, GrantHas b x (w.M i) → w'.Avail b x)
    (ht : ∀ b x, w.InTail b x → w'.Avail b x) : ∀ b x, w.Avail b x → w'.Avail b x := by
  rintro b x (h | ⟨j, h⟩ | h)
  · exact Or.inl (hjh _ h)
  · by_cases hj : j = i
    · subst hj; exact hgi b x h
    · exact Or.inr (Or.inl ⟨j, by rw [hM j hj]; exact h⟩)
  · exact ht b x h

/-- Coverage over the same used nodes. -/
theorem OV.Cov.same {w w' : OV} (hc : w.Cov) (hn : w'.nodes = w.nodes)
    (hav : ∀ b x, w.Avail b x → w'.Avail b x) : w'.Cov :=
  OV.Cov.step hc hav fun nd hnd _ _ hx => Or.inl ⟨nd, hn ▸ hnd, hx⟩

/-- **Availability after grant `i` (`n` bytes at `p`) becomes its first `n'` bytes** (none for a
`free`; `n' > n` for a growth): the bytes past `n'` (released) and the old tail's must be
available. -/
theorem OV.avail_shrink {w w' : OV} {i : Nat} {p : Ptr} {n n' : Nat} {q : Frac} {A : Nat}
    {K : BlockKind} (hMi : w.M i = some (p, n, q, A, K)) (hM : ∀ j, j ≠ i → w'.M j = w.M j)
    (hMi' : ∀ b x, p.block = some b → p.off.toNat ≤ x → x < p.off.toNat + n' → GrantHas b x (w'.M i))
    (hjh : ∀ l, w.jh l ≠ none → w'.jh l ≠ none)
    (hrel : ∀ b x, p.block = some b → p.off.toNat + n' ≤ x → x < p.off.toNat + n → w'.Avail b x)
    (ht : ∀ b x, w.InTail b x → w'.Avail b x) : ∀ b x, w.Avail b x → w'.Avail b x := by
  refine OV.avail_step hjh hM (fun b x hx => ?_) ht
  rw [hMi] at hx
  obtain ⟨hb, h1, h2⟩ := hx
  by_cases hlt : x < p.off.toNat + n'
  · exact Or.inr (Or.inl ⟨i, hMi' b x hb h1 hlt⟩)
  · exact hrel b x hb (by omega) h2

/-- The grant facts after one grant changes. -/
theorem grants_set {ns : List NodeV} {M : GMap} (h : ∀ i g, M i = some g → GrantOk ns g) (i : Nat)
    {x : Option GRegion} (hx : ∀ g, x = some g → GrantOk ns g) :
    ∀ j g, M.set i x j = some g → GrantOk ns g := fun j g hj => by
  by_cases hji : j = i
  · subst hji; rw [GMap.set_same] at hj; exact hx g hj
  · rw [GMap.set_ne _ _ hji] at hj; exact h j g hj

/-- A grant of the map has an id below the map's bound. -/
theorem lt_bound {M : GMap} {N i : Nat} {g : GRegion} (hN : ∀ j, N ≤ j → M j = none)
    (hM : M i = some g) : i < N :=
  Nat.lt_of_not_le fun h => by rw [hN i h] at hM; cases hM

/-- The bound after one grant below it changes. -/
theorem bound_set {M : GMap} {N i : Nat} (hN : ∀ j, N ≤ j → M j = none) (hi : i < N)
    (x : Option GRegion) : ∀ j, N ≤ j → M.set i x j = none := fun j hj => by
  rw [GMap.set_ne _ _ (by omega)]; exact hN j hj

/-- The pool's fractions after a piece is pushed. -/
theorem poolOn_push (b : BlockId) (n : Nat) (f : Nat → BlockId × Frac × Nat) (x : BlockId × Frac × Nat) :
    poolOn b (n + 1) (poolPush n f x) = poolOn b n f + (if x.1 = b then x.2.1.val else 0) := by
  simp only [poolOn, esum]
  rw [esum_congr (g := fun j => if (f j).1 = b then (f j).2.1.val else 0)
    fun j hj => by simp only [poolPush, if_neg (Nat.ne_of_lt hj)]]
  simp [poolPush]

/-- **Accounting of a `free`**: the grant's fraction moves from the grants to the pool. -/
theorem acct_free {ns : List NodeV} {pn N i : Nat} {pf : Nat → BlockId × Frac × Nat} {M : GMap}
    {p : Ptr} {n : Nat} {q : Frac} {A : Nat} {K : BlockKind} {bp : BlockId} {k : Nat}
    (h : ∀ b, ndLent b ns = poolOn b pn pf + grantsOn b M N) (hM : M i = some (p, n, q, A, K))
    (hi : i < N) (hb : p.block = some bp) :
    ∀ b, ndLent b ns = poolOn b (pn + 1) (poolPush pn pf (bp, q, k)) + grantsOn b (M.set i none) N := by
  intro b
  have e := esum_update (f := fun j => grantOn b (M j)) (g := fun j => grantOn b (M.set i none j))
    (fun j hj => by simp only [GMap.set_ne _ _ hj]) hi
  have hf : grantOn b (M i) = if bp = b then q.val else 0 := by simp [hM, grantOn, hb]
  have hg : grantOn b (M.set i none i) = 0 := by simp [GMap.set_same, grantOn]
  simp only [hf, hg] at e
  rw [poolOn_push, h b]
  simp only [grantsOn]
  generalize esum (fun j => grantOn b (M j)) N = x at e ⊢
  generalize esum (fun j => grantOn b (M.set i none j)) N = y at e ⊢
  generalize poolOn b pn pf = z
  by_cases hbb : bp = b
  · simp only [hbb, if_true] at e ⊢; grind
  · simp only [hbb, if_false] at e ⊢; grind

/-- **Accounting of a re-pointed grant** (same pointer and fraction): unchanged. -/
theorem acct_repoint {M : GMap} {i : Nat} {p : Ptr} {n n' : Nat} {q : Frac} {A A' : Nat}
    {K K' : BlockKind} (hM : M i = some (p, n, q, A, K)) (b : BlockId) (N : Nat) :
    grantsOn b (M.set i (some (p, n', q, A', K'))) N = grantsOn b M N :=
  esum_congr fun j _ => by
    by_cases hj : j = i
    · subst hj; simp only [GMap.set_same, hM, grantOn]
    · simp only [GMap.set_ne _ _ hj]

/-- The first node of `used_list`: header, token and share, and the unused tail of its buffer. -/
def FirstPart (CI : Child) (w : OV) : FAssn :=
  match w.first with
  | none => FAssn.emp
  | some N => Header CI N w.A w.S w.K w.sz (BitVec.ofNat 64 w.ei) w.nxt w.qn w.qh ⋆
      up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail)

/-- The first node's claims (`NodeCl`, `TailCl`). -/
def FirstCl (CI : Child) (γ e : Nat) (w : OV) : FAssn :=
  match w.first with
  | none => FAssn.emp
  | some N => NodeCl CI γ e N w.sz ⋆ TailCl γ e N w.ei w.sz

/-- The used nodes' claims. -/
def OV.cls (CI : Child) (γ e : Nat) (w : OV) : FAssn := FirstCl CI γ e w ⋆ RestCl CI γ e w.rest

/-- The arena's resources: the struct, the ledger, the child's state, junk, the receipts, the
pool, the nodes, and the used nodes' claims. -/
def OV.body (CI : Child) (γ e : Nat) (ctx : Ptr) (w : OV) : FAssn :=
  (up (regionIn ctx w.Ac w.Sc w.Kc 8 CI.bytes) ⋆ aptsE (ctx.add 16) w.first ⋆ aptsE (ctx.add 24) w.fl ⋆
    gauthP γ e w.M CI.tag ⋆ CI.own ⋆ vtR CI.vtp CI.fns.toList ⋆ JunkAt w.jh ⋆ Rcpts γ e w.M ⋆ Pool CI.tag w.pn w.pf ⋆ FirstPart CI w ⋆
    UsedRest CI w.rest w.nxt ⋆ FreeList CI w.fl) ⋆ w.cls CI γ e

/-- The arena's state (module doc). -/
def own (CI : Child) (γ e : Nat) (ctx : Ptr) : FAssn :=
  FAssn.ex fun w : OV => ⟪w.Facts⟫ ⋆ w.body CI γ e ctx

/-- The arena's invariant at epoch `e`: the token of a region is a ghost token of epoch `e` that
names it with the lent fraction and its cells' address and kind labels; the grants' shares are
tagged with the epoch, lent off the nodes' shares (tagged like the child's grants: the ledger's
parent is `CI.tag`). The arena's state holds its ledger and the child's state, so it witnesses
its tag (`act`). -/
def inv (CI : Child) (γ e : Nat) (ctx : Ptr) : FAllocInv where
  own := own CI γ e ctx
  tok p n _ A _ K q := FAssn.ex fun i => gfrag γ e i (p, n, q, A, K)
  tag := some (γ, e)
  act r h := by
    obtain ⟨w, h⟩ := h
    obtain ⟨-, h⟩ := sep_lift.mp h
    exact act_gauthP (by within) h (CI.act_within (by within) h)

@[simp] theorem inv_tag (CI : Child) (γ e : Nat) (ctx : Ptr) : (inv CI γ e ctx).tag = some (γ, e) := rfl

/-! ## The precondition of `free` and `resize`

Both entries start from the arena's state, the grant's token and (a part of) its share, and the
client's part `G A S K` (labels of the grant's cells): the whole region for `free`, the bytes a
shrink releases for `resize`. -/

/-- The variables of the precondition on an arena with a first node `N` (block `bN`), a slice in
block `bp` granted under id `i` with the fraction `q` and the labels `A' S' K'`, of whose share
the client gives `q'`, and the struct in block `bc`. -/
structure FV where
  w : OV
  i : Nat
  q : Frac
  q' : Frac
  N : Ptr
  bc : BlockId
  bN : BlockId
  bp : BlockId
  A' : Nat
  S' : Nat
  K' : BlockKind

section Pre

variable (CI : Child) (γ e : Nat) (ctx : Ptr) (s : Slice)

def FV.Facts (v : FV) : Prop :=
  v.w.Facts ∧ v.w.first = some v.N ∧ ctx.block = some v.bc ∧ v.N.block = some v.bN ∧
    s.ptr.block = some v.bp ∧ (v.w.Ac + ctx.off.toNat) % 8 = 0 ∧ 0 < s.len.toNat ∧ 0 ≤ ctx.off ∧
    0 ≤ s.ptr.off ∧ v.w.M v.i = some (s.ptr, s.len.toNat, v.q, v.A', v.K')

/-- The atoms of the precondition. -/
def FV.gA (v : FV) : FAssn := gauthP γ e v.w.M CI.tag
def FV.gT (v : FV) : FAssn := gfrag γ e v.i (s.ptr, s.len.toNat, v.q, v.A', v.K')
def FV.uW (v : FV) : FAssn := aptsE (ctx.add 16) (some v.N)
def FV.eW (v : FV) (ei : Nat) : FAssn := apts (v.N.add 8) (BitVec.ofNat 64 ei)
def FV.nR (v : FV) : FAssn := up (regionIn (v.N.add 16) v.w.A v.w.S v.w.K 8 (Enc.encode v.w.nxt))
def FV.cR (v : FV) : FAssn := up (regionIn ctx v.w.Ac v.w.Sc v.w.Kc 8 CI.bytes)
def FV.tR (v : FV) (ei : Nat) (tail : Array Byte) : FAssn :=
  up (regionIn (v.N.add (24 + ei)) v.w.A v.w.S v.w.K 1 tail)
/-- The first node's token and kept share. -/
def FV.nS (v : FV) : FAssn :=
  CI.tok v.N v.w.sz 3 v.w.A v.w.S v.w.K v.w.qn ⋆ pshare v.N v.w.qh (v.N.off.toNat + v.w.sz) CI.tag
/-- What the entries do not touch. -/
def FV.F (v : FV) : FAssn :=
  apts v.N (BitVec.ofNat 64 v.w.sz) ⋆ v.nS CI ⋆ aptsE (ctx.add 24) v.w.fl ⋆ CI.own ⋆ vtR CI.vtp CI.fns.toList ⋆
    UsedRest CI v.w.rest v.w.nxt ⋆ FreeList CI v.w.fl
/-- The claims of the used nodes: the first node's (`NodeCl`, `TailCl`) and the others'. -/
def FV.cl (v : FV) (ei : Nat) : FAssn :=
  NodeCl CI γ e v.N v.w.sz ⋆ TailCl γ e v.N ei v.w.sz ⋆ RestCl CI γ e v.w.rest
/-- The client's part of the grant's share, the receipts, the pool and the nodes' claims. -/
def FV.xs (v : FV) : FAssn :=
  pshare s.ptr v.q' (s.ptr.off.toNat + s.len.toNat) (some (γ, e)) ⋆ Rcpts γ e v.w.M ⋆ Pool CI.tag v.w.pn v.w.pf ⋆
    v.cl CI γ e v.w.ei

variable (G : Nat → Nat → BlockKind → FAssn)

/-- What the steps do not change before the `cmpxchg`, besides the two words. -/
def FV.R0 (v : FV) : FAssn :=
  v.gA CI γ e ⋆ v.gT γ e s ⋆ v.nR ⋆ v.cR CI ctx ⋆ v.tR v.w.ei v.w.tail ⋆ G v.A' v.S' v.K' ⋆ JunkAt v.w.jh ⋆
    v.F CI ctx ⋆ v.xs CI γ e s

/-- The precondition: the two words the entries read, then the rest. -/
def FV.L (v : FV) : FAssn := v.uW ctx ⋆ (v.eW v.w.ei ⋆ v.R0 CI γ e ctx s G)

/-- `free`'s client part: the region and its claim. -/
def rgn (k : Nat) (bs : Array Byte) : Nat → Nat → BlockKind → FAssn :=
  fun A S K => up (regionIn s.ptr A S K (2 ^ k) bs) ⋆
    pclaim s.ptr s.ptr.off.toNat (s.ptr.off.toNat + bs.size) (some (γ, e))

/-- `resize`'s client part: the bytes a shrink to `n` releases and their claim. -/
def relB (n : Nat) (tl : Array Byte) : Nat → Nat → BlockKind → FAssn :=
  fun A S K => (inv CI γ e ctx).relBytes s.ptr A S K n s.len.toNat tl

end Pre

theorem region_facts {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte} {r : Res}
    (h : up (regionIn p A S K a bs) r) : (∃ b, p.block = some b) ∧ (A + p.off.toNat) % a = 0 ∧
      0 ≤ p.off := by
  obtain ⟨⟨ha, -, b, hb, h0, -⟩, -⟩ := h
  exact ⟨⟨b, hb⟩, ha, h0⟩

section PreProof

variable {CI : Child} {γ e : Nat} {ctx : Ptr} {s : Slice} {G : Nat → Nat → BlockKind → FAssn}

/-- **The precondition in normal form**: the arena's variables, the grant's id (a token of the
current epoch names a grant of the map, `gfrag_mem`, so the arena has a node: O-A), and the
blocks. -/
theorem pre_of {k A S : Nat} {K : BlockKind} {q q' : Frac} {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hpos : 0 < s.len.toNat)
    (hp : ((inv CI γ e ctx).own ⋆ ((inv CI γ e ctx).held s.ptr s.len.toNat k A S K q q' ⋆
      G A S K)) r) :
    (FAssn.ex fun v : FV => ⟪v.Facts ctx s ∧ v.q = q ∧ v.q' = q' ∧ v.A' = A ∧ v.S' = S ∧ v.K' = K⟫ ⋆
      v.L CI γ e ctx s G) r := by
  obtain ⟨w, hp⟩ := sep_ex.mp hp
  obtain ⟨hwf, hp⟩ := sep_lift.mp (sep_assoc hp)
  obtain ⟨i, hp⟩ := sep_ex.mp (of_eq (Q := (FAssn.ex fun i => gfrag γ e i (s.ptr, s.len.toNat, q, A, K)) ⋆
    (pshare s.ptr q' (s.ptr.off.toNat + s.len.toNat) (some (γ, e)) ⋆ (G A S K ⋆ w.body CI γ e ctx)))
    (by simp only [inv, FAllocInv.held]; ac_rfl) hp)
  have hM : w.M i = some (s.ptr, s.len.toNat, q, A, K) := by
    have hp' := of_eq (Q := (gauthP γ e w.M CI.tag ⋆ gfrag γ e i (s.ptr, s.len.toNat, q, A, K)) ⋆
      (pshare s.ptr q' (s.ptr.off.toNat + s.len.toNat) (some (γ, e)) ⋆ G A S K ⋆
      up (regionIn ctx w.Ac w.Sc w.Kc 8 CI.bytes) ⋆ aptsE (ctx.add 16) w.first ⋆ aptsE (ctx.add 24) w.fl ⋆
      CI.own ⋆ vtR CI.vtp CI.fns.toList ⋆ JunkAt w.jh ⋆ Rcpts γ e w.M ⋆ Pool CI.tag w.pn w.pf ⋆ FirstPart CI w ⋆ UsedRest CI w.rest w.nxt ⋆
      FreeList CI w.fl ⋆ w.cls CI γ e)) (by simp only [OV.body]; ac_rfl) hp
    obtain ⟨r₁, r₂, -, rfl, h1, -⟩ := hp'
    exact gfrag_mem h1 (Ghost.Ok.assoc.mp hh.ghost.1)
  have hp0 : 0 ≤ s.ptr.off := (hwf.2.2.1 i _ hM).1
  obtain ⟨bp, hbp⟩ : ∃ bp, s.ptr.block = some bp := by
    obtain ⟨_, _, -, -, -, h1⟩ := id hp
    obtain ⟨_, _, -, -, ⟨bp, hsh⟩, -⟩ := h1
    exact ⟨bp, (sep_lift.mp hsh).1⟩
  cases hfirst : w.first with
  | none =>
    exfalso
    have hn : w.M = GMap.empty := by
      have := hwf.2.1; unfold OV.FirstFacts at this; rw [hfirst] at this; exact this.1
    rw [hn] at hM; cases hM
  | some N =>
    -- the shape with dummy block ids, to read the blocks off the regions
    have hL : ∀ bc bN, (FV.L CI γ e ctx s G ⟨w, i, q, q', N, bc, bN, bp, A, S, K⟩) r := by
      intro bc bN
      refine of_eq ?_ hp
      simp only [OV.body, FirstPart, hfirst, Header, FV.L, FV.R0, FV.gA, FV.gT, FV.uW, FV.eW,
        FV.nR, FV.cR, FV.tR, FV.F, FV.nS, FV.xs, FV.cl, OV.cls, FirstCl]
      ac_rfl
    have h0 := hL 0 0
    unfold FV.L FV.R0 at h0
    obtain ⟨_, _, -, -, -, h1⟩ := h0
    obtain ⟨_, _, -, -, -, h2⟩ := h1
    obtain ⟨_, _, -, -, -, h3⟩ := h2
    obtain ⟨_, _, -, -, -, h4⟩ := h3
    obtain ⟨_, _, -, -, hn, h5⟩ := h4
    obtain ⟨_, _, -, -, hc, -⟩ := h5
    obtain ⟨⟨bc, hbc⟩, hac, hc0⟩ := region_facts hc
    obtain ⟨⟨bN, hbN⟩, -, -⟩ := region_facts hn
    exact ⟨⟨w, i, q, q', N, bc, bN, bp, A, S, K⟩, sep_lift.mpr ⟨⟨⟨hwf, hfirst, hbc,
      by simpa [Ptr.add] using hbN, hbp, hac, hpos, hc0, hp0, hM⟩, rfl, rfl, rfl, rfl, rfl⟩, hL _ _⟩⟩

/-- `free`'s precondition in normal form (`pre_of`; the client gives the whole share). -/
theorem free_pre {k : Nat} {bs : Array Byte} {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size)
    (hp : ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs) r) :
    (FAssn.ex fun v : FV => ⟪v.Facts ctx s ∧ v.q' = v.q⟫ ⋆ v.L CI γ e ctx s (rgn γ e s k bs)) r := by
  obtain ⟨A, hp⟩ := sep_exR hp
  obtain ⟨S, hp⟩ := sep_exR hp
  obtain ⟨K, hp⟩ := sep_exR hp
  obtain ⟨q, hp⟩ := sep_exR hp
  have hp' : ((inv CI γ e ctx).own ⋆ ((inv CI γ e ctx).held s.ptr s.len.toNat k A S K q q ⋆
      rgn γ e s k bs A S K)) r := by
    rw [hlen]; exact of_eq (by simp only [FAllocInv.held, rgn, inv_tag]; ac_rfl) hp
  obtain ⟨v, hv⟩ := pre_of (G := rgn γ e s k bs) hh (by omega) hp'
  obtain ⟨⟨hf, hq, hq', -⟩, hL⟩ := sep_lift.mp hv
  exact ⟨v, sep_lift.mpr ⟨⟨hf, hq'.trans hq.symm⟩, hL⟩⟩

/-- What the memory says about the blocks of the precondition: the struct's from owned bytes,
the node's and the slice's from their extent shares (whose tags the arena's state witnesses as
active, `FAllocInv.act`), and that two live blocks share no byte address. -/
theorem free_mem {v : FV} (hv : v.Facts ctx s) {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hp : v.L CI γ e ctx s G r) (hs : m.FSeq) :
    ∃ blkC blkN blkP, m.blocks[v.bc]? = some blkC ∧ blkC.addr = v.w.Ac ∧
      ctx.off.toNat + 16 ≤ blkC.bytes.size ∧
      m.blocks[v.bN]? = some blkN ∧ blkN.addr = v.w.A ∧ v.N.off.toNat + v.w.sz ≤ blkN.bytes.size ∧
      m.blocks[v.bp]? = some blkP ∧ blkP.live = true ∧
      s.ptr.off.toNat + s.len.toNat ≤ blkP.bytes.size ∧
      (v.bp ≠ v.bN → ∀ x x', x < blkN.bytes.size → x' < blkP.bytes.size → blkN.addr + x ≠ blkP.addr + x') ∧
      (v.bp = v.bN → blkP = blkN) := by
  obtain ⟨-, -, hbc, hbN, hbp, -, hpos, -, -, -⟩ := hv
  have hbN' : (v.N.add 16).block = some v.bN := by simpa [Ptr.add] using hbN
  have hoC : Owns v.bc (ctx.off.toNat + 15) v.w.Ac v.w.Kc (v.L CI γ e ctx s G) :=
    Owns.within (X := v.cR CI ctx) (Owns.region (a := 8) hbc (i := 15) (by simp)) (by within)
  have hoN : Owns v.bN ((v.N.add 16).off.toNat + 0) v.w.A v.w.K (v.L CI γ e ctx s G) :=
    Owns.within (X := v.nR) (Owns.region (a := 8) (bs := Enc.encode v.w.nxt) hbN' (i := 0)
      (by rw [encode_nxt_size]; omega)) (by within)
  obtain ⟨blkC, e1, -, x1, a1, -⟩ := hoC.block hh hp
  obtain ⟨blkN, e2, l2, -, a2, -⟩ := hoN.block hh hp
  have hact : Act r.gh.ls (some (γ, e)) :=
    act_gauthP (M := v.w.M) (p := CI.tag) (show Within (v.gA CI γ e) (v.L CI γ e ctx s G) by within) hp
      (CI.act_within (by within) hp)
  obtain ⟨blkP, e3, l3, s3, -⟩ := Holds.pshareW (p := s.ptr) (t := some (γ, e)) hh (by within) hp hbp hact
  obtain ⟨blkN', e2', -, s2, -⟩ := Holds.pshareW (p := v.N) (t := CI.tag) hh (by within) hp hbN
    (CI.act_within (by within) hp)
  rw [e2] at e2'; cases e2'
  refine ⟨blkC, blkN, blkP, e1, a1, by omega, e2, a2, s2, e3, l3, s3,
    fun hne x x' hx hx' => hs.2.2.1.addr_ne (Ne.symm hne) e2 e3 l2 l3 hx hx', fun heq => ?_⟩
  rw [heq, e2] at e3; cases e3; rfl

/-- **O-F**: the comparison of the first node's `buf + end_index` with the slice's end by address
is decided by the blocks and offsets: in one block by the offsets, across two live blocks never
(`Mem.LiveDisjoint.addr_ne`, at the last byte before each end). -/
theorem last_dec {blkN blkP : Block} {bN bp : BlockId} {P Q : Ptr} {xN xP : Nat}
    (hP : P.off = (xN : Int)) (hQ : Q.off = (xP : Int)) (h0N : 0 < xN) (hN : xN ≤ blkN.bytes.size)
    (h0P : 0 < xP) (hPs : xP ≤ blkP.bytes.size)
    (hap : bp ≠ bN → ∀ x x', x < blkN.bytes.size → x' < blkP.bytes.size → blkN.addr + x ≠ blkP.addr + x')
    (hsame : bp = bN → blkP = blkN) :
    decide (((blkN.addr : Nat) : Int) + P.off = ((blkP.addr : Nat) : Int) + Q.off) =
      decide (bp = bN ∧ xP = xN) := by
  rw [hP, hQ]
  by_cases hb : bp = bN
  · rw [hsame hb]
    exact decide_eq_decide.mpr ⟨fun h => ⟨hb, by omega⟩, fun h => by omega⟩
  · have := hap hb (xN - 1) (xP - 1) (by omega) (by omega)
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => absurd h.1 hb⟩

/-- **The labels of the first node's last grant**: a grant lies in a node of its block with that
node's labels (`GrantOk`); two nodes of one block own cells of the one block, so their labels
agree (`chain_owns`, `Owns.block`). -/
theorem last_labels {v : FV} (hv : v.Facts ctx s) (hb : v.bp = v.bN) {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hp : v.L CI γ e ctx s G r) : v.A' = v.w.A ∧ v.K'.norm = v.w.K.norm := by
  obtain ⟨⟨-, -, hgr, -, -⟩, hfirst, -, hbN, hbp, -, -, -, -, hMi⟩ := hv
  obtain ⟨-, nd, hnd, hblk, hA, hK⟩ := hgr _ _ hMi
  simp only [OV.nodes, hfirst] at hnd
  rcases List.mem_cons.mp hnd with rfl | hm
  · exact ⟨hA, hK⟩
  · have hb' : nd.N.block = some v.bN := by rw [← hblk, hbp, hb]
    have hoN : Owns v.bN ((v.N.add 16).off.toNat + 0) v.w.A v.w.K (v.L CI γ e ctx s G) :=
      Owns.within (X := v.nR) (Owns.region (a := 8) (bs := Enc.encode v.w.nxt)
        (by simpa [Ptr.add] using hbN) (by rw [encode_nxt_size]; omega)) (by within)
    have hoR : Owns v.bN ((nd.N.add 16).off.toNat + 0) nd.A nd.K (v.L CI γ e ctx s G) :=
      Owns.within (X := UsedRest CI v.w.rest v.w.nxt) (chain_owns hb' hm) (by within)
    obtain ⟨b1, e1, -, -, a1, k1⟩ := hoN.block hh hp
    obtain ⟨b2, e2, -, -, a2, k2⟩ := hoR.block hh hp
    rw [e1] at e2; cases e2
    exact ⟨by rw [hA, ← a2, a1], by rw [hK, ← k2, k1]⟩

/-- **Bytes of the client's part that end past the first node's header lie after it**: the
header's `next` word is the arena's (`region_apart`). -/
theorem lo_of {v : FV} (hv : v.Facts ctx s) {p : Ptr} {A₂ S₂ a : Nat} {K₂ : BlockKind}
    {bs : Array Byte} (hw : Within (up (regionIn p A₂ S₂ K₂ a bs)) (G v.A' v.S' v.K'))
    (hpb : p.block = some v.bN) (hn : 0 < bs.size)
    (hend : v.N.off.toNat + 24 ≤ p.off.toNat + bs.size) {r : Res} (hp : v.L CI γ e ctx s G r) :
    v.N.off.toNat + 24 ≤ p.off.toNat := by
  obtain ⟨⟨-, hwf, -⟩, hfirst, -, hbN, -⟩ := hv
  have h0 : 0 ≤ v.N.off := by
    unfold OV.FirstFacts at hwf; rw [hfirst] at hwf; exact hwf.1.off0
  have hr := of_eq (Q := (v.nR ⋆ G v.A' v.S' v.K') ⋆ (v.uW ctx ⋆ v.eW v.w.ei ⋆ v.gA CI γ e ⋆
    v.gT γ e s ⋆ v.cR CI ctx ⋆ v.tR v.w.ei v.w.tail ⋆ JunkAt v.w.jh ⋆ v.F CI ctx ⋆ v.xs CI γ e s))
    (by simp only [FV.L, FV.R0]; ac_rfl) hp
  obtain ⟨_, _, -, -, hr, -⟩ := hr
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := hr
  obtain ⟨R, h2⟩ := hw r₂ h2
  have h3 := sep_assoc' (⟨r₁, r₂, hd, rfl, h1, h2⟩ : (v.nR ⋆ (up (regionIn p A₂ S₂ K₂ a bs) ⋆ R)) _)
  obtain ⟨_, _, -, -, h3, -⟩ := h3
  have := region_apart (by simpa [Ptr.add] using hbN) hpb (by rw [encode_nxt_size]; decide) hn h3
  rw [encode_nxt_size] at this
  simp only [Ptr.add] at this
  omega

end PreProof

/-! ## Run lemmas -/

theorem ptrAddr_run' {m : Mem} {p : Ptr} {b : BlockId} {blk : Block} (hpb : p.block = some b)
    (hb : m.blocks[b]? = some blk) : (ptrAddr p).run m = pure ((blk.addr : Int) + p.off, m) := by
  obtain ⟨pb, po⟩ := p
  simp only at hpb; subst hpb
  exact ptrAddr_run hb po

theorem ptrEqAddr_run {m : Mem} {p q : Ptr} {b b' : BlockId} {blk blk' : Block}
    (hp : p.block = some b) (hb : m.blocks[b]? = some blk) (hq : q.block = some b')
    (hb' : m.blocks[b']? = some blk') :
    (ptrEqAddr p q).run m = pure (decide ((blk.addr : Int) + p.off = (blk'.addr : Int) + q.off), m) := by
  unfold ptrEqAddr
  simp only [StateT.run_bind, ptrAddr_run' hp hb, pure_bind, ptrAddr_run' hq hb', StateT.run_pure]

theorem ptrProject_add_run' {m : Mem} {p : Ptr} {b : BlockId} {blk : Block} {k : Int}
    (hpb : p.block = some b) (hb : m.blocks[b]? = some blk) (h0 : 0 ≤ p.off)
    (hk : 0 ≤ k) (hn : p.off + k ≤ blk.bytes.size) :
    (ptrProject p (·.add k)).run m = pure (p.add k, m) :=
  ptrProject_add_run (inBounds_of hpb hb h0 (by omega)) (inBounds_of (p := p.add k) hpb hb
    (by simp [Ptr.add]; omega) (by simp [Ptr.add]; omega))

theorem ptrProject_elem_run {m : Mem} {p : Ptr} {b : BlockId} {blk : Block} {i : BitVec 64}
    (hpb : p.block = some b) (hb : m.blocks[b]? = some blk) (h0 : 0 ≤ p.off)
    (hn : p.off + i.toNat ≤ blk.bytes.size) :
    (ptrProject p (·.elem 1 i)).run m = pure (p.add i.toNat, m) := by
  have e : (fun x : Ptr => x.elem 1 i) = (·.add (i.toNat : Int)) := by
    funext x; simp [Ptr.elem]
  rw [e]
  exact ptrProject_add_run' hpb hb h0 (by omega) hn

/-- The bits of an even size with the `resizing` bit clear are the size (`Node.Size.toInt`). -/
theorem bits_even (w : BitVec 64) (h : w.toNat % 2 = 0) :
    (Packed.toBits (false : Bool)).setWidth 64 <<< 0 ||| (Packed.toBits (w.extractLsb' 1 63)).setWidth 64 <<< 1 = w := by
  have h0 : w[0] = false := by
    simp [BitVec.getElem_eq_testBit_toNat, Nat.testBit_zero, h]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Packed.toBits, Bool.false_eq_true, ↓reduceIte, BitVec.shiftLeft_zero, BitVec.getLsbD_or,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb']
  rcases i with _ | i
  · simp [h0]
  · simp [show i < 63 by omega, show i < 64 by omega, hi, Nat.add_comm 1 i]

/-- The arena's state from its variables. -/
theorem own_of {CI : Child} {γ e : Nat} {ctx : Ptr} {w : OV} (hw : w.Facts) {X : FAssn}
    {r : Res} (h : (w.body CI γ e ctx ⋆ X) r) : ((inv CI γ e ctx).own ⋆ X) r :=
  sep_mono_left (fun _ h => ⟨w, sep_lift.mpr ⟨hw, h⟩⟩) h

/-- The first `n` bytes of a region keep its alignment; the rest is a region of alignment 1. -/
theorem up_region_split {p : Ptr} {A S : Nat} {K : BlockKind} {a n : Nat} {bs : Array Byte}
    {r : Res} (hn : n ≤ bs.size) (h : up (regionIn p A S K a bs) r) :
    (up (regionIn p A S K a (bs.extract 0 n)) ⋆
      up (regionIn (p.add n) A S K 1 (bs.extract n bs.size))) r := by
  obtain ⟨h1, hk, hg⟩ := h
  exact up_sep ⟨regionIn_split h1 hn (Nat.mod_one _), hk, hg⟩

section Lsz

variable (CI : Child) (γ e : Nat) (ctx : Ptr) (s : Slice) (G : Nat → Nat → BlockKind → FAssn)

/-- The precondition without the node's `size` word. -/
def FV.Lsz (v : FV) : FAssn :=
  v.uW ctx ⋆ v.eW v.w.ei ⋆ v.gA CI γ e ⋆ v.gT γ e s ⋆ v.nR ⋆ v.cR CI ctx ⋆
    v.tR v.w.ei v.w.tail ⋆ G v.A' v.S' v.K' ⋆ JunkAt v.w.jh ⋆ (v.nS CI ⋆ aptsE (ctx.add 24) v.w.fl ⋆ CI.own ⋆ vtR CI.vtp CI.fns.toList ⋆
    UsedRest CI v.w.rest v.w.nxt ⋆ FreeList CI v.w.fl) ⋆ v.xs CI γ e s

theorem FV.L_eq (v : FV) :
    v.L CI γ e ctx s G = (apts v.N (BitVec.ofNat 64 v.w.sz) ⋆ v.Lsz CI γ e ctx s G) := by
  simp only [FV.L, FV.R0, FV.F, FV.Lsz]; ac_rfl

end Lsz

/-- The bytes a shrink releases, when it releases some: their size, and they lie past the first
node's header when they end at its `end_index` (`lo_of`). -/
theorem cut_facts {CI : Child} {γ e : Nat} {ctx : Ptr} {s : Slice} {v : FV} (hv : v.Facts ctx s)
    (hb : v.bp = v.bN) (hoff : s.ptr.off.toNat + s.len.toNat = v.N.off.toNat + 24 + v.w.ei)
    {n : Nat} {tl : Array Byte} (hlt : n < s.len.toNat) {r : Res}
    (hp : v.L CI γ e ctx s (relB CI γ e ctx s n tl) r) :
    tl.size = s.len.toNat - n ∧ v.N.off.toNat + 24 ≤ s.ptr.off.toNat + n := by
  have hw : Within (up (regionIn (s.ptr.add n) v.A' v.S' v.K' 1 tl)) (relB CI γ e ctx s n tl v.A' v.S' v.K') :=
    fun r h => by
      simp only [relB, FAllocInv.relBytes, if_pos hlt] at h; exact ⟨_, of_eq (sep_left_comm_eq _ _ _) h⟩
  have htl : tl.size = s.len.toNat - n := by
    obtain ⟨R, hR⟩ := (show Within (relB CI γ e ctx s n tl v.A' v.S' v.K') (v.L CI γ e ctx s (relB CI γ e ctx s n tl)) by
      unfold FV.L FV.R0; within) r hp
    simp only [relB, FAllocInv.relBytes, if_pos hlt] at hR
    exact (sep_lift.mp (sep_assoc hR)).1
  have hp0 := hv.2.2.2.2.2.2.2.2.1
  have hpb : (s.ptr.add n).block = some v.bN := by simpa [Ptr.add, hb] using hv.2.2.2.2.1
  have := lo_of hv hw hpb (by omega) (by simp only [Ptr.add]; omega) hp
  simp only [Ptr.add] at this
  exact ⟨htl, by omega⟩

/-! ## Ghost and extent updates of `free` and `resize`

A grant `(p, n, q, A, K)` of epoch `e` holds the share `q` tagged `(γ, e)`; the arena holds its
receipt (`Rcpts`). `free` gives the share back against that receipt (`EUpd.returnTw`) and keeps
the untagged-by-`γ` share in its pool; a shrink weakens the share's bound; a growth in the first
node takes back the part of the share the client gives, joins it into the node's and lends it
again at the new end (`EUpd.lendT`); the grant's receipt is split and joined around it
(`brcpt_split`, `EUpd.rjoin`). -/

section Glue

/-- The receipts after a grant is re-pointed with the same pointer and fraction. -/
theorem rcpts_repoint {γ e i : Nat} {M : GMap} {p : Ptr} {n n' : Nat} {q : Frac} {A A' : Nat}
    {K K' : BlockKind} {r : Res} (hM : M i = some (p, n, q, A, K)) (h : Rcpts γ e M r) :
    Rcpts γ e (M.set i (some (p, n', q, A', K'))) r := by
  have := rcpts_put (v := some (p, n', q, A', K')) (GMap.set_same M i none)
    (sep_mono_left (P := rcptOf γ e (some (p, n, q, A, K))) (Q := rcptOf γ e (some (p, n', q, A', K')))
      (fun _ x => x) (rcpts_pick hM h))
  rwa [GMap.set_set] at this

/-- The receipt of a grant, opened: its block and bound. -/
theorem open_rcpt {γ e i : Nat} {M : GMap} {p : Ptr} {n : Nat} {q q' : Frac} {A : Nat} {K : BlockKind}
    {k₀ : Nat} {t : STag} {X : FAssn} {r : Res} (hM : M i = some (p, n, q, A, K))
    (h : (pshare p q' k₀ t ⋆ (Rcpts γ e M ⋆ X)) r) :
    ∃ b k, p.block = some b ∧
      ((bshare b q' k₀ t ⋆ brcpt b q k γ e) ⋆ (Rcpts γ e (M.set i none) ⋆ X)) r := by
  have h1 := sep_mono_right (R := (rcptOf γ e (some (p, n, q, A, K)) ⋆ Rcpts γ e (M.set i none)) ⋆ X)
    (fun _ x => sep_mono_left (Q := rcptOf γ e (some (p, n, q, A, K)) ⋆ Rcpts γ e (M.set i none))
      (fun _ y => rcpts_pick hM y) x) h
  have h2 := of_eq (Q := pshare p q' k₀ t ⋆ (rcptOf γ e (some (p, n, q, A, K)) ⋆
    (Rcpts γ e (M.set i none) ⋆ X))) (by ac_rfl) h1
  obtain ⟨b, h3⟩ := sep_ex.mp h2
  obtain ⟨hb, h3⟩ := sep_lift.mp (sep_assoc h3)
  obtain ⟨b', h4⟩ := sep_ex.mp (of_eq (sep_left_comm_eq _ _ _) h3)
  obtain ⟨k, h4⟩ := sep_ex.mp h4
  obtain ⟨hb', h4⟩ := sep_lift.mp (sep_assoc h4)
  rw [hb] at hb'; cases hb'
  exact ⟨b, k, hb, of_eq (by ac_rfl) h4⟩

/-- The grant's token names a grant of the map. -/
theorem grant_fact {γ e i : Nat} {M : GMap} {t : STag} {g : GRegion} {X : FAssn} :
    ∀ m r rF, Holds m r rF → (gauthP γ e M t ⋆ (gfrag γ e i g ⋆ X)) r → m.FSeq → M i = some g :=
  fun _ _ rF hh hp _ => by
    obtain ⟨r₁, r₂, -, rfl, h1, -⟩ := sep_assoc' hp
    exact gfrag_mem h1 (Ghost.Ok.assoc.mp hh.ghost.1)

/-- **`free`'s ghost part**: the share goes back against its receipt (at the receipt's bound `k`,
on the grant's block `b`), the grant is retired. -/
theorem free_ghost {γ e i : Nat} {M : GMap} {t : STag} {p : Ptr} {n : Nat} {q : Frac} {A : Nat}
    {K : BlockKind} :
    EUpd (gauthP γ e M t ⋆ (gfrag γ e i (p, n, q, A, K) ⋆ (pshare p q (p.off.toNat + n) (some (γ, e)) ⋆
      Rcpts γ e M)))
      (FAssn.ex fun b => FAssn.ex fun k => ⟪p.block = some b⟫ ⋆
        (gauthP γ e (M.set i none) t ⋆ (Rcpts γ e (M.set i none) ⋆ bshare b q k t))) := by
  refine EUpd.withFact grant_fact fun hM => ?_
  refine EUpd.trans (EUpd.of_imp (P' := FAssn.ex fun b => FAssn.ex fun k => ⟪p.block = some b⟫ ⋆
      ((gauthP γ e M t ⋆ (bshare b q (p.off.toNat + n) (some (γ, e)) ⋆ brcpt b q k γ e)) ⋆
        (gfrag γ e i (p, n, q, A, K) ⋆ Rcpts γ e (M.set i none))))
      fun r h => ?_) (EUpd.exAll fun b => EUpd.exAll fun k => EUpd.lift fun hb => ?_)
  · obtain ⟨b, k, hb, h⟩ := open_rcpt (X := gauthP γ e M t ⋆ gfrag γ e i (p, n, q, A, K)) hM
      (of_eq (Q := pshare p q (p.off.toNat + n) (some (γ, e)) ⋆ (Rcpts γ e M ⋆
        (gauthP γ e M t ⋆ gfrag γ e i (p, n, q, A, K)))) (by ac_rfl) h)
    exact ⟨b, k, sep_lift.mpr ⟨hb, of_eq (by ac_rfl) h⟩⟩
  refine EUpd.trans (EUpd.frame EUpd.returnTw) ?_
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ gfrag γ e i (p, n, q, A, K)) ⋆
    (bshare b q k t ⋆ Rcpts γ e (M.set i none))) fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame (EUpd.of_upd Upd.retire)) ?_
  exact EUpd.of_imp fun _ h => ⟨b, k, sep_lift.mpr ⟨hb, of_eq (by ac_rfl) h⟩⟩

/-- **A shrink's ghost part**: the bound of the client's part `q'` of the share comes down to the
new end, the grant is re-pointed; its receipt does not change. -/
theorem shrink_ghost {γ e i : Nat} {M : GMap} {t : STag} {p : Ptr} {n n' : Nat} {q q' : Frac}
    {A : Nat} {K : BlockKind} (hn : n' ≤ n) :
    EUpd (gauthP γ e M t ⋆ (gfrag γ e i (p, n, q, A, K) ⋆ (pshare p q' (p.off.toNat + n) (some (γ, e)) ⋆
      Rcpts γ e M)))
      (gauthP γ e (M.set i (some (p, n', q, A, K))) t ⋆ (gfrag γ e i (p, n', q, A, K) ⋆
        (pshare p q' (p.off.toNat + n') (some (γ, e)) ⋆ Rcpts γ e (M.set i (some (p, n', q, A, K)))))) := by
  refine EUpd.withFact grant_fact fun hM => ?_
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ gfrag γ e i (p, n, q, A, K)) ⋆
    (pshare p q' (p.off.toNat + n) (some (γ, e)) ⋆ Rcpts γ e (M.set i (some (p, n', q, A, K)))))
    fun _ h => sep_assoc' (sep_mono_right (fun _ x => sep_mono_right (fun _ y => sep_mono_right
      (fun _ z => rcpts_repoint hM z) y) x) h)) ?_
  refine EUpd.trans (EUpd.frame (EUpd.of_upd (Upd.reassign (p, n', q, A, K)))) ?_
  refine EUpd.trans (EUpd.frameL (EUpd.frame (EUpd.pweaken (p := p) (q := q') (k := p.off.toNat + n)
    (k' := p.off.toNat + n') (by omega)))) ?_
  exact EUpd.of_imp fun _ h => sep_assoc h

/-- **A growth's extent part** on the node's block `b` (`EUpd.returnTw`, `EUpd.join`,
`EUpd.lendT`): the client's part `q'` of a grant's share goes back against a receipt for it (at
any bound), joins the arena's part `qh` of the node's share at `kN`, and is lent again at the new
end `k'`, with a receipt at `kN`. -/
theorem grow_core {γ e : Nat} {M : GMap} {t : STag} {b : BlockId} {q' qh : Frac} {k₀ k k' kN : Nat}
    (hk : k' ≤ kN) :
    EUpd (gauthP γ e M t ⋆ ((bshare b q' k₀ (some (γ, e)) ⋆ brcpt b q' k γ e) ⋆ bshare b qh kN t))
      (gauthP γ e M t ⋆ ((bshare b q' k' (some (γ, e)) ⋆ brcpt b q' kN γ e) ⋆ bshare b qh kN t)) := by
  refine EUpd.withFact (φ := 0 < q'.val ∧ 0 < qh.val) (fun _ r _ _ h _ => ?_) fun ⟨hq, hqh⟩ => ?_
  · obtain ⟨_, _, -, -, -, _, _, -, -, ⟨_, _, -, -, h1, -⟩, h2⟩ := h
    exact ⟨h1.1, h2.1⟩
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ (bshare b q' k₀ (some (γ, e)) ⋆
    brcpt b q' k γ e)) ⋆ bshare b qh kN t) fun _ h => sep_assoc' h) ?_
  refine EUpd.trans (EUpd.frame EUpd.returnTw) ?_
  refine EUpd.trans (EUpd.of_imp (P' := gauthP γ e M t ⋆ (bshare b qh kN t ⋆ bshare b q' k t))
    fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frameL EUpd.join) ?_
  refine EUpd.trans (EUpd.frameL (EUpd.weaken (k' := kN) (Nat.le_max_left _ _))) ?_
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ bshare b q' kN t) ⋆ bshare b qh kN t)
    fun _ h => of_eq (by ac_rfl) (sep_mono_right (R := bshare b qh kN t ⋆ bshare b q' kN t)
      (fun _ x => (bshare_split hqh hq).mp x) h)) ?_
  refine EUpd.trans (EUpd.frame (EUpd.lendT hk)) ?_
  exact EUpd.of_imp fun _ h => sep_assoc h

/-- **A growth's extent part, from a part of the share**: the client gives back the part `q'` of
the grant's share `q`; the grant's receipt splits (`brcpt_split`), the part `q'` is lent again at
the new end (`grow_core`), and the two receipts join at the lower bound (`EUpd.rjoin`). -/
theorem rcpt_regrow {γ e : Nat} {M : GMap} {t : STag} {b : BlockId} {q q' qh : Frac}
    {k₀ k k' kN : Nat} (hq : q'.val ≤ q.val) (hk : k' ≤ kN) :
    EUpd (gauthP γ e M t ⋆ ((bshare b q' k₀ (some (γ, e)) ⋆ brcpt b q k γ e) ⋆ bshare b qh kN t))
      (gauthP γ e M t ⋆ ((bshare b q' k' (some (γ, e)) ⋆ FAssn.ex fun k₁ => brcpt b q k₁ γ e) ⋆
        bshare b qh kN t)) := by
  by_cases hqq : q'.val = q.val
  · obtain rfl : q' = q := Frac.eq hqq
    exact EUpd.trans (grow_core hk) (EUpd.of_imp fun _ h => sep_mono_right (fun _ x =>
      sep_mono_left (fun _ y => sep_mono_right (fun _ z => ⟨kN, z⟩) y) x) h)
  have hlt : q'.val < q.val := Rat.lt_of_le_of_ne hq hqq
  have hd := Frac.diff_pos hlt
  refine EUpd.withFact (φ := 0 < q'.val) (fun _ r _ _ h _ => ?_) fun hq' => ?_
  · obtain ⟨_, _, -, -, -, _, _, -, -, ⟨_, _, -, -, h1, -⟩, -⟩ := h
    exact h1.1
  have e1 : brcpt b q k γ e = brcpt b (q'.add (q.diff q' (Rat.le_of_lt hlt))) k γ e := by
    rw [Frac.add_diff]
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ ((bshare b q' k₀ (some (γ, e)) ⋆
      brcpt b q' k γ e) ⋆ bshare b qh kN t)) ⋆ brcpt b (q.diff q' (Rat.le_of_lt hlt)) k γ e)
    fun _ h => ?_) ?_
  · rw [e1] at h
    have h := sep_mono_right (R := (bshare b q' k₀ (some (γ, e)) ⋆ (brcpt b q' k γ e ⋆
      brcpt b (q.diff q' (Rat.le_of_lt hlt)) k γ e)) ⋆ bshare b qh kN t)
      (fun _ x => sep_mono_left (Q := bshare b q' k₀ (some (γ, e)) ⋆ (brcpt b q' k γ e ⋆
        brcpt b (q.diff q' (Rat.le_of_lt hlt)) k γ e)) (fun _ y => sep_mono_right
        (R := brcpt b q' k γ e ⋆ brcpt b (q.diff q' (Rat.le_of_lt hlt)) k γ e)
        (fun _ z => (brcpt_split hq' hd).mp z) y) x) h
    exact of_eq (by ac_rfl) h
  refine EUpd.trans (EUpd.frame (grow_core hk)) ?_
  refine EUpd.trans (EUpd.of_imp (P' := (brcpt b q' kN γ e ⋆ brcpt b (q.diff q' (Rat.le_of_lt hlt)) k γ e) ⋆
    (gauthP γ e M t ⋆ (bshare b q' k' (some (γ, e)) ⋆ bshare b qh kN t))) fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame EUpd.rjoin) ?_
  refine EUpd.of_imp fun _ h => ?_
  rw [Frac.add_diff] at h
  have h := sep_mono_left (Q := FAssn.ex fun k₁ => brcpt b q k₁ γ e) (fun _ x => ⟨_, x⟩) h
  exact of_eq (by ac_rfl) h

/-- **A growth's ghost part** (a grant in the node whose share `qh` at `kN` the arena keeps): the
client's part `q'` of the share is re-lent at the new end (`rcpt_regrow`), the grant is re-pointed
at the new length (with the kind label `K'` of the bytes it gets). -/
theorem grow_ghost {γ e i : Nat} {M : GMap} {t : STag} {p N : Ptr} {n n' kN : Nat} {q q' qh : Frac}
    {A : Nat} {K K' : BlockKind} (hq : q'.val ≤ q.val) (hpN : p.block = N.block)
    (hk : p.off.toNat + n' ≤ kN) :
    EUpd (gauthP γ e M t ⋆ (gfrag γ e i (p, n, q, A, K) ⋆ (pshare p q' (p.off.toNat + n) (some (γ, e)) ⋆
        (Rcpts γ e M ⋆ pshare N qh kN t))))
      (gauthP γ e (M.set i (some (p, n', q, A, K'))) t ⋆ (gfrag γ e i (p, n', q, A, K') ⋆
        (pshare p q' (p.off.toNat + n') (some (γ, e)) ⋆
          (Rcpts γ e (M.set i (some (p, n', q, A, K'))) ⋆ pshare N qh kN t)))) := by
  refine EUpd.withFact grant_fact fun hM => ?_
  have hM' : (M.set i none) i = none := GMap.set_same M i none
  refine EUpd.trans (EUpd.of_imp (P' := FAssn.ex fun b => FAssn.ex fun k => ⟪p.block = some b⟫ ⋆
      ((gauthP γ e M t ⋆ ((bshare b q' (p.off.toNat + n) (some (γ, e)) ⋆ brcpt b q k γ e) ⋆
        bshare b qh kN t)) ⋆ (gfrag γ e i (p, n, q, A, K) ⋆ Rcpts γ e (M.set i none))))
      fun r h => ?_) (EUpd.exAll fun b => EUpd.exAll fun k => EUpd.lift fun hb => ?_)
  · obtain ⟨b, k, hb, h⟩ := open_rcpt (X := gauthP γ e M t ⋆ gfrag γ e i (p, n, q, A, K) ⋆
      pshare N qh kN t) hM (of_eq (by ac_rfl) h)
    have hbN : N.block = some b := hpN ▸ hb
    have h := of_eq (Q := pshare N qh kN t ⋆ ((bshare b q' (p.off.toNat + n) (some (γ, e)) ⋆
      brcpt b q k γ e) ⋆ (gauthP γ e M t ⋆ gfrag γ e i (p, n, q, A, K) ⋆ Rcpts γ e (M.set i none))))
      (by ac_rfl) h
    exact ⟨b, k, sep_lift.mpr ⟨hb, of_eq (by ac_rfl) (sep_mono_left (Q := bshare b qh kN t)
      (fun _ x => (pshare_iff hbN).mp x) h)⟩⟩
  have hbN : N.block = some b := hpN ▸ hb
  refine EUpd.trans (EUpd.frame (rcpt_regrow (k' := p.off.toNat + n') hq hk)) ?_
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ gfrag γ e i (p, n, q, A, K)) ⋆
      (bshare b q' (p.off.toNat + n') (some (γ, e)) ⋆ (rcptOf γ e (some (p, n', q, A, K')) ⋆
        (Rcpts γ e (M.set i none) ⋆ bshare b qh kN t)))) fun _ h => ?_) ?_
  · have h := of_eq (Q := (FAssn.ex fun k₁ => brcpt b q k₁ γ e) ⋆ ((gauthP γ e M t ⋆
      gfrag γ e i (p, n, q, A, K)) ⋆ (bshare b q' (p.off.toNat + n') (some (γ, e)) ⋆
        (Rcpts γ e (M.set i none) ⋆ bshare b qh kN t)))) (by ac_rfl) h
    obtain ⟨k₁, h⟩ := sep_ex.mp h
    have h := sep_mono_left (Q := rcptOf γ e (some (p, n', q, A, K')))
      (fun _ x => ⟨b, k₁, sep_lift.mpr ⟨hb, x⟩⟩) h
    exact of_eq (by ac_rfl) h
  refine EUpd.trans (EUpd.frame (EUpd.of_upd (Upd.reassign (p, n', q, A, K')))) ?_
  refine EUpd.of_imp fun _ h => ?_
  have h := of_eq (Q := (rcptOf γ e (some (p, n', q, A, K')) ⋆ Rcpts γ e (M.set i none)) ⋆
    ((gauthP γ e (M.set i (some (p, n', q, A, K'))) t ⋆ gfrag γ e i (p, n', q, A, K')) ⋆
      bshare b q' (p.off.toNat + n') (some (γ, e)) ⋆ bshare b qh kN t)) (by ac_rfl) h
  have h := sep_mono_left (Q := Rcpts γ e ((M.set i none).set i (some (p, n', q, A, K'))))
    (fun _ x => rcpts_put hM' x) h
  rw [GMap.set_set] at h
  have h := of_eq (Q := bshare b q' (p.off.toNat + n') (some (γ, e)) ⋆ (bshare b qh kN t ⋆
    (Rcpts γ e (M.set i (some (p, n', q, A, K'))) ⋆ (gauthP γ e (M.set i (some (p, n', q, A, K'))) t ⋆
      gfrag γ e i (p, n', q, A, K'))))) (by ac_rfl) h
  have h := sep_mono_left (Q := pshare p q' (p.off.toNat + n') (some (γ, e)))
    (fun _ x => (pshare_iff hb).mpr x) h
  have h := sep_mono_right (R := pshare N qh kN t ⋆ (Rcpts γ e (M.set i (some (p, n', q, A, K'))) ⋆
    (gauthP γ e (M.set i (some (p, n', q, A, K'))) t ⋆ gfrag γ e i (p, n', q, A, K'))))
    (fun _ x => sep_mono_left (Q := pshare N qh kN t) (fun _ y => (pshare_iff hbN).mpr y) x) h
  exact of_eq (by ac_rfl) h

end Glue

/-! ## The ends of `free` and `resize`

Each branch of the entries ends in one of these updates from the precondition the code leaves
(the first node's `end_index` word as the `cmpxchg` left it) to the entry's postcondition. -/

/-- The facts after a `free`: the grant retired, its share pushed to the pool, the first node's
`end_index` and tail as given (`hff`). -/
theorem facts_free {w : OV} (hw : w.Facts) {i : Nat} {p : Ptr} {n : Nat} {q : Frac} {A : Nat}
    {K : BlockKind} (hMi : w.M i = some (p, n, q, A, K)) {b : BlockId} {k ei : Nat}
    {tail : Array Byte} {jh : Heap} (hb : p.block = some b)
    (hff : OV.FirstFacts { w with M := w.M.set i none, ei := ei, tail := tail })
    (hcov : OV.Cov { w with M := w.M.set i none, ei := ei, tail := tail, jh := jh }) :
    OV.Facts
      { w with M := w.M.set i none, ei := ei, tail := tail, pn := w.pn + 1,
               pf := poolPush w.pn w.pf (b, q, k), jh := jh } := by
  obtain ⟨hfin, -, hgr, hacct, hqq, -⟩ := hw
  have hi := lt_bound hfin hMi
  exact ⟨bound_set hfin hi _, hff, grants_set hgr _ (fun g hg => by cases hg),
    acct_free hacct hMi hi hb, hqq, hcov⟩

/-- The facts after a grant is re-pointed (same pointer and fraction, labels `A'`, `K'` of a node
of its block), the first node's `end_index` and tail as given (`hff`). -/
theorem facts_repoint {w : OV} (hw : w.Facts) {i : Nat} {p : Ptr} {n n' : Nat} {q : Frac}
    {A A' : Nat} {K K' : BlockKind} (hMi : w.M i = some (p, n, q, A, K)) {ei : Nat} {tail : Array Byte}
    (hg : GrantOk w.nodes (p, n', q, A', K'))
    {jh : Heap}
    (hff : OV.FirstFacts { w with M := w.M.set i (some (p, n', q, A', K')), ei := ei, tail := tail })
    (hcov : OV.Cov { w with M := w.M.set i (some (p, n', q, A', K')), ei := ei, tail := tail, jh := jh }) :
    OV.Facts { w with M := w.M.set i (some (p, n', q, A', K')), ei := ei, tail := tail, jh := jh } := by
  obtain ⟨hfin, -, hgr, hacct, hqq, -⟩ := hw
  exact ⟨bound_set hfin (lt_bound hfin hMi) _, hff, grants_set hgr _ fun g hg' => by cases hg'; exact hg,
    fun b => by show ndLent b w.nodes = _; rw [acct_repoint hMi, hacct b], hqq, hcov⟩

/-- Push the share that `free_ghost` gave back into the pool. -/
theorem pool_of_free {γ e i : Nat} {M : GMap} {t : STag} {p : Ptr} {q : Frac} {pn : Nat}
    {pf : Nat → BlockId × Frac × Nat} {X : FAssn} {r : Res}
    (h : ((FAssn.ex fun b => FAssn.ex fun k => ⟪p.block = some b⟫ ⋆
        (gauthP γ e (M.set i none) t ⋆ (Rcpts γ e (M.set i none) ⋆ bshare b q k t))) ⋆
      (Pool t pn pf ⋆ X)) r) :
    ∃ b k, p.block = some b ∧ ((gauthP γ e (M.set i none) t ⋆ Rcpts γ e (M.set i none) ⋆
      Pool t (pn + 1) (poolPush pn pf (b, q, k))) ⋆ X) r := by
  obtain ⟨b, h⟩ := sep_ex.mp h
  obtain ⟨k, h⟩ := sep_ex.mp h
  obtain ⟨hb, h⟩ := sep_lift.mp (sep_assoc h)
  have h := of_eq (Q := (bshare b q k t ⋆ Pool t pn pf) ⋆ ((gauthP γ e (M.set i none) t ⋆
    Rcpts γ e (M.set i none)) ⋆ X)) (by ac_rfl) h
  exact ⟨b, k, hb, of_eq (by ac_rfl) (sep_mono_left (Q := Pool t (pn + 1) (poolPush pn pf (b, q, k)))
    (fun _ x => pool_add x) h)⟩

section Ends

variable {CI : Child} {γ e : Nat} {ctx : Ptr} {s : Slice}

/-- `resize`'s postcondition `true` from the arena's variables, the re-pointed token and share,
and the new bytes `X` of a growth. -/
theorem rpost_true {w : OV} (hw : w.Facts) {p : Ptr} {k len n A S S' : Nat} {K K' : BlockKind}
    {q q' : Frac} {tl : Array Byte} {i : Nat} {X : FAssn} (hK : K'.norm = K.norm)
    (hX : ∀ r, X r → (inv CI γ e ctx).newBytes p A S' K' len n r) {r : Res}
    (h : (w.body CI γ e ctx ⋆ ((gfrag γ e i (p, n, q, A, K') ⋆
      pshare p q' (p.off.toNat + n) (some (γ, e))) ⋆ X)) r) :
    (inv CI γ e ctx).rresizePost p k len n A S K q q' tl true r :=
  own_of hw (sep_mono_right (fun _ x => ⟨S', K', sep_lift.mpr ⟨hK, sep_mono_left
    (fun _ y => sep_mono_left (fun _ z => ⟨i, z⟩) y) (sep_mono_right hX x)⟩⟩) h)

/-- `resize`'s postcondition `true` of a shrink (no new bytes). -/
theorem rpost_true0 {w : OV} (hw : w.Facts) {p : Ptr} {k len n A S : Nat} {K : BlockKind}
    {q q' : Frac} {tl : Array Byte} {i : Nat} (hle : n ≤ len) {r : Res}
    (h : (w.body CI γ e ctx ⋆ (gfrag γ e i (p, n, q, A, K) ⋆
      pshare p q' (p.off.toNat + n) (some (γ, e)))) r) :
    (inv CI γ e ctx).rresizePost p k len n A S K q q' tl true r :=
  rpost_true (S' := S) hw rfl (fun r hr => by
    simp only [FAllocInv.newBytes, if_neg (show ¬ len < n by omega)]; exact hr)
    (sep_mono_right (fun _ x => sep_emp.mpr x) h)

/-- The junk after bytes `[lo, hi)` of `p`'s block joined it: it keeps its bytes and has those. -/
def JunkGrew (p : Ptr) (lo hi : Nat) (jh jh' : Heap) : Prop :=
  (∀ l, jh l ≠ none → jh' l ≠ none) ∧
    ∀ b x, p.block = some b → p.off.toNat + lo ≤ x → x < p.off.toNat + hi → jh' (b, x) ≠ none

/-- A region joins the junk (`junkAt_absorbR`). -/
theorem junk_grew {p q : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte} {jh : Heap}
    {R : FAssn} {lo : Nat} (hp0 : 0 ≤ p.off) (hq : q.block = p.block) (hqo : q.off = p.off + lo)
    {r : Res} (h : ((up (regionIn q A S K a bs) ⋆ JunkAt jh) ⋆ R) r) :
    ∃ jh', JunkGrew p lo (lo + bs.size) jh jh' ∧ (JunkAt jh' ⋆ R) r := by
  obtain ⟨h₁, hX, h⟩ := junkAt_absorbR h
  refine ⟨h₁ ∪ jh, ⟨fun l hl => Heap.union_ne_none_right hl, fun b x hb h1 h2 => ?_⟩, h⟩
  have ho : q.off.toNat = p.off.toNat + lo := by omega
  exact Covers.region_union (by rw [hq]; exact hb) hX (by omega) (by omega)

/-- Released bytes become junk, their claim is forgotten. -/
theorem relB_junk {n : Nat} {tl : Array Byte} {A S : Nat} {K : BlockKind} {jh : Heap}
    (hp0 : 0 ≤ s.ptr.off) :
    EUpd (relB CI γ e ctx s n tl A S K ⋆ JunkAt jh)
      (FAssn.ex fun jh' => ⟪JunkGrew s.ptr n s.len.toNat jh jh'⟫ ⋆ JunkAt jh') := by
  simp only [relB, FAllocInv.relBytes, inv_tag]
  split
  · rename_i hlt
    refine EUpd.trans (EUpd.of_imp (P' := (FAssn.ex fun jh' => ⟪JunkGrew s.ptr n s.len.toNat jh jh'⟫ ⋆
      JunkAt jh') ⋆ pclaim s.ptr (s.ptr.off.toNat + n) (s.ptr.off.toNat + s.len.toNat) (some (γ, e)))
      fun _ h => ?_) (EUpd.drop fun _ h => pclaim_ghost h)
    obtain ⟨htl, h⟩ := sep_lift.mp (sep_assoc h)
    obtain ⟨jh', hg, h⟩ := junk_grew (p := s.ptr) (q := s.ptr.add n) (lo := n) hp0 rfl rfl (of_eq (Q := (up (regionIn (s.ptr.add n) A S K 1 tl) ⋆
      JunkAt jh) ⋆ pclaim s.ptr (s.ptr.off.toNat + n) (s.ptr.off.toNat + s.len.toNat) (some (γ, e)))
      (by ac_rfl) h)
    rw [htl, show n + (s.len.toNat - n) = s.len.toNat by omega] at hg
    exact sep_mono_left (fun _ y => ⟨jh', sep_lift.mpr ⟨hg, y⟩⟩) h
  · rename_i hge
    refine EUpd.of_imp fun _ h => ⟨jh, sep_lift.mpr ⟨⟨fun _ hl => hl, fun b x _ h1 h2 => by omega⟩,
      of_eq (emp_sep_eq _) h⟩⟩

/-- `resize`'s postcondition `false`: nothing changed. -/
theorem resize_false_of {v : FV} (hv : v.Facts ctx s) (hfirst : v.w.first = some v.N) {k n : Nat}
    {tl : Array Byte} {r : Res} (h : v.L CI γ e ctx s (relB CI γ e ctx s n tl) r) :
    (inv CI γ e ctx).rresizePost s.ptr k s.len.toNat n v.A' v.S' v.K' v.q v.q' tl false r := by
  refine own_of (w := v.w) hv.1 (sep_mono_right (fun _ x => sep_mono_left (fun _ y =>
    sep_mono_left (fun _ z => ⟨v.i, z⟩) y) x) (of_eq (Q := v.w.body CI γ e ctx ⋆
      ((gfrag γ e v.i (s.ptr, s.len.toNat, v.q, v.A', v.K') ⋆
        pshare s.ptr v.q' (s.ptr.off.toNat + s.len.toNat) (some (γ, e))) ⋆ relB CI γ e ctx s n tl v.A' v.S' v.K'))
      ?_ h))
  simp only [OV.body, FirstPart, hfirst, Header, FV.L, FV.R0, FV.gA, FV.gT, FV.uW, FV.eW, FV.nR,
    FV.cR, FV.tR, FV.F, FV.nS, FV.xs, FV.cl, OV.cls, FirstCl]
  ac_rfl

/-- `free` of a slice that is not the first node's last allocation: its bytes leak to junk, its
share goes back into the pool, the grant is retired. -/
theorem free_other_upd {v : FV} (hv : v.Facts ctx s) (hq : v.q' = v.q)
    (hfirst : v.w.first = some v.N) (hnf : NodeFacts v.N v.w.A v.w.sz) (hei : 24 + v.w.ei ≤ v.w.sz)
    (htail : v.w.tail.size = v.w.sz - 24 - v.w.ei) {k : Nat} {bs : Array Byte}
    (hlen : s.len.toNat = bs.size) :
    EUpd (v.L CI γ e ctx s (rgn γ e s k bs)) (inv CI γ e ctx).own := by
  obtain ⟨hw, -, -, -, -, -, -, -, hp0, hMi⟩ := hv
  refine EUpd.trans (EUpd.of_imp (P' := ((gauthP γ e v.w.M CI.tag ⋆
      (gfrag γ e v.i (s.ptr, s.len.toNat, v.q, v.A', v.K') ⋆
      (pshare s.ptr v.q (s.ptr.off.toNat + s.len.toNat) (some (γ, e)) ⋆ Rcpts γ e v.w.M))) ⋆
      (Pool CI.tag v.w.pn v.w.pf ⋆ ((up (regionIn s.ptr v.A' v.S' v.K' (2 ^ k) bs) ⋆ JunkAt v.w.jh) ⋆
        (v.uW ctx ⋆ v.eW v.w.ei ⋆ v.nR ⋆ v.cR CI ctx ⋆ v.tR v.w.ei v.w.tail ⋆ v.F CI ctx ⋆
          v.cl CI γ e v.w.ei)))) ⋆
      pclaim s.ptr s.ptr.off.toNat (s.ptr.off.toNat + bs.size) (some (γ, e)))
    fun _ h => of_eq (by simp only [FV.L, FV.R0, FV.xs, FV.gA, FV.gT, hq, rgn]; ac_rfl) h) ?_
  -- the grant's claim is forgotten
  refine EUpd.trans (EUpd.drop fun _ h => pclaim_ghost h) ?_
  refine EUpd.trans (EUpd.frame free_ghost) ?_
  refine EUpd.of_imp fun r h => ?_
  obtain ⟨b, k', hb, h⟩ := pool_of_free h
  -- the slice's bytes join the junk
  obtain ⟨jh', hg, h⟩ := junk_grew (p := s.ptr) (lo := 0) hp0 rfl (by simp) (of_eq (sep_left_comm_eq _ _ _) h)
  rw [Nat.zero_add, ← hlen] at hg
  have hcov : OV.Cov { v.w with M := v.w.M.set v.i none, ei := v.w.ei, tail := v.w.tail, jh := jh' } :=
    OV.Cov.same hw.2.2.2.2.2 rfl (OV.avail_shrink (n' := 0) hMi (fun j hj => GMap.set_ne _ _ hj)
      (fun _ _ _ _ _ => by omega) hg.1 (fun b x hb h1 h2 => Or.inl (hg.2 b x hb (by omega) h2))
      fun _ _ h => Or.inr (Or.inr h))
  refine ⟨_, sep_lift.mpr ⟨facts_free (k := k') (ei := v.w.ei) (tail := v.w.tail) hw hMi hb ?_ hcov,
    of_eq ?_ h⟩⟩
  · simp only [OV.FirstFacts, hfirst]; exact ⟨hnf, hei, htail⟩
  · simp only [OV.body, FirstPart, hfirst, Header, FV.uW, FV.eW, FV.nR, FV.cR, FV.tR, FV.F, FV.nS,
      FV.cl, OV.cls, FirstCl]
    ac_rfl

/-- `free` of the first node's last allocation: `end_index` moved back; the slice's bytes (relabeled
as the node's, `EUpd.relabel`) rejoin the tail, its share goes back into the pool, the grant is
retired. -/
theorem free_last_upd {φ : Prop} {v : FV} {wv : BitVec 64} (hv : v.Facts ctx s) (hq : v.q' = v.q)
    (hfirst : v.w.first = some v.N) (hnf : NodeFacts v.N v.w.A v.w.sz) (hei : 24 + v.w.ei ≤ v.w.sz)
    (htail : v.w.tail.size = v.w.sz - 24 - v.w.ei) (hb : v.bp = v.bN) (hA : v.A' = v.w.A)
    (hK : v.K'.norm = v.w.K.norm) {k : Nat} {bs : Array Byte} (hlen : s.len.toNat = bs.size)
    (hoff : s.ptr.off.toNat + s.len.toNat = v.N.off.toNat + 24 + v.w.ei)
    (hlo : v.N.off.toNat + 24 ≤ s.ptr.off.toNat) (hw : wv = BitVec.ofNat 64 (v.w.ei - s.len.toNat)) :
    EUpd ((⟪φ⟫ ⋆ apts (v.N.add 8) wv) ⋆ (v.uW ctx ⋆ v.R0 CI γ e ctx s (rgn γ e s k bs)))
      (inv CI γ e ctx).own := by
  subst hw
  obtain ⟨hw, -, -, hbN, hbp, -, -, -, -, hMi⟩ := hv
  have hpN : s.ptr.block = v.N.block := by rw [hbp, hbN, hb]
  -- the slice's claim joins the tail's (`tailCl_join`)
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e v.w.M CI.tag ⋆
      (gfrag γ e v.i (s.ptr, s.len.toNat, v.q, v.A', v.K') ⋆
      (pshare s.ptr v.q (s.ptr.off.toNat + s.len.toNat) (some (γ, e)) ⋆ Rcpts γ e v.w.M))) ⋆
      (Pool CI.tag v.w.pn v.w.pf ⋆ (up (regionIn s.ptr v.A' v.S' v.K' (2 ^ k) bs) ⋆
        (apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei - s.len.toNat)) ⋆ v.uW ctx ⋆ v.nR ⋆
        v.cR CI ctx ⋆ v.tR v.w.ei v.w.tail ⋆ JunkAt v.w.jh ⋆ v.F CI ctx ⋆ v.cl CI γ e (v.w.ei - s.len.toNat)))))
    fun _ h => of_eq (by
        simp only [FV.R0, FV.xs, FV.gA, FV.gT, rgn, hq, FV.cl]
        rw [← tailCl_join (p := s.ptr) (lo := s.ptr.off.toNat) (hi := s.ptr.off.toNat + bs.size)
          (ei' := v.w.ei - s.len.toNat) (ei := v.w.ei) hpN (by omega) (by omega) (by omega) hei]
        ac_rfl)
      (sep_mono_left (Q := apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei - s.len.toNat)))
        (fun _ x => (sep_lift.mp x).2) h)) ?_
  refine EUpd.trans (EUpd.frame free_ghost) ?_
  refine EUpd.trans (EUpd.frameL (EUpd.frameL (EUpd.frame (EUpd.relabel (S' := v.w.S) hK.symm)))) ?_
  refine EUpd.of_imp fun r h => ?_
  obtain ⟨b, k', hb', h⟩ := pool_of_free h
  have hpq : s.ptr = v.N.add (24 + ((v.w.ei - s.len.toNat : Nat) : Int)) := by
    have hb' : s.ptr.block = v.N.block := by rw [hbp, hbN, hb]
    have ho : s.ptr.off = v.N.off + (24 + ((v.w.ei - s.len.toNat : Nat) : Int)) := by
      have := hnf.off0; omega
    rw [show s.ptr = ⟨s.ptr.block, s.ptr.off⟩ from rfl, hb', ho]; rfl
  have hjoin : ∀ r, (up (regionIn s.ptr v.A' v.w.S v.w.K (2 ^ k) bs) ⋆ v.tR v.w.ei v.w.tail) r →
      up (regionIn (v.N.add (24 + ((v.w.ei - s.len.toNat : Nat) : Int))) v.w.A v.w.S v.w.K 1
        (bs ++ v.w.tail)) r := by
    intro r hr
    obtain ⟨⟨h₁, h₂, hd₁, he, x1, x2⟩, hk, hg⟩ := sep_up hr
    refine ⟨?_, hk, hg⟩
    rw [he, ← hpq]
    refine regionIn_join (a' := 1) ⟨h₁, h₂, hd₁, rfl, ?_, ?_⟩
    · rw [hA] at x1; exact regionIn_weaken x1 (Nat.one_dvd _)
    · have : s.ptr.add bs.size = v.N.add (24 + (v.w.ei : Int)) := by
        rw [hpq]; simp only [Ptr.add, Ptr.mk.injEq, true_and]; have := hnf.off0; omega
      rw [this]; exact x2
  have h' := of_eq (Q := (up (regionIn s.ptr v.A' v.w.S v.w.K (2 ^ k) bs) ⋆ v.tR v.w.ei v.w.tail) ⋆
    (gauthP γ e (v.w.M.set v.i none) CI.tag ⋆ Rcpts γ e (v.w.M.set v.i none) ⋆
      Pool CI.tag (v.w.pn + 1) (poolPush v.w.pn v.w.pf (b, v.q, k')) ⋆
      apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei - s.len.toNat)) ⋆ v.uW ctx ⋆ v.nR ⋆ v.cR CI ctx ⋆ JunkAt v.w.jh ⋆
      v.F CI ctx ⋆ v.cl CI γ e (v.w.ei - s.len.toNat))) (by ac_rfl) h
  have h'' := sep_mono_left (Q := up (regionIn (v.N.add (24 + ((v.w.ei - s.len.toNat : Nat) : Int)))
    v.w.A v.w.S v.w.K 1 (bs ++ v.w.tail))) hjoin h'
  -- the slice's bytes are the tail's now
  have hcov : OV.Cov
      { v.w with M := v.w.M.set v.i none, ei := v.w.ei - s.len.toNat,
                 tail := bs ++ v.w.tail, jh := v.w.jh } :=
    OV.Cov.same hw.2.2.2.2.2 rfl (OV.avail_shrink (n' := 0) hMi (fun j hj => GMap.set_ne _ _ hj)
      (fun _ _ _ _ _ => by omega) (fun _ h => h)
      (fun b x hb1 h1 h2 => OV.avail_tail hfirst (by rw [← hpN]; exact hb1) (by dsimp only; omega)
        (by dsimp only; omega))
      fun b x h => by
        obtain ⟨hb1, h1, h2⟩ := h.of_first hfirst
        exact OV.avail_tail hfirst hb1 (by dsimp only; omega) h2)
  refine ⟨_, sep_lift.mpr ⟨facts_free (k := k') (ei := v.w.ei - s.len.toNat) (tail := bs ++ v.w.tail)
    hw hMi hb' ?_ hcov, of_eq ?_ h''⟩⟩
  · simp only [OV.FirstFacts, hfirst]
    exact ⟨hnf, by omega, by simp only [Array.size_append, htail]; have := hnf.hdr; omega⟩
  · simp only [OV.body, FirstPart, hfirst, Header, FV.uW, FV.nR, FV.cR, FV.F, FV.nS, FV.cl, OV.cls,
      FirstCl]
    ac_rfl

/-- `resize` to `n ≤ len` of a slice that is not the first node's last allocation (or of the last
one to the same length): the released bytes leak to junk, the share's bound comes down, the grant
is re-pointed. -/
theorem resize_other_upd {v : FV} (hv : v.Facts ctx s) (hfirst : v.w.first = some v.N)
    (hnf : NodeFacts v.N v.w.A v.w.sz) (hei : 24 + v.w.ei ≤ v.w.sz)
    (htail : v.w.tail.size = v.w.sz - 24 - v.w.ei) {k n : Nat} {tl : Array Byte}
    (hle : n ≤ s.len.toNat) :
    EUpd (v.L CI γ e ctx s (relB CI γ e ctx s n tl))
      ((inv CI γ e ctx).rresizePost s.ptr k s.len.toNat n v.A' v.S' v.K' v.q v.q' tl true) := by
  obtain ⟨hw, -, -, -, -, -, -, -, hp0, hMi⟩ := hv
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e v.w.M CI.tag ⋆
      (gfrag γ e v.i (s.ptr, s.len.toNat, v.q, v.A', v.K') ⋆
      (pshare s.ptr v.q' (s.ptr.off.toNat + s.len.toNat) (some (γ, e)) ⋆ Rcpts γ e v.w.M))) ⋆
      ((relB CI γ e ctx s n tl v.A' v.S' v.K' ⋆ JunkAt v.w.jh) ⋆ (Pool CI.tag v.w.pn v.w.pf ⋆ v.uW ctx ⋆ v.eW v.w.ei ⋆ v.nR ⋆ v.cR CI ctx ⋆
        v.tR v.w.ei v.w.tail ⋆ v.F CI ctx ⋆ v.cl CI γ e v.w.ei)))
    fun _ h => of_eq (by simp only [FV.L, FV.R0, FV.xs, FV.gA, FV.gT]; ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame (shrink_ghost hle)) ?_
  refine EUpd.trans (EUpd.frameL (EUpd.frame (relB_junk hp0))) ?_
  refine EUpd.of_imp fun r h => ?_
  -- the released bytes are junk now
  obtain ⟨jh', h⟩ := sep_ex.mp (of_eq (sep_left_comm_eq _ _ _) h)
  obtain ⟨hg, h⟩ := sep_lift.mp (sep_assoc h)
  have hcov : OV.Cov
      { v.w with M := v.w.M.set v.i (some (s.ptr, n, v.q, v.A', v.K')), ei := v.w.ei,
                 tail := v.w.tail, jh := jh' } :=
    OV.Cov.same hw.2.2.2.2.2 rfl (OV.avail_shrink (n' := n) hMi (fun j hj => GMap.set_ne _ _ hj)
      (fun _ _ hb h1 h2 => GrantHas.set hb h1 h2)
      hg.1 (fun b x hb h1 h2 => Or.inl (hg.2 b x hb h1 h2)) fun _ _ h => Or.inr (Or.inr h))
  refine rpost_true0 (facts_repoint (n' := n) (ei := v.w.ei) (tail := v.w.tail) hw hMi
    (GrantOk.len (hw.2.2.1 _ _ hMi)) ?_ hcov) hle (i := v.i) (of_eq ?_ h)
  · simp only [OV.FirstFacts, hfirst]; exact ⟨hnf, hei, htail⟩
  · simp only [OV.body, FirstPart, hfirst, Header, FV.uW, FV.eW, FV.nR, FV.cR, FV.tR, FV.F, FV.nS,
      FV.cl, OV.cls, FirstCl]
    ac_rfl

/-- `resize` of the first node's last allocation to `n ≤ len`: `end_index` moves back by
`len - n`; the released bytes (relabeled as the node's) rejoin the tail, the share's bound comes
down, the grant is re-pointed. -/
theorem resize_shrink_upd {φ : Prop} {v : FV} {wv : BitVec 64} (hv : v.Facts ctx s)
    (hfirst : v.w.first = some v.N) (hnf : NodeFacts v.N v.w.A v.w.sz) (hei : 24 + v.w.ei ≤ v.w.sz)
    (htail : v.w.tail.size = v.w.sz - 24 - v.w.ei) (hb : v.bp = v.bN) (hA : v.A' = v.w.A)
    (hK : v.K'.norm = v.w.K.norm) (hoff : s.ptr.off.toNat + s.len.toNat = v.N.off.toNat + 24 + v.w.ei)
    {k n : Nat} {tl : Array Byte} (hle : n ≤ s.len.toNat)
    (hcf : n < s.len.toNat → tl.size = s.len.toNat - n ∧ v.N.off.toNat + 24 ≤ s.ptr.off.toNat + n)
    (hw : wv = BitVec.ofNat 64 (v.w.ei - (s.len.toNat - n))) :
    EUpd ((⟪φ⟫ ⋆ apts (v.N.add 8) wv) ⋆ (v.uW ctx ⋆ v.R0 CI γ e ctx s (relB CI γ e ctx s n tl)))
      ((inv CI γ e ctx).rresizePost s.ptr k s.len.toNat n v.A' v.S' v.K' v.q v.q' tl true) := by
  subst hw
  by_cases hsame : n = s.len.toNat
  · -- the same length: `end_index` stays
    have hn : s.len.toNat - n = 0 := by omega
    rw [hn, Nat.sub_zero]
    exact EUpd.trans (EUpd.of_imp fun _ h => of_eq (by simp only [FV.L, FV.eW]; ac_rfl)
      (sep_mono_left (Q := apts (v.N.add 8) (BitVec.ofNat 64 v.w.ei)) (fun _ x => (sep_lift.mp x).2) h))
      (resize_other_upd hv hfirst hnf hei htail hle)
  have hcut : n < s.len.toNat := by omega
  obtain ⟨htl, hlo⟩ := hcf hcut
  obtain ⟨hw, -, -, hbN, hbp, -, -, -, hp0, hMi⟩ := hv
  have h0 := hnf.off0
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e v.w.M CI.tag ⋆
      (gfrag γ e v.i (s.ptr, s.len.toNat, v.q, v.A', v.K') ⋆
      (pshare s.ptr v.q' (s.ptr.off.toNat + s.len.toNat) (some (γ, e)) ⋆ Rcpts γ e v.w.M))) ⋆
      (up (regionIn (s.ptr.add n) v.A' v.S' v.K' 1 tl) ⋆ (Pool CI.tag v.w.pn v.w.pf ⋆
        apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei - (s.len.toNat - n))) ⋆
        v.uW ctx ⋆ v.nR ⋆ v.cR CI ctx ⋆ v.tR v.w.ei v.w.tail ⋆ JunkAt v.w.jh ⋆ v.F CI ctx ⋆
        v.cl CI γ e (v.w.ei - (s.len.toNat - n)))))
    fun _ h => ?_) ?_
  · -- the released bytes' claim joins the tail's (`tailCl_join`)
    have hpN : s.ptr.block = v.N.block := by rw [hbp, hbN, hb]
    have h := sep_mono_left (Q := apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei - (s.len.toNat - n))))
      (fun _ x => (sep_lift.mp x).2) h
    simp only [FV.R0, FV.xs, FV.gA, FV.gT, relB, FAllocInv.relBytes, if_pos hcut, inv_tag, FV.cl] at h
    exact (sep_lift.mp (of_eq (Q := ⟪tl.size = s.len.toNat - n⟫ ⋆ ((gauthP γ e v.w.M CI.tag ⋆
      (gfrag γ e v.i (s.ptr, s.len.toNat, v.q, v.A', v.K') ⋆
      (pshare s.ptr v.q' (s.ptr.off.toNat + s.len.toNat) (some (γ, e)) ⋆ Rcpts γ e v.w.M))) ⋆
      (up (regionIn (s.ptr.add n) v.A' v.S' v.K' 1 tl) ⋆ (Pool CI.tag v.w.pn v.w.pf ⋆
        apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei - (s.len.toNat - n))) ⋆
        v.uW ctx ⋆ v.nR ⋆ v.cR CI ctx ⋆ v.tR v.w.ei v.w.tail ⋆ JunkAt v.w.jh ⋆ v.F CI ctx ⋆
        v.cl CI γ e (v.w.ei - (s.len.toNat - n)))))) (by
          simp only [FV.cl]
          rw [← tailCl_join (p := s.ptr) (lo := s.ptr.off.toNat + n) (hi := s.ptr.off.toNat + s.len.toNat)
            (ei' := v.w.ei - (s.len.toNat - n)) (ei := v.w.ei) hpN (by omega) (by omega) (by omega) hei]
          ac_rfl) h)).2
  refine EUpd.trans (EUpd.frame (shrink_ghost (Nat.le_of_lt hcut))) ?_
  refine EUpd.trans (EUpd.frameL (EUpd.frame (EUpd.relabel (S' := v.w.S) hK.symm))) ?_
  refine EUpd.of_imp fun r h => ?_
  -- the released bytes `[n, len)` lie right before the tail
  have hcutp : s.ptr.add n = v.N.add (24 + ((v.w.ei - (s.len.toNat - n) : Nat) : Int)) := by
    have hb' : s.ptr.block = v.N.block := by rw [hbp, hbN, hb]
    have ho : s.ptr.off + n = v.N.off + (24 + ((v.w.ei - (s.len.toNat - n) : Nat) : Int)) := by omega
    simp only [Ptr.add]; rw [hb', ho]
  have hjoin : ∀ r, (up (regionIn (s.ptr.add n) v.A' v.w.S v.w.K 1 tl) ⋆ v.tR v.w.ei v.w.tail) r →
      up (regionIn (v.N.add (24 + ((v.w.ei - (s.len.toNat - n) : Nat) : Int))) v.w.A v.w.S v.w.K 1
        (tl ++ v.w.tail)) r := by
    intro r hr
    obtain ⟨⟨h₁, h₂, hd₁, he, x1, x2⟩, hk, hg⟩ := sep_up hr
    refine ⟨?_, hk, hg⟩
    rw [he, ← hcutp]
    refine regionIn_join (a' := 1) ⟨h₁, h₂, hd₁, rfl, ?_, ?_⟩
    · rw [hA] at x1; exact x1
    · have : (s.ptr.add n).add tl.size = v.N.add (24 + (v.w.ei : Int)) := by
        rw [hcutp]; simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega
      rw [this]; exact x2
  have h := of_eq (Q := (up (regionIn (s.ptr.add n) v.A' v.w.S v.w.K 1 tl) ⋆ v.tR v.w.ei v.w.tail) ⋆
    (gauthP γ e (v.w.M.set v.i (some (s.ptr, n, v.q, v.A', v.K'))) CI.tag ⋆
      (gfrag γ e v.i (s.ptr, n, v.q, v.A', v.K') ⋆ (pshare s.ptr v.q' (s.ptr.off.toNat + n) (some (γ, e)) ⋆
        Rcpts γ e (v.w.M.set v.i (some (s.ptr, n, v.q, v.A', v.K'))))) ⋆
      (Pool CI.tag v.w.pn v.w.pf ⋆ apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei - (s.len.toNat - n))) ⋆
        v.uW ctx ⋆ v.nR ⋆ v.cR CI ctx ⋆ JunkAt v.w.jh ⋆ v.F CI ctx ⋆ v.cl CI γ e (v.w.ei - (s.len.toNat - n)))))
    (by ac_rfl) h
  have h := sep_mono_left (Q := up (regionIn (v.N.add (24 + ((v.w.ei - (s.len.toNat - n) : Nat) : Int)))
    v.w.A v.w.S v.w.K 1 (tl ++ v.w.tail))) hjoin h
  -- the released bytes are the tail's now
  have hpN : s.ptr.block = v.N.block := by rw [hbp, hbN, hb]
  have hcov : OV.Cov
      { v.w with M := v.w.M.set v.i (some (s.ptr, n, v.q, v.A', v.K')),
                 ei := v.w.ei - (s.len.toNat - n), tail := tl ++ v.w.tail, jh := v.w.jh } :=
    OV.Cov.same hw.2.2.2.2.2 rfl (OV.avail_shrink (n' := n) hMi (fun j hj => GMap.set_ne _ _ hj)
      (fun _ _ hb1 h1 h2 => GrantHas.set hb1 h1 h2)
      (fun _ h => h)
      (fun b x hb1 h1 h2 => OV.avail_tail hfirst (by rw [← hpN]; exact hb1) (by dsimp only; omega)
        (by dsimp only; omega))
      fun b x h => by
        obtain ⟨hb1, h1, h2⟩ := h.of_first hfirst
        exact OV.avail_tail hfirst hb1 (by dsimp only; omega) h2)
  refine rpost_true0 (facts_repoint (n' := n) (ei := v.w.ei - (s.len.toNat - n)) (tail := tl ++ v.w.tail) hw hMi
    (GrantOk.len (hw.2.2.1 _ _ hMi)) ?_ hcov) hle (i := v.i) (of_eq ?_ h)
  · simp only [OV.FirstFacts, hfirst]
    exact ⟨hnf, by omega, by simp only [Array.size_append, htail]; omega⟩
  · simp only [OV.body, FirstPart, hfirst, Header, FV.uW, FV.nR, FV.cR, FV.F, FV.nS, FV.cl, OV.cls,
      FirstCl]
    ac_rfl

/-- `resize` of the first node's last allocation into the tail (`len < n`, room in the tail):
`end_index` moves forward; the client gets the first `n - len` bytes of the tail (with the node's
labels, which are the grant's: `last_labels`); the part of the share the client gives is re-lent at
the new end (`grow_ghost`); the grant is re-pointed. -/
theorem resize_grow_upd {v : FV} {wv : BitVec 64} (hv : v.Facts ctx s)
    (hfirst : v.w.first = some v.N) (hnf : NodeFacts v.N v.w.A v.w.sz) (hei : 24 + v.w.ei ≤ v.w.sz)
    (htail : v.w.tail.size = v.w.sz - 24 - v.w.ei) (hb : v.bp = v.bN) (hA : v.A' = v.w.A)
    (hK : v.K'.norm = v.w.K.norm) (hoff : s.ptr.off.toNat + s.len.toNat = v.N.off.toNat + 24 + v.w.ei)
    {k n : Nat} {tl : Array Byte} (hq : v.q'.val ≤ v.q.val) (hlt : s.len.toNat < n)
    (hfit : n - s.len.toNat ≤ v.w.sz - 24 - v.w.ei)
    (hw : wv = BitVec.ofNat 64 (v.w.ei + (n - s.len.toNat))) :
    EUpd (apts (v.N.add 8) wv ⋆ (v.uW ctx ⋆ v.R0 CI γ e ctx s (relB CI γ e ctx s n tl)))
      ((inv CI γ e ctx).rresizePost s.ptr k s.len.toNat n v.A' v.S' v.K' v.q v.q' tl true) := by
  subst hw
  obtain ⟨hw, -, -, hbN, hbp, -, -, -, hp0, hMi⟩ := hv
  have h0 := hnf.off0
  have hpN : s.ptr.block = v.N.block := by rw [hbp, hbN, hb]
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e v.w.M CI.tag ⋆
      (gfrag γ e v.i (s.ptr, s.len.toNat, v.q, v.A', v.K') ⋆
      (pshare s.ptr v.q' (s.ptr.off.toNat + s.len.toNat) (some (γ, e)) ⋆ (Rcpts γ e v.w.M ⋆
        pshare v.N v.w.qh (v.N.off.toNat + v.w.sz) CI.tag)))) ⋆
      (Pool CI.tag v.w.pn v.w.pf ⋆ apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei + (n - s.len.toNat))) ⋆
        v.uW ctx ⋆ v.nR ⋆ v.cR CI ctx ⋆ v.tR v.w.ei v.w.tail ⋆ JunkAt v.w.jh ⋆ apts v.N (BitVec.ofNat 64 v.w.sz) ⋆
        CI.tok v.N v.w.sz 3 v.w.A v.w.S v.w.K v.w.qn ⋆ aptsE (ctx.add 24) v.w.fl ⋆ CI.own ⋆ vtR CI.vtp CI.fns.toList ⋆
        UsedRest CI v.w.rest v.w.nxt ⋆ FreeList CI v.w.fl ⋆ pclaim s.ptr (s.ptr.off.toNat + s.len.toNat) (s.ptr.off.toNat + n) (some (γ, e)) ⋆
        v.cl CI γ e (v.w.ei + (n - s.len.toNat))))
    fun _ h => ?_) ?_
  · -- the new bytes' claim comes off the front of the tail's (`tailCl_join`)
    simp only [FV.R0, FV.xs, FV.F, FV.nS, FV.gA, FV.gT, relB, FAllocInv.relBytes,
      if_neg (show ¬ n < s.len.toNat by omega), Full.emp_sep_eq, FV.cl] at h
    exact of_eq (by
      simp only [FV.cl]
      rw [← tailCl_join (p := s.ptr) (lo := s.ptr.off.toNat + s.len.toNat) (hi := s.ptr.off.toNat + n)
        (ei' := v.w.ei) (ei := v.w.ei + (n - s.len.toNat)) hpN (by omega) (by omega) (by omega) (by omega)]
      ac_rfl) h
  refine EUpd.trans (EUpd.frame (grow_ghost (n' := n) (kN := v.N.off.toNat + v.w.sz) (K' := v.w.K)
    hq hpN (by omega))) ?_
  refine EUpd.of_imp fun r h => ?_
  -- the client gets the first `n - len` bytes of the tail
  have hend : v.N.add (24 + (v.w.ei : Int)) = s.ptr.add s.len.toNat := by
    have ho : s.ptr.off + s.len.toNat = v.N.off + (24 + (v.w.ei : Int)) := by omega
    simp only [Ptr.add]; rw [hpN, ho]
  have hnt : (v.N.add (24 + (v.w.ei : Int))).add ((n - s.len.toNat : Nat) : Int) =
      v.N.add (24 + ((v.w.ei + (n - s.len.toNat) : Nat) : Int)) := by
    simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega
  have h := of_eq (Q := v.tR v.w.ei v.w.tail ⋆ (gauthP γ e (v.w.M.set v.i (some (s.ptr, n, v.q, v.A', v.w.K))) CI.tag ⋆
      (gfrag γ e v.i (s.ptr, n, v.q, v.A', v.w.K) ⋆ (pshare s.ptr v.q' (s.ptr.off.toNat + n) (some (γ, e)) ⋆
        (Rcpts γ e (v.w.M.set v.i (some (s.ptr, n, v.q, v.A', v.w.K))) ⋆
          pshare v.N v.w.qh (v.N.off.toNat + v.w.sz) CI.tag))) ⋆
      (Pool CI.tag v.w.pn v.w.pf ⋆ apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei + (n - s.len.toNat))) ⋆
        v.uW ctx ⋆ v.nR ⋆ v.cR CI ctx ⋆ JunkAt v.w.jh ⋆ apts v.N (BitVec.ofNat 64 v.w.sz) ⋆
        CI.tok v.N v.w.sz 3 v.w.A v.w.S v.w.K v.w.qn ⋆ aptsE (ctx.add 24) v.w.fl ⋆ CI.own ⋆ vtR CI.vtp CI.fns.toList ⋆
        UsedRest CI v.w.rest v.w.nxt ⋆ FreeList CI v.w.fl ⋆ pclaim s.ptr (s.ptr.off.toNat + s.len.toNat) (s.ptr.off.toNat + n) (some (γ, e)) ⋆
        v.cl CI γ e (v.w.ei + (n - s.len.toNat))))) (by ac_rfl) h
  have h := sep_mono_left (Q := up (regionIn (v.N.add (24 + (v.w.ei : Int))) v.w.A v.w.S v.w.K 1
      (v.w.tail.extract 0 (n - s.len.toNat))) ⋆ up (regionIn ((v.N.add (24 + (v.w.ei : Int))).add
        ((n - s.len.toNat : Nat) : Int)) v.w.A v.w.S v.w.K 1
        (v.w.tail.extract (n - s.len.toNat) v.w.tail.size)))
    (fun _ x => up_region_split (n := n - s.len.toNat) (by omega) x) h
  rw [hnt, hend] at h
  have hsz : (v.w.tail.extract 0 (n - s.len.toNat)).size = n - s.len.toNat := by simp; omega
  -- the tail's first `n - len` bytes are the grant's now
  have hcov : OV.Cov
      { v.w with M := v.w.M.set v.i (some (s.ptr, n, v.q, v.A', v.w.K)),
                 ei := v.w.ei + (n - s.len.toNat), tail := v.w.tail.extract (n - s.len.toNat) v.w.tail.size,
                 jh := v.w.jh } :=
    OV.Cov.same hw.2.2.2.2.2 rfl (OV.avail_shrink (n' := n) hMi (fun j hj => GMap.set_ne _ _ hj)
      (fun _ _ hb1 h1 h2 => GrantHas.set hb1 h1 h2)
      (fun _ h => h) (fun _ _ _ h1 h2 => by omega)
      fun b x h => by
        obtain ⟨hb1, h1, h2⟩ := h.of_first hfirst
        by_cases hx : x < s.ptr.off.toNat + n
        · exact Or.inr (Or.inl ⟨v.i, GrantHas.set (by rw [hpN]; exact hb1) (by omega) hx⟩)
        · exact OV.avail_tail hfirst hb1 (by dsimp only; omega) h2)
  refine rpost_true (facts_repoint (n' := n) (K' := v.w.K) (ei := v.w.ei + (n - s.len.toNat))
    (tail := v.w.tail.extract (n - s.len.toNat) v.w.tail.size) hw hMi
    ⟨hp0, v.w.node v.N, by simp [OV.nodes, hfirst], hpN, hA, rfl⟩ ?_ hcov) hK.symm (S' := v.w.S) (i := v.i)
    (X := up (regionIn (s.ptr.add s.len.toNat) v.w.A v.w.S v.w.K 1 (v.w.tail.extract 0 (n - s.len.toNat))) ⋆
      pclaim s.ptr (s.ptr.off.toNat + s.len.toNat) (s.ptr.off.toNat + n) (some (γ, e)))
    (fun r hr => ?_) (of_eq ?_ h)
  · simp only [OV.FirstFacts, hfirst]
    exact ⟨hnf, by omega, by simp only [Array.size_extract, htail]; omega⟩
  · simp only [FAllocInv.newBytes, if_pos hlt, inv_tag]
    exact ⟨_, sep_lift.mpr ⟨hsz, by rw [hA]; exact hr⟩⟩
  · simp only [OV.body, FirstPart, hfirst, Header, FV.uW, FV.nR, FV.cR, FV.cl, OV.cls, FirstCl]
    ac_rfl

end Ends

/-! ## The ends of `alloc`

A successful `alloc` carves the grant out of the first node's tail (the padding before it leaks to
junk), lends half of the node's kept share at the grant's end against a receipt (`EUpd.lendT`),
and issues the grant under the fresh id `mN` (`Upd.issue`); the accounting moves half of `qh` to
the grants on the node's block. A new node (from the child or the free list) becomes the first
node first (`push_node`). -/

/-- The arena's resources on a first node `N`, without the node's `end_index` word. -/
def OV.bodyE (CI : Child) (γ e : Nat) (ctx : Ptr) (w : OV) (N : Ptr) : FAssn :=
  up (regionIn ctx w.Ac w.Sc w.Kc 8 CI.bytes) ⋆ aptsE (ctx.add 16) (some N) ⋆ aptsE (ctx.add 24) w.fl ⋆
    gauthP γ e w.M CI.tag ⋆ CI.own ⋆ vtR CI.vtp CI.fns.toList ⋆ JunkAt w.jh ⋆ Rcpts γ e w.M ⋆ Pool CI.tag w.pn w.pf ⋆
    apts N (BitVec.ofNat 64 w.sz) ⋆ up (regionIn (N.add 16) w.A w.S w.K 8 (Enc.encode w.nxt)) ⋆
    (CI.tok N w.sz 3 w.A w.S w.K w.qn ⋆ pshare N w.qh (N.off.toNat + w.sz) CI.tag) ⋆
    up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail) ⋆ UsedRest CI w.rest w.nxt ⋆ FreeList CI w.fl

theorem OV.body_split {CI : Child} {γ e : Nat} {ctx : Ptr} {w : OV} {N : Ptr}
    (hfirst : w.first = some N) :
    w.body CI γ e ctx = ((apts (N.add 8) (BitVec.ofNat 64 w.ei) ⋆ w.bodyE CI γ e ctx N) ⋆ w.cls CI γ e) := by
  simp only [OV.body, OV.bodyE, FirstPart, hfirst, Header]; ac_rfl

/-- `GrantOk` reads only the nodes' pointers and labels. -/
theorem GrantOk.mono {ns ns' : List NodeV}
    (h : ∀ nd ∈ ns, ∃ nd' ∈ ns', nd'.N = nd.N ∧ nd'.A = nd.A ∧ nd'.K.norm = nd.K.norm) {g : GRegion}
    (hg : GrantOk ns g) : GrantOk ns' g := by
  obtain ⟨p, n, q, A, K⟩ := g
  obtain ⟨h0, nd, hnd, hb, hA, hK⟩ := hg
  obtain ⟨nd', hnd', e1, e2, e3⟩ := h nd hnd
  exact ⟨h0, nd', hnd', by rw [e1]; exact hb, by rw [e2]; exact hA, by rw [e3]; exact hK⟩

/-- **A grant's ghost part**: half of the node's kept share `qh` (at the node's end `kN`) is lent at
the grant's end against a receipt, and the grant is issued under the unused id `i`. -/
theorem carve_ghost {γ e i : Nat} {M : GMap} {t : STag} {N : Ptr} {bN : BlockId} {qh : Frac}
    {kN : Nat} {p : Ptr} {n A : Nat} {K : BlockKind} (hi : M i = none) (hN : N.block = some bN)
    (hp : p.block = some bN) (hk : p.off.toNat + n ≤ kN) :
    EUpd (gauthP γ e M t ⋆ (pshare N qh kN t ⋆ Rcpts γ e M))
      (gauthP γ e (M.set i (some (p, n, qh.half, A, K))) t ⋆ (gfrag γ e i (p, n, qh.half, A, K) ⋆
        (pshare p qh.half (p.off.toNat + n) (some (γ, e)) ⋆
          (pshare N qh.half kN t ⋆ Rcpts γ e (M.set i (some (p, n, qh.half, A, K))))))) := by
  refine EUpd.trans (EUpd.of_imp (P' := gauthP γ e M t ⋆ (bshare bN qh kN t ⋆ Rcpts γ e M))
    fun _ h => sep_mono_right (fun _ x => sep_mono_left (Q := bshare bN qh kN t)
      (fun _ y => (pshare_iff hN).mp y) x) h) ?_
  refine EUpd.withFact (φ := 0 < qh.val) (fun _ r _ _ h _ => ?_) fun hq => ?_
  · obtain ⟨_, _, -, -, -, _, _, -, -, h1, -⟩ := h
    exact h1.1
  have hh := Frac.half_pos hq
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ bshare bN qh.half kN t) ⋆
      (bshare bN qh.half kN t ⋆ Rcpts γ e M)) fun r h => ?_) ?_
  · rw [← Frac.half_add_half qh] at h
    have h := sep_mono_right (R := (bshare bN qh.half kN t ⋆ bshare bN qh.half kN t) ⋆ Rcpts γ e M)
      (fun _ x => sep_mono_left (Q := bshare bN qh.half kN t ⋆ bshare bN qh.half kN t)
      (fun _ y => (bshare_split hh hh).mp y) x) h
    exact of_eq (by ac_rfl) h
  refine EUpd.trans (EUpd.frame (EUpd.lendT hk)) ?_
  refine EUpd.trans (EUpd.of_imp (P' := gauthP γ e M t ⋆ ((bshare bN qh.half (p.off.toNat + n) (some (γ, e)) ⋆
      brcpt bN qh.half kN γ e) ⋆ (bshare bN qh.half kN t ⋆ Rcpts γ e M))) fun _ h => sep_assoc h) ?_
  refine EUpd.trans (EUpd.frame (EUpd.of_upd (Upd.issue (p, n, qh.half, A, K) hi))) ?_
  refine EUpd.of_imp fun r h => ?_
  have h := of_eq (Q := brcpt bN qh.half kN γ e ⋆ (Rcpts γ e M ⋆
      ((gauthP γ e (M.set i (some (p, n, qh.half, A, K))) t ⋆ gfrag γ e i (p, n, qh.half, A, K)) ⋆
        (bshare bN qh.half (p.off.toNat + n) (some (γ, e)) ⋆ bshare bN qh.half kN t)))) (by ac_rfl) h
  have h := sep_mono_left (Q := rcptOf γ e (some (p, n, qh.half, A, K)))
    (fun _ z => ⟨bN, kN, sep_lift.mpr ⟨hp, z⟩⟩) h
  have h := sep_mono_left (Q := Rcpts γ e (M.set i (some (p, n, qh.half, A, K))))
    (fun _ z => rcpts_put hi z) (sep_assoc' h)
  have h := sep_mono_right (R := (gauthP γ e (M.set i (some (p, n, qh.half, A, K))) t ⋆
      gfrag γ e i (p, n, qh.half, A, K)) ⋆ (pshare p qh.half (p.off.toNat + n) (some (γ, e)) ⋆
        pshare N qh.half kN t))
    (fun _ x => sep_mono_right (R := pshare p qh.half (p.off.toNat + n) (some (γ, e)) ⋆
      pshare N qh.half kN t) (fun _ y => sep_mono (P' := pshare p qh.half (p.off.toNat + n) (some (γ, e)))
      (Q' := pshare N qh.half kN t) (fun _ z => (pshare_iff hp).mpr z) (fun _ z => (pshare_iff hN).mpr z) y) x) h
  exact of_eq (by ac_rfl) h

/-- A region with another alignment its address satisfies. -/
theorem up_realign {p : Ptr} {A S : Nat} {K : BlockKind} {a a' : Nat} {bs : Array Byte} {r : Res}
    (ha : (A + p.off.toNat) % a' = 0) (h : up (regionIn p A S K a bs) r) : up (regionIn p A S K a' bs) r :=
  let ⟨⟨_, hK, hb⟩, hk, hg⟩ := h; ⟨⟨ha, hK, hb⟩, hk, hg⟩

/-- The arena's variables after a grant of `n` bytes at index `ai` of the first node `N` (the
tail after it: `t2`): `carve_ghost`'s ledger and share, `end_index` at `ai + n`. -/
def OV.carve (w : OV) (N : Ptr) (n ai : Nat) (t2 : Array Byte) (jh : Heap) : OV :=
  { w with M := w.M.set w.mN (some (N.add (24 + ai), n, w.qh.half, w.A, w.K)), mN := w.mN + 1,
           ei := ai + n, tail := t2, qh := w.qh.half, jh := jh }

/-- `ndLent` after the first node's kept share changes from `qh` to `q'`. -/
theorem ndLent_qh {w : OV} {N : Ptr} (hfirst : w.first = some N) (q' : Frac) (b : BlockId) :
    ndLent b ({ w with qh := q' } : OV).nodes =
      ndLent b w.nodes + (if N.block = some b then w.qh.val - q'.val else 0) := by
  simp only [OV.nodes, hfirst, ndLent, OV.node]
  split <;> grind

/-- **`alloc` from the first node's tail**: the grant of `n` bytes at index `ai` (from `end_index`
on, alignment `2 ^ k`) with `end_index` moved to `ai + n` (the code's `cmpxchg`). The padding
leaks to junk, half the node's kept share is lent to the grant (`carve_ghost`), the grant gets
the fresh id `mN`. -/
theorem alloc_carve_upd {CI : Child} {γ e : Nat} {ctx : Ptr} {w : OV} {N : Ptr} {bN : BlockId}
    (hw : w.Facts) (hfirst : w.first = some N) (hbN : N.block = some bN) {n k ai : Nat}
    (hn : 0 < n) (hlo : w.ei ≤ ai) (hhi : 24 + ai + n ≤ w.sz)
    (hal : (w.A + N.off.toNat + 24 + ai) % 2 ^ k = 0) :
    EUpd ((apts (N.add 8) (BitVec.ofNat 64 (ai + n)) ⋆ w.bodyE CI γ e ctx N) ⋆ w.cls CI γ e)
      ((inv CI γ e ctx).allocPost n k (some (N.add (24 + ai)))) := by
  obtain ⟨hfin, hff, hgr, hacct, hqq, hcv⟩ := hw
  have hff' := hff
  simp only [OV.FirstFacts, hfirst] at hff'
  obtain ⟨hnf, hei, htail⟩ := hff'
  have h0 := hnf.off0
  have hp0 : (N.add (24 + ai)).off.toNat = N.off.toNat + 24 + ai := by simp only [Ptr.add]; omega
  have hpb : (N.add (24 + ai)).block = some bN := by simpa [Ptr.add] using hbN
  -- the tail: padding, the grant's bytes, the rest
  let t1 := w.tail.extract (ai - w.ei) w.tail.size
  let bs := t1.extract 0 n
  let t2 := t1.extract n t1.size
  have ht1 : t1.size = w.sz - 24 - ai := by simp only [t1, Array.size_extract]; omega
  have hbs : bs.size = n := by simp only [bs, Array.size_extract]; omega
  have ht2 : t2.size = w.sz - 24 - (ai + n) := by simp only [t2, Array.size_extract]; omega
  have hpe1 : (N.add (24 + w.ei)).add ((ai - w.ei : Nat) : Int) = N.add (24 + ai) := by
    simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega
  have hpe2 : (N.add (24 + ai)).add (n : Int) = N.add (24 + ((ai + n : Nat) : Int)) := by
    simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega
  have htsplit : ∀ r, up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail) r →
      (up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 (w.tail.extract 0 (ai - w.ei))) ⋆
        (up (regionIn (N.add (24 + ai)) w.A w.S w.K (2 ^ k) bs) ⋆
          up (regionIn (N.add (24 + ((ai + n : Nat) : Int))) w.A w.S w.K 1 t2))) r := fun r hr => by
    have h1 := up_region_split (n := ai - w.ei) (by omega) hr
    rw [hpe1] at h1
    have h1 := sep_mono_right (R := up (regionIn (N.add (24 + ai)) w.A w.S w.K 1 (t1.extract 0 n)) ⋆
      up (regionIn ((N.add (24 + ai)).add (n : Int)) w.A w.S w.K 1 (t1.extract n t1.size)))
      (fun _ x => up_region_split (n := n) (by omega) x) h1
    rw [hpe2] at h1
    have hal' : (w.A + (N.add (24 + ai)).off.toNat) % 2 ^ k = 0 := by
      rw [hp0, ← Nat.add_assoc, ← Nat.add_assoc]; exact hal
    exact sep_mono_right (fun _ x => sep_mono_left (fun _ y => up_realign hal' y) x) h1
  let R : Heap → FAssn := fun jh => apts (N.add 8) (BitVec.ofNat 64 (ai + n)) ⋆
    up (regionIn ctx w.Ac w.Sc w.Kc 8 CI.bytes) ⋆
    aptsE (ctx.add 16) (some N) ⋆ aptsE (ctx.add 24) w.fl ⋆ CI.own ⋆ vtR CI.vtp CI.fns.toList ⋆ JunkAt jh ⋆
    Pool CI.tag w.pn w.pf ⋆
    apts N (BitVec.ofNat 64 w.sz) ⋆ up (regionIn (N.add 16) w.A w.S w.K 8 (Enc.encode w.nxt)) ⋆
    CI.tok N w.sz 3 w.A w.S w.K w.qn ⋆ up (regionIn (N.add (24 + ((ai + n : Nat) : Int))) w.A w.S w.K 1 t2) ⋆
    UsedRest CI w.rest w.nxt ⋆ FreeList CI w.fl
  let G0 : FAssn := gauthP γ e w.M CI.tag ⋆ (pshare N w.qh (N.off.toNat + w.sz) CI.tag ⋆ Rcpts γ e w.M)
  -- the padding joins the junk
  have himp : ∀ r, (apts (N.add 8) (BitVec.ofNat 64 (ai + n)) ⋆ w.bodyE CI γ e ctx N) r →
      (FAssn.ex fun jh => ⟪JunkGrew N (24 + w.ei) (24 + ai) w.jh jh⟫ ⋆
        (G0 ⋆ (up (regionIn (N.add (24 + ai)) w.A w.S w.K (2 ^ k) bs) ⋆ R jh))) r := by
    intro r h
    simp only [OV.bodyE] at h
    have h := of_eq (Q := up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail) ⋆
      (pshare N w.qh (N.off.toNat + w.sz) CI.tag ⋆ (JunkAt w.jh ⋆ (apts (N.add 8) (BitVec.ofNat 64 (ai + n)) ⋆
      up (regionIn ctx w.Ac w.Sc w.Kc 8 CI.bytes) ⋆ aptsE (ctx.add 16) (some N) ⋆ aptsE (ctx.add 24) w.fl ⋆
      gauthP γ e w.M CI.tag ⋆ CI.own ⋆ vtR CI.vtp CI.fns.toList ⋆ Rcpts γ e w.M ⋆ Pool CI.tag w.pn w.pf ⋆
      apts N (BitVec.ofNat 64 w.sz) ⋆ up (regionIn (N.add 16) w.A w.S w.K 8 (Enc.encode w.nxt)) ⋆
      CI.tok N w.sz 3 w.A w.S w.K w.qn ⋆ UsedRest CI w.rest w.nxt ⋆ FreeList CI w.fl)))) (by ac_rfl) h
    have h := sep_mono_left (fun r x => htsplit r x) h
    have h := of_eq (Q := (up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 (w.tail.extract 0 (ai - w.ei))) ⋆
      JunkAt w.jh) ⋆ (pshare N w.qh (N.off.toNat + w.sz) CI.tag ⋆ (up (regionIn (N.add (24 + ai)) w.A w.S w.K (2 ^ k) bs) ⋆
      up (regionIn (N.add (24 + ((ai + n : Nat) : Int))) w.A w.S w.K 1 t2) ⋆ (apts (N.add 8) (BitVec.ofNat 64 (ai + n)) ⋆
      up (regionIn ctx w.Ac w.Sc w.Kc 8 CI.bytes) ⋆ aptsE (ctx.add 16) (some N) ⋆ aptsE (ctx.add 24) w.fl ⋆
      gauthP γ e w.M CI.tag ⋆ CI.own ⋆ vtR CI.vtp CI.fns.toList ⋆ Rcpts γ e w.M ⋆ Pool CI.tag w.pn w.pf ⋆
      apts N (BitVec.ofNat 64 w.sz) ⋆ up (regionIn (N.add 16) w.A w.S w.K 8 (Enc.encode w.nxt)) ⋆
      CI.tok N w.sz 3 w.A w.S w.K w.qn ⋆ UsedRest CI w.rest w.nxt ⋆ FreeList CI w.fl)))) (by ac_rfl) h
    obtain ⟨jh, hg, h⟩ := junk_grew (p := N) (q := N.add (24 + w.ei)) (lo := 24 + w.ei) h0 rfl
      (by simp [Ptr.add]) h
    have hsz : 24 + w.ei + (w.tail.extract 0 (ai - w.ei)).size = 24 + ai := by simp; omega
    rw [hsz] at hg
    exact ⟨jh, sep_lift.mpr ⟨hg, of_eq (by simp only [R, G0]; ac_rfl) h⟩⟩
  -- the claims: the padding's is forgotten, the grant's comes off the front of the tail's
  -- (`tailCl_join`)
  let CL : FAssn := NodeCl CI γ e N w.sz ⋆ TailCl γ e N (ai + n) w.sz ⋆ RestCl CI γ e w.rest
  let GC : FAssn := pclaim (N.add (24 + ai)) (N.add (24 + ai)).off.toNat ((N.add (24 + ai)).off.toNat + n)
    (some (γ, e))
  refine EUpd.trans (EUpd.of_imp (P' := ((apts (N.add 8) (BitVec.ofNat 64 (ai + n)) ⋆ w.bodyE CI γ e ctx N) ⋆
      (CL ⋆ GC)) ⋆ pclaim N (N.off.toNat + 24 + w.ei) (N.off.toNat + 24 + ai) (some (γ, e)))
    fun _ h => of_eq (by
      simp only [OV.cls, FirstCl, hfirst, CL, GC]
      rw [← tailCl_join (p := N) (lo := N.off.toNat + 24 + w.ei) (hi := N.off.toNat + 24 + ai) (ei' := w.ei)
          (ei := ai) rfl rfl rfl hlo (by omega),
        ← tailCl_join (p := N.add (24 + ai)) (lo := (N.add (24 + ai)).off.toNat)
          (hi := (N.add (24 + ai)).off.toNat + n) (ei' := ai) (ei := ai + n) (by simp [Ptr.add]) hp0
          (by omega) (by omega) (by omega)]
      ac_rfl) h) ?_
  refine EUpd.trans (EUpd.drop fun _ h => pclaim_ghost h) ?_
  refine EUpd.trans (EUpd.of_imp (P' := FAssn.ex fun jh => ⟪JunkGrew N (24 + w.ei) (24 + ai) w.jh jh⟫ ⋆
      (G0 ⋆ ((up (regionIn (N.add (24 + ai)) w.A w.S w.K (2 ^ k) bs) ⋆ GC) ⋆ (R jh ⋆ CL))))
    fun _ h => by
      obtain ⟨jh, h⟩ := sep_ex.mp (sep_mono_left himp h)
      obtain ⟨hg, h⟩ := sep_lift.mp (sep_assoc h)
      exact ⟨jh, sep_lift.mpr ⟨hg, of_eq (by ac_rfl) h⟩⟩) ?_
  refine EUpd.exAll fun jh => EUpd.lift fun hg => ?_
  refine EUpd.trans (EUpd.frame (carve_ghost (i := w.mN) (A := w.A) (K := w.K) (qh := w.qh)
    (kN := N.off.toNat + w.sz) (n := n) (t := CI.tag) (hfin _ (Nat.le_refl _)) hbN hpb
    (by have := hp0; omega))) ?_
  refine EUpd.of_imp fun r h => ?_
  -- the coverage: the padding is junk, the grant's bytes are the grant's, the rest is the tail
  have hcov : (OV.carve w N n ai t2 jh).Cov := by
    refine OV.Cov.step hcv (OV.avail_step (i := w.mN) hg.1 (fun j hj => GMap.set_ne _ _ hj)
      (fun b x h => by rw [hfin _ (Nat.le_refl _)] at h; exact h.elim) fun b x h => ?_)
      fun nd hnd b x hx => Or.inl ?_
    · obtain ⟨hb1, h1, h2⟩ := h.of_first hfirst
      by_cases hx1 : x < N.off.toNat + 24 + ai
      · exact Or.inl (hg.2 b x hb1 (by omega) (by omega))
      · by_cases hx2 : x < N.off.toNat + 24 + ai + n
        · exact Or.inr (Or.inl ⟨w.mN, GrantHas.set (by simpa [Ptr.add] using hb1) (by omega)
            (by omega)⟩)
        · exact OV.avail_tail hfirst hb1 (by dsimp only [OV.carve]; omega) h2
    · simp only [OV.carve, OV.nodes, hfirst, List.mem_cons] at hnd
      simp only [OV.nodes, hfirst, List.mem_cons]
      rcases hnd with rfl | hnd
      · exact ⟨w.node N, Or.inl rfl, hx⟩
      · exact ⟨nd, Or.inr hnd, hx⟩
  -- the new state
  have hwf : OV.Facts (OV.carve w N n ai t2 jh) := by
    have hmem : ∀ nd ∈ w.nodes, ∃ nd' ∈ ({ w with qh := w.qh.half } : OV).nodes,
        nd'.N = nd.N ∧ nd'.A = nd.A ∧ nd'.K.norm = nd.K.norm := fun nd hnd => by
      simp only [OV.nodes, hfirst, List.mem_cons] at hnd ⊢
      rcases hnd with rfl | hnd
      · exact ⟨_, Or.inl rfl, rfl, rfl, rfl⟩
      · exact ⟨nd, Or.inr hnd, rfl, rfl, rfl⟩
    unfold OV.carve at hcov ⊢
    refine ⟨fun i hi => ?_, ?_, fun j g hj => ?_, fun b => ?_, fun nd hnd => ?_, hcov⟩
    · dsimp only at hi ⊢
      rw [GMap.set_ne _ _ (by omega)]; exact hfin i (by omega)
    · simp only [OV.FirstFacts, hfirst]; exact ⟨hnf, by omega, ht2⟩
    · dsimp only at hj
      by_cases hj' : j = w.mN
      · subst hj'
        simp only [GMap.set_same, Option.some.injEq] at hj; subst hj
        exact ⟨by simp only [Ptr.add]; omega, ({ w with qh := w.qh.half } : OV).node N,
          by simp [OV.nodes, hfirst, OV.node], rfl, rfl, rfl⟩
      · exact GrantOk.mono hmem (hgr j g (by simpa [GMap.set_ne _ _ hj'] using hj))
    · show ndLent b ({ w with qh := w.qh.half } : OV).nodes = poolOn b w.pn w.pf +
        esum (fun i => grantOn b (w.M.set w.mN (some (N.add (24 + ai), n, w.qh.half, w.A, w.K)) i)) (w.mN + 1)
      rw [ndLent_qh hfirst, hacct b]
      rw [esum]
      rw [esum_congr (g := fun i => grantOn b (w.M i)) fun j hj => by
        rw [GMap.set_ne _ _ (Nat.ne_of_lt hj)], GMap.set_same]
      simp only [grantsOn, grantOn, hpb, hbN]
      split <;> (try simp only [Frac.half]) <;> grind
    · simp [OV.nodes, hfirst] at hnd
      rcases hnd with rfl | hnd
      · have := hqq (w.node N) (by simp [OV.nodes, hfirst])
        simp only [OV.node, Frac.half] at this ⊢; have := w.qh.nonneg; grind
      · exact hqq nd (by simp [OV.nodes, hfirst, hnd])
  show ((inv CI γ e ctx).own ⋆ FAssn.ex fun bs => ⟪bs.size = n⟫ ⋆
    (inv CI γ e ctx).granted (N.add (24 + ai)) k bs) r
  refine own_of hwf (sep_mono_right (fun r hr => ⟨bs, sep_lift.mpr ⟨hbs, ⟨w.A, w.S, w.K, w.qh.half, by
    simp only [inv, hbs]; exact sep_mono_right (fun _ x => sep_mono_left (fun _ y => ⟨w.mN, y⟩) x) hr⟩⟩⟩)
    (Q := up (regionIn (N.add (24 + ai)) w.A w.S w.K (2 ^ k) bs) ⋆
      (gfrag γ e w.mN (N.add (24 + ai), n, w.qh.half, w.A, w.K) ⋆
        (pshare (N.add (24 + ai)) w.qh.half ((N.add (24 + ai)).off.toNat + n) (some (γ, e)) ⋆ GC))) ?_)
  rw [OV.body_split (w := OV.carve w N n ai t2 jh) hfirst]
  simp only [OV.bodyE, OV.carve, R, G0, OV.cls, FirstCl, hfirst, CL, GC] at h ⊢
  exact of_eq (by ac_rfl) h


/-- An empty region right after a region (e.g. a used node's empty buffer after its header). -/
theorem up_region_nil {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte} {r : Res}
    (h : up (regionIn p A S K a bs) r) :
    (up (regionIn p A S K a bs) ⋆ up (regionIn (p.add bs.size) A S K 1 #[])) r := by
  have := up_region_split (n := bs.size) (Nat.le_refl _) h
  simpa using this

/-- The arena's resources without the `used_list` word. -/
def OV.bodyU (CI : Child) (γ e : Nat) (ctx : Ptr) (w : OV) : FAssn :=
  up (regionIn ctx w.Ac w.Sc w.Kc 8 CI.bytes) ⋆ aptsE (ctx.add 24) w.fl ⋆
    gauthP γ e w.M CI.tag ⋆ CI.own ⋆ vtR CI.vtp CI.fns.toList ⋆ JunkAt w.jh ⋆ Rcpts γ e w.M ⋆ Pool CI.tag w.pn w.pf ⋆ FirstPart CI w ⋆
    UsedRest CI w.rest w.nxt ⋆ FreeList CI w.fl

theorem OV.body_used {CI : Child} {γ e : Nat} {ctx : Ptr} (w : OV) :
    w.body CI γ e ctx = ((aptsE (ctx.add 16) w.first ⋆ w.bodyU CI γ e ctx) ⋆ w.cls CI γ e) := by
  simp only [OV.body, OV.bodyU]; ac_rfl

/-- The arena's variables after the node `nd` (from the child or the free list; the arena keeps
its whole share) becomes the first node, with `end_index` `0` and its whole buffer `buf` as the
tail; the old first node joins the used nodes after it (its tail leaks to the junk, now `jh`). -/
def OV.push (w : OV) (nd : NodeV) (buf : Array Byte) (jh : Heap) : OV :=
  { w with first := some nd.N, nxt := w.first, A := nd.A, S := nd.S, K := nd.K, sz := nd.sz, ei := 0,
           tail := buf, qn := nd.qn, qh := nd.qh, rest := w.nodes, jh := jh }

/-- The junk `jh` after the first node's tail leaked to it. -/
def JunkTook (w : OV) (jh : Heap) : Prop :=
  (∀ l, w.jh l ≠ none → jh l ≠ none) ∧ ∀ b x, w.InTail b x → jh (b, x) ≠ none

theorem facts_push {w : OV} (hw : w.Facts) {nd : NodeV} (hnf : NodeFacts nd.N nd.A nd.sz)
    (hq : nd.qh = nd.qn) {buf : Array Byte} (hbuf : buf.size = nd.sz - 24) {jh : Heap}
    (hjh : JunkTook w jh) : (w.push nd buf jh).Facts := by
  obtain ⟨hfin, -, hgr, hacct, hqq, hcv⟩ := hw
  have hnodes : (w.push nd buf jh).nodes = nd :: w.nodes := rfl
  refine ⟨hfin, ⟨hnf, by simp only [OV.push]; have := hnf.hdr; omega, by simp only [OV.push]; omega⟩,
    fun i g hi => GrantOk.mono (fun x hx => ⟨x, by rw [hnodes]; exact List.mem_cons_of_mem _ hx,
      rfl, rfl, rfl⟩) (hgr i g hi), fun b => ?_, fun x hx => ?_, ?_⟩
  · rw [hnodes]; simp only [ndLent, hq]; rw [hacct b]; simp only [OV.push]; split <;> grind
  · rw [hnodes] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [hq]; exact Rat.le_refl
    · exact hqq x hx
  · -- the old tail is junk; the new node's buffer is the new tail
    refine OV.Cov.step hcv (OV.avail_step (i := 0) hjh.1 (fun _ _ => rfl)
      (fun b x h => Or.inr (Or.inl ⟨0, h⟩)) fun b x h => Or.inl (hjh.2 b x h)) fun nd' hnd b x hx => ?_
    rw [hnodes] at hnd
    rcases List.mem_cons.mp hnd with rfl | hnd
    · obtain ⟨hb, h1, h2⟩ := hx
      exact Or.inr (OV.avail_tail rfl hb (by dsimp only [OV.push]; omega) h2)
    · exact Or.inl ⟨nd', hnd, hx⟩

/-- A new first node, without claims (`push_node_upd`). -/
theorem push_node_body {CI : Child} {γ e : Nat} {ctx : Ptr} {w : OV} (hw : w.Facts) {nd : NodeV}
    (hnf : NodeFacts nd.N nd.A nd.sz) {buf : Array Byte} {ew : BitVec 64} :
    EUpd ((aptsE (ctx.add 16) (some nd.N) ⋆ (apts nd.N (BitVec.ofNat 64 nd.sz) ⋆ apts (nd.N.add 8) ew ⋆
        up (regionIn (nd.N.add 16) nd.A nd.S nd.K 8 (Enc.encode w.first)) ⋆
        up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf) ⋆
        (CI.tok nd.N nd.sz 3 nd.A nd.S nd.K nd.qn ⋆ pshare nd.N nd.qh (nd.N.off.toNat + nd.sz) CI.tag))) ⋆
        w.bodyU CI γ e ctx)
      (FAssn.ex fun jh => ⟪JunkTook w jh⟫ ⋆ (apts (nd.N.add 8) ew ⋆ (w.push nd buf jh).bodyE CI γ e ctx nd.N)) := by
  have hff := hw.2.1
  refine EUpd.of_imp fun r h => ?_
  -- the old first node (if any) joins the used nodes; its tail leaks to junk
  have hc : ∀ r, (FirstPart CI w ⋆ (UsedRest CI w.rest w.nxt ⋆ JunkAt w.jh)) r →
      ∃ jh, JunkTook w jh ∧ (UsedRest CI w.nodes w.first ⋆ JunkAt jh) r := fun r h => by
    cases hf : w.first with
    | none =>
      simp only [OV.FirstFacts, hf] at hff
      obtain ⟨-, hr, hn⟩ := hff
      simp only [FirstPart, hf, OV.nodes, UsedRest, hr, hn, Chain] at h ⊢
      refine ⟨w.jh, ⟨fun _ h => h, fun b x ⟨N, hN, _⟩ => ?_⟩, of_eq (emp_sep_eq _) h⟩
      rw [hf] at hN; cases hN
    | some N =>
      simp only [OV.FirstFacts, hf] at hff
      obtain ⟨hnfN, hei, htail⟩ := hff
      simp only [FirstPart, hf, OV.nodes, UsedRest, Chain, Header] at h ⊢
      have hN24 : (N.add 16).add ((Enc.encode w.nxt).size : Int) = N.add 24 := by
        rw [encode_nxt_size]; simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega
      have h := of_eq (Q := (up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail) ⋆ JunkAt w.jh) ⋆
        (up (regionIn (N.add 16) w.A w.S w.K 8 (Enc.encode w.nxt)) ⋆
          (apts N (BitVec.ofNat 64 w.sz) ⋆ apts (N.add 8) (BitVec.ofNat 64 w.ei) ⋆
            (CI.tok N w.sz 3 w.A w.S w.K w.qn ⋆ pshare N w.qh (N.off.toNat + w.sz) CI.tag) ⋆
            Chain CI false w.rest w.nxt))) (by ac_rfl) h
      obtain ⟨jh, hg, h⟩ := junk_grew (p := N) (q := N.add (24 + w.ei)) (lo := 24 + w.ei) hnfN.off0 rfl
        (by simp [Ptr.add]) h
      have hsz : 24 + w.ei + w.tail.size = w.sz := by omega
      rw [hsz] at hg
      refine ⟨jh, ⟨hg.1, fun b x ⟨N', hN', hb, h1, h2⟩ => ?_⟩, ?_⟩
      · rw [hf] at hN'; cases hN'
        exact hg.2 b x hb (by omega) (by omega)
      have h := of_eq (sep_left_comm_eq _ _ _) h
      have h := sep_mono_left (Q := up (regionIn (N.add 16) w.A w.S w.K 8 (Enc.encode w.nxt)) ⋆
        up (regionIn ((N.add 16).add ((Enc.encode w.nxt).size : Int)) w.A w.S w.K 1 #[]))
        (fun _ x => up_region_nil x) h
      rw [hN24] at h
      refine sep_mono_left (Q := FAssn.ex fun ei : BitVec 64 => FAssn.ex fun nxt : Option Ptr =>
        FAssn.ex fun buf : Array Byte => ⟪(w.node N).N = N ∧ NodeFacts (w.node N).N (w.node N).A
          (w.node N).sz ∧ buf.size = (if false = true then (w.node N).sz - 24 else 0)⟫ ⋆
          (Header CI (w.node N).N (w.node N).A (w.node N).S (w.node N).K (w.node N).sz ei nxt
            (w.node N).qn (w.node N).qh ⋆ up (regionIn ((w.node N).N.add 24) (w.node N).A (w.node N).S
              (w.node N).K 1 buf) ⋆ Chain CI false w.rest nxt))
        (fun _ x => ⟨BitVec.ofNat 64 w.ei, w.nxt, #[], sep_lift.mpr ⟨⟨rfl, hnfN, rfl⟩, by
          simp only [OV.node, Header]; exact of_eq (by ac_rfl) x⟩⟩) ?_
      exact of_eq (by ac_rfl) h
  simp only [OV.bodyU] at h
  have h := of_eq (Q := (FirstPart CI w ⋆ (UsedRest CI w.rest w.nxt ⋆ JunkAt w.jh)) ⋆
      (aptsE (ctx.add 16) (some nd.N) ⋆ (apts nd.N (BitVec.ofNat 64 nd.sz) ⋆ apts (nd.N.add 8) ew ⋆
        up (regionIn (nd.N.add 16) nd.A nd.S nd.K 8 (Enc.encode w.first)) ⋆
        up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf) ⋆
        (CI.tok nd.N nd.sz 3 nd.A nd.S nd.K nd.qn ⋆ pshare nd.N nd.qh (nd.N.off.toNat + nd.sz) CI.tag)) ⋆
      up (regionIn ctx w.Ac w.Sc w.Kc 8 CI.bytes) ⋆ aptsE (ctx.add 24) w.fl ⋆
      gauthP γ e w.M CI.tag ⋆ CI.own ⋆ vtR CI.vtp CI.fns.toList ⋆ Rcpts γ e w.M ⋆ Pool CI.tag w.pn w.pf ⋆ FreeList CI w.fl))
    (by ac_rfl) h
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := h
  obtain ⟨jh, hjh, h1⟩ := hc _ h1
  refine ⟨jh, sep_lift.mpr ⟨hjh, ?_⟩⟩
  have h : ((UsedRest CI w.nodes w.first ⋆ JunkAt jh) ⋆ _) _ := ⟨r₁, r₂, hd, rfl, h1, h2⟩
  simp only [OV.bodyE, OV.push]
  have e0 : nd.N.add (24 + ((0 : Nat) : Int)) = nd.N.add 24 := by simp
  rw [e0]
  exact of_eq (by simp only [UsedRest]; ac_rfl) h

/-- **The claims of a new first node**: the child's claim on the node splits at its header; the
buffer's part is lent as the arena's claim of epoch `e` (`EUpd.plendC`), all of it the new tail's;
the old first node's tail claim is forgotten, its other claims join the rest's. -/
theorem push_cls {CI : Child} {γ e : Nat} {M : GMap} {w : OV} (hw : w.Facts) {nd : NodeV}
    (hnf : NodeFacts nd.N nd.A nd.sz) {buf : Array Byte} {jh : Heap} :
    EUpd (gauthP γ e M CI.tag ⋆ (pclaim nd.N nd.N.off.toNat (nd.N.off.toNat + nd.sz) CI.tag ⋆ w.cls CI γ e))
      (gauthP γ e M CI.tag ⋆ (w.push nd buf jh).cls CI γ e) := by
  have hold : EUpd (w.cls CI γ e) (RestCl CI γ e w.nodes) := by
    have hff := hw.2.1
    cases hf : w.first with
    | none =>
      simp only [OV.FirstFacts, hf] at hff
      simp only [OV.cls, FirstCl, hf, OV.nodes, hff.2.1, RestCl]
      exact EUpd.of_imp fun _ h => of_eq (emp_sep_eq _) h
    | some N =>
      simp only [OV.cls, FirstCl, hf, OV.nodes, RestCl, OV.node]
      refine EUpd.trans (EUpd.of_imp (P' := (NodeCl CI γ e N w.sz ⋆ RestCl CI γ e w.rest) ⋆
        TailCl γ e N w.ei w.sz) fun _ h => of_eq (by ac_rfl) h) ?_
      exact EUpd.drop fun _ h => pclaim_ghost h
  have h24 := hnf.hdr
  refine EUpd.trans (EUpd.frameL (EUpd.frameL hold)) ?_
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M CI.tag ⋆
      pclaim nd.N (nd.N.off.toNat + 24) (nd.N.off.toNat + nd.sz) CI.tag) ⋆
      (pclaim nd.N nd.N.off.toNat (nd.N.off.toNat + 24) CI.tag ⋆ RestCl CI γ e w.nodes))
    fun _ h => of_eq (by rw [← pclaim_split (m := nd.N.off.toNat + 24) (by omega) (by omega)]; ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame EUpd.plendC) ?_
  refine EUpd.of_imp fun _ h => of_eq ?_ h
  simp only [OV.cls, FirstCl, OV.push, NodeCl, TailCl, Nat.add_zero]
  ac_rfl

/-- **A new first node** (`tryPushNode`): the node's header (`size`, `end_index` word `ew`, `next`
= the old first node), its buffer, the child's token, share and claim; the `used_list` word points
at it. The old first node and its tail join the used nodes after it (`push_node_body`); the
claims move as in `push_cls`. -/
theorem push_node_upd {CI : Child} {γ e : Nat} {ctx : Ptr} {w : OV} (hw : w.Facts) {nd : NodeV}
    (hnf : NodeFacts nd.N nd.A nd.sz) {buf : Array Byte} {ew : BitVec 64} :
    EUpd (((aptsE (ctx.add 16) (some nd.N) ⋆ (apts nd.N (BitVec.ofNat 64 nd.sz) ⋆ apts (nd.N.add 8) ew ⋆
        up (regionIn (nd.N.add 16) nd.A nd.S nd.K 8 (Enc.encode w.first)) ⋆
        up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf) ⋆
        (CI.tok nd.N nd.sz 3 nd.A nd.S nd.K nd.qn ⋆ pshare nd.N nd.qh (nd.N.off.toNat + nd.sz) CI.tag))) ⋆
        w.bodyU CI γ e ctx) ⋆
        (pclaim nd.N nd.N.off.toNat (nd.N.off.toNat + nd.sz) CI.tag ⋆ w.cls CI γ e))
      (FAssn.ex fun jh => ⟪JunkTook w jh⟫ ⋆
        ((apts (nd.N.add 8) ew ⋆ (w.push nd buf jh).bodyE CI γ e ctx nd.N) ⋆ (w.push nd buf jh).cls CI γ e)) := by
  let X : FAssn := aptsE (ctx.add 16) (some nd.N) ⋆ (apts nd.N (BitVec.ofNat 64 nd.sz) ⋆ apts (nd.N.add 8) ew ⋆
    up (regionIn (nd.N.add 16) nd.A nd.S nd.K 8 (Enc.encode w.first)) ⋆
    up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf) ⋆
    (CI.tok nd.N nd.sz 3 nd.A nd.S nd.K nd.qn ⋆ pshare nd.N nd.qh (nd.N.off.toNat + nd.sz) CI.tag)) ⋆
    up (regionIn ctx w.Ac w.Sc w.Kc 8 CI.bytes) ⋆ aptsE (ctx.add 24) w.fl ⋆ CI.own ⋆ vtR CI.vtp CI.fns.toList ⋆ JunkAt w.jh ⋆ Rcpts γ e w.M ⋆
    Pool CI.tag w.pn w.pf ⋆ FirstPart CI w ⋆ UsedRest CI w.rest w.nxt ⋆ FreeList CI w.fl
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e w.M CI.tag ⋆
      (pclaim nd.N nd.N.off.toNat (nd.N.off.toNat + nd.sz) CI.tag ⋆ w.cls CI γ e)) ⋆ X)
    fun _ h => of_eq (by simp only [OV.bodyU, X]; ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame (push_cls (buf := buf) (jh := w.jh) hw hnf)) ?_
  refine EUpd.trans (EUpd.of_imp (P' := ((aptsE (ctx.add 16) (some nd.N) ⋆ (apts nd.N (BitVec.ofNat 64 nd.sz) ⋆
        apts (nd.N.add 8) ew ⋆ up (regionIn (nd.N.add 16) nd.A nd.S nd.K 8 (Enc.encode w.first)) ⋆
        up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf) ⋆
        (CI.tok nd.N nd.sz 3 nd.A nd.S nd.K nd.qn ⋆ pshare nd.N nd.qh (nd.N.off.toNat + nd.sz) CI.tag))) ⋆
        w.bodyU CI γ e ctx) ⋆ (w.push nd buf w.jh).cls CI γ e)
    fun _ h => of_eq (by simp only [OV.bodyU, X]; ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame (push_node_body hw hnf)) (EUpd.of_imp fun _ h => ?_)
  -- the claims do not depend on the junk
  obtain ⟨jh, h⟩ := sep_ex.mp h
  obtain ⟨hjh, h⟩ := sep_lift.mp (sep_assoc h)
  exact ⟨jh, sep_lift.mpr ⟨hjh, h⟩⟩

/-- Two adjacent regions of one block with the same labels are one. -/
theorem up_region_join {p q : Ptr} {A S : Nat} {K : BlockKind} {a a' : Nat} {bs bs' : Array Byte}
    {r : Res} (hq : q = p.add bs.size)
    (h : (up (regionIn p A S K a bs) ⋆ up (regionIn q A S K a' bs')) r) :
    up (regionIn p A S K a (bs ++ bs')) r := by
  subst hq
  obtain ⟨⟨h₁, h₂, hd₁, he, x1, x2⟩, hk, hg⟩ := sep_up h
  exact ⟨by rw [he]; exact regionIn_join ⟨h₁, h₂, hd₁, rfl, x1, x2⟩, hk, hg⟩

/-- The arena's resources on a first node `N` without the node's words, regions, token and share. -/
def OV.restE (CI : Child) (γ e : Nat) (ctx : Ptr) (w : OV) (N : Ptr) : FAssn :=
  up (regionIn ctx w.Ac w.Sc w.Kc 8 CI.bytes) ⋆ aptsE (ctx.add 16) (some N) ⋆ aptsE (ctx.add 24) w.fl ⋆
    gauthP γ e w.M CI.tag ⋆ CI.own ⋆ vtR CI.vtp CI.fns.toList ⋆ JunkAt w.jh ⋆ Rcpts γ e w.M ⋆ Pool CI.tag w.pn w.pf ⋆
    UsedRest CI w.rest w.nxt ⋆ FreeList CI w.fl

theorem OV.bodyE_eq {CI : Child} {γ e : Nat} {ctx : Ptr} (w : OV) (N : Ptr) :
    w.bodyE CI γ e ctx N = ((apts N (BitVec.ofNat 64 w.sz) ⋆
      up (regionIn (N.add 16) w.A w.S w.K 8 (Enc.encode w.nxt)) ⋆
      (CI.tok N w.sz 3 w.A w.S w.K w.qn ⋆ pshare N w.qh (N.off.toNat + w.sz) CI.tag) ⋆
      up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail)) ⋆ w.restE CI γ e ctx N) := by
  simp only [OV.bodyE, OV.restE]; ac_rfl

/-- The arena's variables after the child grew the first node in place to `sz'` bytes (labels
`S'`, `K'`), the new bytes `t` appended to the tail. -/
def OV.grow (w : OV) (sz' S' : Nat) (K' : BlockKind) (t : Array Byte) : OV :=
  { w with sz := sz', S := S', K := K', tail := w.tail ++ t }

/-- The first node grown in place, without claims (`grow_node_upd`). -/
theorem grow_node_body {CI : Child} {γ e : Nat} {ctx : Ptr} {w : OV} (hw : w.Facts) {N : Ptr}
    (hfirst : w.first = some N) {sz' S' : Nat} {K' : BlockKind} (hK : K'.norm = w.K.norm)
    (hnf' : NodeFacts N w.A sz') (hlt : w.sz < sz') {t : Array Byte} (ht : t.size = sz' - w.sz) :
    EUpd ((apts N (BitVec.ofNat 64 sz') ⋆ up (regionIn (N.add 16) w.A w.S w.K 8 (Enc.encode w.nxt)) ⋆
        (CI.tok N sz' 3 w.A S' K' w.qn ⋆ pshare N w.qh (N.off.toNat + sz') CI.tag) ⋆
        up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail) ⋆ up (regionIn (N.add w.sz) w.A S' K' 1 t)) ⋆
        w.restE CI γ e ctx N)
      (⟪(w.grow sz' S' K' t).Facts⟫ ⋆ (w.grow sz' S' K' t).bodyE CI γ e ctx N) := by
  obtain ⟨hfin, hff, hgr, hacct, hqq, hcv⟩ := hw
  have hff' := hff
  simp only [OV.FirstFacts, hfirst] at hff'
  obtain ⟨hnf, hei, htail⟩ := hff'
  have hwf : (w.grow sz' S' K' t).Facts := by
    have hnodes : (w.grow sz' S' K' t).nodes = ⟨N, w.A, S', K', sz', w.qn, w.qh⟩ :: w.rest := by
      simp [OV.grow, OV.nodes, hfirst, OV.node]
    have hnodes0 : w.nodes = w.node N :: w.rest := by simp [OV.nodes, hfirst]
    refine ⟨hfin, ?_, fun i g hi => GrantOk.mono (fun nd hnd => ?_) (hgr i g hi), fun b => ?_,
      fun nd hnd => ?_, ?_⟩
    rotate_right
    · -- the new bytes join the tail
      refine OV.Cov.step hcv (OV.avail_step (i := 0) (fun _ h => h) (fun _ _ => rfl)
        (fun b x h => Or.inr (Or.inl ⟨0, h⟩)) fun b x h => ?_) fun nd hnd b x hx => ?_
      · obtain ⟨hb1, h1, h2⟩ := h.of_first hfirst
        exact OV.avail_tail hfirst hb1 h1 (by dsimp only [OV.grow]; omega)
      · rw [hnodes] at hnd
        rcases List.mem_cons.mp hnd with rfl | hnd
        · obtain ⟨hb1, h1, h2⟩ := hx
          by_cases hx' : x < N.off.toNat + w.sz
          · exact Or.inl ⟨w.node N, by rw [hnodes0]; exact List.mem_cons_self .., hb1, h1, hx'⟩
          · exact Or.inr (OV.avail_tail hfirst hb1 (by dsimp only [OV.grow]; omega) h2)
        · exact Or.inl ⟨nd, by rw [hnodes0]; exact List.mem_cons_of_mem _ hnd, hx⟩
    · simp only [OV.FirstFacts, OV.grow, hfirst]
      exact ⟨hnf', by omega, by simp only [Array.size_append, htail, ht]; have := hnf.hdr; omega⟩
    · rw [hnodes0] at hnd; rw [hnodes]
      rcases List.mem_cons.mp hnd with rfl | hnd
      · exact ⟨_, List.mem_cons_self .., rfl, rfl, hK⟩
      · exact ⟨nd, List.mem_cons_of_mem _ hnd, rfl, rfl, rfl⟩
    · rw [hnodes]
      show _ = poolOn b w.pn w.pf + grantsOn b w.M w.mN
      rw [← hacct b, hnodes0]; rfl
    · rw [hnodes] at hnd
      rcases List.mem_cons.mp hnd with rfl | hnd
      · exact hqq (w.node N) (by rw [hnodes0]; exact List.mem_cons_self ..)
      · exact hqq nd (by rw [hnodes0]; exact List.mem_cons_of_mem _ hnd)
  refine EUpd.trans (EUpd.of_imp (P' := (up (regionIn (N.add 16) w.A w.S w.K 8 (Enc.encode w.nxt)) ⋆
      up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail)) ⋆ (apts N (BitVec.ofNat 64 sz') ⋆
      (CI.tok N sz' 3 w.A S' K' w.qn ⋆ pshare N w.qh (N.off.toNat + sz') CI.tag) ⋆
      up (regionIn (N.add w.sz) w.A S' K' 1 t) ⋆ w.restE CI γ e ctx N)) fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame (EUpd.trans (EUpd.frame (EUpd.relabel (S' := S') hK))
    (EUpd.frameL (EUpd.relabel (S' := S') hK)))) ?_
  refine EUpd.of_imp fun r h => sep_lift.mpr ⟨hwf, ?_⟩
  have h0 := hnf.off0
  have hend : (N.add (24 + w.ei)).add (w.tail.size : Int) = N.add w.sz := by
    simp only [Ptr.add, Ptr.mk.injEq, true_and, htail]; omega
  have h := of_eq (Q := (up (regionIn (N.add (24 + w.ei)) w.A S' K' 1 w.tail) ⋆
      up (regionIn (N.add w.sz) w.A S' K' 1 t)) ⋆ (up (regionIn (N.add 16) w.A S' K' 8 (Enc.encode w.nxt)) ⋆
      apts N (BitVec.ofNat 64 sz') ⋆ (CI.tok N sz' 3 w.A S' K' w.qn ⋆ pshare N w.qh (N.off.toNat + sz') CI.tag) ⋆
      w.restE CI γ e ctx N)) (by ac_rfl) h
  have h := sep_mono_left (Q := up (regionIn (N.add (24 + w.ei)) w.A S' K' 1 (w.tail ++ t)))
    (fun _ x => up_region_join hend.symm x) h
  simp only [OV.bodyE, OV.restE, OV.grow] at h ⊢
  exact of_eq (by ac_rfl) h

/-- **The claims of the first node grown in place**: the child's claim on the new bytes is lent as
the arena's claim of epoch `e` (`EUpd.plendC`); the lent claim joins the tail's, its receipt the
node's. -/
theorem grow_cls {CI : Child} {γ e : Nat} {M : GMap} {w : OV} {N : Ptr} (hfirst : w.first = some N)
    (hei : 24 + w.ei ≤ w.sz) {sz' S' : Nat} {K' : BlockKind} {t : Array Byte} (hle : w.sz ≤ sz') :
    EUpd (gauthP γ e M CI.tag ⋆ (pclaim N (N.off.toNat + w.sz) (N.off.toNat + sz') CI.tag ⋆ w.cls CI γ e))
      (gauthP γ e M CI.tag ⋆ (w.grow sz' S' K' t).cls CI γ e) := by
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M CI.tag ⋆
    pclaim N (N.off.toNat + w.sz) (N.off.toNat + sz') CI.tag) ⋆ w.cls CI γ e) fun _ h => sep_assoc' h) ?_
  refine EUpd.trans (EUpd.frame EUpd.plendC) ?_
  refine EUpd.of_imp fun _ h => of_eq ?_ h
  simp only [OV.cls, FirstCl, OV.grow, hfirst, NodeCl, TailCl]
  rw [← pclaim_split (p := N) (lo := N.off.toNat + 24 + w.ei) (m := N.off.toNat + w.sz)
      (hi := N.off.toNat + sz') (by omega) (by omega),
    ← pcrcpt_split (p := N) (lo := N.off.toNat + 24) (m := N.off.toNat + w.sz) (hi := N.off.toNat + sz')
      (by omega) (by omega)]
  ac_rfl

/-- **The first node grown in place by its child** (O-G; `FAllocSpec.resize` refined: the arena
gives the child its token and its kept part `qh` of the node's share, no bytes and no claim): the
`size` word holds the new size, the token and the share are at the new size, the new bytes join
the tail; the node's regions take the new labels (`EUpd.relabel`; a kind of the same normal form).
The child gives the claim on the new bytes with them (`FAllocInv.newBytes`); it moves as in
`grow_cls`. -/
theorem grow_node_upd {CI : Child} {γ e : Nat} {ctx : Ptr} {w : OV} (hw : w.Facts) {N : Ptr}
    (hfirst : w.first = some N) {sz' S' : Nat} {K' : BlockKind} (hK : K'.norm = w.K.norm)
    (hnf' : NodeFacts N w.A sz') (hlt : w.sz < sz') {t : Array Byte} (ht : t.size = sz' - w.sz) :
    EUpd (((apts N (BitVec.ofNat 64 sz') ⋆ up (regionIn (N.add 16) w.A w.S w.K 8 (Enc.encode w.nxt)) ⋆
        (CI.tok N sz' 3 w.A S' K' w.qn ⋆ pshare N w.qh (N.off.toNat + sz') CI.tag) ⋆
        up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail) ⋆ up (regionIn (N.add w.sz) w.A S' K' 1 t)) ⋆
        w.restE CI γ e ctx N) ⋆
        (pclaim N (N.off.toNat + w.sz) (N.off.toNat + sz') CI.tag ⋆ w.cls CI γ e))
      ((⟪(w.grow sz' S' K' t).Facts⟫ ⋆ (w.grow sz' S' K' t).bodyE CI γ e ctx N) ⋆
        (w.grow sz' S' K' t).cls CI γ e) := by
  have hei : 24 + w.ei ≤ w.sz := by
    have hff := hw.2.1; simp only [OV.FirstFacts, hfirst] at hff; exact hff.2.1
  let X : FAssn := (apts N (BitVec.ofNat 64 sz') ⋆ up (regionIn (N.add 16) w.A w.S w.K 8 (Enc.encode w.nxt)) ⋆
    (CI.tok N sz' 3 w.A S' K' w.qn ⋆ pshare N w.qh (N.off.toNat + sz') CI.tag) ⋆
    up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail) ⋆ up (regionIn (N.add w.sz) w.A S' K' 1 t)) ⋆
    up (regionIn ctx w.Ac w.Sc w.Kc 8 CI.bytes) ⋆ aptsE (ctx.add 16) (some N) ⋆ aptsE (ctx.add 24) w.fl ⋆
    CI.own ⋆ vtR CI.vtp CI.fns.toList ⋆ JunkAt w.jh ⋆ Rcpts γ e w.M ⋆ Pool CI.tag w.pn w.pf ⋆ UsedRest CI w.rest w.nxt ⋆ FreeList CI w.fl
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e w.M CI.tag ⋆
      (pclaim N (N.off.toNat + w.sz) (N.off.toNat + sz') CI.tag ⋆ w.cls CI γ e)) ⋆ X)
    fun _ h => of_eq (by simp only [OV.restE, X]; ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame (grow_cls (S' := S') (K' := K') (t := t) hfirst hei (Nat.le_of_lt hlt))) ?_
  refine EUpd.trans (EUpd.of_imp (P' := ((apts N (BitVec.ofNat 64 sz') ⋆
      up (regionIn (N.add 16) w.A w.S w.K 8 (Enc.encode w.nxt)) ⋆
      (CI.tok N sz' 3 w.A S' K' w.qn ⋆ pshare N w.qh (N.off.toNat + sz') CI.tag) ⋆
      up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail) ⋆ up (regionIn (N.add w.sz) w.A S' K' 1 t)) ⋆
      w.restE CI γ e ctx N) ⋆ (w.grow sz' S' K' t).cls CI γ e)
    fun _ h => of_eq (by simp only [OV.restE, X]; ac_rfl) h) ?_
  exact EUpd.frame (grow_node_body hw hfirst hK hnf' hlt ht)

/-! ## `reset`'s ghost part (step 8)

After `Upd.bump` (epoch `e + 1`) every receipt of epoch `e` turns back into a share tagged with the
ledger's parent (`EUpd.revoke`), whatever the clients kept. With the per-block accounting the
revoked shares, the pool and the nodes' kept shares add up to each node's `qn` again. -/

/-- A grant's receipt, revoked: a share tagged `t` at the receipt's bound. -/
def revoked (t : STag) : Option GRegion → FAssn
  | none => FAssn.emp
  | some (p, _, q, _, _) => FAssn.ex fun b => FAssn.ex fun k => ⟪p.block = some b⟫ ⋆ bshare b q k t

/-- **Revoke every receipt** of a past epoch `e` under the ledger at epoch `e'` (`EUpd.revoke`). -/
theorem revoke_all {γ e e' : Nat} {M M' : GMap} {t : STag} (he : e < e') :
    ∀ N : Nat, EUpd (gauthP γ e' M' t ⋆ sepN N (fun i => rcptOf γ e (M i)))
      (gauthP γ e' M' t ⋆ sepN N (fun i => revoked t (M i)))
  | 0 => EUpd.of_imp fun _ h => h
  | N + 1 => by
    simp only [sepN]
    refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e' M' t ⋆ rcptOf γ e (M N)) ⋆
      sepN N (fun i => rcptOf γ e (M i))) fun _ h => sep_assoc' h) ?_
    refine EUpd.trans (EUpd.frame (P' := gauthP γ e' M' t ⋆ revoked t (M N)) ?_) ?_
    · cases hM : M N with
      | none => exact EUpd.of_imp fun _ h => h
      | some g =>
        obtain ⟨p, n, q, A, K⟩ := g
        simp only [rcptOf, revoked]
        refine EUpd.trans (EUpd.of_imp (P' := FAssn.ex fun b => FAssn.ex fun k => ⟪p.block = some b⟫ ⋆
          (gauthP γ e' M' t ⋆ brcpt b q k γ e)) fun _ h => ?_)
          (EUpd.exAll fun b => EUpd.exAll fun k => EUpd.lift fun hb => ?_)
        · obtain ⟨b, h⟩ := sep_exR h
          obtain ⟨k, h⟩ := sep_exR h
          exact ⟨b, k, of_eq (by ac_rfl) h⟩
        · refine EUpd.trans (EUpd.revoke he) (EUpd.of_imp fun _ h => ?_)
          exact sep_mono_right (fun _ x => ⟨b, k, sep_lift.mpr ⟨hb, x⟩⟩) h
    refine EUpd.trans (EUpd.of_imp (P' := revoked t (M N) ⋆ (gauthP γ e' M' t ⋆
      sepN N (fun i => rcptOf γ e (M i)))) fun _ h => of_eq (by ac_rfl) h) ?_
    refine EUpd.trans (EUpd.frameL (revoke_all he N)) ?_
    exact EUpd.of_imp fun _ h => of_eq (by ac_rfl) h

/-! ### Claims at a reset

Once the ledger is past epoch `e`, each used node's claim receipt turns back into the child's claim
on its buffer (`EUpd.prevokeC`) and joins its header's: the whole node's claim, as a free-list node
holds it (`FreeCl`) and as the child's `free` takes it. The claims of epoch `e` that the first
node's tail and the clients hold are stale: the tail's is dropped. -/

/-- **A used node's claims after its epoch**: the whole node's claim, tagged like the child's
grants. -/
theorem nodeCl_revoke {CI : Child} {γ e e' : Nat} {M : GMap} {N : Ptr} {sz : Nat} (he : e < e')
    (h24 : 24 ≤ sz) :
    EUpd (gauthP γ e' M CI.tag ⋆ NodeCl CI γ e N sz)
      (gauthP γ e' M CI.tag ⋆ pclaim N N.off.toNat (N.off.toNat + sz) CI.tag) := by
  refine EUpd.trans (EUpd.of_imp (P' := pclaim N N.off.toNat (N.off.toNat + 24) CI.tag ⋆
    (gauthP γ e' M CI.tag ⋆ pcrcpt N (N.off.toNat + 24) (N.off.toNat + sz) γ e))
    fun _ h => of_eq (by simp only [NodeCl]; ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frameL (EUpd.prevokeC he)) (EUpd.of_imp fun _ h => of_eq ?_ h)
  rw [← pclaim_split (p := N) (lo := N.off.toNat) (m := N.off.toNat + 24) (hi := N.off.toNat + sz)
    (by omega) (by omega)]
  ac_rfl

/-- The used nodes' claims after their epoch (`nodeCl_revoke`, node by node). -/
theorem restCl_revoke {CI : Child} {γ e e' : Nat} {M : GMap} (he : e < e') :
    ∀ ns : List NodeV, (∀ nd ∈ ns, 24 ≤ nd.sz) →
      EUpd (gauthP γ e' M CI.tag ⋆ RestCl CI γ e ns) (gauthP γ e' M CI.tag ⋆ FreeCl CI ns)
  | [], _ => EUpd.of_imp fun _ h => h
  | nd :: ns, h => by
    simp only [RestCl, FreeCl]
    refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc' h) ?_
    refine EUpd.trans (EUpd.frame (nodeCl_revoke he (h nd (List.mem_cons_self ..)))) ?_
    refine EUpd.trans (EUpd.of_imp (P' := pclaim nd.N nd.N.off.toNat (nd.N.off.toNat + nd.sz) CI.tag ⋆
      (gauthP γ e' M CI.tag ⋆ RestCl CI γ e ns)) fun _ h => of_eq (by ac_rfl) h) ?_
    refine EUpd.trans (EUpd.frameL (restCl_revoke he ns fun x hx => h x (List.mem_cons_of_mem _ hx))) ?_
    exact EUpd.of_imp fun _ h => of_eq (by ac_rfl) h

/-- **The arena's claims after its epoch**: every used node's whole claim (`FreeCl` of the used
nodes); the first node's tail claim (of the past epoch) is dropped. -/
theorem cls_revoke {CI : Child} {γ e e' : Nat} {M : GMap} {w : OV} (he : e < e') (hw : w.Facts)
    (h24 : ∀ nd ∈ w.rest, 24 ≤ nd.sz) :
    EUpd (gauthP γ e' M CI.tag ⋆ w.cls CI γ e) (gauthP γ e' M CI.tag ⋆ FreeCl CI w.nodes) := by
  have hff := hw.2.1
  cases hf : w.first with
  | none =>
    simp only [OV.FirstFacts, hf] at hff
    simp only [OV.cls, FirstCl, hf, OV.nodes, hff.2.1, RestCl, FreeCl]
    exact EUpd.of_imp fun _ h => sep_mono_right (fun _ x => of_eq (Full.emp_sep_eq _) x) h
  | some N =>
    simp only [OV.FirstFacts, hf] at hff
    simp only [OV.cls, FirstCl, hf, OV.nodes]
    refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e' M CI.tag ⋆ RestCl CI γ e (w.node N :: w.rest)) ⋆
      TailCl γ e N w.ei w.sz) fun _ h => of_eq (by simp only [RestCl, OV.node]; ac_rfl) h) ?_
    refine EUpd.trans (EUpd.drop fun _ h => pclaim_ghost h) (restCl_revoke he _ fun nd hnd => ?_)
    rcases List.mem_cons.mp hnd with rfl | hnd
    · exact hff.1.hdr
    · exact h24 nd hnd

/-! ### Shares at a reset

After `Upd.bump` every receipt of epoch `e` turns back into a share tagged with the ledger's parent
(`EUpd.revokeL`), whatever the clients kept. With the per-block accounting of `OV.Facts`
(`ndLent b = poolOn b + grantsOn b`) these shares, the pool and the nodes' kept parts `qh` regroup
(`EUpd.regroup`) into each node's whole share `qn`, which the child's `free` takes back with the
node. Each node's kept part is a source on its block at the node's end, so every node's bound is
reached. -/

/-- The block of a pointer whose block is known (`0` otherwise). -/
def blkOf (p : Ptr) : BlockId := p.block.getD 0

/-- The nodes' shares as pieces, with the fraction `sel nd` each, at the nodes' ends. -/
def nodePieces (sel : NodeV → Frac) (ns : List NodeV) : List Piece :=
  ns.map fun nd => (blkOf nd.N, sel nd, nd.N.off.toNat + nd.sz)

/-- The nodes' shares (tag `t`), with the fraction `sel nd` each, at the nodes' ends. -/
def NodeShares (t : STag) (sel : NodeV → Frac) : List NodeV → FAssn
  | [] => FAssn.emp
  | nd :: ns => pshare nd.N (sel nd) (nd.N.off.toNat + nd.sz) t ⋆ NodeShares t sel ns

theorem nodeShares_eq {t : STag} {sel : NodeV → Frac} :
    ∀ {ns : List NodeV}, (∀ nd ∈ ns, nd.N.block ≠ none) →
      NodeShares t sel ns = sharesL t (nodePieces sel ns)
  | [], _ => rfl
  | nd :: ns, h => by
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (h nd (List.mem_cons_self ..))
    have e1 : pshare nd.N (sel nd) (nd.N.off.toNat + nd.sz) t =
        bshare (blkOf nd.N) (sel nd) (nd.N.off.toNat + nd.sz) t := by
      funext r; apply propext; rw [pshare_iff hc]; simp only [blkOf, hc, Option.getD_some]
    show (pshare nd.N (sel nd) (nd.N.off.toNat + nd.sz) t ⋆ NodeShares t sel ns) =
      (bshare (blkOf nd.N) (sel nd) (nd.N.off.toNat + nd.sz) t ⋆ sharesL t (nodePieces sel ns))
    rw [e1, nodeShares_eq fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- `ndLent` as the nodes' whole shares minus their kept parts. -/
theorem ndLent_eq (b : BlockId) : ∀ {ns : List NodeV}, (∀ nd ∈ ns, nd.N.block ≠ none) →
    ndLent b ns = sumOn b (nodePieces NodeV.qn ns) - sumOn b (nodePieces NodeV.qh ns)
  | [], _ => by simp only [ndLent, nodePieces, List.map_nil, sumOn]; grind
  | nd :: ns, h => by
    have ih := ndLent_eq b (ns := ns) fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (h nd (List.mem_cons_self ..))
    simp only [nodePieces] at ih
    simp only [ndLent, nodePieces, List.map_cons, sumOn, blkOf, hc, Option.getD_some, ih,
      Option.some.injEq]
    split <;> grind

/-- The pool's pieces as a list. -/
def poolL (f : Nat → Piece) : Nat → List Piece
  | 0 => []
  | n + 1 => f n :: poolL f n

theorem pool_eq {t : STag} (f : Nat → Piece) : ∀ n, Pool t n f = sharesL t (poolL f n)
  | 0 => rfl
  | n + 1 => by
    have ih := pool_eq (t := t) f n
    simp only [Pool] at ih ⊢
    simp only [sepN, poolL, ih]
    generalize f n = x
    obtain ⟨b, q, k⟩ := x
    rfl

theorem sumOn_poolL (b : BlockId) (f : Nat → Piece) : ∀ n, sumOn b (poolL f n) = poolOn b n f
  | 0 => by simp [poolL, sumOn, poolOn, esum]
  | n + 1 => by
    have ih := sumOn_poolL b f n
    simp only [poolOn] at ih
    simp only [poolL, sumOn, poolOn, esum, ih]
    grind

/-- The receipts of a grant map as a list of pieces, with the grants' fractions per block. -/
theorem rcpts_list {γ e : Nat} {M : GMap} : ∀ N {r : Res}, sepN N (fun i => rcptOf γ e (M i)) r →
    ∃ l, (∀ b, sumOn b l = esum (fun i => grantOn b (M i)) N) ∧ rcptsL γ e l r
  | 0, _, h => ⟨[], fun b => by simp [sumOn, esum], h⟩
  | N + 1, _, h => by
    obtain ⟨r1, r2, hd, rfl, h1, h2⟩ := h
    obtain ⟨l, hl, h2⟩ := rcpts_list N h2
    cases hM : M N with
    | none =>
      simp only [hM, rcptOf] at h1
      exact ⟨l, fun b => by simp only [esum, hM, grantOn, hl b]; grind,
        of_eq (Full.emp_sep_eq _) ⟨r1, r2, hd, rfl, h1, h2⟩⟩
    | some g =>
      obtain ⟨p, n, q, A, K⟩ := g
      simp only [hM, rcptOf] at h1
      obtain ⟨b', k, h1⟩ := h1
      obtain ⟨hb', h1⟩ := sep_lift.mp h1
      refine ⟨(b', q, k) :: l, fun b => ?_, ⟨r1, r2, hd, rfl, h1, h2⟩⟩
      simp only [sumOn, esum, hM, grantOn, hb', hl b, Option.some.injEq]
      grind

theorem esum_stable {f : Nat → Rat} {N : Nat} (h : ∀ j, N ≤ j → f j = 0) :
    ∀ d, esum f (N + d) = esum f N
  | 0 => rfl
  | d + 1 => by
    rw [← Nat.add_assoc]; simp only [esum]; rw [esum_stable h d, h _ (by omega)]; grind

/-- The grants' fractions do not depend on the bound past the map's support. -/
theorem grantsOn_bound {M : GMap} {N N' : Nat} (h : ∀ j, N ≤ j → M j = none)
    (h' : ∀ j, N' ≤ j → M j = none) (b : BlockId) :
    esum (fun i => grantOn b (M i)) N = grantsOn b M N' := by
  have e1 := esum_stable (f := fun i => grantOn b (M i)) (N := N)
    (fun j hj => by simp [h j hj, grantOn]) N'
  have e2 := esum_stable (f := fun i => grantOn b (M i)) (N := N')
    (fun j hj => by simp [h' j hj, grantOn]) N
  rw [grantsOn, ← e1, ← e2, Nat.add_comm]

/-- **The nodes' whole shares at a reset**: past epoch `e`, the grants' receipts (revoked), the
pool and the nodes' kept parts `qh` regroup into each node's whole share `qn`. -/
theorem reset_shares {t : STag} {γ e e' : Nat} {M M' : GMap} {mN pn : Nat} {pf : Nat → Piece}
    {ns : List NodeV} (he : e < e') (hb : ∀ nd ∈ ns, nd.N.block ≠ none)
    (hqq : ∀ nd ∈ ns, nd.qh.val ≤ nd.qn.val) (hfin : ∀ i, mN ≤ i → M i = none)
    (hacct : ∀ b, ndLent b ns = poolOn b pn pf + grantsOn b M mN) :
    EUpd (gauthP γ e' M' t ⋆ (Rcpts γ e M ⋆ (Pool t pn pf ⋆ NodeShares t NodeV.qh ns)))
      (gauthP γ e' M' t ⋆ NodeShares t NodeV.qn ns) := by
  let src := nodePieces NodeV.qh ns ++ poolL pf pn
  refine EUpd.trans (EUpd.of_imp (P' := FAssn.ex fun l : List Piece =>
      ⟪∀ b, sumOn b l = grantsOn b M mN⟫ ⋆ ((gauthP γ e' M' t ⋆ rcptsL γ e l) ⋆ sharesL t src))
    fun r h => ?_) ?_
  · have h := of_eq (Q := Rcpts γ e M ⋆ (gauthP γ e' M' t ⋆ sharesL t src))
      (by simp only [src]; rw [sharesL_append, ← pool_eq, ← nodeShares_eq hb]; ac_rfl) h
    obtain ⟨N, h⟩ := sep_ex.mp h
    obtain ⟨hN, h⟩ := sep_lift.mp (sep_assoc h)
    obtain ⟨r1, r2, hd, rfl, h1, h2⟩ := h
    obtain ⟨l, hl, h1⟩ := rcpts_list N h1
    have h' : (rcptsL γ e l ⋆ (gauthP γ e' M' t ⋆ sharesL t src)) _ := ⟨r1, r2, hd, rfl, h1, h2⟩
    exact ⟨l, sep_lift.mpr ⟨fun b => by rw [hl b]; exact grantsOn_bound hN hfin b,
      of_eq (by ac_rfl) h'⟩⟩
  refine EUpd.exAll fun l => EUpd.lift fun hl => ?_
  refine EUpd.trans (EUpd.frame (EUpd.revokeL he l)) ?_
  refine EUpd.trans (EUpd.of_imp (P' := gauthP γ e' M' t ⋆ sharesL t (src ++ l))
    fun _ h => of_eq (by rw [sharesL_append src l]; ac_rfl) h) ?_
  refine EUpd.withFact (φ := ∀ x ∈ src ++ l, 0 < x.2.1.val)
    (fun _ r _ _ h _ => by obtain ⟨_, _, -, -, -, h2⟩ := h; exact sharesL_pos h2) fun hpos => ?_
  rw [nodeShares_eq hb]
  refine EUpd.frameL (EUpd.regroup _ _ (fun d hd => ?_) (fun b => ?_) (fun d hd => ?_))
  · simp only [nodePieces, List.mem_map] at hd
    obtain ⟨nd, hnd, rfl⟩ := hd
    have h1 := hpos (blkOf nd.N, nd.qh, nd.N.off.toNat + nd.sz)
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨nd, hnd, rfl⟩)))
    have h2 := hqq nd hnd
    simp only at h1 ⊢
    grind
  · simp only [src, sumOn_append, sumOn_poolL, hl b]
    have := hacct b
    rw [ndLent_eq b hb] at this
    grind
  · simp only [nodePieces, List.mem_map] at hd
    obtain ⟨nd, hnd, rfl⟩ := hd
    exact le_maxOn (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨nd, hnd, rfl⟩)))

/-! ## Proof tactics of the entries

Each is elaborated against the code of the module where it is used. The names it refers to are
that module's (`heap_ArenaAllocator_*`, `debug_assert_true`, `loadBuf_ct`, `resize_granted_ct`)
and the statement's (`CI`, `γ`, `e`, `ctx`, `s`, `k`, `n`, `bs`, `tl`, `hlen`, `hpos`, `hn`,
`hq`). -/

set_option hygiene false

/-- `Node.Size.toInt` of the bits of an even size (`toInt_ofBits`). -/
macro "arena_toInt" : tactic => `(tactic| (
  unfold heap_ArenaAllocator_Node_Size_toInt
  simp only [Packed.ofBits, Packed.get]
  show (pure (Packed.toBits ({ resizing := false, «_» := BitVec.extractLsb' 1 63 w } :
    heap_ArenaAllocator_Node_Size)) : Result _) = pure w
  exact congrArg pure (bits_even w h)))

/-- `Node.loadBuf` of a node whose `size` word holds an even size (`loadBuf_ct`). -/
macro "arena_loadBuf" : tactic => `(tactic| (
  have hsz64 : (BitVec.ofNat 64 sz).toNat = sz := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
  unfold heap_ArenaAllocator_Node_loadBuf
  simp only [atomicLoadAsC]
  conc_norm
  refine CTriple.pick_bind ?_
  refine CTriple.readStep (FTriple.atomicLoadAs (α := heap_ArenaAllocator_Node_Size) N
    (BitVec.ofNat 64 sz) _ rfl) rfl ?_
  rw [toInt_ofBits _ (by rw [hsz64]; exact heven)]
  conc_norm
  refine CTriple.pureStep (v := N.add 24) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blk, hblk, hle⟩ := hmem m r rF hh hp hs
    rw [ptrProject_elem_run hb hblk h0 (by simp; omega)]; rfl
  have h24 : (24 : BitVec 64).toNat ≤ (BitVec.ofNat 64 sz).toNat := by rw [hsz64]; simp; omega
  simp only [Ops.le_eq, h24, decide_true, ↓reduceIte, Zig.sub_unsigned_of_le h24, Nat.le_refl]
  conc_norm
  have hce : checkSliceEnd (BitVec.ofNat 64 sz) 24 (BitVec.ofNat 64 sz - 24) 0 = pure () := by
    unfold checkSliceEnd; rw [if_pos (by rw [BitVec.toNat_sub_of_le h24]; simp; omega)]
  rw [hce]
  conc_norm
  have e : BitVec.ofNat 64 sz - 24 = BitVec.ofNat 64 (sz - 24) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le h24, hsz64, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]; rfl
  exact CTriple.ret' _ fun r h => sep_lift.mpr ⟨by rw [e], h⟩))

/-- From the precondition to the load of `end_index`: the prefix that `free` and `resize` share
(`f` is the entry, `pre` the normal form of its precondition, `cl` its client part). -/
macro "arena_prefix" f:ident pre:term:max cl:term:max : tactic => `(tactic| (
  let G : Nat → Nat → BlockKind → FAssn := $cl
  refine CTriple.preM (fun m r rF hh hp hs => $pre) ?_
  refine CTriple.ex fun v => CTriple.lift fun hv0 => ?_
  obtain ⟨hv, hx⟩ := hv0
  have hv' := hv
  obtain ⟨⟨hfin, hwf, hgr, hacct, hqq, hcv⟩, hfirst, hbc, hbN, hbp, hac, hpos', hc0, hp0, hMi⟩ := hv'
  unfold OV.FirstFacts at hwf
  rw [hfirst] at hwf
  obtain ⟨hnf, hei, htail⟩ := hwf
  have hmem := fun m r rF (hh : Holds m r rF) (hp : v.L CI γ e ctx s G r) hs =>
    free_mem (CI := CI) (γ := γ) (e := e) hv hh hp hs
  unfold $f heap_ArenaAllocator_loadFirstNode
  simp only [atomicLoadPtrC, atomicLoadC, cmpxchgC]
  conc_norm
  -- `@intFromPtr(ctx) & 7 == 0`
  refine CTriple.pureStep (v := BitVec.ofInt 64 ((v.w.Ac : Int) + ctx.off)) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, -⟩ := hmem m r rF hh hp hs
    simp only [StateT.run_bind, ptrAddr_run' hbc e1, a1]; rfl
  have h7 : BitVec.ofInt 64 ((v.w.Ac : Int) + ctx.off) &&& 7 = 0 :=
    Ops.and_mask_eq_zero (k := 3) (by decide) (by omega) (by omega)
  simp only [h7, ↓reduceIte]
  -- `@alignCast(ctx)`
  refine CTriple.pureStep (v := ctx) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, -⟩ := hmem m r rF hh hp hs
    have h8 : ((v.w.Ac : Int) + ctx.off) % 8 = 0 := by omega
    unfold checkAlign
    simp only [StateT.run_bind, ptrAddr_run' hbc e1, a1, pure_bind]
    simp [h8]
  simp only [Ops.gt_eq, show decide ((0 : BitVec 64).toNat < s.len.toNat) = true by simp; omega]
  try simp only [show decide ((0 : BitVec 64).toNat < n.toNat) = true by simp; omega]
  simp only [debug_assert_true]
  conc_norm
  -- `&arena.state.used_list`
  refine CTriple.pureStep (v := ctx.add 16) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, -⟩ := hmem m r rF hh hp hs
    exact ptrProject_add_run' hbc e1 hc0 (by decide) (by omega)
  refine CTriple.pick_bind ?_
  refine CTriple.readStep (FTriple.atomicLoadPtr (ctx.add 16) (some v.N) _) rfl ?_
  simp only [Option.isSome_some, ↓reduceIte, optPayload]
  conc_norm
  have hei64 : (BitVec.ofNat 64 v.w.ei).toNat = v.w.ei := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; have := hnf.small; omega
  -- `buf_ptr`, `&node.end_index`, `end_index`
  refine CTriple.pureStep (v := v.N.add 24) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, -⟩ := hmem m r rF hh hp hs
    have := hnf.off0
    rw [ptrProject_elem_run hbN e2 hnf.off0 (by simp; omega)]; rfl
  refine CTriple.pureStep (v := v.N.add 8) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, -⟩ := hmem m r rF hh hp hs
    have := hnf.off0
    exact ptrProject_add_run' hbN e2 hnf.off0 (by decide) (by omega)
  refine CTriple.pick_bind ?_
  refine CTriple.readStep (FTriple.atomicLoad (v.N.add 8) (BitVec.ofNat 64 v.w.ei) _)
    (sep_left_comm_eq _ _ _) ?_))

/-- The bounds check of the patched `free` and `resize` (`docs/upstream/arena-oob-gep.md`):
`end_index` is within the buffer that `loadBuf` reads, so they go on. -/
macro "arena_bounds" : tactic => `(tactic| (
  refine CTriple.pre (P := apts v.N (BitVec.ofNat 64 v.w.sz) ⋆ v.Lsz CI γ e ctx s G) ?_
    (fun r h => of_eq (FV.L_eq CI γ e ctx s G v) h)
  refine CTriple.bind (loadBuf_ct (R := v.Lsz CI γ e ctx s G) hbN hnf.off0 hnf.hdr hnf.even
    (by have := hnf.small; omega) (fun m r rF hh hp hs => ?_))
    fun sl => CTriple.lift fun hsl => ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ :=
      hmem m r rF hh (of_eq (FV.L_eq CI γ e ctx s G v).symm hp) hs
    exact ⟨blkN, e2, s2⟩
  subst hsl
  refine CTriple.pre (P := v.L CI γ e ctx s G) ?_ (fun r h => of_eq (FV.L_eq CI γ e ctx s G v).symm h)
  conc_norm
  have hgt : decide ((BitVec.ofNat 64 (v.w.sz - 24)).toNat < (BitVec.ofNat 64 v.w.ei).toNat) = false := by
    rw [hei64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hnf.small; omega)]
    simp only [decide_eq_false_iff_not, Nat.not_lt]; omega
  simp only [hgt, Bool.false_eq_true, ↓reduceIte]
))

/-- `free` from the comparison of `buf_ptr + end_index` with the slice's end. -/
macro "arena_free_tail" : tactic => `(tactic| (
  -- `buf_ptr + end_index`, `memory.ptr + memory.len`, and their comparison (O-F: `last_dec`)
  refine CTriple.pureStep (v := (v.N.add 24).add v.w.ei) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, -⟩ := hmem m r rF hh hp hs
    have := hnf.off0
    rw [ptrProject_elem_run (by simpa [Ptr.add] using hbN) e2 (by simp [Ptr.add]; omega)
      (by simp [Ptr.add, hei64]; omega), hei64]
  refine CTriple.pureStep (v := s.ptr.add s.len.toNat) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, -⟩ := hmem m r rF hh hp hs
    exact ptrProject_elem_run hbp e3 hp0 (by omega)
  refine CTriple.pureStep (v := !decide (v.bp = v.bN ∧
    s.ptr.off.toNat + s.len.toNat = v.N.off.toNat + 24 + v.w.ei)) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hap, hsame⟩ := hmem m r rF hh hp hs
    have := hnf.off0
    rw [StateT.run_bind, ptrEqAddr_run (q := s.ptr.add s.len.toNat) (by simpa [Ptr.add] using hbN) e2
      (by simpa [Ptr.add] using hbp) e3, last_dec (P := (v.N.add 24).add v.w.ei)
      (Q := s.ptr.add s.len.toNat) (xN := v.N.off.toNat + 24 + v.w.ei)
      (xP := s.ptr.off.toNat + s.len.toNat) (by simp only [Ptr.add]; omega)
      (by simp only [Ptr.add]; omega) (by omega) (by omega) (by omega) (by omega) hap hsame]
    simp only [pure_bind, StateT.run_pure]
  by_cases heq : v.bp = v.bN ∧ s.ptr.off.toNat + s.len.toNat = v.N.off.toNat + 24 + v.w.ei
  · simp only [heq, and_self, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    -- the slice is the first node's last allocation: its labels are the node's (`last_labels`),
    -- and it lies past the header (`lo_of`)
    obtain ⟨hb, hoff⟩ := heq
    refine CTriple.facts (fun m r rF hh hp hs => And.intro (last_labels (G := G) hv hb hh hp)
      (lo_of (G := G) hv (p := s.ptr) (bs := bs) (fun _ h => ⟨_, h⟩) (hb ▸ hbp) hpos (by omega) hp)) ?_
    rintro ⟨⟨hA, hK⟩, hlo⟩
    have hle : s.len.toNat ≤ (BitVec.ofNat 64 v.w.ei).toNat := by rw [hei64]; omega
    have hd : (BitVec.ofNat 64 v.w.ei - s.len).toNat = v.w.ei - s.len.toNat := by
      rw [BitVec.toNat_sub_of_le hle, hei64]
    rw [Zig.sub_unsigned_of_le hle]
    conc_norm
    -- `buf_ptr + new_end_index == memory.ptr`
    refine CTriple.pureStep (v := (v.N.add 24).add (v.w.ei - s.len.toNat : Nat))
      (fun m r rF hh hp hs => ?_) ?_
    · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
      have := hnf.off0
      rw [ptrProject_elem_run (by simpa [Ptr.add] using hbN) e2 (by simp [Ptr.add]; omega)
        (by simp [Ptr.add, hd]; omega), hd]
    refine CTriple.pureStep (v := true) (fun m r rF hh hp hs => ?_) ?_
    · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, hsame⟩ := hmem m r rF hh hp hs
      have := hnf.off0
      rw [ptrEqAddr_run (by simpa [Ptr.add] using hbN) e2 hbp e3, hsame hb]
      have : ((v.N.add 24).add (v.w.ei - s.len.toNat : Nat)).off = s.ptr.off := by
        simp only [Ptr.add]; omega
      simp [this]
    rw [debug_assert_true]
    conc_norm
    refine CTriple.pureStep (v := v.N.add 8) (fun m r rF hh hp hs => ?_) ?_
    · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
      have := hnf.off0
      exact ptrProject_add_run' hbN e2 hnf.off0 (by decide) (by omega)
    refine CTriple.pick_bind ?_
    -- the strong `cmpxchg` finds `end_index` and moves it back
    refine CTriple.pre (P := v.eW v.w.ei ⋆ (v.uW ctx ⋆ v.R0 CI γ e ctx s G)) ?_
      (fun r h => of_eq (sep_left_comm_eq _ _ _) h)
    refine CTriple.bind (CTriple.liftMem ((FTriple.cmpxchgHit (v.N.add 8) (BitVec.ofNat 64 v.w.ei)
      (BitVec.ofNat 64 v.w.ei - s.len) _ _).frame)) fun _ => ?_
    have hnew : BitVec.ofNat 64 v.w.ei - s.len = BitVec.ofNat 64 (v.w.ei - s.len.toNat) := by
      apply BitVec.eq_of_toNat_eq; rw [hd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      have := hnf.small; omega
    refine CTriple.eupd (free_last_upd hv hx hfirst hnf hei htail hb hA hK hlen hoff hlo hnew) ?_
    exact CTriple.ret' () fun _ h => h
  · -- not the last allocation: the slice leaks to the arena
    simp only [heq, decide_false, Bool.not_false, ↓reduceIte]
    refine CTriple.eupd (free_other_upd hv hx hfirst hnf hei htail hlen) ?_
    exact CTriple.ret' () fun _ h => h))

/-- `resize` from the comparison of `buf_ptr + end_index` with the slice's end. -/
macro "arena_resize_tail" : tactic => `(tactic| (
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hx
  -- `buf_ptr + end_index`, `memory.ptr + memory.len`, and their comparison (O-F: `last_dec`)
  refine CTriple.pureStep (v := (v.N.add 24).add v.w.ei) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, -⟩ := hmem m r rF hh hp hs
    have := hnf.off0
    rw [ptrProject_elem_run (by simpa [Ptr.add] using hbN) e2 (by simp [Ptr.add]; omega)
      (by simp [Ptr.add, hei64]; omega), hei64]
  refine CTriple.pureStep (v := s.ptr.add s.len.toNat) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, -⟩ := hmem m r rF hh hp hs
    exact ptrProject_elem_run hbp e3 hp0 (by omega)
  refine CTriple.pureStep (v := !decide (v.bp = v.bN ∧
    s.ptr.off.toNat + s.len.toNat = v.N.off.toNat + 24 + v.w.ei)) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hap, hsame⟩ := hmem m r rF hh hp hs
    have := hnf.off0
    rw [StateT.run_bind, ptrEqAddr_run (q := s.ptr.add s.len.toNat) (by simpa [Ptr.add] using hbN) e2
      (by simpa [Ptr.add] using hbp) e3, last_dec (P := (v.N.add 24).add v.w.ei)
      (Q := s.ptr.add s.len.toNat) (xN := v.N.off.toNat + 24 + v.w.ei)
      (xP := s.ptr.off.toNat + s.len.toNat) (by simp only [Ptr.add]; omega)
      (by simp only [Ptr.add]; omega) (by omega) (by omega) (by omega) (by omega) hap hsame]
    simp only [pure_bind, StateT.run_pure]
  by_cases heq : v.bp = v.bN ∧ s.ptr.off.toNat + s.len.toNat = v.N.off.toNat + 24 + v.w.ei
  · simp only [heq, and_self, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    -- the slice is the first node's last allocation; its labels are the node's (`last_labels`)
    obtain ⟨hb, hoff⟩ := heq
    refine CTriple.facts (fun m r rF hh hp hs => last_labels (G := G) hv hb hh hp) ?_
    rintro ⟨hA, hK⟩
    have hbN' : (v.N.add 24).block = some v.bN := by simpa [Ptr.add] using hbN
    have h0 := hnf.off0
    have hsm := hnf.small
    simp only [Ops.le_eq]
    by_cases hle : n.toNat ≤ s.len.toNat
    · -- shrink: `end_index` moves back by `len - n`; the released bytes rejoin the tail
      simp only [hle, decide_true, ↓reduceIte]
      refine CTriple.facts (fun m r rF hh hp hs => fun (hcut : n.toNat < s.len.toNat) =>
        cut_facts hv hb hoff hcut hp) ?_
      intro hcf
      have hlo' : s.len.toNat - n.toNat ≤ v.w.ei := by
        by_cases hcut : n.toNat < s.len.toNat
        · have := (hcf hcut).2; omega
        · omega
      have hd1 : (s.len - n).toNat = s.len.toNat - n.toNat := BitVec.toNat_sub_of_le hle
      have h2 : (s.len - n).toNat ≤ (BitVec.ofNat 64 v.w.ei).toNat := by rw [hd1, hei64]; exact hlo'
      have hd2 : (BitVec.ofNat 64 v.w.ei - (s.len - n)).toNat = v.w.ei - (s.len.toNat - n.toNat) := by
        rw [BitVec.toNat_sub_of_le h2, hei64, hd1]
      rw [Zig.sub_unsigned_of_le hle]
      conc_norm
      rw [Zig.sub_unsigned_of_le h2]
      conc_norm
      refine CTriple.pureStep (v := (v.N.add 24).add (v.w.ei - (s.len.toNat - n.toNat) : Nat))
        (fun m r rF hh hp hs => ?_) ?_
      · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
        rw [ptrProject_elem_run hbN' e2 (by simp [Ptr.add]; omega) (by simp [Ptr.add, hd2]; omega), hd2]
      refine CTriple.pureStep (v := s.ptr.add n.toNat) (fun m r rF hh hp hs => ?_) ?_
      · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -⟩ := hmem m r rF hh hp hs
        rw [ptrProject_elem_run hbp e3 hp0 (by omega)]
      refine CTriple.pureStep (v := true) (fun m r rF hh hp hs => ?_) ?_
      · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, hsame⟩ := hmem m r rF hh hp hs
        rw [ptrEqAddr_run (by simpa [Ptr.add] using hbN) e2 (by simpa [Ptr.add] using hbp) e3, hsame hb]
        have hxo : ((v.N.add 24).add (v.w.ei - (s.len.toNat - n.toNat) : Nat)).off =
            (s.ptr.add n.toNat).off := by
          simp only [Ptr.add]; omega
        simp only [hxo, decide_true]
      rw [debug_assert_true]
      conc_norm
      refine CTriple.pureStep (v := v.N.add 8) (fun m r rF hh hp hs => ?_) ?_
      · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
        exact ptrProject_add_run' hbN e2 hnf.off0 (by decide) (by omega)
      refine CTriple.pick_bind ?_
      refine CTriple.pre (P := v.eW v.w.ei ⋆ (v.uW ctx ⋆ v.R0 CI γ e ctx s G)) ?_
        (fun r h => of_eq (sep_left_comm_eq _ _ _) h)
      refine CTriple.bind (CTriple.liftMem ((FTriple.cmpxchgHit (v.N.add 8) (BitVec.ofNat 64 v.w.ei)
        (BitVec.ofNat 64 v.w.ei - (s.len - n)) _ _).frame)) fun _ => ?_
      have hnew : BitVec.ofNat 64 v.w.ei - (s.len - n) =
          BitVec.ofNat 64 (v.w.ei - (s.len.toNat - n.toNat)) := by
        apply BitVec.eq_of_toNat_eq; rw [hd2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
      refine CTriple.eupd (resize_shrink_upd (k := k) hv hfirst hnf hei htail hb hA hK hoff hle hcf hnew) ?_
      exact CTriple.ret' true fun _ h => h
    · -- growth into the tail, when the tail has room
      simp only [hle, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hlt : s.len.toNat ≤ n.toNat := by omega
      have hd : (n - s.len).toNat = n.toNat - s.len.toNat := BitVec.toNat_sub_of_le hlt
      refine CTriple.pre (P := apts v.N (BitVec.ofNat 64 v.w.sz) ⋆ v.Lsz CI γ e ctx s G) ?_
        (fun r h => of_eq (FV.L_eq CI γ e ctx s G v) h)
      refine CTriple.bind (loadBuf_ct (R := v.Lsz CI γ e ctx s G) hbN hnf.off0 hnf.hdr hnf.even
        (by have := hnf.small; omega) (fun m r rF hh hp hs => ?_)) fun sl => CTriple.lift fun hsl => ?_
      · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ :=
          hmem m r rF hh (of_eq (FV.L_eq CI γ e ctx s G v).symm hp) hs
        exact ⟨blkN, e2, s2⟩
      subst hsl
      refine CTriple.pre (P := v.L CI γ e ctx s G) ?_ (fun r h => of_eq (FV.L_eq CI γ e ctx s G v).symm h)
      rw [Zig.sub_unsigned_of_le hlt]
      conc_norm
      have hroom : (Zig.subSat false (BitVec.ofNat 64 (v.w.sz - 24)) (BitVec.ofNat 64 v.w.ei)).toNat =
          v.w.sz - 24 - v.w.ei := by
        rw [Zig.subSat_unsigned_toNat, hei64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [Zig.ge, Ops.le_eq, hroom, hd]
      by_cases hfit : n.toNat - s.len.toNat ≤ v.w.sz - 24 - v.w.ei
      · simp only [hfit, decide_true, ↓reduceIte]
        have hadd : (BitVec.ofNat 64 v.w.ei).toNat + (n - s.len).toNat < 2 ^ 64 := by
          rw [hei64, hd]; omega
        have hd2 : (BitVec.ofNat 64 v.w.ei + (n - s.len)).toNat = v.w.ei + (n.toNat - s.len.toNat) := by
          rw [BitVec.toNat_add_of_lt hadd, hei64, hd]
        rw [Zig.add_unsigned_of_lt hadd]
        conc_norm
        refine CTriple.pureStep (v := (v.N.add 24).add (v.w.ei + (n.toNat - s.len.toNat) : Nat))
          (fun m r rF hh hp hs => ?_) ?_
        · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
          rw [ptrProject_elem_run hbN' e2 (by simp [Ptr.add]; omega) (by simp [Ptr.add, hd2]; omega), hd2]
        refine CTriple.pureStep (v := s.ptr.add n.toNat) (fun m r rF hh hp hs => ?_) ?_
        · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
          rw [ptrProject_elem_run (hb ▸ hbp) e2 hp0 (by omega)]
        refine CTriple.pureStep (v := true) (fun m r rF hh hp hs => ?_) ?_
        · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, hsame⟩ := hmem m r rF hh hp hs
          rw [ptrEqAddr_run (by simpa [Ptr.add] using hbN) e2 (by simpa [Ptr.add] using hbp) e3, hsame hb]
          have hxo : ((v.N.add 24).add (v.w.ei + (n.toNat - s.len.toNat) : Nat)).off =
              (s.ptr.add n.toNat).off := by
            simp only [Ptr.add]; omega
          simp only [hxo, decide_true]
        rw [debug_assert_true]
        conc_norm
        refine CTriple.pureStep (v := v.N.add 8) (fun m r rF hh hp hs => ?_) ?_
        · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
          exact ptrProject_add_run' hbN e2 hnf.off0 (by decide) (by omega)
        refine CTriple.pick_bind ?_
        refine CTriple.pre (P := v.eW v.w.ei ⋆ (v.uW ctx ⋆ v.R0 CI γ e ctx s G)) ?_
          (fun r h => of_eq (sep_left_comm_eq _ _ _) h)
        refine CTriple.bind (CTriple.liftMem ((FTriple.cmpxchgHit (v.N.add 8) (BitVec.ofNat 64 v.w.ei)
          (BitVec.ofNat 64 v.w.ei + (n - s.len)) _ _).frame)) fun res => ?_
        refine CTriple.pre (CTriple.lift (P := apts (v.N.add 8) (BitVec.ofNat 64 v.w.ei + (n - s.len)) ⋆
          (v.uW ctx ⋆ v.R0 CI γ e ctx s G)) fun hres => ?_) (fun r h => sep_assoc h)
        subst hres
        simp only [Option.isNone_none]
        have hnew : BitVec.ofNat 64 v.w.ei + (n - s.len) =
            BitVec.ofNat 64 (v.w.ei + (n.toNat - s.len.toNat)) := by
          apply BitVec.eq_of_toNat_eq; rw [hd2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
        refine CTriple.eupd (resize_grow_upd (k := k) hv hfirst hnf hei htail hb hA hK hoff hq (by omega) hfit
          hnew) ?_
        exact CTriple.ret' true fun _ h => h
      · simp only [hfit, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact CTriple.ret' false fun _ h => resize_false_of hv hfirst h
  · -- not the first node's last allocation: only a shrink succeeds; the released bytes become junk
    simp only [heq, decide_false, Bool.not_false, ↓reduceIte, Ops.le_eq]
    by_cases hle : n.toNat ≤ s.len.toNat
    · simp only [hle, decide_true]
      refine CTriple.eupd (resize_other_upd (k := k) hv hfirst hnf hei htail hle) ?_
      exact CTriple.ret' true fun _ h => h
    · simp only [hle, decide_false]
      exact CTriple.ret' false fun _ h => resize_false_of hv hfirst h))

/-- `remap` is `resize`, and returns `memory.ptr` when it succeeds (`resize_granted_ct`). -/
macro "arena_remap" : tactic => `(tactic| (
  unfold heap_ArenaAllocator_remap
  conc_norm
  refine CTriple.bind (resize_granted_ct CI γ e ctx s k n ra bs hlen hpos hn) fun b => ?_
  cases b <;> exact CTriple.ret' _ fun _ h => h))

/-- `free` of the stock arena. -/
macro "arena_free" : tactic => `(tactic| (
  arena_prefix heap_ArenaAllocator_free (free_pre hh hlen hpos hp) (rgn γ e s k bs)
  arena_free_tail))

/-- `free` of the patched arena: the bounds check first. -/
macro "arena_free_checked" : tactic => `(tactic| (
  arena_prefix heap_ArenaAllocator_free (free_pre hh hlen hpos hp) (rgn γ e s k bs)
  arena_bounds
  arena_free_tail))

/-- `resize` of the stock arena. -/
macro "arena_resize" : tactic => `(tactic| (
  arena_prefix heap_ArenaAllocator_resize (pre_of (G := relB CI γ e ctx s n.toNat tl) hh hpos hp) (relB CI γ e ctx s n.toNat tl)
  arena_resize_tail))

/-- `resize` of the patched arena: the bounds check first. -/
macro "arena_resize_checked" : tactic => `(tactic| (
  arena_prefix heap_ArenaAllocator_resize (pre_of (G := relB CI γ e ctx s n.toNat tl) hh hpos hp) (relB CI γ e ctx s n.toNat tl)
  arena_bounds
  arena_resize_tail))

/-! ## The statements of a module's specification

`arena_spec_statements` (stock) and `arena_spec_statements checked` (the patched arena's bounds
check) declare, in the current namespace, the lemmas and theorems of a module's specification
(`free_spec`, `resize_spec`, `remap_spec` and their `CTriple` forms), proved by the tactics
above. The specification files open their module and use it once; the identifiers resolve there. -/

/-- The statements of a module's specification (section doc). -/
macro "arena_spec_statements" chk:(&" checked")? : command => do
  let freeT ← if chk.isSome then `(tactic| arena_free_checked) else `(tactic| arena_free)
  let resizeT ← if chk.isSome then `(tactic| arena_resize_checked) else `(tactic| arena_resize)
  return ⟨Lean.mkNullNode #[
    (← `(command|
theorem debug_assert_true : debug_assert true = pure () := rfl)),
    (← `(command|
/-- `Node.Size.toInt` of the decoded bits of an even size is the size. -/
theorem toInt_ofBits (w : BitVec 64) (h : w.toNat % 2 = 0) :
    heap_ArenaAllocator_Node_Size_toInt (Packed.ofBits w) = pure w := by
  arena_toInt)),
    (← `(command|
/-- `Node.loadBuf` of a node whose `size` word holds the even size `sz`: the buffer after the
header, `sz - 24` bytes. -/
theorem loadBuf_ct {N : Ptr} {b : BlockId} {sz : Nat} {R : FAssn} (hb : N.block = some b)
    (h0 : 0 ≤ N.off) (hsz : 24 ≤ sz) (heven : sz % 2 = 0) (hsmall : sz < 2 ^ 63)
    (hmem : ∀ m r rF, Holds m r rF → (apts N (BitVec.ofNat 64 sz) ⋆ R) r → m.FSeq →
      ∃ blk, m.blocks[b]? = some blk ∧ N.off.toNat + sz ≤ blk.bytes.size) :
    CTriple (Tgt := Tgt) (apts N (BitVec.ofNat 64 sz) ⋆ R) (heap_ArenaAllocator_Node_loadBuf N)
      (fun sl => ⟪sl = ⟨N.add 24, BitVec.ofNat 64 (sz - 24)⟩⟫ ⋆ (apts N (BitVec.ofNat 64 sz) ⋆ R)) := by
  arena_loadBuf)),
    (← `(command|
/-- `free`'s run, case by case (module doc). -/
theorem free_ct (CI : Child) (γ e : Nat) (ctx s : _) (k : Nat) (ra : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (heap_ArenaAllocator_free ctx s ⟨BitVec.ofNat 6 k⟩ ra) (fun _ => (inv CI γ e ctx).own) := by
  $freeT:tactic)),
    (← `(command|
/-- **`free` meets `FAllocSpec`'s `free` field** for the arena invariant at every epoch, every
child `CI` (`Child`), and every depth of the one-thread reading (`Sched.soloRun`). -/
theorem free_spec (CI : Child) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (ra : BitVec 64) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (Sched.soloRun fuel (heap_ArenaAllocator_free ctx s ⟨BitVec.ofNat 6 k⟩ ra))
      (fun _ => (inv CI γ e ctx).own) :=
  free_ct CI γ e ctx s k ra bs hlen hpos fuel)),
    (← `(command|
/-- `resize`'s run, case by case, against the refined contract (`FAllocSpec.resize`): from the
token, the client's part `q'` of the grant's share and the bytes a shrink releases. A slice that
is not the first node's last one only shrinks (the released bytes become junk); the last one moves
`end_index` (shrink, or growth into the tail when it fits: the client gets the new bytes, its part
of the share is re-lent at the new end). A successful resize re-points the grant at the new
length (`Upd.reassign`). -/
theorem resize_ct (CI : Child) (γ e : Nat) (ctx s : _) (k : Nat) (n ra : BitVec 64)
    (A S : Nat) (K : BlockKind) (q q' : Frac) (tl : Array Byte) (hpos : 0 < s.len.toNat)
    (hn : 0 < n.toNat) (hq : q'.val ≤ q.val) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ ((inv CI γ e ctx).held s.ptr s.len.toNat k A S K q q' ⋆
        (inv CI γ e ctx).relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (heap_ArenaAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((inv CI γ e ctx).rresizePost s.ptr k s.len.toNat n.toNat A S K q q' tl) := by
  $resizeT:tactic)),
    (← `(command|
/-- The whole-region `resize` (`FAllocInv.resize_granted_of`). -/
theorem resize_granted_ct (CI : Child) (γ e : Nat) (ctx s : _) (k : Nat) (n ra : BitVec 64)
    (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) (hn : 0 < n.toNat) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (heap_ArenaAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((inv CI γ e ctx).resizePost s.ptr k bs n.toNat) := fun fuel =>
  (inv CI γ e ctx).resize_granted_of (L := FLogic.partial)
    (fun A S K q q' tl h1 _ => resize_ct CI γ e ctx s k n ra A S K q q' tl (by omega) hn h1 fuel) hlen)),
    (← `(command|
/-- `remap` is `resize`, and returns `memory.ptr` when it succeeds. -/
theorem remap_ct (CI : Child) (γ e : Nat) (ctx s : _) (k : Nat) (n ra : BitVec 64)
    (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) (hn : 0 < n.toNat) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (heap_ArenaAllocator_remap ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((inv CI γ e ctx).remapPost s.ptr k bs n.toNat) := by
  arena_remap)),
    (← `(command|
/-- **`resize` meets `FAllocSpec`'s refined `resize` field** for the arena invariant at every
epoch, every child `CI`, and every depth of the one-thread reading. -/
theorem resize_spec (CI : Child) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (n ra : BitVec 64) (A S : Nat) (K : BlockKind) (q q' : Frac) (tl : Array Byte)
    (hpos : 0 < s.len.toNat) (hn : 0 < n.toNat) (hq : q'.val ≤ q.val) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ ((inv CI γ e ctx).held s.ptr s.len.toNat k A S K q q' ⋆
        (inv CI γ e ctx).relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (Sched.soloRun fuel (heap_ArenaAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra))
      ((inv CI γ e ctx).rresizePost s.ptr k s.len.toNat n.toNat A S K q q' tl) :=
  resize_ct CI γ e ctx s k n ra A S K q q' tl hpos hn hq fuel)),
    (← `(command|
/-- **`remap` meets `FAllocSpec`'s `remap` field.** -/
theorem remap_spec (CI : Child) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (n ra : BitVec 64) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size)
    (hn : 0 < n.toNat) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (Sched.soloRun fuel (heap_ArenaAllocator_remap ctx s ⟨BitVec.ofNat 6 k⟩ n ra))
      ((inv CI γ e ctx).remapPost s.ptr k bs n.toNat) :=
  remap_ct CI γ e ctx s k n ra bs hlen hpos hn fuel))]⟩

end AllocArena.Core
