import ZigLean.Sep.AllocSpec.Region
import ZigLean.Sep.AllocSpec.Ops
import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Conc
import ZigLean.Sep.Full.AtomicRules
import ZigLean.Sep.Full.Ghost
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

/-! ## Owned cells -/

/-- `P` owns byte `x` of block `b`, whose cell records address `A` and kind `K` (a cell's size
is a label: `docs/sep-full-state.md` §Block extents). -/
def Owns (b x : Nat) (A : Nat) (K : BlockKind) (P : FAssn) : Prop :=
  ∀ r, P r → ∃ fc, r.heap (b, x) = some fc ∧ fc.cell.addr = A ∧ fc.cell.kind = K

/-- A byte owned by a part (`Within`) is owned. -/
theorem Owns.within {b x A K} {X P : FAssn} (h : Owns b x A K X) (hw : Within X P) : Owns b x A K P := by
  intro r hr
  obtain ⟨R, r₁, r₂, -, rfl, h1, -⟩ := hw r hr
  obtain ⟨fc, hx, e⟩ := h r₁ h1
  exact ⟨fc, by show (r₁.heap (b, x)).or _ = _; rw [hx]; rfl, e⟩

/-- Byte `i` of a `regionIn` is owned. -/
theorem Owns.region {p : Ptr} {b : BlockId} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}
    (hb : p.block = some b) {i : Nat} (hi : i < bs.size) :
    Owns b (p.off.toNat + i) A K (up (regionIn p A S K a bs)) := by
  rintro r ⟨⟨-, -, b', hb', -, hl⟩, -⟩
  rw [hb] at hb'; cases hb'
  have := hl (b, p.off.toNat + i)
  simp only [FHeap.erase] at this
  rw [if_pos (by simp only [true_and]; omega)] at this
  cases e : r.heap (b, p.off.toNat + i) with
  | none => rw [e] at this; cases this
  | some fc =>
    rw [e] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact ⟨fc, rfl, by rw [this], by rw [this]⟩

/-- An owned byte is a byte of a live block of the memory, at the cell's address, with the
cell's kind up to `BlockKind.norm` (`Holds.block`). -/
theorem Owns.block {b x A K} {P : FAssn} (h : Owns b x A K P) {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hp : P r) : ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧
      x < blk.bytes.size ∧ blk.addr = A ∧ blk.kind.norm = K.norm := by
  obtain ⟨fc, hx, rfl, rfl⟩ := h r hp
  obtain ⟨blk, hb, hl, hx', -, ha, hk⟩ := hh.block hx
  exact ⟨blk, hb, hl, hx', ha.symm, hk.symm⟩

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

/-! ## The invariant -/

/-- The pure facts of a node at `N` of `sz` bytes in a block at address `A`. -/
structure NodeFacts (N : Ptr) (A sz : Nat) : Prop where
  off0 : 0 ≤ N.off
  al : (A + N.off.toNat) % 8 = 0
  hdr : 24 ≤ sz
  even : sz % 2 = 0
  small : N.off.toNat + sz < 2 ^ 63

/-- The header of a node, the child's token for it (the child lent the fraction `qn` with it)
and the part `qh` of the node's extent share that the arena keeps (the rest is lent to the
node's grants, or back in the pool): the `size` word (atomic; even, so its `resizing` bit is
clear), the `end_index` word (atomic) and the `next` pointer. The share is tagged like the
child's grants (`CI.tag`). -/
def Header (CI : FAllocInv) (N : Ptr) (A S : Nat) (K : BlockKind) (sz : Nat) (ei : BitVec 64)
    (nxt : Option Ptr) (qn qh : Frac) : FAssn :=
  apts N (BitVec.ofNat 64 sz) ⋆ apts (N.add 8) ei ⋆
    up (regionIn (N.add 16) A S K 8 (Enc.encode nxt)) ⋆
    (CI.tok N sz 3 A S K qn ⋆ pshare N qh (N.off.toNat + sz) CI.tag)

/-- The used nodes after the first (`free = false`) or the free list (`free = true`) as a
`next`-linked chain: headers and tokens, and for the free list the whole buffer. -/
def Chain (CI : FAllocInv) (free : Bool) : List Ptr → Option Ptr → FAssn
  | [], none => FAssn.emp
  | N :: ns, some N' =>
    FAssn.ex fun A : Nat => FAssn.ex fun S : Nat => FAssn.ex fun K : BlockKind =>
    FAssn.ex fun sz : Nat => FAssn.ex fun ei : BitVec 64 => FAssn.ex fun nxt : Option Ptr =>
    FAssn.ex fun buf : Array Byte => FAssn.ex fun qn : Frac => FAssn.ex fun qh : Frac =>
      ⟪N = N' ∧ NodeFacts N A sz ∧ buf.size = (if free then sz - 24 else 0)⟫ ⋆
        (Header CI N A S K sz ei nxt qn qh ⋆ up (regionIn (N.add 24) A S K 1 buf) ⋆ Chain CI free ns nxt)
  | _, _ => ⟪False⟫

/-- The used nodes after the first. -/
def UsedRest (CI : FAllocInv) (nxt : Option Ptr) : FAssn := FAssn.ex fun ns => Chain CI false ns nxt

/-- The free list. -/
def FreeList (CI : FAllocInv) (fl : Option Ptr) : FAssn := FAssn.ex fun ns => Chain CI true ns fl

/-- The receipt the arena keeps for a grant `(p, n, q)` of epoch `e` (`EUpd.lendT`): the
fraction `q` of the extent of `p`'s block, lent at a bound that reaches the grant's end. -/
def rcptOf (γ e : Nat) : Option GRegion → FAssn
  | none => FAssn.emp
  | some (p, n, q) => FAssn.ex fun b => FAssn.ex fun k =>
      ⟪p.block = some b ∧ p.off.toNat + n ≤ k⟫ ⋆ brcpt b q k γ e

/-- One receipt per grant of the map (decision 1 of step 4, `docs/alloc-arena.md`). -/
def Rcpts (γ e : Nat) (M : GMap) : FAssn :=
  FAssn.ex fun N => ⟪∀ i, N ≤ i → M i = none⟫ ⋆ sepN N (fun i => rcptOf γ e (M i))

/-- Shares (tagged `t`) that frees gave back: they belong to the blocks of the arena's nodes and
go back to the child with the nodes. -/
def Pool (t : STag) : FAssn :=
  FAssn.ex fun n => FAssn.ex fun f : Nat → BlockId × Frac × Nat =>
    sepN n (fun j => bshare (f j).1 (f j).2.1 (f j).2.2 t)

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

theorem pool_add {t : STag} {b : BlockId} {q : Frac} {k : Nat} {r : Res}
    (h : (bshare b q k t ⋆ Pool t) r) : Pool t r := by
  obtain ⟨n, h⟩ := sep_exR h
  obtain ⟨f, h⟩ := sep_exR h
  refine ⟨n + 1, fun j => if j = n then (b, q, k) else f j, ?_⟩
  simp only [sepN, if_pos rfl]
  exact of_eq (congrArg _ (sepN_congr fun j hj => by simp [Nat.ne_of_lt hj])) h

/-- The arena's variables: the struct (`Ac`, `Sc`, `Kc`, `cbs`: the child allocator's bytes), the
lists' heads, the grant map `M`, and the first node (`nxt`, `A`, `S`, `K`, `sz`, `ei`, `tail`,
the token's fraction `qn` and the kept share `qh`; unused without one). -/
structure OV where
  Ac : Nat
  Sc : Nat
  Kc : BlockKind
  cbs : Array Byte
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

/-- The facts of the first node: none means no grant. -/
def OV.FirstFacts (w : OV) : Prop :=
  match w.first with
    | none => w.M = GMap.empty
    | some N => NodeFacts N w.A w.sz ∧ 24 + w.ei ≤ w.sz ∧ w.tail.size = w.sz - 24 - w.ei

/-- The facts of the arena's variables. -/
def OV.Facts (w : OV) : Prop := w.cbs.size = 16 ∧ w.M.Fin ∧ w.FirstFacts

/-- The first node of `used_list`: header, token and share, and the unused tail of its buffer. -/
def FirstPart (CI : FAllocInv) (w : OV) : FAssn :=
  match w.first with
  | none => FAssn.emp
  | some N => Header CI N w.A w.S w.K w.sz (BitVec.ofNat 64 w.ei) w.nxt w.qn w.qh ⋆
      up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail)

/-- The arena's resources. -/
def OV.body (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) (w : OV) : FAssn :=
  up (regionIn ctx w.Ac w.Sc w.Kc 8 w.cbs) ⋆ aptsE (ctx.add 16) w.first ⋆ aptsE (ctx.add 24) w.fl ⋆
    gauthP γ e w.M CI.tag ⋆ CI.own ⋆ Junk ⋆ Rcpts γ e w.M ⋆ Pool CI.tag ⋆ FirstPart CI w ⋆
    UsedRest CI w.nxt ⋆ FreeList CI w.fl

/-- The arena's state (module doc). -/
def own (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) : FAssn :=
  FAssn.ex fun w : OV => ⟪w.Facts⟫ ⋆ w.body CI γ e ctx

/-- The arena's invariant at epoch `e`: the token of a region is a ghost token of epoch `e` that
names it with the lent fraction; the grants' shares are tagged with the epoch, lent off the
nodes' shares (tagged like the child's grants: the ledger's parent is `CI.tag`). The arena's
state holds its ledger and the child's state, so it witnesses its tag (`act`). -/
def inv (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) : FAllocInv where
  own := own CI γ e ctx
  tok p n _ _ _ _ q := FAssn.ex fun i => gfrag γ e i (p, n, q)
  tag := some (γ, e)
  act r h := by
    obtain ⟨w, h⟩ := h
    obtain ⟨-, h⟩ := sep_lift.mp h
    exact act_gauthP (by within) h (CI.act_within (by within) h)

/-! ## `free` -/

/-- The variables of `free`'s precondition on an arena with a first node `N` (block `bN`), a
slice in block `bp` granted under id `i` with the fraction `q`, and the struct in block `bc`. -/
structure FV where
  w : OV
  i : Nat
  q : Frac
  N : Ptr
  bc : BlockId
  bN : BlockId
  bp : BlockId
  A' : Nat
  S' : Nat
  K' : BlockKind

section Free

variable (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) (s : Slice) (k : Nat) (bs : Array Byte)

def FV.Facts (v : FV) : Prop :=
  v.w.Facts ∧ v.w.first = some v.N ∧ ctx.block = some v.bc ∧ v.N.block = some v.bN ∧
    s.ptr.block = some v.bp ∧ (v.w.Ac + ctx.off.toNat) % 8 = 0 ∧ s.len.toNat = bs.size ∧
    0 < bs.size ∧ 0 ≤ ctx.off ∧ 0 ≤ s.ptr.off

/-- The atoms of `free`'s precondition. -/
def FV.gA (v : FV) : FAssn := gauthP γ e v.w.M CI.tag
def FV.uW (v : FV) : FAssn := aptsE (ctx.add 16) (some v.N)
def FV.eW (v : FV) (ei : Nat) : FAssn := apts (v.N.add 8) (BitVec.ofNat 64 ei)
def FV.nR (v : FV) : FAssn := up (regionIn (v.N.add 16) v.w.A v.w.S v.w.K 8 (Enc.encode v.w.nxt))
def FV.cR (v : FV) : FAssn := up (regionIn ctx v.w.Ac v.w.Sc v.w.Kc 8 v.w.cbs)
def FV.tR (v : FV) (ei : Nat) (tail : Array Byte) : FAssn :=
  up (regionIn (v.N.add (24 + ei)) v.w.A v.w.S v.w.K 1 tail)
def FV.rg (v : FV) : FAssn := up (regionIn s.ptr v.A' v.S' v.K' (2 ^ k) bs)
/-- The first node's token and kept share. -/
def FV.nS (v : FV) : FAssn :=
  CI.tok v.N v.w.sz 3 v.w.A v.w.S v.w.K v.w.qn ⋆ pshare v.N v.w.qh (v.N.off.toNat + v.w.sz) CI.tag
/-- What `free` does not touch. -/
def FV.F (v : FV) : FAssn :=
  apts v.N (BitVec.ofNat 64 v.w.sz) ⋆ v.nS CI ⋆ aptsE (ctx.add 24) v.w.fl ⋆ CI.own ⋆
    UsedRest CI v.w.nxt ⋆ FreeList CI v.w.fl
/-- The grant's share, the receipts and the pool. -/
def FV.xs (v : FV) : FAssn :=
  pshare s.ptr v.q (s.ptr.off.toNat + bs.size) (some (γ, e)) ⋆ Rcpts γ e v.w.M ⋆ Pool CI.tag

/-- What `free`'s steps do not change before the `cmpxchg`, besides the two words. -/
def FV.R0 (v : FV) : FAssn :=
  v.gA CI γ e ⋆ gfrag γ e v.i (s.ptr, bs.size, v.q) ⋆ v.nR ⋆ v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆
    v.rg s k bs ⋆ Junk ⋆ v.F CI ctx ⋆ v.xs CI γ e s bs

/-- `free`'s precondition: the two words it reads, then the rest. -/
def FV.L (v : FV) : FAssn := v.uW ctx ⋆ (v.eW v.w.ei ⋆ v.R0 CI γ e ctx s k bs)

end Free

theorem region_facts {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte} {r : Res}
    (h : up (regionIn p A S K a bs) r) : (∃ b, p.block = some b) ∧ (A + p.off.toNat) % a = 0 ∧
      0 ≤ p.off := by
  obtain ⟨⟨ha, -, b, hb, h0, -⟩, -⟩ := h
  exact ⟨⟨b, hb⟩, ha, h0⟩

section Free

variable {CI : FAllocInv} {γ e : Nat} {ctx : Ptr} {s : Slice} {k : Nat} {bs : Array Byte}

/-- `free`'s precondition in normal form. A token of the current epoch rules out an arena
without a node (O-A). -/
theorem free_pre {m : Mem} {r rF : Res} (hh : Holds m r rF) (hlen : s.len.toNat = bs.size)
    (hpos : 0 < bs.size) (hp : ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs) r) :
    (FAssn.ex fun v : FV => ⟪v.Facts ctx s bs⟫ ⋆ v.L CI γ e ctx s k bs) r := by
  obtain ⟨w, hp⟩ := sep_ex.mp hp
  obtain ⟨hwf, hp⟩ := sep_lift.mp (sep_assoc hp)
  obtain ⟨A', hp⟩ := sep_ex.mp (sep_comm hp)
  obtain ⟨S', hp⟩ := sep_ex.mp hp
  obtain ⟨K', hp⟩ := sep_ex.mp hp
  obtain ⟨q, hp⟩ := sep_ex.mp hp
  obtain ⟨i, hp⟩ := sep_ex.mp (of_eq (Q := (FAssn.ex fun i => gfrag γ e i (s.ptr, bs.size, q)) ⋆
    (up (regionIn s.ptr A' S' K' (2 ^ k) bs) ⋆
      pshare s.ptr q (s.ptr.off.toNat + bs.size) (some (γ, e)) ⋆ w.body CI γ e ctx))
    (by simp only [inv]; ac_rfl) hp)
  cases hfirst : w.first with
  | none =>
    exfalso
    have hn : w.M = GMap.empty := by have := hwf.2.2; unfold OV.FirstFacts at this; rw [hfirst] at this; exact this
    have hp' := of_eq (Q := (gauthP γ e w.M CI.tag ⋆ gfrag γ e i (s.ptr, bs.size, q)) ⋆
      (up (regionIn s.ptr A' S' K' (2 ^ k) bs) ⋆ pshare s.ptr q (s.ptr.off.toNat + bs.size) (some (γ, e)) ⋆
      up (regionIn ctx w.Ac w.Sc w.Kc 8 w.cbs) ⋆ aptsE (ctx.add 16) w.first ⋆ aptsE (ctx.add 24) w.fl ⋆
      CI.own ⋆ Junk ⋆ Rcpts γ e w.M ⋆ Pool CI.tag ⋆ FirstPart CI w ⋆ UsedRest CI w.nxt ⋆ FreeList CI w.fl))
      (by simp only [OV.body]; ac_rfl) hp
    obtain ⟨r₁, r₂, -, rfl, h1, -⟩ := hp'
    have := gfrag_mem h1 (Ghost.Ok.assoc.mp hh.ghost.1)
    rw [hn] at this; cases this
  | some N =>
    -- the shape with dummy block ids, to read the blocks off the regions
    have hL : ∀ bc bN bp, (FV.L CI γ e ctx s k bs ⟨w, i, q, N, bc, bN, bp, A', S', K'⟩) r := by
      intro bc bN bp
      refine of_eq ?_ hp
      simp only [OV.body, FirstPart, hfirst, Header, FV.L, FV.R0, FV.gA, FV.uW, FV.eW, FV.nR,
        FV.cR, FV.tR, FV.rg, FV.F, FV.nS, FV.xs]
      ac_rfl
    have h0 := hL 0 0 0
    unfold FV.L FV.R0 at h0
    obtain ⟨_, _, -, -, -, h1⟩ := h0
    obtain ⟨_, _, -, -, -, h2⟩ := h1
    obtain ⟨_, _, -, -, -, h3⟩ := h2
    obtain ⟨_, _, -, -, -, h4⟩ := h3
    obtain ⟨_, _, -, -, hn, h5⟩ := h4
    obtain ⟨_, _, -, -, hc, h6⟩ := h5
    obtain ⟨_, _, -, -, -, h7⟩ := h6
    obtain ⟨_, _, -, -, hg, -⟩ := h7
    obtain ⟨⟨bc, hbc⟩, hac, hc0⟩ := region_facts hc
    obtain ⟨⟨bN, hbN⟩, -, -⟩ := region_facts hn
    obtain ⟨⟨bp, hbp⟩, -, hp0⟩ := region_facts hg
    exact ⟨⟨w, i, q, N, bc, bN, bp, A', S', K'⟩, sep_lift.mpr ⟨⟨hwf, hfirst, hbc, by simpa [Ptr.add] using hbN,
      hbp, hac, hlen, hpos, hc0, hp0⟩, hL _ _ _⟩⟩

end Free

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

section FreeProof

variable {CI : FAllocInv} {γ e : Nat} {ctx : Ptr} {s : Slice} {k : Nat} {bs : Array Byte}

theorem encode_nxt_size (nxt : Option Ptr) : (Enc.encode nxt).size = 8 := LawfulEnc.size_encode nxt

/-- What the memory says about the blocks of `free`'s precondition: the struct's and the slice's
from owned bytes, the node's from its extent share (whose tag the child's state witnesses as
active, `FAllocInv.act`), and that two live blocks share no byte address. -/
theorem free_mem {v : FV} (hv : v.Facts ctx s bs) {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hp : v.L CI γ e ctx s k bs r) (hs : m.FSeq) :
    ∃ blkC blkN blkP, m.blocks[v.bc]? = some blkC ∧ blkC.addr = v.w.Ac ∧
      ctx.off.toNat + 16 ≤ blkC.bytes.size ∧
      m.blocks[v.bN]? = some blkN ∧ blkN.addr = v.w.A ∧ v.N.off.toNat + v.w.sz ≤ blkN.bytes.size ∧
      m.blocks[v.bp]? = some blkP ∧ blkP.addr = v.A' ∧ s.ptr.off.toNat + bs.size ≤ blkP.bytes.size ∧
      (v.bp ≠ v.bN → ∀ x x', x < blkN.bytes.size → x' < blkP.bytes.size → v.w.A + x ≠ v.A' + x') ∧
      (v.bp = v.bN → v.A' = v.w.A ∧ v.K'.norm = v.w.K.norm) := by
  obtain ⟨⟨hc16, -, -⟩, -, hbc, hbN, hbp, -, -, hpos, -⟩ := hv
  have hbN' : (v.N.add 16).block = some v.bN := by simpa [Ptr.add] using hbN
  have hoC : Owns v.bc (ctx.off.toNat + 15) v.w.Ac v.w.Kc (v.L CI γ e ctx s k bs) :=
    Owns.within (X := v.cR ctx) (Owns.region (a := 8) hbc (i := 15) (by omega)) (by within)
  have hoN : Owns v.bN ((v.N.add 16).off.toNat + 0) v.w.A v.w.K (v.L CI γ e ctx s k bs) :=
    Owns.within (X := v.nR) (Owns.region (a := 8) (bs := Enc.encode v.w.nxt) hbN' (i := 0)
      (by rw [encode_nxt_size]; omega)) (by within)
  have hoP : Owns v.bp (s.ptr.off.toNat + (bs.size - 1)) v.A' v.K' (v.L CI γ e ctx s k bs) :=
    Owns.within (X := v.rg s k bs) (Owns.region (a := 2 ^ k) hbp (i := bs.size - 1) (by omega)) (by within)
  obtain ⟨blkC, e1, -, x1, a1, -⟩ := hoC.block hh hp
  obtain ⟨blkN, e2, l2, -, a2, k2⟩ := hoN.block hh hp
  obtain ⟨blkP, e3, l3, x3, a3, k3⟩ := hoP.block hh hp
  obtain ⟨blkN', e2', -, s2, -⟩ := Holds.pshareW (p := v.N) (t := CI.tag) hh (by within) hp hbN
    (CI.act_within (by within) hp)
  rw [e2] at e2'; cases e2'
  refine ⟨blkC, blkN, blkP, e1, a1, by omega, e2, a2, s2, e3, a3, by omega,
    fun hne x x' hx hx' => ?_, fun heq => ?_⟩
  · rw [← a2, ← a3]; exact hs.2.2.addr_ne (Ne.symm hne) e2 e3 l2 l3 hx hx'
  · rw [heq, e2] at e3
    cases e3
    exact ⟨a3.symm.trans a2, k3.symm.trans k2⟩

/-- A slice whose end has the address of `buf + end_index` lies in the first node's buffer, right
before `end_index` (O-F: decided by ownership and the node's share, `region_apart`,
`Mem.LiveDisjoint.addr_ne`). -/
theorem last_facts {v : FV} (hv : v.Facts ctx s bs) (hnf : NodeFacts v.N v.w.A v.w.sz)
    (hei : 24 + v.w.ei ≤ v.w.sz)
    (heq : ((v.w.A : Int) + (v.N.off + 24 + v.w.ei)) = (v.A' : Int) + (s.ptr.off + bs.size))
    {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : v.L CI γ e ctx s k bs r) (hs : m.FSeq) :
    v.bp = v.bN ∧ v.A' = v.w.A ∧ v.K'.norm = v.w.K.norm ∧
      v.N.off.toNat + 24 ≤ s.ptr.off.toNat ∧
      s.ptr.off.toNat + bs.size = v.N.off.toNat + 24 + v.w.ei := by
  obtain ⟨-, -, -, hbN, hbp, -, -, hpos, -, hp0⟩ := id hv
  obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hap, hsame⟩ :=
    free_mem hv hh hp hs
  have h0 := hnf.off0
  by_cases hb : v.bp = v.bN
  · obtain ⟨hA, hK⟩ := hsame hb
    rw [hA] at heq
    have hoff : s.ptr.off.toNat + bs.size = v.N.off.toNat + 24 + v.w.ei := by omega
    have hr := of_eq (Q := (v.nR ⋆ v.rg s k bs) ⋆ (v.uW ctx ⋆ v.eW v.w.ei ⋆ v.gA CI γ e ⋆
      gfrag γ e v.i (s.ptr, bs.size, v.q) ⋆ v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆ Junk ⋆ v.F CI ctx ⋆
      v.xs CI γ e s bs))
      (by simp only [FV.L, FV.R0]; ac_rfl) hp
    obtain ⟨_, _, -, -, hr, -⟩ := hr
    have := region_apart (by simpa [Ptr.add] using hbN) (hb ▸ hbp)
      (by rw [encode_nxt_size]; decide) hpos hr
    rw [encode_nxt_size] at this
    simp only [Ptr.add] at this
    exact ⟨hb, hA, hK, by omega, hoff⟩
  · exact absurd (by omega) (hap hb (v.N.off.toNat + 24 + v.w.ei - 1) (s.ptr.off.toNat + bs.size - 1)
      (by omega) (by omega))

end FreeProof

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
theorem own_of {CI : FAllocInv} {γ e : Nat} {ctx : Ptr} {w : OV} (hw : w.Facts) {X : FAssn}
    {r : Res} (h : (w.body CI γ e ctx ⋆ X) r) : ((inv CI γ e ctx).own ⋆ X) r :=
  sep_mono_left (fun _ h => ⟨w, sep_lift.mpr ⟨hw, h⟩⟩) h

/-- A grant from its bytes, the token that names it and its share. -/
theorem granted_of {CI : FAllocInv} {γ e : Nat} {ctx p : Ptr} {k : Nat} {A S : Nat}
    {K : BlockKind} {i : Nat} {q : Frac} {bs : Array Byte} {r : Res}
    (h : (up (regionIn p A S K (2 ^ k) bs) ⋆ (gfrag γ e i (p, bs.size, q) ⋆
      pshare p q (p.off.toNat + bs.size) (some (γ, e)))) r) :
    (inv CI γ e ctx).granted p k bs r :=
  ⟨A, S, K, q, sep_mono_right (fun _ h => sep_mono_left (fun _ h => ⟨i, h⟩) h) h⟩

/-- The first `n` bytes of a region keep its alignment; the rest is a region of alignment 1. -/
theorem up_region_split {p : Ptr} {A S : Nat} {K : BlockKind} {a n : Nat} {bs : Array Byte}
    {r : Res} (hn : n ≤ bs.size) (h : up (regionIn p A S K a bs) r) :
    (up (regionIn p A S K a (bs.extract 0 n)) ⋆
      up (regionIn (p.add n) A S K 1 (bs.extract n bs.size))) r := by
  obtain ⟨h1, hk, hg⟩ := h
  exact up_sep ⟨regionIn_split h1 hn (Nat.mod_one _), hk, hg⟩

/-- The keeps-prefix relation of a shrink and of a growth. -/
theorem keepsPrefix_extract (bs : Array Byte) (n : Nat) : keepsPrefix bs (bs.extract 0 n) := by
  unfold keepsPrefix; simp [Array.extract_extract]; congr 1; omega

theorem keepsPrefix_append (bs ext : Array Byte) : keepsPrefix bs (bs ++ ext) := by
  unfold keepsPrefix; simp [Array.extract_eq_self_of_le (as := bs) (Nat.le_add_right _ _)]

/-- `free`'s precondition without the node's `size` word. -/
def FV.Lsz (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) (s : Slice) (k : Nat) (bs : Array Byte)
    (v : FV) : FAssn :=
  v.uW ctx ⋆ v.eW v.w.ei ⋆ v.gA CI γ e ⋆ gfrag γ e v.i (s.ptr, bs.size, v.q) ⋆ v.nR ⋆ v.cR ctx ⋆
    v.tR v.w.ei v.w.tail ⋆ v.rg s k bs ⋆ Junk ⋆ (v.nS CI ⋆ aptsE (ctx.add 24) v.w.fl ⋆ CI.own ⋆
    UsedRest CI v.w.nxt ⋆ FreeList CI v.w.fl) ⋆ v.xs CI γ e s bs

theorem FV.L_eq {CI : FAllocInv} {γ e : Nat} {ctx : Ptr} {s : Slice} {k : Nat} {bs : Array Byte}
    (v : FV) : v.L CI γ e ctx s k bs = (apts v.N (BitVec.ofNat 64 v.w.sz) ⋆ v.Lsz CI γ e ctx s k bs) := by
  simp only [FV.L, FV.R0, FV.F, FV.Lsz]; ac_rfl

/-! ## Ghost and extent updates of `free` and `resize`

A grant `(p, n, q)` of epoch `e` holds the share `q` tagged `(γ, e)`; the arena holds its receipt
(`Rcpts`). `free` gives the share back against exactly that receipt (`EUpd.returnT`) and keeps the
untagged-by-`γ` share in its pool; a shrink weakens the share's bound; a growth in the first node
returns the share, joins it into the node's and lends it again at the new end (`EUpd.lendT`). -/

section Glue

/-- A receipt for a grant also covers a shorter one. -/
theorem rcptOf_shrink {γ e : Nat} {p : Ptr} {n n' : Nat} {q : Frac} {r : Res} (hn : n' ≤ n)
    (h : rcptOf γ e (some (p, n, q)) r) : rcptOf γ e (some (p, n', q)) r := by
  obtain ⟨b, k, h⟩ := h
  obtain ⟨⟨hb, hk⟩, h⟩ := sep_lift.mp h
  exact ⟨b, k, sep_lift.mpr ⟨⟨hb, by omega⟩, h⟩⟩

/-- The receipts after a grant is re-pointed at a shorter region. -/
theorem rcpts_shrink {γ e i : Nat} {M : GMap} {p : Ptr} {n n' : Nat} {q : Frac} {r : Res}
    (hM : M i = some (p, n, q)) (hn : n' ≤ n) (h : Rcpts γ e M r) :
    Rcpts γ e (M.set i (some (p, n', q))) r := by
  have := rcpts_put (v := some (p, n', q)) (GMap.set_same M i none)
    (sep_mono_left (fun _ z => rcptOf_shrink hn z) (rcpts_pick hM h))
  rwa [GMap.set_set] at this

/-- The receipt of a grant, opened: its block and bound. -/
theorem open_rcpt {γ e i : Nat} {M : GMap} {p : Ptr} {n : Nat} {q : Frac} {t : Option (Nat × Nat)}
    {X : FAssn} {r : Res} (hM : M i = some (p, n, q))
    (h : (pshare p q (p.off.toNat + n) t ⋆ (Rcpts γ e M ⋆ X)) r) :
    ∃ b k, p.block = some b ∧ p.off.toNat + n ≤ k ∧
      ((bshare b q (p.off.toNat + n) t ⋆ brcpt b q k γ e) ⋆ (Rcpts γ e (M.set i none) ⋆ X)) r := by
  have h1 := sep_mono_right (R := (rcptOf γ e (some (p, n, q)) ⋆ Rcpts γ e (M.set i none)) ⋆ X)
    (fun _ x => sep_mono_left (Q := rcptOf γ e (some (p, n, q)) ⋆ Rcpts γ e (M.set i none))
      (fun _ y => rcpts_pick hM y) x) h
  have h2 := of_eq (Q := pshare p q (p.off.toNat + n) t ⋆ (rcptOf γ e (some (p, n, q)) ⋆
    (Rcpts γ e (M.set i none) ⋆ X))) (by ac_rfl) h1
  obtain ⟨b, h3⟩ := sep_ex.mp h2
  obtain ⟨hb, h3⟩ := sep_lift.mp (sep_assoc h3)
  obtain ⟨b', h4⟩ := sep_ex.mp (of_eq (sep_left_comm_eq _ _ _) h3)
  obtain ⟨k, h4⟩ := sep_ex.mp h4
  obtain ⟨⟨hb', hk⟩, h4⟩ := sep_lift.mp (sep_assoc h4)
  rw [hb] at hb'; cases hb'
  exact ⟨b, k, hb, hk, of_eq (by ac_rfl) h4⟩

/-- The grant's token names a grant of the map. -/
theorem grant_fact {γ e i : Nat} {M : GMap} {t : STag} {g : GRegion} {X : FAssn} :
    ∀ m r rF, Holds m r rF → (gauthP γ e M t ⋆ (gfrag γ e i g ⋆ X)) r → m.FSeq → M i = some g :=
  fun _ _ rF hh hp _ => by
    obtain ⟨r₁, r₂, -, rfl, h1, -⟩ := sep_assoc' hp
    exact gfrag_mem h1 (Ghost.Ok.assoc.mp hh.ghost.1)

/-- **`free`'s ghost part**: the share goes back against its receipt into the pool, the grant
is retired. -/
theorem free_ghost {γ e i : Nat} {M : GMap} {t : STag} {p : Ptr} {n : Nat} {q : Frac} :
    EUpd (gauthP γ e M t ⋆ (gfrag γ e i (p, n, q) ⋆ (pshare p q (p.off.toNat + n) (some (γ, e)) ⋆
      (Rcpts γ e M ⋆ Pool t))))
      (gauthP γ e (M.set i none) t ⋆ (Rcpts γ e (M.set i none) ⋆ Pool t)) := by
  refine EUpd.withFact grant_fact fun hM => ?_
  refine EUpd.trans (EUpd.of_imp (P' := FAssn.ex fun b => FAssn.ex fun k =>
      ⟪p.off.toNat + n ≤ k⟫ ⋆ ((gauthP γ e M t ⋆ (bshare b q (p.off.toNat + n) (some (γ, e)) ⋆
        brcpt b q k γ e)) ⋆ (gfrag γ e i (p, n, q) ⋆ (Rcpts γ e (M.set i none) ⋆ Pool t))))
      fun r h => ?_) (EUpd.exAll fun b => EUpd.exAll fun k => EUpd.lift fun hk => ?_)
  · obtain ⟨b, k, -, hk, h⟩ := open_rcpt (X := gauthP γ e M t ⋆ gfrag γ e i (p, n, q) ⋆ Pool t) hM
      (of_eq (Q := pshare p q (p.off.toNat + n) (some (γ, e)) ⋆ (Rcpts γ e M ⋆
        (gauthP γ e M t ⋆ gfrag γ e i (p, n, q) ⋆ Pool t))) (by ac_rfl) h)
    exact ⟨b, k, sep_lift.mpr ⟨hk, of_eq (by ac_rfl) h⟩⟩
  refine EUpd.trans (EUpd.frame (EUpd.returnT hk)) ?_
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ gfrag γ e i (p, n, q)) ⋆
    (bshare b q k t ⋆ (Rcpts γ e (M.set i none) ⋆ Pool t))) fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame (EUpd.of_upd Upd.retire)) ?_
  exact EUpd.of_imp fun _ h => sep_mono_right (fun _ x =>
    sep_mono_right (fun _ y => pool_add y) (of_eq (sep_left_comm_eq _ _ _) x)) h

/-- **A shrink's ghost part**: the share's bound comes down to the new end, the grant is
re-pointed; the receipt still covers it. -/
theorem shrink_ghost {γ e i : Nat} {M : GMap} {t : STag} {p : Ptr} {n n' : Nat} {q : Frac}
    (hn : n' ≤ n) :
    EUpd (gauthP γ e M t ⋆ (gfrag γ e i (p, n, q) ⋆ (pshare p q (p.off.toNat + n) (some (γ, e)) ⋆
      Rcpts γ e M)))
      (gauthP γ e (M.set i (some (p, n', q))) t ⋆ (gfrag γ e i (p, n', q) ⋆
        (pshare p q (p.off.toNat + n') (some (γ, e)) ⋆ Rcpts γ e (M.set i (some (p, n', q)))))) := by
  refine EUpd.withFact grant_fact fun hM => ?_
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ gfrag γ e i (p, n, q)) ⋆
    (pshare p q (p.off.toNat + n) (some (γ, e)) ⋆ Rcpts γ e (M.set i (some (p, n', q)))))
    fun _ h => sep_assoc' (sep_mono_right (fun _ x => sep_mono_right (fun _ y =>
      sep_mono_right (fun _ z => rcpts_shrink hM hn z) y) x) h)) ?_
  refine EUpd.trans (EUpd.frame (EUpd.of_upd (Upd.reassign (p, n', q)))) ?_
  refine EUpd.trans (EUpd.frameL (EUpd.frame (EUpd.pweaken (p := p) (k := p.off.toNat + n)
    (k' := p.off.toNat + n') (by omega)))) ?_
  exact EUpd.of_imp fun _ h => sep_assoc h

/-- **A growth's ghost part** (a grant in the node whose share `qh` at `kN` the arena keeps): the
share goes back against its receipt, joins the node's, and the same fraction is lent again at the
new end, with a receipt at `kN`. -/
theorem grow_ghost {γ e i : Nat} {M : GMap} {t : STag} {p N : Ptr} {n n' kN : Nat} {q qh : Frac}
    (hpN : p.block = N.block) (hk : p.off.toNat + n' ≤ kN) :
    EUpd (gauthP γ e M t ⋆ (gfrag γ e i (p, n, q) ⋆ (pshare p q (p.off.toNat + n) (some (γ, e)) ⋆
        (Rcpts γ e M ⋆ pshare N qh kN t))))
      (gauthP γ e (M.set i (some (p, n', q))) t ⋆ (gfrag γ e i (p, n', q) ⋆
        (pshare p q (p.off.toNat + n') (some (γ, e)) ⋆
          (Rcpts γ e (M.set i (some (p, n', q))) ⋆ pshare N qh kN t)))) := by
  refine EUpd.withFact grant_fact fun hM => ?_
  have hM' : (M.set i none) i = none := GMap.set_same M i none
  refine EUpd.trans (EUpd.of_imp (P' := FAssn.ex fun b => FAssn.ex fun k =>
      ⟪p.block = some b ∧ p.off.toNat + n ≤ k ∧ 0 < q.val ∧ 0 < qh.val⟫ ⋆
      ((gauthP γ e M t ⋆ (bshare b q (p.off.toNat + n) (some (γ, e)) ⋆ brcpt b q k γ e)) ⋆
        (bshare b qh kN t ⋆ (gfrag γ e i (p, n, q) ⋆ Rcpts γ e (M.set i none)))))
      fun r h => ?_) (EUpd.exAll fun b => EUpd.exAll fun k => EUpd.lift fun ⟨hb, hk', hq, hqh⟩ => ?_)
  · obtain ⟨b, k, hb, hk', h⟩ := open_rcpt (X := gauthP γ e M t ⋆ gfrag γ e i (p, n, q) ⋆
      pshare N qh kN t) hM (of_eq (by ac_rfl) h)
    have h := of_eq (Q := pshare N qh kN t ⋆ (bshare b q (p.off.toNat + n) (some (γ, e)) ⋆
      (brcpt b q k γ e ⋆ (gauthP γ e M t ⋆ gfrag γ e i (p, n, q) ⋆ Rcpts γ e (M.set i none)))))
      (by ac_rfl) h
    have hbN : N.block = some b := hpN ▸ hb
    obtain ⟨r₁, r₂, -, rfl, h1, h2⟩ := id h
    have hqh := ((pshare_iff hbN).mp h1).1
    obtain ⟨r₃, r₄, -, rfl, h3, -⟩ := id h2
    have hq := h3.1
    refine ⟨b, k, sep_lift.mpr ⟨⟨hb, hk', hq, hqh⟩, of_eq (by ac_rfl)
      (sep_mono_left (Q := bshare b qh kN t) (fun _ x => (pshare_iff hbN).mp x) h)⟩⟩
  refine EUpd.trans (EUpd.frame (EUpd.returnT hk')) ?_
  refine EUpd.trans (EUpd.of_imp (P' := (bshare b qh kN t ⋆ bshare b q k t) ⋆
    (gauthP γ e M t ⋆ (gfrag γ e i (p, n, q) ⋆ Rcpts γ e (M.set i none))))
    fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame EUpd.join) ?_
  refine EUpd.trans (EUpd.frame (EUpd.weaken (k' := kN) (Nat.le_max_left _ _))) ?_
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ bshare b q kN t) ⋆
    (bshare b qh kN t ⋆ (gfrag γ e i (p, n, q) ⋆ Rcpts γ e (M.set i none))))
    fun _ h => of_eq (by ac_rfl) (sep_mono_left (Q := bshare b qh kN t ⋆ bshare b q kN t)
      (fun _ x => (bshare_split hqh hq).mp x) h)) ?_
  refine EUpd.trans (EUpd.frame (EUpd.lendT hk)) ?_
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ gfrag γ e i (p, n, q)) ⋆
    (bshare b q (p.off.toNat + n') (some (γ, e)) ⋆ (rcptOf γ e (some (p, n', q)) ⋆
      Rcpts γ e (M.set i none) ⋆ bshare b qh kN t)))
    fun _ h => ?_) ?_
  · have h := of_eq (Q := brcpt b q kN γ e ⋆ ((gauthP γ e M t ⋆ gfrag γ e i (p, n, q)) ⋆
      (bshare b q (p.off.toNat + n') (some (γ, e)) ⋆ (Rcpts γ e (M.set i none) ⋆ bshare b qh kN t))))
      (by ac_rfl) h
    have h := sep_mono_left (Q := rcptOf γ e (some (p, n', q)))
      (fun _ x => ⟨b, kN, sep_lift.mpr ⟨⟨hb, hk⟩, x⟩⟩) h
    exact of_eq (by ac_rfl) h
  refine EUpd.trans (EUpd.frame (EUpd.of_upd (Upd.reassign (p, n', q)))) ?_
  refine EUpd.of_imp fun _ h => ?_
  have hbN : N.block = some b := hpN ▸ hb
  have h := of_eq (Q := rcptOf γ e (some (p, n', q)) ⋆ Rcpts γ e (M.set i none) ⋆
    ((gauthP γ e (M.set i (some (p, n', q))) t ⋆ gfrag γ e i (p, n', q)) ⋆
      bshare b q (p.off.toNat + n') (some (γ, e)) ⋆ bshare b qh kN t)) (by ac_rfl) h
  have h := sep_assoc' h
  have h := sep_mono_left (Q := Rcpts γ e ((M.set i none).set i (some (p, n', q)))) (fun _ x => rcpts_put hM' x) h
  rw [GMap.set_set] at h
  have h := of_eq (Q := bshare b q (p.off.toNat + n') (some (γ, e)) ⋆ (bshare b qh kN t ⋆
    (Rcpts γ e (M.set i (some (p, n', q))) ⋆ (gauthP γ e (M.set i (some (p, n', q))) t ⋆
      gfrag γ e i (p, n', q))))) (by ac_rfl) h
  have h := sep_mono_left (Q := pshare p q (p.off.toNat + n') (some (γ, e))) (fun _ x => (pshare_iff hb).mpr x) h
  have h := sep_mono_right (R := pshare N qh kN t ⋆ (Rcpts γ e (M.set i (some (p, n', q))) ⋆
    (gauthP γ e (M.set i (some (p, n', q))) t ⋆ gfrag γ e i (p, n', q))))
    (fun _ x => sep_mono_left (Q := pshare N qh kN t) (fun _ y => (pshare_iff hbN).mpr y) x) h
  exact of_eq (by ac_rfl) h

end Glue

/-! ## The ends of `free` and `resize`

Each branch of the entries ends in one of these updates from the precondition the code leaves
(the first node's `end_index` word as the `cmpxchg` left it) to the entry's postcondition. -/

section Ends

variable {CI : FAllocInv} {γ e : Nat} {ctx : Ptr} {s : Slice} {k : Nat} {bs : Array Byte}

/-- A grant from its bytes, the token that names it with `n` bytes and its share. -/
theorem granted_of_sz {ctx p : Ptr} {k n : Nat} {A S : Nat} {K : BlockKind} {i : Nat} {q : Frac}
    {bs : Array Byte} {r : Res} (hsz : bs.size = n)
    (h : (up (regionIn p A S K (2 ^ k) bs) ⋆ (gfrag γ e i (p, n, q) ⋆
      pshare p q (p.off.toNat + n) (some (γ, e)))) r) :
    (inv CI γ e ctx).granted p k bs r := by
  subst hsz; exact granted_of h

/-- `resize`'s postcondition `true` from the arena's variables and the new grant. -/
theorem resizePost_of {p : Ptr} {n : Nat} {w : OV} (hw : w.Facts) {bs' : Array Byte}
    (hsz : bs'.size = n) (hkp : keepsPrefix bs bs') {A S : Nat} {K : BlockKind} {i : Nat} {q : Frac}
    {r : Res} (h : (w.body CI γ e ctx ⋆ (up (regionIn p A S K (2 ^ k) bs') ⋆ (gfrag γ e i (p, n, q) ⋆
      pshare p q (p.off.toNat + n) (some (γ, e))))) r) :
    (inv CI γ e ctx).resizePost p k bs n true r :=
  own_of hw (sep_mono_right (fun _ h => ⟨bs', sep_lift.mpr ⟨⟨hsz, hkp⟩, granted_of_sz hsz h⟩⟩) h)

/-- `resize`'s postcondition `false`: nothing changed. -/
theorem resize_false_of {v : FV} (hv : v.Facts ctx s bs) (hfirst : v.w.first = some v.N)
    (hnf : NodeFacts v.N v.w.A v.w.sz) (hei : 24 + v.w.ei ≤ v.w.sz)
    (htail : v.w.tail.size = v.w.sz - 24 - v.w.ei) {n : Nat} {r : Res}
    (h : v.L CI γ e ctx s k bs r) : (inv CI γ e ctx).resizePost s.ptr k bs n false r := by
  obtain ⟨⟨hc16, hfin, -⟩, -⟩ := hv
  refine own_of (w := v.w) ⟨hc16, hfin, by simp only [OV.FirstFacts, hfirst]; exact ⟨hnf, hei, htail⟩⟩
    (sep_mono_right (fun _ x => granted_of x) (of_eq (Q := v.w.body CI γ e ctx ⋆
      (up (regionIn s.ptr v.A' v.S' v.K' (2 ^ k) bs) ⋆ (gfrag γ e v.i (s.ptr, bs.size, v.q) ⋆
        pshare s.ptr v.q (s.ptr.off.toNat + bs.size) (some (γ, e))))) ?_ h))
  simp only [OV.body, FirstPart, hfirst, Header, FV.L, FV.R0, FV.gA, FV.uW, FV.eW, FV.nR, FV.cR,
    FV.tR, FV.rg, FV.F, FV.nS, FV.xs]
  ac_rfl

/-- `free` of a slice that is not the first node's last allocation: its bytes leak to junk, its
share goes back into the pool, the grant is retired. -/
theorem free_other_upd {v : FV} (hv : v.Facts ctx s bs) (hfirst : v.w.first = some v.N)
    (hnf : NodeFacts v.N v.w.A v.w.sz) (hei : 24 + v.w.ei ≤ v.w.sz)
    (htail : v.w.tail.size = v.w.sz - 24 - v.w.ei) :
    EUpd (v.L CI γ e ctx s k bs) (inv CI γ e ctx).own := by
  obtain ⟨⟨hc16, hfin, -⟩, -⟩ := hv
  refine EUpd.trans (EUpd.of_imp (P' := (v.gA CI γ e ⋆ (gfrag γ e v.i (s.ptr, bs.size, v.q) ⋆
      (pshare s.ptr v.q (s.ptr.off.toNat + bs.size) (some (γ, e)) ⋆ (Rcpts γ e v.w.M ⋆ Pool CI.tag)))) ⋆
      ((v.rg s k bs ⋆ Junk) ⋆ (v.uW ctx ⋆ v.eW v.w.ei ⋆ v.nR ⋆ v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆
        v.F CI ctx)))
    fun _ h => of_eq (by simp only [FV.L, FV.R0, FV.xs]; ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame free_ghost) ?_
  refine EUpd.of_imp fun r h => ?_
  have h := sep_mono_right (R := Junk ⋆ (v.uW ctx ⋆ v.eW v.w.ei ⋆ v.nR ⋆ v.cR ctx ⋆
    v.tR v.w.ei v.w.tail ⋆ v.F CI ctx)) (fun _ x => sep_mono_left (Q := Junk) (fun _ y => junk_absorb y) x) h
  refine ⟨{ v.w with M := v.w.M.set v.i none }, sep_lift.mpr ⟨⟨hc16, hfin.set _ _, ?_⟩, of_eq ?_ h⟩⟩
  · simp only [OV.FirstFacts, hfirst]; exact ⟨hnf, hei, htail⟩
  · simp only [OV.body, FirstPart, hfirst, Header, FV.uW, FV.eW, FV.nR, FV.cR, FV.tR, FV.F, FV.nS]
    ac_rfl

/-- `free` of the first node's last allocation: `end_index` moved back; the slice's bytes (relabeled
as the node's, `EUpd.relabel`) rejoin the tail, its share goes back into the pool, the grant is
retired. -/
theorem free_last_upd {φ : Prop} {v : FV} {wv : BitVec 64} (hv : v.Facts ctx s bs)
    (hfirst : v.w.first = some v.N) (hnf : NodeFacts v.N v.w.A v.w.sz) (hei : 24 + v.w.ei ≤ v.w.sz)
    (htail : v.w.tail.size = v.w.sz - 24 - v.w.ei) (hb : v.bp = v.bN) (hA : v.A' = v.w.A)
    (hK : v.K'.norm = v.w.K.norm) (hoff : s.ptr.off.toNat + bs.size = v.N.off.toNat + 24 + v.w.ei)
    (hlo : v.N.off.toNat + 24 ≤ s.ptr.off.toNat) (hw : wv = BitVec.ofNat 64 (v.w.ei - bs.size)) :
    EUpd ((⟪φ⟫ ⋆ apts (v.N.add 8) wv) ⋆ (v.uW ctx ⋆ v.R0 CI γ e ctx s k bs)) (inv CI γ e ctx).own := by
  subst hw
  obtain ⟨⟨hc16, hfin, -⟩, -, -, hbN, hbp, -, -, -, -, -⟩ := hv
  refine EUpd.trans (EUpd.of_imp (P' := (v.gA CI γ e ⋆ (gfrag γ e v.i (s.ptr, bs.size, v.q) ⋆
      (pshare s.ptr v.q (s.ptr.off.toNat + bs.size) (some (γ, e)) ⋆ (Rcpts γ e v.w.M ⋆ Pool CI.tag)))) ⋆
      (v.rg s k bs ⋆ (apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei - bs.size)) ⋆ v.uW ctx ⋆ v.nR ⋆
        v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆ Junk ⋆ v.F CI ctx)))
    fun _ h => of_eq (by simp only [FV.R0, FV.xs]; ac_rfl)
      (sep_mono_left (Q := apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei - bs.size)))
        (fun _ x => (sep_lift.mp x).2) h)) ?_
  refine EUpd.trans (EUpd.frame free_ghost) ?_
  refine EUpd.trans (EUpd.frameL (EUpd.frame (EUpd.relabel (S' := v.w.S) hK.symm))) ?_
  refine EUpd.of_imp fun r h => ?_
  have hpq : s.ptr = v.N.add (24 + ((v.w.ei - bs.size : Nat) : Int)) := by
    have hb' : s.ptr.block = v.N.block := by rw [hbp, hbN, hb]
    have ho : s.ptr.off = v.N.off + (24 + ((v.w.ei - bs.size : Nat) : Int)) := by
      have := hnf.off0; omega
    rw [show s.ptr = ⟨s.ptr.block, s.ptr.off⟩ from rfl, hb', ho]; rfl
  have hjoin : ∀ r, (up (regionIn s.ptr v.A' v.w.S v.w.K (2 ^ k) bs) ⋆ v.tR v.w.ei v.w.tail) r →
      up (regionIn (v.N.add (24 + ((v.w.ei - bs.size : Nat) : Int))) v.w.A v.w.S v.w.K 1
        (bs ++ v.w.tail)) r := by
    intro r hr
    obtain ⟨⟨h₁, h₂, hd₁, he, x1, x2⟩, hk, hg⟩ := sep_up hr
    refine ⟨?_, hk, hg⟩
    rw [he, ← hpq]
    refine regionIn_join (a' := 1) ⟨h₁, h₂, hd₁, rfl, ?_, ?_⟩
    · rw [hA] at x1; exact regionIn_weaken x1 (Nat.one_dvd _)
    · have : s.ptr.add bs.size = v.N.add (24 + (v.w.ei : Int)) := by
        rw [hpq]; simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega
      rw [this]; exact x2
  have h' := of_eq (Q := (up (regionIn s.ptr v.A' v.w.S v.w.K (2 ^ k) bs) ⋆ v.tR v.w.ei v.w.tail) ⋆
    (gauthP γ e (v.w.M.set v.i none) CI.tag ⋆ Rcpts γ e (v.w.M.set v.i none) ⋆ Pool CI.tag ⋆
      apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei - bs.size)) ⋆ v.uW ctx ⋆ v.nR ⋆ v.cR ctx ⋆ Junk ⋆
      v.F CI ctx)) (by ac_rfl) h
  have h'' := sep_mono_left (Q := up (regionIn (v.N.add (24 + ((v.w.ei - bs.size : Nat) : Int)))
    v.w.A v.w.S v.w.K 1 (bs ++ v.w.tail))) hjoin h'
  refine ⟨{ v.w with M := v.w.M.set v.i none, ei := v.w.ei - bs.size, tail := bs ++ v.w.tail },
    sep_lift.mpr ⟨⟨hc16, hfin.set _ _, ?_⟩, of_eq ?_ h''⟩⟩
  · simp only [OV.FirstFacts, hfirst]
    exact ⟨hnf, by omega, by simp only [Array.size_append, htail]; have := hnf.hdr; omega⟩
  · simp only [OV.body, FirstPart, hfirst, Header, FV.uW, FV.nR, FV.cR, FV.F, FV.nS]
    ac_rfl

/-- `resize` of a slice that is not the first node's last allocation to `n ≤ len`: the cut bytes
leak to junk, the share's bound comes down, the grant is re-pointed. -/
theorem resize_other_upd {v : FV} (hv : v.Facts ctx s bs) (hfirst : v.w.first = some v.N)
    (hnf : NodeFacts v.N v.w.A v.w.sz) (hei : 24 + v.w.ei ≤ v.w.sz)
    (htail : v.w.tail.size = v.w.sz - 24 - v.w.ei) {n : Nat} (hle : n ≤ bs.size) :
    EUpd (v.L CI γ e ctx s k bs) ((inv CI γ e ctx).resizePost s.ptr k bs n true) := by
  obtain ⟨⟨hc16, hfin, -⟩, -⟩ := hv
  refine EUpd.trans (EUpd.of_imp (P' := (v.gA CI γ e ⋆ (gfrag γ e v.i (s.ptr, bs.size, v.q) ⋆
      (pshare s.ptr v.q (s.ptr.off.toNat + bs.size) (some (γ, e)) ⋆ Rcpts γ e v.w.M))) ⋆
      (v.rg s k bs ⋆ (Pool CI.tag ⋆ v.uW ctx ⋆ v.eW v.w.ei ⋆ v.nR ⋆ v.cR ctx ⋆
        v.tR v.w.ei v.w.tail ⋆ Junk ⋆ v.F CI ctx)))
    fun _ h => of_eq (by simp only [FV.L, FV.R0, FV.xs]; ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame (shrink_ghost hle)) ?_
  refine EUpd.of_imp fun r h => ?_
  have h := sep_mono_right (R := (up (regionIn s.ptr v.A' v.S' v.K' (2 ^ k) (bs.extract 0 n)) ⋆
      up (regionIn (s.ptr.add n) v.A' v.S' v.K' 1 (bs.extract n bs.size))) ⋆
      (Pool CI.tag ⋆ v.uW ctx ⋆ v.eW v.w.ei ⋆ v.nR ⋆ v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆ Junk ⋆ v.F CI ctx))
    (fun _ x => sep_mono_left (fun _ y => up_region_split hle y) x) h
  have h := of_eq (Q := ((up (regionIn (s.ptr.add n) v.A' v.S' v.K' 1 (bs.extract n bs.size)) ⋆ Junk) ⋆
    (up (regionIn s.ptr v.A' v.S' v.K' (2 ^ k) (bs.extract 0 n)) ⋆
      (gauthP γ e (v.w.M.set v.i (some (s.ptr, n, v.q))) CI.tag ⋆ (gfrag γ e v.i (s.ptr, n, v.q) ⋆
        (pshare s.ptr v.q (s.ptr.off.toNat + n) (some (γ, e)) ⋆ Rcpts γ e (v.w.M.set v.i (some (s.ptr, n, v.q)))))) ⋆
      (Pool CI.tag ⋆ v.uW ctx ⋆ v.eW v.w.ei ⋆ v.nR ⋆ v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆ v.F CI ctx))))
    (by ac_rfl) h
  have h := sep_mono_left (Q := Junk) (fun _ x => junk_absorb x) h
  have hsz : (bs.extract 0 n).size = n := by simp; omega
  refine resizePost_of (w := { v.w with M := v.w.M.set v.i (some (s.ptr, n, v.q)) })
    ⟨hc16, hfin.set _ _, by simp only [OV.FirstFacts, hfirst]; exact ⟨hnf, hei, htail⟩⟩ hsz
    (keepsPrefix_extract _ _) (A := v.A') (S := v.S') (K := v.K') (i := v.i) (q := v.q) (of_eq ?_ h)
  simp only [OV.body, FirstPart, hfirst, Header, FV.uW, FV.eW, FV.nR, FV.cR, FV.tR, FV.F, FV.nS]
  ac_rfl

/-- `resize` of the first node's last allocation to `n ≤ len`: `end_index` moved back; the cut
bytes (relabeled as the node's) rejoin the tail, the share's bound comes down, the grant is
re-pointed. -/
theorem resize_shrink_upd {φ : Prop} {v : FV} {wv : BitVec 64} (hv : v.Facts ctx s bs)
    (hfirst : v.w.first = some v.N) (hnf : NodeFacts v.N v.w.A v.w.sz) (hei : 24 + v.w.ei ≤ v.w.sz)
    (htail : v.w.tail.size = v.w.sz - 24 - v.w.ei) (hb : v.bp = v.bN) (hA : v.A' = v.w.A)
    (hK : v.K'.norm = v.w.K.norm) (hoff : s.ptr.off.toNat + bs.size = v.N.off.toNat + 24 + v.w.ei)
    (hlo : v.N.off.toNat + 24 ≤ s.ptr.off.toNat) {n : Nat} (hle : n ≤ bs.size)
    (hw : wv = BitVec.ofNat 64 (v.w.ei - (bs.size - n))) :
    EUpd ((⟪φ⟫ ⋆ apts (v.N.add 8) wv) ⋆ (v.uW ctx ⋆ v.R0 CI γ e ctx s k bs))
      ((inv CI γ e ctx).resizePost s.ptr k bs n true) := by
  subst hw
  obtain ⟨⟨hc16, hfin, -⟩, -, -, hbN, hbp, -, -, -, -, hp0⟩ := hv
  have h0 := hnf.off0
  have hlenei : bs.size ≤ v.w.ei := by omega
  refine EUpd.trans (EUpd.of_imp (P' := (v.gA CI γ e ⋆ (gfrag γ e v.i (s.ptr, bs.size, v.q) ⋆
      (pshare s.ptr v.q (s.ptr.off.toNat + bs.size) (some (γ, e)) ⋆ Rcpts γ e v.w.M))) ⋆
      (v.rg s k bs ⋆ (Pool CI.tag ⋆ apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei - (bs.size - n))) ⋆
        v.uW ctx ⋆ v.nR ⋆ v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆ Junk ⋆ v.F CI ctx)))
    fun _ h => of_eq (by simp only [FV.R0, FV.xs]; ac_rfl)
      (sep_mono_left (Q := apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei - (bs.size - n))))
        (fun _ x => (sep_lift.mp x).2) h)) ?_
  refine EUpd.trans (EUpd.frame (shrink_ghost hle)) ?_
  refine EUpd.trans (EUpd.frameL (EUpd.frame (EUpd.relabel (S' := v.w.S) hK.symm))) ?_
  refine EUpd.of_imp fun r h => ?_
  -- the cut bytes `[n, len)` lie right before the tail
  have hcut : s.ptr.add n = v.N.add (24 + ((v.w.ei - (bs.size - n) : Nat) : Int)) := by
    have hb' : s.ptr.block = v.N.block := by rw [hbp, hbN, hb]
    have ho : s.ptr.off + n = v.N.off + (24 + ((v.w.ei - (bs.size - n) : Nat) : Int)) := by omega
    simp only [Ptr.add]; rw [hb', ho]
  have hjoin : ∀ r, (up (regionIn (s.ptr.add n) v.A' v.w.S v.w.K 1 (bs.extract n bs.size)) ⋆
      v.tR v.w.ei v.w.tail) r →
      up (regionIn (v.N.add (24 + ((v.w.ei - (bs.size - n) : Nat) : Int))) v.w.A v.w.S v.w.K 1
        (bs.extract n bs.size ++ v.w.tail)) r := by
    intro r hr
    obtain ⟨⟨h₁, h₂, hd₁, he, x1, x2⟩, hk, hg⟩ := sep_up hr
    refine ⟨?_, hk, hg⟩
    rw [he, ← hcut]
    refine regionIn_join (a' := 1) ⟨h₁, h₂, hd₁, rfl, ?_, ?_⟩
    · rw [hA] at x1; exact x1
    · have : (s.ptr.add n).add (bs.extract n bs.size).size = v.N.add (24 + (v.w.ei : Int)) := by
        rw [hcut]; simp only [Ptr.add, Array.size_extract, Ptr.mk.injEq, true_and]; omega
      rw [this]; exact x2
  have h := sep_mono_right (R := (up (regionIn s.ptr v.A' v.w.S v.w.K (2 ^ k) (bs.extract 0 n)) ⋆
      up (regionIn (s.ptr.add n) v.A' v.w.S v.w.K 1 (bs.extract n bs.size))) ⋆
      (Pool CI.tag ⋆ apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei - (bs.size - n))) ⋆
        v.uW ctx ⋆ v.nR ⋆ v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆ Junk ⋆ v.F CI ctx))
    (fun _ x => sep_mono_left (fun _ y => up_region_split hle y) x) h
  have h := of_eq (Q := (up (regionIn (s.ptr.add n) v.A' v.w.S v.w.K 1 (bs.extract n bs.size)) ⋆
      v.tR v.w.ei v.w.tail) ⋆
    (up (regionIn s.ptr v.A' v.w.S v.w.K (2 ^ k) (bs.extract 0 n)) ⋆
      (gauthP γ e (v.w.M.set v.i (some (s.ptr, n, v.q))) CI.tag ⋆ (gfrag γ e v.i (s.ptr, n, v.q) ⋆
        (pshare s.ptr v.q (s.ptr.off.toNat + n) (some (γ, e)) ⋆ Rcpts γ e (v.w.M.set v.i (some (s.ptr, n, v.q)))))) ⋆
      (Pool CI.tag ⋆ apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei - (bs.size - n))) ⋆
        v.uW ctx ⋆ v.nR ⋆ v.cR ctx ⋆ Junk ⋆ v.F CI ctx)))
    (by ac_rfl) h
  have h := sep_mono_left (Q := up (regionIn (v.N.add (24 + ((v.w.ei - (bs.size - n) : Nat) : Int)))
    v.w.A v.w.S v.w.K 1 (bs.extract n bs.size ++ v.w.tail))) hjoin h
  have hsz : (bs.extract 0 n).size = n := by simp; omega
  refine resizePost_of (w := { v.w with M := v.w.M.set v.i (some (s.ptr, n, v.q)), ei := v.w.ei - (bs.size - n), tail := bs.extract n bs.size ++ v.w.tail })
    ⟨hc16, hfin.set _ _, by
      simp only [OV.FirstFacts, hfirst]
      exact ⟨hnf, by omega, by simp only [Array.size_append, Array.size_extract, htail]; omega⟩⟩
    hsz (keepsPrefix_extract _ _) (A := v.A') (S := v.w.S) (K := v.w.K) (i := v.i) (q := v.q) (of_eq ?_ h)
  simp only [OV.body, FirstPart, hfirst, Header, FV.uW, FV.nR, FV.cR, FV.F, FV.nS]
  ac_rfl

/-- `resize` of the first node's last allocation into the tail (`len ≤ n`, room in the tail):
`end_index` moved forward; the slice (relabeled as the node's) takes the first bytes of the tail;
its share is returned, joined into the node's and lent again at the new end
(`grow_ghost`); the grant is re-pointed. -/
theorem resize_grow_upd {v : FV} {wv : BitVec 64} (hv : v.Facts ctx s bs)
    (hfirst : v.w.first = some v.N) (hnf : NodeFacts v.N v.w.A v.w.sz) (hei : 24 + v.w.ei ≤ v.w.sz)
    (htail : v.w.tail.size = v.w.sz - 24 - v.w.ei) (hb : v.bp = v.bN) (hA : v.A' = v.w.A)
    (hK : v.K'.norm = v.w.K.norm) (hoff : s.ptr.off.toNat + bs.size = v.N.off.toNat + 24 + v.w.ei)
    {n : Nat} (hlt : bs.size ≤ n) (hfit : n - bs.size ≤ v.w.sz - 24 - v.w.ei)
    (hw : wv = BitVec.ofNat 64 (v.w.ei + (n - bs.size))) :
    EUpd (apts (v.N.add 8) wv ⋆ (v.uW ctx ⋆ v.R0 CI γ e ctx s k bs))
      ((inv CI γ e ctx).resizePost s.ptr k bs n true) := by
  subst hw
  obtain ⟨⟨hc16, hfin, -⟩, -, -, hbN, hbp, -, -, -, -, hp0⟩ := hv
  have h0 := hnf.off0
  have hpN : s.ptr.block = v.N.block := by rw [hbp, hbN, hb]
  refine EUpd.trans (EUpd.of_imp (P' := (v.gA CI γ e ⋆ (gfrag γ e v.i (s.ptr, bs.size, v.q) ⋆
      (pshare s.ptr v.q (s.ptr.off.toNat + bs.size) (some (γ, e)) ⋆ (Rcpts γ e v.w.M ⋆
        pshare v.N v.w.qh (v.N.off.toNat + v.w.sz) CI.tag)))) ⋆
      (v.rg s k bs ⋆ (Pool CI.tag ⋆ apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei + (n - bs.size))) ⋆
        v.uW ctx ⋆ v.nR ⋆ v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆ Junk ⋆ apts v.N (BitVec.ofNat 64 v.w.sz) ⋆
        CI.tok v.N v.w.sz 3 v.w.A v.w.S v.w.K v.w.qn ⋆ aptsE (ctx.add 24) v.w.fl ⋆ CI.own ⋆
        UsedRest CI v.w.nxt ⋆ FreeList CI v.w.fl)))
    fun _ h => of_eq (by simp only [FV.R0, FV.xs, FV.F, FV.nS]; ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame (grow_ghost (n' := n) (kN := v.N.off.toNat + v.w.sz) hpN (by omega))) ?_
  refine EUpd.trans (EUpd.frameL (EUpd.frame (EUpd.relabel (S' := v.w.S) hK.symm))) ?_
  refine EUpd.of_imp fun r h => ?_
  -- the slice grows into the first `n - len` bytes of the tail
  have hend : s.ptr.add bs.size = v.N.add (24 + (v.w.ei : Int)) := by
    have ho : s.ptr.off + bs.size = v.N.off + (24 + (v.w.ei : Int)) := by omega
    simp only [Ptr.add]; rw [hpN, ho]
  have hnt : (v.N.add (24 + (v.w.ei : Int))).add ((n - bs.size : Nat) : Int) =
      v.N.add (24 + ((v.w.ei + (n - bs.size) : Nat) : Int)) := by
    simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega
  have hgrow : ∀ r, (up (regionIn s.ptr v.A' v.w.S v.w.K (2 ^ k) bs) ⋆ v.tR v.w.ei v.w.tail) r →
      (up (regionIn s.ptr v.A' v.w.S v.w.K (2 ^ k) (bs ++ v.w.tail.extract 0 (n - bs.size))) ⋆
        up (regionIn (v.N.add (24 + ((v.w.ei + (n - bs.size) : Nat) : Int))) v.w.A v.w.S v.w.K
          1 (v.w.tail.extract (n - bs.size) v.w.tail.size))) r := by
    intro r hr
    have h1 := sep_assoc' (sep_mono_right (Q := v.tR v.w.ei v.w.tail)
      (R := up (regionIn (v.N.add (24 + (v.w.ei : Int))) v.w.A v.w.S v.w.K 1
          (v.w.tail.extract 0 (n - bs.size))) ⋆
        up (regionIn ((v.N.add (24 + (v.w.ei : Int))).add ((n - bs.size : Nat) : Int)) v.w.A v.w.S v.w.K 1
          (v.w.tail.extract (n - bs.size) v.w.tail.size)))
      (fun _ x => up_region_split (bs := v.w.tail) (n := n - bs.size) (by omega) x) hr)
    rw [hnt] at h1
    refine sep_mono_left (fun r x => ?_) h1
    obtain ⟨⟨h₁, h₂, hd₁, he, x1, x2⟩, hk, hg⟩ := sep_up x
    refine ⟨?_, hk, hg⟩
    rw [he]
    rw [← hend, ← hA] at x2
    exact regionIn_join (a' := 1) ⟨h₁, h₂, hd₁, rfl, x1, x2⟩
  have h := of_eq (Q := (up (regionIn s.ptr v.A' v.w.S v.w.K (2 ^ k) bs) ⋆ v.tR v.w.ei v.w.tail) ⋆
    (gauthP γ e (v.w.M.set v.i (some (s.ptr, n, v.q))) CI.tag ⋆ (gfrag γ e v.i (s.ptr, n, v.q) ⋆
      (pshare s.ptr v.q (s.ptr.off.toNat + n) (some (γ, e)) ⋆ (Rcpts γ e (v.w.M.set v.i (some (s.ptr, n, v.q))) ⋆
        pshare v.N v.w.qh (v.N.off.toNat + v.w.sz) CI.tag))) ⋆
      (Pool CI.tag ⋆ apts (v.N.add 8) (BitVec.ofNat 64 (v.w.ei + (n - bs.size))) ⋆
        v.uW ctx ⋆ v.nR ⋆ v.cR ctx ⋆ Junk ⋆ apts v.N (BitVec.ofNat 64 v.w.sz) ⋆
        CI.tok v.N v.w.sz 3 v.w.A v.w.S v.w.K v.w.qn ⋆ aptsE (ctx.add 24) v.w.fl ⋆ CI.own ⋆
        UsedRest CI v.w.nxt ⋆ FreeList CI v.w.fl))) (by ac_rfl) h
  have h := sep_mono_left hgrow h
  have hsz : (bs ++ v.w.tail.extract 0 (n - bs.size)).size = n := by simp; omega
  refine resizePost_of (w := { v.w with M := v.w.M.set v.i (some (s.ptr, n, v.q)), ei := v.w.ei + (n - bs.size), tail := v.w.tail.extract (n - bs.size) v.w.tail.size })
    ⟨hc16, hfin.set _ _, by
      simp only [OV.FirstFacts, hfirst]
      exact ⟨hnf, by omega, by simp only [Array.size_extract, htail]; omega⟩⟩
    hsz (keepsPrefix_append _ _) (A := v.A') (S := v.w.S) (K := v.w.K) (i := v.i) (q := v.q) (of_eq ?_ h)
  simp only [OV.body, FirstPart, hfirst, Header, FV.uW, FV.nR, FV.cR]
  ac_rfl

end Ends

/-! ## Proof tactics of the entries

Each is elaborated against the code of the module where it is used. The names it refers to are
that module's (`heap_ArenaAllocator_*`, `debug_assert_true`, `loadBuf_ct`, `resize_ct`) and the
statement's (`CI`, `γ`, `e`, `ctx`, `s`, `k`, `n`, `bs`, `hlen`, `hpos`, `hn`). -/

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
(`f` is the entry). -/
macro "arena_prefix" f:ident : tactic => `(tactic| (
  refine CTriple.preM (fun m r rF hh hp hs => free_pre hh hlen hpos hp) ?_
  refine CTriple.ex fun v => CTriple.lift fun hv => ?_
  have hv' := hv
  obtain ⟨⟨hc16, hfin, hwf⟩, hfirst, hbc, hbN, hbp, hac, -, -, hc0, hp0⟩ := hv'
  unfold OV.FirstFacts at hwf
  rw [hfirst] at hwf
  obtain ⟨hnf, hei, htail⟩ := hwf
  have hmem := fun m r rF (hh : Holds m r rF) hp hs => free_mem (CI := CI) (γ := γ) (e := e) (k := k) hv hh hp hs
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
  refine CTriple.pre (P := apts v.N (BitVec.ofNat 64 v.w.sz) ⋆ v.Lsz CI γ e ctx s k bs) ?_
    (fun r h => of_eq (FV.L_eq v) h)
  refine CTriple.bind (loadBuf_ct (R := v.Lsz CI γ e ctx s k bs) hbN hnf.off0 hnf.hdr hnf.even
    (by have := hnf.small; omega) (fun m r rF hh hp hs => ?_))
    fun sl => CTriple.lift fun hsl => ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh (of_eq (FV.L_eq v).symm hp) hs
    exact ⟨blkN, e2, s2⟩
  subst hsl
  refine CTriple.pre (P := v.L CI γ e ctx s k bs) ?_ (fun r h => of_eq (FV.L_eq v).symm h)
  conc_norm
  have hgt : decide ((BitVec.ofNat 64 (v.w.sz - 24)).toNat < (BitVec.ofNat 64 v.w.ei).toNat) = false := by
    rw [hei64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hnf.small; omega)]
    simp only [decide_eq_false_iff_not, Nat.not_lt]; omega
  simp only [hgt, Bool.false_eq_true, ↓reduceIte]
))

/-- `free` from the comparison of `buf_ptr + end_index` with the slice's end. -/
macro "arena_free_tail" : tactic => `(tactic| (
  -- `buf_ptr + end_index`, `memory.ptr + memory.len`, and their comparison
  refine CTriple.pureStep (v := (v.N.add 24).add v.w.ei) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, -⟩ := hmem m r rF hh hp hs
    have := hnf.off0
    rw [ptrProject_elem_run (by simpa [Ptr.add] using hbN) e2 (by simp [Ptr.add]; omega)
      (by simp [Ptr.add, hei64]; omega), hei64]
  refine CTriple.pureStep (v := s.ptr.add bs.size) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, -⟩ := hmem m r rF hh hp hs
    rw [ptrProject_elem_run hbp e3 hp0 (by omega), hlen]
  refine CTriple.pureStep (v := !decide (((v.w.A : Int) + (v.N.off + 24 + v.w.ei)) =
    (v.A' : Int) + (s.ptr.off + bs.size))) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, -⟩ := hmem m r rF hh hp hs
    have := hnf.off0
    rw [StateT.run_bind, ptrEqAddr_run (q := s.ptr.add bs.size) (by simpa [Ptr.add] using hbN) e2
      (by simpa [Ptr.add] using hbp) e3, a2, a3]
    simp only [Ptr.add, pure_bind, StateT.run_pure]
    congr 4
  by_cases heq : ((v.w.A : Int) + (v.N.off + 24 + v.w.ei)) = (v.A' : Int) + (s.ptr.off + bs.size)
  · simp only [heq, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    -- the slice is the last allocation of the first node (O-F: decided by ownership)
    refine CTriple.facts (fun m r rF hh hp hs => last_facts hv hnf hei heq hh hp hs) ?_
    rintro ⟨hb, hA, hK, hlo, hoff⟩
    have hle : s.len.toNat ≤ (BitVec.ofNat 64 v.w.ei).toNat := by rw [hei64, hlen]; omega
    have hd : (BitVec.ofNat 64 v.w.ei - s.len).toNat = v.w.ei - bs.size := by
      rw [BitVec.toNat_sub_of_le hle, hei64, hlen]
    rw [Zig.sub_unsigned_of_le hle]
    conc_norm
    -- `buf_ptr + new_end_index == memory.ptr`
    refine CTriple.pureStep (v := (v.N.add 24).add (v.w.ei - bs.size : Nat))
      (fun m r rF hh hp hs => ?_) ?_
    · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
      have := hnf.off0
      rw [ptrProject_elem_run (by simpa [Ptr.add] using hbN) e2 (by simp [Ptr.add]; omega)
        (by simp [Ptr.add, hd]; omega), hd]
    refine CTriple.pureStep (v := true) (fun m r rF hh hp hs => ?_) ?_
    · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -⟩ := hmem m r rF hh hp hs
      have := hnf.off0
      rw [ptrEqAddr_run (by simpa [Ptr.add] using hbN) e2 hbp e3, a2, a3, hA]
      have : (v.w.A : Int) + (v.N.add 24 |>.add (v.w.ei - bs.size : Nat)).off = v.w.A + s.ptr.off := by
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
    refine CTriple.pre (P := v.eW v.w.ei ⋆ (v.uW ctx ⋆ v.R0 CI γ e ctx s k bs)) ?_
      (fun r h => of_eq (sep_left_comm_eq _ _ _) h)
    refine CTriple.bind (CTriple.liftMem ((FTriple.cmpxchgHit (v.N.add 8) (BitVec.ofNat 64 v.w.ei)
      (BitVec.ofNat 64 v.w.ei - s.len) _ _).frame)) fun _ => ?_
    have hnew : BitVec.ofNat 64 v.w.ei - s.len = BitVec.ofNat 64 (v.w.ei - bs.size) := by
      apply BitVec.eq_of_toNat_eq; rw [hd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      have := hnf.small; omega
    refine CTriple.eupd (free_last_upd hv hfirst hnf hei htail hb hA hK hoff hlo hnew) ?_
    exact CTriple.ret' () fun _ h => h
  · -- not the last allocation: the slice leaks to the arena
    simp only [heq, decide_false, Bool.not_false, ↓reduceIte]
    refine CTriple.eupd (free_other_upd hv hfirst hnf hei htail) ?_
    exact CTriple.ret' () fun _ h => h))

/-- `resize` from the comparison of `buf_ptr + end_index` with the slice's end. -/
macro "arena_resize_tail" : tactic => `(tactic| (
  -- `buf_ptr + end_index`, `memory.ptr + memory.len`, and their comparison
  refine CTriple.pureStep (v := (v.N.add 24).add v.w.ei) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, -⟩ := hmem m r rF hh hp hs
    have := hnf.off0
    rw [ptrProject_elem_run (by simpa [Ptr.add] using hbN) e2 (by simp [Ptr.add]; omega)
      (by simp [Ptr.add, hei64]; omega), hei64]
  refine CTriple.pureStep (v := s.ptr.add bs.size) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, -⟩ := hmem m r rF hh hp hs
    rw [ptrProject_elem_run hbp e3 hp0 (by omega), hlen]
  refine CTriple.pureStep (v := !decide (((v.w.A : Int) + (v.N.off + 24 + v.w.ei)) =
    (v.A' : Int) + (s.ptr.off + bs.size))) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -, -⟩ := hmem m r rF hh hp hs
    have := hnf.off0
    rw [StateT.run_bind, ptrEqAddr_run (q := s.ptr.add bs.size) (by simpa [Ptr.add] using hbN) e2
      (by simpa [Ptr.add] using hbp) e3, a2, a3]
    simp only [Ptr.add, pure_bind, StateT.run_pure]
    congr 4
  by_cases heq : ((v.w.A : Int) + (v.N.off + 24 + v.w.ei)) = (v.A' : Int) + (s.ptr.off + bs.size)
  · simp only [heq, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    -- the slice is the last allocation of the first node
    refine CTriple.facts (fun m r rF hh hp hs => last_facts hv hnf hei heq hh hp hs) ?_
    rintro ⟨hb, hA, hK, hlo, hoff⟩
    have hbN' : (v.N.add 24).block = some v.bN := by simpa [Ptr.add] using hbN
    have h0 := hnf.off0
    have hsm := hnf.small
    have hlenei : bs.size ≤ v.w.ei := by omega
    simp only [Ops.le_eq, hlen]
    by_cases hle : n.toNat ≤ bs.size
    · -- shrink: `end_index` moves back by `len - n`; the cut bytes rejoin the tail
      simp only [hle, decide_true, ↓reduceIte]
      have h1 : n.toNat ≤ s.len.toNat := by rw [hlen]; exact hle
      have hd1 : (s.len - n).toNat = bs.size - n.toNat := by rw [BitVec.toNat_sub_of_le h1, hlen]
      have h2 : (s.len - n).toNat ≤ (BitVec.ofNat 64 v.w.ei).toNat := by rw [hd1, hei64]; omega
      have hd2 : (BitVec.ofNat 64 v.w.ei - (s.len - n)).toNat = v.w.ei - (bs.size - n.toNat) := by
        rw [BitVec.toNat_sub_of_le h2, hei64, hd1]
      rw [Zig.sub_unsigned_of_le h1]
      conc_norm
      rw [Zig.sub_unsigned_of_le h2]
      conc_norm
      refine CTriple.pureStep (v := (v.N.add 24).add (v.w.ei - (bs.size - n.toNat) : Nat))
        (fun m r rF hh hp hs => ?_) ?_
      · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
        rw [ptrProject_elem_run hbN' e2 (by simp [Ptr.add]; omega) (by simp [Ptr.add, hd2]; omega), hd2]
      refine CTriple.pureStep (v := s.ptr.add n.toNat) (fun m r rF hh hp hs => ?_) ?_
      · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -⟩ := hmem m r rF hh hp hs
        rw [ptrProject_elem_run hbp e3 hp0 (by omega)]
      refine CTriple.pureStep (v := true) (fun m r rF hh hp hs => ?_) ?_
      · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -⟩ := hmem m r rF hh hp hs
        rw [ptrEqAddr_run (by simpa [Ptr.add] using hbN) e2 (by simpa [Ptr.add] using hbp) e3, a2, a3, hA]
        have hx : (v.w.A : Int) + (v.N.off + 24 + ((v.w.ei - (bs.size - n.toNat) : Nat) : Int)) =
            v.w.A + (s.ptr.off + n.toNat) := by omega
        simp only [Ptr.add, hx, decide_true]
      rw [debug_assert_true]
      conc_norm
      refine CTriple.pureStep (v := v.N.add 8) (fun m r rF hh hp hs => ?_) ?_
      · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
        exact ptrProject_add_run' hbN e2 hnf.off0 (by decide) (by omega)
      refine CTriple.pick_bind ?_
      refine CTriple.pre (P := v.eW v.w.ei ⋆ (v.uW ctx ⋆ v.R0 CI γ e ctx s k bs)) ?_
        (fun r h => of_eq (sep_left_comm_eq _ _ _) h)
      refine CTriple.bind (CTriple.liftMem ((FTriple.cmpxchgHit (v.N.add 8) (BitVec.ofNat 64 v.w.ei)
        (BitVec.ofNat 64 v.w.ei - (s.len - n)) _ _).frame)) fun _ => ?_
      have hnew : BitVec.ofNat 64 v.w.ei - (s.len - n) =
          BitVec.ofNat 64 (v.w.ei - (bs.size - n.toNat)) := by
        apply BitVec.eq_of_toNat_eq; rw [hd2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
      refine CTriple.eupd (resize_shrink_upd hv hfirst hnf hei htail hb hA hK hoff hlo hle hnew) ?_
      exact CTriple.ret' true fun _ h => h
    · -- growth into the tail, when the tail has room
      simp only [hle, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hlt : s.len.toNat ≤ n.toNat := by rw [hlen]; omega
      have hd : (n - s.len).toNat = n.toNat - bs.size := by rw [BitVec.toNat_sub_of_le hlt, hlen]
      refine CTriple.pre (P := apts v.N (BitVec.ofNat 64 v.w.sz) ⋆ v.Lsz CI γ e ctx s k bs) ?_
        (fun r h => of_eq (FV.L_eq v) h)
      refine CTriple.bind (loadBuf_ct (R := v.Lsz CI γ e ctx s k bs) hbN hnf.off0 hnf.hdr hnf.even
        (by have := hnf.small; omega) (fun m r rF hh hp hs => ?_)) fun sl => CTriple.lift fun hsl => ?_
      · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh (of_eq (FV.L_eq v).symm hp) hs
        exact ⟨blkN, e2, s2⟩
      subst hsl
      refine CTriple.pre (P := v.L CI γ e ctx s k bs) ?_ (fun r h => of_eq (FV.L_eq v).symm h)
      rw [Zig.sub_unsigned_of_le hlt]
      conc_norm
      have hroom : (Zig.subSat false (BitVec.ofNat 64 (v.w.sz - 24)) (BitVec.ofNat 64 v.w.ei)).toNat =
          v.w.sz - 24 - v.w.ei := by
        rw [Zig.subSat_unsigned_toNat, hei64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [Zig.ge, Ops.le_eq, hroom, hd]
      by_cases hfit : n.toNat - bs.size ≤ v.w.sz - 24 - v.w.ei
      · simp only [hfit, decide_true, ↓reduceIte]
        have hadd : (BitVec.ofNat 64 v.w.ei).toNat + (n - s.len).toNat < 2 ^ 64 := by
          rw [hei64, hd]; omega
        have hd2 : (BitVec.ofNat 64 v.w.ei + (n - s.len)).toNat = v.w.ei + (n.toNat - bs.size) := by
          rw [BitVec.toNat_add_of_lt hadd, hei64, hd]
        rw [Zig.add_unsigned_of_lt hadd]
        conc_norm
        refine CTriple.pureStep (v := (v.N.add 24).add (v.w.ei + (n.toNat - bs.size) : Nat))
          (fun m r rF hh hp hs => ?_) ?_
        · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
          rw [ptrProject_elem_run hbN' e2 (by simp [Ptr.add]; omega) (by simp [Ptr.add, hd2]; omega), hd2]
        refine CTriple.pureStep (v := s.ptr.add n.toNat) (fun m r rF hh hp hs => ?_) ?_
        · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
          rw [ptrProject_elem_run (hb ▸ hbp) e2 hp0 (by omega)]
        refine CTriple.pureStep (v := true) (fun m r rF hh hp hs => ?_) ?_
        · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -⟩ := hmem m r rF hh hp hs
          rw [ptrEqAddr_run (by simpa [Ptr.add] using hbN) e2 (by simpa [Ptr.add] using hbp) e3, a2, a3, hA]
          have hx : (v.w.A : Int) + (v.N.off + 24 + ((v.w.ei + (n.toNat - bs.size) : Nat) : Int)) =
              v.w.A + (s.ptr.off + n.toNat) := by omega
          simp only [Ptr.add, hx, decide_true]
        rw [debug_assert_true]
        conc_norm
        refine CTriple.pureStep (v := v.N.add 8) (fun m r rF hh hp hs => ?_) ?_
        · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
          exact ptrProject_add_run' hbN e2 hnf.off0 (by decide) (by omega)
        refine CTriple.pick_bind ?_
        refine CTriple.pre (P := v.eW v.w.ei ⋆ (v.uW ctx ⋆ v.R0 CI γ e ctx s k bs)) ?_
          (fun r h => of_eq (sep_left_comm_eq _ _ _) h)
        refine CTriple.bind (CTriple.liftMem ((FTriple.cmpxchgHit (v.N.add 8) (BitVec.ofNat 64 v.w.ei)
          (BitVec.ofNat 64 v.w.ei + (n - s.len)) _ _).frame)) fun res => ?_
        refine CTriple.pre (CTriple.lift (P := apts (v.N.add 8) (BitVec.ofNat 64 v.w.ei + (n - s.len)) ⋆
          (v.uW ctx ⋆ v.R0 CI γ e ctx s k bs)) fun hres => ?_) (fun r h => sep_assoc h)
        subst hres
        simp only [Option.isNone_none]
        have hnew : BitVec.ofNat 64 v.w.ei + (n - s.len) = BitVec.ofNat 64 (v.w.ei + (n.toNat - bs.size)) := by
          apply BitVec.eq_of_toNat_eq; rw [hd2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
        refine CTriple.eupd (resize_grow_upd hv hfirst hnf hei htail hb hA hK hoff (by omega) hfit hnew) ?_
        exact CTriple.ret' true fun _ h => h
      · simp only [hfit, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact CTriple.ret' false fun _ h => resize_false_of hv hfirst hnf hei htail h
  · -- not the first node's last allocation: only a shrink succeeds; the cut bytes become junk
    simp only [heq, decide_false, Bool.not_false, ↓reduceIte, Ops.le_eq, hlen]
    by_cases hle : n.toNat ≤ bs.size
    · simp only [hle, decide_true]
      refine CTriple.eupd (resize_other_upd hv hfirst hnf hei htail hle) ?_
      exact CTriple.ret' true fun _ h => h
    · simp only [hle, decide_false]
      exact CTriple.ret' false fun _ h => resize_false_of hv hfirst hnf hei htail h))

/-- `remap` is `resize`, and returns `memory.ptr` when it succeeds (`resize_ct`). -/
macro "arena_remap" : tactic => `(tactic| (
  unfold heap_ArenaAllocator_remap
  conc_norm
  refine CTriple.bind (resize_ct CI γ e ctx s k n ra bs hlen hpos hn) fun b => ?_
  cases b <;> exact CTriple.ret' _ fun _ h => h))

/-- `free` of the stock arena. -/
macro "arena_free" : tactic => `(tactic| (arena_prefix heap_ArenaAllocator_free; arena_free_tail))

/-- `free` of the patched arena: the bounds check first. -/
macro "arena_free_checked" : tactic =>
  `(tactic| (arena_prefix heap_ArenaAllocator_free; arena_bounds; arena_free_tail))

/-- `resize` of the stock arena. -/
macro "arena_resize" : tactic => `(tactic| (arena_prefix heap_ArenaAllocator_resize; arena_resize_tail))

/-- `resize` of the patched arena: the bounds check first. -/
macro "arena_resize_checked" : tactic =>
  `(tactic| (arena_prefix heap_ArenaAllocator_resize; arena_bounds; arena_resize_tail))

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
theorem free_ct (CI : FAllocInv) (γ e : Nat) (ctx s : _) (k : Nat) (ra : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (heap_ArenaAllocator_free ctx s ⟨BitVec.ofNat 6 k⟩ ra) (fun _ => (inv CI γ e ctx).own) := by
  $freeT:tactic)),
    (← `(command|
/-- **`free` meets `FAllocSpec`'s `free` field** for the arena invariant at every epoch, every
child invariant `CI`, and every depth of the one-thread reading (`Sched.soloRun`). -/
theorem free_spec (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (ra : BitVec 64) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (Sched.soloRun fuel (heap_ArenaAllocator_free ctx s ⟨BitVec.ofNat 6 k⟩ ra))
      (fun _ => (inv CI γ e ctx).own) :=
  free_ct CI γ e ctx s k ra bs hlen hpos fuel)),
    (← `(command|
/-- `resize`'s run, case by case: a slice that is not the first node's last one only shrinks (its
cut bytes become junk); the last one moves `end_index` (shrink, or growth into the tail when it
fits). A successful resize re-points the grant at the new length (`Upd.reassign`). -/
theorem resize_ct (CI : FAllocInv) (γ e : Nat) (ctx s : _) (k : Nat) (n ra : BitVec 64)
    (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) (hn : 0 < n.toNat) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (heap_ArenaAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((inv CI γ e ctx).resizePost s.ptr k bs n.toNat) := by
  $resizeT:tactic)),
    (← `(command|
/-- `remap` is `resize`, and returns `memory.ptr` when it succeeds. -/
theorem remap_ct (CI : FAllocInv) (γ e : Nat) (ctx s : _) (k : Nat) (n ra : BitVec 64)
    (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) (hn : 0 < n.toNat) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (heap_ArenaAllocator_remap ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((inv CI γ e ctx).remapPost s.ptr k bs n.toNat) := by
  arena_remap)),
    (← `(command|
/-- **`resize` meets `FAllocSpec`'s `resize` field** for the arena invariant at every epoch, every
child invariant `CI`, and every depth of the one-thread reading. -/
theorem resize_spec (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (n ra : BitVec 64) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size)
    (hn : 0 < n.toNat) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (Sched.soloRun fuel (heap_ArenaAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra))
      ((inv CI γ e ctx).resizePost s.ptr k bs n.toNat) :=
  resize_ct CI γ e ctx s k n ra bs hlen hpos hn fuel)),
    (← `(command|
/-- **`remap` meets `FAllocSpec`'s `remap` field.** -/
theorem remap_spec (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (n ra : BitVec 64) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size)
    (hn : 0 < n.toNat) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (Sched.soloRun fuel (heap_ArenaAllocator_remap ctx s ⟨BitVec.ofNat 6 k⟩ n ra))
      ((inv CI γ e ctx).remapPost s.ptr k bs n.toNat) :=
  remap_ct CI γ e ctx s k n ra bs hlen hpos hn fuel))]⟩

end AllocArena.Core
