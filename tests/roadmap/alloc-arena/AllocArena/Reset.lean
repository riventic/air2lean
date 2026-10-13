import AllocArena.Core

/-!
# The translated `ArenaAllocator`: `reset`'s ghost part

`reset` (every mode) needs the arena's state with no grant outstanding, which the whole epoch token
shows (`own_epTok_empty`, the reset ledger `ZigLean/Sep/Full/ResetLedger.lean`). From there the
arena's resources are rearranged, without running code, into `Released`: the ledger at the next
epoch with that epoch's whole token, and **both lists as lists of whole nodes** (`FreeList`: a
node's header, its whole buffer, the child's token, the node's whole extent share and whole claim),
which is what the code then gives back to the child (`free` of each node) or keeps as the next
epoch's nodes (`reset_release`). Like `Core`, this layer does not mention the generated code.

* Shares: the nodes' kept parts, the pool and the grants' receipts regroup into each node's whole
  share (`reset_shares`); with no grant the receipts are empty.
* Claims: each used node's lent buffer claim reverts to it (`cls_revoke`), so the arena holds every
  used node's whole claim. Two claims of one active world on one byte are invalid, so the used
  nodes are pairwise disjoint (`freeCl_pairwise`).
* Bytes: with no grant every byte of a used node's buffer is junk or the first node's tail
  (`OV.Cov`, `cov_rest`, `cov_first`); the junk of each buffer becomes a region with the node's
  labels (`EUpd.junkRegion`, `chainH_junk`), and the first node's joins its tail.
-/

namespace AllocArena.Core

open Zig Zig.Region Zig.Full Zig.Full.FAssn

/-! ## `reset`'s release: the nodes as whole nodes -/

/-- A node's header without its share: the `size` and `end_index` words, the `next` pointer and
the child's token. -/
def HeadH (CI : Child) (nd : NodeV) (ei : BitVec 64) (nxt : Option Ptr) : FAssn :=
  wpts nd.N (BitVec.ofNat 64 nd.sz) ⋆ wpts (nd.N.add 8) ei ⋆
    up (regionIn (nd.N.add 16) nd.A nd.S nd.K 8 (Enc.encode nxt)) ⋆
    CI.ntok nd.N nd.sz 3 nd.A nd.S nd.K nd.qn

theorem header_eq (CI : Child) (nd : NodeV) (ei : BitVec 64) (nxt : Option Ptr) (qh : Frac) :
    Header CI nd.N nd.A nd.S nd.K nd.sz ei nxt nd.qn qh =
      (HeadH CI nd ei nxt ⋆ pshare nd.N qh (nd.N.off.toNat + nd.sz) CI.tag) := by
  simp only [Header, HeadH]; ac_rfl

/-- The nodes `ns` as a `next`-linked chain from `N'` without their extent shares: headers,
tokens, and the buffers (whole for `free = true`, empty for the used nodes). -/
def ChainH (CI : Child) (free : Bool) : List NodeV → Option Ptr → FAssn
  | [], none => FAssn.emp
  | nd :: ns, some N' =>
    FAssn.ex fun ei : BitVec 64 => FAssn.ex fun nxt : Option Ptr => FAssn.ex fun buf : Array Byte =>
      ⟪nd.N = N' ∧ NodeFacts nd.N nd.A nd.sz ∧ buf.size = (if free then nd.sz - 24 else 0)⟫ ⋆
        (HeadH CI nd ei nxt ⋆ up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf) ⋆ ChainH CI free ns nxt)
  | _, _ => ⟪False⟫

/-- A chain is its chain without shares and the nodes' kept shares. -/
theorem chain_split {CI : Child} {free : Bool} :
    ∀ {ns : List NodeV} {nxt : Option Ptr} {r : Res}, Chain CI free ns nxt r →
      (ChainH CI free ns nxt ⋆ NodeShares CI.tag NodeV.qh ns) r
  | [], none, _, h => sep_emp.mpr h
  | [], some _, _, h => h.1.elim
  | _ :: _, none, _, h => h.1.elim
  | nd :: ns, some N', r, h => by
    obtain ⟨ei, nx, buf, h⟩ := h
    obtain ⟨hf, h⟩ := sep_lift.mp h
    rw [header_eq] at h
    have h := of_eq (Q := (pshare nd.N nd.qh (nd.N.off.toNat + nd.sz) CI.tag ⋆
      (HeadH CI nd ei nx ⋆ up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf))) ⋆ Chain CI free ns nx)
      (by ac_rfl) h
    have h := sep_mono_right (R := ChainH CI free ns nx ⋆ NodeShares CI.tag NodeV.qh ns)
      (fun _ z => chain_split z) h
    show ((FAssn.ex fun ei : BitVec 64 => FAssn.ex fun nxt : Option Ptr =>
      FAssn.ex fun buf : Array Byte => ⟪nd.N = N' ∧ NodeFacts nd.N nd.A nd.sz ∧
        buf.size = (if free then nd.sz - 24 else 0)⟫ ⋆
        (HeadH CI nd ei nxt ⋆ up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf) ⋆
          ChainH CI free ns nxt)) ⋆
        (pshare nd.N nd.qh (nd.N.off.toNat + nd.sz) CI.tag ⋆ NodeShares CI.tag NodeV.qh ns)) r
    exact sep_ex.mpr ⟨ei, sep_ex.mpr ⟨nx, sep_ex.mpr ⟨buf,
      sep_assoc' (sep_lift.mpr ⟨hf, of_eq (by ac_rfl) h⟩)⟩⟩⟩

/-- A chain without shares and the nodes' whole shares are a chain of nodes that keep their whole
share. -/
theorem chain_join {CI : Child} {free : Bool} :
    ∀ {ns : List NodeV} {nxt : Option Ptr} {r : Res},
      (ChainH CI free ns nxt ⋆ NodeShares CI.tag NodeV.qn ns) r →
      Chain CI free (ns.map NodeV.full) nxt r
  | [], none, _, h => sep_emp.mp h
  | [], some _, _, h => by obtain ⟨_, _, -, -, h, -⟩ := h; exact h.1.elim
  | _ :: _, none, _, h => by obtain ⟨_, _, -, -, h, -⟩ := h; exact h.1.elim
  | nd :: ns, some N', r, h => by
    have h : ((FAssn.ex fun ei : BitVec 64 => FAssn.ex fun nxt : Option Ptr =>
      FAssn.ex fun buf : Array Byte => ⟪nd.N = N' ∧ NodeFacts nd.N nd.A nd.sz ∧
        buf.size = (if free then nd.sz - 24 else 0)⟫ ⋆
        (HeadH CI nd ei nxt ⋆ up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf) ⋆
          ChainH CI free ns nxt)) ⋆
        (pshare nd.N nd.qn (nd.N.off.toNat + nd.sz) CI.tag ⋆ NodeShares CI.tag NodeV.qn ns)) r := h
    obtain ⟨ei, h⟩ := sep_ex.mp h
    obtain ⟨nx, h⟩ := sep_ex.mp h
    obtain ⟨buf, h⟩ := sep_ex.mp h
    obtain ⟨hf, h⟩ := sep_lift.mp (sep_assoc h)
    have h := of_eq (Q := (pshare nd.N nd.qn (nd.N.off.toNat + nd.sz) CI.tag ⋆
      (HeadH CI nd ei nx ⋆ up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf))) ⋆
        (ChainH CI free ns nx ⋆ NodeShares CI.tag NodeV.qn ns)) (by ac_rfl) h
    have h := sep_mono_right (R := Chain CI free (ns.map NodeV.full) nx) (fun _ z => chain_join z) h
    refine ⟨ei, nx, buf, sep_lift.mpr ⟨hf, ?_⟩⟩
    have e := header_eq CI nd.full ei nx nd.full.qh
    simp only [NodeV.full] at e ⊢
    rw [e]
    simp only [HeadH] at h ⊢
    exact of_eq (by ac_rfl) h

/-- Two nodes in one block do not overlap. -/
def NodeDisj (a c : NodeV) : Prop :=
  ∀ b, a.N.block = some b → c.N.block = some b →
    a.N.off.toNat + a.sz ≤ c.N.off.toNat ∨ c.N.off.toNat + c.sz ≤ a.N.off.toNat

/-- Junk covering a node's buffer: every byte of `[N + 24, N + sz)` of its block. -/
def JunkCovers (hj : Heap) (nd : NodeV) : Prop :=
  ∀ b, nd.N.block = some b → Zig.Covers b (nd.N.off.toNat + 24) (nd.N.off.toNat + nd.sz) hj

/-- Cutting bytes of another node out of the junk keeps the coverage of a disjoint node. -/
theorem JunkCovers.cutIn {hj : Heap} {nd nd' : NodeV} {b : BlockId} {lo hi : Nat}
    (hc : JunkCovers hj nd') (hb : nd.N.block = some b) (hd : NodeDisj nd nd')
    (hlo : nd.N.off.toNat ≤ lo) (hhi : hi ≤ nd.N.off.toNat + nd.sz) :
    JunkCovers (hj.cut b lo hi) nd' := by
  intro b' hb' i h1 h2
  unfold Heap.cut
  split
  · rename_i hc'
    obtain ⟨he, h3, h4⟩ := hc'
    simp only at he
    subst he
    rcases hd _ hb hb' with e | e <;> omega
  · exact hc b' hb' i h1 h2

/-- Cutting another node's buffer out of the junk keeps the coverage of a disjoint node. -/
theorem JunkCovers.cut {hj : Heap} {nd nd' : NodeV} {b : BlockId} (hc : JunkCovers hj nd')
    (hb : nd.N.block = some b) (hd : NodeDisj nd nd') :
    JunkCovers (hj.cut b (nd.N.off.toNat + 24) (nd.N.off.toNat + nd.sz)) nd' :=
  hc.cutIn hb hd (by omega) (Nat.le_refl _)

/-- A free-list node's claim is among the claims of its list. -/
theorem freeCl_within {CI : Child} {nd : NodeV} :
    ∀ {ns : List NodeV}, nd ∈ ns →
      Within (pclaim nd.N nd.N.off.toNat (nd.N.off.toNat + nd.sz) CI.tag) (FreeCl CI ns)
  | [], h => absurd h List.not_mem_nil
  | nd' :: ns, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Within.sepL (Within.refl _)
    · exact Within.sepR (freeCl_within h)

/-- **The nodes whose whole claims are held are pairwise disjoint** (`Holds.bclaim_disjoint`):
two claims of one active world on one byte are invalid (decision O1). -/
theorem freeCl_pairwise {CI : Child} {m : Mem} {rF : Res} :
    ∀ {ns : List NodeV} {R : FAssn} {r : Res}, Holds m r rF → (FreeCl CI ns ⋆ R) r →
      Act r.gh.ls CI.tag → (∀ nd ∈ ns, 0 < nd.sz) → ns.Pairwise NodeDisj
  | [], _, _, _, _, _, _ => List.Pairwise.nil
  | nd :: ns, R, r, hh, h, ha, hsz => by
    have h : (FreeCl CI ns ⋆ (pclaim nd.N nd.N.off.toNat (nd.N.off.toNat + nd.sz) CI.tag ⋆ R)) r :=
      of_eq (by simp only [FreeCl]; ac_rfl) h
    refine List.Pairwise.cons (fun nd' hm b hb hb' => ?_)
      (freeCl_pairwise hh h ha fun x hx => hsz x (List.mem_cons_of_mem _ hx))
    obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := h
    obtain ⟨R', h1⟩ := freeCl_within (CI := CI) hm r₁ h1
    have h3 : ((pclaim nd'.N nd'.N.off.toNat (nd'.N.off.toNat + nd'.sz) CI.tag ⋆ R') ⋆
        (pclaim nd.N nd.N.off.toNat (nd.N.off.toNat + nd.sz) CI.tag ⋆ R)) _ :=
      ⟨r₁, r₂, hd, rfl, h1, h2⟩
    have h3 := of_eq (Q := pclaim nd.N nd.N.off.toNat (nd.N.off.toNat + nd.sz) CI.tag ⋆
      (pclaim nd'.N nd'.N.off.toNat (nd'.N.off.toNat + nd'.sz) CI.tag ⋆ (R' ⋆ R))) (by ac_rfl) h3
    obtain ⟨ra, rb, hdab, he, ⟨b₁, ha'⟩, hrb⟩ := h3
    obtain ⟨hb₁, ha'⟩ := sep_lift.mp ha'
    obtain ⟨rc, rd, hdcd, rfl, ⟨b₂, hc'⟩, hrd⟩ := hrb
    obtain ⟨hb₂, hc'⟩ := sep_lift.mp hc'
    rw [hb] at hb₁; cases hb₁
    rw [hb'] at hb₂; cases hb₂
    have := hh.bclaim_disjoint (R := R' ⋆ R) ⟨ra, _, hdab, he, ha', rc, rd, hdcd, rfl, hc', hrd⟩ ha
    have h1 := hsz nd (List.mem_cons_self ..)
    have h2 := hsz nd' (List.mem_cons_of_mem _ hm)
    omega

/-- The node's `next` word is owned with the node's labels. -/
theorem headH_owns {CI : Child} {nd : NodeV} {ei : BitVec 64} {nx : Option Ptr} {b : BlockId}
    {R : FAssn} (hb : nd.N.block = some b) :
    Owns b ((nd.N.add 16).off.toNat + 0) nd.A nd.K (HeadH CI nd ei nx ⋆ R) :=
  Owns.within (X := up (regionIn (nd.N.add 16) nd.A nd.S nd.K 8 (Enc.encode nx)))
    (Owns.region (a := 8) (by simpa [Ptr.add] using hb) (by rw [encode_nxt_size]; omega))
    (by unfold HeadH; within)

/-- The facts of a chain's nodes: `NodeFacts` and a block. -/
theorem chainH_facts {CI : Child} {free : Bool} :
    ∀ {ns : List NodeV} {nxt : Option Ptr} {r : Res}, ChainH CI free ns nxt r →
      ∀ nd ∈ ns, NodeFacts nd.N nd.A nd.sz ∧ ∃ b, nd.N.block = some b
  | [], _, _, _ => fun _ h => absurd h List.not_mem_nil
  | _ :: _, none, _, h => fun _ _ => h.1.elim
  | nd :: ns, some N', r, h => fun nd' hm => by
    obtain ⟨ei, nx, buf, h⟩ := h
    obtain ⟨⟨-, hnf, -⟩, h⟩ := sep_lift.mp h
    obtain ⟨_, _, -, -, h1, h2⟩ := h
    rcases List.mem_cons.mp hm with rfl | hm
    · unfold HeadH at h1
      obtain ⟨_, _, -, -, -, h3⟩ := h1
      obtain ⟨_, _, -, -, -, h4⟩ := h3
      obtain ⟨_, _, -, -, h5, -⟩ := h4
      obtain ⟨⟨-, -, b, hb, -⟩, -⟩ := h5
      exact ⟨hnf, b, by simpa [Ptr.add] using hb⟩
    · obtain ⟨_, _, -, -, -, h3⟩ := h2
      exact chainH_facts h3 nd' hm

/-- A header's node has a block, and its kind is not a `const` global's (its `next` word). -/
theorem headH_block {CI : Child} {nd : NodeV} {ei : BitVec 64} {nx : Option Ptr} {R : FAssn}
    {r : Res} (h : (HeadH CI nd ei nx ⋆ R) r) : (∃ b, nd.N.block = some b) ∧ nd.K ≠ .constGlobal := by
  obtain ⟨_, _, -, -, h1, -⟩ := h
  unfold HeadH at h1
  obtain ⟨_, _, -, -, -, h3⟩ := h1
  obtain ⟨_, _, -, -, -, h4⟩ := h3
  obtain ⟨_, _, -, -, h5, -⟩ := h4
  obtain ⟨⟨-, hK, b, hb, -⟩, -⟩ := h5
  exact ⟨⟨b, by simpa [Ptr.add] using hb⟩, hK⟩

/-- With no grant, the junk covers the buffers of the used nodes after the first (the first
node's tail is disjoint from them). -/
theorem cov_rest {w : OV} {N : Ptr} (hw : w.Facts) (hM : w.M = GMap.empty) (hf : w.first = some N)
    (hpw : w.nodes.Pairwise NodeDisj) : ∀ nd ∈ w.rest, JunkCovers w.jh nd := by
  intro nd hnd b hb x h1 h2
  simp only [OV.nodes, hf] at hpw
  have hc := hw.2.2.2.2.2 nd (by simp only [OV.nodes, hf]; exact List.mem_cons_of_mem _ hnd) b x
    ⟨hb, h1, h2⟩
  rcases hc with h | ⟨i, h⟩ | h
  · exact h
  · rw [hM] at h; exact h.elim
  · obtain ⟨hb', h3, h4⟩ := OV.InTail.of_first hf h
    rcases List.rel_of_pairwise_cons hpw hnd b hb' hb with e | e <;> simp only [OV.node] at e <;> omega

/-- With no grant, the junk covers the first node's buffer before its tail. -/
theorem cov_first {w : OV} {N : Ptr} {b : BlockId} (hw : w.Facts) (hM : w.M = GMap.empty)
    (hf : w.first = some N) (hb : N.block = some b) :
    Zig.Covers b (N.off.toNat + 24) (N.off.toNat + 24 + w.ei) w.jh := by
  intro x h1 h2
  have hff := hw.2.1
  simp only [OV.FirstFacts, hf] at hff
  have hc := hw.2.2.2.2.2 (w.node N) (by simp only [OV.nodes, hf]; exact List.mem_cons_self ..) b x
    ⟨hb, h1, by simp only [OV.node]; omega⟩
  rcases hc with h | ⟨i, h⟩ | h
  · exact h
  · rw [hM] at h; exact h.elim
  · obtain ⟨-, h3, -⟩ := OV.InTail.of_first hf h
    omega

/-- **The used nodes' buffers from the junk** (`EUpd.junkRegion`, node by node): each node's buffer
is covered by the junk, and the nodes are pairwise disjoint, so the junk's bytes of each buffer
become the node's whole buffer, with the node's labels. -/
theorem chainH_junk {CI : Child} :
    ∀ (ns : List NodeV) {nxt : Option Ptr} {hj : Heap}, (∀ nd ∈ ns, JunkCovers hj nd) →
      ns.Pairwise NodeDisj →
      EUpd (ChainH CI false ns nxt ⋆ JunkAt hj)
        (FAssn.ex fun hj' => ChainH CI true ns nxt ⋆ JunkAt hj')
  | [], none, hj, _, _ => EUpd.of_imp fun _ h => ⟨hj, h⟩
  | [], some _, _, _, _ => EUpd.of_imp fun _ h => by obtain ⟨_, _, -, -, h, -⟩ := h; exact h.1.elim
  | _ :: _, none, _, _, _ => EUpd.of_imp fun _ h => by obtain ⟨_, _, -, -, h, -⟩ := h; exact h.1.elim
  | nd :: ns, some N', hj, hcov, hpw => by
    show EUpd ((FAssn.ex fun ei : BitVec 64 => FAssn.ex fun nxt : Option Ptr =>
      FAssn.ex fun buf : Array Byte => ⟪nd.N = N' ∧ NodeFacts nd.N nd.A nd.sz ∧
        buf.size = (if false then nd.sz - 24 else 0)⟫ ⋆
        (HeadH CI nd ei nxt ⋆ up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf) ⋆
          ChainH CI false ns nxt)) ⋆ JunkAt hj) _
    refine EUpd.ex fun ei => EUpd.ex fun nx => EUpd.ex fun buf => ?_
    refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc h) (EUpd.lift fun ⟨hN, hnf, hbuf⟩ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte] at hbuf
    -- the node's block and kind, from its `next` word
    refine EUpd.withFact (φ := ∃ b, nd.N.block = some b ∧ nd.K ≠ .constGlobal)
      (fun _ r _ _ h _ => ?_) fun ⟨b, hb, hK⟩ => ?_
    · obtain ⟨r₁, -, -, rfl, h1, -⟩ := h
      obtain ⟨r₂, -, -, rfl, h2, -⟩ := h1
      unfold HeadH at h2
      obtain ⟨-, r₃, -, rfl, -, h3⟩ := h2
      obtain ⟨-, r₄, -, rfl, -, h4⟩ := h3
      obtain ⟨r₅, -, -, rfl, h5, -⟩ := h4
      obtain ⟨⟨-, hK, b, hb, -⟩, -⟩ := h5
      exact ⟨b, by simpa [Ptr.add] using hb, hK⟩
    have hp0 := hnf.off0
    have hoff : (nd.N.add 24).off.toNat = nd.N.off.toNat + 24 := by simp only [Ptr.add]; omega
    have hc := hcov nd (List.mem_cons_self ..) b hb
    -- the junk's bytes of the buffer become a region
    refine EUpd.trans (EUpd.of_imp (P' := JunkAt hj ⋆ (HeadH CI nd ei nx ⋆
      up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf) ⋆ ChainH CI false ns nx))
      fun _ h => sep_comm h) ?_
    refine EUpd.trans (EUpd.junkRegion (p := nd.N.add 24) (n := nd.sz - 24) (S := nd.S)
      (by simpa [Ptr.add] using hb)
      (by simp only [Ptr.add]; omega) hK (headH_owns hb)
      (by rw [hoff, show nd.N.off.toNat + 24 + (nd.sz - 24) = nd.N.off.toNat + nd.sz by
        have := hnf.hdr; omega]; exact hc)) ?_
    rw [hoff, show nd.N.off.toNat + 24 + (nd.sz - 24) = nd.N.off.toNat + nd.sz by
      have := hnf.hdr; omega]
    refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc h) (EUpd.ex fun bs => ?_)
    refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc h) (EUpd.lift fun hbs => ?_)
    -- the rest of the chain, from the junk without this buffer
    have ih := chainH_junk (CI := CI) ns (nxt := nx)
      (hj := hj.cut b (nd.N.off.toNat + 24) (nd.N.off.toNat + nd.sz))
      (fun nd' h => (hcov nd' (List.mem_cons_of_mem _ h)).cut hb (List.rel_of_pairwise_cons hpw h))
      (List.Pairwise.of_cons hpw)
    refine EUpd.trans (EUpd.of_imp (P' := (ChainH CI false ns nx ⋆
      JunkAt (hj.cut b (nd.N.off.toNat + 24) (nd.N.off.toNat + nd.sz))) ⋆
        (up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 bs) ⋆ (HeadH CI nd ei nx ⋆
          up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf))))
      fun _ h => of_eq (by ac_rfl) h) ?_
    refine EUpd.trans (EUpd.frame ih) (EUpd.of_imp fun r h => ?_)
    obtain ⟨hj', h⟩ := sep_ex.mp h
    -- the empty region and the buffer join
    have hjn := fun r (h : (up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf) ⋆
        up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 bs)) r) =>
      up_region_join (q := nd.N.add 24) (by rw [hbuf]; simp) h
    have h := of_eq (Q := (up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf) ⋆
        up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 bs)) ⋆
      (HeadH CI nd ei nx ⋆ (ChainH CI true ns nx ⋆ JunkAt hj'))) (by ac_rfl) h
    have h := sep_mono_left (Q := up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 (buf ++ bs)))
      (fun _ x => hjn _ x) h
    have hnil : buf = #[] := Array.eq_empty_of_size_eq_zero hbuf
    subst hnil
    refine ⟨hj', ?_⟩
    show ((FAssn.ex fun ei : BitVec 64 => FAssn.ex fun nxt : Option Ptr =>
      FAssn.ex fun buf : Array Byte => ⟪nd.N = N' ∧ NodeFacts nd.N nd.A nd.sz ∧
        buf.size = (if true then nd.sz - 24 else 0)⟫ ⋆
        (HeadH CI nd ei nxt ⋆ up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf) ⋆
          ChainH CI true ns nxt)) ⋆ JunkAt hj') r
    refine sep_ex.mpr ⟨ei, sep_ex.mpr ⟨nx, sep_ex.mpr ⟨bs, sep_assoc' (sep_lift.mpr
      ⟨⟨hN, hnf, by simpa using hbs⟩, ?_⟩)⟩⟩⟩
    simp only [Array.empty_append] at h
    exact of_eq (by ac_rfl) h

/-- **The used list at a reset, released** (no grant, the ledger past epoch `e`, each used node's
whole claim): the nodes' kept shares, the pool and the receipts regroup into each node's whole
share (`reset_shares`), the junk's bytes of each buffer and the first node's tail become the
node's whole buffer (`EUpd.junkRegion`, `chainH_junk`), and the used list is a list of whole
nodes, as the free list holds them (`FreeList`). The junk that is left stays. -/
theorem release_used {CI : Child} {γ e : Nat} {w : OV} (hw : w.Facts) (hM : w.M = GMap.empty)
    (hpw : w.nodes.Pairwise NodeDisj) :
    EUpd (gauthP γ (e + 1) GMap.empty CI.tag ⋆ (JunkAt w.jh ⋆ Pool CI.tag w.pn w.pf ⋆ FirstPart CI w ⋆
        UsedRest CI w.rest w.nxt ⋆ FreeCl CI w.nodes))
      (gauthP γ (e + 1) GMap.empty CI.tag ⋆ FAssn.ex fun jh => JunkAt jh ⋆ FreeList CI w.first) := by
  have hfin : ∀ i, w.mN ≤ i → GMap.empty i = none := fun _ _ => rfl
  have hacct : ∀ b, ndLent b w.nodes = poolOn b w.pn w.pf + grantsOn b GMap.empty w.mN := fun b => by
    rw [← hM]; exact hw.2.2.2.1 b
  have hqq := hw.2.2.2.2.1
  have hff := hw.2.1
  cases hf : w.first with
  | none =>
    simp only [OV.FirstFacts, hf] at hff
    obtain ⟨-, hrest, hnxt⟩ := hff
    have hn : w.nodes = [] := by simp only [OV.nodes, hf]
    rw [hn] at hacct hqq
    simp only [FirstPart, hf, UsedRest, hrest, hnxt, hn, Chain, FreeCl]
    refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ (e + 1) GMap.empty CI.tag ⋆
        (LedgerRcpts γ e GMap.empty ⋆ (Pool CI.tag w.pn w.pf ⋆ NodeShares CI.tag NodeV.qh []))) ⋆
        JunkAt w.jh) fun _ h => ?_) ?_
    · rw [ledgerRcpts_empty]
      simp only [NodeShares]
      exact of_eq (by simp only [Full.emp_sep_eq, Full.sep_emp_eq]; ac_rfl) h
    refine EUpd.trans (EUpd.frame (reset_shares (Nat.lt_succ_self e) (by simp) (by simp) hfin hacct)) ?_
    refine EUpd.of_imp fun _ h => ?_
    simp only [NodeShares, Full.sep_emp_eq] at h
    refine sep_mono_right (R := FAssn.ex fun jh => JunkAt jh ⋆ FreeList CI none)
      (fun _ x => ⟨w.jh, sep_mono_right (R := FreeList CI none)
        (fun _ y => ⟨[], sep_emp.mpr y⟩) (sep_emp.mpr x)⟩) h
  | some N =>
    simp only [OV.FirstFacts, hf] at hff
    obtain ⟨hnf, hei, htail⟩ := hff
    let nd := w.node N
    have hn : w.nodes = nd :: w.rest := by simp only [OV.nodes, hf]; rfl
    have hpw' := hpw
    rw [hn] at hpw' hacct hqq
    have hfp : FirstPart CI w = ((HeadH CI nd (BitVec.ofNat 64 w.ei) w.nxt ⋆
        pshare nd.N nd.qh (nd.N.off.toNat + nd.sz) CI.tag) ⋆
        up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail)) := by
      simp only [FirstPart, hf]
      exact congrArg (· ⋆ _) (header_eq CI nd _ w.nxt nd.qh)
    rw [hfp, hn]
    -- the kept shares out of the headers
    refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ (e + 1) GMap.empty CI.tag ⋆
        (LedgerRcpts γ e GMap.empty ⋆ (Pool CI.tag w.pn w.pf ⋆ NodeShares CI.tag NodeV.qh (nd :: w.rest)))) ⋆
        (JunkAt w.jh ⋆ (HeadH CI nd (BitVec.ofNat 64 w.ei) w.nxt ⋆ (up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail) ⋆
          (ChainH CI false w.rest w.nxt ⋆ FreeCl CI (nd :: w.rest)))))) fun _ h => ?_) ?_
    · have h := of_eq (Q := UsedRest CI w.rest w.nxt ⋆ ((gauthP γ (e + 1) GMap.empty CI.tag ⋆
        (Pool CI.tag w.pn w.pf ⋆ pshare nd.N nd.qh (nd.N.off.toNat + nd.sz) CI.tag)) ⋆
        (JunkAt w.jh ⋆ (HeadH CI nd (BitVec.ofNat 64 w.ei) w.nxt ⋆ (up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail) ⋆ FreeCl CI (nd :: w.rest))))))
        (by ac_rfl) h
      have h := sep_mono_left (Q := ChainH CI false w.rest w.nxt ⋆ NodeShares CI.tag NodeV.qh w.rest)
        (fun _ x => chain_split x) h
      rw [ledgerRcpts_empty]
      simp only [NodeShares, Full.emp_sep_eq]
      exact of_eq (by ac_rfl) h
    -- the blocks of the nodes and the first node's kind
    refine EUpd.withFact (φ := (∃ b, N.block = some b) ∧ w.K ≠ .constGlobal ∧
        ∀ x ∈ w.rest, NodeFacts x.N x.A x.sz ∧ ∃ b, x.N.block = some b)
      (fun _ r _ _ h _ => ?_) fun ⟨⟨b, hbN⟩, hK, hrest⟩ => ?_
    · obtain ⟨_, _, -, -, -, h⟩ := h
      obtain ⟨_, _, -, -, -, h⟩ := h
      have h1 := headH_block h
      obtain ⟨_, _, -, -, -, h⟩ := h
      obtain ⟨_, _, -, -, -, h⟩ := h
      obtain ⟨_, _, -, -, h, -⟩ := h
      exact ⟨h1.1, h1.2, chainH_facts h⟩
    have hb : ∀ x ∈ nd :: w.rest, x.N.block ≠ none := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · show N.block ≠ none; rw [hbN]; simp
      · obtain ⟨-, b', hb'⟩ := hrest x hx; rw [hb']; simp
    -- the whole shares (`reset_shares`)
    refine EUpd.trans (EUpd.frame (reset_shares (Nat.lt_succ_self e) hb hqq hfin hacct)) ?_
    -- the first node's buffer before its tail, from the junk
    have hp0 := hnf.off0
    have hoff : (N.add 24).off.toNat = N.off.toNat + 24 := by simp only [Ptr.add]; omega
    refine EUpd.trans (EUpd.of_imp (P' := (JunkAt w.jh ⋆ (HeadH CI nd (BitVec.ofNat 64 w.ei) w.nxt ⋆
        ((gauthP γ (e + 1) GMap.empty CI.tag ⋆ NodeShares CI.tag NodeV.qn (nd :: w.rest)) ⋆ (up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail) ⋆
          (ChainH CI false w.rest w.nxt ⋆ FreeCl CI (nd :: w.rest)))))))
      fun _ h => of_eq (by ac_rfl) h) ?_
    refine EUpd.trans (EUpd.junkRegion (p := N.add 24) (n := w.ei) (S := w.S)
      (by simpa [Ptr.add] using hbN) (by simp only [Ptr.add]; omega) hK (headH_owns (nd := nd) hbN)
      (by rw [hoff]; exact cov_first hw hM hf hbN)) ?_
    rw [hoff]
    refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc h) (EUpd.ex fun bs => ?_)
    refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc h) (EUpd.lift fun hbs => ?_)
    -- the other used nodes' buffers (`chainH_junk`)
    have ih := chainH_junk (CI := CI) w.rest (nxt := w.nxt)
      (hj := w.jh.cut b (N.off.toNat + 24) (N.off.toNat + 24 + w.ei))
      (fun x hx => (cov_rest hw hM hf hpw x hx).cutIn (nd := nd) hbN (List.rel_of_pairwise_cons hpw' hx)
        (by show N.off.toNat ≤ _; omega) (by show _ ≤ N.off.toNat + w.sz; omega))
      (List.Pairwise.of_cons hpw')
    refine EUpd.trans (EUpd.of_imp (P' := (ChainH CI false w.rest w.nxt ⋆
        JunkAt (w.jh.cut b (N.off.toNat + 24) (N.off.toNat + 24 + w.ei))) ⋆
        (up (regionIn (N.add 24) nd.A w.S nd.K 1 bs) ⋆ (HeadH CI nd (BitVec.ofNat 64 w.ei) w.nxt ⋆
          ((gauthP γ (e + 1) GMap.empty CI.tag ⋆ NodeShares CI.tag NodeV.qn (nd :: w.rest)) ⋆
            (up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail) ⋆ FreeCl CI (nd :: w.rest))))))
      fun _ h => of_eq (by ac_rfl) h) ?_
    refine EUpd.trans (EUpd.frame ih) (EUpd.of_imp fun r h => ?_)
    obtain ⟨hj', h⟩ := sep_ex.mp h
    -- the first node's buffer: the junk's bytes and the tail
    have hq : N.add (24 + w.ei) = (N.add 24).add bs.size := by
      rw [hbs]; simp only [Ptr.add]; congr 1; omega
    have h := of_eq (Q := (up (regionIn (N.add 24) w.A w.S w.K 1 bs) ⋆
      up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail)) ⋆
      ((gauthP γ (e + 1) GMap.empty CI.tag ⋆ NodeShares CI.tag NodeV.qn (nd :: w.rest)) ⋆
        (HeadH CI nd (BitVec.ofNat 64 w.ei) w.nxt ⋆ (ChainH CI true w.rest w.nxt ⋆
          (JunkAt hj' ⋆ FreeCl CI (nd :: w.rest)))))) (by ac_rfl) h
    have h := sep_mono_left (Q := up (regionIn (N.add 24) w.A w.S w.K 1 (bs ++ w.tail)))
      (fun _ x => up_region_join hq x) h
    -- the used list as whole nodes
    have hch : ∀ r, ((up (regionIn (N.add 24) w.A w.S w.K 1 (bs ++ w.tail)) ⋆
        (HeadH CI nd (BitVec.ofNat 64 w.ei) w.nxt ⋆ ChainH CI true w.rest w.nxt)) ⋆
          NodeShares CI.tag NodeV.qn (nd :: w.rest)) r →
        Chain CI true ((nd :: w.rest).map NodeV.full) (some N) r := fun r h => by
      refine chain_join (sep_mono_left (Q := ChainH CI true (nd :: w.rest) (some N))
        (fun r h => ?_) h)
      refine ⟨BitVec.ofNat 64 w.ei, w.nxt, bs ++ w.tail, sep_lift.mpr ⟨⟨rfl, hnf, ?_⟩, ?_⟩⟩
      · simp only [ite_true, Array.size_append, hbs, htail]; show w.ei + (w.sz - 24 - w.ei) = w.sz - 24
        omega
      · exact of_eq (by ac_rfl) h
    have h := of_eq (Q := gauthP γ (e + 1) GMap.empty CI.tag ⋆ (JunkAt hj' ⋆
      ((((up (regionIn (N.add 24) w.A w.S w.K 1 (bs ++ w.tail)) ⋆
        (HeadH CI nd (BitVec.ofNat 64 w.ei) w.nxt ⋆ ChainH CI true w.rest w.nxt)) ⋆
          NodeShares CI.tag NodeV.qn (nd :: w.rest))) ⋆ FreeCl CI (nd :: w.rest)))) (by ac_rfl) h
    refine sep_mono_right (fun _ x => ⟨hj', sep_mono_right (fun _ y => ?_) x⟩) h
    exact ⟨nd :: w.rest, sep_mono_left (fun _ z => hch _ z) y⟩

/-- **The arena released at a reset**: its struct, the ledger at the next epoch with no grant and
that epoch's whole token, the child (with the arena's reservoir of its fee) and its vtable, junk,
and both lists as lists of whole nodes (`FreeList`: each node's header, whole buffer, the
child's token, the node's whole share and whole claim), which the code gives back to the child or
keeps. -/
def Released (CI : Child) (γ e : Nat) (ctx : Ptr) : FAssn :=
  FAssn.ex fun Ac : Nat => FAssn.ex fun Sc : Nat => FAssn.ex fun Kc : BlockKind =>
    FAssn.ex fun first : Option Ptr => FAssn.ex fun fl : Option Ptr => FAssn.ex fun jh : Heap =>
      up (regionIn ctx Ac Sc Kc 8 CI.bytes) ⋆ aptsE (ctx.add 16) first ⋆ aptsE (ctx.add 24) fl ⋆
        ((gauthP γ (e + 1) GMap.empty CI.tag ⋆ LedgerRcpts γ (e + 1) GMap.empty) ⋆
          epTok γ (e + 1) Frac.one) ⋆
        CI.cown ⋆ vtR CI.vtp CI.fns.toList ⋆ JunkAt jh ⋆ FreeList CI first ⋆ FreeList CI fl

/-- **`reset`'s ghost part**: from the arena's state at epoch `e` and the whole epoch token (no
grant is outstanding, `own_epTok_empty`), the ledger moves to epoch `e + 1` with that epoch's whole
token (`ledger_bump`), the claims the used nodes lent revert to them (`cls_revoke`), the pool and
the nodes' kept shares regroup into each node's whole share (`reset_shares`), and the junk and
the first node's tail become each node's whole buffer (`release_used`): `Released`. -/
theorem reset_release (CI : Child) (γ e : Nat) (ctx : Ptr) :
    EUpd ((inv CI γ e ctx).own ⋆ epTok γ e Frac.one) (Released CI γ e ctx) := by
  refine EUpd.trans (ResetLedger.own_bump (ledger CI γ e ctx)) (EUpd.exAll fun w => ?_)
  refine EUpd.lift fun ⟨hw, hM⟩ => ?_
  have hw : w.Facts := hw
  have hM : w.M = GMap.empty := hM
  show EUpd (((gauthP γ (e + 1) GMap.empty CI.tag ⋆ LedgerRcpts γ (e + 1) GMap.empty) ⋆
    epTok γ (e + 1) Frac.one) ⋆ w.bodyG CI γ e ctx) _
  have hff := hw.2.1
  -- the sizes of the used nodes after the first
  refine EUpd.withFact (φ := ∀ nd ∈ w.rest, NodeFacts nd.N nd.A nd.sz ∧ ∃ b, nd.N.block = some b)
    (fun _ r _ _ h _ => ?_) fun hrest => ?_
  · obtain ⟨_, _, -, -, -, h⟩ := h
    have h := of_eq (Q := UsedRest CI w.rest w.nxt ⋆ (up (regionIn ctx w.Ac w.Sc w.Kc 8 CI.bytes) ⋆
      aptsE (ctx.add 16) w.first ⋆ aptsE (ctx.add 24) w.fl ⋆ CI.cown ⋆ vtR CI.vtp CI.fns.toList ⋆
      JunkAt w.jh ⋆ Pool CI.tag w.pn w.pf ⋆ FirstPart CI w ⋆ FreeList CI w.fl ⋆ w.cls CI γ e))
      (by simp only [OV.bodyG]; ac_rfl) h
    obtain ⟨_, _, -, -, h, -⟩ := h
    obtain ⟨_, _, -, -, h, -⟩ := chain_split h
    exact chainH_facts h
  -- the used nodes' claims revert to them (`cls_revoke`)
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ (e + 1) GMap.empty CI.tag ⋆ w.cls CI γ e) ⋆
      ((LedgerRcpts γ (e + 1) GMap.empty ⋆ epTok γ (e + 1) Frac.one) ⋆
        (up (regionIn ctx w.Ac w.Sc w.Kc 8 CI.bytes) ⋆ aptsE (ctx.add 16) w.first ⋆
          aptsE (ctx.add 24) w.fl ⋆ CI.cown ⋆ vtR CI.vtp CI.fns.toList ⋆ JunkAt w.jh ⋆
          Pool CI.tag w.pn w.pf ⋆ FirstPart CI w ⋆ UsedRest CI w.rest w.nxt ⋆ FreeList CI w.fl)))
    fun _ h => of_eq (by simp only [OV.bodyG]; ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame (cls_revoke (Nat.lt_succ_self e) hw
    fun nd h => (hrest nd h).1.hdr)) ?_
  -- the used nodes are disjoint (their whole claims, `freeCl_pairwise`)
  have hsz : ∀ nd ∈ w.nodes, 0 < nd.sz := by
    intro nd hnd
    cases hf : w.first with
    | none => simp only [OV.nodes, hf] at hnd; exact absurd hnd List.not_mem_nil
    | some N =>
      simp only [OV.FirstFacts, hf] at hff
      simp only [OV.nodes, hf] at hnd
      rcases List.mem_cons.mp hnd with rfl | hnd
      · have := hff.1.hdr; simp only [OV.node]; omega
      · have := (hrest nd hnd).1.hdr; omega
  refine EUpd.withFact (φ := w.nodes.Pairwise NodeDisj) (fun _ r _ hh h _ => ?_) fun hpw => ?_
  · have ha := CI.act_within (P := (gauthP γ (e + 1) GMap.empty CI.tag ⋆ FreeCl CI w.nodes) ⋆
      ((LedgerRcpts γ (e + 1) GMap.empty ⋆ epTok γ (e + 1) Frac.one) ⋆
        (up (regionIn ctx w.Ac w.Sc w.Kc 8 CI.bytes) ⋆ aptsE (ctx.add 16) w.first ⋆
          aptsE (ctx.add 24) w.fl ⋆ CI.cown ⋆ vtR CI.vtp CI.fns.toList ⋆ JunkAt w.jh ⋆
          Pool CI.tag w.pn w.pf ⋆ FirstPart CI w ⋆ UsedRest CI w.rest w.nxt ⋆ FreeList CI w.fl)))
      (by unfold Child.cown; within) h
    exact freeCl_pairwise (R := gauthP γ (e + 1) GMap.empty CI.tag ⋆
      ((LedgerRcpts γ (e + 1) GMap.empty ⋆ epTok γ (e + 1) Frac.one) ⋆
        (up (regionIn ctx w.Ac w.Sc w.Kc 8 CI.bytes) ⋆ aptsE (ctx.add 16) w.first ⋆
          aptsE (ctx.add 24) w.fl ⋆ CI.cown ⋆ vtR CI.vtp CI.fns.toList ⋆ JunkAt w.jh ⋆
          Pool CI.tag w.pn w.pf ⋆ FirstPart CI w ⋆ UsedRest CI w.rest w.nxt ⋆ FreeList CI w.fl)))
      hh (of_eq (by ac_rfl) h) ha hsz
  -- the used list released (`release_used`)
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ (e + 1) GMap.empty CI.tag ⋆ (JunkAt w.jh ⋆
      Pool CI.tag w.pn w.pf ⋆ FirstPart CI w ⋆ UsedRest CI w.rest w.nxt ⋆ FreeCl CI w.nodes)) ⋆
      ((LedgerRcpts γ (e + 1) GMap.empty ⋆ epTok γ (e + 1) Frac.one) ⋆
        (up (regionIn ctx w.Ac w.Sc w.Kc 8 CI.bytes) ⋆ aptsE (ctx.add 16) w.first ⋆
          aptsE (ctx.add 24) w.fl ⋆ CI.cown ⋆ vtR CI.vtp CI.fns.toList ⋆ FreeList CI w.fl)))
    fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame (release_used hw hM hpw)) (EUpd.of_imp fun _ h => ?_)
  have h := of_eq (Q := (FAssn.ex fun jh => JunkAt jh ⋆ FreeList CI w.first) ⋆
    (gauthP γ (e + 1) GMap.empty CI.tag ⋆ ((LedgerRcpts γ (e + 1) GMap.empty ⋆ epTok γ (e + 1) Frac.one) ⋆
        (up (regionIn ctx w.Ac w.Sc w.Kc 8 CI.bytes) ⋆ aptsE (ctx.add 16) w.first ⋆
          aptsE (ctx.add 24) w.fl ⋆ CI.cown ⋆ vtR CI.vtp CI.fns.toList ⋆ FreeList CI w.fl))))
    (by ac_rfl) h
  obtain ⟨jh, h⟩ := sep_ex.mp h
  exact ⟨w.Ac, w.Sc, w.Kc, w.first, w.fl, jh, of_eq (by ac_rfl) h⟩

/-! ## The sizes of a list's nodes fit in the address space

`reset`'s retaining modes sum the buffer sizes of a list (`countListCapacity`) with an
overflow-checked `+`. The list owns every byte of its nodes (header words, `next`, whole buffer),
so their sizes sum to at most `2 ^ 63` (`Holds.owned_length_le`, `ZigLean/Sep/Full/OwnedBound.lean`:
owned bytes have different addresses below `2 ^ 63`). -/

/-- The bytes of a node: `[N, N + sz)` of its block. -/
def NodeV.locs (nd : NodeV) : List Loc := locRange (blkOf nd.N) nd.N.off.toNat nd.sz

theorem locRange_append (b lo n k : Nat) : locRange b lo n ++ locRange b (lo + n) k = locRange b lo (n + k) := by
  simp only [locRange, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp, Nat.add_assoc]

/-- **A list of whole nodes owns every byte of its nodes.** -/
theorem chain_ownsList (CI : Child) :
    ∀ (ns : List NodeV) (x : Option Ptr), OwnsList (ns.flatMap NodeV.locs) (Chain CI true ns x)
  | [], none => OwnsList.nil
  | [], some _ => fun _ h => h.1.elim
  | _ :: _, none => fun _ h => h.1.elim
  | nd :: ns, some N' => fun r h => by
    obtain ⟨ei, nx, buf, h⟩ := h
    obtain ⟨⟨-, hnf, hbuf⟩, h⟩ := sep_lift.mp h
    simp only [ite_true] at hbuf
    obtain ⟨b, hb⟩ : ∃ b, nd.N.block = some b := by
      obtain ⟨_, _, -, -, h1, -⟩ := h
      obtain ⟨_, _, -, -, hw, -⟩ := h1
      exact (facts_wpts _ hw).1
    have h0 := hnf.off0
    have hsz := hnf.hdr
    have e8 : (nd.N.add 8).off.toNat = nd.N.off.toNat + 8 := by simp only [Ptr.add]; omega
    have e16 : (nd.N.add 16).off.toNat = nd.N.off.toNat + 8 + 8 := by simp only [Ptr.add]; omega
    have e24 : (nd.N.add 24).off.toNat = nd.N.off.toNat + 8 + 8 + 8 := by simp only [Ptr.add]; omega
    have hbk : ∀ k : Int, (nd.N.add k).block = some b := fun _ => by simpa [Ptr.add] using hb
    have hnode : OwnsList (nd.locs ++ ns.flatMap NodeV.locs)
        ((wpts nd.N (BitVec.ofNat 64 nd.sz) ⋆ wpts (nd.N.add 8) ei ⋆
          up (regionIn (nd.N.add 16) nd.A nd.S nd.K 8 (Enc.encode nx)) ⋆
          (CI.ntok nd.N nd.sz 3 nd.A nd.S nd.K nd.qn ⋆ pshare nd.N nd.qh (nd.N.off.toNat + nd.sz) CI.tag)) ⋆
          up (regionIn (nd.N.add 24) nd.A nd.S nd.K 1 buf) ⋆ Chain CI true ns nx) := by
      refine OwnsList.of_eq ((((OwnsList.wpts hb).sep ((OwnsList.wpts (hbk 8)).sep
        ((OwnsList.region (hbk 16)).sep (OwnsList.nil (P := CI.ntok nd.N nd.sz 3 nd.A nd.S nd.K nd.qn ⋆
          pshare nd.N nd.qh (nd.N.off.toNat + nd.sz) CI.tag))))).sep
        ((OwnsList.region (hbk 24)).sep (chain_ownsList CI ns nx)))) ?_
      simp only [e8, e16, e24, encode_nxt_size, hbuf, List.append_nil, ← List.append_assoc]
      rw [locRange_append, locRange_append, locRange_append]
      simp only [NodeV.locs, blkOf, hb, Option.getD_some]
      congr 2; omega
    exact (OwnsList.of_eq hnode (by simp only [List.flatMap_cons])) r h

/-- **The sizes of a list's nodes sum to at most `2 ^ 63`.** -/
theorem chain_sizes_le {CI : Child} {ns : List NodeV} {x : Option Ptr} {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hp : Chain CI true ns x r) (hs : m.FSeq) : (ns.map NodeV.sz).sum ≤ 2 ^ 63 := by
  have := (chain_ownsList CI ns x).length_le hh hp hs
  simpa [NodeV.locs, locRange, List.length_flatMap] using this

/-- **An arena with no node** at epoch `e`: its struct with empty lists, the ledger with no grant,
the child with the reservoir and its vtable, and junk (what `reset`'s `free_all` leaves). -/
theorem own_empty (CI : Child) (γ e : Nat) (ctx : Ptr) {Ac Sc : Nat} {Kc : BlockKind} {jh : Heap} :
    EUpd (up (regionIn ctx Ac Sc Kc 8 CI.bytes) ⋆ aptsE (ctx.add 16) (none : Option Ptr) ⋆
        aptsE (ctx.add 24) (none : Option Ptr) ⋆ gauthP γ e GMap.empty CI.tag ⋆
        LedgerRcpts γ e GMap.empty ⋆ CI.cown ⋆ vtR CI.vtp CI.fns.toList ⋆ JunkAt jh)
      (own CI γ e ctx) := by
  refine EUpd.of_imp fun r h => ⟨⟨Ac, Sc, Kc, none, none, GMap.empty, none, 0, 0, .heap,
    0, 0, #[], Frac.one, Frac.one, [], 0, 0, fun _ => (0, Frac.one, 0), jh⟩, sep_lift.mpr ⟨?_, ?_⟩⟩
  · refine ⟨fun _ _ => rfl, ⟨rfl, rfl, rfl⟩, fun _ _ h => ?_, fun _ => ?_, fun _ h => ?_, fun _ h => ?_⟩
    · cases h
    · simp only [ndLent, poolOn, grantsOn, esum, OV.nodes]; exact (Rat.add_zero 0).symm
    · cases h
    · cases h
  · simp only [OV.body, OV.cls, FirstCl, FirstPart, RestCl, UsedRest, Chain, Pool, Full.sepN,
      freeList_none, Full.sep_emp_eq]
    exact of_eq (by ac_rfl) h

end AllocArena.Core
