import ZigLean.Sep.Full.LockPair

/-!
# The two-lock product: one protocol, two locks, either lock's view

(ledger #two-lock-product, item (1).) A thread may hold one lock `A` while it runs the code of
another lock `B` (a lock order; the RwLock writer, which holds the outer mutex while the
semaphore's mutex runs). The protocol then fits both locks over one ghost value (`FLock.Pair`).
Each lock's invariant (`FLock.Inv`) sees the threads' parts as `part ⋆ held` of its own lock; the
other lock's word, its free resource and its holders' resources lie in its rest. The two views
split the same resources differently, so either one gives the other (`Pair.swap`). The rules of
each lock's code then need only their own lock's `Fits`; the other lock rides in `U`
(`Pair.U`).

* **Regrouping the parts** (`FOwned.out`, `FOwned.into`): a family of resources `b` moves out of
  the threads' parts into the rest, as their composition `rb` (`sepN`), and back. Moving in needs
  that each thread's clock owns its new bytes (`Mem.Owns`), which the rest does not record.
* `FLock.Facts`: the lock invariant without the parts (`FOwned`), at a given free resource. In the
  other lock's view these are what the product keeps of a lock (`Pair.U`), with the holders'
  ownership of their resources.
* `Pair.swap`: `A`'s invariant and `B`'s facts give `B`'s invariant and `A`'s facts.
-/

namespace Zig
namespace Full

open FAssn Conc Proto

/-! ## Regrouping the parts -/

/-- Two resources and two others, regrouped: the middle two change places. -/
theorem rsum_rsum_comm {a b c d : Res} (hbc : FHeap.Disjoint b.heap c.heap) :
    rsum (rsum a b) (rsum c d) = rsum (rsum a c) (rsum b d) := by
  rw [rsum_assoc, ← rsum_assoc (a := b), rsum_comm hbc, rsum_assoc, ← rsum_assoc]

/-- The parts are exactly composed: `sepN` of exact parts has one resource. -/
theorem sepN_partOf_unique {own : ThreadId → Res} :
    ∀ {n : Nat} {r r' : Res}, sepN n (partOf own) r → sepN n (partOf own) r' → r = r'
  | 0, r, r', ⟨h1, k1, g1⟩, ⟨h2, k2, g2⟩ => by rw [res_eta r, res_eta r', h1, k1, g1, h2, k2, g2]
  | n + 1, _, _, ⟨_, _, _, rfl, rfl, h1⟩, ⟨_, _, _, rfl, rfl, h2⟩ => by
    rw [sepN_partOf_unique h1 h2]

/-- **Pointwise sums of parts are the sum of the two families' compositions** (both directions:
splitting needs that each pair is apart). -/
theorem sepN_partOf_rsum {a b : ThreadId → Res} :
    ∀ {n : Nat} {r : Res}, (∀ u, FHeap.Disjoint (a u).heap (b u).heap) →
      (sepN n (partOf fun u => rsum (a u) (b u)) r ↔
        ∃ ra rb, sepN n (partOf a) ra ∧ sepN n (partOf b) rb ∧ FHeap.Disjoint ra.heap rb.heap ∧
          r = rsum ra rb)
  | 0, r, _ => by
    constructor
    · intro h
      refine ⟨rnil, rnil, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, FHeap.disjoint_empty _, ?_⟩
      obtain ⟨h1, k1, g1⟩ := h
      rw [res_eta r, h1, k1, g1]; exact (rsum_rnil rnil).symm
    · rintro ⟨ra, rb, ⟨h1, k1, g1⟩, ⟨h2, k2, g2⟩, -, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · show ra.heap ∪ rb.heap = _; rw [h1, h2]; exact FHeap.union_empty _
      · show ra.know.union rb.know = _; rw [k1, k2]; exact Know.none_union _
      · show ra.gh.add rb.gh = _; rw [g1, g2]; exact Ghost.add_unit _
  | n + 1, r, hab => by
    constructor
    · rintro ⟨r₁, r₂, hd, rfl, rfl, h2⟩
      obtain ⟨ra, rb, ha, hb, hd', rfl⟩ := (sepN_partOf_rsum (n := n) hab).mp h2
      obtain ⟨hd1, hd2⟩ := FHeap.disjoint_union_left.mp hd
      obtain ⟨hab1, hab2⟩ := FHeap.disjoint_union_right.mp hd1
      obtain ⟨hbb1, hbb2⟩ := FHeap.disjoint_union_right.mp hd2
      refine ⟨rsum (a n) ra, rsum (b n) rb, ⟨a n, ra, hab1, rfl, rfl, ha⟩,
        ⟨b n, rb, hbb2, rfl, rfl, hb⟩, FHeap.disjoint_union_left.mpr
          ⟨FHeap.disjoint_union_right.mpr ⟨hab n, hab2⟩,
           FHeap.disjoint_union_right.mpr ⟨hbb1.symm, hd'⟩⟩, ?_⟩
      exact rsum_rsum_comm hbb1
    · rintro ⟨ra, rb, ⟨a₁, ra', hda, rfl, rfl, ha⟩, ⟨b₁, rb', hdb, rfl, rfl, hb⟩, hd, rfl⟩
      obtain ⟨hd1, hd2⟩ := FHeap.disjoint_union_left.mp hd
      obtain ⟨h11, h12⟩ := FHeap.disjoint_union_right.mp hd1
      obtain ⟨h21, h22⟩ := FHeap.disjoint_union_right.mp hd2
      refine ⟨rsum (a n) (b n), rsum ra' rb', ?_, rsum_rsum_comm h21,
        rfl, (sepN_partOf_rsum (n := n) hab).mpr ⟨ra', rb', ha, hb, h22, rfl⟩⟩
      exact FHeap.disjoint_union_left.mpr ⟨FHeap.disjoint_union_right.mpr ⟨hda, h12⟩,
        FHeap.disjoint_union_right.mpr ⟨h21.symm, hdb⟩⟩

/-- A part of an exact composition has no `cur` token when the composition has none. -/
theorem sepN_partOf_noCur {own : ThreadId → Res} {n : Nat} {r : Res}
    (h : sepN n (partOf own) r) (hc : r.NoCur) {u : ThreadId} (hu : u < n) : (own u).NoCur := by
  obtain ⟨rR, -, -, rfl⟩ := parts_pick hu h
  exact Res.NoCur.left (b := rR) hc

namespace FOwned

variable {a b : ThreadId → Res} {rO rb : Res} {m : Mem}

/-- The parts own their bytes: a part of an exact composition is in a part. -/
theorem owns_right (ho : FOwned (fun u => rsum (a u) (b u)) rO m) {u : ThreadId}
    (hu : u < m.threads.size) : m.Owns u (b u).owned :=
  (ho.owns u hu).sub fun _ hl => (Res.owned_sep rfl rfl).mpr (.inr hl)

/-- **A family moves out of the parts into the rest**: each thread's part `a u ⋆ b u` keeps
`a u`, and the composition `rb` of the `b u` joins the rest. -/
theorem out (ho : FOwned (fun u => rsum (a u) (b u)) rO m)
    (hab : ∀ u, FHeap.Disjoint (a u).heap (b u).heap)
    (haout : ∀ u, m.threads.size ≤ u → emp (a u)) :
    ∃ rb, sepN m.threads.size (partOf b) rb ∧ FHeap.Disjoint rb.heap rO.heap ∧
      FOwned a (rsum rb rO) m := by
  obtain ⟨rT, hs, hh⟩ := ho.holds
  obtain ⟨ra, rb, ha, hb, hd, rfl⟩ := (sepN_partOf_rsum hab).mp hs
  obtain ⟨hdT, -⟩ := id hh
  obtain ⟨hdaO, hdbO⟩ := FHeap.disjoint_union_left.mp hdT
  have hcT : (rsum ra rb).NoCur := sepN_noCur (fun j r h => by rw [h]; exact ho.noCur.1 j) hs
  exact ⟨rb, hb, hdbO, ⟨ra, ha, hh.regroup (FHeap.disjoint_union_right.mpr ⟨hd, hdaO⟩)
    rsum_assoc.symm⟩, fun u hu => (ho.owns u hu).sub fun l hl => (Res.owned_sep rfl rfl).mpr
    (.inl hl), haout, ho.csize, ho.conc, ⟨fun u => Res.NoCur.left (ho.noCur.1 u),
    Res.noCur_rsum (Res.NoCur.right hcT) ho.noCur.2⟩⟩

/-- **A family moves from the rest into the parts**: the composition `rb` of the `b u` leaves
the rest, and each thread's part grows by `b u`, whose bytes its clock owns. -/
theorem into (ho : FOwned a (rsum rb rO) m) (hb : sepN m.threads.size (partOf b) rb)
    (hbO : FHeap.Disjoint rb.heap rO.heap) (hown : ∀ u < m.threads.size, m.Owns u (b u).owned)
    (hbout : ∀ u, m.threads.size ≤ u → emp (b u)) :
    FOwned (fun u => rsum (a u) (b u)) rO m := by
  obtain ⟨ra, ha, hh⟩ := ho.holds
  obtain ⟨hdT, -⟩ := id hh
  obtain ⟨hdab, hdaO⟩ := FHeap.disjoint_union_right.mp hdT
  have hab : ∀ u, FHeap.Disjoint (a u).heap (b u).heap := fun u l => by
    by_cases hu : u < m.threads.size
    · by_cases e : (a u).heap l = none
      · exact .inl e
      · obtain ⟨_, rfl, hsa⟩ := sepN_mem ha hu
        obtain ⟨_, rfl, hsb⟩ := sepN_mem hb hu
        refine .inr (Classical.byContradiction fun e' => ?_)
        rcases hdab l with h | h
        · exact hsa l e h
        · exact hsb l e' h
    · exact .inr (by rw [(hbout u (Nat.le_of_not_lt hu)).1]; rfl)
  have hcR : (rsum rb rO).NoCur := ho.noCur.2
  refine ⟨⟨rsum ra rb, (sepN_partOf_rsum hab).mpr ⟨ra, rb, ha, hb, hdab, rfl⟩,
    hh.regroup (FHeap.disjoint_union_left.mpr ⟨hdaO, hbO⟩) rsum_assoc⟩, fun u hu => ?_,
    fun u hu => ?_, ho.csize, ho.conc,
    ⟨fun u => Res.noCur_rsum (ho.noCur.1 u) ?_, Res.NoCur.right hcR⟩⟩
  · have h1 := ho.owns u hu
    have h2 := hown u hu
    exact (h1.union h2).sub fun l hl => Res.owned_sub_union rfl rfl hl
  · obtain ⟨h1, k1, g1⟩ := ho.outside u hu
    obtain ⟨h2, k2, g2⟩ := hbout u hu
    refine ⟨?_, ?_, ?_⟩
    · show (a u).heap ∪ (b u).heap = _; rw [h1, h2]; exact FHeap.union_empty _
    · show (a u).know.union (b u).know = _; rw [k1, k2]; exact Know.none_union _
    · show (a u).gh.add (b u).gh = _; rw [g1, g2]; exact Ghost.add_unit _
  · by_cases hu : u < m.threads.size
    · exact sepN_partOf_noCur hb (Res.NoCur.left hcR) hu
    · intro v; rw [(hbout u (Nat.le_of_not_lt hu)).2.2]; rfl

end FOwned

/-- `c` moves past `a` and `b` (each apart from `c`). -/
theorem rsum_rot {a b c z : Res} (hca : FHeap.Disjoint c.heap a.heap)
    (hcb : FHeap.Disjoint c.heap b.heap) :
    rsum c (rsum a (rsum b z)) = rsum a (rsum b (rsum c z)) := by
  rw [← rsum_assoc (a := c), rsum_comm hca, rsum_assoc, ← rsum_assoc (a := c), rsum_comm hcb,
    rsum_assoc]

theorem rsum_three (a b c z : Res) : rsum (rsum a (rsum b c)) z = rsum a (rsum b (rsum c z)) := by
  simp only [rsum_assoc]

namespace LockWord

variable {L : LockWord} {m : Mem} {h : FHeap}

/-- A heap without the word's bytes is apart from the word's cells. -/
theorem off_disj (hh : L.Off h.erase) : FHeap.Disjoint (L.wordR m).heap h := fun l => by
  by_cases hl : L.In l
  · exact .inr (off_erase.mp hh l hl)
  · exact .inl (cellsAt_none hl)

/-- A heap apart from the word's cells has none of the word's bytes. -/
theorem off_of_wordDisj (hb : L.BlkOk m) (hd : FHeap.Disjoint h (L.wordR m).heap) : L.Off h.erase :=
  off_erase.mpr fun l hl => (hd l).resolve_right (wordR_some hb hl)

end LockWord

namespace FLock

variable {γ : Type} (L : FLock γ)

/-- Thread `u`'s part without the lock's resource; a joined thread owns nothing. -/
def base (G : ThreadId → γ) (m : Mem) (u : ThreadId) : Res :=
  if joinedB m u then rnil else L.part (G u)

/-- The resource thread `u` holds of the lock; a joined thread holds nothing. -/
def heldOf (G : ThreadId → γ) (m : Mem) (u : ThreadId) : Res :=
  if joinedB m u then rnil else L.held (G u)

theorem own_eq (G : ThreadId → γ) (m : Mem) :
    L.own G m = fun u => rsum (L.base G m u) (L.heldOf G m u) := by
  funext u; unfold own base heldOf
  split
  · exact (rsum_rnil rnil).symm
  · rfl

/-- **The lock's invariant without the threads' parts** (`FOwned`), at the free resource `rL`
(module doc). -/
structure Facts (G : ThreadId → γ) (m : Mem) (rL : Res) : Prop where
  w : L.WInv (L.pl G) m
  loff : L.Off rL.heap.erase
  free : L.Free G → L.R G rL ∧ L.toLockWord.Owns (L.pl G) m rL.owned
  busy : ¬ L.Free G → rL = rnil
  pdisj : ∀ u, FHeap.Disjoint (L.part (G u)).heap (L.held (G u)).heap
  idle : ∀ u, (L.ph (G u)).held = false → L.held (G u) = rnil
  res : ∀ u, (L.ph (G u)).held = true → L.R G (L.held (G u))

variable {L} {G : ThreadId → γ} {m : Mem} {rL rX : Res}

theorem Inv.facts (hi : L.Inv G rX m) : ∃ rL, L.FreeRes G rX m rL ∧ L.Facts G m rL :=
  let ⟨rL, hfr⟩ := hi.rest
  ⟨rL, hfr, hi.w, hfr.2.1, hfr.2.2.2.1, hfr.2.2.2.2, hi.pdisj, hi.idle, hi.res⟩

theorem Facts.inv (hf : L.Facts G m rL)
    (ho : FOwned (L.own G m) (rsum (L.wordR m) (rsum rL rX)) m)
    (hLX : FHeap.Disjoint rL.heap rX.heap) (hxoff : L.Off rX.heap.erase) : L.Inv G rX m :=
  ⟨hf.w, ⟨rL, ho, hf.loff, hLX, hf.free, hf.busy⟩, hxoff, hf.pdisj, hf.idle, hf.res⟩

/-- A thread beyond the threads holds nothing. -/
theorem Facts.held_out (hf : L.Facts G m rL) {u : ThreadId} (hu : m.threads.size ≤ u) :
    L.held (G u) = rnil :=
  hf.idle u (by
    by_cases hg : L.ph (G u) = .gone
    · rw [hg]; rfl
    · exact absurd (hf.w.live u hg).1 (Nat.not_lt.mpr hu))

theorem joinedB_out {m : Mem} {u : ThreadId} (hu : m.threads.size ≤ u) : joinedB m u = false := by
  simp [joinedB, Array.getElem?_eq_none hu]

theorem Facts.heldOf_out (hf : L.Facts G m rL) {u : ThreadId} (hu : m.threads.size ≤ u) :
    emp (L.heldOf G m u) := by
  unfold heldOf; rw [joinedB_out hu, hf.held_out hu]; exact ⟨rfl, rfl, rfl⟩

theorem Facts.heldOf_disj (hf : L.Facts G m rL) (u : ThreadId) :
    FHeap.Disjoint (L.base G m u).heap (L.heldOf G m u).heap := by
  unfold base heldOf; split
  · exact FHeap.disjoint_empty _
  · exact hf.pdisj u

/-- Beyond the threads the part is empty (`FOwned.outside`). -/
theorem Facts.base_out (hf : L.Facts G m rL) {rO : Res} (ho : FOwned (L.own G m) rO m)
    {u : ThreadId} (hu : m.threads.size ≤ u) : emp (L.base G m u) := by
  have h := ho.outside u hu
  unfold own at h; unfold base
  rw [joinedB_out hu] at h ⊢
  rw [hf.held_out hu, rsum_rnil] at h; exact h

/-- While the lock is free its holders' resources are empty; while it is held its free
resource is. -/
theorem Facts.free_held_disj (hf : L.Facts G m rL) {rH : Res}
    (hH : sepN m.threads.size (partOf (L.heldOf G m)) rH) : FHeap.Disjoint rL.heap rH.heap := by
  by_cases hF : L.Free G
  · intro l
    refine .inr (Classical.byContradiction fun hl => ?_)
    obtain ⟨j, -, _, rfl, hj⟩ := sepN_cover hH hl
    unfold heldOf at hj
    split at hj
    · exact hj rfl
    · rw [hf.idle j (hF.held j)] at hj; exact hj rfl
  · rw [hf.busy hF]; exact fun _ => .inl rfl

/-- **`B` in the other lock's view**: `B`'s word, its free resource `rL` and its holders'
resources `rH`. -/
abbrev side (B : FLock γ) (m : Mem) (rL rH : Res) : Res := rsum (B.wordR m) (rsum rL rH)

/-- **What the product keeps of `B` in the other lock's view** (module doc), next to the
protocol's own rest `rX`: `B`'s facts at its free resource `rL`, its holders' resources `rH`
(each holder's clock owns them), and the bytes of `rH` and `rX` apart from `B`'s word and
from `rL`, `rH`. -/
structure Keeps (B : FLock γ) (G : ThreadId → γ) (m : Mem) (rL rH rX : Res) : Prop where
  facts : B.Facts G m rL
  held : sepN m.threads.size (partOf (B.heldOf G m)) rH
  owns : ∀ u < m.threads.size, m.Owns u (B.heldOf G m u).owned
  hoff : B.Off rH.heap.erase
  xdisj : FHeap.Disjoint (rsum rL rH).heap rX.heap
  xoff : B.Off rX.heap.erase

end FLock

namespace FLock.Pair

variable {γ : Type} {A B : FLock γ} {G : ThreadId → γ} {m : Mem}

/-- **The two-lock product's rest for `A`** (`FLock.Fits.inv`): the rest of `A`'s invariant is
`B`'s side next to the protocol's own rest `rX`, `B` is kept, and the protocol's own `U` holds
at `rX`. -/
def U (B : FLock γ) (U : (ThreadId → γ) → Res → Mem → Prop) :
    (ThreadId → γ) → Res → Mem → Prop := fun G rXA m =>
  ∃ rL rH rX, rXA = rsum (side B m rL rH) rX ∧ B.Keeps G m rL rH rX ∧ U G rX m

/-- **Either lock's view gives the other's** (module doc): `A`'s invariant with `B`'s side in its
rest, and `B` kept, give `B`'s invariant with `A`'s side in its rest, and `A` kept. The holders'
resources of `A` move out of the threads' parts into `B`'s rest, and those of `B` move in. -/
theorem swap (hp : A.Pair B) {rLB rHB rX : Res}
    (hi : A.Inv G (rsum (side B m rLB rHB) rX) m) (hk : B.Keeps G m rLB rHB rX) :
    ∃ rLA rHA, B.Inv G (rsum (side A m rLA rHA) rX) m ∧ A.Keeps G m rLA rHA rX := by
  obtain ⟨rLA, ⟨hoA, hLoffA, hLXA, -, -⟩, hfA⟩ := hi.facts
  have hxA := hi.xoff
  rw [FLock.own_eq] at hoA
  obtain ⟨rHA, hHA, hdHA, ho1⟩ := hoA.out hfA.heldOf_disj fun u hu => by
    have := hi.rest; obtain ⟨_, ho, -⟩ := this
    exact hfA.base_out ho hu
  have hbB : B.BlkOk m := hk.facts.w.blk
  -- the disjointness of the pieces
  have hdA := FHeap.disjoint_union_right.mp hdHA
  have hdA2 := FHeap.disjoint_union_right.mp hdA.2
  have hdA3 := FHeap.disjoint_union_right.mp hdA2.2
  have hLX := FHeap.disjoint_union_right.mp hLXA
  have hAX : FHeap.Disjoint (A.wordR m).heap (rsum (side B m rLB rHB) rX).heap :=
    LockWord.off_disj hxA
  have hAX2 := FHeap.disjoint_union_right.mp hAX
  have hAw_LA : FHeap.Disjoint (A.wordR m).heap rLA.heap := LockWord.off_disj hLoffA
  have hSA_SB : FHeap.Disjoint (side A m rLA rHA).heap (side B m rLB rHB).heap :=
    FHeap.disjoint_union_left.mpr ⟨hAX2.1, FHeap.disjoint_union_left.mpr ⟨hLX.1, hdA3.1⟩⟩
  have hSA_X : FHeap.Disjoint (side A m rLA rHA).heap rX.heap :=
    FHeap.disjoint_union_left.mpr ⟨hAX2.2, FHeap.disjoint_union_left.mpr ⟨hLX.2, hdA3.2⟩⟩
  -- `rLB`, `rHB` apart from `A`'s side, `rHB` apart from `B`'s word and free resource
  have hSB := FHeap.disjoint_union_left.mp
    (FHeap.disjoint_union_left.mp hSA_SB.symm).2
  have hLB_SA : FHeap.Disjoint rLB.heap (side A m rLA rHA).heap := hSB.1
  have hHB_SA : FHeap.Disjoint rHB.heap (side A m rLA rHA).heap := hSB.2
  have hxd := FHeap.disjoint_union_left.mp hk.xdisj
  have hHB_Bw : FHeap.Disjoint rHB.heap (B.wordR m).heap := (LockWord.off_disj hk.hoff).symm
  have hHB_LB : FHeap.Disjoint rHB.heap rLB.heap := (hk.facts.free_held_disj hk.held).symm
  -- regroup the rest: `A`'s holders out, `B`'s holders to the front
  have he : rsum rHA (rsum (A.wordR m) (rsum rLA (rsum (side B m rLB rHB) rX))) =
      rsum rHB (rsum (B.wordR m) (rsum rLB (rsum (side A m rLA rHA) rX))) := by
    rw [rsum_rot hdA.1 hdA2.1, ← rsum_three, ← rsum_assoc,
      rsum_comm (a := rsum (A.wordR m) (rsum rLA rHA)) hSA_SB, rsum_assoc, rsum_three,
      ← rsum_rot hHB_Bw hHB_LB]
  rw [he] at ho1
  have hbase : A.base G m = B.base G m := funext fun u => by
    unfold base; rw [hp.part]
  rw [hbase] at ho1
  have hHB_O : FHeap.Disjoint rHB.heap
      (rsum (B.wordR m) (rsum rLB (rsum (side A m rLA rHA) rX))).heap :=
    FHeap.disjoint_union_right.mpr ⟨hHB_Bw, FHeap.disjoint_union_right.mpr ⟨hHB_LB,
      FHeap.disjoint_union_right.mpr ⟨hHB_SA, hxd.2⟩⟩⟩
  have ho2 := ho1.into hk.held hHB_O hk.owns fun u hu => hk.facts.heldOf_out hu
  rw [← FLock.own_eq] at ho2
  have hBX : B.Off (rsum (side A m rLA rHA) rX).heap.erase :=
    LockWord.off_erase.mpr fun l hl => by
      have hn := LockWord.off_erase.mp hk.xoff l hl
      have hw : (A.wordR m).heap l = none := cellsAt_none (hp.apart.symm.not_in hl)
      have hS : (side A m rLA rHA).heap l = none := by
        rcases hSA_SB l with e | e
        · exact e
        · exact absurd e (by
            show ((B.wordR m).heap ∪ (rsum rLB rHB).heap) l ≠ none
            simp only [FHeap.union_apply]
            have := LockWord.wordR_some hbB hl
            cases e' : (B.wordR m).heap l <;> simp_all)
      show ((side A m rLA rHA).heap ∪ rX.heap) l = none
      rw [FHeap.union_apply, hS, hn]; rfl
  refine ⟨rLA, rHA, hk.facts.inv ho2 (FHeap.disjoint_union_right.mpr ⟨hLB_SA, hxd.1⟩) hBX,
    hfA, hHA, fun u hu => ?_, ?_, FHeap.disjoint_union_left.mpr ⟨hLX.2, hdA3.2⟩,
    LockWord.off_erase.mpr fun l hl => ?_⟩
  · have := hi.rest; obtain ⟨_, ho, -⟩ := this
    rw [FLock.own_eq] at ho
    exact ho.owns_right hu
  · exact LockWord.off_of_wordDisj hfA.w.blk (FHeap.disjoint_union_right.mp hdHA).1
  · have := LockWord.off_erase.mp hxA l hl
    simp only [FHeap.union_apply, Option.or_eq_none_iff] at this
    exact this.2

/-- **The two-lock product's invariant is the same in either lock's view**: a protocol whose
invariant is `A`'s with `Pair.U B U` is also `B`'s with `Pair.U A U` (`FLock.Fits.inv` for both
locks). -/
theorem inv_iff (hp : A.Pair B) {U : (ThreadId → γ) → Res → Mem → Prop} :
    (∃ rX, A.Inv G rX m ∧ Pair.U B U G rX m) ↔ (∃ rX, B.Inv G rX m ∧ Pair.U A U G rX m) := by
  constructor
  · rintro ⟨_, hi, rL, rH, rX, rfl, hk, hU⟩
    obtain ⟨rL', rH', hi', hk'⟩ := hp.swap hi hk
    exact ⟨_, hi', rL', rH', rX, rfl, hk', hU⟩
  · rintro ⟨_, hi, rL, rH, rX, rfl, hk, hU⟩
    obtain ⟨rL', rH', hi', hk'⟩ := hp.symm.swap hi hk
    exact ⟨_, hi', rL', rH', rX, rfl, hk', hU⟩

end FLock.Pair

end Full
end Zig
