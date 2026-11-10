import ZigLean.Sep.Full.LockPair
import ZigLean.Sep.Full.LockOrder
import ZigLean.Sep.Full.Word

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
* `Pair.swap`: `A`'s invariant and `B`'s facts give `B`'s invariant and `A`'s facts;
  `Pair.inv_iff`: so one protocol invariant serves both locks' `Fits.inv`.
* **Read shares**: the holders' resources move into the parts without gathering a partial share
  (`FLock.NoGatherHeld`, `NoGatherHeld.of_R` for a resource without partial shares; F4's
  `Mem.OwnsRes.gather`), so `Pair.swap` and `Pair.inv_iff` take it.
* **`B` kept across `A`'s view's steps**: a step of `A`'s code (`Pair.Keeps.otherStep`; a thread it
  queues is `away` from `B`, or holds `B` at `holdsAway` with `A`'s key in `B`'s nest), a change
  of `A`'s coordinates such as a nap (`Keeps.setA`), a stop (`Keeps.cur`), a step on a thread's
  own part (`Keeps.partStep`, in `Inv.wp_liftMem`'s frame: `A`'s rest with its read shares; `B`'s
  word cells stay up to `Cell.norm`, so the same rest stores `B`'s side at the new memory).
* **`B`'s side as the rest stores it** (`Pair.U`): alike to `side B m` up to `Cell.norm`
  (`Res.Sim`: the same bytes up to it and tags, knowledge and ghost state), the framework's reading
  of a rest (`Inv.congrX`, `FOwned.congrRest`); `Pair.inv_side`, `FreeRes.congrX` and
  `Transfer.congrX` give the exact side back.
  `Pair.U_stable`, `U_setA`, `U_atStop`, `U_partStep` and `U_partTick` lift them to `Pair.U` for
  `A`'s `Fits.stable`, `Fits.nap`'s `hU`, `Fits.atStop`, a part step's continuation and
  `Fits.kstep`'s `PartTick`; `U_relabel` a relabel of one thread that keeps its place and held
  resource at `B`.
* **`B` kept across a primitive's own steps** (item (4)): `Keeps.stepIn` once for every native
  step whose frame (`FStepIn`) covers `B`'s side; `Keeps.partStep` is an instance, and
  `Keeps.wordStep`/`U_wordStep` the atomic op at another shared word (`Inv.wordStep`'s facts),
  `Keeps.wordRun` an actual run of it; a futex wait's sleep at another word (`Keeps.sleepAt`,
  `LockWord.WInv.push`) and a wake at another key (`Keeps.wakeAt`); a relabel that keeps `B`'s
  places (`Keeps.relabel`) and a change of the queue (`Keeps.queue`). A condition's steps:
  `ZigLean/Sep/Full/CondProd.lean`.
* **Both locks' `Fits` from the client's** (item (4)): `Pair.fits` builds `A`'s `Fits` at
  `Pair.U B U` from the client's obligations at its own rest `U` (and that a thread `A`'s code
  queues is `away` from `B`), `fitsEmpty` for a lock without a primitive, and `fitsOrder` both
  locks' for a lock order (`holdLive_inner`, `holdLive_none`). `FLock.prodA`/`prodB`/`prodPair`:
  two locks of one ghost value (`FLG2`), an instance. The client `Proofs/Sync/NestedMutex.lean`
  nests two mutexes over every `MutexImpl`.
-/

namespace Zig
namespace Full

open FAssn Conc Proto

/-! ## Regrouping the parts -/

/-- Two resources and two others, regrouped: the middle two change places. -/
theorem rsum_rsum_comm {a b c d : Res} (hbc : FHeap.Disjoint b.heap c.heap) :
    rsum (rsum a b) (rsum c d) = rsum (rsum a c) (rsum b d) := by
  rw [rsum_assoc, ← rsum_assoc (a := b), rsum_comm hbc, rsum_assoc, ← rsum_assoc]

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

/-- The parts own their resources: a part of an exact composition is in a part. -/
theorem owns_right (ho : FOwned (fun u => rsum (a u) (b u)) rO m) {u : ThreadId}
    (hu : u < m.threads.size) : m.OwnsRes u (b u) :=
  (ho.owns u hu).sepR rfl rfl

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
    rsum_assoc.symm⟩, fun u hu => (ho.owns u hu).sepL rfl rfl, haout, ho.csize, ho.conc, ⟨fun u => Res.NoCur.left (ho.noCur.1 u),
    Res.noCur_rsum (Res.NoCur.right hcT) ho.noCur.2⟩⟩

/-- **A family moves from the rest into the parts**: the composition `rb` of the `b u` leaves
the rest, and each thread's part grows by `b u`, which its clock owns (`Mem.OwnsRes`). No byte
gathers two partial shares (`hg`, `Mem.OwnsRes.gather`): a whole share would need every read of
it ordered before the thread, which `OwnsRes` of the two shares does not give (`ShareRaceCX`). -/
theorem into (ho : FOwned a (rsum rb rO) m) (hb : sepN m.threads.size (partOf b) rb)
    (hbO : FHeap.Disjoint rb.heap rO.heap) (hown : ∀ u < m.threads.size, m.OwnsRes u (b u))
    (hg : ∀ u < m.threads.size, ∀ l, (a u).shared l = none ∨ (b u).shared l = none)
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
  · exact (ho.owns u hu).gather (hown u hu) (hg u hu)
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

/-! ## Rests alike up to `Cell.norm` -/

/-- **Two resources alike as rests**: the same bytes up to `Cell.norm`, with the same tags, and
the same knowledge and ghost state. The framework reads a rest this way (`Inv.congrX`,
`FOwned.congrRest`, `Inv.restCell`): a native step keeps the frame's cells only up to `Cell.norm`
(a block's size and live start, `Mmap.lean`'s `munmapTail'`/`mremapShrink'`). -/
structure Res.Sim (r r' : Res) : Prop where
  heap : FHeap.Sim r.heap r'.heap
  know : r.know = r'.know
  gh : r.gh = r'.gh

namespace Res.Sim

variable {a a' b b' c : Res}

theorem refl (r : Res) : Res.Sim r r := ⟨FHeap.Sim.refl _, rfl, rfl⟩

theorem symm (h : Res.Sim a b) : Res.Sim b a := ⟨h.heap.symm, h.know.symm, h.gh.symm⟩

theorem trans (h₁ : Res.Sim a b) (h₂ : Res.Sim b c) : Res.Sim a c :=
  ⟨fun l => (h₁.heap l).trans (h₂.heap l), h₁.know.trans h₂.know, h₁.gh.trans h₂.gh⟩

theorem union (ha : Res.Sim a a') (hb : Res.Sim b b') : Res.Sim (rsum a b) (rsum a' b') :=
  ⟨ha.heap.union hb.heap, by show a.know.union b.know = _; rw [ha.know, hb.know],
    by show a.gh.add b.gh = _; rw [ha.gh, hb.gh]⟩

theorem heap_none (h : Res.Sim a b) {l : Zig.Loc} : a.heap l = Option.none ↔ b.heap l = Option.none :=
  h.heap.none

theorem disj (h : Res.Sim a b) {x : FHeap} (hd : FHeap.Disjoint b.heap x) :
    FHeap.Disjoint a.heap x := fun l => (hd l).imp h.heap_none.mpr id

theorem owned_none (h : Res.Sim a b) {l : Zig.Loc} :
    a.owned l = Option.none ↔ b.owned l = Option.none :=
  Decidable.not_iff_not.mp (show a.owned l ≠ Option.none ↔ b.owned l ≠ Option.none by
    rw [Res.owned_ne, Res.owned_ne, h.gh, ne_eq, ne_eq, h.heap_none])

theorem excl_none (h : Res.Sim a b) {l : Zig.Loc} :
    a.excl l = Option.none ↔ b.excl l = Option.none :=
  Decidable.not_iff_not.mp (show a.excl l ≠ Option.none ↔ b.excl l ≠ Option.none by
    rw [Res.excl_ne, Res.excl_ne, h.gh, ne_eq, ne_eq, h.heap_none])

end Res.Sim

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

/-- **A part of the rest beside the word owns no byte of the word**: the rest holds the word's
bytes as cells, so no share of them (`FOwned.rest_noShare`). -/
theorem off_owned_of_rest {own : ThreadId → Res} {rO rc : Res}
    (ho : FOwned own (rsum (L.wordR m) rO) m) (hb : L.BlkOk m) (hO : L.Off rO.heap.erase)
    (hsub : ∀ l, rc.owned l ≠ none → rO.owned l ≠ none) : L.Off rc.owned := fun x h1 h2 =>
  Classical.byContradiction fun hn => by
    rcases Res.owned_ne.mp (hsub _ hn) with hh | hp
    · exact hh (off_erase.mp hO _ ⟨rfl, h1, h2⟩)
    · refine ho.rest_noShare (l := (L.b, x)) ?_ ?_
      · simp only [FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
        exact fun h => absurd h (wordR_some hb ⟨rfl, h1, h2⟩)
      · simp only [Ghost.add_share]
        exact SCell.pos_add_iff.mpr (.inr hp)

/-- **A thread joins the futex queue at another key** (the sleep of another word's futex wait,
`FCond.MStep.sleep`; `WInv.waitOff`/`waitNest` for the whole wait): the invariant holds with
`(t, k)` in the queue, when `t` is `away` from the lock or holds it at `holdsAway` with `k` in its
nest (`Queue`), unless `t` was queued at `k` already. -/
theorem WInv.push {P : ThreadId → LPh} {t : ThreadId} {k : FutexKey} (hi : L.WInv P m)
    (hk : k ≠ L.key m)
    (hph : (t, k) ∉ m.waiters → P t = .away ∨ (P t = .holdsAway ∧ L.NestKey m k)) :
    L.WInv P { m with waiters := m.waiters.push (t, k) } := by
  refine hi.requeue (c := m.current) (wk := m.woken) (fun w hw => ?_) fun hw => ?_
  · rcases Array.mem_push.mp hw with hw | rfl
    · exact hi.fq w hw
    · by_cases hm : (t, k) ∈ m.waiters
      · exact hi.fq _ hm
      · rcases hph hm with h | ⟨h1, h2⟩
        · exact .inr (.inl ⟨hk, h⟩)
        · exact .inr (.inr ⟨hk, h1, h2⟩)
  · have hw' : L.Waits m m.waiters := by
      unfold LockWord.Waits at hw ⊢
      rw [Array.any_push] at hw
      simpa [hk] using hw
    obtain ⟨v, hv, hvq, h1, h2⟩ := hi.wit hw'
    refine ⟨v, hv, fun hvw => ?_, h1, h2⟩
    have hvq' : m.waiters.any (·.1 == v) = false := hvq hvw
    have hvt : v ≠ t := by
      rintro rfl
      by_cases hm : (v, k) ∈ m.waiters
      · exact ne_of_notQ hvq' hm rfl
      · rcases hph hm with h | ⟨h, -⟩ <;> rw [h] at hvw <;> cases hvw
    show (m.waiters.push (t, k)).any (·.1 == v) = false
    rw [Array.any_push, hvq']; simp [Ne.symm hvt]

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
  free : L.Free G → L.R G rL ∧ L.toLockWord.OwnsRes (L.pl G) m rL
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

/-- **The facts at a new ghost value and memory**: the same places and held resources, the
resource kept (`hR`), the word invariant and the free resource's ownership at the new memory, and
each part apart from its held resource. -/
theorem Facts.relabel {G' : ThreadId → γ} {m' : Mem} (hf : L.Facts G m rL)
    (hph : ∀ u, L.ph (G' u) = L.ph (G u)) (hheld : ∀ u, L.held (G' u) = L.held (G u))
    (hR : ∀ r, L.R G r → L.R G' r) (hw : L.WInv (L.pl G) m')
    (hown : L.Free G → L.toLockWord.OwnsRes (L.pl G) m' rL)
    (hpd : ∀ u, FHeap.Disjoint (L.part (G' u)).heap (L.held (G' u)).heap) :
    L.Facts G' m' rL := by
  have hpl : L.pl G' = L.pl G := funext hph
  have hfree : L.Free G' ↔ L.Free G := by unfold FLock.Free; rw [hpl]
  refine ⟨by rw [hpl]; exact hw, hf.loff, fun hF => ⟨hR rL (hf.free (hfree.mp hF)).1, ?_⟩,
    fun hF => hf.busy fun h' => hF (hfree.mpr h'), hpd, fun u hu => ?_, fun u hu => ?_⟩
  · rw [hpl]; exact hown (hfree.mp hF)
  · rw [hph u] at hu; rw [hheld u]; exact hf.idle u hu
  · rw [hph u] at hu; rw [hheld u]; exact hR _ (hf.res u hu)

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

variable (L) in
/-- **No thread's part and held resource share a byte partially** (`FOwned.into`'s `hg`): moving
the held resources into the parts gathers no read share (`Mem.OwnsRes.gather`; engine ledger
#share-gather). -/
def NoGatherHeld (G : ThreadId → γ) (m : Mem) : Prop :=
  ∀ u < m.threads.size, ∀ l, (L.base G m u).shared l = none ∨ (L.heldOf G m u).shared l = none

/-- A lock whose resource holds no partial share gathers none (`FAssn.Unshared`): a holder's
resource satisfies `R`, any other thread holds nothing. -/
theorem NoGatherHeld.of_R (hR : ∀ G, (L.R G).Unshared) (hf : L.Facts G m rL) :
    L.NoGatherHeld G m := fun u _ l => .inr (by
  unfold heldOf; split
  · exact FAssn.Unshared.emp _ ⟨rfl, rfl, rfl⟩ l
  · cases e : (L.ph (G u)).held
    · rw [hf.idle u e]; exact FAssn.Unshared.emp _ ⟨rfl, rfl, rfl⟩ l
    · exact hR G _ (hf.res u e) l)

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
  owns : ∀ u < m.threads.size, m.OwnsRes u (B.heldOf G m u)
  hoff : B.Off rH.heap.erase
  xdisj : FHeap.Disjoint (rsum rL rH).heap rX.heap
  xoff : B.Off rX.heap.erase

/-- **`B`'s side is apart from the protocol's own rest** (`Keeps.xdisj`, `Keeps.xoff`). -/
theorem Keeps.side_disj {B : FLock γ} {G : ThreadId → γ} {m : Mem} {rL rH rX : Res}
    (hk : B.Keeps G m rL rH rX) : FHeap.Disjoint (side B m rL rH).heap rX.heap :=
  FHeap.disjoint_union_left.mpr ⟨LockWord.off_disj hk.xoff, hk.xdisj⟩

/-- **A new ghost value of `t` with its place and held resource at `B` keeps every thread's.** -/
theorem keep_upd (B : FLock γ) {t : ThreadId} {g : γ} (hph : B.ph g = B.ph (G t))
    (hheld : B.held g = B.held (G t)) (u : ThreadId) :
    B.ph (upd G t g u) = B.ph (G u) ∧ B.held (upd G t g u) = B.held (G u) := by
  by_cases e : u = t
  · subst e; rw [upd_self]; exact ⟨hph, hheld⟩
  · rw [upd_ne _ _ e]; exact ⟨rfl, rfl⟩

/-- **A new ghost value of `t` with its part and held resource at the lock keeps each part apart
from its held resource.** -/
theorem Facts.pdisj_upd (hf : L.Facts G m rL) {t : ThreadId} {g : γ}
    (hpart : L.part g = L.part (G t)) (hheld : L.held g = L.held (G t)) (u : ThreadId) :
    FHeap.Disjoint (L.part (upd G t g u)).heap (L.held (upd G t g u)).heap := by
  by_cases e : u = t
  · subst e; rw [upd_self, hpart, hheld]; exact hf.pdisj u
  · rw [upd_ne _ _ e]; exact hf.pdisj u

/-- **The side of a lock that protects nothing owns only the lock's word** (`R = emp`): its free
resource and its holders' resources are empty. -/
theorem Keeps.side_owned {B : FLock γ} {rH : Res} (hR : ∀ G, B.R G = emp)
    (hk : B.Keeps G m rL rH rX) {l : Zig.Loc} (h : (side B m rL rH).owned l ≠ none) : B.In l := by
  have hemp : ∀ r, emp r → r.owned l = none := fun r ⟨he, _, hg⟩ =>
    Res.owned_plain hg (by rw [he]; rfl)
  have hf := hk.facts
  rcases (Res.owned_sep rfl rfl).mp h with h | h
  · exact Classical.byContradiction fun hn => h (cellsAt_owned_none hn)
  rcases (Res.owned_sep rfl rfl).mp h with h | h
  · refine absurd ?_ h
    by_cases hF : B.Free G
    · exact hemp _ (by have h' := (hf.free hF).1; rwa [hR] at h')
    · rw [hf.busy hF]; exact hemp _ ⟨rfl, rfl, rfl⟩
  · obtain ⟨j, -, rj, rfl, hj⟩ := sepN_cover_owned hk.held h
    refine absurd ?_ hj
    unfold FLock.heldOf; split
    · exact hemp _ ⟨rfl, rfl, rfl⟩
    · cases e : (B.ph (G j)).held
      · rw [hf.idle j e]; exact hemp _ ⟨rfl, rfl, rfl⟩
      · exact hemp _ (by have h' := hf.res j e; rwa [hR] at h')

/-- **What a thread holds of a lock that protects nothing has no bytes** (`R = emp`). -/
theorem Facts.held_heap (hR : ∀ G, L.R G = emp) (hf : L.Facts G m rL) (u : ThreadId) :
    (L.held (G u)).heap = FHeap.empty := by
  cases e : (L.ph (G u)).held
  · rw [hf.idle u e]
  · have h := hf.res u e
    rw [hR] at h
    exact h.1

/-- **The free resource next to a rest alike** (`Res.Sim`, as `Inv.congrX`). -/
theorem FreeRes.congrX {rX' : Res} (h : L.FreeRes G rX m rL) (hs : Res.Sim rX' rX) :
    L.FreeRes G rX' m rL :=
  have hw := (Res.Sim.refl (L.wordR m)).union ((Res.Sim.refl rL).union hs)
  ⟨h.1.congrRest hw.heap hw.know hw.gh, h.2.1, fun l => (h.2.2.1 l).imp id hs.heap_none.mpr, h.2.2.2⟩

/-- **The resource a step moves, next to a rest alike** (`FreeRes.congrX`). -/
theorem Transfer.congrX {rX' : Res} {m' : Mem} {t : ThreadId} {p : LPh} {h : Res}
    (htr : L.Transfer G rX m m' t p h) (hs : Res.Sim rX' rX) : L.Transfer G rX' m m' t p h :=
  ⟨htr.1, htr.2.1, fun a b => (htr.2.2.1 a b).imp id fun hf => hf.congrX hs,
    fun a b => (htr.2.2.2 a b).congrX hs⟩

end FLock

namespace FLock.Pair

variable {γ : Type} {A B : FLock γ} {G : ThreadId → γ} {m : Mem}

/-- **The two-lock product's rest for `A`** (`FLock.Fits.inv`): the rest of `A`'s invariant is
`B`'s side `sB` next to the protocol's own rest `rX`, `B` is kept, and the protocol's own `U` holds
at `rX`. The rest stores `B`'s side as it was when it entered the rest: alike to `side B m` up to
`Cell.norm` (`Res.Sim`), the framework's reading of a rest (`Inv.restCell`, `Inv.congrX`,
`FOwned.congrRest`). A native step keeps the cells of its frame only so far, and a primitive's
step on a thread's own part fixes the rest after it (`FSem.Move.hold`, `FPrim.ofWords`).
Counterexample to an exact side: a hold step that unmaps page 2 of a two-page mapping changes the
size field of `B`'s word cells, so the rest after it equals `side B m'` for no `U` (ledger
#two-lock-product, fifth obstruction; coordinator decision 2026-11-09, option (A), #741; rejected:
(B) primitives rebuild their rest, which changes `FSem`/`FCond` `Fits`, and (C) a `Sim` closure for
the semaphore's view only, a second mechanism). -/
def U (B : FLock γ) (U : (ThreadId → γ) → Res → Mem → Prop) :
    (ThreadId → γ) → Res → Mem → Prop := fun G rXA m =>
  ∃ sB rL rH rX, rXA = rsum sB rX ∧ Res.Sim sB (side B m rL rH) ∧ B.Keeps G m rL rH rX ∧
    U G rX m

/-- **`A`'s invariant at the exact side** (`Inv.congrX`): the rest of `Pair.U` is alike to `B`'s
side next to `rX`. -/
theorem inv_side {sB rL rH rX : Res} (hi : A.Inv G (rsum sB rX) m)
    (hs : Res.Sim sB (side B m rL rH)) : A.Inv G (rsum (side B m rL rH) rX) m :=
  have h := hs.symm.union (Res.Sim.refl rX)
  hi.congrX h.heap h.know h.gh

/-- **Either lock's view gives the other's** (module doc): `A`'s invariant with `B`'s side in its
rest, and `B` kept, give `B`'s invariant with `A`'s side in its rest, and `A` kept. The holders'
resources of `A` move out of the threads' parts into `B`'s rest, and those of `B` move in,
gathering no read share (`hg`; `NoGatherHeld.of_R` for a resource without partial shares). -/
theorem swap (hp : A.Pair B) {rLB rHB rX : Res}
    (hi : A.Inv G (rsum (side B m rLB rHB) rX) m) (hk : B.Keeps G m rLB rHB rX)
    (hg : B.NoGatherHeld G m) :
    ∃ rLA rHA, B.Inv G (rsum (side A m rLA rHA) rX) m ∧ A.Keeps G m rLA rHA rX := by
  obtain ⟨rLA, ⟨hoA0, hLoffA, hLXA, -, -⟩, hfA⟩ := hi.facts
  have hxA := hi.xoff
  have hoA := hoA0
  rw [FLock.own_eq] at hoA
  obtain ⟨rHA, hHA, hdHA, ho1⟩ := hoA.out hfA.heldOf_disj fun u hu => hfA.base_out hoA0 hu
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
  have ho2 := ho1.into hk.held hHB_O hk.owns hg fun u hu => hk.facts.heldOf_out hu
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
  · exact hoA.owns_right hu
  · exact LockWord.off_of_wordDisj hfA.w.blk hdA.1
  · have := LockWord.off_erase.mp hxA l hl
    simp only [FHeap.union_apply, Option.or_eq_none_iff] at this
    exact this.2

/-- `A`'s `set` is invisible to `B`: the same places, parts and resources. -/
theorem B_upd (hp : A.Pair B) (G : ThreadId → γ) (t : ThreadId) (p : LPh) (h : Res)
    (u : ThreadId) :
    B.ph (upd G t (A.set (G t) p h) u) = B.ph (G u) ∧
      B.part (upd G t (A.set (G t) p h) u) = B.part (G u) ∧
      B.held (upd G t (A.set (G t) p h) u) = B.held (G u) := by
  by_cases e : u = t
  · subst e; rw [upd_self]
    exact ⟨hp.ph_ab _ _ _, by rw [← hp.part, ← hp.part, A.part_set], hp.held_ab _ _ _⟩
  · rw [upd_ne _ _ e]; exact ⟨rfl, rfl, rfl⟩

/-- **A step of `A`'s code keeps what the product keeps of `B`** (`LockWord.WInv.otherStep`,
`LockWord.Owns.otherStep`), at the same free resource, holders' resources and rest; `B`'s word
cells stay. A step that queues `t` (`A`'s futex wait) needs `t` away from `B`, or holding `B` at
`holdsAway` with `A`'s futex key in `B`'s nest. -/
theorem Keeps.otherStep (hp : A.Pair B) {rL rH rX : Res} {t : ThreadId} {m' : Mem} {p : LPh}
    {h : Res} (hi : A.Inv G (rsum (side B m rL rH) rX) m) (hk : B.Keeps G m rL rH rX)
    (hs : A.Step t m m')
    (ht : (∃ w ∈ m'.waiters, w ∉ m.waiters) →
      B.ph (G t) = .away ∨ (B.ph (G t) = .holdsAway ∧ B.toLockWord.NestKey m (A.key m))) :
    side B m' rL rH = side B m rL rH ∧ B.Keeps (upd G t (A.set (G t) p h)) m' rL rH rX := by
  have hap : B.ApartL A.toLockWord := hp.apart.symm
  have hU := hp.B_upd G t p h
  have hheld : B.heldOf (upd G t (A.set (G t) p h)) m' = B.heldOf G m := funext fun u => by
    unfold heldOf; rw [LockWord.joinedB_congr hs.threads, (hU u).2.2]
  obtain ⟨rLA, ⟨ho, hLoffA, -, -, -⟩, -⟩ := hi.facts
  have hbA : A.BlkOk m := hi.w.blk
  have hbl : A.b < m.blocks.size := by
    obtain ⟨blk, hb, -⟩ := hbA; exact (Array.getElem?_eq_some_iff.mp hb).1
  have hl : m.LiveLayout := ho.conc.2.1
  -- the rest beside `A`'s word, without `A`'s word bytes
  have hO : A.Off (rsum rLA (rsum (side B m rL rH) rX)).heap.erase :=
    LockWord.off_erase.mpr fun l hl' => by
      show (rLA.heap ∪ (rsum (side B m rL rH) rX).heap) l = none
      rw [FHeap.union_apply, LockWord.off_erase.mp hLoffA l hl',
        LockWord.off_erase.mp hi.xoff l hl']; rfl
  have hsub : ∀ {rc : Res}, (∀ l, rc.owned l ≠ none →
      (rsum (side B m rL rH) rX).owned l ≠ none) → A.Off rc.owned := fun hc =>
    LockWord.off_owned_of_rest ho hbA hO fun l hl' =>
      (Res.owned_sep rfl rfl).mpr (.inr (hc l hl'))
  have hLown : A.Off rL.owned := hsub fun l hl' => (Res.owned_sep rfl rfl).mpr (.inl
    ((Res.owned_sep rfl rfl).mpr (.inr ((Res.owned_sep rfl rfl).mpr (.inl hl')))))
  have hHown : ∀ u < m.threads.size, A.Off (B.heldOf G m u).owned := fun u hu => by
    obtain ⟨_, rfl, hj⟩ := sepN_owned hk.held hu
    exact hsub fun l hl' => (Res.owned_sep rfl rfl).mpr (.inl
      ((Res.owned_sep rfl rfl).mpr (.inr ((Res.owned_sep rfl rfl).mpr (.inr (hj l hl'))))))
  have hf := hk.facts
  refine ⟨by unfold FLock.side; rw [LockWord.wordR_otherStep hs hap],
    ⟨hf.relabel (fun u => (hU u).1) (fun u => (hU u).2.2) (fun r => (hp.R_ab G t p h r).mpr)
      (hf.w.otherStep hs hap (hap.key_ne hl hf.w.blk hbA) ht)
      (fun hF => ⟨(hf.free hF).2.1.otherStep hs hap hLown.excl hbl fun _ h => h,
        (hf.free hF).2.2.otherStep hs hap hLown.shared hbl fun _ h => h⟩)
      (fun u => by rw [(hU u).2.1, (hU u).2.2]; exact hf.pdisj u),
    ?_, fun u hu => ?_, hk.hoff, hk.xdisj, hk.xoff⟩⟩
  · rw [hheld, hs.threads]; exact hk.held
  · rw [hs.threads] at hu; rw [hheld]
    refine (hs.rest hbA).ownsRes (hk.owns u hu) fun l hl => ?_
    obtain ⟨b, x⟩ := l
    obtain ⟨h1, h2, h3⟩ := hl; simp only at h1 h2 h3; subst h1
    exact hHown u hu x h2 h3

/-- **A change of the ghost values that keeps `B`'s places and held resources keeps what the
product keeps of `B`**, at the same memory, free and holders' resources, and a new protocol rest
`rX'` (with its facts in `Keeps`). -/
theorem Keeps.relabel {G' : ThreadId → γ} {rL rH rX rX' : Res} (hk : B.Keeps G m rL rH rX)
    (hG : ∀ u, B.ph (G' u) = B.ph (G u) ∧ B.held (G' u) = B.held (G u))
    (hRk : ∀ r, B.R G r → B.R G' r)
    (hpd : ∀ u, FHeap.Disjoint (B.part (G' u)).heap (B.held (G' u)).heap)
    (hxd : FHeap.Disjoint (rsum rL rH).heap rX'.heap) (hxo : B.Off rX'.heap.erase) :
    B.Keeps G' m rL rH rX' := by
  have hf := hk.facts
  have hheld : B.heldOf G' m = B.heldOf G m := funext fun u => by
    unfold heldOf; rw [(hG u).2]
  exact ⟨hf.relabel (fun u => (hG u).1) (fun u => (hG u).2) hRk hf.w (fun hF => (hf.free hF).2)
    hpd, by rw [hheld]; exact hk.held, by rw [hheld]; exact hk.owns, hk.hoff, hxd, hxo⟩

/-- **A change of `A`'s coordinates keeps what the product keeps of `B`**, at the same memory
(e.g. `A`'s nap and unnap, `FLock.Fits.nap`/`unnap`). -/
theorem Keeps.setA (hp : A.Pair B) {rL rH rX : Res} {t : ThreadId} {p : LPh} {h : Res}
    (hk : B.Keeps G m rL rH rX) : B.Keeps (upd G t (A.set (G t) p h)) m rL rH rX := by
  have hU := hp.B_upd G t p h
  exact Keeps.relabel hk (fun u => ⟨(hU u).1, (hU u).2.2⟩) (fun r => (hp.R_ab G t p h r).mpr)
    (fun u => by rw [(hU u).2.1, (hU u).2.2]; exact hk.facts.pdisj u) hk.xdisj hk.xoff

/-- **A relabel of `t` at `A` keeps the product's rest** (the `hU` of `FLock.Fits.nap`, `unnap`,
`goAway` and `unaway` at `A`, in their form: `t`'s ghost value `g`), when the protocol's own `U`
is kept. -/
theorem U_setA (hp : A.Pair B) {U : (ThreadId → γ) → Res → Mem → Prop} {rXA : Res} {t : ThreadId}
    {g : γ} {p : LPh} {h : Res} (hU : Pair.U B U (upd G t g) rXA m)
    (hcl : ∀ rX, U (upd G t g) rX m → U (upd G t (A.set g p h)) rX m) :
    Pair.U B U (upd G t (A.set g p h)) rXA m := by
  obtain ⟨sB, rL, rH, rX, rfl, hs, hk, hu⟩ := hU
  have hk' := Keeps.setA (t := t) (p := p) (h := h) hp hk
  rw [upd_self, upd_upd] at hk'
  exact ⟨sB, rL, rH, rX, rfl, hs, hk', hcl rX hu⟩

/-- **A relabel of `t` that keeps its place and held resource at `B` keeps the product's rest**
(`Keeps.relabel` at one thread, the same memory and rest; e.g. a primitive's step that moves a
resource into `t`'s part, `FRw.Fits.utake`): `B`'s resource stays (`hR`) and `t`'s new part is
apart from what it holds of `B` (`hpd`, given `B`'s facts), when the protocol's own `U` is kept. -/
theorem U_relabel {U : (ThreadId → γ) → Res → Mem → Prop} {rXA : Res} {t : ThreadId} {g g' : γ}
    (hU : Pair.U B U (upd G t g) rXA m) (hph : B.ph g' = B.ph g) (hheld : B.held g' = B.held g)
    (hR : ∀ r, B.R (upd G t g) r → B.R (upd G t g') r)
    (hpd : ∀ rL, B.Facts (upd G t g) m rL → FHeap.Disjoint (B.part g').heap (B.held g).heap)
    (hcl : ∀ sB rL rH rX, rXA = rsum sB rX → Res.Sim sB (side B m rL rH) →
      B.Keeps (upd G t g') m rL rH rX → U (upd G t g) rX m → U (upd G t g') rX m) :
    Pair.U B U (upd G t g') rXA m := by
  obtain ⟨sB, rL, rH, rX, rfl, hs, hk, hu⟩ := hU
  have hk' : B.Keeps (upd G t g') m rL rH rX := Keeps.relabel hk
    (fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, upd_self]; exact ⟨hph, hheld⟩
      · rw [upd_ne _ _ e, upd_ne _ _ e]; exact ⟨rfl, rfl⟩)
    hR
    (fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, hheld]; exact hpd rL hk.facts
      · have h := hk.facts.pdisj u
        rw [upd_ne _ _ e] at h ⊢; exact h)
    hk.xdisj hk.xoff
  exact ⟨sB, rL, rH, rX, rfl, hs, hk', hcl sB rL rH rX rfl hs hk' hu⟩

/-- **A change of the futex queue, the woken threads and the current thread keeps what the product
keeps of `B`**, given `B`'s word invariant after it (`LockWord.WInv.requeue`, `WInv.push`,
`WInv.wakeOff`). -/
theorem Keeps.queue {rL rH rX : Res} (hk : B.Keeps G m rL rH rX) {c : ThreadId}
    {ws : Array (ThreadId × FutexKey)} {wk : Array ThreadId}
    (hw : B.WInv (B.pl G) { m with current := c, waiters := ws, woken := wk }) :
    B.Keeps G { m with current := c, waiters := ws, woken := wk } rL rH rX :=
  { hk with facts := { hk.facts with w := hw } }

/-- **A stop keeps what the product keeps of `B`** (`current := t`). -/
theorem Keeps.cur {rL rH rX : Res} (hk : B.Keeps G m rL rH rX) (t : ThreadId) :
    side B { m with current := t } rL rH = side B m rL rH ∧
      B.Keeps G { m with current := t } rL rH rX :=
  ⟨rfl, Keeps.queue hk (hk.facts.w.current t)⟩

/-- **A step of `A`'s code keeps the product's rest for `A`** (`FLock.Fits.stable` of `A` for
`Pair.U B U`), when the protocol's own `U` is stable under it. -/
theorem U_stable (hp : A.Pair B) {U : (ThreadId → γ) → Res → Mem → Prop} {rXA : Res}
    {t : ThreadId} {m' : Mem} {p : LPh} {h : Res} (hi : A.Inv G rXA m) (hU : Pair.U B U G rXA m)
    (hs : A.Step t m m')
    (ht : (∃ w ∈ m'.waiters, w ∉ m.waiters) →
      B.ph (G t) = .away ∨ (B.ph (G t) = .holdsAway ∧ B.toLockWord.NestKey m (A.key m)))
    (hcl : ∀ sB rL rH rX, rXA = rsum sB rX → Res.Sim sB (side B m rL rH) →
      B.Keeps G m rL rH rX → U G rX m → U (upd G t (A.set (G t) p h)) rX m') :
    Pair.U B U (upd G t (A.set (G t) p h)) rXA m' := by
  obtain ⟨sB, rL, rH, rX, rfl, hsB, hk, hu⟩ := hU
  obtain ⟨he, hk'⟩ := Keeps.otherStep (p := p) (h := h) hp (inv_side hi hsB) hk hs ht
  exact ⟨sB, rL, rH, rX, rfl, by rw [he]; exact hsB, hk', hcl sB rL rH rX rfl hsB hk hu⟩

/-- **A stop keeps the product's rest** (`FLock.Fits.atStop`), when the protocol's own `U` is
kept. -/
theorem U_atStop {U : (ThreadId → γ) → Res → Mem → Prop} {rXA : Res} (t : ThreadId)
    (hU : Pair.U B U G rXA m) (hcl : ∀ rX, U G rX m → U G rX { m with current := t }) :
    Pair.U B U G rXA { m with current := t } := by
  obtain ⟨sB, rL, rH, rX, rfl, hsB, hk, hu⟩ := hU
  obtain ⟨he, hk'⟩ := Keeps.cur hk t
  exact ⟨sB, rL, rH, rX, rfl, by rw [he]; exact hsB, hk', hcl rX hu⟩

/-- **A step whose frame holds `B`'s side keeps what the product keeps of `B`** (the one rule
for every step outside `B`'s code that is no step of `A`'s lock code: a step on a part, a
primitive's step such as an atomic op at another word that moves a resource between the rest and
the thread's part, or a store of a semaphore's count under its mutex). The step is an `FStepIn`
whose frame `hF` holds the bytes of `B`'s side (its word, free resource and holders' resources)
and whose read shares `hR` hold none of their exclusive bytes; `B`'s word cells stay up to
`Cell.norm` (`hcells`). The new ghost values `G'` keep every thread's place and held resource at
`B`, and `B`'s resource; each part stays apart from its held resource (`hpd`); the protocol's
rest may change to `rX'` (`hxd`, `hxo`: its facts in `Keeps`). Then `B`'s side is the same up to
`Cell.norm` and `B` is kept at the same free and holders' resources. -/
theorem Keeps.stepIn {G' : ThreadId → γ} {rL rH rX rX' : Res} {m' : Mem} {hF hR : Heap}
    (hk : B.Keeps G m rL rH rX) (hs : FStepIn hF m m' hR)
    (hFo : ∀ l, (side B m rL rH).owned l ≠ none → hF l ≠ none)
    (hFx : ∀ l, (side B m rL rH).excl l ≠ none → hR l = none)
    (hcells : ∀ l, B.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm)
    (hG : ∀ u, B.ph (G' u) = B.ph (G u) ∧ B.held (G' u) = B.held (G u))
    (hRk : ∀ r, B.R G r → B.R G' r)
    (hpd : ∀ u, FHeap.Disjoint (B.part (G' u)).heap (B.held (G' u)).heap)
    (hxd : FHeap.Disjoint (rsum rL rH).heap rX'.heap) (hxo : B.Off rX'.heap.erase) :
    FHeap.Sim (side B m' rL rH).heap (side B m rL rH).heap ∧ B.Keeps G' m' rL rH rX' := by
  have hf := hk.facts
  have hbB : B.BlkOk m := hf.w.blk
  have hsim : FHeap.Sim (side B m' rL rH).heap (side B m rL rH).heap := by
    intro l
    show (((B.wordR m').heap l).or ((rsum rL rH).heap l)).map (fun fc => (fc.cell.norm, fc.atom)) =
      (((B.wordR m).heap l).or ((rsum rL rH).heap l)).map (fun fc => (fc.cell.norm, fc.atom))
    by_cases hl : B.In l
    · have := hcells l hl
      rw [cellsAt_of hl, cellsAt_of hl]
      cases e : m.heap l <;> cases e' : m'.heap l <;> simp_all [Option.map]
    · rw [cellsAt_none hl, cellsAt_none hl]
  -- `B`'s word bytes are cells of the side: in the frame, not among its read shares
  have hwH : ∀ x, B.o ≤ x → x < B.o + 4 → (side B m rL rH).heap (B.b, x) ≠ none :=
    fun x h1 h2 hn => by
      refine LockWord.wordR_some hbB (l := (B.b, x)) ⟨rfl, h1, h2⟩ ?_
      have hn' : ((B.wordR m).heap (B.b, x)).or ((rsum rL rH).heap (B.b, x)) = none := hn
      exact (Option.or_eq_none_iff.mp hn').1
  have hwF : ∀ x, B.o ≤ x → x < B.o + 4 → hF (B.b, x) ≠ none :=
    fun x h1 h2 => hFo _ (Res.owned_of_heap (hwH x h1 h2))
  have hwR : ∀ x, B.o ≤ x → x < B.o + 4 → hR (B.b, x) = none :=
    fun x h1 h2 => hFx _ (Res.excl_of_heap (hwH x h1 h2))
  have hjb : joinedB m' = joinedB m := LockWord.joinedB_congr hs.threads
  have hheldOf : B.heldOf G' m' = B.heldOf G m := funext fun u => by
    unfold heldOf; rw [hjb, (hG u).2]
  have hok : ∀ i l, B.Loc m i l → l.len = 4 := fun i l hl => (hf.w.loc.ok i l hl).1
  refine ⟨hsim, hf.relabel (fun u => (hG u).1) (fun u => (hG u).2) hRk
      (hf.w.stepIn hs hwF hwR fun x h1 h2 => hcells _ ⟨rfl, h1, h2⟩)
      (fun hfr => (hf.free hfr).2.stepIn hs (fun l hl => hFo l ((Res.owned_sep rfl rfl).mpr
          (.inr ((Res.owned_sep rfl rfl).mpr (.inl hl))))) hwF hok
        fun l hl => hFx l (Res.excl_sep rfl rfl (.inr (Res.excl_sep rfl rfl (.inl hl))))) hpd,
    by rw [hheldOf, hs.threads]; exact hk.held, fun u hu => ?_, hk.hoff, hxd, hxo⟩
  rw [hs.threads] at hu; rw [hheldOf]
  by_cases e : u = m.current
  · rw [e]
    have := (hk.owns _ (e ▸ hu)).fstepCur hs
    rwa [hs.current] at this
  obtain ⟨_, rfl, hsj⟩ := sepN_owned hk.held hu
  obtain ⟨_, rfl, hxj⟩ := sepN_excl hk.held hu
  have hin : ∀ l, (B.heldOf G m u).owned l ≠ none → hF l ≠ none := fun l hl =>
    hFo l ((Res.owned_sep rfl rfl).mpr (.inr ((Res.owned_sep rfl rfl).mpr (.inr (hsj l hl)))))
  exact (hk.owns u hu).fstep hs e
    (fun l hl => ⟨hin l (Res.owned_of_excl hl),
      hFx l (Res.excl_sep rfl rfl (.inr (Res.excl_sep rfl rfl (.inr (hxj l hl)))))⟩)
    fun l hl => hin l (Res.owned_of_shared hl)

/-- **A native step at another shared word keeps what the product keeps of `B`** (`Keeps.stepIn`;
a primitive's atomic op, such as the reader/writer lock's at its state word): the step changes
only the bytes `W` (`RestStep`) and is an `FStepIn` in every frame without them (the atomic rules'
`Word.atomicRmw_fstep`, …; `Inv.wordStep` takes the same two facts), and `B`'s side owns no byte
of `W`. `B`'s side is then exactly the same. -/
theorem Keeps.wordStep {W : Zig.Loc → Prop} {G' : ThreadId → γ} {rL rH rX rX' : Res} {m' : Mem}
    (hk : B.Keeps G m rL rH rX) (hr : RestStep W m m')
    (hs : ∀ hF : Heap, (∀ l, W l → hF l = none) → FStepIn hF m m')
    (hW : ∀ l, W l → (side B m rL rH).owned l = none)
    (hG : ∀ u, B.ph (G' u) = B.ph (G u) ∧ B.held (G' u) = B.held (G u))
    (hRk : ∀ r, B.R G r → B.R G' r)
    (hpd : ∀ u, FHeap.Disjoint (B.part (G' u)).heap (B.held (G' u)).heap)
    (hxd : FHeap.Disjoint (rsum rL rH).heap rX'.heap) (hxo : B.Off rX'.heap.erase) :
    side B m' rL rH = side B m rL rH ∧ B.Keeps G' m' rL rH rX' := by
  have hbB : B.BlkOk m := hk.facts.w.blk
  have hBW : ∀ l, B.In l → ¬ W l := fun l hl hw => Res.owned_of_heap (fun hn => by
    have hn' : ((B.wordR m).heap l).or ((rsum rL rH).heap l) = none := hn
    exact LockWord.wordR_some hbB hl (Option.or_eq_none_iff.mp hn').1) (hW l hw)
  have hwR : B.wordR m' = B.wordR m := cellsAt_congr fun l hl => hr.heap l (hBW l hl)
  obtain ⟨-, hk'⟩ := Keeps.stepIn hk (hs _ hW) (fun _ h => h) (fun _ _ => rfl)
    (fun l hl => by rw [hr.heap l (hBW l hl)]) hG hRk hpd hxd hxo
  exact ⟨by unfold FLock.side; rw [hwR], hk'⟩

/-- **An actual op at a word apart from `B`'s side keeps what the product keeps of `B`**
(`Keeps.wordStep` at `Word.actualRun_rest` and `Word.actualRun_fstep`): `B`'s side is the same. -/
theorem Keeps.wordRun {n nb : Nat} {W : Word n nb} {X : ThreadId → Prop} {rL rH rX : Res}
    {m' : Mem} (hk : B.Keeps G m rL rH rX) (hw : W.Ok m X) (hc : m.current < m.clocks.size)
    (hop :
      (∃ (c : Nat) (ord : AtomicOrder) (v : BitVec n),
        ((atomicLoadAt c ord nb W.ptr).run m).run = some (.ok (v, m'))) ∨
      (∃ (c : Nat) (op : RmwOp) (signed : Bool) (ord : AtomicOrder) (v old : BitVec n),
        ((atomicRmwAt c op signed ord nb W.ptr v).run m).run = some (.ok (old, m'))) ∨
      (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec n) (r : Option (BitVec n)),
        ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m'))) ∨
      (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec n) (r : Option (BitVec n)),
        ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m'))) ∨
      m' = m.recordAt W.b W.o nb .atomicRead)
    (hWo : ∀ l, W.In l → (side B m rL rH).owned l = none) :
    side B m' rL rH = side B m rL rH ∧ B.Keeps G m' rL rH rX :=
  Keeps.wordStep hk (Word.actualRun_rest hw hc hop)
    (fun _ h0 => Word.actualRun_fstep hw hc (fun _ h1 h2 => h0 _ ⟨rfl, h1, h2⟩) hop) hWo
    (fun _ => ⟨rfl, rfl⟩) (fun _ h => h) hk.facts.pdisj hk.xdisj hk.xoff

/-- **The sleep of a futex wait at another word keeps what the product keeps of `B`** (an event's
or a condition's `MStep.sleep`): `t`'s read of the word, then `t` in the futex queue at the word's
key, `away` from `B` or holding it at `holdsAway` with the key in `B`'s nest (`LockWord.Queue`,
`WInv.push`), unless it was queued there. `B`'s side is the same. -/
theorem Keeps.sleepAt {W : Word 32 4} {X : ThreadId → Prop} {rL rH rX : Res} {t : ThreadId}
    (hk : B.Keeps G m rL rH rX) (hw : W.Ok { m with current := t } X) (hc : t < m.clocks.size)
    (hWo : ∀ l, W.In l → (side B m rL rH).owned l = none) (hkey : W.key m ≠ B.key m)
    (ht : (t, W.key m) ∉ m.waiters →
      B.ph (G t) = .away ∨ (B.ph (G t) = .holdsAway ∧ B.toLockWord.NestKey m (W.key m))) :
    side B { (({ m with current := t } : Mem).recordAt W.b W.o 4 .atomicRead) with
        waiters := m.waiters.push (t, W.key m) } rL rH = side B m rL rH ∧
      B.Keeps G { (({ m with current := t } : Mem).recordAt W.b W.o 4 .atomicRead) with
        waiters := m.waiters.push (t, W.key m) } rL rH rX := by
  obtain ⟨he, hkM⟩ := Keeps.wordRun (m := { m with current := t }) (Keeps.cur hk t).2 hw hc
    (.inr (.inr (.inr (.inr rfl)))) hWo
  exact ⟨he, Keeps.queue hkM (hkM.facts.w.push hkey ht)⟩

/-- **A futex wake at another key keeps what the product keeps of `B`** (an event's or a
condition's `MStep.wake`, `LockWord.WInv.wakeOff`): `B`'s side is the same. -/
theorem Keeps.wakeAt {rL rH rX : Res} {t : ThreadId} {k : FutexKey} {n : Nat} {cs : List Nat}
    {m' : Mem} (hk : B.Keeps G m rL rH rX) (hkey : k ≠ B.key m)
    (h : ((Thread.futexWake k n cs).run { m with current := t }).run = some (.ok ((), m'))) :
    side B m' rL rH = side B m rL rH ∧ B.Keeps G m' rL rH rX := by
  have hk₁ := (Keeps.cur hk t).2
  have hw := hk₁.facts.w.wakeOff hkey h
  obtain rfl := Proto.modify_ok h
  exact ⟨rfl, Keeps.queue hk₁ hw⟩

/-- **A native step at another shared word keeps the product's rest** (`FLock.Fits.kstep` at a
primitive's atomic op, `Keeps.wordStep`): the client gives, for the step, the protocol's own rest
`rX'` after it (`A`'s new rest is `B`'s side next to it) and its `U` there. -/
theorem U_wordStep {U : (ThreadId → γ) → Res → Mem → Prop} {W : Zig.Loc → Prop}
    {rXA rXA' : Res} {G' : ThreadId → γ} {m' : Mem} (hU : Pair.U B U G rXA m)
    (hr : RestStep W m m') (hs : ∀ hF : Heap, (∀ l, W l → hF l = none) → FStepIn hF m m')
    (hG : ∀ u, B.ph (G' u) = B.ph (G u) ∧ B.held (G' u) = B.held (G u))
    (hRk : ∀ r, B.R G r → B.R G' r)
    (hpd : ∀ u, FHeap.Disjoint (B.part (G' u)).heap (B.held (G' u)).heap)
    (hcl : ∀ sB rL rH rX, rXA = rsum sB rX → Res.Sim sB (side B m rL rH) →
      B.Keeps G m rL rH rX → U G rX m →
      (∀ l, W l → (side B m rL rH).owned l = none) ∧ ∃ rX', rXA' = rsum sB rX' ∧
        FHeap.Disjoint (rsum rL rH).heap rX'.heap ∧ B.Off rX'.heap.erase ∧ U G' rX' m') :
    Pair.U B U G' rXA' m' := by
  obtain ⟨sB, rL, rH, rX, rfl, hsB, hk, hu⟩ := hU
  obtain ⟨hW, rX', rfl, hxd, hxo, hu'⟩ := hcl sB rL rH rX rfl hsB hk hu
  obtain ⟨he, hk'⟩ := Keeps.wordStep hk hr hs hW hG hRk hpd hxd hxo
  exact ⟨sB, rL, rH, rX', rfl, by rw [he]; exact hsB, hk', hu'⟩

/-- **A step in the frame of `A`'s word and a rest that stores `B`'s side keeps what the product
keeps of `B`** (`Keeps.stepIn` at the frame of `Inv.wp_liftMem` and `FSem.Move.hold`: `A`'s word
and rest, read at their partial shares): the same rest stores `B`'s side at the new memory. -/
theorem Keeps.stepAt {sB rL rH rX rX' : Res} {hO : Heap} {G' : ThreadId → γ} {m' : Mem}
    (hk : B.Keeps G m rL rH rX) (hsB : Res.Sim sB (side B m rL rH))
    (hs : FStepIn (rsum (A.wordR m) (rsum sB rX)).owned m m'
      ((rsum (A.wordR m) (rsum sB rX)).shared.inter hO))
    (hcells : ∀ l, B.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm)
    (hG : ∀ u, B.ph (G' u) = B.ph (G u) ∧ B.held (G' u) = B.held (G u))
    (hRk : ∀ r, B.R G r → B.R G' r)
    (hpd : ∀ u, FHeap.Disjoint (B.part (G' u)).heap (B.held (G' u)).heap)
    (hxd : FHeap.Disjoint (rsum rL rH).heap rX'.heap) (hxo : B.Off rX'.heap.erase) :
    Res.Sim sB (side B m' rL rH) ∧ B.Keeps G' m' rL rH rX' := by
  have hsO : ∀ l, (side B m rL rH).owned l ≠ none → sB.owned l ≠ none := fun l h e =>
    h (hsB.owned_none.mp e)
  have hsX : ∀ l, (side B m rL rH).excl l ≠ none → sB.excl l ≠ none := fun l h e =>
    h (hsB.excl_none.mp e)
  obtain ⟨hsim, hk'⟩ := Keeps.stepIn hk hs
    (fun l hl => (Res.owned_sep rfl rfl).mpr (.inr ((Res.owned_sep rfl rfl).mpr (.inl (hsO l hl)))))
    (fun l hl => Heap.inter_none (Res.excl_shared_disj
      (Res.excl_sep rfl rfl (.inr (Res.excl_sep rfl rfl (.inl (hsX l hl)))))))
    hcells hG hRk hpd hxd hxo
  exact ⟨hsB.trans ⟨hsim.symm, rfl, rfl⟩, hk'⟩

/-- **`B`'s word cells stay up to `Cell.norm` across a step after which a rest that stores `B`'s
side is `A`'s rest** (`Inv.restCell`): the rest holds them, alike to the memory's before. -/
theorem Keeps.cellsOf {sB rL rH rX rX' : Res} {G'' : ThreadId → γ} {m' : Mem}
    (hk : B.Keeps G m rL rH rX) (hsB : Res.Sim sB (side B m rL rH))
    (hi' : A.Inv G'' (rsum sB rX') m') :
    ∀ l, B.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm := by
  have hbB : B.BlkOk m := hk.facts.w.blk
  intro l hl
  obtain ⟨b, x⟩ := l
  obtain ⟨h1, h2, h3⟩ := hl; simp only at h1 h2 h3; subst h1
  cases e : m.heap (B.b, x) with
  | none => exact absurd e (hbB.cell h2 h3)
  | some c =>
    have hS : (side B m rL rH).heap (B.b, x) = some ⟨c, none⟩ := by
      show ((B.wordR m).heap (B.b, x)).or ((rsum rL rH).heap (B.b, x)) = _
      rw [cellsAt_of (show B.In (B.b, x) from ⟨rfl, h2, h3⟩), e]; rfl
    obtain ⟨fc, hfc, hn, -⟩ := hsB.heap.some hS
    have hX : (rsum sB rX').heap (B.b, x) = some fc := by
      show (sB.heap (B.b, x)).or (rX'.heap (B.b, x)) = _
      rw [hfc]; rfl
    rw [hi'.restCell hX, hn]; rfl

/-- **A step on a thread's own part in `A`'s view keeps what the product keeps of `B`**
(`Keeps.stepIn`), in the frame of `Inv.wp_liftMem` (`A`'s word and rest, with their read shares):
`B`'s word cells stay up to `Cell.norm` (from `A`'s invariant after the step, `hi'`), so the
same rest stores `B`'s side at the new memory (`Res.Sim`), and `B` is kept at the same free
resource and holders' resources, beside the protocol's rest `rX'` after the step (`hxd`, `hxo`;
`rX` itself for a step that keeps it, `U_partStep`). The thread's new ghost value `g` keeps its
place and its held resource at `B`, and `B`'s resource. -/
theorem Keeps.partStep {sB rL rH rX rX' : Res} {hO : Heap} {t : ThreadId} {g : γ} {m' : Mem}
    (hp : A.Pair B) (hk : B.Keeps G m rL rH rX) (hsB : Res.Sim sB (side B m rL rH))
    (hs : FStepIn (rsum (A.wordR m) (rsum sB rX)).owned m m'
      ((rsum (A.wordR m) (rsum sB rX)).shared.inter hO))
    (hi' : A.Inv (upd G t g) (rsum sB rX') m')
    (hph : B.ph g = B.ph (G t)) (hheld : B.held g = B.held (G t))
    (hR : ∀ r, B.R G r → B.R (upd G t g) r)
    (hxd : FHeap.Disjoint (rsum rL rH).heap rX'.heap) (hxo : B.Off rX'.heap.erase) :
    Res.Sim sB (side B m' rL rH) ∧ B.Keeps (upd G t g) m' rL rH rX' := by
  have hf := hk.facts
  obtain ⟨rLA, ho', -⟩ := hi'.rest
  -- `B`'s word cells: in `A`'s rest, so the same up to `Cell.norm`
  have hcellsL := Keeps.cellsOf hk hsB hi'
  -- the new ghost value is `G`'s at `B`
  have hU := B.keep_upd hph hheld
  have hjb : joinedB m' = joinedB m := LockWord.joinedB_congr hs.threads
  -- the thread's new part at `A` is apart from its resource at `B`, which is in `A`'s rest
  have hpdt : FHeap.Disjoint (B.part g).heap (B.held (G t)).heap := by
    by_cases hg : B.ph (G t) = .gone
    · rw [hf.idle t (by rw [hg]; rfl)]; exact fun _ => .inr rfl
    obtain ⟨ht, hjt⟩ := hf.w.live t hg
    obtain ⟨rj, hrj, hsj⟩ := sepN_mem hk.held ht
    simp only [partOf, heldOf, hjt, Bool.false_eq_true, ↓reduceIte] at hrj; subst hrj
    intro l
    refine (Classical.em ((B.held (G t)).heap l = none)).symm.imp (fun hn => ?_) id
    have hO : (rsum (A.wordR m') (rsum rLA (rsum sB rX'))).heap l ≠ none :=
      fun e => hsj l hn (rsum_heap_none.mp (rsum_heap_none.mp (hsB.heap_none.mp
        (rsum_heap_none.mp (rsum_heap_none.mp (rsum_heap_none.mp e).2).2).1)).2).2
    have := ho'.part_off (u := t) (by rw [hs.threads]; exact ht) hO
    have e' : ((A.part g).heap l).or ((A.held g).heap l) = none := by
      have h0 := this
      simp only [FLock.own, hjb, hjt, upd_self, Bool.false_eq_true, ↓reduceIte] at h0
      exact h0
    rw [← hp.part]; exact (Option.or_eq_none_iff.mp e').1
  have hpd : ∀ u, FHeap.Disjoint (B.part (upd G t g u)).heap (B.held (upd G t g u)).heap :=
    fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, hheld]; exact hpdt
      · rw [upd_ne _ _ e]; exact hf.pdisj u
  -- the frame holds `B`'s side, its exclusive bytes not among the frame's read shares
  exact Keeps.stepAt hk hsB hs hcellsL hU hR hpd hxd hxo

/-- **A step on a thread's own part in `A`'s view keeps the product's rest** (`Inv.wp_liftMem`'s
continuation): the same rest stores `B`'s side at the new memory, when the protocol's own `U` is
kept. -/
theorem U_partStep (hp : A.Pair B) {U : (ThreadId → γ) → Res → Mem → Prop} {rXA : Res}
    {hO : Heap} {t : ThreadId} {g : γ} {m' : Mem} (hU : Pair.U B U G rXA m)
    (hs : FStepIn (rsum (A.wordR m) rXA).owned m m' ((rsum (A.wordR m) rXA).shared.inter hO))
    (hi' : A.Inv (upd G t g) rXA m')
    (hph : B.ph g = B.ph (G t)) (hheld : B.held g = B.held (G t))
    (hR : ∀ r, B.R G r → B.R (upd G t g) r)
    (hcl : ∀ sB rL rH rX, rXA = rsum sB rX → Res.Sim sB (side B m rL rH) →
      B.Keeps G m rL rH rX → U G rX m → U (upd G t g) rX m') :
    Pair.U B U (upd G t g) rXA m' := by
  obtain ⟨sB, rL, rH, rX, rfl, hsB, hk, hu⟩ := hU
  obtain ⟨hsB', hk'⟩ := Keeps.partStep hp hk hsB hs hi' hph hheld hR hk.xdisj hk.xoff
  exact ⟨sB, rL, rH, rX, rfl, hsB', hk', hcl sB rL rH rX rfl hsB hk hu⟩

/-- **A tick on a part keeps the product's rest** (`A.PartTick`, for `A`'s `Fits.kstep`): the
tick changes no byte; the protocol's own `U` must be kept. -/
theorem U_partTick (hp : A.Pair B) {U : (ThreadId → γ) → Res → Mem → Prop} {t : ThreadId}
    {rXA rXA' : Res} {G' : ThreadId → γ} {m' : Mem} (hU : Pair.U B U G rXA m)
    (htick : A.PartTick t G rXA m G' rXA' m')
    (hcl : ∀ rX, U G rX m → U G' rX m') : Pair.U B U G' rXA' m' := by
  obtain ⟨-, -, -, r, -, rfl, rfl, rfl, hi'⟩ := htick
  have hpart : A.setPart (G t) r = B.setPart (G t) r := hp.setPart _ _
  exact U_partStep (hO := Heap.empty) hp hU (FStepIn.ticked m _).reads hi'
    (by rw [hpart, B.ph_setPart])
    (by rw [hpart, B.held_setPart]) (fun r' h => by rw [hpart]; exact (B.R_setPart G t r r').mpr h)
    fun _ _ _ rX _ _ _ hu => hcl rX hu

/-- **The two-lock product's invariant is the same in either lock's view**: a protocol whose
invariant is `A`'s with `Pair.U B U` is also `B`'s with `Pair.U A U` (`FLock.Fits.inv` for both
locks). Neither lock's held resources gather a read share with the parts (`hgA`, `hgB`;
`NoGatherHeld.of_R`). -/
theorem inv_iff (hp : A.Pair B) {U : (ThreadId → γ) → Res → Mem → Prop}
    (hgA : ∀ rL, A.Facts G m rL → A.NoGatherHeld G m)
    (hgB : ∀ rL, B.Facts G m rL → B.NoGatherHeld G m) :
    (∃ rX, A.Inv G rX m ∧ Pair.U B U G rX m) ↔ (∃ rX, B.Inv G rX m ∧ Pair.U A U G rX m) := by
  constructor
  · rintro ⟨_, hi, sB, rL, rH, rX, rfl, hsB, hk, hU⟩
    obtain ⟨rL', rH', hi', hk'⟩ := hp.swap (inv_side hi hsB) hk (hgB rL hk.facts)
    exact ⟨_, hi', _, rL', rH', rX, rfl, Res.Sim.refl _, hk', hU⟩
  · rintro ⟨_, hi, sA, rL, rH, rX, rfl, hsA, hk, hU⟩
    obtain ⟨rL', rH', hi', hk'⟩ := hp.symm.swap (inv_side hi hsA) hk (hgA rL hk.facts)
    exact ⟨_, hi', _, rL', rH', rX, rfl, Res.Sim.refl _, hk', hU⟩

end FLock.Pair

/-! ## Both locks' `Fits` from the product's rest

(ledger #two-lock-product, item (4).) A protocol whose invariant is `A`'s with `B` kept in its rest
(`Pair.U B U`, the client's own rest `U` at the common rest) has both locks' `FLock.Fits`:
`Pair.fits` builds `A`'s from the client's obligations, stated at `U`; `Pair.inv_swap` gives the
same invariant in `B`'s view, so `Pair.fits` at `hp.symm` builds `B`'s. The product supplies what
the other lock needs: `B` kept over `A`'s steps (`Pair.U_stable`), stops (`U_atStop`) and part
ticks (`U_partTick`). The client supplies its own `U`'s, and that a thread in `A`'s code is
`away` from `B` when one of `A`'s steps queues it, or holds `B` at `holdsAway` with `A`'s word
in `B`'s nest (`B`'s futex queue admits no other place: `LockWord.Queue`; `Pair.away_of`).
A primitive's own steps next to `A` (`kstep`) are the client's, through `Pair.U_wordStep` or
`Keeps.stepIn`. `Pair.U` stores `B`'s side up to `Cell.norm` (`Res.Sim`), as `Keeps.stepIn`
gives it, so a primitive step on a thread's own part whose rest after it is fixed
(`FSem.Move.hold`, `FPrim.ofWords`' own-part case) keeps `Pair.U` (ledger #two-lock-product, fifth
obstruction, option (A)). The client's obligations see `A`'s invariant and the resource a step
moves at `B`'s exact side (`inv_side`, `Transfer.congrX`), and `K`'s rest at the stored one.

`Pair.fitsOrder` is the lock order of two locks alone (`FPrim.empty`): `A` outer, whose holder
sleeps only at `B`'s word, `B` inner without a nest; `A`'s `holdLive` comes from `B`'s `Fits`
(`holdLive_inner`), `B`'s from `holdLive_none`.

`FLock.prodA`/`prodB` are two locks over one ghost value `FLG2 × X` (as `FLock.prod` for one),
a pair (`FLock.prodPair`). -/

namespace FLock.Pair

variable {γ : Type} {A B : FLock γ} {Tgt : Type} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop}

/-- **The other lock's view of the protocol** (`inv_iff`): a protocol whose invariant is `A`'s with
`Pair.U B U` is `B`'s with `Pair.U A U` (`FLock.Fits.inv` of `B`). -/
theorem inv_swap (hp : A.Pair B)
    (hgA : ∀ G m rL, A.Facts G m rL → A.NoGatherHeld G m)
    (hgB : ∀ G m rL, B.Facts G m rL → B.NoGatherHeld G m)
    (inv : ∀ G m, P.inv G m ↔ ∃ rX, A.Inv G rX m ∧ Pair.U B U G rX m) :
    ∀ G m, P.inv G m ↔ ∃ rX, B.Inv G rX m ∧ Pair.U A U G rX m :=
  fun G m => (inv G m).trans (hp.inv_iff (hgA G m) (hgB G m))

/-- **A thread `away` from `B`, or holding it at `holdsAway` with `A`'s word in `B`'s nest, may
sleep in `A`'s code** (`Fits.stable`'s queue premise for `B`, `Keeps.otherStep`): `A`'s word's
key is a key of `B`'s nest (`LockWord.BlkOk.keyAt`). -/
theorem away_of {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} (hi : A.Inv G rX m)
    (h : B.ph (G t) = .away ∨ (B.ph (G t) = .holdsAway ∧ B.nest A.ptr)) :
    B.ph (G t) = .away ∨ (B.ph (G t) = .holdsAway ∧ B.toLockWord.NestKey m (A.key m)) :=
  h.imp id fun ⟨h1, h2⟩ => ⟨h1, A.ptr, h2, hi.w.blk.keyAt⟩

/-- **The product's `Fits` for `A`**, with the primitive `K` (module section doc): `stable`,
`atStop` and the part ticks of `kstep` from the client's `U` and the product (`U_stable`,
`U_atStop`, `U_partTick`); the queue premise `away`; `K`'s laws, its rest (`sub`, at `B`'s side
as the rest stores it, next to the common rest) and its steps (`kstep`, at the product's rest)
and `holdLive` are the client's. -/
theorem fits (hp : A.Pair B) {K : FPrim γ} {ok : γ → Prop}
    (inv : ∀ G m, P.inv G m ↔ ∃ rX, A.Inv G rX m ∧ Pair.U B U G rX m)
    (fin : ∀ g, P.fin g → A.ph g = .gone) (joins : ∀ g, P.joins g → A.ph g = .out)
    (ok_set : ∀ g p h, ok (A.set g p h) ↔ ok g) (ok_setPart : ∀ g r, ok (A.setPart g r) ↔ ok g)
    (away : ∀ G rXA m m' t, ok (G t) → A.Inv G rXA m → Pair.U B U G rXA m → A.Step t m m' →
      (∃ w ∈ m'.waiters, w ∉ m.waiters) →
      B.ph (G t) = .away ∨ (B.ph (G t) = .holdsAway ∧ B.toLockWord.NestKey m (A.key m)))
    (stable : ∀ G rL rH rX m m' t p h, ok (G t) → (A.ph (G t)).next p = true →
      (A.ph (G t) = .out → K.enter (K.pl.ph (G t))) →
      A.Inv G (rsum (side B m rL rH) rX) m → B.Keeps G m rL rH rX →
      U G rX m → A.Step t m m' → (A.ph (G t) = .holds → p ≠ .holds → A.Before m' (m.clocks[t]!)) →
      A.Transfer G (rsum (side B m rL rH) rX) m m' t p h → U (upd G t (A.set (G t) p h)) rX m')
    (atStop : ∀ G rX m t, t < m.threads.size → U G rX m → U G rX { m with current := t })
    (tick : ∀ t G rX m r, U G rX m → U (upd G t (A.setPart (G t) r)) rX m.ticked)
    (noGather : ∀ G rX m t, A.Inv G rX m → Pair.U B U G rX m → A.NoGather G m t)
    (kfin : ∀ g, P.fin g → K.pl.ph g = K.out) (kjoins : ∀ g, P.joins g → K.pl.ph g = K.out)
    (sub : ∀ G sB rL rH rX m, Res.Sim sB (side B m rL rH) → B.Keeps G m rL rH rX → U G rX m →
      K.Sub G (rsum sB rX) m)
    (apart : K.Apart)
    (lph : ∀ g p, A.ph (K.pl.set g p) = A.ph g) (lpart : ∀ g p, A.part (K.pl.set g p) = A.part g)
    (lheld : ∀ g p, A.held (K.pl.set g p) = A.held g)
    (lR : ∀ G t p r, A.R G r → A.R (upd G t (K.pl.set (G t) p)) r)
    (ph_l : ∀ g q h, K.pl.ph (A.set g q h) = K.pl.ph g)
    (set_l : ∀ g p q h, K.pl.set (A.set g q h) p = A.set (K.pl.set g p) q h)
    (ph_part : ∀ g r, K.pl.ph (A.setPart g r) = K.pl.ph g)
    (set_part : ∀ g p r, K.pl.set (A.setPart g r) p = A.setPart (K.pl.set g p) r)
    (role_l : ∀ i g q h, K.role i (A.set g q h) ↔ K.role i g)
    (role_part : ∀ i g r, K.role i (A.setPart g r) ↔ K.role i g)
    (ok_calm : ∀ g p q, K.calm p → K.calm q → (ok (K.pl.set g p) ↔ ok (K.pl.set g q)))
    (kstep : ∀ t G rX m G' rX' m', K.Step t G rX m G' rX' m' → Pair.U B U G rX m →
      Pair.U B U G' rX' m')
    (holdLive : ∀ G rX m v, A.Inv G rX m → Pair.U B U G rX m → A.ph (G v) = .holdsAway →
      P.Live v G m) :
    A.Fits K P (Pair.U B U) ok where
  inv := inv
  fin := fin
  joins := joins
  ok_set := ok_set
  ok_setPart := ok_setPart
  stable G rXA m m' t p h hok hn hen hi hU hs hb htr :=
    U_stable hp hi hU hs (away G rXA m m' t hok hi hU hs) fun sB rL rH rX he hsB hk hu => by
      subst he
      exact stable G rL rH rX m m' t p h hok hn hen (inv_side hi hsB) hk hu hs hb
        (htr.congrX (hsB.symm.union (Res.Sim.refl rX)))
  atStop G _ m t ht hU := U_atStop t hU fun rX hu => atStop G rX m t ht hu
  noGather := noGather
  kfin := kfin
  kjoins := kjoins
  sub G rXA m hU := by
    obtain ⟨sB, rL, rH, rX, rfl, hsB, hk, hu⟩ := hU
    exact sub G sB rL rH rX m hsB hk hu
  apart := apart
  lph := lph
  lpart := lpart
  lheld := lheld
  lR := lR
  ph_l := ph_l
  set_l := set_l
  ph_part := ph_part
  set_part := set_part
  role_l := role_l
  role_part := role_part
  ok_calm := ok_calm
  kstep t G rXA m G' rXA' m' h hU := h.elim (fun h => kstep t G rXA m G' rXA' m' h hU) fun h =>
    U_partTick hp hU h fun rX hu => by
      obtain ⟨-, -, -, r, -, rfl, -, rfl, -⟩ := h
      exact tick t G rX m r hu
  holdLive := holdLive

/-- **The product's `Fits` for `A` alone with its word** (`FPrim.empty`; `fits`, as
`FLock.Fits.ofLock` for one lock). -/
theorem fitsEmpty (hp : A.Pair B) {ok : γ → Prop}
    (inv : ∀ G m, P.inv G m ↔ ∃ rX, A.Inv G rX m ∧ Pair.U B U G rX m)
    (fin : ∀ g, P.fin g → A.ph g = .gone) (joins : ∀ g, P.joins g → A.ph g = .out)
    (ok_set : ∀ g p h, ok (A.set g p h) ↔ ok g) (ok_setPart : ∀ g r, ok (A.setPart g r) ↔ ok g)
    (away : ∀ G rXA m m' t, ok (G t) → A.Inv G rXA m → Pair.U B U G rXA m → A.Step t m m' →
      (∃ w ∈ m'.waiters, w ∉ m.waiters) →
      B.ph (G t) = .away ∨ (B.ph (G t) = .holdsAway ∧ B.toLockWord.NestKey m (A.key m)))
    (stable : ∀ G rL rH rX m m' t p h, ok (G t) → (A.ph (G t)).next p = true →
      A.Inv G (rsum (side B m rL rH) rX) m → B.Keeps G m rL rH rX →
      U G rX m → A.Step t m m' → (A.ph (G t) = .holds → p ≠ .holds → A.Before m' (m.clocks[t]!)) →
      A.Transfer G (rsum (side B m rL rH) rX) m m' t p h → U (upd G t (A.set (G t) p h)) rX m')
    (atStop : ∀ G rX m t, t < m.threads.size → U G rX m → U G rX { m with current := t })
    (tick : ∀ t G rX m r, U G rX m → U (upd G t (A.setPart (G t) r)) rX m.ticked)
    (noGather : ∀ G rX m t, A.Inv G rX m → Pair.U B U G rX m → A.NoGather G m t)
    (holdLive : ∀ G rX m v, A.Inv G rX m → Pair.U B U G rX m → A.ph (G v) = .holdsAway →
      P.Live v G m) :
    A.Fits (FPrim.empty γ) P (Pair.U B U) ok :=
  hp.fits inv fin joins ok_set ok_setPart away
    (fun G rL rH rX m m' t p h hok hn _ => stable G rL rH rX m m' t p h hok hn) atStop tick
    noGather (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ => trivial) trivial (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun G t _ r h => by show A.R (upd G t (G t)) r; rwa [upd_same])
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun i => nomatch i) (fun i => nomatch i) (fun _ _ _ _ _ => Iff.rfl)
    (fun _ _ _ _ _ _ _ h _ => nomatch h) holdLive

/-- **A lock order of two locks alone** (module section doc): `A` outer, whose holder sleeps only
at `B`'s word (`hnA`), `B` inner without a nest (`hnB`). A thread runs `A`'s code `away` from `B`
(`awayA`), and `B`'s `away` from `A` or holding `A` at `holdsAway` (`awayB`). Both locks' `Fits`
from the client's obligations at the common rest `U`: `B`'s view by `inv_swap`, `A`'s `holdLive`
by `holdLive_inner` from `B`'s `Fits`, `B`'s by `holdLive_none`. -/
theorem fitsOrder (hp : A.Pair B) {okA okB : γ → Prop}
    (hnA : ∀ p, A.nest p ↔ p = B.ptr) (hnB : ∀ p, ¬ B.nest p)
    (hgA : ∀ G m rL, A.Facts G m rL → A.NoGatherHeld G m)
    (hgB : ∀ G m rL, B.Facts G m rL → B.NoGatherHeld G m)
    (inv : ∀ G m, P.inv G m ↔ ∃ rX, A.Inv G rX m ∧ Pair.U B U G rX m)
    (finA : ∀ g, P.fin g → A.ph g = .gone) (finB : ∀ g, P.fin g → B.ph g = .gone)
    (joinsA : ∀ g, P.joins g → A.ph g = .out) (joinsB : ∀ g, P.joins g → B.ph g = .out)
    (okA_set : ∀ g p h, okA (A.set g p h) ↔ okA g)
    (okA_setPart : ∀ g r, okA (A.setPart g r) ↔ okA g)
    (okB_set : ∀ g p h, okB (B.set g p h) ↔ okB g)
    (okB_setPart : ∀ g r, okB (B.setPart g r) ↔ okB g)
    (awayA : ∀ g, okA g → B.ph g = .away)
    (awayB : ∀ g, okB g → A.ph g = .away ∨ A.ph g = .holdsAway)
    (stableA : ∀ G rL rH rX m m' t p h, okA (G t) → (A.ph (G t)).next p = true →
      A.Inv G (rsum (side B m rL rH) rX) m → B.Keeps G m rL rH rX →
      U G rX m → A.Step t m m' → (A.ph (G t) = .holds → p ≠ .holds → A.Before m' (m.clocks[t]!)) →
      A.Transfer G (rsum (side B m rL rH) rX) m m' t p h → U (upd G t (A.set (G t) p h)) rX m')
    (stableB : ∀ G rL rH rX m m' t p h, okB (G t) → (B.ph (G t)).next p = true →
      B.Inv G (rsum (side A m rL rH) rX) m → A.Keeps G m rL rH rX →
      U G rX m → B.Step t m m' → (B.ph (G t) = .holds → p ≠ .holds → B.Before m' (m.clocks[t]!)) →
      B.Transfer G (rsum (side A m rL rH) rX) m m' t p h → U (upd G t (B.set (G t) p h)) rX m')
    (atStop : ∀ G rX m t, t < m.threads.size → U G rX m → U G rX { m with current := t })
    (tick : ∀ t G rX m r, U G rX m → U (upd G t (A.setPart (G t) r)) rX m.ticked)
    (noGatherA : ∀ G rX m t, A.Inv G rX m → Pair.U B U G rX m → A.NoGather G m t)
    (noGatherB : ∀ G rX m t, B.Inv G rX m → Pair.U A U G rX m → B.NoGather G m t) :
    A.Fits (FPrim.empty γ) P (Pair.U B U) okA ∧ B.Fits (FPrim.empty γ) P (Pair.U A U) okB := by
  have hB : B.Fits (FPrim.empty γ) P (Pair.U A U) okB :=
    hp.symm.fitsEmpty (hp.inv_swap hgA hgB inv) finB joinsB okB_set okB_setPart
      (fun _ _ _ _ _ hok hi _ _ _ =>
        away_of hi ((awayB _ hok).imp id fun h => ⟨h, (hnA _).mpr rfl⟩))
      stableB atStop (fun t G rX m r hu => by rw [← hp.setPart]; exact tick t G rX m r hu)
      noGatherB fun _ _ _ _ hi _ hv => holdLive_none hnB hi hv
  exact ⟨hp.fitsEmpty inv finA joinsA okA_set okA_setPart
    (fun _ _ _ _ _ hok _ _ _ _ => .inl (awayA _ hok)) stableA atStop tick noGatherA
    (holdLive_inner hB (fun p h => (hnA p).mp h) fun G rX m hi hU => (inv G m).mpr ⟨rX, hi, hU⟩),
    hB⟩

end FLock.Pair

/-! ### Two locks over one ghost value -/

/-- A thread's ghost value for two locks `A` and `B` (`FLock.prodA`, `prodB`): its place and the
resource it holds in each, and its part, which both locks see. -/
structure FLG2 where
  phA : LPh := .gone
  heldA : Res := rnil
  phB : LPh := .gone
  heldB : Res := rnil
  part : Res := rnil

/-- `X` of two ghost values is kept by a change of the first component. -/
private theorem upd_snd_keep {X Y : Type} (G : ThreadId → Y × X) (t : ThreadId) (y : Y) :
    (fun u => (upd G t (y, (G t).2) u).2) = fun u => (G u).2 := by
  funext u; unfold upd; split
  · rename_i e; subst e; rfl
  · rfl

/-- **Lock `A` of two locks over `FLG2 × X`** (`FLock.prod` for two locks): its place and held
resource are `phA`, `heldA`; the part is shared with `B` (`prodB`); its nest is `nest` (the
words at which its holder may sleep); its resource reads only `X`. -/
def FLock.prodA {X : Type} (b o : Nat) (R : (ThreadId → X) → FAssn)
    (nest : Ptr → Prop := fun _ => False) (c : Nat := 2)
    (c_ok : c = 1 ∨ c = 2 ∨ c = 3 := by decide) : FLock (FLG2 × X) where
  b := b
  o := o
  c := c
  c_ok := c_ok
  nest := nest
  R G := R fun u => (G u).2
  ph g := g.1.phA
  part g := g.1.part
  held g := g.1.heldA
  set g p h := ({ g.1 with phA := p, heldA := h }, g.2)
  ph_set _ _ _ := rfl
  part_set _ _ _ := rfl
  held_set _ _ _ := rfl
  set_self _ := rfl
  set_set _ _ _ _ _ := rfl
  R_set G t p h r := by
    show R (fun u => (upd G t ({ (G t).1 with phA := p, heldA := h }, (G t).2) u).2) r ↔
      R (fun u => (G u).2) r
    rw [upd_snd_keep]
  setPart g r := ({ g.1 with part := r }, g.2)
  ph_setPart _ _ := rfl
  part_setPart _ _ := rfl
  held_setPart _ _ := rfl
  setPart_self _ := rfl
  setPart_setPart _ _ _ := rfl
  setPart_set _ _ _ _ := rfl
  R_setPart G t r r' := by
    show R (fun u => (upd G t ({ (G t).1 with part := r }, (G t).2) u).2) r' ↔
      R (fun u => (G u).2) r'
    rw [upd_snd_keep]

/-- **Lock `B` of two locks over `FLG2 × X`** (`prodA`): its place and held resource are `phB`,
`heldB`. -/
def FLock.prodB {X : Type} (b o : Nat) (R : (ThreadId → X) → FAssn)
    (nest : Ptr → Prop := fun _ => False) (c : Nat := 2)
    (c_ok : c = 1 ∨ c = 2 ∨ c = 3 := by decide) : FLock (FLG2 × X) where
  b := b
  o := o
  c := c
  c_ok := c_ok
  nest := nest
  R G := R fun u => (G u).2
  ph g := g.1.phB
  part g := g.1.part
  held g := g.1.heldB
  set g p h := ({ g.1 with phB := p, heldB := h }, g.2)
  ph_set _ _ _ := rfl
  part_set _ _ _ := rfl
  held_set _ _ _ := rfl
  set_self _ := rfl
  set_set _ _ _ _ _ := rfl
  R_set G t p h r := by
    show R (fun u => (upd G t ({ (G t).1 with phB := p, heldB := h }, (G t).2) u).2) r ↔
      R (fun u => (G u).2) r
    rw [upd_snd_keep]
  setPart g r := ({ g.1 with part := r }, g.2)
  ph_setPart _ _ := rfl
  part_setPart _ _ := rfl
  held_setPart _ _ := rfl
  setPart_self _ := rfl
  setPart_setPart _ _ _ := rfl
  setPart_set _ _ _ _ := rfl
  R_setPart G t r r' := by
    show R (fun u => (upd G t ({ (G t).1 with part := r }, (G t).2) u).2) r' ↔
      R (fun u => (G u).2) r'
    rw [upd_snd_keep]

/-- **`prodA` and `prodB` are a pair** when their words are apart. -/
theorem FLock.prodPair {X : Type} {bA oA bB oB : Nat} {RA RB : (ThreadId → X) → FAssn}
    {nA nB : Ptr → Prop} {cA cB : Nat} {hA : cA = 1 ∨ cA = 2 ∨ cA = 3}
    {hB : cB = 1 ∨ cB = 2 ∨ cB = 3}
    (hap : (FLock.prodA bA oA RA nA cA hA).ApartL (FLock.prodB bB oB RB nB cB hB).toLockWord) :
    (FLock.prodA bA oA RA nA cA hA).Pair (FLock.prodB bB oB RB nB cB hB) where
  apart := hap
  ph_ab _ _ _ := rfl
  held_ab _ _ _ := rfl
  R_ab G t p h r := by
    show RB (fun u => (upd G t ({ (G t).1 with phA := p, heldA := h }, (G t).2) u).2) r ↔
      RB (fun u => (G u).2) r
    rw [upd_snd_keep]
  ph_ba _ _ _ := rfl
  held_ba _ _ _ := rfl
  R_ba G t p h r := by
    show RA (fun u => (upd G t ({ (G t).1 with phB := p, heldB := h }, (G t).2) u).2) r ↔
      RA (fun u => (G u).2) r
    rw [upd_snd_keep]
  part _ := rfl
  setPart _ _ := rfl
  set_comm _ _ _ _ _ := rfl

end Full
end Zig
