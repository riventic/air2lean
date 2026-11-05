import ZigLean.Sep.Full.Lock

/-!
# Two locks: a step of one lock's code keeps the other lock's word

A thread may hold one lock `L` while it runs the code of another lock `K` (a lock order: `K` is
an inner lock of `L`). Both invariants hold at once; this file is the word-level part of their
product.

* `LockWord.ApartL L K`: the two words do not overlap.
* `WInv.otherStep`: a step of `K`'s code (`LockWord.Step`) by a thread `t` that is outside `L`'s
  code keeps `L`'s invariant with the same places. In `L`'s view `t` is `away`, or `holdsAway`
  if it holds `L` and `K`'s word is in `L`'s nest (`LockWord.nest`): `K`'s futex wait may queue
  `t` at `K`'s word (`Step.newQ`: only `t` joins the queue), and `L`'s queue admits exactly those
  two places at another futex (`Queue`). A thread inside `L`'s code (`spin`, `wait`, `holds`,
  `wake`) does not run `K`'s code.
* `Before.otherStep`, `Owns.otherStep`: `K`'s step keeps `L`'s newest message and so what the
  free `L` owns, for a resource without `K`'s word.
* `FLock.Inv.otherStep`: the same for the lock over full-state resources, with `K`'s word in
  `L`'s rest; its cells are the new ones after the step.
* `FLock.Inv.nap`/`unnap` and `FLock.Fits.nap`/`unnap`: the holder of `L` goes to `holdsAway`
  before `K`'s code may put it to sleep, and back to `holds` after it. No memory step. The
  protocol's `U` must be stable under this relabel: a hypothesis of `Fits.nap`/`unnap` that each
  nesting protocol discharges (decision on #667; `FLock.Fits.stable` does not cover it).
-/

namespace Zig
namespace Full

open Conc Proto

/-- The cells at bytes `W` are apart from a heap without them. -/
theorem disj_cellsAt {W : Zig.Loc → Prop} [DecidablePred W] {h : FHeap} {m : Mem}
    (hW : ∀ l, W l → h l = none) : FHeap.Disjoint h (cellsAt W m).heap := fun l => by
  by_cases hl : W l
  · exact .inl (hW l hl)
  · exact .inr (cellsAt_none hl)

namespace LockWord

/-- The words of the locks `L` and `K` do not overlap. -/
def ApartL (L K : LockWord) : Prop := L.b ≠ K.b ∨ L.o + 4 ≤ K.o ∨ K.o + 4 ≤ L.o

variable {L K : LockWord}

theorem ApartL.symm (h : L.ApartL K) : K.ApartL L := by
  rcases h with h | h | h
  · exact .inl (Ne.symm h)
  · exact .inr (.inr h)
  · exact .inr (.inl h)

/-- Apart words are at other places. -/
theorem ApartL.ne (h : L.ApartL K) : L.b ≠ K.b ∨ L.o ≠ K.o := by
  rcases h with h | h | h
  · exact .inl h
  · exact .inr (by omega)
  · exact .inr (by omega)

/-- Apart words have other pointers. -/
theorem ApartL.ptr_ne (h : L.ApartL K) : L.ptr ≠ K.ptr := fun e => by
  simp only [LockWord.ptr, Ptr.mk.injEq, Option.some.injEq, Int.natCast_inj] at e
  rcases h.ne with h | h
  · exact h e.1
  · exact h e.2

/-- A byte of `L`'s word is not a byte of `K`'s. -/
theorem ApartL.not_in (h : L.ApartL K) {l : Zig.Loc} (hl : L.In l) : ¬ K.In l := by
  obtain ⟨b, x⟩ := l
  rintro ⟨hb', h3, h4⟩
  obtain ⟨hb, h1, h2⟩ := hl
  rcases h with h | h | h
  · exact h (hb.symm.trans hb')
  · omega
  · omega

/-- `K`'s step keeps `L`'s word's location: the first location at `L`'s word is the same. -/
theorem Step.otherLoc {t : ThreadId} {m m' : Mem} (hs : K.Step t m m') (hap : L.ApartL K)
    (i : Nat) (l : ALoc) : L.Loc m' i l ↔ L.Loc m i l :=
  hs.first_iff L.b L.o hap.ne i l

/-- `K`'s step keeps `L`'s word's block and bytes. -/
theorem BlkOk.otherStep {t : ThreadId} {m m' : Mem} (hs : K.Step t m m') (hap : L.ApartL K)
    (hb : L.BlkOk m) : L.BlkOk m' ∧ curBytes m' L.b L.o 4 = curBytes m L.b L.o 4 :=
  word_congr (fun x h1 h2 => hs.heap (hap.not_in ⟨rfl, h1, h2⟩)) hb

/-- `K`'s step keeps a clock that happened before `L`'s newest message. -/
theorem Before.otherStep {t : ThreadId} {m m' : Mem} {c : VClock} (hs : K.Step t m m')
    (hap : L.ApartL K) (h : L.Before m c) : L.Before m' c := by
  obtain ⟨i, l, hl, hle⟩ := h
  exact ⟨i, l, (hs.otherLoc hap i l).mpr hl, hle⟩

/-- **`K`'s step keeps `L`'s invariant** with the same places, at any place of `t`; a step that
queues `t` (`K`'s futex wait) needs `t` at `away`, or at `holdsAway` with `K`'s word in `L`'s nest
(module doc). -/
theorem WInv.otherStep {P : ThreadId → LPh} {t : ThreadId} {m m' : Mem} (hi : L.WInv P m)
    (hs : K.Step t m m') (hap : L.ApartL K)
    (ht : (∃ w ∈ m'.waiters, w ∉ m.waiters) → P t = .away ∨ (P t = .holdsAway ∧ L.nest K.ptr)) :
    L.WInv P m' := by
  obtain ⟨hblk', hcur⟩ := BlkOk.otherStep hs hap hi.blk
  have hU32 : ∀ v, L.U32 m' v ↔ L.U32 m v := fun v => by unfold LockWord.U32; rw [hcur]
  have hloc := hs.otherLoc hap
  have hpne := hap.ptr_ne.symm
  -- A queue entry that is new is `t`'s at `K`'s word.
  have hnew : ∀ w ∈ m'.waiters, w ∉ m.waiters → w.1 = t ∧ w.2 = K.ptr := fun w hw hn =>
    ⟨hs.newQ w hw hn, Classical.byContradiction fun h2 => hn ((hs.waiters_mem w h2).mp hw)⟩
  refine ⟨by rw [hs.csize, hs.threads]; exact hi.csize, fun u hu => ?_, hblk', ?_, hi.one,
    ⟨fun l hl hb h1 h2 => ?_, fun i l hl => ?_, fun i l hl => ?_⟩,
    fun e he hh => ?_, fun i l hl => ?_, fun w hw => ?_, fun hw => ?_, fun u hu => ?_⟩
  · rw [hs.threads, joinedB_congr hs.threads]; exact hi.live u hu
  · obtain ⟨w, hw, hu, hz⟩ := hi.word
    exact ⟨w, hw, (hU32 _).mpr hu, hz⟩
  · rcases hs.atomic_mem hl with hold | hshape
    · exact hi.loc.only l hold hb h1 h2
    · obtain ⟨hbl, ho, hlen⟩ : l.block = K.b ∧ l.off = K.o ∧ l.len = 4 := by
        simpa only [ALoc.shape, LockWord.shape, Prod.mk.injEq] using hshape
      rw [hbl] at hb
      rw [ho] at h1
      rw [ho, hlen] at h2
      rcases hap with h | h | h
      · exact absurd hb.symm h
      · omega
      · omega
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hi.loc.ok i l ((hloc i l).mp hl)
    exact ⟨h1, h2, h3, h4, by rw [h5, hcur]⟩
  · exact (hi.loc.plain i l ((hloc i l).mp hl)).of_fp fun e he =>
      (hs.fp e he).imp id fun h => plainHit_atomic h.2.2.2.1
  · rcases hs.fp e he with hold | ⟨-, -, -, hk, hle⟩
    · rcases hi.wfp e hold hh with ⟨hk, hle⟩ | hle
      · exact .inl ⟨hk, hs.someLe hle⟩
      · exact .inr (hs.liveLe (fun _ h => h) hle)
    · exact .inl ⟨hk, hle⟩
  · obtain ⟨h1, h2⟩ := hi.rel i l ((hloc i l).mp hl)
    exact ⟨hs.someLe h1, fun u hu => VClock.le_trans (h2 u hu) (hs.clocks u)⟩
  · by_cases hold : w ∈ m.waiters
    · exact hi.fq w hold
    · obtain ⟨h1, h2⟩ := hnew w hw hold
      rw [h1, h2]
      rcases ht ⟨w, hw, hold⟩ with ht | ⟨ht, hn⟩
      · exact .inr (.inl ⟨hpne, ht⟩)
      · exact .inr (.inr ⟨hpne, ht, hn⟩)
  · -- an entry at `L`'s word is an old one
    have hw' : L.Waits m.waiters := by
      obtain ⟨w, hwm, he⟩ := Array.any_eq_true'.mp hw
      exact Array.any_eq_true'.mpr
        ⟨w, (hs.waiters_mem w (by rw [beq_iff_eq.mp he]; exact hpne.symm)).mp hwm, he⟩
    obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit hw'
    refine ⟨v, hs.threads ▸ hv, fun hvw => Array.any_eq_false'.mpr fun w hw hy => ?_, h1,
      fun hh => (hU32 _).mpr (h2 hh)⟩
    by_cases hold : w ∈ m.waiters
    · exact ne_of_notQ (hq hvw) hold (beq_iff_eq.mp hy)
    · -- a new entry is `t`'s, and `t` is not at `L`'s `wait`
      have e : v = t := (beq_iff_eq.mp hy).symm.trans (hnew w hw hold).1
      subst e
      rcases ht ⟨w, hw, hold⟩ with ht | ⟨ht, -⟩ <;> rw [ht] at hvw <;> cases hvw
  · obtain ⟨i, l, hl, hw⟩ := hi.owner u hu
    exact ⟨i, l, (hloc i l).mpr hl, hw⟩

/-- `K`'s step keeps what the free `L` owns in a resource `h` without `K`'s word (whose block
exists): `K`'s new accesses are at `K`'s word, and `L`'s newest message stays. -/
theorem Owns.otherStep {P P' : ThreadId → LPh} {t : ThreadId} {m m' : Mem} {h : Heap}
    (hs : K.Step t m m') (hap : L.ApartL K) (hoff : K.Off h) (hbl : K.b < m.blocks.size)
    (hg : ∀ u, P' u ≠ .gone → P u ≠ .gone) (ho : L.Owns P m h) : L.Owns P' m' h := by
  intro e he htc
  by_cases hm : e ∈ m.footprint
  · rcases ho e hm (htc.imp id fun h => by rw [← hs.bsize]; exact h) with h | h
    · exact .inl (hs.liveLe hg h)
    · exact .inr (h.otherStep hs hap)
  · rcases htc with htc | hbe
    · exact absurd htc (hs.fpOff hoff he hm)
    · rcases hs.fp e he with h | ⟨heb, -⟩
      · exact absurd h hm
      · rw [heb, hs.bsize] at hbe; exact absurd hbl (Nat.not_lt.mpr hbe)

/-- `K`'s step keeps `L`'s word's cells. -/
theorem wordR_otherStep {t : ThreadId} {m m' : Mem} (hs : K.Step t m m') (hap : L.ApartL K) :
    L.wordR m' = L.wordR m := by
  simp only [LockWord.wordR, cellsAt, Res.mk.injEq, and_true]
  funext l; split
  · rename_i hl; rw [hs.heap (hap.not_in hl)]
  · rfl

end LockWord

namespace FLock

variable {γ : Type} {L : FLock γ}

/-- New ghost values that `L` does not tell apart from the old ones: the same places, parts and
resources, and the resource assertion keeps holding (e.g. another lock's step changed only its
own coordinates of the ghost values). -/
theorem Inv.congrG {G G' : ThreadId → γ} {rX : Res} {m : Mem} (hi : L.Inv G rX m)
    (hG : ∀ u, L.ph (G' u) = L.ph (G u) ∧ L.part (G' u) = L.part (G u) ∧
      L.held (G' u) = L.held (G u))
    (hR : ∀ r, L.R G r → L.R G' r) : L.Inv G' rX m := by
  have hpl : L.pl G' = L.pl G := funext fun u => (hG u).1
  have hown : L.own G' m = L.own G m := by
    funext u; unfold FLock.own; rw [(hG u).2.1, (hG u).2.2]
  have hfree : L.Free G' ↔ L.Free G := by unfold FLock.Free; rw [hpl]
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  refine ⟨hpl ▸ hi.w, ⟨rL, hown ▸ ho, hLoff, hLX, fun hF' => ?_,
    fun h => hnF fun h' => h (hfree.mpr h')⟩, hi.xoff, fun u => ?_, fun u hu => ?_,
    fun u hu => ?_⟩
  · obtain ⟨h1, h2⟩ := hF (hfree.mp hF')
    exact ⟨hR rL h1, hpl ▸ h2⟩
  · rw [(hG u).2.1, (hG u).2.2]; exact hi.pdisj u
  · rw [(hG u).1] at hu; rw [(hG u).2.2]; exact hi.idle u hu
  · rw [(hG u).1] at hu; rw [(hG u).2.2]; exact hR _ (hi.res u hu)

section

variable {K : LockWord}

/-- `K`'s step with the same ghost values (`Inv.otherStep`). -/
private theorem Inv.otherStay {G : ThreadId → γ} {rY : Res} {t : ThreadId} {m m' : Mem}
    (hi : L.Inv G (rsum (K.wordR m) rY) m) (hs : K.Step t m m') (hap : L.ApartL K)
    (hKb : K.BlkOk m) (hYoff : K.Off rY.heap.erase)
    (ht : (∃ w ∈ m'.waiters, w ∉ m.waiters) →
      L.ph (G t) = .away ∨ (L.ph (G t) = .holdsAway ∧ L.nest K.ptr)) :
    L.Inv G (rsum (K.wordR m') rY) m' := by
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  have hjb := LockWord.joinedB_congr hs.threads
  have hown : L.own G m' = L.own G m := by funext u; unfold FLock.own; rw [hjb]
  have hKbl : K.b < m.blocks.size := by
    obtain ⟨blk, hb, -⟩ := hKb; exact (Array.getElem?_eq_some_iff.mp hb).1
  -- `rL` and `rY` have no byte of `K`'s word: the rest has it, apart from `rL`.
  have hXY := FHeap.disjoint_union_right.mp hLX
  have hLK : ∀ l, K.In l → rL.heap l = none := fun l hl =>
    (hXY.1 l).resolve_right (LockWord.wordR_some hKb hl)
  have hYK : ∀ l, K.In l → rY.heap l = none := LockWord.off_erase.mp hYoff
  have hLwK : ∀ (n : Mem) l, K.In l → (L.wordR n).heap l = none := fun n l hl =>
    cellsAt_none fun h => hap.not_in h hl
  -- Bring `K`'s word to the front, step it, and put it back.
  have hperm : ∀ n : Mem, rsum (L.wordR n) (rsum rL (rsum (K.wordR n) rY)) =
      rsum (K.wordR n) (rsum (L.wordR n) (rsum rL rY)) := fun n => by
    rw [← rsum_assoc (a := rL), rsum_comm (a := rL) (disj_cellsAt hLK), rsum_assoc,
      ← rsum_assoc, rsum_comm (a := L.wordR n) (disj_cellsAt (hLwK n)), rsum_assoc]
  have ho' := (hperm m ▸ ho).restStep (hs.rest hKb)
    (fun l hl => by
      obtain ⟨b, x⟩ := l; obtain ⟨h1, h2, h3⟩ := hl; simp only at h1 h2 h3; subst h1
      exact hKb.cell h2 h3)
    (fun l hl => by simp only [FHeap.union_apply, hLwK m l hl, hLK l hl, hYK l hl]; rfl)
  rw [← LockWord.wordR_otherStep hs hap, ← hperm m', ← hown] at ho'
  refine ⟨hi.w.otherStep hs hap ht, ⟨rL, ho', hLoff,
    FHeap.disjoint_union_right.mpr ⟨disj_cellsAt hLK, hXY.2⟩, fun hF' => ?_, hnF⟩, ?_, hi.pdisj,
    hi.idle, hi.res⟩
  · obtain ⟨h1, h2⟩ := hF hF'
    exact ⟨h1, h2.otherStep hs hap (LockWord.off_erase.mpr hLK) hKbl (fun _ h => h)⟩
  · refine LockWord.off_erase.mpr fun l hl => ?_
    have h := LockWord.off_erase.mp hi.xoff l hl
    simp only [FHeap.union_apply, Option.or_eq_none_iff] at h ⊢
    exact ⟨cellsAt_none fun h' => hap.not_in hl h', h.2⟩

/-- **`K`'s step keeps `L`'s invariant**, for a thread `t` outside `L`'s code
(`LockWord.WInv.otherStep`). `K`'s word is in `L`'s rest (`rsum (K.wordR m) rY`); its cells are
the new ones after the step. The step's new ghost values `G'` change only what `L` does not read
(`Inv.congrG`: `K`'s place, `K`'s held resource). `K`'s resource, free or held, is inside `rY` in
`L`'s view, so an acquire or a release of `K` keeps `rY`. -/
theorem Inv.otherStep {G G' : ThreadId → γ} {rY : Res} {t : ThreadId} {m m' : Mem}
    (hi : L.Inv G (rsum (K.wordR m) rY) m) (hs : K.Step t m m') (hap : L.ApartL K)
    (hKb : K.BlkOk m) (hYoff : K.Off rY.heap.erase)
    (ht : (∃ w ∈ m'.waiters, w ∉ m.waiters) →
      L.ph (G t) = .away ∨ (L.ph (G t) = .holdsAway ∧ L.nest K.ptr))
    (hG : ∀ u, L.ph (G' u) = L.ph (G u) ∧ L.part (G' u) = L.part (G u) ∧
      L.held (G' u) = L.held (G u))
    (hR : ∀ r, L.R G r → L.R G' r) :
    L.Inv G' (rsum (K.wordR m') rY) m' :=
  (hi.otherStay hs hap hKb hYoff ht).congrG hG hR

end

/-- A holder `t` that is not in the futex queue changes between the holding places (`holds`,
`holdsAway`) and keeps its part and its resource (`LockWord.WInv.reheld`). No memory step. -/
theorem Inv.reheld {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} {p : LPh}
    (hi : L.Inv G rX m) (hph : (L.ph (G t)).held = true) (hp : p.held = true)
    (hq : m.waiters.any (·.1 == t) = false) :
    L.Inv (upd G t (L.set (G t) p (L.held (G t)))) rX m := by
  have hown : L.own (upd G t (L.set (G t) p (L.held (G t)))) m = L.own G m := by
    funext u; unfold FLock.own
    by_cases h : u = t
    · subst h; rw [upd_self, L.part_set, L.held_set]
    · rw [upd_ne _ _ h]
  have hphu : ∀ u, L.ph (upd G t (L.set (G t) p (L.held (G t))) u) =
      if u = t then p else L.ph (G u) := fun u => by
    unfold upd; split
    · exact L.ph_set _ _ _
    · rfl
  have hholds : ∀ u, (L.ph (upd G t (L.set (G t) p (L.held (G t))) u)).held = true ↔
      (L.ph (G u)).held = true := by
    intro u; rw [hphu]; split
    · rename_i h; subst h; rw [hp, hph]
    · exact Iff.rfl
  have hfree := free_iff_of (L := L) hholds
  have hgw : ∀ u, L.ph (upd G t (L.set (G t) p (L.held (G t))) u) ≠ .gone →
      L.ph (G u) ≠ .gone := fun u h => by
    rw [hphu] at h; split at h
    · rename_i e; subst e; exact LPh.ne_gone_of_held hph
    · exact h
  have hR : ∀ r, L.R G r → L.R (upd G t (L.set (G t) p (L.held (G t)))) r :=
    fun r h => (L.R_set G t p _ r).mpr h
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  refine ⟨by rw [pl_upd_set]; exact hi.w.reheld hph hp hq, ⟨rL, hown ▸ ho, hLoff, hLX,
    fun hF' => ?_, fun h => hnF (fun h' => h (hfree.mpr h'))⟩, hi.xoff, fun u => ?_,
    fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨h1, h2⟩ := hF (hfree.mp hF')
    exact ⟨hR rL h1, h2.weaken hgw⟩
  · by_cases h : u = t
    · subst h; rw [upd_self, L.part_set, L.held_set]; exact hi.pdisj u
    · rw [upd_ne _ _ h]; exact hi.pdisj u
  · by_cases h : u = t
    · subst h; rw [upd_self, L.ph_set, hp] at hu; cases hu
    · rw [upd_ne _ _ h] at hu ⊢; exact hi.idle u hu
  · by_cases h : u = t
    · subst h; rw [upd_self, L.held_set]; exact hR _ (hi.res u hph)
    · rw [upd_ne _ _ h] at hu ⊢; exact hR _ (hi.res u hu)

/-- **The nap**: the holder `t` goes from `holds` to `holdsAway`, before the futex wait of an
object of the lock's nest (`LockWord.WInv.nap`). No memory step. -/
theorem Inv.nap {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} (hi : L.Inv G rX m)
    (hph : L.ph (G t) = .holds) :
    L.Inv (upd G t (L.set (G t) .holdsAway (L.held (G t)))) rX m :=
  have hp : L.pl G t = .holds := hph
  hi.reheld (LPh.held_of_holds hph) rfl
    (hi.w.notQ (by rw [hp]; decide) (by rw [hp]; decide) (by rw [hp]; decide))

/-- **The unnap**: the holder `t` at `holdsAway`, not in the futex queue, goes back to `holds`
(`LockWord.WInv.unnap`). The caller shows that `t` is awake, e.g. from the inner lock's invariant
at which `t` now holds (`LockWord.WInv.notQ`). No memory step. -/
theorem Inv.unnap {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} (hi : L.Inv G rX m)
    (hph : L.ph (G t) = .holdsAway) (hq : m.waiters.any (·.1 == t) = false) :
    L.Inv (upd G t (L.set (G t) .holds (L.held (G t)))) rX m :=
  hi.reheld (by rw [hph]; rfl) rfl hq

variable {K : FPrim γ} {Tgt : Type} {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop}
  {ok : γ → Prop}

/-- **The nap of a protocol** (`Inv.nap`): thread `t` at `g`, holding `L`, goes to `holdsAway`.
`U`'s stability over this relabel is the rule's hypothesis, which a nesting protocol proves for
its own `U` (decision on #667: it is not part of `Fits.stable`). -/
theorem Fits.nap (hP : L.Fits K P U ok) {G : ThreadId → γ} {m : Mem} {t : ThreadId} {g : γ}
    (hg : L.ph g = .holds) (hi : P.inv (upd G t g) m)
    (hU : ∀ rX, U (upd G t g) rX m → L.Inv (upd G t g) rX m →
      U (upd G t (L.set g .holdsAway (L.held g))) rX m) :
    P.inv (upd G t (L.set g .holdsAway (L.held g))) m := by
  obtain ⟨rX, hiL, hU₀⟩ := (hP.inv _ _).mp hi
  have h := hiL.nap (t := t) (by rw [upd_self]; exact hg)
  rw [upd_upd, upd_self] at h
  exact (hP.inv _ _).mpr ⟨rX, h, hU rX hU₀ hiL⟩

/-- **The unnap of a protocol** (`Inv.unnap`): thread `t` at `g`, holding `L` at `holdsAway` and
not in the futex queue, goes back to `holds`. `U`'s stability over this relabel is the rule's
hypothesis, as for `Fits.nap`. -/
theorem Fits.unnap (hP : L.Fits K P U ok) {G : ThreadId → γ} {m : Mem} {t : ThreadId} {g : γ}
    (hg : L.ph g = .holdsAway) (hi : P.inv (upd G t g) m) (hq : m.waiters.any (·.1 == t) = false)
    (hU : ∀ rX, U (upd G t g) rX m → L.Inv (upd G t g) rX m →
      U (upd G t (L.set g .holds (L.held g))) rX m) :
    P.inv (upd G t (L.set g .holds (L.held g))) m := by
  obtain ⟨rX, hiL, hU₀⟩ := (hP.inv _ _).mp hi
  have h := hiL.unnap (t := t) (by rw [upd_self]; exact hg) hq
  rw [upd_upd, upd_self] at h
  exact (hP.inv _ _).mpr ⟨rX, h, hU rX hU₀ hiL⟩

end FLock

end Full
end Zig
