import ZigLean.Sep.Full.Sem
import ZigLean.Sep.Full.LockProd

/-!
# A condition and a semaphore next to the other lock of a two-lock product

(ledger #two-lock-product, item (5).) In a two-lock product (`ZigLean/Sep/Full/LockProd.lean`) the
semaphore's mutex `L` may run a condition `C` (`FCond.prim`, a semaphore's `FSem.prim`) while the
other lock `B` rides in `L`'s rest (`FLock.Pair.U B U`). This module states once, for every lock
`B`, every condition `C` and every semaphore `S`, what `B` keeps over the condition's and the
semaphore's steps and where the condition's words lie next to `B`'s side; a product's view of `L`
(the reader/writer lock's semaphore, `ZigLean/Sep/Full/RwLockProd.lean`) uses them.

- **`B` kept over a step of the condition's code** (`FLock.Pair.Keeps.mstep`, every `FCond.MStep`
  at a word `W` of the condition): no change, a stop or a return from a futex wait (`same`,
  `resume`, `woken`: the futex queue and the woken threads change, `Keeps.queue`); an op at `W`
  (`op`, `Keeps.wordRun`: `Word.actualRun_rest`'s `RestStep` and `Word.actualRun_fstep`'s
  `FStepIn`), the futex wait's sleep at the epoch (`sleep`: a read of the epoch, then `t` in the
  futex queue at the epoch's key, `LockWord.WInv.push`: `t` is `away` from `B`, or holds it at
  `holdsAway` with the epoch's key in `B`'s nest, as `LockWord.Queue` admits; the same premise as
  `Keeps.otherStep`'s), and a futex wake at the epoch (`wake`, `LockWord.WInv.wakeOff`). `B`'s side
  owns no byte of `W` or of the epoch, and the epoch's key is not `B`'s. `B`'s side is then exactly
  the same. A change of the stepping thread's places that keeps `B`'s is `Keeps.relabel`
  (`ZigLean/Sep/Full/LockProd.lean`, with `Keeps.queue`, `Keeps.wordRun`, `Keeps.sleepAt`,
  `Keeps.wakeAt` and `WInv.push`: they hold for any lock and any futex word, an event's too).
- **The condition's words next to `B`'s side** (`FPrim.ofWords_sub_rsum`): a primitive over futex
  words whose `Sub` holds at the protocol's own rest also holds with a resource apart from it in
  front (`B`'s side, `FLock.Keeps.side_disj`), the `sub` of `FLock.Pair.fits` for such a primitive.
  A step at a word keeps `B`'s side in front of the rest beside the word's cells
  (`FLock.Pair.rest_words`, `Keeps.words`).
- **The semaphore's steps keep the product's rest** (`FLock.Pair.U_semStep`, the `kstep` of
  `L.Fits S.prim` at `Pair.U B U`): a step of the condition's code (`Keeps.mstep`, then
  `Keeps.relabel` at the word's new cells), a native step on the thread's own part
  (`Keeps.partStep`), the waiter's entry (`Keeps.relabel`) and the holder's step on the mutex's
  resource (`FSem.Move.hold`: `Keeps.stepAt`, `B`'s word cells from the lock's invariant after it,
  `Keeps.cellsOf`). The rest after a primitive's step is fixed by the step (`FSem.Move.hold`: the
  same rest; `FPrim.ofWords`: the word's new cells beside the same rest), so the product's rest
  stores `B`'s side up to `Cell.norm` (`Pair.U`, decision (A) on #741). The client keeps its own
  `U`, gives `B`'s coordinates over the semaphore's places, that `B`'s side owns no byte of the
  condition's words, the keys apart, and that a waiter of the condition is `away` from `B` or holds
  it at `holdsAway` with the epoch in `B`'s nest.
-/

namespace Zig
namespace Full

open Conc Proto

namespace FLock.Pair

variable {γ : Type} {B : FLock γ} {G : ThreadId → γ} {m : Mem} {rL rH rX : Res}
  {C : FCond γ} {W : Word 32 4} {t : ThreadId} {m' : Mem}

/-- **A step of the condition's code keeps what the product keeps of `B`** (module doc): every
`FCond.MStep` at a word `W` of the condition, when `B`'s side owns no byte of `W` or of the epoch
and the epoch's key is not `B`'s; a sleep at the epoch queues `t` `away` from `B`, or holding it
at `holdsAway` with the epoch's key in `B`'s nest (`ht`, as `Keeps.otherStep`). `B`'s side is the
same. -/
theorem Keeps.mstep (hk : B.Keeps G m rL rH rX) (hs : C.MStep W t m m')
    (hWo : ∀ l, W.In l → (side B m rL rH).owned l = none)
    (hEo : ∀ l, C.Ep.In l → (side B m rL rH).owned l = none) (hkey : C.Ep.key m ≠ B.key m)
    (ht : (∃ w ∈ m'.waiters, w ∉ m.waiters) →
      B.ph (G t) = .away ∨ (B.ph (G t) = .holdsAway ∧ B.toLockWord.NestKey m (C.Ep.key m))) :
    side B m' rL rH = side B m rL rH ∧ B.Keeps G m' rL rH rX := by
  have hk₁ := (Keeps.cur hk t).2
  cases hs with
  | same => exact ⟨rfl, hk⟩
  | op hw hc hop _ _ => exact Keeps.wordRun (m := { m with current := t }) hk₁ hw hc hop hWo
  | @sleep M hw hc hM _ _ =>
    subst hM
    exact Keeps.sleepAt hk hw hc hEo hkey fun hn => ht ⟨_, Array.mem_push_self, hn⟩
  | woken => exact ⟨rfl, Keeps.queue hk₁ (hk₁.facts.w.requeue hk₁.facts.w.fq hk₁.facts.w.wit)⟩
  | resume => exact ⟨rfl, hk₁⟩
  | wake c cs h => exact Keeps.wakeAt hk hkey h

/-- **A rest at a word's cells with `B`'s side in front** (module doc): the side as the rest
stores it (`sB`, apart from the protocol's rest at the word's cells) has none of the word's bytes,
so the rest beside the word's cells is the side next to the protocol's rest beside them, and after
a step at the word it is again the side next to the protocol's rest at the word's new cells. -/
theorem rest_words {X : ThreadId → Prop} {sB rY₀ rY : Res} (hok : W.Ok m X)
    (hd : FHeap.Disjoint sB.heap (rsum (W.cellsR m) rY₀).heap)
    (hY₀ : ∀ l, W.In l → rY₀.heap l = none)
    (he : rsum sB (rsum (W.cellsR m) rY₀) = rsum (W.cellsR m) rY)
    (hY : ∀ l, W.In l → rY.heap l = none) (m' : Mem) :
    rsum (W.cellsR m') rY = rsum sB (rsum (W.cellsR m') rY₀) := by
  have hsW : ∀ l, W.In l → sB.heap l = none := fun l hl =>
    (hd l).resolve_right fun e => cellsAt_some hl (hok.cellIn hl) (rsum_heap_none.mp e).1
  have hY' : rY = rsum sB rY₀ := cellsAt_cancel
    (he.symm.trans (rsum_left_comm (disj_cellsAt hsW)))
    hY fun l hl => rsum_heap_none.mpr ⟨hsW l hl, hY₀ l hl⟩
  rw [hY', rsum_left_comm (disj_cellsAt hsW).symm]

/-- **`B` kept beside a rest at a word's cells is kept beside the rest at its new cells**: the
word's cells before the step lie in the rest, so `B`'s free and holders' resources and `B`'s word
have none of the word's bytes. -/
theorem Keeps.words {X : ThreadId → Prop} {rY₀ : Res} (hk : B.Keeps G m rL rH (rsum (W.cellsR m) rY₀))
    (hok : W.Ok m X) (m' : Mem) :
    FHeap.Disjoint (rsum rL rH).heap (rsum (W.cellsR m') rY₀).heap ∧
      B.Off (rsum (W.cellsR m') rY₀).heap.erase := by
  have hc : ∀ l, W.In l → (rsum (W.cellsR m) rY₀).heap l ≠ none := fun l hl e =>
    cellsAt_some hl (hok.cellIn hl) (rsum_heap_none.mp e).1
  have hxd := FHeap.disjoint_union_right.mp hk.xdisj
  refine ⟨FHeap.disjoint_union_right.mpr ⟨fun l => ?_, hxd.2⟩,
    LockWord.off_erase.mpr fun l hl => rsum_heap_none.mpr ⟨?_,
      (rsum_heap_none.mp (LockWord.off_erase.mp hk.xoff l hl)).2⟩⟩
  · by_cases hw : W.In l
    · exact .inl ((hk.xdisj l).resolve_right (hc l hw))
    · exact .inr (cellsAt_none hw)
  · by_cases hw : W.In l
    · exact absurd (LockWord.off_erase.mp hk.xoff l hl) (hc l hw)
    · exact cellsAt_none hw

end FLock.Pair

/-- **A primitive over futex words keeps its `Sub` next to a resource apart from the rest**
(module doc; `FLock.Pair.fits`'s `sub` at `B`'s side, `FLock.Keeps.side_disj`): each word's cells
are in the rest, so the resource has none of their bytes and the rest beside them grows by it. -/
theorem FPrim.ofWords_sub_rsum {γ Ph Rl : Type} {L : FLock γ} {pl : FPlace γ Ph} {out : Ph}
    {calm : Ph → Prop} {role : Rl → γ → Prop} {Ws : Word 32 4 → Prop}
    {Lv : Word 32 4 → γ → Prop} {Inv : (ThreadId → γ) → Mem → Prop}
    {Move : Word 32 4 → ThreadId → γ → Ph → LPh → Res → Mem → Mem → Prop} {ownAt : LPh → Prop}
    {G : ThreadId → γ} {rX r : Res} {m : Mem}
    (hsub : (FPrim.ofWords L pl out calm role Ws Lv Inv Move ownAt).Sub G rX m)
    (hd : FHeap.Disjoint r.heap rX.heap) :
    (FPrim.ofWords L pl out calm role Ws Lv Inv Move ownAt).Sub G (rsum r rX) m := by
  refine ⟨hsub.1, fun W hW => ?_⟩
  obtain ⟨hok, rY, rfl, hY⟩ := hsub.2 W hW
  have hdc := (FHeap.disjoint_union_right.mp hd).1
  have hrW : ∀ l, W.In l → r.heap l = none := fun l hl =>
    (hdc l).resolve_right (cellsAt_some hl (hok.cellIn hl))
  refine ⟨hok, rsum r rY, rsum_left_comm (disj_cellsAt hrW), fun l hl => by
    show (r.heap l).or (rY.heap l) = none
    rw [hrW l hl, hY l hl]; rfl⟩

namespace FLock.Pair

variable {γ Y : Type} {L B : FLock γ} {C : FCond γ} {S : FSem γ Y L C}

/-- **A step of the semaphore keeps the two-lock product's rest** (module doc; `FSem.prim`'s
`Step`, the `kstep` of `L.Fits S.prim` at `Pair.U B U₀`): `B` stays kept, the rest stores its side
at the new memory, and the client keeps its own `U₀` at the protocol's rest after the step
(`hcl`). The client gives where its `U₀` keeps the condition (`hsub`), `B`'s coordinates over the
semaphore's places (`bph`, `bheld`, `lpart`, `bR`) and the condition's over `L`'s (`cph_l`), that
`B`'s side owns no byte of the condition's words (`hWo`), the keys apart (`hkey`), and that a
waiter of the condition is `away` from `B` or holds it at `holdsAway` with the epoch in `B`'s nest
(`hsleep`). -/
theorem U_semStep (hp : L.Pair B) {U₀ : (ThreadId → γ) → Res → Mem → Prop} {t : ThreadId}
    {G G' : ThreadId → γ} {rX rX' : Res} {m m' : Mem} (hs : S.prim.Step t G rX m G' rX' m')
    (hU : Pair.U B U₀ G rX m)
    (hsub : ∀ G rX m, U₀ G rX m → (C.prim L).Sub G rX m)
    (bph : ∀ g q, B.ph (S.place.set g q) = B.ph g)
    (bheld : ∀ g q, B.held (S.place.set g q) = B.held g)
    (lpart : ∀ g q, L.part (S.place.set g q) = L.part g)
    (cph_l : ∀ g q h, C.ph (L.set g q h) = C.ph g)
    (bR : ∀ G t q r, B.R G r → B.R (upd G t (S.place.set (G t) q)) r)
    (hWo : ∀ G m rL rH rX₀, B.Keeps G m rL rH rX₀ → U₀ G rX₀ m → ∀ W : Word 32 4,
      (W = C.S ∨ W = C.Ep) → ∀ l, W.In l → (side B m rL rH).owned l = none)
    (hkey : ∀ m, C.Ep.key m ≠ B.key m)
    (hsleep : ∀ G rX₀ m t, U₀ G rX₀ m → (C.ph (G t)).waits = true →
      B.ph (G t) = .away ∨ (B.ph (G t) = .holdsAway ∧ B.nest C.Ep.ptr))
    (hcl : ∀ sB rL rH rX₀ rX₀', rX = rsum sB rX₀ → rX' = rsum sB rX₀' →
      Res.Sim sB (side B m rL rH) → B.Keeps G m rL rH rX₀ → B.Keeps G' m' rL rH rX₀' →
      U₀ G rX₀ m → U₀ G' rX₀' m') :
    Pair.U B U₀ G' rX' m' := by
  obtain ⟨sB, rL, rH, rX₀, rfl, hsB, hk, hu⟩ := hU
  have hf := hk.facts
  -- `B`'s coordinates over the condition's and the semaphore's places
  have hpl : ∀ g q, B.ph (S.place.set g q) = B.ph g ∧ B.held (S.place.set g q) = B.held g ∧
      B.part (S.place.set g q) = B.part g := fun g q =>
    ⟨bph g q, bheld g q, by rw [← hp.part, ← hp.part, lpart]⟩
  have hc : ∀ g p, B.ph (C.set g p) = B.ph g ∧ B.held (C.set g p) = B.held g ∧
      B.part (C.set g p) = B.part g := fun g p => by
    rw [← S.place_c g p]; exact hpl g _
  have hss : ∀ g s, B.ph (S.set g s) = B.ph g ∧ B.held (S.set g s) = B.held g ∧
      B.part (S.set g s) = B.part g := fun g s => by
    rw [← S.place_s g s]; exact hpl g _
  have hl : ∀ g q h, B.ph (L.set g q h) = B.ph g ∧ B.held (L.set g q h) = B.held g ∧
      B.part (L.set g q h) = B.part g := fun g q h =>
    ⟨hp.ph_ab g q h, hp.held_ab g q h, hp.symm.part_ba g q h⟩
  -- `B`'s resource over the relabels of `t`
  have hRC : ∀ G t p r, B.R G r → B.R (upd G t (C.set (G t) p)) r := fun G t p r h => by
    have h' := bR G t (p, S.ph (G t)) r h; rwa [S.place_c] at h'
  have hRS : ∀ G t s r, B.R G r → B.R (upd G t (S.set (G t) s)) r := fun G t s r h => by
    have h' := bR G t (C.ph (G t), s) r h; rwa [S.place_s] at h'
  have hRL : ∀ (G : ThreadId → γ) t q h' r, B.R G r → B.R (upd G t (L.set (G t) q h')) r :=
    fun G t q h' r h => (hp.R_ab G t q h' r).mpr h
  rcases hs with ⟨-, hcs | ⟨-, hmv⟩⟩
  · -- a step of the condition's code at one of its words
    obtain ⟨Wd, rY, hWs, he, rfl, hY, hCI', hcase⟩ := hcs
    have hS := hsub G _ m hu
    obtain ⟨hok, rY₀, rfl, hY₀⟩ := hS.2 Wd hWs
    have hrot := rest_words hok (hsB.disj hk.side_disj) hY₀ he hY m'
    obtain ⟨hxd, hxo⟩ := Keeps.words hk hok m'
    rcases hcase with hmv | hown
    · obtain ⟨p, q, h, ⟨hnext, -, hms, -, -⟩, -, rfl⟩ := hmv
      have hWo' := hWo G m rL rH _ hk hu
      -- the sleep queues a waiter of the condition
      obtain ⟨hside, hk₁⟩ := Keeps.mstep hk hms (hWo' Wd hWs) (hWo' C.Ep (.inr rfl)) (hkey m)
        fun ⟨w, hw', hn⟩ => by
          have hEp := (hS.2 C.Ep (.inr rfl)).1
          rcases hms.waiters hw' with h' | rfl
          · exact absurd h' hn
          obtain ⟨i, jr, e, hreg, -⟩ := hCI'.q _ hw' (hms.key hEp).symm
          rw [upd_self, cph_l, C.ph_set] at hreg
          have hw : (C.ph (G t)).waits = true := hnext.waits (by rw [hreg]; rfl)
          exact (hsleep G _ m t hu hw).imp id fun ⟨h1, h2⟩ => ⟨h1, C.Ep.ptr, h2, hEp.keyAt⟩
      have hg := And.intro ((hl (C.set (G t) p) q h).1.trans (hc (G t) p).1)
        (And.intro ((hl (C.set (G t) p) q h).2.1.trans (hc (G t) p).2.1)
          ((hl (C.set (G t) p) q h).2.2.trans (hc (G t) p).2.2))
      have hk' := Keeps.relabel hk₁ (B.keep_upd hg.1 hg.2.1)
        (fun r h' => by
          have h₁ := hRL _ t q h r (hRC G t p r h')
          rwa [upd_self, upd_upd] at h₁)
        (hf.pdisj_upd hg.2.2 hg.2.1) hxd hxo
      exact ⟨sB, rL, rH, _, hrot, by rw [hside]; exact hsB, hk',
        hcl sB rL rH _ _ rfl hrot hsB hk hk' hu⟩
    · -- a native step on the thread's own part
      obtain ⟨r, -, -, -, hfs, -, -, -, hLi', rfl⟩ := hown
      rw [hrot] at hLi'
      have hpart : L.setPart (G t) r = B.setPart (G t) r := hp.setPart _ _
      obtain ⟨hsB', hk'⟩ := Keeps.partStep hp hk hsB hfs hLi' (by rw [hpart, B.ph_setPart])
        (by rw [hpart, B.held_setPart])
        (fun r' h' => by rw [hpart]; exact (B.R_setPart G t r r').mpr h') hxd hxo
      exact ⟨sB, rL, rH, _, hrot, hsB', hk', hcl sB rL rH _ _ rfl hrot hsB hk hk' hu⟩
  · cases hmv with
    | enter =>
      -- the waiter's entry into the condition: a relabel
      have hk' := Keeps.relabel hk (B.keep_upd (hc _ _).1 (hc _ _).2.1) (hRC G t .en)
        (hf.pdisj_upd (hc _ _).2.2 (hc _ _).2.1) hk.xdisj hk.xoff
      exact ⟨sB, rL, rH, rX₀, rfl, hsB, hk', hcl sB rL rH rX₀ rX₀ rfl rfl hsB hk hk' hu⟩
    | hold s h _ _ _ _ hfs hLi' _ _ =>
      -- the holder's step on the mutex's resource: `B`'s word cells from `L`'s invariant after it
      obtain ⟨G'', hLi''⟩ := hLi'
      have hg := And.intro ((hss (L.set (G t) .holds h) s).1.trans (hl (G t) .holds h).1)
        (And.intro ((hss (L.set (G t) .holds h) s).2.1.trans (hl (G t) .holds h).2.1)
          ((hss (L.set (G t) .holds h) s).2.2.trans (hl (G t) .holds h).2.2))
      obtain ⟨hsB', hk'⟩ := Keeps.stepAt hk hsB hfs (Keeps.cellsOf hk hsB hLi'')
        (B.keep_upd hg.1 hg.2.1)
        (fun r h' => by
          have h₁ := hRS _ t s r (hRL G t .holds h r h')
          rwa [upd_self, upd_upd] at h₁)
        (hf.pdisj_upd hg.2.2 hg.2.1) hk.xdisj hk.xoff
      exact ⟨sB, rL, rH, rX₀, rfl, hsB', hk', hcl sB rL rH rX₀ rX₀ rfl rfl hsB hk hk' hu⟩

end FLock.Pair

end Full
end Zig
