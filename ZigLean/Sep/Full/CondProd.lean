import ZigLean.Sep.Full.Cond
import ZigLean.Sep.Full.LockProd

/-!
# A condition next to the other lock of a two-lock product

(ledger #two-lock-product, item (5).) In a two-lock product (`ZigLean/Sep/Full/LockProd.lean`) the
semaphore's mutex `L` may run a condition `C` (`FCond.prim`, a semaphore's `FSem.prim`) while the
other lock `B` rides in `L`'s rest (`FLock.Pair.U B U`). This module states once, for every lock
`B` and every condition `C`, what `B` keeps over the condition's steps and where the condition's
words lie next to `B`'s side; a product's view of `L` (the reader/writer lock's semaphore,
`ZigLean/Sep/Full/RwLockProd.lean`) uses them.

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
  (`ZigLean/Sep/Full/LockProd.lean`, with `Keeps.queue`, `Keeps.wordRun` and `WInv.push`: they
  hold for any lock).
- **The condition's words next to `B`'s side** (`FPrim.ofWords_sub_rsum`): a primitive over futex
  words whose `Sub` holds at the protocol's own rest also holds with a resource apart from it in
  front (`B`'s side, `FLock.Keeps.side_disj`), the `sub` of `FLock.Pair.fits` for such a primitive.
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
    obtain ⟨he, hkM⟩ := Keeps.wordRun (m := { m with current := t }) hk₁ hw hc
      (.inr (.inr (.inr (.inr rfl)))) hEo
    exact ⟨he, Keeps.queue hkM (hkM.facts.w.push hkey fun hn => ht ⟨_, Array.mem_push_self, hn⟩)⟩
  | woken => exact ⟨rfl, Keeps.queue hk₁ (hk₁.facts.w.requeue hk₁.facts.w.fq hk₁.facts.w.wit)⟩
  | resume => exact ⟨rfl, hk₁⟩
  | wake c cs h =>
    have hw := hk₁.facts.w.wakeOff hkey h
    obtain rfl := Proto.modify_ok h
    exact ⟨rfl, Keeps.queue hk₁ hw⟩

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

end Full
end Zig
