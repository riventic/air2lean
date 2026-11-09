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
  (`op`: `Word.actualRun_rest`'s `RestStep` and `Word.actualRun_fstep`'s `FStepIn`, as
  `Keeps.wordStep`), the futex wait's sleep at the epoch (`sleep`: a read of the epoch, then `t`
  in the futex queue at the epoch's key, `LockWord.WInv.push`: `t` is `away` from `B`, or holds it
  at `holdsAway` with the epoch's key in `B`'s nest, as `LockWord.Queue` admits; the same premise
  as `Keeps.otherStep`'s), and a futex wake at the epoch (`wake`, `LockWord.WInv.wakeOff`). `B`'s
  side owns no byte of `W` or of the epoch, and the epoch's key is not `B`'s. `B`'s side is then
  exactly the same. A change of the stepping thread's places that keeps `B`'s is
  `Keeps.relabel`.
- **The condition's words next to `B`'s side** (`FPrim.ofWords_sub_rsum`): a primitive over futex
  words whose `Sub` holds at the protocol's own rest also holds with a resource apart from it in
  front (`B`'s side, `FLock.Keeps.side_disj`), the `sub` of `FLock.Pair.fits` for such a primitive.
-/

namespace Zig
namespace Full

open Conc Proto

namespace LockWord

variable {L : LockWord}

/-- **A thread joins the futex queue at another key** (the sleep of a futex wait at another word,
`FCond.MStep.sleep`; `WInv.waitOff`/`waitNest` for the whole wait): the invariant holds with
`(t, k)` in the queue, when `t` is `away` from the lock or holds it at `holdsAway` with `k` in its
nest (`Queue`), unless `t` was queued at `k` already. -/
theorem WInv.push {P : ThreadId → LPh} {m : Mem} {t : ThreadId} {k : FutexKey} (hi : L.WInv P m)
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

namespace FLock.Pair

variable {γ : Type} {B : FLock γ} {G : ThreadId → γ} {m : Mem} {rL rH rX : Res}

/-- **A change of the ghost values that keeps `B`'s places and held resources keeps what the
product keeps of `B`**, at the same memory, free and holders' resources, and a new protocol rest
`rX'` (with its facts in `Keeps`). -/
theorem Keeps.relabel {G' : ThreadId → γ} {rX' : Res} (hk : B.Keeps G m rL rH rX)
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

/-- **A change of the futex queue, the woken threads and the current thread keeps what the product
keeps of `B`**, given `B`'s word invariant after it (`LockWord.WInv.requeue`, `WInv.push`,
`WInv.wakeOff`). -/
theorem Keeps.queue (hk : B.Keeps G m rL rH rX) {c : ThreadId} {ws : Array (ThreadId × FutexKey)}
    {wk : Array ThreadId} (hw : B.WInv (B.pl G) { m with current := c, waiters := ws, woken := wk }) :
    B.Keeps G { m with current := c, waiters := ws, woken := wk } rL rH rX :=
  { hk with facts := { hk.facts with w := hw } }

/-- **An actual op at a word apart from `B`'s side keeps what the product keeps of `B`**
(`Keeps.wordStep` at `Word.actualRun_rest` and `Word.actualRun_fstep`): `B`'s side is the same. -/
theorem Keeps.wordRun {n nb : Nat} {W : Word n nb} {A : ThreadId → Prop} {m' : Mem}
    (hk : B.Keeps G m rL rH rX) (hw : W.Ok m A) (hc : m.current < m.clocks.size)
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

variable {C : FCond γ} {W : Word 32 4} {t : ThreadId} {m' : Mem}

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
    refine ⟨he, Keeps.queue hkM (hkM.facts.w.push hkey fun hn => ht ?_)⟩
    exact ⟨_, Array.mem_push_self, hn⟩
  | woken => exact ⟨rfl, Keeps.queue hk₁ (hk₁.facts.w.requeue hk₁.facts.w.fq hk₁.facts.w.wit)⟩
  | resume => exact ⟨rfl, hk₁⟩
  | wake c cs h =>
    have hw := hk₁.facts.w.wakeOff hkey h
    have hm' := Proto.modify_ok h
    subst hm'
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
  have hrW : ∀ l, W.In l → r.heap l = none := fun l hl =>
    (hd l).resolve_right fun e => by
      have e' : ((W.cellsR m).heap l).or (rY.heap l) = none := e
      exact cellsAt_some hl (hok.cellIn hl) (Option.or_eq_none_iff.mp e').1
  refine ⟨hok, rsum r rY, ?_, fun l hl => by
    show (r.heap l).or (rY.heap l) = none
    rw [hrW l hl, hY l hl]; rfl⟩
  rw [← rsum_assoc, rsum_comm (disj_cellsAt hrW), rsum_assoc]

end Full
end Zig
