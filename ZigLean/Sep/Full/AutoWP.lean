import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.ThreadOwned

/-!
# The `WP` rules of `fsym` (a thread's run in a protocol, `Proto.WP`)

`fsym` walks a goal `P.WP t x Q G m n` with its `WP` backend (`Auto.lean`, §The `WP` backend;
`docs/proof-automation.md` §WP). Its step rules are `@[fsym]` theorems whose conclusion is a
`WP` of one command; this module registers the library's:

- **`MemM` segments** of a thread that owns its part (`FOwned`): `WP.liftMem_fowned` (a
  partial thread triple, for a protocol with `Proto.Partial`) and `WP.liftMem_fownedT` (a total
  one, for every protocol), and their forms for a step of a concurrent body (`liftM`, `callMC`).
  The segment's triple is walked by the thread backend, its post inferred.
- **Stops**: `spawn` and `join` (`WP.spawnC`, `WP.joinC`): the thread's ghost value at the stop
  is fixed by the invariant in the context.

A protocol's own rules (a lock's code, `LockRules.lean`; a contract such as
`MutexImpl.lock_wp`) are passed as `fsym [r, …]` with their protocol arguments.
-/

namespace Zig
namespace Conc
namespace Proto

open Full

variable {Tgt γ σ α : Type} {P : Proto Tgt γ} {t : ThreadId} {G : ThreadId → γ} {m : Mem}
  {n : Nat} {own : ThreadId → Res} {rO : Res}

/-- `WP.liftMem_fowned` with a total thread triple: for every protocol (also one that counts
turns, where `Proto.Partial` fails). -/
theorem WP.liftMem_fownedT {x : MemM α} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop} (ht : FTTotalTriple Pa x Qa) (ho : FOwned own rO m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → FOwned (upd own t r') rO m' → Qa a r' →
      m'.current = t → m'.threads = m.threads → Q a G m' n) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n :=
  WP.liftMem_fowned ht.1 ho hc htl hp h (.inr ht.2)

/-- `WP.liftM_fowned` with a total thread triple. -/
theorem WP.liftM_fownedT {x : MemM α} {s : σ} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop} (ht : FTTotalTriple Pa x Qa) (ho : FOwned own rO m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → FOwned (upd own t r') rO m' → Qa a r' →
      m'.current = t → m'.threads = m.threads → Q (a, s) G m' n) :
    P.WP t ((_root_.liftM x : CM Tgt σ α).run s) Q G m n :=
  WP.liftM_fowned ht.1 ho hc htl hp h (.inr ht.2)

/-- `WP.callMC_fowned` with a total thread triple. -/
theorem WP.callMC_fownedT {x : MemM α} {s : σ} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop} (ht : FTTotalTriple Pa x Qa) (ho : FOwned own rO m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → FOwned (upd own t r') rO m' → Qa a r' →
      m'.current = t → m'.threads = m.threads → Q (a, s) G m' n) :
    P.WP t ((Zig.callMC x : CM Tgt σ α).run s) Q G m n :=
  WP.callMC_fowned ht.1 ho hc htl hp h (.inr ht.2)

/-- A `MemM` step whose run the protocol knows (`hx`, a lemma of the protocol's memory: a field
pointer of a shared object, a read of a constant): no stop, its value. -/
theorem WP.liftMem_pure {x : MemM α} {v : α} {m' : Mem}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop} (hx : x.run m = pure (v, m'))
    (hsz : m'.threads.size = m.threads.size) (h : Q v G m' n) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n := by
  have hr : (x.run m).run = some (.ok (v, m')) := by rw [hx]; rfl
  refine WP.liftMem (fun e he => ?_) (fun a m'' he => ?_) fun hn => ?_
  · rw [hr] at he; cases he
  · rw [hr] at he; cases he; exact ⟨hsz, h⟩
  · rw [hr] at hn; cases hn

/-- `WP.liftMem_pure` for a step of a concurrent body (`callMC x`, `liftM x`). -/
theorem WP.callMC_pure {x : MemM α} {v : α} {m' : Mem} {s : σ}
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop} (hx : x.run m = pure (v, m'))
    (hsz : m'.threads.size = m.threads.size) (h : Q (v, s) G m' n) :
    P.WP t ((Zig.callMC x : CM Tgt σ α).run s) Q G m n := by
  have hr : (x.run m).run = some (.ok (v, m')) := by rw [hx]; rfl
  refine WP.callMC (fun e he => ?_) (fun a m'' he => ?_) fun hn => ?_
  · rw [hr] at he; cases he
  · rw [hr] at he; cases he; exact ⟨hsz, h⟩
  · rw [hr] at hn; cases hn

-- the steps of a concurrent body that need no protocol: a call of a concurrent function, a
-- pure step
attribute [fsym] WP.callC WP.callRC

-- the total forms first: the rules are tried last-registered first, so a partial protocol
-- takes the partial triple (no termination needed) and a turn-counting one the total triple
attribute [fsym] WP.liftMem_fownedT WP.liftM_fownedT WP.callMC_fownedT
attribute [fsym] WP.liftMem_fowned WP.liftM_fowned WP.callMC_fowned
attribute [fsym] WP.spawnC WP.joinC

end Proto
end Conc
end Zig
