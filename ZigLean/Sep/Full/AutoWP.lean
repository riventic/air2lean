import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.ThreadOwned

/-!
# The `WP` rules of `fsym` (a thread's run in a protocol, `Proto.WP`)

`fsym` walks a goal `P.WP t x Q G m n` with its `WP` backend (`Auto.lean`, §The `WP` backend;
`docs/proof-automation.md` §WP). Its step rules are `@[fsym]` theorems whose conclusion is a
`WP` of one command; this module registers the library's.

**One form for memory steps.** The walk sees a concurrent body in normal form: a memory step of
generated code (`(callMC x).run s`, `(liftM x).run s`, `(callRC x).run s`, `liftR`) is
`ConcM.liftMem x >>= fun a => pure (a, s)` (`fsym_norm`, `CNorm.run_*`), and consecutive steps are
one `ConcM.liftMem` (`liftMem_bind`). So every rule for a memory step, of the library or of a
protocol (`fsym [r]`), is stated on `ConcM.liftMem x` with a post over the step's value `a`; a
rule stated on the step form (`WP.liftM_fowned`, `WP.callMC_ptrProject`, …: hand proofs) never
applies. Stops (atomics, `sync`, `spawn`, `join`) keep their step form (`WP.spawnC`, the lock
rules `wp_casOn`, …): their definitions are not unfolded in a `WP` walk.

- **`MemM` segments** of a thread that owns its part (`FOwned`): `WP.liftMem_fowned` (a
  partial thread triple, for a protocol with `Proto.Partial`) and `WP.liftMem_fownedT` (a total
  one, for every protocol). The segment's triple is walked by the thread backend, its post
  inferred.
- **Steps without a stop**: `WP.liftMem_liftR` (a pure function's result; the checked `+`/`-`
  that do not overflow by `WP.liftMem_add`/`_sub`, their values as facts), `WP.liftMem_pure` (a
  step whose run a protocol lemma gives: a field pointer of a shared object, `fsym
  [WP.liftMem_pure h]`).
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

/-- **A pure step** (`callRC x`, `liftM x` of a `Result`, in normal form): no stop, its value.
In strict mode it does not throw (`herr`). -/
theorem WP.liftMem_liftR {x : Result α} {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
    (herr : ∀ e, x.run = some (.error e) → P.strict = false)
    (h : ∀ a, x.run = some (.ok a) → Q a G m n)
    (hnone : x.run = none → P.Partial := by
      intro
      first
        | exact .inl rfl
        | exact .inr rfl
        | assumption) :
    P.WP t (ConcM.liftMem (StateT.lift x : MemM α) : ConcM Tgt α) Q G m n := by
  refine WP.liftMem (fun e he => herr e ?_) (fun a m' he => ?_) fun hn => hnone ?_
  · simp only [StateT.run, StateT.lift, ExceptT.run_bind] at he
    match hr : x.run, he with
    | none, he => simp at he
    | some (.error _), he => simpa using he
    | some (.ok _), he => simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at he
  · obtain ⟨hx, rfl⟩ := MemM.lift_ok he
    exact ⟨rfl, h a hx⟩
  · simp only [StateT.run, StateT.lift, ExceptT.run_bind] at hn
    match hr : x.run, hn with
    | none, _ => rfl
    | some (.error _), hn => simp at hn
    | some (.ok _), hn => simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at hn

/-- **A checked unsigned `+` that does not overflow** (as `add_step` of a thread's walk): its
value as a fact. -/
theorem WP.liftMem_add {w : Nat} {a b : BitVec w} {Q : BitVec w → (ThreadId → γ) → Mem → Nat → Prop}
    (hlt : a.toNat + b.toNat < 2 ^ w) (h : ∀ r : BitVec w, r.toNat = a.toNat + b.toNat → Q r G m n) :
    P.WP t (ConcM.liftMem (StateT.lift (Zig.add false a b) : MemM (BitVec w)) : ConcM Tgt (BitVec w))
      Q G m n := by
  have e : Zig.add false a b = pure (a + b) := by
    simp only [Zig.add, BitVec.uaddOverflow, Bool.false_eq_true, ↓reduceIte]
    rw [if_neg (by simp; omega)]
  exact WP.liftMem_pure (by rw [e]; rfl) rfl (h _ (BitVec.toNat_add_of_lt hlt))

/-- **A checked unsigned `-` that does not overflow** (as `sub_step`). -/
theorem WP.liftMem_sub {w : Nat} {a b : BitVec w} {Q : BitVec w → (ThreadId → γ) → Mem → Nat → Prop}
    (hle : b.toNat ≤ a.toNat) (h : ∀ r : BitVec w, r.toNat + b.toNat = a.toNat → Q r G m n) :
    P.WP t (ConcM.liftMem (StateT.lift (Zig.sub false a b) : MemM (BitVec w)) : ConcM Tgt (BitVec w))
      Q G m n := by
  have e : Zig.sub false a b = pure (a - b) := by
    simp only [Zig.sub, BitVec.usubOverflow, Bool.false_eq_true, ↓reduceIte]
    rw [if_neg (by simp; omega)]
  refine WP.liftMem_pure (by rw [e]; rfl) rfl (h _ ?_)
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]; omega

-- (after the general pure step: tried first, they leave facts instead of a run's equation)
attribute [fsym] WP.liftMem_liftR
attribute [fsym] WP.liftMem_add WP.liftMem_sub

-- the total forms first: the rules are tried last-registered first, so a partial protocol
-- takes the partial triple (no termination needed) and a turn-counting one the total triple
attribute [fsym] WP.liftMem_fownedT
attribute [fsym] WP.liftMem_fowned
attribute [fsym] WP.spawnC WP.joinC

end Proto
end Conc
end Zig
