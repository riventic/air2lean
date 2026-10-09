import Proofs.Sync.RwLockContract

/-!
# Reusable synchronization contracts (C14)

Each contract below is a `Prop` structure over the *operations* of a sync object, not over its
code. A client proof that takes a contract as a hypothesis never sees the std implementation:
it cannot unfold `Io_Mutex_lockUncancelable` or `Io_Semaphore_waitUncancelable`, because it
receives only the operation as an abstract function. Each contract is proved once against the
translated Zig 0.16.0 std code (`examples/sync`, `Proofs/Sync/Gen.lean`); the futex under it is
the model (`ZigLean/Mem/Thread.lean`, `ZigLean/Conc/Sched.lean`).

| Contract | Operations | Proved once by | Scope |
|---|---|---|---|
| `MutexContract` | `Io.Mutex.lockUncancelable`, `unlock` | `mutex` (from `MutexOps.lock_specOn`, `unlock_specOn`) | every protocol with the lock (`Lock.FitsOn`), every thread count, any resource `R` |
| `SemContract` | `Io.Semaphore.waitUncancelable`, `post` | `semaphore` (from `Sem.wait_spec`, `post_spec`) | every protocol with the semaphore (`Sem.Fits`), any permit resource `Res`; at most one thread waits at its condition at a time (`hone`) |
| `CondContract` | `Io.Condition.waitUncancelable`, `signal` | `condition` (from `Sem.condWait_spec`, `signal_spec`) | the condition and mutex of an `Io.Semaphore` layout: the waited predicate is "permit count is 0", rechecked by the caller's loop; one waiter |
| `RwContract` | `Io.RwLock.lockSharedUncancelable`, `unlockShared`, `lockUncancelable`, `unlock` | `rwLock` (from the existing `RwLockRead` specs) | only the restricted protocol of `Proofs/Sync/RwLock.lean`: reader 0, writer 1, the counter resource `NPts` |

**Lock invariant and ownership transfer rules.** The mutex contract is the CSL lock rule:
`lock` moves a heap `hL` with `L.R G hL` (the lock invariant, read from the holder's ghost
value by `Lock.Inv.res`) from the lock into the caller's `held` part; `unlock` moves it back
and the release clock of the word's newest message is above every access to it
(`Lock.Inv.free`, `Lock.Owns`). The semaphore contract is the permit transfer rule: `post`
moves a heap `h₃` from the caller's part into the free permits' resource `Res`; `wait` moves a
heap `T` out of it (`hmv`). Facts about the protected heap are only available while it is
owned; pure snapshot facts never justify a transfer.

**Out of scope (stated, not claimed).**
- *Fairness, termination and starvation freedom*: every contract is partial correctness plus
  strict safety; a run that runs out of fuel satisfies every post. No contract states that a
  waiter is eventually woken or that `lock` eventually returns.
- *General RwLock*: the reusable `RwLock` contract for any number of readers and an arbitrary
  protected resource needs a new kit for the state word (`Proofs/Sync/RwLock.lean` fixes reader 0,
  writer 1 and `NPts`). `RwContract` only packages the restricted specs.
- *`Io.Event` / `ResetEvent`*: the translated `Io_Event_set` and `Io_Event_waitUncancelable` are
  proved only inside the fixed `handoff` protocol (`Proofs/Sync/Handoff.lean`); no reusable event
  kit exists yet.
- *WaitGroup*: Zig 0.16.0's `examples/sync` has no translated `WaitGroup`; the 0.15.2
  `Thread.WaitGroup` proof (`Proofs/Threadsync/WaitGroup.lean`) is a fixed two-task client.
- *Multiple condition waiters, broadcast, timeouts and cancellation* are not covered.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Sync Assn

namespace Sync.Contracts

/-! ## `Io.Mutex` -/

/-- The reusable `Io.Mutex` contract for operations `lockOp`, `unlockOp` at the lock word
`L.ptr` (contended value 2). It holds for every protocol `P` that has the lock `L`
(`Lock.FitsOn`), where only threads with `ok` run the lock's code. -/
structure MutexContract (lockOp unlockOp : Ptr → Io → ConcM Tgt Unit) : Prop where
  /-- `lock` by thread `t` at `out`: it holds the lock, with a resource `hL`
  (`L.R G hL` by `Lock.Inv.res`). The depth decreases: `lock` stops at least once. -/
  lock : ∀ {γ : Type} {L : Lock γ} {P : Proto Tgt γ} {U : (ThreadId → γ) → Mem → Prop}
    {ok : γ → Prop}, L.FitsOn P U ok → L.c = 2 → ∀ (t : ThreadId) (g : γ), L.ph g = .out →
    ok g → ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat), P.inv (upd G t g) m →
    P.WP t (lockOp L.ptr io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ hL, P.inv (upd G' t (L.set g .holds hL)) m') G m d
  /-- `unlock` by the holder `t`, the current thread: it goes to `out` and the lock owns the
  resource again. -/
  unlock : ∀ {γ : Type} {L : Lock γ} {P : Proto Tgt γ} {U : (ThreadId → γ) → Mem → Prop}
    {ok : γ → Prop}, L.FitsOn P U ok → L.c = 2 → ∀ (t : ThreadId) (g : γ), L.ph g = .holds →
    ok g → ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat), P.inv (upd G t g) m →
    m.current = t →
    P.WP t (unlockOp L.ptr io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (L.set g .out Heap.empty)) m') G m d

theorem ptr_add0 (p : Ptr) : (p.add 0).add 0 = p := by
  cases p; simp [Ptr.add]

/-- **The translated `Io.Mutex` satisfies the contract**, proved once from the generated code
(`Proofs/Sync/Lock.lean`). -/
theorem mutex : MutexContract Io_Mutex_lockUncancelable Io_Mutex_unlock where
  lock hP hc t g hg hok io G m d hi :=
    MutexOps.lock_specOn hP (ptr_add0 _) (by rw [hc]; rfl) t g hg hok io G m d hi
  unlock hP hc t g hg hok io G m d hi hcur :=
    MutexOps.unlock_specOn hP (ptr_add0 _) (by rw [hc]; rfl) t g hg hok io G m d hi hcur

/-- The lock invariant, as a client sees it: the holder's resource satisfies `L.R`. -/
theorem MutexContract.held_res {γ : Type} {L : Lock γ} {G : ThreadId → γ} {m : Mem}
    {t : ThreadId} (hi : L.Inv G m) (hh : L.ph (G t) = .holds) : L.R G (L.held (G t)) :=
  hi.res t hh

/-! ## `Io.Semaphore` -/

/-- The reusable `Io.Semaphore` contract for the operations `waitOp`, `postOp` of the semaphore
`S`, for every protocol with it (`Sem.Fits`). The permit resource `Res` and the transfer `T`
are arbitrary. `hone`: while `t` waits for a permit, no other thread is registered at the
semaphore's condition. -/
structure SemContract {X : Type} (S : Sem X) (waitOp postOp : Ptr → Io → ConcM Tgt Unit) :
    Prop where
  /-- `wait` by `t` at `x`: it takes one permit and with it a heap `h₃` with `T h₃`. -/
  wait : ∀ {P : Proto Tgt (SGh X)} {U : (ThreadId → SGh X) → Mem → Prop}, S.Fits P U →
    ∀ (t : ThreadId) (pa : Heap) (x x' : X) (T : Assn) (io : Io),
    (∀ G' m', P.inv G' m' → (G' t).2.2 = x → (G' t).1.ph = .holds → S.PZ m' → ∀ u, u ≠ t →
      ∀ i jr sn e, (G' u).2.1 ≠ .reg i jr sn e) → S.wx x → S.inS x → S.inS x' →
    (∀ Y : ThreadId → X, Y t = x → S.pv Y ≠ 0 → S.pv (upd Y t x') = S.pv Y - 1 ∧
      ∀ hr, S.Res Y hr → ∃ h₁ h₂, hr = h₁ ∪ h₂ ∧ Heap.Disjoint h₁ h₂ ∧ S.Res (upd Y t x') h₁ ∧
        T h₂) →
    (∀ G m h₁ h₂ h₃ h₄, T h₃ → Heap.Disjoint h₄ h₃ →
      S.Res (Sem.xs fun u => (upd G t (⟨.holds, pa, h₁⟩, .none, x) u).2) (h₄ ∪ h₃) →
      U (upd G t (⟨.holds, pa, h₁⟩, .none, x)) m → U (upd G t (⟨.holds, pa ∪ h₃, h₂⟩, .none, x')) m) →
    ∀ (G : ThreadId → SGh X) (m : Mem) (d : Nat),
    P.inv (upd G t (⟨.out, pa, Heap.empty⟩, .none, x)) m →
    P.WP t (waitOp S.ptr io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ h₃, T h₃ ∧ P.inv (upd G' t (⟨.out, pa ∪ h₃, Heap.empty⟩, .none, x')) m') G m d
  /-- `post` by `t` at `x`, with `h₃` in its part: it gives one permit and `h₃` to `Res`. -/
  post : ∀ {P : Proto Tgt (SGh X)} {U : (ThreadId → SGh X) → Mem → Prop}, S.Fits P U →
    ∀ (t : ThreadId) (pa h₃ : Heap) (x x' : X) (io : Io), S.inS x → S.inS x' →
    (∀ G m hL, P.inv (upd G t (⟨.holds, pa ∪ h₃, hL⟩, .pst, x)) m →
      S.pv (upd (Sem.xs fun u => (upd G t (⟨.holds, pa ∪ h₃, hL⟩, .pst, x) u).2) t x') =
        S.pv (Sem.xs fun u => (upd G t (⟨.holds, pa ∪ h₃, hL⟩, .pst, x) u).2) + 1 ∧
      (S.pv (Sem.xs fun u => (upd G t (⟨.holds, pa ∪ h₃, hL⟩, .pst, x) u).2)).toNat + 1 < 2 ^ 64 ∧
      ∀ hr, S.Res (Sem.xs fun u => (upd G t (⟨.holds, pa ∪ h₃, hL⟩, .pst, x) u).2) hr →
        Heap.Disjoint h₃ hr →
        S.Res (upd (Sem.xs fun u => (upd G t (⟨.holds, pa ∪ h₃, hL⟩, .pst, x) u).2) t x')
          (h₃ ∪ hr)) →
    (∀ G m h₁ h₂, U (upd G t (⟨.holds, pa ∪ h₃, h₁⟩, .pst, x)) m →
      U (upd G t (⟨.holds, pa, h₂⟩, .pst, x')) m) →
    Heap.Disjoint pa h₃ → ∀ (G : ThreadId → SGh X) (m : Mem) (d : Nat),
    P.inv (upd G t (⟨.out, pa ∪ h₃, Heap.empty⟩, .none, x)) m →
    P.WP t (postOp S.ptr io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (⟨.out, pa, Heap.empty⟩, .none, x')) m') G m d

/-- **The translated `Io.Semaphore` satisfies the contract** (`Proofs/Sync/Semaphore.lean`);
its `wait` is the condition-variable loop of std (`while permits == 0: cond.wait`). -/
theorem semaphore {X : Type} (S : Sem X) :
    SemContract S Io_Semaphore_waitUncancelable Io_Semaphore_post where
  wait hP t pa x x' T io hone hwx hinS hinS' hmv hU G m d hi :=
    Sem.wait_spec hP t pa x x' T io hone hwx hinS hinS' hmv hU G m d hi
  post hP t pa h₃ x x' io hinS hinS' hmv hU hdj G m d hi :=
    Sem.post_spec hP t pa h₃ x x' io hinS hinS' hmv hU hdj G m d hi

/-! ## `Io.Condition` (in the semaphore layout) -/

/-- The `Io.Condition` contract in the layout of an `Io.Semaphore` `S`: the condition at
`S.ptr + 12`, its mutex at `S.ptr + 8`, and the waited predicate "the `u64` at `S.ptr` is 0".
`wait` atomically releases the mutex, sleeps, and returns holding the mutex again with a new
resource `hL'`; the caller must recheck its predicate (std's `while` loop). `signal` is called
by the mutex holder in the condition's critical code (`.pst`). -/
structure CondContract {X : Type} (S : Sem X)
    (waitOp : Ptr → Io → Ptr → ConcM Tgt Unit) (signalOp : Ptr → Io → ConcM Tgt Unit) :
    Prop where
  wait : ∀ {P : Proto Tgt (SGh X)} {U : (ThreadId → SGh X) → Mem → Prop}, S.Fits P U →
    ∀ (t : ThreadId) (pa hL : Heap) (x : X) (io : Io) (G : ThreadId → SGh X) (m : Mem) (d : Nat),
    P.inv (upd G t (⟨.holds, pa, hL⟩, .none, x)) m →
    (∃ hp, pts S.ptr 8 (0 : BitVec 64) hp ∧ hp.Sub hL) →
    (∀ G' m', P.inv G' m' → (G' t).2.2 = x → (G' t).1.ph = .holds → S.PZ m' → ∀ u, u ≠ t →
      ∀ i jr sn e, (G' u).2.1 ≠ .reg i jr sn e) → S.wx x → S.inS x →
    P.WP t (waitOp (S.ptr.add 12) io (S.ptr.add 8)) (fun _ G' m' d' =>
      d' < d ∧ m'.current = t ∧ ∃ hL', P.inv (upd G' t (⟨.holds, pa, hL'⟩, .none, x)) m') G m d
  signal : ∀ {P : Proto Tgt (SGh X)} {U : (ThreadId → SGh X) → Mem → Prop}, S.Fits P U →
    ∀ (t : ThreadId) (a : LG) (x : X), a.ph = .holds → S.inS x →
    ∀ (io : Io) (G : ThreadId → SGh X) (m : Mem) (d : Nat), P.inv (upd G t (a, .pst, x)) m →
    P.WP t (signalOp (S.ptr.add 12) io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (a, .none, x)) m') G m d

/-- **The translated `Io.Condition` satisfies the contract** (`Proofs/Sync/Semaphore.lean`). -/
theorem condition {X : Type} (S : Sem X) :
    CondContract S Io_Condition_waitUncancelable Io_Condition_signal where
  wait hP t pa hL x io G m d hi hz hone hwx hinS :=
    Sem.condWait_spec hP t pa hL x io G m d hi hz hone hwx hinS
  signal hP t a x ha hinS io G m d hi := Sem.signal_spec hP t a x ha hinS io G m d hi

/-! ## `Io.RwLock` (restricted) -/

section RwLock

open Sync.RwLockRead

variable {S : Type} [Inhabited S]

/-- The shared and exclusive `Io.RwLock` rules of the restricted protocol `proto E` of
`Proofs/Sync/RwLock.lean` (reader 0, writer 1, counter resource `NPts`), over a semaphore part
`E` with `E.Spec`. Not a contract for arbitrary readers or resources. -/
structure RwContract (E : Sync.RwLockRead.Sem S)
    (lockS unlockS lockX unlockX : Ptr → Io → ConcM Tgt Unit) : Prop where
  lockShared : ∀ {j : Bool} {io : Io} {G : ThreadId → Gh S} {m : Mem} {d : Nat},
    (proto E).inv (upd G 0 (gA (.ls j) Heap.empty default)) m →
    (proto E).WP 0 (lockS (bPtr.add 16) io) (fun _ G' m' d' => d' ≤ d ∧
      m'.current = 0 ∧ ∃ h, (proto E).inv (upd G' 0 (gA (.sh j) h default)) m') G m d
  unlockShared : ∀ {j : Bool} {h : Heap} {io : Io} {G : ThreadId → Gh S} {m : Mem} {d : Nat},
    (proto E).inv (upd G 0 (gA (.sh j) h default)) m →
    (proto E).WP 0 (unlockS (bPtr.add 16) io) (fun _ G' m' d' => d' ≤ d ∧
      m'.current = 0 ∧ (proto E).inv (upd G' 0 (gA (.dn j) Heap.empty default)) m') G m d
  lock : ∀ {k : Nat}, k < 2 → ∀ {io : Io} {G : ThreadId → Gh S} {m : Mem} {d : Nat},
    (proto E).inv (upd G 1 (gA (.wo k) Heap.empty default)) m →
    (proto E).WP 1 (lockX (bPtr.add 16) io) (fun _ G' m' d' => d' < d ∧
      m'.current = 1 ∧ ∃ h, NPts k h ∧ (proto E).inv (upd G' 1 (gA (.wn k) h default)) m') G m d
  unlock : ∀ {k : Nat} {hn : Heap}, NPts k hn → ∀ {io : Io} {G : ThreadId → Gh S} {m : Mem}
    {d : Nat}, (proto E).inv (upd G 1 (gA (.wn k) hn default)) m →
    (proto E).WP 1 (unlockX (bPtr.add 16) io) (fun _ G' m' d' => d' < d ∧
      m'.current = 1 ∧ (proto E).inv (upd G' 1 (gA (.wo k) Heap.empty default)) m') G m d

/-- **The translated `Io.RwLock` satisfies the restricted contract**, for every semaphore part
with `E.Spec` (`spec₀` gives it for the translated semaphore). -/
theorem rwLock {E : Sync.RwLockRead.Sem S} (hE : E.Spec) :
    RwContract E Io_RwLock_lockSharedUncancelable Io_RwLock_unlockShared
      Io_RwLock_lockUncancelable Io_RwLock_unlock where
  lockShared hi := lockS_spec hE hi
  unlockShared hi := unlockS_spec hE hi
  lock hk _ _ _ _ hi := wlock_spec hE hk hi
  unlock hp _ _ _ _ hi := wunlock_spec hE hp hi

end RwLock

end Sync.Contracts
