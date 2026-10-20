import Proofs.Threadsync.Variant
import ZigLean.Sep.Full.Mutex
import ZigLean.Sep.Full.LockSteps
import ZigLean.Sep.Full.AutoWP

/-!
# `Thread.Mutex` of `examples/threadsync` as a mutex (`MutexImpl`, 0.15.2, Linux and macOS)

The per-item obligation of `Thread.Mutex` (Zig 0.15.2's std code) in this program's generated
code: `Thread_Mutex_lock` and `Thread_Mutex_unlock` satisfy the mutex contract
(`ZigLean/Sep/Full/Mutex.lean`) for every protocol that has the lock (`FLock.Fits`). The steps
are the rules of a lock's code (`ZigLean/Sep/Full/LockRules.lean`); this file follows the
generated control flow. The translation depends on the target (`Proofs/Threadsync/Variant.lean`):

- **Linux** (`FutexImpl`, the committed `Gen.lean`): `tryLock` is an acquire `or(1)`
  (`wp_orLock`), or on aarch64-linux (`tests/golden/0.15.2/threadsync/Gen-linux-aarch64.lean`) a
  weak acquire `cmpxchg` `0 → 1` (`wp_casWeakLock`); `lockSlow` a relaxed load and a loop of
  `xchg(3)` with a futex wait, `unlock` the owner check, an `xchg(0)` with a release and a wake.
  The contended value is `3`.
- **macOS** (`DarwinImpl`): `lock` is `os_unfair_lock_lock` (`Zig.osUnfairLockC`): a loop of an
  acquire `cmpxchg 0 → 1` with a futex wait while the word is `1`; `unlock` the owner check, a
  release `xchg 0` and a wake. The contended value is `1`.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FLock

namespace Threadsync

/-- The states of `Thread.Mutex.FutexImpl`: `unlocked`, `locked`, `contended` (`3`). -/
def threadMutexW : LockWord.States (BitVec 32) where
  unl := 0
  one := 1
  two := 3
  c := 3
  bits0 := rfl
  bits1 := rfl
  bits2 := rfl
  dec0 := rfl
  dec1 := rfl
  dec2 := rfl
  ne01 := by decide
  ne02 := by decide
  ne12 := by decide

namespace ThreadMutex

variable {γ : Type} {L : FLock γ} {K : FPrim γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

if_decl Thread_Mutex_FutexImpl_lock in

/-- `tryLock` by thread `t` at `out` (`g`): `true` and `t` holds the mutex, or `false` and `t` is
at `spin`. -/
theorem tryLock_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) (hc3 : L.c = 3) {p : Ptr}
    (hp : p = L.ptr) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g) (G : ThreadId → γ)
    (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_FutexImpl_tryLock p) (fun r G' m' d' => d' < d ∧ m'.current = t ∧
      ((r = true ∧ ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') ∨
       (r = false ∧ P.inv (upd G' t (L.set g .spin rnil)) m'))) G m d := by
  subst hp
  fsym [wp_orLock hP hc3, wp_casWeakLock hP, L.ph_set, L.set_set, hP.ok_set]

/-- The loop invariant of `lockSlow`: thread `t` is at `spin`. -/
def lockInv (P : Proto Tgt γ) (L : FLock γ) (t : ThreadId) (g : γ) (D : Nat)
    (_ : Thread_Mutex_FutexImpl_lockSlowLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ P.inv (upd G t (L.set g .spin rnil)) m

/-- The loop of `lockSlow` ends when thread `t` holds the mutex. -/
def lockPost (P : Proto Tgt γ) (L : FLock γ) (t : ThreadId) (g : γ) (D : Nat)
    (r : Thread_Mutex_FutexImpl_lockSlowExit × Thread_Mutex_FutexImpl_lockSlowLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  r.1 = .br15 ∧ d < D ∧ m.current = t ∧ ∃ rL, P.inv (upd G t (L.set g .holds rL)) m

/-- One repeat of `lockSlow`'s loop: `xchg(3)`; the thread holds the mutex, or it waits at the
futex (a stop, so the depth gets smaller). -/
theorem loop16_body (hP : L.Fits K P U ok) (hcost : P.cost = none) (hc3 : L.c = 3)
    (t : ThreadId) (g : γ) (hok : ok g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered)
    (D : Nat) (s : Thread_Mutex_FutexImpl_lockSlowLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (h : lockInv P L t g D s G m d) :
    P.WP t ((Thread_Mutex_FutexImpl_lockSlow.loop16 L.ptr).run s) (fun r G' m' d' =>
      if Thread_Mutex_FutexImpl_lockSlow.again16 r.1 then lockInv P L t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 <
          (fun (_ : Thread_Mutex_FutexImpl_lockSlowLocals) => 0) s)
      else lockPost P L t g D r G' m' d') G m d := by
  obtain ⟨hD, hcur, hi⟩ := h
  have hS : threadMutexW.c = L.c := hc3.symm
  fsym [hP.wp_tick_unmetered, wp_xchgLockOn hP threadMutexW hS,
    wp_waitOn hP threadMutexW hS, atomicRmwC_eq, threadFutexWaitC_eq,
    L.part_set, L.ph_set, L.set_set, hP.ok_set, threadMutexW,
    lockInv, lockPost, Thread_Mutex_FutexImpl_lockSlow.again16]

/-- `lockSlow` by thread `t` at `spin`: it holds the mutex. -/
theorem lockSlow_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) (hc3 : L.c = 3) {p : Ptr}
    (hp : p = L.ptr) (t : ThreadId) (g : γ) (hok : ok g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered)
    (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t (L.set g .spin rnil)) m) :
    P.WP t (Thread_Mutex_FutexImpl_lockSlow p) (fun _ G' m' d' => d' < d ∧
      m'.current = t ∧ ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  subst hp
  have hS : threadMutexW.c = L.c := hc3.symm
  fsym [wp_loadLock hP, wp_waitOn hP threadMutexW hS, hP.toWait,
    WP.loop _ _ (lockInv P L t g d) (fun _ => 0) (lockPost P L t g d)
      (loop16_body hP hcost hc3 t g hok hu d),
    threadFutexWaitC_eq, L.ph_set, L.set_set, hP.ok_set,
    lockInv, lockPost]

/-- `FutexImpl.lock` by thread `t` at `out` (`g`): it holds the mutex. -/
theorem futexLock_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) (hc3 : L.c = 3) {p : Ptr}
    (hp : p = L.ptr) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered) (G : ThreadId → γ)
    (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_FutexImpl_lock p) (fun _ G' m' d' => d' < d ∧
      m'.current = t ∧ ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  fsym [tryLock_wp hP hcost hc3 hp t g hg hok,
    lockSlow_wp hP hcost hc3 hp t g hok hu]

/-- `Thread.Mutex.lock` is `FutexImpl.lock` (Linux). -/
theorem lock_eq (p : Ptr) : Thread_Mutex_lock p =
    (Thread_Mutex_FutexImpl_lock p >>= fun _ => pure ()) := by
  unfold Thread_Mutex_lock
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, pure_bind, callC, StateT.run_lift,
    bind_assoc, map_bind, map_pure]

/-- `lock` (Linux) by thread `t` at `out` (`g`): it holds the mutex, with a resource `rL`. -/
theorem lock_wp_unmetered (hP : L.Fits K P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hc : L.c = mutexC) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered) (_ : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_lock p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  fsym [futexLock_wp hP hcost hc hp t g hg hok hu]

/-- The actual Linux emitted loop pays each reachable tick from an unmetered caller part;
all remaining caller fragments, including stack resources, keep their exact values. -/
def lockResources : CallerResources where
  pre _ r := 0 < r.gh.ac.frag .unmetered
  during _ r r' := r' = r
  post _ r r' := r' = r
  plain_pre _ _ hp := hp.2
  plain_post _ _ _ _ hr := hr

theorem lock_wp_resource (hP : L.Fits K P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hc : L.c = mutexC) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g)
    (hu : lockResources.pre t (L.part g)) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_lock p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ r rL, lockResources.post t (L.part g) r ∧
        P.inv (upd G' t (L.set (L.setPart g r) .holds rL)) m') G m d := by
  refine WP.mono ?_ (lock_wp_unmetered hP hcost hp hc t g hg hok hu io G m d hi)
  rintro _ G' m' d' ⟨hd, hcur, rL, hi'⟩
  exact ⟨hd, hcur, L.part g, rL, rfl, by simpa only [L.setPart_self] using hi'⟩

/-- The existing Linux Plain rule is the exact-part unmetered specialization. -/
theorem lock_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hc : L.c = mutexC) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g)
    (hplain : (L.part g).Plain) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_lock p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d :=
  lock_wp_unmetered hP hcost hp hc t g hg hok hplain.2 io G m d hi

/-- `Thread.Mutex.unlock` is `FutexImpl.unlock` (Linux). -/
theorem unlock_eq (p : Ptr) : Thread_Mutex_unlock p =
    (Thread_Mutex_FutexImpl_unlock p >>= fun _ => pure ()) := by
  unfold Thread_Mutex_unlock
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, pure_bind, callC, StateT.run_lift,
    bind_assoc, map_bind, map_pure]

/-- `unlock` (Linux) by the holder `t` (`g`), the current thread: the owner check passes, and it
goes to `out`. -/
theorem unlock_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hc : L.c = mutexC) (t : ThreadId) (g : γ) (hg : L.ph g = .holds) (hok : ok g) (_ : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) (hcur : m.current = t) :
    P.WP t (Thread_Mutex_unlock p) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (L.set g .out rnil)) m') G m d := by
  subst hp
  have hS : threadMutexW.c = L.c := hc.symm
  obtain ⟨rX, hiL, -⟩ := (hP.inv _ _).mp hi
  have hrun := hiL.w.ownerCheck (t := t)
    (by show L.ph (upd G t g t) = _; rw [upd_self]; exact hg) hcur
  unfold Thread_Mutex_unlock Thread_Mutex_FutexImpl_unlock mutexOwnerCheck
  fsym [WP.liftMem_pure (x := Thread.mutexOwnerCheck L.ptr) hrun rfl,
    wp_xchgUnlockOn hP threadMutexW hS, wp_wakeOn hP,
    atomicRmwC_eq, threadFutexWakeC_eq, L.ph_set, L.set_set, hP.ok_set, threadMutexW]

end_if

if_decl Thread_Mutex_DarwinImpl in

/-- The loop invariant of `os_unfair_lock_lock`: thread `t` is at `out` (`g`, the first try) or at
`spin` (after a futex wait). -/
def lockInvD (P : Proto Tgt γ) (L : FLock γ) (t : ThreadId) (g : γ) (D : Nat)
    (_ : Thread_Mutex_lockLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d ≤ D ∧ ∃ g₀, (g₀ = g ∨ g₀ = L.set g .spin rnil) ∧ P.inv (upd G t g₀) m

/-- The loop ends when thread `t` holds the mutex. -/
def lockPostD (P : Proto Tgt γ) (L : FLock γ) (t : ThreadId) (g : γ) (D : Nat)
    (r : Bool × Thread_Mutex_lockLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  r.1 = false ∧ d < D ∧ m.current = t ∧ ∃ rL, P.inv (upd G t (L.set g .holds rL)) m

/-- One repeat of the loop: the `cmpxchg 0 → 1`; the thread holds the mutex, or it waits at the
futex (a stop, so the depth gets smaller). -/
theorem loopD_body (hP : L.Fits K P U ok) (hcost : P.cost = none) (hc1 : L.c = 1) (t : ThreadId)
    (g : γ) (hg : L.ph g = .out) (hok : ok g) (D : Nat) (s : Thread_Mutex_lockLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (h : lockInvD P L t g D s G m d) :
    P.WP t ((osUnfairLockTry L.ptr : CM Tgt Thread_Mutex_lockLocals Bool).run s) (fun r G' m' d' =>
      if id r.1 then lockInvD P L t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Thread_Mutex_lockLocals) => 0) s)
      else lockPostD P L t g D r G' m' d') G m d := by
  obtain ⟨hD, g₀, hg₀, hi⟩ := h
  have hset : ∀ q h, L.set g₀ q h = L.set g q h := by
    intro q h; rcases hg₀ with rfl | rfl
    · rfl
    · exact L.set_set _ _ _ _ _
  have hph : L.ph g₀ = .out ∨ L.ph g₀ = .spin := by
    rcases hg₀ with rfl | rfl
    · exact .inl hg
    · exact .inr (L.ph_set _ _ _)
  have hok₀ : ok g₀ := by
    rcases hg₀ with rfl | rfl
    · exact hok
    · exact (hP.ok_set _ _ _).mpr hok
  unfold osUnfairLockTry
  fsym [wp_casD hP hc1 (g := g₀), wp_waitD hP, hset,
    L.ph_set, L.set_set, hP.ok_set, lockInvD, lockPostD]

/-- The unticked native macOS lock preserves every actual caller-part assertion as a
spatial frame beside its returned protected resource. No mode/payment admission is needed. -/
theorem lock_wp_part (hP : L.Fits K P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hc : L.c = mutexC) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g)
    (A : FAssn) (hA : A (L.part g)) (_ : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_lock p) (fun _ G' m' d' => (d' < d ∧ m'.current = t) ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m' ∧
        (A ⋆ fun r => r = rL) (L.own (upd G' t (L.set g .holds rL)) m' t)) G m d := by
  subst hp
  have hc1 : L.c = 1 := hc
  refine hP.wp_preservePart (p := .holds) (A := A)
    (B := fun _ _ m' d' => d' < d ∧ m'.current = t) (by decide) hA ?_
  unfold Thread_Mutex_lock osUnfairLockC
  fsym [WP.loop _ _ (lockInvD P L t g d) (fun _ => 0) (lockPostD P L t g d)
    (loopD_body hP hcost hc1 t g hg hok d), lockInvD, lockPostD]

/-- This native wrapper performs no emitted tick and preserves the exact arbitrary caller
part. Its profile imposes no payment closure or unmetered guard. -/
def lockResources : CallerResources where
  pre _ _ := True
  during _ r r' := r' = r
  post _ r r' := r' = r
  plain_pre _ _ _ := True.intro
  plain_post _ _ _ _ hr := hr

theorem lock_wp_resource (hP : L.Fits K P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hc : L.c = mutexC) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g)
    (_hpre : lockResources.pre t (L.part g)) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_lock p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ r rL, lockResources.post t (L.part g) r ∧
        P.inv (upd G' t (L.set (L.setPart g r) .holds rL)) m') G m d := by
  refine WP.mono ?_ (lock_wp_part hP hcost hp hc t g hg hok (fun r => r = L.part g)
    rfl io G m d hi)
  rintro _ G' m' d' ⟨⟨hd, hcur⟩, rL, hi', _⟩
  exact ⟨hd, hcur, L.part g, rL, rfl, by simpa only [L.setPart_self] using hi'⟩

/-- The existing Plain macOS rule retains its real spatial caller-resource proof. -/
theorem lock_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hc : L.c = mutexC) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g)
    (hplain : (L.part g).Plain) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_lock p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d :=
  WP.mono (fun _ _ _ _ ⟨⟨hd, hcur⟩, rL, hi', _⟩ => ⟨hd, hcur, rL, hi'⟩)
    (lock_wp_part hP hcost hp hc t g hg hok (fun r => r = L.part g ∧ r.Plain)
      ⟨rfl, hplain⟩ io G m d hi)

/-- `unlock` (macOS) by the holder `t` (`g`), the current thread: it goes to `out`. -/
theorem unlock_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hc : L.c = mutexC) (t : ThreadId) (g : γ) (hg : L.ph g = .holds) (hok : ok g) (_ : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) (hcur : m.current = t) :
    P.WP t (Thread_Mutex_unlock p) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (L.set g .out rnil)) m') G m d := by
  subst hp
  have hc1 : L.c = 1 := hc
  obtain ⟨rX, hiL, -⟩ := (hP.inv _ _).mp hi
  have hrun := hiL.w.ownerCheck (t := t)
    (by show L.ph (upd G t g t) = _; rw [upd_self]; exact hg) hcur
  unfold Thread_Mutex_unlock osUnfairUnlockC
  fsym [WP.liftMem_pure (x := Thread.mutexOwnerCheck L.ptr) hrun rfl,
    wp_xchgRel hP hc1, wp_wakeOn hP, threadFutexWakeC_eq,
    L.ph_set, L.set_set, hP.ok_set]

end_if

end ThreadMutex

/-- **`Thread.Mutex` of this program is a mutex** (`MutexImpl`), on Linux and on macOS. -/
def threadMutex : MutexImpl Tgt where
  lock p _ := Thread_Mutex_lock p
  unlock p _ := Thread_Mutex_unlock p
  c := mutexC
  lock_resources := ThreadMutex.lockResources
  lock_wp_resource hP hcost := ThreadMutex.lock_wp_resource hP hcost
  unlock_wp hP hcost := ThreadMutex.unlock_wp hP hcost

end Threadsync
