import Proofs.MutexCounter.Protocol
import Proofs.Threadsync.ThreadMutex
import ZigLean.Sep.Full.AutoWP
import ZigLean.Conc.Unroll
import ZigLean.Witness

/-!
# `threadsync.mutexCounter` over all schedules

`mutexCounter` spawns one thread; each of the two threads adds 1 two times to a counter, under
a `Thread.Mutex` (translated from Zig 0.15.2's std code: `FutexImpl` on Linux, `os_unfair_lock`
on macOS; the futex under it is the model). The result is 4 under every schedule
(`mutexCounter_spec`), and no schedule gives an error (`mutexCounter_safe`): no data race on the
counter, and no deadlock at the futex.

The proof is in the full-state concurrent separation logic (`docs/sep-threads.md`) and uses only
the mutex contract (`MutexImpl`): this program's `Thread.Mutex` is `Threadsync.threadMutex`. The
protocol and its steps are once for every version (`Proofs/MutexCounter/Protocol.lean`, as for
`Proofs/Sync/Mutex.lean`); this file gives the `Counter`'s layout (`lo`: no `io`, the mutex at 0,
the counter at 4) and walks `work` (by `fsym`, with the protocol's steps and the mutex contract as
rules) and `main`, which stores the whole `Counter` and reads it back after its join.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Zig.MutexCounter Threadsync

namespace Threadsync.MutexCounter

/- The rules (`WP.bind`, `lock_wp`, …) need `WP` only as a name: unfolding it runs the program. -/
attribute [local irreducible] Proto.WP
-- The mutex's code is a stop for the walk of `work` (its rules are the contract's): unification
-- must not unfold `lock` into `unlock`.
attribute [local irreducible] Thread_Mutex_lock Thread_Mutex_unlock

/-- The `Counter`'s layout (module doc). -/
def lo : Layout where
  size := 8
  align := 4
  io := 0
  mo := 0
  c := mutexC
  c_ok := by unfold mutexC; decide
  ok := by decide

/-- The kid's argument. -/
def workOf : Tgt → Option Ptr
  | .work p => some p
  | _ => none

/-- This program's protocol. -/
abbrev P : Proto Tgt Gh := proto lo workOf

/-! ## `work` -/

/-- `work`'s loop invariant: thread `t` did `local1` increments and is out of the lock's code. -/
def workInv (t : ThreadId) (s : workLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  m.current = t ∧ ∃ k, P.inv (upd G t (gOut k)) m ∧ s.local1.toNat = k ∧ k ≤ 2

/-- `work`'s loop ends after 2 increments. -/
def workPost (t : ThreadId) (r : workExit × workLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) :
    Prop :=
  r.1 = .br3 ∧ m.current = t ∧ ∃ k, P.inv (upd G t (gOut k)) m ∧ k = 2

/-- One run of `work`'s loop: `lock`, the increment of the counter, `unlock`. Walked by `fsym` in
its `WP` mode, with the protocol's steps and the rules of `threadMutex` (`ThreadMutex.lock_wp`,
`unlock_wp`: the contract's rules stated on the program's `Thread_Mutex_lock`/`unlock`). -/
theorem loop4_body (t : ThreadId) (s : workLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (h : workInv t s G m d) :
    P.WP t ((work.loop4 cPtr).run s) (fun r G' m' d' =>
      if work.again4 r.1 then workInv t r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : workLocals) => 0) s)
      else workPost t r G' m' d') G m d := by
  obtain ⟨hc, k, hi, hk, hle⟩ := h
  unfold work.loop4
  fsym [WP.liftMem_pure (projI (Lo := lo) (workOf := workOf) _ _) rfl,
    ThreadMutex.lock_wp (fits (Lo := lo) (workOf := workOf)) rfl rfl rfl _ _ _ _ ⟨⟩,
    ThreadMutex.unlock_wp (fits (Lo := lo) (workOf := workOf)) rfl rfl rfl _ _ _ _ ⟨⟩,
    wp_load (Lo := lo) (workOf := workOf), wp_store (Lo := lo) (workOf := workOf),
    set_out, set_hold, ph_out, ph_hold, work.again4]

/-- `work`: two runs of its loop. -/
theorem work_spec (t : ThreadId) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t (gOut 0)) m) (hc : m.current = t) :
    P.WP t (work cPtr) (fun _ G' m' _ => m'.current = t ∧ P.inv (upd G' t (gOut 2)) m') G m d := by
  unfold work
  fsym [WP.loop _ _ (workInv t) (fun _ => 0) (workPost t) (loop4_body t)]

/-- The kid: `work` on the `Counter`, then its end. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : P.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : P.inv G m) :
    P.WP u (dispatch tgt) (P.QKid u) G { m with current := u } d := by
  cases tgt with
  | work p =>
    obtain ⟨hp, rfl⟩ := hg
    obtain rfl : p = cPtr := Option.some.inj hp
    have hu1 : u = 1 := by
      obtain ⟨rX, -, hU⟩ := id hi
      have := (shape_work hU.shape (t := u) (k := 0) (by show (G u).2 = _; rw [hgu])).1
      unfold ThreadId at *; omega
    subst hu1
    show P.WP 1 ((fun _ => ()) <$> work cPtr) _ G _ d
    refine WP.map (WP.mono ?_ (work_spec 1 G _ d
      (by rw [show gOut 0 = G 1 from hgu.symm, upd_same]
          exact inv_cur 1 hi (by rw [hgu]; nofun)) rfl))
    rintro _ G' m' _ ⟨-, hi'⟩
    exact qkid hi'
  | producer p => exact absurd hg.1 (by simp [workOf])
  | task p => exact absurd hg.1 (by simp [workOf])

/-! ## `main` -/

/-- The initial `Counter`. -/
def counter0 : Counter :=
  { m := mutexOf 0, n := 0 }

/-- The bytes of the `Counter` at the end: the word `w` and the counter `4`. -/
theorem cnt_decode {bs : Array Byte} {w : BitVec 32} (_hs : bs.size = 8)
    (hw : (intOfBytes 32 (bs.extract 0 4)).run = some (.ok w))
    (hn' : (intOfBytes 32 (bs.extract 4 8)).run = some (.ok (BitVec.ofNat 32 4))) :
    Enc.decode (α := Counter) (bs.extract 0 (0 + Enc.size Counter)) =
      pure { m := mutexOf w, n := BitVec.ofNat 32 4 } := by
  have hw2 : intOfBytes 32 (bs.extract 0 4) = pure w := ExceptT.ext (by rw [hw]; rfl)
  have hn2 : intOfBytes 32 (bs.extract 4 8) = pure (BitVec.ofNat 32 4) :=
    ExceptT.ext (by rw [hn']; rfl)
  have h4 : alignUp ((32 + 7) / 8) (intAlign 32) = 4 := by decide
  simp only [Enc.decode, Enc.decodeAt, Enc.size, intSize, Array.extract_extract, Nat.zero_add,
    Nat.add_zero, Nat.min_def, h4, Nat.le_refl, ↓reduceIte, show (4 : Nat) ≤ 8 by decide,
    show (4 + 4 : Nat) ≤ 8 by decide, show (4 + 4 : Nat) = 8 by rfl, hw2, hn2, pure_bind]

/-- **`main`'s load of the whole `Counter`** after its join: the counter is 4; no race, `main`
owns both words (`main_counter`). -/
theorem wp_counter {σ : Type} {s : σ} {G : ThreadId → Gh} {m : Mem} {n : Nat}
    {own : ThreadId → Res} {rX r : Res} {w : Nat} (ho : FOwned (upd own 0 r) rX m)
    (hc : m.current = 0) (ht : 0 < m.threads.size)
    (hp : ((fun r => r = own 0) ⋆ (up (pts (cPtr.add (lo.mo + 4)) 4 (BitVec.ofNat 32 4)) ⋆
      fun r => r = (L lo).wordR m)) r) (hb : BlkOk lo m) (hcl : m.ClocksLe)
    (hw : (L lo).U32 m (BitVec.ofNat 32 w))
    {Q : Counter × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ c m', c.n = BitVec.ofNat 32 4 → BlkOk lo m' → m'.ClocksLe →
      m'.threads = m.threads → Q (c, s) G m' n) :
    P.WP 0 ((liftM (load Counter 4 cPtr) : CM Tgt σ Counter).run s) Q G m n := by
  obtain ⟨blk, hblk, hl, hsz, hk, hA, hw4, hn4, hnr⟩ := main_counter ho hc ht hp hb hw
  have hacc : m.access cPtr (Enc.size Counter) 4 = pure (0, blk, 0) :=
    access_of (p := cPtr) rfl hblk hl (by decide) (by rw [hsz]; decide)
      (by simpa [cPtr] using hA) (by rw [hk]; simp [BlockKind.mappedLo, cPtr])
  have hn4' : Enc.decode (α := BitVec 32) (blk.bytes.extract 4 8) = pure (BitVec.ofNat 32 4) := hn4
  have hd := cnt_decode (bs := blk.bytes) (by rw [hsz]; rfl) hw4 (by
    show (Enc.decode (α := BitVec 32) _).run = _; rw [hn4']; rfl)
  have hrun : (load Counter 4 cPtr).run m =
      pure ({ m := mutexOf (BitVec.ofNat 32 w), n := BitVec.ofNat 32 4 },
        m.recordAt 0 0 (Enc.size Counter) .read) :=
    load_run hacc hd (by rw [hk]; decide) (hnr .read)
  refine WP.liftM (fun e he => (MemM.noErr_of_run hrun e he).elim) fun v m' hr => ?_
  rw [hrun] at hr
  simp only [pure, ExceptT.pure, ExceptT.mk, ExceptT.run, Option.some.injEq, Except.ok.injEq,
    Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨rfl, h _ _ rfl ⟨blk, hblk, hl, hsz, hk⟩ (hcl.recordAt _ _ _ _) rfl⟩

theorem main_spec (σ : Placement) (d : Nat) :
    P.WP 0 mutexCounter QM G0 { mem0 σ with current := 0 } d := by
  unfold mutexCounter
  have ht0 : ({ mem0 σ with current := 0 } : Mem).threads = #[{ spawner := 0, joined := true }] :=
    rfl
  -- the `Counter`: block 0, a stack block; `main` gives up the plain mode
  refine WP.bind (WP.liftMem_fownedS (FTTriple.allocStackDrop 8 4 (by decide) (by decide))
    (FOwned.start0_plain σ) rfl (by rw [ht0]; decide) (by rw [plainOwn_zero]; exact plain_intro)
    fun s0 m₁ r₁ _ hr₁ ho₁ hq₁ hs₁ => ?_)
  simp only [plainOwn, upd_upd] at ho₁
  obtain ⟨rfl, hm₁e⟩ := alloc_ok hr₁
  obtain ⟨A, b, hq₁⟩ := hq₁
  obtain ⟨⟨hpb, -, hA4⟩, F₁⟩ := Full.sep_lift.mp hq₁
  obtain rfl : b = 0 := by cases hpb; rfl
  rw [show (⟨some ({ mem0 σ with current := 0 } : Mem).blocks.size, 0⟩ : Ptr) = cPtr from rfl]
    at F₁ ⊢
  have hc₁ : m₁.current = 0 := hs₁.current
  have ht₁ : m₁.threads = #[{ spawner := 0, joined := true }] := hs₁.threads.trans ht0
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  -- the `Counter`: the mutex and the counter
  refine WP.bind (WP.callMC_fownedS (FTTriple.storeAt' (p := cPtr) (A := A) (S := 8)
    (K := .stack) (k := 0) (a := 4) counter0 (by decide +kernel) rfl rfl (by decide)
    (by decide +kernel) (by simp [cPtr]; omega) (by decide)) ho₁ hc₁ (by rw [ht₁]; decide)
    F₁ fun _ m₂ r₂ _ hr₂ ho₂ F₂ hs₂ => ?_)
  rw [upd_upd] at ho₂
  have hc₂ : m₂.current = 0 := hs₂.current.trans hc₁
  have ht₂ : m₂.threads = #[{ spawner := 0, joined := true }] := hs₂.threads.trans ht₁
  have hat₂ : m₂.atomics = #[] := by rw [store_atomics hr₂, hm₁e]; rfl
  have hq₂ : m₂.waiters = #[] := by rw [hs₂.waiters, hs₁.waiters]; rfl
  have hi₀ := inv_start (Lo := lo) (workOf := workOf) ho₂ F₂ (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (fun h => absurd h (by decide)) hA4 ht₂ hat₂ hq₂
  -- the spawn
  refine WP.bind (WP.spawnC fun k _ => ⟨gPre, hi₀, fun G₁ m₅ hg₁ hi₅ =>
    ⟨gOut 0, ⟨rfl, rfl⟩, fun child m₆ hf => ?_⟩⟩)
  obtain ⟨rfl, hc₆, hi₆⟩ := inv_spawn hi₅ hg₁ hf
  dsimp only
  simp only [StateT.run_bind]
  -- `work`
  refine WP.bind (WP.callC (WP.mono ?_ (work_spec 0 _ _ k hi₆ hc₆)))
  rintro _ G₂ m₇ d₂ ⟨hc₇, hi₇⟩
  -- the join of the kid; `main` takes the `Counter` back
  refine WP.bind (wp_join (inv_end hi₇ (.inl ⟨rfl, rfl⟩))
    fun k₂ G₃ m₈ own rX r hk₂ hc₈ ho hp hb₈ hcl₈ hja hs₈ ⟨w, hw⟩ => ?_)
  -- the `Counter`: its counter is 4
  refine WP.bind (wp_counter ho hc₈ (by rw [hs₈]; decide) hp hb₈ hcl₈ hw
    fun c m₉ hn hb₉ hcl₉ hth₉ => ?_)
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  -- the free of the `Counter`
  refine WP.bind (wp_free hb₉ hcl₉ fun m₁₀ hth => ?_)
  exact WP.pure' ⟨by rw [hn]; rfl, fun r hr hsp => hja r (by rw [← hth₉, ← hth]; exact hr) hsp⟩

/-! ## The results -/

/-- **`threadsync.mutexCounter` gives 4 under every schedule** (every oracle `o`, every `fuel`). -/
theorem mutexCounter_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run env dispatch fuel o mutexCounter (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 4 := by
  obtain ⟨_, _, hv, -⟩ := P.run_sound env (Proto.of_available henv) dispatch G0 dispatch_spec
    (fun _ _ _ _ _ hq => hq.2) rfl (main_spec σ) h
  exact hv

/-- **No run of `threadsync.mutexCounter` gives an error**: no data race on the counter, no deadlock
at the futex, no panic, under every schedule. -/
theorem mutexCounter_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} :
    e ≠ .stackOverflow → (Sched.run env dispatch fuel o mutexCounter (mem0 σ)).run ≠ some (.error e) :=
  P.run_safe env (Proto.of_available henv) dispatch G0 rfl dispatch_spec (fun _ _ _ _ hq => hq.2) rfl (main_spec σ)

/-- One schedule completes: under the oracle that always picks option 0, the `std.Thread.Mutex` counter returns 4 within
fuel 1000, from `mem0` with the translation's spawn policy. The kernel computes the run, with
each loop cut after 10 iterations (`unroll_sched`, `ZigLean/Conc/Unroll.lean`). -/
theorem mutexCounter_completes :
    ∃ σ, Witness.okVal (Sched.run ⟨.any, .available⟩ dispatch 1000 (fun _ => 0) mutexCounter (mem0 σ)) = some 4 :=
  ⟨.fresh, by unroll_sched 10⟩

nonvacuity_witness cnt_decode :=
  ⟨Enc.encode (0 : BitVec 32) ++ Enc.encode (4 : BitVec 32), 0, by decide +kernel,
    by with_unfolding_all rfl, by with_unfolding_all rfl, trivial⟩

end Threadsync.MutexCounter
