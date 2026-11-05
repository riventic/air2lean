import Proofs.Sync.Mailbox.Start
import Proofs.Sync.IoSemaphore
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.AutoWP
import ZigLean.Sep.Full.Local

/-!
# A producer/consumer mailbox against the semaphore's contract (C14 client)

A model client written in Lean (it is not a Zig export, `Proofs/Sync/Mailbox/Code.lean`): a block
holds an `Io.Semaphore` with no permit (bytes 0..24: the permit count, its mutex and its
`Io.Condition`) and a two-field message `a` (24..28), `b` (28..32). `main` stores zeros, spawns a
producer and hands it the message cells. The producer writes `a = 3`, `b = 4` and `post`s; `main`
`wait`s, reads both fields, joins the producer and returns `10 * a + b`. The result is 34 under
every schedule (`mailbox_spec`) and no schedule gives an error (`mailbox_safe`): no data race on
the message, no deadlock (the consumer may sleep at the condition before the producer posts).

The proof is in the full-state concurrent separation logic (`docs/sep-threads.md`). The client's
code takes the semaphore as a `SemImpl` (`ZigLean/Sep/Full/Sem.lean`) and its proof uses only that
contract: `dispatch_spec` and `main_spec` hold for every implementation `I` and every value of its
mutex (`Cfg`). The results instantiate it with the translated std semaphore (`Sync.ioSem`,
`Proofs/Sync/IoSemaphore.lean`; `stdMain`, `stdDispatch`). A run that the kernel computes
(`mailbox_completes`) depends on the translation's loops and is with the 0.16.0 runs in
`tests/roadmap/sync-contracts/Runtime.lean`.

**Ownership transfer.** The message cells move: `main` → producer (at the spawn), producer → the
free permit (`post`: the pool holds `Msg 2` while the permit is available), free permit → `main`
(`wait`: the take moves the pool into its part). `main` reads the cells while the producer still
runs, with no further synchronization, because it owns them. The protocol, its steps and its start
are in `Proofs/Sync/Mailbox/{Protocol,Steps,Start}.lean`.

Scope: one producer, one consumer, one message; at most one thread waits at the condition.
No fairness or termination claim.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Sync

namespace Sync.Mailbox

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/Handoff.lean`).
attribute [local irreducible] Proto.WP

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 34 ∧ joinedAll 0 m

section Proofs

variable {K : Cfg}

/-- Only the producer (thread 1) is at a place of the producer. -/
theorem Shape.one {Y : ThreadId → X} {m : Mem} (h : Shape Y m) {u : ThreadId}
    (hp : (Y u).ph.isProd = true) : u = 1 := by
  obtain ⟨-, ⟨-, hy, hu⟩ | ⟨-, -, hm, -, -, -, hu⟩⟩ := h
  · refine Classical.byContradiction fun hne => ?_
    by_cases h0 : u = 0
    · subst h0; rw [hy] at hp; cases hp
    · rw [hu u (by simp only [ThreadId] at *; omega)] at hp; cases hp
  · refine Classical.byContradiction fun hne => ?_
    by_cases h0 : u = 0
    · subst h0
      rw [Ph.isMain_of_isProd hp] at hm; cases hm
    · rw [hu u (by simp only [ThreadId] at *; omega)] at hp; cases hp

/-- **The producer**: its code, then its end. -/
theorem dispatch_spec (I : SemImpl Tgt) (hLc : K.c = I.c) (tgt : Tgt) (g : Gh) (hg : (proto K).init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g)
    (hi : (proto K).inv G m) :
    (proto K).WP u (dispatch I tgt) ((proto K).QKid u) G { m with current := u } d := by
  cases tgt with
  | semWork p =>
    obtain ⟨rfl, rp, rc, hp, hrc, hdj, rfl⟩ := hg
    have hu1 : u = 1 := by
      obtain ⟨rX, -, hU⟩ := id hi
      exact hU.shape.one (u := u) (by show (G u).2.ph.isProd = true; rw [hgu]; rfl)
    subst hu1
    refine WP.mono ?_ (producer_spec I hLc G _ d (Res.plain_of hp) hrc hdj
      (by rw [show gO (rsum rp rc) { ph := .pr 0 } = G 1 from hgu.symm, upd_same]
          exact inv_cur 1 hi (by rw [hgu]; nofun)) rfl)
    rintro _ G' m' _ ⟨-, hi'⟩
    exact qkid hi'
  | producer p => exact absurd hg (by simp [proto])
  | work p => exact absurd hg (by simp [proto])
  | writer p => exact absurd hg (by simp [proto])

/-- **`main`**: the mailbox's block and its stores, the protocol's start (`inv_of_box`), the spawn
(`inv_spawn`), the wait (`wp_waitM`), the loads of the message from its part, the join of the
producer and the free of the block. -/
theorem main_spec (I : SemImpl Tgt) (hLc : K.c = I.c) (σ : Placement) (io : Io) (d : Nat) :
    (proto K).WP 0 (mailMain I io) QM G0 { mem0 σ with current := 0 } d := by
  have := FOwned.start0_facts (σ := σ) (m := mem0 σ) rfl
  unfold mailMain
  fsym [inv_of_box (K := K), inv_spawn (K := K), wp_waitM I hLc io,
    wp_loadA (K := K), wp_loadB (K := K), inv_joins (K := K),
    wp_join (K := K), wp_free (K := K), joinedAll_of_threads, empty_disj]

end Proofs

/-! ## The results, for the translated `Io.Semaphore` -/

/-- The mailbox client with the translated std semaphore. -/
abbrev stdMain := mailMain ioSem

/-- The spawn targets with the translated std semaphore. -/
abbrev stdDispatch := dispatch ioSem

/-- The std semaphore's mutex value. -/
def stdK : Cfg := ⟨ioSem.c, .inr (.inl rfl)⟩

/-- **The consumer receives the whole message under every schedule**: every completed run of
the mailbox client returns 34 (every oracle, every fuel; the spawn does not fail). -/
theorem mailbox_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (io : Io) (h : (Sched.run env stdDispatch fuel o (stdMain io) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 34 := by
  obtain ⟨_, _, hv, -⟩ := (proto stdK).run_sound env (Proto.of_available henv) stdDispatch G0
    (dispatch_spec ioSem rfl) (fun _ _ _ _ _ hq => hq.2) rfl (main_spec ioSem rfl σ io) h
  exact hv

/-- **No run of the mailbox client gives an error**: no data race on the message, no deadlock
(also when the consumer sleeps at the condition first), no lifetime error at the free. -/
theorem mailbox_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    e ≠ .stackOverflow → (Sched.run env stdDispatch fuel o (stdMain io) (mem0 σ)).run ≠ some (.error e) :=
  (proto stdK).run_safe env (Proto.of_available henv) stdDispatch G0 rfl (dispatch_spec ioSem rfl)
    (fun _ _ _ _ hq => hq.2) rfl (main_spec ioSem rfl σ io)

end Sync.Mailbox
