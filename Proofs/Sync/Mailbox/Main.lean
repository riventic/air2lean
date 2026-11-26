import Proofs.Sync.Mailbox.Start
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.AutoWP
import ZigLean.Sep.Full.Local

/-!
# The mailbox's two threads against the protocol

The walks of the mailbox's code (`Proofs/Sync/Mailbox/Code.lean`) against its protocol
(`Proofs/Sync/Mailbox/{Protocol,Steps,Start}.lean`), once for every translation of the Sync
profile and every semaphore implementation:

- **The producer** (`dispatch_spec`): a spawn target that the protocol admits (`proto.init`) is
  the producer's on the mailbox, so `dispatch` runs `producer` (`producer_spec`), then its end
  (`qkid`).
- **`main`** (`main_spec`), from the start memory `m₀` of a translation with no globals (its
  `mem0 σ`, `hm₀`).
- **The results** (`run_spec`, `run_safe`): every completed run returns 34, and no run gives an
  error, from the protocol's soundness (`Proto.run_sound`, `Proto.run_safe`).

The parameters: the spawn targets `Tgt` with the producer's target `sw` and its reader `swOf`
(`hsw`), the semaphore type `Sm` with its value `z` with no permit (`hz`: its bytes are
`semBytes`), the semaphore implementation `I : SemImpl Tgt` and the value of its mutex (`K`,
`hLc`). `Proofs/Sync/Mailbox.lean` and `Proofs/Sync/MailboxCases.lean` instantiate them.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

namespace Sync.Mailbox

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/Handoff.lean`).
attribute [local irreducible] Proto.WP

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 34 ∧ joinedAll 0 m

variable {K : Cfg} {Tgt : Type} {swOf : Tgt → Option Ptr}

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
theorem dispatch_spec (I : SemImpl Tgt) (hLc : K.c = I.c) (tgt : Tgt) (g : Gh)
    (hg : (proto K swOf).init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g)
    (hi : (proto K swOf).inv G m) :
    (proto K swOf).WP u (dispatch swOf I tgt) ((proto K swOf).QKid u) G
      { m with current := u } d := by
  obtain ⟨htgt, rp, rc, hp, hrc, hdj, rfl⟩ := hg
  have hu1 : u = 1 := by
    obtain ⟨rX, -, hU⟩ := id hi
    exact hU.shape.one (u := u) (by show (G u).2.ph.isProd = true; rw [hgu]; rfl)
  subst hu1
  have hd : dispatch swOf I tgt = producer I cPtr := by unfold dispatch; rw [htgt]
  rw [hd]
  refine WP.mono ?_ (producer_spec I hLc G _ d (Res.plain_of hp) hrc hdj
    (by rw [show gO (rsum rp rc) { ph := .pr 0 } = G 1 from hgu.symm, upd_same]
        exact inv_cur 1 hi (by rw [hgu]; nofun)) rfl)
  rintro _ G' m' _ ⟨-, hi'⟩
  exact qkid hi'

/-- **`main`**: the mailbox's block and its stores, the protocol's start (`inv_of_box`), the spawn
(`inv_spawn`), the wait (`wp_waitM`), the loads of the message from its part, the join of the
producer and the free of the block. -/
theorem main_spec (sw : Ptr → Tgt) (hsw : ∀ p, swOf (sw p) = some p) {Sm : Type} [Enc Sm]
    (z : Sm) (hz : Enc.encode z = semBytes) (I : SemImpl Tgt) (hLc : K.c = I.c) {σ : Placement}
    {m₀ : Mem} (hm₀ : m₀ = Mem.ofGlobals σ []) (io : Io) (d : Nat) :
    (proto K swOf).WP 0 (mailMain sw z I io) QM G0 { m₀ with current := 0 } d := by
  obtain ⟨ho, hpl, hth, hat, hq, hb⟩ := FOwned.start0_facts hm₀
  clear hm₀
  have hzs : (Enc.encode z).size = 24 := by rw [hz]; decide +kernel
  unfold mailMain
  fsym [inv_of_box (K := K) (swOf := swOf), inv_spawn (K := K) (swOf := swOf), wp_waitM I hLc io,
    wp_loadA (K := K) (swOf := swOf), wp_loadB (K := K) (swOf := swOf),
    inv_joins (K := K) (swOf := swOf), wp_join (K := K) (swOf := swOf),
    wp_free (K := K) (swOf := swOf), joinedAll_of_threads, empty_disj, hsw, hz, semBytes, hb]

/-! ## The results, for every translation and every semaphore implementation -/

section Results

variable (sw : Ptr → Tgt) (hsw : ∀ p, swOf (sw p) = some p) {Sm : Type} [Enc Sm] (z : Sm)
  (hz : Enc.encode z = semBytes) (I : SemImpl Tgt) (K : Cfg) (hLc : K.c = I.c) (env : Env)
  (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} (io : Io)

include hsw hz hLc henv

/-- **The consumer receives the whole message under every schedule**: every completed run of
the mailbox client returns 34 (every oracle, every fuel; the spawn does not fail). -/
theorem run_spec {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run env (dispatch swOf I) fuel o (mailMain sw z I io) (Mem.ofGlobals σ [])).run =
      some (.ok (v, m))) : v = .ok 34 := by
  obtain ⟨_, _, hv, -⟩ := (proto K swOf).run_sound env (Proto.of_available henv) (dispatch swOf I)
    G0 (dispatch_spec I hLc) (fun _ _ _ _ _ hq => hq.2) rfl (main_spec sw hsw z hz I hLc rfl io) h
  exact hv

/-- **No run of the mailbox client gives an error**: no data race on the message, no deadlock
(also when the consumer sleeps at the condition first), no lifetime error at the free. -/
theorem run_safe {e : Error} : e ≠ .stackOverflow →
    (Sched.run env (dispatch swOf I) fuel o (mailMain sw z I io) (Mem.ofGlobals σ [])).run ≠
      some (.error e) :=
  (proto K swOf).run_safe env (Proto.of_available henv) (dispatch swOf I) G0 rfl
    (dispatch_spec I hLc) (fun _ _ _ _ hq => hq.2) rfl (main_spec sw hsw z hz I hLc rfl io)

end Results

end Sync.Mailbox
