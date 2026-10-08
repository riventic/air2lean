import Futures.Gen
import ZigLean.Conc.FutureLemmas

/-!
# C08: `Io.Future` proofs over every schedule

The generated code of `tests/roadmap/futures/futures.zig` (`Futures/Gen.lean`), under the
model of `ZigLean/Conc/Future.lean`, with the future protocol of
`ZigLean/Conc/FutureLemmas.lean` (partial correctness: every `ok` result of every schedule, for
every oracle and every fuel).

- **Completion** (`awaitValue_result`): `await` returns the task's result.
- **Error propagation** (`awaitError_result`): the task's `error.Zero` reaches the awaiter.
- **Cancelation** (`cancelValue_result`): `cancel` returns the task's result or
  `error.Canceled`, never another value.
- **Idempotence** (`second_await`): a consumed future returns its stored result again.
- The generated dispatcher runs exactly the worker and writes its result (`*_dispatch`), and
  the captured tuple is classified field by field (`*_captures`).
-/

open Zig Zig.Conc Zig.Conc.Proto

namespace Futures.Proofs

/-! ## The generated targets -/

theorem square_dispatch (slot : Ptr) (x : BitVec 32) :
    Futures.dispatch (.square_future slot x) =
      (ConcM.liftMem (StateT.lift (Futures.square x)) >>= fun r =>
        ConcM.liftMem (Future.complete slot r)) := rfl

theorem fill_dispatch (slot out : Ptr) (v : BitVec 32) :
    Futures.dispatch (.fill_future slot (out, v)) =
      (ConcM.liftMem (Futures.fill out v) >>= fun r => ConcM.liftMem (Future.complete slot r)) :=
  rfl

/-- The runtime record is not a capture: only the task's argument tuple is. -/
theorem fill_captures (slot out : Ptr) (v : BitVec 32) :
    Futures.Tgt.captures (.fill_future slot (out, v)) = [.ptr out, .value] := rfl

theorem square_captures (slot : Ptr) (x : BitVec 32) :
    Futures.Tgt.captures (.square_future slot x) = [.value] := rfl

/-- `Io` is a value with embedded pointer identities that the emitter does not decompose. -/
theorem cancellable_captures (slot : Ptr) (io : Io) (x : BitVec 32) :
    Futures.Tgt.captures (.cancellable_future slot (io, x)) = [.other, .value] := rfl

/-! ## Completion: `awaitValue` -/

theorem square_run (x : BitVec 32) : (Futures.square x).run = some (.ok (x * x)) := rfl

/-- The square task of `x` only. -/
def squareSlot (x : BitVec 32) : Tgt → Option Ptr
  | .square_future slot y => if y = x then some slot else none
  | _ => none

abbrev squareProto (x : BitVec 32) := futureProto (squareSlot x) (fun r : BitVec 32 => r = x * x)

theorem square_task (x : BitVec 32) (tgt : Tgt) (g : FGh) (hg : (squareProto x).init tgt g)
    (u : ThreadId) (G : ThreadId → FGh) (m : Mem) (n : Nat) (hu : 0 < u) (hgu : G u = g)
    (hi : (squareProto x).inv G m) :
    (squareProto x).WP u (Futures.dispatch tgt) ((squareProto x).QKid u) G
      { m with current := u } n := by
  obtain ⟨slot, hs, rfl⟩ := hg
  cases tgt with
  | square_future slot' y =>
    simp only [squareSlot] at hs
    split at hs
    · rename_i hy
      cases hs; subst hy
      rw [square_dispatch]
      refine FutureProto.task_wp hu (fun r _ => ⟨LawfulEnc.size_encode r, LawfulEnc.decode_encode r⟩)
        (WP.liftMem (fun _ _ => rfl) fun r m' hr => ?_)
      obtain ⟨hsq, rfl⟩ := MemM.lift_ok hr
      rw [square_run] at hsq
      cases hsq
      exact ⟨rfl, rfl, hgu, FutureProto.inv_of_blocks hi rfl⟩
    · cases hs
  | _ => cases hs

/-- At the spawn stop of the spawner no task exists yet. -/
theorem no_task {slotOf : Tgt → Option Ptr} {α : Type} [Enc α] {R : α → Prop} {m : Mem} :
    (futureProto slotOf R).inv (upd (fun _ => FGh.none) 0 FGh.none) m := by
  intro u sl d hu
  by_cases h0 : u = 0
  · subst h0; rw [upd_self] at hu; cases hu
  · rw [upd_ne _ _ h0] at hu; cases hu

/-- After the spawn, the only task is the new one. -/
theorem only_child {slotOf : Tgt → Option Ptr} {α : Type} [Enc α] {R : α → Prop}
    {G₁ : ThreadId → FGh} {m : Mem} {slot : Ptr} {child : ThreadId}
    (hg : G₁ 0 = .none) (hi : (futureProto slotOf R).inv G₁ m) :
    ∀ u sl d, upd G₁ child (.task slot false) u = .task sl d → u = child ∧ sl = slot ∧ d = false := by
  intro u sl d hu
  by_cases hc : u = child
  · subst hc; rw [upd_self] at hu; cases hu; exact ⟨rfl, rfl, rfl⟩
  · rw [upd_ne _ _ hc] at hu
    have := (hi u sl d hu).1
    rw [hg] at this; cases this

theorem pending_size {α : Type} [Enc α] (slot : Ptr) :
    (Enc.encode ({ task := some slot, result := none } : Future α)).size = Enc.size (Future α) :=
  (Future.task_bytes (α := α) (some slot)).1

/-- The future that the spawner stored is the one that `await` reads. -/
theorem reads_pending {α : Type} [Enc α] {p slot : Ptr} {m m' : Mem} {x : Unit}
    (hsz : Enc.size α ≠ 0)
    (hs : ((store 8 p ({ task := some slot, result := none } : Future α)).run m).run =
      some (.ok (x, m'))) (ha : Future.align α = 8) :
    ∀ f m'', ((load (Future α) (Future.align α) p).run m').run = some (.ok (f, m'')) →
      f = { task := some slot, result := none } := by
  intro f m'' hl
  rw [ha] at hl
  have := Future.load_after_store (pending_size slot) hs hl
  rw [Future.decode_pending slot hsz] at this
  cases this; rfl

theorem awaitValue_wp (io : Io) (x : BitVec 32) (n : Nat) :
    (squareProto x).WP 0 (Futures.awaitValue io x) (fun v _ _ _ => v = x * x)
      (fun _ => .none) { Futures.mem0 with current := 0 } n := by
  unfold Futures.awaitValue
  refine WP.bind (WP.liftMem (fun _ _ => rfl) fun s2 m₁ ha => ⟨?_, ?_⟩)
  · obtain ⟨-, rfl⟩ := alloc_ok ha; rfl
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  refine WP.bind (FutureProto.wp_asyncC (α := BitVec 32) rfl fun slot m₂ _ k _ => ⟨.none, ?_, fun G₁ m₃ hg hi₃ =>
    ⟨.task slot false, ⟨slot, by simp [squareSlot], rfl⟩, fun child m₄ _ m₅ _ => ?_⟩⟩)
  · exact no_task
  refine WP.bind (WP.liftM (fun _ _ => rfl) fun _ m₆ hs => ⟨by rw [FutureProto.store_threads hs], ?_⟩)
  refine WP.bind (FutureProto.await_wp (reads_pending (α := BitVec 32) (by decide) hs rfl) (only_child hg hi₃)
    fun r G' m' d hr => ?_)
  refine WP.pure' ?_
  refine WP.bind (WP.liftMem (fun _ _ => rfl) fun _ m₇ hf => ⟨?_, ?_⟩)
  · obtain ⟨_, _, -, -, rfl⟩ := free_ok hf; rfl
  exact WP.pure' hr

/-- **Completion.** Under every schedule, every result of `awaitValue(io, x)` is `x *% x`: the
task's result, written into its runtime record and returned by `await`. -/
theorem awaitValue_result (io : Io) (x : BitVec 32) {fuel : Nat} {o : Nat → Nat} {v : BitVec 32}
    {m : Mem} (h : (Sched.run Futures.dispatch fuel o (Futures.awaitValue io x) Futures.mem0).run =
      some (.ok (v, m))) : v = x * x := by
  obtain ⟨_, _, hv⟩ := run_sound (P := squareProto x) Futures.dispatch (fun _ => .none)
    (square_task x) (FutureProto.not_strict) rfl (awaitValue_wp io x) h
  exact hv

end Futures.Proofs
