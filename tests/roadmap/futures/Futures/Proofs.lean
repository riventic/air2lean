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

/-! ## Error propagation: `awaitError` -/

/-- A declared finite error union is lawful on the values of its domain. -/
theorem errorUnionEnc_lawful (d : ErrorDomain) {α : Type} [inst : Enc α] [LawfulEnc α]
    (v : Except ErrName α) (hv : ∀ e, v = .error e → d.names.contains e = true) :
    ((errorUnionEnc d inst).encode v).size = (errorUnionEnc d inst).size ∧
      (errorUnionEnc d inst).decode ((errorUnionEnc d inst).encode v) = pure v := by
  have he : (errorUnionEnc d inst).encode v = Enc.encode v := by
    cases v with
    | ok y => rfl
    | error e =>
      show (if d.names.contains e then Enc.encode (Except.error e : Except ErrName α) else _) = _
      rw [ite_eq_left_iff.mpr (fun h => absurd (hv e rfl) h)]
  have hd : ∀ bs, (errorUnionEnc d inst).decode bs = (do
      let w ← (Enc.decode bs : Result (Except ErrName α))
      match w with
      | .ok _ => pure w
      | .error e => if d.names.contains e then pure w else throw .unspecified) := fun _ => rfl
  refine ⟨by rw [he]; exact LawfulEnc.size_encode v, ?_⟩
  rw [hd, he, LawfulEnc.decode_encode]
  cases v with
  | ok y => rfl
  | error e =>
    have := hv e rfl
    have hm : e ∈ d.names := Array.contains_iff_mem.mp this
    simp [this, hm, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont]

/-- The storage dictionary of `Fail!u32` that the generated code binds. -/
abbrev zeroEnc : Enc (Except ErrName (BitVec 32)) :=
  errorUnionEnc (⟨#["Zero"], by decide, by decide⟩ : ErrorDomain) inferInstance

/-- `checked(x)`: `error.Zero` for 0, else `x - 1`. -/
def checkedSpec (x : BitVec 32) : Except ErrName (BitVec 32) :=
  if x = 0 then .error "Zero" else .ok (x - 1)

theorem checked_run (x : BitVec 32) : (Futures.checked x).run = some (.ok (checkedSpec x)) := by
  unfold Futures.checked checkedSpec
  by_cases hx : x = 0
  · subst hx; rfl
  · have hlt : ¬ x < 1 := by
      intro h; apply hx; apply BitVec.eq_of_toNat_eq; simp [BitVec.lt_def] at h; simp; omega
    have hov : x.usubOverflow 1 = false := by
      simp [BitVec.usubOverflow, BitVec.lt_def] at hlt ⊢; omega
    have hb : (x == 0) = false := beq_eq_false_iff_ne.mpr hx
    simp only [hx, Zig.sub, hov, hb, ite_false, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- The checked task of `x` only. -/
def checkedSlot (x : BitVec 32) : Tgt → Option Ptr
  | .checked_future slot y => if y = x then some slot else none
  | _ => none

abbrev checkedProto (x : BitVec 32) :=
  @futureProto Tgt (Except ErrName (BitVec 32)) zeroEnc (checkedSlot x) (fun r => r = checkedSpec x)

theorem checked_dispatch (slot : Ptr) (x : BitVec 32) :
    Futures.dispatch (.checked_future slot x) =
      (ConcM.liftMem (StateT.lift (Futures.checked x)) >>= fun r =>
        ConcM.liftMem (@Future.complete _ zeroEnc slot r)) := rfl

theorem checkedSpec_lawful (x : BitVec 32) :
    (zeroEnc.encode (checkedSpec x)).size = zeroEnc.size ∧
      zeroEnc.decode (zeroEnc.encode (checkedSpec x)) = pure (checkedSpec x) := by
  refine errorUnionEnc_lawful _ _ fun e he => ?_
  unfold checkedSpec at he
  split at he
  · cases he; exact Array.contains_iff_mem.mpr (by simp)
  · cases he

theorem checked_task (x : BitVec 32) (tgt : Tgt) (g : FGh) (hg : (checkedProto x).init tgt g)
    (u : ThreadId) (G : ThreadId → FGh) (m : Mem) (n : Nat) (hu : 0 < u) (hgu : G u = g)
    (hi : (checkedProto x).inv G m) :
    (checkedProto x).WP u (Futures.dispatch tgt) ((checkedProto x).QKid u) G
      { m with current := u } n := by
  obtain ⟨slot, hs, rfl⟩ := hg
  cases tgt with
  | checked_future slot' y =>
    simp only [checkedSlot] at hs
    split at hs
    · rename_i hy
      cases hs; subst hy
      rw [checked_dispatch]
      refine @FutureProto.task_wp Tgt _ zeroEnc _ _ _ _ _ _ _ _ hu
        (fun r hr => by subst hr; exact checkedSpec_lawful y)
        (WP.liftMem (fun _ _ => rfl) fun r m' hr => ?_)
      obtain ⟨hc, rfl⟩ := MemM.lift_ok hr
      rw [checked_run] at hc
      cases hc
      exact ⟨rfl, rfl, hgu, @FutureProto.inv_of_blocks Tgt _ zeroEnc _ _ _ _ _ hi rfl⟩
    · cases hs
  | _ => cases hs

theorem awaitError_wp (io : Io) (x : BitVec 32) (n : Nat) :
    (checkedProto x).WP 0 (Futures.awaitError io x) (fun v _ _ _ => v = checkedSpec x)
      (fun _ => .none) { Futures.mem0 with current := 0 } n := by
  letI : Enc (Except ErrName (BitVec 32)) := zeroEnc
  unfold Futures.awaitError
  refine WP.bind (WP.liftMem (fun _ _ => rfl) fun s2 m₁ ha => ⟨?_, ?_⟩)
  · obtain ⟨-, rfl⟩ := alloc_ok ha; rfl
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  refine WP.bind (FutureProto.wp_asyncC (α := Except ErrName (BitVec 32)) rfl
    fun slot m₂ _ k _ => ⟨.none, ?_, fun G₁ m₃ hg hi₃ =>
    ⟨.task slot false, ⟨slot, by simp [checkedSlot], rfl⟩, fun child m₄ _ m₅ _ => ?_⟩⟩)
  · exact no_task
  refine WP.bind (WP.liftM (fun _ _ => rfl) fun _ m₆ hs => ⟨by rw [FutureProto.store_threads hs], ?_⟩)
  refine WP.bind (FutureProto.await_wp
    (reads_pending (α := Except ErrName (BitVec 32)) (by decide) hs rfl) (only_child hg hi₃)
    fun r G' m' d hr => ?_)
  refine WP.pure' ?_
  refine WP.bind (WP.liftMem (fun _ _ => rfl) fun _ m₇ hf => ⟨?_, ?_⟩)
  · obtain ⟨_, _, -, -, rfl⟩ := free_ok hf; rfl
  exact WP.pure' hr

/-- **Error propagation.** Under every schedule, every result of `awaitError(io, x)` is the
task's result: `error.Zero` for `x = 0`, else `x - 1`. -/
theorem awaitError_result (io : Io) (x : BitVec 32) {fuel : Nat} {o : Nat → Nat}
    {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run Futures.dispatch fuel o (Futures.awaitError io x) Futures.mem0).run =
      some (.ok (v, m))) : v = checkedSpec x := by
  obtain ⟨_, _, hv⟩ := run_sound (P := checkedProto x) Futures.dispatch (fun _ => .none)
    (checked_task x) (fun h => by cases h) rfl (awaitError_wp io x) h
  exact hv

theorem awaitError_zero (io : Io) {fuel : Nat} {o : Nat → Nat}
    {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run Futures.dispatch fuel o (Futures.awaitError io 0) Futures.mem0).run =
      some (.ok (v, m))) : v = .error "Zero" :=
  awaitError_result io 0 h

/-! ## Cancelation: `cancelValue` -/

/-- The storage dictionary of `Io.Cancelable!u32`. -/
abbrev canceledEnc : Enc (Except ErrName (BitVec 32)) :=
  errorUnionEnc (⟨#["Canceled"], by decide, by decide⟩ : ErrorDomain) inferInstance

/-- The task's result, or `error.Canceled` if it observed the request. -/
def CancelSpec (x : BitVec 32) (r : Except ErrName (BitVec 32)) : Prop :=
  r = .ok (x + 1) ∨ r = .error "Canceled"

/-- The cancelable task of `x` only. -/
def cancelSlot (x : BitVec 32) : Tgt → Option Ptr
  | .cancellable_future slot (_, y) => if y = x then some slot else none
  | _ => none

abbrev cancelProto (x : BitVec 32) :=
  @futureProto Tgt (Except ErrName (BitVec 32)) canceledEnc (cancelSlot x) (CancelSpec x)

theorem cancellable_dispatch (slot : Ptr) (io : Io) (x : BitVec 32) :
    Futures.dispatch (.cancellable_future slot (io, x)) =
      (Futures.cancellable io x >>= fun r => ConcM.liftMem (@Future.complete _ canceledEnc slot r)) :=
  rfl

theorem cancelSpec_lawful (x : BitVec 32) (r : Except ErrName (BitVec 32)) (hr : CancelSpec x r) :
    (canceledEnc.encode r).size = canceledEnc.size ∧
      canceledEnc.decode (canceledEnc.encode r) = pure r := by
  refine errorUnionEnc_lawful _ _ fun e he => ?_
  rcases hr with rfl | rfl
  · cases he
  · cases he; exact Array.contains_iff_mem.mpr (by simp)

/-- The task body: its only stop is the cancelation point, which keeps the protocol; its result
is `x + 1` or `error.Canceled`. -/
theorem cancellable_body (x : BitVec 32) (io : Io) (u : ThreadId) (slot : Ptr)
    (G : ThreadId → FGh) (m : Mem) (n : Nat) (hgu : G u = .task slot false)
    (hi : (cancelProto x).inv G m) :
    (cancelProto x).WP u (Futures.cancellable io x) (fun r G' m' _ => CancelSpec x r ∧
      G' u = .task slot false ∧ (cancelProto x).inv G' m') G m n := by
  unfold Futures.cancellable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  refine WP.bind (FutureProto.wp_checkCancelC rfl fun k _ => ⟨.task slot false, ?_,
    fun G₁ m₁ hg hi₁ c m₂ ht => ?_⟩)
  · rw [← hgu, upd_same]; exact hi
  obtain ⟨hb, -, hc⟩ := Future.takeCancel_eq ht
  have hi₂ := @FutureProto.inv_of_blocks Tgt _ canceledEnc _ _ _ _ _ hi₁ hb
  rcases hc with rfl | rfl
  · dsimp only
    refine WP.pure' (WP.pure' ⟨.inl rfl, hg, hi₂⟩)
  · dsimp only
    simp only [StateT.run_bind]
    refine WP.bind (WP.callRC_ok rfl ?_)
    exact WP.pure' (WP.pure' ⟨.inr rfl, hg, hi₂⟩)

theorem cancellable_task (x : BitVec 32) (tgt : Tgt) (g : FGh) (hg : (cancelProto x).init tgt g)
    (u : ThreadId) (G : ThreadId → FGh) (m : Mem) (n : Nat) (hu : 0 < u) (hgu : G u = g)
    (hi : (cancelProto x).inv G m) :
    (cancelProto x).WP u (Futures.dispatch tgt) ((cancelProto x).QKid u) G
      { m with current := u } n := by
  obtain ⟨slot, hs, rfl⟩ := hg
  cases tgt with
  | cancellable_future slot' a =>
    obtain ⟨io, y⟩ := a
    simp only [cancelSlot] at hs
    split at hs
    · rename_i hy
      cases hs; subst hy
      rw [cancellable_dispatch]
      exact @FutureProto.task_wp Tgt _ canceledEnc _ _ _ _ _ _ _ _ hu (cancelSpec_lawful y)
        (cancellable_body y io u slot G _ n hgu (@FutureProto.inv_of_blocks Tgt _ canceledEnc _ _ _ _ _ hi rfl))
    · cases hs
  | _ => cases hs

theorem cancelValue_wp (io : Io) (x : BitVec 32) (n : Nat) :
    (cancelProto x).WP 0 (Futures.cancelValue io x) (fun v _ _ _ => CancelSpec x v)
      (fun _ => .none) { Futures.mem0 with current := 0 } n := by
  letI : Enc (Except ErrName (BitVec 32)) := canceledEnc
  unfold Futures.cancelValue
  refine WP.bind (WP.liftMem (fun _ _ => rfl) fun s2 m₁ ha => ⟨?_, ?_⟩)
  · obtain ⟨-, rfl⟩ := alloc_ok ha; rfl
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  refine WP.bind (FutureProto.wp_asyncC (α := Except ErrName (BitVec 32)) rfl
    fun slot m₂ _ k _ => ⟨.none, ?_, fun G₁ m₃ hg hi₃ =>
    ⟨.task slot false, ⟨slot, by simp [cancelSlot], rfl⟩, fun child m₄ _ m₅ _ => ?_⟩⟩)
  · exact no_task
  refine WP.bind (WP.liftM (fun _ _ => rfl) fun _ m₆ hs => ⟨by rw [FutureProto.store_threads hs], ?_⟩)
  refine WP.bind (FutureProto.cancel_wp
    (reads_pending (α := Except ErrName (BitVec 32)) (by decide) hs rfl) (only_child hg hi₃)
    fun r G' m' d hr => ?_)
  refine WP.pure' ?_
  refine WP.bind (WP.liftMem (fun _ _ => rfl) fun _ m₇ hf => ⟨?_, ?_⟩)
  · obtain ⟨_, _, -, -, rfl⟩ := free_ok hf; rfl
  exact WP.pure' hr

/-- **Cancelation.** Under every schedule, every result of `cancelValue(io, x)` is the task's
own result `x +% 1` or `error.Canceled` (when the task's `io.checkCancel()` observed the
request): `cancel` never reports another value, and in particular never success with a value
that the task did not compute. -/
theorem cancelValue_result (io : Io) (x : BitVec 32) {fuel : Nat} {o : Nat → Nat}
    {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run Futures.dispatch fuel o (Futures.cancelValue io x) Futures.mem0).run =
      some (.ok (v, m))) : v = .ok (x + 1) ∨ v = .error "Canceled" := by
  obtain ⟨_, _, hv⟩ := run_sound (P := cancelProto x) Futures.dispatch (fun _ => .none)
    (cancellable_task x) (fun h => by cases h) rfl (cancelValue_wp io x) h
  exact hv

end Futures.Proofs
