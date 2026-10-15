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

/-- Floor 1: the future's storage, `main`'s first block (block 0), stays, so the runtime record is
another block. -/
abbrev squareProto (x : BitVec 32) := futureProto (squareSlot x) (fun r : BitVec 32 => r = x * x) 1

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
        (WP.liftMem (fun _ he => by
          have := MemM.lift_err he; rw [square_run] at this; cases this) fun r m' hr => ?_)
      obtain ⟨hsq, rfl⟩ := MemM.lift_ok hr
      rw [square_run] at hsq
      cases hsq
      exact ⟨rfl, rfl, hgu, FutureProto.inv_of_blocks hi rfl⟩
    · cases hs
  | _ => cases hs

/-- At the spawn stop of the spawner no task exists yet. -/
theorem no_task {slotOf : Tgt → Option Ptr} {α : Type} [Enc α] {R : α → Prop} {fl : Nat}
    {m : Mem} (hm : fl ≤ m.blocks.size) :
    (futureProto slotOf R fl).inv (upd (fun _ => FGh.none) 0 FGh.none) m := by
  refine ⟨hm, fun u sl d hu => ?_⟩
  by_cases h0 : u = 0
  · subst h0; rw [upd_self] at hu; cases hu
  · rw [upd_ne _ _ h0] at hu; cases hu

/-- At the spawn stop after `Io.async`'s choice: `main` has no task, so no task exists. -/
theorem no_task_of {slotOf : Tgt → Option Ptr} {α : Type} [Enc α] {R : α → Prop} {fl : Nat}
    {G : ThreadId → FGh} {m m' : Mem} (hg : G 0 = .none) (hi : (futureProto slotOf R fl).inv G m)
    (hm : fl ≤ m'.blocks.size) :
    (futureProto slotOf R fl).inv (upd G 0 FGh.none) m' := by
  refine ⟨hm, fun u sl d hu => ?_⟩
  by_cases h0 : u = 0
  · subst h0; rw [upd_self] at hu; cases hu
  · rw [upd_ne _ _ h0] at hu
    have := (hi.2 u sl d hu).1
    rw [hg] at this; cases this

/-- After the spawn, the only task is the new one. -/
theorem only_child {slotOf : Tgt → Option Ptr} {α : Type} [Enc α] {R : α → Prop} {fl : Nat}
    {G₁ : ThreadId → FGh} {m : Mem} {slot : Ptr} {child : ThreadId}
    (hg : G₁ 0 = .none) (hi : (futureProto slotOf R fl).inv G₁ m) :
    ∀ u sl d, upd G₁ child (.task slot false) u = .task sl d → u = child ∧ sl = slot ∧ d = false := by
  intro u sl d hu
  by_cases hc : u = child
  · subst hc; rw [upd_self] at hu; cases hu; exact ⟨rfl, rfl, rfl⟩
  · rw [upd_ne _ _ hc] at hu
    have := (hi.2 u sl d hu).1
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
  rw [decodeLoad_of_decode (Future.decode_pending slot hsz)] at this
  cases this; rfl

/-- The spawner's view of the record after `Io.async` and the store of the future at `p`
(audit soundness-2026-10-14 S4): the future decodes and is pending at `slot`, the task's
thread id at `slot` decodes (the store of the future went to another block), and the memory keeps
its blocks. -/
theorem pending_view {α : Type} [Enc α] {p slot : Ptr} {child : ThreadId} {m₄ m₅ m₆ : Mem}
    {x y : Unit} (hsz : Enc.size α ≠ 0) (ha : Future.align α = 8)
    (hs₅ : ((store 8 slot child).run m₄).run = some (.ok (x, m₅)))
    (hs₆ : ((store 8 p ({ task := some slot, result := none } : Future α)).run m₅).run =
      some (.ok (y, m₆)))
    (hne : p.block ≠ slot.block) :
    (Decodes (Future α) (Future.align α) p m₆ ∧
      ∀ f m', ((load (Future α) (Future.align α) p).run m₆).run = some (.ok (f, m')) →
        f = { task := some slot, result := none }) ∧
    Decodes ThreadId 8 slot m₆ ∧ m₆.blocks.size = m₄.blocks.size := by
  refine ⟨⟨?_, reads_pending hsz hs₆ ha⟩, ?_, ?_⟩
  · rw [ha]
    exact Future.decodes_after_store (pending_size slot) hs₆
      ⟨_, by rw [decodeLoad_of_decode (Future.decode_pending slot hsz)]; rfl⟩
  · exact Future.decodes_store_other (Future.decodes_after_store (LawfulEnc.size_encode child) hs₅
      ⟨child, by rw [decodeLoad_of_decode (LawfulEnc.decode_encode child)]; rfl⟩) hs₆ hne
  · rw [Future.store_blocks_size hs₆, Future.store_blocks_size hs₅]

/-- `alloc` and a fork keep the blocks there were, so the floor of the protocol. -/
theorem alloc_size {m m' : Mem} {kind : BlockKind} {size align : Nat} {q : Ptr}
    (h : ((alloc kind size align).run m).run = some (.ok (q, m'))) :
    q = ⟨some m.blocks.size, 0⟩ ∧ m'.blocks.size = m.blocks.size + 1 := by
  obtain ⟨rfl, rfl⟩ := alloc_ok h
  exact ⟨rfl, by simp [Mem.afterAlloc]⟩

theorem fork_blocks {m m' : Mem} {c : ThreadId}
    (h : (Thread.fork.run m).run = some (.ok (c, m'))) : m'.blocks = m.blocks := by
  rw [fork_run] at h; cases h; rfl

/-- A consumed future's result of an integer or error-union type is never all undefined bytes:
their decode of undefined bytes throws. -/
theorem undef_u32 (v : BitVec 32) :
    Enc.decode (Array.replicate (Enc.size (BitVec 32)) Byte.undef) ≠ (pure v : Result (BitVec 32)) := by
  intro h
  have : (Enc.decode (Array.replicate (Enc.size (BitVec 32)) Byte.undef) :
      Result (BitVec 32)).run = some (.error .unspecified) := by decide
  rw [h] at this; cases this

theorem awaitValue_wp (σ : Placement) (io : Io) (x : BitVec 32) (n : Nat) :
    (squareProto x).WP 0 (Futures.awaitValue io x) (fun v _ _ _ => v = x * x)
      (fun _ => .none) { Futures.mem0 σ with current := 0 } n := by
  unfold Futures.awaitValue
  refine WP.bind (WP.liftMem (ErrOk.of_run rfl alloc_native) fun s2 m₁ ha => ?_)
  obtain ⟨hs2, hm₁⟩ := alloc_size ha
  refine ⟨by obtain ⟨-, rfl⟩ := alloc_ok ha; rfl, ?_⟩
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  refine WP.bind (FutureProto.wp_asyncWithPolicyC fun _ _ => ⟨FGh.none,
    no_task (by rw [hm₁]; exact Nat.le_add_left _ _), fun G₀ m₀ hg₀ hi₀ c _ => ?_⟩)
  unfold asyncOutcomeC
  split
  · -- `Io.async` ran the task in the caller: a consumed future
    refine FutureProto.wp_asyncEagerC (WP.liftMem (fun _ he => by
      have := MemM.lift_err he; rw [square_run] at this; cases this) fun r m₂ hr => ?_)
    obtain ⟨hsq, rfl⟩ := MemM.lift_ok hr
    rw [square_run] at hsq
    cases hsq
    refine ⟨rfl, ?_⟩
    refine WP.bind (WP.liftM (ErrOk.of_run rfl store_native) fun _ m₆ hs =>
      ⟨by rw [FutureProto.store_threads hs], ?_⟩)
    refine WP.bind (FutureProto.await_consumed_wp rfl
      (FutureProto.reads_consumed_def (LawfulEnc.size_encode _) (LawfulEnc.decode_encode _)
        undef_u32 hs) fun _ _ => ?_)
    refine WP.pure' ?_
    refine WP.bind (WP.liftMem (ErrOk.of_run rfl free_native) fun _ m₇ hf => ⟨?_, ?_⟩)
    · obtain ⟨_, _, -, -, rfl⟩ := free_ok hf; rfl
    exact WP.pure' rfl
  refine FutureProto.wp_asyncC (α := BitVec 32) rfl fun slot m₂ hsl k _ => ?_
  obtain ⟨hslot, hm₂⟩ := alloc_size hsl
  refine ⟨.none, no_task_of hg₀ hi₀ (by rw [hm₂]; exact Nat.le_succ_of_le hi₀.1),
    fun G₁ m₃ hg hi₃ => ⟨.task slot false, ⟨slot, by simp [squareSlot], rfl⟩,
      fun child m₄ hf m₅ hs₅ => ?_⟩⟩
  refine WP.bind (WP.liftM (ErrOk.of_run rfl store_native) fun _ m₆ hs =>
    ⟨by rw [FutureProto.store_threads hs], ?_⟩)
  -- `main`'s storage is block 0, below the floor; the record is a newer block.
  have hne : s2.block ≠ slot.block := by
    rw [hs2, hslot]
    intro h
    simp only [Option.some.injEq] at h
    change 0 = m₀.blocks.size at h
    have := hi₀.1
    omega
  obtain ⟨hp, htid, hsz⟩ := pending_view (α := BitVec 32) (by decide) rfl hs₅ hs hne
  refine WP.bind (FutureProto.await_wp hp htid
    (by rw [hsz, fork_blocks hf]; exact hi₃.1) (only_child hg hi₃) fun r G' m' d hr => ?_)
  refine WP.pure' ?_
  refine WP.bind (WP.liftMem (ErrOk.of_run rfl free_native) fun _ m₇ hf => ⟨?_, ?_⟩)
  · obtain ⟨_, _, -, -, rfl⟩ := free_ok hf; rfl
  exact WP.pure' hr

/-- **Completion.** Under every schedule, every result of `awaitValue(io, x)` is `x *% x`: the
task's result, written into its runtime record and returned by `await`. -/
theorem awaitValue_result (env : Env) (henv : env.spawn = .available) {σ : Placement} (io : Io) (x : BitVec 32) {fuel : Nat} {o : Nat → Nat} {v : BitVec 32}
    {m : Mem} (h : (Sched.run env Futures.dispatch fuel o (Futures.awaitValue io x) (Futures.mem0 σ)).run =
      some (.ok (v, m))) : v = x * x := by
  obtain ⟨_, _, hv⟩ := run_sound (P := squareProto x) env (Proto.of_available henv) Futures.dispatch (fun _ => .none)
    (square_task x) (FutureProto.not_strict) rfl (awaitValue_wp σ io x) h
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
    simp [hm, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont]

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
    simp only [hx, Zig.sub, hov, hb, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- The checked task of `x` only. -/
def checkedSlot (x : BitVec 32) : Tgt → Option Ptr
  | .checked_future slot y => if y = x then some slot else none
  | _ => none

abbrev checkedProto (x : BitVec 32) :=
  @futureProto Tgt (Except ErrName (BitVec 32)) zeroEnc (checkedSlot x) (fun r => r = checkedSpec x) 1

/-- The undefined bytes of a `Fail!u32` do not decode (audit soundness-2026-10-14 S4). -/
theorem undef_zero (v : Except ErrName (BitVec 32)) :
    zeroEnc.decode (Array.replicate zeroEnc.size Byte.undef) ≠ pure v := by
  intro h
  have : (zeroEnc.decode (Array.replicate zeroEnc.size Byte.undef)).run =
      some (.error .unspecified) := by decide
  rw [h] at this; cases this

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
      refine @FutureProto.task_wp Tgt _ zeroEnc _ _ _ _ _ _ _ _ _ hu
        (fun r hr => by subst hr; exact checkedSpec_lawful y)
        (WP.liftMem (fun _ he => by
          have := MemM.lift_err he; rw [checked_run] at this; cases this) fun r m' hr => ?_)
      obtain ⟨hc, rfl⟩ := MemM.lift_ok hr
      rw [checked_run] at hc
      cases hc
      exact ⟨rfl, rfl, hgu, @FutureProto.inv_of_blocks Tgt _ zeroEnc _ _ _ _ _ _ hi rfl⟩
    · cases hs
  | _ => cases hs

theorem awaitError_wp (σ : Placement) (io : Io) (x : BitVec 32) (n : Nat) :
    (checkedProto x).WP 0 (Futures.awaitError io x) (fun v _ _ _ => v = checkedSpec x)
      (fun _ => .none) { Futures.mem0 σ with current := 0 } n := by
  letI : Enc (Except ErrName (BitVec 32)) := zeroEnc
  unfold Futures.awaitError
  refine WP.bind (WP.liftMem (ErrOk.of_run rfl alloc_native) fun s2 m₁ ha => ?_)
  obtain ⟨hs2, hm₁⟩ := alloc_size ha
  refine ⟨by obtain ⟨-, rfl⟩ := alloc_ok ha; rfl, ?_⟩
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  refine WP.bind (FutureProto.wp_asyncWithPolicyC fun _ _ => ⟨FGh.none,
    no_task (by rw [hm₁]; exact Nat.le_add_left _ _), fun G₀ m₀ hg₀ hi₀ c _ => ?_⟩)
  unfold asyncOutcomeC
  split
  · -- `Io.async` ran the task in the caller: a consumed future
    refine FutureProto.wp_asyncEagerC (WP.liftMem (fun _ he => by
      have := MemM.lift_err he; rw [checked_run] at this; cases this) fun r m₂ hr => ?_)
    obtain ⟨hck, rfl⟩ := MemM.lift_ok hr
    rw [checked_run] at hck
    cases hck
    refine ⟨rfl, ?_⟩
    obtain ⟨hsz, hdec⟩ := checkedSpec_lawful x
    refine WP.bind (WP.liftM (ErrOk.of_run rfl store_native) fun _ m₆ hs =>
      ⟨by rw [FutureProto.store_threads hs], ?_⟩)
    refine WP.bind (FutureProto.await_consumed_wp rfl
      (FutureProto.reads_consumed_def hsz hdec undef_zero hs) fun _ _ => ?_)
    refine WP.pure' ?_
    refine WP.bind (WP.liftMem (ErrOk.of_run rfl free_native) fun _ m₇ hf => ⟨?_, ?_⟩)
    · obtain ⟨_, _, -, -, rfl⟩ := free_ok hf; rfl
    exact WP.pure' rfl
  refine FutureProto.wp_asyncC (α := Except ErrName (BitVec 32)) rfl fun slot m₂ hsl k _ => ?_
  obtain ⟨hslot, hm₂⟩ := alloc_size hsl
  refine ⟨.none, no_task_of hg₀ hi₀ (by rw [hm₂]; exact Nat.le_succ_of_le hi₀.1),
    fun G₁ m₃ hg hi₃ => ⟨.task slot false, ⟨slot, by simp [checkedSlot], rfl⟩,
      fun child m₄ hf m₅ hs₅ => ?_⟩⟩
  refine WP.bind (WP.liftM (ErrOk.of_run rfl store_native) fun _ m₆ hs =>
    ⟨by rw [FutureProto.store_threads hs], ?_⟩)
  have hne : s2.block ≠ slot.block := by
    rw [hs2, hslot]
    intro h
    simp only [Option.some.injEq] at h
    change 0 = m₀.blocks.size at h
    have := hi₀.1
    omega
  obtain ⟨hp, htid, hsz⟩ := pending_view (α := Except ErrName (BitVec 32)) (by decide) rfl hs₅ hs hne
  refine WP.bind (FutureProto.await_wp hp htid
    (by rw [hsz, fork_blocks hf]; exact hi₃.1) (only_child hg hi₃) fun r G' m' d hr => ?_)
  refine WP.pure' ?_
  refine WP.bind (WP.liftMem (ErrOk.of_run rfl free_native) fun _ m₇ hf => ⟨?_, ?_⟩)
  · obtain ⟨_, _, -, -, rfl⟩ := free_ok hf; rfl
  exact WP.pure' hr

/-- **Error propagation.** Under every schedule, every result of `awaitError(io, x)` is the
task's result: `error.Zero` for `x = 0`, else `x - 1`. -/
theorem awaitError_result (env : Env) (henv : env.spawn = .available) {σ : Placement} (io : Io) (x : BitVec 32) {fuel : Nat} {o : Nat → Nat}
    {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run env Futures.dispatch fuel o (Futures.awaitError io x) (Futures.mem0 σ)).run =
      some (.ok (v, m))) : v = checkedSpec x := by
  obtain ⟨_, _, hv⟩ := run_sound (P := checkedProto x) env (Proto.of_available henv) Futures.dispatch (fun _ => .none)
    (checked_task x) (fun h => by cases h) rfl (awaitError_wp σ io x) h
  exact hv

theorem awaitError_zero (env : Env) (henv : env.spawn = .available) {σ : Placement} (io : Io) {fuel : Nat} {o : Nat → Nat}
    {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run env Futures.dispatch fuel o (Futures.awaitError io 0) (Futures.mem0 σ)).run =
      some (.ok (v, m))) : v = .error "Zero" :=
  awaitError_result env henv io 0 h

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
  @futureProto Tgt (Except ErrName (BitVec 32)) canceledEnc (cancelSlot x) (CancelSpec x) 1

/-- The undefined bytes of an `Io.Cancelable!u32` do not decode (audit soundness-2026-10-14 S4). -/
theorem undef_canceled (v : Except ErrName (BitVec 32)) :
    canceledEnc.decode (Array.replicate canceledEnc.size Byte.undef) ≠ pure v := by
  intro h
  have : (canceledEnc.decode (Array.replicate canceledEnc.size Byte.undef)).run =
      some (.error .unspecified) := by decide
  rw [h] at this; cases this

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
theorem cancellable_body (x : BitVec 32) (io : Io) (u : ThreadId) (g : FGh)
    (G : ThreadId → FGh) (m : Mem) (n : Nat) (hgu : G u = g)
    (hi : (cancelProto x).inv G m) :
    (cancelProto x).WP u (Futures.cancellable io x) (fun r G' m' _ => CancelSpec x r ∧
      G' u = g ∧ (cancelProto x).inv G' m') G m n := by
  unfold Futures.cancellable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  refine WP.bind (FutureProto.wp_checkCancelC rfl fun k _ => ⟨g, ?_,
    fun G₁ m₁ hg hi₁ c m₂ ht => ?_⟩)
  · rw [← hgu, upd_same]; exact hi
  obtain ⟨hb, -, hc⟩ := Future.takeCancel_eq ht
  have hi₂ := @FutureProto.inv_of_blocks Tgt _ canceledEnc _ _ _ _ _ _ hi₁ hb
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
      exact @FutureProto.task_wp Tgt _ canceledEnc _ _ _ _ _ _ _ _ _ hu (cancelSpec_lawful y)
        (cancellable_body y io u (.task slot false) G _ n hgu
          (@FutureProto.inv_of_blocks Tgt _ canceledEnc _ _ _ _ _ _ hi rfl))
    · cases hs
  | _ => cases hs

theorem cancelValue_wp (σ : Placement) (io : Io) (x : BitVec 32) (n : Nat) :
    (cancelProto x).WP 0 (Futures.cancelValue io x) (fun v _ _ _ => CancelSpec x v)
      (fun _ => .none) { Futures.mem0 σ with current := 0 } n := by
  letI : Enc (Except ErrName (BitVec 32)) := canceledEnc
  unfold Futures.cancelValue
  refine WP.bind (WP.liftMem (ErrOk.of_run rfl alloc_native) fun s2 m₁ ha => ?_)
  obtain ⟨hs2, hm₁⟩ := alloc_size ha
  refine ⟨by obtain ⟨-, rfl⟩ := alloc_ok ha; rfl, ?_⟩
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  refine WP.bind (FutureProto.wp_asyncWithPolicyC fun _ _ => ⟨FGh.none,
    no_task (by rw [hm₁]; exact Nat.le_add_left _ _), fun G₀ m₀ hg₀ hi₀ c _ => ?_⟩)
  unfold asyncOutcomeC
  split
  · -- `Io.async` ran the task in the caller (`main`): a consumed future
    refine FutureProto.wp_asyncEagerC (WP.mono (fun r G' m' d (h : CancelSpec x r ∧ G' 0 = .none ∧
        (cancelProto x).inv G' m') => ?_) (cancellable_body x io 0 .none G₀ _ _ hg₀ hi₀))
    obtain ⟨hr, -, -⟩ := h
    obtain ⟨hsz, hdec⟩ := cancelSpec_lawful x r hr
    refine WP.bind (WP.liftM (ErrOk.of_run rfl store_native) fun _ m₆ hs =>
      ⟨by rw [FutureProto.store_threads hs], ?_⟩)
    refine WP.bind (FutureProto.cancel_consumed_wp rfl
      (FutureProto.reads_consumed_def hsz hdec undef_canceled hs) fun _ _ => ?_)
    refine WP.pure' ?_
    refine WP.bind (WP.liftMem (ErrOk.of_run rfl free_native) fun _ m₇ hf => ⟨?_, ?_⟩)
    · obtain ⟨_, _, -, -, rfl⟩ := free_ok hf; rfl
    exact WP.pure' hr
  refine FutureProto.wp_asyncC (α := Except ErrName (BitVec 32)) rfl fun slot m₂ hsl k _ => ?_
  obtain ⟨hslot, hm₂⟩ := alloc_size hsl
  refine ⟨.none, no_task_of hg₀ hi₀ (by rw [hm₂]; exact Nat.le_succ_of_le hi₀.1),
    fun G₁ m₃ hg hi₃ => ⟨.task slot false, ⟨slot, by simp [cancelSlot], rfl⟩,
      fun child m₄ hf m₅ hs₅ => ?_⟩⟩
  refine WP.bind (WP.liftM (ErrOk.of_run rfl store_native) fun _ m₆ hs =>
    ⟨by rw [FutureProto.store_threads hs], ?_⟩)
  have hne : s2.block ≠ slot.block := by
    rw [hs2, hslot]
    intro h
    simp only [Option.some.injEq] at h
    change 0 = m₀.blocks.size at h
    have := hi₀.1
    omega
  obtain ⟨hp, htid, hsz⟩ := pending_view (α := Except ErrName (BitVec 32)) (by decide) rfl hs₅ hs hne
  refine WP.bind (FutureProto.cancel_wp hp htid
    (by rw [hsz, fork_blocks hf]; exact hi₃.1) (only_child hg hi₃) fun r G' m' d hr => ?_)
  refine WP.pure' ?_
  refine WP.bind (WP.liftMem (ErrOk.of_run rfl free_native) fun _ m₇ hf => ⟨?_, ?_⟩)
  · obtain ⟨_, _, -, -, rfl⟩ := free_ok hf; rfl
  exact WP.pure' hr

/-- **Cancelation.** Under every schedule, every result of `cancelValue(io, x)` is the task's
own result `x +% 1` or `error.Canceled` (when the task's `io.checkCancel()` observed the
request): `cancel` never reports another value, and in particular never success with a value
that the task did not compute. -/
theorem cancelValue_result (env : Env) (henv : env.spawn = .available) {σ : Placement} (io : Io) (x : BitVec 32) {fuel : Nat} {o : Nat → Nat}
    {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run env Futures.dispatch fuel o (Futures.cancelValue io x) (Futures.mem0 σ)).run =
      some (.ok (v, m))) : v = .ok (x + 1) ∨ v = .error "Canceled" := by
  obtain ⟨_, _, hv⟩ := run_sound (P := cancelProto x) env (Proto.of_available henv) Futures.dispatch (fun _ => .none)
    (cancellable_task x) (fun h => by cases h) rfl (cancelValue_wp σ io x) h
  exact hv

/-! ## Idempotence -/

/-- **Idempotence.** A consumed future (`any_future = null`) returns its stored result again,
with no sync op: `awaitTwice` returns the same value twice. -/
theorem second_await {σ : Type} (io : Io) (p : Ptr) (r : BitVec 32) (s : σ) (m m' : Mem) (n : Nat)
    (hl : (load (Future (BitVec 32)) (Future.align (BitVec 32)) p).run m =
      pure ({ task := none, result := some r }, m')) :
    ((awaitC io p : CM Tgt σ (BitVec 32)).run s) n m = .leaf (some (.ok ((r, s), m'))) :=
  Future.awaitC_consumed n hl

/-- The stored consumed future reads back as itself. -/
theorem consumed_reads_back (r : BitVec 32) :
    (Enc.decode (Enc.encode ({ task := none, result := some r } : Future (BitVec 32))) :
      Result (Future (BitVec 32))) = pure { task := none, result := some r } :=
  Future.decode_consumed (LawfulEnc.size_encode r) (LawfulEnc.decode_encode r) (by
    rw [Array.all_eq_false]
    refine ⟨0, by rw [LawfulEnc.size_encode]; decide, ?_⟩
    simp [Enc.encode, padTo, intBytes, intSize])

/-! ## Rejected uses

Hand-written clients of the model, each checked by the kernel on one schedule (`decide
+kernel`, kernel reduction only); `Futures/Runtime.lean` enumerates every schedule of each. -/

/-- A squaring task and a thread that awaits a future it did not create. -/
inductive H where
  | square (slot : Ptr) (x : BitVec 32)
  | awaiter (p : Ptr)

def hDispatch : H → ConcM H Unit
  | .square slot x => ConcM.liftMem (Future.complete slot (x * x))
  | .awaiter p => discard ((awaitC (α := BitVec 32) ⟨⟩ p : CM H Unit (BitVec 32)).run' ())

/-- `Io.async` without `await`/`cancel`. -/
def leak : ConcM H Unit := (do
  let _ ← asyncC (α := BitVec 32) (fun slot => H.square slot 3) (pure (3 * 3))
  pure () : CM H Unit Unit).run' ()

/-- A second thread awaits the main thread's future. -/
def foreignAwait : ConcM H Unit := (do
  let f ← asyncC (α := BitVec 32) (fun slot => H.square slot 3) (pure (3 * 3))
  let p ← callMC (alloc .stack 16 8)
  callMC (store 8 p f)
  let helper := (← spawnC (H.awaiter p)).toOption.getD 0
  joinC helper
  let _ ← awaitC (α := BitVec 32) ⟨⟩ p
  pure () : CM H Unit Unit).run' ()

/-- Two threads await one future concurrently. -/
def doubleAwait : ConcM H (BitVec 32) := (do
  let f ← asyncC (α := BitVec 32) (fun slot => H.square slot 3) (pure (3 * 3))
  let p ← callMC (alloc .stack 16 8)
  callMC (store 8 p f)
  let helper := (← spawnC (H.awaiter p)).toOption.getD 0
  let r ← awaitC (α := BitVec 32) ⟨⟩ p
  joinC helper
  pure r : CM H Unit (BitVec 32)).run' ()

def outcome {α : Type} (r : Option (Except Error (α × Mem))) : Option (Except Error Unit) :=
  r.map (·.map fun _ => ())

/-- **Leak.** A future that is never awaited or canceled is reported: its task is an unjoined
thread of the spawner (`.illegal`). -/
theorem leak_illegal :
    outcome (Sched.run ⟨.any, .available⟩ hDispatch 10 (fun _ => 0) leak {}).run = some (.error .illegal) := by
  decide +kernel

/-- **Foreign consumer.** Only the spawner may consume a future (`.illegal`). -/
theorem foreignAwait_illegal :
    outcome (Sched.run ⟨.any, .available⟩ hDispatch 20 (fun _ => 0) foreignAwait {}).run = some (.error .illegal) := by
  decide +kernel

/-- **Concurrent double await.** `await` is not threadsafe: two consumers race on the future
value or join a task that is not theirs (`.illegal`), on both orders of the two awaits. -/
theorem doubleAwait_illegal :
    outcome (Sched.run ⟨.any, .available⟩ hDispatch 20 (fun _ => 0) doubleAwait {}).run = some (.error .illegal) ∧
      outcome (Sched.run ⟨.any, .available⟩ hDispatch 20 (fun _ => 1) doubleAwait {}).run = some (.error .illegal) := by
  decide +kernel

/-- The model rule behind both: a join by a thread other than the spawner throws. -/
theorem join_foreign_illegal (m : Mem) (tid : ThreadId) (rec : ThreadRec)
    (hr : m.threads[tid]? = some rec) (hs : rec.spawner ≠ m.current) :
    ((Thread.join tid).run m).run = some (.error .illegal) := by
  simp [Thread.join, hr, hs, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure,
    throw, throwThe, MonadExceptOf.throw, StateT.lift]

end Futures.Proofs
