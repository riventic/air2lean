import Callbacks.Gen
import CallbackModel
import ZigLean.External.Callback
import ZigLean.Sep.Loop
import Proofs.Asm.Effects

/-!
# Function-pointer call sites bound to a callback contract (E02)

`Callbacks/Gen.lean` is the translator's output for `air/0.17.0` under `registry-0.17.0.json`,
which binds the address-taken `extern fn ext_visit` to the opaque `CallbackModel.visit` with
the callback contract `visitCallback` (assumed: `air2lean_model_0_evidence`, premises EXT-02,
EXT-03). Every call through a `*const fn (*u32, u32) callconv(.c) bool` dispatches over the
callable-address table: `ext_visit`'s block runs the registry model, `sumVisit`'s block the
translated function, any other pointer throws `.illegal`.

* `evaluate_eq`: the emitted call site is `dispatch targets` (the table's targets of the type).
* `sumVisit_holds`: the translated target satisfies the same contract (a proof, no assumption).
* `site_holds`: so the call site satisfies the contract at every pointer
  (`CallbackContract.Holds.dispatch`): a client needs no callback body.
* `evaluate_spec`: the evaluator, for every function pointer.
* `callOps_spec`: a call through a vtable field loaded from memory.
* `forEach_spec`: the observer loop, for every function pointer: a run that returns gives
  `true` (the contract never cancels), keeps the context live and changes no other block
  (`Zig.loopMM_partial`: the callback may fail or not return, so the loop rule is partial).
* `runExternal_spec`: the vtable `ext_ops` holds `&ext_visit`; the whole chain uses only the
  contract.
-/

namespace CallbacksProofs

open Zig Zig.External Callbacks CallbackModel

abbrev Visit := Ptr × BitVec 32 → MemM Bool

/-- The callable-address table's targets of `fn (*u32, u32) callconv(.c) bool`, in `mem0`
order: `ext_visit`'s block (the registry model), then `sumVisit`'s. -/
def targets : List (Ptr × Visit) :=
  [(⟨some 1, 0⟩, fun a => air2lean_model_0 a.1 a.2), (⟨some 3, 0⟩, fun a => sumVisit a.1 a.2)]

/-- The emitted call through the pointer is the table dispatch, for every pointer. -/
theorem evaluate_eq (p ctx : Ptr) (x : BitVec 32) :
    evaluate p ctx x = dispatch targets p (ctx, x) := by
  funext m
  by_cases h1 : p = ⟨some 1, 0⟩
  · subst h1
    simp [evaluate, dispatch, targets, StateT.run'_eq, callM, StateT.run_lift]
  by_cases h3 : p = ⟨some 3, 0⟩
  · subst h3
    simp [evaluate, dispatch, targets, StateT.run'_eq, callM, StateT.run_lift]
  simp [evaluate, dispatch, targets, h1, h3, StateT.run'_eq]
  rfl

/-- The registry model meets the callback contract (its assumed evidence, EXT-02). -/
theorem model_holds : visitCallback.Holds (fun a => air2lean_model_0 a.1 a.2) :=
  ⟨wellFormed, by
    have h := air2lean_model_0_evidence.1
    simpa [air2lean_model_0, air2lean_model_0_contract, contract, visitCallback, allErrors]
      using h⟩

theorem sumVisit_eq (p : Ptr) (x : BitVec 32) :
    sumVisit p x =
      (load (BitVec 32) 4 p >>= fun v => store 4 p (addWrap v x) >>= fun _ => pure true) := by
  simp [sumVisit, StateT.run'_eq, StateT.run_bind, StateT.run_monadLift]

/-- The translated target satisfies the contract too: it writes only its context. -/
theorem sumVisit_holds : visitCallback.Holds (fun a => sumVisit a.1 a.2) := by
  refine ⟨wellFormed, fun a before _ => ?_⟩
  dsimp only
  generalize hr : sumVisit a.1 a.2 before = r
  match r, hr with
  | none, _ => exact ⟨rfl, trivial⟩
  | some (.error e), _ => exact ⟨mem_allErrors e, trivial⟩
  | some (.ok (res, after)), hr =>
    have run : (sumVisit a.1 a.2).run before = pure (res, after) := hr
    rw [sumVisit_eq] at run
    obtain ⟨v, m₁, hl, hs⟩ := Asm.run_bind_ok run
    obtain ⟨_, m₂, hst, hp⟩ := Asm.run_bind_ok hs
    have hp : some (Except.ok (true, m₂)) = some (Except.ok (res, after)) := hp
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    obtain ⟨b, blk, o, hacc, -, rfl⟩ := load_inv hl
    obtain ⟨b', blk', o', hacc', rfl⟩ := Asm.storeBytes_inv hst
    obtain ⟨hb, -, -, -, -, -, -⟩ := access_eq hacc
    obtain ⟨hb', hblk', hlive', -, -, -, -⟩ := access_eq (Asm.access_of_accessW hacc')
    have hlt : b' < (before.recordAt b o (Enc.size (BitVec 32)) .read).blocks.size :=
      (Array.getElem?_eq_some_iff.mp hblk').1
    let m₁ := before.recordAt b o (Enc.size (BitVec 32)) .read
    let e₁ : FootprintEntry := ⟨before.current,
      VClock.bump (before.clocks[before.current]!) before.current, b, o,
      Enc.size (BitVec 32), .read⟩
    let e₂ : FootprintEntry := ⟨m₁.current, VClock.bump (m₁.clocks[m₁.current]!) m₁.current,
      b', o', (Enc.encode (addWrap v a.2)).size, .write⟩
    refine ⟨rfl, ⟨fun c hc => ?_, fun _ => ?_⟩, ⟨#[e₁, e₂], ?_, ?_⟩, fun h => nomatch h⟩
    · have hne : b' ≠ c := fun e => hc (e ▸ hb'.symm)
      simp [Mem.write, Mem.recordAt, Array.getElem?_setIfInBounds_ne hne]
    · refine ⟨b', { blk' with bytes := writeBytes blk'.bytes o' (Enc.encode (addWrap v a.2)) },
        hb', ?_, hlive'⟩
      simp only [Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds]
      exact Array.getElem?_setIfInBounds_self_of_lt hlt
    · have push2 : ∀ (xs : Array FootprintEntry) x y, (xs.push x).push y = xs ++ #[x, y] := by
        intro xs x y; apply Array.toList_inj.mp; simp
      simp only [Mem.write, Mem.recordAt, m₁, e₁, e₂, push2]
    · intro entry hentry
      simp only [List.mem_cons, List.not_mem_nil, or_false, e₁, e₂] at hentry
      rcases hentry with rfl | rfl
      · exact hb.symm
      · exact hb'.symm

theorem targets_holds : ∀ t ∈ targets, visitCallback.Holds t.2 := by
  intro t ht
  simp only [targets, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact model_holds
  · exact sumVisit_holds

/-- Every call through a pointer of the callback type satisfies the contract, whichever
pointer it is: a table target meets it, any other pointer fails with `.illegal`. -/
theorem site_holds (p : Ptr) : visitCallback.Holds (dispatch targets p) :=
  CallbackContract.Holds.dispatch targets_holds (mem_allErrors _) (fun _ _ => trivial) p
    wellFormed

/-- The evaluator, for every function pointer: a call that returns gives `true`, keeps the
context live and changes no block other than the context's. -/
theorem evaluate_spec {p ctx : Ptr} {x : BitVec 32} {before after : Mem} {r : Bool}
    (run : evaluate p ctx x before = some (.ok (r, after))) :
    r = true ∧ (Live before ctx → Live after ctx) ∧
      ∀ b, some b ≠ ctx.block → after.blocks[b]? = before.blocks[b]? := by
  rw [evaluate_eq] at run
  have h := CallbackContract.call (site_holds p) (cc := visitCallback) trivial run
  exact ⟨h.1, h.2.1, fun b hb => h.2.2 b hb (by simp [visitCallback])⟩

/-! ## The observer loop -/

/-- The frame of a callback-only run, relative to the memory `before`: the context stays live
and no other block changes. -/
def Kept (ctx : Ptr) (before m : Mem) : Prop :=
  (Live before ctx → Live m ctx) ∧ ∀ b, some b ≠ ctx.block → m.blocks[b]? = before.blocks[b]?

theorem Kept.refl (ctx : Ptr) (m : Mem) : Kept ctx m m := ⟨id, fun _ _ => rfl⟩

theorem Kept.trans {ctx : Ptr} {a b c : Mem} (h₁ : Kept ctx a b) (h₂ : Kept ctx b c) :
    Kept ctx a c :=
  ⟨fun h => h₂.1 (h₁.1 h), fun x hx => (h₂.2 x hx).trans (h₁.2 x hx)⟩

/-- Recording an access changes no block. -/
theorem Kept.recordAt (ctx : Ptr) (m : Mem) (b o n : Nat) (k : AccessKind) :
    Kept ctx m (m.recordAt b o n k) := ⟨id, fun _ _ => rfl⟩

/-- A call through the pointer, as the emitted `if … else throw .illegal` chain in `MM`. -/
theorem site_mm_eq {σ : Type} (cb ctx : Ptr) (x : BitVec 32) :
    (if (cb == (⟨some 1, 0⟩ : Ptr)) = true then (callM (air2lean_model_0 ctx x) : MM σ Bool)
      else if (cb == (⟨some 3, 0⟩ : Ptr)) = true then callM (sumVisit ctx x)
      else throw .illegal) = callM (dispatch targets cb (ctx, x)) := by
  by_cases h1 : cb = ⟨some 1, 0⟩
  · subst h1; simp [dispatch, targets]
  by_cases h3 : cb = ⟨some 3, 0⟩
  · subst h3; simp [dispatch, targets]
  simp [dispatch, targets, h1, h3, callM]
  rfl

/-- One iteration of the observer loop: the callback runs at most once, through the contract,
and an iteration that returns keeps the frame and never stops early. -/
theorem forEach_step (xs : Slice) (ctx cb : Ptr) (n : BitVec 64) (before : Mem) :
    ∀ (s : forEachLocals) m, Kept ctx before m → ∀ e s' m',
      ((forEach.loop7 xs ctx cb n).run s).run m = pure ((e, s'), m') →
      if forEach.again7 e then Kept ctx before m'
      else Kept ctx before m' ∧ ∀ v, e = .ret v → v = true := by
  intro s m hk e s' m' h
  simp only [forEach.loop7, bind_assoc, pure_bind] at h
  obtain ⟨a, s₁, m₁, hg, hA⟩ := MM.run_bind_ok h
  obtain ⟨ha, hs₁, hm₁⟩ := MM.run_get_ok hg
  subst a s₁ m₁
  obtain ⟨d, s₂, m₂, hI, hB⟩ := MM.run_bind_ok hA
  -- The inner block: the bounds test, the item load, the callback, the cancellation test.
  have inner : Kept ctx before m₂ ∧ d ≠ .ret false := by
    split at hI
    · obtain ⟨i14, s₃, m₃, hL, hC⟩ := MM.run_bind_ok hI
      obtain ⟨hs₃, hM⟩ := MM.run_callM_ok hL
      subst s₃
      obtain ⟨_, m₃', hci, hld⟩ := Asm.run_bind_ok hM
      have hm₃' : m₃' = m := by
        unfold checkIndex at hci
        split at hci
        · have hci : some (Except.ok ((), m)) = some (Except.ok ((), m₃')) := hci
          simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hci
          exact hci.2.symm
        · cases hci
      subst m₃'
      obtain ⟨b, -, o, -, -, rfl⟩ := load_inv hld
      have k₃ : Kept ctx before (m.recordAt b o (Enc.size (BitVec 32)) .read) :=
        hk.trans (Kept.recordAt ctx m b o _ _)
      obtain ⟨r, s₄, m₄, hD, hE⟩ := MM.run_bind_ok hC
      rw [site_mm_eq] at hD
      obtain ⟨hs₄, hV⟩ := MM.run_callM_ok hD
      subst s₄
      have hcall := CallbackContract.call (site_holds cb) (cc := visitCallback) trivial hV
      have k₄ : Kept ctx before m₄ := k₃.trans
        ⟨hcall.2.1, fun b hb => hcall.2.2 b hb (by simp [visitCallback])⟩
      have hr : r = true := hcall.1
      subst hr
      obtain ⟨d', s₅, m₅, hF, hG⟩ := MM.run_bind_ok hE
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hF
      obtain ⟨rfl, rfl, rfl⟩ := MM.run_pure_ok hF
      obtain ⟨rfl, rfl, rfl⟩ := MM.run_pure_ok hG
      exact ⟨k₄, fun h => nomatch h⟩
    · obtain ⟨rfl, rfl, rfl⟩ := MM.run_pure_ok hI
      exact ⟨hk, fun h => nomatch h⟩
  -- The continuation: `br9` increments the index and repeats; any other exit leaves.
  match d, inner, hB with
  | .br9, ⟨k₂, _⟩, hB =>
    dsimp only at hB
    obtain ⟨i23, s₆, m₆, hAdd, hB⟩ := MM.run_bind_ok hB
    obtain ⟨-, hs₆, hm₆⟩ := MM.run_liftR_ok hAdd
    subst s₆ m₆
    obtain ⟨_, s₇, m₇, hMod, hB⟩ := MM.run_bind_ok hB
    obtain ⟨hs₇, hm₇⟩ := MM.run_modify_ok hMod
    subst s₇ m₇
    obtain ⟨he, -, rfl⟩ := MM.run_pure_ok hB
    subst he
    exact k₂
  | .ret v, ⟨k₂, hne⟩, hB =>
    dsimp only at hB
    obtain ⟨rfl, rfl, rfl⟩ := MM.run_pure_ok hB
    cases v
    · exact absurd rfl hne
    · exact ⟨k₂, fun _ h => by cases h; rfl⟩
  | .br6, ⟨k₂, _⟩, hB =>
    dsimp only at hB
    obtain ⟨rfl, rfl, rfl⟩ := MM.run_pure_ok hB
    exact ⟨k₂, fun _ h => nomatch h⟩
  | .br15, ⟨k₂, _⟩, hB =>
    dsimp only at hB
    obtain ⟨rfl, rfl, rfl⟩ := MM.run_pure_ok hB
    exact ⟨k₂, fun _ h => nomatch h⟩
  | .rep7, ⟨k₂, _⟩, hB =>
    dsimp only at hB
    obtain ⟨rfl, rfl, rfl⟩ := MM.run_pure_ok hB
    exact k₂

/-- The observer, for every function pointer: a run that returns gives `true` (the contract
never cancels), keeps the context live and changes no other block. -/
theorem forEach_spec {xs : Slice} {ctx cb : Ptr} {before after : Mem} {r : Bool}
    (run : forEach xs ctx cb before = some (.ok (r, after))) :
    r = true ∧ Kept ctx before after := by
  have run : (forEach xs ctx cb).run before = pure (r, after) := run
  simp only [forEach] at run
  obtain ⟨e, m₁, hb, hm⟩ := Asm.run_bind_ok run
  obtain ⟨s₁, hb⟩ := MM.run'_ok hb
  obtain ⟨_, s₂, m₂, hMod, hb⟩ := MM.run_bind_ok hb
  obtain ⟨hs₂, hm₂⟩ := MM.run_modify_ok hMod
  subst s₂ m₂
  obtain ⟨n, s₄, m₄, hN, hb⟩ := MM.run_bind_ok hb
  obtain ⟨hn, hs₄, hm₄⟩ := MM.run_pure_ok hN
  subst n s₄ m₄
  obtain ⟨d, s₃, m₃, hL, hb⟩ := MM.run_bind_ok hb
  have hpost := loopMM_partial _ _ (fun _ m => Kept ctx before m)
    (fun (e : forEachExit) _ m => Kept ctx before m ∧ ∀ v, e = .ret v → v = true)
    (forEach_step xs ctx cb xs.len before) _ _ (Kept.refl ctx before) d s₃ m₃ hL
  match d, hpost, hb with
  | .br6, ⟨k, _⟩, hb =>
    obtain ⟨he, -, rfl⟩ := MM.run_pure_ok hb
    subst he
    obtain ⟨hr, rfl⟩ : r = true ∧ after = m₁ := by
      have hm : some (Except.ok (true, m₁)) = some (Except.ok (r, after)) := hm
      simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hm
      exact ⟨hm.1.symm, hm.2.symm⟩
    exact ⟨hr, k⟩
  | .ret v, ⟨k, hv⟩, hb =>
    obtain ⟨he, -, rfl⟩ := MM.run_pure_ok hb
    subst he
    have hm : some (Except.ok (v, m₁)) = some (Except.ok (r, after)) := hm
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ⟨hv v rfl, k⟩
  | .br15, _, hb | .br9, _, hb | .rep7, _, hb =>
    obtain ⟨he, -, rfl⟩ := MM.run_pure_ok hb
    subst he
    cases hm

/-- A call through the vtable field `ops.visit`, a pointer loaded from memory: whatever it holds,
a call that returns meets the contract. -/
theorem callOps_spec {ops ctx : Ptr} {x : BitVec 32} {before after : Mem} {r : Bool}
    (run : callOps ops ctx x before = some (.ok (r, after))) :
    r = true ∧ Kept ctx before after := by
  have run : (callOps ops ctx x).run before = pure (r, after) := run
  simp only [callOps] at run
  obtain ⟨e, m₁, hb, hm⟩ := Asm.run_bind_ok run
  obtain ⟨s₁, hb⟩ := MM.run'_ok hb
  obtain ⟨_, s₀, m₀, hP, hb⟩ := MM.run_bind_ok hb
  obtain ⟨-, hs₀, hm₀⟩ := MM.run_pure_ok hP
  subst s₀ m₀
  obtain ⟨q, s₂, m₂, hld, hb⟩ := MM.run_bind_ok hb
  obtain ⟨b, -, o, -, -, rfl⟩ := load_inv (MM.run_lift_ok hld).2
  obtain ⟨hs₂, -⟩ := MM.run_lift_ok hld
  subst s₂
  obtain ⟨v, s₃, m₃, hD, hb⟩ := MM.run_bind_ok hb
  rw [site_mm_eq] at hD
  obtain ⟨hs₃, hV⟩ := MM.run_callM_ok hD
  subst s₃
  have hcall := CallbackContract.call (site_holds q) (cc := visitCallback) trivial hV
  obtain ⟨he, -, rfl⟩ := MM.run_pure_ok hb
  subst he
  have hm : some (Except.ok (v, m₁)) = some (Except.ok (r, after)) := hm
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  exact ⟨hcall.1, (Kept.recordAt ctx before b o _ _).trans
    ⟨hcall.2.1, fun b hb => hcall.2.2 b hb (by simp [visitCallback])⟩⟩

/-- The observer through a vtable loaded from memory. -/
theorem viaOps_spec {ops : Ptr} {xs : Slice} {ctx : Ptr} {before after : Mem} {r : Bool}
    (run : viaOps ops xs ctx before = some (.ok (r, after))) :
    r = true ∧ Kept ctx before after := by
  have run : (viaOps ops xs ctx).run before = pure (r, after) := run
  simp only [viaOps] at run
  obtain ⟨e, m₁, hb, hm⟩ := Asm.run_bind_ok run
  obtain ⟨s₁, hb⟩ := MM.run'_ok hb
  obtain ⟨_, s₀, m₀, hP, hb⟩ := MM.run_bind_ok hb
  obtain ⟨-, hs₀, hm₀⟩ := MM.run_pure_ok hP
  subst s₀ m₀
  obtain ⟨q, s₂, m₂, hld, hb⟩ := MM.run_bind_ok hb
  obtain ⟨b, -, o, -, -, rfl⟩ := load_inv (MM.run_lift_ok hld).2
  obtain ⟨hs₂, -⟩ := MM.run_lift_ok hld
  subst s₂
  obtain ⟨v, s₃, m₃, hF, hb⟩ := MM.run_bind_ok hb
  obtain ⟨hs₃, hF'⟩ := MM.run_callM_ok hF
  subst s₃
  have hf := forEach_spec hF'
  obtain ⟨he, -, rfl⟩ := MM.run_pure_ok hb
  subst he
  have hm : some (Except.ok (v, m₁)) = some (Except.ok (r, after)) := hm
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  exact ⟨hf.1, (Kept.recordAt ctx before b o _ _).trans hf.2⟩

/-- `runExternal` passes the vtable `ext_ops`, whose field is `&ext_visit`: the foreign
callback runs through its registry contract only. -/
theorem runExternal_spec {xs : Slice} {ctx : Ptr} {before after : Mem} {r : Bool}
    (run : runExternal xs ctx before = some (.ok (r, after))) :
    r = true ∧ Kept ctx before after := by
  have run : (runExternal xs ctx).run before = pure (r, after) := run
  simp only [runExternal] at run
  obtain ⟨e, m₁, hb, hm⟩ := Asm.run_bind_ok run
  obtain ⟨s₁, hb⟩ := MM.run'_ok hb
  obtain ⟨v, s₂, m₂, hV, hb⟩ := MM.run_bind_ok hb
  obtain ⟨hs₂, hV'⟩ := MM.run_callM_ok hV
  subst s₂
  have hv := viaOps_spec hV'
  obtain ⟨he, -, rfl⟩ := MM.run_pure_ok hb
  subst he
  have hm : some (Except.ok (v, m₁)) = some (Except.ok (r, after)) := hm
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  exact hv

end CallbacksProofs
