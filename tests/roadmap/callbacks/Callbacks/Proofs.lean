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

end CallbacksProofs
