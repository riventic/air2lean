import ZigLean.External.Callback
import tests.roadmap.models.Fill

/-! Callback contracts (E02). `forEach(xs, ctx, cb)` and `evaluate(cb, ctx, x)` are observer
and evaluator clients whose callback is opaque except for its `CallbackContract`. Their
theorems hold for every implementation of that contract. They cover the callback's
postcondition, the context-pointer frame, the borrowed context's lifetime, reentrancy and
cancellation. `mark` is one concrete callback, built from the E01 `fill` contract. The
negative tests show that an uncontracted callback cannot be given empty effects. -/
namespace CallbackExample
open Zig Zig.External

/-! ## Clients -/

/-- Observer: `cb(ctx, x)` for each `x`, in order. It stops at the first result the callback
marks as `stop`, and returns whether every element was visited. -/
def forEach {α β : Type} (cb : Ptr × α → MemM β) (stop : β → Bool) (ctx : Ptr) :
    List α → MemM Bool
  | [] => pure true
  | x :: xs => do
    let r ← cb (ctx, x)
    if stop r then pure false else forEach cb stop ctx xs

/-- Evaluator: one call `cb(ctx, x)`, whose result is returned. -/
def evaluate {α β : Type} (cb : Ptr × α → MemM β) (ctx : Ptr) (x : α) : MemM β := cb (ctx, x)

variable {α β : Type} {cc : CallbackContract α β} {impl : Ptr × α → MemM β}

/-- The evaluator from the contract alone: the postcondition and the context frame. -/
theorem evaluate_spec (h : cc.Holds impl) {ctx : Ptr} {x : α} {before after : Mem} {r : β}
    (pre : cc.contract.pre (ctx, x) before)
    (run : evaluate impl ctx x before = some (.ok (r, after))) :
    cc.contract.post (ctx, x) before r after ∧
      ∀ b, some b ≠ ctx.block → some b ∉ cc.reentry (ctx, x) →
        after.blocks[b]? = before.blocks[b]? :=
  let c := CallbackContract.call h pre run
  ⟨c.1, c.2.2⟩

/-- The observer from the contract alone. `Inv` is a caller invariant that implies each call's
precondition and is restored by its postcondition. At the end, `Inv` holds and a live context
is still live. Every block outside the context and the declared re-entry blocks is unchanged,
including the caller's own blocks. A callback that never cancels lets the loop finish. -/
theorem forEach_spec (h : cc.Holds impl) (Inv : Mem → Prop) {ctx : Ptr} {xs : List α}
    (hpre : ∀ x ∈ xs, ∀ m, Inv m → cc.contract.pre (ctx, x) m)
    (hpost : ∀ x ∈ xs, ∀ m r m', Inv m → cc.contract.post (ctx, x) m r m' → Inv m')
    {before after : Mem} {done : Bool} (inv : Inv before)
    (run : forEach impl cc.stop ctx xs before = some (.ok (done, after))) :
    Inv after ∧ (Live before ctx → Live after ctx) ∧
      (∀ b, some b ≠ ctx.block → (∀ x ∈ xs, some b ∉ cc.reentry (ctx, x)) →
        after.blocks[b]? = before.blocks[b]?) ∧
      (cc.cancellation = .never → done = true) := by
  induction xs generalizing before with
  | nil =>
    simp only [forEach] at run
    cases run
    exact ⟨inv, id, fun _ _ _ => rfl, fun _ => rfl⟩
  | cons x xs ih =>
    simp only [forEach] at run
    obtain ⟨r, mid, first, rest⟩ := Conc.Proto.MemM.bind_ok run
    have pre := hpre x (.head _) before inv
    obtain ⟨post, live, frame⟩ := CallbackContract.call h pre first
    have invMid := hpost x (.head _) before r mid inv post
    by_cases hs : cc.stop r = true
    · simp only [hs, ↓reduceIte] at rest
      cases rest
      refine ⟨invMid, live, fun b hb hre => frame b hb (hre x (.head _)), fun never => ?_⟩
      rw [CallbackContract.call_continues h never pre first] at hs
      cases hs
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at rest
      obtain ⟨invEnd, liveEnd, frameEnd, doneEnd⟩ :=
        ih (fun y hy => hpre y (.tail _ hy)) (fun y hy => hpost y (.tail _ hy)) invMid rest
      refine ⟨invEnd, liveEnd ∘ live, fun b hb hre => ?_, doneEnd⟩
      rw [frameEnd b hb (fun y hy => hre y (.tail _ hy)), frame b hb (hre x (.head _))]

/-- A non-re-entrant callback leaves every block other than the context unchanged. -/
theorem forEach_frame (h : cc.Holds impl) (forbidden : cc.reentrancy = .forbidden)
    (Inv : Mem → Prop) {ctx : Ptr} {xs : List α}
    (hpre : ∀ x ∈ xs, ∀ m, Inv m → cc.contract.pre (ctx, x) m)
    (hpost : ∀ x ∈ xs, ∀ m r m', Inv m → cc.contract.post (ctx, x) m r m' → Inv m')
    {before after : Mem} {done : Bool} (inv : Inv before)
    (run : forEach impl cc.stop ctx xs before = some (.ok (done, after)))
    {b : BlockId} (outside : some b ≠ ctx.block) : after.blocks[b]? = before.blocks[b]? :=
  (forEach_spec h Inv hpre hpost inv run).2.2.1 b outside
    (fun _ _ => by simp [h.1.reentrancy forbidden])

/-! ## A concrete callback: `mark(ctx, v)` stores `v` at `ctx`

It forwards to the E01 `fill` model with a one-byte slice. Its contract is `fill`'s contract
read through that adapter, with a frame that also keeps every live block live. -/

def toFill (a : Ptr × BitVec 8) : Slice × BitVec 8 := (⟨a.1, 1⟩, a.2)

def mark : Ptr × BitVec 8 → MemM Unit := FillExample.fill ∘ toFill

/-- `fill` frees no block: its only write keeps the written block's lifetime. -/
theorem fill_live {a : Slice × BitVec 8} {before after : Mem} {r : Unit}
    (run : FillExample.fill a before = some (.ok (r, after))) {p : Ptr} (live : Live before p) :
    Live after p := by
  let bs := Array.replicate a.1.len.toNat (Byte.int a.2)
  rw [show FillExample.fill a before = (storeBytes a.1.ptr 1 bs).run before from rfl] at run
  rcases FillExample.storeBytes_cases a.1.ptr 1 bs before with hs | ⟨b, blk, o, hacc, hs⟩
  · rw [hs] at run; cases run
  · rw [hs] at run
    cases run
    obtain ⟨-, hblk, hlive, -⟩ := access_eq hacc
    obtain ⟨b', blk', hb', hblk', hlive'⟩ := live
    have hlt : b < before.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
    by_cases e : b = b'
    · subst e
      refine ⟨b, { blk with bytes := writeBytes blk.bytes o bs }, hb', ?_, hlive⟩
      simp only [Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds]
      exact Array.getElem?_setIfInBounds_self_of_lt hlt
    · refine ⟨b', blk', hb', ?_, hlive'⟩
      simp only [Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_ne e]
      exact hblk'

def markContract : Contract (Ptr × BitVec 8) Unit :=
  let c := FillExample.contract.comap toFill
  { c with frame := fun a before after => c.frame a before after ∧ (Live before a.1 → Live after a.1) }

/-- Writes only its context block, never re-enters its caller, never cancels. -/
def markCallback : CallbackContract (BitVec 8) Unit where
  contract := markContract
  termination := .total
  errors := [.illegal]
  effects := .tracked
  reads := fun _ => []
  reentrancy := .forbidden
  reentry := fun _ => []
  cancellation := .never
  stop := fun _ => false

theorem mark_evidence : markCallback.Holds mark := by
  refine ⟨⟨fun _ _ => rfl, fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ frame => frame.2, ?_, ?_⟩, ?_⟩
  · intro a _ entry ⟨hblock, _⟩
    exact .inl (by simp [CallbackContract.footprint, markCallback, toFill, hblock])
  · intro a before after _ frame b outside
    exact frame.1 b fun e => outside (by simp [CallbackContract.footprint, markCallback, toFill, e])
  · intro a before pre
    have h := (FillExample.evidence.1.comap toFill) a before pre
    simp only [mark, Function.comp_apply] at h ⊢
    generalize hr : FillExample.fill (toFill a) before = res at h ⊢
    rcases res with _ | (error | ⟨r, after⟩)
    · exact h
    · exact h
    · obtain ⟨post, frame, log, preserves⟩ := h
      exact ⟨post, ⟨frame, fill_live hr⟩, log, preserves⟩

/-- The last call's postcondition survives: it is the last call. -/
theorem forEach_mark_last {ctx : Ptr} {last : BitVec 8} :
    ∀ {xs : List (BitVec 8)} {before after : Mem} {done : Bool},
      forEach mark markCallback.stop ctx (xs ++ [last]) before = some (.ok (done, after)) →
      FillExample.Filled after ⟨ctx, 1⟩ last
  | [], before, after, done, run => by
    simp only [List.nil_append, forEach] at run
    obtain ⟨r, mid, first, rest⟩ := Conc.Proto.MemM.bind_ok run
    simp only [markCallback, Bool.false_eq_true, ↓reduceIte] at rest
    cases rest
    exact (markCallback.call mark_evidence trivial first).1
  | x :: xs, before, after, done, run => by
    simp only [List.cons_append, forEach] at run
    obtain ⟨r, mid, _, rest⟩ := Conc.Proto.MemM.bind_ok run
    simp only [markCallback, Bool.false_eq_true, ↓reduceIte] at rest
    exact forEach_mark_last rest

/-- `forEach(xs, ctx, mark)` over a nonempty list: the context holds the last element, the
loop is not cancelled, and every other block, for example the caller's own buffer, is
unchanged. The proof uses `markCallback` only, not `mark`'s body. -/
theorem forEach_mark {ctx : Ptr} {xs : List (BitVec 8)} {last : BitVec 8} {before after : Mem}
    {done : Bool} (run : forEach mark markCallback.stop ctx (xs ++ [last]) before =
      some (.ok (done, after))) :
    FillExample.Filled after ⟨ctx, 1⟩ last ∧ done = true ∧
      ∀ b, some b ≠ ctx.block → after.blocks[b]? = before.blocks[b]? := by
  have spec := forEach_spec mark_evidence (fun _ => True) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial) trivial run
  exact ⟨forEach_mark_last run, spec.2.2.2 rfl,
    fun b hb => spec.2.2.1 b hb fun _ _ => by simp [markCallback]⟩

/-! ## Negative tests: an uncontracted callback has no empty effects -/

/-- A callback body that frees every block. It is a legal model of an unknown callback, so
nothing about an uncontracted callback can be assumed. -/
def clobber : Ptr × BitVec 8 → MemM Unit := fun _ m => some (.ok ((), { m with blocks := #[] }))

/-- One block: the context of the negative tests. -/
def oneBlock : Mem := { blocks := #[{ bytes := #[], align := 1, kind := .heap, live := true, addr := 4096 }] }

/-- Without a contract, a callback cannot be assumed effect-free. -/
theorem uncontracted_not_effect_free :
    ¬ ∀ (cb : Ptr × BitVec 8 → MemM Unit) a m r m', cb a m = some (.ok (r, m')) → m' = m := by
  intro h
  have := congrArg (·.blocks.size) (h clobber (⟨some 0, 0⟩, 0) oneBlock () _ rfl)
  simp [oneBlock] at this

/-- Without a contract, the observer's liveness fact fails: `clobber` ends the lifetime of a
live context. -/
theorem uncontracted_forEach_frame_fails :
    ∃ before after done, forEach clobber (fun _ => false) ⟨some 0, 0⟩ [0] before =
        some (.ok (done, after)) ∧ Live before ⟨some 0, 0⟩ ∧ ¬ Live after ⟨some 0, 0⟩ :=
  ⟨oneBlock, { oneBlock with blocks := #[] }, true, rfl, ⟨0, _, rfl, rfl, rfl⟩,
    fun ⟨_, _, hb, hblk, _⟩ => by cases hb; simp at hblk⟩

/-- An unknown contract cannot claim the empty footprint: a frame that allows any change does
not respect it. Only a contract that proves its frame gets frame facts. -/
def havoc : Contract (Ptr × BitVec 8) Unit where
  pre := fun _ _ => True
  post := fun _ _ _ _ => True
  frame := fun _ _ _ => True
  access := fun _ _ _ => True
  failure := fun _ _ _ => True
  divergence := fun _ _ => True

theorem havoc_not_empty : ¬ havoc.Respects { reads := fun _ => [], writes := fun _ => [] } := by
  intro ⟨_, frame⟩
  have := frame (⟨some 0, 0⟩, 0) oneBlock { oneBlock with blocks := #[] } trivial trivial 0
    (by simp)
  simp [oneBlock] at this

/-- `clobber` satisfies `havoc`, so `havoc` is no stronger than no contract. -/
theorem clobber_havoc : havoc.Holds .«partial» [] .tracked clobber :=
  fun _ _ _ => ⟨trivial, trivial, ⟨#[], by simp, by simp⟩, fun h => nomatch h⟩

/-- A non-re-entrant callback contract whose frame allows any change is not well formed. -/
theorem havoc_not_callback (cc : CallbackContract (BitVec 8) Unit) (hc : cc.contract = havoc)
    (forbidden : cc.reentrancy = .forbidden) : ¬ cc.WellFormed := by
  intro wf
  have := wf.respects.2 (⟨none, 0⟩, 0) oneBlock { oneBlock with blocks := #[] }
    (by rw [hc]; trivial) (by rw [hc]; trivial) 0
    (by simp [CallbackContract.footprint, wf.reentrancy forbidden])
  simp [oneBlock] at this

/-- A call through a pointer with no known target and no contract always fails. The emitted
fallback arm (`Proofs/Layout/Proofs.lean`, `applyTwice_illegal`) is the same throw. -/
theorem unknown_call_fails (p : Ptr) (v : BitVec 8) (m : Mem) :
    ∀ r m', dispatch ([] : List (Ptr × (BitVec 8 → MemM Unit))) p v m ≠ some (.ok (r, m')) := by
  intro r m' h
  rw [dispatch_unknown] at h
  cases h

/-- A successful indirect call with known targets ran one of those targets. -/
example (p : Ptr) (v : BitVec 8) (m m' : Mem)
    (run : dispatch [(⟨some 0, 0⟩, fun v => mark (⟨some 5, 0⟩, v))] p v m = some (.ok ((), m'))) :
    p = ⟨some 0, 0⟩ := by
  obtain ⟨_, mem, _⟩ := dispatch_ok run
  simp at mem
  exact mem.1

end CallbackExample
