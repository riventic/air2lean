import ZigLean.Sep.Full.AutoAll

/-!
# Total stack pushes from the stack depth token (`docs/sep-full-state.md` §Stack depth)

`fsym` walks stack blocks and frames of a thread with a stack budget by the token rules of
`Full/Stack` (`FTotalTriple.allocStack_sp`, `free_sp`, `enterFrame_sp`, `leaveFrame_sp`): the
running thread `t` (`cur t`) with `sp t S D` and a fact `D + c ≤ S` pushes, and the free of the
top block gives the depth back. The same walks run in a thread (`FTTotalTriple`, the sequential
rules with the locality providers). The program-start adequacy (`FTotalTriple.run_init_stack`)
gives `main` the token. Rejected (mutations): a push whose charge does not fit, a free that is not
of the top block, a frame left open, a push without `cur t`.
-/

namespace SepAuto.Stack

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- A local whose address escapes: written, read back, freed. -/
def local8 (v : BitVec 64) : MemM (BitVec 64) := do
  let p ← Zig.allocStack 8 8
  Zig.store 8 p v
  let x ← Zig.load (BitVec 64) 8 p
  Zig.free p
  pure x

/-- **A total stack block from the token**: the charge `8 + 8` fits, so the push returns; the
free of the top block gives the depth back. -/
theorem local8_total (t S D : Nat) (v : BitVec 64) :
    FTotalTriple (⟪D + 16 ≤ S⟫ ⋆ (cur t ⋆ sp t S D)) (local8 v)
      (fun x => ⟪x = v⟫ ⋆ (cur t ⋆ sp t S D)) := by
  unfold local8
  fsym

/-- Two locals, freed in reverse order (the emitters' order, MM-18): each free is of the top. -/
def two (v w : BitVec 32) : MemM Unit := do
  let p ← Zig.allocStack 4 4
  let q ← Zig.allocStack 4 4
  Zig.store 4 p v
  Zig.store 4 q w
  Zig.free q
  Zig.free p

theorem two_total (t S D : Nat) (v w : BitVec 32) :
    FTotalTriple (⟪D + 16 ≤ S⟫ ⋆ (cur t ⋆ sp t S D)) (two v w) (fun _ => cur t ⋆ sp t S D) := by
  unfold two
  fsym

/-- A frame of a recursive call with a local in it. -/
def framed (v : BitVec 32) : MemM Unit := do
  Zig.enterFrame
  let p ← Zig.allocStack 4 4
  Zig.store 4 p v
  Zig.free p
  Zig.leaveFrame

theorem framed_total (t S D : Nat) (v : BitVec 32) :
    FTotalTriple (⟪D + frameBase + 8 ≤ S⟫ ⋆ (cur t ⋆ sp t S D)) (framed v)
      (fun _ => cur t ⋆ sp t S D) := by
  unfold framed
  fsym

/-- **In a thread**: the same walk as a thread step, by the sequential rules and the providers
(`ThreadLocal.allocStack`, `ThreadLocal.free_of`, `ThreadLocal.enterFrame`/`leaveFrame`). -/
theorem local8_thread (t S D : Nat) (v : BitVec 64) :
    FTTotalTriple (⟪D + 16 ≤ S⟫ ⋆ (cur t ⋆ sp t S D)) (local8 v)
      (fun x => ⟪x = v⟫ ⋆ (cur t ⋆ sp t S D)) := by
  unfold local8
  fsym

theorem framed_thread (t S D : Nat) (v : BitVec 32) :
    FTTotalTriple (⟪D + frameBase + 8 ≤ S⟫ ⋆ (cur t ⋆ sp t S D)) (framed v)
      (fun _ => cur t ⋆ sp t S D) := by
  unfold framed
  fsym

/-- `main`'s statement over its start mode (`stackStart S`: `cur 0 ⋆ sp 0 S 0 ⋆ unmetered`). -/
theorem local8_main (S : Nat) (hS : 16 ≤ S) (v : BitVec 64) :
    FTotalTriple (globals [] ⋆ stackStart S) (local8 v)
      (fun x => ⟪x = v⟫ ⋆ (globals [] ⋆ stackStart S)) := by
  unfold local8 stackStart
  fsym

/-- **From program start**: `main` with the budget `S ≥ 16` runs `local8` to its end, under every
placement whose reserve for the budget fits (STK-02). No run premise. -/
theorem local8_start (σ : Placement) (S : Nat) (hS : 16 ≤ S)
    (hr : ((Mem.ofGlobals σ []).reserveAt? 0 S).isSome) (v : BitVec 64) :
    ∃ x m' r', (local8 v).run ((Mem.ofGlobals σ []).withStack S) = pure (x, m') ∧
      Holds m' r' ⟨FHeap.empty, Know.none, Ghost.unit⟩ ∧
        (⟪x = v⟫ ⋆ (globals [] ⋆ stackStart S)) r' ∧ m'.FSeq :=
  FTotalTriple.run_init_stack σ [] (by simp [Mem.GlobalsFit]) (by simp) S hr (local8_main S hS v)

/-! ## Mutations: rejected -/

set_option linter.unusedVariables false in
/-- The charge `8 + 8` does not fit below `D + 15 ≤ S`: no total push. -/
example (t S D : Nat) (v : BitVec 64) : True := by
  fail_if_success
    have : FTotalTriple (⟪D + 15 ≤ S⟫ ⋆ (cur t ⋆ sp t S D)) (local8 v)
        (fun x => ⟪x = v⟫ ⋆ (cur t ⋆ sp t S D)) := by unfold local8; fsym
  trivial

set_option linter.unusedVariables false in
/-- Without the running thread's token there is no push from `sp`. -/
example (t S D : Nat) (v : BitVec 64) : True := by
  fail_if_success
    have : FTotalTriple (⟪D + 16 ≤ S⟫ ⋆ sp t S D) (local8 v) (fun x => ⟪x = v⟫ ⋆ sp t S D) := by
      unfold local8; fsym
  trivial

/-- The first local freed first: not the top of the stack. -/
def wrongOrder (v w : BitVec 32) : MemM Unit := do
  let p ← Zig.allocStack 4 4
  let q ← Zig.allocStack 4 4
  Zig.store 4 p v
  Zig.store 4 q w
  Zig.free p
  Zig.free q

set_option linter.unusedVariables false in
/-- Freeing below the top does not give the depth back: the post `sp t S D` is not reached. -/
example (t S D : Nat) (v w : BitVec 32) : True := by
  fail_if_success
    have : FTotalTriple (⟪D + 16 ≤ S⟫ ⋆ (cur t ⋆ sp t S D)) (wrongOrder v w)
        (fun _ => cur t ⋆ sp t S D) := by unfold wrongOrder; fsym
  trivial

/-- A frame entered and not left. -/
def openFrame : MemM Unit := Zig.enterFrame

set_option linter.unusedVariables false in
/-- A frame left open keeps its charge: the post `sp t S D` is not reached. -/
example (t S D : Nat) : True := by
  fail_if_success
    have : FTotalTriple (⟪D + frameBase ≤ S⟫ ⋆ (cur t ⋆ sp t S D)) openFrame
        (fun _ => cur t ⋆ sp t S D) := by unfold openFrame; fsym
  trivial

end SepAuto.Stack
