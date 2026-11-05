import ZigLean.Sep.Full.AutoAll

/-!
# Loops with a registered invariant (`@[fsym_inv]`, P09-E4)

A loop body `B` in the shape the translator emits (`Zig.loop (B p n) again` over a locals
structure, its exit matched by the caller) with the invariant `B.inv`, the measure `B.meas` and
the exit post `B.post` registered by `@[fsym_inv]`. `fsym` proves the function that runs the loop
with no loop lemma: at the loop it applies `FTotalTriple.loop_measure` (`FTriple.loop` in the
partial logic) with the registered definitions, plans the invariant at entry (the unknown `v0`,
the value at `p` there, and the frame) and walks the body's step.

A wrong invariant (one that the body does not keep) is rejected: the walk of the step fails.
-/

namespace SepAuto.LoopInv
open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

structure Locals where
  i : BitVec 32
  deriving Inhabited

inductive Exit where
  | ret
  | brk
  | rep

def again : Exit → Bool
  | .rep => true
  | _ => false

/-- `while (i < n) : (i += 1) { *p += 1; }` -/
def fill.loop (p : Ptr) (n : BitVec 32) : MM Locals Exit := do
  let i ← pure ((← get).i)
  if Zig.lt false i n then (do
    let v ← Zig.load (BitVec 64) 8 p
    let v' ← Zig.add false v (1 : BitVec 64)
    Zig.store (α := BitVec 64) 8 p v'
    let i' ← Zig.add false ((← get).i) (1 : BitVec 32)
    modify (fun s => { s with i := i' })
    pure .rep)
  else (do
    pure .brk)

/-- The invariant: `*p` went up by `i` since the entry, where it was `v0`. -/
@[fsym_inv] def fill.loop.inv (p : Ptr) (n : BitVec 32) (v0 : BitVec 64) (s : Locals) : FAssn :=
  ⟪s.i.toNat ≤ n.toNat ∧ v0.toNat + n.toNat < 2 ^ 64⟫ ⋆
    (FAssn.ex fun v : BitVec 64 => ⟪v.toNat = v0.toNat + s.i.toNat⟫ ⋆ up (pts p 8 v))

/-- The iterations left. -/
@[fsym_inv] def fill.loop.meas (n : BitVec 32) (s : Locals) : Nat :=
  n.toNat - s.i.toNat

/-- At the exit `*p` went up by `n`. -/
@[fsym_inv] def fill.loop.post (p : Ptr) (n : BitVec 32) (v0 : BitVec 64) (r : Exit × Locals) :
    FAssn :=
  ⟪r.1 = .brk⟫ ⋆ (FAssn.ex fun v : BitVec 64 => ⟪v.toNat = v0.toNat + n.toNat⟫ ⋆ up (pts p 8 v))

def fill (p : Ptr) (n : BitVec 32) : MemM Unit := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (fill.loop p n) again) : MM Locals Exit) with
    | .brk => (do
      pure .ret)
    | e => pure e) : MM Locals Exit).run' (default : Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

/-- **The loop by its registered invariant**: no loop lemma, no `fsym` argument; the frame `R`
stays outside the loop. -/
theorem fill_total (R : FAssn) (p : Ptr) (n : BitVec 32) (v : BitVec 64)
    (hfit : v.toNat + n.toNat < 2 ^ 64) :
    FTotalTriple (up (pts p 8 v) ⋆ R) (fill p n)
      (fun _ => (FAssn.ex fun w : BitVec 64 => ⟪w.toNat = v.toNat + n.toNat⟫ ⋆ up (pts p 8 w)) ⋆ R) := by
  unfold fill
  fsym

/-- The same loop in the partial logic (`FTriple.loop`: the measure is not used). -/
theorem fill_partial (p : Ptr) (n : BitVec 32) (v : BitVec 64) (hfit : v.toNat + n.toNat < 2 ^ 64) :
    FTriple (up (pts p 8 v)) (fill p n)
      (fun _ => FAssn.ex fun w : BitVec 64 => ⟪w.toNat = v.toNat + n.toNat⟫ ⋆ up (pts p 8 w)) := by
  unfold fill
  fsym

/-- The same loop in a thread (`FTTotalTriple.loop_measure`: the body's steps with the locality
of their commands). -/
theorem fill_thread (p : Ptr) (n : BitVec 32) (v : BitVec 64) (hfit : v.toNat + n.toNat < 2 ^ 64) :
    FTTotalTriple (up (pts p 8 v)) (fill p n)
      (fun _ => FAssn.ex fun w : BitVec 64 => ⟪w.toNat = v.toNat + n.toNat⟫ ⋆ up (pts p 8 w)) := by
  unfold fill
  fsym

/-- The same body under another name … -/
def bad.loop (p : Ptr) (n : BitVec 32) : MM Locals Exit := do
  let i ← pure ((← get).i)
  if Zig.lt false i n then (do
    let v ← Zig.load (BitVec 64) 8 p
    let v' ← Zig.add false v (1 : BitVec 64)
    Zig.store (α := BitVec 64) 8 p v'
    let i' ← Zig.add false ((← get).i) (1 : BitVec 32)
    modify (fun s => { s with i := i' })
    pure .rep)
  else (do
    pure .brk)

/-- … whose registered invariant is wrong: it holds at the entry, but the step does not keep it
(`*p` goes up by 1 per iteration, not by 2). -/
@[fsym_inv] def bad.loop.inv (p : Ptr) (n : BitVec 32) (v0 : BitVec 64) (s : Locals) : FAssn :=
  ⟪s.i.toNat ≤ n.toNat ∧ v0.toNat + 2 * n.toNat < 2 ^ 64⟫ ⋆
    (FAssn.ex fun v : BitVec 64 => ⟪v.toNat = v0.toNat + 2 * s.i.toNat⟫ ⋆ up (pts p 8 v))

@[fsym_inv] def bad.loop.meas (n : BitVec 32) (s : Locals) : Nat :=
  n.toNat - s.i.toNat

@[fsym_inv] def bad.loop.post (p : Ptr) (n : BitVec 32) (v0 : BitVec 64) (r : Exit × Locals) :
    FAssn :=
  ⟪r.1 = .brk⟫ ⋆ (FAssn.ex fun v : BitVec 64 => ⟪v.toNat = v0.toNat + 2 * n.toNat⟫ ⋆ up (pts p 8 v))

def bad (p : Ptr) (n : BitVec 32) : MemM Unit := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (bad.loop p n) again) : MM Locals Exit) with
    | .brk => (do
      pure .ret)
    | e => pure e) : MM Locals Exit).run' (default : Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

section
open Lean Meta Elab Tactic Zig.Full.Auto.Report

set_option linter.unusedVariables false in
/-- **A wrong invariant is rejected**: `fsym` does not prove the (false) claim of `bad` with it.
It applies the loop rule (the invariant holds at the entry) and leaves goals: the walk of the step
does not reach the invariant at the next iteration. The goal is inspected, never admitted. -/
example (p : Ptr) (n : BitVec 32) (v : BitVec 64) (hfit : v.toNat + 2 * n.toNat < 2 ^ 64) :
    True := by
  run_tac withMainContext do
    let ty ← elabTerm (← `(FTotalTriple (up (pts p 8 v)) (bad p n) (fun _ =>
      FAssn.ex fun w : BitVec 64 => ⟪w.toNat = v.toNat + 2 * n.toNat⟫ ⋆ up (pts p 8 w)))) none
    let g ← mkFreshExprSyntheticOpaqueMVar (← deltaExpand ty (· == ``bad))
    let (gs, report) ← runReport g.mvarId!
    unless !gs.isEmpty && report.residuals.all (·.origin.reason != "invariant_not_established") &&
        ((← instantiateMVars g).find? (·.isConstOf ``FTotalTriple.loop_measure)).isSome do
      throwError "the wrong invariant was not rejected by the walk of its step: {line report}"
  trivial

/-- A body whose invariant does not hold at the entry (`*p` would be `v0 + 1` there). -/
def early.loop (p : Ptr) (n : BitVec 32) : MM Locals Exit := bad.loop p n

@[fsym_inv] def early.loop.inv (p : Ptr) (n : BitVec 32) (v0 : BitVec 64) (s : Locals) : FAssn :=
  ⟪s.i.toNat ≤ n.toNat⟫ ⋆ (FAssn.ex fun v : BitVec 64 => ⟪v.toNat = v0.toNat + s.i.toNat + 1⟫ ⋆ up (pts p 8 v))

@[fsym_inv] def early.loop.meas (n : BitVec 32) (s : Locals) : Nat :=
  n.toNat - s.i.toNat

/-- **An invariant that does not hold at the entry** is reported as such: one residual, the loop
with `invariant_not_established` at `loop_entry`. -/
example (p : Ptr) (n : BitVec 32) (v : BitVec 64) : True := by
  run_tac withMainContext do
    let ty ← elabTerm (← `(FTotalTriple (up (pts p 8 v))
      ((Zig.loop (early.loop p n) again).run { i := 0 }) (fun _ => up (pts p 8 v)))) none
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let (gs, report) ← runReport g.mvarId!
    unless gs.length == 1 && report.residuals.size == 1 &&
        report.residuals[0]!.origin.reason == "invariant_not_established" &&
        report.residuals[0]!.origin.condition == "loop_entry" do
      throwError "the entry was not reported: {line report}"
  trivial

end

/-- The loop concurrently: a body of `CM` over the locals `Nat` that counts down, its invariant
for every target (`CTriple.loop`) and no registered exit post (the invariant at an exit). -/
def cdown {Tgt : Type} : CM Tgt Nat Bool := do
  callMC Zig.tick
  let n ← get
  if n == 0 then pure false
  else
    set (n - 1)
    pure true

set_option linter.unusedVariables false in
@[fsym_inv] def cdown.inv (Tgt : Type) (s : Nat) : FAssn := plain

theorem cdown_loop {Tgt : Type} (R : FAssn) (s : Nat) :
    CTriple (Tgt := Tgt) (R ⋆ plain) ((Zig.loop cdown fun b : Bool => b).run s) (fun _ => R ⋆ plain) := by
  fsym

/-- Registrations that are not a loop body's invariant are rejected when they are added. -/
def notALoop : Nat := 0

/-- error: @[fsym_inv] SepAuto.LoopInv.notALoop.invariant: its name does not end in `inv`, `meas` or `post`; expected the definition `B.inv`, `B.meas` or `B.post` of a loop body `B` -/
#guard_msgs in
@[fsym_inv] def notALoop.invariant (s : Locals) : FAssn := emp

/-- error: @[fsym_inv] SepAuto.LoopInv.fill.loop.post2: its name does not end in `inv`, `meas` or `post`; expected the definition `B.inv`, `B.meas` or `B.post` of a loop body `B` -/
#guard_msgs in
@[fsym_inv] def fill.loop.post2 (r : Exit × Locals) : FAssn := emp

set_option linter.unusedVariables false in
/-- error: @[fsym_inv] SepAuto.LoopInv.early.loop.post: its last parameter is not of type Exit × Locals; expected the definition `B.inv`, `B.meas` or `B.post` of a loop body `B` -/
#guard_msgs in
@[fsym_inv] def early.loop.post (s : Locals) : FAssn := emp

end SepAuto.LoopInv
