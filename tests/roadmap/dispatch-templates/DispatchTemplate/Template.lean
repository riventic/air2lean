import ZigLean.Sep.Full.Loop
import ZigLean.Sep.Full.Auto

/-!
# Dispatch loops in the full-state logic: small machines

`mach` has the shape the emitter gives a labelled `switch` (`f.loopN` reads `dispatchValueN`,
stores the next selector on `.dispatchN`, `f.againN` repeats only on `.dispatchN`). Every machine
here is an instance of the one dispatch-loop rule `FTotalTriple.loop_dispatch`
(`ZigLean/Sep/Full/Loop.lean`): it supplies the selector, the state-indexed invariant, the
consumed data and the state rank with a bound `B` above every rank (the measure
`B * data + rank` is lexicographic over the two), and proves one body run by a case split on the
selector and `fsym`.

Negative checks: a wrong invariant (`badInv`, `count` entered without work left) and a rank that
does not order the states (`flatRank`) are not established by the walk, while the same walk proves
the other states (positive controls). `word` has a `BitVec 8` selector: no case split, `fsym`
splits on the selector's tests, the rank is the distance to the returning state and the
invariant excludes the selectors outside `0, 1, 2`.
-/

namespace DispatchTemplateTest
open Zig Zig.Full Zig.Full.FAssn

inductive Phase where
  | idle | count | done
  deriving DecidableEq, Inhabited

structure machLocals where
  n : Nat
  acc : Nat
  dispatchValue3 : Phase
  deriving Inhabited

inductive machExit where
  | ret (v : Nat)
  | dispatch3 (v : Phase)

def mach.again3 : machExit → Bool
  | .dispatch3 _ => true
  | _ => false

/-- `idle` moves to `count` (lower rank) or `done`; `count` consumes one unit, back to `idle`. -/
def mach.loop3 : MM machLocals machExit := do
  let dispatchValue := (← get).dispatchValue3
  let dispatchExit ← (do
    match dispatchValue with
    | .idle => if (← get).n = 0 then pure (.dispatch3 .done) else pure (.dispatch3 .count)
    | .count => do
      modify fun s => { s with n := s.n - 1, acc := s.acc + 1 }
      pure (.dispatch3 .idle)
    | .done => pure (.ret (← get).acc) : MM machLocals machExit)
  match dispatchExit with
  | .dispatch3 dispatchValue => do
    modify fun s => { s with dispatchValue3 := dispatchValue }
    pure dispatchExit
  | _ => pure dispatchExit

def rank : Phase → Nat
  | .done => 0 | .count => 1 | .idle => 2

/-- A rank that does not order the states: a transition that consumes nothing does not lower it. -/
def flatRank (_ : Phase) : Nat := 0

/-- The state-indexed invariant: `count` is entered only with work left. -/
def inv (N : Nat) : Phase → machLocals → FAssn
  | .idle, s => ⟪s.acc + s.n = N⟫
  | .count, s => ⟪s.acc + s.n = N ∧ 0 < s.n⟫
  | .done, s => ⟪s.acc = N⟫

/-- A wrong invariant: `count` may be entered without work left. -/
def badInv (N : Nat) : Phase → machLocals → FAssn
  | .idle, s => ⟪s.acc + s.n = N⟫
  | .count, s => ⟪s.acc + s.n = N⟫
  | .done, s => ⟪s.acc = N⟫

def post (N : Nat) (r : machExit × machLocals) : FAssn := ⟪r.1 = .ret N⟫

-- The ranks of the states are arithmetic facts for `fsym`.
attribute [local fsym_arith] rank flatRank

/-- The step premise of `FTotalTriple.loop_dispatch` for `mach` (data: the units left; ranks below 3). -/
abbrev Step (J : Phase → machLocals → FAssn) (R : Phase → Nat) (N : Nat) (s : machLocals) : Prop :=
  FTotalTriple (J s.dispatchValue3 s) (mach.loop3.run s)
    (fun r => if mach.again3 r.1 then
        ⟪3 * r.2.n + R r.2.dispatchValue3 < 3 * s.n + R s.dispatchValue3⟫ ⋆ J r.2.dispatchValue3 r.2
      else post N r)

theorem mach_step (N : Nat) (s : machLocals) : Step (inv N) rank N s := by
  obtain ⟨n, acc, k⟩ := s
  unfold Step mach.loop3 post
  cases k <;> fsym

theorem mach_total (N : Nat) :
    FTotalTriple emp ((Zig.loop mach.loop3 mach.again3).run ⟨N, 0, .idle⟩) (fun r => ⟪r.1 = .ret N⟫) :=
  (FTotalTriple.loop_dispatch (fun s : machLocals => s.dispatchValue3) (inv N) (·.n) rank 3 (post N) (mach_step N) _).pre
    fun _ h => ⟨by simp, h⟩

/-! ## A wrong invariant or rank is not established -/

-- `badInv`: the walk fails at `count` (it may be entered with `n = 0`: the measure goal
-- `3 * (n - 1) + 2 < 3 * n + 1` is left) ...
example : True := by
  fail_if_success
    (have : ∀ N n acc, Step (badInv N) rank N ⟨n, acc, .count⟩ := by
      intro N n acc; unfold Step mach.loop3 post; fsym; done)
  trivial

-- ... and proves the other states (positive controls).
example (N n acc : Nat) : Step (badInv N) rank N ⟨n, acc, .idle⟩ := by
  unfold Step mach.loop3 post; fsym
example (N n acc : Nat) : Step (badInv N) rank N ⟨n, acc, .done⟩ := by
  unfold Step mach.loop3 post; fsym

-- `flatRank`: the walk fails at `idle` (`idle → count` and `idle → done` consume nothing and do
-- not lower the rank) ...
example : True := by
  fail_if_success
    (have : ∀ N n acc, Step (inv N) flatRank N ⟨n, acc, .idle⟩ := by
      intro N n acc; unfold Step mach.loop3 post; fsym; done)
  trivial

-- ... and proves the consuming state.
example (N n acc : Nat) : Step (inv N) flatRank N ⟨n, acc, .count⟩ := by
  unfold Step mach.loop3 post; fsym

/-! ## An integer selector -/

structure wordLocals where
  dispatchValue7 : BitVec 8
  deriving Inhabited

inductive wordExit where
  | ret (v : BitVec 8)
  | dispatch7 (v : BitVec 8)

def word.again7 : wordExit → Bool
  | .dispatch7 _ => true
  | _ => false

/-- `0 → 1 → 2 → return 42`; other selectors return 9. -/
def word.loop7 : MM wordLocals wordExit := do
  let dispatchValue := (← get).dispatchValue7
  let dispatchExit ← (do
    if dispatchValue = 0 then pure (.dispatch7 1)
    else if dispatchValue = 1 then pure (.dispatch7 2)
    else if dispatchValue = 2 then pure (.ret 42)
    else pure (.ret 9) : MM wordLocals wordExit)
  match dispatchExit with
  | .dispatch7 dispatchValue => do
    modify fun s => { s with dispatchValue7 := dispatchValue }
    pure dispatchExit
  | _ => pure dispatchExit

/-- The selector stays in `0, 1, 2`. -/
def wordInv (k : BitVec 8) (_ : wordLocals) : FAssn := ⟪k.toNat ≤ 2⟫

/-- The distance to the returning state `2`. -/
def wordRank (k : BitVec 8) : Nat := 2 - k.toNat

theorem word_step (s : wordLocals) :
    FTotalTriple (wordInv s.dispatchValue7 s) (word.loop7.run s)
      (fun r => if word.again7 r.1 then
          ⟪3 * 0 + wordRank r.2.dispatchValue7 < 3 * 0 + wordRank s.dispatchValue7⟫ ⋆
            wordInv r.2.dispatchValue7 r.2
        else ⟪r.1 = wordExit.ret 42⟫) := by
  obtain ⟨d⟩ := s
  unfold word.loop7 wordRank
  fsym

theorem word_total :
    FTotalTriple emp ((Zig.loop word.loop7 word.again7).run ⟨0⟩) (fun r => ⟪r.1 = .ret 42⟫) :=
  (FTotalTriple.loop_dispatch (fun s : wordLocals => s.dispatchValue7) wordInv (fun _ => 0) wordRank 3
    (fun r => ⟪r.1 = wordExit.ret 42⟫) word_step _).pre fun _ h => ⟨by decide, h⟩

end DispatchTemplateTest

-- Only the standard axioms.
/-- info: 'DispatchTemplateTest.mach_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DispatchTemplateTest.mach_total

/-- info: 'DispatchTemplateTest.word_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DispatchTemplateTest.word_total
