import ZigLean.Sep.Full.AutoAll
import ZigLean.Sep.Full.Cost

/-!
# Loops with a second registered invariant, for the credit mode (`@[fsym_inv]`, P09)

A loop body `B` registers one invariant per mode: `B.inv`/`B.meas`/`B.post` for the plain mode,
and `B.credits.inv`/`B.credits.post` for a walk that pays its steps with credits (the invariant
at its exact count `n`, the body runs left before the last one). `fsym` reads the mode off the
state at the loop: credits and no plain mode is the credit mode, and it then applies the counted
loop rule (`FTotalTriple.loop_exact`, `CTriple.loop_exact`), which adds `credits (n + 1)` and
returns `spent (n + 1)`.

* `count_total`, `count_exact`: the same function and the same body, proved in the plain mode and
  with its exact step count, each by `fsym` alone.
* A wrong count is rejected: an invariant that counts two per body run (the step does not keep
  it), and a claim with one credit too few (the invariant has no plan at the entry).
* A credit walk at a body that registers only its plain-mode invariant is an error: the
  plain-mode invariant is never taken for it.
* The registration's checks (`checkLoopInv`): no measure in the credit mode, and an invariant
  that ends in its count.
-/

namespace SepAuto.LoopCredits
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

/-- `while (i < n) : (i += 1) { *p += 1; }`, each body run a step. -/
def count.loop (p : Ptr) (n : BitVec 32) : MM Locals Exit := do
  Zig.callM Zig.tick
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

/-- The plain-mode invariant: `*p` went up by `i` since the entry, where it was `v0`. -/
@[fsym_inv] def count.loop.inv (p : Ptr) (n : BitVec 32) (v0 : BitVec 64) (s : Locals) : FAssn :=
  ⟪s.i.toNat ≤ n.toNat ∧ v0.toNat + n.toNat < 2 ^ 64⟫ ⋆
    (FAssn.ex fun v : BitVec 64 => ⟪v.toNat = v0.toNat + s.i.toNat⟫ ⋆ up (pts p 8 v)) ⋆ plain

@[fsym_inv] def count.loop.meas (n : BitVec 32) (s : Locals) : Nat :=
  n.toNat - s.i.toNat

@[fsym_inv] def count.loop.post (p : Ptr) (n : BitVec 32) (v0 : BitVec 64) (r : Exit × Locals) :
    FAssn :=
  ⟪r.1 = .brk⟫ ⋆ (FAssn.ex fun v : BitVec 64 => ⟪v.toNat = v0.toNat + n.toNat⟫ ⋆ up (pts p 8 v)) ⋆
    plain

/-- The credit-mode invariant: the same without the plain mode, at the exact count `k` of the
body runs left before the last one (the iterations left). -/
@[fsym_inv] def count.loop.credits.inv (p : Ptr) (n : BitVec 32) (v0 : BitVec 64) (s : Locals)
    (k : Nat) : FAssn :=
  ⟪s.i.toNat ≤ n.toNat ∧ v0.toNat + n.toNat < 2 ^ 64 ∧ k = n.toNat - s.i.toNat⟫ ⋆
    (FAssn.ex fun v : BitVec 64 => ⟪v.toNat = v0.toNat + s.i.toNat⟫ ⋆ up (pts p 8 v))

@[fsym_inv] def count.loop.credits.post (p : Ptr) (n : BitVec 32) (v0 : BitVec 64)
    (r : Exit × Locals) : FAssn :=
  ⟪r.1 = .brk⟫ ⋆ (FAssn.ex fun v : BitVec 64 => ⟪v.toNat = v0.toNat + n.toNat⟫ ⋆ up (pts p 8 v))

def count (p : Ptr) (n : BitVec 32) : MemM Unit := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (count.loop p n) again) : MM Locals Exit) with
    | .brk => (do
      pure .ret)
    | e => pure e) : MM Locals Exit).run' (default : Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

/-- **The plain mode**: the state holds `plain`, so `fsym` takes `count.loop.inv`. -/
theorem count_total (R : FAssn) (p : Ptr) (n : BitVec 32) (v : BitVec 64)
    (hfit : v.toNat + n.toNat < 2 ^ 64) :
    FTotalTriple ((up (pts p 8 v) ⋆ R) ⋆ plain) (count p n)
      (fun _ => ((FAssn.ex fun w : BitVec 64 => ⟪w.toNat = v.toNat + n.toNat⟫ ⋆ up (pts p 8 w)) ⋆ R) ⋆
        plain) := by
  unfold count
  fsym

/-- **The credit mode**: the state holds credits and no plain mode, so `fsym` takes
`count.loop.credits.inv` and the counted loop rule. The function runs exactly `n + 1` steps (one
per iteration and the final test): no loop lemma, no `fsym` argument, and the frame `R` stays
outside the loop. -/
theorem count_exact (R : FAssn) (p : Ptr) (n : BitVec 32) (v : BitVec 64)
    (hfit : v.toNat + n.toNat < 2 ^ 64) :
    FTotalTriple ((up (pts p 8 v) ⋆ R) ⋆ credits (n.toNat + 1)) (count p n)
      (fun _ => ((FAssn.ex fun w : BitVec 64 => ⟪w.toNat = v.toNat + n.toNat⟫ ⋆ up (pts p 8 w)) ⋆ R) ⋆
        spent (n.toNat + 1)) := by
  unfold count
  fsym

/-- The counted statement is tight: with the receipts it returns, no proof pays the same run with
fewer credits (`FTotalTriple.not_fewer_credits`). -/
theorem count_not_within (p : Ptr) (n : BitVec 32) (v : BitVec 64)
    (hfit : v.toNat + n.toNat < 2 ^ 64) {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hp : (up (pts p 8 v) ⋆ FAssn.emp) r) (hs : m.FSeq) (hc : CreditFree r rF)
    (Q : Unit → FAssn) :
    ¬ FTotalTriple ((up (pts p 8 v) ⋆ FAssn.emp) ⋆ credits n.toNat) (count p n) Q :=
  FTotalTriple.not_fewer_credits (count_exact FAssn.emp p n v hfit) (Nat.lt_succ_self _) hh hp hs hc

/-- The loop of a concurrent function (`CTriple.loop_exact`): a body of `CM` that counts up to
`n`, its credit-mode invariant for every target. -/
def ccount.loop (Tgt : Type) (n : BitVec 32) : CM Tgt Locals Exit := do
  Zig.callMC Zig.tick
  let i ← pure ((← get).i)
  if Zig.lt false i n then (do
    let i' ← Zig.add false ((← get).i) (1 : BitVec 32)
    modify (fun s => { s with i := i' })
    pure .rep)
  else (do
    pure .brk)

set_option linter.unusedVariables false in
@[fsym_inv] def ccount.loop.credits.inv (Tgt : Type) (n : BitVec 32) (s : Locals) (k : Nat) :
    FAssn :=
  ⟪s.i.toNat ≤ n.toNat ∧ k = n.toNat - s.i.toNat⟫

set_option linter.unusedVariables false in
@[fsym_inv] def ccount.loop.credits.post (Tgt : Type) (n : BitVec 32) (r : Exit × Locals) : FAssn :=
  ⟪r.1 = .brk ∧ r.2.i.toNat = n.toNat⟫

theorem ccount_exact {Tgt : Type} (R : FAssn) (n : BitVec 32) :
    CTriple (Tgt := Tgt) (R ⋆ credits (n.toNat + 1))
      ((Zig.loop (ccount.loop Tgt n) again).run { i := 0 })
      (fun r => ⟪r.2.i.toNat = n.toNat⟫ ⋆ (R ⋆ spent (n.toNat + 1))) := by
  fsym

/-- The same body under another name … -/
def bad.loop (p : Ptr) (n : BitVec 32) : MM Locals Exit := count.loop p n

/-- … whose credit-mode invariant counts wrong: two per iteration. It holds at the entry with
`2 * n + 1` credits, but a body run lowers the iterations left by one, not the count by one. -/
@[fsym_inv] def bad.loop.credits.inv (p : Ptr) (n : BitVec 32) (v0 : BitVec 64) (s : Locals)
    (k : Nat) : FAssn :=
  ⟪s.i.toNat ≤ n.toNat ∧ v0.toNat + n.toNat < 2 ^ 64 ∧ k = 2 * (n.toNat - s.i.toNat)⟫ ⋆
    (FAssn.ex fun v : BitVec 64 => ⟪v.toNat = v0.toNat + s.i.toNat⟫ ⋆ up (pts p 8 v))

@[fsym_inv] def bad.loop.credits.post (p : Ptr) (n : BitVec 32) (v0 : BitVec 64)
    (r : Exit × Locals) : FAssn :=
  ⟪r.1 = .brk⟫ ⋆ (FAssn.ex fun v : BitVec 64 => ⟪v.toNat = v0.toNat + n.toNat⟫ ⋆ up (pts p 8 v))

/-- A body that registers only its plain-mode invariant. -/
def plainOnly.loop (p : Ptr) (n : BitVec 32) : MM Locals Exit := count.loop p n

@[fsym_inv] def plainOnly.loop.inv (p : Ptr) (n : BitVec 32) (v0 : BitVec 64) (s : Locals) : FAssn :=
  count.loop.inv p n v0 s

@[fsym_inv] def plainOnly.loop.meas (n : BitVec 32) (s : Locals) : Nat :=
  n.toNat - s.i.toNat

/-- Definitions whose registration is rejected (`checkLoopInv`, below). -/
def count.loop.credits.meas (n : BitVec 32) (s : Locals) : Nat :=
  n.toNat - s.i.toNat

def plainOnly.loop.credits.inv (p : Ptr) (n : BitVec 32) (v0 : BitVec 64) (s : Locals) : FAssn :=
  count.loop.inv p n v0 s

section
open Lean Meta Elab Tactic Zig.Full.Auto.Report
-- The claims below are quoted inside `run_tac`: unhygienic, so they name the example's variables.
set_option hygiene false

set_option linter.unusedVariables false in
/-- **A wrong count is rejected**: with the invariant that counts two per body run, `fsym` does
not prove the (false) claim that the loop runs `2 * n + 1` steps. The invariant holds at the
entry, and the walk of the counted rule's step leaves goals. The goal is inspected, never
admitted. -/
example (p : Ptr) (n : BitVec 32) (v : BitVec 64) (hfit : v.toNat + n.toNat < 2 ^ 64) :
    True := by
  run_tac withMainContext do
    let ty ← elabTerm (← `(FTotalTriple (up (pts p 8 v) ⋆ credits (2 * n.toNat + 1))
      ((Zig.loop (bad.loop p n) again).run { i := 0 })
      (fun _ => (FAssn.ex fun w : BitVec 64 => up (pts p 8 w)) ⋆ spent (2 * n.toNat + 1)))) none
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let (gs, report) ← runReport g.mvarId!
    if gs.isEmpty then
      throwError "the wrong count was not rejected: {line report}"
    if report.residuals.any (·.origin.reason == "invariant_not_established") then
      throwError "the wrong count was rejected at the entry, not by the walk of its step: {line report}"
  trivial

set_option linter.unusedVariables false in
/-- **One credit too few is rejected**: with the right invariant, `n` credits do not pay the loop
(the counted rule needs `k + 1` credits at the count `k = n`): `fsym` leaves the goal. -/
example (p : Ptr) (n : BitVec 32) (v : BitVec 64) (hfit : v.toNat + n.toNat < 2 ^ 64) :
    True := by
  run_tac withMainContext do
    let ty ← elabTerm (← `(FTotalTriple (up (pts p 8 v) ⋆ credits n.toNat)
      ((Zig.loop (count.loop p n) again).run { i := 0 })
      (fun _ => (FAssn.ex fun w : BitVec 64 => up (pts p 8 w)) ⋆ spent n.toNat))) none
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let (gs, report) ← runReport g.mvarId!
    if gs.isEmpty then
      throwError "too few credits were not rejected: {line report}"
  trivial

set_option linter.unusedVariables false in
/-- **A credit walk never takes a plain-mode invariant**: at a body that registers only `B.inv`,
`fsym` stops with an error that says so (no fallback). -/
example (p : Ptr) (n : BitVec 32) (v : BitVec 64) (hfit : v.toNat + n.toNat < 2 ^ 64) :
    True := by
  run_tac withMainContext do
    let ty ← elabTerm (← `(FTotalTriple (up (pts p 8 v) ⋆ credits (n.toNat + 1))
      ((Zig.loop (plainOnly.loop p n) again).run { i := 0 })
      (fun _ => (FAssn.ex fun w : BitVec 64 => up (pts p 8 w)) ⋆ spent (n.toNat + 1)))) none
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let said ← try
        discard <| runReport g.mvarId!
        pure false
      catch ex =>
        pure (((← ex.toMessageData.toString).splitOn "registers only its plain-mode invariant").length > 1)
    unless said do
      throwError "a credit walk at a loop with only a plain-mode invariant was not refused"
  trivial

/-- **The registration's checks**: the credit mode has no measure, and its invariant ends in its
exact count. -/
example : True := by
  run_tac do
    for decl in [``count.loop.credits.meas, ``plainOnly.loop.credits.inv] do
      let refused ← try
          checkLoopInv decl
          pure false
        catch _ => pure true
      unless refused do
        throwError "@[fsym_inv] would register {decl}"
    -- (and the credit-mode definitions above are what it accepts)
    checkLoopInv ``count.loop.credits.inv
    checkLoopInv ``count.loop.credits.post
  trivial

end

end SepAuto.LoopCredits
