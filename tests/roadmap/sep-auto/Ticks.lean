import ZigLean.Sep.Full.AutoAll

/-!
# Step ticks in the existing execution modes

Handwritten programs in the shapes emitted for memory and concurrent functions. Every loop
body ticks, including the final exit. Plain-mode proofs preserve arbitrary framed resources
and claim no cost bound; the one-credit proof checks the metered rule. Loop proofs provide
only the invariant and measure; `fsym` walks each body. Total recursion waits on
engine ledger #recursive-group-total; no per-program induction stands in for that rule.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Zig.Full.Auto

namespace SepAuto.Ticks

/-- Two steps in plain mode: each receipt may be dropped. -/
def two : MemM Unit := do
  Zig.tick
  Zig.tick

theorem two_total (R : FAssn) :
    FTotalTriple (R ⋆ plain) two (fun _ => R ⋆ plain) := by
  unfold two
  fsym

theorem two_thread (R : FAssn) :
    FTTotalTriple (R ⋆ plain) two (fun _ => R ⋆ plain) := by
  unfold two
  fsym

theorem one_credit : FTotalTriple (credits 1) Zig.tick (fun _ => spent 1) := by
  fsym

theorem two_concurrent {Tgt : Type} (R : FAssn) :
    CTriple (Tgt := Tgt) (R ⋆ plain) (ConcM.liftMem two) (fun _ => R ⋆ plain) := by
  unfold two
  fsym

/-- A generated-style body: the exit at zero also ticks. -/
def body : MM Nat Bool := do
  callM Zig.tick
  let n ← get
  if n == 0 then pure false
  else
    set (n - 1)
    pure true

theorem body_thread (R : FAssn) (s : Nat) :
    FTTotalTriple (R ⋆ plain) (body.run s)
      (fun r => if r.1 then ⟪r.2 < s⟫ ⋆ (R ⋆ plain)
        else ⟪r.1 = false ∧ r.2 = 0⟫ ⋆ (R ⋆ plain)) := by
  unfold body
  fsym

theorem loop_thread (R : FAssn) (s : Nat) :
    FTTotalTriple (R ⋆ plain) ((Zig.loop body fun b : Bool => b).run s)
      (fun r => ⟪r.1 = false ∧ r.2 = 0⟫ ⋆ (R ⋆ plain)) :=
  FTTotalTriple.loop_measure (fun _ => R ⋆ plain) id _ (body_thread R) s

theorem loop_total (R : FAssn) (s : Nat) :
    FTotalTriple (R ⋆ plain) ((Zig.loop body fun b : Bool => b).run s)
      (fun r => ⟪r.1 = false ∧ r.2 = 0⟫ ⋆ (R ⋆ plain)) :=
  (loop_thread R s).toFTotalTriple

/-- The concurrent body uses the same memory tick through `callMC`. -/
def cbody {Tgt : Type} : CM Tgt Nat Bool := do
  callMC Zig.tick
  let n ← get
  if n == 0 then pure false
  else
    set (n - 1)
    pure true

theorem cbody_spec {Tgt : Type} (R : FAssn) (s : Nat) :
    CTriple (Tgt := Tgt) (R ⋆ plain) (cbody.run s)
      (fun r => if r.1 then R ⋆ plain else R ⋆ plain) := by
  unfold cbody
  fsym

theorem cloop_spec {Tgt : Type} (R : FAssn) (s : Nat) :
    CTriple (Tgt := Tgt) (R ⋆ plain) ((Zig.loop cbody fun b : Bool => b).run s)
      (fun _ => R ⋆ plain) :=
  CTriple.loop (fun _ => R ⋆ plain) (fun _ => R ⋆ plain) (cbody_spec R) s

attribute [local irreducible] Proto.WP

/-- Straight-line ticks are memory segments of every partial protocol. -/
theorem two_wp {Tgt γ : Type} (P : Proto Tgt γ) (hpart : P.Partial) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (own : ThreadId → Res) (rO : Res)
    (R : FAssn) (ho : FOwned own rO m) (hc : m.current = t)
    (htl : t < m.threads.size) (hp : (R ⋆ plain) (own t)) :
    P.WP t (ConcM.liftMem two) (fun _ _ m' _ => m'.current = t) G m d := by
  unfold two
  fsym

/-- The WP backend derives its memory segment from the same thread loop rule. -/
theorem loop_wp {Tgt γ : Type} (P : Proto Tgt γ) (hpart : P.Partial) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (own : ThreadId → Res) (rO : Res)
    (R : FAssn) (s : Nat) (ho : FOwned own rO m) (hc : m.current = t)
    (htl : t < m.threads.size) (hp : (R ⋆ plain) (own t)) :
    P.WP t (ConcM.liftMem ((Zig.loop body fun b : Bool => b).run s))
      (fun r _ _ _ => r.1 = false ∧ r.2 = 0) G m d := by
  fsym [loop_thread]

end SepAuto.Ticks
