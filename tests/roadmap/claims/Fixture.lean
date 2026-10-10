import ZigLean.Sep.Witness
import ZigLean.Sep.Bounded
import ZigLean.Conc.Own
import ZigLean.Conc.Total

/-!
Claim-strength fixtures. `scripts/claims.py` classifies each theorem from the statement
structure that `tools/Assurance.lean` extracts from its kernel type. No name or comment here is
read by the classifier. `diverge`, `ret`, `boom` and `countdown` stand in for generated roots.
-/

open Zig Assn

namespace ClaimFixture

def diverge : MemM Unit := fun _ => ExceptT.mk none

def ret (v : Nat) : MemM Nat := pure v

def boom : MemM Unit := throw Error.panic

/-- Partial correctness holds vacuously for divergence, even with a false postcondition. -/
theorem diverge_partial (P : Assn) : Triple P diverge (fun _ _ => False) := by
  intro m hP hF hd hm hp hs
  trivial

nonvacuity_witness diverge_partial :=
  ⟨emp, {}, Heap.empty, Heap.empty, Heap.disjoint_empty _, Mem.heap_default_split, rfl,
    Mem.seq_default, trivial⟩

/-- Vacuity guard: with any admissible input, divergence has no total triple. -/
theorem diverge_not_total (P : Assn) (Q : Unit → Assn) (m : Mem) (hP hF : Heap)
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq) :
    ¬ TotalTriple P diverge Q := by
  intro ht
  obtain ⟨v, m', hQ, hr, _⟩ := ht m hP hF hd hm hp hs
  change none = some (Except.ok (v, m')) at hr
  cases hr

theorem ret_total (P : Assn) (v : Nat) : TotalTriple P (ret v) (fun _ => P) :=
  TotalTriple.ret (Q := fun _ => P) v

nonvacuity_witness ret_total :=
  ⟨emp, 0, {}, Heap.empty, Heap.empty, Heap.disjoint_empty _, Mem.heap_default_split, rfl,
    Mem.seq_default, trivial⟩

theorem ret_returns (P : Assn) (v : Nat) : Returns P (ret v) :=
  (ret_total P v).returns

nonvacuity_witness ret_returns :=
  ⟨emp, 0, {}, Heap.empty, Heap.empty, Heap.disjoint_empty _, Mem.heap_default_split, rfl,
    Mem.seq_default, trivial⟩

theorem ret_partial (P : Assn) (v : Nat) : Triple P (ret v) (fun _ => P) :=
  (ret_total P v).toPartial

nonvacuity_witness ret_partial :=
  ⟨emp, 0, {}, Heap.empty, Heap.empty, Heap.disjoint_empty _, Mem.heap_default_split, rfl,
    Mem.seq_default, trivial⟩

liveness_witness ret_partial :=
  ⟨emp, 0, {}, Heap.empty, Heap.empty, Heap.disjoint_empty _, Mem.heap_default_split, rfl,
    Mem.seq_default, _, rfl⟩

/-- An exact successful run is a guaranteed return with an exact result. -/
theorem ret_run (v : Nat) (m : Mem) : (ret v).run m = pure (v, m) := rfl

/-- One ground input: the domain is a single point, so the claim is scoped. -/
theorem ret_run_ground (m : Mem) : (ret 7).run m = pure (7, m) := rfl

/-- An exact run that ends in a safety error is not a no-panic claim. -/
theorem panic_run (m : Mem) : boom.run m = throw Error.panic := rfl

/-- The same exact successful run, stated through the result option. -/
theorem ret_some (v : Nat) (m : Mem) : ((ret v).run m).run = some (.ok (v, m)) := rfl

theorem panic_some (m : Mem) : (boom.run m).run = some (.error Error.panic) := rfl

/-- `pure` in `Option` is `some`: wrapping a safety error it states a panic, not a return. -/
theorem panic_pure (m : Mem) : (boom.run m).run = pure (Except.error Error.panic) := rfl

theorem ret_pure_ok (v : Nat) (m : Mem) : ((ret v).run m).run = pure (Except.ok (v, m)) := rfl

/-- A premise over the root's parameter constrains the domain: scoped. -/
theorem premise_total (P : Assn) (v : Nat) (_h : 0 < v) :
    TotalTriple P (ret v) (fun _ => P) := ret_total P v

nonvacuity_witness premise_total :=
  ⟨emp, 1, Nat.one_pos, {}, Heap.empty, Heap.empty, Heap.disjoint_empty _,
    Mem.heap_default_split, rfl, Mem.seq_default, trivial⟩

/-- Definitions are not unfolded: a wrapper does not inherit total strength. -/
def Wrapped (P : Assn) (c : MemM Nat) : Prop := TotalTriple P c (fun _ => P)

theorem wrapped_total (P : Assn) (v : Nat) : Wrapped P (ret v) := ret_total P v

/-- A conjunction is not classified, even when its parts would establish total correctness. -/
theorem partial_and_returns (P : Assn) (v : Nat) :
    Triple P (ret v) (fun _ => P) ∧ Returns P (ret v) :=
  ⟨ret_partial P v, ret_returns P v⟩

/-- A thread triple (registered head `Zig.TTriple`). -/
theorem ret_thread (P : Assn) (v : Nat) : TTriple P (ret v) (fun _ => P) :=
  TTriple.ret (Q := fun _ => P) v

/-- Concurrent total correctness (registered head `Zig.Conc.Total.EventuallyReturns`); its
initial memory is fixed, so the claim is scoped to that memory. -/
theorem countdown_total (env : Env) (n : Nat) :
    Conc.Total.EventuallyReturns env (fun _ => pure ()) (Conc.Total.countdown n) {}
      (fun _ m => m = {}) :=
  Conc.Total.countdown_total env n

/-! Bounded and concurrent return interfaces. -/

/-- A loop body that exits at once. -/
def exitBody : MM Unit Bool := pure false

/-- A loop body that always repeats: the loop never exits. -/
def spinBody : MM Unit Bool := pure true

/-- A bounded total triple: one body run. -/
theorem exit_within (P : Assn) : TotalTripleWithin 1 P exitBody id () (fun _ _ => P) := by
  apply TotalTripleWithin.exit
  intro m hP _ hd hm hp hs
  exact ⟨(false, ()), m, hP, rfl, hd, hm, sep_lift.mpr ⟨rfl, hp⟩, hs⟩

nonvacuity_witness exit_within :=
  ⟨emp, {}, Heap.empty, Heap.empty, Heap.disjoint_empty _, Mem.heap_default_split, rfl,
    Mem.seq_default, trivial⟩

theorem exit_within_total (P : Assn) :
    TotalTriple P ((Zig.loop exitBody id).run ()) (fun _ => P) :=
  (exit_within P).toTotal

nonvacuity_witness exit_within_total :=
  ⟨emp, {}, Heap.empty, Heap.empty, Heap.disjoint_empty _, Mem.heap_default_split, rfl,
    Mem.seq_default, trivial⟩

/-- The spinning loop has no counted run. -/
theorem spin_no_run : ∀ s m k e s' m', ¬ LoopRuns spinBody id s m k e s' m' := by
  intro s m k e s' m' h
  induction h with
  | exit hb ha =>
    -- `rfl` rather than unfolding `spinBody`, which would add an equation lemma to the report.
    rw [show (spinBody.run _).run _ = pure ((true, _), _) from rfl] at hb
    simp only [pure, ExceptT.pure, ExceptT.mk] at hb
    cases hb
    simp at ha
  | next _ _ _ ih => exact ih

/-- Vacuity guard: with any admissible input, divergence has no bounded triple for any bound. -/
theorem spin_not_within (B : Nat) (P : Assn) (Q : Bool → Unit → Assn) (m : Mem) (hP hF : Heap)
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq) :
    ¬ TotalTripleWithin B P spinBody id () Q :=
  TotalTripleWithin.not_within_of_stuck hd hm hp hs (spin_no_run () m)

open Zig.Conc.Total in
/-- Unconditional concurrent return: every oracle, every large enough budget. -/
theorem countdown_eventually (env : Env) :
    EventuallyReturns env (fun _ => pure ()) (countdown 2) {} (fun _ m => m = {}) :=
  Zig.Conc.Total.countdown_total env 2

open Zig.Conc.Total in
/-- Bounded concurrent return: two scheduler turns under every oracle. -/
theorem countdown_bounded (env : Env) :
    ReturnsWithin 2 env (fun _ => pure ()) (countdown 2) {} (fun _ m => m = {}) :=
  countdown_within env 2

-- The budget premise `2 ≤ fuel` is met.
nonvacuity_witness countdown_bounded := ⟨⟨.any, .available⟩, fun _ => 0, 2, Nat.le_refl 2, trivial⟩

open Zig.Conc.Total in
/-- A premise-dependent return. Its premise is unsatisfiable, so it holds even for a program
that never returns: the conditional form must not satisfy an unconditional goal. -/
theorem stuck_under_false (env : Env) :
    EventuallyReturnsUnder (fun _ => False) env (fun (_ : Unit) => pure ()) (stuck : ConcM Unit Unit)
      {} (fun _ _ => False) :=
  under_false

open Zig.Conc.Total in
/-- A true program stated conditionally is still only a conditional claim. -/
theorem countdown_under (env : Env) (Fair : (Nat → Nat) → Prop) :
    EventuallyReturnsUnder Fair env (fun _ => pure ()) (countdown 2) {} (fun _ m => m = {}) :=
  (Zig.Conc.Total.countdown_total env 2).under Fair

open Zig.Conc.Total in
theorem stuck_not_total (env : Env) :
    ¬ EventuallyReturns env (fun (_ : Unit) => pure ()) (stuck : ConcM Unit Unit) {} (fun _ _ => True) :=
  stuck_not_eventuallyReturns env _ _ _

end ClaimFixture
