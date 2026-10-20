import Runtime
import SpawnFailure.Gen
import ZigLean.Sep.Full.Witness
import ZigLean.Sep.Full.Init
import ZigLean.Sep.Full.ThreadFacts

/-!
The seven Runtime theorem declarations and their executable tail stay unchanged.
Every memory below is either the generated SpawnFailure.mem0 or an endpoint supplied
by an existing native fork/join run theorem. There is no hand-built memory seed.
-/

open Zig Zig.Conc Zig.Full Zig.Full.FAssn

namespace SpawnFailure.RuntimeNonvacuity

/-- The actual generated start admits the full-state parts and the plain ghost resource. -/
private theorem start_owned (σ : Placement) :
    ∃ rO, FOwned plainOwn rO (SpawnFailure.mem0 σ) := by
  refine ⟨rnil, ?_⟩
  simpa only [SpawnFailure.mem0, Mem.ofGlobals, List.foldl_nil] using FOwned.start0_plain σ

/-- Native fork and join endpoints that inhabit the refusal contract's premises.
The fork hands the complete plain resource to its child, leaving the parent rnil. -/
private theorem fork_join_inputs (σ : Placement) :
    ∃ (own : ThreadId → Res) (rO : Res) (m m' : Mem) (first : ThreadId),
      (Thread.fork.run { SpawnFailure.mem0 σ with current := 0 }).run =
        some (.ok (first, m)) ∧
      FOwned own rO m ∧ 0 < m.threads.size ∧ first ≠ 0 ∧
      ((Thread.join first).run { m with current := 0 }).run = some (.ok ((), m')) ∧
      own 0 = rnil ∧ own first = plainOwn 0 := by
  obtain ⟨rO, ho0⟩ := start_owned σ
  have ht0 : 0 < (SpawnFailure.mem0 σ).threads.size := by
    simp [SpawnFailure.mem0, Mem.ofGlobals]
  obtain ⟨first, m, hf⟩ :
      ∃ (first : ThreadId) (m : Mem),
        (Thread.fork.run { SpawnFailure.mem0 σ with current := 0 }).run =
          some (.ok (first, m)) :=
    ⟨_, _, Proto.fork_run _⟩
  obtain ⟨hfirst, hthreads⟩ :=
    Zig.Conc.fork_threads (m := SpawnFailure.mem0 σ) (t := 0) (gt := false) hf
  have hne : first ≠ 0 := by
    rw [hfirst]
    exact Nat.ne_of_gt ht0
  let own : ThreadId → Res := upd (upd plainOwn 0 rnil) first (plainOwn 0)
  have hsplit : plainOwn 0 = rsum rnil (plainOwn 0) := (rnil_rsum _).symm
  have hd : FHeap.Disjoint rnil.heap (plainOwn 0).heap :=
    (FHeap.disjoint_empty _).symm
  have ho : FOwned own rO m :=
    FOwned.fork (m := SpawnFailure.mem0 σ) (t := 0) (gt := false)
      ho0 ht0 hsplit hd hf
  have ht : 0 < m.threads.size := by
    rw [hthreads]
    simp
  have hr : m.threads[first]? =
      some ({ spawner := 0, joined := false, gated := false } : ThreadRec) := by
    rw [hthreads, hfirst]
    simp
  obtain ⟨m', hj⟩ := Proto.join_run (m := { m with current := 0 }) hr rfl rfl (.inl rfl)
  have hparent : own 0 = rnil := by
    simp [own, upd, Ne.symm hne]
  have hchild : own first = plainOwn 0 := by
    simp [own, upd]
  exact ⟨own, rO, m, m', first, hf, ho, ht, hne, hj, hparent, hchild⟩

/- The computed telescope of failedSpawnOwnership is, in order:
   own, rO, m, P, G, t, depth, ho, True.
   WP unfolds to Safe; neither contributes forall binders for this pure result.
   FOwned is the ho premise, so withPremises does not open its fields. -/
nonvacuity_witness _root_.failedSpawnOwnership := by
  obtain ⟨rO, ho⟩ := start_owned .fresh
  let P : Proto _root_.Target Unit := {
    inv := fun _ m => ∃ own rO, FOwned own rO m
    init := fun _ _ => True
    fin := fun _ => True
    strict := true
    spawnFails := true
  }
  exact ⟨plainOwn, rO, SpawnFailure.mem0 .fresh, P, (fun _ => ()), 0, 0, ho, trivial⟩

/- The computed telescope of refusedSecondThenJoin is, in order:
   own, rO, m, m', t, first, c, depth, hc, ho, ht, hne, hj, True.
   Its And conclusion adds no binders. The run premise hj is supplied by join_run,
   at an actual fork endpoint rather than a separately constructed memory. -/
nonvacuity_witness _root_.refusedSecondThenJoin := by
  obtain ⟨own, rO, m, m', first, -, ho, ht, hne, hj, -, -⟩ := fork_join_inputs .fresh
  exact ⟨own, rO, m, m', 0, first, 1, 0, by decide, ho, ht, hne, hj, trivial⟩

/-- A positive start instance, independently useful even if the producer classifies the
original WP head as structural. No protocol or ghost environment is assumed to exist. -/
theorem failed_ownership_from_start (P : Proto _root_.Target Unit) (G : ThreadId → Unit) :
    ∃ rO, FOwned plainOwn rO (SpawnFailure.mem0 .fresh) ∧
      P.WP 0 ((spawnOutcomeC 1 _root_.Target.worker : CM _root_.Target Unit _).run ())
        (fun result _ m' _ => result = (.error "ThreadQuotaExceeded", ()) ∧
          FOwned plainOwn rO m') G (SpawnFailure.mem0 .fresh) 0 := by
  obtain ⟨rO, ho⟩ := start_owned .fresh
  exact ⟨rO, ho, _root_.failedSpawnOwnership (P := P) (G := G) (t := 0) (depth := 0) ho⟩

/-- A positive refusal-followed-by-join instance whose input came from the real start
and a real fork. The whole child resource returns, including its non-unit plain ghost.
This is resource inhabitability evidence, not a scheduler liveness claim. -/
theorem refusal_join_plain_inhabited :
    ∃ (own : ThreadId → Res) (rO : Res) (m m' : Mem) (first : ThreadId),
      (Thread.fork.run { SpawnFailure.mem0 .fresh with current := 0 }).run =
        some (.ok (first, m)) ∧
      ((spawnOutcomeC 1 _root_.Target.worker : CM _root_.Target Unit _).run () 0
          { m with current := 0 } =
        CoN.leaf (some (.ok ((.error (spawnErrorAt (1 - 1)), ()),
          { m with current := 0 }))) ∧
        FOwned (upd (upd own 0 (rsum (own 0) (own first))) first rnil) rO m') ∧
      (upd (upd own 0 (rsum (own 0) (own first))) first rnil 0) = plainOwn 0 ∧
      plain (upd (upd own 0 (rsum (own 0) (own first))) first rnil 0) ∧
      (upd (upd own 0 (rsum (own 0) (own first))) first rnil 0).gh ≠ Ghost.unit := by
  obtain ⟨own, rO, m, m', first, hf, ho, ht, hne, hj, hparent, hchild⟩ :=
    fork_join_inputs .fresh
  let returned : ThreadId → Res := upd (upd own 0 (rsum (own 0) (own first))) first rnil
  have hreturned : returned 0 = plainOwn 0 := by
    simp only [returned, upd_ne _ _ (Ne.symm hne), upd_self, hparent, hchild, rnil_rsum]
  have hplain : plain (returned 0) := by
    rw [hreturned, plainOwn_zero]
    exact plain_intro
  have hnonunit : (returned 0).gh ≠ Ghost.unit := by
    intro he
    have hn := plain_noStack (R := emp) (sep_emp.mpr hplain)
    rw [he] at hn
    change (0 : Nat) < 0 at hn
    exact (Nat.lt_irrefl 0) hn
  have hresult := _root_.refusedSecondThenJoin (own := own) (rO := rO) (m := m) (m' := m')
    (t := 0) (first := first) (c := 1) (depth := 0) (by decide) ho ht hne hj
  exact ⟨own, rO, m, m', first, hf, hresult, hreturned, hplain, hnonunit⟩

end SpawnFailure.RuntimeNonvacuity

