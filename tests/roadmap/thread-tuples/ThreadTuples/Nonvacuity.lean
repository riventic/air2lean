import ThreadTuples.Proofs
import ZigLean.Mem.Reuse
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Init
import ZigLean.Sep.Full.Local
import ZigLean.Sep.Full.ThreadFacts
import ZigLean.Sep.Full.ThreadRest
import ZigLean.Sep.Full.Witness
import ZigLean.Witness

/-!
These are per-item resource-admission obligations. `makeZeroPair` constructs the two
zero output cells required by the existing tuple grants using real allocation and
store operations from `ThreadTuples.mem0`. It is not a wrapper around, a replacement
for, or an execution proof of generated `ThreadTuples.mixed` / `atomicShared`.

There is one whole-program `fsym` walk, below. A concrete returning run is taken
from the existing canonical `Placement.fresh`; no memory record or scheduler oracle
is seeded here. Every resource comes from the native rules and their adequacy.

The copied scalar arguments remain arbitrary. The frozen twenty tuple contracts
and seven Runtime contracts are not changed or discharged merely by these names.
-/

namespace ThreadTuples.Nonvacuity

open Zig Zig.Conc Zig.Full Zig.Full.FAssn

/-- Permanent per-item construction of the resources in the tuple grants. -/
def makeZeroPair : MemM (Ptr × Ptr) := do
  let out ← allocStack 4 4
  let other ← allocStack 4 4
  store (α := BitVec 32) 4 out 0
  store (α := BitVec 32) 4 other 0
  pure (out, other)

/-- Each output keeps its own full allocation extent, together with the plain mode. -/
def pairKeep (ps : Ptr × Ptr) : FAssn :=
  (FAssn.ex fun b : BlockId => ⟪ps.1.block = some b⟫ ⋆ bext b 4 .stack) ⋆
    ((FAssn.ex fun b : BlockId => ⟪ps.2.block = some b⟫ ⋆ bext b 4 .stack) ⋆ plain)

def pairPost (ps : Ptr × Ptr) : FAssn :=
  (up (pts ps.1 4 (0#32)) ⋆ up (pts ps.2 4 (0#32))) ⋆ pairKeep ps

/-- A genuine full-state statement, proved by one generic walk. It is partial
because the address space may be full. The admission below proves an actual
successful run; it does not add a run premise to a public program theorem. -/
theorem makeZeroPair_spec :
    FTTriple (globals [] ⋆ plain) makeZeroPair pairPost := by
  fsym [makeZeroPair, pairPost, pairKeep, globals]

/-- Real initial ownership, with its complete plain-mode resource. -/
theorem start_owned :
    FOwned plainOwn rnil (ThreadTuples.mem0 Placement.fresh) := by
  simpa only [ThreadTuples.mem0, Mem.ofGlobals, List.foldl_nil] using
    FOwned.start0_plain Placement.fresh

/-- The output pointer identities are returned by the actual construction, not
chosen independently of its run. The final memory is inferred from that run. -/
theorem makeZeroPair_returns :
    ∃ m', (makeZeroPair.run (ThreadTuples.mem0 Placement.fresh)).run =
      some (.ok (((⟨some 0, 0⟩ : Ptr), (⟨some 1, 0⟩ : Ptr)), m')) := by
  have hr : runValue makeZeroPair (ThreadTuples.mem0 Placement.fresh) =
      some (.ok ((⟨some 0, 0⟩ : Ptr), (⟨some 1, 0⟩ : Ptr))) := by decide +kernel
  unfold runValue at hr
  obtain ⟨result, hrun, hresult⟩ := Option.map_eq_some_iff.mp hr
  cases result with
  | error e => cases hresult
  | ok result =>
      obtain ⟨ps, m'⟩ := result
      cases hresult
      exact ⟨m', hrun⟩

/- The statement of this companion is computed from `makeZeroPair_spec`'s actual
type by the existing command. Its full framed precondition is the real start. -/
nonvacuity_witness makeZeroPair_spec := by
  change Witness.FTTAdmit (globals [] ⋆ plain)
  obtain ⟨hh, hp⟩ := initRes_holds_plain Placement.fresh [] (by simp)
  have hs := Mem.init_fseq Placement.fresh [] (by simp [Mem.GlobalsFit])
  exact ⟨ThreadTuples.mem0 Placement.fresh, _, rnil, hh, hp, hs.fconc,
    Witness.owns_of_footprint rfl _ _, trivial⟩

/- The computed liveness companion is tied to the same actual initializer run. -/
liveness_witness makeZeroPair_spec := by
  change Witness.FTTLive (globals [] ⋆ plain) makeZeroPair
  obtain ⟨m', hr⟩ := makeZeroPair_returns
  obtain ⟨hh, hp⟩ := initRes_holds_plain Placement.fresh [] (by simp)
  have hs := Mem.init_fseq Placement.fresh [] (by simp [Mem.GlobalsFit])
  exact ⟨ThreadTuples.mem0 Placement.fresh, _, rnil, hh, hp, hs.fconc,
    Witness.owns_of_footprint rfl _ _,
    (((⟨some 0, 0⟩ : Ptr), (⟨some 1, 0⟩ : Ptr)), m'), hr⟩

/-- Apply the one whole-initializer thread judgment at the real initial part.
The existing cur-frame discipline and `FOwned.step` preserve the complete resource;
there is no `WP` leaf conversion, proof-bind walk, or local transport rule. -/
theorem zero_pair_owned :
    ∃ m' r,
      (makeZeroPair.run (ThreadTuples.mem0 Placement.fresh)).run =
        some (.ok (((⟨some 0, 0⟩ : Ptr), (⟨some 1, 0⟩ : Ptr)), m')) ∧
      FOwned (upd plainOwn 0 r) rnil m' ∧
      pairPost ((⟨some 0, 0⟩ : Ptr), (⟨some 1, 0⟩ : Ptr)) r ∧
      m'.current = 0 ∧ m'.threads = #[{ spawner := 0, joined := true }] := by
  obtain ⟨m', hr⟩ := makeZeroPair_returns
  let m0 := ThreadTuples.mem0 Placement.fresh
  have ho : FOwned plainOwn rnil m0 := start_owned
  have ht : 0 < m0.threads.size := by decide
  obtain ⟨rR, hR, hRO, hh⟩ := ho.part ht
  have hp : (globals [] ⋆ plain) (plainOwn 0) := by
    change (emp ⋆ plain) (plainOwn 0)
    exact sep_comm (sep_emp.mpr (by rw [plainOwn_zero]; exact plain_intro))
  have hcm : m0.FConc :=
    ⟨by rw [ho.csize]; exact ht, ho.conc.1, ho.conc.2.1⟩
  have hx := makeZeroPair_spec m0 (plainOwn 0) _
    (hh.addCurF (ho.part_noCur hR)) hp hcm (ho.owns 0 ht)
  rw [hr] at hx
  obtain ⟨r, hh', hq, hcm', how, hs⟩ := hx
  obtain ⟨hnc, hh'⟩ := hh'.dropCurF
  exact ⟨m', r, hr, ho.step rfl ht hR hRO hh' hcm' how hs hnc,
    hq, hs.current, hs.threads⟩

/-- Native adequacy supplies full resources, their frame, and sequential memory
invariants at the memory that the construction actually returns. -/
theorem zero_pair_resources :
    ∃ m' outCell otherCell keep,
      (makeZeroPair.run (ThreadTuples.mem0 Placement.fresh)).run =
        some (.ok (((⟨some 0, 0⟩ : Ptr), (⟨some 1, 0⟩ : Ptr)), m')) ∧
      Holds m' (rsum (rsum outCell otherCell) keep) rnil ∧
      up (pts ⟨some 0, 0⟩ 4 (0#32)) outCell ∧
      up (pts ⟨some 1, 0⟩ 4 (0#32)) otherCell ∧
      FHeap.Disjoint outCell.heap otherCell.heap ∧
      FHeap.Disjoint (rsum outCell otherCell).heap keep.heap ∧
      pairKeep ((⟨some 0, 0⟩ : Ptr), (⟨some 1, 0⟩ : Ptr)) keep ∧ m'.FSeq := by
  obtain ⟨m', hr⟩ := makeZeroPair_returns
  have hp := FTriple.run_init_plain Placement.fresh []
    (by simp [Mem.GlobalsFit]) (by simp) makeZeroPair_spec.toFTriple
  simp only [ThreadTuples.mem0] at hr
  rw [hr] at hp
  obtain ⟨r, hh, hpost, hs⟩ := hp
  obtain ⟨child, keep, hd, rfl, hchild, hkeep⟩ := hpost
  obtain ⟨outCell, otherCell, hdo, rfl, hout, hother⟩ := hchild
  exact ⟨m', outCell, otherCell, keep, hr, hh, hout, hother, hdo, hd, hkeep, hs⟩

/-- The mixed grant is inhabited in a memory reached from the real start, for
every pair of copied scalar arguments. `Holds.split` retains the complete frame. -/
theorem mixed_grant_at_source (first second : BitVec 32) :
    ∃ m', (makeZeroPair.run (ThreadTuples.mem0 Placement.fresh)).run =
        some (.ok (((⟨some 0, 0⟩ : Ptr), (⟨some 1, 0⟩ : Ptr)), m')) ∧
      Witness.FAdmit.At m'
        (ThreadTuples.Proofs.mixedGrant
          (.mixedWorker (first, ⟨some 0, 0⟩, second, ⟨some 1, 0⟩))) := by
  obtain ⟨m', outCell, otherCell, keep, hr, hh, hout, hother, hdo, hd, _, _⟩ :=
    zero_pair_resources
  exact ⟨m', hr, rsum outCell otherCell, rsum keep rnil, Holds.split hd hh,
    outCell, otherCell, hdo, rfl, hout, hother⟩

/-- The atomic grant's private output is disjoint from a complete second resource
in its frame. This proves the grant's admission, not an atomic worker's accesses
or a protocol's invariant. -/
theorem atomic_grant_at_source (first second : BitVec 32) :
    ∃ m' sharedPart, (makeZeroPair.run (ThreadTuples.mem0 Placement.fresh)).run =
        some (.ok (((⟨some 0, 0⟩ : Ptr), (⟨some 1, 0⟩ : Ptr)), m')) ∧
      Witness.FAdmit.At m'
        (ThreadTuples.Proofs.atomicGrant sharedPart ⟨some 1, 0⟩
          (.atomicWorker (⟨some 0, 0⟩, ⟨some 1, 0⟩, first, second))) := by
  obtain ⟨m', outCell, otherCell, keep, hr, hh, hout, _, hdo, hd, _, _⟩ :=
    zero_pair_resources
  exact ⟨m', otherCell.heap, hr, outCell, rsum otherCell (rsum keep rnil),
    Holds.split hdo (Holds.split hd hh), hout, rfl, hdo⟩

/-- Actual source resources inhabit every premise of the existing mixed capture
spawn, and also the ownership and run premises needed by `worker_join`. The raw
fork/join are bookkeeping steps; this is not a scheduler or worker execution proof. -/
theorem mixed_capture_fork_join_source (first second : BitVec 32) :
    ∃ (m mfork mjoin : Mem) (own : ThreadId → Res) (keep outCell otherCell : Res),
      (makeZeroPair.run (ThreadTuples.mem0 Placement.fresh)).run =
        some (.ok (((⟨some 0, 0⟩ : Ptr), (⟨some 1, 0⟩ : Ptr)), m)) ∧
      FOwned own rnil m ∧ 0 < m.threads.size ∧
      own 0 = rsum keep (rsum outCell otherCell) ∧
      FHeap.Disjoint keep.heap (outCell.heap ∪ otherCell.heap) ∧
      FHeap.Disjoint outCell.heap otherCell.heap ∧
      up (pts ⟨some 0, 0⟩ 4 (0#32)) outCell ∧
      up (pts ⟨some 1, 0⟩ 4 (0#32)) otherCell ∧
      (Thread.fork.run {m with current := 0}).run = some (.ok (m.threads.size, mfork)) ∧
      FOwned (upd (upd own 0 keep) m.threads.size (rsum outCell otherCell)) rnil mfork ∧
      ThreadTuples.Tgt.spawnInit
        (ThreadTuples.Proofs.ownedProtocol (fun p => .owned (up (pts p 4 (0#32)))))
        (.mixedWorker (first, ⟨some 0, 0⟩, second, ⟨some 1, 0⟩))
        { captured := .mixedWorker (first, ⟨some 0, 0⟩, second, ⟨some 1, 0⟩),
          privateRes := rsum outCell otherCell } ∧
      0 < mfork.threads.size ∧ m.threads.size ≠ 0 ∧
      ((Thread.join m.threads.size).run {mfork with current := 0}).run =
        some (.ok ((), mjoin)) := by
  obtain ⟨m, r, hr, ho, hp, _, hthreads⟩ := zero_pair_owned
  obtain ⟨child, keep, hd, rfl, hchild, _⟩ := hp
  obtain ⟨outCell, otherCell, hdo, rfl, hout, hother⟩ := hchild
  let own := upd plainOwn 0 (rsum (rsum outCell otherCell) keep)
  have ht : 0 < m.threads.size := by rw [hthreads]; decide
  have hsplit : own 0 = rsum keep (rsum outCell otherCell) := by
    change rsum (rsum outCell otherCell) keep = rsum keep (rsum outCell otherCell)
    exact rsum_comm hd
  obtain ⟨mfork, hf⟩ : ∃ mfork,
      (Thread.fork.run {m with current := 0}).run = some (.ok (m.threads.size, mfork)) :=
    ⟨_, Proto.forkWith_run false _⟩
  have hfork := ThreadTuples.Proofs.mixed_spawn
    (mode := fun p => .owned (up (pts p 4 (0#32))))
    first second ⟨some 0, 0⟩ ⟨some 1, 0⟩ rfl rfl ho ht hsplit hd.symm hdo hout hother hf
  have htf := (fork_threads (m := m) (t := 0) (gt := false) hf).2
  have hrec : mfork.threads[m.threads.size]? =
      some { spawner := 0, joined := false, gated := false } := by
    rw [htf]
    simp
  obtain ⟨mjoin, hj⟩ := Proto.join_run (m := {mfork with current := 0}) hrec rfl rfl
  have hlt : 0 < mfork.threads.size := by rw [htf]; simp
  have hne : m.threads.size ≠ 0 := by rw [hthreads]; decide
  exact ⟨m, mfork, mjoin, own, keep, outCell, otherCell, hr, ho, ht, hsplit,
    hd.symm, hdo, hout, hother, hf, hfork.1, hfork.2, hlt, hne, hj⟩

/-- The complete second cell moves into the protocol's rest by `FOwned.give`.
The native atomic-capture theorem then receives its original owned/shared mode
premises and a real fork. This does not prove the atomic worker's accesses. -/
theorem atomic_capture_fork_source (first second : BitVec 32) :
    ∃ (m mfork : Mem) (own : ThreadId → Res) (rO keep child shared : Res) (mode : Ptr → FTransfer),
      (makeZeroPair.run (ThreadTuples.mem0 Placement.fresh)).run =
        some (.ok (((⟨some 0, 0⟩ : Ptr), (⟨some 1, 0⟩ : Ptr)), m)) ∧
      FOwned own rO m ∧ rO = rsum shared rnil ∧ 0 < m.threads.size ∧
      own 0 = rsum keep child ∧ FHeap.Disjoint keep.heap child.heap ∧
      up (pts ⟨some 0, 0⟩ 4 (0#32)) child ∧
      up (pts ⟨some 1, 0⟩ 4 (0#32)) shared ∧
      FHeap.Disjoint child.heap shared.heap ∧
      mode ⟨some 0, 0⟩ = .owned (up (pts ⟨some 0, 0⟩ 4 (0#32))) ∧
      mode ⟨some 1, 0⟩ = .shared shared.heap ∧
      (Thread.fork.run {m with current := 0}).run = some (.ok (m.threads.size, mfork)) ∧
      FOwned (upd (upd own 0 keep) m.threads.size child) rO mfork ∧
      ThreadTuples.Tgt.spawnInit (ThreadTuples.Proofs.ownedProtocol mode)
        (.atomicWorker (⟨some 0, 0⟩, ⟨some 1, 0⟩, first, second))
        { captured := .atomicWorker (⟨some 0, 0⟩, ⟨some 1, 0⟩, first, second),
          privateRes := child } := by
  obtain ⟨m, r, hr, ho, hp, _, hthreads⟩ := zero_pair_owned
  obtain ⟨pair, keep, hd, rfl, hpair, _⟩ := hp
  obtain ⟨outCell, otherCell, hdo, rfl, hout, hother⟩ := hpair
  let own0 := upd plainOwn 0 (rsum (rsum outCell otherCell) keep)
  have ht : 0 < m.threads.size := by rw [hthreads]; decide
  have hdko : FHeap.Disjoint keep.heap outCell.heap :=
    (FHeap.disjoint_union_left.mp hd).1.symm
  have hdGive : FHeap.Disjoint (rsum keep outCell).heap otherCell.heap :=
    FHeap.disjoint_union_left.mpr ⟨(FHeap.disjoint_union_left.mp hd).2.symm, hdo⟩
  have hsGive : own0 0 = rsum (rsum keep outCell) otherCell := by
    change rsum (rsum outCell otherCell) keep = rsum (rsum keep outCell) otherCell
    rw [rsum_comm hd, ← rsum_assoc]
  have hoGive := FOwned.give ho ht hsGive hdGive
  let own := upd own0 0 (rsum keep outCell)
  let mode : Ptr → FTransfer := fun p =>
    if p = (⟨some 1, 0⟩ : Ptr) then .shared otherCell.heap
    else .owned (up (pts p 4 (0#32)))
  have hmodeOut : mode ⟨some 0, 0⟩ = .owned (up (pts ⟨some 0, 0⟩ 4 (0#32))) := rfl
  have hmodeShared : mode ⟨some 1, 0⟩ = .shared otherCell.heap := rfl
  have hsplit : own 0 = rsum keep outCell := by simp only [own, upd_self]
  obtain ⟨mfork, hf⟩ : ∃ mfork,
      (Thread.fork.run {m with current := 0}).run = some (.ok (m.threads.size, mfork)) :=
    ⟨_, Proto.forkWith_run false _⟩
  have hfork := ThreadTuples.Proofs.atomic_spawn
    ⟨some 0, 0⟩ ⟨some 1, 0⟩ first second hmodeOut hmodeShared
    hoGive ht hsplit hdko hout hdo hf
  exact ⟨m, mfork, own, rsum otherCell rnil, keep, outCell, otherCell, mode,
    hr, hoGive, rfl, ht, hsplit, hdko, hout, hother, hdo,
    hmodeOut, hmodeShared, hf, hfork.1, hfork.2⟩

/- No new ownership API, premise, judgment, or tactic is used here. None of these
facts claims generated worker execution or a complete generated-program proof. -/

end ThreadTuples.Nonvacuity

