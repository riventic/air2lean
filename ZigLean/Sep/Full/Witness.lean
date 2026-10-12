import ZigLean.Sep.Full.Strength
import ZigLean.Sep.Full.Conc
import ZigLean.Sep.Full.Thread
import ZigLean.Mem.Witness

/-!
# Admissible inputs of full-state claims (`docs/claim-strength.md` §Witnesses)

`nonvacuity_witness` and `liveness_witness` (`ZigLean/Witness.lean`) compute a claim's premise
telescope from its type: the theorem's binders, then those of its conclusion head unfolded, and
for a total head (`FTotalTriple = FTriple ∧ FReturns`, `FTTotalTriple`) or a concurrent one
(`CTriple = ∀ n, FTriple …`) those of the partial triple inside. The statements `T.nonvacuous`
and `T.returns` of a full-state claim `T` therefore end in these definitions:

| head | `T.nonvacuous` ends in | `T.returns` ends in |
|---|---|---|
| `FTriple`, `FTotalTriple` | `FAdmit P` | `FLive P c` |
| `CTriple` | `CAdmit P` | `CLive P x` |
| `FTTriple`, `FTTotalTriple` | `FTTAdmit P` | `FTTLive P c` |

An admissible input is a memory `m` with `Mem.FSeq` (thread triples: `Mem.FConc` and ownership of
the precondition's bytes) and resources `r`, `rF` that `m` holds with `P r`. `FAdmit.of_mem`
builds one from any `FSeq` memory, owning all of its bytes with an empty frame
(`holds_ofHeap`); `FAdmit.of_exts` adds knowledge and the full extents (`bext`) that are true in
it (`holds_exts`); `FAdmit.up` does it for a legacy precondition `up P` that holds of the
memory's heap, `FAdmit.init` for the globals at program start (`initRes_holds`). The default
memory and `Witness.mem1` are `FSeq` memories (`fseq_default`, `mem1_fseq`). A total triple turns an admissible input into a returning
run (`FLive.of_total`, `FTTLive.of_total`).
-/

namespace Zig
namespace Witness

open Full FAssn Sched

variable {α : Type}

/-! ## Admissible inputs and returning runs -/

/-- An admissible input of a full-state triple with precondition `P`. -/
def FAdmit (P : FAssn) : Prop :=
  ∃ (m : Mem) (r rF : Res) (_ : Holds m r rF) (_ : P r) (_ : m.FSeq), True

/-- An admissible input of a full-state triple with precondition `P` on which `c` returns. -/
def FLive (P : FAssn) (c : MemM α) : Prop :=
  ∃ (m : Mem) (r rF : Res) (_ : Holds m r rF) (_ : P r) (_ : m.FSeq),
    ∃ v, (c.run m).run = some (.ok v)

/-- An admissible input of a concurrent triple with precondition `P`, at some depth. -/
def CAdmit (P : FAssn) : Prop := ∃ (_ : Nat), FAdmit P

/-- An admissible input of a concurrent triple on which `x` returns at some depth. -/
def CLive {Tgt : Type} (P : FAssn) (x : ConcM Tgt α) : Prop := ∃ n, FLive P (soloRun n x)

/-- An admissible input of a thread triple with precondition `P`. -/
def FTTAdmit (P : FAssn) : Prop :=
  ∃ (m : Mem) (r rF : Res) (_ : Holds m r rF) (_ : P r) (_ : m.FConc)
    (_ : m.Owns m.current r.heap.erase), True

/-- An admissible input of a thread triple with precondition `P` on which `c` returns. -/
def FTTLive (P : FAssn) (c : MemM α) : Prop :=
  ∃ (m : Mem) (r rF : Res) (_ : Holds m r rF) (_ : P r) (_ : m.FConc)
    (_ : m.Owns m.current r.heap.erase), ∃ v, (c.run m).run = some (.ok v)

/-- A memory holds all of its bytes, with an empty frame (`holds_ofHeap`). -/
theorem holds_mem (m : Mem) :
    ∃ rF, Holds m ⟨m.fheap, Know.none, Ghost.unit⟩ rF :=
  ⟨_, holds_ofHeap (Heap.disjoint_empty m.heap) (Heap.union_empty m.heap).symm⟩

theorem FAdmit.of_mem {P : FAssn} {m : Mem} (hp : P ⟨m.fheap, Know.none, Ghost.unit⟩)
    (hs : m.FSeq) : FAdmit P :=
  have ⟨rF, hh⟩ := holds_mem m
  ⟨m, _, rF, hh, hp, hs, trivial⟩

/-- All bytes of a memory with knowledge `k` and the full extents `E` that are true in it
(`holds_exts`, `exts_true`): for a precondition with `known` and `bext` parts. -/
theorem FAdmit.of_exts {P : FAssn} {m : Mem} {k : Know} {E : BlockId → Option (Nat × BlockKind)}
    (hk : Know.Sub k m.kn) (ht : ExtTrue m (Ghost.exts E)) (hp : P ⟨m.fheap, k, Ghost.exts E⟩)
    (hs : m.FSeq) : FAdmit P :=
  ⟨m, _, _, holds_exts (FMatch.fheap m) hk ht, hp, hs, trivial⟩

/-- A legacy precondition that holds of an `FSeq` memory's heap. -/
theorem FAdmit.up {P : Assn} {m : Mem} (hp : P m.heap) (hs : m.FSeq) : FAdmit (up P) :=
  FAdmit.of_mem ⟨by simpa using hp, rfl, rfl⟩ hs

/-- The globals at program start (`initRes_holds`, `Mem.init_fseq`). -/
theorem FAdmit.init (σ : Placement) (gs : List (Array Byte × Nat × BlockKind))
    (h : Mem.GlobalsFit gs) (hK : ∀ g ∈ gs, g.2.2.mappedLo = 0) : FAdmit (globals gs) :=
  ⟨_, _, _, (initRes_holds σ gs hK).1, (initRes_holds σ gs hK).2, Mem.init_fseq σ gs h, trivial⟩

theorem FLive.of_run {P : FAssn} {c : MemM α} {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hp : P r) (hs : m.FSeq) (hr : ∃ v, (c.run m).run = some (.ok v)) : FLive P c :=
  ⟨m, r, rF, hh, hp, hs, hr⟩

theorem FLive.of_mem {P : FAssn} {c : MemM α} {m : Mem} (hp : P ⟨m.fheap, Know.none, Ghost.unit⟩)
    (hs : m.FSeq) (hr : ∃ v, (c.run m).run = some (.ok v)) : FLive P c :=
  have ⟨_, hh⟩ := holds_mem m
  FLive.of_run hh hp hs hr

theorem FLive.of_exts {P : FAssn} {c : MemM α} {m : Mem} {k : Know}
    {E : BlockId → Option (Nat × BlockKind)} (hk : Know.Sub k m.kn) (ht : ExtTrue m (Ghost.exts E))
    (hp : P ⟨m.fheap, k, Ghost.exts E⟩) (hs : m.FSeq) (hr : ∃ v, (c.run m).run = some (.ok v)) :
    FLive P c :=
  FLive.of_run (holds_exts (FMatch.fheap m) hk ht) hp hs hr

theorem FLive.admit {P : FAssn} {c : MemM α} (h : FLive P c) : FAdmit P :=
  have ⟨m, r, rF, hh, hp, hs, _⟩ := h
  ⟨m, r, rF, hh, hp, hs, trivial⟩

/-- A total triple returns on every admissible input. -/
theorem FLive.of_total {P : FAssn} {c : MemM α} {Q : α → FAssn} (ht : FTotalTriple P c Q)
    (h : FAdmit P) : FLive P c := by
  obtain ⟨m, r, rF, hh, hp, hs, -⟩ := h
  obtain ⟨v, m', e⟩ := ht.2 m r rF hh hp hs
  exact ⟨m, r, rF, hh, hp, hs, (v, m'), by rw [e]; rfl⟩

theorem CAdmit.of {P : FAssn} (h : FAdmit P) : CAdmit P := ⟨0, h⟩

theorem CLive.of_run {Tgt : Type} {P : FAssn} {x : ConcM Tgt α} (n : Nat) (h : FLive P (soloRun n x)) :
    CLive P x :=
  ⟨n, h⟩

/-- A memory without recorded accesses lets its current thread own every heap. -/
theorem owns_of_footprint {m : Mem} (hf : m.footprint = #[]) (t : ThreadId) (h : Heap) :
    m.Owns t h := fun e he => by rw [hf] at he; cases he; contradiction

theorem FTTAdmit.of_mem {P : FAssn} {m : Mem} (hp : P ⟨m.fheap, Know.none, Ghost.unit⟩)
    (hs : m.FSeq) (hf : m.footprint = #[]) : FTTAdmit P :=
  have ⟨rF, hh⟩ := holds_mem m
  ⟨m, _, rF, hh, hp, hs.fconc, owns_of_footprint hf _ _, trivial⟩

theorem FTTLive.of_mem {P : FAssn} {c : MemM α} {m : Mem} (hp : P ⟨m.fheap, Know.none, Ghost.unit⟩)
    (hs : m.FSeq) (hf : m.footprint = #[]) (hr : ∃ v, (c.run m).run = some (.ok v)) : FTTLive P c :=
  have ⟨rF, hh⟩ := holds_mem m
  ⟨m, _, rF, hh, hp, hs.fconc, owns_of_footprint hf _ _, hr⟩

theorem FTTAdmit.of_exts {P : FAssn} {m : Mem} {k : Know} {E : BlockId → Option (Nat × BlockKind)}
    (hk : Know.Sub k m.kn) (ht : ExtTrue m (Ghost.exts E)) (hp : P ⟨m.fheap, k, Ghost.exts E⟩)
    (hs : m.FSeq) (hf : m.footprint = #[]) : FTTAdmit P :=
  ⟨m, _, _, holds_exts (FMatch.fheap m) hk ht, hp, hs.fconc, owns_of_footprint hf _ _, trivial⟩

theorem FTTLive.of_exts {P : FAssn} {c : MemM α} {m : Mem} {k : Know}
    {E : BlockId → Option (Nat × BlockKind)} (hk : Know.Sub k m.kn) (ht : ExtTrue m (Ghost.exts E))
    (hp : P ⟨m.fheap, k, Ghost.exts E⟩) (hs : m.FSeq) (hf : m.footprint = #[])
    (hr : ∃ v, (c.run m).run = some (.ok v)) : FTTLive P c :=
  ⟨m, _, _, holds_exts (FMatch.fheap m) hk ht, hp, hs.fconc, owns_of_footprint hf _ _, hr⟩

/-- A total thread triple returns on every admissible input. -/
theorem FTTLive.of_total {P : FAssn} {c : MemM α} {Q : α → FAssn} (ht : FTTotalTriple P c Q)
    (h : FTTAdmit P) : FTTLive P c := by
  obtain ⟨m, r, rF, hh, hp, hc, ho, -⟩ := h
  obtain ⟨v, m', e⟩ := ht.2 m r rF hh hp hc ho
  exact ⟨m, r, rF, hh, hp, hc, ho, (v, m'), by rw [e]; rfl⟩

/-! ## Concrete `FSeq` memories -/

/-- The default memory (no blocks, one thread) is an `FSeq` memory. -/
theorem fseq_default : ({} : Mem).FSeq :=
  ⟨⟨singleThread_empty rfl (by decide)⟩, by simp [shapes, ShapesWF], fun _ _ _ _ _ hb => by simp at hb,
    fun _ _ hb => by simp at hb⟩

/-- `mem1 bs` (one block at address 4096) is an `FSeq` memory when the block ends inside the
address space. -/
theorem mem1_fseq (bs : Array Byte) (kind : BlockKind) (h : 4096 + bs.size ≤ 2 ^ 63) :
    (mem1 bs kind).FSeq := by
  refine ⟨⟨singleThread_empty rfl Nat.zero_lt_one⟩, by simp [shapes, ShapesWF, mem1],
    fun b b' _ _ hne hb hb' _ => ?_, fun b bl hb _ => ?_⟩
  · have h1 : b = 0 := Nat.lt_one_iff.mp (Array.getElem?_eq_some_iff.mp hb).1
    have h2 : b' = 0 := Nat.lt_one_iff.mp (Array.getElem?_eq_some_iff.mp hb').1
    exact absurd (h1.trans h2.symm) hne
  · obtain rfl : b = 0 := Nat.lt_one_iff.mp (Array.getElem?_eq_some_iff.mp hb).1
    obtain rfl : blk bs kind = bl := Option.some.inj hb
    simpa [blk] using h

end Witness
end Zig
