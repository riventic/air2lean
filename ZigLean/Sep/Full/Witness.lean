import ZigLean.Sep.Full.Strength
import ZigLean.Sep.Full.Conc
import ZigLean.Sep.Full.Thread
import ZigLean.Mem.Witness

/-!
# Admissible inputs of full-state claims (`docs/claim-strength.md` §Witnesses)

`nonvacuity_witness` and `liveness_witness` (`ZigLean/Witness.lean`) compute a claim's premise
telescope from its type: the theorem's binders, then those of its conclusion head unfolded, and
for a total head (`FTotalTriple = FTriple ∧ FReturns`, `FTTotalTriple`) those of the partial
triple inside; a concurrent one (`CTriple`) has a thread triple's premises at a depth, and its
liveness is the run read in the thread (`soloTree`). The statements `T.nonvacuous`
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

/-- An admissible input of a thread triple with precondition `P`. -/
def FTTAdmit (P : FAssn) : Prop :=
  ∃ (m : Mem) (r rF : Res) (_ : Holds m r rF) (_ : P r) (_ : m.FConc)
    (_ : m.Owns m.current r.heap.erase), True

/-- An admissible input of a thread triple with precondition `P` on which `c` returns. -/
def FTTLive (P : FAssn) (c : MemM α) : Prop :=
  ∃ (m : Mem) (r rF : Res) (_ : Holds m r rF) (_ : P r) (_ : m.FConc)
    (_ : m.Owns m.current r.heap.erase), ∃ v, (c.run m).run = some (.ok v)

/-- An admissible input of a concurrent triple with precondition `P`, at some depth: a thread
triple's (`FTTAdmit`). -/
def CAdmit (P : FAssn) : Prop := ∃ (_ : Nat), FTTAdmit P

/-- An admissible input of a concurrent triple on which `x`, read in the thread at some depth
(`soloTree`: each stop answered in the memory it stopped with), returns. -/
def CLive {Tgt : Type} (P : FAssn) (x : ConcM Tgt α) : Prop :=
  ∃ (n : Nat) (m : Mem) (r rF : Res) (_ : Holds m r rF) (_ : P r) (_ : m.FConc)
    (_ : m.Owns m.current r.heap.erase), ∃ v, soloTree (x n m) = some (.ok v)

/-- A memory without stack budgets holds all of its bytes, with an empty frame (`holds_ofHeap`). -/
theorem holds_mem (m : Mem) (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) :
    ∃ rF, Holds m ⟨m.fheap, Know.none, Ghost.unit⟩ rF :=
  ⟨_, holds_ofHeap (Heap.disjoint_empty m.heap) (Heap.union_empty m.heap).symm hns⟩

theorem FAdmit.of_mem {P : FAssn} {m : Mem} (hp : P ⟨m.fheap, Know.none, Ghost.unit⟩)
    (hs : m.FSeq) (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) : FAdmit P :=
  have ⟨rF, hh⟩ := holds_mem m hns
  ⟨m, _, rF, hh, hp, hs, trivial⟩

/-- All bytes of a memory with knowledge `k` and the full extents `E` that are true in it
(`holds_exts`, `exts_true`): for a precondition with `known` and `bext` parts. -/
theorem FAdmit.of_exts {P : FAssn} {m : Mem} {k : Know} {E : BlockId → Option (Nat × BlockKind)}
    (hk : Know.Sub k m.kn) (ht : ExtTrue m (Ghost.exts E)) (hp : P ⟨m.fheap, k, Ghost.exts E⟩)
    (hs : m.FSeq) (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) : FAdmit P :=
  ⟨m, _, _, holds_exts (FMatch.fheap m) hk ht hns, hp, hs, trivial⟩

/-- A legacy precondition that holds of an `FSeq` memory's heap. -/
theorem FAdmit.up {P : Assn} {m : Mem} (hp : P m.heap) (hs : m.FSeq)
    (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) : FAdmit (up P) :=
  FAdmit.of_mem ⟨by simpa using hp, rfl, rfl⟩ hs hns

/-- The globals at program start (`initRes_holds`, `Mem.init_fseq`). -/
theorem FAdmit.init (σ : Placement) (gs : List (Array Byte × Nat × BlockKind))
    (h : Mem.GlobalsFit gs) (hK : ∀ g ∈ gs, g.2.2.mappedLo = 0) : FAdmit (globals gs) :=
  ⟨_, _, _, (initRes_holds σ gs hK).1, (initRes_holds σ gs hK).2, Mem.init_fseq σ gs h, trivial⟩

theorem FLive.of_run {P : FAssn} {c : MemM α} {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hp : P r) (hs : m.FSeq) (hr : ∃ v, (c.run m).run = some (.ok v)) : FLive P c :=
  ⟨m, r, rF, hh, hp, hs, hr⟩

theorem FLive.of_mem {P : FAssn} {c : MemM α} {m : Mem} (hp : P ⟨m.fheap, Know.none, Ghost.unit⟩)
    (hs : m.FSeq) (hr : ∃ v, (c.run m).run = some (.ok v))
    (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) : FLive P c :=
  have ⟨_, hh⟩ := holds_mem m hns
  FLive.of_run hh hp hs hr

theorem FLive.of_exts {P : FAssn} {c : MemM α} {m : Mem} {k : Know}
    {E : BlockId → Option (Nat × BlockKind)} (hk : Know.Sub k m.kn) (ht : ExtTrue m (Ghost.exts E))
    (hp : P ⟨m.fheap, k, Ghost.exts E⟩) (hs : m.FSeq) (hr : ∃ v, (c.run m).run = some (.ok v))
    (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) : FLive P c :=
  FLive.of_run (holds_exts (FMatch.fheap m) hk ht hns) hp hs hr

theorem FLive.toAdmit {P : FAssn} {c : MemM α} (h : FLive P c) : FAdmit P :=
  have ⟨m, r, rF, hh, hp, hs, _⟩ := h
  ⟨m, r, rF, hh, hp, hs, trivial⟩

/-- A total triple returns on every admissible input. -/
theorem FLive.of_total {P : FAssn} {c : MemM α} {Q : α → FAssn} (ht : FTotalTriple P c Q)
    (h : FAdmit P) : FLive P c := by
  obtain ⟨m, r, rF, hh, hp, hs, -⟩ := h
  obtain ⟨v, m', e⟩ := ht.2 m r rF hh hp hs
  exact ⟨m, r, rF, hh, hp, hs, (v, m'), by rw [e]; rfl⟩

/-- Total creation from an admissible input establishes an admissible postcondition. This is
the generic non-vacuity argument for allocator creation companions, over the existing judgment. -/
theorem FAdmit.of_total {P : FAssn} {c : MemM α} {Q : α → FAssn}
    (ht : FTotalTriple P c Q) (h : FAdmit P) : ∃ v, FAdmit (Q v) := by
  obtain ⟨m, r, rF, hh, hp, hs, -⟩ := h
  obtain ⟨v, m', e⟩ := ht.2 m r rF hh hp hs
  have h1 := ht.1 m r rF hh hp hs
  rw [e] at h1
  obtain ⟨r', hh', hq, hs'⟩ := h1
  exact ⟨v, m', r', rF, hh', hq, hs', trivial⟩

theorem CAdmit.of {P : FAssn} (h : FTTAdmit P) : CAdmit P := ⟨0, h⟩

theorem CLive.of_run {Tgt : Type} {P : FAssn} {x : ConcM Tgt α} (n : Nat)
    (h : FTTLive P (soloRun n x)) : CLive P x :=
  have ⟨m, r, rF, hh, hp, hc, ho, hr⟩ := h
  ⟨n, m, r, rF, hh, hp, hc, ho, hr⟩

/-- A memory without recorded accesses lets its current thread own every heap. -/
theorem owns_of_footprint {m : Mem} (hf : m.footprint = #[]) (t : ThreadId) (h : Heap) :
    m.Owns t h := fun e he => by rw [hf] at he; cases he; contradiction

theorem FTTAdmit.of_mem {P : FAssn} {m : Mem} (hp : P ⟨m.fheap, Know.none, Ghost.unit⟩)
    (hs : m.FSeq) (hf : m.footprint = #[]) (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) :
    FTTAdmit P :=
  have ⟨rF, hh⟩ := holds_mem m hns
  ⟨m, _, rF, hh, hp, hs.fconc, owns_of_footprint hf _ _, trivial⟩

theorem FTTLive.of_mem {P : FAssn} {c : MemM α} {m : Mem} (hp : P ⟨m.fheap, Know.none, Ghost.unit⟩)
    (hs : m.FSeq) (hf : m.footprint = #[]) (hr : ∃ v, (c.run m).run = some (.ok v))
    (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) : FTTLive P c :=
  have ⟨rF, hh⟩ := holds_mem m hns
  ⟨m, _, rF, hh, hp, hs.fconc, owns_of_footprint hf _ _, hr⟩

theorem FTTAdmit.of_exts {P : FAssn} {m : Mem} {k : Know} {E : BlockId → Option (Nat × BlockKind)}
    (hk : Know.Sub k m.kn) (ht : ExtTrue m (Ghost.exts E)) (hp : P ⟨m.fheap, k, Ghost.exts E⟩)
    (hs : m.FSeq) (hf : m.footprint = #[]) (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) :
    FTTAdmit P :=
  ⟨m, _, _, holds_exts (FMatch.fheap m) hk ht hns, hp, hs.fconc, owns_of_footprint hf _ _, trivial⟩

theorem FTTLive.of_exts {P : FAssn} {c : MemM α} {m : Mem} {k : Know}
    {E : BlockId → Option (Nat × BlockKind)} (hk : Know.Sub k m.kn) (ht : ExtTrue m (Ghost.exts E))
    (hp : P ⟨m.fheap, k, Ghost.exts E⟩) (hs : m.FSeq) (hf : m.footprint = #[])
    (hr : ∃ v, (c.run m).run = some (.ok v)) (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) :
    FTTLive P c :=
  ⟨m, _, _, holds_exts (FMatch.fheap m) hk ht hns, hp, hs.fconc, owns_of_footprint hf _ _, hr⟩

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

/-- The empty resources hold in the default, sequential memory. -/
theorem FAdmit.emp : FAdmit emp :=
  FAdmit.of_mem (m := {}) ⟨rfl, rfl, rfl⟩ fseq_default

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

/-! ## Bytes and values of concrete memories

`Witness.mem1 bs` holds the bytes `bs` in block `0` at address 4096, `Witness.mem2` two blocks
(`ZigLean/Mem/Witness.lean`). A precondition over them holds of the whole heap (`FAdmit.up`). -/

open Assn

theorem mem1_heap (bs : Array Byte) (kind : BlockKind) (l : Loc)
    (hk : kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    (mem1 bs kind).heap l =
      if l.1 = 0 ∧ l.2 < bs.size then some ⟨bs[l.2]!, 4096, bs.size, kind⟩ else none := by
  obtain ⟨b, o⟩ := l
  rcases b with _ | b
  · by_cases h : o < bs.size <;> simp [Mem.heap, mem1, blk, h, hk]
  · simp [Mem.heap, mem1]

theorem mem1_seq (bs : Array Byte) (kind : BlockKind) : (mem1 bs kind).Seq :=
  ⟨singleThread_empty rfl Nat.zero_lt_one⟩

theorem mem1_bytesAt (bs : Array Byte) (kind : BlockKind) (hk : kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    bytesAt p0 4096 bs.size kind bs (mem1 bs kind).heap :=
  ⟨0, rfl, by decide, fun l => by simp [mem1_heap _ _ _ hk, p0]⟩

theorem mem1_bytesAt' {bs : Array Byte} {kind : BlockKind} {S : Nat} (h : bs.size = S) (hk : kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    bytesAt p0 4096 S kind bs (mem1 bs kind).heap := h ▸ mem1_bytesAt bs kind hk

/-- `p0` points to the value that the block holds. -/
theorem mem1_pts {T : Type} [Enc T] {bs : Array Byte} {kind : BlockKind} {a : Nat} {v : T}
    (hs : bs.size = Enc.size T) (hv : Enc.decode bs = pure v) (ha : 4096 % a = 0)
    (hk : kind ≠ .constGlobal) (hlo : kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    pts p0 a v (mem1 bs kind).heap :=
  ⟨4096, bs.size, kind, bs, by simpa [p0] using ha, hs, hv, mem1_bytesAt bs kind hlo, hk⟩

theorem mem1_pts' {T : Type} [Enc T] [LawfulEnc T] (v : T) {a : Nat} (ha : 4096 % a = 0) :
    pts p0 a v (mem1 (Enc.encode v)).heap :=
  mem1_pts (LawfulEnc.size_encode v) (LawfulEnc.decode_encode v) ha (by decide)

/-- `p0` points to the empty array. -/
theorem mem1_arr0 {T : Type} [Enc T] (ha : 4096 % Enc.align T = 0) :
    arr p0 ([] : List T) (mem1 #[]).heap :=
  ⟨4096, _, .heap, #[], by simpa [p0] using ha, by simp, fun i hi => by simp at hi,
    mem1_bytesAt _ _, by decide⟩

/-- `p0` points to the one-item array `[v]`. -/
theorem mem1_arr1 {T : Type} [Enc T] [LawfulEnc T] (v : T) (ha : 4096 % Enc.align T = 0) :
    arr p0 [v] (mem1 (Enc.encode v)).heap := by
  have hs := LawfulEnc.size_encode v
  refine ⟨4096, _, .heap, Enc.encode v, by simpa [p0] using ha, by simp [hs], fun i hi => ?_,
    mem1_bytesAt _ _, by decide⟩
  have : i = 0 := by simp at hi; omega
  subst this
  simpa [← hs] using LawfulEnc.decode_encode v

/-- `p0` of `mem1` holds the `u32` `0`, the one-item array `[0]`, or one undefined byte. -/
theorem pts32 : pts p0 4 (0 : BitVec 32) (mem1 (Enc.encode (0 : BitVec 32))).heap :=
  mem1_pts' 0 (by decide)

theorem arr32 : arr p0 [(0 : BitVec 32)] (mem1 (Enc.encode (0 : BitVec 32))).heap :=
  mem1_arr1 0 (by decide +kernel)

theorem byte1 (kind : BlockKind)
    (hk : kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    bytesAt p0 4096 1 kind #[.undef] (mem1 #[.undef] kind).heap :=
  mem1_bytesAt _ _ hk

/-- Two values one after the other: `p0` points to `v` and `p0.add (Enc.size T)` to `w`. -/
theorem mem1_pts₂ {T U : Type} [Enc T] [LawfulEnc T] [Enc U] [LawfulEnc U] (v : T) (w : U)
    {a b : Nat} (ha : 4096 % a = 0) (hb : (4096 + Enc.size T) % b = 0) :
    (pts p0 a v ∗ pts (p0.add (Enc.size T)) b w)
      (mem1 (Enc.encode v ++ Enc.encode w)).heap := by
  have hv := LawfulEnc.size_encode v
  have hw := LawfulEnc.size_encode w
  obtain ⟨h₁, h₂, hd, he, hb₁, hb₂⟩ :=
    bytesAt_split (mem1_bytesAt (Enc.encode v ++ Enc.encode w) .heap) (k := Enc.size T)
      (by simp [hv])
  have e₁ : (Enc.encode v ++ Enc.encode w).extract 0 (Enc.size T) = Enc.encode v := by
    simp [Array.extract_append, ← hv]
  have e₂ : (Enc.encode v ++ Enc.encode w).extract (Enc.size T)
      (Enc.encode v ++ Enc.encode w).size = Enc.encode w := by
    simp [Array.extract_append, ← hv]
  rw [e₁] at hb₁
  rw [e₂] at hb₂
  refine ⟨h₁, h₂, hd, he, ⟨_, _, _, _, by simpa [p0] using ha, hv, LawfulEnc.decode_encode v, hb₁,
    by decide⟩, ⟨_, _, _, _, ?_, hw, LawfulEnc.decode_encode w, hb₂, by decide⟩⟩
  simpa [p0, Ptr.add] using hb

theorem mem2_heap (bs₁ bs₂ : Array Byte) (k₁ k₂ : BlockKind) (l : Loc)
    (hk₁ : k₁.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo])
    (hk₂ : k₂.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    (mem2 bs₁ bs₂ k₁ k₂).heap l =
      if l.1 = 0 ∧ l.2 < bs₁.size then some ⟨bs₁[l.2]!, 4096, bs₁.size, k₁⟩
      else if l.1 = 1 ∧ l.2 < bs₂.size then some ⟨bs₂[l.2]!, 8192, bs₂.size, k₂⟩ else none := by
  obtain ⟨b, o⟩ := l
  rcases b with _ | _ | b
  · by_cases h : o < bs₁.size <;> simp [Mem.heap, mem2, blk, h, hk₁]
  · by_cases h : o < bs₂.size <;> simp [Mem.heap, mem2, blk, h, hk₂]
  · simp [Mem.heap, mem2]

theorem mem2_seq {bs₁ bs₂ : Array Byte} (k₁ k₂ : BlockKind) (h : bs₁.size < 4096) :
    (mem2 bs₁ bs₂ k₁ k₂).Seq :=
  ⟨singleThread_empty rfl Nat.zero_lt_one⟩

/-- Each block of `mem2` is owned separately. -/
theorem mem2_bytesAt (bs₁ bs₂ : Array Byte) (k₁ k₂ : BlockKind)
    (hk₁ : k₁.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo])
    (hk₂ : k₂.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    (bytesAt p0 4096 bs₁.size k₁ bs₁ ∗ bytesAt p1 8192 bs₂.size k₂ bs₂) (mem2 bs₁ bs₂ k₁ k₂).heap := by
  refine ⟨fun l => if l.1 = 0 ∧ l.2 < bs₁.size then some ⟨bs₁[l.2]!, 4096, bs₁.size, k₁⟩ else none,
    fun l => if l.1 = 1 ∧ l.2 < bs₂.size then some ⟨bs₂[l.2]!, 8192, bs₂.size, k₂⟩ else none,
    fun l => ?_, funext fun l => ?_, ⟨0, rfl, by decide, fun l => by simp [p0]⟩,
    ⟨1, rfl, by decide, fun l => by simp [p1]⟩⟩
  · by_cases h : l.1 = 0
    · right; simp [h]
    · left; simp [h]
  · rw [mem2_heap _ _ _ _ _ hk₁ hk₂]
    by_cases h : l.1 = 0 ∧ l.2 < bs₁.size
    · simp [h]
    · simp only [h, ↓reduceIte, Heap.union_apply, Option.none_or]

theorem mem2_bytesAt' {bs₁ bs₂ : Array Byte} {k₁ k₂ : BlockKind} {S₁ S₂ : Nat} (h₁ : bs₁.size = S₁)
    (h₂ : bs₂.size = S₂) (hk₁ : k₁.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo])
    (hk₂ : k₂.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    (bytesAt p0 4096 S₁ k₁ bs₁ ∗ bytesAt p1 8192 S₂ k₂ bs₂) (mem2 bs₁ bs₂ k₁ k₂).heap := by
  subst h₁ h₂; exact mem2_bytesAt bs₁ bs₂ k₁ k₂ hk₁ hk₂

/-! ## Runs that return, decided -/

/-- A successful result as an `Option`: `okb d` exactly when `d = some (.ok r)`. -/
def okb {ε β : Type} : Option (Except ε β) → Bool
  | some (.ok _) => true
  | _ => false

theorem ok_of_okb {ε β : Type} {d : Option (Except ε β)} (h : okb d = true) :
    ∃ r, d = some (.ok r) := by
  match d, h with
  | some (.ok r), _ => exact ⟨r, rfl⟩

/-! ## Weakening -/

theorem FAdmit.mono {P P' : FAssn} (h : FAdmit P) (hp : ∀ r, P r → P' r) : FAdmit P' :=
  have ⟨m, r, rF, hh, hP, hs, _⟩ := h
  ⟨m, r, rF, hh, hp r hP, hs, trivial⟩

end Witness
end Zig
