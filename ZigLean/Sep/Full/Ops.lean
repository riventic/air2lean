import ZigLean.Sep.Full.Extent
import ZigLean.Sep.Full.Tame
import ZigLean.Sep.Full.ThreadStep
import ZigLean.Mem.Reuse

/-!
# Total full-state rules for the pointer operations of generated code

Native rules (no legacy lifting) for `@intFromPtr` (`ptrAddr`), the model's `@alignCast` check
(`checkAlign`), pointer `==` (`ptrEqAddr`) and pointer formation (`ptrProject`), and the lifted
total rules for `load`/`store` of `pts`. A rule takes what it needs of the memory from a
**provider**, a property of every memory that holds the precondition:

* `AddrOf b A P`: block `b` exists at address `A`. Knowledge gives it (`AddrOf.known`), and so
  does an owned cell (`AddrOf.owned`).
* `Reaches b k P`: block `b` exists with at least `k` bytes. An owned byte `j` gives `j + 1`
  (`Reaches.owned`): in-bounds facts come from ownership. A share of the block's extent at bound
  `k` gives `k` (`Reaches.share`): a pointer up to a bound that the program owns no byte below,
  such as a fixed buffer's end when every byte is lent out.

The providers frame (`AddrOf.sepL`, `Reaches.sepL`, and the `…R` versions).
-/

namespace Zig
namespace Full

open FAssn

/-! ## Providers -/

/-- Every memory that holds `P` has block `b` at address `A`. -/
def AddrOf (b : BlockId) (A : Nat) (P : FAssn) : Prop :=
  ∀ m r rF, Holds m r rF → P r → ∃ blk, m.blocks[b]? = some blk ∧ blk.addr = A

/-- Every memory that holds `P` has block `b` with at least `k` bytes. -/
def Reaches (b : BlockId) (k : Nat) (P : FAssn) : Prop :=
  ∀ m r rF, Holds m r rF → P r → ∃ blk, m.blocks[b]? = some blk ∧ k ≤ blk.bytes.size

section Providers

variable {b : BlockId} {A k : Nat} {P R : FAssn}

theorem AddrOf.sepL (h : AddrOf b A P) : AddrOf b A (P ⋆ R) := fun m _ rF hh hp => by
  obtain ⟨r₁, r₂, hd, rfl, h1, -⟩ := hp
  exact h m r₁ _ (Holds.split hd hh) h1

theorem AddrOf.sepR (h : AddrOf b A P) : AddrOf b A (R ⋆ P) := fun m r rF hh hp =>
  h.sepL m r rF hh (sep_comm hp)

theorem AddrOf.of_imp {P' : FAssn} (h : AddrOf b A P) (hp : ∀ r, P' r → P r) : AddrOf b A P' :=
  fun m r rF hh h' => h m r rF hh (hp r h')

theorem AddrOf.known : AddrOf b A (known b A) := fun _ _ _ hh hp =>
  hh.know (.addr b A) (by rw [hp.2.1]; rfl)

/-- An owned cell of block `b` gives its address. -/
theorem AddrOf.owned (h : ∀ r, P r → ∃ x fc, r.heap (b, x) = some fc ∧ fc.cell.addr = A) :
    AddrOf b A P := fun _ r _ hh hp => by
  obtain ⟨x, fc, hx, rfl⟩ := h r hp
  obtain ⟨blk, hb, -, -, -, ha, -⟩ := hh.block hx
  exact ⟨blk, hb, ha.symm⟩

theorem Reaches.sepL (h : Reaches b k P) : Reaches b k (P ⋆ R) := fun m _ rF hh hp => by
  obtain ⟨r₁, r₂, hd, rfl, h1, -⟩ := hp
  exact h m r₁ _ (Holds.split hd hh) h1

theorem Reaches.sepR (h : Reaches b k P) : Reaches b k (R ⋆ P) := fun m r rF hh hp =>
  h.sepL m r rF hh (sep_comm hp)

theorem Reaches.of_imp {P' : FAssn} (h : Reaches b k P) (hp : ∀ r, P' r → P r) : Reaches b k P' :=
  fun m r rF hh h' => h m r rF hh (hp r h')

theorem Reaches.mono {k' : Nat} (h : Reaches b k P) (hk : k' ≤ k) : Reaches b k' P :=
  fun m r rF hh hp => by obtain ⟨blk, hb, hs⟩ := h m r rF hh hp; exact ⟨blk, hb, by omega⟩

/-- An owned byte `j` of block `b`: the block has more than `j` bytes. -/
theorem Reaches.owned {j : Nat} (h : ∀ r, P r → ∃ fc, r.heap (b, j) = some fc) :
    Reaches b (j + 1) P := fun _ r _ hh hp => by
  obtain ⟨fc, hx⟩ := h r hp
  obtain ⟨blk, hb, -, hj, -⟩ := hh.block hx
  exact ⟨blk, hb, hj⟩

/-- A share of block `b`'s extent at bound `k`. -/
theorem Reaches.share {q : Frac} : Reaches b k (bshare b q k) := fun _ r _ hh hp => by
  obtain ⟨blk, hb, -, hk, -⟩ := hh.bshare (R := emp) (sep_emp.mpr hp)
  exact ⟨blk, hb, hk⟩

end Providers

/-- Owned cells of a legacy assertion: a cell of the erased heap is a cell of the resource. -/
theorem erase_cell {h : FHeap} {l : Loc} {c : Cell} (hc : h.erase l = some c) :
    ∃ fc, h l = some fc ∧ fc.cell = c := by
  simp only [FHeap.erase, Option.map_eq_some_iff] at hc
  exact hc

/-- `Holds` reads a memory only through its blocks and its atomic layout. -/
theorem Holds.congrMem {m m' : Mem} {r rF : Res} (hb : m'.blocks = m.blocks)
    (ha : m'.atomics = m.atomics) (hh : Holds m r rF) : Holds m' r rF := by
  have e1 : m'.heap = m.heap := by funext ⟨x, o⟩; simp only [Mem.heap, hb]
  have e2 : shapes m' = shapes m := by simp only [shapes, ha]
  have e3 : m'.kn = m.kn := by funext f; cases f <;> simp only [Mem.kn, hb]
  obtain ⟨hd, hm, hk, hkF, hg, ht, hcf⟩ := hh
  refine ⟨hd, ?_, e3 ▸ hk, e3 ▸ hkF, hg, fun x => ?_, fun x hx => hcf x (by rw [← hb]; exact hx)⟩
  · unfold FMatch; rw [e1, e2]; exact hm
  · have := ht x; unfold ECell.TrueIn at this ⊢; simpa only [hb] using this

/-! ## Every triple holds under every placement (M05, `ZigLean/Mem/Reuse.lean`) -/

/-- A memory with another placement and provenance mode holds the same resources. -/
theorem Holds.withPlacement {m : Mem} {r rF : Res} (hh : Holds m r rF) (σ : Placement)
    (pm : ProvenanceMode) : Holds (m.withPlacement σ pm) r rF :=
  Holds.congrMem (m := m) rfl rfl hh

theorem _root_.Zig.Mem.FSeq.withPlacement {m : Mem} (hs : m.FSeq) (σ : Placement)
    (pm : ProvenanceMode) : (m.withPlacement σ pm).FSeq :=
  ⟨⟨hs.1.single⟩, hs.2.1, hs.2.2⟩

/-- **A full-state triple holds from a memory with any placement and provenance mode** (the frame
rule, the allocation and free rules and every client spec built from them are
address-independent): a triple quantifies over every `Mem.FSeq` memory, whatever its placement. -/
theorem FTriple.withPlacement {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}
    (ht : FTriple P c Q) {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : P r) (hs : m.FSeq)
    (σ : Placement) (pm : ProvenanceMode) :
    match (c.run (m.withPlacement σ pm)).run with
    | none => True
    | some (.error e) => e = .stackOverflow
    | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FSeq :=
  ht _ r rF (hh.withPlacement σ pm) hp (hs.withPlacement σ pm)

/-- **A total full-state triple returns from a memory with any placement and provenance mode**,
with its postcondition. -/
theorem FTotalTriple.withPlacement {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}
    (ht : FTotalTriple P c Q) {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : P r) (hs : m.FSeq)
    (σ : Placement) (pm : ProvenanceMode) :
    ∃ v m' r', c.run (m.withPlacement σ pm) = pure (v, m') ∧ Holds m' r' rF ∧ Q v r' ∧ m'.FSeq := by
  obtain ⟨v, m', hr⟩ := ht.2 _ r rF (hh.withPlacement σ pm) hp (hs.withPlacement σ pm)
  have h := ht.1.withPlacement hh hp hs σ pm
  rw [hr] at h
  obtain ⟨r', hh', hq, hs'⟩ := h
  exact ⟨v, m', r', hr, hh', hq, hs'⟩

/-! ## Thread rules

Each rule below holds in a thread (`FTTotalTriple`, `ZigLean/Sep/Full/ThreadStep.lean`): a read
that leaves the memory as it is (`FTTotalTriple.of_read`), or a sequential triple of an owned
access (`FTTotalTriple.ofSeq`, `ThreadLocal.load`/`store`). The sequential rules (next section)
are these rules read sequentially (`FTTotalTriple.toFTotalTriple`). -/

/-- The bytes of `pts` at `q`. -/
theorem OwnsPtr.pts {T : Type} [Enc T] {q : Ptr} {a : Nat} {v : T} :
    OwnsPtr (up (Zig.pts q a v)) q (Enc.size T) := by
  rintro b hqb r ⟨⟨A, S, K, bs, -, hs, -, hb, -⟩, -, -⟩
  rw [← hs]; exact bytesAt_has hb hqb

namespace FTTotalTriple

variable {α : Type} {P : FAssn} {q p : Ptr} {b : BlockId} {A K : Nat}

/-- **`@intFromPtr`** of a pointer into block `b` at address `A`. -/
theorem ptrAddr_of (hqb : q.block = some b) (h : AddrOf b A P) :
    FTTotalTriple P (Zig.ptrAddr q) (fun x => ⟪x = (A : Int) + q.off⟫ ⋆ P) := by
  obtain ⟨qb, qo⟩ := q
  simp only at hqb; subst hqb
  refine of_read fun m r rF hh hp _ => ?_
  obtain ⟨blk, hb, rfl⟩ := h m r rF hh hp
  exact ptrAddr_run hb qo

/-- **The model's `@alignCast` check** of a pointer at an address that `al` divides. -/
theorem checkAlign_of {al : Nat} (hqb : q.block = some b) (h : AddrOf b A P)
    (hal : ((A : Int) + q.off) % al = 0) : FTTotalTriple P (checkAlign al q) (fun _ => P) := by
  unfold checkAlign
  refine bind (ptrAddr_of hqb h) fun x => lift fun hx => ?_
  subst hx
  rw [if_neg (by simp [hal])]
  exact ret (Q := fun _ => P) ()

/-- **Pointer `==`** of two pointers into one block: their offsets are equal (MM-4). -/
theorem ptrEqAddr_of (hpb : p.block = some b) (hqb : q.block = some b) (h : AddrOf b A P) :
    FTTotalTriple P (ptrEqAddr p q) (fun r => ⟪r = decide (p.off = q.off)⟫ ⋆ P) := by
  unfold ptrEqAddr
  refine bind (ptrAddr_of hpb h) fun x => lift fun hx => ?_
  refine bind (ptrAddr_of hqb h) fun y => lift fun hy => ?_
  subst hx hy
  exact conseq (ret (Q := fun r => ⟪r = decide (p.off = q.off)⟫ ⋆ P) _)
    (fun _ hh => sep_lift.mpr ⟨by simp, hh⟩) (fun _ _ h => h)

/-- **Pointer formation** (`ptrProject`, MM-3) of a byte offset `k` of `q` that stays within the
first `K` bytes of a block that reaches `K`. -/
theorem ptrProject_of {k : Int} (hqb : q.block = some b) (h : Reaches b K P) (h0 : 0 ≤ q.off)
    (hq : q.off ≤ K) (hk0 : 0 ≤ q.off + k) (hk : q.off + k ≤ K) :
    FTTotalTriple P (ptrProject q (·.add k)) (fun r => ⟪r = q.add k⟫ ⋆ P) :=
  of_read fun m r rF hh hp _ => by
    obtain ⟨blk, hb, hK⟩ := h m r rF hh hp
    exact ptrProject_add_run (inBounds_of hqb hb h0 (by omega))
      (inBounds_of (p := q.add k) hqb hb (by simp [Ptr.add]; omega) (by simp [Ptr.add]; omega))

/-- `ptrProject_of` for an item pointer `q.elem size i`. -/
theorem ptrProject_elem_of {size : Nat} {i : BitVec 64} (hqb : q.block = some b)
    (h : Reaches b K P) (h0 : 0 ≤ q.off) (hk : q.off + ((size * i.toNat : Nat) : Int) ≤ K) :
    FTTotalTriple P (ptrProject q (·.elem size i)) (fun r => ⟪r = q.elem size i⟫ ⋆ P) := by
  have e : (fun x : Ptr => x.elem size i) = (·.add ((size * i.toNat : Nat) : Int)) := by
    funext x; exact Ptr.elem_eq x size i
  rw [e, Ptr.elem_eq]
  exact ptrProject_of hqb h h0 (by omega) (by omega) hk

/-- **Load** of a typed value (`pts`) in a thread. -/
theorem load {T : Type} [Enc T] {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    FTTotalTriple (up (pts q a v)) (Zig.load T a q) (fun x => ⟪x = v⟫ ⋆ up (pts q a v)) :=
  ofSeq ((FTotalTriple.ofTotal_up (TotalTriple.load hn) (Tame.load T a q) (SizeFree.pts q a v)
    (Keeps.load T a q)).post fun _ _ h => sep_lift.mpr (up_lift.mp h))
    (ThreadLocal.load hn OwnsPtr.pts)

/-- **Store** of a typed value (`pts`) in a thread. -/
theorem store {T : Type} [Enc T] [LawfulEnc T] {a : Nat} {v : T} (hn : 0 < Enc.size T) (w : T) :
    FTTotalTriple (up (pts q a v)) (Zig.store a q w) (fun _ => up (pts q a w)) :=
  ofSeq (FTotalTriple.ofTotal_up (TotalTriple.store hn w) (Tame.store a q w) (SizeFree.pts q a v)
    (Keeps.store a q w))
    (ThreadLocal.store (by rw [LawfulEnc.size_encode]; exact hn)
      (by rw [LawfulEnc.size_encode]; exact OwnsPtr.pts))

end FTTotalTriple

/-! ## Rules -/

namespace FTotalTriple

variable {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}

theorem of_run
    (h : ∀ m r rF, Holds m r rF → P r → m.FSeq →
      ∃ v m' r', c.run m = pure (v, m') ∧ Holds m' r' rF ∧ Q v r' ∧ m'.FSeq) :
    FTotalTriple P c Q :=
  ⟨FTriple.of_run h, fun m r rF hh hp hs => by
    obtain ⟨v, m', -, hr, -⟩ := h m r rF hh hp hs; exact ⟨v, m', hr⟩⟩

/-- A step that returns `v` and leaves the memory as it is. -/
theorem of_read {v : α} (h : ∀ m r rF, Holds m r rF → P r → m.FSeq → c.run m = pure (v, m)) :
    FTotalTriple P c (fun x => ⟪x = v⟫ ⋆ P) :=
  of_run fun m r rF hh hp hs => ⟨v, m, r, h m r rF hh hp hs, hh, sep_lift.mpr ⟨rfl, hp⟩, hs⟩

variable {q p : Ptr} {b : BlockId} {A K : Nat}

/-- **`@intFromPtr`** of a pointer into block `b` at address `A`. -/
theorem ptrAddr_of (hqb : q.block = some b) (h : AddrOf b A P) :
    FTotalTriple P (Zig.ptrAddr q) (fun x => ⟪x = (A : Int) + q.off⟫ ⋆ P) :=
  (FTTotalTriple.ptrAddr_of hqb h).toFTotalTriple

/-- **The model's `@alignCast` check** of a pointer at an address that `al` divides. -/
theorem checkAlign_of {al : Nat} (hqb : q.block = some b) (h : AddrOf b A P)
    (hal : ((A : Int) + q.off) % al = 0) : FTotalTriple P (checkAlign al q) (fun _ => P) :=
  (FTTotalTriple.checkAlign_of hqb h hal).toFTotalTriple

/-- **Pointer `==`** of two pointers into one block: their offsets are equal (MM-4). -/
theorem ptrEqAddr_of (hpb : p.block = some b) (hqb : q.block = some b) (h : AddrOf b A P) :
    FTotalTriple P (ptrEqAddr p q) (fun r => ⟪r = decide (p.off = q.off)⟫ ⋆ P) :=
  (FTTotalTriple.ptrEqAddr_of hpb hqb h).toFTotalTriple

/-- **Pointer formation** (`ptrProject`, MM-3) of a byte offset `k` of `q` that stays within the
first `K` bytes of a block that reaches `K`. -/
theorem ptrProject_of {k : Int} (hqb : q.block = some b) (h : Reaches b K P) (h0 : 0 ≤ q.off)
    (hq : q.off ≤ K) (hk0 : 0 ≤ q.off + k) (hk : q.off + k ≤ K) :
    FTotalTriple P (ptrProject q (·.add k)) (fun r => ⟪r = q.add k⟫ ⋆ P) :=
  (FTTotalTriple.ptrProject_of hqb h h0 hq hk0 hk).toFTotalTriple

/-- `ptrProject_of` for an item pointer `q.elem size i`. -/
theorem ptrProject_elem_of {size : Nat} {i : BitVec 64} (hqb : q.block = some b)
    (h : Reaches b K P) (h0 : 0 ≤ q.off) (hk : q.off + ((size * i.toNat : Nat) : Int) ≤ K) :
    FTotalTriple P (ptrProject q (·.elem size i)) (fun r => ⟪r = q.elem size i⟫ ⋆ P) :=
  (FTTotalTriple.ptrProject_elem_of hqb h h0 hk).toFTotalTriple

/-- **Load** of a typed value (`pts`). -/
theorem load {T : Type} [Enc T] {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    FTotalTriple (up (pts q a v)) (Zig.load T a q) (fun x => ⟪x = v⟫ ⋆ up (pts q a v)) :=
  (FTTotalTriple.load hn).toFTotalTriple

/-- **Store** of a typed value (`pts`). -/
theorem store {T : Type} [Enc T] [LawfulEnc T] {a : Nat} {v : T} (hn : 0 < Enc.size T) (w : T) :
    FTotalTriple (up (pts q a v)) (Zig.store a q w) (fun _ => up (pts q a w)) :=
  (FTTotalTriple.store hn w).toFTotalTriple

end FTotalTriple

end Full
end Zig
