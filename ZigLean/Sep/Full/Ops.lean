import ZigLean.Sep.Full.Extent
import ZigLean.Sep.Full.Tame

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
  hh.know b A (by rw [hp.2.1]; exact ⟨rfl, rfl⟩)

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
    FTotalTriple P (Zig.ptrAddr q) (fun x => ⟪x = (A : Int) + q.off⟫ ⋆ P) := by
  obtain ⟨qb, qo⟩ := q
  simp only at hqb; subst hqb
  refine of_read fun m r rF hh hp _ => ?_
  obtain ⟨blk, hb, rfl⟩ := h m r rF hh hp
  exact ptrAddr_run hb qo

/-- **The model's `@alignCast` check** of a pointer at an address that `al` divides. -/
theorem checkAlign_of {al : Nat} (hqb : q.block = some b) (h : AddrOf b A P)
    (hal : ((A : Int) + q.off) % al = 0) : FTotalTriple P (checkAlign al q) (fun _ => P) := by
  unfold checkAlign
  refine bind (ptrAddr_of hqb h) fun x => lift fun hx => ?_
  subst hx
  rw [if_neg (by simp [hal])]
  exact ret (Q := fun _ => P) ()

/-- **Pointer `==`** of two pointers into one block: their offsets are equal (MM-4). -/
theorem ptrEqAddr_of (hpb : p.block = some b) (hqb : q.block = some b) (h : AddrOf b A P) :
    FTotalTriple P (ptrEqAddr p q) (fun r => ⟪r = decide (p.off = q.off)⟫ ⋆ P) := by
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
    FTotalTriple P (ptrProject q (·.add k)) (fun r => ⟪r = q.add k⟫ ⋆ P) :=
  of_read fun m r rF hh hp _ => by
    obtain ⟨blk, hb, hK⟩ := h m r rF hh hp
    exact ptrProject_add_run (inBounds_of hqb hb h0 (by omega))
      (inBounds_of (p := q.add k) hqb hb (by simp [Ptr.add]; omega) (by simp [Ptr.add]; omega))

/-- `ptrProject_of` for an item pointer `q.elem size i`. -/
theorem ptrProject_elem_of {size : Nat} {i : BitVec 64} (hqb : q.block = some b)
    (h : Reaches b K P) (h0 : 0 ≤ q.off) (hk : q.off + ((size * i.toNat : Nat) : Int) ≤ K) :
    FTotalTriple P (ptrProject q (·.elem size i)) (fun r => ⟪r = q.elem size i⟫ ⋆ P) := by
  have e : (fun x : Ptr => x.elem size i) = (·.add ((size * i.toNat : Nat) : Int)) := by
    funext x; exact Ptr.elem_eq x size i
  rw [e, Ptr.elem_eq]
  exact ptrProject_of hqb h h0 (by omega) (by omega) hk

/-- **Load** of a typed value (`pts`, lifted). -/
theorem load {T : Type} [Enc T] {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    FTotalTriple (up (pts q a v)) (Zig.load T a q) (fun x => ⟪x = v⟫ ⋆ up (pts q a v)) :=
  (FTotalTriple.ofTotal_up (TotalTriple.load hn) (Tame.load T a q) (SizeFree.pts q a v)
    (Keeps.load T a q)).post fun _ _ h => sep_lift.mpr (up_lift.mp h)

/-- **Store** of a typed value (`pts`, lifted). -/
theorem store {T : Type} [Enc T] [LawfulEnc T] {a : Nat} {v : T} (hn : 0 < Enc.size T) (w : T) :
    FTotalTriple (up (pts q a v)) (Zig.store a q w) (fun _ => up (pts q a w)) :=
  FTotalTriple.ofTotal_up (TotalTriple.store hn w) (Tame.store a q w) (SizeFree.pts q a v)
    (Keeps.store a q w)

end FTotalTriple

end Full
end Zig
