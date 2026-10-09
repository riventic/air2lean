import ZigLean.Sep.AllocSpec.Region

/-!
# Triples for the other operations of translated allocators and wrappers

* `returnAddress` (`@returnAddress()`, the oracle `arbitraryWord`): changes no assertion.
* `ptrAddr` (`@intFromPtr`) of a pointer into a block of which the precondition owns a cell: the
  block's address (which every cell records) plus the offset. Nothing about the address itself
  is assumed: it is whatever the placement chose, read from the owned cell.
* `ptrLe` of two such pointers.
* `ptsR`: a typed value that a load can read, in any block, including a `const` global (a
  vtable): `pts` without the write permission.

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig

open Assn

/-- `@returnAddress()` reads the oracle and changes nothing else. -/
theorem returnAddress_triple {P : Assn} : TotalTriple P returnAddress (fun _ => P) := by
  intro m hP hF hd hm hp hst
  refine ⟨_, { m with arbitraryNext := m.arbitraryNext + 1 }, hP, rfl, hd, hm, hp, ?_⟩
  exact ⟨hst.1, hst.2⟩

/-- `h` owns a cell of block `b` with address `A`. -/
def OwnsIn (b : BlockId) (A : Nat) (h : Heap) : Prop :=
  ∃ o c, h (b, o) = some c ∧ c.addr = A

theorem OwnsIn.union_left {b : BlockId} {A : Nat} {h₁ h₂ : Heap} (h : OwnsIn b A h₁) :
    OwnsIn b A (h₁ ∪ h₂) := by
  obtain ⟨o, c, hc, hA⟩ := h; exact ⟨o, c, by simp [hc], hA⟩

theorem OwnsIn.union_right {b : BlockId} {A : Nat} {h₁ h₂ : Heap} (hd : Heap.Disjoint h₁ h₂)
    (h : OwnsIn b A h₂) : OwnsIn b A (h₁ ∪ h₂) := by
  rw [Heap.union_comm hd]; exact h.union_left

/-- The block of an owned cell exists, with the cell's address. -/
theorem OwnsIn.block {m : Mem} {b : BlockId} {A : Nat} {h hF : Heap} (ho : OwnsIn b A h)
    (hm : m.heap = h ∪ hF) : ∃ blk, m.blocks[b]? = some blk ∧ blk.addr = A := by
  obtain ⟨o, c, hc, hA⟩ := ho
  have : m.heap (b, o) = some c := by rw [hm]; simp [hc]
  obtain ⟨blk, hblk, -, -, rfl⟩ := Mem.heap_some this
  exact ⟨blk, hblk, hA⟩

/-- A nonempty `bytesAt` owns a cell of its block. -/
theorem bytesAt_ownsIn {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {h : Heap}
    (hb : bytesAt p A S K bs h) (hpos : 0 < bs.size) :
    ∃ b, p.block = some b ∧ OwnsIn b A h := by
  obtain ⟨b, hpb, -, hl⟩ := hb
  refine ⟨b, hpb, p.off.toNat, ⟨bs[0]!, A, S, K⟩, ?_, rfl⟩
  rw [hl]; simp [hpos]

theorem regionIn_ownsIn {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}
    {h : Heap} (hr : regionIn p A S K a bs h) (hpos : 0 < bs.size) :
    ∃ b, p.block = some b ∧ OwnsIn b A h :=
  bytesAt_ownsIn hr.2.2 hpos

/-- `ptrAddr q` for `q` in a block of which the precondition owns a cell with address `A`. -/
theorem ptrAddr_owned {P : Assn} {q : Ptr} {b : BlockId} {A : Nat} (hqb : q.block = some b)
    (hown : ∀ h, P h → OwnsIn b A h) :
    TotalTriple P (ptrAddr q) (fun r => ⌜r = (A : Int) + q.off⌝ ∗ P) := by
  intro m hP hF hd hm hp hst
  obtain ⟨blk, hblk, hA⟩ := (hown hP hp).block hm
  refine ⟨_, m, hP, ?_, hd, hm, sep_lift.mpr ⟨rfl, hp⟩, hst⟩
  simp [ptrAddr, hqb, hblk, hA, zig_unfold, get, getThe, MonadStateOf.get, StateT.get]

/-- `ptrLe x y` for `x`, `y` in blocks of which the precondition owns cells. -/
theorem ptrLe_owned {P : Assn} {x y : Ptr} {b₁ b₂ : BlockId} {A₁ A₂ : Nat}
    (hx : x.block = some b₁) (hy : y.block = some b₂) (h₁ : ∀ h, P h → OwnsIn b₁ A₁ h)
    (h₂ : ∀ h, P h → OwnsIn b₂ A₂ h) :
    TotalTriple P (ptrLe x y)
      (fun r => ⌜r = decide ((A₁ : Int) + x.off ≤ (A₂ : Int) + y.off)⌝ ∗ P) := by
  intro m hP hF hd hm hp hst
  obtain ⟨blk₁, hblk₁, hA₁⟩ := (h₁ hP hp).block hm
  obtain ⟨blk₂, hblk₂, hA₂⟩ := (h₂ hP hp).block hm
  refine ⟨_, m, hP, ?_, hd, hm, sep_lift.mpr ⟨rfl, hp⟩, hst⟩
  simp [ptrLe, ptrAddr, hx, hy, hblk₁, hblk₂, hA₁, hA₂, zig_unfold, get, getThe,
    MonadStateOf.get, StateT.get]

/-- `p` points to `v`, readable with alignment `a`, in a block of any kind (a `const` global
too): a read-only `pts`. -/
def ptsR {T : Type} [Enc T] (p : Ptr) (a : Nat) (v : T) : Assn := fun h =>
  ∃ A S K bs, (A + p.off.toNat) % a = 0 ∧ bs.size = Enc.size T ∧ Enc.decode bs = pure v ∧
    bytesAt p A S K bs h

theorem ptsR_load {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    TotalTriple (ptsR p a v) (load T a p) (fun r => ⌜r = v⌝ ∗ ptsR p a v) := by
  intro m hP hF hd hm hp hst
  obtain ⟨A, S, K, bs, ha, hs, hv, hb⟩ := id hp
  obtain ⟨b, blk, hacc, -, -, -, hx⟩ :=
    bytesAt_access (q := p) (k := 0) (n := Enc.size T) (a := a) hb hm (by simp [Ptr.add])
      hn (by omega) (by simpa using ha)
  simp only [Nat.add_zero] at hx
  have hv' : Enc.decode (blk.bytes.extract p.off.toNat (p.off.toNat + Enc.size T)) = pure v := by
    rw [hx, show bs.extract 0 (0 + Enc.size T) = bs by rw [← hs]; simp]; exact hv
  refine ⟨v, _, hP, load_run (by simpa using hacc) hv' (noRace_of_singleThread hst.single _ _ _ _),
    hd, ?_, sep_lift.mpr ⟨rfl, hp⟩, hst.recordAt _ _ _ _⟩
  funext l; rw [Mem.heap_recordAt]; exact congrFun hm l

end Zig
