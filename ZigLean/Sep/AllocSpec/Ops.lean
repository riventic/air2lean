import ZigLean.Sep.AllocSpec.Region
import ZigLean.Sep.Block
import ZigLean.Mem.Null

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
  exact ⟨hst.1⟩

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
  obtain ⟨blk, hblk, -, ho, hcb⟩ := Mem.heap_some this
  subst hcb
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

/-- The model's `@alignCast` check (`Zig.checkAlign`, MM) of a pointer into a block of which the
precondition owns a cell, at an address that `al` divides: no effect. -/
theorem checkAlign_owned {P : Assn} {q : Ptr} {b : BlockId} {A al : Nat} (hqb : q.block = some b)
    (hown : ∀ h, P h → OwnsIn b A h) (hal : ((A : Int) + q.off) % al = 0) :
    TotalTriple P (checkAlign al q) (fun _ => P) := by
  unfold checkAlign
  refine TotalTriple.bind (ptrAddr_owned hqb hown) fun r => TotalTriple.lift fun hr => ?_
  subst hr
  rw [if_neg (by simp [hal])]
  exact TotalTriple.ret (Q := fun _ => P) ()

/-- `h` owns the cell at offset `j` of block `b`. -/
def OwnsAt (b : BlockId) (j : Nat) (h : Heap) : Prop := ∃ c, h (b, j) = some c

/-- A nonempty `bytesAt` owns the cell of its last byte. -/
theorem bytesAt_ownsAt {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {h : Heap}
    (hb : bytesAt p A S K bs h) (hpos : 0 < bs.size) :
    ∃ b, p.block = some b ∧ 0 ≤ p.off ∧ OwnsAt b (p.off.toNat + (bs.size - 1)) h := by
  obtain ⟨b, hpb, h0, hl⟩ := hb
  refine ⟨b, hpb, h0, ⟨bs[bs.size - 1]!, A, S, K⟩, ?_⟩
  rw [hl]; simp only [true_and]; rw [if_pos ⟨by omega, by omega⟩]; congr 3; omega

theorem OwnsAt.union_left {b : BlockId} {j : Nat} {h₁ h₂ : Heap} (h : OwnsAt b j h₁) :
    OwnsAt b j (h₁ ∪ h₂) := by
  obtain ⟨c, hc⟩ := h; exact ⟨c, by simp [hc]⟩

theorem OwnsAt.union_right {b : BlockId} {j : Nat} {h₁ h₂ : Heap} (h : OwnsAt b j h₂)
    (hd : Heap.Disjoint h₁ h₂) : OwnsAt b j (h₁ ∪ h₂) := by
  rw [Heap.union_comm hd]; exact h.union_left

/-- Pointer formation (`ptrProject`, MM-3) of a byte offset `k ≥ 0` from `q`, when the
precondition owns a cell of `q`'s block at an offset at or past `q.off + k - 1`: the block reaches
`q + k`, so both are in bounds and the offset pointer is formed, with no effect. -/
theorem ptrProject_ownsAt {P : Assn} {q : Ptr} {b : BlockId} {j : Nat} {k : Int}
    (hqb : q.block = some b) (h0 : 0 ≤ q.off) (hk : 0 ≤ k) (hj : q.off + k ≤ (j : Int) + 1)
    (hown : ∀ h, P h → OwnsAt b j h) :
    TotalTriple P (ptrProject q (·.add k)) (fun r => ⌜r = q.add k⌝ ∗ P) := by
  intro m hP hF hd hm hp hst
  obtain ⟨c, hc⟩ := hown hP hp
  have : m.heap (b, j) = some c := by rw [hm]; simp [hc]
  obtain ⟨blk, hblk, -, hjs, -⟩ := Mem.heap_some this
  refine ⟨_, m, hP, ptrProject_add_run (inBounds_of hqb hblk h0 (by omega))
    (inBounds_of (p := q.add k) hqb hblk (by simp [Ptr.add]; omega) (by simp [Ptr.add]; omega)),
    hd, hm, sep_lift.mpr ⟨rfl, hp⟩, hst⟩

/-- `ptrProject_ownsAt` for an item pointer `q.elem size i`. -/
theorem ptrProject_elem_ownsAt {P : Assn} {q : Ptr} {b : BlockId} {j size : Nat} {i : BitVec 64}
    (hqb : q.block = some b) (h0 : 0 ≤ q.off) (hj : q.off + ((size * i.toNat : Nat) : Int) ≤ (j : Int) + 1)
    (hown : ∀ h, P h → OwnsAt b j h) :
    TotalTriple P (ptrProject q (·.elem size i)) (fun r => ⌜r = q.elem size i⌝ ∗ P) := by
  have e : (fun x : Ptr => x.elem size i) = (·.add ((size * i.toNat : Nat) : Int)) := by
    funext x; exact Ptr.elem_eq x size i
  rw [e, Ptr.elem_eq]
  exact ptrProject_ownsAt hqb h0 (by omega) hj hown

/-- The model's bounds check of a slicing that is in bounds: no effect. -/
theorem checkSliceEnd_ok {srcLen start len : BitVec 64} {extra : Nat}
    (h : start.toNat + len.toNat + extra ≤ srcLen.toNat) : checkSliceEnd srcLen start len extra = pure () := by
  simp [checkSliceEnd, h]

/-- The model's address check of `@ptrFromInt` (`Zig.checkAddr`) of an aligned address: no
effect. -/
theorem checkAddr_ok {align n : Nat} (h : n % align = 0) : checkAddr align false n = pure () := by
  simp [checkAddr, h]

theorem checkIndex_ok {s : Slice} {i : BitVec 64} (h : i.toNat < s.len.toNat) :
    checkIndex s i = pure () := by
  simp [checkIndex, h]

theorem checkSentinelIndex_ok {s : Slice} {i : BitVec 64} (h : i.toNat ≤ s.len.toNat) :
    checkSentinelIndex s i = pure () := by
  simp [checkSentinelIndex, h]

/-- `@memcpy` with equal counts whose ranges the precondition shows apart is `@memmove`. -/
theorem TotalTriple.memcpy_of {P : Assn} {Q : Unit → Assn} {size da sa : Nat} {d s : Ptr}
    {n : BitVec 64}
    (hsep : ∀ (m : Mem) (h hF : Heap), m.heap = h ∪ hF → P h → d.overlaps s (n.toNat * size) = false)
    (ht : TotalTriple P (memmove size da sa d s n) Q) : TotalTriple P (memcpy size da sa d s n n) Q := by
  intro m hP hF hd hm hp hst
  have := hsep m hP hF hm hp
  unfold memcpy
  rw [if_neg (by simp [this])]
  exact ht m hP hF hd hm hp hst

/-- Two cells of one block in a part of the memory's heap record the block's address. -/
theorem cell_addr_eq {m : Mem} {h hF : Heap} (hm : m.heap = h ∪ hF) {b : BlockId} {x y : Nat}
    {c₁ c₂ : Cell} (h₁ : h (b, x) = some c₁) (h₂ : h (b, y) = some c₂) : c₁.addr = c₂.addr := by
  have e₁ : m.heap (b, x) = some c₁ := by rw [hm]; simp [h₁]
  have e₂ : m.heap (b, y) = some c₂ := by rw [hm]; simp [h₂]
  obtain ⟨blk, hb, -, -, rfl⟩ := Mem.heap_some e₁
  obtain ⟨blk', hb', -, -, rfl⟩ := Mem.heap_some e₂
  rw [hb] at hb'; cases hb'; rfl

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

/-- `pts` with the block's address `A`, size `S` and kind `K` explicit, so that adjacent values
of one block rejoin into its bytes (`bytesAt_append`). -/
def ptsM {T : Type} [Enc T] (p : Ptr) (A S : Nat) (K : BlockKind) (a : Nat) (v : T) : Assn :=
  fun h => (A + p.off.toNat) % a = 0 ∧ K ≠ .constGlobal ∧
    ∃ bs, bs.size = Enc.size T ∧ Enc.decode bs = pure v ∧ bytesAt p A S K bs h

theorem ptsM_pts {T : Type} [Enc T] {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {v : T}
    {h : Heap} (hp : ptsM p A S K a v h) : pts p a v h := by
  obtain ⟨ha, hK, bs, hs, hv, hb⟩ := hp
  exact ⟨A, S, K, bs, ha, hs, hv, hb, hK⟩

theorem ptsM_load {T : Type} [Enc T] {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {v : T}
    (hn : 0 < Enc.size T) :
    TotalTriple (ptsM p A S K a v) (load T a p) (fun r => ⌜r = v⌝ ∗ ptsM p A S K a v) := by
  intro m hP hF hd hm hp hst
  obtain ⟨m', hr, hheap, hs'⟩ := pts_load_run (ptsM_pts hp) hm hn hst
  exact ⟨v, m', hP, hr, hd, hheap, sep_lift.mpr ⟨rfl, hp⟩, hs'⟩

theorem ptsM_store {T : Type} [Enc T] [LawfulEnc T] {p : Ptr} {A S : Nat} {K : BlockKind}
    {a : Nat} {v : T} (hn : 0 < Enc.size T) (w : T) :
    TotalTriple (ptsM p A S K a v) (store a p w) (fun _ => ptsM p A S K a w) := by
  intro m hP hF hd hm hp hst
  obtain ⟨ha, hK, bs, hs, -, hb⟩ := hp
  have hw := LawfulEnc.size_encode w
  obtain ⟨m', hrun, hst', h', hd', hm', hb'⟩ :=
    bytesAt_store (q := p) (k := 0) (a := a) (bs' := Enc.encode w) hb hm hd (by simp [Ptr.add])
      (by omega) (by omega) (by simpa using ha) hst hK
  refine ⟨(), m', h', hrun, hd', hm', ⟨ha, hK, _, ?_, ?_, hb'⟩, hst'⟩ <;>
    rw [writeBytes_all (by omega)]
  · exact hw
  · exact LawfulEnc.decode_encode w

/-- Use a pure fact that the precondition implies. -/
theorem TotalTriple.of_pure {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn} {φ : Prop}
    (hφ : ∀ h, P h → φ) (ht : φ → TotalTriple P c Q) : TotalTriple P c Q := by
  intro m hP hF hd hm hp hst
  exact ht (hφ hP hp) m hP hF hd hm hp hst

theorem regionIn_facts {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}
    {h : Heap} (hr : regionIn p A S K a bs h) :
    (A + p.off.toNat) % a = 0 ∧ 0 ≤ p.off ∧ K ≠ .constGlobal ∧ p.block.isSome := by
  obtain ⟨ha, hK, b, hpb, h0, -⟩ := hr
  exact ⟨ha, h0, hK, by simp [hpb]⟩

/-- A load of an item from the bytes of a region. -/
theorem loadItemIn {T : Type} [Enc T] {p : Ptr} {A S : Nat} {K : BlockKind} {a al o : Nat}
    {bs : Array Byte} {v : T} (hpos : 0 < Enc.size T) (ho : o + Enc.size T ≤ bs.size)
    (hal : al ∣ a) (halo : al ∣ o) (hv : Enc.decode (bs.extract o (o + Enc.size T)) = pure v) :
    TotalTriple (regionIn p A S K a bs) (load T al (p.add o))
      (fun r => ⌜r = v⌝ ∗ regionIn p A S K a bs) := by
  intro m hP hF hd hm hp hst
  obtain ⟨hA, hK, hb⟩ := id hp
  have ha : (A + p.off.toNat + o) % al = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_trans hal (Nat.dvd_of_mod_eq_zero hA)) halo)
  obtain ⟨b, blk, hacc, -, -, -, hx⟩ :=
    bytesAt_access (q := p.add o) (k := o) (n := Enc.size T) (a := al) hb hm rfl hpos ho ha
  have hv' : Enc.decode (blk.bytes.extract (p.off.toNat + o) (p.off.toNat + o + Enc.size T)) =
      pure v := by rw [hx]; exact hv
  refine ⟨v, _, hP, load_run hacc hv' (noRace_of_singleThread hst.single _ _ _ _), hd, ?_,
    sep_lift.mpr ⟨rfl, hp⟩, hst.recordAt _ _ _ _⟩
  funext l; rw [Mem.heap_recordAt]; exact congrFun hm l

/-! ## Arithmetic of the wrappers' checks -/

namespace Ops

/-- The `@alignCast` test passes for an address that is a multiple of `2 ^ k`. -/
theorem and_mask_eq_zero {x : Int} {k : Nat} (hk : k < 64) (h0 : 0 ≤ x) (hx : x % 2 ^ k = 0) :
    (BitVec.ofInt 64 x &&& BitVec.ofNat 64 (2 ^ k - 1)) = 0 := by
  obtain ⟨N, rfl⟩ : ∃ N : Nat, x = N := ⟨x.toNat, (Int.toNat_of_nonneg h0).symm⟩
  have hN : N % 2 ^ k = 0 := by exact_mod_cast hx
  have hpk : 2 ^ k ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (Nat.le_of_lt hk)
  have hlt : 2 ^ k - 1 < 2 ^ 64 := by
    have := Nat.pow_lt_pow_right (a := 2) (by decide) hk; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.ofInt_natCast, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hlt, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ hpk, hN]
  rfl

/-- `math.mul(usize, size, n)` overflows exactly when the product reaches `2 ^ 64`. -/
theorem umulOverflow_ofNat {size : Nat} (hs : size < 2 ^ 64) (n : BitVec 64) :
    (BitVec.ofNat 64 size).umulOverflow n = decide (2 ^ 64 ≤ size * n.toNat) := by
  simp [BitVec.umulOverflow, Nat.mod_eq_of_lt hs]

theorem toNat_mul_ofNat {size : Nat} (hs : size < 2 ^ 64) {n : BitVec 64}
    (h : size * n.toNat < 2 ^ 64) : (BitVec.ofNat 64 size * n).toNat = size * n.toNat := by
  simp [BitVec.toNat_mul, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt h]

theorem two_pow_lt {k : Nat} (hk : k < 64) : 2 ^ k < 2 ^ 64 :=
  Nat.pow_lt_pow_right (by decide) hk

theorem toNat_two_pow {k : Nat} (hk : k < 64) : (BitVec.ofNat 64 (2 ^ k)).toNat = 2 ^ k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (two_pow_lt hk)]

/-- A checked `+` that does not overflow. -/
theorem add_ok {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    Zig.add false a b = pure (a + b) := by
  simp only [Zig.add, BitVec.uaddOverflow, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by simp; omega)]

theorem gt_eq (a b : BitVec 64) : Zig.gt false a b = decide (b.toNat < a.toNat) := by
  simp [Zig.gt, Zig.lt, BitVec.ult]

theorem lt_eq (a b : BitVec 64) : Zig.lt false a b = decide (a.toNat < b.toNat) := by
  simp [Zig.lt, BitVec.ult]

theorem le_eq (a b : BitVec 64) : Zig.le false a b = decide (a.toNat ≤ b.toNat) := by
  simp [Zig.le, BitVec.ule]

end Ops


/-! ## Coverage of a byte range of a block -/

/-- `h` has every byte `[lo, hi)` of block `b`. -/
def Covers (b : BlockId) (lo hi : Nat) (h : Heap) : Prop := ∀ i, lo ≤ i → i < hi → h (b, i) ≠ none

/-- `h` owns a byte of block `b`, whose size is `S` and kind `K`. -/
def Pins (b : BlockId) (S : Nat) (K : BlockKind) (h : Heap) : Prop :=
  ∃ o c, h (b, o) = some c ∧ c.size = S ∧ c.kind = K

theorem regionIn_pins {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte} {h : Heap}
    {b : BlockId} (hr : regionIn p A S K a bs h) (hb : p.block = some b) (hpos : 0 < bs.size) :
    Pins b S K h := by
  obtain ⟨-, -, b', hb', -, hl⟩ := hr
  rw [hb] at hb'; cases hb'
  refine ⟨p.off.toNat, ⟨bs[0]!, A, S, K⟩, ?_, rfl, rfl⟩
  rw [hl]; simp [hpos]

/-- Coverage survives a command whose frame keeps a byte `G` of the block: the block stays live
with its size and kind, so its bytes from the kind's first live offset on that the frame does not
have are still owned. -/
theorem TotalTriple.covers {α : Type} {P G : Assn} {c : MemM α} {Q : α → Assn} {b : BlockId}
    {S lo hi : Nat} {K : BlockKind} (ht : TotalTriple P c Q) (hG : ∀ h, G h → Pins b S K h)
    (hhi : hi ≤ S) (hK : K.mappedLo ≤ lo) :
    TotalTriple (fun h => (P ∗ G) h ∧ Covers b lo hi h) c
      (fun v h => (Q v ∗ G) h ∧ Covers b lo hi h) := by
  intro m hP hF hd hm ⟨hp, hcov⟩ hst
  obtain ⟨v, m', hQ, hr, hd', hm', hq, hst'⟩ := (TotalTriple.frame (R := G) ht) m hP hF hd hm hp hst
  refine ⟨v, m', hQ, hr, hd', hm', ⟨hq, ?_⟩, hst'⟩
  intro i hlo hlt
  obtain ⟨hq₁, hq₂, hd₁₂, rfl, -, hg⟩ := hq
  obtain ⟨o, c', hc', hcS, hcK⟩ := hG _ hg
  have hpin : m'.heap (b, o) = some c' := by rw [hm']; simp [Heap.union_of_right (hd₁₂ (b, o) |>.resolve_right (by simp [hc'])), hc']
  obtain ⟨blk, hblk, hlive, ho, hc⟩ := Mem.heap_some hpin
  have hsz : blk.bytes.size = S := by rw [← hcS, hc]
  have hk : blk.kind = K := by rw [← hcK, hc]
  have hin : m'.heap (b, i) ≠ none := by
    simp [Mem.heap, hblk, hlive, hsz, hk]; omega
  have hFi : hF (b, i) = none := (hd (b, i)).resolve_left (hcov i hlo hlt)
  rw [hm', Heap.union_apply, hFi, Option.or_none] at hin
  exact hin

/-- `free` of a whole block: its bytes go. -/
theorem free_whole {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {R : Assn}
    (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S) :
    TotalTriple (bytesAt p A S K bs ∗ R) (free p) (fun _ => R) := by
  intro m hP hF hd hm hp hst
  obtain ⟨h₁, h₂, hd₁₂, rfl, hb, hr⟩ := hp
  obtain ⟨hd₁F, hd₂F⟩ := Heap.disjoint_union_left.mp hd
  have hm₁ : m.heap = h₁ ∪ (h₂ ∪ hF) := by rw [hm, Heap.union_assoc]
  obtain ⟨m', hrun, hm', hst', -⟩ := free_run hb hm₁ (Heap.disjoint_union_right.mpr ⟨hd₁₂, hd₁F⟩)
    hS h0 hpos hst
  exact ⟨(), m', h₂, hrun, hd₂F, by rw [hm', Heap.empty_union], hr, hst'⟩

/-- `ptrProject_elem_ownsAt` for an item pointer into a nonempty region, at most one past it. -/
theorem ptrProject_elem_region {p : Ptr} {A S : Nat} {K : BlockKind} {a size : Nat}
    {bs : Array Byte} {i : BitVec 64} (hpos : 0 < bs.size) (hi : size * i.toNat ≤ bs.size) :
    TotalTriple (regionIn p A S K a bs) (ptrProject p (·.elem size i))
      (fun r => ⌜r = p.elem size i⌝ ∗ regionIn p A S K a bs) := by
  refine TotalTriple.of_pure (φ := ∃ b, p.block = some b ∧ 0 ≤ p.off)
    (fun h hr => let ⟨b, hb, h0, _⟩ := bytesAt_ownsAt hr.2.2 hpos; ⟨b, hb, h0⟩)
    fun ⟨b, hb, h0⟩ => ptrProject_elem_ownsAt (j := p.off.toNat + (bs.size - 1)) hb h0
      (by push_cast; omega) fun h hr => ?_
  obtain ⟨b', hb', -, ho⟩ := bytesAt_ownsAt hr.2.2 hpos
  rw [hb] at hb'; cases hb'; exact ho

/-- `h` owns a cell of block `b`; cells record their block's byte count `S`. -/
def OwnsSz (b : BlockId) (S : Nat) (h : Heap) : Prop :=
  ∃ o c, h (b, o) = some c ∧ c.size = S

theorem OwnsSz.union_left {b : BlockId} {S : Nat} {h₁ h₂ : Heap} (h : OwnsSz b S h₁) :
    OwnsSz b S (h₁ ∪ h₂) := by
  obtain ⟨o, c, hc, hS⟩ := h; exact ⟨o, c, by simp [hc], hS⟩

theorem OwnsSz.union_right {b : BlockId} {S : Nat} {h₁ h₂ : Heap} (h : OwnsSz b S h₂)
    (hd : Heap.Disjoint h₁ h₂) : OwnsSz b S (h₁ ∪ h₂) := by
  rw [Heap.union_comm hd]; exact h.union_left

/-- A nonempty `bytesAt` owns a cell that records its block's size. -/
theorem bytesAt_ownsSz {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {h : Heap}
    (hb : bytesAt p A S K bs h) (hpos : 0 < bs.size) : ∃ b, p.block = some b ∧ OwnsSz b S h := by
  obtain ⟨b, hpb, -, hl⟩ := hb
  refine ⟨b, hpb, p.off.toNat, ⟨bs[0]!, A, S, K⟩, ?_, rfl⟩
  rw [hl]; simp [hpos]

/-- Pointer formation (`ptrProject`, MM-3) of an offset of `q` that stays in `[0, S]` of a block
whose size `S` an owned cell records: formed, no effect. -/
theorem ptrProject_sized {P : Assn} {q : Ptr} {b : BlockId} {S : Nat} {k : Int}
    (hqb : q.block = some b) (h0 : 0 ≤ q.off) (hq : q.off ≤ S) (hk0 : 0 ≤ q.off + k)
    (hk : q.off + k ≤ S) (hown : ∀ h, P h → OwnsSz b S h) :
    TotalTriple P (ptrProject q (·.add k)) (fun r => ⌜r = q.add k⌝ ∗ P) := by
  intro m hP hF hd hm hp hst
  obtain ⟨o, c, hc, hS⟩ := hown hP hp
  have : m.heap (b, o) = some c := by rw [hm]; simp [hc]
  obtain ⟨blk, hblk, -, ho, hcb⟩ := Mem.heap_some this
  have hS' : blk.bytes.size = S := by rw [← hS, hcb]
  refine ⟨_, m, hP, ptrProject_add_run (inBounds_of hqb hblk h0 (by omega))
    (inBounds_of (p := q.add k) hqb hblk (by simp [Ptr.add]; omega) (by simp [Ptr.add]; omega)),
    hd, hm, sep_lift.mpr ⟨rfl, hp⟩, hst⟩

/-- `ptrProject_sized` for an item pointer `q.elem size i`. -/
theorem ptrProject_elem_sized {P : Assn} {q : Ptr} {b : BlockId} {S size : Nat} {i : BitVec 64}
    (hqb : q.block = some b) (h0 : 0 ≤ q.off) (hk : q.off + ((size * i.toNat : Nat) : Int) ≤ S)
    (hown : ∀ h, P h → OwnsSz b S h) :
    TotalTriple P (ptrProject q (·.elem size i)) (fun r => ⌜r = q.elem size i⌝ ∗ P) := by
  have e : (fun x : Ptr => x.elem size i) = (·.add ((size * i.toNat : Nat) : Int)) := by
    funext x; exact Ptr.elem_eq x size i
  rw [e, Ptr.elem_eq]
  exact ptrProject_sized hqb h0 (by omega) (by omega) hk hown

/-- `==` of two pointers into one block of which the precondition owns a cell (MM-4): their
offsets are equal. -/
theorem ptrEqAddr_owned {P : Assn} {p q : Ptr} {b : BlockId} {A : Nat} (hp : p.block = some b)
    (hq : q.block = some b) (hown : ∀ h, P h → OwnsIn b A h) :
    TotalTriple P (ptrEqAddr p q) (fun r => ⌜r = decide (p.off = q.off)⌝ ∗ P) := by
  unfold ptrEqAddr
  refine TotalTriple.bind (ptrAddr_owned hp hown) fun x => TotalTriple.lift fun hx => ?_
  refine TotalTriple.bind (ptrAddr_owned hq hown) fun y => TotalTriple.lift fun hy => ?_
  subst hx hy
  refine TotalTriple.conseq (TotalTriple.ret (Q := fun r => ⌜r = decide (p.off = q.off)⌝ ∗ P) _)
    (fun h hh => sep_lift.mpr ⟨?_, hh⟩) (fun _ _ h => h)
  simp

end Zig
