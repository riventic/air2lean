import ZigLean.Sep.AllocSpec.Region
import ZigLean.Sep.Block

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

end Ops


/-! ## Coverage of a byte range of a block -/

/-- `h` has every byte `[lo, hi)` of block `b`. -/
def Covers (b : BlockId) (lo hi : Nat) (h : Heap) : Prop := ∀ i, lo ≤ i → i < hi → h (b, i) ≠ none

/-- `h` owns a byte of block `b`, whose size is `S`. -/
def Pins (b : BlockId) (S : Nat) (h : Heap) : Prop := ∃ o c, h (b, o) = some c ∧ c.size = S

theorem regionIn_pins {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte} {h : Heap}
    {b : BlockId} (hr : regionIn p A S K a bs h) (hb : p.block = some b) (hpos : 0 < bs.size) :
    Pins b S h := by
  obtain ⟨-, -, b', hb', -, hl⟩ := hr
  rw [hb] at hb'; cases hb'
  refine ⟨p.off.toNat, ⟨bs[0]!, A, S, K⟩, ?_, rfl⟩
  rw [hl]; simp [hpos]

/-- Coverage survives a command whose frame keeps a byte `G` of the block: the block stays live
with its size, so its bytes that the frame does not have are still owned. -/
theorem TotalTriple.covers {α : Type} {P G : Assn} {c : MemM α} {Q : α → Assn} {b : BlockId}
    {S lo hi : Nat} (ht : TotalTriple P c Q) (hG : ∀ h, G h → Pins b S h) (hhi : hi ≤ S) :
    TotalTriple (fun h => (P ∗ G) h ∧ Covers b lo hi h) c
      (fun v h => (Q v ∗ G) h ∧ Covers b lo hi h) := by
  intro m hP hF hd hm ⟨hp, hcov⟩ hst
  obtain ⟨v, m', hQ, hr, hd', hm', hq, hst'⟩ := (TotalTriple.frame (R := G) ht) m hP hF hd hm hp hst
  refine ⟨v, m', hQ, hr, hd', hm', ⟨hq, ?_⟩, hst'⟩
  intro i hlo hlt
  obtain ⟨hq₁, hq₂, hd₁₂, rfl, -, hg⟩ := hq
  obtain ⟨o, c', hc', hcS⟩ := hG _ hg
  have hpin : m'.heap (b, o) = some c' := by rw [hm']; simp [Heap.union_of_right (hd₁₂ (b, o) |>.resolve_right (by simp [hc'])), hc']
  obtain ⟨blk, hblk, hlive, ho, hc⟩ := Mem.heap_some hpin
  have hsz : blk.bytes.size = S := by rw [← hcS, hc]
  have hin : m'.heap (b, i) ≠ none := by
    simp [Mem.heap, hblk, hlive, hsz]; omega
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

end Zig
