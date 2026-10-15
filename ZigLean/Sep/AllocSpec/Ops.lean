import ZigLean.Sep.AllocSpec.Region
import ZigLean.Mem.Null

/-!
# Ownership facts for the other operations of translated allocators and wrappers

* `OwnsIn`/`OwnsAt`/`OwnsSz`: a heap owns a cell of a block (with its address, at an offset,
  with its size), what `ptrAddr` (`@intFromPtr`), `ptrLe` and pointer formation of a block need
  to know. Nothing about the address itself is assumed: it is whatever the placement chose, read
  from the owned cell.
* `ptsR`: a typed value that a load can read, in any block, including a `const` global (a
  vtable): `pts` without the write permission. `ptsM`: `pts` with its block data explicit.
* `Covers`/`Pins`: the bytes of a byte range of a block, and a byte that pins the block.
* The arithmetic of the wrappers' checks (`Ops.*`) and the checks that pass (`check*_ok`).

Vocabulary only, no program judgment: the full-state rules for these operations are in
`ZigLean/Sep/Full/` (`docs/proof-framework.md`). Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig

open Assn

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

/-- The model's bounds check of a slicing that is in bounds: no effect. -/
theorem checkSliceEnd_ok {srcLen start len : BitVec 64} {extra : Nat}
    (h : start.toNat + len.toNat + extra ≤ srcLen.toNat) : checkSliceEnd srcLen start len extra = pure () := by
  simp [checkSliceEnd, h]

/-- The model's address check of `@ptrFromInt` (`Zig.checkAddr`) of an aligned address: no
effect. -/
theorem checkAddr_ok {align n : Nat} (h : n % align = 0) : checkAddr align false n = pure () := by
  simp [checkAddr, h]

theorem checkIndex_ok {n : Nat} {len i : BitVec n} (h : i.toNat < len.toNat) :
    checkIndex len i = pure () := by
  simp [checkIndex, h]

theorem checkSentinelIndex_ok {n : Nat} {len i : BitVec n} (h : i.toNat ≤ len.toNat) :
    checkSentinelIndex len i = pure () := by
  simp [checkSentinelIndex, h]

/-- Two cells of one block in a part of the memory's heap record the block's address. -/
theorem cell_addr_eq {m : Mem} {h hF : Heap} (hm : m.heap = h ∪ hF) {b : BlockId} {x y : Nat}
    {c₁ c₂ : Cell} (h₁ : h (b, x) = some c₁) (h₂ : h (b, y) = some c₂) : c₁.addr = c₂.addr := by
  have e₁ : m.heap (b, x) = some c₁ := by rw [hm]; simp [h₁]
  have e₂ : m.heap (b, y) = some c₂ := by rw [hm]; simp [h₂]
  obtain ⟨blk, hb, -, -, rfl⟩ := Mem.heap_some e₁
  obtain ⟨blk', hb', -, -, rfl⟩ := Mem.heap_some e₂
  rw [hb] at hb'; cases hb'; rfl

/-- `p` points to `v`, readable with alignment `a`, in a block of any kind (a `const` global
too): a read-only `pts`. -/
def ptsR {T : Type} [Enc T] (p : Ptr) (a : Nat) (v : T) : Assn := fun h =>
  ∃ A S K bs, (A + p.off.toNat) % a = 0 ∧ bs.size = Enc.size T ∧ Enc.decode bs = pure v ∧
    bytesAt p A S K bs h

/-- `pts` with the block's address `A`, size `S` and kind `K` explicit, so that adjacent values
of one block rejoin into its bytes (`bytesAt_append`). -/
def ptsM {T : Type} [Enc T] (p : Ptr) (A S : Nat) (K : BlockKind) (a : Nat) (v : T) : Assn :=
  fun h => (A + p.off.toNat) % a = 0 ∧ K ≠ .constGlobal ∧
    ∃ bs, bs.size = Enc.size T ∧ Enc.decode bs = pure v ∧ bytesAt p A S K bs h

theorem ptsM_pts {T : Type} [Enc T] {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {v : T}
    {h : Heap} (hp : ptsM p A S K a v h) : pts p a v h := by
  obtain ⟨ha, hK, bs, hs, hv, hb⟩ := hp
  exact ⟨A, S, K, bs, ha, hs, hv, hb, hK⟩

theorem regionIn_facts {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}
    {h : Heap} (hr : regionIn p A S K a bs h) :
    (A + p.off.toNat) % a = 0 ∧ 0 ≤ p.off ∧ K ≠ .constGlobal ∧ p.block.isSome := by
  obtain ⟨ha, hK, b, hpb, h0, -⟩ := hr
  exact ⟨ha, h0, hK, by simp [hpb]⟩

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

end Zig
