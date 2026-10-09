import ZigLean.Sep.AllocSpec.Wrap
import ZigLean.Sep.AllocSpec.Ops
import ZigLean.Sep.AllocSpec.Norm
import ZigLean.Sep.Automation

/-!
# Contracts of the `std.mem.Allocator` wrappers over any allocator that satisfies `AllocSpec`

`Wrap.*` (`ZigLean/Sep/AllocSpec/Wrap.lean`) are the step semantics of the wrappers of
`lib/std/mem/Allocator.zig` (Zig 0.16.0) as the compiler emits them. Each `*_spec` theorem proves
a wrapper's contract in any logic `L` from `AllocSpec L vt ctx I` alone. A translated wrapper gets
the same contract because it is equal to its `Wrap.*` (`tests/roadmap/alloc-fba/AllocFba/Bridge.lean`).

`owned I k p bs` is what a client owns for a slice: nothing for zero bytes (the pointer is a
constant without a block), else the granted region.

Premises beyond `AllocSpec`, each a check in the generated code:

* `I.fits n k` for each request that reaches the allocator (its arithmetic range);
* for `dupe` and the copying path of `realloc`: the two ranges of the `@memcpy` are disjoint as
  address ranges (`RangeSep`), which the generated code checks with two `ptrLe`. Two owned byte
  ranges of one block are (`GrantSep` holds for an allocator whose token fixes the block); for
  two blocks it is a fact about their placement that the client supplies (`SrcSep`). The memory
  model's `Mem.Seq` does not say that live blocks have disjoint address ranges.
-/

/-- Close an assertion goal from a hypothesis with the same separating conjuncts. -/
macro "sep_from " h:ident : tactic =>
  `(tactic| first
    | exact $h
    | (sep_normalize at $h:ident ⊢; exact $h)
    | (sep_normalize at $h:ident; exact $h)
    | (sep_normalize; exact $h))

namespace Zig

open Assn

theorem sep_ex_right {γ : Type} {P : Assn} {Q : γ → Assn} {h : Heap} :
    (P ∗ Assn.ex Q) h ↔ ∃ x, (P ∗ Q x) h := by
  constructor
  · rintro ⟨h₁, h₂, hd, rfl, hp, x, hq⟩; exact ⟨x, h₁, h₂, hd, rfl, hp, hq⟩
  · rintro ⟨x, h₁, h₂, hd, rfl, hp, hq⟩; exact ⟨h₁, h₂, hd, rfl, hp, x, hq⟩

theorem sep_lift_right {φ : Prop} {P Q : Assn} {h : Heap} :
    (P ∗ (⌜φ⌝ ∗ Q)) h ↔ φ ∧ (P ∗ Q) h := by
  rw [sep_left_comm_eq]; exact sep_lift

/-- Two address ranges `[x, x + n₁)` and `[y, y + n₂)` do not overlap. -/
def RangeSep (x : Int) (n₁ : Nat) (y : Int) (n₂ : Nat) : Prop := x + n₁ ≤ y ∨ y + n₂ ≤ x

theorem RangeSep.mono {x y : Int} {n₁ n₂ m : Nat} (h : RangeSep x n₁ y n₂) (h₁ : m ≤ n₁)
    (h₂ : m ≤ n₂) : RangeSep x m y m := by
  unfold RangeSep at *; omega

/-- Any two nonempty regions that `I` granted with alignment `2 ^ k` have disjoint address ranges
(the copying path of `realloc`). -/
def GrantSep (I : AllocInv) (k : Nat) : Prop :=
  ∀ (h : Heap) (p q : Ptr) (bs bs' : Array Byte) (A S A' S' : Nat) (K K' : BlockKind),
    0 < bs.size → 0 < bs'.size →
    ((regionIn p A S K (2 ^ k) bs ∗ I.tok p bs.size k A S K) ∗
      (regionIn q A' S' K' (2 ^ k) bs' ∗ I.tok q bs'.size k A' S' K')) h →
    RangeSep ((A : Int) + p.off) bs.size ((A' : Int) + q.off) bs'.size

/-- Every nonempty region that `I` grants with alignment `2 ^ k` is disjoint, as an address range,
from the source `src` (address `A'`) of a `dupe`. -/
def SrcSep (I : AllocInv) (k : Nat) (src : Ptr) (A' S' : Nat) (K' : BlockKind) (a' : Nat)
    (bsrc : Array Byte) : Prop :=
  ∀ (h : Heap) (d : Ptr) (bs : Array Byte) (A S : Nat) (K : BlockKind), 0 < bs.size →
    ((regionIn d A S K (2 ^ k) bs ∗ I.tok d bs.size k A S K) ∗ regionIn src A' S' K' a' bsrc) h →
    RangeSep ((A : Int) + d.off) bs.size ((A' : Int) + src.off) bsrc.size

namespace Wrap

/-- The owned bytes of an allocated slice (module doc). -/
def owned (I : AllocInv) (k : Nat) (p : Ptr) (bs : Array Byte) : Assn :=
  if bs.size = 0 then emp else granted I p k bs

theorem owned_zero {I : AllocInv} {k : Nat} {p : Ptr} {bs : Array Byte} (h : bs.size = 0) :
    owned I k p bs = emp := by simp [owned, h]

theorem owned_pos {I : AllocInv} {k : Nat} {p : Ptr} {bs : Array Byte} (h : bs.size ≠ 0) :
    owned I k p bs = granted I p k bs := by simp [owned, h]

/-- The result of an allocation of `n` undefined bytes. -/
def allocResult (I : AllocInv) (k n : Nat) : Except ErrName Ptr → Assn
  | .ok p => I.own ∗ owned I k p (Array.replicate n .undef)
  | .error e => ⌜e = outOfMemory⌝ ∗ I.own

/-- The result of an allocation of a slice of `len` items, `n` undefined bytes. -/
def sliceResult (I : AllocInv) (k : Nat) (len : BitVec 64) (n : Nat) : Except ErrName Slice → Assn
  | .ok s => ⌜s.len = len⌝ ∗ (I.own ∗ owned I k s.ptr (Array.replicate n .undef))
  | .error e => ⌜e = outOfMemory⌝ ∗ I.own

/-- A request that reaches the allocator is within its range. -/
def Fits (I : AllocInv) (n k : Nat) : Prop := 0 < n → n < 2 ^ 64 → I.fits n k

variable {vt : RawVTable} {ctx : Ptr} {L : Logic} {I : AllocInv}

/-! ## Structural helpers -/

theorem Logic.of_pure {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn} {φ : Prop}
    (hφ : ∀ h, P h → φ) (ht : φ → L.T P c Q) : L.T P c Q :=
  L.pre (L.lift ht) fun h hp => sep_lift.mpr ⟨hφ h hp, hp⟩

/-- Open the result of a successful `alloc`, under a frame `R`. -/
theorem granted_ex {α : Type} {c : MemM α} {Q : α → Assn} {p : Ptr} {k n : Nat} {R : Assn}
    (hc : ∀ bs, bs.size = n → L.T ((I.own ∗ granted I p k bs) ∗ R) c Q) :
    L.T ((I.own ∗ Assn.ex fun bs => ⌜bs.size = n⌝ ∗ granted I p k bs) ∗ R) c Q := by
  refine L.pre (L.ex (P := fun bs => ⌜bs.size = n⌝ ∗ ((I.own ∗ granted I p k bs) ∗ R))
    fun bs => L.lift fun hs => hc bs hs) ?_
  rintro h ⟨h₁, h₂, hd, rfl, hq, hr⟩
  obtain ⟨bs, hq⟩ := sep_ex_right.mp hq
  obtain ⟨hs, hq⟩ := sep_lift_right.mp hq
  exact ⟨bs, sep_lift.mpr ⟨hs, h₁, h₂, hd, rfl, hq, hr⟩⟩

theorem granted_ex' {α : Type} {c : MemM α} {Q : α → Assn} {p : Ptr} {k n : Nat}
    (hc : ∀ bs, bs.size = n → L.T (I.own ∗ granted I p k bs) c Q) :
    L.T (I.own ∗ Assn.ex fun bs => ⌜bs.size = n⌝ ∗ granted I p k bs) c Q :=
  L.pre (granted_ex (R := emp) fun bs hs => L.pre (hc bs hs) fun _ hp => sep_emp.mp hp)
    fun _ hp => sep_emp.mpr hp

/-- Open a granted region: its block is some `A`, `S`, `K`. -/
theorem granted_open {α : Type} {c : MemM α} {Q : α → Assn} {p : Ptr} {k : Nat}
    {bs : Array Byte} {R : Assn}
    (hc : ∀ A S K, L.T (R ∗ (regionIn p A S K (2 ^ k) bs ∗ I.tok p bs.size k A S K)) c Q) :
    L.T (R ∗ granted I p k bs) c Q := by
  refine L.pre (L.ex fun A => L.ex fun S => L.ex fun K => hc A S K) ?_
  rintro h ⟨h₁, h₂, hd, rfl, hr, A, S, K, hg⟩
  exact ⟨A, S, K, h₁, h₂, hd, rfl, hr, hg⟩

theorem granted_intro {p : Ptr} {k : Nat} {bs : Array Byte} {A S : Nat} {K : BlockKind}
    {h : Heap} (hg : (regionIn p A S K (2 ^ k) bs ∗ I.tok p bs.size k A S K) h) :
    granted I p k bs h := ⟨A, S, K, hg⟩

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ne_zero_toNat {n : BitVec 64} (h : ¬ n = 0) : 0 < n.toNat := by
  rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
  · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) h
  · exact h0

theorem ret_eq {α : Type} {P : Assn} {v : α} :
    TotalTriple P (pure v : MemM α) (fun r => ⌜r = v⌝ ∗ P) :=
  TotalTriple.conseq (TotalTriple.ret (Q := fun r => ⌜r = v⌝ ∗ P) v)
    (fun _ hp => sep_lift.mpr ⟨rfl, hp⟩) (fun _ _ h => h)

/-- Apply a premise about part of the heap. -/
theorem sep_part {P Q : Assn} {φ : Prop} {h : Heap} (hp : (P ∗ Q) h) (hq : ∀ h', Q h' → φ) : φ := by
  obtain ⟨-, h₂, -, -, -, hq'⟩ := hp; exact hq h₂ hq'

/-- `alignCast` of a pointer to a nonempty region aligned to `2 ^ k` succeeds. -/
theorem alignCast_spec {p : Ptr} {A S : Nat} {K : BlockKind} {k : Nat} {bs : Array Byte}
    (hk : k < 64) (hpos : 0 < bs.size) :
    TotalTriple (regionIn p A S K (2 ^ k) bs) (alignCast k p)
      (fun r => ⌜r = .ok p⌝ ∗ regionIn p A S K (2 ^ k) bs) := by
  unfold alignCast
  split
  · exact ret_eq
  refine TotalTriple.of_pure (fun h hr => regionIn_facts hr) fun ⟨ha, h0, _, hb⟩ => ?_
  obtain ⟨b, hpb⟩ := Option.isSome_iff_exists.mp hb
  refine TotalTriple.bind (ptrAddr_owned (A := A) hpb fun h hr => ?_) fun r => ?_
  · obtain ⟨b', hpb', ho⟩ := regionIn_ownsIn hr hpos
    rw [hpb] at hpb'; cases hpb'; exact ho
  refine TotalTriple.lift fun hr => ?_
  subst hr
  have hx : ((A : Int) + p.off) % 2 ^ k = 0 := by
    have : ((A + p.off.toNat : Nat) : Int) % ((2 ^ k : Nat) : Int) = 0 := by exact_mod_cast ha
    rw [Int.natCast_add, Int.toNat_of_nonneg h0] at this; exact_mod_cast this
  rw [if_pos (Ops.and_mask_eq_zero hk (by omega) hx)]
  exact ret_eq

/-! ## Allocation -/

theorem allocBytes_spec (h : AllocSpec L vt ctx I) (k : Nat) (n ra : BitVec 64) (hk : k < 64)
    (hfit : Fits I n.toNat k) :
    L.T I.own (allocBytes vt ctx k n ra) (allocResult I k n.toNat) := by
  unfold allocBytes
  split
  · rename_i h0
    refine L.ret' _ fun hh hp => ?_
    simp only [allocResult]
    rw [owned_zero (by simp [h0])]
    exact sep_emp.mpr hp
  · rename_i h0
    have hn := ne_zero_toNat h0
    refine L.bind (h.alloc n k ra hn hk (hfit hn n.isLt)) fun r => ?_
    cases r with
    | none => exact L.ret' _ fun hh hp => sep_lift.mpr ⟨rfl, hp⟩
    | some p =>
      dsimp only
      refine granted_ex' fun bs hs => granted_open fun A S K => ?_
      refine L.bind (L.pre (L.frame (R := I.own ∗ I.tok p bs.size k A S K)
        (L.ofTotal (Region.memsetUndefIn (p := p) (A := A) (S := S) (K := K) (a := 2 ^ k)
          (n := n) hs.symm)))
        fun hh hp => by sep_normalize at hp ⊢; exact hp) fun _ => ?_
      refine L.conseq (L.frame (R := I.own ∗ I.tok p bs.size k A S K)
        (L.ofTotal (alignCast_spec (p := p) (A := A) (S := S) (K := K)
          (bs := Array.replicate n.toNat Byte.undef) hk (by simpa using hn))))
        (fun hh hp => hp) fun r hh hp => ?_
      obtain ⟨hr, hp'⟩ := sep_lift.mp (sep_assoc hp)
      subst hr
      simp only [allocResult]
      rw [owned_pos (by rw [Array.size_replicate]; omega)]
      have e : (Array.replicate n.toNat Byte.undef).size = bs.size := by simp [hs]
      have hz : (I.own ∗ (regionIn p A S K (2 ^ k) (Array.replicate n.toNat Byte.undef) ∗
          I.tok p (Array.replicate n.toNat Byte.undef).size k A S K)) hh := by
        rw [e, sep_left_comm_eq]; exact hp'
      exact sep_mono (fun _ x => x) (fun _ x => granted_intro x) hz

theorem allocItems_spec (h : AllocSpec L vt ctx I) (size k : Nat) (n ra : BitVec 64)
    (hk : k < 64) (hs : size < 2 ^ 64) (hfit : Fits I (size * n.toNat) k) :
    L.T I.own (allocItems vt ctx size k n ra) (allocResult I k (size * n.toNat)) := by
  unfold allocItems
  rw [Ops.umulOverflow_ofNat hs]
  split
  · exact L.ret' _ fun hh hp => sep_lift.mpr ⟨rfl, hp⟩
  · rename_i hov
    have hlt : size * n.toNat < 2 ^ 64 := by simpa using hov
    have := allocBytes_spec h k (BitVec.ofNat 64 size * n) ra hk
      (by rw [Ops.toNat_mul_ofNat hs hlt]; exact hfit)
    rwa [Ops.toNat_mul_ofNat hs hlt] at this

theorem allocAdvanced_spec (h : AllocSpec L vt ctx I) (size k : Nat) (n ra : BitVec 64)
    (hk : k < 64) (hs : size < 2 ^ 64) (hfit : Fits I (size * n.toNat) k) :
    L.T I.own (allocAdvanced vt ctx size k n ra) (sliceResult I k n (size * n.toNat)) := by
  refine L.bind (allocItems_spec h size k n ra hk hs hfit) fun r => ?_
  cases r with
  | error e => exact L.ret' _ fun hh hp => hp
  | ok p => exact L.ret' _ fun hh hp => sep_lift.mpr ⟨rfl, hp⟩

/-- `alloc(T, n)` / `alignedAlloc(T, k, n)`: `n` items of `size` bytes, undefined. -/
theorem allocSlice_spec (h : AllocSpec L vt ctx I) (size k : Nat) (n : BitVec 64)
    (hk : k < 64) (hs : size < 2 ^ 64) (hfit : Fits I (size * n.toNat) k) :
    L.T I.own (allocSlice vt ctx size k n) (sliceResult I k n (size * n.toNat)) :=
  L.bind (L.ofTotal returnAddress_triple) fun ra => allocAdvanced_spec h size k n ra hk hs hfit

/-- `create(T)`: one item of `size` bytes, undefined. -/
theorem create_spec (h : AllocSpec L vt ctx I) (size k : Nat) (hk : k < 64)
    (hs : size < 2 ^ 64) (hfit : Fits I size k) :
    L.T I.own (create vt ctx size k) (allocResult I k size) := by
  unfold create
  split
  · rename_i h0
    subst h0
    refine L.ret' _ fun hh hp => ?_
    simp only [allocResult]
    rw [owned_zero (by simp)]
    exact sep_emp.mpr hp
  · refine L.bind (L.ofTotal returnAddress_triple) fun ra => ?_
    have := allocBytes_spec h k (BitVec.ofNat 64 size) ra hk (by rw [toNat_ofNat_lt hs]; exact hfit)
    rwa [toNat_ofNat_lt hs] at this

/-- `destroy(p)` of what `create` returned. -/
theorem destroy_spec (h : AllocSpec L vt ctx I) (size k : Nat) (p : Ptr) (bs : Array Byte)
    (hk : k < 64) (hsz : bs.size = size) (hs : size < 2 ^ 64) :
    L.T (I.own ∗ owned I k p bs) (destroy vt ctx size k p) (fun _ => I.own) := by
  unfold destroy
  split
  · rename_i h0
    refine L.ret' _ fun hh hp => ?_
    rw [owned_zero (by omega)] at hp
    exact sep_emp.mp hp
  · rename_i h0
    rw [owned_pos (by omega)]
    refine L.bind (L.ofTotal returnAddress_triple) fun ra => ?_
    exact h.free ⟨p, BitVec.ofNat 64 size⟩ k ra bs hk
      (by show (BitVec.ofNat 64 size).toNat = bs.size; rw [toNat_ofNat_lt hs, hsz]) (by omega)

/-! ## Free -/

/-- `free` of a byte slice: the bytes go back to the allocator. -/
theorem freeBytes_spec (h : AllocSpec L vt ctx I) (k : Nat) (s : Slice) (bs : Array Byte)
    (hk : k < 64) (hsz : bs.size = s.len.toNat) :
    L.T (I.own ∗ owned I k s.ptr bs) (freeBytes vt ctx k s) (fun _ => I.own) := by
  unfold freeBytes
  split
  · rename_i h0
    refine L.ret' _ fun hh hp => ?_
    rw [owned_zero (by simp [hsz, h0])] at hp
    exact sep_emp.mp hp
  · rename_i h0
    have hn := ne_zero_toNat h0
    rw [owned_pos (by omega)]
    refine granted_open fun A S K => ?_
    refine L.bind (L.pre (L.frame (R := I.own ∗ I.tok s.ptr bs.size k A S K)
      (L.ofTotal (Region.memsetUndefIn (p := s.ptr) (A := A) (S := S) (K := K) (a := 2 ^ k)
        (n := s.len) hsz.symm)))
      fun hh hp => by sep_normalize at hp ⊢; exact hp) fun _ => ?_
    refine L.bind (L.ofTotal returnAddress_triple) fun ra => ?_
    refine L.pre (h.free s k ra (Array.replicate s.len.toNat .undef) hk (by simp) (by simp; omega)) ?_
    intro hh hp
    have e : (Array.replicate s.len.toNat Byte.undef).size = bs.size := by simp [hsz]
    have hz : (I.own ∗ (regionIn s.ptr A S K (2 ^ k) (Array.replicate s.len.toNat Byte.undef) ∗
        I.tok s.ptr (Array.replicate s.len.toNat Byte.undef).size k A S K)) hh := by
      rw [e]; sep_from hp
    exact sep_mono (fun _ x => x) (fun _ x => granted_intro x) hz

/-- `free(memory)`: the slice's bytes go back to the allocator. -/
theorem free_spec (h : AllocSpec L vt ctx I) (size k : Nat) (s : Slice) (bs : Array Byte)
    (hk : k < 64) (hsz : bs.size = s.len.toNat * size) (hs : bs.size < 2 ^ 64) :
    L.T (I.own ∗ owned I k s.ptr bs) (free vt ctx size k s) (fun _ => I.own) :=
  freeBytes_spec h k ⟨s.ptr, byteLen size s⟩ bs hk
    (by show bs.size = (byteLen size s).toNat; unfold byteLen; rw [← hsz, toNat_ofNat_lt hs])

/-- `free` of a sentinel-terminated slice of `len` items: `len + 1` items go back. -/
theorem freeSentinel_spec (h : AllocSpec L vt ctx I) (size k : Nat) (s : Slice) (bs : Array Byte)
    (hk : k < 64) (hn : s.len.toNat + 1 < 2 ^ 64) (hsz : bs.size = (s.len.toNat + 1) * size)
    (hs : bs.size < 2 ^ 64) :
    L.T (I.own ∗ owned I k s.ptr bs) (freeSentinel vt ctx size k s) (fun _ => I.own) := by
  have e : Zig.add false s.len 1 = pure (s.len + 1) := by
    simp only [Zig.add, BitVec.uaddOverflow, Bool.false_eq_true, ↓reduceIte]
    rw [if_neg (by simp; omega)]
  unfold freeSentinel
  rw [e]
  have e1 : (s.len + 1).toNat = s.len.toNat + 1 := by
    rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl]; exact Nat.mod_eq_of_lt hn
  exact free_spec h size k ⟨s.ptr, s.len + 1⟩ bs hk (by rw [hsz]; show _ = (s.len + 1).toNat * size; rw [e1]) hs

/-! ## Copies -/

/-- The checked `@memcpy` of `n` items of `size` bytes between two nonempty regions whose address
ranges are disjoint. -/
theorem copyChecked_spec {d s : Ptr} {A S A' S' : Nat} {K K' : BlockKind} {a a' da sa size : Nat}
    {bd bsrc : Array Byte} {n : BitVec 64} (hpos : 0 < n.toNat * size)
    (hnd : n.toNat * size ≤ bd.size) (hns : n.toNat * size ≤ bsrc.size) (hda : da ∣ a)
    (hsa : sa ∣ a') (hsep : RangeSep ((A : Int) + d.off) (n.toNat * size) ((A' : Int) + s.off)
      (n.toNat * size)) :
    TotalTriple (regionIn d A S K a bd ∗ regionIn s A' S' K' a' bsrc) (copyChecked size da sa d s n)
      (fun _ => regionIn d A S K a (writeBytes bd 0 (bsrc.extract 0 (n.toNat * size))) ∗
        regionIn s A' S' K' a' bsrc) := by
  unfold copyChecked
  refine TotalTriple.of_pure (φ := (∃ b, d.block = some b) ∧ (∃ b, s.block = some b) ∧
    0 ≤ d.off ∧ 0 ≤ s.off) (fun h hp => ?_) fun ⟨⟨bd', hbd⟩, ⟨bs', hbs⟩, h0d, h0s⟩ => ?_
  · obtain ⟨h₁, h₂, -, rfl, hr₁, hr₂⟩ := hp
    have f₁ := regionIn_facts hr₁; have f₂ := regionIn_facts hr₂
    exact ⟨Option.isSome_iff_exists.mp f₁.2.2.2, Option.isSome_iff_exists.mp f₂.2.2.2, f₁.2.1, f₂.2.1⟩
  have own₁ : ∀ h, (regionIn d A S K a bd ∗ regionIn s A' S' K' a' bsrc) h → OwnsIn bd' A h := by
    rintro h ⟨h₁, h₂, hdj, rfl, hr₁, -⟩
    obtain ⟨b, hb, ho⟩ := regionIn_ownsIn hr₁ (by omega)
    rw [hbd] at hb; cases hb; exact ho.union_left
  have own₂ : ∀ h, (regionIn d A S K a bd ∗ regionIn s A' S' K' a' bsrc) h → OwnsIn bs' A' h := by
    rintro h ⟨h₁, h₂, hdj, rfl, -, hr₂⟩
    obtain ⟨b, hb, ho⟩ := regionIn_ownsIn hr₂ (by omega)
    rw [hbs] at hb; cases hb; exact ho.union_right hdj
  refine TotalTriple.bind (ptrLe_owned (x := s.elem size n) (y := d) hbs hbd own₂ own₁)
    fun b₁ => TotalTriple.lift fun hb₁ => ?_
  refine TotalTriple.bind (ptrLe_owned (x := d.elem size n) (y := s) hbd hbs own₁ own₂)
    fun b₂ => TotalTriple.lift fun hb₂ => ?_
  subst hb₁ hb₂
  have he : ∀ q : Ptr, (q.elem size n).off = q.off + ((n.toNat * size : Nat) : Int) := fun q => by
    simp [Ptr.elem, Ptr.add, Nat.mul_comm]
  unfold RangeSep at hsep
  rw [if_pos (by simp only [Bool.or_eq_true, decide_eq_true_eq, he]; omega)]
  exact Region.memcpyIn hnd hns hda hsa

/-- The result of `dupe`: a copy of the source bytes. -/
def dupeResult (I : AllocInv) (k : Nat) (src : Slice) (A' S' : Nat) (K' : BlockKind) (a' : Nat)
    (bsrc : Array Byte) : Except ErrName Slice → Assn
  | .ok d => ⌜d.len = src.len⌝ ∗ (I.own ∗ (owned I k d.ptr bsrc ∗ regionIn src.ptr A' S' K' a' bsrc))
  | .error e => ⌜e = outOfMemory⌝ ∗ (I.own ∗ regionIn src.ptr A' S' K' a' bsrc)

/-- `dupe(T, m)`: a fresh copy of the `size * m.len` bytes at `m` (nonempty). -/
theorem dupe_spec (h : AllocSpec L vt ctx I) (size k sa a' : Nat) (src : Slice) {A' S' : Nat}
    {K' : BlockKind} (bsrc : Array Byte) (hk : k < 64) (hsz : bsrc.size = src.len.toNat * size)
    (hpos : 0 < bsrc.size) (hs : size < 2 ^ 64) (hsa : sa ∣ a')
    (hfit : Fits I (size * src.len.toNat) k) (hsep : SrcSep I k src.ptr A' S' K' a' bsrc) :
    L.T (I.own ∗ regionIn src.ptr A' S' K' a' bsrc) (dupe vt ctx size k sa src)
      (dupeResult I k src A' S' K' a' bsrc) := by
  have hsize : size * src.len.toNat = bsrc.size := by rw [hsz, Nat.mul_comm]
  refine L.bind (L.frame (R := regionIn src.ptr A' S' K' a' bsrc)
    (allocSlice_spec h size k src.len hk hs hfit)) fun r => ?_
  cases r with
  | error e => exact L.ret' _ fun hh hp => sep_assoc hp
  | ok d =>
    dsimp only
    refine L.pre ?_ fun hh hp => sep_assoc hp
    refine L.lift fun hlen => ?_
    rw [if_pos hlen, owned_pos (by rw [Array.size_replicate, hsize]; omega)]
    refine L.pre (granted_open (p := d.ptr) (k := k)
      (bs := Array.replicate (size * src.len.toNat) Byte.undef)
      (R := I.own ∗ regionIn src.ptr A' S' K' a' bsrc) fun A S K => ?_)
      fun hh hp => by sep_normalize at hp ⊢; exact hp
    refine Logic.of_pure (fun hh hp => sep_part (P := I.own) (show (I.own ∗
      ((regionIn d.ptr A S K (2 ^ k) (Array.replicate (size * src.len.toNat) Byte.undef) ∗
        I.tok d.ptr (Array.replicate (size * src.len.toNat) Byte.undef).size k A S K) ∗
        regionIn src.ptr A' S' K' a' bsrc)) hh by sep_from hp)
      fun h' hq => hsep h' d.ptr _ A S K (by rw [Array.size_replicate, hsize]; omega) hq) fun hsp => ?_
    have hr : (Array.replicate (size * src.len.toNat) Byte.undef).size = bsrc.size := by simp [hsize]
    refine L.bind (L.pre (L.frame (R := I.own ∗ I.tok d.ptr
        (Array.replicate (size * src.len.toNat) Byte.undef).size k A S K)
      (L.ofTotal (copyChecked_spec (d := d.ptr) (s := src.ptr) (A := A) (S := S) (K := K)
        (A' := A') (S' := S') (K' := K') (a := 2 ^ k) (a' := a') (da := 2 ^ k) (sa := sa)
        (size := size) (bd := Array.replicate (size * src.len.toNat) Byte.undef) (bsrc := bsrc)
        (n := d.len) (by rw [hlen]; omega) (by rw [hlen, hr, hsz]; omega) (by rw [hlen, hsz]; omega)
        (Nat.dvd_refl _) hsa (by rw [hlen, ← hsz]; simpa [hr] using hsp))))
      fun hh hp => by sep_normalize at hp ⊢; exact hp) fun _ => L.ret' _ fun hh hp => ?_
    have ew : writeBytes (Array.replicate (size * src.len.toNat) Byte.undef) 0
        (bsrc.extract 0 (d.len.toNat * size)) = bsrc := by
      rw [hlen, Array.extract_eq_self_of_le (by omega), writeBytes_all hr.symm]
    rw [ew] at hp
    show (⌜d.len = src.len⌝ ∗ (I.own ∗ (owned I k d.ptr bsrc ∗ regionIn src.ptr A' S' K' a' bsrc))) hh
    rw [owned_pos (by omega)]
    refine sep_lift.mpr ⟨hlen, ?_⟩
    have hp' : ((I.own ∗ regionIn src.ptr A' S' K' a' bsrc) ∗
        (regionIn d.ptr A S K (2 ^ k) bsrc ∗ I.tok d.ptr bsrc.size k A S K)) hh := by
      rw [hr] at hp; sep_from hp
    have hz := sep_mono (fun _ x => x) (fun _ x => granted_intro (I := I) x) hp'
    sep_from hz

/-! ## Reallocation -/

/-- `new` keeps the common prefix of `old` after a copy of the common prefix. -/
theorem keepsPrefix_copy (bs bn : Array Byte) :
    keepsPrefix bs (writeBytes bn 0 (bs.extract 0 (Min.min bn.size bs.size))) := by
  unfold keepsPrefix
  rcases Nat.le_total bs.size bn.size with hle | hle
  · rw [Nat.min_eq_right hle, Array.extract_size, writeBytes_size bn 0 bs (by omega),
      Array.extract_eq_self_of_le hle]
    simpa using extract_writeBytes bn 0 bs (by omega)
  · have hx : (bs.extract 0 bn.size).size = bn.size := by simp; omega
    rw [Nat.min_eq_left hle, writeBytes_all hx, Array.extract_eq_self_of_le (by rw [hx]; exact hle), hx]

theorem min_toNat (x y : BitVec 64) : (Zig.min false x y).toNat = Min.min x.toNat y.toNat := by
  simp only [Zig.min, Bool.false_eq_true, ↓reduceIte]
  split <;> rename_i h <;> simp only [BitVec.ule, decide_eq_true_eq, Bool.not_eq_true,
    decide_eq_false_iff_not] at h <;> omega

theorem le_min_right (x y : BitVec 64) : Zig.le false (Zig.min false x y) y = true := by
  simp only [Zig.le, Bool.false_eq_true, ↓reduceIte, BitVec.ule_iff_le]
  rw [BitVec.le_def, min_toNat]; omega

/-- The result of `realloc` of the bytes `bs`: a slice of `size * newN` bytes that keeps the
common prefix, or `OutOfMemory` with the old slice unchanged. -/
def reallocResult (I : AllocInv) (k size : Nat) (old : Slice) (newN : BitVec 64)
    (bs : Array Byte) : Except ErrName Slice → Assn
  | .ok s => ⌜s.len = newN⌝ ∗ (I.own ∗ Assn.ex fun bs' =>
      ⌜bs'.size = size * newN.toNat ∧ keepsPrefix bs bs'⌝ ∗ owned I k s.ptr bs')
  | .error e => ⌜e = outOfMemory⌝ ∗ (I.own ∗ owned I k old.ptr bs)

/-- `reallocAdvanced(old, newN, ra)`: remap in place or moved, else allocate, copy and free. -/
theorem reallocAdvanced_spec (h : AllocSpec L vt ctx I) (size k : Nat) (old : Slice)
    (newN ra : BitVec 64) (bs : Array Byte) (hk : k < 64) (hsize : 0 < size) (hs : size < 2 ^ 64)
    (hsz : bs.size = old.len.toNat * size) (hbs : bs.size < 2 ^ 64)
    (hfit : Fits I (size * newN.toNat) k) (hsep : GrantSep I k) :
    L.T (I.own ∗ owned I k old.ptr bs) (reallocAdvanced vt ctx size k old newN ra)
      (reallocResult I k size old newN bs) := by
  unfold reallocAdvanced
  split
  · rename_i h0
    have hb0 : bs.size = 0 := by rw [hsz, h0]; simp
    rw [owned_zero hb0]
    refine L.post (L.pre (allocAdvanced_spec h size k newN ra hk hs hfit) fun hh hp => sep_emp.mp hp)
      fun v hh hq => ?_
    cases v with
    | error e =>
      show (⌜e = outOfMemory⌝ ∗ (I.own ∗ owned I k old.ptr bs)) hh
      rw [owned_zero hb0, sep_emp_eq]; exact hq
    | ok s =>
      obtain ⟨hl, hq⟩ := sep_lift.mp hq
      have hbe : bs = #[] := Array.eq_empty_of_size_eq_zero hb0
      refine sep_lift.mpr ⟨hl, sep_ex_right.mpr ⟨_, sep_lift_right.mpr ⟨⟨by simp, ?_⟩, hq⟩⟩⟩
      subst hbe; simp [keepsPrefix]
  · rename_i h0
    have hbpos : 0 < bs.size := by rw [hsz]; exact Nat.mul_pos (ne_zero_toNat h0) hsize
    split
    · rename_i h1
      refine L.bind (free_spec h size k old bs hk hsz hbs) fun _ => L.ret' _ fun hh hp => ?_
      refine sep_lift.mpr ⟨h1.symm, sep_ex_right.mpr ⟨#[], sep_lift_right.mpr
        ⟨⟨by simp [h1], by simp [keepsPrefix]⟩, ?_⟩⟩⟩
      rw [owned_zero rfl]; exact sep_emp.mpr hp
    · rename_i h1
      rw [owned_pos (by omega)]
      rw [Ops.umulOverflow_ofNat hs]
      split
      · exact L.ret' _ fun hh hp => sep_lift.mpr ⟨rfl, by rw [owned_pos (by omega)]; exact hp⟩
      · rename_i hov
        have hlt : size * newN.toNat < 2 ^ 64 := by simpa using hov
        have ec : (BitVec.ofNat 64 size * newN).toNat = size * newN.toNat :=
          Ops.toNat_mul_ofNat hs hlt
        have eo : (byteLen size old).toNat = bs.size := by
          unfold byteLen; rw [← hsz]; exact toNat_ofNat_lt hbs
        have hcpos : 0 < size * newN.toNat := Nat.mul_pos hsize (ne_zero_toNat h1)
        have hf : I.fits (BitVec.ofNat 64 size * newN).toNat k := by rw [ec]; exact hfit hcpos hlt
        dsimp only
        refine L.bind (h.remap ⟨old.ptr, byteLen size old⟩ k (BitVec.ofNat 64 size * newN) ra bs hk
          (by rw [ec]; exact hcpos) hf eo hbpos) fun r => ?_
        cases r with
        | some p =>
          dsimp only
          refine L.ret' _ fun hh hp => ?_
          simp only [remapPost, ec] at hp
          obtain ⟨bs', hp⟩ := sep_ex_right.mp hp
          obtain ⟨⟨hs', hkp⟩, hp⟩ := sep_lift_right.mp hp
          refine sep_lift.mpr ⟨rfl, sep_ex_right.mpr ⟨bs', sep_lift_right.mpr ⟨⟨hs', hkp⟩, ?_⟩⟩⟩
          rw [owned_pos (by omega)]; exact hp
        | none =>
          dsimp only
          refine L.bind (L.pre (L.frame (R := granted I old.ptr k bs)
            (h.alloc (BitVec.ofNat 64 size * newN) k ra (by rw [ec]; omega) hk hf))
            fun hh hp => hp) fun r' => ?_
          cases r' with
          | none =>
            dsimp only
            exact L.ret' _ fun hh hp => sep_lift.mpr ⟨rfl, by rw [owned_pos (by omega)]; exact hp⟩
          | some p =>
            dsimp only
            refine granted_ex fun bn hbn => ?_
            rw [ec] at hbn
            rw [if_pos (le_min_right _ _)]
            -- open both grants
            refine L.pre (granted_open (R := I.own ∗ granted I p k bn) fun A S K => ?_)
              fun hh hp => by sep_normalize at hp ⊢; exact hp
            refine L.pre (granted_open (R := I.own ∗ (regionIn old.ptr A S K (2 ^ k) bs ∗
              I.tok old.ptr bs.size k A S K)) fun A₂ S₂ K₂ => ?_)
              fun hh hp => by sep_normalize at hp ⊢; exact hp
            have em : (Zig.min false (BitVec.ofNat 64 size * newN) (byteLen size old)).toNat * 1 =
                Min.min bn.size bs.size := by
              rw [Nat.mul_one, min_toNat, ec, eo, ← hbn]
            refine Logic.of_pure (fun hh hp => sep_part (P := I.own) (show (I.own ∗
              ((regionIn p A₂ S₂ K₂ (2 ^ k) bn ∗ I.tok p bn.size k A₂ S₂ K₂) ∗
                (regionIn old.ptr A S K (2 ^ k) bs ∗ I.tok old.ptr bs.size k A S K))) hh by sep_from hp)
              fun h' hq => hsep h' p old.ptr bn bs A₂ S₂ A S K₂ K (by omega) hbpos hq) fun hsp => ?_
            -- copy the common prefix into the new region
            refine L.bind (L.pre (L.frame
              (R := I.own ∗ (I.tok p bn.size k A₂ S₂ K₂ ∗ I.tok old.ptr bs.size k A S K))
              (L.ofTotal (copyChecked_spec (d := p) (s := old.ptr) (A := A₂) (S := S₂) (K := K₂)
                (A' := A) (S' := S) (K' := K) (a := 2 ^ k) (a' := 2 ^ k) (da := 1) (sa := 1)
                (size := 1) (bd := bn) (bsrc := bs)
                (n := Zig.min false (BitVec.ofNat 64 size * newN) (byteLen size old))
                (by rw [em]; omega) (by rw [em]; omega) (by rw [em]; omega) (Nat.one_dvd _)
                (Nat.one_dvd _) (by rw [em]; exact hsp.mono (by omega) (by omega)))))
              fun hh hp => by sep_normalize at hp ⊢; exact hp) fun _ => ?_
            rw [em]
            -- poison the old region
            refine L.bind (L.pre (L.frame
              (R := regionIn p A₂ S₂ K₂ (2 ^ k) (writeBytes bn 0 (bs.extract 0 (Min.min bn.size bs.size))) ∗
                (I.own ∗ (I.tok p bn.size k A₂ S₂ K₂ ∗ I.tok old.ptr bs.size k A S K)))
              (L.ofTotal (Region.memsetUndefIn (p := old.ptr) (A := A) (S := S) (K := K)
                (a := 2 ^ k) (bs := bs) (n := byteLen size old) eo)))
              fun hh hp => by sep_normalize at hp ⊢; exact hp) fun _ => ?_
            -- free it
            refine L.bind (L.pre (L.frame
              (R := regionIn p A₂ S₂ K₂ (2 ^ k) (writeBytes bn 0 (bs.extract 0 (Min.min bn.size bs.size))) ∗
                I.tok p bn.size k A₂ S₂ K₂)
              (h.free ⟨old.ptr, byteLen size old⟩ k ra
                (Array.replicate (byteLen size old).toNat .undef) hk (by simp) (by simp; omega)))
              fun hh hp => ?_) fun _ => L.ret' _ fun hh hp => ?_
            · have et : I.tok old.ptr (byteLen size old).toNat k A S K = I.tok old.ptr bs.size k A S K := by
                rw [eo]
              have hz : ((I.own ∗ (regionIn old.ptr A S K (2 ^ k)
                  (Array.replicate (byteLen size old).toNat .undef) ∗
                  I.tok old.ptr (Array.replicate (byteLen size old).toNat Byte.undef).size k A S K)) ∗
                  (regionIn p A₂ S₂ K₂ (2 ^ k) (writeBytes bn 0 (bs.extract 0 (Min.min bn.size bs.size))) ∗
                    I.tok p bn.size k A₂ S₂ K₂)) hh := by
                rw [Array.size_replicate, et]; sep_from hp
              exact sep_mono (fun _ x => sep_mono (fun _ y => y) (fun _ y => granted_intro y) x)
                (fun _ x => x) hz
            · have hw : (writeBytes bn 0 (bs.extract 0 (Min.min bn.size bs.size))).size = bn.size :=
                writeBytes_size _ _ _ (by simp; omega)
              refine sep_lift.mpr ⟨rfl, sep_ex_right.mpr ⟨_, sep_lift_right.mpr
                ⟨⟨by rw [hw, hbn], keepsPrefix_copy bs bn⟩, ?_⟩⟩⟩
              show (I.own ∗ owned I k p _) hh
              rw [owned_pos (by rw [hw, hbn]; omega)]
              have hz : (I.own ∗ (regionIn p A₂ S₂ K₂ (2 ^ k)
                  (writeBytes bn 0 (bs.extract 0 (Min.min bn.size bs.size))) ∗
                  I.tok p (writeBytes bn 0 (bs.extract 0 (Min.min bn.size bs.size))).size k A₂ S₂ K₂)) hh := by
                rw [hw]; sep_from hp
              exact sep_mono (fun _ x => x) (fun _ x => granted_intro x) hz

/-- `realloc(old, newN)`. -/
theorem realloc_spec (h : AllocSpec L vt ctx I) (size k : Nat) (old : Slice) (newN : BitVec 64)
    (bs : Array Byte) (hk : k < 64) (hsize : 0 < size) (hs : size < 2 ^ 64)
    (hsz : bs.size = old.len.toNat * size) (hbs : bs.size < 2 ^ 64)
    (hfit : Fits I (size * newN.toNat) k) (hsep : GrantSep I k) :
    L.T (I.own ∗ owned I k old.ptr bs) (realloc vt ctx size k old newN)
      (reallocResult I k size old newN bs) :=
  L.bind (L.ofTotal returnAddress_triple) fun ra =>
    reallocAdvanced_spec h size k old newN ra bs hk hsize hs hsz hbs hfit hsep

/-! ## Sentinel -/

/-- The result of `allocSentinel`: `n + 1` items, undefined but the last. -/
def sentinelResult {T : Type} [Enc T] (I : AllocInv) (k : Nat) (n : BitVec 64) (sentinel : T) :
    Except ErrName Slice → Assn
  | .ok s => ⌜s.len = n⌝ ∗ (I.own ∗ granted I s.ptr k
      (writeBytes (Array.replicate (Enc.size T * (n.toNat + 1)) .undef) (Enc.size T * n.toNat)
        (Enc.encode sentinel)))
  | .error e => ⌜e = outOfMemory⌝ ∗ I.own

theorem add_one_ok {n : BitVec 64} (hn : n.toNat + 1 < 2 ^ 64) : Zig.add false n 1 = pure (n + 1) := by
  simp only [Zig.add, BitVec.uaddOverflow, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by simp; omega)]

theorem toNat_add_one {n : BitVec 64} (hn : n.toNat + 1 < 2 ^ 64) : (n + 1).toNat = n.toNat + 1 := by
  rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl]; exact Nat.mod_eq_of_lt hn

/-- `allocSentinel(T, n, sentinel)`. -/
theorem allocSentinel_spec {T : Type} [Enc T] [LawfulEnc T] [DecidableEq T]
    (h : AllocSpec L vt ctx I) (k : Nat) (n : BitVec 64) (sentinel : T) (hk : k < 64)
    (hT : 0 < Enc.size T) (hTs : Enc.size T < 2 ^ 64) (hal : Enc.align T ∣ 2 ^ k)
    (hals : Enc.align T ∣ Enc.size T) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : Fits I (Enc.size T * (n.toNat + 1)) k) :
    L.T I.own (allocSentinel vt ctx k n sentinel) (sentinelResult I k n sentinel) := by
  have e1 := toNat_add_one hn
  unfold allocSentinel
  simp only [liftR, add_one_ok hn, Norm.lift_pure, pure_bind]
  refine L.bind (L.ofTotal returnAddress_triple) fun ra => ?_
  refine L.bind (allocAdvanced_spec h (Enc.size T) k (n + 1) ra hk hTs (by rw [e1]; exact hfit)) fun r => ?_
  cases r with
  | error e => exact L.ret' _ fun hh hp => hp
  | ok s =>
    dsimp only
    refine L.lift fun hlen => ?_
    rw [hlen, e1]
    have hpos : Enc.size T * (n.toNat + 1) ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hT (Nat.succ_pos _))
    rw [owned_pos (by rw [Array.size_replicate]; exact hpos)]
    refine granted_open fun A S K => ?_
    have hlt : Zig.lt false n (n + 1) = true := by
      simp only [Zig.lt, Bool.false_eq_true, ↓reduceIte, BitVec.ult_iff_lt, BitVec.lt_def, e1]; omega
    have hle : Zig.le false (n + 1) (n + 1) = true := by
      simp only [Zig.le, Bool.false_eq_true, ↓reduceIte, BitVec.ule_iff_le, BitVec.le_def]; omega
    rw [if_pos hlt, Ptr.elem_eq]
    have ho : Enc.size T * n.toNat + Enc.size T ≤
        (Array.replicate (Enc.size T * (n.toNat + 1)) Byte.undef).size := by
      simp [Nat.mul_succ]
    have halo : Enc.align T ∣ Enc.size T * n.toNat := Nat.dvd_trans hals (Nat.dvd_mul_right _ _)
    refine L.bind (L.pre (L.frame (R := I.own ∗ I.tok s.ptr
          (Array.replicate (Enc.size T * (n.toNat + 1)) Byte.undef).size k A S K)
        (L.ofTotal (Region.storeItemIn (p := s.ptr) (A := A) (S := S) (K := K) (a := 2 ^ k)
          (bs := Array.replicate (Enc.size T * (n.toNat + 1)) Byte.undef)
          (o := Enc.size T * n.toNat) (al := Enc.align T) sentinel hT ho hal halo)))
        fun hh hp => by sep_normalize at hp ⊢; exact hp) fun _ => ?_
    rw [if_pos hle]
    have hw : (Enc.encode sentinel).size = Enc.size T := LawfulEnc.size_encode sentinel
    have ho' : Enc.size T * n.toNat + Enc.size T ≤ (writeBytes
        (Array.replicate (Enc.size T * (n.toNat + 1)) Byte.undef) (Enc.size T * n.toNat)
        (Enc.encode sentinel)).size := by
      rw [writeBytes_size _ _ _ (by rw [hw]; exact ho)]; exact ho
    have hv : Enc.decode ((writeBytes (Array.replicate (Enc.size T * (n.toNat + 1)) Byte.undef)
        (Enc.size T * n.toNat) (Enc.encode sentinel)).extract (Enc.size T * n.toNat)
        (Enc.size T * n.toNat + Enc.size T)) = pure sentinel := by
      rw [extract_writeBytes_in _ _ _ _ _ (by rw [hw]; exact ho) (Nat.le_refl _) (by omega)]
      simp only [Nat.sub_self, Nat.zero_add]
      rw [← hw, Array.extract_size]; exact LawfulEnc.decode_encode sentinel
    refine L.bind (L.pre (L.frame (R := I.own ∗ I.tok s.ptr
          (Array.replicate (Enc.size T * (n.toNat + 1)) Byte.undef).size k A S K)
        (L.ofTotal (loadItemIn (p := s.ptr) (A := A) (S := S) (K := K) (a := 2 ^ k)
          (al := Enc.align T) hT ho' hal halo hv)))
        fun hh hp => hp) fun x => ?_
    refine L.pre (L.lift fun hx => ?_) fun hh hp => sep_assoc hp
    subst x
    rw [if_pos rfl]
    refine L.ret' _ fun hh hp => sep_lift.mpr ⟨rfl, ?_⟩
    have hs' : (writeBytes (Array.replicate (Enc.size T * (n.toNat + 1)) Byte.undef)
        (Enc.size T * n.toNat) (Enc.encode sentinel)).size =
        (Array.replicate (Enc.size T * (n.toNat + 1)) Byte.undef).size :=
      writeBytes_size _ _ _ (by rw [hw]; exact ho)
    have hz : (I.own ∗ (regionIn s.ptr A S K (2 ^ k) (writeBytes (Array.replicate
        (Enc.size T * (n.toNat + 1)) Byte.undef) (Enc.size T * n.toNat) (Enc.encode sentinel)) ∗
        I.tok s.ptr (writeBytes (Array.replicate (Enc.size T * (n.toNat + 1)) Byte.undef)
          (Enc.size T * n.toNat) (Enc.encode sentinel)).size k A S K)) hh := by
      rw [hs']; sep_from hp
    exact sep_mono (fun _ x => x) (fun _ x => granted_intro x) hz

end Wrap

end Zig
