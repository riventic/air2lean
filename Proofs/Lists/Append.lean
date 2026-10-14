import Proofs.Lists.Alloc
import ZigLean.Sep.Full.Slice

/-!
# `ArrayListUnmanaged(u32).append` for every allocator

`append` takes a `std.mem.Allocator`. In `Proofs/Lists/Open.lean` every call through it reaches
the environment (`Ext`, premise EXT-05; `docs/interfaces.md`), so the theorems here assume only
the allocator contract `CAllocSpec` of the environment's allocator at the vtable `fns`
(`CVTable.env`, `Lists.Alloc.env`), with invariant `I`, and hold for every allocator that meets
it: a concrete allocator enters only through its proved contract.

`alist I φ p xs`: the list header at `p` (`items = ⟨ptr, len⟩`, `capacity = cap`,
`pointer_stability` unlocked; a typed value) and its buffer (`buf`, keyed by `cap`): for
`cap > 0` a grant of `I`'s allocator for the fee `φ` (`FAllocInv.fee`, `docs/sep-full-state.md`
§The fee of a grant) of `4 * cap` bytes whose first `xs.length` items are `xs` (`ItemsOk`); for
`cap = 0` no bytes, the unspent fee `I.fee φ` and the
knowledge of the address of the items pointer's block (`addrKnown`): `.empty` points into a
constant global, whose address is known (`docs/sep-full-state.md`).

* `append_spec`: `append` takes a fee `I.fee φ`, gives `xs ++ [v]`, or `error.OutOfMemory` and the
  same list, and gives the fee back. When the buffer is full, `ensureTotalCapacityPrecise` first
  asks the allocator to `remap` the buffer; if it cannot, it allocates a new buffer
  (`alignedAlloc`, for the fee taken), copies the items with a `@memcpy` and frees the old buffer
  (whose fee comes back). The `@memcpy` alias check reads the two buffers' addresses: two grants
  are disjoint, for every placement (`docs/address-placement.md`). An empty list's buffer is
  allocated for the list's unspent fee; nothing is copied or freed.
* `I.fits (4 * growTo (xs.length + 1)) 2`: the room the allocator's contract asks of a request
  of the grown capacity (`growCapacity`), at the items' alignment `2 ^ 2`.

These are `CTriple`s (partial correctness, no panic): the contract `CAllocSpec` is one, so a
client of an arbitrary allocator gets no more. The generated code is walked by `fsym` with the
allocator calls (`remap_spec`, `alignedAlloc_spec`, `free_spec`) and the slice rules of
`ZigLean/Sep/Full/Slice.lean` as its rules.
-/

namespace Lists.Append

open Zig Zig.Full Zig.Full.FAssn Lists.Open Lists.Alloc

theorem fromByteUnits_4 : mem_Alignment_fromByteUnits 4 = pure mem_Alignment.«4» := by
  have h : (4 : BitVec 64).ctz = 2 := Zig.ctz_twoPow (k := 2) (by decide)
  unfold mem_Alignment_fromByteUnits math_isPowerOfTwo__anon_38853e1fe316 debug_assert
  simp only [Zig.ctz, h]
  rfl

/-! ## Items -/

/-- Item `i` of the bytes `bs` is `xs[i]`. -/
def ItemsOk (bs : Array Byte) (xs : List (BitVec 32)) : Prop :=
  ∀ i (hi : i < xs.length), bs.extract (4 * i) (4 * i + 4) = Enc.encode xs[i]

theorem ItemsOk.of_length {bs : Array Byte} {xs : List (BitVec 32)} (h : xs.length = 0) :
    ItemsOk bs xs :=
  fun _ hi => absurd hi (by omega)

/-- A buffer that keeps the prefix of `bs` keeps its items. -/
theorem ItemsOk.keep {bs bs' : Array Byte} {xs : List (BitVec 32)} (h : ItemsOk bs xs)
    (hk : keepsPrefix bs bs') (h1 : 4 * xs.length ≤ bs.size) (h2 : 4 * xs.length ≤ bs'.size) :
    ItemsOk bs' xs := by
  intro i hi
  rw [← h i hi]
  have e1 : bs'.extract (4 * i) (4 * i + 4) = (bs'.extract 0 bs.size).extract (4 * i) (4 * i + 4) := by
    rw [Array.extract_extract]; congr 1 <;> omega
  have e2 : bs.extract (4 * i) (4 * i + 4) = (bs.extract 0 bs'.size).extract (4 * i) (4 * i + 4) := by
    rw [Array.extract_extract]; congr 1 <;> omega
  rw [e1, e2, hk]

/-- The first `m` bytes of `bs` copied to the front of `bn` keep the items. -/
theorem ItemsOk.copy {bs bn : Array Byte} {xs : List (BitVec 32)} {m : Nat} (h : ItemsOk bs xs)
    (h1 : 4 * xs.length ≤ m) (h2 : m ≤ bs.size) (h3 : m ≤ bn.size) :
    ItemsOk (writeBytes bn 0 (bs.extract 0 m)) xs := by
  intro i hi
  rw [← h i hi, extract_writeBytes_in _ _ _ _ _ (by simp; omega) (Nat.zero_le _) (by simp; omega)]
  simp only [Nat.sub_zero, Array.extract_extract, Nat.zero_add]
  congr 1 <;> omega

/-- `v` stored after the items is the last item. -/
theorem ItemsOk.push {bs : Array Byte} {xs : List (BitVec 32)} (v : BitVec 32) (h : ItemsOk bs xs)
    (hs : 4 * xs.length + 4 ≤ bs.size) {o : Nat} (ho : o = 4 * xs.length) :
    ItemsOk (writeBytes bs o (Enc.encode v)) (xs ++ [v]) := by
  subst ho
  have hw : (Enc.encode v).size = 4 := LawfulEnc.size_encode v
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hil : i < xs.length
  · rw [extract_writeBytes_disjoint _ _ _ _ _ (by omega) (by omega) (by omega),
      List.getElem_append_left hil]
    exact h i hil
  · have hi' : i = xs.length := by omega
    subst hi'
    rw [show 4 * xs.length + 4 = 4 * xs.length + (Enc.encode v).size by rw [hw],
      extract_writeBytes_in _ _ _ _ _ (by omega) (Nat.le_refl _) (Nat.le_refl _)]
    simp only [Nat.sub_self, Nat.zero_add]
    rw [List.getElem_append_right (by omega)]
    simp [Array.extract_size]

/-! ## The allocator calls of `ArrayListUnmanaged(u32)` -/

variable [Ext] (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac)

/-- What `remap` of a buffer `bs` of `u32` items at `old` to `n` items returns. -/
def remapped (old : Ptr) (bs : Array Byte) (n : BitVec 64) : Option Slice → FAssn
  | none => I.granted old 2 φ bs
  | some s => ⟪s.len = n ∧ 4 * n.toNat < 2 ^ 64⟫ ⋆ FAssn.ex fun bs' =>
      ⟪bs'.size = 4 * n.toNat ∧ keepsPrefix bs bs'⟫ ⋆ I.granted s.ptr 2 φ bs'

theorem remap_spec (s : Slice) (n : BitVec 64) (bs : Array Byte) (hlen : 4 * s.len.toNat = bs.size)
    (hs : 4 * s.len.toNat < 2 ^ 64) (h0 : 0 < s.len.toNat) (hn : 0 < n.toNat)
    (hfit : I.fits (4 * n.toNat) 2) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_remap__anon_fdce5ddbfdcf ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (remapped I φ s.ptr bs n r ⋆ vtR vtp fns.toList)) := by
  -- fsym does not evaluate the pure helper on its literal (fsym-engine ledger)
  unfold mem_Allocator_remap__anon_fdce5ddbfdcf
  simp only [fromByteUnits_4]
  fsym [CAllocSpec.remap h]

/-- What `alignedAlloc(u32, n)` returns. -/
def allocated (n : BitVec 64) : Except ErrName Slice → FAssn
  | .ok s => ⟪s.len = n ∧ 4 * n.toNat < 2 ^ 64⟫ ⋆ I.owned 2 φ s.ptr (Array.replicate (4 * n.toNat) .undef)
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ I.fee φ

theorem alignedAlloc_spec (n : BitVec 64) (hfit : I.fits (4 * n.toNat) 2)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList))
      (mem_Allocator_alignedAlloc__anon_0b20c0554625 ⟨ctx, vtp⟩ n)
      (fun r => I.own ⋆ (allocated I φ n r ⋆ vtR vtp fns.toList)) := by
  fsym [CAllocSpec.alloc h]

theorem free_spec (s : Slice) (bs : Array Byte) (hlen : 4 * s.len.toNat = bs.size)
    (hs : 4 * s.len.toNat < 2 ^ 64) (h0 : 0 < s.len.toNat)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_10fd68fdc68d ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold mem_Allocator_free__anon_10fd68fdc68d
  simp only [fromByteUnits_4]
  fsym [fun (s : Slice) ra (h' : 0 < s.len.toNat) =>
    CAllocSpec.free h s 2 ra φ (Array.replicate s.len.toNat .undef) (by decide) (by simp) (by simpa using h')]

/-! ## The list -/

/-- The list header's value: `items = ⟨ptr, len⟩`, `capacity = cap`, `pointer_stability`
unlocked. -/
abbrev hdrVal (ptr : Ptr) (len cap : BitVec 64) : array_list_Aligned_u32_null :=
  { items := ⟨ptr, len⟩, capacity := cap,
    pointer_stability := { state := debug_SafetyLock_State__enum_1.unlocked } }

omit [Ext] in
/-- The address of `ptr`'s block is known (the items pointer of a list without a buffer). -/
def addrKnown (ptr : Ptr) : FAssn := FAssn.ex fun b => FAssn.ex fun A => ⟪ptr.block = some b⟫ ⋆ known b A

omit [Ext] in
/-- The buffer of a list with capacity `cap` holding `xs`: for `cap = 0` no bytes, the unspent
fee `φ` and the address of `ptr`'s block, else a grant of `I`'s allocator for the fee `φ` of
`4 * cap` bytes whose first items are `xs`. The header's `cap` determines which. -/
def buf (ptr : Ptr) (cap : BitVec 64) (xs : List (BitVec 32)) : FAssn :=
  if cap.toNat = 0 then addrKnown ptr ⋆ I.fee φ
  else FAssn.ex fun bs => ⟪bs.size = 4 * cap.toNat ∧ ItemsOk bs xs⟫ ⋆ I.granted ptr 2 φ bs

omit [Ext] in
/-- The list at `p` holds `xs`. -/
def alist (p : Ptr) (xs : List (BitVec 32)) : FAssn :=
  FAssn.ex fun ptr => FAssn.ex fun len : BitVec 64 => FAssn.ex fun cap : BitVec 64 =>
    ⟪len.toNat = xs.length ∧ xs.length ≤ cap.toNat ∧ 4 * cap.toNat < 2 ^ 64⟫ ⋆
    (up (pts p 8 (hdrVal ptr len cap)) ⋆ buf I φ ptr cap xs)

/-- What `ensureTotalCapacityPrecise` to `g` items gives: a granted buffer of `g` items that
keeps the items, or `error.OutOfMemory` and the header and the old buffer `old` as they were. -/
def ensured (p ptr : Ptr) (len cap g : BitVec 64) (xs : List (BitVec 32)) (old : FAssn) :
    Except ErrName Unit → FAssn
  | .ok _ => FAssn.ex fun ptr' => FAssn.ex fun bs' =>
      ⟪bs'.size = 4 * g.toNat ∧ 4 * g.toNat < 2 ^ 64 ∧ ItemsOk bs' xs⟫ ⋆
        (up (pts p 8 (hdrVal ptr' len g)) ⋆ I.granted ptr' 2 φ bs')
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ (up (pts p 8 (hdrVal ptr len cap)) ⋆ old)

/-- `ensureTotalCapacityPrecise` of a granted buffer to `g > cap` items: `remap`, else
`alignedAlloc`, `@memcpy` and `free`. -/
theorem precise_pos (p ptr : Ptr) (len cap g : BitVec 64) (xs : List (BitVec 32)) (bs : Array Byte)
    (hbs : bs.size = 4 * cap.toNat) (hc4 : 4 * cap.toNat < 2 ^ 64) (hcap : 0 < cap.toNat)
    (hxs : xs.length = len.toNat) (hit : ItemsOk bs xs)
    (hle : len.toNat ≤ cap.toNat) (hg : cap.toNat < g.toNat) (hfit : I.fits (4 * g.toNat) 2)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ ((up (pts p 8 (hdrVal ptr len cap)) ⋆ I.granted ptr 2 φ bs) ⋆
        vtR vtp fns.toList)))
      (array_list_Aligned_u32_null_ensureTotalCapacityPrecise p ⟨ctx, vtp⟩ g)
      (fun r => I.own ⋆ (I.fee φ ⋆ (ensured I φ p ptr len cap g xs (I.granted ptr 2 φ bs) r ⋆
        vtR vtp fns.toList))) := by
  unfold array_list_Aligned_u32_null_ensureTotalCapacityPrecise
  fsym [remap_spec ctx vtp fns I e φ (h := h), alignedAlloc_spec ctx vtp fns I e φ (h := h),
    free_spec ctx vtp fns I e φ (h := h)]
  all_goals first
    | exact ItemsOk.keep hit ‹keepsPrefix _ _› (by fsym_arith) (by fsym_arith)
    | exact ItemsOk.copy hit (by fsym_arith) (by fsym_arith) (by fsym_arith)

/-- `ensureTotalCapacityPrecise` of a list without a buffer to `g > 0` items: `alignedAlloc`, for
the list's unspent fee; nothing is copied or freed. -/
theorem precise_zero (p ptr : Ptr) (len cap g : BitVec 64) (xs : List (BitVec 32))
    (hcap : cap.toNat = 0) (hxs : xs.length = len.toNat)
    (hle : len.toNat ≤ cap.toNat) (hg : cap.toNat < g.toNat) (hfit : I.fits (4 * g.toNat) 2)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ ((up (pts p 8 (hdrVal ptr len cap)) ⋆ (addrKnown ptr ⋆ I.fee φ)) ⋆
        vtR vtp fns.toList)))
      (array_list_Aligned_u32_null_ensureTotalCapacityPrecise p ⟨ctx, vtp⟩ g)
      (fun r => I.own ⋆ (I.fee φ ⋆ (ensured I φ p ptr len cap g xs (addrKnown ptr ⋆ I.fee φ) r ⋆
        vtR vtp fns.toList))) := by
  unfold array_list_Aligned_u32_null_ensureTotalCapacityPrecise
  fsym [alignedAlloc_spec ctx vtp fns I e φ (h := h)]
  all_goals exact ItemsOk.of_length (by fsym_arith)

/-! ## `append` -/

/-- What `append` gives: the list with `v` at the end, or `error.OutOfMemory` and the list as it
was. -/
def appended (p : Ptr) (xs : List (BitVec 32)) (v : BitVec 32) : Except ErrName Unit → FAssn
  | .ok _ => alist I φ p (xs ++ [v])
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ alist I φ p xs

/-- The capacity `growCapacity` asks for when the list grows to `n` items. -/
def growTo (n : Nat) : Nat := Min.min (n + (n / 2 + 32)) (2 ^ 64 - 1)

attribute [local fsym_arith] List.length_append List.length_singleton List.length_cons List.length_nil

/-- `append` to a list with a granted buffer. -/
theorem append_pos (p ptr : Ptr) (len cap : BitVec 64) (xs : List (BitVec 32))
    (v : BitVec 32) (hlen : len.toNat = xs.length) (hle : xs.length ≤ cap.toNat)
    (hc4 : 4 * cap.toNat < 2 ^ 64) (hcap : cap.toNat ≠ 0)
    (hfit : I.fits (4 * growTo (xs.length + 1)) 2)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ ((up (pts p 8 (hdrVal ptr len cap)) ⋆ buf I φ ptr cap xs) ⋆
        vtR vtp fns.toList)))
      (array_list_Aligned_u32_null_append p ⟨ctx, vtp⟩ v)
      (fun r => I.own ⋆ (I.fee φ ⋆ (appended I φ p xs v r ⋆ vtR vtp fns.toList))) := by
  simp only [buf, hcap, ↓reduceIte]
  unfold array_list_Aligned_u32_null_append array_list_Aligned_u32_null_addOne
    array_list_Aligned_u32_null_ensureTotalCapacity
  fsym [precise_pos ctx vtp fns I e φ (h := h)]
  all_goals (apply ItemsOk.push v <;> first | assumption | fsym_arith)

-- the store of `v` at item `0` of a new buffer (not a default rule, `Full/Region.lean`)
attribute [local fsym] FTotalTriple.regionStore0 in
/-- `append` to a list without a buffer. -/
theorem append_zero (p ptr : Ptr) (len cap : BitVec 64) (xs : List (BitVec 32)) (v : BitVec 32)
    (hcap : cap.toNat = 0) (hlen : len.toNat = xs.length) (hle : xs.length ≤ cap.toNat)
    (hfit : I.fits (4 * growTo (xs.length + 1)) 2)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ ((up (pts p 8 (hdrVal ptr len cap)) ⋆ buf I φ ptr cap xs) ⋆
        vtR vtp fns.toList)))
      (array_list_Aligned_u32_null_append p ⟨ctx, vtp⟩ v)
      (fun r => I.own ⋆ (I.fee φ ⋆ (appended I φ p xs v r ⋆ vtR vtp fns.toList))) := by
  simp only [buf, hcap, ↓reduceIte]
  unfold array_list_Aligned_u32_null_append array_list_Aligned_u32_null_addOne
    array_list_Aligned_u32_null_ensureTotalCapacity
  fsym [precise_zero ctx vtp fns I e φ (h := h)]
  all_goals first
    | exact ItemsOk.push v (ItemsOk.of_length (by fsym_arith)) (by fsym_arith) (by fsym_arith)
    | exact ItemsOk.of_length (by fsym_arith)

/-- **`append`** takes a fee and gives `xs ++ [v]`, or `error.OutOfMemory` and the same list,
and the fee back, for every allocator that meets the contract. -/
theorem append_spec (p : Ptr) (xs : List (BitVec 32)) (v : BitVec 32)
    (hfit : I.fits (4 * growTo (xs.length + 1)) 2)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ (alist I φ p xs ⋆ vtR vtp fns.toList)))
      (array_list_Aligned_u32_null_append p ⟨ctx, vtp⟩ v)
      (fun r => I.own ⋆ (I.fee φ ⋆ (appended I φ p xs v r ⋆ vtR vtp fns.toList))) := by
  refine CTriple.pre (P := FAssn.ex fun ptr => FAssn.ex fun len : BitVec 64 =>
      FAssn.ex fun cap : BitVec 64 =>
      ⟪len.toNat = xs.length ∧ xs.length ≤ cap.toNat ∧ 4 * cap.toNat < 2 ^ 64⟫ ⋆
      (I.own ⋆ (I.fee φ ⋆ ((up (pts p 8 (hdrVal ptr len cap)) ⋆ buf I φ ptr cap xs) ⋆
        vtR vtp fns.toList))))
    (CTriple.ex fun ptr => CTriple.ex fun len => CTriple.ex fun cap =>
      CTriple.lift fun ⟨hlen, hle, hc4⟩ => ?_) fun _ h => ?_
  · by_cases hcap : cap.toNat = 0
    · exact append_zero ctx vtp fns I e φ p ptr len cap xs v hcap hlen hle hfit h
    · exact append_pos ctx vtp fns I e φ p ptr len cap xs v hlen hle hc4 hcap hfit h
  · obtain ⟨r₁, r₂, hd, rfl, h1, r₃, r₄, hd', rfl, h3, r₅, r₆, hd'', rfl, ⟨ptr, len, cap, h5⟩, h6⟩ := h
    obtain ⟨hf, h5⟩ := Full.sep_lift.mp h5
    exact ⟨ptr, len, cap, Full.sep_lift.mpr ⟨hf, r₁, _, hd, rfl, h1, r₃, _, hd', rfl, h3,
      r₅, r₆, hd'', rfl, h5, h6⟩⟩

end Lists.Append
