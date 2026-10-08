import ZigLean.Sep.AllocSpec
import ZigLean.Sep.Automation

/-!
# The `std.mem.Allocator` wrappers over any allocator that satisfies `AllocSpec`

The wrapper functions of `lib/std/mem/Allocator.zig` (Zig 0.16.0) call the vtable through the
`Allocator` value `{ ptr = ctx, vtable }`. `Wrap.*` are their step semantics over a `RawVTable`,
at the byte level (an item type is its size `size` and the log2 `k` of its alignment):

| Zig                                          | here                                 |
|----------------------------------------------|--------------------------------------|
| `allocBytesWithAlignment(k, n)`              | `Wrap.allocBytes vt ctx k n ra`      |
| `allocWithSizeAndAlignment(size, k, n)`      | `Wrap.allocItems vt ctx size k n ra` |
| `alloc(T, n)`, `alignedAlloc(T, k, n)`       | `Wrap.allocSlice vt ctx size k n ra` |
| `create(T)`                                  | `Wrap.create vt ctx size k ra`       |
| `destroy(p)`                                 | `Wrap.destroy vt ctx size k p ra`    |
| `free(memory)`                               | `Wrap.free vt ctx size k s ra`       |
| `dupe(T, m)`                                 | `Wrap.dupe vt ctx size k sa m ra`    |
| `allocSentinel(T, n, s)`                     | `Wrap.allocSentinel vt ctx k n s ra` |
| `realloc(old, n)` (`reallocAdvanced`)        | `Wrap.realloc vt ctx size k old n ra`|

Each `*_spec` theorem proves the wrapper's contract in any logic `L` from `AllocSpec L vt ctx I`
alone. A translated wrapper (`--allocator-model=translated`) gets the same contract by
`Logic.congr` once its runs are shown equal to these (unfold the generated code; the vtable
loads and the indirect calls reduce to `vt.*`).

`owned I k p bs` is what a client owns for a slice: nothing for zero bytes (the pointer is a
constant without a block), else the granted region.
-/

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

namespace Wrap

def outOfMemory : ErrName := "OutOfMemory"

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

/-- The byte length of a slice of items of `size` bytes (`@ptrCast` to `[]u8`). -/
def byteLen (size : Nat) (s : Slice) : BitVec 64 := BitVec.ofNat 64 (s.len.toNat * size)

/-- The byte count of `n` items of `size` bytes (checked for overflow before use). -/
def itemBytes (size : Nat) (n : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (size * n.toNat)

variable (vt : RawVTable) (ctx : Ptr)

/-- `allocBytesWithAlignment`. -/
def allocBytes (k : Nat) (n ra : BitVec 64) : MemM (Except ErrName Ptr) :=
  if n.toNat = 0 then pure (.ok (zeroAllocPtr (2 ^ k))) else
  vt.alloc ctx n k ra >>= fun r => match r with
    | none => pure (.error outOfMemory)
    | some p => memset (α := BitVec 8) 1 p n none >>= fun _ => pure (.ok p)

/-- `allocWithSizeAndAlignment`: the byte count, checked for overflow. -/
def allocItems (size k : Nat) (n ra : BitVec 64) : MemM (Except ErrName Ptr) :=
  if 2 ^ 64 ≤ size * n.toNat then pure (.error outOfMemory)
  else allocBytes vt ctx k (BitVec.ofNat 64 (size * n.toNat)) ra

/-- `alloc(T, n)` and `alignedAlloc(T, k, n)` (`allocAdvancedWithRetAddr`). -/
def allocSlice (size k : Nat) (n ra : BitVec 64) : MemM (Except ErrName Slice) :=
  allocItems vt ctx size k n ra >>= fun r => match r with
    | .error e => pure (.error e)
    | .ok p => pure (.ok ⟨p, n⟩)

/-- `create(T)`. -/
def create (size k : Nat) (ra : BitVec 64) : MemM (Except ErrName Ptr) :=
  if size = 0 then pure (.ok (zeroAllocPtr (2 ^ k)))
  else allocBytes vt ctx k (BitVec.ofNat 64 size) ra

/-- `destroy(p)`: no `@memset`, a direct `rawFree`. -/
def destroy (size k : Nat) (p : Ptr) (ra : BitVec 64) : MemM Unit :=
  if size = 0 then pure () else vt.free ctx ⟨p, BitVec.ofNat 64 size⟩ k ra

/-- `free(memory)` for a slice of items of `size` bytes. -/
def free (size k : Nat) (s : Slice) (ra : BitVec 64) : MemM Unit :=
  if (byteLen size s).toNat = 0 then pure () else
  memset (α := BitVec 8) 1 s.ptr (byteLen size s) none >>= fun _ =>
    vt.free ctx ⟨s.ptr, byteLen size s⟩ k ra

/-- `dupe(T, m)`: `alloc` and `@memcpy` (source alignment `sa`). -/
def dupe (size k sa : Nat) (src : Slice) (ra : BitVec 64) : MemM (Except ErrName Slice) :=
  allocSlice vt ctx size k src.len ra >>= fun r => match r with
    | .error e => pure (.error e)
    | .ok d => memmove size (2 ^ k) sa d.ptr src.ptr src.len >>= fun _ => pure (.ok d)

/-- `allocSentinel(T, n, sentinel)`: `n + 1` items, the last the sentinel. -/
def allocSentinel {T : Type} [Enc T] (k : Nat) (n : BitVec 64) (sentinel : T) (ra : BitVec 64) :
    MemM (Except ErrName Slice) :=
  allocItems vt ctx (Enc.size T) k (n + 1) ra >>= fun r => match r with
    | .error e => pure (.error e)
    | .ok p => store (Enc.align T) (p.elem (Enc.size T) n) sentinel >>= fun _ => pure (.ok ⟨p, n⟩)

/-- `realloc(old, newN)` (`reallocAdvanced`). -/
def realloc (size k : Nat) (old : Slice) (newN ra : BitVec 64) : MemM (Except ErrName Slice) :=
  if old.len.toNat = 0 then allocSlice vt ctx size k newN ra else
  if newN.toNat = 0 then
    free vt ctx size k old ra >>= fun _ => pure (.ok ⟨zeroAllocPtr (2 ^ k), 0⟩) else
  if 2 ^ 64 ≤ size * newN.toNat then pure (.error outOfMemory) else
  vt.remap ctx ⟨old.ptr, byteLen size old⟩ k (itemBytes size newN) ra >>= fun r => match r with
    | some p => pure (.ok ⟨p, newN⟩)
    | none => vt.alloc ctx (itemBytes size newN) k ra >>= fun r' => match r' with
      | none => pure (.error outOfMemory)
      | some p =>
        memmove 1 1 1 p old.ptr
            (BitVec.ofNat 64 (min (itemBytes size newN).toNat (byteLen size old).toNat)) >>= fun _ =>
        memset (α := BitVec 8) 1 old.ptr (byteLen size old) none >>= fun _ =>
        vt.free ctx ⟨old.ptr, byteLen size old⟩ k ra >>= fun _ => pure (.ok ⟨p, newN⟩)

/-! ## Contracts -/

variable {vt ctx} {L : Logic} {I : AllocInv}

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

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The copy of `realloc` keeps the common prefix. -/
theorem keepsPrefix_copy (bs bn : Array Byte) :
    keepsPrefix bs (writeBytes bn 0 (bs.extract 0 (min bn.size bs.size))) := by
  unfold keepsPrefix
  rcases Nat.le_total bs.size bn.size with hle | hle
  · rw [Nat.min_eq_right hle, Array.extract_size, writeBytes_size bn 0 bs (by omega),
      Array.extract_eq_self_of_le hle]
    simpa using extract_writeBytes bn 0 bs (by omega)
  · have hx : (bs.extract 0 bn.size).size = bn.size := by simp; omega
    rw [Nat.min_eq_left hle, writeBytes_all hx, Array.extract_eq_self_of_le (by simp), hx]

theorem allocBytes_spec (h : AllocSpec L vt ctx I) (k : Nat) (n ra : BitVec 64) (hk : k < 64) :
    L.T I.own (allocBytes vt ctx k n ra) (allocResult I k n.toNat) := by
  unfold allocBytes
  split
  · rename_i h0
    refine L.ret' _ fun hh hp => ?_
    simp only [allocResult]
    rw [owned_zero (by simp [h0])]
    exact sep_emp.mpr hp
  · rename_i h0
    refine L.bind (h.alloc n k ra (by omega) hk) fun r => ?_
    cases r with
    | none => exact L.ret' _ fun hh hp => sep_lift.mpr ⟨rfl, hp⟩
    | some p =>
      dsimp only
      refine granted_ex' fun bs hs => ?_
      refine L.bind (L.pre (L.frame (R := I.own ∗ I.tok p bs.size k)
        (L.ofTotal (Region.memsetUndef (p := p) (a := 2 ^ k) (n := n) hs.symm)))
        fun hh hp => by unfold granted at hp; sep_normalize at hp ⊢; exact hp) fun _ => ?_
      refine L.ret' _ fun hh hp => ?_
      simp only [allocResult]
      rw [owned_pos (by simpa using h0), granted, Array.size_replicate]
      rw [hs] at hp
      sep_normalize at hp ⊢; exact hp

theorem allocItems_spec (h : AllocSpec L vt ctx I) (size k : Nat) (n ra : BitVec 64)
    (hk : k < 64) :
    L.T I.own (allocItems vt ctx size k n ra) (allocResult I k (size * n.toNat)) := by
  unfold allocItems
  split
  · exact L.ret' _ fun hh hp => sep_lift.mpr ⟨rfl, hp⟩
  · rename_i hov
    have := allocBytes_spec h k (BitVec.ofNat 64 (size * n.toNat)) ra hk
    rwa [toNat_ofNat_lt (Nat.lt_of_not_le hov)] at this

/-- `alloc(T, n)` / `alignedAlloc(T, k, n)`: `n` items of `size` bytes, undefined. -/
theorem allocSlice_spec (h : AllocSpec L vt ctx I) (size k : Nat) (n ra : BitVec 64)
    (hk : k < 64) :
    L.T I.own (allocSlice vt ctx size k n ra) (sliceResult I k n (size * n.toNat)) := by
  refine L.bind (allocItems_spec h size k n ra hk) fun r => ?_
  cases r with
  | error e => exact L.ret' _ fun hh hp => hp
  | ok p => exact L.ret' _ fun hh hp => sep_lift.mpr ⟨rfl, hp⟩

/-- `create(T)`: one item of `size` bytes, undefined. -/
theorem create_spec (h : AllocSpec L vt ctx I) (size k : Nat) (ra : BitVec 64) (hk : k < 64)
    (hs : size < 2 ^ 64) :
    L.T I.own (create vt ctx size k ra) (allocResult I k size) := by
  unfold create
  split
  · rename_i h0
    subst h0
    refine L.ret' _ fun hh hp => ?_
    simp only [allocResult]
    rw [owned_zero (by simp)]
    exact sep_emp.mpr hp
  · have := allocBytes_spec h k (BitVec.ofNat 64 size) ra hk
    rwa [toNat_ofNat_lt hs] at this

/-- `destroy(p)` of what `create` returned. -/
theorem destroy_spec (h : AllocSpec L vt ctx I) (size k : Nat) (p : Ptr) (ra : BitVec 64)
    (bs : Array Byte) (hk : k < 64) (hsz : bs.size = size) (hs : size < 2 ^ 64) :
    L.T (I.own ∗ owned I k p bs) (destroy vt ctx size k p ra) (fun _ => I.own) := by
  unfold destroy
  split
  · rename_i h0
    refine L.ret' _ fun hh hp => ?_
    rw [owned_zero (by omega)] at hp
    exact sep_emp.mp hp
  · rename_i h0
    rw [owned_pos (by omega)]
    exact h.free ⟨p, BitVec.ofNat 64 size⟩ k ra bs hk
      (by show (BitVec.ofNat 64 size).toNat = bs.size; rw [toNat_ofNat_lt hs, hsz]) (by omega)

/-- `free(memory)`: the slice's bytes go back to the allocator. -/
theorem free_spec (h : AllocSpec L vt ctx I) (size k : Nat) (s : Slice) (ra : BitVec 64)
    (bs : Array Byte) (hk : k < 64) (hsz : bs.size = s.len.toNat * size) (hs : bs.size < 2 ^ 64) :
    L.T (I.own ∗ owned I k s.ptr bs) (free vt ctx size k s ra) (fun _ => I.own) := by
  have e : (byteLen size s).toNat = bs.size := by
    unfold byteLen; rw [← hsz]; exact toNat_ofNat_lt hs
  unfold free
  split
  · rename_i h0
    refine L.ret' _ fun hh hp => ?_
    rw [owned_zero (by omega)] at hp
    exact sep_emp.mp hp
  · rename_i h0
    rw [owned_pos (by omega)]
    refine L.bind (L.pre (L.frame (R := I.own ∗ I.tok s.ptr bs.size k)
      (L.ofTotal (Region.memsetUndef (p := s.ptr) (a := 2 ^ k) (n := byteLen size s) e)))
      fun hh hp => by unfold granted at hp; sep_normalize at hp ⊢; exact hp) fun _ => ?_
    refine L.pre (h.free ⟨s.ptr, byteLen size s⟩ k ra
      (Array.replicate (byteLen size s).toNat .undef) hk (by simp) (by simp; omega)) ?_
    intro hh hp
    unfold granted
    rw [Array.size_replicate]
    rw [← e] at hp
    sep_normalize at hp ⊢; exact hp

/-- The result of `dupe`: a copy of the source bytes. -/
def dupeResult (I : AllocInv) (k a' : Nat) (src : Slice) (bsrc : Array Byte) :
    Except ErrName Slice → Assn
  | .ok d => ⌜d.len = src.len⌝ ∗ (I.own ∗ (owned I k d.ptr bsrc ∗ region src.ptr a' bsrc))
  | .error e => ⌜e = outOfMemory⌝ ∗ (I.own ∗ region src.ptr a' bsrc)

/-- `dupe(T, m)`: a fresh copy of the `size * m.len` bytes at `m`. -/
theorem dupe_spec (h : AllocSpec L vt ctx I) (size k sa a' : Nat) (src : Slice) (ra : BitVec 64)
    (bsrc : Array Byte) (hk : k < 64) (hsz : bsrc.size = src.len.toNat * size) (hsa : sa ∣ a') :
    L.T (I.own ∗ region src.ptr a' bsrc) (dupe vt ctx size k sa src ra)
      (dupeResult I k a' src bsrc) := by
  refine L.bind (L.frame (R := region src.ptr a' bsrc) (allocSlice_spec h size k src.len ra hk))
    fun r => ?_
  cases r with
  | error e => exact L.ret' _ fun hh hp => sep_assoc hp
  | ok d =>
    dsimp only
    refine L.pre ?_ fun hh hp => sep_assoc hp
    refine L.lift fun hlen => ?_
    by_cases h0 : size * src.len.toNat = 0
    · rw [owned_zero (by simp [h0])]
      refine L.bind (L.ofTotal (Region.memmoveZero (by rw [Nat.mul_comm]; exact h0)))
        fun _ => L.ret' _ fun hh hp => ?_
      have hb0 : bsrc.size = 0 := by rw [hsz, Nat.mul_comm]; exact h0
      show (⌜d.len = src.len⌝ ∗ (I.own ∗ (owned I k d.ptr bsrc ∗ region src.ptr a' bsrc))) hh
      rw [owned_zero hb0]
      exact sep_lift.mpr ⟨hlen, by sep_normalize at hp ⊢; exact hp⟩
    · rw [owned_pos (by simpa using h0)]
      unfold granted
      have hr : (Array.replicate (size * src.len.toNat) Byte.undef).size = bsrc.size := by
        simp [hsz, Nat.mul_comm]
      refine L.bind (L.pre (L.frame (R := I.own ∗ I.tok d.ptr
          (Array.replicate (size * src.len.toNat) Byte.undef).size k)
        (L.ofTotal (Region.memcpy (d := d.ptr) (s := src.ptr) (a := 2 ^ k) (a' := a')
          (da := 2 ^ k) (sa := sa) (sz := size)
          (bd := Array.replicate (size * src.len.toNat) Byte.undef) (bsrc := bsrc) (n := src.len)
          (by simp [Nat.mul_comm]) (by omega) (Nat.dvd_refl _) hsa)))
        fun hh hp => by sep_normalize at hp ⊢; exact hp) fun _ => L.ret' _ fun hh hp => ?_
      have ew : writeBytes (Array.replicate (size * src.len.toNat) Byte.undef) 0
          (bsrc.extract 0 (src.len.toNat * size)) = bsrc := by
        rw [Array.extract_eq_self_of_le (by omega), writeBytes_all hr.symm]
      rw [ew, hr] at hp
      show (⌜d.len = src.len⌝ ∗ (I.own ∗ (owned I k d.ptr bsrc ∗ region src.ptr a' bsrc))) hh
      rw [owned_pos (by omega)]
      unfold granted
      exact sep_lift.mpr ⟨hlen, by sep_normalize at hp ⊢; exact hp⟩

/-- The result of `allocSentinel`: `n + 1` items, undefined but the last. -/
def sentinelResult {T : Type} [Enc T] (I : AllocInv) (k : Nat) (n : BitVec 64) (sentinel : T) :
    Except ErrName Slice → Assn
  | .ok s => ⌜s.len = n⌝ ∗ (I.own ∗ granted I s.ptr k
      (writeBytes (Array.replicate (Enc.size T * (n.toNat + 1)) .undef) (Enc.size T * n.toNat)
        (Enc.encode sentinel)))
  | .error e => ⌜e = outOfMemory⌝ ∗ I.own

/-- `allocSentinel(T, n, sentinel)`. -/
theorem allocSentinel_spec {T : Type} [Enc T] [LawfulEnc T] (h : AllocSpec L vt ctx I) (k : Nat)
    (n : BitVec 64) (sentinel : T) (ra : BitVec 64) (hk : k < 64) (hT : 0 < Enc.size T)
    (hal : Enc.align T ∣ 2 ^ k) (hals : Enc.align T ∣ Enc.size T) (hn : n.toNat + 1 < 2 ^ 64) :
    L.T I.own (allocSentinel vt ctx k n sentinel ra) (sentinelResult I k n sentinel) := by
  have e1 : (n + 1).toNat = n.toNat + 1 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  refine L.bind (allocItems_spec h (Enc.size T) k (n + 1) ra hk) fun r => ?_
  cases r with
  | error e => exact L.ret' _ fun hh hp => hp
  | ok p =>
    dsimp only
    simp only [allocResult]
    rw [e1, owned_pos (by simp; exact Nat.mul_pos hT (by omega)), Ptr.elem_eq]
    unfold granted
    have ho : Enc.size T * n.toNat + Enc.size T ≤
        (Array.replicate (Enc.size T * (n.toNat + 1)) Byte.undef).size := by
      simp [Nat.mul_succ]
    refine L.bind (L.pre (L.frame (R := I.own ∗ I.tok p
          (Array.replicate (Enc.size T * (n.toNat + 1)) Byte.undef).size k)
        (L.ofTotal (Region.storeItem (p := p) (a := 2 ^ k)
          (bs := Array.replicate (Enc.size T * (n.toNat + 1)) Byte.undef)
          (o := Enc.size T * n.toNat) (al := Enc.align T) sentinel hT ho hal
          (Nat.dvd_trans hals (Nat.dvd_mul_right _ _)))))
        fun hh hp => by sep_normalize at hp ⊢; exact hp) fun _ => L.ret' _ fun hh hp => ?_
    show (⌜n = n⌝ ∗ (I.own ∗ granted I p k _)) hh
    unfold granted
    rw [writeBytes_size _ _ _ (by rw [LawfulEnc.size_encode]; exact ho)]
    exact sep_lift.mpr ⟨rfl, by sep_normalize at hp ⊢; exact hp⟩

/-- The result of `realloc` of the bytes `bs`: a slice of `size * newN` bytes that keeps the
common prefix, or `OutOfMemory` with the old slice unchanged. -/
def reallocResult (I : AllocInv) (k size : Nat) (old : Slice) (newN : BitVec 64)
    (bs : Array Byte) : Except ErrName Slice → Assn
  | .ok s => ⌜s.len = newN⌝ ∗ (I.own ∗ Assn.ex fun bs' =>
      ⌜bs'.size = size * newN.toNat ∧ keepsPrefix bs bs'⌝ ∗ owned I k s.ptr bs')
  | .error e => ⌜e = outOfMemory⌝ ∗ (I.own ∗ owned I k old.ptr bs)

/-- `realloc(old, newN)`: remap in place or moved, else allocate, copy and free. -/
theorem realloc_spec (h : AllocSpec L vt ctx I) (size k : Nat) (old : Slice) (newN ra : BitVec 64)
    (bs : Array Byte) (hk : k < 64) (hsize : 0 < size) (hsz : bs.size = old.len.toNat * size)
    (hs : bs.size < 2 ^ 64) :
    L.T (I.own ∗ owned I k old.ptr bs) (realloc vt ctx size k old newN ra)
      (reallocResult I k size old newN bs) := by
  unfold realloc
  split
  · rename_i h0
    have hb0 : bs.size = 0 := by rw [hsz, h0]; simp
    rw [owned_zero hb0]
    refine L.post (L.pre (allocSlice_spec h size k newN ra hk) fun hh hp => sep_emp.mp hp)
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
    have hbpos : 0 < bs.size := by rw [hsz]; exact Nat.mul_pos (by omega) hsize
    split
    · rename_i h1
      have hN : newN = 0 := by apply BitVec.eq_of_toNat_eq; simp [h1]
      refine L.bind (free_spec h size k old ra bs hk hsz hs) fun _ => L.ret' _ fun hh hp => ?_
      refine sep_lift.mpr ⟨hN.symm, sep_ex_right.mpr ⟨#[], sep_lift_right.mpr
        ⟨⟨by simp [h1], by simp [keepsPrefix]⟩, ?_⟩⟩⟩
      rw [owned_zero rfl]; exact sep_emp.mpr hp
    · rename_i h1
      rw [owned_pos (by omega)]
      split
      · exact L.ret' _ fun hh hp => sep_lift.mpr ⟨rfl, by rw [owned_pos (by omega)]; exact hp⟩
      · rename_i hov
        have ec : (itemBytes size newN).toNat = size * newN.toNat :=
          toNat_ofNat_lt (Nat.lt_of_not_le hov)
        have eo : (byteLen size old).toNat = bs.size := by
          unfold byteLen; rw [← hsz]; exact toNat_ofNat_lt hs
        have hcpos : 0 < size * newN.toNat := Nat.mul_pos hsize (by omega)
        refine L.bind (h.remap ⟨old.ptr, byteLen size old⟩ k (itemBytes size newN) ra bs hk
          (by rw [ec]; exact hcpos) eo hbpos) fun r => ?_
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
            (h.alloc (itemBytes size newN) k ra (by omega) hk)) fun hh hp => hp) fun r' => ?_
          cases r' with
          | none =>
            dsimp only
            exact L.ret' _ fun hh hp => sep_lift.mpr ⟨rfl, by rw [owned_pos (by omega)]; exact hp⟩
          | some p =>
            dsimp only
            refine granted_ex fun bn hbn => ?_
            rw [ec] at hbn
            unfold granted
            have em : (BitVec.ofNat 64 (min (itemBytes size newN).toNat
                (byteLen size old).toNat)).toNat * 1 = min bn.size bs.size := by
              rw [ec, eo, Nat.mul_one, ← hbn]
              exact toNat_ofNat_lt (by omega)
            -- copy the common prefix into the new region
            refine L.bind (L.pre (L.frame
              (R := I.own ∗ (I.tok p bn.size k ∗ I.tok old.ptr bs.size k))
              (L.ofTotal (Region.memcpy (d := p) (s := old.ptr) (a := 2 ^ k) (a' := 2 ^ k)
                (da := 1) (sa := 1) (sz := 1) (bd := bn) (bsrc := bs)
                (n := BitVec.ofNat 64 (min (itemBytes size newN).toNat (byteLen size old).toNat))
                (by rw [em]; omega) (by rw [em]; omega) (Nat.one_dvd _) (Nat.one_dvd _))))
              fun hh hp => by sep_normalize at hp ⊢; exact hp) fun _ => ?_
            rw [em]
            -- poison the old region
            refine L.bind (L.pre (L.frame
              (R := region p (2 ^ k) (writeBytes bn 0 (bs.extract 0 (min bn.size bs.size))) ∗
                (I.own ∗ (I.tok p bn.size k ∗ I.tok old.ptr bs.size k)))
              (L.ofTotal (Region.memsetUndef (p := old.ptr) (a := 2 ^ k) (bs := bs)
                (n := byteLen size old) eo)))
              fun hh hp => by sep_normalize at hp ⊢; exact hp) fun _ => ?_
            -- free it
            refine L.bind (L.pre (L.frame
              (R := region p (2 ^ k) (writeBytes bn 0 (bs.extract 0 (min bn.size bs.size))) ∗
                I.tok p bn.size k)
              (h.free ⟨old.ptr, byteLen size old⟩ k ra
                (Array.replicate (byteLen size old).toNat .undef) hk (by simp) (by simp; omega)))
              fun hh hp => ?_) fun _ => L.ret' _ fun hh hp => ?_
            · unfold granted
              rw [Array.size_replicate]
              rw [← eo] at hp
              sep_normalize at hp ⊢; exact hp
            · have hw : (writeBytes bn 0 (bs.extract 0 (min bn.size bs.size))).size = bn.size :=
                writeBytes_size _ _ _ (by simp; omega)
              refine sep_lift.mpr ⟨rfl, sep_ex_right.mpr ⟨_, sep_lift_right.mpr
                ⟨⟨by rw [hw, hbn], keepsPrefix_copy bs bn⟩, ?_⟩⟩⟩
              show (I.own ∗ owned I k p _) hh
              rw [owned_pos (by rw [hw, hbn]; omega)]
              unfold granted
              rw [hw]
              sep_normalize at hp ⊢; exact hp
