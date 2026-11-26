import ZigLean.Sep.Full.Wrappers
import ZigLean.Sep.Full.Dispatch

/-!
# Sentinel buffers through `std.mem.Allocator`: the statements, for every item kind (M04)

A sentinel buffer `[:s]T` of `len` items that a `std.mem.Allocator` granted is a grant of
`(len + 1) * sz` bytes at alignment `2 ^ k`, the sentinel item counted, with `sz = @sizeOf(T)`
and `2 ^ k` the slice's alignment (`@alignOf(T)`, or more for an over-aligned slice). This module
states that once, for every item size `sz`, log2 alignment `k`, sentinel bytes `z` (the encoding
of `s`) and allocator invariant `I`:

* the bytes of a reallocated buffer: `Appended`, `Resized`;
* what the four operations of a client return, as plain assertions (`docs/interfaces.md`: a
  contract is a pre- and a postcondition, there is no judgment of its own): `made`, `appended`,
  `resized`; `release` gives the fee back;
* **the generic theorems** of the two operations that reallocate: `append_grant` and
  `resize_grant`. Zig compiles one copy of a generic client per item type, so the code of an
  instance is walked per instance (`fsym`); what the walk gives is the instance's *shape*: the
  reallocated grant with the item and the sentinel written at their byte offsets (`appendedAt`,
  `resizedAt`). The theorems derive the statement from the shape and the sizes of the encodings,
  for every `sz`, `k` and `z`. An instance supplies only those facts.

`make` (`allocSentinel`) and `release` (`free`) have no step between the walk and the statement:
an instance proves `made` and the fee directly.

Instances: `tests/roadmap/interfaces/Interfaces/SentinelSpec.lean` (`u8`: `sz = 1`, `k = 0`),
`WideSpec.lean` (`u16`, `u32`, `u64`).
-/

namespace Zig.Full.SentinelBuf

open Zig.Full.FAssn

/-! ## The bytes -/

/-- The bytes of `append`'s grant: `len + 2` items of `sz` bytes, the old payload (items
`[0, len)`), then the item `c`, then the sentinel `z`. -/
def Appended (sz : Nat) (z c bs bs' : Array Byte) (len : Nat) : Prop :=
  bs'.size = (len + 2) * sz ∧ bs'.extract 0 (len * sz) = bs.extract 0 (len * sz) ∧
    bs'.extract (len * sz) ((len + 1) * sz) = c ∧ bs'.extract ((len + 1) * sz) ((len + 2) * sz) = z

/-- The bytes of `resize`'s grant to `n` items of `sz` bytes: `n + 1` items, the old items below
`min n (len + 1)`, the sentinel `z` at item `n`. -/
def Resized (sz : Nat) (z bs bs' : Array Byte) (len n : Nat) : Prop :=
  bs'.size = (n + 1) * sz ∧
    bs'.extract 0 (Min.min n (len + 1) * sz) = bs.extract 0 (Min.min n (len + 1) * sz) ∧
    bs'.extract (n * sz) ((n + 1) * sz) = z

section Bytes

variable {g z c bs : Array Byte} {sz len n : Nat}

/-- A reallocated buffer of `len + 2` items with the item `c` written at item `len` and the
sentinel `z` after it is `append`'s. -/
theorem Appended.of_writes (hc : c.size = sz) (hz : z.size = sz) (hlen : (len + 1) * sz = bs.size)
    (hg : g.size = (len + 2) * sz) (hk : keepsPrefix bs g) :
    Appended sz z c bs (writeBytes (writeBytes g (len * sz) c) ((len + 1) * sz) z) len := by
  have e1 : (len + 1) * sz = len * sz + sz := by rw [Nat.add_mul, Nat.one_mul]
  have e2 : (len + 2) * sz = len * sz + sz + sz := by rw [Nat.add_mul]; omega
  unfold Appended
  rw [e1] at hlen ⊢
  rw [e2] at hg ⊢
  have hw := writeBytes_size g (len * sz) c (by omega)
  have hw' := writeBytes_size (writeBytes g (len * sz) c) (len * sz + sz) z (by omega)
  refine ⟨by omega, ?_, ?_, ?_⟩
  · rw [extract_writeBytes_other (by omega) (by omega) (by omega) (by right; omega),
      extract_writeBytes_other (by omega) (by omega) (by omega) (by right; omega)]
    exact extract_of_keepsPrefix hk (by omega) (by omega)
  · rw [extract_writeBytes_other (by omega) (by omega) (by omega) (by right; omega)]
    have e := extract_writeBytes g (len * sz) c (by omega)
    rwa [hc] at e
  · have e := extract_writeBytes (writeBytes g (len * sz) c) (len * sz + sz) z (by omega)
    rwa [hz] at e

/-- A reallocated buffer of `n + 1` items with the sentinel `z` written at item `n` is
`resize`'s. -/
theorem Resized.of_write (hz : z.size = sz) (hlen : (len + 1) * sz = bs.size)
    (hg : g.size = (n + 1) * sz) (hk : keepsPrefix bs g) :
    Resized sz z bs (writeBytes g (n * sz) z) len n := by
  have hm : Min.min n (len + 1) * sz ≤ n * sz := Nat.mul_le_mul_right sz (Nat.min_le_left _ _)
  have hm' : Min.min n (len + 1) * sz ≤ (len + 1) * sz :=
    Nat.mul_le_mul_right sz (Nat.min_le_right _ _)
  have e1 : (n + 1) * sz = n * sz + sz := by rw [Nat.add_mul, Nat.one_mul]
  unfold Resized
  rw [e1] at hg ⊢
  refine ⟨by rw [writeBytes_size g (n * sz) z (by omega)]; exact hg, ?_, ?_⟩
  · rw [extract_writeBytes_other (by omega) (by omega) (by omega) (by right; omega)]
    exact extract_of_keepsPrefix hk (by omega) (by omega)
  · have e := extract_writeBytes g (n * sz) z (by omega)
    rwa [hz] at e

end Bytes

/-! ## What the clients return -/

variable (I : FAllocInv) (φ : Frac)

/-- What `make` returns: `n` undefined items of `sz` bytes and the sentinel `z` after them, or
`error.OutOfMemory` and the fee back. -/
def made (k sz : Nat) (z : Array Byte) (n : BitVec 64) : Except ErrName Slice → FAssn
  | .ok r => ⟪r.len = n⟫ ⋆ I.granted r.ptr k φ
      (writeBytes (Array.replicate ((n.toNat + 1) * sz) .undef) (n.toNat * sz) z)
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ I.fee φ

/-- What `append` of the item `c` to a buffer of `len` items (the grant `bs` at `old`) returns. -/
def appended (k sz : Nat) (z c : Array Byte) (old : Ptr) (bs : Array Byte) (len : Nat) :
    Except ErrName Slice → FAssn
  | .ok r => ⟪r.len.toNat = len + 1⟫ ⋆ ((FAssn.ex fun bs' => ⟪Appended sz z c bs bs' len⟫ ⋆
      I.granted r.ptr k φ bs') ⋆ I.fee φ)
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ (I.granted old k φ bs ⋆ I.fee φ)

/-- What `resize` of a buffer of `len` items (the grant `bs` at `old`) to `n` items returns. -/
def resized (k sz : Nat) (z : Array Byte) (old : Ptr) (bs : Array Byte) (len : Nat) (n : BitVec 64) :
    Except ErrName Slice → FAssn
  | .ok r => ⟪r.len = n⟫ ⋆ ((FAssn.ex fun bs' => ⟪Resized sz z bs bs' len n.toNat⟫ ⋆
      I.granted r.ptr k φ bs') ⋆ I.fee φ)
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ (I.granted old k φ bs ⋆ I.fee φ)

/-! ## The shape of an instance's code, and the generic theorems

The byte offsets of the stores are stated as values with their equations (`o₁ = len * sz`), not
as terms of the bytes: a walk has them in its own normal form (`s.len.toNat * 2`), and proves
the equations by arithmetic. -/

/-- The shape of `append`: the absorbed buffer reallocated to `len + 2` items (`g`, which keeps
the old bytes), then the item `c` stored at byte `o₁ = len * sz` and the sentinel `z` at byte
`o₂ = (len + 1) * sz`; or the failure of the reallocation, the old grant unchanged. -/
def appendedAt (k sz : Nat) (z c : Array Byte) (old : Ptr) (bs : Array Byte) (len : Nat) :
    Except ErrName Slice → FAssn
  | .ok r => ⟪r.len.toNat = len + 1⟫ ⋆ ((FAssn.ex fun g => FAssn.ex fun o₁ => FAssn.ex fun o₂ =>
      ⟪g.size = (len + 2) * sz ∧ keepsPrefix bs g ∧ o₁ = len * sz ∧ o₂ = (len + 1) * sz⟫ ⋆
        I.granted r.ptr k φ (writeBytes (writeBytes g o₁ c) o₂ z)) ⋆ I.fee φ)
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ (I.granted old k φ bs ⋆ I.fee φ)

/-- The shape of `resize`: the absorbed buffer reallocated to `n + 1` items (`g`, which keeps the
common prefix), then the sentinel `z` stored at byte `o = n * sz`; or the failure of the
reallocation, the old grant unchanged. -/
def resizedAt (k sz : Nat) (z : Array Byte) (old : Ptr) (bs : Array Byte) (n : BitVec 64) :
    Except ErrName Slice → FAssn
  | .ok r => ⟪r.len = n⟫ ⋆ ((FAssn.ex fun g => FAssn.ex fun o =>
      ⟪g.size = (n.toNat + 1) * sz ∧ keepsPrefix bs g ∧ o = n.toNat * sz⟫ ⋆
        I.granted r.ptr k φ (writeBytes g o z)) ⋆ I.fee φ)
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ (I.granted old k φ bs ⋆ I.fee φ)

variable {I φ} {Tgt : Type} {x : ConcM Tgt (Except ErrName Slice)} {P F : FAssn} {k sz len : Nat}
  {z c bs : Array Byte} {old : Ptr}

/-- A consequence in the result assertion of a client's postcondition. -/
private theorem post_result {A B : Except ErrName Slice → FAssn}
    (h : CTriple P x (fun r => I.own ⋆ (A r ⋆ F) ⋆ plain)) (hab : ∀ r res, A r res → B r res) :
    CTriple P x (fun r => I.own ⋆ (B r ⋆ F) ⋆ plain) :=
  h.post fun r _ => sep_mono_right fun _ => sep_mono_left fun _ => sep_mono_left (hab r)

/-- **`append`, for every item kind**: code of the shape `appendedAt` for an item and a sentinel
of `sz` bytes each returns one more item `c` with the sentinel after it, the old payload kept; or
the old buffer. -/
theorem append_grant (hc : c.size = sz) (hz : z.size = sz) (hlen : (len + 1) * sz = bs.size)
    (h : CTriple P x (fun r => I.own ⋆ (appendedAt I φ k sz z c old bs len r ⋆ F) ⋆ plain)) :
    CTriple P x (fun r => I.own ⋆ (appended I φ k sz z c old bs len r ⋆ F) ⋆ plain) :=
  post_result h fun r _ hr => by
    cases r with
    | error e => exact hr
    | ok r =>
      refine sep_mono_right (fun _ => sep_mono_left ?_) hr
      rintro _ ⟨g, o₁, o₂, hg⟩
      obtain ⟨⟨hs, hk, rfl, rfl⟩, hg⟩ := sep_lift.mp hg
      exact ⟨_, sep_lift.mpr ⟨Appended.of_writes hc hz hlen hs hk, hg⟩⟩

/-- **`resize`, for every item kind**: code of the shape `resizedAt` for a sentinel of `sz` bytes
returns `n` items, the old items below `min n (len + 1)` kept, the sentinel at item `n`; or the
old buffer. -/
theorem resize_grant {n : BitVec 64} (hz : z.size = sz) (hlen : (len + 1) * sz = bs.size)
    (h : CTriple P x (fun r => I.own ⋆ (resizedAt I φ k sz z old bs n r ⋆ F) ⋆ plain)) :
    CTriple P x (fun r => I.own ⋆ (resized I φ k sz z old bs len n r ⋆ F) ⋆ plain) :=
  post_result h fun r _ hr => by
    cases r with
    | error e => exact hr
    | ok r =>
      refine sep_mono_right (fun _ => sep_mono_left ?_) hr
      rintro _ ⟨g, o, hg⟩
      obtain ⟨⟨hs, hk, rfl⟩, hg⟩ := sep_lift.mp hg
      exact ⟨_, sep_lift.mpr ⟨Resized.of_write hz hlen hs hk, hg⟩⟩

/-- The vtable's `free` of a slice that the `free` wrapper has made undefined
(`@memset(bytes, undefined)` of the whole slice): the fee back. `CAllocSpec.free'` at those
bytes, for a walk whose state holds them by the slice's length. -/
theorem free_undef {vt : CVTable Tgt} {ctx : Ptr} (h : CAllocSpec vt ctx I) (s : Slice) (k : Nat)
    (ra : BitVec 64) (hk : k < 64) (hs : 0 < s.len.toNat) :
    CTriple (I.own ⋆ I.granted s.ptr k φ (Array.replicate s.len.toNat .undef))
      (vt.free ctx s k ra) (fun _ => I.own ⋆ I.fee φ) :=
  CAllocSpec.free' h s k ra φ _ hk (by simp) (by simpa using hs)

end Zig.Full.SentinelBuf
