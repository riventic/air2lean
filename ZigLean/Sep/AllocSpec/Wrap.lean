import ZigLean.Sep.AllocSpec

/-!
# The step semantics of the `std.mem.Allocator` wrappers (Zig 0.16.0)

`Wrap.*` follow `lib/std/mem/Allocator.zig` as the compiler emits it, over a `RawVTable` `vt`
with context `ctx` (the `Allocator` value `{ ptr = ctx, vtable }`). The generated wrappers of a
translated program (`--allocator-model=translated`) are equal to these once the vtable load and
the indirect call are the dispatch of `ZigLean/Sep/AllocSpec/Dispatch.lean`
(`tests/roadmap/alloc-fba/AllocFba/Bridge.lean`): the generated code is the ground truth, and
each detail below is in it.

* `@returnAddress()` is read (the oracle `returnAddress`) where the source reads it: first in
  `alloc`/`alignedAlloc`/`create`/`allocSentinel`/`realloc`, after the `@memset` in `free`, and
  not at all for a zero-sized `create`/`destroy` or an empty `free`.
* `allocBytesWithAlignment` checks the `@alignCast` of the result (`alignCast`) when the
  alignment is above 1.
* `dupe` and the copying path of `realloc` check that the two ranges of the `@memcpy` do not
  overlap (two `ptrLe` address comparisons), and the lengths agree.
* `allocSentinel` computes `n + 1` with an overflow check, stores the sentinel, and reads it
  back when it slices `ptr[0..n :sentinel]`.
* `free` of a sentinel-terminated slice absorbs the sentinel with an overflow-checked `len + 1`.

An item type is its size `size` and the log2 `k` of its alignment.
-/

namespace Zig

namespace Wrap

def outOfMemory : ErrName := "OutOfMemory"

/-- The pointer of a zero-byte allocation: no block, the highest address with alignment `a`
(`alignment.backward(maxInt(usize))`). -/
def zeroPtr (a : Nat) : Ptr := ⟨none, 2 ^ 64 - a⟩

/-- The byte length of a slice of items of `size` bytes (`@ptrCast` to `[]u8`). -/
def byteLen (size : Nat) (s : Slice) : BitVec 64 := BitVec.ofNat 64 (s.len.toNat * size)

/-- A pure helper (overflow-checked arithmetic) in `MemM`. -/
abbrev liftR {α : Type} (r : Result α) : MemM α := StateT.lift r

variable (vt : RawVTable) (ctx : Ptr)

/-- `@alignCast` of a fresh pointer to alignment `2 ^ k`: no check for `k = 0`. -/
def alignCast (k : Nat) (p : Ptr) : MemM (Except ErrName Ptr) :=
  if k = 0 then pure (.ok p) else
  ptrAddr p >>= fun a =>
    if (BitVec.ofInt 64 a &&& BitVec.ofNat 64 (2 ^ k - 1)) = 0 then pure (.ok p) else throw .panic

/-- `allocBytesWithAlignment`. -/
def allocBytes (k : Nat) (n ra : BitVec 64) : MemM (Except ErrName Ptr) :=
  if n = 0 then pure (.ok (zeroPtr (2 ^ k))) else
  vt.alloc ctx n k ra >>= fun r => match r with
    | none => pure (.error outOfMemory)
    | some p => memset (α := BitVec 8) 1 p n none >>= fun _ => alignCast k p

/-- `allocWithSizeAndAlignment`: the byte count, checked for overflow (`math.mul`). -/
def allocItems (size k : Nat) (n ra : BitVec 64) : MemM (Except ErrName Ptr) :=
  if (BitVec.ofNat 64 size).umulOverflow n then pure (.error outOfMemory)
  else allocBytes vt ctx k (BitVec.ofNat 64 size * n) ra

/-- `allocAdvancedWithRetAddr`: a slice of `n` items. -/
def allocAdvanced (size k : Nat) (n ra : BitVec 64) : MemM (Except ErrName Slice) :=
  allocItems vt ctx size k n ra >>= fun r => match r with
    | .error e => pure (.error e)
    | .ok p => pure (.ok ⟨p, n⟩)

/-- `alloc(T, n)` and `alignedAlloc(T, k, n)`. -/
def allocSlice (size k : Nat) (n : BitVec 64) : MemM (Except ErrName Slice) :=
  returnAddress >>= fun ra => allocAdvanced vt ctx size k n ra

/-- `create(T)`. -/
def create (size k : Nat) : MemM (Except ErrName Ptr) :=
  if size = 0 then pure (.ok (zeroPtr (2 ^ k)))
  else returnAddress >>= fun ra => allocBytes vt ctx k (BitVec.ofNat 64 size) ra

/-- `destroy(p)`: no `@memset`, a direct `rawFree`. -/
def destroy (size k : Nat) (p : Ptr) : MemM Unit :=
  if size = 0 then pure ()
  else returnAddress >>= fun ra => vt.free ctx ⟨p, BitVec.ofNat 64 size⟩ k ra

/-- `free` of the byte slice `bytes`. -/
def freeBytes (k : Nat) (bytes : Slice) : MemM Unit :=
  if bytes.len = 0 then pure () else
  memset (α := BitVec 8) 1 bytes.ptr bytes.len none >>= fun _ =>
    returnAddress >>= fun ra => vt.free ctx bytes k ra

/-- `free(memory)` for a slice of items of `size` bytes. -/
def free (size k : Nat) (s : Slice) : MemM Unit :=
  freeBytes vt ctx k ⟨s.ptr, byteLen size s⟩

/-- `free(memory)` of a sentinel-terminated slice: `mem.absorbSentinel` adds the sentinel item. -/
def freeSentinel (size k : Nat) (s : Slice) : MemM Unit :=
  liftR (Zig.add false s.len 1) >>= fun n => free vt ctx size k ⟨s.ptr, n⟩

/-- `@memcpy(dst[0..n], src[0..n])` of `n` items of `size` bytes, after its checks: the lengths
agree and the two address ranges do not overlap. -/
def copyChecked (size da sa : Nat) (dst src : Ptr) (n : BitVec 64) : MemM Unit :=
  ptrLe (src.elem size n) dst >>= fun b₁ => ptrLe (dst.elem size n) src >>= fun b₂ =>
    if (b₁ || b₂) = true then memmove size da sa dst src n else throw .panic

/-- `dupe(T, m)`: `alloc` and `@memcpy` (source alignment `sa`). -/
def dupe (size k sa : Nat) (src : Slice) : MemM (Except ErrName Slice) :=
  allocSlice vt ctx size k src.len >>= fun r => match r with
    | .error e => pure (.error e)
    | .ok d =>
      if d.len = src.len then
        copyChecked size (2 ^ k) sa d.ptr src.ptr d.len >>= fun _ => pure (.ok d)
      else throw .panic

/-- `allocSentinel(T, n, sentinel)` (`allocWithOptionsRetAddr`): `n + 1` items, the last the
sentinel, which the slicing `ptr[0..n :sentinel]` reads back. -/
def allocSentinel {T : Type} [Enc T] [DecidableEq T] (k : Nat) (n : BitVec 64) (sentinel : T) :
    MemM (Except ErrName Slice) :=
  returnAddress >>= fun ra => liftR (Zig.add false n 1) >>= fun n₁ =>
  allocAdvanced vt ctx (Enc.size T) k n₁ ra >>= fun r => match r with
    | .error e => pure (.error e)
    | .ok s =>
      if Zig.lt false n s.len = true then
        store (Enc.align T) (s.ptr.elem (Enc.size T) n) sentinel >>= fun _ =>
        liftR (Zig.add false n 1) >>= fun n₂ =>
        if Zig.le false n₂ s.len = true then
          load T (Enc.align T) (s.ptr.elem (Enc.size T) n) >>= fun x =>
          if sentinel = x then pure (.ok ⟨s.ptr, n⟩) else throw .panic
        else throw .outOfBounds
      else throw .outOfBounds

/-- `reallocAdvanced(old, newN, ra)`: remap in place or moved, else allocate, copy the common
prefix (checked `@memcpy`), poison and free the old bytes. -/
def reallocAdvanced (size k : Nat) (old : Slice) (newN ra : BitVec 64) :
    MemM (Except ErrName Slice) :=
  if old.len = 0 then allocAdvanced vt ctx size k newN ra else
  if newN = 0 then free vt ctx size k old >>= fun _ => pure (.ok ⟨zeroPtr (2 ^ k), 0⟩) else
  if (BitVec.ofNat 64 size).umulOverflow newN then pure (.error outOfMemory) else
  let ob : Slice := ⟨old.ptr, byteLen size old⟩
  let nb := BitVec.ofNat 64 size * newN
  vt.remap ctx ob k nb ra >>= fun r => match r with
    | some p => pure (.ok ⟨p, newN⟩)
    | none => vt.alloc ctx nb k ra >>= fun r' => match r' with
      | none => pure (.error outOfMemory)
      | some q =>
        let c := Zig.min false nb ob.len
        if Zig.le false c ob.len = true then
          copyChecked 1 1 1 q ob.ptr c >>= fun _ =>
          memset (α := BitVec 8) 1 ob.ptr ob.len none >>= fun _ =>
          vt.free ctx ob k ra >>= fun _ => pure (.ok ⟨q, newN⟩)
        else throw .outOfBounds

/-- `realloc(old, newN)`. -/
def realloc (size k : Nat) (old : Slice) (newN : BitVec 64) : MemM (Except ErrName Slice) :=
  returnAddress >>= fun ra => reallocAdvanced vt ctx size k old newN ra

/-! ## Byte-sized items -/

theorem byteLen_one (s : Slice) : byteLen 1 s = s.len := by
  simp [byteLen]

theorem allocItems_one (k : Nat) (n ra : BitVec 64) :
    allocItems vt ctx 1 k n ra = allocBytes vt ctx k n ra := by
  have h : (BitVec.ofNat 64 1).umulOverflow n = false := by
    simp [BitVec.umulOverflow, n.isLt]
  simp only [allocItems, h, Bool.false_eq_true, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt n.isLt]

theorem free_one (k : Nat) (s : Slice) : free vt ctx 1 k s = freeBytes vt ctx k s := by
  simp [free, byteLen_one]

end Wrap

end Zig
