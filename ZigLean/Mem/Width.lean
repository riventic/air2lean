import ZigLean.Mem.Alloc

/-!
# Pointer width (T02)

The target's pointer width as a parameter: `PtrWidth.w64` (x86_64, aarch64) or `PtrWidth.w32`
(wasm32). It fixes the size of a pointer (`PtrWidth.bytes`), of `usize`/`isize`
(`PtrWidth.bits`), the layout of a slice (pointer, then length, each `bytes` bytes) and the
bound of every address and byte count (`PtrWidth.bound = 2 ^ bits`).

The definitions of `ZigLean/Mem/Basic.lean`, `Enc.lean` and `Alloc.lean` remain the 64-bit
model. Each width-parameterized definition here is proved equal to that model at `.w64`
(`ptrEnc_w64`, `sliceEnc_w64_encode`, `Allocator.allocOf_w64`, … in the proof-only
`ZigLean/Mem/WidthLemmas.lean`, so a differential mutation of the 64-bit model never breaks
this runtime module), so the 64-bit generated code keeps its existing terms and proofs. Generated code for a 32-bit profile uses the
definitions here, and opens `Zig.Wasm32` for the 4-byte encodings of `Ptr`, `?*T` and
`std.mem.Allocator` (`docs/generated-code.md` §Pointer width).
-/

namespace Zig

/-- The pointer width of a target profile (`profile.pointer_bits`). -/
inductive PtrWidth where
  | w32
  | w64
  deriving DecidableEq, Repr, Inhabited

namespace PtrWidth

/-- The size and alignment of a pointer, `usize` and `isize`. -/
abbrev bytes : PtrWidth → Nat
  | .w32 => 4
  | .w64 => 8

/-- The width of `usize`: `8 * bytes` (`bits_eq`). Reducible to a literal, so that
`SliceOf PtrWidth.w32.bits` is `Slice32` for instance search. -/
abbrev bits : PtrWidth → Nat
  | .w32 => 32
  | .w64 => 64

/-- `2 ^ bits`: every address, item count and byte count of the target is below it. -/
def bound (w : PtrWidth) : Nat := 2 ^ w.bits

/-- The profile's `pointer_bits`, if the model has that width. -/
def ofBits? : Nat → Option PtrWidth
  | 32 => some .w32
  | 64 => some .w64
  | _ => none

@[simp] theorem bits_w32 : PtrWidth.w32.bits = 32 := rfl
@[simp] theorem bits_w64 : PtrWidth.w64.bits = 64 := rfl
@[simp] theorem bound_w32 : PtrWidth.w32.bound = 2 ^ 32 := rfl
@[simp] theorem bound_w64 : PtrWidth.w64.bound = 2 ^ 64 := rfl

theorem bits_eq (w : PtrWidth) : w.bits = 8 * w.bytes := by cases w <;> rfl

theorem bytes_le_8 (w : PtrWidth) : w.bytes ≤ 8 := by cases w <;> decide

theorem ofBits?_bits (w : PtrWidth) : ofBits? w.bits = some w := by cases w <;> rfl

end PtrWidth

/-! ## Encodings -/

/-- The `w.bytes` fragments of the pointer `p`, little-endian. -/
def ptrFrags (w : PtrWidth) (p : Ptr) : Array Byte :=
  ((Array.finRange 8).extract 0 w.bytes).map (.ptrFrag p)

/-- A pointer of width `w`: `w.bytes` bytes that each remember the pointer. As for `Enc Ptr`
(MM-11), `w.bytes` integer bytes read as a pointer give the pointer to that address without a
block. -/
@[instance_reducible] def ptrEnc (w : PtrWidth) : Enc Ptr where
  size := w.bytes
  align := w.bytes
  encode p := ptrFrags w p
  decode bs := match (bs[0]? : Option Byte) with
    | some (.ptrFrag p _) =>
      if bs.extract 0 w.bytes == ptrFrags w p then pure p else throw .unspecified
    | some (.int _) => do
      let n ← intOfBytes w.bits bs
      pure ⟨none, n.toNat⟩
    | _ => throw .unspecified

/-- `?*T` of width `w`: `null` is address 0, `w.bytes` zero bytes. -/
@[instance_reducible] def optPtrEnc (w : PtrWidth) : Enc (Option Ptr) where
  size := w.bytes
  align := w.bytes
  encode
    | none => Array.replicate w.bytes (.int 0)
    | some p => ptrFrags w p
  decode bs :=
    if bs.extract 0 w.bytes == Array.replicate w.bytes (.int 0) then pure none
    else some <$> (ptrEnc w).decode bs

/-- A slice whose length is a `usize` of `n` bits. `SliceOf 64` is `Slice` (`Slice.toOf`). -/
structure SliceOf (n : Nat) where
  ptr : Ptr
  len : BitVec n
  deriving DecidableEq, Repr, Inhabited

/-- A wasm32 slice. -/
abbrev Slice32 := SliceOf 32

def Slice.toOf (s : Slice) : SliceOf 64 := ⟨s.ptr, s.len⟩
def SliceOf.toSlice (s : SliceOf 64) : Slice := ⟨s.ptr, s.len⟩

@[simp] theorem Slice.toOf_toSlice (s : SliceOf 64) : s.toSlice.toOf = s := rfl
@[simp] theorem SliceOf.toSlice_toOf (s : Slice) : s.toOf.toSlice = s := rfl

/-- A slice of width `w`: the pointer at offset 0, the length at offset `w.bytes`. -/
@[instance_reducible] def sliceEnc (w : PtrWidth) : Enc (SliceOf w.bits) where
  size := 2 * w.bytes
  align := w.bytes
  encode s := (ptrEnc w).encode s.ptr ++ Enc.encode s.len
  decode bs := do
    pure ⟨← (ptrEnc w).decode (bs.extract 0 w.bytes), ← Enc.decode (bs.extract w.bytes (2 * w.bytes))⟩

/-- `?[]T` of width `w`: `null` is a pointer with address 0; the length bytes are undefined. -/
@[instance_reducible] def optSliceEnc (w : PtrWidth) : Enc (Option (SliceOf w.bits)) where
  size := 2 * w.bytes
  align := w.bytes
  encode
    | none => Array.replicate w.bytes (.int 0) ++ Array.replicate w.bytes .undef
    | some s => (sliceEnc w).encode s
  decode bs :=
    if bs.extract 0 w.bytes == Array.replicate w.bytes (.int 0) then pure none
    else some <$> (sliceEnc w).decode bs

/-- `std.mem.Allocator`: two pointers. -/
@[instance_reducible] def allocatorEnc (w : PtrWidth) : Enc Allocator where
  size := 2 * w.bytes
  align := w.bytes
  encode _ := Array.replicate (2 * w.bytes) (.int 0)
  decode _ := pure ⟨⟩

instance instEncSlice32 : Enc Slice32 := sliceEnc .w32
instance (priority := high) instEncOptionSlice32 : Enc (Option Slice32) := optSliceEnc .w32

/-! The 4-byte encodings of the types whose global instance is the 64-bit one. Generated
code for a 32-bit profile opens `Zig.Wasm32`; its priority is above every global `Enc`
instance of these types. -/

namespace Wasm32
scoped instance (priority := 20000) encPtr : Enc Ptr := ptrEnc .w32
scoped instance (priority := 20000) encOptPtr : Enc (Option Ptr) := optPtrEnc .w32
scoped instance (priority := 20000) encAllocator : Enc Allocator := allocatorEnc .w32
end Wasm32

/-! ## `usize`-indexed operations

The same terms as the 64-bit operations, for an index or count of any width. Each is the
64-bit operation at `BitVec 64` by `rfl`. -/

/-- `Ptr.elem` for a `usize` of `n` bits. -/
@[inline] def Ptr.elemOf (p : Ptr) (size : Nat) {n : Nat} (i : BitVec n) : Ptr := p.add (size * i.toInt)

/-- `Ptr.elemSub` for a `usize` of `n` bits. -/
@[inline] def Ptr.elemSubOf (p : Ptr) (size : Nat) {n : Nat} (i : BitVec n) : Ptr :=
  p.add (-(size * i.toInt))

/-- `Zig.index` for a `usize` of `n` bits. -/
@[inline] def indexOf {α : Type} {n : Nat} (a : Array α) (i : BitVec n) : Result α :=
  if h : i.toNat < a.size then pure a[i.toNat] else throw .outOfBounds

/-- `Zig.vindex` for a `usize` of `n` bits. -/
@[inline] def vindexOf {α : Type} {k n : Nat} (a : Vector α k) (i : BitVec n) : Result α :=
  if h : i.toNat < k then pure a[i.toNat] else throw .outOfBounds

/-- `Zig.len` as a `usize` of `n` bits. An array of a pure function's `[]const T` comes from
`readSliceOf`, so its size is a `usize` of the target. -/
@[inline] def lenOf (n : Nat) {α : Type} (a : Array α) : BitVec n := BitVec.ofNat n a.size

/-- `@memset` with an item count of `n` bits. -/
def memsetOf {α : Type} [Enc α] {n : Nat} (align : Nat) (p : Ptr) (k : BitVec n) (v : Option α) :
    MemM Unit := do
  if k.toNat = 0 ∨ Enc.size α = 0 then return
  let _ ← (← get).access p (k.toNat * Enc.size α) align
  let item := match v with
    | some x => Enc.encode x
    | none => Array.replicate (Enc.size α) .undef
  storeBytes p align (Array.replicate k.toNat item).flatten

/-- `@memcpy`/`@memmove` with an item count of `n` bits. -/
def memmoveOf {n : Nat} (size dstAlign srcAlign : Nat) (dst src : Ptr) (k : BitVec n) : MemM Unit := do
  if k.toNat = 0 ∨ size = 0 then return
  let _ ← (← get).access dst (k.toNat * size) dstAlign
  let bs ← loadBytes src (k.toNat * size) srcAlign
  storeBytes dst dstAlign bs

/-- `memcpy` (`Zig.memcpy`) with item counts of `n` bits: the counts must agree and the ranges
must not overlap, else `.illegal` (`docs/illegal-behavior.md`). -/
def memcpyOf {n : Nat} (size dstAlign srcAlign : Nat) (dst src : Ptr) (k m : BitVec n) :
    MemM Unit :=
  if k ≠ m || dst.overlaps src (k.toNat * size) then throw .illegal
  else memmoveOf size dstAlign srcAlign dst src k

/-- `readSlice` of a slice with a length of `n` bits. -/
def readSliceOf (α : Type) [Enc α] {n : Nat} (align : Nat) (s : SliceOf n) : MemM (Array α) := do
  if s.len.toNat = 0 then return #[]
  let bs ← if Enc.size α = 0 then pure #[] else
    loadBytes s.ptr (s.len.toNat * Enc.size α) align
  (Array.range s.len.toNat).mapM fun i =>
    (Enc.decode (bs.extract (i * Enc.size α) ((i + 1) * Enc.size α)) : Result α)

/-- `@intFromPtr` on a target of width `w`. The model's address of a block can exceed the
target's address space (`alloc` does not bound `Mem.nextAddr`); the model chooses no
address then (`.unspecified`), so a proof that the code never throws shows that every
converted address fits. -/
def ptrAddrOf (w : PtrWidth) (p : Ptr) : MemM (BitVec w.bits) := do
  let a ← ptrAddr p
  if 0 ≤ a ∧ a < w.bound then pure (BitVec.ofInt w.bits a) else throw .unspecified

/-! ## Allocation arithmetic -/

/-- `zeroAllocPtr` on a target of width `w`: the highest address with the alignment. -/
def zeroAllocPtrOf (w : PtrWidth) (align : Nat) : Ptr := ⟨none, w.bound - align⟩

/-- `allocBytes` on a target of width `w`. -/
def allocBytesOf (w : PtrWidth) (align n : Nat) : MemM (Except ErrName Ptr) := do
  if n = 0 then return .ok (zeroAllocPtrOf w align)
  match ← rawAlloc n align with
  | some p => pure (.ok p)
  | none => pure (.error "OutOfMemory")

/-- `create(T)` on a target of width `w`. -/
def Allocator.createOf (w : PtrWidth) (_ : Allocator) (size align : Nat) :
    MemM (Except ErrName Ptr) :=
  allocBytesOf w align size

/-- `alloc(T, n)` on a target of width `w`: `n * size` bytes. A product that does not fit a
`usize` (`math.mul` overflow) is `error.OutOfMemory`, before any allocator decision. -/
def Allocator.allocOf (w : PtrWidth) (_ : Allocator) (size align : Nat) (n : BitVec w.bits) :
    MemM (Except ErrName (SliceOf w.bits)) := do
  if w.bound ≤ size * n.toNat then return .error "OutOfMemory"
  match ← allocBytesOf w align (size * n.toNat) with
  | .ok p => pure (.ok ⟨p, n⟩)
  | .error e => pure (.error e)

/-- `free(s)` of a slice with a length of `n` bits. -/
def Allocator.freeOf {n : Nat} (_ : Allocator) (size : Nat) (s : SliceOf n) : MemM Unit :=
  if size * s.len.toNat = 0 then pure () else poisonFree s.ptr (size * s.len.toNat)

/-- The size check of `allocOf`: a request of `size * n ≥ 2 ^ bits` bytes is
`error.OutOfMemory` without a change to memory, and consumes no allocation attempt. -/
theorem Allocator.allocOf_overflow (w : PtrWidth) (a : Allocator) (size align : Nat)
    (n : BitVec w.bits) (h : w.bound ≤ size * n.toNat) :
    a.allocOf w size align n = pure (.error "OutOfMemory") := by
  simp [Allocator.allocOf, h]

/-- A request below the bound is the byte allocation of `size * n` bytes. -/
theorem Allocator.allocOf_fits (w : PtrWidth) (a : Allocator) (size align : Nat)
    (n : BitVec w.bits) (h : size * n.toNat < w.bound) :
    a.allocOf w size align n = (do
      match ← allocBytesOf w align (size * n.toNat) with
      | .ok p => pure (.ok ⟨p, n⟩)
      | .error e => pure (.error e)) := by
  simp [Allocator.allocOf, Nat.not_le.mpr h]

/-- A successful `allocOf` returns `n` items whose byte count fits the target. -/
theorem Allocator.allocOf_ok (w : PtrWidth) (a : Allocator) (size align : Nat)
    (n : BitVec w.bits) (m m' : Mem) (s : SliceOf w.bits)
    (h : (a.allocOf w size align n).run m = pure (.ok s, m')) :
    s.len = n ∧ size * s.len.toNat < w.bound := by
  by_cases hb : w.bound ≤ size * n.toNat
  · rw [Allocator.allocOf_overflow w a size align n hb] at h
    simp only [StateT.run, pure, StateT.pure, ExceptT.pure, ExceptT.mk] at h
    cases h
  · have hlt := Nat.not_le.mp hb
    rw [Allocator.allocOf_fits w a size align n hlt] at h
    simp only [StateT.run, bind, StateT.bind, ExceptT.bind, ExceptT.mk] at h
    rcases hr : (allocBytesOf w align (size * n.toNat)) m with _ | _ | ⟨_ | p, m''⟩ <;>
      rw [hr] at h <;> simp only [ExceptT.bindCont, Option.bind, pure, StateT.pure, ExceptT.pure,
        ExceptT.mk, reduceCtorEq] at h
    all_goals (cases h; try exact ⟨rfl, hlt⟩)

end Zig
