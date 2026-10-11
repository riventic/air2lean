import ZigLean.Mem.Enc

/-! Value, storage and projection operations for nonoptional C and allowzero pointers.
The pointer representation (`Ptr`, with `Ptr.null` at address zero) is separate from the
validity conditions of a dereference: address zero has no allocated block, and every access
still requires the existing live-block, bounds and alignment rule (`Mem.access`). An
optional of a nullable pointer (`?*allowzero T`) is deliberately not qualified. -/

namespace Zig

/-- A raw address-zero pointer with no provenance. It allocates no storage. -/
def Ptr.null : Ptr := ⟨none, 0⟩

/-- Address zero of a nullable pointer remains provenance-free, even if an external memory
state describes an object at zero. Nonzero casts use the existing provenance resolution. -/
def ptrFromAddrNullable (n : Nat) : MemM Ptr :=
  if n == 0 then pure Ptr.null else ptrFromAddr n

/-- `@ptrFromInt` to a pointer type of alignment `align`: address zero (if `nonNull`, the type does
not allow it) and a misaligned address are illegal behaviour that only Sema's safety checks
(`castToNull`, `incorrectAlignment`) catch, so the model checks them itself: `.illegal`. -/
def checkAddr (align : Nat) (nonNull : Bool) (n : Nat) : MemM Unit :=
  if (nonNull && n == 0) || n % align != 0 then throw .illegal else pure ()

/-- `@alignCast` (a pointer cast to a stricter alignment `align`): a misaligned pointer is
illegal behaviour that only Sema's check (`incorrectAlignment`) catches: `.illegal`. -/
def checkAlign (align : Nat) (p : Ptr) : MemM Unit := do
  if (← ptrAddr p) % align != 0 then throw .illegal

/-- Sentinel slicing `[..len :s]` of bytes at `p`: the byte at `len` must be `s`. Otherwise
illegal behaviour that only Sema's check (`sentinelMismatch`) catches: `.illegal`. -/
def checkSentinelByte (p : Ptr) (len : BitVec 64) (s : BitVec 8) : MemM Unit := do
  if (← load (BitVec 8) 1 (p.elem 1 len)) != s then throw .illegal

/-- Null tests observe the address and do not dereference the pointer. -/
def ptrIsNull (p : Ptr) : MemM Bool := do
  pure (decide ((← ptrAddr p) = 0))

/-- A C-pointer unwrap or nullable-to-nonnullable cast in the ReleaseSafe fragment. A
nonzero address preserves its pointer value; it does not establish dereference validity. -/
def ptrRequireNonNull (p : Ptr) : MemM Ptr := do
  if ← ptrIsNull p then throw .panic else pure p

/-- The storage dictionary of a C/allowzero pointer value in memory (a `[*c]T` variable,
struct field or array item). `Ptr.null` is eight zero integer bytes, the target's null
representation and the same bytes as a null `?*T` (`Enc (Option Ptr)`). The test is structural
(`p = Ptr.null`), not `ptrIsNull`: a pointer that reaches address zero by arithmetic on its
provenance keeps its fragments. Zero bytes from any
other source (`@memset`, zero-initialised storage) read back as `Ptr.null`. Every other pointer
keeps its provenance fragments; integer bytes other than zero remain unspecified. -/
def nullablePtrEnc : Enc Ptr where
  size := 8
  align := 8
  encode p := if p = Ptr.null then Array.replicate 8 (.int 0) else Enc.encode p
  decode bs :=
    if bs.extract 0 8 == Array.replicate 8 (.int 0) then pure Ptr.null else Enc.decode bs

/-- A projection of a C/allowzero base (`struct_field_ptr`, `ptr_elem_ptr`, `ptr_add`,
`ptr_sub`) is pointer formation, `ptrProject` (`ZigLean/Mem/Basic.lean`), as from any other base.
The compiler inserts no null check. A constant offset 0 is the base itself, also at address
zero; any other offset from a pointer without a block (address zero, a `@ptrFromInt` address no
block covers) is `.illegal`, because LLVM's `getelementptr inbounds` needs an allocated object
(native ReleaseSafe builds fold `p + n == null` to `p == null`). This variant is for a result
that the compiler types as a nonnullable pointer: Zig 0.14.1 and 0.15.2 type `&p.*.field` of a
`[*c]T` or `*allowzero T` as `*F`, not `*allowzero F` (0.16.0 keeps `allowzero`). Address zero
must not become a `*F`, so every offset from address zero is `.illegal` here. -/
def ptrProjectNonnull (p : Ptr) (project : Ptr → Ptr) : MemM Ptr := do
  if ← ptrIsNull p then throw .illegal else ptrProject p project

/-- A C/allowzero pointer coerced or cast to an ordinary optional pointer (`?*T`): address
zero becomes the explicit `none`; any other value becomes `some` of the same pointer. -/
def ptrToOptional (p : Ptr) : MemM (Option Ptr) := do
  if ← ptrIsNull p then pure none else pure (some p)

/-- An ordinary optional pointer (`?*T`) coerced or cast to a C/allowzero pointer: `none`
becomes address zero. No dereference or allocation takes place. -/
def ptrOfOptional : Option Ptr → Ptr
  | none => Ptr.null
  | some p => p

/-- A null pointer never supplies an allocation for an access, including zero-byte access. -/
theorem null_access (m : Mem) (n a : Nat) :
    m.access Ptr.null n a = throw .illegal := by rfl

/-- The zero conversion does not change memory or acquire provenance. -/
theorem nullable_from_zero (m : Mem) :
    (ptrFromAddrNullable 0).run m = pure (Ptr.null, m) := by rfl

/-- The null test is valid in every memory state and does not access any block. -/
theorem null_is_null (m : Mem) :
    (ptrIsNull Ptr.null).run m = pure (true, m) := by rfl

/-- A C unwrap or a nonnullable cast of null fails; it cannot turn zero into storage. -/
theorem null_unwrap (m : Mem) :
    (ptrRequireNonNull Ptr.null).run m = throw .panic := by rfl

/-- A nonzero integer address still cannot be dereferenced without block provenance. -/
theorem raw_address_access (m : Mem) (off : Int) (n a : Nat) :
    m.access ⟨none, off⟩ n a = throw .illegal := by rfl

/-- A zero-offset projection of address zero is address zero; memory is unchanged. -/
theorem null_project_zero (m : Mem) (project : Ptr → Ptr) (h : project Ptr.null = Ptr.null) :
    (ptrProject Ptr.null project).run m = pure (Ptr.null, m) := by
  simp [ptrProject, StateT.run, h]

/-- A nonzero-offset projection from address zero is illegal behaviour; it cannot reach an
object. -/
theorem null_project (m : Mem) (project : Ptr → Ptr) (h : project Ptr.null ≠ Ptr.null) :
    (ptrProject Ptr.null project).run m = throw .illegal := by
  simp only [ptrProject, StateT.run]
  rw [if_neg (by simp only [Ptr.null] at h; simp [h, Mem.inBounds, Ptr.null])]

/-- A projection typed as a nonnullable pointer never yields address zero. -/
theorem null_project_nonnull (m : Mem) (project : Ptr → Ptr) :
    (ptrProjectNonnull Ptr.null project).run m = throw .illegal := by rfl

/-- Every pointer derived from address zero by an offset still has no block: an access
through it fails, for every size and alignment. -/
theorem null_offset_access (m : Mem) (off : Int) (n a : Nat) :
    m.access (Ptr.null.add off) n a = throw .illegal := by rfl

/-- Address zero converts to the explicit `none` of an ordinary optional pointer. -/
theorem null_to_optional (m : Mem) :
    (ptrToOptional Ptr.null).run m = pure (none, m) := by rfl

/-- An ordinary optional `none` converts to address zero. -/
theorem optional_none_to_null : ptrOfOptional none = Ptr.null := rfl

end Zig
