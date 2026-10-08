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

/-- Null tests observe the address and do not dereference the pointer. -/
def ptrIsNull (p : Ptr) : MemM Bool := do
  pure (decide ((← ptrAddr p) = 0))

/-- Equality of nullable pointers observes addresses, including address zero. -/
def ptrEqAddr (p q : Ptr) : MemM Bool := do
  pure (decide ((← ptrAddr p) = (← ptrAddr q)))

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

/-- A field or element projection (`struct_field_ptr`, `ptr_elem_ptr`, `ptr_add`, `ptr_sub`)
whose base is a C/allowzero pointer. Address zero is `.illegal`; the compiler inserts no
safety check. This is a deliberate over-approximation: native Zig is defined for some of these
projections (an offset-0 field pointer emits no `getelementptr`, `allowzero` makes address 0 a
valid address, and the langref places the illegal behaviour at the dereference). It is
conservative for proofs that nothing is illegal, but wrong for outcome reports and native
differential comparisons, which see `.illegal` where the native program is defined. A nonnull
base is projected unchanged. Nonnull does not establish provenance, lifetime, bounds or alignment: a later
access through the result still needs `Mem.access`'s premises for the base's block. -/
def ptrProjectNullable (p : Ptr) (project : Ptr → Ptr) : MemM Ptr := do
  if ← ptrIsNull p then throw .illegal else pure (project p)

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

/-- A projection from address zero is illegal behaviour; it cannot reach an object. -/
theorem null_project (m : Mem) (project : Ptr → Ptr) :
    (ptrProjectNullable Ptr.null project).run m = throw .illegal := by rfl

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
