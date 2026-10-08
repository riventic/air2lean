import ZigLean.Mem.Basic

/-! Value operations for nonoptional C and allowzero pointers. Nullable-pointer memory
encodings and optional(nullable-pointer) representations are deliberately not qualified.
Address zero has no allocated block; access still requires the existing live-block rule. -/

namespace Zig

/-- A raw address-zero pointer with no provenance. It allocates no storage. -/
def Ptr.null : Ptr := ⟨none, 0⟩

/-- Address zero of a nullable pointer remains provenance-free, even if an external memory
state describes an object at zero. Nonzero casts use the existing provenance resolution. -/
def ptrFromAddrNullable (n : Nat) : MemM Ptr :=
  if n == 0 then pure Ptr.null else ptrFromAddr n

/-- Null tests observe the address and do not dereference the pointer. -/
def ptrIsNull (p : Ptr) : MemM Bool := do
  pure (decide ((← ptrAddr p) = 0))

/-- A C-pointer unwrap or nullable-to-nonnullable cast in the ReleaseSafe fragment. A
nonzero address preserves its pointer value; it does not establish dereference validity. -/
def ptrRequireNonNull (p : Ptr) : MemM Ptr := do
  if ← ptrIsNull p then throw .panic else pure p

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

end Zig
