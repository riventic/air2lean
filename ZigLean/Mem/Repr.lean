import ZigLean.Mem.Enc
import ZigLean.Mem.Null

/-!
# Zig ≤0.16 representation casts and optional-pointer conversions

Up to 0.16.0, `@bitCast` of an array, `extern` struct or `extern` union reinterprets the
in-memory representation (`docs/aggregate-casts.md`; 0.17.0 changed `@bitCast` to the logical
bit order and made `extern` struct and union casts compile errors). `reprCast β x` is that
reinterpretation: the bytes of `x` (`Enc.encode`, padding bytes `.undef`), then `β` decoded
from them. A destination part that needs a padding-derived (undefined) bit throws
`.unspecified`: Zig leaves it open, and the model does not choose a value.

`?*T` is `Option Ptr`, null is `none`, and its bytes are 8 zero bytes (address 0,
`ZigLean/Mem/Enc.lean`). The explicit conversions:

| Zig | Model | null |
|---|---|---|
| `*T` → `?*T` (wrap) | `optPtrWrap p = some p` | never null |
| `?*T` → `*U` (unwrap) | `optPtrUnwrap` | `.panic` |
| `?*T` → `usize` | `optPtrAddr` | 0 |
| `usize` → `?*T` | `optPtrFromAddr` | 0 gives null |

The lemmas below need no memory lemmas. The round-trip conditions of `reprCast` are in
`ZigLean/ReprCast.lean`.
-/

namespace Zig

/-- A Zig ≤0.16 `@bitCast` to `β`: decode `β` from the memory bytes of `x`. Bytes past the end
of `x`'s encoding are undefined. -/
def reprCast (β : Type) {α : Type} [Enc α] [Enc β] (x : α) : Result β :=
  Enc.decode (padTo (Enc.size β) (Enc.encode x))

/-- `*T` → `?*T`: the pointer itself. Its bytes are the pointer's bytes (`optPtr_encode_wrap`). -/
def optPtrWrap (p : Ptr) : Option Ptr := some p

/-- `?*T` → `*U`: requires a non-null pointer. The checked (safe) build tests the address
before the cast; a null operand here throws `.panic`, as `ptrRequireNonNull` does. -/
def optPtrUnwrap : Option Ptr → Result Ptr
  | some p => pure p
  | none => throw .panic

/-- `@intFromPtr` of `?*T`: null is address 0. -/
def optPtrAddr : Option Ptr → MemM Int
  | none => pure 0
  | some p => ptrAddr p

/-- `@ptrFromInt` to `?*T`: address 0 is null, any other address `ptrFromAddr`. -/
def optPtrFromAddr (n : Nat) : MemM (Option Ptr) :=
  if n == 0 then pure none else some <$> ptrFromAddr n

theorem optPtrUnwrap_wrap (p : Ptr) : optPtrUnwrap (optPtrWrap p) = pure p := rfl

theorem optPtrUnwrap_null : optPtrUnwrap none = throw .panic := rfl

/-- Unwrapping succeeds exactly on a wrapped pointer: the round trip `?*T → *T → ?*T` holds
only for a non-null operand. -/
theorem optPtrUnwrap_eq_pure {o : Option Ptr} {p : Ptr} :
    optPtrUnwrap o = pure p ↔ o = optPtrWrap p := by
  cases o with
  | none => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | some q => exact ⟨fun h => (by cases h; rfl), fun h => (by cases h; rfl)⟩

theorem optPtrWrap_ne_null (p : Ptr) : optPtrWrap p ≠ none := nofun

/-- Null is 8 zero bytes; a wrapped pointer has the pointer's own bytes. -/
theorem optPtr_encode_null : Enc.encode (none : Option Ptr) = Array.replicate 8 (.int 0) := rfl

theorem optPtr_encode_wrap (p : Ptr) : Enc.encode (optPtrWrap p) = Enc.encode p := rfl

theorem optPtr_decode_null :
    (Enc.decode (Array.replicate 8 (Byte.int 0)) : Result (Option Ptr)) = pure none := rfl

theorem optPtrAddr_null (m : Mem) : (optPtrAddr none).run m = pure (0, m) := rfl

theorem optPtrAddr_wrap (p : Ptr) : optPtrAddr (optPtrWrap p) = ptrAddr p := rfl

theorem optPtrFromAddr_zero (m : Mem) : (optPtrFromAddr 0).run m = pure (none, m) := rfl

/-- A non-zero address never gives null. -/
theorem optPtrFromAddr_pos (n : Nat) (h : n ≠ 0) :
    optPtrFromAddr n = optPtrWrap <$> ptrFromAddr n := by
  simp [optPtrFromAddr, h]; rfl

/-- `usize` → `?*T` → `usize` returns 0 for 0. -/
theorem optPtrAddr_fromAddr_zero (m : Mem) :
    (optPtrFromAddr 0 >>= optPtrAddr).run m = pure (0, m) := rfl

end Zig
