import TryPointers.Gen
import ZigLean.Sep.Full.Try
import ZigLean.Sep.Full.Auto

/-! Whole-union memory rules for the actual retained generated `writeAlias`, `cleanup` and
`coldPayload` definitions. Unlike `Proofs.lean` (tag/readable-byte ownership of `payload8` and
`payload64`), these own the typed union `pts p 2 u`, so they state what the payload aliases
observe and what the cleanup paths write:

* `writeAlias`: both pointer-try results address the same payload. A write through the first
  is the value read through the second and is left in the union; the tag is not written.
  An error returns the original name and writes nothing.
* `cleanup` with distinct counters: success runs only `defer`; error runs `errdefer` and
  `defer`, returns the original error, and leaves the union unchanged.
* `cleanup` with one counter passed for both cleanup pointers (aliased cleanup targets):
  error increments that counter twice, success once.
* `coldPayload`: the cold error body runs its `errdefer`; success returns the payload address.

The result value is captured before cleanup runs. Counter increments use `add_safe`, so each
rule requires the counter to have room for its increments. The triples are total full-state
ones, each proved by `fsym` on each shape of the union (`ZigLean/Sep/Full/Try.lean`); the error's
membership in the declared domain is the one side goal it leaves. -/

open Zig
open scoped Zig
open Zig.Full Zig.Full.FAssn

namespace TryPointersAliasProofs

/-- The finite domain declared by every retained source AIR function. -/
abbrev domain : ErrorDomain := ⟨#["Bad", "Other"], by decide, by decide⟩

def admitted (u : Except ErrName (BitVec 8)) : Prop :=
  ∀ e, u = .error e → domain.names.contains e = true

theorem admitted_all {u : Except ErrName (BitVec 8)} (h : admitted u) :
    (errTagOf u).all domain.names.contains = true := by
  cases u with
  | ok => rfl
  | error e => exact h e rfl

/-! ## Two pointer-try results alias -/

theorem writeAlias_owned (p : Ptr) (u : Except ErrName (BitVec 8)) (y : BitVec 8)
    (hdom : admitted u) :
    FTotalTriple (up (pts p 2 u)) (TryPointers.writeAlias p y)
      (fun r => ⟪r = writeView y u⟫ ⋆ up (pts p 2 (writeView y u))) := by
  have hd := admitted_all hdom
  unfold TryPointers.writeAlias; cases u <;> fsym <;> exact hd

/-! ## Cleanup paths -/

theorem cleanup_owned (p o e : Ptr) (u : Except ErrName (BitVec 8)) (c k : BitVec 32)
    (hdom : admitted u) (hc : c.toNat + 1 < 2 ^ 32) (hk : k.toNat + 1 < 2 ^ 32) :
    FTotalTriple (up (pts p 2 u) ⋆ (up (pts o 4 c) ⋆ up (pts e 4 k))) (TryPointers.cleanup p o e)
      (fun r => ⟪r = u⟫ ⋆
        (up (pts p 2 u) ⋆ (up (pts o 4 (c + 1)) ⋆
          up (pts e 4 (match u with | .ok _ => k | .error _ => k + 1))))) := by
  have hd := admitted_all hdom
  unfold TryPointers.cleanup; cases u <;> fsym <;> exact hd

/-- Aliased cleanup targets: one counter is passed for both `ordinary` and `on_error`.
Error increments it twice (errdefer, then defer), success once. -/
theorem cleanup_shared_owned (p c : Ptr) (u : Except ErrName (BitVec 8)) (k : BitVec 32)
    (hdom : admitted u) (hk : k.toNat + 2 < 2 ^ 32) :
    FTotalTriple (up (pts p 2 u) ⋆ up (pts c 4 k)) (TryPointers.cleanup p c c)
      (fun r => ⟪r = u⟫ ⋆
        (up (pts p 2 u) ⋆ up (pts c 4 (match u with | .ok _ => k + 1 | .error _ => k + 1 + 1)))) := by
  have hd := admitted_all hdom
  unfold TryPointers.cleanup; cases u <;> fsym <;> exact hd

/-- The cold error body runs its `errdefer`; success returns the payload address untouched. -/
theorem coldPayload_owned (p e : Ptr) (u : Except ErrName (BitVec 8)) (k : BitVec 32)
    (hdom : admitted u) (hk : k.toNat + 1 < 2 ^ 32) :
    FTotalTriple (up (pts p 2 u) ⋆ up (pts e 4 k)) (TryPointers.coldPayload p e)
      (fun r => ⟪r = tryView (BitVec 8) p u⟫ ⋆
        (up (pts p 2 u) ⋆ up (pts e 4 (match u with | .ok _ => k | .error _ => k + 1)))) := by
  have hd := admitted_all hdom
  unfold TryPointers.coldPayload; cases u <;> fsym <;> exact hd

end TryPointersAliasProofs
