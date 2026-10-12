import ZigLean.Mem.Alloc
import ZigLean.Mem.Lemmas

/-!
# Facts about `rawAlloc` (proof-only)

The failure decision of an allocation attempt (`Mem.allocDenied`) and `rawAlloc` unfolded into
its three outcomes (`rawAlloc_eq`). Both logics use them: the legacy rules (`ZigLean/Sep/Alloc.lean`)
and the full-state rules (`ZigLean/Sep/Full/Block.lean`). Proof-only: this module imports
`ZigLean.Mem.Lemmas`, so it stays out of the runtime umbrella.
-/

namespace Zig

/-- Every failure decision of `rawAlloc`: a fixed/legacy rule or the general oracle/budget. -/
def Mem.allocDenied (m : Mem) (n : Nat) : Prop :=
  (m.failAt = some m.allocs ∨ m.allocPolicy.maxBytes < n ∨ m.allocs ∈ m.allocPolicy.failures) ∨
    m.oracleDenies n = true

/-- `rawAlloc` counts the attempt, then fails without changing the heap (by the failure
decision, or for want of room in the address space: `Mem.roomFor`) or allocates a block. -/
theorem rawAlloc_eq (m : Mem) (n align : Nat) [Decidable (m.allocDenied n)] :
    (rawAlloc n align).run m =
      if m.allocDenied n then pure (none, { m with allocs := m.allocs + 1 })
      else if m.roomFor n align then (some <$> alloc .heap n align).run { m with allocs := m.allocs + 1 }
      else pure (none, { m with allocs := m.allocs + 1 }) := by
  by_cases hc : m.failAt = some m.allocs ∨ m.allocPolicy.maxBytes < n ∨ m.allocs ∈ m.allocPolicy.failures
  · simp only [show m.allocDenied n from .inl hc, ↓reduceIte]
    simp [rawAlloc, hc, zig_unfold, set, StateT.set, MonadStateOf.set]
  by_cases ho : m.oracleDenies n = true
  · simp only [show m.allocDenied n from .inr ho, ↓reduceIte]
    simp only [not_or] at hc
    simp [rawAlloc, hc, ho, zig_unfold, set, StateT.set, MonadStateOf.set]
  · simp only [show ¬ m.allocDenied n from fun h => h.elim hc ho, ↓reduceIte]
    simp only [not_or] at hc
    cases hr : m.roomFor n align <;>
      simp [rawAlloc, hc, ho, hr, zig_unfold, set, StateT.set, MonadStateOf.set]

end Zig
