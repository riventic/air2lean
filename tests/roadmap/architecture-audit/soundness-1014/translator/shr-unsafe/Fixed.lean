import Gen
/-! S3b fixed: the unchecked `@shrExact` is `.illegal`; the checked one (Sema's `shrOverflow`
check after the op, `Canon.checkedShrExact`) keeps its safety panic; an exact shift returns the
value either way. -/
open Shr

theorem shrUnsafe_illegal : shrUnsafe 3#32 1#5 = throw .illegal := rfl
theorem shrSafe_panics : shrSafe 3#32 1#5 = throw .overflow := rfl
theorem shrUnsafe_ok : shrUnsafe 4#32 1#5 = pure 2#32 := rfl
theorem shrSafe_ok : shrSafe 4#32 1#5 = pure 2#32 := rfl
