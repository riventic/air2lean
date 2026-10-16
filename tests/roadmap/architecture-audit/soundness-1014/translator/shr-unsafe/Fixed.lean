import Gen
/-! S3b fixed: an inexact `@shrExact` is `.illegal` with and without Sema's check after the op
(`docs/illegal-behavior.md` row 13); an exact shift returns the value in both forms. -/
open Shr

theorem shrUnsafe_illegal : shrUnsafe 3#32 1#5 = throw .illegal := rfl
theorem shrSafe_illegal : shrSafe 3#32 1#5 = throw .illegal := rfl
theorem shrUnsafe_ok : shrUnsafe 4#32 1#5 = pure 2#32 := rfl
theorem shrSafe_ok : shrSafe 4#32 1#5 = pure 2#32 := rfl
