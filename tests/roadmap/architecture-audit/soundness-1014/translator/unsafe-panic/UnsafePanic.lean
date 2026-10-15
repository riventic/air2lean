import Gen
/-! Unsafe-AIR `@enumFromInt` and inactive union field (runtime safety off) are modelled as
`.panic`, a Sema safety-check outcome. Native ReleaseSafe (stock 0.16.0, `native.zig`) prints
`enumUnsafe(3) = 3`, `unionUnsafe(.b=7) = 7`, `bareUnsafe(.b=9) = 9`: no panic happens. -/
open Up

theorem enumUnsafe_panics : enumUnsafe 3#2 = throw .panic := rfl

theorem unionUnsafe_panics : unionUnsafe (.b 7#32) = throw .panic := rfl

theorem bareUnsafe_panics : bareUnsafe (.b 9#32) = throw .panic := rfl

theorem unionLocal_panics : unionLocal 11#32 = throw .panic := rfl
