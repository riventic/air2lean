import Gen
/-! S3 fixed: the unchecked forms of the ops in `up.zig` (runtime safety off, no check in or before
the op) give `.illegal`, not a safety-panic constructor (`Zig.Error.ifSafe`,
`docs/illegal-behavior.md` rows 6-8, 18, 21). Natively (`native.zig`) none of them panics. -/
open Up

theorem enumUnsafe_illegal : enumUnsafe 3#2 = throw .illegal := rfl
theorem unionUnsafe_illegal : unionUnsafe (.b 7#32) = throw .illegal := rfl
theorem bareUnsafe_illegal : bareUnsafe (.b 9#32) = throw .illegal := rfl
theorem unionLocal_illegal : unionLocal 11#32 = throw .illegal := rfl
theorem bareLocal_illegal : bareLocal 11#32 = throw .illegal := rfl
theorem addUnsafe_illegal : addUnsafe 0xFFFFFFFF#32 7#32 = throw .illegal := rfl
theorem divUnsafe_illegal : divUnsafe 5#32 0#32 = throw .illegal := rfl
theorem intCastUnsafe_illegal : intCastUnsafe 300#32 = throw .illegal := rfl

-- In range, the same functions return the value.
theorem enumUnsafe_ok : enumUnsafe 2#2 = pure 2#2 := rfl
theorem addUnsafe_ok : addUnsafe 1#32 2#32 = pure 3#32 := rfl
theorem intCastUnsafe_ok : intCastUnsafe 200#32 = pure 200#8 := rfl
