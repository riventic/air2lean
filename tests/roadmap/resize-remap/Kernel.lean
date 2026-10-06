import ZigLean.Sep.Remap
open Zig

-- The ownership helper does not manufacture definedness in an extended buffer.
example : remapBytes #[.int 3, .undef, .int 7] 5 =
    #[.int 3, .undef, .int 7, .undef, .undef] := rfl
example : remapBytes #[.int 3, .undef, .int 7] 2 = #[.int 3, .undef] := rfl
