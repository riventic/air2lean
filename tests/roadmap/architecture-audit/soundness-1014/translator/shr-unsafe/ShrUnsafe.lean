import Gen
/-! S3b: an `@shrExact` that shifts out a set bit is modelled as the safety panic `.overflow`, with
or without Sema's `shrOverflow` check after the op (`shr.zig`, real 0.16.0 export). Natively neither
form panics (`native.zig`, stock ReleaseSafe: both return `3` with 0.16.0, `1` with 0.17.0): the
op is LLVM `lshr exact`, poison on an inexact shift, and the check after it is deleted.
Vulnerable while either form is `.overflow`. Fixed: this no longer holds (`Fixed.lean`). -/
open Shr

theorem shrExact_panics :
    shrUnsafe 3#32 1#5 = throw .overflow ∨ shrSafe 3#32 1#5 = throw .overflow := by
  first | exact .inl rfl | exact .inr rfl
