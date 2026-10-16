import Gen
/-! S3b: an `@shrExact` that shifts out a set bit is modelled as the safety panic `.overflow`, with
or without Sema's check after the op (`shr.zig`, real 0.16.0 export). Natively neither form panics
(stock ReleaseSafe, `illegal-behavior/native/ReleaseSafe.txt`). The disjunction makes the case
vulnerable while either form is `.overflow`. Fixed: this no longer holds (`Fixed.lean`). -/
open Shr

theorem shrExact_panics :
    shrUnsafe 3#32 1#5 = throw .overflow ∨ shrSafe 3#32 1#5 = throw .overflow := by
  first | exact .inl rfl | exact .inr rfl
