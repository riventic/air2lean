import Gen
/-! S3b: `@shrExact` with runtime safety off (`shr_exact`, no Sema check after it) is modelled as
the safety panic `.overflow`, although a shifted-out bit is unchecked illegal behaviour that no
check catches (`shr.zig`, real 0.16.0 export). Fixed: this no longer holds (`Fixed.lean`). -/
open Shr

theorem shrUnsafe_panics : shrUnsafe 3#32 1#5 = throw .overflow := rfl
