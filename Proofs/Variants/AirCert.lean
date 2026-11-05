-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Variants.Gen

set_option linter.unusedSimpArgs false

namespace Variants.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: (none)

Outside the certificate fragment:

* `variants.advance`: a parameter that is not an integer, bool, plain pointer or slice
* `variants.area`: a parameter that is not an integer, bool, plain pointer or slice
* `variants.codeOf`: a return type that is not an integer, bool, plain pointer or void, or an optional or error union of one
* `variants.isRound`: a parameter that is not an integer, bool, plain pointer or slice
* `variants.isUrgent`: a parameter that is not an integer, bool, plain pointer or slice
* `variants.lightOf`: a return type that is not an integer, bool, plain pointer or void, or an optional or error union of one
* `variants.next`: a parameter that is not an integer, bool, plain pointer or slice
* `variants.prioValue`: a parameter that is not an integer, bool, plain pointer or slice
* `variants.radius`: a parameter that is not an integer, bool, plain pointer or slice
* `variants.scale`: a parameter that is not an integer, bool, plain pointer or slice
* `variants.severity`: a parameter that is not an integer, bool, plain pointer or slice
* `variants.totalArea`: a slice parameter whose items are not integers or `bool`

The Canon rewrites that fired on each function (`Raw.canonicalizeTraced`); a certificate
is over the canonical AIR, so they are trusted (docs/air-semantics.md §Canonicalization).
`renumber` is not listed where its native binding to `Renumber.execFunc_rename` holds:

* `variants.advance` trusted-Canon: none
* `variants.area` trusted-Canon: none
* `variants.codeOf` trusted-Canon: none
* `variants.isRound` trusted-Canon: none
* `variants.isUrgent` trusted-Canon: none
* `variants.lightOf` trusted-Canon: none
* `variants.next` trusted-Canon: none
* `variants.prioValue` trusted-Canon: none
* `variants.radius` trusted-Canon: none
* `variants.scale` trusted-Canon: none
* `variants.severity` trusted-Canon: none
* `variants.totalArea` trusted-Canon: none
-/

end Variants.AirCert
