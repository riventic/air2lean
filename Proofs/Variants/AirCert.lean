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
is over the canonical AIR, so they are trusted (docs/air-semantics.md §Canonicalization):

* `variants.advance` trusted-Canon: renumber
* `variants.area` trusted-Canon: renumber
* `variants.codeOf` trusted-Canon: renumber
* `variants.isRound` trusted-Canon: renumber
* `variants.isUrgent` trusted-Canon: renumber
* `variants.lightOf` trusted-Canon: renumber
* `variants.next` trusted-Canon: renumber
* `variants.prioValue` trusted-Canon: renumber
* `variants.radius` trusted-Canon: renumber
* `variants.scale` trusted-Canon: renumber
* `variants.severity` trusted-Canon: renumber
* `variants.totalArea` trusted-Canon: renumber
-/

end Variants.AirCert
