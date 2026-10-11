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
* `variants.codeOf`: a return type that is not an integer, bool, plain pointer or void
* `variants.isRound`: a parameter that is not an integer, bool, plain pointer or slice
* `variants.isUrgent`: a parameter that is not an integer, bool, plain pointer or slice
* `variants.lightOf`: a return type that is not an integer, bool, plain pointer or void
* `variants.next`: a parameter that is not an integer, bool, plain pointer or slice
* `variants.prioValue`: a parameter that is not an integer, bool, plain pointer or slice
* `variants.radius`: a parameter that is not an integer, bool, plain pointer or slice
* `variants.scale`: a parameter that is not an integer, bool, plain pointer or slice
* `variants.severity`: a parameter that is not an integer, bool, plain pointer or slice
* `variants.totalArea`: a slice parameter of a function without memory (an `Array`; docs/air-semantics.md §Next fragments)
-/

end Variants.AirCert
