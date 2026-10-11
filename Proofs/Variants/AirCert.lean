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
-/

end Variants.AirCert
