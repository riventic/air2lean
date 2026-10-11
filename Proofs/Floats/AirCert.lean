-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Floats.Gen

set_option linter.unusedSimpArgs false

namespace Floats.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: (none)

Outside the certificate fragment:

* `floats.celsius`: a parameter that is not an integer, bool, plain pointer or slice
* `floats.clamp`: a parameter that is not an integer, bool, plain pointer or slice
* `floats.dot`: a slice parameter of a function without memory (an `Array`; docs/air-semantics.md §Next fragments)
* `floats.fitness`: a slice parameter of a function without memory (an `Array`; docs/air-semantics.md §Next fragments)
* `floats.hypot2`: a parameter that is not an integer, bool, plain pointer or slice
* `floats.isNan`: a parameter that is not an integer, bool, plain pointer or slice
* `floats.lerp`: a parameter that is not an integer, bool, plain pointer or slice
-/

end Floats.AirCert
