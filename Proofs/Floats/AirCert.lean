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
* `floats.dot`: a slice parameter whose items are not integers or `bool`
* `floats.fitness`: a parameter that is not an integer, bool, plain pointer or slice
* `floats.hypot2`: a parameter that is not an integer, bool, plain pointer or slice
* `floats.isNan`: a parameter that is not an integer, bool, plain pointer or slice
* `floats.lerp`: a parameter that is not an integer, bool, plain pointer or slice

The Canon rewrites that fired on each function (`Raw.canonicalizeTraced`); a certificate
is over the canonical AIR, so they are trusted (docs/air-semantics.md §Canonicalization):

* `floats.celsius` trusted-Canon: renumber
* `floats.clamp` trusted-Canon: renumber
* `floats.dot` trusted-Canon: renumber
* `floats.fitness` trusted-Canon: renumber
* `floats.hypot2` trusted-Canon: renumber
* `floats.isNan` trusted-Canon: renumber
* `floats.lerp` trusted-Canon: renumber
-/

end Floats.AirCert
