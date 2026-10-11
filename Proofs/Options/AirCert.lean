-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Options.Gen

set_option linter.unusedSimpArgs false

namespace Options.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: (none)

Outside the certificate fragment:

* `options.find`: a slice parameter of a function without memory (an `Array`; docs/air-semantics.md §Next fragments)
* `options.findOr`: a slice parameter of a function without memory (an `Array`; docs/air-semantics.md §Next fragments)
* `options.firstIndexPlusOne`: a slice parameter of a function without memory (an `Array`; docs/air-semantics.md §Next fragments)
-/

end Options.AirCert
