-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Options.Gen

set_option linter.unusedSimpArgs false

namespace Options.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: (none)

Outside the certificate fragment:

* `options.find`: a function with a slice parameter that reads memory other than through its items (`Sem.roBody`)
* `options.findOr`: a function with a slice parameter that reads memory other than through its items (`Sem.roBody`)
* `options.firstIndexPlusOne`: a function with a slice parameter that reads memory other than through its items (`Sem.roBody`)
-/

end Options.AirCert
