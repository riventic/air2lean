-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Errors.Gen

set_option linter.unusedSimpArgs false

namespace Errors.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: (none)

Outside the certificate fragment:

* `errors.digitOrZero`: inst 3: an instruction outside the fragment
* `errors.parseDigit`: a return type that is not an integer, bool, plain pointer or void
* `errors.sumDigits`: a function with a slice parameter that reads memory other than through its items (`Sem.roBody`)
-/

end Errors.AirCert
