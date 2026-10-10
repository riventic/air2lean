-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Errors.Gen

namespace Errors.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: (none)

Outside the certificate fragment:

* `errors.digitOrZero`: inst 3: an instruction outside the fragment
* `errors.parseDigit`: a return type that is not an integer, bool, plain pointer or void
* `errors.sumDigits`: a parameter that is not an integer, bool or plain pointer
-/

end Errors.AirCert
