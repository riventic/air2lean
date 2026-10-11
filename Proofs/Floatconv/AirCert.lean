-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Floatconv.Gen

set_option linter.unusedSimpArgs false

namespace Floatconv.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: (none)

Outside the certificate fragment:

* `floatconv.bits32`: a parameter that is not an integer, bool, plain pointer or slice
* `floatconv.f16ToF128`: a parameter that is not an integer, bool, plain pointer or slice
* `floatconv.f64ToF16`: a parameter that is not an integer, bool, plain pointer or slice
* `floatconv.f80ToF64`: a parameter that is not an integer, bool, plain pointer or slice
* `floatconv.fromI64`: a return type that is not an integer, bool, plain pointer or void
* `floatconv.fromU128`: a return type that is not an integer, bool, plain pointer or void
* `floatconv.ofBits64`: a return type that is not an integer, bool, plain pointer or void
* `floatconv.toByte`: a parameter that is not an integer, bool, plain pointer or slice
* `floatconv.toI32`: a parameter that is not an integer, bool, plain pointer or slice
* `floatconv.toU64`: a parameter that is not an integer, bool, plain pointer or slice
-/

end Floatconv.AirCert
