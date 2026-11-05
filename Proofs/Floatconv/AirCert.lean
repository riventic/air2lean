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
* `floatconv.fromI64`: a return type that is not an integer, bool, plain pointer or void, or an optional or error union of one
* `floatconv.fromU128`: a return type that is not an integer, bool, plain pointer or void, or an optional or error union of one
* `floatconv.ofBits64`: a return type that is not an integer, bool, plain pointer or void, or an optional or error union of one
* `floatconv.toByte`: a parameter that is not an integer, bool, plain pointer or slice
* `floatconv.toI32`: a parameter that is not an integer, bool, plain pointer or slice
* `floatconv.toU64`: a parameter that is not an integer, bool, plain pointer or slice

The Canon rewrites that fired on each function (`Raw.canonicalizeTraced`); a certificate
is over the canonical AIR, so they are trusted (docs/air-semantics.md §Canonicalization).
`renumber` is not listed where its native binding to `Renumber.execFunc_rename` holds:

* `floatconv.bits32` trusted-Canon: none
* `floatconv.f16ToF128` trusted-Canon: none
* `floatconv.f64ToF16` trusted-Canon: none
* `floatconv.f80ToF64` trusted-Canon: none
* `floatconv.fromI64` trusted-Canon: none
* `floatconv.fromU128` trusted-Canon: none
* `floatconv.ofBits64` trusted-Canon: none
* `floatconv.toByte` trusted-Canon: none
* `floatconv.toI32` trusted-Canon: none
* `floatconv.toU64` trusted-Canon: none
-/

end Floatconv.AirCert
