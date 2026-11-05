-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Asm.Gen

set_option linter.unusedSimpArgs false

namespace Asm.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: (none)

Outside the certificate fragment:

* `asm.bswap32`: inst 1: an instruction outside the fragment
* `asm.divmod`: inst 3: an operand outside the fragment
* `asm.lzcnt64`: inst 1: an instruction outside the fragment
* `asm.popcnt64`: inst 1: an instruction outside the fragment

The Canon rewrites that fired on each function (`Raw.canonicalizeTraced`); a certificate
is over the canonical AIR, so they are trusted (docs/air-semantics.md §Canonicalization):

* `asm.bswap32` trusted-Canon: renumber
* `asm.divmod` trusted-Canon: renumber
* `asm.lzcnt64` trusted-Canon: renumber
* `asm.popcnt64` trusted-Canon: renumber
-/

end Asm.AirCert
