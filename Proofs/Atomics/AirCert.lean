-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Atomics.Gen

set_option linter.unusedSimpArgs false

namespace Atomics.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: (none)

Outside the certificate fragment:

* `atomic.Value(u32).init`: a return type that is not an integer, bool, plain pointer or void, or an optional or error union of one
* `atomics.mpRelAcq`: a concurrent function (`Zig.ConcM`)
* `atomics.mpRelaxed`: a concurrent function (`Zig.ConcM`)
* `atomics.mpWriter`: a concurrent function (`Zig.ConcM`)
* `atomics.mpWriterRelaxed`: a concurrent function (`Zig.ConcM`)
* `atomics.push`: a concurrent function (`Zig.ConcM`)
* `atomics.sb`: a concurrent function (`Zig.ConcM`)
* `atomics.sbRelaxed`: a concurrent function (`Zig.ConcM`)
* `atomics.stackPush`: a concurrent function (`Zig.ConcM`)
* `atomics.twoPlusTwoW`: a concurrent function (`Zig.ConcM`)
* `atomics.ww`: a concurrent function (`Zig.ConcM`)

The Canon rewrites that fired on each function (`Raw.canonicalizeTraced`); a certificate
is over the canonical AIR, so they are trusted (docs/air-semantics.md §Canonicalization).
`renumber` is not listed where its native binding to `Renumber.execFunc_rename` holds:

* `atomic.Value(u32).init` trusted-Canon: none
* `atomics.mpRelAcq` trusted-Canon: forwardReadOnlyCopies
* `atomics.mpRelaxed` trusted-Canon: forwardReadOnlyCopies
* `atomics.mpWriter` trusted-Canon: forwardReadOnlyCopies
* `atomics.mpWriterRelaxed` trusted-Canon: forwardReadOnlyCopies
* `atomics.push` trusted-Canon: forwardReadOnlyCopies
* `atomics.sb` trusted-Canon: forwardReadOnlyCopies
* `atomics.sbRelaxed` trusted-Canon: forwardReadOnlyCopies
* `atomics.stackPush` trusted-Canon: forwardReadOnlyCopies, itemReads
* `atomics.twoPlusTwoW` trusted-Canon: forwardReadOnlyCopies
* `atomics.ww` trusted-Canon: forwardReadOnlyCopies
-/

end Atomics.AirCert
