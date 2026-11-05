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
is over the canonical AIR, so they are trusted (docs/air-semantics.md §Canonicalization):

* `atomic.Value(u32).init` trusted-Canon: renumber
* `atomics.mpRelAcq` trusted-Canon: forwardReadOnlyCopies, renumber
* `atomics.mpRelaxed` trusted-Canon: forwardReadOnlyCopies, renumber
* `atomics.mpWriter` trusted-Canon: forwardReadOnlyCopies, renumber
* `atomics.mpWriterRelaxed` trusted-Canon: forwardReadOnlyCopies, renumber
* `atomics.push` trusted-Canon: forwardReadOnlyCopies, renumber
* `atomics.sb` trusted-Canon: forwardReadOnlyCopies, renumber
* `atomics.sbRelaxed` trusted-Canon: forwardReadOnlyCopies, renumber
* `atomics.stackPush` trusted-Canon: forwardReadOnlyCopies, itemReads, renumber
* `atomics.twoPlusTwoW` trusted-Canon: forwardReadOnlyCopies, renumber
* `atomics.ww` trusted-Canon: forwardReadOnlyCopies, renumber
-/

end Atomics.AirCert
