-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Atomics.Gen

set_option linter.unusedSimpArgs false

namespace Atomics.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: (none)

Outside the certificate fragment:

* `atomic.Value(u32).init`: a return type that is not an integer, bool, plain pointer or void
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
-/

end Atomics.AirCert
