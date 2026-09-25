import ZigLean.Float.Format
import ZigLean.Float.Value
import ZigLean.Float.Round
import ZigLean.Float.Ops

/-!
# Float model

The executable IEEE-754 model: formats (`Format.lean`), values and decoding (`Value.lean`),
rounding (`Round.lean`) and operations (`Ops.lean`). `Float/Libm.lean` (transcendentals) is
deliberately not re-exported here — it is extern-backed and uninterpreted, so a file that only
needs the core model (e.g. `Proofs`) should not have to pull it in. Import `ZigLean.Float.Libm`
directly for `Float.libm`.
-/
