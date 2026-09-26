import ZigLean.Float.Format
import ZigLean.Float.Value
import ZigLean.Float.Round
import ZigLean.Float.Ops
import ZigLean.Float.CompilerRt

/-!
# Float model

The executable IEEE-754 model: formats (`Format.lean`), values and decoding (`Value.lean`),
rounding (`Round.lean`), operations (`Ops.lean`), the `compiler-rt`-semantics opt-in
(`CompilerRt.lean`; `docs/floats.md`). Not re-exported here:
* `Float/Libm.lean` (transcendentals): extern-backed and uninterpreted. Import it directly.
* The lemma library (`Float/Lemmas.lean`, `Float/RoundTrip.lean`): proofs import
  `ZigLean.Float.RoundTrip`. Generated code imports only the model, so a lemma about the
  rounding internals cannot break the build of the differential test under
  `scripts/mutate.sh` (d).
-/
