import ZigLean.VC.Rules
import ZigLean.Witness

/-!
# Non-vacuity witnesses: verification-condition programs

Concrete programs for the lemmas of `ZigLean/VC/Result.lean` (`docs/claim-strength.md`). Memory
VCs have no program of their own: they are the walk of `fsym` over the rule library.
-/

namespace Zig.Witness

open VC

nonvacuity_witness ResultProgram.eval.eq_1 := ⟨Unit, (), trivial⟩

end Zig.Witness
