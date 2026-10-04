import Lean

namespace AssuranceFixture

theorem compilerDependentProof : (2 : Nat) + 2 = 4 := by native_decide

end AssuranceFixture
