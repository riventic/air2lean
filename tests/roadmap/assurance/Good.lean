namespace AssuranceFixture

-- Opacity by itself is not an axiom. The checked value has no sorry or new axiom.
opaque checkedOpaque : Nat := 7

theorem opaque_reflexive : checkedOpaque = checkedOpaque := rfl

private theorem private_checked : checkedOpaque = checkedOpaque := rfl

theorem classical_allowed (p : Prop) : p ∨ ¬p := Classical.em p

end AssuranceFixture
