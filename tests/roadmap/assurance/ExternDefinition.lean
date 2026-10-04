namespace AssuranceFixture

@[extern "air2lean_assurance_fixture"]
def externalDefinition (x : Nat) : Nat := x

@[extern "air2lean_assurance_unused_fixture"]
def unusedExternalDefinition (x : Nat) : Nat := x

theorem external_spec (x : Nat) : externalDefinition x = x := rfl

end AssuranceFixture
