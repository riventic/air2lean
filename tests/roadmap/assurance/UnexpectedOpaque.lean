namespace AssuranceFixture

opaque unexpectedOpaque : Nat := 9

theorem opaqueWrapper : unexpectedOpaque = unexpectedOpaque := rfl

end AssuranceFixture
