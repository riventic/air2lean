namespace AssuranceFixture

def runtimeImplementation : Bool := false

@[implemented_by runtimeImplementation]
def logicalDefinition : Bool := true

theorem logicalWrapper : logicalDefinition = true := rfl

end AssuranceFixture
