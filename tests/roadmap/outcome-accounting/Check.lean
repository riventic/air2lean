import Outcome
open DiffOutcome

-- Source error returns are payload values, distinct from model safety errors.
example : valueKind (.error "AllocationFailed" : Except Zig.ErrName Nat) = .errorReturn := rfl
example : valueKind (some (.error "Overflow" : Except Zig.ErrName Nat)) = .errorReturn := rfl
example : valueKind (.ok (7 : Nat) : Except Zig.ErrName Nat) = .value := rfl
example : errorKind .panic = .modelPanic := rfl
example : errorKind .illegal = .illegal := rfl
example : errorKind .unspecified = .unspecified := rfl
example : errorKind .deadlock = .deadlock := rfl
-- An unsupported timer has its own kind and wire tag, apart from an unspecified result.
example : errorKind .unsupportedTimer = .unspecifiedTimer := rfl
example : Kind.tag .unspecifiedTimer = "unspecified_timer" := rfl
example : (failure .unsupportedTimer).kind = .unspecifiedTimer := rfl
example : noResult.kind = .boundedNoResult := rfl

example : Nonempty Observation := inferInstance
