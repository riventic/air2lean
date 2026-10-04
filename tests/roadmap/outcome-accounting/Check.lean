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
example : noResult.kind = .boundedNoResult := rfl
