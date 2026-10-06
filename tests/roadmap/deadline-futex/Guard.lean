import Air2Lean.TimedCheck

/-! Regression for the selected opcode boundary. Actual canonicalization replaces
observe's immutable copy and pointer/load chain by this ordinary value projection.
Operand shape/index/result checks remain in preflight; this guard alone is not a
type checker. Unsupported control flow, indirect calls and atomics stay rejected. -/
open Air2Lean

example (value : Val) (field : Nat) :
    Timed.admitted (.structFieldVal value field) = true := rfl

example : Timed.admitted (.loop #[]) = false := rfl
example : Timed.admitted (.loopSwitchBr .void #[] #[]) = false := rfl
example : Timed.admitted (.«repeat» 0) = false := rfl
example : Timed.admitted (.br 0 .void) = false := rfl
example : Timed.admitted (.condBr (.bool true) #[] #[]) = false := rfl
example : Timed.admitted (.tryPtr (.inst 0) #[]) = false := rfl
example : Timed.admitted (.call (.inst 0) #[]) = false := rfl
example : Timed.admitted (.call (.func "unselected" true none) #[]) = false := rfl
example : Timed.admitted (.atomicLoad (.inst 0) .monotonic) = false := rfl
