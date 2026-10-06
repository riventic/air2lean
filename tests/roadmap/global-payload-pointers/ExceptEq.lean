import ZigLean.Basic

-- Kernel-reduced controls exercise both equal/unequal payload branches and tags.
example : (Except.error "Bad" : Except String (BitVec 8)) = .error "Bad" := by decide
example : (Except.error "Bad" : Except String (BitVec 8)) ≠ .error "Other" := by decide
example : (Except.ok (19 : BitVec 8) : Except String (BitVec 8)) = .ok 19 := by decide
example : (Except.ok (19 : BitVec 8) : Except String (BitVec 8)) ≠ .ok 20 := by decide
example : (Except.error "Bad" : Except String (BitVec 8)) ≠ .ok 19 := by decide
example : (Except.ok (19 : BitVec 8) : Except String (BitVec 8)) ≠ .error "Bad" := by decide

private structure GeneratedErrorFields where
  optional : Option (BitVec 8)
  small : Except Zig.ErrName (BitVec 8)
  wide : Except Zig.ErrName (BitVec 64)
  equal : Except Zig.ErrName (BitVec 16)
  deriving DecidableEq

private def sample : GeneratedErrorFields :=
  {optional := some 7, small := .ok 19, wide := .ok 41, equal := .ok 23}
example : sample = sample := by decide
example : sample ≠ {sample with small := .error "Bad"} := by decide
example : sample ≠ {sample with wide := .ok 42} := by decide
