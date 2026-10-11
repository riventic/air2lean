import ZigLean.External

/-! A trusted-base model of libc's `abs` (`extern "c" fn abs(c_int) c_int`), bound at that
linker identity by `registry.json` under premise EXT-03. `abs(INT_MIN)` is undefined in C: the
model throws `.illegal` there, and the contract excludes it. -/
namespace ExternModel

def intMin : BitVec 32 := BitVec.intMin 32

def abs (x : BitVec 32) : Zig.MemM (BitVec 32) :=
  if x == intMin then throw .illegal else pure (if x.slt 0 then -x else x)

def absContract : Zig.External.Contract (BitVec 32) (BitVec 32) where
  pre := fun x _ => x ≠ intMin
  post := fun x before result after => result = (if x.slt 0 then -x else x) ∧ after = before
  frame := fun _ before after => after = before
  access := fun _ _ _ => False
  failure := fun _ _ _ => False
  divergence := fun _ _ => False

end ExternModel
