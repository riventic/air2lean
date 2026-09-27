import ZigLean


namespace Asm

opaque airAsm_3500345798 (i0 : BitVec 32) : BitVec 32

opaque airAsm_3884223243 (i0 : BitVec 64) : BitVec 64

opaque airAsm_4040357768 (i0 : BitVec 64) : BitVec 64

structure bswap32Locals where
  deriving Inhabited

inductive bswap32Exit where
  | ret (v : BitVec 32)

def bswap32 (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (airAsm_3500345798 p0)
    pure (.ret i1)) : Zig.M bswap32Locals bswap32Exit).run' (default : bswap32Locals)
  match e with
  | .ret v => pure v

structure lzcnt64Locals where
  deriving Inhabited

inductive lzcnt64Exit where
  | ret (v : BitVec 64)

def lzcnt64 (p0 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← pure (airAsm_3884223243 p0)
    pure (.ret i1)) : Zig.M lzcnt64Locals lzcnt64Exit).run' (default : lzcnt64Locals)
  match e with
  | .ret v => pure v

structure popcnt64Locals where
  deriving Inhabited

inductive popcnt64Exit where
  | ret (v : BitVec 64)

def popcnt64 (p0 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← pure (airAsm_4040357768 p0)
    pure (.ret i1)) : Zig.M popcnt64Locals popcnt64Exit).run' (default : popcnt64Locals)
  match e with
  | .ret v => pure v

end Asm