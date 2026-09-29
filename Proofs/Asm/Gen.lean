import ZigLean


namespace Asm

opaque airAsm_3500345798 (i0 : BitVec 32) : BitVec 32

opaque airAsm_2482283570 (i0 : BitVec 32) (i1 : BitVec 32) : BitVec 32 × BitVec 32

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

structure divmodLocals where
  rem : BitVec 32
  deriving Inhabited

inductive divmodExit where
  | ret (v : BitVec 64)

def divmod (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with rem := (0#32) })
    let a4 := airAsm_2482283570 p0 p1
    let i4 ← pure a4.1
    modify (fun s => { s with rem := a4.2 })
    let i5 ← pure ((← get).rem)
    let i6 ← Zig.intCast false false 64 i5
    let i7 ← pure (Zig.shl i6 (32 : BitVec 6))
    let i8 ← Zig.intCast false false 64 i4
    let i9 ← pure (i7 ||| i8)
    pure (.ret i9)) : Zig.M divmodLocals divmodExit).run' (default : divmodLocals)
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