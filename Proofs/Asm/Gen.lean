import ZigLean


namespace Asm

def airIsa_3500345798_block : Zig.Isa.X86.Block where
  instrs := [.un .bswap .w32 (.vreg 0)]
  inputs := [(.vreg 0, .w32)]
  outputs := [(.vreg 0, .w32)]
  early := []
  clobbers := []

theorem airIsa_3500345798_wf : airIsa_3500345798_block.check = none := by decide

def airIsa_3500345798 (i0 : BitVec 32) : BitVec 32 :=
  (airIsa_3500345798_block.out [i0.setWidth 64] 0).setWidth 32

attribute [zig_unfold] airIsa_3500345798_block airIsa_3500345798

def airIsa_3653072158_block : Zig.Isa.X86.Block where
  instrs := [.bin .xor .w32 (.loc (.reg 2)) (.reg 2), .div .w32 (.vreg 3)]
  inputs := [(.reg 0, .w32), (.vreg 3, .w32)]
  outputs := [(.reg 0, .w32), (.reg 2, .w32)]
  early := [.reg 2]
  clobbers := []

theorem airIsa_3653072158_wf : airIsa_3653072158_block.check = none := by decide

def airIsa_3653072158 (i0 : BitVec 32) (i1 : BitVec 32) : BitVec 32 × BitVec 32 :=
  ((airIsa_3653072158_block.out [i0.setWidth 64, i1.setWidth 64] 0).setWidth 32, (airIsa_3653072158_block.out [i0.setWidth 64, i1.setWidth 64] 1).setWidth 32)

def airIsa_3653072158_fault (i0 : BitVec 32) (i1 : BitVec 32) : Option Zig.Isa.X86.Fault :=
  airIsa_3653072158_block.fault [i0.setWidth 64, i1.setWidth 64]

attribute [zig_unfold] airIsa_3653072158_block airIsa_3653072158 airIsa_3653072158_fault

def airIsa_3884223243_block : Zig.Isa.X86.Block where
  instrs := [.cnt .lzcnt .w64 (.vreg 1) (.vreg 0)]
  inputs := [(.vreg 1, .w64)]
  outputs := [(.vreg 0, .w64)]
  early := []
  clobbers := []

theorem airIsa_3884223243_wf : airIsa_3884223243_block.check = none := by decide

def airIsa_3884223243 (i0 : BitVec 64) : BitVec 64 :=
  (airIsa_3884223243_block.out [i0.setWidth 64] 0).setWidth 64

attribute [zig_unfold] airIsa_3884223243_block airIsa_3884223243

def airIsa_4040357768_block : Zig.Isa.X86.Block where
  instrs := [.cnt .popcnt .w64 (.vreg 1) (.vreg 0)]
  inputs := [(.vreg 1, .w64)]
  outputs := [(.vreg 0, .w64)]
  early := []
  clobbers := []

theorem airIsa_4040357768_wf : airIsa_4040357768_block.check = none := by decide

def airIsa_4040357768 (i0 : BitVec 64) : BitVec 64 :=
  (airIsa_4040357768_block.out [i0.setWidth 64] 0).setWidth 64

attribute [zig_unfold] airIsa_4040357768_block airIsa_4040357768

structure bswap32Locals where
  deriving Inhabited

inductive bswap32Exit where
  | ret (v : BitVec 32)

def bswap32 (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (airIsa_3500345798 p0)
    pure (.ret i1)) : Zig.M bswap32Locals bswap32Exit).run' (default : bswap32Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] bswap32

structure divmodLocals where
  rem : BitVec 32
  deriving Inhabited

inductive divmodExit where
  | ret (v : BitVec 64)

def divmod (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with rem := (0#32) })
    let a4 ← Zig.Asm.isaFault (airIsa_3653072158_fault p0 p1) (airIsa_3653072158 p0 p1)
    let i4 ← pure a4.1
    modify (fun s => { s with rem := a4.2 })
    let i5 ← pure ((← get).rem)
    let i6 ← Zig.intCast false false 64 i5 (safe := false)
    let i7 ← pure (Zig.shl i6 (32 : BitVec 6))
    let i8 ← Zig.intCast false false 64 i4 (safe := false)
    let i9 ← pure (i7 ||| i8)
    pure (.ret i9)) : Zig.M divmodLocals divmodExit).run' (default : divmodLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] divmod

structure lzcnt64Locals where
  deriving Inhabited

inductive lzcnt64Exit where
  | ret (v : BitVec 64)

def lzcnt64 (p0 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← pure (airIsa_3884223243 p0)
    pure (.ret i1)) : Zig.M lzcnt64Locals lzcnt64Exit).run' (default : lzcnt64Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] lzcnt64

structure popcnt64Locals where
  deriving Inhabited

inductive popcnt64Exit where
  | ret (v : BitVec 64)

def popcnt64 (p0 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← pure (airIsa_4040357768 p0)
    pure (.ret i1)) : Zig.M popcnt64Locals popcnt64Exit).run' (default : popcnt64Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] popcnt64

end Asm