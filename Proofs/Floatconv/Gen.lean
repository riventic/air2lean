import ZigLean


namespace Floatconv

structure bits32Locals where
  deriving Inhabited

inductive bits32Exit where
  | ret (v : BitVec 32)

def bits32 (p0 : Zig.F32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i2 ← Zig.Float.toBits? p0
    pure (.ret i2)) : Zig.M bits32Locals bits32Exit).run' (default : bits32Locals)
  match e with
  | .ret v => pure v

structure f16ToF128Locals where
  deriving Inhabited

inductive f16ToF128Exit where
  | ret (v : Zig.F128)

def f16ToF128 (p0 : Zig.F16) : Zig.Result (Zig.F128) := do
  let e ← ((do
    let i2 ← pure (Zig.Float.conv .f128 p0)
    pure (.ret i2)) : Zig.M f16ToF128Locals f16ToF128Exit).run' (default : f16ToF128Locals)
  match e with
  | .ret v => pure v

structure f64ToF16Locals where
  deriving Inhabited

inductive f64ToF16Exit where
  | ret (v : Zig.F16)

def f64ToF16 (p0 : Zig.F64) : Zig.Result (Zig.F16) := do
  let e ← ((do
    let i2 ← pure (Zig.Float.conv .f16 p0)
    pure (.ret i2)) : Zig.M f64ToF16Locals f64ToF16Exit).run' (default : f64ToF16Locals)
  match e with
  | .ret v => pure v

structure f80ToF64Locals where
  deriving Inhabited

inductive f80ToF64Exit where
  | ret (v : Zig.F64)

def f80ToF64 (p0 : Zig.F80) : Zig.Result (Zig.F64) := do
  let e ← ((do
    let i2 ← pure (Zig.Float.conv .f64 p0)
    pure (.ret i2)) : Zig.M f80ToF64Locals f80ToF64Exit).run' (default : f80ToF64Locals)
  match e with
  | .ret v => pure v

structure fromI64Locals where
  deriving Inhabited

inductive fromI64Exit where
  | ret (v : Zig.F32)

def fromI64 (p0 : BitVec 64) : Zig.Result (Zig.F32) := do
  let e ← ((do
    let i2 ← pure (Zig.Float.ofInt .f32 true p0)
    pure (.ret i2)) : Zig.M fromI64Locals fromI64Exit).run' (default : fromI64Locals)
  match e with
  | .ret v => pure v

structure fromU128Locals where
  deriving Inhabited

inductive fromU128Exit where
  | ret (v : Zig.F64)

def fromU128 (p0 : BitVec 128) : Zig.Result (Zig.F64) := do
  let e ← ((do
    let i2 ← pure (Zig.Float.ofInt .f64 false p0)
    pure (.ret i2)) : Zig.M fromU128Locals fromU128Exit).run' (default : fromU128Locals)
  match e with
  | .ret v => pure v

structure ofBits64Locals where
  deriving Inhabited

inductive ofBits64Exit where
  | ret (v : Zig.F64)

def ofBits64 (p0 : BitVec 64) : Zig.Result (Zig.F64) := do
  let e ← ((do
    let i2 ← pure ((Zig.Float.ofBits p0) : Zig.F64)
    pure (.ret i2)) : Zig.M ofBits64Locals ofBits64Exit).run' (default : ofBits64Locals)
  match e with
  | .ret v => pure v

structure toByteLocals where
  deriving Inhabited

inductive toByteExit where
  | ret (v : BitVec 8)

def toByte (p0 : Zig.F32) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i2 ← Zig.Float.toInt false 8 true p0
    pure (.ret i2)) : Zig.M toByteLocals toByteExit).run' (default : toByteLocals)
  match e with
  | .ret v => pure v

structure toI32Locals where
  deriving Inhabited

inductive toI32Exit where
  | ret (v : BitVec 32)

def toI32 (p0 : Zig.F64) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i2 ← Zig.Float.toInt true 32 true p0
    pure (.ret i2)) : Zig.M toI32Locals toI32Exit).run' (default : toI32Locals)
  match e with
  | .ret v => pure v

structure toU64Locals where
  deriving Inhabited

inductive toU64Exit where
  | ret (v : BitVec 64)

def toU64 (p0 : Zig.F32) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← Zig.Float.toInt false 64 true p0
    pure (.ret i2)) : Zig.M toU64Locals toU64Exit).run' (default : toU64Locals)
  match e with
  | .ret v => pure v

end Floatconv