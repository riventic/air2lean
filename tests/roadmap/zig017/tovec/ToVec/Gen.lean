import ZigLean


namespace ToVec

structure toVecBoolLocals where
  deriving Inhabited

inductive toVecBoolExit where
  | ret (v : Zig.Vec (Bool) 5)

def toVecBool (p0 : Vector (Bool) 5) : Zig.Result (Zig.Vec (Bool) 5) := do
  let e ← ((do
    let i1 ← pure (⟨p0⟩ : Zig.Vec (Bool) 5)
    pure (.ret i1)) : Zig.M toVecBoolLocals toVecBoolExit).run' (default : toVecBoolLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] toVecBool

structure toVecF128Locals where
  deriving Inhabited

inductive toVecF128Exit where
  | ret (v : Zig.Vec (Zig.F128) 2)

def toVecF128 (p0 : Vector (Zig.F128) 2) : Zig.Result (Zig.Vec (Zig.F128) 2) := do
  let e ← ((do
    let i1 ← pure (⟨p0⟩ : Zig.Vec (Zig.F128) 2)
    pure (.ret i1)) : Zig.M toVecF128Locals toVecF128Exit).run' (default : toVecF128Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] toVecF128

structure toVecF16Locals where
  deriving Inhabited

inductive toVecF16Exit where
  | ret (v : Zig.Vec (Zig.F16) 3)

def toVecF16 (p0 : Vector (Zig.F16) 3) : Zig.Result (Zig.Vec (Zig.F16) 3) := do
  let e ← ((do
    let i1 ← pure (⟨p0⟩ : Zig.Vec (Zig.F16) 3)
    pure (.ret i1)) : Zig.M toVecF16Locals toVecF16Exit).run' (default : toVecF16Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] toVecF16

structure toVecF32Locals where
  deriving Inhabited

inductive toVecF32Exit where
  | ret (v : Zig.Vec (Zig.F32) 4)

def toVecF32 (p0 : Vector (Zig.F32) 4) : Zig.Result (Zig.Vec (Zig.F32) 4) := do
  let e ← ((do
    let i1 ← pure (⟨p0⟩ : Zig.Vec (Zig.F32) 4)
    pure (.ret i1)) : Zig.M toVecF32Locals toVecF32Exit).run' (default : toVecF32Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] toVecF32

structure toVecF64Locals where
  deriving Inhabited

inductive toVecF64Exit where
  | ret (v : Zig.Vec (Zig.F64) 2)

def toVecF64 (p0 : Vector (Zig.F64) 2) : Zig.Result (Zig.Vec (Zig.F64) 2) := do
  let e ← ((do
    let i1 ← pure (⟨p0⟩ : Zig.Vec (Zig.F64) 2)
    pure (.ret i1)) : Zig.M toVecF64Locals toVecF64Exit).run' (default : toVecF64Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] toVecF64

structure toVecF80Locals where
  deriving Inhabited

inductive toVecF80Exit where
  | ret (v : Zig.Vec (Zig.F80) 2)

def toVecF80 (p0 : Vector (Zig.F80) 2) : Zig.Result (Zig.Vec (Zig.F80) 2) := do
  let e ← ((do
    let i1 ← pure (⟨p0⟩ : Zig.Vec (Zig.F80) 2)
    pure (.ret i1)) : Zig.M toVecF80Locals toVecF80Exit).run' (default : toVecF80Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] toVecF80

structure toVecI128Locals where
  deriving Inhabited

inductive toVecI128Exit where
  | ret (v : Zig.Vec (BitVec 128) 2)

def toVecI128 (p0 : Vector (BitVec 128) 2) : Zig.Result (Zig.Vec (BitVec 128) 2) := do
  let e ← ((do
    let i1 ← pure (⟨p0⟩ : Zig.Vec (BitVec 128) 2)
    pure (.ret i1)) : Zig.M toVecI128Locals toVecI128Exit).run' (default : toVecI128Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] toVecI128

structure toVecI16Locals where
  deriving Inhabited

inductive toVecI16Exit where
  | ret (v : Zig.Vec (BitVec 16) 3)

def toVecI16 (p0 : Vector (BitVec 16) 3) : Zig.Result (Zig.Vec (BitVec 16) 3) := do
  let e ← ((do
    let i1 ← pure (⟨p0⟩ : Zig.Vec (BitVec 16) 3)
    pure (.ret i1)) : Zig.M toVecI16Locals toVecI16Exit).run' (default : toVecI16Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] toVecI16

structure toVecI32Locals where
  deriving Inhabited

inductive toVecI32Exit where
  | ret (v : Zig.Vec (BitVec 32) 4)

def toVecI32 (p0 : Vector (BitVec 32) 4) : Zig.Result (Zig.Vec (BitVec 32) 4) := do
  let e ← ((do
    let i1 ← pure (⟨p0⟩ : Zig.Vec (BitVec 32) 4)
    pure (.ret i1)) : Zig.M toVecI32Locals toVecI32Exit).run' (default : toVecI32Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] toVecI32

structure toVecI7Locals where
  deriving Inhabited

inductive toVecI7Exit where
  | ret (v : Zig.Vec (BitVec 7) 5)

def toVecI7 (p0 : Vector (BitVec 7) 5) : Zig.Result (Zig.Vec (BitVec 7) 5) := do
  let e ← ((do
    let i1 ← pure (⟨p0⟩ : Zig.Vec (BitVec 7) 5)
    pure (.ret i1)) : Zig.M toVecI7Locals toVecI7Exit).run' (default : toVecI7Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] toVecI7

structure toVecU1Locals where
  deriving Inhabited

inductive toVecU1Exit where
  | ret (v : Zig.Vec (BitVec 1) 8)

def toVecU1 (p0 : Vector (BitVec 1) 8) : Zig.Result (Zig.Vec (BitVec 1) 8) := do
  let e ← ((do
    let i1 ← pure (⟨p0⟩ : Zig.Vec (BitVec 1) 8)
    pure (.ret i1)) : Zig.M toVecU1Locals toVecU1Exit).run' (default : toVecU1Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] toVecU1

structure toVecU24Locals where
  deriving Inhabited

inductive toVecU24Exit where
  | ret (v : Zig.Vec (BitVec 24) 3)

def toVecU24 (p0 : Vector (BitVec 24) 3) : Zig.Result (Zig.Vec (BitVec 24) 3) := do
  let e ← ((do
    let i1 ← pure (⟨p0⟩ : Zig.Vec (BitVec 24) 3)
    pure (.ret i1)) : Zig.M toVecU24Locals toVecU24Exit).run' (default : toVecU24Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] toVecU24

structure toVecU64Locals where
  deriving Inhabited

inductive toVecU64Exit where
  | ret (v : Zig.Vec (BitVec 64) 2)

def toVecU64 (p0 : Vector (BitVec 64) 2) : Zig.Result (Zig.Vec (BitVec 64) 2) := do
  let e ← ((do
    let i1 ← pure (⟨p0⟩ : Zig.Vec (BitVec 64) 2)
    pure (.ret i1)) : Zig.M toVecU64Locals toVecU64Exit).run' (default : toVecU64Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] toVecU64

structure toVecU8Locals where
  deriving Inhabited

inductive toVecU8Exit where
  | ret (v : Zig.Vec (BitVec 8) 16)

def toVecU8 (p0 : Vector (BitVec 8) 16) : Zig.Result (Zig.Vec (BitVec 8) 16) := do
  let e ← ((do
    let i1 ← pure (⟨p0⟩ : Zig.Vec (BitVec 8) 16)
    pure (.ret i1)) : Zig.M toVecU8Locals toVecU8Exit).run' (default : toVecU8Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] toVecU8

structure toVecZ16Locals where
  deriving Inhabited

inductive toVecZ16Exit where
  | ret (v : Zig.Vec (BitVec 16) 3)

def toVecZ16 (p0 : Vector (BitVec 16) 4) : Zig.Result (Zig.Vec (BitVec 16) 3) := do
  let e ← ((do
    let i1 ← pure (⟨(p0 : Vector (BitVec 16) 4).pop⟩ : Zig.Vec (BitVec 16) 3)
    pure (.ret i1)) : Zig.M toVecZ16Locals toVecZ16Exit).run' (default : toVecZ16Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] toVecZ16

structure toVecZ8Locals where
  deriving Inhabited

inductive toVecZ8Exit where
  | ret (v : Zig.Vec (BitVec 8) 5)

def toVecZ8 (p0 : Vector (BitVec 8) 6) : Zig.Result (Zig.Vec (BitVec 8) 5) := do
  let e ← ((do
    let i1 ← pure (⟨(p0 : Vector (BitVec 8) 6).pop⟩ : Zig.Vec (BitVec 8) 5)
    pure (.ret i1)) : Zig.M toVecZ8Locals toVecZ8Exit).run' (default : toVecZ8Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] toVecZ8

end ToVec