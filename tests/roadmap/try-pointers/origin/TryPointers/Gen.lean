import ZigLean


namespace TryPointers

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

structure cleanupLocals where
  deriving Inhabited

inductive cleanupExit where
  | ret (v : Except Zig.ErrName (BitVec 8))

def cleanup (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : Zig.Ptr) : Zig.MemM (Except Zig.ErrName (BitVec 8)) := do
  let e ← ((do
    Zig.loadDiscardBytes 4 2 p0
    match ← Zig.tryPayloadPtr (BitVec 8) 2 p0 with
    | .error _ => (do
      let i5 ← Zig.errCodeAt (BitVec 8) 2 p0
      let i6 ← Zig.load (BitVec 32) 4 p2
      let i7 ← Zig.add false i6 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p2 i7
      let i9 ← Zig.load (BitVec 32) 4 p1
      let i10 ← Zig.add false i9 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p1 i10
      let i12 ← pure ((.error i5) : Except Zig.ErrName (BitVec 8))
      pure (.ret i12))
    | .ok v4 => (do
      let i14 ← Zig.load (BitVec 8) 1 v4
      let i15 ← Zig.load (BitVec 32) 4 p1
      let i16 ← Zig.add false i15 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p1 i16
      let i18 ← pure ((.ok i14) : Except Zig.ErrName (BitVec 8))
      pure (.ret i18))) : Zig.MM cleanupLocals cleanupExit).run' (default : cleanupLocals)
  match e with
  | .ret v => pure v

structure coldPayloadLocals where
  deriving Inhabited

inductive coldPayloadExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

def coldPayload (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    Zig.loadDiscardBytes 4 2 p0
    match ← Zig.tryPayloadPtr (BitVec 8) 2 p0 with
    | .error _ => (do
      let i4 ← Zig.errCodeAt (BitVec 8) 2 p0
      let i5 ← Zig.load (BitVec 32) 4 p1
      let i6 ← Zig.add false i5 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p1 i6
      let i8 ← pure ((.error i4) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i8))
    | .ok v3 => (do
      let i10 ← pure ((.ok v3) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i10))) : Zig.MM coldPayloadLocals coldPayloadExit).run' (default : coldPayloadLocals)
  match e with
  | .ret v => pure v

structure payload64Locals where
  deriving Inhabited

inductive payload64Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

def payload64 (p0 : Zig.Ptr) : Zig.MemM (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    Zig.loadDiscardBytes 16 8 p0
    match ← Zig.tryPayloadPtr (BitVec 64) 8 p0 with
    | .error _ => (do
      let i3 ← Zig.errCodeAt (BitVec 64) 8 p0
      let i4 ← pure ((.error i3) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i4))
    | .ok v2 => (do
      let i6 ← pure ((.ok v2) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i6))) : Zig.MM payload64Locals payload64Exit).run' (default : payload64Locals)
  match e with
  | .ret v => pure v

structure payload8Locals where
  deriving Inhabited

inductive payload8Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

def payload8 (p0 : Zig.Ptr) : Zig.MemM (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    Zig.loadDiscardBytes 4 2 p0
    match ← Zig.tryPayloadPtr (BitVec 8) 2 p0 with
    | .error _ => (do
      let i3 ← Zig.errCodeAt (BitVec 8) 2 p0
      let i4 ← pure ((.error i3) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i4))
    | .ok v2 => (do
      let i6 ← pure ((.ok v2) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i6))) : Zig.MM payload8Locals payload8Exit).run' (default : payload8Locals)
  match e with
  | .ret v => pure v

structure writeAliasLocals where
  deriving Inhabited

inductive writeAliasExit where
  | ret (v : Except Zig.ErrName (BitVec 8))

def writeAlias (p0 : Zig.Ptr) (p1 : BitVec 8) : Zig.MemM (Except Zig.ErrName (BitVec 8)) := do
  let e ← ((do
    Zig.loadDiscardBytes 4 2 p0
    match ← Zig.tryPayloadPtr (BitVec 8) 2 p0 with
    | .error _ => (do
      let i4 ← Zig.errCodeAt (BitVec 8) 2 p0
      let i5 ← pure ((.error i4) : Except Zig.ErrName (BitVec 8))
      pure (.ret i5))
    | .ok v3 => (do
      Zig.loadDiscardBytes 4 2 p0
      match ← Zig.tryPayloadPtr (BitVec 8) 2 p0 with
      | .error _ => (do
        let i9 ← Zig.errCodeAt (BitVec 8) 2 p0
        let i10 ← pure ((.error i9) : Except Zig.ErrName (BitVec 8))
        pure (.ret i10))
      | .ok v8 => (do
        Zig.store (α := BitVec 8) 1 v3 p1
        let i13 ← Zig.load (BitVec 8) 1 v8
        let i14 ← pure ((.ok i13) : Except Zig.ErrName (BitVec 8))
        pure (.ret i14)))) : Zig.MM writeAliasLocals writeAliasExit).run' (default : writeAliasLocals)
  match e with
  | .ret v => pure v

end TryPointers