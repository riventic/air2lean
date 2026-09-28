import ZigLean


namespace Layout

structure Point where
  x : BitVec 32
  y : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Point where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.x), (4, Zig.Enc.encode v.y)]
  decode bs := do pure { x := ← Zig.Enc.decodeAt bs 0, y := ← Zig.Enc.decodeAt bs 4 }

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

structure addrEqLocals where
  deriving Inhabited

inductive addrEqExit where
  | ret (v : Bool)

def addrEq (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (Bool) := do
  let e ← ((do
    let i2 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
    let i3 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p1)))
    let i4 ← pure (i2)
    let i5 ← pure (i3)
    let i6 ← pure (i4 == i5)
    pure (.ret i6)) : Zig.MM addrEqLocals addrEqExit).run' (default : addrEqLocals)
  match e with
  | .ret v => pure v

structure align4Locals where
  deriving Inhabited

inductive align4Exit where
  | ret (v : Zig.Ptr)
  | br4

def align4 (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
    let i2 ← pure (i1 &&& (3 : BitVec 64))
    let i3 ← pure (i2 == (0 : BitVec 64))
    match ← ((do
      if i3 then (do
        pure .br4)
      else (do
        throw .panic)) : Zig.MM align4Locals align4Exit) with
    | .br4 => (do
      let i9 ← pure (p0)
      pure (.ret i9))
    | e => pure e) : Zig.MM align4Locals align4Exit).run' (default : align4Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure asConstLocals where
  deriving Inhabited

inductive asConstExit where
  | ret (v : Zig.Ptr)

def asConst (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← pure (p0)
    pure (.ret i1)) : Zig.MM asConstLocals asConstExit).run' (default : asConstLocals)
  match e with
  | .ret v => pure v

structure asVolatileLocals where
  deriving Inhabited

inductive asVolatileExit where
  | ret (v : Zig.Ptr)

def asVolatile (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← pure (p0)
    let i2 ← pure (i1)
    pure (.ret i2)) : Zig.MM asVolatileLocals asVolatileExit).run' (default : asVolatileLocals)
  match e with
  | .ret v => pure v

structure dropConstLocals where
  deriving Inhabited

inductive dropConstExit where
  | ret (v : Zig.Ptr)

def dropConst (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← pure (p0)
    pure (.ret i1)) : Zig.MM dropConstLocals dropConstExit).run' (default : dropConstLocals)
  match e with
  | .ret v => pure v

structure parentOfXLocals where
  deriving Inhabited

inductive parentOfXExit where
  | ret (v : Zig.Ptr)

def parentOfX (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← pure (p0.add (-(0 : Int)))
    let i2 ← pure (i1)
    pure (.ret i2)) : Zig.MM parentOfXLocals parentOfXExit).run' (default : parentOfXLocals)
  match e with
  | .ret v => pure v

structure parentOfYLocals where
  deriving Inhabited

inductive parentOfYExit where
  | ret (v : Zig.Ptr)

def parentOfY (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← pure (p0.add (-(4 : Int)))
    let i2 ← pure (i1)
    pure (.ret i2)) : Zig.MM parentOfYLocals parentOfYExit).run' (default : parentOfYLocals)
  match e with
  | .ret v => pure v

structure ptrFromAddrLocals where
  deriving Inhabited

inductive ptrFromAddrExit where
  | ret (v : Zig.Ptr)
  | br2
  | br9

def ptrFromAddr (p0 : BitVec 64) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← pure (p0 != (0 : BitVec 64))
    match ← ((do
      if i1 then (do
        pure .br2)
      else (do
        throw .panic)) : Zig.MM ptrFromAddrLocals ptrFromAddrExit) with
    | .br2 => (do
      let i7 ← pure (p0 &&& (3 : BitVec 64))
      let i8 ← pure (i7 == (0 : BitVec 64))
      match ← ((do
        if i8 then (do
          pure .br9)
        else (do
          throw .panic)) : Zig.MM ptrFromAddrLocals ptrFromAddrExit) with
      | .br9 => (do
        let i14 ← Zig.callM (Zig.ptrFromAddr (p0).toNat)
        pure (.ret i14))
      | e => pure e)
    | e => pure e) : Zig.MM ptrFromAddrLocals ptrFromAddrExit).run' (default : ptrFromAddrLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure ptrRoundTripLocals where
  deriving Inhabited

inductive ptrRoundTripExit where
  | ret (v : Zig.Ptr)
  | br3
  | br10

def ptrRoundTrip (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
    let i2 ← pure (i1 != (0 : BitVec 64))
    match ← ((do
      if i2 then (do
        pure .br3)
      else (do
        throw .panic)) : Zig.MM ptrRoundTripLocals ptrRoundTripExit) with
    | .br3 => (do
      let i8 ← pure (i1 &&& (3 : BitVec 64))
      let i9 ← pure (i8 == (0 : BitVec 64))
      match ← ((do
        if i9 then (do
          pure .br10)
        else (do
          throw .panic)) : Zig.MM ptrRoundTripLocals ptrRoundTripExit) with
      | .br10 => (do
        let i15 ← Zig.callM (Zig.ptrFromAddr (i1).toNat)
        pure (.ret i15))
      | e => pure e)
    | e => pure e) : Zig.MM ptrRoundTripLocals ptrRoundTripExit).run' (default : ptrRoundTripLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end Layout