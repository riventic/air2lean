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

structure Flags where
  ready : Bool
  err : Bool
  mode : BitVec 2
  count : BitVec 4
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Flags 8 where
  toBits v := ((Zig.Packed.toBits v.ready).setWidth 8 <<< 0) ||| ((Zig.Packed.toBits v.err).setWidth 8 <<< 1) ||| ((Zig.Packed.toBits v.mode).setWidth 8 <<< 2) ||| ((Zig.Packed.toBits v.count).setWidth 8 <<< 4)
  ofBits b := { ready := Zig.Packed.get b 0, err := Zig.Packed.get b 1, mode := Zig.Packed.get b 2, count := Zig.Packed.get b 4 }

instance : Zig.Enc Flags where
  size := 1
  align := 1
  encode v := Zig.Enc.encode (Zig.Packed.toBits v)
  decode bs := do
    let b : BitVec 8 ← Zig.Enc.decode bs
    pure (Zig.Packed.ofBits b)

structure Header where
  magic : BitVec 32
  len : BitVec 16
  kind : BitVec 8
  flags : Flags
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Header where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.magic), (4, Zig.Enc.encode v.len), (6, Zig.Enc.encode v.kind), (7, Zig.Enc.encode v.flags)]
  decode bs := do pure { magic := ← Zig.Enc.decodeAt bs 0, len := ← Zig.Enc.decodeAt bs 4, kind := ← Zig.Enc.decodeAt bs 6, flags := ← Zig.Enc.decodeAt bs 7 }

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

structure bitsToFloatLocals where
  deriving Inhabited

inductive bitsToFloatExit where
  | ret (v : Zig.F32)

def bitsToFloat (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Zig.F32) := do
  let e ← ((do
    let i2 ← pure (p0)
    Zig.store (α := BitVec 32) 4 i2 p1
    let i4 ← Zig.load (Zig.F32) 4 p0
    pure (.ret i4)) : Zig.MM bitsToFloatLocals bitsToFloatExit).run' (default : bitsToFloatLocals)
  match e with
  | .ret v => pure v

structure byteToFlagsLocals where
  deriving Inhabited

inductive byteToFlagsExit where
  | ret (v : Flags)

def byteToFlags (p0 : BitVec 8) : Zig.Result (Flags) := do
  let e ← ((do
    let i1 ← pure (Zig.Packed.ofBits p0 : Flags)
    pure (.ret i1)) : Zig.M byteToFlagsLocals byteToFlagsExit).run' (default : byteToFlagsLocals)
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

structure flagsToByteLocals where
  deriving Inhabited

inductive flagsToByteExit where
  | ret (v : BitVec 8)

def flagsToByte (p0 : Flags) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i1 ← pure (Zig.Packed.toBits p0)
    pure (.ret i1)) : Zig.M flagsToByteLocals flagsToByteExit).run' (default : flagsToByteLocals)
  match e with
  | .ret v => pure v

structure floatBitsLocals where
  deriving Inhabited

inductive floatBitsExit where
  | ret (v : BitVec 32)

def floatBits (p0 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (p0)
    let i2 ← Zig.load (BitVec 32) 4 i1
    pure (.ret i2)) : Zig.MM floatBitsLocals floatBitsExit).run' (default : floatBitsLocals)
  match e with
  | .ret v => pure v

structure headerLenLocals where
  local1 : Zig.Slice
  deriving Inhabited

inductive headerLenExit where
  | ret (v : Option (BitVec 16))
  | br4
  | br15

def headerLen (p0 : Zig.Slice) : Zig.MemM (Option (BitVec 16)) := do
  let e ← ((do
    modify (fun s => { s with local1 := p0 })
    match ← ((do
      let i6 ← pure (((← get).local1).len)
      let i7 ← pure (i6)
      let i8 ← pure (Zig.lt false i7 (8 : BitVec 64))
      if i8 then (do
        pure (.ret none))
      else (do
        pure .br4)) : Zig.MM headerLenLocals headerLenExit) with
    | .br4 => (do
      let i13 ← pure (((← get).local1).ptr)
      let i14 ← pure (i13)
      match ← ((do
        let i16 ← pure (i14.add 0)
        let i17 ← Zig.load (BitVec 32) 1 i16
        let i18 ← pure (i17 != (1280461121 : BitVec 32))
        if i18 then (do
          pure (.ret none))
        else (do
          pure .br15)) : Zig.MM headerLenLocals headerLenExit) with
      | .br15 => (do
        let i22 ← pure (i14.add 4)
        let i23 ← Zig.load (BitVec 16) 1 i22
        let i24 ← pure (some i23)
        pure (.ret i24))
      | e => pure e)
    | e => pure e) : Zig.MM headerLenLocals headerLenExit).run' (default : headerLenLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure incCountLocals where
  deriving Inhabited

inductive incCountExit where
  | ret

def incCount (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i1 ← pure (p0.add 0)
    let i2 ← Zig.loadBits (BitVec 4) 1 1 4 i1
    let i3 ← pure (Zig.addWrap i2 (1 : BitVec 4))
    Zig.storeBits (α := BitVec 4) 1 1 4 i1 i3
    pure .ret) : Zig.MM incCountLocals incCountExit).run' (default : incCountLocals)
  match e with
  | .ret => pure ()

structure isOkLocals where
  deriving Inhabited

inductive isOkExit where
  | ret (v : Bool)
  | br3 (v : Bool)

def isOk (p0 : Zig.Ptr) : Zig.MemM (Bool) := do
  let e ← ((do
    let i1 ← pure (p0.add 0)
    let i2 ← Zig.loadBits (Bool) 1 1 0 i1
    match ← ((do
      if i2 then (do
        let i5 ← pure (p0.add 0)
        let i6 ← Zig.loadBits (Bool) 1 1 1 i5
        let i7 ← pure (!i6)
        pure (.br3 i7))
      else (do
        pure (.br3 false))) : Zig.MM isOkLocals isOkExit) with
    | .br3 v3 => (do
      pure (.ret v3))
    | e => pure e) : Zig.MM isOkLocals isOkExit).run' (default : isOkLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

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

structure readHeaderLocals where
  local1 : Zig.Slice
  deriving Inhabited

inductive readHeaderExit where
  | ret (v : Header)

def readHeader (p0 : Zig.Slice) : Zig.MemM (Header) := do
  let e ← ((do
    modify (fun s => { s with local1 := p0 })
    let i5 ← pure (((← get).local1).ptr)
    let i6 ← pure (i5)
    let i7 ← Zig.load (Header) 1 i6
    pure (.ret i7)) : Zig.MM readHeaderLocals readHeaderExit).run' (default : readHeaderLocals)
  match e with
  | .ret v => pure v

structure setModeLocals where
  f : Flags
  deriving Inhabited

inductive setModeExit where
  | ret (v : BitVec 8)

def setMode (p0 : BitVec 8) (p1 : BitVec 2) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i3 ← pure (Zig.Packed.ofBits p0 : Flags)
    modify (fun s => { s with f := i3 })
    modify (fun s => { s with f := { s.f with mode := p1 } })
    let i7 ← pure ((← get).f)
    let i8 ← pure (Zig.Packed.toBits i7)
    pure (.ret i8)) : Zig.M setModeLocals setModeExit).run' (default : setModeLocals)
  match e with
  | .ret v => pure v

end Layout