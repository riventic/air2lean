import ZigLean


namespace Layout

inductive ShapeTag where
  | circle
  | rect
  | none
  deriving Repr, Inhabited, DecidableEq

def ShapeTag.toBits : ShapeTag → BitVec 2
  | .circle => (0 : BitVec 2)
  | .rect => (1 : BitVec 2)
  | .none => (2 : BitVec 2)

def ShapeTag.ofInt? (v : Int) : Option ShapeTag :=
  if v = 0 then Option.some .circle else if v = 1 then Option.some .rect else if v = 2 then Option.some .none else Option.none

def ShapeTag.isNamed (_ : ShapeTag) : Bool := true

instance : Zig.Enc ShapeTag where
  size := 1
  align := 1
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 2 ← Zig.Enc.decode bs
    match ShapeTag.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

structure Rect where
  w : BitVec 16
  h : BitVec 16
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Rect where
  size := 4
  align := 2
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.w), (2, Zig.Enc.encode v.h)]
  decode bs := do pure { w := ← Zig.Enc.decodeAt bs 0, h := ← Zig.Enc.decodeAt bs 2 }

inductive Shape where
  | circle (v : BitVec 32)
  | rect (v : Rect)
  | none
  deriving Repr, Inhabited, DecidableEq

def Shape.tag : Shape → ShapeTag
  | .circle _ => .circle
  | .rect _ => .rect
  | .none => .none

def Shape.get_circle : Shape → Zig.Result (BitVec 32)
  | .circle v => pure v
  | _ => throw .panic

def Shape.modify_circle (g : BitVec 32 → BitVec 32) : Shape → Shape
  | .circle v => .circle (g v)
  | _ => .circle (g default)

def Shape.setTag_circle : Shape → Shape
  | .circle v => .circle v
  | _ => .circle default

def Shape.get_rect : Shape → Zig.Result (Rect)
  | .rect v => pure v
  | _ => throw .panic

def Shape.modify_rect (g : Rect → Rect) : Shape → Shape
  | .rect v => .rect (g v)
  | _ => .rect (g default)

def Shape.setTag_rect : Shape → Shape
  | .rect v => .rect v
  | _ => .rect default

def Shape.get_none : Shape → Zig.Result (Unit)
  | .none => pure ()
  | _ => throw .panic

def Shape.modify_none (_g : Unit → Unit) : Shape → Shape
  | .none => .none
  | _ => .none

def Shape.setTag_none : Shape → Shape
  | .none => .none
  | _ => .none

instance : Zig.Enc Shape where
  size := 8
  align := 4
  encode v := match v with
    | .circle x => Zig.Enc.fields 8 [(4, Zig.Enc.encode v.tag), (0, Zig.Enc.encode x)]
    | .rect x => Zig.Enc.fields 8 [(4, Zig.Enc.encode v.tag), (0, Zig.Enc.encode x)]
    | .none => Zig.Enc.fields 8 [(4, Zig.Enc.encode v.tag)]
  decode bs := do
    let t : ShapeTag ← Zig.Enc.decodeAt bs 4
    match t with
    | .circle => pure (.circle (← Zig.Enc.decodeAt bs 0))
    | .rect => pure (.rect (← Zig.Enc.decodeAt bs 0))
    | .none => pure .none

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
def mem0 : Zig.Mem := Zig.Mem.ofGlobals [
  -- 0: layout.double
  (#[.undef], 1),
  -- 1: layout.square
  (#[.undef], 1),
  -- 2: layout.succ
  (#[.undef], 1)]

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

structure doubleLocals where
  deriving Inhabited

inductive doubleExit where
  | ret (v : BitVec 32)

def double (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (Zig.mulWrap p0 (2 : BitVec 32))
    pure (.ret i1)) : Zig.M doubleLocals doubleExit).run' (default : doubleLocals)
  match e with
  | .ret v => pure v

structure squareLocals where
  deriving Inhabited

inductive squareExit where
  | ret (v : BitVec 32)

def square (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (Zig.mulWrap p0 p0)
    pure (.ret i1)) : Zig.M squareLocals squareExit).run' (default : squareLocals)
  match e with
  | .ret v => pure v

structure succLocals where
  deriving Inhabited

inductive succExit where
  | ret (v : BitVec 32)

def succ (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (Zig.addWrap p0 (1 : BitVec 32))
    pure (.ret i1)) : Zig.M succLocals succExit).run' (default : succLocals)
  match e with
  | .ret v => pure v

structure applyOpLocals where
  deriving Inhabited

inductive applyOpExit where
  | ret (v : BitVec 32)
  | br3

def applyOp (p0 : BitVec 64) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i2 ← pure (Zig.lt false p0 (3 : BitVec 64))
    match ← ((do
      if i2 then (do
        pure .br3)
      else (do
        throw .outOfBounds)) : Zig.MM applyOpLocals applyOpExit) with
    | .br3 => (do
      let _i8 ← Zig.callR (Zig.vindex (#v[(⟨some 0, 0⟩ : Zig.Ptr), (⟨some 1, 0⟩ : Zig.Ptr), (⟨some 2, 0⟩ : Zig.Ptr)] : Vector (Zig.Ptr) 3) p0)
      let i9 ← (if _i8 == (⟨some 0, 0⟩ : Zig.Ptr) then Zig.callR (double p1) else if _i8 == (⟨some 1, 0⟩ : Zig.Ptr) then Zig.callR (square p1) else if _i8 == (⟨some 2, 0⟩ : Zig.Ptr) then Zig.callR (succ p1) else throw .illegal)
      pure (.ret i9))
    | e => pure e) : Zig.MM applyOpLocals applyOpExit).run' (default : applyOpLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure applyTwiceLocals where
  deriving Inhabited

inductive applyTwiceExit where
  | ret (v : BitVec 32)

def applyTwice (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i2 ← (if p0 == (⟨some 0, 0⟩ : Zig.Ptr) then Zig.callR (double p1) else if p0 == (⟨some 1, 0⟩ : Zig.Ptr) then Zig.callR (square p1) else if p0 == (⟨some 2, 0⟩ : Zig.Ptr) then Zig.callR (succ p1) else throw .illegal)
    let i3 ← (if p0 == (⟨some 0, 0⟩ : Zig.Ptr) then Zig.callR (double i2) else if p0 == (⟨some 1, 0⟩ : Zig.Ptr) then Zig.callR (square i2) else if p0 == (⟨some 2, 0⟩ : Zig.Ptr) then Zig.callR (succ i2) else throw .illegal)
    pure (.ret i3)) : Zig.MM applyTwiceLocals applyTwiceExit).run' (default : applyTwiceLocals)
  match e with
  | .ret v => pure v

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

structure bumpLocals where
  deriving Inhabited

inductive bumpExit where
  | ret
  | br1

def bump (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    match ← ((do
      let i2 ← Zig.load (Except Zig.ErrName (BitVec 8)) 2 p0
      let i3 ← pure (Zig.isNonErr i2)
      if i3 then (do
        let i5 ← pure (Zig.errPayloadPtr (BitVec 8) p0)
        let i6 ← Zig.load (BitVec 8) 1 i5
        let i7 ← pure (Zig.addWrap i6 (1 : BitVec 8))
        Zig.store (α := BitVec 8) 1 i5 i7
        pure .br1)
      else (do
        let _i10 ← Zig.errCodeAt (BitVec 8) 2 p0
        pure .br1)) : Zig.MM bumpLocals bumpExit) with
    | .br1 => (do
      pure .ret)
    | e => pure e) : Zig.MM bumpLocals bumpExit).run' (default : bumpLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure digitLocals where
  deriving Inhabited

inductive digitExit where
  | ret (v : Except Zig.ErrName (BitVec 8))
  | br1
  | br6

def digit (p0 : BitVec 8) : Zig.Result (Except Zig.ErrName (BitVec 8)) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure (p0 == (0 : BitVec 8))
      if i2 then (do
        pure (.ret (.error "Empty" : Except Zig.ErrName (BitVec 8))))
      else (do
        pure .br1)) : Zig.M digitLocals digitExit) with
    | .br1 => (do
      match ← ((do
        let i7 ← pure (Zig.gt false p0 (9 : BitVec 8))
        if i7 then (do
          pure (.ret (.error "TooBig" : Except Zig.ErrName (BitVec 8))))
        else (do
          pure .br6)) : Zig.M digitLocals digitExit) with
      | .br6 => (do
        let i11 ← pure ((.ok p0) : Except Zig.ErrName (BitVec 8))
        pure (.ret i11))
      | e => pure e)
    | e => pure e) : Zig.M digitLocals digitExit).run' (default : digitLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure bumpDigitLocals where
  r : Zig.Ptr
  deriving Inhabited

inductive bumpDigitExit where
  | ret (v : BitVec 8)
  | br7 (v : BitVec 8)

def bumpDigit (p0 : BitVec 8) : Zig.MemM (BitVec 8) := do
  let s1 ← Zig.allocStack 4 2
  let e ← ((do
    let i1 ← pure (← get).r
    let i2 ← Zig.callR (digit p0)
    Zig.store (α := Except Zig.ErrName (BitVec 8)) 2 i1 i2
    let _i4 ← Zig.callM (bump i1)
    let i5 ← Zig.load (Except Zig.ErrName (BitVec 8)) 2 i1
    let i6 ← pure (Zig.isNonErr i5)
    match ← ((do
      if i6 then (do
        let i9 ← Zig.callR (Zig.unwrapPayload i5)
        pure (.br7 i9))
      else (do
        let i11 ← Zig.callR (Zig.unwrapErr i5)
        if i11 == "Empty" then (do
          pure (.br7 (100 : BitVec 8)))
        else (do
          if i11 == "TooBig" then (do
            pure (.br7 (200 : BitVec 8)))
          else (do
            throw .panic)))) : Zig.MM bumpDigitLocals bumpDigitExit) with
    | .br7 v7 => (do
      pure (.ret v7))
    | e => pure e) : Zig.MM bumpDigitLocals bumpDigitExit).run' { (default : bumpDigitLocals) with r := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v
  | _ => throw .panic

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

structure growCircleLocals where
  deriving Inhabited

inductive growCircleExit where
  | ret
  | br3
  | br6

def growCircle (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i1 ← Zig.load (Shape) 4 p0
    let i2 ← pure (Shape.tag i1)
    match ← ((do
      if i2 == ShapeTag.circle then (do
        let i12 ← pure (p0.add 0)
        let i13 ← Zig.load (BitVec 32) 4 i12
        let i14 ← pure (Zig.addWrap i13 (1 : BitVec 32))
        Zig.store (α := BitVec 32) 4 i12 i14
        pure .br3)
      else (do
        let i5 ← pure (ShapeTag.isNamed i2)
        match ← ((do
          if i5 then (do
            pure .br6)
          else (do
            throw .panic)) : Zig.MM growCircleLocals growCircleExit) with
        | .br6 => (do
          pure .br3)
        | e => pure e)) : Zig.MM growCircleLocals growCircleExit) with
    | .br3 => (do
      pure .ret)
    | e => pure e) : Zig.MM growCircleLocals growCircleExit).run' (default : growCircleLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

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

structure setCircleLocals where
  deriving Inhabited

inductive setCircleExit where
  | ret

def setCircle (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    Zig.store (α := ShapeTag) 1 (p0.add 4) ShapeTag.circle
    let i3 ← pure (p0.add 0)
    Zig.store (α := BitVec 32) 4 i3 p1
    pure .ret) : Zig.MM setCircleLocals setCircleExit).run' (default : setCircleLocals)
  match e with
  | .ret => pure ()

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

structure shapeAreaLocals where
  deriving Inhabited

inductive shapeAreaExit where
  | ret (v : BitVec 32)
  | br3 (v : BitVec 32)

def shapeArea (p0 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.load (Shape) 4 p0
    let i2 ← pure (Shape.tag i1)
    match ← ((do
      match i2 with
      | .circle => (do
        let i7 ← Zig.callR (Shape.get_circle i1)
        let i8 ← pure (Zig.mulWrap (3 : BitVec 32) i7)
        let i9 ← pure (Zig.mulWrap i8 i7)
        pure (.br3 i9))
      | .rect => (do
        let i11 ← Zig.callR (Shape.get_rect i1)
        let i12 ← pure ((i11).w)
        let i13 ← Zig.intCast false false 32 i12
        let i14 ← pure ((i11).h)
        let i15 ← Zig.intCast false false 32 i14
        let i16 ← pure (Zig.mulWrap i13 i15)
        pure (.br3 i16))
      | .none => (do
        pure (.br3 (0 : BitVec 32)))) : Zig.MM shapeAreaLocals shapeAreaExit) with
    | .br3 v3 => (do
      pure (.ret v3))
    | e => pure e) : Zig.MM shapeAreaLocals shapeAreaExit).run' (default : shapeAreaLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure twiceLocals where
  deriving Inhabited

inductive twiceExit where
  | ret (v : BitVec 32)
  | br2 (v : Zig.Ptr)

def twice (p0 : Bool) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    match ← ((do
      if p0 then (do
        pure (.br2 (⟨some 1, 0⟩ : Zig.Ptr)))
      else (do
        pure (.br2 (⟨some 0, 0⟩ : Zig.Ptr)))) : Zig.MM twiceLocals twiceExit) with
    | .br2 v2 => (do
      let i6 ← Zig.callM (applyTwice v2 p1)
      pure (.ret i6))
    | e => pure e) : Zig.MM twiceLocals twiceExit).run' (default : twiceLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end Layout