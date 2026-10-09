-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"gnu","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"westmere","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","aes","avx","avx2","bmi","bmi2","cmov","crc32","cx16","cx8","f16c","fma","fxsr","idivq_to_divl","lzcnt","macrofusion","mmx","movbe","no_bypass_delay_mov","nopl","pclmul","popcnt","rdrnd","sahf","sse","sse2","sse3","sse4_1","sse4_2","ssse3","vzeroupper","x87","xsave"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.7.0.14...7.0.14-gnu.2.39","zig_version":"0.15.2"}}
import ZigLean


namespace Layout

structure Word where
  bytes : Vector Zig.Byte 4
  deriving Repr, Inhabited, DecidableEq

def Word.get_int (u : Word) : Zig.Result (BitVec 32) := Zig.Raw.get (BitVec 32) u.bytes

def Word.modify_int (g : BitVec 32 → BitVec 32) (u : Word) : Word :=
  ⟨Zig.Raw.set u.bytes (g (Zig.Raw.getD (Zig.Raw.get (BitVec 32) u.bytes)))⟩

def Word.get_half (u : Word) : Zig.Result (BitVec 16) := Zig.Raw.get (BitVec 16) u.bytes

def Word.modify_half (g : BitVec 16 → BitVec 16) (u : Word) : Word :=
  ⟨Zig.Raw.set u.bytes (g (Zig.Raw.getD (Zig.Raw.get (BitVec 16) u.bytes)))⟩

def Word.get_bytes (u : Word) : Zig.Result (Vector (BitVec 8) 4) := Zig.Raw.get (Vector (BitVec 8) 4) u.bytes

def Word.modify_bytes (g : Vector (BitVec 8) 4 → Vector (BitVec 8) 4) (u : Word) : Word :=
  ⟨Zig.Raw.set u.bytes (g (Zig.Raw.getD (Zig.Raw.get (Vector (BitVec 8) 4) u.bytes)))⟩

instance : Zig.Enc Word where
  size := 4
  align := 4
  encode v := v.bytes.toArray
  decode bs := pure ⟨Zig.Raw.ofArray 4 bs⟩

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

instance : Zig.Packed ShapeTag 2 where
  toBits := ShapeTag.toBits
  ofBits b := (ShapeTag.ofInt? (Zig.val false b)).getD default
  valid b := (ShapeTag.ofInt? (Zig.val false b)).isSome

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
    Zig.Packed.ofBits? b

structure Reg where
  bytes : Vector Zig.Byte 1
  deriving Repr, Inhabited, DecidableEq

def Reg.get_raw (u : Reg) : Zig.Result (BitVec 8) := Zig.PackedU.get (BitVec 8) u.bytes

def Reg.modify_raw (g : BitVec 8 → BitVec 8) (u : Reg) : Reg :=
  ⟨Zig.PackedU.set u.bytes (g (Zig.Raw.getD (Zig.PackedU.get (BitVec 8) u.bytes)))⟩

def Reg.get_signed (u : Reg) : Zig.Result (BitVec 8) := Zig.PackedU.get (BitVec 8) u.bytes

def Reg.modify_signed (g : BitVec 8 → BitVec 8) (u : Reg) : Reg :=
  ⟨Zig.PackedU.set u.bytes (g (Zig.Raw.getD (Zig.PackedU.get (BitVec 8) u.bytes)))⟩

def Reg.get_flags (u : Reg) : Zig.Result (Flags) := Zig.PackedU.get (Flags) u.bytes

def Reg.modify_flags (g : Flags → Flags) (u : Reg) : Reg :=
  ⟨Zig.PackedU.set u.bytes (g (Zig.Raw.getD (Zig.PackedU.get (Flags) u.bytes)))⟩

instance : Zig.Enc Reg where
  size := 1
  align := 1
  encode v := v.bytes.toArray
  decode bs := pure ⟨Zig.Raw.ofArray 1 bs⟩

structure Point where
  x : BitVec 32
  y : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Point where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.x), (4, Zig.Enc.encode v.y)]
  decode bs := do pure { x := ← Zig.Enc.decodeAt bs 0, y := ← Zig.Enc.decodeAt bs 4 }

structure Pair where
  lo : BitVec 3
  hi : BitVec 3
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Pair 6 where
  toBits v := ((Zig.Packed.toBits v.lo).setWidth 6 <<< 0) ||| ((Zig.Packed.toBits v.hi).setWidth 6 <<< 3)
  ofBits b := { lo := Zig.Packed.get b 0, hi := Zig.Packed.get b 3 }

instance : Zig.Enc Pair where
  size := 1
  align := 1
  encode v := Zig.Enc.encode (Zig.Packed.toBits v)
  decode bs := do
    let b : BitVec 6 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

inductive NumTag where
  | int
  | small
  deriving Repr, Inhabited, DecidableEq

def NumTag.toBits : NumTag → BitVec 1
  | .int => (0 : BitVec 1)
  | .small => (1 : BitVec 1)

def NumTag.ofInt? (v : Int) : Option NumTag :=
  if v = 0 then Option.some .int else if v = 1 then Option.some .small else Option.none

def NumTag.isNamed (_ : NumTag) : Bool := true

instance : Zig.Packed NumTag 1 where
  toBits := NumTag.toBits
  ofBits b := (NumTag.ofInt? (Zig.val false b)).getD default
  valid b := (NumTag.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc NumTag where
  size := 1
  align := 1
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 1 ← Zig.Enc.decode bs
    match NumTag.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

inductive Num where
  | int (v : BitVec 32)
  | small (v : BitVec 8)
  deriving Repr, Inhabited, DecidableEq

def Num.tag : Num → NumTag
  | .int _ => .int
  | .small _ => .small

def Num.get_int : Num → Zig.Result (BitVec 32)
  | .int v => pure v
  | _ => throw .panic

def Num.modify_int (g : BitVec 32 → BitVec 32) : Num → Num
  | .int v => .int (g v)
  | _ => .int (g default)

def Num.setTag_int : Num → Num
  | .int v => .int v
  | _ => .int default

def Num.get_small : Num → Zig.Result (BitVec 8)
  | .small v => pure v
  | _ => throw .panic

def Num.modify_small (g : BitVec 8 → BitVec 8) : Num → Num
  | .small v => .small (g v)
  | _ => .small (g default)

def Num.setTag_small : Num → Num
  | .small v => .small v
  | _ => .small default

instance : Zig.Enc Num where
  size := 8
  align := 4
  encode v := match v with
    | .int x => Zig.Enc.fields 8 [(4, Zig.Enc.encode v.tag), (0, Zig.Enc.encode x)]
    | .small x => Zig.Enc.fields 8 [(4, Zig.Enc.encode v.tag), (0, Zig.Enc.encode x)]
  decode bs := do
    let t : NumTag ← Zig.Enc.decodeAt bs 4
    match t with
    | .int => pure (.int (← Zig.Enc.decodeAt bs 0))
    | .small => pure (.small (← Zig.Enc.decodeAt bs 0))

structure Nib where
  bytes : Vector Zig.Byte 1
  deriving Repr, Inhabited, DecidableEq

def Nib.get_lo (u : Nib) : Zig.Result (BitVec 4) := Zig.PackedU.get (BitVec 4) u.bytes

def Nib.modify_lo (g : BitVec 4 → BitVec 4) (u : Nib) : Nib :=
  ⟨Zig.PackedU.set u.bytes (g (Zig.Raw.getD (Zig.PackedU.get (BitVec 4) u.bytes)))⟩

def Nib.get_signed (u : Nib) : Zig.Result (BitVec 4) := Zig.PackedU.get (BitVec 4) u.bytes

def Nib.modify_signed (g : BitVec 4 → BitVec 4) (u : Nib) : Nib :=
  ⟨Zig.PackedU.set u.bytes (g (Zig.Raw.getD (Zig.PackedU.get (BitVec 4) u.bytes)))⟩

instance : Zig.Enc Nib where
  size := 1
  align := 1
  encode v := v.bytes.toArray
  decode bs := pure ⟨Zig.Raw.ofArray 1 bs⟩

inductive Mode where
  | off
  | low
  | high
  deriving Repr, Inhabited, DecidableEq

def Mode.toBits : Mode → BitVec 2
  | .off => (0 : BitVec 2)
  | .low => (1 : BitVec 2)
  | .high => (2 : BitVec 2)

def Mode.ofInt? (v : Int) : Option Mode :=
  if v = 0 then Option.some .off else if v = 1 then Option.some .low else if v = 2 then Option.some .high else Option.none

def Mode.isNamed (_ : Mode) : Bool := true

instance : Zig.Packed Mode 2 where
  toBits := Mode.toBits
  ofBits b := (Mode.ofInt? (Zig.val false b)).getD default
  valid b := (Mode.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc Mode where
  size := 1
  align := 1
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 2 ← Zig.Enc.decode bs
    match Mode.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

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

structure Ctl where
  on : Bool
  mode : Mode
  level : BitVec 5
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Ctl 8 where
  toBits v := ((Zig.Packed.toBits v.on).setWidth 8 <<< 0) ||| ((Zig.Packed.toBits v.mode).setWidth 8 <<< 1) ||| ((Zig.Packed.toBits v.level).setWidth 8 <<< 3)
  ofBits b := { on := Zig.Packed.get b 0, mode := Zig.Packed.get b 1, level := Zig.Packed.get b 3 }
  valid b := Zig.Packed.validAt (Mode) b 1

instance : Zig.Enc Ctl where
  size := 1
  align := 1
  encode v := Zig.Enc.encode (Zig.Packed.toBits v)
  decode bs := do
    let b : BitVec 8 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals [
  -- 0: layout.double
  (#[.undef], 1, .constGlobal),
  -- 1: layout.square
  (#[.undef], 1, .constGlobal),
  -- 2: layout.succ
  (#[.undef], 1, .constGlobal),
  -- 3: layout.table
  (Zig.Enc.encode ((#v[(10 : BitVec 32), (20 : BitVec 32), (30 : BitVec 32)] : Vector (BitVec 32) 3) : Vector (BitVec 32) 3), 4, .constGlobal)]

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
      let i9 ← Zig.callM (Zig.checkAlign 4 p0 >>= fun _ => pure p0)
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
      let i8 ← Zig.callR (Zig.vindex (#v[(⟨some 0, 0⟩ : Zig.Ptr), (⟨some 1, 0⟩ : Zig.Ptr), (⟨some 2, 0⟩ : Zig.Ptr)] : Vector (Zig.Ptr) 3) p0)
      let i9 ← (if i8 == (⟨some 0, 0⟩ : Zig.Ptr) then Zig.callR (double p1) else if i8 == (⟨some 1, 0⟩ : Zig.Ptr) then Zig.callR (square p1) else if i8 == (⟨some 2, 0⟩ : Zig.Ptr) then Zig.callR (succ p1) else throw .illegal)
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
      let i2 ← (letI : Zig.Enc (Except Zig.ErrName (BitVec 8)) := Zig.errorUnionEnc (⟨#["Empty", "TooBig"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 8))); Zig.load (Except Zig.ErrName (BitVec 8)) 2 p0)
      let i3 ← pure (Zig.isNonErr i2)
      if i3 then (do
        let i5 ← pure (Zig.errPayloadPtr (BitVec 8) p0)
        let i6 ← Zig.load (BitVec 8) 1 i5
        let i7 ← pure (Zig.addWrap i6 (1 : BitVec 8))
        Zig.store (α := BitVec 8) 1 i5 i7
        pure .br1)
      else (do
        let _i10 ← Zig.finiteErrCodeAt (⟨#["Empty", "TooBig"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 p0
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
    (letI : Zig.Enc (Except Zig.ErrName (BitVec 8)) := Zig.errorUnionEnc (⟨#["Empty", "TooBig"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 8))); Zig.store (α := Except Zig.ErrName (BitVec 8)) 2 i1 i2)
    let _i4 ← Zig.callM (bump i1)
    let i5 ← (letI : Zig.Enc (Except Zig.ErrName (BitVec 8)) := Zig.errorUnionEnc (⟨#["Empty", "TooBig"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 8))); Zig.load (Except Zig.ErrName (BitVec 8)) 2 i1)
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

structure bumpPairLocals where
  deriving Inhabited

inductive bumpPairExit where
  | ret (v : BitVec 3)

def bumpPair (p0 : Zig.Ptr) (p1 : BitVec 6) : Zig.MemM (BitVec 3) := do
  let e ← ((do
    let i2 ← Zig.Packed.ofBits? (α := Pair) p1
    Zig.store (α := Pair) 1 p0 i2
    let i4 ← pure (p0.add 0)
    let i5 ← Zig.loadBits (BitVec 3) 1 1 3 i4
    let i6 ← pure (Zig.addWrap i5 (1 : BitVec 3))
    Zig.storeBits (α := BitVec 3) 1 1 3 i4 i6
    let i8 ← pure (p0.add 0)
    let i9 ← Zig.loadBits (BitVec 3) 1 1 0 i8
    pure (.ret i9)) : Zig.MM bumpPairLocals bumpPairExit).run' (default : bumpPairLocals)
  match e with
  | .ret v => pure v

structure byteToFlagsLocals where
  deriving Inhabited

inductive byteToFlagsExit where
  | ret (v : Flags)

def byteToFlags (p0 : BitVec 8) : Zig.Result (Flags) := do
  let e ← ((do
    let i1 ← Zig.Packed.ofBits? (α := Flags) p0
    pure (.ret i1)) : Zig.M byteToFlagsLocals byteToFlagsExit).run' (default : byteToFlagsLocals)
  match e with
  | .ret v => pure v

structure ctlModeLocals where
  deriving Inhabited

inductive ctlModeExit where
  | ret (v : BitVec 8)

def ctlMode (p0 : Zig.Ptr) : Zig.MemM (BitVec 8) := do
  let e ← ((do
    let i1 ← pure (p0.add 0)
    let i2 ← Zig.loadBits (Mode) 1 1 1 i1
    let i3 ← pure (Mode.toBits i2)
    let i4 ← Zig.intCast false false 8 i3
    pure (.ret i4)) : Zig.MM ctlModeLocals ctlModeExit).run' (default : ctlModeLocals)
  match e with
  | .ret v => pure v

structure ctlSumLocals where
  deriving Inhabited

inductive ctlSumExit where
  | ret (v : BitVec 8)

def ctlSum (p0 : BitVec 8) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i1 ← Zig.Packed.ofBits? (α := Ctl) p0
    let i2 ← pure ((i1).mode)
    let i3 ← pure (Mode.toBits i2)
    let i4 ← Zig.intCast false false 8 i3
    let i5 ← pure ((i1).level)
    let i6 ← Zig.intCast false false 8 i5
    let i7 ← Zig.add false i4 i6
    pure (.ret i7)) : Zig.M ctlSumLocals ctlSumExit).run' (default : ctlSumLocals)
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
  deriving Inhabited

inductive headerLenExit where
  | ret (v : Option (BitVec 16))
  | br1
  | br10

def headerLen (p0 : Zig.Slice) : Zig.MemM (Option (BitVec 16)) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure p0.len
      let i3 ← pure (i2)
      let i4 ← pure (Zig.lt false i3 (8 : BitVec 64))
      if i4 then (do
        pure (.ret none))
      else (do
        pure .br1)) : Zig.MM headerLenLocals headerLenExit) with
    | .br1 => (do
      let i8 ← pure p0.ptr
      let i9 ← pure (i8)
      match ← ((do
        let i11 ← pure (i9.add 0)
        let i12 ← Zig.load (BitVec 32) 1 i11
        let i13 ← pure (i12 != (1280461121 : BitVec 32))
        if i13 then (do
          pure (.ret none))
        else (do
          pure .br10)) : Zig.MM headerLenLocals headerLenExit) with
      | .br10 => (do
        let i17 ← pure (i9.add 4)
        let i18 ← Zig.load (BitVec 16) 1 i17
        let i19 ← pure (some i18)
        pure (.ret i19))
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

structure laneSetLocals where
  deriving Inhabited

inductive laneSetExit where
  | ret (v : BitVec 32)

def laneSet (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i2 ← pure (p0.elem 4 (2 : BitVec 64))
    Zig.store (α := BitVec 32) 4 i2 p1
    let i4 ← Zig.callM (Zig.load (BitVec 32) 4 (p0.elem 4 (1 : BitVec 64)))
    let i5 ← Zig.callM (Zig.load (BitVec 32) 4 (p0.elem 4 (2 : BitVec 64)))
    let i6 ← pure (Zig.addWrap i4 i5)
    pure (.ret i6)) : Zig.MM laneSetLocals laneSetExit).run' (default : laneSetLocals)
  match e with
  | .ret v => pure v

structure lowByteLocals where
  deriving Inhabited

inductive lowByteExit where
  | ret (v : BitVec 8)

def lowByte (p0 : Word) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i1 ← Zig.call (Word.get_bytes p0)
    let i2 ← Zig.call (Zig.vindex i1 (0 : BitVec 64))
    pure (.ret i2)) : Zig.M lowByteLocals lowByteExit).run' (default : lowByteLocals)
  match e with
  | .ret v => pure v

structure maskCountLocals where
  deriving Inhabited

inductive maskCountExit where
  | ret (v : BitVec 32)

def maskCount (p0 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.load (Zig.Vec (Bool) 4) 1 p0
    let i2 ← pure (Zig.Vec.select i1 ((⟨#v[(1 : BitVec 32), (1 : BitVec 32), (1 : BitVec 32), (1 : BitVec 32)]⟩) : Zig.Vec (BitVec 32) 4) ((⟨#v[(0 : BitVec 32), (0 : BitVec 32), (0 : BitVec 32), (0 : BitVec 32)]⟩) : Zig.Vec (BitVec 32) 4))
    let i3 ← pure (Zig.Vec.reduce Zig.addWrap i2)
    pure (.ret i3)) : Zig.MM maskCountLocals maskCountExit).run' (default : maskCountLocals)
  match e with
  | .ret v => pure v

structure maskStoreLocals where
  local2 : Zig.Ptr
  deriving Inhabited

inductive maskStoreExit where
  | ret (v : BitVec 32)

def maskStore (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s2 ← Zig.allocStack 16 16
  let e ← ((do
    let i2 ← pure (← get).local2
    let i3 ← pure (i2.elem 4 (0 : BitVec 64))
    let i4 ← pure (p1 &&& (255 : BitVec 32))
    Zig.store (α := BitVec 32) 4 i3 i4
    let i6 ← pure (i2.elem 4 (1 : BitVec 64))
    let i7 ← pure (Zig.shr false p1 (8 : BitVec 5))
    let i8 ← pure (i7 &&& (255 : BitVec 32))
    Zig.store (α := BitVec 32) 4 i6 i8
    let i10 ← pure (i2.elem 4 (2 : BitVec 64))
    let i11 ← pure (Zig.shr false p1 (16 : BitVec 5))
    let i12 ← pure (i11 &&& (255 : BitVec 32))
    Zig.store (α := BitVec 32) 4 i10 i12
    let i14 ← pure (i2.elem 4 (3 : BitVec 64))
    let i15 ← pure (Zig.shr false p1 (24 : BitVec 5))
    Zig.store (α := BitVec 32) 4 i14 i15
    let i17 ← pure (i2)
    let i18 ← Zig.load (Zig.Vec (BitVec 32) 4) 16 i17
    let i19 ← Zig.Vec.map2M (fun x0 x1 => pure (Zig.gt false x0 x1)) i18 ((⟨#v[(127 : BitVec 32), (127 : BitVec 32), (127 : BitVec 32), (127 : BitVec 32)]⟩) : Zig.Vec (BitVec 32) 4)
    Zig.store (α := Zig.Vec (Bool) 4) 1 p0 i19
    let i21 ← Zig.load (Zig.Vec (Bool) 4) 1 p0
    let i22 ← pure (Zig.Vec.select i21 ((⟨#v[(1 : BitVec 32), (1 : BitVec 32), (1 : BitVec 32), (1 : BitVec 32)]⟩) : Zig.Vec (BitVec 32) 4) ((⟨#v[(0 : BitVec 32), (0 : BitVec 32), (0 : BitVec 32), (0 : BitVec 32)]⟩) : Zig.Vec (BitVec 32) 4))
    let i23 ← pure (Zig.Vec.reduce Zig.addWrap i22)
    pure (.ret i23)) : Zig.MM maskStoreLocals maskStoreExit).run' { (default : maskStoreLocals) with local2 := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v

structure nibSignedLocals where
  deriving Inhabited

inductive nibSignedExit where
  | ret (v : BitVec 4)

def nibSigned (p0 : Nib) : Zig.Result (BitVec 4) := do
  let e ← ((do
    let i1 ← Zig.call (Nib.get_signed p0)
    pure (.ret i1)) : Zig.M nibSignedLocals nibSignedExit).run' (default : nibSignedLocals)
  match e with
  | .ret v => pure v

structure nibArgLocals where
  deriving Inhabited

inductive nibArgExit where
  | ret (v : BitVec 4)

def nibArg (p0 : BitVec 4) : Zig.Result (BitVec 4) := do
  let e ← ((do
    let i1 ← pure (⟨Zig.PackedU.init 1 (p0 : BitVec 4)⟩ : Nib)
    let i2 ← Zig.call (nibSigned i1)
    pure (.ret i2)) : Zig.M nibArgLocals nibArgExit).run' (default : nibArgLocals)
  match e with
  | .ret v => pure v

structure numIntLocals where
  deriving Inhabited

inductive numIntExit where
  | ret (v : BitVec 32)
  | br4

def numInt (p0 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.load (Num) 4 p0
    let i2 ← pure (Num.tag i1)
    let i3 ← pure (i2 == NumTag.int)
    match ← ((do
      if i3 then (do
        pure .br4)
      else (do
        throw .panic)) : Zig.MM numIntLocals numIntExit) with
    | .br4 => (do
      let i9 ← pure (p0.add 0)
      let i10 ← Zig.load (BitVec 32) 4 i9
      pure (.ret i10))
    | e => pure e) : Zig.MM numIntLocals numIntExit).run' (default : numIntLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure setNumLocals where
  deriving Inhabited

inductive setNumExit where
  | ret
  | br3

def setNum (p0 : Zig.Ptr) (p1 : Bool) (p2 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    match ← ((do
      if p1 then (do
        Zig.store (α := NumTag) 1 (p0.add 4) NumTag.int
        let i6 ← pure (p0.add 0)
        Zig.store (α := BitVec 32) 4 i6 p2
        pure .br3)
      else (do
        Zig.store (α := NumTag) 1 (p0.add 4) NumTag.small
        let i10 ← pure (p0.add 0)
        let i11 ← pure (Zig.trunc 8 p2)
        Zig.store (α := BitVec 8) 1 i10 i11
        pure .br3)) : Zig.MM setNumLocals setNumExit) with
    | .br3 => (do
      pure .ret)
    | e => pure e) : Zig.MM setNumLocals setNumExit).run' (default : setNumLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure numRoundTripLocals where
  n : Zig.Ptr
  deriving Inhabited

inductive numRoundTripExit where
  | ret (v : BitVec 32)

def numRoundTrip (p0 : Bool) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s2 ← Zig.allocStack 8 4
  let e ← ((do
    let i2 ← pure (← get).n
    Zig.storeUndef (Num) 4 i2
    let _i4 ← Zig.callM (setNum i2 p0 p1)
    let i5 ← pure (i2)
    let i6 ← Zig.callM (numInt i5)
    pure (.ret i6)) : Zig.MM numRoundTripLocals numRoundTripExit).run' { (default : numRoundTripLocals) with n := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v

structure parentOfXLocals where
  deriving Inhabited

inductive parentOfXExit where
  | ret (v : Zig.Ptr)

def parentOfX (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.checkParent 8 4 (p0.add (-(0 : Int))) >>= fun _ => pure (p0.add (-(0 : Int))))
    pure (.ret i1)) : Zig.MM parentOfXLocals parentOfXExit).run' (default : parentOfXLocals)
  match e with
  | .ret v => pure v

structure parentOfYLocals where
  deriving Inhabited

inductive parentOfYExit where
  | ret (v : Zig.Ptr)

def parentOfY (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.checkParent 8 4 (p0.add (-(4 : Int))) >>= fun _ => pure (p0.add (-(4 : Int))))
    pure (.ret i1)) : Zig.MM parentOfYLocals parentOfYExit).run' (default : parentOfYLocals)
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
        let i14 ← Zig.callM (Zig.checkAddr 4 true (p0).toNat >>= fun _ => Zig.ptrFromAddr (p0).toNat)
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
        let i15 ← Zig.callM (Zig.checkAddr 4 true (i1).toNat >>= fun _ => Zig.ptrFromAddr (i1).toNat)
        pure (.ret i15))
      | e => pure e)
    | e => pure e) : Zig.MM ptrRoundTripLocals ptrRoundTripExit).run' (default : ptrRoundTripLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure readHeaderLocals where
  deriving Inhabited

inductive readHeaderExit where
  | ret (v : Header)

def readHeader (p0 : Zig.Slice) : Zig.MemM (Header) := do
  let e ← ((do
    let i1 ← pure p0.ptr
    let i2 ← pure (i1)
    let i3 ← Zig.load (Header) 1 i2
    pure (.ret i3)) : Zig.MM readHeaderLocals readHeaderExit).run' (default : readHeaderLocals)
  match e with
  | .ret v => pure v

structure regSignedLocals where
  local1 : Reg
  deriving Inhabited

inductive regSignedExit where
  | ret (v : BitVec 8)

def regSigned (p0 : BitVec 8) : Zig.Result (BitVec 8) := do
  let e ← ((do
    modify (fun s => { s with local1 := (Reg.modify_raw (fun _ => p0) s.local1) })
    let i5 ← pure ((← get).local1)
    let i6 ← Zig.call (Reg.get_signed i5)
    pure (.ret i6)) : Zig.M regSignedLocals regSignedExit).run' (default : regSignedLocals)
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

structure setHalfLocals where
  deriving Inhabited

inductive setHalfExit where
  | ret (v : BitVec 32)

def setHalf (p0 : Zig.Ptr) (p1 : BitVec 16) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i2 ← pure (p0.add 0)
    Zig.store (α := BitVec 16) 2 i2 p1
    let i4 ← pure (p0.add 0)
    let i5 ← Zig.load (BitVec 32) 4 i4
    pure (.ret i5)) : Zig.MM setHalfLocals setHalfExit).run' (default : setHalfLocals)
  match e with
  | .ret v => pure v

structure setModeLocals where
  f : Flags
  deriving Inhabited

inductive setModeExit where
  | ret (v : BitVec 8)

def setMode (p0 : BitVec 8) (p1 : BitVec 2) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i3 ← Zig.Packed.ofBits? (α := Flags) p0
    modify (fun s => { s with f := i3 })
    modify (fun s => { s with f := { s.f with mode := p1 } })
    let i7 ← pure ((← get).f)
    let i8 ← pure (Zig.Packed.toBits i7)
    pure (.ret i8)) : Zig.M setModeLocals setModeExit).run' (default : setModeLocals)
  match e with
  | .ret v => pure v

structure setNibLocals where
  deriving Inhabited

inductive setNibExit where
  | ret (v : BitVec 4)

def setNib (p0 : Zig.Ptr) (p1 : BitVec 4) : Zig.MemM (BitVec 4) := do
  let e ← ((do
    let i2 ← pure (p0.add 0)
    Zig.store (α := BitVec 4) 1 i2 p1
    let i4 ← pure (p0.add 0)
    let i5 ← Zig.load (BitVec 4) 1 i4
    pure (.ret i5)) : Zig.MM setNibLocals setNibExit).run' (default : setNibLocals)
  match e with
  | .ret v => pure v

structure setRegFlagsLocals where
  deriving Inhabited

inductive setRegFlagsExit where
  | ret (v : BitVec 8)

def setRegFlags (p0 : Zig.Ptr) (p1 : Flags) : Zig.MemM (BitVec 8) := do
  let e ← ((do
    let i2 ← pure (p0.add 0)
    Zig.store (α := Flags) 1 i2 p1
    let i4 ← pure (p0.add 0)
    let i5 ← Zig.load (BitVec 8) 1 i4
    pure (.ret i5)) : Zig.MM setRegFlagsLocals setRegFlagsExit).run' (default : setRegFlagsLocals)
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

structure wordArgLocals where
  deriving Inhabited

inductive wordArgExit where
  | ret (v : BitVec 8)

def wordArg (p0 : BitVec 32) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i1 ← pure (⟨Zig.Raw.init 4 (p0 : BitVec 32)⟩ : Word)
    let i2 ← Zig.call (lowByte i1)
    pure (.ret i2)) : Zig.M wordArgLocals wordArgExit).run' (default : wordArgLocals)
  match e with
  | .ret v => pure v

structure wordOfLocals where
  local1 : Word
  deriving Inhabited

inductive wordOfExit where
  | ret (v : Word)

def wordOf (p0 : BitVec 32) : Zig.Result (Word) := do
  let e ← ((do
    modify (fun s => { s with local1 := (Word.modify_int (fun _ => p0) s.local1) })
    pure (.ret (← get).local1)) : Zig.M wordOfLocals wordOfExit).run' (default : wordOfLocals)
  match e with
  | .ret v => pure v

structure wordByteLocals where
  w : Word
  deriving Inhabited

inductive wordByteExit where
  | ret (v : BitVec 8)
  | br9

def wordByte (p0 : BitVec 32) (p1 : BitVec 2) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i3 ← Zig.call (wordOf p0)
    modify (fun s => { s with w := i3 })
    let i6 ← pure ((← Zig.call (Word.get_bytes (← get).w)))
    let i7 ← Zig.intCast false false 64 p1
    let i8 ← pure (Zig.lt false i7 (4 : BitVec 64))
    match ← ((do
      if i8 then (do
        pure .br9)
      else (do
        throw .outOfBounds)) : Zig.M wordByteLocals wordByteExit) with
    | .br9 => (do
      let i14 ← Zig.call (Zig.vindex i6 i7)
      pure (.ret i14))
    | e => pure e) : Zig.M wordByteLocals wordByteExit).run' (default : wordByteLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure wordHalfLocals where
  deriving Inhabited

inductive wordHalfExit where
  | ret (v : BitVec 16)

def wordHalf (p0 : BitVec 32) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← Zig.call (wordOf p0)
    let i2 ← Zig.call (Word.get_half i1)
    pure (.ret i2)) : Zig.M wordHalfLocals wordHalfExit).run' (default : wordHalfLocals)
  match e with
  | .ret v => pure v

structure writeTableLocals where
  deriving Inhabited

inductive writeTableExit where
  | ret (v : BitVec 32)
  | br3

def writeTable (p0 : BitVec 64) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i2 ← pure (Zig.lt false p0 (3 : BitVec 64))
    match ← ((do
      if i2 then (do
        pure .br3)
      else (do
        throw .outOfBounds)) : Zig.MM writeTableLocals writeTableExit) with
    | .br3 => (do
      let i8 ← pure ((⟨some 3, 0⟩ : Zig.Ptr).elem 4 p0)
      let i9 ← pure (i8)
      Zig.store (α := BitVec 32) 4 i9 p1
      let i11 ← Zig.callR (Zig.vindex (#v[(10 : BitVec 32), (20 : BitVec 32), (30 : BitVec 32)] : Vector (BitVec 32) 3) p0)
      pure (.ret i11))
    | e => pure e) : Zig.MM writeTableLocals writeTableExit).run' (default : writeTableLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end Layout