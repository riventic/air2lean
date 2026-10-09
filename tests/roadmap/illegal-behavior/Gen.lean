-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace IllegalBehavior

structure S where
  a : BitVec 32
  b : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc S where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.a), (4, Zig.Enc.encode v.b)]
  decode bs := do pure { a := ← Zig.Enc.decodeAt bs 0, b := ← Zig.Enc.decodeAt bs 4 }

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

structure copyLenUnsafeLocals where
  deriving Inhabited

inductive copyLenUnsafeExit where
  | ret

def copyLenUnsafe (p0 : Zig.Slice) (p1 : Zig.Slice) : Zig.MemM (Unit) := do
  let e ← ((do
    let _i2 ← pure p0.len
    let _i3 ← pure p1.len
    let i4 ← pure p1.ptr
    Zig.callM (Zig.memcpy 1 1 1 p0.ptr i4 p0.len p1.len)
    pure .ret) : Zig.MM copyLenUnsafeLocals copyLenUnsafeExit).run' (default : copyLenUnsafeLocals)
  match e with
  | .ret => pure ()

structure copyOverlapUnsafeLocals where
  deriving Inhabited

inductive copyOverlapUnsafeExit where
  | ret

def copyOverlapUnsafe (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← Zig.add false p1 (1 : BitVec 64)
    let i3 ← pure (p0.elem 1 (1 : BitVec 64))
    let i4 ← Zig.sub false i2 (1 : BitVec 64)
    let i5 ← pure (⟨i3, i4⟩ : Zig.Slice)
    let i6 ← pure (p0.elem 1 (0 : BitVec 64))
    let i7 ← Zig.sub false p1 (0 : BitVec 64)
    let i8 ← pure (⟨i6, i7⟩ : Zig.Slice)
    let _i9 ← pure i5.len
    let _i10 ← pure i8.len
    let i11 ← pure i8.ptr
    Zig.callM (Zig.memcpy 1 1 1 i5.ptr i11 i5.len i8.len)
    pure .ret) : Zig.MM copyOverlapUnsafeLocals copyOverlapUnsafeExit).run' (default : copyOverlapUnsafeLocals)
  match e with
  | .ret => pure ()

structure divExactIntUnsafeLocals where
  deriving Inhabited

inductive divExactIntUnsafeExit where
  | ret (v : BitVec 32)

def divExactIntUnsafe (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i2 ← Zig.divExact true p0 p1
    pure (.ret i2)) : Zig.M divExactIntUnsafeLocals divExactIntUnsafeExit).run' (default : divExactIntUnsafeLocals)
  match e with
  | .ret v => pure v

structure divExactLanesLocals where
  deriving Inhabited

inductive divExactLanesExit where
  | ret (v : Zig.Vec (Zig.F64) 2)
  | br6

def divExactLanes (p0 : Zig.Vec (Zig.F64) 2) (p1 : Zig.Vec (Zig.F64) 2) : Zig.Result (Zig.Vec (Zig.F64) 2) := do
  let e ← ((do
    let i2 ← Zig.Vec.map2M (fun x0 x1 => Zig.Float.divExactTrunc x0 x1 (Zig.Float.div x0 x1)) p0 p1
    let i3 ← Zig.Vec.mapM (fun x0 => Zig.Float.floorChk x0) i2
    let i4 ← Zig.Vec.map2M (fun x0 x1 => pure (Zig.Float.eq x0 x1)) i2 i3
    let i5 ← pure (Zig.Vec.reduce (· && ·) i4)
    match ← ((do
      if i5 then (do
        pure .br6)
      else (do
        throw .panic)) : Zig.M divExactLanesLocals divExactLanesExit) with
    | .br6 => (do
      pure (.ret i2))
    | e => pure e) : Zig.M divExactLanesLocals divExactLanesExit).run' (default : divExactLanesLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure divExactSafeLocals where
  deriving Inhabited

inductive divExactSafeExit where
  | ret (v : Zig.F64)
  | br5

def divExactSafe (p0 : Zig.F64) (p1 : Zig.F64) : Zig.Result (Zig.F64) := do
  let e ← ((do
    let i2 ← Zig.Float.divExactTrunc p0 p1 (Zig.Float.div p0 p1)
    let i3 ← Zig.Float.floorChk i2
    let i4 ← pure (Zig.Float.eq i2 i3)
    match ← ((do
      if i4 then (do
        pure .br5)
      else (do
        throw .panic)) : Zig.M divExactSafeLocals divExactSafeExit) with
    | .br5 => (do
      pure (.ret i2))
    | e => pure e) : Zig.M divExactSafeLocals divExactSafeExit).run' (default : divExactSafeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure divExactUnsafeLocals where
  deriving Inhabited

inductive divExactUnsafeExit where
  | ret (v : Zig.F64)

def divExactUnsafe (p0 : Zig.F64) (p1 : Zig.F64) : Zig.Result (Zig.F64) := do
  let e ← ((do
    let i2 ← Zig.Float.divExactChk p0 p1 (Zig.Float.div p0 p1)
    pure (.ret i2)) : Zig.M divExactUnsafeLocals divExactUnsafeExit).run' (default : divExactUnsafeLocals)
  match e with
  | .ret v => pure v

structure forArrayLocals where
  sum : BitVec 32
  local4 : BitVec 64
  deriving Inhabited

inductive forArrayExit where
  | ret (v : BitVec 32)
  | br8
  | br15
  | br12
  | rep13

def forArray.again13 : forArrayExit → Bool
  | .rep13 => true
  | _ => false

def forArray.loop13 (p0 : Zig.Slice) (p1 : Zig.Ptr) : Zig.MM forArrayLocals forArrayExit := do
  let i14 ← pure ((← get).local4)
  match ← ((do
    let i16 ← pure (i14)
    let i17 ← pure (Zig.lt false i16 (3 : BitVec 64))
    if i17 then (do
      let i19 ← Zig.callM (Zig.checkIndex p0 i14 >>= fun _ => Zig.load (BitVec 32) 4 (p0.ptr.elem 4 i14))
      let i20 ← Zig.callM (Zig.load (BitVec 32) 4 (p1.elem 4 i14))
      let i21 ← pure ((← get).sum)
      let i22 ← pure (Zig.addWrap i19 i20)
      let i23 ← pure (Zig.addWrap i21 i22)
      modify (fun s => { s with sum := i23 })
      pure .br15)
    else (do
      pure .br12)) : Zig.MM forArrayLocals forArrayExit) with
  | .br15 => (do
    let i27 ← Zig.add false i14 (1 : BitVec 64)
    modify (fun s => { s with local4 := i27 })
    pure .rep13)
  | e => pure e

def forArray (p0 : Zig.Slice) (p1 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with sum := (0 : BitVec 32) })
    modify (fun s => { s with local4 := (0 : BitVec 64) })
    let i6 ← pure p0.len
    let i7 ← pure ((3 : BitVec 64) == i6)
    match ← ((do
      if i7 then (do
        pure .br8)
      else (do
        throw .illegal)) : Zig.MM forArrayLocals forArrayExit) with
    | .br8 => (do
      match ← ((do
        Zig.loop (forArray.loop13 p0 p1) forArray.again13) : Zig.MM forArrayLocals forArrayExit) with
      | .br12 => (do
        let i30 ← pure ((← get).sum)
        pure (.ret i30))
      | e => pure e)
    | e => pure e) : Zig.MM forArrayLocals forArrayExit).run' (default : forArrayLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure forLenLocals where
  sum : BitVec 32
  local4 : BitVec 64
  deriving Inhabited

inductive forLenExit where
  | ret (v : BitVec 32)
  | br9
  | br16
  | br13
  | rep14

def forLen.again14 : forLenExit → Bool
  | .rep14 => true
  | _ => false

def forLen.loop14 (p0 : Array (BitVec 32)) (p1 : Array (BitVec 32)) (i6 : BitVec 64) : Zig.M forLenLocals forLenExit := do
  let i15 ← pure ((← get).local4)
  match ← ((do
    let i17 ← pure (i15)
    let i18 ← pure (i6)
    let i19 ← pure (Zig.lt false i17 i18)
    if i19 then (do
      let i21 ← Zig.call (Zig.index p0 i15)
      let i22 ← Zig.call (Zig.index p1 i15)
      let i23 ← pure ((← get).sum)
      let i24 ← pure (Zig.addWrap i21 i22)
      let i25 ← pure (Zig.addWrap i23 i24)
      modify (fun s => { s with sum := i25 })
      pure .br16)
    else (do
      pure .br13)) : Zig.M forLenLocals forLenExit) with
  | .br16 => (do
    let i29 ← Zig.add false i15 (1 : BitVec 64)
    modify (fun s => { s with local4 := i29 })
    pure .rep14)
  | e => pure e

def forLen (p0 : Array (BitVec 32)) (p1 : Array (BitVec 32)) : Zig.Result (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with sum := (0 : BitVec 32) })
    modify (fun s => { s with local4 := (0 : BitVec 64) })
    let i6 ← pure (Zig.len p0)
    let i7 ← pure (Zig.len p1)
    let i8 ← pure (i6 == i7)
    match ← ((do
      if i8 then (do
        pure .br9)
      else (do
        throw .illegal)) : Zig.M forLenLocals forLenExit) with
    | .br9 => (do
      match ← ((do
        Zig.loop (forLen.loop14 p0 p1 i6) forLen.again14) : Zig.M forLenLocals forLenExit) with
      | .br13 => (do
        let i32 ← pure ((← get).sum)
        pure (.ret i32))
      | e => pure e)
    | e => pure e) : Zig.M forLenLocals forLenExit).run' (default : forLenLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure forLenMemLocals where
  sum : BitVec 32
  local4 : BitVec 64
  deriving Inhabited

inductive forLenMemExit where
  | ret (v : BitVec 32)
  | br11
  | br18
  | br15
  | rep16

def forLenMem.again16 : forLenMemExit → Bool
  | .rep16 => true
  | _ => false

def forLenMem.loop16 (i6 : Zig.Slice) (i7 : Zig.Slice) (i8 : BitVec 64) : Zig.MM forLenMemLocals forLenMemExit := do
  let i17 ← pure ((← get).local4)
  match ← ((do
    let i19 ← pure (i17)
    let i20 ← pure (i8)
    let i21 ← pure (Zig.lt false i19 i20)
    if i21 then (do
      let i23 ← Zig.callM (Zig.checkIndex i6 i17 >>= fun _ => Zig.load (BitVec 32) 4 (i6.ptr.elem 4 i17))
      let i24 ← Zig.callM (Zig.checkIndex i7 i17 >>= fun _ => Zig.load (BitVec 32) 4 (i7.ptr.elem 4 i17))
      let i25 ← pure ((← get).sum)
      let i26 ← pure (Zig.addWrap i23 i24)
      let i27 ← pure (Zig.addWrap i25 i26)
      modify (fun s => { s with sum := i27 })
      pure .br18)
    else (do
      pure .br15)) : Zig.MM forLenMemLocals forLenMemExit) with
  | .br18 => (do
    let i31 ← Zig.add false i17 (1 : BitVec 64)
    modify (fun s => { s with local4 := i31 })
    pure .rep16)
  | e => pure e

def forLenMem (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with sum := (0 : BitVec 32) })
    modify (fun s => { s with local4 := (0 : BitVec 64) })
    let i6 ← Zig.load (Zig.Slice) 8 p0
    let i7 ← Zig.load (Zig.Slice) 8 p1
    let i8 ← pure i6.len
    let i9 ← pure i7.len
    let i10 ← pure (i8 == i9)
    match ← ((do
      if i10 then (do
        pure .br11)
      else (do
        throw .illegal)) : Zig.MM forLenMemLocals forLenMemExit) with
    | .br11 => (do
      match ← ((do
        Zig.loop (forLenMem.loop16 i6 i7 i8) forLenMem.again16) : Zig.MM forLenMemLocals forLenMemExit) with
      | .br15 => (do
        let i34 ← pure ((← get).sum)
        pure (.ret i34))
      | e => pure e)
    | e => pure e) : Zig.MM forLenMemLocals forLenMemExit).run' (default : forLenMemLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure forRangeLocals where
  sum : BitVec 32
  local4 : BitVec 64
  deriving Inhabited

inductive forRangeExit where
  | ret (v : BitVec 32)
  | br8
  | br15
  | br12
  | rep13

def forRange.again13 : forRangeExit → Bool
  | .rep13 => true
  | _ => false

def forRange.loop13 (p0 : Array (BitVec 32)) (i6 : BitVec 64) : Zig.M forRangeLocals forRangeExit := do
  let i14 ← pure ((← get).local4)
  match ← ((do
    let i16 ← pure (i14)
    let i17 ← pure (i6)
    let i18 ← pure (Zig.lt false i16 i17)
    if i18 then (do
      let i20 ← Zig.call (Zig.index p0 i14)
      let i21 ← pure ((← get).sum)
      let i22 ← pure (Zig.trunc 32 i14)
      let i23 ← pure (Zig.addWrap i20 i22)
      let i24 ← pure (Zig.addWrap i21 i23)
      modify (fun s => { s with sum := i24 })
      pure .br15)
    else (do
      pure .br12)) : Zig.M forRangeLocals forRangeExit) with
  | .br15 => (do
    let i28 ← Zig.add false i14 (1 : BitVec 64)
    modify (fun s => { s with local4 := i28 })
    pure .rep13)
  | e => pure e

def forRange (p0 : Array (BitVec 32)) (p1 : BitVec 64) : Zig.Result (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with sum := (0 : BitVec 32) })
    modify (fun s => { s with local4 := (0 : BitVec 64) })
    let i6 ← pure (Zig.len p0)
    let i7 ← pure (i6 == p1)
    match ← ((do
      if i7 then (do
        pure .br8)
      else (do
        throw .illegal)) : Zig.M forRangeLocals forRangeExit) with
    | .br8 => (do
      match ← ((do
        Zig.loop (forRange.loop13 p0 i6) forRange.again13) : Zig.M forRangeLocals forRangeExit) with
      | .br12 => (do
        let i31 ← pure ((← get).sum)
        pure (.ret i31))
      | e => pure e)
    | e => pure e) : Zig.M forRangeLocals forRangeExit).run' (default : forRangeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure forRangeFromLocals where
  sum : BitVec 32
  local5 : BitVec 64
  deriving Inhabited

inductive forRangeFromExit where
  | ret (v : BitVec 32)
  | br10
  | br17
  | br14
  | rep15

def forRangeFrom.again15 : forRangeFromExit → Bool
  | .rep15 => true
  | _ => false

def forRangeFrom.loop15 (p0 : Array (BitVec 32)) (p1 : BitVec 64) (i7 : BitVec 64) : Zig.M forRangeFromLocals forRangeFromExit := do
  let i16 ← pure ((← get).local5)
  match ← ((do
    let i18 ← pure (i16)
    let i19 ← pure (i7)
    let i20 ← pure (Zig.lt false i18 i19)
    if i20 then (do
      let i22 ← Zig.call (Zig.index p0 i16)
      let i23 ← Zig.add false p1 i16
      let i24 ← pure ((← get).sum)
      let i25 ← pure (Zig.trunc 32 i23)
      let i26 ← pure (Zig.addWrap i22 i25)
      let i27 ← pure (Zig.addWrap i24 i26)
      modify (fun s => { s with sum := i27 })
      pure .br17)
    else (do
      pure .br14)) : Zig.M forRangeFromLocals forRangeFromExit) with
  | .br17 => (do
    let i31 ← Zig.add false i16 (1 : BitVec 64)
    modify (fun s => { s with local5 := i31 })
    pure .rep15)
  | e => pure e

def forRangeFrom (p0 : Array (BitVec 32)) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.Result (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with sum := (0 : BitVec 32) })
    modify (fun s => { s with local5 := (0 : BitVec 64) })
    let i7 ← pure (Zig.len p0)
    let i8 ← Zig.sub false p2 p1
    let i9 ← pure (i7 == i8)
    match ← ((do
      if i9 then (do
        pure .br10)
      else (do
        throw .illegal)) : Zig.M forRangeFromLocals forRangeFromExit) with
    | .br10 => (do
      match ← ((do
        Zig.loop (forRangeFrom.loop15 p0 p1 i7) forRangeFrom.again15) : Zig.M forRangeFromLocals forRangeFromExit) with
      | .br14 => (do
        let i34 ← pure ((← get).sum)
        pure (.ret i34))
      | e => pure e)
    | e => pure e) : Zig.M forRangeFromLocals forRangeFromExit).run' (default : forRangeFromLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure itemUnsafeLocals where
  deriving Inhabited

inductive itemUnsafeExit where
  | ret (v : BitVec 32)

def itemUnsafe (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i2 ← Zig.load (Zig.Slice) 8 p0
    let i3 ← Zig.callM (Zig.checkIndex i2 p1 >>= fun _ => Zig.load (BitVec 32) 4 (i2.ptr.elem 4 p1))
    pure (.ret i3)) : Zig.MM itemUnsafeLocals itemUnsafeExit).run' (default : itemUnsafeLocals)
  match e with
  | .ret v => pure v

structure parentOfLocals where
  deriving Inhabited

inductive parentOfExit where
  | ret (v : Zig.Ptr)

def parentOf (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.checkParent 8 4 (p0.add (-(4 : Int))) >>= fun _ => pure (p0.add (-(4 : Int))))
    let i2 ← pure (i1)
    pure (.ret i2)) : Zig.MM parentOfLocals parentOfExit).run' (default : parentOfLocals)
  match e with
  | .ret v => pure v

structure sentinelBytesLocals where
  deriving Inhabited

inductive sentinelBytesExit where
  | ret (v : Zig.Slice)

def sentinelBytes (p0 : Zig.Slice) (p1 : BitVec 64) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    let i2 ← pure p0.ptr
    let i3 ← pure (i2.elem 1 (0 : BitVec 64))
    let i4 ← Zig.sub false p1 (0 : BitVec 64)
    let i5 ← Zig.callM (Zig.checkSliceEnd p0.len (0 : BitVec 64) i4 1 >>= fun _ => Zig.checkSentinelByte i3 i4 (0 : BitVec 8) >>= fun _ => pure (⟨i3, i4⟩ : Zig.Slice))
    pure (.ret i5)) : Zig.MM sentinelBytesLocals sentinelBytesExit).run' (default : sentinelBytesLocals)
  match e with
  | .ret v => pure v

structure shl24UnsafeLocals where
  deriving Inhabited

inductive shl24UnsafeExit where
  | ret (v : BitVec 24)

def shl24Unsafe (p0 : BitVec 24) (p1 : BitVec 5) : Zig.Result (BitVec 24) := do
  let e ← ((do
    let i2 ← Zig.shlChk p0 p1
    pure (.ret i2)) : Zig.M shl24UnsafeLocals shl24UnsafeExit).run' (default : shl24UnsafeLocals)
  match e with
  | .ret v => pure v

structure shlExactUnsafeLocals where
  deriving Inhabited

inductive shlExactUnsafeExit where
  | ret (v : BitVec 32)

def shlExactUnsafe (p0 : BitVec 32) (p1 : BitVec 5) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i2 ← Zig.shlExact false p0 p1
    pure (.ret i2)) : Zig.M shlExactUnsafeLocals shlExactUnsafeExit).run' (default : shlExactUnsafeLocals)
  match e with
  | .ret v => pure v

structure shr24UnsafeLocals where
  deriving Inhabited

inductive shr24UnsafeExit where
  | ret (v : BitVec 24)

def shr24Unsafe (p0 : BitVec 24) (p1 : BitVec 5) : Zig.Result (BitVec 24) := do
  let e ← ((do
    let i2 ← Zig.shrChk false p0 p1
    pure (.ret i2)) : Zig.M shr24UnsafeLocals shr24UnsafeExit).run' (default : shr24UnsafeLocals)
  match e with
  | .ret v => pure v

structure sliceArrayLocals where
  deriving Inhabited

inductive sliceArrayExit where
  | ret (v : Zig.Slice)

def sliceArray (p0 : Zig.Ptr) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    let i3 ← pure (p0)
    let i4 ← pure (i3.elem 4 p1)
    let i5 ← Zig.sub false p2 p1
    let i6 ← Zig.callM (Zig.checkSliceEnd (4 : BitVec 64) p1 i5 0 >>= fun _ => pure (⟨i4, i5⟩ : Zig.Slice))
    pure (.ret i6)) : Zig.MM sliceArrayLocals sliceArrayExit).run' (default : sliceArrayLocals)
  match e with
  | .ret v => pure v

structure sliceEndLocals where
  deriving Inhabited

inductive sliceEndExit where
  | ret (v : Zig.Slice)

def sliceEnd (p0 : Zig.Ptr) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    let i3 ← Zig.load (Zig.Slice) 8 p0
    let i4 ← pure i3.ptr
    let i5 ← pure (i4.elem 4 p1)
    let i6 ← Zig.sub false p2 p1
    let i7 ← Zig.callM (Zig.checkSliceEnd i3.len p1 i6 0 >>= fun _ => pure (⟨i5, i6⟩ : Zig.Slice))
    pure (.ret i7)) : Zig.MM sliceEndLocals sliceEndExit).run' (default : sliceEndLocals)
  match e with
  | .ret v => pure v

structure toIntSafeLocals where
  deriving Inhabited

inductive toIntSafeExit where
  | ret (v : BitVec 32)

def toIntSafe (p0 : Zig.F64) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.Float.toInt true 32 true p0
    pure (.ret i1)) : Zig.M toIntSafeLocals toIntSafeExit).run' (default : toIntSafeLocals)
  match e with
  | .ret v => pure v

structure toIntUnsafeLocals where
  deriving Inhabited

inductive toIntUnsafeExit where
  | ret (v : BitVec 32)

def toIntUnsafe (p0 : Zig.F64) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.Float.toInt true 32 false p0
    pure (.ret i1)) : Zig.M toIntUnsafeLocals toIntUnsafeExit).run' (default : toIntUnsafeLocals)
  match e with
  | .ret v => pure v

end IllegalBehavior