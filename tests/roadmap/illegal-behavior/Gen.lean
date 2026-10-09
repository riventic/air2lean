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

structure forLenLocals where
  sum : BitVec 32
  local4 : BitVec 64
  deriving Inhabited

inductive forLenExit where
  | ret (v : BitVec 32)
  | br11
  | br8
  | rep9

def forLen.again9 : forLenExit → Bool
  | .rep9 => true
  | _ => false

def forLen.loop9 (p0 : Array (BitVec 32)) (p1 : Array (BitVec 32)) (i6 : BitVec 64) : Zig.M forLenLocals forLenExit := do
  let i10 ← pure ((← get).local4)
  match ← ((do
    let i12 ← pure (i10)
    let i13 ← pure (i6)
    let i14 ← pure (Zig.lt false i12 i13)
    if i14 then (do
      let i16 ← Zig.call (Zig.index p0 i10)
      let i17 ← Zig.call (Zig.index p1 i10)
      let i18 ← pure ((← get).sum)
      let i19 ← pure (Zig.addWrap i16 i17)
      let i20 ← pure (Zig.addWrap i18 i19)
      modify (fun s => { s with sum := i20 })
      pure .br11)
    else (do
      pure .br8)) : Zig.M forLenLocals forLenExit) with
  | .br11 => (do
    let i24 ← Zig.add false i10 (1 : BitVec 64)
    modify (fun s => { s with local4 := i24 })
    pure .rep9)
  | e => pure e

def forLen (p0 : Array (BitVec 32)) (p1 : Array (BitVec 32)) : Zig.Result (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with sum := (0 : BitVec 32) })
    modify (fun s => { s with local4 := (0 : BitVec 64) })
    let i6 ← pure (Zig.len p0)
    let _i7 ← Zig.call (Zig.forLen (Zig.len p1) i6)
    match ← ((do
      Zig.loop (forLen.loop9 p0 p1 i6) forLen.again9) : Zig.M forLenLocals forLenExit) with
    | .br8 => (do
      let i27 ← pure ((← get).sum)
      pure (.ret i27))
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
  | br13
  | br10
  | rep11

def forLenMem.again11 : forLenMemExit → Bool
  | .rep11 => true
  | _ => false

def forLenMem.loop11 (i6 : Zig.Slice) (i7 : Zig.Slice) (i8 : BitVec 64) : Zig.MM forLenMemLocals forLenMemExit := do
  let i12 ← pure ((← get).local4)
  match ← ((do
    let i14 ← pure (i12)
    let i15 ← pure (i8)
    let i16 ← pure (Zig.lt false i14 i15)
    if i16 then (do
      let i18 ← Zig.callM (Zig.checkIndex i6 i12 >>= fun _ => Zig.load (BitVec 32) 4 (i6.ptr.elem 4 i12))
      let i19 ← Zig.callM (Zig.checkIndex i7 i12 >>= fun _ => Zig.load (BitVec 32) 4 (i7.ptr.elem 4 i12))
      let i20 ← pure ((← get).sum)
      let i21 ← pure (Zig.addWrap i18 i19)
      let i22 ← pure (Zig.addWrap i20 i21)
      modify (fun s => { s with sum := i22 })
      pure .br13)
    else (do
      pure .br10)) : Zig.MM forLenMemLocals forLenMemExit) with
  | .br13 => (do
    let i26 ← Zig.add false i12 (1 : BitVec 64)
    modify (fun s => { s with local4 := i26 })
    pure .rep11)
  | e => pure e

def forLenMem (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with sum := (0 : BitVec 32) })
    modify (fun s => { s with local4 := (0 : BitVec 64) })
    let i6 ← Zig.load (Zig.Slice) 8 p0
    let i7 ← Zig.load (Zig.Slice) 8 p1
    let i8 ← pure i6.len
    let _i9 ← Zig.callR (Zig.forLen i7.len i8)
    match ← ((do
      Zig.loop (forLenMem.loop11 i6 i7 i8) forLenMem.again11) : Zig.MM forLenMemLocals forLenMemExit) with
    | .br10 => (do
      let i29 ← pure ((← get).sum)
      pure (.ret i29))
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
  | br10
  | br7
  | rep8

def forRange.again8 : forRangeExit → Bool
  | .rep8 => true
  | _ => false

def forRange.loop8 (p0 : Array (BitVec 32)) (i6 : BitVec 64) : Zig.M forRangeLocals forRangeExit := do
  let i9 ← pure ((← get).local4)
  match ← ((do
    let i11 ← pure (i9)
    let i12 ← pure (i6)
    let i13 ← pure (Zig.lt false i11 i12)
    if i13 then (do
      let i15 ← Zig.call (Zig.index p0 i9)
      let i16 ← pure ((← get).sum)
      let i17 ← pure (Zig.trunc 32 i9)
      let i18 ← pure (Zig.addWrap i15 i17)
      let i19 ← pure (Zig.addWrap i16 i18)
      modify (fun s => { s with sum := i19 })
      pure .br10)
    else (do
      pure .br7)) : Zig.M forRangeLocals forRangeExit) with
  | .br10 => (do
    let i23 ← Zig.add false i9 (1 : BitVec 64)
    modify (fun s => { s with local4 := i23 })
    pure .rep8)
  | e => pure e

def forRange (p0 : Array (BitVec 32)) (p1 : BitVec 64) : Zig.Result (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with sum := (0 : BitVec 32) })
    modify (fun s => { s with local4 := (0 : BitVec 64) })
    let i6 ← pure (Zig.len p0)
    match ← ((do
      Zig.loop (forRange.loop8 p0 i6) forRange.again8) : Zig.M forRangeLocals forRangeExit) with
    | .br7 => (do
      let i26 ← pure ((← get).sum)
      pure (.ret i26))
    | e => pure e) : Zig.M forRangeLocals forRangeExit).run' (default : forRangeLocals)
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