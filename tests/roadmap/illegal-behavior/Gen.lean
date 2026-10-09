-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace IllegalBehavior

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