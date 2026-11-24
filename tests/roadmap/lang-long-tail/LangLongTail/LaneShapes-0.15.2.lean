-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.16-musl","zig_version":"0.15.2"}}
import ZigLean


namespace LaneShapes

structure Holder where
  p : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Holder where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.p)]
  decode bs := do pure { p := ← Zig.Enc.decodeAt bs 0 }

structure Framed where
  a : BitVec 8
  v : Zig.Vec (BitVec 9) 4
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Framed where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(8, Zig.Enc.encode v.a), (0, Zig.Enc.encode v.v)]
  decode bs := do pure { a := ← Zig.Enc.decodeAt bs 8, v := ← Zig.Enc.decodeAt bs 0 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: lane_shapes.g
  (Zig.Enc.encode (((⟨#v[(1 : BitVec 9), (2 : BitVec 9), (3 : BitVec 9), (4 : BitVec 9)]⟩) : Zig.Vec (BitVec 9) 4) : Zig.Vec (BitVec 9) 4), 8, .global)]

structure byteLocalLocals where
  v : Zig.Ptr
  deriving Inhabited

inductive byteLocalExit where
  | ret (v : BitVec 32)

def byteLocal (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s2 ← Zig.allocStack 16 16
  let e ← ((do
    let i2 ← pure (← get).v
    let i3 ← pure i2
    Zig.store (α := BitVec 32) 4 i3 p0
    let i5 ← Zig.callM (Zig.ptrProject i2 (·.elem 4 (1 : BitVec 64)))
    let i6 ← pure (Zig.addWrap p0 (1 : BitVec 32))
    Zig.store (α := BitVec 32) 4 i5 i6
    let i8 ← Zig.callM (Zig.ptrProject i2 (·.elem 4 (2 : BitVec 64)))
    let i9 ← pure (Zig.addWrap p0 (2 : BitVec 32))
    Zig.store (α := BitVec 32) 4 i8 i9
    let i11 ← Zig.callM (Zig.ptrProject i2 (·.elem 4 (3 : BitVec 64)))
    let i12 ← pure (Zig.addWrap p0 (3 : BitVec 32))
    Zig.store (α := BitVec 32) 4 i11 i12
    let i14 ← Zig.callM (Zig.ptrProject i2 (·.elem 4 (1 : BitVec 64)))
    let i15 ← Zig.load (BitVec 32) 4 i14
    let i16 ← pure (Zig.addWrap i15 p1)
    Zig.store (α := BitVec 32) 4 i14 i16
    let i18 ← Zig.callM (Zig.ptrProject i2 (·.elem 4 (3 : BitVec 64)))
    Zig.store (α := BitVec 32) 4 i18 p1
    let i20 ← Zig.callM (Zig.load (BitVec 32) 4 (i2.elem 4 (0 : BitVec 64)))
    let i21 ← Zig.load (BitVec 32) 4 i14
    let i22 ← pure (Zig.mulWrap i21 (3 : BitVec 32))
    let i23 ← pure (i20 ^^^ i22)
    let i24 ← Zig.callM (Zig.load (BitVec 32) 4 (i2.elem 4 (2 : BitVec 64)))
    let i25 ← pure (Zig.mulWrap i24 (5 : BitVec 32))
    let i26 ← pure (i23 ^^^ i25)
    let i27 ← Zig.callM (Zig.load (BitVec 32) 4 (i2.elem 4 (3 : BitVec 64)))
    let i28 ← pure (Zig.mulWrap i27 (7 : BitVec 32))
    let i29 ← pure (i26 ^^^ i28)
    pure (.ret i29)) : Zig.MM byteLocalLocals byteLocalExit).run' { (default : byteLocalLocals) with v := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v

attribute [zig_run] byteLocal

structure lanesLocals where
  local1 : Zig.Ptr
  deriving Inhabited

inductive lanesExit where
  | ret (v : Zig.Vec (BitVec 9) 4)

def lanes (p0 : BitVec 32) : Zig.MemM (Zig.Vec (BitVec 9) 4) := do
  let s1 ← Zig.allocStack 8 8
  let e ← ((do
    let i1 ← pure (← get).local1
    let i2 ← pure i1
    let i3 ← pure (Zig.trunc 9 p0)
    Zig.storeLane (α := BitVec 9) 5 8 0 i2 i3
    let i5 ← pure i1
    let i6 ← pure (Zig.shr false p0 (9 : BitVec 5))
    let i7 ← pure (Zig.trunc 9 i6)
    Zig.storeLane (α := BitVec 9) 5 8 9 i5 i7
    let i9 ← pure i1
    let i10 ← pure (Zig.shr false p0 (18 : BitVec 5))
    let i11 ← pure (Zig.trunc 9 i10)
    Zig.storeLane (α := BitVec 9) 5 8 18 i9 i11
    let i13 ← pure i1
    let i14 ← pure (Zig.shr false p0 (27 : BitVec 5))
    let i15 ← pure (Zig.trunc 9 i14)
    Zig.storeLane (α := BitVec 9) 5 8 27 i13 i15
    pure (.ret (← Zig.load (Zig.Vec (BitVec 9) 4) 8 i1))) : Zig.MM lanesLocals lanesExit).run' { (default : lanesLocals) with local1 := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

attribute [zig_run] lanes

structure readConstLocals where
  deriving Inhabited

inductive readConstExit where
  | ret (v : BitVec 9)

def readConst (p0 : Zig.Ptr) : Zig.MemM (BitVec 9) := do
  let e ← ((do
    let i1 ← pure p0
    let i2 ← Zig.loadLane (BitVec 9) 5 8 27 i1
    pure (.ret i2)) : Zig.MM readConstLocals readConstExit).run' (default : readConstLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] readConst

structure constLaneLocals where
  local2 : Zig.Ptr
  deriving Inhabited

inductive constLaneExit where
  | ret (v : BitVec 16)

def constLane (p0 : BitVec 32) : Zig.MemM (BitVec 16) := do
  let s2 ← Zig.allocStack 8 8
  let e ← ((do
    let i1 ← Zig.callM (lanes p0)
    let i2 ← pure (← get).local2
    Zig.store (α := Zig.Vec (BitVec 9) 4) 8 i2 i1
    let i4 ← pure (i2)
    let i5 ← Zig.callM (readConst i4)
    let i6 ← Zig.intCast false false 16 i5 (safe := false)
    pure (.ret i6)) : Zig.MM constLaneLocals constLaneExit).run' { (default : constLaneLocals) with local2 := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v

attribute [zig_run] constLane

structure packLocals where
  deriving Inhabited

inductive packExit where
  | ret (v : BitVec 64)

def pack (p0 : Zig.Vec (BitVec 9) 4) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.call (Zig.vindex p0.lanes (0 : BitVec 64))
    let i2 ← Zig.intCast false false 64 i1 (safe := false)
    let i3 ← Zig.call (Zig.vindex p0.lanes (1 : BitVec 64))
    let i4 ← Zig.intCast false false 64 i3 (safe := false)
    let i5 ← pure (Zig.shl i4 (9 : BitVec 6))
    let i6 ← pure (i2 ||| i5)
    let i7 ← Zig.call (Zig.vindex p0.lanes (2 : BitVec 64))
    let i8 ← Zig.intCast false false 64 i7 (safe := false)
    let i9 ← pure (Zig.shl i8 (18 : BitVec 6))
    let i10 ← pure (i6 ||| i9)
    let i11 ← Zig.call (Zig.vindex p0.lanes (3 : BitVec 64))
    let i12 ← Zig.intCast false false 64 i11 (safe := false)
    let i13 ← pure (Zig.shl i12 (27 : BitVec 6))
    let i14 ← pure (i10 ||| i13)
    pure (.ret i14)) : Zig.M packLocals packExit).run' (default : packLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] pack

structure fieldLaneLocals where
  s : Zig.Ptr
  deriving Inhabited

inductive fieldLaneExit where
  | ret (v : BitVec 64)

def fieldLane (p0 : BitVec 32) (p1 : BitVec 16) : Zig.MemM (BitVec 64) := do
  let s2 ← Zig.allocStack 16 8
  let e ← ((do
    let i2 ← pure (← get).s
    let i3 ← Zig.callM (Zig.ptrProject i2 (·.add 8))
    Zig.store (α := BitVec 8) 1 i3 (7 : BitVec 8)
    let i5 ← pure i2
    let i6 ← Zig.callM (lanes p0)
    Zig.store (α := Zig.Vec (BitVec 9) 4) 8 i5 i6
    let i8 ← pure i2
    let i9 ← pure i8
    let i10 ← pure (Zig.trunc 9 p1)
    Zig.storeLane (α := BitVec 9) 5 8 27 i9 i10
    let i12 ← pure i2
    let i13 ← pure i12
    let i14 ← Zig.load (Framed) 8 i2
    let i15 ← pure ((i14).v)
    let i16 ← Zig.callR (pack i15)
    let i17 ← Zig.loadLane (BitVec 9) 5 8 0 i13
    let i18 ← Zig.intCast false false 64 i17 (safe := false)
    let i19 ← pure (Zig.shl i18 (36 : BitVec 6))
    let i20 ← pure (i16 ||| i19)
    let i21 ← Zig.load (Framed) 8 i2
    let i22 ← pure ((i21).a)
    let i23 ← Zig.intCast false false 64 i22 (safe := false)
    let i24 ← pure (Zig.shl i23 (45 : BitVec 6))
    let i25 ← pure (i20 ||| i24)
    pure (.ret i25)) : Zig.MM fieldLaneLocals fieldLaneExit).run' { (default : fieldLaneLocals) with s := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v

attribute [zig_run] fieldLane

structure globalLaneLocals where
  deriving Inhabited

inductive globalLaneExit where
  | ret (v : BitVec 64)

def globalLane (p0 : BitVec 16) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.loadLane (BitVec 9) 5 8 18 (⟨some 0, 0⟩ : Zig.Ptr)
    let i2 ← Zig.intCast false false 64 i1 (safe := false)
    let i3 ← pure (Zig.trunc 9 p0)
    Zig.storeLane (α := BitVec 9) 5 8 18 (⟨some 0, 0⟩ : Zig.Ptr) i3
    let i5 ← Zig.load (Zig.Vec (BitVec 9) 4) 8 (⟨some 0, 0⟩ : Zig.Ptr)
    let i6 ← Zig.callR (pack i5)
    let i7 ← pure (Zig.shl i2 (36 : BitVec 6))
    let i8 ← pure (i6 ||| i7)
    pure (.ret i8)) : Zig.MM globalLaneLocals globalLaneExit).run' (default : globalLaneLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] globalLane

structure pickLocals where
  deriving Inhabited

inductive pickExit where
  | ret (v : Zig.Ptr)

def pick (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← pure p0
    pure (.ret i1)) : Zig.MM pickLocals pickExit).run' (default : pickLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] pick

structure writeHeldLocals where
  deriving Inhabited

inductive writeHeldExit where
  | ret

def writeHeld (p0 : Zig.Ptr) (p1 : BitVec 9) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.load (Zig.Ptr) 8 i2
    Zig.storeLane (α := BitVec 9) 5 8 9 i3 p1
    pure .ret) : Zig.MM writeHeldLocals writeHeldExit).run' (default : writeHeldLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] writeHeld

structure viaFieldLocals where
  v : Zig.Ptr
  local5 : Zig.Ptr
  deriving Inhabited

inductive viaFieldExit where
  | ret (v : BitVec 64)

def viaField (p0 : BitVec 32) (p1 : BitVec 16) : Zig.MemM (BitVec 64) := do
  let s2 ← Zig.allocStack 8 8
  let s5 ← Zig.allocStack 8 8
  let e ← ((do
    let i2 ← pure (← get).v
    let i3 ← Zig.callM (lanes p0)
    Zig.store (α := Zig.Vec (BitVec 9) 4) 8 i2 i3
    let i5 ← pure (← get).local5
    let i6 ← pure i5
    let i7 ← pure i2
    Zig.store (α := Zig.Ptr) 8 i6 i7
    let i9 ← pure (i5)
    let i10 ← pure (Zig.trunc 9 p1)
    let _i11 ← Zig.callM (writeHeld i9 i10)
    let i12 ← Zig.load (Zig.Vec (BitVec 9) 4) 8 i2
    let i13 ← Zig.callR (pack i12)
    let i14 ← Zig.load (Holder) 8 i9
    let i15 ← pure ((i14).p)
    let i16 ← Zig.loadLane (BitVec 9) 5 8 9 i15
    let i17 ← Zig.intCast false false 64 i16 (safe := false)
    let i18 ← pure (Zig.shl i17 (36 : BitVec 6))
    let i19 ← pure (i13 ||| i18)
    pure (.ret i19)) : Zig.MM viaFieldLocals viaFieldExit).run' { (default : viaFieldLocals) with v := s2, local5 := s5 }
  Zig.free s5
  Zig.free s2
  match e with
  | .ret v => pure v

attribute [zig_run] viaField

structure viaResultLocals where
  v : Zig.Ptr
  deriving Inhabited

inductive viaResultExit where
  | ret (v : BitVec 64)

def viaResult (p0 : BitVec 32) (p1 : BitVec 16) : Zig.MemM (BitVec 64) := do
  let s2 ← Zig.allocStack 8 8
  let e ← ((do
    let i2 ← pure (← get).v
    let i3 ← Zig.callM (lanes p0)
    Zig.store (α := Zig.Vec (BitVec 9) 4) 8 i2 i3
    let i5 ← Zig.callM (pick i2)
    let i6 ← Zig.loadLane (BitVec 9) 5 8 9 i5
    let i7 ← Zig.intCast false false 64 i6 (safe := false)
    let i8 ← pure (Zig.trunc 9 p1)
    Zig.storeLane (α := BitVec 9) 5 8 9 i5 i8
    let i10 ← Zig.load (Zig.Vec (BitVec 9) 4) 8 i2
    let i11 ← Zig.callR (pack i10)
    let i12 ← pure (Zig.shl i7 (36 : BitVec 6))
    let i13 ← pure (i11 ||| i12)
    pure (.ret i13)) : Zig.MM viaResultLocals viaResultExit).run' { (default : viaResultLocals) with v := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v

attribute [zig_run] viaResult

end LaneShapes