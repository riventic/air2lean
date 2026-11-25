-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.16-musl","zig_version":"0.15.2"}}
import ZigLean


namespace LaneValues

structure Lanes_u8_Holder where
  p : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Lanes_u8_Holder where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.p)]
  decode bs := do pure { p := ← Zig.Enc.decodeAt bs 0 }

structure Lanes_u64_Holder where
  p : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Lanes_u64_Holder where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.p)]
  decode bs := do pure { p := ← Zig.Enc.decodeAt bs 0 }

structure Lanes_u32_Holder where
  p : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Lanes_u32_Holder where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.p)]
  decode bs := do pure { p := ← Zig.Enc.decodeAt bs 0 }

structure Lanes_u128_Holder where
  p : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Lanes_u128_Holder where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.p)]
  decode bs := do pure { p := ← Zig.Enc.decodeAt bs 0 }

structure Lanes_i16_Holder where
  p : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Lanes_i16_Holder where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.p)]
  decode bs := do pure { p := ← Zig.Enc.decodeAt bs 0 }

structure Lanes_f64_Holder where
  p : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Lanes_f64_Holder where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.p)]
  decode bs := do pure { p := ← Zig.Enc.decodeAt bs 0 }

structure Lanes_f32_Holder where
  p : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Lanes_f32_Holder where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.p)]
  decode bs := do pure { p := ← Zig.Enc.decodeAt bs 0 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: lane_values.Lanes(f64).g
  (Zig.Enc.encode (((⟨#v[(Zig.Float.ofBits (4607182418800017408 : BitVec 64) : Zig.F64), (Zig.Float.ofBits (4611686018427387904 : BitVec 64) : Zig.F64), (Zig.Float.ofBits (4613937818241073152 : BitVec 64) : Zig.F64), (Zig.Float.ofBits (4616189618054758400 : BitVec 64) : Zig.F64)]⟩) : Zig.Vec (Zig.F64) 4) : Zig.Vec (Zig.F64) 4), 32, .global),
  -- 1: lane_values.Lanes(u128).g
  (Zig.Enc.encode (((⟨#v[(210306068529402873165736369884012333109 : BitVec 128), (80329770137867282868098132336256454762 : BitVec 128), (290635838667270156033834502220268787871 : BitVec 128), (160659540275734565736196264672512909524 : BitVec 128)]⟩) : Zig.Vec (BitVec 128) 4) : Zig.Vec (BitVec 128) 4), 64, .global),
  -- 2: lane_values.Lanes(u32).g
  (Zig.Enc.encode (((⟨#v[(1559087157 : BitVec 32), (3118174314 : BitVec 32), (382294175 : BitVec 32), (1941381332 : BitVec 32)]⟩) : Zig.Vec (BitVec 32) 4) : Zig.Vec (BitVec 32) 4), 16, .global),
  -- 3: lane_values.Lanes(u8).g
  (Zig.Enc.encode (((⟨#v[(53 : BitVec 8), (106 : BitVec 8), (159 : BitVec 8), (212 : BitVec 8)]⟩) : Zig.Vec (BitVec 8) 4) : Zig.Vec (BitVec 8) 4), 4, .global)]

structure Lanes_f32_bitsLocals where
  deriving Inhabited

inductive Lanes_f32_bitsExit where
  | ret (v : BitVec 128)

def Lanes_f32_bits (p0 : Zig.F32) : Zig.Result (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.Float.toInt false 128 true p0
    pure (.ret i1)) : Zig.M Lanes_f32_bitsLocals Lanes_f32_bitsExit).run' (default : Lanes_f32_bitsLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_f32_bits

structure Lanes_f32_ofLocals where
  deriving Inhabited

inductive Lanes_f32_ofExit where
  | ret (v : Zig.F32)

def Lanes_f32_of (p0 : BitVec 32) : Zig.Result (Zig.F32) := do
  let e ← ((do
    let i1 ← Zig.intCast false false 128 p0 (safe := false)
    let _i2 ← pure (Zig.mulWrap i1 (210306068529402873165736369884012333109 : BitVec 128))
    let i3 ← pure (p0 &&& (255 : BitVec 32))
    let i4 ← pure (Zig.Float.ofInt .f32 false i3)
    pure (.ret i4)) : Zig.M Lanes_f32_ofLocals Lanes_f32_ofExit).run' (default : Lanes_f32_ofLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_f32_of

structure Lanes_f32_lanesLocals where
  local1 : Zig.Ptr
  deriving Inhabited

inductive Lanes_f32_lanesExit where
  | ret (v : Zig.Vec (Zig.F32) 4)

def Lanes_f32_lanes (p0 : BitVec 32) : Zig.MemM (Zig.Vec (Zig.F32) 4) := do
  let s1 ← Zig.allocStack 16 16
  let e ← ((do
    let i1 ← pure (← get).local1
    let i2 ← pure i1
    let i3 ← Zig.callR (Lanes_f32_of p0)
    Zig.store (α := Zig.F32) 4 i2 i3
    let i5 ← Zig.callM (Zig.ptrProject i1 (·.elem 4 (1 : BitVec 64)))
    let i6 ← pure (Zig.shr false p0 (3 : BitVec 5))
    let i7 ← Zig.callR (Lanes_f32_of i6)
    Zig.store (α := Zig.F32) 4 i5 i7
    let i9 ← Zig.callM (Zig.ptrProject i1 (·.elem 4 (2 : BitVec 64)))
    let i10 ← pure (Zig.shr false p0 (7 : BitVec 5))
    let i11 ← Zig.callR (Lanes_f32_of i10)
    Zig.store (α := Zig.F32) 4 i9 i11
    let i13 ← Zig.callM (Zig.ptrProject i1 (·.elem 4 (3 : BitVec 64)))
    let i14 ← pure (Zig.shr false p0 (13 : BitVec 5))
    let i15 ← Zig.callR (Lanes_f32_of i14)
    Zig.store (α := Zig.F32) 4 i13 i15
    pure (.ret (← Zig.load (Zig.Vec (Zig.F32) 4) 16 i1))) : Zig.MM Lanes_f32_lanesLocals Lanes_f32_lanesExit).run' { (default : Lanes_f32_lanesLocals) with local1 := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_f32_lanes

structure Lanes_f32_packLocals where
  deriving Inhabited

inductive Lanes_f32_packExit where
  | ret (v : BitVec 128)

def Lanes_f32_pack (p0 : Zig.Vec (Zig.F32) 4) : Zig.Result (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.call (Zig.vindex p0.lanes (0 : BitVec 64))
    let i2 ← Zig.call (Lanes_f32_bits i1)
    let i3 ← Zig.call (Zig.vindex p0.lanes (1 : BitVec 64))
    let i4 ← Zig.call (Lanes_f32_bits i3)
    let i5 ← pure (Zig.mulWrap i4 (256 : BitVec 128))
    let i6 ← pure (Zig.addWrap i2 i5)
    let i7 ← Zig.call (Zig.vindex p0.lanes (2 : BitVec 64))
    let i8 ← Zig.call (Lanes_f32_bits i7)
    let i9 ← pure (Zig.mulWrap i8 (65536 : BitVec 128))
    let i10 ← pure (Zig.addWrap i6 i9)
    let i11 ← Zig.call (Zig.vindex p0.lanes (3 : BitVec 64))
    let i12 ← Zig.call (Lanes_f32_bits i11)
    let i13 ← pure (Zig.mulWrap i12 (16777216 : BitVec 128))
    let i14 ← pure (Zig.addWrap i10 i13)
    pure (.ret i14)) : Zig.M Lanes_f32_packLocals Lanes_f32_packExit).run' (default : Lanes_f32_packLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_f32_pack

structure Lanes_f32_pickLocals where
  deriving Inhabited

inductive Lanes_f32_pickExit where
  | ret (v : Zig.Ptr)

def Lanes_f32_pick (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.elem 4 (2 : BitVec 64)))
    pure (.ret i1)) : Zig.MM Lanes_f32_pickLocals Lanes_f32_pickExit).run' (default : Lanes_f32_pickLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_f32_pick

structure Lanes_f32_putLocals where
  deriving Inhabited

inductive Lanes_f32_putExit where
  | ret

def Lanes_f32_put (p0 : Zig.Ptr) (p1 : Zig.F32) : Zig.MemM (Unit) := do
  let e ← ((do
    Zig.store (α := Zig.F32) 4 p0 p1
    pure .ret) : Zig.MM Lanes_f32_putLocals Lanes_f32_putExit).run' (default : Lanes_f32_putLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Lanes_f32_put

structure Lanes_f32_readConstLocals where
  deriving Inhabited

inductive Lanes_f32_readConstExit where
  | ret (v : Zig.F32)

def Lanes_f32_readConst (p0 : Zig.Ptr) : Zig.MemM (Zig.F32) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.load (Zig.F32) 4 (p0.elem 4 (3 : BitVec 64)))
    pure (.ret i1)) : Zig.MM Lanes_f32_readConstLocals Lanes_f32_readConstExit).run' (default : Lanes_f32_readConstLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_f32_readConst

structure Lanes_f32_writeHeldLocals where
  deriving Inhabited

inductive Lanes_f32_writeHeldExit where
  | ret

def Lanes_f32_writeHeld (p0 : Zig.Ptr) (p1 : Zig.F32) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.load (Zig.Ptr) 8 i2
    Zig.store (α := Zig.F32) 4 i3 p1
    pure .ret) : Zig.MM Lanes_f32_writeHeldLocals Lanes_f32_writeHeldExit).run' (default : Lanes_f32_writeHeldLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Lanes_f32_writeHeld

structure Lanes_f32_valuesLocals where
  v : Zig.Ptr
  local14 : Zig.Ptr
  deriving Inhabited

inductive Lanes_f32_valuesExit where
  | ret (v : BitVec 128)

def Lanes_f32_values (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let s2 ← Zig.allocStack 16 16
  let s14 ← Zig.allocStack 8 8
  let e ← ((do
    let i2 ← pure (← get).v
    let i3 ← Zig.callM (Lanes_f32_lanes p0)
    Zig.store (α := Zig.Vec (Zig.F32) 4) 16 i2 i3
    let i5 ← Zig.callM (Zig.ptrProject i2 (·.elem 4 (1 : BitVec 64)))
    let i6 ← Zig.callR (Lanes_f32_of p1)
    let _i7 ← Zig.callM (Lanes_f32_put i5 i6)
    let i8 ← Zig.callM (Lanes_f32_pick i2)
    let i9 ← Zig.load (Zig.F32) 4 i8
    let i10 ← Zig.callR (Lanes_f32_bits i9)
    let i11 ← pure (Zig.shr false p1 (4 : BitVec 5))
    let i12 ← Zig.callR (Lanes_f32_of i11)
    Zig.store (α := Zig.F32) 4 i8 i12
    let i14 ← pure (← get).local14
    let i15 ← pure i14
    let i16 ← Zig.callM (Zig.ptrProject i2 (·.elem 4 (1 : BitVec 64)))
    Zig.store (α := Zig.Ptr) 8 i15 i16
    let i18 ← pure (i14)
    let i19 ← pure (Zig.shr false p1 (8 : BitVec 5))
    let i20 ← Zig.callR (Lanes_f32_of i19)
    let _i21 ← Zig.callM (Lanes_f32_writeHeld i18 i20)
    let i22 ← Zig.load (Zig.Vec (Zig.F32) 4) 16 i2
    let i23 ← Zig.callR (Lanes_f32_pack i22)
    let i24 ← pure (Zig.shl i10 (64 : BitVec 7))
    let i25 ← pure (i23 ^^^ i24)
    let i26 ← pure (i2)
    let i27 ← Zig.callM (Lanes_f32_readConst i26)
    let i28 ← Zig.callR (Lanes_f32_bits i27)
    let i29 ← pure (Zig.shl i28 (96 : BitVec 7))
    let i30 ← pure (i25 ^^^ i29)
    pure (.ret i30)) : Zig.MM Lanes_f32_valuesLocals Lanes_f32_valuesExit).run' { (default : Lanes_f32_valuesLocals) with v := s2, local14 := s14 }
  Zig.free s14
  Zig.free s2
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_f32_values

structure Lanes_f64_bitsLocals where
  deriving Inhabited

inductive Lanes_f64_bitsExit where
  | ret (v : BitVec 128)

def Lanes_f64_bits (p0 : Zig.F64) : Zig.Result (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.Float.toInt false 128 true p0
    pure (.ret i1)) : Zig.M Lanes_f64_bitsLocals Lanes_f64_bitsExit).run' (default : Lanes_f64_bitsLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_f64_bits

structure Lanes_f64_ofLocals where
  deriving Inhabited

inductive Lanes_f64_ofExit where
  | ret (v : Zig.F64)

def Lanes_f64_of (p0 : BitVec 32) : Zig.Result (Zig.F64) := do
  let e ← ((do
    let i1 ← Zig.intCast false false 128 p0 (safe := false)
    let _i2 ← pure (Zig.mulWrap i1 (210306068529402873165736369884012333109 : BitVec 128))
    let i3 ← pure (p0 &&& (255 : BitVec 32))
    let i4 ← pure (Zig.Float.ofInt .f64 false i3)
    pure (.ret i4)) : Zig.M Lanes_f64_ofLocals Lanes_f64_ofExit).run' (default : Lanes_f64_ofLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_f64_of

structure Lanes_f64_packLocals where
  deriving Inhabited

inductive Lanes_f64_packExit where
  | ret (v : BitVec 128)

def Lanes_f64_pack (p0 : Zig.Vec (Zig.F64) 4) : Zig.Result (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.call (Zig.vindex p0.lanes (0 : BitVec 64))
    let i2 ← Zig.call (Lanes_f64_bits i1)
    let i3 ← Zig.call (Zig.vindex p0.lanes (1 : BitVec 64))
    let i4 ← Zig.call (Lanes_f64_bits i3)
    let i5 ← pure (Zig.mulWrap i4 (256 : BitVec 128))
    let i6 ← pure (Zig.addWrap i2 i5)
    let i7 ← Zig.call (Zig.vindex p0.lanes (2 : BitVec 64))
    let i8 ← Zig.call (Lanes_f64_bits i7)
    let i9 ← pure (Zig.mulWrap i8 (65536 : BitVec 128))
    let i10 ← pure (Zig.addWrap i6 i9)
    let i11 ← Zig.call (Zig.vindex p0.lanes (3 : BitVec 64))
    let i12 ← Zig.call (Lanes_f64_bits i11)
    let i13 ← pure (Zig.mulWrap i12 (16777216 : BitVec 128))
    let i14 ← pure (Zig.addWrap i10 i13)
    pure (.ret i14)) : Zig.M Lanes_f64_packLocals Lanes_f64_packExit).run' (default : Lanes_f64_packLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_f64_pack

structure Lanes_f64_globalLocals where
  deriving Inhabited

inductive Lanes_f64_globalExit where
  | ret (v : BitVec 128)

def Lanes_f64_global (p0 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.load (Zig.F64) 8 (⟨some 0, 16⟩ : Zig.Ptr)
    let i2 ← Zig.callR (Lanes_f64_bits i1)
    let i3 ← Zig.callR (Lanes_f64_of p0)
    Zig.store (α := Zig.F64) 8 (⟨some 0, 16⟩ : Zig.Ptr) i3
    let i5 ← Zig.load (Zig.Vec (Zig.F64) 4) 32 (⟨some 0, 0⟩ : Zig.Ptr)
    let i6 ← Zig.callR (Lanes_f64_pack i5)
    let i7 ← pure (Zig.shl i2 (64 : BitVec 7))
    let i8 ← pure (i6 ^^^ i7)
    pure (.ret i8)) : Zig.MM Lanes_f64_globalLocals Lanes_f64_globalExit).run' (default : Lanes_f64_globalLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_f64_global

structure Lanes_f64_lanesLocals where
  local1 : Zig.Ptr
  deriving Inhabited

inductive Lanes_f64_lanesExit where
  | ret (v : Zig.Vec (Zig.F64) 4)

def Lanes_f64_lanes (p0 : BitVec 32) : Zig.MemM (Zig.Vec (Zig.F64) 4) := do
  let s1 ← Zig.allocStack 32 32
  let e ← ((do
    let i1 ← pure (← get).local1
    let i2 ← pure i1
    let i3 ← Zig.callR (Lanes_f64_of p0)
    Zig.store (α := Zig.F64) 8 i2 i3
    let i5 ← Zig.callM (Zig.ptrProject i1 (·.elem 8 (1 : BitVec 64)))
    let i6 ← pure (Zig.shr false p0 (3 : BitVec 5))
    let i7 ← Zig.callR (Lanes_f64_of i6)
    Zig.store (α := Zig.F64) 8 i5 i7
    let i9 ← Zig.callM (Zig.ptrProject i1 (·.elem 8 (2 : BitVec 64)))
    let i10 ← pure (Zig.shr false p0 (7 : BitVec 5))
    let i11 ← Zig.callR (Lanes_f64_of i10)
    Zig.store (α := Zig.F64) 8 i9 i11
    let i13 ← Zig.callM (Zig.ptrProject i1 (·.elem 8 (3 : BitVec 64)))
    let i14 ← pure (Zig.shr false p0 (13 : BitVec 5))
    let i15 ← Zig.callR (Lanes_f64_of i14)
    Zig.store (α := Zig.F64) 8 i13 i15
    pure (.ret (← Zig.load (Zig.Vec (Zig.F64) 4) 32 i1))) : Zig.MM Lanes_f64_lanesLocals Lanes_f64_lanesExit).run' { (default : Lanes_f64_lanesLocals) with local1 := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_f64_lanes

structure Lanes_f64_offsetLocals where
  v : Zig.Ptr
  deriving Inhabited

inductive Lanes_f64_offsetExit where
  | ret (v : BitVec 64)

def Lanes_f64_offset (p0 : BitVec 32) : Zig.MemM (BitVec 64) := do
  let s1 ← Zig.allocStack 32 32
  let e ← ((do
    let i1 ← pure (← get).v
    let i2 ← Zig.callM (Lanes_f64_lanes p0)
    Zig.store (α := Zig.Vec (Zig.F64) 4) 32 i1 i2
    let i4 ← Zig.callM (Zig.ptrProject i1 (·.elem 8 (1 : BitVec 64)))
    let i5 ← pure (Zig.addWrap p0 (1 : BitVec 32))
    let i6 ← Zig.callR (Lanes_f64_of i5)
    Zig.store (α := Zig.F64) 8 i4 i6
    let i8 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i4)))
    let i9 ← pure i1
    let i10 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i9)))
    let i11 ← Zig.sub false i8 i10
    pure (.ret i11)) : Zig.MM Lanes_f64_offsetLocals Lanes_f64_offsetExit).run' { (default : Lanes_f64_offsetLocals) with v := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_f64_offset

structure Lanes_f64_pickLocals where
  deriving Inhabited

inductive Lanes_f64_pickExit where
  | ret (v : Zig.Ptr)

def Lanes_f64_pick (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.elem 8 (2 : BitVec 64)))
    pure (.ret i1)) : Zig.MM Lanes_f64_pickLocals Lanes_f64_pickExit).run' (default : Lanes_f64_pickLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_f64_pick

structure Lanes_f64_putLocals where
  deriving Inhabited

inductive Lanes_f64_putExit where
  | ret

def Lanes_f64_put (p0 : Zig.Ptr) (p1 : Zig.F64) : Zig.MemM (Unit) := do
  let e ← ((do
    Zig.store (α := Zig.F64) 8 p0 p1
    pure .ret) : Zig.MM Lanes_f64_putLocals Lanes_f64_putExit).run' (default : Lanes_f64_putLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Lanes_f64_put

structure Lanes_f64_readConstLocals where
  deriving Inhabited

inductive Lanes_f64_readConstExit where
  | ret (v : Zig.F64)

def Lanes_f64_readConst (p0 : Zig.Ptr) : Zig.MemM (Zig.F64) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.load (Zig.F64) 8 (p0.elem 8 (3 : BitVec 64)))
    pure (.ret i1)) : Zig.MM Lanes_f64_readConstLocals Lanes_f64_readConstExit).run' (default : Lanes_f64_readConstLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_f64_readConst

structure Lanes_f64_writeHeldLocals where
  deriving Inhabited

inductive Lanes_f64_writeHeldExit where
  | ret

def Lanes_f64_writeHeld (p0 : Zig.Ptr) (p1 : Zig.F64) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.load (Zig.Ptr) 8 i2
    Zig.store (α := Zig.F64) 8 i3 p1
    pure .ret) : Zig.MM Lanes_f64_writeHeldLocals Lanes_f64_writeHeldExit).run' (default : Lanes_f64_writeHeldLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Lanes_f64_writeHeld

structure Lanes_f64_valuesLocals where
  v : Zig.Ptr
  local14 : Zig.Ptr
  deriving Inhabited

inductive Lanes_f64_valuesExit where
  | ret (v : BitVec 128)

def Lanes_f64_values (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let s2 ← Zig.allocStack 32 32
  let s14 ← Zig.allocStack 8 8
  let e ← ((do
    let i2 ← pure (← get).v
    let i3 ← Zig.callM (Lanes_f64_lanes p0)
    Zig.store (α := Zig.Vec (Zig.F64) 4) 32 i2 i3
    let i5 ← Zig.callM (Zig.ptrProject i2 (·.elem 8 (1 : BitVec 64)))
    let i6 ← Zig.callR (Lanes_f64_of p1)
    let _i7 ← Zig.callM (Lanes_f64_put i5 i6)
    let i8 ← Zig.callM (Lanes_f64_pick i2)
    let i9 ← Zig.load (Zig.F64) 8 i8
    let i10 ← Zig.callR (Lanes_f64_bits i9)
    let i11 ← pure (Zig.shr false p1 (4 : BitVec 5))
    let i12 ← Zig.callR (Lanes_f64_of i11)
    Zig.store (α := Zig.F64) 8 i8 i12
    let i14 ← pure (← get).local14
    let i15 ← pure i14
    let i16 ← Zig.callM (Zig.ptrProject i2 (·.elem 8 (1 : BitVec 64)))
    Zig.store (α := Zig.Ptr) 8 i15 i16
    let i18 ← pure (i14)
    let i19 ← pure (Zig.shr false p1 (8 : BitVec 5))
    let i20 ← Zig.callR (Lanes_f64_of i19)
    let _i21 ← Zig.callM (Lanes_f64_writeHeld i18 i20)
    let i22 ← Zig.load (Zig.Vec (Zig.F64) 4) 32 i2
    let i23 ← Zig.callR (Lanes_f64_pack i22)
    let i24 ← pure (Zig.shl i10 (64 : BitVec 7))
    let i25 ← pure (i23 ^^^ i24)
    let i26 ← pure (i2)
    let i27 ← Zig.callM (Lanes_f64_readConst i26)
    let i28 ← Zig.callR (Lanes_f64_bits i27)
    let i29 ← pure (Zig.shl i28 (96 : BitVec 7))
    let i30 ← pure (i25 ^^^ i29)
    pure (.ret i30)) : Zig.MM Lanes_f64_valuesLocals Lanes_f64_valuesExit).run' { (default : Lanes_f64_valuesLocals) with v := s2, local14 := s14 }
  Zig.free s14
  Zig.free s2
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_f64_values

structure Lanes_i16_bitsLocals where
  deriving Inhabited

inductive Lanes_i16_bitsExit where
  | ret (v : BitVec 128)

def Lanes_i16_bits (p0 : BitVec 16) : Zig.Result (BitVec 128) := do
  let e ← ((do
    let i1 ← pure (p0)
    let i2 ← Zig.intCast false false 128 i1 (safe := false)
    pure (.ret i2)) : Zig.M Lanes_i16_bitsLocals Lanes_i16_bitsExit).run' (default : Lanes_i16_bitsLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_i16_bits

structure Lanes_i16_ofLocals where
  deriving Inhabited

inductive Lanes_i16_ofExit where
  | ret (v : BitVec 16)

def Lanes_i16_of (p0 : BitVec 32) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← Zig.intCast false false 128 p0 (safe := false)
    let i2 ← pure (Zig.mulWrap i1 (210306068529402873165736369884012333109 : BitVec 128))
    let i3 ← pure (Zig.trunc 16 i2)
    let i4 ← pure (i3)
    pure (.ret i4)) : Zig.M Lanes_i16_ofLocals Lanes_i16_ofExit).run' (default : Lanes_i16_ofLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_i16_of

structure Lanes_i16_lanesLocals where
  local1 : Zig.Ptr
  deriving Inhabited

inductive Lanes_i16_lanesExit where
  | ret (v : Zig.Vec (BitVec 16) 4)

def Lanes_i16_lanes (p0 : BitVec 32) : Zig.MemM (Zig.Vec (BitVec 16) 4) := do
  let s1 ← Zig.allocStack 8 8
  let e ← ((do
    let i1 ← pure (← get).local1
    let i2 ← pure i1
    let i3 ← Zig.callR (Lanes_i16_of p0)
    Zig.store (α := BitVec 16) 2 i2 i3
    let i5 ← Zig.callM (Zig.ptrProject i1 (·.elem 2 (1 : BitVec 64)))
    let i6 ← pure (Zig.shr false p0 (3 : BitVec 5))
    let i7 ← Zig.callR (Lanes_i16_of i6)
    Zig.store (α := BitVec 16) 2 i5 i7
    let i9 ← Zig.callM (Zig.ptrProject i1 (·.elem 2 (2 : BitVec 64)))
    let i10 ← pure (Zig.shr false p0 (7 : BitVec 5))
    let i11 ← Zig.callR (Lanes_i16_of i10)
    Zig.store (α := BitVec 16) 2 i9 i11
    let i13 ← Zig.callM (Zig.ptrProject i1 (·.elem 2 (3 : BitVec 64)))
    let i14 ← pure (Zig.shr false p0 (13 : BitVec 5))
    let i15 ← Zig.callR (Lanes_i16_of i14)
    Zig.store (α := BitVec 16) 2 i13 i15
    pure (.ret (← Zig.load (Zig.Vec (BitVec 16) 4) 8 i1))) : Zig.MM Lanes_i16_lanesLocals Lanes_i16_lanesExit).run' { (default : Lanes_i16_lanesLocals) with local1 := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_i16_lanes

structure Lanes_i16_packLocals where
  deriving Inhabited

inductive Lanes_i16_packExit where
  | ret (v : BitVec 128)

def Lanes_i16_pack (p0 : Zig.Vec (BitVec 16) 4) : Zig.Result (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.call (Zig.vindex p0.lanes (0 : BitVec 64))
    let i2 ← Zig.call (Lanes_i16_bits i1)
    let i3 ← Zig.call (Zig.vindex p0.lanes (1 : BitVec 64))
    let i4 ← Zig.call (Lanes_i16_bits i3)
    let i5 ← pure (Zig.mulWrap i4 (256 : BitVec 128))
    let i6 ← pure (Zig.addWrap i2 i5)
    let i7 ← Zig.call (Zig.vindex p0.lanes (2 : BitVec 64))
    let i8 ← Zig.call (Lanes_i16_bits i7)
    let i9 ← pure (Zig.mulWrap i8 (65536 : BitVec 128))
    let i10 ← pure (Zig.addWrap i6 i9)
    let i11 ← Zig.call (Zig.vindex p0.lanes (3 : BitVec 64))
    let i12 ← Zig.call (Lanes_i16_bits i11)
    let i13 ← pure (Zig.mulWrap i12 (16777216 : BitVec 128))
    let i14 ← pure (Zig.addWrap i10 i13)
    pure (.ret i14)) : Zig.M Lanes_i16_packLocals Lanes_i16_packExit).run' (default : Lanes_i16_packLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_i16_pack

structure Lanes_i16_pickLocals where
  deriving Inhabited

inductive Lanes_i16_pickExit where
  | ret (v : Zig.Ptr)

def Lanes_i16_pick (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.elem 2 (2 : BitVec 64)))
    pure (.ret i1)) : Zig.MM Lanes_i16_pickLocals Lanes_i16_pickExit).run' (default : Lanes_i16_pickLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_i16_pick

structure Lanes_i16_putLocals where
  deriving Inhabited

inductive Lanes_i16_putExit where
  | ret

def Lanes_i16_put (p0 : Zig.Ptr) (p1 : BitVec 16) : Zig.MemM (Unit) := do
  let e ← ((do
    Zig.store (α := BitVec 16) 2 p0 p1
    pure .ret) : Zig.MM Lanes_i16_putLocals Lanes_i16_putExit).run' (default : Lanes_i16_putLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Lanes_i16_put

structure Lanes_i16_readConstLocals where
  deriving Inhabited

inductive Lanes_i16_readConstExit where
  | ret (v : BitVec 16)

def Lanes_i16_readConst (p0 : Zig.Ptr) : Zig.MemM (BitVec 16) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.load (BitVec 16) 2 (p0.elem 2 (3 : BitVec 64)))
    pure (.ret i1)) : Zig.MM Lanes_i16_readConstLocals Lanes_i16_readConstExit).run' (default : Lanes_i16_readConstLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_i16_readConst

structure Lanes_i16_writeHeldLocals where
  deriving Inhabited

inductive Lanes_i16_writeHeldExit where
  | ret

def Lanes_i16_writeHeld (p0 : Zig.Ptr) (p1 : BitVec 16) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.load (Zig.Ptr) 8 i2
    Zig.store (α := BitVec 16) 2 i3 p1
    pure .ret) : Zig.MM Lanes_i16_writeHeldLocals Lanes_i16_writeHeldExit).run' (default : Lanes_i16_writeHeldLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Lanes_i16_writeHeld

structure Lanes_i16_valuesLocals where
  v : Zig.Ptr
  local14 : Zig.Ptr
  deriving Inhabited

inductive Lanes_i16_valuesExit where
  | ret (v : BitVec 128)

def Lanes_i16_values (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let s2 ← Zig.allocStack 8 8
  let s14 ← Zig.allocStack 8 8
  let e ← ((do
    let i2 ← pure (← get).v
    let i3 ← Zig.callM (Lanes_i16_lanes p0)
    Zig.store (α := Zig.Vec (BitVec 16) 4) 8 i2 i3
    let i5 ← Zig.callM (Zig.ptrProject i2 (·.elem 2 (1 : BitVec 64)))
    let i6 ← Zig.callR (Lanes_i16_of p1)
    let _i7 ← Zig.callM (Lanes_i16_put i5 i6)
    let i8 ← Zig.callM (Lanes_i16_pick i2)
    let i9 ← Zig.load (BitVec 16) 2 i8
    let i10 ← Zig.callR (Lanes_i16_bits i9)
    let i11 ← pure (Zig.shr false p1 (4 : BitVec 5))
    let i12 ← Zig.callR (Lanes_i16_of i11)
    Zig.store (α := BitVec 16) 2 i8 i12
    let i14 ← pure (← get).local14
    let i15 ← pure i14
    let i16 ← Zig.callM (Zig.ptrProject i2 (·.elem 2 (1 : BitVec 64)))
    Zig.store (α := Zig.Ptr) 8 i15 i16
    let i18 ← pure (i14)
    let i19 ← pure (Zig.shr false p1 (8 : BitVec 5))
    let i20 ← Zig.callR (Lanes_i16_of i19)
    let _i21 ← Zig.callM (Lanes_i16_writeHeld i18 i20)
    let i22 ← Zig.load (Zig.Vec (BitVec 16) 4) 8 i2
    let i23 ← Zig.callR (Lanes_i16_pack i22)
    let i24 ← pure (Zig.shl i10 (64 : BitVec 7))
    let i25 ← pure (i23 ^^^ i24)
    let i26 ← pure (i2)
    let i27 ← Zig.callM (Lanes_i16_readConst i26)
    let i28 ← Zig.callR (Lanes_i16_bits i27)
    let i29 ← pure (Zig.shl i28 (96 : BitVec 7))
    let i30 ← pure (i25 ^^^ i29)
    pure (.ret i30)) : Zig.MM Lanes_i16_valuesLocals Lanes_i16_valuesExit).run' { (default : Lanes_i16_valuesLocals) with v := s2, local14 := s14 }
  Zig.free s14
  Zig.free s2
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_i16_values

structure Lanes_u128_bitsLocals where
  deriving Inhabited

inductive Lanes_u128_bitsExit where
  | ret (v : BitVec 128)

def Lanes_u128_bits (p0 : BitVec 128) : Zig.Result (BitVec 128) := do
  let e ← ((do
    pure (.ret p0)) : Zig.M Lanes_u128_bitsLocals Lanes_u128_bitsExit).run' (default : Lanes_u128_bitsLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u128_bits

structure Lanes_u128_ofLocals where
  deriving Inhabited

inductive Lanes_u128_ofExit where
  | ret (v : BitVec 128)

def Lanes_u128_of (p0 : BitVec 32) : Zig.Result (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.intCast false false 128 p0 (safe := false)
    let i2 ← pure (Zig.mulWrap i1 (210306068529402873165736369884012333109 : BitVec 128))
    pure (.ret i2)) : Zig.M Lanes_u128_ofLocals Lanes_u128_ofExit).run' (default : Lanes_u128_ofLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u128_of

structure Lanes_u128_packLocals where
  deriving Inhabited

inductive Lanes_u128_packExit where
  | ret (v : BitVec 128)

def Lanes_u128_pack (p0 : Zig.Vec (BitVec 128) 4) : Zig.Result (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.call (Zig.vindex p0.lanes (0 : BitVec 64))
    let i2 ← Zig.call (Lanes_u128_bits i1)
    let i3 ← Zig.call (Zig.vindex p0.lanes (1 : BitVec 64))
    let i4 ← Zig.call (Lanes_u128_bits i3)
    let i5 ← pure (Zig.mulWrap i4 (256 : BitVec 128))
    let i6 ← pure (Zig.addWrap i2 i5)
    let i7 ← Zig.call (Zig.vindex p0.lanes (2 : BitVec 64))
    let i8 ← Zig.call (Lanes_u128_bits i7)
    let i9 ← pure (Zig.mulWrap i8 (65536 : BitVec 128))
    let i10 ← pure (Zig.addWrap i6 i9)
    let i11 ← Zig.call (Zig.vindex p0.lanes (3 : BitVec 64))
    let i12 ← Zig.call (Lanes_u128_bits i11)
    let i13 ← pure (Zig.mulWrap i12 (16777216 : BitVec 128))
    let i14 ← pure (Zig.addWrap i10 i13)
    pure (.ret i14)) : Zig.M Lanes_u128_packLocals Lanes_u128_packExit).run' (default : Lanes_u128_packLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u128_pack

structure Lanes_u128_globalLocals where
  deriving Inhabited

inductive Lanes_u128_globalExit where
  | ret (v : BitVec 128)

def Lanes_u128_global (p0 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.load (BitVec 128) 16 (⟨some 1, 32⟩ : Zig.Ptr)
    let i2 ← Zig.callR (Lanes_u128_bits i1)
    let i3 ← Zig.callR (Lanes_u128_of p0)
    Zig.store (α := BitVec 128) 16 (⟨some 1, 32⟩ : Zig.Ptr) i3
    let i5 ← Zig.load (Zig.Vec (BitVec 128) 4) 64 (⟨some 1, 0⟩ : Zig.Ptr)
    let i6 ← Zig.callR (Lanes_u128_pack i5)
    let i7 ← pure (Zig.shl i2 (64 : BitVec 7))
    let i8 ← pure (i6 ^^^ i7)
    pure (.ret i8)) : Zig.MM Lanes_u128_globalLocals Lanes_u128_globalExit).run' (default : Lanes_u128_globalLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u128_global

structure Lanes_u128_lanesLocals where
  local1 : Zig.Ptr
  deriving Inhabited

inductive Lanes_u128_lanesExit where
  | ret (v : Zig.Vec (BitVec 128) 4)

def Lanes_u128_lanes (p0 : BitVec 32) : Zig.MemM (Zig.Vec (BitVec 128) 4) := do
  let s1 ← Zig.allocStack 64 64
  let e ← ((do
    let i1 ← pure (← get).local1
    let i2 ← pure i1
    let i3 ← Zig.callR (Lanes_u128_of p0)
    Zig.store (α := BitVec 128) 16 i2 i3
    let i5 ← Zig.callM (Zig.ptrProject i1 (·.elem 16 (1 : BitVec 64)))
    let i6 ← pure (Zig.shr false p0 (3 : BitVec 5))
    let i7 ← Zig.callR (Lanes_u128_of i6)
    Zig.store (α := BitVec 128) 16 i5 i7
    let i9 ← Zig.callM (Zig.ptrProject i1 (·.elem 16 (2 : BitVec 64)))
    let i10 ← pure (Zig.shr false p0 (7 : BitVec 5))
    let i11 ← Zig.callR (Lanes_u128_of i10)
    Zig.store (α := BitVec 128) 16 i9 i11
    let i13 ← Zig.callM (Zig.ptrProject i1 (·.elem 16 (3 : BitVec 64)))
    let i14 ← pure (Zig.shr false p0 (13 : BitVec 5))
    let i15 ← Zig.callR (Lanes_u128_of i14)
    Zig.store (α := BitVec 128) 16 i13 i15
    pure (.ret (← Zig.load (Zig.Vec (BitVec 128) 4) 64 i1))) : Zig.MM Lanes_u128_lanesLocals Lanes_u128_lanesExit).run' { (default : Lanes_u128_lanesLocals) with local1 := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u128_lanes

structure Lanes_u128_pickLocals where
  deriving Inhabited

inductive Lanes_u128_pickExit where
  | ret (v : Zig.Ptr)

def Lanes_u128_pick (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.elem 16 (2 : BitVec 64)))
    pure (.ret i1)) : Zig.MM Lanes_u128_pickLocals Lanes_u128_pickExit).run' (default : Lanes_u128_pickLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u128_pick

structure Lanes_u128_putLocals where
  deriving Inhabited

inductive Lanes_u128_putExit where
  | ret

def Lanes_u128_put (p0 : Zig.Ptr) (p1 : BitVec 128) : Zig.MemM (Unit) := do
  let e ← ((do
    Zig.store (α := BitVec 128) 16 p0 p1
    pure .ret) : Zig.MM Lanes_u128_putLocals Lanes_u128_putExit).run' (default : Lanes_u128_putLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Lanes_u128_put

structure Lanes_u128_readConstLocals where
  deriving Inhabited

inductive Lanes_u128_readConstExit where
  | ret (v : BitVec 128)

def Lanes_u128_readConst (p0 : Zig.Ptr) : Zig.MemM (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.load (BitVec 128) 16 (p0.elem 16 (3 : BitVec 64)))
    pure (.ret i1)) : Zig.MM Lanes_u128_readConstLocals Lanes_u128_readConstExit).run' (default : Lanes_u128_readConstLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u128_readConst

structure Lanes_u128_writeHeldLocals where
  deriving Inhabited

inductive Lanes_u128_writeHeldExit where
  | ret

def Lanes_u128_writeHeld (p0 : Zig.Ptr) (p1 : BitVec 128) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.load (Zig.Ptr) 8 i2
    Zig.store (α := BitVec 128) 16 i3 p1
    pure .ret) : Zig.MM Lanes_u128_writeHeldLocals Lanes_u128_writeHeldExit).run' (default : Lanes_u128_writeHeldLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Lanes_u128_writeHeld

structure Lanes_u128_valuesLocals where
  v : Zig.Ptr
  local14 : Zig.Ptr
  deriving Inhabited

inductive Lanes_u128_valuesExit where
  | ret (v : BitVec 128)

def Lanes_u128_values (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let s2 ← Zig.allocStack 64 64
  let s14 ← Zig.allocStack 8 8
  let e ← ((do
    let i2 ← pure (← get).v
    let i3 ← Zig.callM (Lanes_u128_lanes p0)
    Zig.store (α := Zig.Vec (BitVec 128) 4) 64 i2 i3
    let i5 ← Zig.callM (Zig.ptrProject i2 (·.elem 16 (1 : BitVec 64)))
    let i6 ← Zig.callR (Lanes_u128_of p1)
    let _i7 ← Zig.callM (Lanes_u128_put i5 i6)
    let i8 ← Zig.callM (Lanes_u128_pick i2)
    let i9 ← Zig.load (BitVec 128) 16 i8
    let i10 ← Zig.callR (Lanes_u128_bits i9)
    let i11 ← pure (Zig.shr false p1 (4 : BitVec 5))
    let i12 ← Zig.callR (Lanes_u128_of i11)
    Zig.store (α := BitVec 128) 16 i8 i12
    let i14 ← pure (← get).local14
    let i15 ← pure i14
    let i16 ← Zig.callM (Zig.ptrProject i2 (·.elem 16 (1 : BitVec 64)))
    Zig.store (α := Zig.Ptr) 8 i15 i16
    let i18 ← pure (i14)
    let i19 ← pure (Zig.shr false p1 (8 : BitVec 5))
    let i20 ← Zig.callR (Lanes_u128_of i19)
    let _i21 ← Zig.callM (Lanes_u128_writeHeld i18 i20)
    let i22 ← Zig.load (Zig.Vec (BitVec 128) 4) 64 i2
    let i23 ← Zig.callR (Lanes_u128_pack i22)
    let i24 ← pure (Zig.shl i10 (64 : BitVec 7))
    let i25 ← pure (i23 ^^^ i24)
    let i26 ← pure (i2)
    let i27 ← Zig.callM (Lanes_u128_readConst i26)
    let i28 ← Zig.callR (Lanes_u128_bits i27)
    let i29 ← pure (Zig.shl i28 (96 : BitVec 7))
    let i30 ← pure (i25 ^^^ i29)
    pure (.ret i30)) : Zig.MM Lanes_u128_valuesLocals Lanes_u128_valuesExit).run' { (default : Lanes_u128_valuesLocals) with v := s2, local14 := s14 }
  Zig.free s14
  Zig.free s2
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u128_values

structure Lanes_u32_bitsLocals where
  deriving Inhabited

inductive Lanes_u32_bitsExit where
  | ret (v : BitVec 128)

def Lanes_u32_bits (p0 : BitVec 32) : Zig.Result (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.intCast false false 128 p0 (safe := false)
    pure (.ret i1)) : Zig.M Lanes_u32_bitsLocals Lanes_u32_bitsExit).run' (default : Lanes_u32_bitsLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u32_bits

structure Lanes_u32_ofLocals where
  deriving Inhabited

inductive Lanes_u32_ofExit where
  | ret (v : BitVec 32)

def Lanes_u32_of (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.intCast false false 128 p0 (safe := false)
    let i2 ← pure (Zig.mulWrap i1 (210306068529402873165736369884012333109 : BitVec 128))
    let i3 ← pure (Zig.trunc 32 i2)
    pure (.ret i3)) : Zig.M Lanes_u32_ofLocals Lanes_u32_ofExit).run' (default : Lanes_u32_ofLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u32_of

structure Lanes_u32_packLocals where
  deriving Inhabited

inductive Lanes_u32_packExit where
  | ret (v : BitVec 128)

def Lanes_u32_pack (p0 : Zig.Vec (BitVec 32) 4) : Zig.Result (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.call (Zig.vindex p0.lanes (0 : BitVec 64))
    let i2 ← Zig.call (Lanes_u32_bits i1)
    let i3 ← Zig.call (Zig.vindex p0.lanes (1 : BitVec 64))
    let i4 ← Zig.call (Lanes_u32_bits i3)
    let i5 ← pure (Zig.mulWrap i4 (256 : BitVec 128))
    let i6 ← pure (Zig.addWrap i2 i5)
    let i7 ← Zig.call (Zig.vindex p0.lanes (2 : BitVec 64))
    let i8 ← Zig.call (Lanes_u32_bits i7)
    let i9 ← pure (Zig.mulWrap i8 (65536 : BitVec 128))
    let i10 ← pure (Zig.addWrap i6 i9)
    let i11 ← Zig.call (Zig.vindex p0.lanes (3 : BitVec 64))
    let i12 ← Zig.call (Lanes_u32_bits i11)
    let i13 ← pure (Zig.mulWrap i12 (16777216 : BitVec 128))
    let i14 ← pure (Zig.addWrap i10 i13)
    pure (.ret i14)) : Zig.M Lanes_u32_packLocals Lanes_u32_packExit).run' (default : Lanes_u32_packLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u32_pack

structure Lanes_u32_globalLocals where
  deriving Inhabited

inductive Lanes_u32_globalExit where
  | ret (v : BitVec 128)

def Lanes_u32_global (p0 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.load (BitVec 32) 4 (⟨some 2, 8⟩ : Zig.Ptr)
    let i2 ← Zig.callR (Lanes_u32_bits i1)
    let i3 ← Zig.callR (Lanes_u32_of p0)
    Zig.store (α := BitVec 32) 4 (⟨some 2, 8⟩ : Zig.Ptr) i3
    let i5 ← Zig.load (Zig.Vec (BitVec 32) 4) 16 (⟨some 2, 0⟩ : Zig.Ptr)
    let i6 ← Zig.callR (Lanes_u32_pack i5)
    let i7 ← pure (Zig.shl i2 (64 : BitVec 7))
    let i8 ← pure (i6 ^^^ i7)
    pure (.ret i8)) : Zig.MM Lanes_u32_globalLocals Lanes_u32_globalExit).run' (default : Lanes_u32_globalLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u32_global

structure Lanes_u32_lanesLocals where
  local1 : Zig.Ptr
  deriving Inhabited

inductive Lanes_u32_lanesExit where
  | ret (v : Zig.Vec (BitVec 32) 4)

def Lanes_u32_lanes (p0 : BitVec 32) : Zig.MemM (Zig.Vec (BitVec 32) 4) := do
  let s1 ← Zig.allocStack 16 16
  let e ← ((do
    let i1 ← pure (← get).local1
    let i2 ← pure i1
    let i3 ← Zig.callR (Lanes_u32_of p0)
    Zig.store (α := BitVec 32) 4 i2 i3
    let i5 ← Zig.callM (Zig.ptrProject i1 (·.elem 4 (1 : BitVec 64)))
    let i6 ← pure (Zig.shr false p0 (3 : BitVec 5))
    let i7 ← Zig.callR (Lanes_u32_of i6)
    Zig.store (α := BitVec 32) 4 i5 i7
    let i9 ← Zig.callM (Zig.ptrProject i1 (·.elem 4 (2 : BitVec 64)))
    let i10 ← pure (Zig.shr false p0 (7 : BitVec 5))
    let i11 ← Zig.callR (Lanes_u32_of i10)
    Zig.store (α := BitVec 32) 4 i9 i11
    let i13 ← Zig.callM (Zig.ptrProject i1 (·.elem 4 (3 : BitVec 64)))
    let i14 ← pure (Zig.shr false p0 (13 : BitVec 5))
    let i15 ← Zig.callR (Lanes_u32_of i14)
    Zig.store (α := BitVec 32) 4 i13 i15
    pure (.ret (← Zig.load (Zig.Vec (BitVec 32) 4) 16 i1))) : Zig.MM Lanes_u32_lanesLocals Lanes_u32_lanesExit).run' { (default : Lanes_u32_lanesLocals) with local1 := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u32_lanes

structure Lanes_u32_offsetLocals where
  v : Zig.Ptr
  deriving Inhabited

inductive Lanes_u32_offsetExit where
  | ret (v : BitVec 64)

def Lanes_u32_offset (p0 : BitVec 32) : Zig.MemM (BitVec 64) := do
  let s1 ← Zig.allocStack 16 16
  let e ← ((do
    let i1 ← pure (← get).v
    let i2 ← Zig.callM (Lanes_u32_lanes p0)
    Zig.store (α := Zig.Vec (BitVec 32) 4) 16 i1 i2
    let i4 ← Zig.callM (Zig.ptrProject i1 (·.elem 4 (1 : BitVec 64)))
    let i5 ← pure (Zig.addWrap p0 (1 : BitVec 32))
    let i6 ← Zig.callR (Lanes_u32_of i5)
    Zig.store (α := BitVec 32) 4 i4 i6
    let i8 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i4)))
    let i9 ← pure i1
    let i10 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i9)))
    let i11 ← Zig.sub false i8 i10
    pure (.ret i11)) : Zig.MM Lanes_u32_offsetLocals Lanes_u32_offsetExit).run' { (default : Lanes_u32_offsetLocals) with v := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u32_offset

structure Lanes_u32_pickLocals where
  deriving Inhabited

inductive Lanes_u32_pickExit where
  | ret (v : Zig.Ptr)

def Lanes_u32_pick (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.elem 4 (2 : BitVec 64)))
    pure (.ret i1)) : Zig.MM Lanes_u32_pickLocals Lanes_u32_pickExit).run' (default : Lanes_u32_pickLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u32_pick

structure Lanes_u32_putLocals where
  deriving Inhabited

inductive Lanes_u32_putExit where
  | ret

def Lanes_u32_put (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    Zig.store (α := BitVec 32) 4 p0 p1
    pure .ret) : Zig.MM Lanes_u32_putLocals Lanes_u32_putExit).run' (default : Lanes_u32_putLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Lanes_u32_put

structure Lanes_u32_readConstLocals where
  deriving Inhabited

inductive Lanes_u32_readConstExit where
  | ret (v : BitVec 32)

def Lanes_u32_readConst (p0 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.load (BitVec 32) 4 (p0.elem 4 (3 : BitVec 64)))
    pure (.ret i1)) : Zig.MM Lanes_u32_readConstLocals Lanes_u32_readConstExit).run' (default : Lanes_u32_readConstLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u32_readConst

structure Lanes_u32_writeHeldLocals where
  deriving Inhabited

inductive Lanes_u32_writeHeldExit where
  | ret

def Lanes_u32_writeHeld (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.load (Zig.Ptr) 8 i2
    Zig.store (α := BitVec 32) 4 i3 p1
    pure .ret) : Zig.MM Lanes_u32_writeHeldLocals Lanes_u32_writeHeldExit).run' (default : Lanes_u32_writeHeldLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Lanes_u32_writeHeld

structure Lanes_u32_valuesLocals where
  v : Zig.Ptr
  local14 : Zig.Ptr
  deriving Inhabited

inductive Lanes_u32_valuesExit where
  | ret (v : BitVec 128)

def Lanes_u32_values (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let s2 ← Zig.allocStack 16 16
  let s14 ← Zig.allocStack 8 8
  let e ← ((do
    let i2 ← pure (← get).v
    let i3 ← Zig.callM (Lanes_u32_lanes p0)
    Zig.store (α := Zig.Vec (BitVec 32) 4) 16 i2 i3
    let i5 ← Zig.callM (Zig.ptrProject i2 (·.elem 4 (1 : BitVec 64)))
    let i6 ← Zig.callR (Lanes_u32_of p1)
    let _i7 ← Zig.callM (Lanes_u32_put i5 i6)
    let i8 ← Zig.callM (Lanes_u32_pick i2)
    let i9 ← Zig.load (BitVec 32) 4 i8
    let i10 ← Zig.callR (Lanes_u32_bits i9)
    let i11 ← pure (Zig.shr false p1 (4 : BitVec 5))
    let i12 ← Zig.callR (Lanes_u32_of i11)
    Zig.store (α := BitVec 32) 4 i8 i12
    let i14 ← pure (← get).local14
    let i15 ← pure i14
    let i16 ← Zig.callM (Zig.ptrProject i2 (·.elem 4 (1 : BitVec 64)))
    Zig.store (α := Zig.Ptr) 8 i15 i16
    let i18 ← pure (i14)
    let i19 ← pure (Zig.shr false p1 (8 : BitVec 5))
    let i20 ← Zig.callR (Lanes_u32_of i19)
    let _i21 ← Zig.callM (Lanes_u32_writeHeld i18 i20)
    let i22 ← Zig.load (Zig.Vec (BitVec 32) 4) 16 i2
    let i23 ← Zig.callR (Lanes_u32_pack i22)
    let i24 ← pure (Zig.shl i10 (64 : BitVec 7))
    let i25 ← pure (i23 ^^^ i24)
    let i26 ← pure (i2)
    let i27 ← Zig.callM (Lanes_u32_readConst i26)
    let i28 ← Zig.callR (Lanes_u32_bits i27)
    let i29 ← pure (Zig.shl i28 (96 : BitVec 7))
    let i30 ← pure (i25 ^^^ i29)
    pure (.ret i30)) : Zig.MM Lanes_u32_valuesLocals Lanes_u32_valuesExit).run' { (default : Lanes_u32_valuesLocals) with v := s2, local14 := s14 }
  Zig.free s14
  Zig.free s2
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u32_values

structure Lanes_u64_bitsLocals where
  deriving Inhabited

inductive Lanes_u64_bitsExit where
  | ret (v : BitVec 128)

def Lanes_u64_bits (p0 : BitVec 64) : Zig.Result (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.intCast false false 128 p0 (safe := false)
    pure (.ret i1)) : Zig.M Lanes_u64_bitsLocals Lanes_u64_bitsExit).run' (default : Lanes_u64_bitsLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u64_bits

structure Lanes_u64_ofLocals where
  deriving Inhabited

inductive Lanes_u64_ofExit where
  | ret (v : BitVec 64)

def Lanes_u64_of (p0 : BitVec 32) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.intCast false false 128 p0 (safe := false)
    let i2 ← pure (Zig.mulWrap i1 (210306068529402873165736369884012333109 : BitVec 128))
    let i3 ← pure (Zig.trunc 64 i2)
    pure (.ret i3)) : Zig.M Lanes_u64_ofLocals Lanes_u64_ofExit).run' (default : Lanes_u64_ofLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u64_of

structure Lanes_u64_lanesLocals where
  local1 : Zig.Ptr
  deriving Inhabited

inductive Lanes_u64_lanesExit where
  | ret (v : Zig.Vec (BitVec 64) 4)

def Lanes_u64_lanes (p0 : BitVec 32) : Zig.MemM (Zig.Vec (BitVec 64) 4) := do
  let s1 ← Zig.allocStack 32 32
  let e ← ((do
    let i1 ← pure (← get).local1
    let i2 ← pure i1
    let i3 ← Zig.callR (Lanes_u64_of p0)
    Zig.store (α := BitVec 64) 8 i2 i3
    let i5 ← Zig.callM (Zig.ptrProject i1 (·.elem 8 (1 : BitVec 64)))
    let i6 ← pure (Zig.shr false p0 (3 : BitVec 5))
    let i7 ← Zig.callR (Lanes_u64_of i6)
    Zig.store (α := BitVec 64) 8 i5 i7
    let i9 ← Zig.callM (Zig.ptrProject i1 (·.elem 8 (2 : BitVec 64)))
    let i10 ← pure (Zig.shr false p0 (7 : BitVec 5))
    let i11 ← Zig.callR (Lanes_u64_of i10)
    Zig.store (α := BitVec 64) 8 i9 i11
    let i13 ← Zig.callM (Zig.ptrProject i1 (·.elem 8 (3 : BitVec 64)))
    let i14 ← pure (Zig.shr false p0 (13 : BitVec 5))
    let i15 ← Zig.callR (Lanes_u64_of i14)
    Zig.store (α := BitVec 64) 8 i13 i15
    pure (.ret (← Zig.load (Zig.Vec (BitVec 64) 4) 32 i1))) : Zig.MM Lanes_u64_lanesLocals Lanes_u64_lanesExit).run' { (default : Lanes_u64_lanesLocals) with local1 := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u64_lanes

structure Lanes_u64_packLocals where
  deriving Inhabited

inductive Lanes_u64_packExit where
  | ret (v : BitVec 128)

def Lanes_u64_pack (p0 : Zig.Vec (BitVec 64) 4) : Zig.Result (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.call (Zig.vindex p0.lanes (0 : BitVec 64))
    let i2 ← Zig.call (Lanes_u64_bits i1)
    let i3 ← Zig.call (Zig.vindex p0.lanes (1 : BitVec 64))
    let i4 ← Zig.call (Lanes_u64_bits i3)
    let i5 ← pure (Zig.mulWrap i4 (256 : BitVec 128))
    let i6 ← pure (Zig.addWrap i2 i5)
    let i7 ← Zig.call (Zig.vindex p0.lanes (2 : BitVec 64))
    let i8 ← Zig.call (Lanes_u64_bits i7)
    let i9 ← pure (Zig.mulWrap i8 (65536 : BitVec 128))
    let i10 ← pure (Zig.addWrap i6 i9)
    let i11 ← Zig.call (Zig.vindex p0.lanes (3 : BitVec 64))
    let i12 ← Zig.call (Lanes_u64_bits i11)
    let i13 ← pure (Zig.mulWrap i12 (16777216 : BitVec 128))
    let i14 ← pure (Zig.addWrap i10 i13)
    pure (.ret i14)) : Zig.M Lanes_u64_packLocals Lanes_u64_packExit).run' (default : Lanes_u64_packLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u64_pack

structure Lanes_u64_pickLocals where
  deriving Inhabited

inductive Lanes_u64_pickExit where
  | ret (v : Zig.Ptr)

def Lanes_u64_pick (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.elem 8 (2 : BitVec 64)))
    pure (.ret i1)) : Zig.MM Lanes_u64_pickLocals Lanes_u64_pickExit).run' (default : Lanes_u64_pickLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u64_pick

structure Lanes_u64_putLocals where
  deriving Inhabited

inductive Lanes_u64_putExit where
  | ret

def Lanes_u64_put (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (Unit) := do
  let e ← ((do
    Zig.store (α := BitVec 64) 8 p0 p1
    pure .ret) : Zig.MM Lanes_u64_putLocals Lanes_u64_putExit).run' (default : Lanes_u64_putLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Lanes_u64_put

structure Lanes_u64_readConstLocals where
  deriving Inhabited

inductive Lanes_u64_readConstExit where
  | ret (v : BitVec 64)

def Lanes_u64_readConst (p0 : Zig.Ptr) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.load (BitVec 64) 8 (p0.elem 8 (3 : BitVec 64)))
    pure (.ret i1)) : Zig.MM Lanes_u64_readConstLocals Lanes_u64_readConstExit).run' (default : Lanes_u64_readConstLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u64_readConst

structure Lanes_u64_writeHeldLocals where
  deriving Inhabited

inductive Lanes_u64_writeHeldExit where
  | ret

def Lanes_u64_writeHeld (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.load (Zig.Ptr) 8 i2
    Zig.store (α := BitVec 64) 8 i3 p1
    pure .ret) : Zig.MM Lanes_u64_writeHeldLocals Lanes_u64_writeHeldExit).run' (default : Lanes_u64_writeHeldLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Lanes_u64_writeHeld

structure Lanes_u64_valuesLocals where
  v : Zig.Ptr
  local14 : Zig.Ptr
  deriving Inhabited

inductive Lanes_u64_valuesExit where
  | ret (v : BitVec 128)

def Lanes_u64_values (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let s2 ← Zig.allocStack 32 32
  let s14 ← Zig.allocStack 8 8
  let e ← ((do
    let i2 ← pure (← get).v
    let i3 ← Zig.callM (Lanes_u64_lanes p0)
    Zig.store (α := Zig.Vec (BitVec 64) 4) 32 i2 i3
    let i5 ← Zig.callM (Zig.ptrProject i2 (·.elem 8 (1 : BitVec 64)))
    let i6 ← Zig.callR (Lanes_u64_of p1)
    let _i7 ← Zig.callM (Lanes_u64_put i5 i6)
    let i8 ← Zig.callM (Lanes_u64_pick i2)
    let i9 ← Zig.load (BitVec 64) 8 i8
    let i10 ← Zig.callR (Lanes_u64_bits i9)
    let i11 ← pure (Zig.shr false p1 (4 : BitVec 5))
    let i12 ← Zig.callR (Lanes_u64_of i11)
    Zig.store (α := BitVec 64) 8 i8 i12
    let i14 ← pure (← get).local14
    let i15 ← pure i14
    let i16 ← Zig.callM (Zig.ptrProject i2 (·.elem 8 (1 : BitVec 64)))
    Zig.store (α := Zig.Ptr) 8 i15 i16
    let i18 ← pure (i14)
    let i19 ← pure (Zig.shr false p1 (8 : BitVec 5))
    let i20 ← Zig.callR (Lanes_u64_of i19)
    let _i21 ← Zig.callM (Lanes_u64_writeHeld i18 i20)
    let i22 ← Zig.load (Zig.Vec (BitVec 64) 4) 32 i2
    let i23 ← Zig.callR (Lanes_u64_pack i22)
    let i24 ← pure (Zig.shl i10 (64 : BitVec 7))
    let i25 ← pure (i23 ^^^ i24)
    let i26 ← pure (i2)
    let i27 ← Zig.callM (Lanes_u64_readConst i26)
    let i28 ← Zig.callR (Lanes_u64_bits i27)
    let i29 ← pure (Zig.shl i28 (96 : BitVec 7))
    let i30 ← pure (i25 ^^^ i29)
    pure (.ret i30)) : Zig.MM Lanes_u64_valuesLocals Lanes_u64_valuesExit).run' { (default : Lanes_u64_valuesLocals) with v := s2, local14 := s14 }
  Zig.free s14
  Zig.free s2
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u64_values

structure Lanes_u8_bitsLocals where
  deriving Inhabited

inductive Lanes_u8_bitsExit where
  | ret (v : BitVec 128)

def Lanes_u8_bits (p0 : BitVec 8) : Zig.Result (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.intCast false false 128 p0 (safe := false)
    pure (.ret i1)) : Zig.M Lanes_u8_bitsLocals Lanes_u8_bitsExit).run' (default : Lanes_u8_bitsLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u8_bits

structure Lanes_u8_ofLocals where
  deriving Inhabited

inductive Lanes_u8_ofExit where
  | ret (v : BitVec 8)

def Lanes_u8_of (p0 : BitVec 32) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i1 ← Zig.intCast false false 128 p0 (safe := false)
    let i2 ← pure (Zig.mulWrap i1 (210306068529402873165736369884012333109 : BitVec 128))
    let i3 ← pure (Zig.trunc 8 i2)
    pure (.ret i3)) : Zig.M Lanes_u8_ofLocals Lanes_u8_ofExit).run' (default : Lanes_u8_ofLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u8_of

structure Lanes_u8_packLocals where
  deriving Inhabited

inductive Lanes_u8_packExit where
  | ret (v : BitVec 128)

def Lanes_u8_pack (p0 : Zig.Vec (BitVec 8) 4) : Zig.Result (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.call (Zig.vindex p0.lanes (0 : BitVec 64))
    let i2 ← Zig.call (Lanes_u8_bits i1)
    let i3 ← Zig.call (Zig.vindex p0.lanes (1 : BitVec 64))
    let i4 ← Zig.call (Lanes_u8_bits i3)
    let i5 ← pure (Zig.mulWrap i4 (256 : BitVec 128))
    let i6 ← pure (Zig.addWrap i2 i5)
    let i7 ← Zig.call (Zig.vindex p0.lanes (2 : BitVec 64))
    let i8 ← Zig.call (Lanes_u8_bits i7)
    let i9 ← pure (Zig.mulWrap i8 (65536 : BitVec 128))
    let i10 ← pure (Zig.addWrap i6 i9)
    let i11 ← Zig.call (Zig.vindex p0.lanes (3 : BitVec 64))
    let i12 ← Zig.call (Lanes_u8_bits i11)
    let i13 ← pure (Zig.mulWrap i12 (16777216 : BitVec 128))
    let i14 ← pure (Zig.addWrap i10 i13)
    pure (.ret i14)) : Zig.M Lanes_u8_packLocals Lanes_u8_packExit).run' (default : Lanes_u8_packLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u8_pack

structure Lanes_u8_globalLocals where
  deriving Inhabited

inductive Lanes_u8_globalExit where
  | ret (v : BitVec 128)

def Lanes_u8_global (p0 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.load (BitVec 8) 1 (⟨some 3, 2⟩ : Zig.Ptr)
    let i2 ← Zig.callR (Lanes_u8_bits i1)
    let i3 ← Zig.callR (Lanes_u8_of p0)
    Zig.store (α := BitVec 8) 1 (⟨some 3, 2⟩ : Zig.Ptr) i3
    let i5 ← Zig.load (Zig.Vec (BitVec 8) 4) 4 (⟨some 3, 0⟩ : Zig.Ptr)
    let i6 ← Zig.callR (Lanes_u8_pack i5)
    let i7 ← pure (Zig.shl i2 (64 : BitVec 7))
    let i8 ← pure (i6 ^^^ i7)
    pure (.ret i8)) : Zig.MM Lanes_u8_globalLocals Lanes_u8_globalExit).run' (default : Lanes_u8_globalLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u8_global

structure Lanes_u8_lanesLocals where
  local1 : Zig.Ptr
  deriving Inhabited

inductive Lanes_u8_lanesExit where
  | ret (v : Zig.Vec (BitVec 8) 4)

def Lanes_u8_lanes (p0 : BitVec 32) : Zig.MemM (Zig.Vec (BitVec 8) 4) := do
  let s1 ← Zig.allocStack 4 4
  let e ← ((do
    let i1 ← pure (← get).local1
    let i2 ← pure i1
    let i3 ← Zig.callR (Lanes_u8_of p0)
    Zig.store (α := BitVec 8) 1 i2 i3
    let i5 ← Zig.callM (Zig.ptrProject i1 (·.elem 1 (1 : BitVec 64)))
    let i6 ← pure (Zig.shr false p0 (3 : BitVec 5))
    let i7 ← Zig.callR (Lanes_u8_of i6)
    Zig.store (α := BitVec 8) 1 i5 i7
    let i9 ← Zig.callM (Zig.ptrProject i1 (·.elem 1 (2 : BitVec 64)))
    let i10 ← pure (Zig.shr false p0 (7 : BitVec 5))
    let i11 ← Zig.callR (Lanes_u8_of i10)
    Zig.store (α := BitVec 8) 1 i9 i11
    let i13 ← Zig.callM (Zig.ptrProject i1 (·.elem 1 (3 : BitVec 64)))
    let i14 ← pure (Zig.shr false p0 (13 : BitVec 5))
    let i15 ← Zig.callR (Lanes_u8_of i14)
    Zig.store (α := BitVec 8) 1 i13 i15
    pure (.ret (← Zig.load (Zig.Vec (BitVec 8) 4) 4 i1))) : Zig.MM Lanes_u8_lanesLocals Lanes_u8_lanesExit).run' { (default : Lanes_u8_lanesLocals) with local1 := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u8_lanes

structure Lanes_u8_offsetLocals where
  v : Zig.Ptr
  deriving Inhabited

inductive Lanes_u8_offsetExit where
  | ret (v : BitVec 64)

def Lanes_u8_offset (p0 : BitVec 32) : Zig.MemM (BitVec 64) := do
  let s1 ← Zig.allocStack 4 4
  let e ← ((do
    let i1 ← pure (← get).v
    let i2 ← Zig.callM (Lanes_u8_lanes p0)
    Zig.store (α := Zig.Vec (BitVec 8) 4) 4 i1 i2
    let i4 ← Zig.callM (Zig.ptrProject i1 (·.elem 1 (1 : BitVec 64)))
    let i5 ← pure (Zig.addWrap p0 (1 : BitVec 32))
    let i6 ← Zig.callR (Lanes_u8_of i5)
    Zig.store (α := BitVec 8) 1 i4 i6
    let i8 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i4)))
    let i9 ← pure i1
    let i10 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i9)))
    let i11 ← Zig.sub false i8 i10
    pure (.ret i11)) : Zig.MM Lanes_u8_offsetLocals Lanes_u8_offsetExit).run' { (default : Lanes_u8_offsetLocals) with v := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u8_offset

structure Lanes_u8_pickLocals where
  deriving Inhabited

inductive Lanes_u8_pickExit where
  | ret (v : Zig.Ptr)

def Lanes_u8_pick (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.elem 1 (2 : BitVec 64)))
    pure (.ret i1)) : Zig.MM Lanes_u8_pickLocals Lanes_u8_pickExit).run' (default : Lanes_u8_pickLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u8_pick

structure Lanes_u8_putLocals where
  deriving Inhabited

inductive Lanes_u8_putExit where
  | ret

def Lanes_u8_put (p0 : Zig.Ptr) (p1 : BitVec 8) : Zig.MemM (Unit) := do
  let e ← ((do
    Zig.store (α := BitVec 8) 1 p0 p1
    pure .ret) : Zig.MM Lanes_u8_putLocals Lanes_u8_putExit).run' (default : Lanes_u8_putLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Lanes_u8_put

structure Lanes_u8_readConstLocals where
  deriving Inhabited

inductive Lanes_u8_readConstExit where
  | ret (v : BitVec 8)

def Lanes_u8_readConst (p0 : Zig.Ptr) : Zig.MemM (BitVec 8) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.load (BitVec 8) 1 (p0.elem 1 (3 : BitVec 64)))
    pure (.ret i1)) : Zig.MM Lanes_u8_readConstLocals Lanes_u8_readConstExit).run' (default : Lanes_u8_readConstLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u8_readConst

structure Lanes_u8_writeHeldLocals where
  deriving Inhabited

inductive Lanes_u8_writeHeldExit where
  | ret

def Lanes_u8_writeHeld (p0 : Zig.Ptr) (p1 : BitVec 8) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.load (Zig.Ptr) 8 i2
    Zig.store (α := BitVec 8) 1 i3 p1
    pure .ret) : Zig.MM Lanes_u8_writeHeldLocals Lanes_u8_writeHeldExit).run' (default : Lanes_u8_writeHeldLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Lanes_u8_writeHeld

structure Lanes_u8_valuesLocals where
  v : Zig.Ptr
  local14 : Zig.Ptr
  deriving Inhabited

inductive Lanes_u8_valuesExit where
  | ret (v : BitVec 128)

def Lanes_u8_values (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let s2 ← Zig.allocStack 4 4
  let s14 ← Zig.allocStack 8 8
  let e ← ((do
    let i2 ← pure (← get).v
    let i3 ← Zig.callM (Lanes_u8_lanes p0)
    Zig.store (α := Zig.Vec (BitVec 8) 4) 4 i2 i3
    let i5 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (1 : BitVec 64)))
    let i6 ← Zig.callR (Lanes_u8_of p1)
    let _i7 ← Zig.callM (Lanes_u8_put i5 i6)
    let i8 ← Zig.callM (Lanes_u8_pick i2)
    let i9 ← Zig.load (BitVec 8) 1 i8
    let i10 ← Zig.callR (Lanes_u8_bits i9)
    let i11 ← pure (Zig.shr false p1 (4 : BitVec 5))
    let i12 ← Zig.callR (Lanes_u8_of i11)
    Zig.store (α := BitVec 8) 1 i8 i12
    let i14 ← pure (← get).local14
    let i15 ← pure i14
    let i16 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (1 : BitVec 64)))
    Zig.store (α := Zig.Ptr) 8 i15 i16
    let i18 ← pure (i14)
    let i19 ← pure (Zig.shr false p1 (8 : BitVec 5))
    let i20 ← Zig.callR (Lanes_u8_of i19)
    let _i21 ← Zig.callM (Lanes_u8_writeHeld i18 i20)
    let i22 ← Zig.load (Zig.Vec (BitVec 8) 4) 4 i2
    let i23 ← Zig.callR (Lanes_u8_pack i22)
    let i24 ← pure (Zig.shl i10 (64 : BitVec 7))
    let i25 ← pure (i23 ^^^ i24)
    let i26 ← pure (i2)
    let i27 ← Zig.callM (Lanes_u8_readConst i26)
    let i28 ← Zig.callR (Lanes_u8_bits i27)
    let i29 ← pure (Zig.shl i28 (96 : BitVec 7))
    let i30 ← pure (i25 ^^^ i29)
    pure (.ret i30)) : Zig.MM Lanes_u8_valuesLocals Lanes_u8_valuesExit).run' { (default : Lanes_u8_valuesLocals) with v := s2, local14 := s14 }
  Zig.free s14
  Zig.free s2
  match e with
  | .ret v => pure v

attribute [zig_run] Lanes_u8_values

structure globalF64Locals where
  deriving Inhabited

inductive globalF64Exit where
  | ret (v : BitVec 128)

def globalF64 (p0 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.callM (Lanes_f64_global p0)
    pure (.ret i1)) : Zig.MM globalF64Locals globalF64Exit).run' (default : globalF64Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] globalF64

structure globalU128Locals where
  deriving Inhabited

inductive globalU128Exit where
  | ret (v : BitVec 128)

def globalU128 (p0 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.callM (Lanes_u128_global p0)
    pure (.ret i1)) : Zig.MM globalU128Locals globalU128Exit).run' (default : globalU128Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] globalU128

structure globalU32Locals where
  deriving Inhabited

inductive globalU32Exit where
  | ret (v : BitVec 128)

def globalU32 (p0 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.callM (Lanes_u32_global p0)
    pure (.ret i1)) : Zig.MM globalU32Locals globalU32Exit).run' (default : globalU32Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] globalU32

structure globalU8Locals where
  deriving Inhabited

inductive globalU8Exit where
  | ret (v : BitVec 128)

def globalU8 (p0 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let e ← ((do
    let i1 ← Zig.callM (Lanes_u8_global p0)
    pure (.ret i1)) : Zig.MM globalU8Locals globalU8Exit).run' (default : globalU8Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] globalU8

structure offsetF64Locals where
  deriving Inhabited

inductive offsetF64Exit where
  | ret (v : BitVec 64)

def offsetF64 (p0 : BitVec 32) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.callM (Lanes_f64_offset p0)
    pure (.ret i1)) : Zig.MM offsetF64Locals offsetF64Exit).run' (default : offsetF64Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] offsetF64

structure offsetU32Locals where
  deriving Inhabited

inductive offsetU32Exit where
  | ret (v : BitVec 64)

def offsetU32 (p0 : BitVec 32) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.callM (Lanes_u32_offset p0)
    pure (.ret i1)) : Zig.MM offsetU32Locals offsetU32Exit).run' (default : offsetU32Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] offsetU32

structure offsetU8Locals where
  deriving Inhabited

inductive offsetU8Exit where
  | ret (v : BitVec 64)

def offsetU8 (p0 : BitVec 32) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.callM (Lanes_u8_offset p0)
    pure (.ret i1)) : Zig.MM offsetU8Locals offsetU8Exit).run' (default : offsetU8Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] offsetU8

structure valuesF32Locals where
  deriving Inhabited

inductive valuesF32Exit where
  | ret (v : BitVec 128)

def valuesF32 (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let e ← ((do
    let i2 ← Zig.callM (Lanes_f32_values p0 p1)
    pure (.ret i2)) : Zig.MM valuesF32Locals valuesF32Exit).run' (default : valuesF32Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] valuesF32

structure valuesF64Locals where
  deriving Inhabited

inductive valuesF64Exit where
  | ret (v : BitVec 128)

def valuesF64 (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let e ← ((do
    let i2 ← Zig.callM (Lanes_f64_values p0 p1)
    pure (.ret i2)) : Zig.MM valuesF64Locals valuesF64Exit).run' (default : valuesF64Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] valuesF64

structure valuesI16Locals where
  deriving Inhabited

inductive valuesI16Exit where
  | ret (v : BitVec 128)

def valuesI16 (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let e ← ((do
    let i2 ← Zig.callM (Lanes_i16_values p0 p1)
    pure (.ret i2)) : Zig.MM valuesI16Locals valuesI16Exit).run' (default : valuesI16Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] valuesI16

structure valuesU128Locals where
  deriving Inhabited

inductive valuesU128Exit where
  | ret (v : BitVec 128)

def valuesU128 (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let e ← ((do
    let i2 ← Zig.callM (Lanes_u128_values p0 p1)
    pure (.ret i2)) : Zig.MM valuesU128Locals valuesU128Exit).run' (default : valuesU128Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] valuesU128

structure valuesU32Locals where
  deriving Inhabited

inductive valuesU32Exit where
  | ret (v : BitVec 128)

def valuesU32 (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let e ← ((do
    let i2 ← Zig.callM (Lanes_u32_values p0 p1)
    pure (.ret i2)) : Zig.MM valuesU32Locals valuesU32Exit).run' (default : valuesU32Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] valuesU32

structure valuesU64Locals where
  deriving Inhabited

inductive valuesU64Exit where
  | ret (v : BitVec 128)

def valuesU64 (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let e ← ((do
    let i2 ← Zig.callM (Lanes_u64_values p0 p1)
    pure (.ret i2)) : Zig.MM valuesU64Locals valuesU64Exit).run' (default : valuesU64Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] valuesU64

structure valuesU8Locals where
  deriving Inhabited

inductive valuesU8Exit where
  | ret (v : BitVec 128)

def valuesU8 (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 128) := do
  let e ← ((do
    let i2 ← Zig.callM (Lanes_u8_values p0 p1)
    pure (.ret i2)) : Zig.MM valuesU8Locals valuesU8Exit).run' (default : valuesU8Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] valuesU8

end LaneValues