-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"}}
import ZigLean


namespace EncExactness

structure E24 where
  bits : BitVec 24
  deriving Repr, Inhabited, DecidableEq

def E24.a : E24 := ⟨(5 : BitVec 24)⟩
def E24.b : E24 := ⟨(8388608 : BitVec 24)⟩

def E24.toBits (e : E24) : BitVec 24 := e.bits

def E24.ofInt? (v : Int) : Option E24 :=
  if 0 ≤ v ∧ v ≤ 16777215 then Option.some ⟨BitVec.ofInt 24 v⟩ else Option.none

def E24.isNamed (e : E24) : Bool := e.bits == (5 : BitVec 24) || e.bits == (8388608 : BitVec 24)

instance : Zig.Packed E24 24 where
  toBits := E24.toBits
  ofBits b := ⟨b⟩

instance : Zig.Enc E24 where
  size := 4
  align := 4
  encode v := (Zig.intEncExt .little false 24).encode v.toBits
  decode bs := do
    let b : BitVec 24 ← (Zig.intEncExt .little false 24).decode bs
    pure ⟨b⟩

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: enc_exactness.w16
  (Zig.Enc.encode ((0 : BitVec 16) : BitVec 16), 2, .global),
  -- 1: enc_exactness.w32
  (Zig.Enc.encode ((0 : BitVec 32) : BitVec 32), 4, .global)]

structure boolByteLocals where
  deriving Inhabited

inductive boolByteExit where
  | ret (v : BitVec 8)

def boolByte (p0 : Bool) : Zig.MemM (BitVec 8) := do
  let e ← ((do
    Zig.store (α := BitVec 16) 2 (⟨some 0, 0⟩ : Zig.Ptr) (65535 : BitVec 16)
    Zig.store (α := Bool) 1 (⟨some 0, 0⟩ : Zig.Ptr) p0
    let i3 ← Zig.load (BitVec 16) 2 (⟨some 0, 0⟩ : Zig.Ptr)
    let i4 ← pure (Zig.trunc 8 i3)
    pure (.ret i4)) : Zig.MM boolByteLocals boolByteExit).run' (default : boolByteLocals)
  match e with
  | .ret v => pure v

structure e24SetPadLocals where
  deriving Inhabited

inductive e24SetPadExit where
  | ret (v : BitVec 32)

def e24SetPad (p0 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    Zig.store (α := BitVec 32) 4 (⟨some 1, 0⟩ : Zig.Ptr) p0
    let i2 ← Zig.load (E24) 4 (⟨some 1, 0⟩ : Zig.Ptr)
    let i3 ← pure (E24.toBits i2)
    let i4 ← Zig.intCast false false 32 i3 (safe := false)
    pure (.ret i4)) : Zig.MM e24SetPadLocals e24SetPadExit).run' (default : e24SetPadLocals)
  match e with
  | .ret v => pure v

structure i10StoreBytesLocals where
  deriving Inhabited

inductive i10StoreBytesExit where
  | ret (v : BitVec 16)

def i10StoreBytes (p0 : BitVec 10) : Zig.MemM (BitVec 16) := do
  let e ← ((do
    Zig.store (α := BitVec 16) 2 (⟨some 0, 0⟩ : Zig.Ptr) (65535 : BitVec 16)
    (letI : Zig.Enc (BitVec 10) := Zig.intEncExt .little true 10; Zig.store (α := BitVec 10) 2 (⟨some 0, 0⟩ : Zig.Ptr) p0)
    let i3 ← Zig.load (BitVec 16) 2 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i3)) : Zig.MM i10StoreBytesLocals i10StoreBytesExit).run' (default : i10StoreBytesLocals)
  match e with
  | .ret v => pure v

structure i10ZeroPadLocals where
  deriving Inhabited

inductive i10ZeroPadExit where
  | ret (v : BitVec 16)

def i10ZeroPad (p0 : BitVec 16) : Zig.MemM (BitVec 16) := do
  let e ← ((do
    Zig.store (α := BitVec 16) 2 (⟨some 0, 0⟩ : Zig.Ptr) p0
    let i2 ← (letI : Zig.Enc (BitVec 10) := Zig.intEncExt .little true 10; Zig.load (BitVec 10) 2 (⟨some 0, 0⟩ : Zig.Ptr))
    let i3 ← Zig.intCast true true 16 i2 (safe := false)
    pure (.ret i3)) : Zig.MM i10ZeroPadLocals i10ZeroPadExit).run' (default : i10ZeroPadLocals)
  match e with
  | .ret v => pure v

structure i24RoundTripLocals where
  deriving Inhabited

inductive i24RoundTripExit where
  | ret (v : BitVec 32)

def i24RoundTrip (p0 : BitVec 24) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    (letI : Zig.Enc (BitVec 24) := Zig.intEncExt .little true 24; Zig.store (α := BitVec 24) 4 (⟨some 1, 0⟩ : Zig.Ptr) p0)
    let i2 ← (letI : Zig.Enc (BitVec 24) := Zig.intEncExt .little true 24; Zig.load (BitVec 24) 4 (⟨some 1, 0⟩ : Zig.Ptr))
    let i3 ← Zig.intCast true true 32 i2 (safe := false)
    pure (.ret i3)) : Zig.MM i24RoundTripLocals i24RoundTripExit).run' (default : i24RoundTripLocals)
  match e with
  | .ret v => pure v

structure i24ZeroPadLocals where
  deriving Inhabited

inductive i24ZeroPadExit where
  | ret (v : BitVec 32)

def i24ZeroPad (p0 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    Zig.store (α := BitVec 32) 4 (⟨some 1, 0⟩ : Zig.Ptr) p0
    let i2 ← (letI : Zig.Enc (BitVec 24) := Zig.intEncExt .little true 24; Zig.load (BitVec 24) 4 (⟨some 1, 0⟩ : Zig.Ptr))
    let i3 ← Zig.intCast true true 32 i2 (safe := false)
    pure (.ret i3)) : Zig.MM i24ZeroPadLocals i24ZeroPadExit).run' (default : i24ZeroPadLocals)
  match e with
  | .ret v => pure v

structure u24SetPadLocals where
  deriving Inhabited

inductive u24SetPadExit where
  | ret (v : BitVec 32)

def u24SetPad (p0 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    Zig.store (α := BitVec 32) 4 (⟨some 1, 0⟩ : Zig.Ptr) p0
    let i2 ← (letI : Zig.Enc (BitVec 24) := Zig.intEncExt .little false 24; Zig.load (BitVec 24) 4 (⟨some 1, 0⟩ : Zig.Ptr))
    let i3 ← Zig.intCast false false 32 i2 (safe := false)
    pure (.ret i3)) : Zig.MM u24SetPadLocals u24SetPadExit).run' (default : u24SetPadLocals)
  match e with
  | .ret v => pure v

structure u24StoreBytesLocals where
  deriving Inhabited

inductive u24StoreBytesExit where
  | ret (v : BitVec 32)

def u24StoreBytes (p0 : BitVec 24) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    Zig.store (α := BitVec 32) 4 (⟨some 1, 0⟩ : Zig.Ptr) (4294967295 : BitVec 32)
    (letI : Zig.Enc (BitVec 24) := Zig.intEncExt .little false 24; Zig.store (α := BitVec 24) 4 (⟨some 1, 0⟩ : Zig.Ptr) p0)
    let i3 ← Zig.load (BitVec 32) 4 (⟨some 1, 0⟩ : Zig.Ptr)
    pure (.ret i3)) : Zig.MM u24StoreBytesLocals u24StoreBytesExit).run' (default : u24StoreBytesLocals)
  match e with
  | .ret v => pure v

end EncExactness