-- air2lean-profile: {"admission":"unqualified-build-mode","correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_x86_64","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace ConstBases

structure Cell where
  tag : BitVec 16
  bytes : Vector (BitVec 8) 4
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Cell where
  size := 6
  align := 2
  encode v := Zig.Enc.fields 6 [(0, Zig.Enc.encode v.tag), (2, Zig.Enc.encode v.bytes)]
  decode bs := do pure { tag := ← Zig.Enc.decodeAt bs 0, bytes := ← Zig.Enc.decodeAt bs 2 }

structure Holder where
  head : BitVec 64
  maybe : Option (Cell)
  res : Except Zig.ErrName (Vector (BitVec 8) 3)
  tail : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Holder where
  size := 32
  align := 8
  encode v := Zig.Enc.fields 32 [(0, Zig.Enc.encode v.head), (12, Zig.Enc.encode v.maybe), (20, (letI : Zig.Enc (Except Zig.ErrName (Vector (BitVec 8) 3)) := Zig.errorUnionEnc (⟨#["Bad"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Vector (BitVec 8) 3))); Zig.Enc.encode v.res)), (8, Zig.Enc.encode v.tail)]
  decode bs := do pure { head := ← Zig.Enc.decodeAt bs 0, maybe := ← Zig.Enc.decodeAt bs 12, res := ← (letI : Zig.Enc (Except Zig.ErrName (Vector (BitVec 8) 3)) := Zig.errorUnionEnc (⟨#["Bad"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Vector (BitVec 8) 3))); Zig.Enc.decodeAt bs 20), tail := ← Zig.Enc.decodeAt bs 8 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: const_bases.table
  (Zig.Enc.encode (({ head := (1 : BitVec 64), maybe := (some ({ tag := (85 : BitVec 16), bytes := (#v[(10 : BitVec 8), (11 : BitVec 8), (12 : BitVec 8), (13 : BitVec 8)] : Vector (BitVec 8) 4) } : Cell)), res := (.ok (#v[(20 : BitVec 8), (21 : BitVec 8), (22 : BitVec 8)] : Vector (BitVec 8) 3) : Except Zig.ErrName (Vector (BitVec 8) 3)), tail := (99 : BitVec 32) } : Holder) : Holder), 1, .constGlobal)]

structure maybeBytePtrLocals where
  deriving Inhabited

inductive maybeBytePtrExit where
  | ret (v : Zig.Ptr)

def maybeBytePtr  : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    pure (.ret (⟨some 0, 15⟩ : Zig.Ptr))) : Zig.MM maybeBytePtrLocals maybeBytePtrExit).run' (default : maybeBytePtrLocals)
  match e with
  | .ret v => pure v

structure maybeElemPtrLocals where
  deriving Inhabited

inductive maybeElemPtrExit where
  | ret (v : Zig.Ptr)

def maybeElemPtr  : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    pure (.ret (⟨some 0, 15⟩ : Zig.Ptr))) : Zig.MM maybeElemPtrLocals maybeElemPtrExit).run' (default : maybeElemPtrLocals)
  match e with
  | .ret v => pure v

structure maybeSliceLocals where
  deriving Inhabited

inductive maybeSliceExit where
  | ret (v : Zig.Slice)

def maybeSlice  : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret (⟨(⟨some 0, 15⟩ : Zig.Ptr), (2 : BitVec 64)⟩ : Zig.Slice))) : Zig.MM maybeSliceLocals maybeSliceExit).run' (default : maybeSliceLocals)
  match e with
  | .ret v => pure v

structure projectMaybeLocals where
  deriving Inhabited

inductive projectMaybeExit where
  | ret (v : Zig.Ptr)

def projectMaybe (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.add 12))
    let i2 ← pure i1
    let i3 ← Zig.callM (Zig.ptrProject i2 (·.add 2))
    let i4 ← Zig.callM (Zig.ptrProject i3 (·.elem 1 (1 : BitVec 64)))
    pure (.ret i4)) : Zig.MM projectMaybeLocals projectMaybeExit).run' (default : projectMaybeLocals)
  match e with
  | .ret v => pure v

structure projectResLocals where
  deriving Inhabited

inductive projectResExit where
  | ret (v : Zig.Ptr)

def projectRes (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.add 20))
    let i2 ← Zig.callM (Zig.ptrProject i1 (Zig.errPayloadPtr (Vector (BitVec 8) 3)))
    let i3 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (2 : BitVec 64)))
    pure (.ret i3)) : Zig.MM projectResLocals projectResExit).run' (default : projectResLocals)
  match e with
  | .ret v => pure v

structure readResElemLocals where
  deriving Inhabited

inductive readResElemExit where
  | ret (v : BitVec 8)

def readResElem  : Zig.MemM (BitVec 8) := do
  let e ← ((do
    let i0 ← Zig.load (BitVec 8) 1 (⟨some 0, 24⟩ : Zig.Ptr)
    pure (.ret i0)) : Zig.MM readResElemLocals readResElemExit).run' (default : readResElemLocals)
  match e with
  | .ret v => pure v

structure resCodePtrLocals where
  deriving Inhabited

inductive resCodePtrExit where
  | ret (v : Zig.Ptr)

def resCodePtr  : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    pure (.ret (⟨some 0, 20⟩ : Zig.Ptr))) : Zig.MM resCodePtrLocals resCodePtrExit).run' (default : resCodePtrLocals)
  match e with
  | .ret v => pure v

structure resElemPtrLocals where
  deriving Inhabited

inductive resElemPtrExit where
  | ret (v : Zig.Ptr)

def resElemPtr  : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    pure (.ret (⟨some 0, 24⟩ : Zig.Ptr))) : Zig.MM resElemPtrLocals resElemPtrExit).run' (default : resElemPtrLocals)
  match e with
  | .ret v => pure v

end ConstBases