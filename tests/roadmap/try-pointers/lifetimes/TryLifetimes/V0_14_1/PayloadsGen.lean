-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.4.19...6.13.4-musl","zig_version":"0.14.1"}}
import ZigLean


namespace TryLifetimes.V0_14_1.Payloads

structure Pair where
  a : BitVec 32
  b : BitVec 16
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Pair where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.a), (4, Zig.Enc.encode v.b)]
  decode bs := do pure { a := ← Zig.Enc.decodeAt bs 0, b := ← Zig.Enc.decodeAt bs 4 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure cleanup16Locals where
  deriving Inhabited

inductive cleanup16Exit where
  | ret (v : Except Zig.ErrName (BitVec 16))

def cleanup16 (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : Zig.Ptr) : Zig.MemM (Except Zig.ErrName (BitVec 16)) := do
  let e ← ((do
    Zig.loadDiscardBytes 4 2 p0
    match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 16) 2 p0 with
    | .error _ => (do
      let i5 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 16) 2 p0
      let i6 ← Zig.load (BitVec 32) 4 p2
      let i7 ← Zig.add false i6 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p2 i7
      let i9 ← Zig.load (BitVec 32) 4 p1
      let i10 ← Zig.add false i9 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p1 i10
      let i12 ← pure ((.error i5) : Except Zig.ErrName (BitVec 16))
      pure (.ret i12))
    | .ok v4 => (do
      let i14 ← Zig.load (BitVec 16) 2 v4
      let i15 ← Zig.load (BitVec 32) 4 p1
      let i16 ← Zig.add false i15 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p1 i16
      let i18 ← pure ((.ok i14) : Except Zig.ErrName (BitVec 16))
      pure (.ret i18))) : Zig.MM cleanup16Locals cleanup16Exit).run' (default : cleanup16Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] cleanup16

structure cleanup32Locals where
  deriving Inhabited

inductive cleanup32Exit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def cleanup32 (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : Zig.Ptr) : Zig.MemM (Except Zig.ErrName (BitVec 32)) := do
  let e ← ((do
    Zig.loadDiscardBytes 8 4 p0
    match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 32) 4 p0 with
    | .error _ => (do
      let i5 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 32) 4 p0
      let i6 ← Zig.load (BitVec 32) 4 p2
      let i7 ← Zig.add false i6 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p2 i7
      let i9 ← Zig.load (BitVec 32) 4 p1
      let i10 ← Zig.add false i9 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p1 i10
      let i12 ← pure ((.error i5) : Except Zig.ErrName (BitVec 32))
      pure (.ret i12))
    | .ok v4 => (do
      let i14 ← Zig.load (BitVec 32) 4 v4
      let i15 ← Zig.load (BitVec 32) 4 p1
      let i16 ← Zig.add false i15 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p1 i16
      let i18 ← pure ((.ok i14) : Except Zig.ErrName (BitVec 32))
      pure (.ret i18))) : Zig.MM cleanup32Locals cleanup32Exit).run' (default : cleanup32Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] cleanup32

structure cleanup64Locals where
  deriving Inhabited

inductive cleanup64Exit where
  | ret (v : Except Zig.ErrName (BitVec 64))

def cleanup64 (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : Zig.Ptr) : Zig.MemM (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    Zig.loadDiscardBytes 16 8 p0
    match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 64) 8 p0 with
    | .error _ => (do
      let i5 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 64) 8 p0
      let i6 ← Zig.load (BitVec 32) 4 p2
      let i7 ← Zig.add false i6 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p2 i7
      let i9 ← Zig.load (BitVec 32) 4 p1
      let i10 ← Zig.add false i9 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p1 i10
      let i12 ← pure ((.error i5) : Except Zig.ErrName (BitVec 64))
      pure (.ret i12))
    | .ok v4 => (do
      let i14 ← Zig.load (BitVec 64) 8 v4
      let i15 ← Zig.load (BitVec 32) 4 p1
      let i16 ← Zig.add false i15 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p1 i16
      let i18 ← pure ((.ok i14) : Except Zig.ErrName (BitVec 64))
      pure (.ret i18))) : Zig.MM cleanup64Locals cleanup64Exit).run' (default : cleanup64Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] cleanup64

structure cleanupAnyLocals where
  deriving Inhabited

inductive cleanupAnyExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def cleanupAny (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : Zig.Ptr) : Zig.MemM (Except Zig.ErrName (BitVec 32)) := do
  let e ← ((do
    Zig.loadDiscardBytes 8 4 p0
    match ← Zig.tryPayloadPtr (BitVec 32) 4 p0 with
    | .error _ => (do
      let i5 ← Zig.errCodeAt (BitVec 32) 4 p0
      let i6 ← Zig.load (BitVec 32) 4 p2
      let i7 ← Zig.add false i6 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p2 i7
      let i9 ← Zig.load (BitVec 32) 4 p1
      let i10 ← Zig.add false i9 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p1 i10
      let i12 ← pure ((.error i5) : Except Zig.ErrName (BitVec 32))
      pure (.ret i12))
    | .ok v4 => (do
      let i14 ← Zig.load (BitVec 32) 4 v4
      let i15 ← Zig.load (BitVec 32) 4 p1
      let i16 ← Zig.add false i15 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p1 i16
      let i18 ← pure ((.ok i14) : Except Zig.ErrName (BitVec 32))
      pure (.ret i18))) : Zig.MM cleanupAnyLocals cleanupAnyExit).run' (default : cleanupAnyLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] cleanupAny

structure cleanupPairLocals where
  deriving Inhabited

inductive cleanupPairExit where
  | ret (v : Except Zig.ErrName (Pair))

def cleanupPair (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : Zig.Ptr) : Zig.MemM (Except Zig.ErrName (Pair)) := do
  let e ← ((do
    Zig.loadDiscardBytes 12 4 p0
    match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (Pair) 4 p0 with
    | .error _ => (do
      let i5 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (Pair) 4 p0
      let i6 ← Zig.load (BitVec 32) 4 p2
      let i7 ← Zig.add false i6 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p2 i7
      let i9 ← Zig.load (BitVec 32) 4 p1
      let i10 ← Zig.add false i9 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p1 i10
      let i12 ← pure ((.error i5) : Except Zig.ErrName (Pair))
      pure (.ret i12))
    | .ok v4 => (do
      let i14 ← Zig.load (Pair) 4 v4
      let i15 ← Zig.load (BitVec 32) 4 p1
      let i16 ← Zig.add false i15 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 p1 i16
      let i18 ← pure ((.ok i14) : Except Zig.ErrName (Pair))
      pure (.ret i18))) : Zig.MM cleanupPairLocals cleanupPairExit).run' (default : cleanupPairLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] cleanupPair

structure resetOnError16Locals where
  deriving Inhabited

inductive resetOnError16Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

def resetOnError16 (p0 : Zig.Ptr) (p1 : BitVec 16) : Zig.MemM (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    Zig.loadDiscardBytes 4 2 p0
    match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 16) 2 p0 with
    | .error _ => (do
      let i4 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 16) 2 p0
      let i5 ← pure ((.ok p1) : Except Zig.ErrName (BitVec 16))
      (letI : Zig.Enc (Except Zig.ErrName (BitVec 16)) := Zig.errorUnionEnc (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 16))); Zig.store (α := Except Zig.ErrName (BitVec 16)) 2 p0 i5)
      let i7 ← pure ((.error i4) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i7))
    | .ok v3 => (do
      let i9 ← pure ((.ok v3) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i9))) : Zig.MM resetOnError16Locals resetOnError16Exit).run' (default : resetOnError16Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] resetOnError16

structure resetOnError32Locals where
  deriving Inhabited

inductive resetOnError32Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

def resetOnError32 (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    Zig.loadDiscardBytes 8 4 p0
    match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 32) 4 p0 with
    | .error _ => (do
      let i4 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 32) 4 p0
      let i5 ← pure ((.ok p1) : Except Zig.ErrName (BitVec 32))
      (letI : Zig.Enc (Except Zig.ErrName (BitVec 32)) := Zig.errorUnionEnc (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 32))); Zig.store (α := Except Zig.ErrName (BitVec 32)) 4 p0 i5)
      let i7 ← pure ((.error i4) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i7))
    | .ok v3 => (do
      let i9 ← pure ((.ok v3) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i9))) : Zig.MM resetOnError32Locals resetOnError32Exit).run' (default : resetOnError32Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] resetOnError32

structure resetOnError64Locals where
  deriving Inhabited

inductive resetOnError64Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

def resetOnError64 (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    Zig.loadDiscardBytes 16 8 p0
    match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 64) 8 p0 with
    | .error _ => (do
      let i4 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 64) 8 p0
      let i5 ← pure ((.ok p1) : Except Zig.ErrName (BitVec 64))
      (letI : Zig.Enc (Except Zig.ErrName (BitVec 64)) := Zig.errorUnionEnc (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 64))); Zig.store (α := Except Zig.ErrName (BitVec 64)) 8 p0 i5)
      let i7 ← pure ((.error i4) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i7))
    | .ok v3 => (do
      let i9 ← pure ((.ok v3) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i9))) : Zig.MM resetOnError64Locals resetOnError64Exit).run' (default : resetOnError64Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] resetOnError64

structure resetOnErrorPairLocals where
  deriving Inhabited

inductive resetOnErrorPairExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

def resetOnErrorPair (p0 : Zig.Ptr) (p1 : Pair) : Zig.MemM (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    Zig.loadDiscardBytes 12 4 p0
    match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (Pair) 4 p0 with
    | .error _ => (do
      let i4 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (Pair) 4 p0
      let i5 ← pure ((.ok p1) : Except Zig.ErrName (Pair))
      (letI : Zig.Enc (Except Zig.ErrName (Pair)) := Zig.errorUnionEnc (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Pair))); Zig.store (α := Except Zig.ErrName (Pair)) 4 p0 i5)
      let i7 ← pure ((.error i4) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i7))
    | .ok v3 => (do
      let i9 ← pure ((.ok v3) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i9))) : Zig.MM resetOnErrorPairLocals resetOnErrorPairExit).run' (default : resetOnErrorPairLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] resetOnErrorPair

structure writeAlias16Locals where
  deriving Inhabited

inductive writeAlias16Exit where
  | ret (v : Except Zig.ErrName (BitVec 16))

def writeAlias16 (p0 : Zig.Ptr) (p1 : BitVec 16) : Zig.MemM (Except Zig.ErrName (BitVec 16)) := do
  let e ← ((do
    Zig.loadDiscardBytes 4 2 p0
    match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 16) 2 p0 with
    | .error _ => (do
      let i4 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 16) 2 p0
      let i5 ← pure ((.error i4) : Except Zig.ErrName (BitVec 16))
      pure (.ret i5))
    | .ok v3 => (do
      Zig.loadDiscardBytes 4 2 p0
      match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 16) 2 p0 with
      | .error _ => (do
        let i9 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 16) 2 p0
        let i10 ← pure ((.error i9) : Except Zig.ErrName (BitVec 16))
        pure (.ret i10))
      | .ok v8 => (do
        Zig.store (α := BitVec 16) 2 v3 p1
        let i13 ← Zig.load (BitVec 16) 2 v8
        let i14 ← pure ((.ok i13) : Except Zig.ErrName (BitVec 16))
        pure (.ret i14)))) : Zig.MM writeAlias16Locals writeAlias16Exit).run' (default : writeAlias16Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] writeAlias16

structure writeAlias32Locals where
  deriving Inhabited

inductive writeAlias32Exit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def writeAlias32 (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Except Zig.ErrName (BitVec 32)) := do
  let e ← ((do
    Zig.loadDiscardBytes 8 4 p0
    match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 32) 4 p0 with
    | .error _ => (do
      let i4 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 32) 4 p0
      let i5 ← pure ((.error i4) : Except Zig.ErrName (BitVec 32))
      pure (.ret i5))
    | .ok v3 => (do
      Zig.loadDiscardBytes 8 4 p0
      match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 32) 4 p0 with
      | .error _ => (do
        let i9 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 32) 4 p0
        let i10 ← pure ((.error i9) : Except Zig.ErrName (BitVec 32))
        pure (.ret i10))
      | .ok v8 => (do
        Zig.store (α := BitVec 32) 4 v3 p1
        let i13 ← Zig.load (BitVec 32) 4 v8
        let i14 ← pure ((.ok i13) : Except Zig.ErrName (BitVec 32))
        pure (.ret i14)))) : Zig.MM writeAlias32Locals writeAlias32Exit).run' (default : writeAlias32Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] writeAlias32

structure writeAlias64Locals where
  deriving Inhabited

inductive writeAlias64Exit where
  | ret (v : Except Zig.ErrName (BitVec 64))

def writeAlias64 (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    Zig.loadDiscardBytes 16 8 p0
    match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 64) 8 p0 with
    | .error _ => (do
      let i4 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 64) 8 p0
      let i5 ← pure ((.error i4) : Except Zig.ErrName (BitVec 64))
      pure (.ret i5))
    | .ok v3 => (do
      Zig.loadDiscardBytes 16 8 p0
      match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 64) 8 p0 with
      | .error _ => (do
        let i9 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 64) 8 p0
        let i10 ← pure ((.error i9) : Except Zig.ErrName (BitVec 64))
        pure (.ret i10))
      | .ok v8 => (do
        Zig.store (α := BitVec 64) 8 v3 p1
        let i13 ← Zig.load (BitVec 64) 8 v8
        let i14 ← pure ((.ok i13) : Except Zig.ErrName (BitVec 64))
        pure (.ret i14)))) : Zig.MM writeAlias64Locals writeAlias64Exit).run' (default : writeAlias64Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] writeAlias64

structure writeAliasAnyLocals where
  deriving Inhabited

inductive writeAliasAnyExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def writeAliasAny (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Except Zig.ErrName (BitVec 32)) := do
  let e ← ((do
    Zig.loadDiscardBytes 8 4 p0
    match ← Zig.tryPayloadPtr (BitVec 32) 4 p0 with
    | .error _ => (do
      let i4 ← Zig.errCodeAt (BitVec 32) 4 p0
      let i5 ← pure ((.error i4) : Except Zig.ErrName (BitVec 32))
      pure (.ret i5))
    | .ok v3 => (do
      Zig.loadDiscardBytes 8 4 p0
      match ← Zig.tryPayloadPtr (BitVec 32) 4 p0 with
      | .error _ => (do
        let i9 ← Zig.errCodeAt (BitVec 32) 4 p0
        let i10 ← pure ((.error i9) : Except Zig.ErrName (BitVec 32))
        pure (.ret i10))
      | .ok v8 => (do
        Zig.store (α := BitVec 32) 4 v3 p1
        let i13 ← Zig.load (BitVec 32) 4 v8
        let i14 ← pure ((.ok i13) : Except Zig.ErrName (BitVec 32))
        pure (.ret i14)))) : Zig.MM writeAliasAnyLocals writeAliasAnyExit).run' (default : writeAliasAnyLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] writeAliasAny

structure writeAliasPairLocals where
  deriving Inhabited

inductive writeAliasPairExit where
  | ret (v : Except Zig.ErrName (Pair))

def writeAliasPair (p0 : Zig.Ptr) (p1 : Pair) : Zig.MemM (Except Zig.ErrName (Pair)) := do
  let e ← ((do
    Zig.loadDiscardBytes 12 4 p0
    match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (Pair) 4 p0 with
    | .error _ => (do
      let i4 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (Pair) 4 p0
      let i5 ← pure ((.error i4) : Except Zig.ErrName (Pair))
      pure (.ret i5))
    | .ok v3 => (do
      Zig.loadDiscardBytes 12 4 p0
      match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (Pair) 4 p0 with
      | .error _ => (do
        let i9 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (Pair) 4 p0
        let i10 ← pure ((.error i9) : Except Zig.ErrName (Pair))
        pure (.ret i10))
      | .ok v8 => (do
        Zig.store (α := Pair) 4 v3 p1
        let i13 ← Zig.load (Pair) 4 v8
        let i14 ← pure ((.ok i13) : Except Zig.ErrName (Pair))
        pure (.ret i14)))) : Zig.MM writeAliasPairLocals writeAliasPairExit).run' (default : writeAliasPairLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] writeAliasPair

structure writeAliasSignedLocals where
  deriving Inhabited

inductive writeAliasSignedExit where
  | ret (v : Except Zig.ErrName (BitVec 16))

def writeAliasSigned (p0 : Zig.Ptr) (p1 : BitVec 16) : Zig.MemM (Except Zig.ErrName (BitVec 16)) := do
  let e ← ((do
    Zig.loadDiscardBytes 4 2 p0
    match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 16) 2 p0 with
    | .error _ => (do
      let i4 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 16) 2 p0
      let i5 ← pure ((.error i4) : Except Zig.ErrName (BitVec 16))
      pure (.ret i5))
    | .ok v3 => (do
      let i7 ← pure (v3)
      Zig.loadDiscardBytes 4 2 p0
      match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 16) 2 p0 with
      | .error _ => (do
        let i10 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 16) 2 p0
        let i11 ← pure ((.error i10) : Except Zig.ErrName (BitVec 16))
        pure (.ret i11))
      | .ok v9 => (do
        Zig.store (α := BitVec 16) 2 i7 p1
        let i14 ← Zig.load (BitVec 16) 2 v9
        let i15 ← pure ((.ok i14) : Except Zig.ErrName (BitVec 16))
        pure (.ret i15)))) : Zig.MM writeAliasSignedLocals writeAliasSignedExit).run' (default : writeAliasSignedLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] writeAliasSigned

end TryLifetimes.V0_14_1.Payloads