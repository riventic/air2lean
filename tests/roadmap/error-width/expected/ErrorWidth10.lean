-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"gnu","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":10,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-gnu.2.31","zig_version":"0.16.0"}}
import ZigLean


namespace ErrorWidth10

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

structure loadOptionalLocals where
  deriving Inhabited

inductive loadOptionalExit where
  | ret (v : Option (Zig.ErrName))

def loadOptional (p0 : Zig.Ptr) : Zig.MemM (Option (Zig.ErrName)) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Option (Zig.ErrName)) := Zig.optionalErrorEncW 10 (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain); Zig.load (Option (Zig.ErrName)) 2 p0)
    pure (.ret i1)) : Zig.MM loadOptionalLocals loadOptionalExit).run' (default : loadOptionalLocals)
  match e with
  | .ret v => pure v

structure loadUnionLocals where
  deriving Inhabited

inductive loadUnionExit where
  | ret (v : Except Zig.ErrName (BitVec 8))

def loadUnion (p0 : Zig.Ptr) : Zig.MemM (Except Zig.ErrName (BitVec 8)) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Except Zig.ErrName (BitVec 8)) := Zig.errorUnionEncW 10 (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 8))); Zig.load (Except Zig.ErrName (BitVec 8)) 2 p0)
    pure (.ret i1)) : Zig.MM loadUnionLocals loadUnionExit).run' (default : loadUnionLocals)
  match e with
  | .ret v => pure v

structure setPayloadLocals where
  deriving Inhabited

inductive setPayloadExit where
  | ret (v : Bool)

def setPayload (p0 : Zig.Ptr) (p1 : BitVec 8) : Zig.MemM (Bool) := do
  let e ← ((do
    let i2 ← Zig.errSetOkW 10 (BitVec 8) 2 p0
    Zig.store (α := BitVec 8) 1 i2 p1
    let i4 ← Zig.finiteErrIsErrAtW 10 (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 p0
    pure (.ret i4)) : Zig.MM setPayloadLocals setPayloadExit).run' (default : setPayloadLocals)
  match e with
  | .ret v => pure v

structure storeErrorLocals where
  deriving Inhabited

inductive storeErrorExit where
  | ret (v : Zig.ErrName)

def storeError (p0 : Zig.Ptr) (p1 : Zig.ErrName) : Zig.MemM (Zig.ErrName) := do
  let e ← ((do
    (letI : Zig.Enc (Zig.ErrName) := Zig.errorEncW 10 (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain); Zig.store (α := Zig.ErrName) 2 p0 p1)
    let i3 ← (letI : Zig.Enc (Zig.ErrName) := Zig.errorEncW 10 (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain); Zig.load (Zig.ErrName) 2 p0)
    pure (.ret i3)) : Zig.MM storeErrorLocals storeErrorExit).run' (default : storeErrorLocals)
  match e with
  | .ret v => pure v

structure storeOptionalLocals where
  deriving Inhabited

inductive storeOptionalExit where
  | ret (v : Bool)

def storeOptional (p0 : Zig.Ptr) (p1 : Option (Zig.ErrName)) : Zig.MemM (Bool) := do
  let e ← ((do
    (letI : Zig.Enc (Option (Zig.ErrName)) := Zig.optionalErrorEncW 10 (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain); Zig.store (α := Option (Zig.ErrName)) 2 p0 p1)
    let i3 ← Zig.optionalErrorIsSomeW 10 (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) 2 p0
    pure (.ret i3)) : Zig.MM storeOptionalLocals storeOptionalExit).run' (default : storeOptionalLocals)
  match e with
  | .ret v => pure v

structure unionTry64Locals where
  deriving Inhabited

inductive unionTry64Exit where
  | ret (v : Except Zig.ErrName (BitVec 64))

def unionTry64 (p0 : Zig.Ptr) (p1 : Except Zig.ErrName (BitVec 64)) : Zig.MemM (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    (letI : Zig.Enc (Except Zig.ErrName (BitVec 64)) := Zig.errorUnionEncW 10 (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 64))); Zig.store (α := Except Zig.ErrName (BitVec 64)) 8 p0 p1)
    match ← Zig.finiteTryPayloadPtrW 10 (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 64) 8 p0 with
    | .error _ => (do
      let i4 ← Zig.finiteErrCodeAtW 10 (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 64) 8 p0
      let i5 ← pure ((.error i4) : Except Zig.ErrName (BitVec 64))
      pure (.ret i5))
    | .ok v3 => (do
      let i7 ← Zig.load (BitVec 64) 8 v3
      let i8 ← pure ((.ok i7) : Except Zig.ErrName (BitVec 64))
      pure (.ret i8))) : Zig.MM unionTry64Locals unionTry64Exit).run' (default : unionTry64Locals)
  match e with
  | .ret v => pure v

structure unionTry8Locals where
  deriving Inhabited

inductive unionTry8Exit where
  | ret (v : Except Zig.ErrName (BitVec 8))

def unionTry8 (p0 : Zig.Ptr) (p1 : Except Zig.ErrName (BitVec 8)) : Zig.MemM (Except Zig.ErrName (BitVec 8)) := do
  let e ← ((do
    (letI : Zig.Enc (Except Zig.ErrName (BitVec 8)) := Zig.errorUnionEncW 10 (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 8))); Zig.store (α := Except Zig.ErrName (BitVec 8)) 2 p0 p1)
    match ← Zig.finiteTryPayloadPtrW 10 (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 p0 with
    | .error _ => (do
      let i4 ← Zig.finiteErrCodeAtW 10 (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 p0
      let i5 ← pure ((.error i4) : Except Zig.ErrName (BitVec 8))
      pure (.ret i5))
    | .ok v3 => (do
      let i7 ← Zig.load (BitVec 8) 1 v3
      let i8 ← pure ((.ok i7) : Except Zig.ErrName (BitVec 8))
      pure (.ret i8))) : Zig.MM unionTry8Locals unionTry8Exit).run' (default : unionTry8Locals)
  match e with
  | .ret v => pure v

end ErrorWidth10