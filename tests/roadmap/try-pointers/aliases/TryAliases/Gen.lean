-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"unverified","backend":"unverified","build_mode":"unverified","cpu":"unverified","endian":"little","error_layout":"reference-model","error_set_bits":16,"error_tracing":null,"export_stage":"unverified","features":[],"float_mode":"unverified","name":"legacy-abi64-le","pointer_bits":64,"schema":11,"target_triple":"unverified","zig_version":"0.16.0"}}
import ZigLean


namespace TryAliases

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

structure resetOnErrorLocals where
  deriving Inhabited

inductive resetOnErrorExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

def resetOnError (p0 : Zig.Ptr) (p1 : BitVec 8) : Zig.MemM (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    Zig.loadDiscardBytes 4 2 p0
    match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 p0 with
    | .error _ => (do
      let i4 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 p0
      let i5 ← pure ((.ok p1) : Except Zig.ErrName (BitVec 8))
      (letI : Zig.Enc (Except Zig.ErrName (BitVec 8)) := Zig.errorUnionEnc (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 8))); Zig.store (α := Except Zig.ErrName (BitVec 8)) 2 p0 i5)
      let i7 ← pure ((.error i4) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i7))
    | .ok v3 => (do
      let i9 ← pure ((.ok v3) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i9))) : Zig.MM resetOnErrorLocals resetOnErrorExit).run' (default : resetOnErrorLocals)
  match e with
  | .ret v => pure v

structure twoPathsLocals where
  deriving Inhabited

inductive twoPathsExit where
  | ret (v : Except Zig.ErrName (BitVec 8))

def twoPaths (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : BitVec 8) : Zig.MemM (Except Zig.ErrName (BitVec 8)) := do
  let e ← ((do
    Zig.loadDiscardBytes 4 2 p0
    match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 p0 with
    | .error _ => (do
      let i5 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 p0
      let i6 ← pure ((.error i5) : Except Zig.ErrName (BitVec 8))
      pure (.ret i6))
    | .ok v4 => (do
      Zig.loadDiscardBytes 4 2 p1
      match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 p1 with
      | .error _ => (do
        let i10 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 p1
        let i11 ← pure ((.error i10) : Except Zig.ErrName (BitVec 8))
        pure (.ret i11))
      | .ok v9 => (do
        Zig.store (α := BitVec 8) 1 v4 p2
        let i14 ← Zig.load (BitVec 8) 1 v9
        let i15 ← pure ((.ok i14) : Except Zig.ErrName (BitVec 8))
        pure (.ret i15)))) : Zig.MM twoPathsLocals twoPathsExit).run' (default : twoPathsLocals)
  match e with
  | .ret v => pure v

end TryAliases