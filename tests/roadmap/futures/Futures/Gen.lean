-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace Futures

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

/-- The spawn targets of the program; fields are captured by value. -/
inductive Tgt where
  | checked_future (futureSlot : Zig.Ptr) (a : BitVec 32)
  | fill_future (futureSlot : Zig.Ptr) (a : (Zig.Ptr) × (BitVec 32))
  | square_future (futureSlot : Zig.Ptr) (a : BitVec 32)
  | cancellable_future (futureSlot : Zig.Ptr) (a : (Zig.Io) × (BitVec 32))

/-- The child protocol obligation for the complete captured tuple. Pointer
identities are copied; a proof must explicitly justify ownership transfer or sharing. -/
abbrev Tgt.spawnInit {γ : Type} (P : Zig.Conc.Proto Tgt γ) (target : Tgt) (ghost : γ) : Prop :=
  P.init target ghost

/-- Each captured field in source order. A value is copied and carries no ownership;
a pointer or slice copies only its identity, so a spawn proof must hand over or share its
region (`Zig.Conc.Capture.grant`). An `other` field's obligation cannot be discharged. -/
def Tgt.captures : Tgt → List Zig.Conc.Capture
  | .checked_future _ _ => [.value]
  | .fill_future _ (capture0, _) => [.ptr capture0, .value]
  | .square_future _ _ => [.value]
  | .cancellable_future _ (_, _) => [.other, .value]

structure checkedLocals where
  deriving Inhabited

inductive checkedExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br1

def checked (p0 : BitVec 32) : Zig.Result (Except Zig.ErrName (BitVec 32)) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure (p0 == (0 : BitVec 32))
      if i2 then (do
        pure (.ret (.error "Zero" : Except Zig.ErrName (BitVec 32))))
      else (do
        pure .br1)) : Zig.M checkedLocals checkedExit) with
    | .br1 => (do
      let i6 ← Zig.sub false p0 (1 : BitVec 32)
      let i7 ← pure ((.ok i6) : Except Zig.ErrName (BitVec 32))
      pure (.ret i7))
    | e => pure e) : Zig.M checkedLocals checkedExit).run' (default : checkedLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure awaitErrorLocals where
  f : Zig.Ptr
  deriving Inhabited

inductive awaitErrorExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

-- air2lean-premises: {"IOM-01":[0]}
def awaitError (p0 : Zig.Io) (p1 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s2 ← Zig.allocStack 16 8
  let e ← ((do
    let i2 ← pure (← get).f
    let i3 ← pure (p1)
    let i4 ← (letI : Zig.Enc (Except Zig.ErrName (BitVec 32)) := Zig.errorUnionEnc (⟨#["Zero"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 32))); Zig.asyncWithPolicyC (α := Except Zig.ErrName (BitVec 32)) .available (fun futureSlot => Tgt.checked_future futureSlot i3) ((fun a => (do Zig.ConcM.liftMem (StateT.lift (checked a)))) i3))
    (letI : Zig.Enc (Zig.Future (Except Zig.ErrName (BitVec 32))) := @Zig.Future.instEnc (Except Zig.ErrName (BitVec 32)) (Zig.errorUnionEnc (⟨#["Zero"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 32)))); Zig.store (α := Zig.Future (Except Zig.ErrName (BitVec 32))) 8 i2 i4)
    let i6 ← (letI : Zig.Enc (Except Zig.ErrName (BitVec 32)) := Zig.errorUnionEnc (⟨#["Zero"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 32))); Zig.awaitC (α := Except Zig.ErrName (BitVec 32)) p0 i2)
    pure (.ret i6)) : Zig.CM Tgt awaitErrorLocals awaitErrorExit).run' { (default : awaitErrorLocals) with f := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v

structure fillLocals where
  deriving Inhabited

inductive fillExit where
  | ret

def fill (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    Zig.store (α := BitVec 32) 4 p0 p1
    pure .ret) : Zig.MM fillLocals fillExit).run' (default : fillLocals)
  match e with
  | .ret => pure ()

structure awaitOwnedLocals where
  out : Zig.Ptr
  f : Zig.Ptr
  deriving Inhabited

inductive awaitOwnedExit where
  | ret (v : BitVec 32)

-- air2lean-premises: {"IOM-01":[0]}
def awaitOwned (p0 : Zig.Io) (p1 : BitVec 32) : Zig.ConcM Tgt (BitVec 32) := do
  let s2 ← Zig.allocStack 4 4
  let s4 ← Zig.allocStack 8 8
  let e ← ((do
    let i2 ← pure (← get).out
    Zig.store (α := BitVec 32) 4 i2 (0 : BitVec 32)
    let i4 ← pure (← get).f
    let i5 ← pure (i2, p1)
    let i6 ← Zig.asyncWithPolicyC (α := Unit) .available (fun futureSlot => Tgt.fill_future futureSlot i5) ((fun a => (do let (capture0, capture1) := a; Zig.ConcM.liftMem (fill capture0 capture1))) i5)
    Zig.store (α := Zig.Future (Unit)) 8 i4 i6
    let _i8 ← Zig.awaitC (α := Unit) p0 i4
    let i9 ← Zig.load (BitVec 32) 4 i2
    pure (.ret i9)) : Zig.CM Tgt awaitOwnedLocals awaitOwnedExit).run' { (default : awaitOwnedLocals) with out := s2, f := s4 }
  Zig.free s2
  Zig.free s4
  match e with
  | .ret v => pure v

structure squareLocals where
  deriving Inhabited

inductive squareExit where
  | ret (v : BitVec 32)

def square (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (Zig.mulWrap p0 p0)
    pure (.ret i1)) : Zig.M squareLocals squareExit).run' (default : squareLocals)
  match e with
  | .ret v => pure v

structure awaitTwiceLocals where
  f : Zig.Ptr
  deriving Inhabited

inductive awaitTwiceExit where
  | ret (v : BitVec 32)

-- air2lean-premises: {"IOM-01":[0]}
def awaitTwice (p0 : Zig.Io) (p1 : BitVec 32) : Zig.ConcM Tgt (BitVec 32) := do
  let s2 ← Zig.allocStack 16 8
  let e ← ((do
    let i2 ← pure (← get).f
    let i3 ← pure (p1)
    let i4 ← Zig.asyncWithPolicyC (α := BitVec 32) .available (fun futureSlot => Tgt.square_future futureSlot i3) ((fun a => (do Zig.ConcM.liftMem (StateT.lift (square a)))) i3)
    Zig.store (α := Zig.Future (BitVec 32)) 8 i2 i4
    let i6 ← Zig.awaitC (α := BitVec 32) p0 i2
    let i7 ← Zig.awaitC (α := BitVec 32) p0 i2
    let i8 ← pure (Zig.addWrap i6 i7)
    pure (.ret i8)) : Zig.CM Tgt awaitTwiceLocals awaitTwiceExit).run' { (default : awaitTwiceLocals) with f := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v

structure awaitValueLocals where
  f : Zig.Ptr
  deriving Inhabited

inductive awaitValueExit where
  | ret (v : BitVec 32)

-- air2lean-premises: {"IOM-01":[0]}
def awaitValue (p0 : Zig.Io) (p1 : BitVec 32) : Zig.ConcM Tgt (BitVec 32) := do
  let s2 ← Zig.allocStack 16 8
  let e ← ((do
    let i2 ← pure (← get).f
    let i3 ← pure (p1)
    let i4 ← Zig.asyncWithPolicyC (α := BitVec 32) .available (fun futureSlot => Tgt.square_future futureSlot i3) ((fun a => (do Zig.ConcM.liftMem (StateT.lift (square a)))) i3)
    Zig.store (α := Zig.Future (BitVec 32)) 8 i2 i4
    let i6 ← Zig.awaitC (α := BitVec 32) p0 i2
    pure (.ret i6)) : Zig.CM Tgt awaitValueLocals awaitValueExit).run' { (default : awaitValueLocals) with f := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v

structure cancellableLocals where
  deriving Inhabited

inductive cancellableExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

-- air2lean-premises: {"IOM-01":[0]}
def cancellable (p0 : Zig.Io) (p1 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let e ← ((do
    let i2 ← Zig.checkCancelC p0
    match i2 with
    | .error _ => (do
      let i4 ← Zig.callRC (Zig.unwrapErr i2)
      let i5 ← pure ((.error i4) : Except Zig.ErrName (BitVec 32))
      pure (.ret i5))
    | .ok _v3 => (do
      let i7 ← pure (Zig.addWrap p1 (1 : BitVec 32))
      let i8 ← pure ((.ok i7) : Except Zig.ErrName (BitVec 32))
      pure (.ret i8))) : Zig.CM Tgt cancellableLocals cancellableExit).run' (default : cancellableLocals)
  match e with
  | .ret v => pure v

structure cancelValueLocals where
  f : Zig.Ptr
  deriving Inhabited

inductive cancelValueExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

-- air2lean-premises: {"IOM-01":[0]}
def cancelValue (p0 : Zig.Io) (p1 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s2 ← Zig.allocStack 16 8
  let e ← ((do
    let i2 ← pure (← get).f
    let i3 ← pure (p0, p1)
    let i4 ← (letI : Zig.Enc (Except Zig.ErrName (BitVec 32)) := Zig.errorUnionEnc (⟨#["Canceled"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 32))); Zig.asyncWithPolicyC (α := Except Zig.ErrName (BitVec 32)) .available (fun futureSlot => Tgt.cancellable_future futureSlot i3) ((fun a => (do let (capture0, capture1) := a; cancellable capture0 capture1)) i3))
    (letI : Zig.Enc (Zig.Future (Except Zig.ErrName (BitVec 32))) := @Zig.Future.instEnc (Except Zig.ErrName (BitVec 32)) (Zig.errorUnionEnc (⟨#["Canceled"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 32)))); Zig.store (α := Zig.Future (Except Zig.ErrName (BitVec 32))) 8 i2 i4)
    let i6 ← (letI : Zig.Enc (Except Zig.ErrName (BitVec 32)) := Zig.errorUnionEnc (⟨#["Canceled"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 32))); Zig.cancelC (α := Except Zig.ErrName (BitVec 32)) p0 i2)
    pure (.ret i6)) : Zig.CM Tgt cancelValueLocals cancelValueExit).run' { (default : cancelValueLocals) with f := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .checked_future futureSlot a => do
      let futureResult ← Zig.ConcM.liftMem (StateT.lift (checked a))
      Zig.ConcM.liftMem ((letI : Zig.Enc (Except Zig.ErrName (BitVec 32)) := Zig.errorUnionEnc (⟨#["Zero"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 32))); Zig.Future.complete futureSlot futureResult))
  | .fill_future futureSlot a =>
    let (capture0, capture1) := a
    do
      let futureResult ← Zig.ConcM.liftMem (fill capture0 capture1)
      Zig.ConcM.liftMem (Zig.Future.complete futureSlot futureResult)
  | .square_future futureSlot a => do
      let futureResult ← Zig.ConcM.liftMem (StateT.lift (square a))
      Zig.ConcM.liftMem (Zig.Future.complete futureSlot futureResult)
  | .cancellable_future futureSlot a =>
    let (capture0, capture1) := a
    do
      let futureResult ← cancellable capture0 capture1
      Zig.ConcM.liftMem ((letI : Zig.Enc (Except Zig.ErrName (BitVec 32)) := Zig.errorUnionEnc (⟨#["Canceled"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 32))); Zig.Future.complete futureSlot futureResult))

end Futures