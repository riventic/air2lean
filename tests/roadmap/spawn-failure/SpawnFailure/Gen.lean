-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean

/- Thread assignment policy: fallible; all declared spawn errors and Io.Group caller fallback are modeled. -/


namespace SpawnFailure

structure atomic_Value___anyopaque where
  raw : Option (Zig.Ptr)
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc atomic_Value___anyopaque where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.raw)]
  decode bs := do pure { raw := ← Zig.Enc.decodeAt bs 0 }

structure Thread_SpawnConfig where
  stack_size : BitVec 64
  allocator : Option (Zig.Allocator)
  deriving Repr, Inhabited, DecidableEq

structure Io_Group where
  token : atomic_Value___anyopaque
  state : BitVec 64
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Io_Group where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.token), (8, Zig.Enc.encode v.state)]
  decode bs := do pure { token := ← Zig.Enc.decodeAt bs 0, state := ← Zig.Enc.decodeAt bs 8 }

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

/-- The spawn targets of the program; fields are captured by value. -/
inductive Tgt where
  | writeWorker (a : (Zig.Ptr) × (BitVec 32))

/-- The child protocol obligation for the complete captured tuple. Pointer
identities are copied; a proof must explicitly justify ownership transfer or sharing. -/
abbrev Tgt.spawnInit {γ : Type} (P : Zig.Conc.Proto Tgt γ) (target : Tgt) (ghost : γ) : Prop :=
  P.init target ghost

/-- Each captured field in source order. A value is copied and carries no ownership;
a pointer or slice copies only its identity, so a spawn proof must hand over or share its
region (`Zig.Conc.Capture.grant`). An `other` field's obligation cannot be discharged. -/
def Tgt.captures : Tgt → List Zig.Conc.Capture
  | .writeWorker (capture0, _) => [.ptr capture0, .value]

structure writeWorkerLocals where
  deriving Inhabited

inductive writeWorkerExit where
  | ret

def writeWorker (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    Zig.store (α := BitVec 32) 4 p0 p1
    pure .ret) : Zig.MM writeWorkerLocals writeWorkerExit).run' (default : writeWorkerLocals)
  match e with
  | .ret => pure ()

structure groupAsyncLocals where
  out : Zig.Ptr
  group : Zig.Ptr
  deriving Inhabited

inductive groupAsyncExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

-- air2lean-premises: {"IOM-01":[0]}
def groupAsync (p0 : Zig.Io) (p1 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s2 ← Zig.allocStack 4 4
  let s4 ← Zig.allocStack 16 8
  let e ← ((do
    let i2 ← pure (← get).out
    Zig.store (α := BitVec 32) 4 i2 (0 : BitVec 32)
    let i4 ← pure (← get).group
    Zig.store (α := Io_Group) 8 i4 ({ token := ({ raw := none } : atomic_Value___anyopaque), state := (0 : BitVec 64) } : Io_Group)
    let i6 ← pure (i2, p1)
    let _i7 ← Zig.groupAsyncWithPolicyC .fallible i4 p0 (Tgt.writeWorker i6) ((fun a => (do let (capture0, capture1) := a; discard (Zig.ConcM.liftMem (writeWorker capture0 capture1)) : Zig.ConcM Tgt Unit)) i6)
    let i8 ← Zig.groupAwaitC i4 p0
    match i8 with
    | .error _ => (do
      let i10 ← Zig.callRC (Zig.unwrapErr i8)
      let i11 ← pure (i10)
      let i12 ← pure ((.error i11) : Except Zig.ErrName (BitVec 32))
      pure (.ret i12))
    | .ok _v9 => (do
      let i14 ← Zig.load (BitVec 32) 4 i2
      let i15 ← pure ((.ok i14) : Except Zig.ErrName (BitVec 32))
      pure (.ret i15))) : Zig.CM Tgt groupAsyncLocals groupAsyncExit).run' { (default : groupAsyncLocals) with out := s2, group := s4 }
  Zig.free s2
  Zig.free s4
  match e with
  | .ret v => pure v

structure groupConcurrentLocals where
  out : Zig.Ptr
  group : Zig.Ptr
  deriving Inhabited

inductive groupConcurrentExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

-- air2lean-premises: {"IOM-01":[0]}
def groupConcurrent (p0 : Zig.Io) (p1 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s2 ← Zig.allocStack 4 4
  let s4 ← Zig.allocStack 16 8
  let e ← ((do
    let i2 ← pure (← get).out
    Zig.store (α := BitVec 32) 4 i2 (0 : BitVec 32)
    let i4 ← pure (← get).group
    Zig.store (α := Io_Group) 8 i4 ({ token := ({ raw := none } : atomic_Value___anyopaque), state := (0 : BitVec 64) } : Io_Group)
    let i6 ← pure (i2, p1)
    let i7 ← Zig.groupConcurrentWithPolicyC .fallible i4 p0 (Tgt.writeWorker i6)
    match i7 with
    | .error _ => (do
      let i9 ← Zig.callRC (Zig.unwrapErr i7)
      let _i10 ← Zig.groupCancelC i4 p0
      let i11 ← pure (i9)
      let i12 ← pure ((.error i11) : Except Zig.ErrName (BitVec 32))
      pure (.ret i12))
    | .ok _v8 => (do
      let i14 ← Zig.groupAwaitC i4 p0
      match i14 with
      | .error _ => (do
        let i16 ← Zig.callRC (Zig.unwrapErr i14)
        let _i17 ← Zig.groupCancelC i4 p0
        let i18 ← pure (i16)
        let i19 ← pure ((.error i18) : Except Zig.ErrName (BitVec 32))
        pure (.ret i19))
      | .ok _v15 => (do
        let i21 ← Zig.load (BitVec 32) 4 i2
        let _i22 ← Zig.groupCancelC i4 p0
        let i23 ← pure ((.ok i21) : Except Zig.ErrName (BitVec 32))
        pure (.ret i23)))) : Zig.CM Tgt groupConcurrentLocals groupConcurrentExit).run' { (default : groupConcurrentLocals) with out := s2, group := s4 }
  Zig.free s2
  Zig.free s4
  match e with
  | .ret v => pure v

structure threadCatchLocals where
  out : Zig.Ptr
  deriving Inhabited

inductive threadCatchExit where
  | ret (v : BitVec 32)
  | br3 (v : Zig.ThreadId)

def threadCatch (p0 : BitVec 32) : Zig.ConcM Tgt (BitVec 32) := do
  let s1 ← Zig.allocStack 4 4
  let e ← ((do
    let i1 ← pure (← get).out
    Zig.store (α := BitVec 32) 4 i1 (0 : BitVec 32)
    match ← ((do
      let i4 ← pure (i1, p0)
      let i5 ← Zig.spawnWithPolicyC .fallible (Tgt.writeWorker i4)
      let i6 ← pure (Zig.isNonErr i5)
      if i6 then (do
        let i8 ← Zig.callRC (Zig.unwrapPayload i5)
        pure (.br3 i8))
      else (do
        let _i10 ← Zig.callRC (Zig.unwrapErr i5)
        let i11 ← Zig.load (BitVec 32) 4 i1
        pure (.ret i11))) : Zig.CM Tgt threadCatchLocals threadCatchExit) with
    | .br3 v3 => (do
      let _i13 ← Zig.joinC v3
      let i14 ← Zig.load (BitVec 32) 4 i1
      pure (.ret i14))
    | e => pure e) : Zig.CM Tgt threadCatchLocals threadCatchExit).run' { (default : threadCatchLocals) with out := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure threadPairLocals where
  left : Zig.Ptr
  right : Zig.Ptr
  deriving Inhabited

inductive threadPairExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def threadPair (p0 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s1 ← Zig.allocStack 4 4
  let s3 ← Zig.allocStack 4 4
  let e ← ((do
    let i1 ← pure (← get).left
    Zig.store (α := BitVec 32) 4 i1 (0 : BitVec 32)
    let i3 ← pure (← get).right
    Zig.store (α := BitVec 32) 4 i3 (0 : BitVec 32)
    let i5 ← pure (i1, p0)
    let i6 ← Zig.spawnWithPolicyC .fallible (Tgt.writeWorker i5)
    match i6 with
    | .error _ => (do
      let i8 ← Zig.callRC (Zig.unwrapErr i6)
      let i9 ← pure (i8)
      let i10 ← pure ((.error i9) : Except Zig.ErrName (BitVec 32))
      pure (.ret i10))
    | .ok v7 => (do
      let i12 ← pure (Zig.addWrap p0 (1 : BitVec 32))
      let i13 ← pure (i3, i12)
      let i14 ← Zig.spawnWithPolicyC .fallible (Tgt.writeWorker i13)
      match i14 with
      | .error _ => (do
        let i16 ← Zig.callRC (Zig.unwrapErr i14)
        let _i17 ← Zig.joinC v7
        let i18 ← pure (i16)
        let i19 ← pure ((.error i18) : Except Zig.ErrName (BitVec 32))
        pure (.ret i19))
      | .ok v15 => (do
        let _i21 ← Zig.joinC v7
        let _i22 ← Zig.joinC v15
        let i23 ← Zig.load (BitVec 32) 4 i1
        let i24 ← Zig.load (BitVec 32) 4 i3
        let i25 ← pure (Zig.addWrap i23 i24)
        let i26 ← pure ((.ok i25) : Except Zig.ErrName (BitVec 32))
        pure (.ret i26)))) : Zig.CM Tgt threadPairLocals threadPairExit).run' { (default : threadPairLocals) with left := s1, right := s3 }
  Zig.free s1
  Zig.free s3
  match e with
  | .ret v => pure v

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .writeWorker a =>
    let (capture0, capture1) := a
    discard (Zig.ConcM.liftMem (writeWorker capture0 capture1))

end SpawnFailure