import ZigLean


namespace ThreadTuples

structure atomic_Value_u32 where
  raw : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc atomic_Value_u32 where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.raw)]
  decode bs := do pure { raw := ← Zig.Enc.decodeAt bs 0 }

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
  | atomicWorker (a : (Zig.Ptr) × (Zig.Ptr) × (BitVec 32) × (BitVec 32))
  | copyWorker (a : (Zig.Ptr) × (BitVec 32) × (BitVec 32) × (BitVec 32))
  | zeroWorker (a : Unit)
  | ZeroWorker_u8_run (a : Unit)
  | mixedWorker (a : (BitVec 32) × (Zig.Ptr) × (BitVec 32) × (Zig.Ptr))

/-- The child protocol obligation for the complete captured tuple. Pointer
identities are copied; a proof must explicitly justify ownership transfer or sharing. -/
abbrev Tgt.spawnInit {γ : Type} (P : Zig.Conc.Proto Tgt γ) (target : Tgt) (ghost : γ) : Prop :=
  P.init target ghost

/-- Each captured field in source order. A value is copied and carries no ownership;
a pointer or slice copies only its identity, so a spawn proof must hand over or share its
region (`Zig.Conc.Capture.grant`). An `other` field's obligation cannot be discharged. -/
def Tgt.captures : Tgt → List Zig.Conc.Capture
  | .atomicWorker (capture0, capture1, _, _) => [.ptr capture0, .ptr capture1, .value, .value]
  | .copyWorker (capture0, _, _, _) => [.ptr capture0, .value, .value, .value]
  | .zeroWorker _ => []
  | .ZeroWorker_u8_run _ => []
  | .mixedWorker (_, capture1, _, capture3) => [.value, .ptr capture1, .value, .ptr capture3]

structure atomic_Value_u32_initLocals where
  local1 : atomic_Value_u32
  deriving Inhabited

inductive atomic_Value_u32_initExit where
  | ret (v : atomic_Value_u32)

def atomic_Value_u32_init (p0 : BitVec 32) : Zig.Result (atomic_Value_u32) := do
  let e ← ((do
    modify (fun s => { s with local1 := { s.local1 with raw := p0 } })
    pure (.ret (← get).local1)) : Zig.M atomic_Value_u32_initLocals atomic_Value_u32_initExit).run' (default : atomic_Value_u32_initLocals)
  match e with
  | .ret v => pure v

structure ZeroWorker_u8_runLocals where
  deriving Inhabited

inductive ZeroWorker_u8_runExit where
  | ret

def ZeroWorker_u8_run  : Zig.Result (Unit) := do
  let e ← ((do
    pure .ret) : Zig.M ZeroWorker_u8_runLocals ZeroWorker_u8_runExit).run' (default : ZeroWorker_u8_runLocals)
  match e with
  | .ret => pure ()

structure atomicWorkerLocals where
  deriving Inhabited

inductive atomicWorkerExit where
  | ret
  | br6 (v : BitVec 32)

def atomicWorker (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : BitVec 32) (p3 : BitVec 32) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i4 ← pure (Zig.addWrap p2 p3)
    Zig.store (α := BitVec 32) 4 p0 i4
    match ← ((do
      let i7 ← pure p1
      let i8 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.seqCst 4 i7 p3
      pure (.br6 i8)) : Zig.CM Tgt atomicWorkerLocals atomicWorkerExit) with
    | .br6 _v6 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt atomicWorkerLocals atomicWorkerExit).run' (default : atomicWorkerLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure atomicSharedLocals where
  shared : Zig.Ptr
  left : Zig.Ptr
  right : Zig.Ptr
  deriving Inhabited

inductive atomicSharedExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br30 (v : BitVec 32)

def atomicShared (p0 : BitVec 32) (p1 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s5 ← Zig.allocStack 4 4
  let s2 ← Zig.allocStack 4 4
  let s7 ← Zig.allocStack 4 4
  let e ← ((do
    let i2 ← pure (← get).shared
    let i3 ← Zig.callRC (atomic_Value_u32_init (0 : BitVec 32))
    Zig.store (α := atomic_Value_u32) 4 i2 i3
    let i5 ← pure (← get).left
    Zig.store (α := BitVec 32) 4 i5 (0 : BitVec 32)
    let i7 ← pure (← get).right
    Zig.store (α := BitVec 32) 4 i7 (0 : BitVec 32)
    let i9 ← pure (i5, i2, p0, p1)
    let i10 ← Zig.spawnC (Tgt.atomicWorker i9)
    match i10 with
    | .error _ => (do
      let i12 ← Zig.callRC (Zig.unwrapErr i10)
      let i13 ← pure (i12)
      let i14 ← pure ((.error i13) : Except Zig.ErrName (BitVec 32))
      pure (.ret i14))
    | .ok v11 => (do
      let i16 ← pure (i7, i2, p1, p0)
      let i17 ← Zig.spawnC (Tgt.atomicWorker i16)
      match i17 with
      | .error _ => (do
        let i19 ← Zig.callRC (Zig.unwrapErr i17)
        let _i20 ← Zig.joinC v11
        let i21 ← pure (i19)
        let i22 ← pure ((.error i21) : Except Zig.ErrName (BitVec 32))
        pure (.ret i22))
      | .ok v18 => (do
        let _i24 ← Zig.joinC v11
        let _i25 ← Zig.joinC v18
        let i26 ← Zig.load (BitVec 32) 4 i5
        let i27 ← Zig.load (BitVec 32) 4 i7
        let i28 ← pure (Zig.addWrap i26 i27)
        let i29 ← pure (i2)
        match ← ((do
          let i31 ← pure i29
          let i32 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.seqCst 4 i31
          pure (.br30 i32)) : Zig.CM Tgt atomicSharedLocals atomicSharedExit) with
        | .br30 v30 => (do
          let i34 ← pure (Zig.addWrap i28 v30)
          let i35 ← pure ((.ok i34) : Except Zig.ErrName (BitVec 32))
          pure (.ret i35))
        | e => pure e))) : Zig.CM Tgt atomicSharedLocals atomicSharedExit).run' { (default : atomicSharedLocals) with left := s5, shared := s2, right := s7 }
  Zig.free s5
  Zig.free s2
  Zig.free s7
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure copyWorkerLocals where
  deriving Inhabited

inductive copyWorkerExit where
  | ret

def copyWorker (p0 : Zig.Ptr) (p1 : BitVec 32) (p2 : BitVec 32) (p3 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    let i4 ← pure (Zig.mulWrap p1 (3 : BitVec 32))
    let i5 ← pure (Zig.mulWrap p2 (5 : BitVec 32))
    let i6 ← pure (Zig.addWrap i4 i5)
    let i7 ← pure (Zig.mulWrap p3 (7 : BitVec 32))
    let i8 ← pure (Zig.addWrap i6 i7)
    Zig.store (α := BitVec 32) 4 p0 i8
    pure .ret) : Zig.MM copyWorkerLocals copyWorkerExit).run' (default : copyWorkerLocals)
  match e with
  | .ret => pure ()

structure copiedLocals where
  snapshot : BitVec 32
  out : Zig.Ptr
  deriving Inhabited

inductive copiedExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def copied (p0 : BitVec 32) (p1 : BitVec 32) (p2 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s5 ← Zig.allocStack 4 4
  let e ← ((do
    modify (fun s => { s with snapshot := p0 })
    let i5 ← pure (← get).out
    Zig.store (α := BitVec 32) 4 i5 (0 : BitVec 32)
    let i7 ← pure ((← get).snapshot)
    let i8 ← pure (i5, i7, p1, p2)
    let i9 ← Zig.spawnC (Tgt.copyWorker i8)
    match i9 with
    | .error _ => (do
      let i11 ← Zig.callRC (Zig.unwrapErr i9)
      let i12 ← pure (i11)
      let i13 ← pure ((.error i12) : Except Zig.ErrName (BitVec 32))
      pure (.ret i13))
    | .ok v10 => (do
      modify (fun s => { s with snapshot := (99 : BitVec 32) })
      let _i16 ← Zig.joinC v10
      let i17 ← Zig.load (BitVec 32) 4 i5
      let i18 ← pure ((← get).snapshot)
      let i19 ← pure (Zig.addWrap i17 i18)
      let i20 ← pure ((.ok i19) : Except Zig.ErrName (BitVec 32))
      pure (.ret i20))) : Zig.CM Tgt copiedLocals copiedExit).run' { (default : copiedLocals) with out := s5 }
  Zig.free s5
  match e with
  | .ret v => pure v

structure zeroWorkerLocals where
  deriving Inhabited

inductive zeroWorkerExit where
  | ret

def zeroWorker  : Zig.Result (Unit) := do
  let e ← ((do
    pure .ret) : Zig.M zeroWorkerLocals zeroWorkerExit).run' (default : zeroWorkerLocals)
  match e with
  | .ret => pure ()

structure emptyLocals where
  deriving Inhabited

inductive emptyExit where
  | ret (v : Except Zig.ErrName (Unit))

def empty  : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    let i0 ← Zig.spawnC (Tgt.zeroWorker ())
    match i0 with
    | .error _ => (do
      let i2 ← Zig.callRC (Zig.unwrapErr i0)
      let i3 ← pure (i2)
      let i4 ← pure ((.error i3) : Except Zig.ErrName (Unit))
      pure (.ret i4))
    | .ok v1 => (do
      let _i6 ← Zig.joinC v1
      pure (.ret (.ok () : Except Zig.ErrName (Unit))))) : Zig.CM Tgt emptyLocals emptyExit).run' (default : emptyLocals)
  match e with
  | .ret v => pure v

structure genericEmptyLocals where
  deriving Inhabited

inductive genericEmptyExit where
  | ret (v : Except Zig.ErrName (Unit))

def genericEmpty  : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    let i0 ← Zig.spawnC (Tgt.ZeroWorker_u8_run ())
    match i0 with
    | .error _ => (do
      let i2 ← Zig.callRC (Zig.unwrapErr i0)
      let i3 ← pure (i2)
      let i4 ← pure ((.error i3) : Except Zig.ErrName (Unit))
      pure (.ret i4))
    | .ok v1 => (do
      let _i6 ← Zig.joinC v1
      pure (.ret (.ok () : Except Zig.ErrName (Unit))))) : Zig.CM Tgt genericEmptyLocals genericEmptyExit).run' (default : genericEmptyLocals)
  match e with
  | .ret v => pure v

structure mixedWorkerLocals where
  deriving Inhabited

inductive mixedWorkerExit where
  | ret

def mixedWorker (p0 : BitVec 32) (p1 : Zig.Ptr) (p2 : BitVec 32) (p3 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i4 ← pure (Zig.mulWrap p0 (17 : BitVec 32))
    let i5 ← pure (Zig.mulWrap p2 (3 : BitVec 32))
    let i6 ← pure (Zig.addWrap i4 i5)
    Zig.store (α := BitVec 32) 4 p1 i6
    let i8 ← pure (Zig.mulWrap p0 (5 : BitVec 32))
    let i9 ← pure (Zig.mulWrap p2 (11 : BitVec 32))
    let i10 ← pure (Zig.addWrap i8 i9)
    Zig.store (α := BitVec 32) 4 p3 i10
    pure .ret) : Zig.MM mixedWorkerLocals mixedWorkerExit).run' (default : mixedWorkerLocals)
  match e with
  | .ret => pure ()

structure groupMixedLocals where
  out : Zig.Ptr
  other : Zig.Ptr
  group : Zig.Ptr
  deriving Inhabited

inductive groupMixedExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def groupMixed (p0 : Zig.Io) (p1 : BitVec 32) (p2 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s7 ← Zig.allocStack 16 8
  let s3 ← Zig.allocStack 4 4
  let s5 ← Zig.allocStack 4 4
  let e ← ((do
    let i3 ← pure (← get).out
    Zig.store (α := BitVec 32) 4 i3 (0 : BitVec 32)
    let i5 ← pure (← get).other
    Zig.store (α := BitVec 32) 4 i5 (0 : BitVec 32)
    let i7 ← pure (← get).group
    Zig.store (α := Io_Group) 8 i7 ({ token := ({ raw := none } : atomic_Value___anyopaque), state := (0 : BitVec 64) } : Io_Group)
    let _i9 ← Zig.groupAsyncC i7 p0 (Tgt.zeroWorker ())
    let i10 ← pure (p1, i3, p2, i5)
    let _i11 ← Zig.groupAsyncC i7 p0 (Tgt.mixedWorker i10)
    let i12 ← Zig.groupConcurrentC i7 p0 (Tgt.zeroWorker ())
    match i12 with
    | .error _ => (do
      let i14 ← Zig.callRC (Zig.unwrapErr i12)
      let _i15 ← Zig.groupCancelC i7 p0
      let i16 ← pure (i14)
      let i17 ← pure ((.error i16) : Except Zig.ErrName (BitVec 32))
      pure (.ret i17))
    | .ok _v13 => (do
      let i19 ← Zig.groupAwaitC i7 p0
      match i19 with
      | .error _ => (do
        let i21 ← Zig.callRC (Zig.unwrapErr i19)
        let _i22 ← Zig.groupCancelC i7 p0
        let i23 ← pure (i21)
        let i24 ← pure ((.error i23) : Except Zig.ErrName (BitVec 32))
        pure (.ret i24))
      | .ok _v20 => (do
        let i26 ← Zig.load (BitVec 32) 4 i3
        let i27 ← Zig.load (BitVec 32) 4 i5
        let i28 ← pure (Zig.mulWrap i27 (7 : BitVec 32))
        let i29 ← pure (Zig.addWrap i26 i28)
        let _i30 ← Zig.groupCancelC i7 p0
        let i31 ← pure ((.ok i29) : Except Zig.ErrName (BitVec 32))
        pure (.ret i31)))) : Zig.CM Tgt groupMixedLocals groupMixedExit).run' { (default : groupMixedLocals) with group := s7, out := s3, other := s5 }
  Zig.free s7
  Zig.free s3
  Zig.free s5
  match e with
  | .ret v => pure v

structure mixedLocals where
  out : Zig.Ptr
  other : Zig.Ptr
  deriving Inhabited

inductive mixedExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def mixed (p0 : BitVec 32) (p1 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s2 ← Zig.allocStack 4 4
  let s4 ← Zig.allocStack 4 4
  let e ← ((do
    let i2 ← pure (← get).out
    Zig.store (α := BitVec 32) 4 i2 (0 : BitVec 32)
    let i4 ← pure (← get).other
    Zig.store (α := BitVec 32) 4 i4 (0 : BitVec 32)
    let i6 ← pure (p0, i2, p1, i4)
    let i7 ← Zig.spawnC (Tgt.mixedWorker i6)
    match i7 with
    | .error _ => (do
      let i9 ← Zig.callRC (Zig.unwrapErr i7)
      let i10 ← pure (i9)
      let i11 ← pure ((.error i10) : Except Zig.ErrName (BitVec 32))
      pure (.ret i11))
    | .ok v8 => (do
      let _i13 ← Zig.joinC v8
      let i14 ← Zig.load (BitVec 32) 4 i2
      let i15 ← Zig.load (BitVec 32) 4 i4
      let i16 ← pure (Zig.mulWrap i15 (7 : BitVec 32))
      let i17 ← pure (Zig.addWrap i14 i16)
      let i18 ← pure ((.ok i17) : Except Zig.ErrName (BitVec 32))
      pure (.ret i18))) : Zig.CM Tgt mixedLocals mixedExit).run' { (default : mixedLocals) with out := s2, other := s4 }
  Zig.free s2
  Zig.free s4
  match e with
  | .ret v => pure v

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .atomicWorker a =>
    let (capture0, capture1, capture2, capture3) := a
    discard (atomicWorker capture0 capture1 capture2 capture3)
  | .copyWorker a =>
    let (capture0, capture1, capture2, capture3) := a
    discard (Zig.ConcM.liftMem (copyWorker capture0 capture1 capture2 capture3))
  | .zeroWorker a => discard (Zig.ConcM.liftMem (StateT.lift (zeroWorker)))
  | .ZeroWorker_u8_run a => discard (Zig.ConcM.liftMem (StateT.lift (ZeroWorker_u8_run)))
  | .mixedWorker a =>
    let (capture0, capture1, capture2, capture3) := a
    discard (Zig.ConcM.liftMem (mixedWorker capture0 capture1 capture2 capture3))

end ThreadTuples