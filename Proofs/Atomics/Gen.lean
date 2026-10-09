import ZigLean


namespace Atomics

structure WwCtx where
  a : Zig.Ptr
  b : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc WwCtx where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.a), (8, Zig.Enc.encode v.b)]
  decode bs := do pure { a := ← Zig.Enc.decodeAt bs 0, b := ← Zig.Enc.decodeAt bs 8 }

structure atomic_Value_u32 where
  raw : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc atomic_Value_u32 where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.raw)]
  decode bs := do pure { raw := ← Zig.Enc.decodeAt bs 0 }

structure Stack where
  head : atomic_Value_u32
  next : Vector (BitVec 32) 3
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Stack where
  size := 16
  align := 4
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.head), (4, Zig.Enc.encode v.next)]
  decode bs := do pure { head := ← Zig.Enc.decodeAt bs 0, next := ← Zig.Enc.decodeAt bs 4 }

structure SbCtx where
  mine : Zig.Ptr
  other : Zig.Ptr
  out : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc SbCtx where
  size := 24
  align := 8
  encode v := Zig.Enc.fields 24 [(0, Zig.Enc.encode v.mine), (8, Zig.Enc.encode v.other), (16, Zig.Enc.encode v.out)]
  decode bs := do pure { mine := ← Zig.Enc.decodeAt bs 0, other := ← Zig.Enc.decodeAt bs 8, out := ← Zig.Enc.decodeAt bs 16 }

structure PushCtx where
  s : Zig.Ptr
  node : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc PushCtx where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.s), (8, Zig.Enc.encode v.node)]
  decode bs := do pure { s := ← Zig.Enc.decodeAt bs 0, node := ← Zig.Enc.decodeAt bs 8 }

structure MpCtx where
  data : Zig.Ptr
  flag : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc MpCtx where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.data), (8, Zig.Enc.encode v.flag)]
  decode bs := do pure { data := ← Zig.Enc.decodeAt bs 0, flag := ← Zig.Enc.decodeAt bs 8 }

structure Thread_SpawnConfig where
  stack_size : BitVec 64
  allocator : Option (Zig.Allocator)
  deriving Repr, Inhabited, DecidableEq

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

/-- The spawn targets of the program. -/
inductive Tgt where
  | mpWriter (a : Zig.Ptr)
  | mpWriterRelaxed (a : Zig.Ptr)
  | sb (a : Zig.Ptr)
  | push (a : Zig.Ptr)
  | ww (a : Zig.Ptr)

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

structure mpWriterLocals where
  deriving Inhabited

inductive mpWriterExit where
  | ret
  | br6

def mpWriter (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let i2 ← Zig.load (Zig.Ptr) 8 i1
    Zig.store (α := BitVec 32) 4 i2 (42 : BitVec 32)
    let i4 ← Zig.callMC (Zig.ptrProject p0 (·.add 8))
    let i5 ← Zig.load (Zig.Ptr) 8 i4
    match ← ((do
      let i7 ← pure i5
      Zig.atomicStoreC Zig.AtomicOrder.release 4 i7 (1 : BitVec 32)
      pure .br6) : Zig.CM Tgt mpWriterLocals mpWriterExit) with
    | .br6 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt mpWriterLocals mpWriterExit).run' (default : mpWriterLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure mpRelAcqLocals where
  data : Zig.Ptr
  flag : Zig.Ptr
  c : Zig.Ptr
  deriving Inhabited

inductive mpRelAcqExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br19 (v : BitVec 32)
  | br17 (v : BitVec 32)

def mpRelAcq  : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s0 ← Zig.allocStack 4 4
  let s2 ← Zig.allocStack 4 4
  let s5 ← Zig.allocStack 16 8
  let e ← ((do
    let i0 ← pure (← get).data
    Zig.store (α := BitVec 32) 4 i0 (0 : BitVec 32)
    let i2 ← pure (← get).flag
    let i3 ← Zig.callRC (atomic_Value_u32_init (0 : BitVec 32))
    Zig.store (α := atomic_Value_u32) 4 i2 i3
    let i5 ← pure (← get).c
    let i6 ← pure i5
    Zig.store (α := Zig.Ptr) 8 i6 i0
    let i8 ← Zig.callMC (Zig.ptrProject i5 (·.add 8))
    Zig.store (α := Zig.Ptr) 8 i8 i2
    let i10 ← pure (i5)
    let i11 ← Zig.spawnC (Tgt.mpWriter i10)
    match i11 with
    | .error _ => (do
      let i13 ← Zig.callRC (Zig.unwrapErr i11)
      let i14 ← pure (i13)
      let i15 ← pure ((.error i14) : Except Zig.ErrName (BitVec 32))
      pure (.ret i15))
    | .ok v12 => (do
      match ← ((do
        let i18 ← pure (i2)
        match ← ((do
          let i20 ← pure i18
          let i21 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.acquire 4 i20
          pure (.br19 i21)) : Zig.CM Tgt mpRelAcqLocals mpRelAcqExit) with
        | .br19 v19 => (do
          let i23 ← pure (v19 == (1 : BitVec 32))
          if i23 then (do
            let i25 ← Zig.load (BitVec 32) 4 i0
            pure (.br17 i25))
          else (do
            pure (.br17 (0 : BitVec 32))))
        | e => pure e) : Zig.CM Tgt mpRelAcqLocals mpRelAcqExit) with
      | .br17 v17 => (do
        let _i28 ← Zig.joinC v12
        let i29 ← pure ((.ok v17) : Except Zig.ErrName (BitVec 32))
        pure (.ret i29))
      | e => pure e)) : Zig.CM Tgt mpRelAcqLocals mpRelAcqExit).run' { (default : mpRelAcqLocals) with data := s0, flag := s2, c := s5 }
  Zig.free s0
  Zig.free s2
  Zig.free s5
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mpWriterRelaxedLocals where
  deriving Inhabited

inductive mpWriterRelaxedExit where
  | ret
  | br6

def mpWriterRelaxed (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let i2 ← Zig.load (Zig.Ptr) 8 i1
    Zig.store (α := BitVec 32) 4 i2 (42 : BitVec 32)
    let i4 ← Zig.callMC (Zig.ptrProject p0 (·.add 8))
    let i5 ← Zig.load (Zig.Ptr) 8 i4
    match ← ((do
      let i7 ← pure i5
      Zig.atomicStoreC Zig.AtomicOrder.relaxed 4 i7 (1 : BitVec 32)
      pure .br6) : Zig.CM Tgt mpWriterRelaxedLocals mpWriterRelaxedExit) with
    | .br6 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt mpWriterRelaxedLocals mpWriterRelaxedExit).run' (default : mpWriterRelaxedLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure mpRelaxedLocals where
  data : Zig.Ptr
  flag : Zig.Ptr
  c : Zig.Ptr
  deriving Inhabited

inductive mpRelaxedExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br19 (v : BitVec 32)
  | br17 (v : BitVec 32)

def mpRelaxed  : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s0 ← Zig.allocStack 4 4
  let s2 ← Zig.allocStack 4 4
  let s5 ← Zig.allocStack 16 8
  let e ← ((do
    let i0 ← pure (← get).data
    Zig.store (α := BitVec 32) 4 i0 (0 : BitVec 32)
    let i2 ← pure (← get).flag
    let i3 ← Zig.callRC (atomic_Value_u32_init (0 : BitVec 32))
    Zig.store (α := atomic_Value_u32) 4 i2 i3
    let i5 ← pure (← get).c
    let i6 ← pure i5
    Zig.store (α := Zig.Ptr) 8 i6 i0
    let i8 ← Zig.callMC (Zig.ptrProject i5 (·.add 8))
    Zig.store (α := Zig.Ptr) 8 i8 i2
    let i10 ← pure (i5)
    let i11 ← Zig.spawnC (Tgt.mpWriterRelaxed i10)
    match i11 with
    | .error _ => (do
      let i13 ← Zig.callRC (Zig.unwrapErr i11)
      let i14 ← pure (i13)
      let i15 ← pure ((.error i14) : Except Zig.ErrName (BitVec 32))
      pure (.ret i15))
    | .ok v12 => (do
      match ← ((do
        let i18 ← pure (i2)
        match ← ((do
          let i20 ← pure i18
          let i21 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.relaxed 4 i20
          pure (.br19 i21)) : Zig.CM Tgt mpRelaxedLocals mpRelaxedExit) with
        | .br19 v19 => (do
          let i23 ← pure (v19 == (1 : BitVec 32))
          if i23 then (do
            let i25 ← Zig.load (BitVec 32) 4 i0
            pure (.br17 i25))
          else (do
            pure (.br17 (0 : BitVec 32))))
        | e => pure e) : Zig.CM Tgt mpRelaxedLocals mpRelaxedExit) with
      | .br17 v17 => (do
        let _i28 ← Zig.joinC v12
        let i29 ← pure ((.ok v17) : Except Zig.ErrName (BitVec 32))
        pure (.ret i29))
      | e => pure e)) : Zig.CM Tgt mpRelaxedLocals mpRelaxedExit).run' { (default : mpRelaxedLocals) with data := s0, flag := s2, c := s5 }
  Zig.free s0
  Zig.free s2
  Zig.free s5
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure pushLocals where
  h : BitVec 32
  deriving Inhabited

inductive pushExit where
  | ret
  | br6 (v : BitVec 32)
  | br20
  | br35 (v : Option (BitVec 32))
  | br28 (v : BitVec 32)
  | br11
  | rep12

def push.again12 : pushExit → Bool
  | .rep12 => true
  | _ => false

def push.loop12 (p0 : Zig.Ptr) : Zig.CM Tgt pushLocals pushExit := do
  let i13 ← pure p0
  let i14 ← Zig.load (Zig.Ptr) 8 i13
  let i15 ← Zig.callMC (Zig.ptrProject i14 (·.add 4))
  let i16 ← Zig.callMC (Zig.ptrProject p0 (·.add 8))
  let i17 ← Zig.load (BitVec 32) 4 i16
  let i18 ← Zig.intCast false false 64 i17
  let i19 ← pure (Zig.lt false i18 (3 : BitVec 64))
  match ← ((do
    if i19 then (do
      pure .br20)
    else (do
      throw .outOfBounds)) : Zig.CM Tgt pushLocals pushExit) with
  | .br20 => (do
    let i25 ← Zig.callMC (Zig.ptrProject i15 (·.elem 4 i18))
    let i26 ← pure ((← get).h)
    Zig.store (α := BitVec 32) 4 i25 i26
    match ← ((do
      let i29 ← pure p0
      let i30 ← Zig.load (Zig.Ptr) 8 i29
      let i31 ← pure i30
      let i32 ← pure ((← get).h)
      let i33 ← Zig.callMC (Zig.ptrProject p0 (·.add 8))
      let i34 ← Zig.load (BitVec 32) 4 i33
      match ← ((do
        let i36 ← pure i31
        let i37 ← Zig.cmpxchgWeakC Zig.AtomicOrder.release Zig.AtomicOrder.relaxed 4 i36 i32 i34
        pure (.br35 i37)) : Zig.CM Tgt pushLocals pushExit) with
      | .br35 v35 => (do
        let i39 ← pure ((v35).isSome)
        if i39 then (do
          let i41 ← Zig.optPayload v35
          pure (.br28 i41))
        else (do
          pure .br11))
      | e => pure e) : Zig.CM Tgt pushLocals pushExit) with
    | .br28 v28 => (do
      modify (fun s => { s with h := v28 })
      pure .rep12)
    | e => pure e)
  | e => pure e

def push (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.load (Zig.Ptr) 8 i2
    let i4 ← pure i3
    let i5 ← pure (i4)
    match ← ((do
      let i7 ← pure i5
      let i8 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.relaxed 4 i7
      pure (.br6 i8)) : Zig.CM Tgt pushLocals pushExit) with
    | .br6 v6 => (do
      modify (fun s => { s with h := v6 })
      match ← ((do
        Zig.loop (push.loop12 p0) push.again12) : Zig.CM Tgt pushLocals pushExit) with
      | .br11 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt pushLocals pushExit).run' (default : pushLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure sbLocals where
  deriving Inhabited

inductive sbExit where
  | ret
  | br3
  | br12 (v : BitVec 32)

def sb (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let i2 ← Zig.load (Zig.Ptr) 8 i1
    match ← ((do
      let i4 ← pure i2
      Zig.atomicStoreC Zig.AtomicOrder.relaxed 4 i4 (1 : BitVec 32)
      pure .br3) : Zig.CM Tgt sbLocals sbExit) with
    | .br3 => (do
      let i7 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
      let i8 ← Zig.load (Zig.Ptr) 8 i7
      let i9 ← Zig.callMC (Zig.ptrProject p0 (·.add 8))
      let i10 ← Zig.load (Zig.Ptr) 8 i9
      let i11 ← pure (i10)
      match ← ((do
        let i13 ← pure i11
        let i14 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.relaxed 4 i13
        pure (.br12 i14)) : Zig.CM Tgt sbLocals sbExit) with
      | .br12 v12 => (do
        Zig.store (α := BitVec 32) 4 i8 v12
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt sbLocals sbExit).run' (default : sbLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure sbRelaxedLocals where
  x : Zig.Ptr
  y : Zig.Ptr
  r1 : Zig.Ptr
  r2 : Zig.Ptr
  c1 : Zig.Ptr
  c2 : Zig.Ptr
  deriving Inhabited

inductive sbRelaxedExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def sbRelaxed  : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s0 ← Zig.allocStack 4 4
  let s3 ← Zig.allocStack 4 4
  let s6 ← Zig.allocStack 4 4
  let s8 ← Zig.allocStack 4 4
  let s10 ← Zig.allocStack 24 8
  let s17 ← Zig.allocStack 24 8
  let e ← ((do
    let i0 ← pure (← get).x
    let i1 ← Zig.callRC (atomic_Value_u32_init (0 : BitVec 32))
    Zig.store (α := atomic_Value_u32) 4 i0 i1
    let i3 ← pure (← get).y
    let i4 ← Zig.callRC (atomic_Value_u32_init (0 : BitVec 32))
    Zig.store (α := atomic_Value_u32) 4 i3 i4
    let i6 ← pure (← get).r1
    Zig.store (α := BitVec 32) 4 i6 (0 : BitVec 32)
    let i8 ← pure (← get).r2
    Zig.store (α := BitVec 32) 4 i8 (0 : BitVec 32)
    let i10 ← pure (← get).c1
    let i11 ← pure i10
    Zig.store (α := Zig.Ptr) 8 i11 i0
    let i13 ← Zig.callMC (Zig.ptrProject i10 (·.add 8))
    Zig.store (α := Zig.Ptr) 8 i13 i3
    let i15 ← Zig.callMC (Zig.ptrProject i10 (·.add 16))
    Zig.store (α := Zig.Ptr) 8 i15 i6
    let i17 ← pure (← get).c2
    let i18 ← pure i17
    Zig.store (α := Zig.Ptr) 8 i18 i3
    let i20 ← Zig.callMC (Zig.ptrProject i17 (·.add 8))
    Zig.store (α := Zig.Ptr) 8 i20 i0
    let i22 ← Zig.callMC (Zig.ptrProject i17 (·.add 16))
    Zig.store (α := Zig.Ptr) 8 i22 i8
    let i24 ← pure (i10)
    let i25 ← Zig.spawnC (Tgt.sb i24)
    match i25 with
    | .error _ => (do
      let i27 ← Zig.callRC (Zig.unwrapErr i25)
      let i28 ← pure (i27)
      let i29 ← pure ((.error i28) : Except Zig.ErrName (BitVec 32))
      pure (.ret i29))
    | .ok v26 => (do
      let i31 ← pure (i17)
      let i32 ← Zig.spawnC (Tgt.sb i31)
      match i32 with
      | .error _ => (do
        let i34 ← Zig.callRC (Zig.unwrapErr i32)
        let _i35 ← Zig.joinC v26
        let i36 ← pure (i34)
        let i37 ← pure ((.error i36) : Except Zig.ErrName (BitVec 32))
        pure (.ret i37))
      | .ok v33 => (do
        let _i39 ← Zig.joinC v26
        let _i40 ← Zig.joinC v33
        let i41 ← Zig.load (BitVec 32) 4 i6
        let i42 ← Zig.load (BitVec 32) 4 i8
        let i43 ← pure (Zig.shl i42 (1 : BitVec 5))
        let i44 ← pure (i41 ||| i43)
        let i45 ← pure ((.ok i44) : Except Zig.ErrName (BitVec 32))
        pure (.ret i45)))) : Zig.CM Tgt sbRelaxedLocals sbRelaxedExit).run' { (default : sbRelaxedLocals) with x := s0, y := s3, r1 := s6, r2 := s8, c1 := s10, c2 := s17 }
  Zig.free s0
  Zig.free s3
  Zig.free s6
  Zig.free s8
  Zig.free s10
  Zig.free s17
  match e with
  | .ret v => pure v

structure stackPushLocals where
  s : Zig.Ptr
  c1 : Zig.Ptr
  c2 : Zig.Ptr
  deriving Inhabited

inductive stackPushExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br40 (v : BitVec 32)
  | br48
  | br60
  | br68

def stackPush  : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s0 ← Zig.allocStack 16 4
  let s11 ← Zig.allocStack 16 8
  let s16 ← Zig.allocStack 16 8
  let e ← ((do
    let i0 ← pure (← get).s
    let i1 ← pure i0
    let i2 ← Zig.callRC (atomic_Value_u32_init (0 : BitVec 32))
    Zig.store (α := atomic_Value_u32) 4 i1 i2
    let i4 ← Zig.callMC (Zig.ptrProject i0 (·.add 4))
    let i5 ← pure i4
    Zig.store (α := BitVec 32) 4 i5 (0 : BitVec 32)
    let i7 ← Zig.callMC (Zig.ptrProject i4 (·.elem 4 (1 : BitVec 64)))
    Zig.store (α := BitVec 32) 4 i7 (0 : BitVec 32)
    let i9 ← Zig.callMC (Zig.ptrProject i4 (·.elem 4 (2 : BitVec 64)))
    Zig.store (α := BitVec 32) 4 i9 (0 : BitVec 32)
    let i11 ← pure (← get).c1
    let i12 ← pure i11
    Zig.store (α := Zig.Ptr) 8 i12 i0
    let i14 ← Zig.callMC (Zig.ptrProject i11 (·.add 8))
    Zig.store (α := BitVec 32) 4 i14 (1 : BitVec 32)
    let i16 ← pure (← get).c2
    let i17 ← pure i16
    Zig.store (α := Zig.Ptr) 8 i17 i0
    let i19 ← Zig.callMC (Zig.ptrProject i16 (·.add 8))
    Zig.store (α := BitVec 32) 4 i19 (2 : BitVec 32)
    let i21 ← pure (i11)
    let i22 ← Zig.spawnC (Tgt.push i21)
    match i22 with
    | .error _ => (do
      let i24 ← Zig.callRC (Zig.unwrapErr i22)
      let i25 ← pure (i24)
      let i26 ← pure ((.error i25) : Except Zig.ErrName (BitVec 32))
      pure (.ret i26))
    | .ok v23 => (do
      let i28 ← pure (i16)
      let i29 ← Zig.spawnC (Tgt.push i28)
      match i29 with
      | .error _ => (do
        let i31 ← Zig.callRC (Zig.unwrapErr i29)
        let _i32 ← Zig.joinC v23
        let i33 ← pure (i31)
        let i34 ← pure ((.error i33) : Except Zig.ErrName (BitVec 32))
        pure (.ret i34))
      | .ok v30 => (do
        let _i36 ← Zig.joinC v23
        let _i37 ← Zig.joinC v30
        let i38 ← pure i0
        let i39 ← pure (i38)
        match ← ((do
          let i41 ← pure i39
          let i42 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.acquire 4 i41
          pure (.br40 i42)) : Zig.CM Tgt stackPushLocals stackPushExit) with
        | .br40 v40 => (do
          let i44 ← Zig.mul false (100 : BitVec 32) v40
          let i45 ← Zig.callMC (Zig.ptrProject i0 (·.add 4))
          let i46 ← Zig.intCast false false 64 v40
          let i47 ← pure (Zig.lt false i46 (3 : BitVec 64))
          match ← ((do
            if i47 then (do
              pure .br48)
            else (do
              throw .outOfBounds)) : Zig.CM Tgt stackPushLocals stackPushExit) with
          | .br48 => (do
            let i53 ← Zig.callMC (Zig.load (BitVec 32) 4 (i45.elem 4 i46))
            let i54 ← Zig.mul false (10 : BitVec 32) i53
            let i55 ← Zig.add false i44 i54
            let i56 ← Zig.callMC (Zig.ptrProject i0 (·.add 4))
            let i57 ← Zig.callMC (Zig.ptrProject i0 (·.add 4))
            let i58 ← Zig.intCast false false 64 v40
            let i59 ← pure (Zig.lt false i58 (3 : BitVec 64))
            match ← ((do
              if i59 then (do
                pure .br60)
              else (do
                throw .outOfBounds)) : Zig.CM Tgt stackPushLocals stackPushExit) with
            | .br60 => (do
              let i65 ← Zig.callMC (Zig.load (BitVec 32) 4 (i57.elem 4 i58))
              let i66 ← Zig.intCast false false 64 i65
              let i67 ← pure (Zig.lt false i66 (3 : BitVec 64))
              match ← ((do
                if i67 then (do
                  pure .br68)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt stackPushLocals stackPushExit) with
              | .br68 => (do
                let i73 ← Zig.callMC (Zig.load (BitVec 32) 4 (i56.elem 4 i66))
                let i74 ← Zig.add false i55 i73
                let i75 ← pure ((.ok i74) : Except Zig.ErrName (BitVec 32))
                pure (.ret i75))
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e))) : Zig.CM Tgt stackPushLocals stackPushExit).run' { (default : stackPushLocals) with s := s0, c1 := s11, c2 := s16 }
  Zig.free s0
  Zig.free s11
  Zig.free s16
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure wwLocals where
  deriving Inhabited

inductive wwExit where
  | ret
  | br3
  | br9

def ww (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let i2 ← Zig.load (Zig.Ptr) 8 i1
    match ← ((do
      let i4 ← pure i2
      Zig.atomicStoreC Zig.AtomicOrder.relaxed 4 i4 (1 : BitVec 32)
      pure .br3) : Zig.CM Tgt wwLocals wwExit) with
    | .br3 => (do
      let i7 ← Zig.callMC (Zig.ptrProject p0 (·.add 8))
      let i8 ← Zig.load (Zig.Ptr) 8 i7
      match ← ((do
        let i10 ← pure i8
        Zig.atomicStoreC Zig.AtomicOrder.relaxed 4 i10 (2 : BitVec 32)
        pure .br9) : Zig.CM Tgt wwLocals wwExit) with
      | .br9 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt wwLocals wwExit).run' (default : wwLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure twoPlusTwoWLocals where
  x : Zig.Ptr
  y : Zig.Ptr
  c1 : Zig.Ptr
  c2 : Zig.Ptr
  deriving Inhabited

inductive twoPlusTwoWExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br34 (v : BitVec 32)
  | br40 (v : BitVec 32)

def twoPlusTwoW  : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s0 ← Zig.allocStack 4 4
  let s3 ← Zig.allocStack 4 4
  let s6 ← Zig.allocStack 16 8
  let s11 ← Zig.allocStack 16 8
  let e ← ((do
    let i0 ← pure (← get).x
    let i1 ← Zig.callRC (atomic_Value_u32_init (0 : BitVec 32))
    Zig.store (α := atomic_Value_u32) 4 i0 i1
    let i3 ← pure (← get).y
    let i4 ← Zig.callRC (atomic_Value_u32_init (0 : BitVec 32))
    Zig.store (α := atomic_Value_u32) 4 i3 i4
    let i6 ← pure (← get).c1
    let i7 ← pure i6
    Zig.store (α := Zig.Ptr) 8 i7 i0
    let i9 ← Zig.callMC (Zig.ptrProject i6 (·.add 8))
    Zig.store (α := Zig.Ptr) 8 i9 i3
    let i11 ← pure (← get).c2
    let i12 ← pure i11
    Zig.store (α := Zig.Ptr) 8 i12 i3
    let i14 ← Zig.callMC (Zig.ptrProject i11 (·.add 8))
    Zig.store (α := Zig.Ptr) 8 i14 i0
    let i16 ← pure (i6)
    let i17 ← Zig.spawnC (Tgt.ww i16)
    match i17 with
    | .error _ => (do
      let i19 ← Zig.callRC (Zig.unwrapErr i17)
      let i20 ← pure (i19)
      let i21 ← pure ((.error i20) : Except Zig.ErrName (BitVec 32))
      pure (.ret i21))
    | .ok v18 => (do
      let i23 ← pure (i11)
      let i24 ← Zig.spawnC (Tgt.ww i23)
      match i24 with
      | .error _ => (do
        let i26 ← Zig.callRC (Zig.unwrapErr i24)
        let _i27 ← Zig.joinC v18
        let i28 ← pure (i26)
        let i29 ← pure ((.error i28) : Except Zig.ErrName (BitVec 32))
        pure (.ret i29))
      | .ok v25 => (do
        let _i31 ← Zig.joinC v18
        let _i32 ← Zig.joinC v25
        let i33 ← pure (i0)
        match ← ((do
          let i35 ← pure i33
          let i36 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.seqCst 4 i35
          pure (.br34 i36)) : Zig.CM Tgt twoPlusTwoWLocals twoPlusTwoWExit) with
        | .br34 v34 => (do
          let i38 ← Zig.mul false (10 : BitVec 32) v34
          let i39 ← pure (i3)
          match ← ((do
            let i41 ← pure i39
            let i42 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.seqCst 4 i41
            pure (.br40 i42)) : Zig.CM Tgt twoPlusTwoWLocals twoPlusTwoWExit) with
          | .br40 v40 => (do
            let i44 ← Zig.add false i38 v40
            let i45 ← pure ((.ok i44) : Except Zig.ErrName (BitVec 32))
            pure (.ret i45))
          | e => pure e)
        | e => pure e))) : Zig.CM Tgt twoPlusTwoWLocals twoPlusTwoWExit).run' { (default : twoPlusTwoWLocals) with x := s0, y := s3, c1 := s6, c2 := s11 }
  Zig.free s0
  Zig.free s3
  Zig.free s6
  Zig.free s11
  match e with
  | .ret v => pure v
  | _ => throw .panic

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .mpWriter a => discard (mpWriter a)
  | .mpWriterRelaxed a => discard (mpWriterRelaxed a)
  | .sb a => discard (sb a)
  | .push a => discard (push a)
  | .ww a => discard (ww a)

end Atomics