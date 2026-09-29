import ZigLean


namespace Sync

inductive Io_Mutex_State where
  | unlocked
  | locked_once
  | contended
  deriving Repr, Inhabited, DecidableEq

def Io_Mutex_State.toBits : Io_Mutex_State → BitVec 32
  | .unlocked => (0 : BitVec 32)
  | .locked_once => (1 : BitVec 32)
  | .contended => (2 : BitVec 32)

def Io_Mutex_State.ofInt? (v : Int) : Option Io_Mutex_State :=
  if v = 0 then Option.some .unlocked else if v = 1 then Option.some .locked_once else if v = 2 then Option.some .contended else Option.none

def Io_Mutex_State.isNamed (_ : Io_Mutex_State) : Bool := true

instance : Zig.Packed Io_Mutex_State 32 where
  toBits := Io_Mutex_State.toBits
  ofBits b := (Io_Mutex_State.ofInt? (Zig.val false b)).getD default
  valid b := (Io_Mutex_State.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc Io_Mutex_State where
  size := 4
  align := 4
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 32 ← Zig.Enc.decode bs
    match Io_Mutex_State.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

structure atomic_Value_Io_Mutex_State where
  raw : Io_Mutex_State
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc atomic_Value_Io_Mutex_State where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.raw)]
  decode bs := do pure { raw := ← Zig.Enc.decodeAt bs 0 }

structure Io_Mutex where
  state : atomic_Value_Io_Mutex_State
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Io_Mutex where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.state)]
  decode bs := do pure { state := ← Zig.Enc.decodeAt bs 0 }

structure Counter where
  io : Zig.Io
  m : Io_Mutex
  n : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Counter where
  size := 24
  align := 8
  encode v := Zig.Enc.fields 24 [(0, Zig.Enc.encode v.io), (16, Zig.Enc.encode v.m), (20, Zig.Enc.encode v.n)]
  decode bs := do pure { io := ← Zig.Enc.decodeAt bs 0, m := ← Zig.Enc.decodeAt bs 16, n := ← Zig.Enc.decodeAt bs 20 }

structure Thread_SpawnConfig where
  stack_size : BitVec 64
  allocator : Option (Zig.Allocator)
  deriving Repr, Inhabited, DecidableEq

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

/-- The spawn targets of the program. -/
inductive Tgt where
  | work (a : Zig.Ptr)

structure Io_Mutex_lockLocals where
  deriving Inhabited

inductive Io_Mutex_lockExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br4 (v : Option (Io_Mutex_State))
  | br2 (v : Io_Mutex_State)
  | br13
  | br30 (v : Io_Mutex_State)
  | br28
  | br26
  | rep27

def Io_Mutex_lock.again27 : Io_Mutex_lockExit → Bool
  | .rep27 => true
  | _ => false

def Io_Mutex_lock.loop27 (p0 : Zig.Ptr) (p1 : Zig.Io) : Zig.CM Tgt Io_Mutex_lockLocals Io_Mutex_lockExit := do
  match ← ((do
    let i29 ← pure (p0.add 0)
    match ← ((do
      let i31 ← pure (i29.add 0)
      let i32 ← Zig.atomicRmwAsC Zig.RmwOp.xchg Zig.AtomicOrder.acquire 4 i31 Io_Mutex_State.contended
      pure (.br30 i32)) : Zig.CM Tgt Io_Mutex_lockLocals Io_Mutex_lockExit) with
    | .br30 v30 => (do
      let i34 ← pure (v30 != Io_Mutex_State.unlocked)
      if i34 then (do
        let i36 ← pure (p0.add 0)
        let i37 ← pure (i36.add 0)
        let i38 ← pure (i37)
        let i39 ← Zig.futexWaitCancelableC p1 i38 Io_Mutex_State.contended
        match i39 with
        | .error _ => (do
          let i41 ← Zig.callRC (Zig.unwrapErr i39)
          let i42 ← pure ((.error i41) : Except Zig.ErrName (Unit))
          pure (.ret i42))
        | .ok _v40 => (do
          pure .br28))
      else (do
        pure .br26))
    | e => pure e) : Zig.CM Tgt Io_Mutex_lockLocals Io_Mutex_lockExit) with
  | .br28 => (do
    pure .rep27)
  | e => pure e

def Io_Mutex_lock (p0 : Zig.Ptr) (p1 : Zig.Io) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (p0.add 0)
      match ← ((do
        let i5 ← pure (i3.add 0)
        let i6 ← Zig.cmpxchgAsC Zig.AtomicOrder.acquire Zig.AtomicOrder.relaxed 4 i5 Io_Mutex_State.unlocked Io_Mutex_State.locked_once
        pure (.br4 i6)) : Zig.CM Tgt Io_Mutex_lockLocals Io_Mutex_lockExit) with
      | .br4 v4 => (do
        let i8 ← pure ((v4).isSome)
        if i8 then (do
          let i10 ← Zig.optPayload v4
          pure (.br2 i10))
        else (do
          pure (.ret (.ok () : Except Zig.ErrName (Unit)))))
      | e => pure e) : Zig.CM Tgt Io_Mutex_lockLocals Io_Mutex_lockExit) with
    | .br2 v2 => (do
      match ← ((do
        let i14 ← pure (v2 == Io_Mutex_State.contended)
        if i14 then (do
          let i16 ← pure (p0.add 0)
          let i17 ← pure (i16.add 0)
          let i18 ← pure (i17)
          let i19 ← Zig.futexWaitCancelableC p1 i18 Io_Mutex_State.contended
          match i19 with
          | .error _ => (do
            let i21 ← Zig.callRC (Zig.unwrapErr i19)
            let i22 ← pure ((.error i21) : Except Zig.ErrName (Unit))
            pure (.ret i22))
          | .ok _v20 => (do
            pure .br13))
        else (do
          pure .br13)) : Zig.CM Tgt Io_Mutex_lockLocals Io_Mutex_lockExit) with
      | .br13 => (do
        match ← ((do
          Zig.loop (Io_Mutex_lock.loop27 p0 p1) Io_Mutex_lock.again27) : Zig.CM Tgt Io_Mutex_lockLocals Io_Mutex_lockExit) with
        | .br26 => (do
          pure (.ret (.ok () : Except Zig.ErrName (Unit))))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Io_Mutex_lockLocals Io_Mutex_lockExit).run' (default : Io_Mutex_lockLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Io_Mutex_lockUncancelableLocals where
  deriving Inhabited

inductive Io_Mutex_lockUncancelableExit where
  | ret
  | br4 (v : Option (Io_Mutex_State))
  | br2 (v : Io_Mutex_State)
  | br13
  | br26 (v : Io_Mutex_State)
  | br24
  | br22
  | rep23

def Io_Mutex_lockUncancelable.again23 : Io_Mutex_lockUncancelableExit → Bool
  | .rep23 => true
  | _ => false

def Io_Mutex_lockUncancelable.loop23 (p0 : Zig.Ptr) (p1 : Zig.Io) : Zig.CM Tgt Io_Mutex_lockUncancelableLocals Io_Mutex_lockUncancelableExit := do
  match ← ((do
    let i25 ← pure (p0.add 0)
    match ← ((do
      let i27 ← pure (i25.add 0)
      let i28 ← Zig.atomicRmwAsC Zig.RmwOp.xchg Zig.AtomicOrder.acquire 4 i27 Io_Mutex_State.contended
      pure (.br26 i28)) : Zig.CM Tgt Io_Mutex_lockUncancelableLocals Io_Mutex_lockUncancelableExit) with
    | .br26 v26 => (do
      let i30 ← pure (v26 != Io_Mutex_State.unlocked)
      if i30 then (do
        let i32 ← pure (p0.add 0)
        let i33 ← pure (i32.add 0)
        let i34 ← pure (i33)
        let _i35 ← Zig.futexWaitC p1 i34 Io_Mutex_State.contended
        pure .br24)
      else (do
        pure .br22))
    | e => pure e) : Zig.CM Tgt Io_Mutex_lockUncancelableLocals Io_Mutex_lockUncancelableExit) with
  | .br24 => (do
    pure .rep23)
  | e => pure e

def Io_Mutex_lockUncancelable (p0 : Zig.Ptr) (p1 : Zig.Io) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (p0.add 0)
      match ← ((do
        let i5 ← pure (i3.add 0)
        let i6 ← Zig.cmpxchgAsC Zig.AtomicOrder.acquire Zig.AtomicOrder.relaxed 4 i5 Io_Mutex_State.unlocked Io_Mutex_State.locked_once
        pure (.br4 i6)) : Zig.CM Tgt Io_Mutex_lockUncancelableLocals Io_Mutex_lockUncancelableExit) with
      | .br4 v4 => (do
        let i8 ← pure ((v4).isSome)
        if i8 then (do
          let i10 ← Zig.optPayload v4
          pure (.br2 i10))
        else (do
          pure .ret))
      | e => pure e) : Zig.CM Tgt Io_Mutex_lockUncancelableLocals Io_Mutex_lockUncancelableExit) with
    | .br2 v2 => (do
      match ← ((do
        let i14 ← pure (v2 == Io_Mutex_State.contended)
        if i14 then (do
          let i16 ← pure (p0.add 0)
          let i17 ← pure (i16.add 0)
          let i18 ← pure (i17)
          let _i19 ← Zig.futexWaitC p1 i18 Io_Mutex_State.contended
          pure .br13)
        else (do
          pure .br13)) : Zig.CM Tgt Io_Mutex_lockUncancelableLocals Io_Mutex_lockUncancelableExit) with
      | .br13 => (do
        match ← ((do
          Zig.loop (Io_Mutex_lockUncancelable.loop23 p0 p1) Io_Mutex_lockUncancelable.again23) : Zig.CM Tgt Io_Mutex_lockUncancelableLocals Io_Mutex_lockUncancelableExit) with
        | .br22 => (do
          pure .ret)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Io_Mutex_lockUncancelableLocals Io_Mutex_lockUncancelableExit).run' (default : Io_Mutex_lockUncancelableLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Io_Mutex_tryLockLocals where
  deriving Inhabited

inductive Io_Mutex_tryLockExit where
  | ret (v : Bool)
  | br2 (v : Option (Io_Mutex_State))

def Io_Mutex_tryLock (p0 : Zig.Ptr) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    let i1 ← pure (p0.add 0)
    match ← ((do
      let i3 ← pure (i1.add 0)
      let i4 ← Zig.cmpxchgAsC Zig.AtomicOrder.acquire Zig.AtomicOrder.relaxed 4 i3 Io_Mutex_State.unlocked Io_Mutex_State.locked_once
      pure (.br2 i4)) : Zig.CM Tgt Io_Mutex_tryLockLocals Io_Mutex_tryLockExit) with
    | .br2 v2 => (do
      let i6 ← pure ((v2).isNone)
      pure (.ret i6))
    | e => pure e) : Zig.CM Tgt Io_Mutex_tryLockLocals Io_Mutex_tryLockExit).run' (default : Io_Mutex_tryLockLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Io_Mutex_unlockLocals where
  deriving Inhabited

inductive Io_Mutex_unlockExit where
  | ret
  | br3 (v : Io_Mutex_State)
  | br7

def Io_Mutex_unlock (p0 : Zig.Ptr) (p1 : Zig.Io) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← pure (p0.add 0)
    match ← ((do
      let i4 ← pure (i2.add 0)
      let i5 ← Zig.atomicRmwAsC Zig.RmwOp.xchg Zig.AtomicOrder.release 4 i4 Io_Mutex_State.unlocked
      pure (.br3 i5)) : Zig.CM Tgt Io_Mutex_unlockLocals Io_Mutex_unlockExit) with
    | .br3 v3 => (do
      match ← ((do
        match v3 with
        | .unlocked => (do
          throw .unreachable)
        | .locked_once => (do
          pure .br7)
        | .contended => (do
          let i14 ← pure (p0.add 0)
          let i15 ← pure (i14.add 0)
          let i16 ← pure (i15)
          let _i17 ← Zig.futexWakeC p1 i16 (1 : BitVec 32)
          pure .br7)) : Zig.CM Tgt Io_Mutex_unlockLocals Io_Mutex_unlockExit) with
      | .br7 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Io_Mutex_unlockLocals Io_Mutex_unlockExit).run' (default : Io_Mutex_unlockLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure workLocals where
  local1 : BitVec 64
  deriving Inhabited

inductive workExit where
  | ret
  | br6
  | br3
  | rep4

def work.again4 : workExit → Bool
  | .rep4 => true
  | _ => false

def work.loop4 (p0 : Zig.Ptr) : Zig.CM Tgt workLocals workExit := do
  let i5 ← pure ((← get).local1)
  match ← ((do
    let i7 ← pure (i5)
    let i8 ← pure (Zig.lt false i7 (2 : BitVec 64))
    if i8 then (do
      let i10 ← pure (p0.add 16)
      let i11 ← pure (p0.add 0)
      let i12 ← Zig.load (Zig.Io) 8 i11
      let _i13 ← Zig.callC (Io_Mutex_lockUncancelable i10 i12)
      let i14 ← pure (p0.add 20)
      let i15 ← Zig.load (BitVec 32) 4 i14
      let i16 ← Zig.add false i15 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 i14 i16
      let i18 ← pure (p0.add 16)
      let i19 ← pure (p0.add 0)
      let i20 ← Zig.load (Zig.Io) 8 i19
      let _i21 ← Zig.callC (Io_Mutex_unlock i18 i20)
      pure .br6)
    else (do
      pure .br3)) : Zig.CM Tgt workLocals workExit) with
  | .br6 => (do
    let i24 ← Zig.add false i5 (1 : BitVec 64)
    modify (fun s => { s with local1 := i24 })
    pure .rep4)
  | e => pure e

def work (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    modify (fun s => { s with local1 := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (work.loop4 p0) work.again4) : Zig.CM Tgt workLocals workExit) with
    | .br3 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt workLocals workExit).run' (default : workLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure mutexCounterLocals where
  c : Zig.Ptr
  deriving Inhabited

inductive mutexCounterExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def mutexCounter (p0 : Zig.Io) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s1 ← Zig.allocStack 24 8
  let e ← ((do
    let i1 ← pure (← get).c
    let i2 ← pure (i1.add 0)
    Zig.store (α := Zig.Io) 8 i2 p0
    let i4 ← pure (i1.add 16)
    Zig.store (α := Io_Mutex) 4 i4 ({ state := ({ raw := Io_Mutex_State.unlocked } : atomic_Value_Io_Mutex_State) } : Io_Mutex)
    let i6 ← pure (i1.add 20)
    Zig.store (α := BitVec 32) 4 i6 (0 : BitVec 32)
    let i8 ← pure (i1)
    let i9 ← Zig.spawnC (Tgt.work i8)
    match i9 with
    | .error _ => (do
      let i11 ← Zig.callRC (Zig.unwrapErr i9)
      let i12 ← pure (i11)
      let i13 ← pure ((.error i12) : Except Zig.ErrName (BitVec 32))
      pure (.ret i13))
    | .ok v10 => (do
      let _i15 ← Zig.callC (work i1)
      let _i16 ← Zig.joinC v10
      let i17 ← pure (i1.add 20)
      let i18 ← Zig.load (BitVec 32) 4 i17
      let i19 ← pure ((.ok i18) : Except Zig.ErrName (BitVec 32))
      pure (.ret i19))) : Zig.CM Tgt mutexCounterLocals mutexCounterExit).run' { (default : mutexCounterLocals) with c := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .work a => discard (work a)

end Sync