import ZigLean


namespace Iogroup

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

structure atomic_Value___anyopaque where
  raw : Option (Zig.Ptr)
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc atomic_Value___anyopaque where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.raw)]
  decode bs := do pure { raw := ← Zig.Enc.decodeAt bs 0 }

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

/-- The spawn targets of the program. -/
inductive Tgt where
  | add (a : Zig.Ptr)

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

structure debug_assertLocals where
  deriving Inhabited

inductive debug_assertExit where
  | ret
  | br1

def debug_assert (p0 : Bool) : Zig.Result (Unit) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure (!p0)
      if i2 then (do
        throw .unreachable)
      else (do
        pure .br1)) : Zig.M debug_assertLocals debug_assertExit) with
    | .br1 => (do
      pure .ret)
    | e => pure e) : Zig.M debug_assertLocals debug_assertExit).run' (default : debug_assertLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure addLocals where
  deriving Inhabited

inductive addExit where
  | ret

def add (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure (p0.add 16)
    let i2 ← pure (p0.add 0)
    let i3 ← Zig.load (Zig.Io) 8 i2
    let _i4 ← Zig.callC (Io_Mutex_lockUncancelable i1 i3)
    let i5 ← pure (p0.add 20)
    let i6 ← Zig.load (BitVec 32) 4 i5
    let i7 ← Zig.add false i6 (1 : BitVec 32)
    Zig.store (α := BitVec 32) 4 i5 i7
    let i9 ← pure (p0.add 16)
    let i10 ← pure (p0.add 0)
    let i11 ← Zig.load (Zig.Io) 8 i10
    let _i12 ← Zig.callC (Io_Mutex_unlock i9 i11)
    pure .ret) : Zig.CM Tgt addLocals addExit).run' (default : addLocals)
  match e with
  | .ret => pure ()

structure groupConcurrentLocals where
  c : Zig.Ptr
  g : Zig.Ptr
  local10 : BitVec 64
  deriving Inhabited

inductive groupConcurrentExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br15
  | br12
  | rep13

def groupConcurrent.again13 : groupConcurrentExit → Bool
  | .rep13 => true
  | _ => false

def groupConcurrent.loop13 (p0 : Zig.Io) (i1 : Zig.Ptr) (i8 : Zig.Ptr) : Zig.CM Tgt groupConcurrentLocals groupConcurrentExit := do
  let i14 ← pure ((← get).local10)
  match ← ((do
    let i16 ← pure (i14)
    let i17 ← pure (Zig.lt false i16 (2 : BitVec 64))
    if i17 then (do
      let i19 ← pure (i1)
      let i20 ← Zig.groupConcurrentC i8 p0 (Tgt.add i19)
      match i20 with
      | .error _ => (do
        let i22 ← Zig.callRC (Zig.unwrapErr i20)
        let i23 ← pure (i22)
        let i24 ← pure ((.error i23) : Except Zig.ErrName (BitVec 32))
        pure (.ret i24))
      | .ok _v21 => (do
        pure .br15))
    else (do
      pure .br12)) : Zig.CM Tgt groupConcurrentLocals groupConcurrentExit) with
  | .br15 => (do
    let i28 ← Zig.add false i14 (1 : BitVec 64)
    modify (fun s => { s with local10 := i28 })
    pure .rep13)
  | e => pure e

def groupConcurrent (p0 : Zig.Io) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s1 ← Zig.allocStack 24 8
  let s8 ← Zig.allocStack 16 8
  let e ← ((do
    let i1 ← pure (← get).c
    let i2 ← pure (i1.add 0)
    Zig.store (α := Zig.Io) 8 i2 p0
    let i4 ← pure (i1.add 16)
    Zig.store (α := Io_Mutex) 4 i4 ({ state := ({ raw := Io_Mutex_State.unlocked } : atomic_Value_Io_Mutex_State) } : Io_Mutex)
    let i6 ← pure (i1.add 20)
    Zig.store (α := BitVec 32) 4 i6 (0 : BitVec 32)
    let i8 ← pure (← get).g
    Zig.store (α := Io_Group) 8 i8 ({ token := ({ raw := none } : atomic_Value___anyopaque), state := (0 : BitVec 64) } : Io_Group)
    modify (fun s => { s with local10 := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (groupConcurrent.loop13 p0 i1 i8) groupConcurrent.again13) : Zig.CM Tgt groupConcurrentLocals groupConcurrentExit) with
    | .br12 => (do
      let _i31 ← Zig.groupCancelC i8 p0
      let i32 ← pure (i1.add 20)
      let i33 ← Zig.load (BitVec 32) 4 i32
      let i34 ← pure ((.ok i33) : Except Zig.ErrName (BitVec 32))
      pure (.ret i34))
    | e => pure e) : Zig.CM Tgt groupConcurrentLocals groupConcurrentExit).run' { (default : groupConcurrentLocals) with c := s1, g := s8 }
  Zig.free s1
  Zig.free s8
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure groupCounterLocals where
  c : Zig.Ptr
  g : Zig.Ptr
  local10 : BitVec 64
  deriving Inhabited

inductive groupCounterExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br15
  | br12
  | rep13

def groupCounter.again13 : groupCounterExit → Bool
  | .rep13 => true
  | _ => false

def groupCounter.loop13 (p0 : Zig.Io) (i1 : Zig.Ptr) (i8 : Zig.Ptr) : Zig.CM Tgt groupCounterLocals groupCounterExit := do
  let i14 ← pure ((← get).local10)
  match ← ((do
    let i16 ← pure (i14)
    let i17 ← pure (Zig.lt false i16 (3 : BitVec 64))
    if i17 then (do
      let i19 ← pure (i1)
      let _i20 ← Zig.groupAsyncC i8 p0 (Tgt.add i19)
      pure .br15)
    else (do
      pure .br12)) : Zig.CM Tgt groupCounterLocals groupCounterExit) with
  | .br15 => (do
    let i23 ← Zig.add false i14 (1 : BitVec 64)
    modify (fun s => { s with local10 := i23 })
    pure .rep13)
  | e => pure e

def groupCounter (p0 : Zig.Io) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s1 ← Zig.allocStack 24 8
  let s8 ← Zig.allocStack 16 8
  let e ← ((do
    let i1 ← pure (← get).c
    let i2 ← pure (i1.add 0)
    Zig.store (α := Zig.Io) 8 i2 p0
    let i4 ← pure (i1.add 16)
    Zig.store (α := Io_Mutex) 4 i4 ({ state := ({ raw := Io_Mutex_State.unlocked } : atomic_Value_Io_Mutex_State) } : Io_Mutex)
    let i6 ← pure (i1.add 20)
    Zig.store (α := BitVec 32) 4 i6 (0 : BitVec 32)
    let i8 ← pure (← get).g
    Zig.store (α := Io_Group) 8 i8 ({ token := ({ raw := none } : atomic_Value___anyopaque), state := (0 : BitVec 64) } : Io_Group)
    modify (fun s => { s with local10 := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (groupCounter.loop13 p0 i1 i8) groupCounter.again13) : Zig.CM Tgt groupCounterLocals groupCounterExit) with
    | .br12 => (do
      let i26 ← Zig.groupAwaitC i8 p0
      match i26 with
      | .error _ => (do
        let i28 ← Zig.callRC (Zig.unwrapErr i26)
        let i29 ← pure (i28)
        let i30 ← pure ((.error i29) : Except Zig.ErrName (BitVec 32))
        pure (.ret i30))
      | .ok _v27 => (do
        let i32 ← pure (i1.add 20)
        let i33 ← Zig.load (BitVec 32) 4 i32
        let i34 ← pure ((.ok i33) : Except Zig.ErrName (BitVec 32))
        pure (.ret i34)))
    | e => pure e) : Zig.CM Tgt groupCounterLocals groupCounterExit).run' { (default : groupCounterLocals) with c := s1, g := s8 }
  Zig.free s1
  Zig.free s8
  match e with
  | .ret v => pure v
  | _ => throw .panic

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .add a => discard (add a)

end Iogroup