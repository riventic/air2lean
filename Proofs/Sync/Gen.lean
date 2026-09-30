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

structure Io_Condition_State where
  waiters : BitVec 16
  signals : BitVec 16
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Io_Condition_State 32 where
  toBits v := ((Zig.Packed.toBits v.waiters).setWidth 32 <<< 0) ||| ((Zig.Packed.toBits v.signals).setWidth 32 <<< 16)
  ofBits b := { waiters := Zig.Packed.get b 0, signals := Zig.Packed.get b 16 }

instance : Zig.Enc Io_Condition_State where
  size := 4
  align := 4
  encode v := Zig.Enc.encode (Zig.Packed.toBits v)
  decode bs := do
    let b : BitVec 32 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

structure atomic_Value_Io_Condition_State where
  raw : Io_Condition_State
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc atomic_Value_Io_Condition_State where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.raw)]
  decode bs := do pure { raw := ← Zig.Enc.decodeAt bs 0 }

structure atomic_Value_u32 where
  raw : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc atomic_Value_u32 where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.raw)]
  decode bs := do pure { raw := ← Zig.Enc.decodeAt bs 0 }

structure Io_Condition where
  state : atomic_Value_Io_Condition_State
  epoch : atomic_Value_u32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Io_Condition where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.state), (4, Zig.Enc.encode v.epoch)]
  decode bs := do pure { state := ← Zig.Enc.decodeAt bs 0, epoch := ← Zig.Enc.decodeAt bs 4 }

structure Io_Semaphore where
  mutex : Io_Mutex
  cond : Io_Condition
  permits : BitVec 64
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Io_Semaphore where
  size := 24
  align := 8
  encode v := Zig.Enc.fields 24 [(8, Zig.Enc.encode v.mutex), (12, Zig.Enc.encode v.cond), (0, Zig.Enc.encode v.permits)]
  decode bs := do pure { mutex := ← Zig.Enc.decodeAt bs 8, cond := ← Zig.Enc.decodeAt bs 12, permits := ← Zig.Enc.decodeAt bs 0 }

structure Io_RwLock where
  state : BitVec 64
  mutex : Io_Mutex
  semaphore : Io_Semaphore
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Io_RwLock where
  size := 40
  align := 8
  encode v := Zig.Enc.fields 40 [(0, Zig.Enc.encode v.state), (32, Zig.Enc.encode v.mutex), (8, Zig.Enc.encode v.semaphore)]
  decode bs := do pure { state := ← Zig.Enc.decodeAt bs 0, mutex := ← Zig.Enc.decodeAt bs 32, semaphore := ← Zig.Enc.decodeAt bs 8 }

structure Shared where
  io : Zig.Io
  l : Io_RwLock
  n : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Shared where
  size := 64
  align := 8
  encode v := Zig.Enc.fields 64 [(0, Zig.Enc.encode v.io), (16, Zig.Enc.encode v.l), (56, Zig.Enc.encode v.n)]
  decode bs := do pure { io := ← Zig.Enc.decodeAt bs 0, l := ← Zig.Enc.decodeAt bs 16, n := ← Zig.Enc.decodeAt bs 56 }

structure SemCounter where
  io : Zig.Io
  s : Io_Semaphore
  n : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc SemCounter where
  size := 48
  align := 8
  encode v := Zig.Enc.fields 48 [(0, Zig.Enc.encode v.io), (16, Zig.Enc.encode v.s), (40, Zig.Enc.encode v.n)]
  decode bs := do pure { io := ← Zig.Enc.decodeAt bs 0, s := ← Zig.Enc.decodeAt bs 16, n := ← Zig.Enc.decodeAt bs 40 }

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

inductive Io_Event where
  | unset
  | waiting
  | is_set
  deriving Repr, Inhabited, DecidableEq

def Io_Event.toBits : Io_Event → BitVec 32
  | .unset => (0 : BitVec 32)
  | .waiting => (1 : BitVec 32)
  | .is_set => (2 : BitVec 32)

def Io_Event.ofInt? (v : Int) : Option Io_Event :=
  if v = 0 then Option.some .unset else if v = 1 then Option.some .waiting else if v = 2 then Option.some .is_set else Option.none

def Io_Event.isNamed (_ : Io_Event) : Bool := true

instance : Zig.Packed Io_Event 32 where
  toBits := Io_Event.toBits
  ofBits b := (Io_Event.ofInt? (Zig.val false b)).getD default
  valid b := (Io_Event.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc Io_Event where
  size := 4
  align := 4
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 32 ← Zig.Enc.decode bs
    match Io_Event.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

structure Box where
  io : Zig.Io
  m : Io_Mutex
  c : Io_Condition
  ready : Bool
  done : Io_Event
  v : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Box where
  size := 40
  align := 8
  encode v := Zig.Enc.fields 40 [(0, Zig.Enc.encode v.io), (16, Zig.Enc.encode v.m), (20, Zig.Enc.encode v.c), (36, Zig.Enc.encode v.ready), (28, Zig.Enc.encode v.done), (32, Zig.Enc.encode v.v)]
  decode bs := do pure { io := ← Zig.Enc.decodeAt bs 0, m := ← Zig.Enc.decodeAt bs 16, c := ← Zig.Enc.decodeAt bs 20, ready := ← Zig.Enc.decodeAt bs 36, done := ← Zig.Enc.decodeAt bs 28, v := ← Zig.Enc.decodeAt bs 32 }

structure Thread_SpawnConfig where
  stack_size : BitVec 64
  allocator : Option (Zig.Allocator)
  deriving Repr, Inhabited, DecidableEq

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

/-- The spawn targets of the program. -/
inductive Tgt where
  | producer (a : Zig.Ptr)
  | work (a : Zig.Ptr)
  | writer (a : Zig.Ptr)
  | semWork (a : Zig.Ptr)

structure Io_Condition_signalLocals where
  prev_state : Io_Condition_State
  deriving Inhabited

inductive Io_Condition_signalExit where
  | ret
  | br5 (v : Io_Condition_State)
  | br28 (v : Option (Io_Condition_State))
  | br19 (v : Io_Condition_State)
  | br37 (v : BitVec 32)
  | br12
  | br10
  | rep11

def Io_Condition_signal.again11 : Io_Condition_signalExit → Bool
  | .rep11 => true
  | _ => false

def Io_Condition_signal.loop11 (p0 : Zig.Ptr) (p1 : Zig.Io) : Zig.CM Tgt Io_Condition_signalLocals Io_Condition_signalExit := do
  match ← ((do
    let i14 ← pure (((← get).prev_state).waiters)
    let i16 ← pure (((← get).prev_state).signals)
    let i17 ← pure (Zig.gt false i14 i16)
    if i17 then (do
      match ← ((do
        let i20 ← pure (p0.add 0)
        let i21 ← pure ((← get).prev_state)
        let i23 ← pure (((← get).prev_state).waiters)
        let i25 ← pure (((← get).prev_state).signals)
        let i26 ← Zig.add false i25 (1 : BitVec 16)
        let i27 ← pure { waiters := i23, signals := i26 : Io_Condition_State }
        match ← ((do
          let i29 ← pure (i20.add 0)
          let i30 ← Zig.cmpxchgAsC Zig.AtomicOrder.release Zig.AtomicOrder.relaxed 4 i29 i21 i27
          pure (.br28 i30)) : Zig.CM Tgt Io_Condition_signalLocals Io_Condition_signalExit) with
        | .br28 v28 => (do
          let i32 ← pure ((v28).isSome)
          if i32 then (do
            let i34 ← Zig.optPayload v28
            pure (.br19 i34))
          else (do
            let i36 ← pure (p0.add 4)
            match ← ((do
              let i38 ← pure (i36.add 0)
              let i39 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.release 4 i38 (1 : BitVec 32)
              pure (.br37 i39)) : Zig.CM Tgt Io_Condition_signalLocals Io_Condition_signalExit) with
            | .br37 _v37 => (do
              let i41 ← pure (p0.add 4)
              let i42 ← pure (i41.add 0)
              let i43 ← pure (i42)
              let _i44 ← Zig.futexWakeC p1 i43 (1 : BitVec 32)
              pure .ret)
            | e => pure e))
        | e => pure e) : Zig.CM Tgt Io_Condition_signalLocals Io_Condition_signalExit) with
      | .br19 v19 => (do
        modify (fun s => { s with prev_state := v19 })
        pure .br12)
      | e => pure e)
    else (do
      pure .br10)) : Zig.CM Tgt Io_Condition_signalLocals Io_Condition_signalExit) with
  | .br12 => (do
    pure .rep11)
  | e => pure e

def Io_Condition_signal (p0 : Zig.Ptr) (p1 : Zig.Io) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i3 ← pure (p0.add 0)
    let i4 ← pure (i3)
    match ← ((do
      let i6 ← pure (i4.add 0)
      let i7 ← Zig.atomicLoadAsC (Io_Condition_State) Zig.AtomicOrder.relaxed 4 i6
      pure (.br5 i7)) : Zig.CM Tgt Io_Condition_signalLocals Io_Condition_signalExit) with
    | .br5 v5 => (do
      modify (fun s => { s with prev_state := v5 })
      match ← ((do
        Zig.loop (Io_Condition_signal.loop11 p0 p1) Io_Condition_signal.again11) : Zig.CM Tgt Io_Condition_signalLocals Io_Condition_signalExit) with
      | .br10 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Io_Condition_signalLocals Io_Condition_signalExit).run' (default : Io_Condition_signalLocals)
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

structure Io_Condition_waitInnerLocals where
  epoch : BitVec 32
  prev_state : Io_Condition_State
  deriving Inhabited

inductive Io_Condition_waitInnerExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br7 (v : BitVec 32)
  | br14 (v : Io_Condition_State)
  | br12
  | br25 (v : Except Zig.ErrName (Unit))
  | br41 (v : BitVec 32)
  | br50 (v : Io_Condition_State)
  | br72 (v : Option (Io_Condition_State))
  | br62 (v : Io_Condition_State)
  | br57
  | br55
  | br46
  | br87
  | br94 (v : Io_Condition_State)
  | br24
  | rep56
  | rep23

def Io_Condition_waitInner.again56 : Io_Condition_waitInnerExit → Bool
  | .rep56 => true
  | _ => false

def Io_Condition_waitInner.again23 : Io_Condition_waitInnerExit → Bool
  | .rep23 => true
  | _ => false

def Io_Condition_waitInner.loop56 (p0 : Zig.Ptr) (p1 : Zig.Io) (p2 : Zig.Ptr) : Zig.CM Tgt Io_Condition_waitInnerLocals Io_Condition_waitInnerExit := do
  match ← ((do
    let i59 ← pure (((← get).prev_state).signals)
    let i60 ← pure (Zig.gt false i59 (0 : BitVec 16))
    if i60 then (do
      match ← ((do
        let i63 ← pure (p0.add 0)
        let i64 ← pure ((← get).prev_state)
        let i66 ← pure (((← get).prev_state).waiters)
        let i67 ← Zig.sub false i66 (1 : BitVec 16)
        let i69 ← pure (((← get).prev_state).signals)
        let i70 ← Zig.sub false i69 (1 : BitVec 16)
        let i71 ← pure { waiters := i67, signals := i70 : Io_Condition_State }
        match ← ((do
          let i73 ← pure (i63.add 0)
          let i74 ← Zig.cmpxchgAsC Zig.AtomicOrder.acquire Zig.AtomicOrder.relaxed 4 i73 i64 i71
          pure (.br72 i74)) : Zig.CM Tgt Io_Condition_waitInnerLocals Io_Condition_waitInnerExit) with
        | .br72 v72 => (do
          let i76 ← pure ((v72).isSome)
          if i76 then (do
            let i78 ← Zig.optPayload v72
            pure (.br62 i78))
          else (do
            let _i80 ← Zig.callC (Io_Mutex_lockUncancelable p2 p1)
            pure (.ret (.ok () : Except Zig.ErrName (Unit)))))
        | e => pure e) : Zig.CM Tgt Io_Condition_waitInnerLocals Io_Condition_waitInnerExit) with
      | .br62 v62 => (do
        modify (fun s => { s with prev_state := v62 })
        pure .br57)
      | e => pure e)
    else (do
      pure .br55)) : Zig.CM Tgt Io_Condition_waitInnerLocals Io_Condition_waitInnerExit) with
  | .br57 => (do
    pure .rep56)
  | e => pure e

def Io_Condition_waitInner.loop23 (p0 : Zig.Ptr) (p1 : Zig.Io) (p2 : Zig.Ptr) (p3 : Bool) : Zig.CM Tgt Io_Condition_waitInnerLocals Io_Condition_waitInnerExit := do
  match ← ((do
    match ← ((do
      if p3 then (do
        let i27 ← pure (p0.add 4)
        let i28 ← pure (i27.add 0)
        let i29 ← pure (i28)
        let i30 ← pure ((← get).epoch)
        let _i31 ← Zig.futexWaitC p1 i29 i30
        pure (.br25 (.ok () : Except Zig.ErrName (Unit))))
      else (do
        let i33 ← pure (p0.add 4)
        let i34 ← pure (i33.add 0)
        let i35 ← pure (i34)
        let i36 ← pure ((← get).epoch)
        let i37 ← Zig.futexWaitCancelableC p1 i35 i36
        pure (.br25 i37))) : Zig.CM Tgt Io_Condition_waitInnerLocals Io_Condition_waitInnerExit) with
    | .br25 v25 => (do
      let i39 ← pure (p0.add 4)
      let i40 ← pure (i39)
      match ← ((do
        let i42 ← pure (i40.add 0)
        let i43 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.acquire 4 i42
        pure (.br41 i43)) : Zig.CM Tgt Io_Condition_waitInnerLocals Io_Condition_waitInnerExit) with
      | .br41 v41 => (do
        modify (fun s => { s with epoch := v41 })
        match ← ((do
          let i48 ← pure (p0.add 0)
          let i49 ← pure (i48)
          match ← ((do
            let i51 ← pure (i49.add 0)
            let i52 ← Zig.atomicLoadAsC (Io_Condition_State) Zig.AtomicOrder.relaxed 4 i51
            pure (.br50 i52)) : Zig.CM Tgt Io_Condition_waitInnerLocals Io_Condition_waitInnerExit) with
          | .br50 v50 => (do
            modify (fun s => { s with prev_state := v50 })
            match ← ((do
              Zig.loop (Io_Condition_waitInner.loop56 p0 p1 p2) Io_Condition_waitInner.again56) : Zig.CM Tgt Io_Condition_waitInnerLocals Io_Condition_waitInnerExit) with
            | .br55 => (do
              pure .br46)
            | e => pure e)
          | e => pure e) : Zig.CM Tgt Io_Condition_waitInnerLocals Io_Condition_waitInnerExit) with
        | .br46 => (do
          match ← ((do
            let i88 ← pure (Zig.isNonErr v25)
            if i88 then (do
              pure .br87)
            else (do
              let _i91 ← Zig.callRC (Zig.unwrapErr v25)
              let i92 ← Zig.callRC (Zig.unwrapErr v25)
              let i93 ← pure (p0.add 0)
              match ← ((do
                let i95 ← pure (i93.add 0)
                let i96 ← Zig.atomicRmwAsC Zig.RmwOp.sub Zig.AtomicOrder.relaxed 4 i95 (Zig.Packed.ofBits (1 : BitVec 32) : Io_Condition_State)
                pure (.br94 i96)) : Zig.CM Tgt Io_Condition_waitInnerLocals Io_Condition_waitInnerExit) with
              | .br94 v94 => (do
                let i98 ← pure ((v94).waiters)
                let i99 ← pure (Zig.gt false i98 (0 : BitVec 16))
                let _i100 ← Zig.callRC (debug_assert i99)
                let _i101 ← Zig.callC (Io_Mutex_lockUncancelable p2 p1)
                let i102 ← pure ((.error i92) : Except Zig.ErrName (Unit))
                pure (.ret i102))
              | e => pure e)) : Zig.CM Tgt Io_Condition_waitInnerLocals Io_Condition_waitInnerExit) with
          | .br87 => (do
            pure .br24)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Io_Condition_waitInnerLocals Io_Condition_waitInnerExit) with
  | .br24 => (do
    pure .rep23)
  | e => pure e

def Io_Condition_waitInner (p0 : Zig.Ptr) (p1 : Zig.Io) (p2 : Zig.Ptr) (p3 : Bool) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    let i5 ← pure (p0.add 4)
    let i6 ← pure (i5)
    match ← ((do
      let i8 ← pure (i6.add 0)
      let i9 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.acquire 4 i8
      pure (.br7 i9)) : Zig.CM Tgt Io_Condition_waitInnerLocals Io_Condition_waitInnerExit) with
    | .br7 v7 => (do
      modify (fun s => { s with epoch := v7 })
      match ← ((do
        let i13 ← pure (p0.add 0)
        match ← ((do
          let i15 ← pure (i13.add 0)
          let i16 ← Zig.atomicRmwAsC Zig.RmwOp.add Zig.AtomicOrder.relaxed 4 i15 (Zig.Packed.ofBits (1 : BitVec 32) : Io_Condition_State)
          pure (.br14 i16)) : Zig.CM Tgt Io_Condition_waitInnerLocals Io_Condition_waitInnerExit) with
        | .br14 v14 => (do
          let i18 ← pure ((v14).waiters)
          let i19 ← pure (Zig.lt false i18 (65535 : BitVec 16))
          let _i20 ← Zig.callRC (debug_assert i19)
          pure .br12)
        | e => pure e) : Zig.CM Tgt Io_Condition_waitInnerLocals Io_Condition_waitInnerExit) with
      | .br12 => (do
        let _i22 ← Zig.callC (Io_Mutex_unlock p2 p1)
        Zig.loop (Io_Condition_waitInner.loop23 p0 p1 p2 p3) Io_Condition_waitInner.again23)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Io_Condition_waitInnerLocals Io_Condition_waitInnerExit).run' (default : Io_Condition_waitInnerLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Io_Condition_waitLocals where
  deriving Inhabited

inductive Io_Condition_waitExit where
  | ret (v : Except Zig.ErrName (Unit))

def Io_Condition_wait (p0 : Zig.Ptr) (p1 : Zig.Io) (p2 : Zig.Ptr) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    let i3 ← Zig.callC (Io_Condition_waitInner p0 p1 p2 false)
    match i3 with
    | .error _ => (do
      let i5 ← Zig.callRC (Zig.unwrapErr i3)
      let i6 ← pure ((.error i5) : Except Zig.ErrName (Unit))
      pure (.ret i6))
    | .ok _v4 => (do
      pure (.ret (.ok () : Except Zig.ErrName (Unit))))) : Zig.CM Tgt Io_Condition_waitLocals Io_Condition_waitExit).run' (default : Io_Condition_waitLocals)
  match e with
  | .ret v => pure v

structure Io_Condition_waitUncancelableLocals where
  deriving Inhabited

inductive Io_Condition_waitUncancelableExit where
  | ret
  | br5

def Io_Condition_waitUncancelable (p0 : Zig.Ptr) (p1 : Zig.Io) (p2 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i3 ← Zig.callC (Io_Condition_waitInner p0 p1 p2 true)
    let i4 ← pure (Zig.isNonErr i3)
    match ← ((do
      if i4 then (do
        pure .br5)
      else (do
        let i8 ← Zig.callRC (Zig.unwrapErr i3)
        if i8 == "Canceled" then (do
          let _i12 ← pure (i8)
          throw .panic)
        else (do
          throw .panic))) : Zig.CM Tgt Io_Condition_waitUncancelableLocals Io_Condition_waitUncancelableExit) with
    | .br5 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt Io_Condition_waitUncancelableLocals Io_Condition_waitUncancelableExit).run' (default : Io_Condition_waitUncancelableLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Io_Event_setLocals where
  deriving Inhabited

inductive Io_Event_setExit where
  | ret
  | br3

def Io_Event_set (p0 : Zig.Ptr) (p1 : Zig.Io) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.atomicRmwAsC Zig.RmwOp.xchg Zig.AtomicOrder.release 4 p0 Io_Event.is_set
    match ← ((do
      match i2 with
      | .waiting => (do
        let i7 ← pure (p0)
        let _i8 ← Zig.futexWakeC p1 i7 (4294967295 : BitVec 32)
        pure .br3)
      | .unset | .is_set => (do
        pure .br3)) : Zig.CM Tgt Io_Event_setLocals Io_Event_setExit) with
    | .br3 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt Io_Event_setLocals Io_Event_setExit).run' (default : Io_Event_setLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Io_Event_waitUncancelableLocals where
  deriving Inhabited

inductive Io_Event_waitUncancelableExit where
  | ret
  | br7
  | br2
  | br18
  | rep17

def Io_Event_waitUncancelable.again17 : Io_Event_waitUncancelableExit → Bool
  | .rep17 => true
  | _ => false

def Io_Event_waitUncancelable.loop17 (p0 : Zig.Ptr) (p1 : Zig.Io) : Zig.CM Tgt Io_Event_waitUncancelableLocals Io_Event_waitUncancelableExit := do
  match ← ((do
    let i19 ← pure (p0)
    let _i20 ← Zig.futexWaitC p1 i19 Io_Event.waiting
    let i21 ← pure (p0)
    let i22 ← Zig.atomicLoadAsC (Io_Event) Zig.AtomicOrder.acquire 4 i21
    match i22 with
    | .unset => (do
      throw .unreachable)
    | .waiting => (do
      pure .br18)
    | .is_set => (do
      pure .ret)) : Zig.CM Tgt Io_Event_waitUncancelableLocals Io_Event_waitUncancelableExit) with
  | .br18 => (do
    pure .rep17)
  | e => pure e

def Io_Event_waitUncancelable (p0 : Zig.Ptr) (p1 : Zig.Io) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    match ← ((do
      let i3 ← Zig.cmpxchgAsC Zig.AtomicOrder.acquire Zig.AtomicOrder.acquire 4 p0 Io_Event.unset Io_Event.waiting
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        match ← ((do
          match i6 with
          | .unset => (do
            throw .unreachable)
          | .waiting => (do
            pure .br7)
          | .is_set => (do
            pure .ret)) : Zig.CM Tgt Io_Event_waitUncancelableLocals Io_Event_waitUncancelableExit) with
        | .br7 => (do
          pure .br2)
        | e => pure e)
      else (do
        pure .br2)) : Zig.CM Tgt Io_Event_waitUncancelableLocals Io_Event_waitUncancelableExit) with
    | .br2 => (do
      Zig.loop (Io_Event_waitUncancelable.loop17 p0 p1) Io_Event_waitUncancelable.again17)
    | e => pure e) : Zig.CM Tgt Io_Event_waitUncancelableLocals Io_Event_waitUncancelableExit).run' (default : Io_Event_waitUncancelableLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

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

structure Io_RwLock_lockSharedUncancelableLocals where
  state : BitVec 64
  deriving Inhabited

inductive Io_RwLock_lockSharedUncancelableExit where
  | ret
  | br15 (v : BitVec 64)
  | br9
  | br7
  | rep8

def Io_RwLock_lockSharedUncancelable.again8 : Io_RwLock_lockSharedUncancelableExit → Bool
  | .rep8 => true
  | _ => false

def Io_RwLock_lockSharedUncancelable.loop8 (p0 : Zig.Ptr) : Zig.CM Tgt Io_RwLock_lockSharedUncancelableLocals Io_RwLock_lockSharedUncancelableExit := do
  match ← ((do
    let i10 ← pure ((← get).state)
    let i11 ← pure (i10 &&& (4294967295 : BitVec 64))
    let i12 ← pure (i11)
    let i13 ← pure (i12 == (0 : BitVec 64))
    if i13 then (do
      match ← ((do
        let i16 ← pure (p0.add 0)
        let i17 ← pure ((← get).state)
        let i18 ← pure ((← get).state)
        let i19 ← Zig.add false i18 (4294967296 : BitVec 64)
        let i20 ← Zig.cmpxchgC Zig.AtomicOrder.seqCst Zig.AtomicOrder.seqCst 8 i16 i17 i19
        let i21 ← pure ((i20).isSome)
        if i21 then (do
          let i23 ← Zig.optPayload i20
          pure (.br15 i23))
        else (do
          pure .ret)) : Zig.CM Tgt Io_RwLock_lockSharedUncancelableLocals Io_RwLock_lockSharedUncancelableExit) with
      | .br15 v15 => (do
        modify (fun s => { s with state := v15 })
        pure .br9)
      | e => pure e)
    else (do
      pure .br7)) : Zig.CM Tgt Io_RwLock_lockSharedUncancelableLocals Io_RwLock_lockSharedUncancelableExit) with
  | .br9 => (do
    pure .rep8)
  | e => pure e

def Io_RwLock_lockSharedUncancelable (p0 : Zig.Ptr) (p1 : Zig.Io) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i3 ← pure (p0.add 0)
    let i4 ← pure (i3)
    let i5 ← Zig.atomicLoadC (n := 64) Zig.AtomicOrder.seqCst 8 i4
    modify (fun s => { s with state := i5 })
    match ← ((do
      Zig.loop (Io_RwLock_lockSharedUncancelable.loop8 p0) Io_RwLock_lockSharedUncancelable.again8) : Zig.CM Tgt Io_RwLock_lockSharedUncancelableLocals Io_RwLock_lockSharedUncancelableExit) with
    | .br7 => (do
      let i30 ← pure (p0.add 32)
      let _i31 ← Zig.callC (Io_Mutex_lockUncancelable i30 p1)
      let i32 ← pure (p0.add 0)
      let _i33 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.seqCst 8 i32 (4294967296 : BitVec 64)
      let i34 ← pure (p0.add 32)
      let _i35 ← Zig.callC (Io_Mutex_unlock i34 p1)
      pure .ret)
    | e => pure e) : Zig.CM Tgt Io_RwLock_lockSharedUncancelableLocals Io_RwLock_lockSharedUncancelableExit).run' (default : Io_RwLock_lockSharedUncancelableLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Io_Semaphore_waitUncancelableLocals where
  deriving Inhabited

inductive Io_Semaphore_waitUncancelableExit where
  | ret
  | br6
  | br4
  | br22
  | rep5

def Io_Semaphore_waitUncancelable.again5 : Io_Semaphore_waitUncancelableExit → Bool
  | .rep5 => true
  | _ => false

def Io_Semaphore_waitUncancelable.loop5 (p0 : Zig.Ptr) (p1 : Zig.Io) : Zig.CM Tgt Io_Semaphore_waitUncancelableLocals Io_Semaphore_waitUncancelableExit := do
  match ← ((do
    let i7 ← pure (p0.add 0)
    let i8 ← Zig.load (BitVec 64) 8 i7
    let i9 ← pure (i8)
    let i10 ← pure (i9 == (0 : BitVec 64))
    if i10 then (do
      let i12 ← pure (p0.add 12)
      let i13 ← pure (p0.add 8)
      let _i14 ← Zig.callC (Io_Condition_waitUncancelable i12 p1 i13)
      pure .br6)
    else (do
      pure .br4)) : Zig.CM Tgt Io_Semaphore_waitUncancelableLocals Io_Semaphore_waitUncancelableExit) with
  | .br6 => (do
    pure .rep5)
  | e => pure e

def Io_Semaphore_waitUncancelable (p0 : Zig.Ptr) (p1 : Zig.Io) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← pure (p0.add 8)
    let _i3 ← Zig.callC (Io_Mutex_lockUncancelable i2 p1)
    match ← ((do
      Zig.loop (Io_Semaphore_waitUncancelable.loop5 p0 p1) Io_Semaphore_waitUncancelable.again5) : Zig.CM Tgt Io_Semaphore_waitUncancelableLocals Io_Semaphore_waitUncancelableExit) with
    | .br4 => (do
      let i18 ← pure (p0.add 0)
      let i19 ← Zig.load (BitVec 64) 8 i18
      let i20 ← Zig.sub false i19 (1 : BitVec 64)
      Zig.store (α := BitVec 64) 8 i18 i20
      match ← ((do
        let i23 ← pure (p0.add 0)
        let i24 ← Zig.load (BitVec 64) 8 i23
        let i25 ← pure (i24)
        let i26 ← pure (Zig.gt false i25 (0 : BitVec 64))
        if i26 then (do
          let i28 ← pure (p0.add 12)
          let _i29 ← Zig.callC (Io_Condition_signal i28 p1)
          pure .br22)
        else (do
          pure .br22)) : Zig.CM Tgt Io_Semaphore_waitUncancelableLocals Io_Semaphore_waitUncancelableExit) with
      | .br22 => (do
        let i32 ← pure (p0.add 8)
        let _i33 ← Zig.callC (Io_Mutex_unlock i32 p1)
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Io_Semaphore_waitUncancelableLocals Io_Semaphore_waitUncancelableExit).run' (default : Io_Semaphore_waitUncancelableLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Io_RwLock_lockUncancelableLocals where
  deriving Inhabited

inductive Io_RwLock_lockUncancelableExit where
  | ret
  | br8

def Io_RwLock_lockUncancelable (p0 : Zig.Ptr) (p1 : Zig.Io) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← pure (p0.add 0)
    let _i3 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.seqCst 8 i2 (2 : BitVec 64)
    let i4 ← pure (p0.add 32)
    let _i5 ← Zig.callC (Io_Mutex_lockUncancelable i4 p1)
    let i6 ← pure (p0.add 0)
    let i7 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.seqCst 8 i6 (18446744073709551615 : BitVec 64)
    match ← ((do
      let i9 ← pure (i7 &&& (9223372032559808512 : BitVec 64))
      let i10 ← pure (i9)
      let i11 ← pure (i10 != (0 : BitVec 64))
      if i11 then (do
        let i13 ← pure (p0.add 8)
        let _i14 ← Zig.callC (Io_Semaphore_waitUncancelable i13 p1)
        pure .br8)
      else (do
        pure .br8)) : Zig.CM Tgt Io_RwLock_lockUncancelableLocals Io_RwLock_lockUncancelableExit) with
    | .br8 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt Io_RwLock_lockUncancelableLocals Io_RwLock_lockUncancelableExit).run' (default : Io_RwLock_lockUncancelableLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Io_RwLock_unlockLocals where
  deriving Inhabited

inductive Io_RwLock_unlockExit where
  | ret

def Io_RwLock_unlock (p0 : Zig.Ptr) (p1 : Zig.Io) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← pure (p0.add 0)
    let _i3 ← Zig.atomicRmwC Zig.RmwOp.and false Zig.AtomicOrder.seqCst 8 i2 (18446744073709551614 : BitVec 64)
    let i4 ← pure (p0.add 32)
    let _i5 ← Zig.callC (Io_Mutex_unlock i4 p1)
    pure .ret) : Zig.CM Tgt Io_RwLock_unlockLocals Io_RwLock_unlockExit).run' (default : Io_RwLock_unlockLocals)
  match e with
  | .ret => pure ()

structure Io_Semaphore_postLocals where
  deriving Inhabited

inductive Io_Semaphore_postExit where
  | ret

def Io_Semaphore_post (p0 : Zig.Ptr) (p1 : Zig.Io) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← pure (p0.add 8)
    let _i3 ← Zig.callC (Io_Mutex_lockUncancelable i2 p1)
    let i4 ← pure (p0.add 0)
    let i5 ← Zig.load (BitVec 64) 8 i4
    let i6 ← Zig.add false i5 (1 : BitVec 64)
    Zig.store (α := BitVec 64) 8 i4 i6
    let i8 ← pure (p0.add 12)
    let _i9 ← Zig.callC (Io_Condition_signal i8 p1)
    let i10 ← pure (p0.add 8)
    let _i11 ← Zig.callC (Io_Mutex_unlock i10 p1)
    pure .ret) : Zig.CM Tgt Io_Semaphore_postLocals Io_Semaphore_postExit).run' (default : Io_Semaphore_postLocals)
  match e with
  | .ret => pure ()

structure Io_RwLock_unlockSharedLocals where
  deriving Inhabited

inductive Io_RwLock_unlockSharedExit where
  | ret
  | br8 (v : Bool)
  | br4

def Io_RwLock_unlockShared (p0 : Zig.Ptr) (p1 : Zig.Io) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← pure (p0.add 0)
    let i3 ← Zig.atomicRmwC Zig.RmwOp.sub false Zig.AtomicOrder.seqCst 8 i2 (4294967296 : BitVec 64)
    match ← ((do
      let i5 ← pure (i3 &&& (9223372032559808512 : BitVec 64))
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (4294967296 : BitVec 64))
      match ← ((do
        if i7 then (do
          let i10 ← pure (i3 &&& (1 : BitVec 64))
          let i11 ← pure (i10)
          let i12 ← pure (i11 != (0 : BitVec 64))
          pure (.br8 i12))
        else (do
          pure (.br8 false))) : Zig.CM Tgt Io_RwLock_unlockSharedLocals Io_RwLock_unlockSharedExit) with
      | .br8 v8 => (do
        if v8 then (do
          let i16 ← pure (p0.add 8)
          let _i17 ← Zig.callC (Io_Semaphore_post i16 p1)
          pure .br4)
        else (do
          pure .br4))
      | e => pure e) : Zig.CM Tgt Io_RwLock_unlockSharedLocals Io_RwLock_unlockSharedExit) with
    | .br4 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt Io_RwLock_unlockSharedLocals Io_RwLock_unlockSharedExit).run' (default : Io_RwLock_unlockSharedLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure producerLocals where
  deriving Inhabited

inductive producerExit where
  | ret

def producer (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure (p0.add 16)
    let i2 ← pure (p0.add 0)
    let i3 ← Zig.load (Zig.Io) 8 i2
    let _i4 ← Zig.callC (Io_Mutex_lockUncancelable i1 i3)
    let i5 ← pure (p0.add 32)
    Zig.store (α := BitVec 32) 4 i5 (7 : BitVec 32)
    let i7 ← pure (p0.add 36)
    Zig.store (α := Bool) 1 i7 true
    let i9 ← pure (p0.add 16)
    let i10 ← pure (p0.add 0)
    let i11 ← Zig.load (Zig.Io) 8 i10
    let _i12 ← Zig.callC (Io_Mutex_unlock i9 i11)
    let i13 ← pure (p0.add 20)
    let i14 ← pure (p0.add 0)
    let i15 ← Zig.load (Zig.Io) 8 i14
    let _i16 ← Zig.callC (Io_Condition_signal i13 i15)
    let i17 ← pure (p0.add 28)
    let i18 ← pure (p0.add 0)
    let i19 ← Zig.load (Zig.Io) 8 i18
    let _i20 ← Zig.callC (Io_Event_set i17 i19)
    pure .ret) : Zig.CM Tgt producerLocals producerExit).run' (default : producerLocals)
  match e with
  | .ret => pure ()

structure handoffLocals where
  b : Zig.Ptr
  deriving Inhabited

inductive handoffExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br25
  | br23
  | rep24

def handoff.again24 : handoffExit → Bool
  | .rep24 => true
  | _ => false

def handoff.loop24 (p0 : Zig.Io) (i1 : Zig.Ptr) : Zig.CM Tgt handoffLocals handoffExit := do
  match ← ((do
    let i26 ← pure (i1.add 36)
    let i27 ← Zig.load (Bool) 1 i26
    let i28 ← pure (!i27)
    if i28 then (do
      let i30 ← pure (i1.add 20)
      let i31 ← pure (i1.add 16)
      let _i32 ← Zig.callC (Io_Condition_waitUncancelable i30 p0 i31)
      pure .br25)
    else (do
      pure .br23)) : Zig.CM Tgt handoffLocals handoffExit) with
  | .br25 => (do
    pure .rep24)
  | e => pure e

def handoff (p0 : Zig.Io) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s1 ← Zig.allocStack 40 8
  let e ← ((do
    let i1 ← pure (← get).b
    let i2 ← pure (i1.add 0)
    Zig.store (α := Zig.Io) 8 i2 p0
    let i4 ← pure (i1.add 16)
    Zig.store (α := Io_Mutex) 4 i4 ({ state := ({ raw := Io_Mutex_State.unlocked } : atomic_Value_Io_Mutex_State) } : Io_Mutex)
    let i6 ← pure (i1.add 20)
    Zig.store (α := Io_Condition) 4 i6 ({ state := ({ raw := (Zig.Packed.ofBits (0 : BitVec 32) : Io_Condition_State) } : atomic_Value_Io_Condition_State), epoch := ({ raw := (0 : BitVec 32) } : atomic_Value_u32) } : Io_Condition)
    let i8 ← pure (i1.add 36)
    Zig.store (α := Bool) 1 i8 false
    let i10 ← pure (i1.add 28)
    Zig.store (α := Io_Event) 4 i10 Io_Event.unset
    let i12 ← pure (i1.add 32)
    Zig.store (α := BitVec 32) 4 i12 (0 : BitVec 32)
    let i14 ← pure (i1)
    let i15 ← Zig.spawnC (Tgt.producer i14)
    match i15 with
    | .error _ => (do
      let i17 ← Zig.callRC (Zig.unwrapErr i15)
      let i18 ← pure (i17)
      let i19 ← pure ((.error i18) : Except Zig.ErrName (BitVec 32))
      pure (.ret i19))
    | .ok v16 => (do
      let i21 ← pure (i1.add 16)
      let _i22 ← Zig.callC (Io_Mutex_lockUncancelable i21 p0)
      match ← ((do
        Zig.loop (handoff.loop24 p0 i1) handoff.again24) : Zig.CM Tgt handoffLocals handoffExit) with
      | .br23 => (do
        let i36 ← pure (i1.add 32)
        let i37 ← Zig.load (BitVec 32) 4 i36
        let i38 ← pure (i1.add 16)
        let _i39 ← Zig.callC (Io_Mutex_unlock i38 p0)
        let i40 ← pure (i1.add 28)
        let _i41 ← Zig.callC (Io_Event_waitUncancelable i40 p0)
        let _i42 ← Zig.joinC v16
        let i43 ← pure ((.ok i37) : Except Zig.ErrName (BitVec 32))
        pure (.ret i43))
      | e => pure e)) : Zig.CM Tgt handoffLocals handoffExit).run' { (default : handoffLocals) with b := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v
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

structure readSharedLocals where
  deriving Inhabited

inductive readSharedExit where
  | ret (v : BitVec 32)

def readShared (p0 : Zig.Ptr) : Zig.ConcM Tgt (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (p0.add 16)
    let i2 ← pure (p0.add 0)
    let i3 ← Zig.load (Zig.Io) 8 i2
    let _i4 ← Zig.callC (Io_RwLock_lockSharedUncancelable i1 i3)
    let i5 ← pure (p0.add 56)
    let i6 ← Zig.load (BitVec 32) 4 i5
    let i7 ← pure (p0.add 16)
    let i8 ← pure (p0.add 0)
    let i9 ← Zig.load (Zig.Io) 8 i8
    let _i10 ← Zig.callC (Io_RwLock_unlockShared i7 i9)
    pure (.ret i6)) : Zig.CM Tgt readSharedLocals readSharedExit).run' (default : readSharedLocals)
  match e with
  | .ret v => pure v

structure writerLocals where
  local1 : BitVec 64
  deriving Inhabited

inductive writerExit where
  | ret
  | br6
  | br3
  | rep4

def writer.again4 : writerExit → Bool
  | .rep4 => true
  | _ => false

def writer.loop4 (p0 : Zig.Ptr) : Zig.CM Tgt writerLocals writerExit := do
  let i5 ← pure ((← get).local1)
  match ← ((do
    let i7 ← pure (i5)
    let i8 ← pure (Zig.lt false i7 (2 : BitVec 64))
    if i8 then (do
      let i10 ← pure (p0.add 16)
      let i11 ← pure (p0.add 0)
      let i12 ← Zig.load (Zig.Io) 8 i11
      let _i13 ← Zig.callC (Io_RwLock_lockUncancelable i10 i12)
      let i14 ← pure (p0.add 56)
      let i15 ← Zig.load (BitVec 32) 4 i14
      let i16 ← Zig.add false i15 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 i14 i16
      let i18 ← pure (p0.add 16)
      let i19 ← pure (p0.add 0)
      let i20 ← Zig.load (Zig.Io) 8 i19
      let _i21 ← Zig.callC (Io_RwLock_unlock i18 i20)
      pure .br6)
    else (do
      pure .br3)) : Zig.CM Tgt writerLocals writerExit) with
  | .br6 => (do
    let i24 ← Zig.add false i5 (1 : BitVec 64)
    modify (fun s => { s with local1 := i24 })
    pure .rep4)
  | e => pure e

def writer (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    modify (fun s => { s with local1 := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (writer.loop4 p0) writer.again4) : Zig.CM Tgt writerLocals writerExit) with
    | .br3 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt writerLocals writerExit).run' (default : writerLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure rwLockReadLocals where
  sh : Zig.Ptr
  deriving Inhabited

inductive rwLockReadExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def rwLockRead (p0 : Zig.Io) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s1 ← Zig.allocStack 64 8
  let e ← ((do
    let i1 ← pure (← get).sh
    let i2 ← pure (i1.add 0)
    Zig.store (α := Zig.Io) 8 i2 p0
    let i4 ← pure (i1.add 16)
    Zig.store (α := Io_RwLock) 8 i4 ({ state := (0 : BitVec 64), mutex := ({ state := ({ raw := Io_Mutex_State.unlocked } : atomic_Value_Io_Mutex_State) } : Io_Mutex), semaphore := ({ mutex := ({ state := ({ raw := Io_Mutex_State.unlocked } : atomic_Value_Io_Mutex_State) } : Io_Mutex), cond := ({ state := ({ raw := (Zig.Packed.ofBits (0 : BitVec 32) : Io_Condition_State) } : atomic_Value_Io_Condition_State), epoch := ({ raw := (0 : BitVec 32) } : atomic_Value_u32) } : Io_Condition), permits := (0 : BitVec 64) } : Io_Semaphore) } : Io_RwLock)
    let i6 ← pure (i1.add 56)
    Zig.store (α := BitVec 32) 4 i6 (0 : BitVec 32)
    let i8 ← pure (i1)
    let i9 ← Zig.spawnC (Tgt.writer i8)
    match i9 with
    | .error _ => (do
      let i11 ← Zig.callRC (Zig.unwrapErr i9)
      let i12 ← pure (i11)
      let i13 ← pure ((.error i12) : Except Zig.ErrName (BitVec 32))
      pure (.ret i13))
    | .ok v10 => (do
      let i15 ← Zig.callC (readShared i1)
      let _i16 ← Zig.joinC v10
      let i17 ← Zig.mul false (10 : BitVec 32) i15
      let i18 ← Zig.callC (readShared i1)
      let i19 ← Zig.add false i17 i18
      let i20 ← pure ((.ok i19) : Except Zig.ErrName (BitVec 32))
      pure (.ret i20))) : Zig.CM Tgt rwLockReadLocals rwLockReadExit).run' { (default : rwLockReadLocals) with sh := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

structure semWorkLocals where
  local1 : BitVec 64
  deriving Inhabited

inductive semWorkExit where
  | ret
  | br6
  | br3
  | rep4

def semWork.again4 : semWorkExit → Bool
  | .rep4 => true
  | _ => false

def semWork.loop4 (p0 : Zig.Ptr) : Zig.CM Tgt semWorkLocals semWorkExit := do
  let i5 ← pure ((← get).local1)
  match ← ((do
    let i7 ← pure (i5)
    let i8 ← pure (Zig.lt false i7 (2 : BitVec 64))
    if i8 then (do
      let i10 ← pure (p0.add 16)
      let i11 ← pure (p0.add 0)
      let i12 ← Zig.load (Zig.Io) 8 i11
      let _i13 ← Zig.callC (Io_Semaphore_waitUncancelable i10 i12)
      let i14 ← pure (p0.add 40)
      let i15 ← Zig.load (BitVec 32) 4 i14
      let i16 ← Zig.add false i15 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 i14 i16
      let i18 ← pure (p0.add 16)
      let i19 ← pure (p0.add 0)
      let i20 ← Zig.load (Zig.Io) 8 i19
      let _i21 ← Zig.callC (Io_Semaphore_post i18 i20)
      pure .br6)
    else (do
      pure .br3)) : Zig.CM Tgt semWorkLocals semWorkExit) with
  | .br6 => (do
    let i24 ← Zig.add false i5 (1 : BitVec 64)
    modify (fun s => { s with local1 := i24 })
    pure .rep4)
  | e => pure e

def semWork (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    modify (fun s => { s with local1 := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (semWork.loop4 p0) semWork.again4) : Zig.CM Tgt semWorkLocals semWorkExit) with
    | .br3 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt semWorkLocals semWorkExit).run' (default : semWorkLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure semaphoreCounterLocals where
  c : Zig.Ptr
  deriving Inhabited

inductive semaphoreCounterExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def semaphoreCounter (p0 : Zig.Io) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s1 ← Zig.allocStack 48 8
  let e ← ((do
    let i1 ← pure (← get).c
    let i2 ← pure (i1.add 0)
    Zig.store (α := Zig.Io) 8 i2 p0
    let i4 ← pure (i1.add 16)
    Zig.store (α := Io_Semaphore) 8 i4 ({ mutex := ({ state := ({ raw := Io_Mutex_State.unlocked } : atomic_Value_Io_Mutex_State) } : Io_Mutex), cond := ({ state := ({ raw := (Zig.Packed.ofBits (0 : BitVec 32) : Io_Condition_State) } : atomic_Value_Io_Condition_State), epoch := ({ raw := (0 : BitVec 32) } : atomic_Value_u32) } : Io_Condition), permits := (1 : BitVec 64) } : Io_Semaphore)
    let i6 ← pure (i1.add 40)
    Zig.store (α := BitVec 32) 4 i6 (0 : BitVec 32)
    let i8 ← pure (i1)
    let i9 ← Zig.spawnC (Tgt.semWork i8)
    match i9 with
    | .error _ => (do
      let i11 ← Zig.callRC (Zig.unwrapErr i9)
      let i12 ← pure (i11)
      let i13 ← pure ((.error i12) : Except Zig.ErrName (BitVec 32))
      pure (.ret i13))
    | .ok v10 => (do
      let _i15 ← Zig.callC (semWork i1)
      let _i16 ← Zig.joinC v10
      let i17 ← pure (i1.add 40)
      let i18 ← Zig.load (BitVec 32) 4 i17
      let i19 ← pure ((.ok i18) : Except Zig.ErrName (BitVec 32))
      pure (.ret i19))) : Zig.CM Tgt semaphoreCounterLocals semaphoreCounterExit).run' { (default : semaphoreCounterLocals) with c := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .producer a => discard (producer a)
  | .work a => discard (work a)
  | .writer a => discard (writer a)
  | .semWork a => discard (semWork a)

end Sync