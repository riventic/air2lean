import ZigLean


namespace Threadsync

structure c_timespec__struct_1 where
  sec : BitVec 64
  nsec : BitVec 64
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc c_timespec__struct_1 where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.sec), (8, Zig.Enc.encode v.nsec)]
  decode bs := do pure { sec := ← Zig.Enc.decodeAt bs 0, nsec := ← Zig.Enc.decodeAt bs 8 }

structure time_Instant where
  timestamp : c_timespec__struct_1
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc time_Instant where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.timestamp)]
  decode bs := do pure { timestamp := ← Zig.Enc.decodeAt bs 0 }

structure time_Timer where
  started : time_Instant
  previous : time_Instant
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc time_Timer where
  size := 32
  align := 8
  encode v := Zig.Enc.fields 32 [(0, Zig.Enc.encode v.started), (16, Zig.Enc.encode v.previous)]
  decode bs := do pure { started := ← Zig.Enc.decodeAt bs 0, previous := ← Zig.Enc.decodeAt bs 16 }

structure atomic_Value_usize where
  raw : BitVec 64
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc atomic_Value_usize where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.raw)]
  decode bs := do pure { raw := ← Zig.Enc.decodeAt bs 0 }

structure atomic_Value_u32 where
  raw : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc atomic_Value_u32 where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.raw)]
  decode bs := do pure { raw := ← Zig.Enc.decodeAt bs 0 }

structure Thread_ResetEvent_FutexImpl where
  state : atomic_Value_u32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Thread_ResetEvent_FutexImpl where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.state)]
  decode bs := do pure { state := ← Zig.Enc.decodeAt bs 0 }

structure Thread_ResetEvent where
  impl : Thread_ResetEvent_FutexImpl
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Thread_ResetEvent where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.impl)]
  decode bs := do pure { impl := ← Zig.Enc.decodeAt bs 0 }

structure Thread_WaitGroup where
  state : atomic_Value_usize
  event : Thread_ResetEvent
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Thread_WaitGroup where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.state), (8, Zig.Enc.encode v.event)]
  decode bs := do pure { state := ← Zig.Enc.decodeAt bs 0, event := ← Zig.Enc.decodeAt bs 8 }

structure c_darwin_os_unfair_lock where
  _os_unfair_lock_opaque : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc c_darwin_os_unfair_lock where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v._os_unfair_lock_opaque)]
  decode bs := do pure { _os_unfair_lock_opaque := ← Zig.Enc.decodeAt bs 0 }

structure Thread_Mutex_DarwinImpl where
  oul : c_darwin_os_unfair_lock
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Thread_Mutex_DarwinImpl where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.oul)]
  decode bs := do pure { oul := ← Zig.Enc.decodeAt bs 0 }

structure Thread_Mutex where
  impl : Thread_Mutex_DarwinImpl
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Thread_Mutex where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.impl)]
  decode bs := do pure { impl := ← Zig.Enc.decodeAt bs 0 }

structure Tally where
  wg : Thread_WaitGroup
  m : Thread_Mutex
  n : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Tally where
  size := 24
  align := 8
  encode v := Zig.Enc.fields 24 [(0, Zig.Enc.encode v.wg), (16, Zig.Enc.encode v.m), (20, Zig.Enc.encode v.n)]
  decode bs := do pure { wg := ← Zig.Enc.decodeAt bs 0, m := ← Zig.Enc.decodeAt bs 16, n := ← Zig.Enc.decodeAt bs 20 }

structure Counter where
  m : Thread_Mutex
  n : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Counter where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.m), (4, Zig.Enc.encode v.n)]
  decode bs := do pure { m := ← Zig.Enc.decodeAt bs 0, n := ← Zig.Enc.decodeAt bs 4 }

structure Thread_Condition_FutexImpl where
  state : atomic_Value_u32
  epoch : atomic_Value_u32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Thread_Condition_FutexImpl where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.state), (4, Zig.Enc.encode v.epoch)]
  decode bs := do pure { state := ← Zig.Enc.decodeAt bs 0, epoch := ← Zig.Enc.decodeAt bs 4 }

structure Thread_Condition where
  impl : Thread_Condition_FutexImpl
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Thread_Condition where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.impl)]
  decode bs := do pure { impl := ← Zig.Enc.decodeAt bs 0 }

structure Box where
  m : Thread_Mutex
  c : Thread_Condition
  ready : Bool
  done : Thread_ResetEvent
  v : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Box where
  size := 24
  align := 4
  encode v := Zig.Enc.fields 24 [(0, Zig.Enc.encode v.m), (4, Zig.Enc.encode v.c), (20, Zig.Enc.encode v.ready), (12, Zig.Enc.encode v.done), (16, Zig.Enc.encode v.v)]
  decode bs := do pure { m := ← Zig.Enc.decodeAt bs 0, c := ← Zig.Enc.decodeAt bs 4, ready := ← Zig.Enc.decodeAt bs 20, done := ← Zig.Enc.decodeAt bs 12, v := ← Zig.Enc.decodeAt bs 16 }

structure Thread_SpawnConfig where
  stack_size : BitVec 64
  allocator : Option (Zig.Allocator)
  deriving Repr, Inhabited, DecidableEq

structure Thread_Futex_Deadline where
  timeout : Option (BitVec 64)
  started : time_Timer
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Thread_Futex_Deadline where
  size := 48
  align := 8
  encode v := Zig.Enc.fields 48 [(0, Zig.Enc.encode v.timeout), (16, Zig.Enc.encode v.started)]
  decode bs := do pure { timeout := ← Zig.Enc.decodeAt bs 0, started := ← Zig.Enc.decodeAt bs 16 }

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

/-- The spawn targets of the program. -/
inductive Tgt where
  | producer (a : Zig.Ptr)
  | work (a : Zig.Ptr)
  | task (a : Zig.Ptr)

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

structure Thread_Mutex_unlockLocals where
  deriving Inhabited

inductive Thread_Mutex_unlockExit where
  | ret

def Thread_Mutex_unlock (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let _i2 ← Zig.osUnfairUnlockC i1
    pure .ret) : Zig.CM Tgt Thread_Mutex_unlockLocals Thread_Mutex_unlockExit).run' (default : Thread_Mutex_unlockLocals)
  match e with
  | .ret => pure ()

structure Thread_Futex_Deadline_initLocals where
  deadline : Zig.Bytes (Thread_Futex_Deadline)
  deriving Inhabited

inductive Thread_Futex_Deadline_initExit where
  | ret (v : Zig.Bytes (Thread_Futex_Deadline))
  | br11 (v : time_Timer)
  | br5

def Thread_Futex_Deadline_init (p0 : Option (BitVec 64)) : Zig.ConcM Tgt (Zig.Bytes (Thread_Futex_Deadline)) := do
  let e ← ((do
    modify (fun s => { s with deadline := Zig.Bytes.setUndef (Thread_Futex_Deadline) s.deadline 0 })
    modify (fun s => { s with deadline := Zig.Bytes.set s.deadline 0 (p0 : Option (BitVec 64)) })
    match ← ((do
      let i6 ← pure (← get).deadline
      let i7 ← Zig.Bytes.get (Option (BitVec 64)) i6 0
      let i8 ← pure ((i7).isSome)
      if i8 then (do
        match ← ((do
          let i12 ← Zig.callRC (throw Zig.Error.unsupportedTimer)
          let i13 ← pure (Zig.isNonErr i12)
          if i13 then (do
            let i15 ← Zig.callRC (Zig.unwrapPayload i12)
            pure (.br11 i15))
          else (do
            let i17 ← Zig.callRC (Zig.unwrapErr i12)
            let _i18 ← pure (i17)
            throw .panic)) : Zig.CM Tgt Thread_Futex_Deadline_initLocals Thread_Futex_Deadline_initExit) with
        | .br11 v11 => (do
          modify (fun s => { s with deadline := Zig.Bytes.set s.deadline 16 (v11 : time_Timer) })
          pure .br5)
        | e => pure e)
      else (do
        pure .br5)) : Zig.CM Tgt Thread_Futex_Deadline_initLocals Thread_Futex_Deadline_initExit) with
    | .br5 => (do
      let i24 ← pure (← get).deadline
      pure (.ret i24))
    | e => pure e) : Zig.CM Tgt Thread_Futex_Deadline_initLocals Thread_Futex_Deadline_initExit).run' { (default : Thread_Futex_Deadline_initLocals) with deadline := Zig.Bytes.undef (Thread_Futex_Deadline) }
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure math_sub__anon_1Locals where
  deriving Inhabited

inductive math_sub__anon_1Exit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br3

def math_sub__anon_1 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← pure (Zig.subWithOverflow false p0 p1)
    match ← ((do
      let i4 ← pure ((i2).2)
      let i5 ← pure (i4 != (0 : BitVec 1))
      if i5 then (do
        pure (.ret (.error "Overflow" : Except Zig.ErrName (BitVec 64))))
      else (do
        pure .br3)) : Zig.M math_sub__anon_1Locals math_sub__anon_1Exit) with
    | .br3 => (do
      let i9 ← pure ((i2).1)
      let i10 ← pure ((.ok i9) : Except Zig.ErrName (BitVec 64))
      pure (.ret i10))
    | e => pure e) : Zig.M math_sub__anon_1Locals math_sub__anon_1Exit).run' (default : math_sub__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Thread_Futex_Deadline_waitLocals where
  deriving Inhabited

inductive Thread_Futex_Deadline_waitExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br3 (v : BitVec 64)
  | br14 (v : BitVec 64)

def Thread_Futex_Deadline_wait (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure p0
      let i5 ← Zig.load (Option (BitVec 64)) 8 i4
      let i6 ← pure ((i5).isSome)
      if i6 then (do
        let i8 ← Zig.optPayload i5
        pure (.br3 i8))
      else (do
        let _i10 ← Zig.threadFutexWaitC p1 p2
        pure (.ret (.ok () : Except Zig.ErrName (Unit))))) : Zig.CM Tgt Thread_Futex_Deadline_waitLocals Thread_Futex_Deadline_waitExit) with
    | .br3 v3 => (do
      let i12 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
      let i13 ← Zig.callRC (throw Zig.Error.unsupportedTimer)
      match ← ((do
        let i15 ← Zig.callRC (math_sub__anon_1 v3 i13)
        let i16 ← pure (Zig.isNonErr i15)
        if i16 then (do
          let i18 ← Zig.callRC (Zig.unwrapPayload i15)
          pure (.br14 i18))
        else (do
          let _i20 ← Zig.callRC (Zig.unwrapErr i15)
          pure (.br14 (0 : BitVec 64)))) : Zig.CM Tgt Thread_Futex_Deadline_waitLocals Thread_Futex_Deadline_waitExit) with
      | .br14 v14 => (do
        let i22 ← Zig.callRC (throw Zig.Error.unsupportedTimer)
        pure (.ret i22))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_Futex_Deadline_waitLocals Thread_Futex_Deadline_waitExit).run' (default : Thread_Futex_Deadline_waitLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Thread_Mutex_lockLocals where
  deriving Inhabited

inductive Thread_Mutex_lockExit where
  | ret

def Thread_Mutex_lock (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let _i2 ← Zig.osUnfairLockC i1
    pure .ret) : Zig.CM Tgt Thread_Mutex_lockLocals Thread_Mutex_lockExit).run' (default : Thread_Mutex_lockLocals)
  match e with
  | .ret => pure ()

structure Thread_Condition_FutexImpl_waitLocals where
  epoch : BitVec 32
  state : BitVec 32
  futex_deadline : Zig.Ptr
  deriving Inhabited

inductive Thread_Condition_FutexImpl_waitExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br6 (v : BitVec 32)
  | br13 (v : BitVec 32)
  | br35
  | br58 (v : Option (BitVec 32))
  | br55 (v : BitVec 32)
  | br51
  | br46
  | br44
  | br78 (v : Option (BitVec 32))
  | br75 (v : BitVec 32)
  | br43
  | br94 (v : BitVec 32)
  | br101 (v : BitVec 32)
  | br120 (v : Option (BitVec 32))
  | br117 (v : BitVec 32)
  | br113
  | br108
  | br106
  | rep45
  | rep42
  | rep107
  | rep29

def Thread_Condition_FutexImpl_wait.again107 : Thread_Condition_FutexImpl_waitExit → Bool
  | .rep107 => true
  | _ => false

def Thread_Condition_FutexImpl_wait.again45 : Thread_Condition_FutexImpl_waitExit → Bool
  | .rep45 => true
  | _ => false

def Thread_Condition_FutexImpl_wait.again42 : Thread_Condition_FutexImpl_waitExit → Bool
  | .rep42 => true
  | _ => false

def Thread_Condition_FutexImpl_wait.again29 : Thread_Condition_FutexImpl_waitExit → Bool
  | .rep29 => true
  | _ => false

def Thread_Condition_FutexImpl_wait.loop107 (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit := do
  match ← ((do
    let i109 ← pure ((← get).state)
    let i110 ← pure (i109 &&& (4294901760 : BitVec 32))
    let i111 ← pure (i110 != (0 : BitVec 32))
    if i111 then (do
      match ← ((do
        let i114 ← pure ((← get).state)
        let i115 ← Zig.sub false i114 (1 : BitVec 32)
        let i116 ← Zig.sub false i115 (65536 : BitVec 32)
        match ← ((do
          let i118 ← pure p0
          let i119 ← pure ((← get).state)
          match ← ((do
            let i121 ← pure i118
            let i122 ← Zig.cmpxchgWeakC Zig.AtomicOrder.acquire Zig.AtomicOrder.relaxed 4 i121 i119 i116
            pure (.br120 i122)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
          | .br120 v120 => (do
            let i124 ← pure ((v120).isSome)
            if i124 then (do
              let i126 ← Zig.optPayload v120
              pure (.br117 i126))
            else (do
              let _i128 ← Zig.callC (Thread_Mutex_lock p1)
              pure (.ret (.ok () : Except Zig.ErrName (Unit)))))
          | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
        | .br117 v117 => (do
          modify (fun s => { s with state := v117 })
          pure .br113)
        | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
      | .br113 => (do
        pure .br108)
      | e => pure e)
    else (do
      pure .br106)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
  | .br108 => (do
    pure .rep107)
  | e => pure e

def Thread_Condition_FutexImpl_wait.loop45 (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit := do
  match ← ((do
    let i47 ← pure ((← get).state)
    let i48 ← pure (i47 &&& (4294901760 : BitVec 32))
    let i49 ← pure (i48 != (0 : BitVec 32))
    if i49 then (do
      match ← ((do
        let i52 ← pure ((← get).state)
        let i53 ← Zig.sub false i52 (1 : BitVec 32)
        let i54 ← Zig.sub false i53 (65536 : BitVec 32)
        match ← ((do
          let i56 ← pure p0
          let i57 ← pure ((← get).state)
          match ← ((do
            let i59 ← pure i56
            let i60 ← Zig.cmpxchgWeakC Zig.AtomicOrder.acquire Zig.AtomicOrder.relaxed 4 i59 i57 i54
            pure (.br58 i60)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
          | .br58 v58 => (do
            let i62 ← pure ((v58).isSome)
            if i62 then (do
              let i64 ← Zig.optPayload v58
              pure (.br55 i64))
            else (do
              let _i66 ← Zig.callC (Thread_Mutex_lock p1)
              pure (.ret (.ok () : Except Zig.ErrName (Unit)))))
          | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
        | .br55 v55 => (do
          modify (fun s => { s with state := v55 })
          pure .br51)
        | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
      | .br51 => (do
        pure .br46)
      | e => pure e)
    else (do
      pure .br44)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
  | .br46 => (do
    pure .rep45)
  | e => pure e

def Thread_Condition_FutexImpl_wait.loop42 (p0 : Zig.Ptr) (p1 : Zig.Ptr) (i38 : Zig.ErrName) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit := do
  match ← ((do
    match ← ((do
      Zig.loop (Thread_Condition_FutexImpl_wait.loop45 p0 p1) Thread_Condition_FutexImpl_wait.again45) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
    | .br44 => (do
      let i73 ← pure ((← get).state)
      let i74 ← Zig.sub false i73 (1 : BitVec 32)
      match ← ((do
        let i76 ← pure p0
        let i77 ← pure ((← get).state)
        match ← ((do
          let i79 ← pure i76
          let i80 ← Zig.cmpxchgWeakC Zig.AtomicOrder.relaxed Zig.AtomicOrder.relaxed 4 i79 i77 i74
          pure (.br78 i80)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
        | .br78 v78 => (do
          let i82 ← pure ((v78).isSome)
          if i82 then (do
            let i84 ← Zig.optPayload v78
            pure (.br75 i84))
          else (do
            let _i86 ← Zig.callC (Thread_Mutex_lock p1)
            let i87 ← pure ((.error i38) : Except Zig.ErrName (Unit))
            pure (.ret i87)))
        | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
      | .br75 v75 => (do
        modify (fun s => { s with state := v75 })
        pure .br43)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
  | .br43 => (do
    pure .rep42)
  | e => pure e

def Thread_Condition_FutexImpl_wait.loop29 (p0 : Zig.Ptr) (p1 : Zig.Ptr) (i26 : Zig.Ptr) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit := do
  let i30 ← Zig.callMC (Zig.ptrProject p0 (·.add 4))
  let i31 ← pure (i30)
  let i32 ← pure ((← get).epoch)
  let i33 ← Zig.callC (Thread_Futex_Deadline_wait i26 i31 i32)
  let i34 ← pure (Zig.isNonErr i33)
  match ← ((do
    if i34 then (do
      pure .br35)
    else (do
      let i38 ← Zig.callRC (Zig.unwrapErr i33)
      if i38 == "Timeout" then (do
        Zig.loop (Thread_Condition_FutexImpl_wait.loop42 p0 p1 i38) Thread_Condition_FutexImpl_wait.again42)
      else (do
        throw .panic))) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
  | .br35 => (do
    let i92 ← Zig.callMC (Zig.ptrProject p0 (·.add 4))
    let i93 ← pure (i92)
    match ← ((do
      let i95 ← pure i93
      let i96 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.acquire 4 i95
      pure (.br94 i96)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
    | .br94 v94 => (do
      modify (fun s => { s with epoch := v94 })
      let i99 ← pure p0
      let i100 ← pure (i99)
      match ← ((do
        let i102 ← pure i100
        let i103 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.relaxed 4 i102
        pure (.br101 i103)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
      | .br101 v101 => (do
        modify (fun s => { s with state := v101 })
        match ← ((do
          Zig.loop (Thread_Condition_FutexImpl_wait.loop107 p0 p1) Thread_Condition_FutexImpl_wait.again107) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
        | .br106 => (do
          pure .rep29)
        | e => pure e)
      | e => pure e)
    | e => pure e)
  | e => pure e

def Thread_Condition_FutexImpl_wait (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : Option (BitVec 64)) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let s26 ← Zig.allocStack 48 8
  let e ← ((do
    let i4 ← Zig.callMC (Zig.ptrProject p0 (·.add 4))
    let i5 ← pure (i4)
    match ← ((do
      let i7 ← pure i5
      let i8 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.acquire 4 i7
      pure (.br6 i8)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
    | .br6 v6 => (do
      modify (fun s => { s with epoch := v6 })
      let i12 ← pure p0
      match ← ((do
        let i14 ← pure i12
        let i15 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.relaxed 4 i14 (1 : BitVec 32)
        pure (.br13 i15)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
      | .br13 v13 => (do
        modify (fun s => { s with state := v13 })
        let i18 ← pure ((← get).state)
        let i19 ← pure (i18 &&& (65535 : BitVec 32))
        let i20 ← pure (i19 != (65535 : BitVec 32))
        let _i21 ← Zig.callRC (debug_assert i20)
        let i22 ← pure ((← get).state)
        let i23 ← Zig.add false i22 (1 : BitVec 32)
        modify (fun s => { s with state := i23 })
        let _i25 ← Zig.callC (Thread_Mutex_unlock p1)
        let i26 ← pure (← get).futex_deadline
        let i27 ← Zig.callC (Thread_Futex_Deadline_init p2)
        Zig.storeBytes i26 8 i27
        Zig.loop (Thread_Condition_FutexImpl_wait.loop29 p0 p1 i26) Thread_Condition_FutexImpl_wait.again29)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit).run' { (default : Thread_Condition_FutexImpl_waitLocals) with futex_deadline := s26 }
  Zig.free s26
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Thread_Condition_FutexImpl_wake__anon_1Locals where
  state : BitVec 32
  deriving Inhabited

inductive Thread_Condition_FutexImpl_wake__anon_1Exit where
  | ret
  | br4 (v : BitVec 32)
  | br18
  | br28 (v : Option (BitVec 32))
  | br25 (v : BitVec 32)
  | br37 (v : BitVec 32)
  | br10
  | rep9

def Thread_Condition_FutexImpl_wake__anon_1.again9 : Thread_Condition_FutexImpl_wake__anon_1Exit → Bool
  | .rep9 => true
  | _ => false

def Thread_Condition_FutexImpl_wake__anon_1.loop9 (p0 : Zig.Ptr) : Zig.CM Tgt Thread_Condition_FutexImpl_wake__anon_1Locals Thread_Condition_FutexImpl_wake__anon_1Exit := do
  match ← ((do
    let i11 ← pure ((← get).state)
    let i12 ← pure (i11 &&& (65535 : BitVec 32))
    let i13 ← Zig.divTrunc false i12 (1 : BitVec 32)
    let i14 ← pure ((← get).state)
    let i15 ← pure (i14 &&& (4294901760 : BitVec 32))
    let i16 ← Zig.divTrunc false i15 (65536 : BitVec 32)
    let i17 ← Zig.sub false i13 i16
    match ← ((do
      let i19 ← pure (i17 == (0 : BitVec 32))
      if i19 then (do
        pure .ret)
      else (do
        pure .br18)) : Zig.CM Tgt Thread_Condition_FutexImpl_wake__anon_1Locals Thread_Condition_FutexImpl_wake__anon_1Exit) with
    | .br18 => (do
      let i23 ← pure ((← get).state)
      let i24 ← Zig.add false i23 (65536 : BitVec 32)
      match ← ((do
        let i26 ← pure p0
        let i27 ← pure ((← get).state)
        match ← ((do
          let i29 ← pure i26
          let i30 ← Zig.cmpxchgWeakC Zig.AtomicOrder.release Zig.AtomicOrder.relaxed 4 i29 i27 i24
          pure (.br28 i30)) : Zig.CM Tgt Thread_Condition_FutexImpl_wake__anon_1Locals Thread_Condition_FutexImpl_wake__anon_1Exit) with
        | .br28 v28 => (do
          let i32 ← pure ((v28).isSome)
          if i32 then (do
            let i34 ← Zig.optPayload v28
            pure (.br25 i34))
          else (do
            let i36 ← Zig.callMC (Zig.ptrProject p0 (·.add 4))
            match ← ((do
              let i38 ← pure i36
              let i39 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.release 4 i38 (1 : BitVec 32)
              pure (.br37 i39)) : Zig.CM Tgt Thread_Condition_FutexImpl_wake__anon_1Locals Thread_Condition_FutexImpl_wake__anon_1Exit) with
            | .br37 _v37 => (do
              let i41 ← Zig.callMC (Zig.ptrProject p0 (·.add 4))
              let i42 ← pure (i41)
              let _i43 ← Zig.threadFutexWakeC i42 (1 : BitVec 32)
              pure .ret)
            | e => pure e))
        | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_wake__anon_1Locals Thread_Condition_FutexImpl_wake__anon_1Exit) with
      | .br25 v25 => (do
        modify (fun s => { s with state := v25 })
        pure .br10)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_wake__anon_1Locals Thread_Condition_FutexImpl_wake__anon_1Exit) with
  | .br10 => (do
    pure .rep9)
  | e => pure e

def Thread_Condition_FutexImpl_wake__anon_1 (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← pure (i2)
    match ← ((do
      let i5 ← pure i3
      let i6 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.relaxed 4 i5
      pure (.br4 i6)) : Zig.CM Tgt Thread_Condition_FutexImpl_wake__anon_1Locals Thread_Condition_FutexImpl_wake__anon_1Exit) with
    | .br4 v4 => (do
      modify (fun s => { s with state := v4 })
      Zig.loop (Thread_Condition_FutexImpl_wake__anon_1.loop9 p0) Thread_Condition_FutexImpl_wake__anon_1.again9)
    | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_wake__anon_1Locals Thread_Condition_FutexImpl_wake__anon_1Exit).run' (default : Thread_Condition_FutexImpl_wake__anon_1Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Thread_Condition_signalLocals where
  deriving Inhabited

inductive Thread_Condition_signalExit where
  | ret

def Thread_Condition_signal (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let _i2 ← Zig.callC (Thread_Condition_FutexImpl_wake__anon_1 i1)
    pure .ret) : Zig.CM Tgt Thread_Condition_signalLocals Thread_Condition_signalExit).run' (default : Thread_Condition_signalLocals)
  match e with
  | .ret => pure ()

structure Thread_Condition_waitLocals where
  deriving Inhabited

inductive Thread_Condition_waitExit where
  | ret
  | br5

def Thread_Condition_wait (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.callC (Thread_Condition_FutexImpl_wait i2 p1 none)
    let i4 ← pure (Zig.isNonErr i3)
    match ← ((do
      if i4 then (do
        pure .br5)
      else (do
        let i8 ← Zig.callRC (Zig.unwrapErr i3)
        if i8 == "Timeout" then (do
          let _i12 ← pure (i8)
          throw .panic)
        else (do
          throw .panic))) : Zig.CM Tgt Thread_Condition_waitLocals Thread_Condition_waitExit) with
    | .br5 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt Thread_Condition_waitLocals Thread_Condition_waitExit).run' (default : Thread_Condition_waitLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Thread_ResetEvent_FutexImpl_isSetLocals where
  deriving Inhabited

inductive Thread_ResetEvent_FutexImpl_isSetExit where
  | ret (v : Bool)
  | br2 (v : BitVec 32)

def Thread_ResetEvent_FutexImpl_isSet (p0 : Zig.Ptr) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    let i1 ← pure p0
    match ← ((do
      let i3 ← pure i1
      let i4 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.acquire 4 i3
      pure (.br2 i4)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_isSetLocals Thread_ResetEvent_FutexImpl_isSetExit) with
    | .br2 v2 => (do
      let i6 ← pure (v2 == (2 : BitVec 32))
      pure (.ret i6))
    | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_isSetLocals Thread_ResetEvent_FutexImpl_isSetExit).run' (default : Thread_ResetEvent_FutexImpl_isSetLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Thread_ResetEvent_FutexImpl_setLocals where
  deriving Inhabited

inductive Thread_ResetEvent_FutexImpl_setExit where
  | ret
  | br4 (v : BitVec 32)
  | br1
  | br14 (v : BitVec 32)
  | br12

def Thread_ResetEvent_FutexImpl_set (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure p0
      let i3 ← pure (i2)
      match ← ((do
        let i5 ← pure i3
        let i6 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.relaxed 4 i5
        pure (.br4 i6)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_setLocals Thread_ResetEvent_FutexImpl_setExit) with
      | .br4 v4 => (do
        let i8 ← pure (v4 == (2 : BitVec 32))
        if i8 then (do
          pure .ret)
        else (do
          pure .br1))
      | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_setLocals Thread_ResetEvent_FutexImpl_setExit) with
    | .br1 => (do
      match ← ((do
        let i13 ← pure p0
        match ← ((do
          let i15 ← pure i13
          let i16 ← Zig.atomicRmwC Zig.RmwOp.xchg false Zig.AtomicOrder.release 4 i15 (2 : BitVec 32)
          pure (.br14 i16)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_setLocals Thread_ResetEvent_FutexImpl_setExit) with
        | .br14 v14 => (do
          let i18 ← pure (v14 == (1 : BitVec 32))
          if i18 then (do
            let i20 ← pure p0
            let i21 ← pure (i20)
            let _i22 ← Zig.threadFutexWakeC i21 (4294967295 : BitVec 32)
            pure .br12)
          else (do
            pure .br12))
        | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_setLocals Thread_ResetEvent_FutexImpl_setExit) with
      | .br12 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_setLocals Thread_ResetEvent_FutexImpl_setExit).run' (default : Thread_ResetEvent_FutexImpl_setLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Thread_ResetEvent_FutexImpl_waitUntilSetLocals where
  state : BitVec 32
  futex_deadline : Zig.Ptr
  deriving Inhabited

inductive Thread_ResetEvent_FutexImpl_waitUntilSetExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br5 (v : BitVec 32)
  | br17 (v : Option (BitVec 32))
  | br14 (v : BitVec 32)
  | br10
  | br44 (v : BitVec 32)
  | br36
  | br49
  | br38
  | br29
  | rep37

def Thread_ResetEvent_FutexImpl_waitUntilSet.again37 : Thread_ResetEvent_FutexImpl_waitUntilSetExit → Bool
  | .rep37 => true
  | _ => false

def Thread_ResetEvent_FutexImpl_waitUntilSet.loop37 (p0 : Zig.Ptr) (i33 : Zig.Ptr) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit := do
  match ← ((do
    let i39 ← pure p0
    let i40 ← pure (i39)
    let i41 ← Zig.callC (Thread_Futex_Deadline_wait i33 i40 (1 : BitVec 32))
    let i42 ← pure p0
    let i43 ← pure (i42)
    match ← ((do
      let i45 ← pure i43
      let i46 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.acquire 4 i45
      pure (.br44 i46)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
    | .br44 v44 => (do
      modify (fun s => { s with state := v44 })
      match ← ((do
        let i50 ← pure ((← get).state)
        let i51 ← pure (i50 != (1 : BitVec 32))
        if i51 then (do
          pure .br36)
        else (do
          pure .br49)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
      | .br49 => (do
        match i41 with
        | .error _ => (do
          let i56 ← Zig.callRC (Zig.unwrapErr i41)
          let i57 ← pure ((.error i56) : Except Zig.ErrName (Unit))
          pure (.ret i57))
        | .ok _v55 => (do
          pure .br38))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
  | .br38 => (do
    pure .rep37)
  | e => pure e

def Thread_ResetEvent_FutexImpl_waitUntilSet (p0 : Zig.Ptr) (p1 : Option (BitVec 64)) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let s33 ← Zig.allocStack 48 8
  let e ← ((do
    let i3 ← pure p0
    let i4 ← pure (i3)
    match ← ((do
      let i6 ← pure i4
      let i7 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.acquire 4 i6
      pure (.br5 i7)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
    | .br5 v5 => (do
      modify (fun s => { s with state := v5 })
      match ← ((do
        let i11 ← pure ((← get).state)
        let i12 ← pure (i11 == (0 : BitVec 32))
        if i12 then (do
          match ← ((do
            let i15 ← pure p0
            let i16 ← pure ((← get).state)
            match ← ((do
              let i18 ← pure i15
              let i19 ← Zig.cmpxchgC Zig.AtomicOrder.acquire Zig.AtomicOrder.acquire 4 i18 i16 (1 : BitVec 32)
              pure (.br17 i19)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
            | .br17 v17 => (do
              let i21 ← pure ((v17).isSome)
              if i21 then (do
                let i23 ← Zig.optPayload v17
                pure (.br14 i23))
              else (do
                pure (.br14 (1 : BitVec 32))))
            | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
          | .br14 v14 => (do
            modify (fun s => { s with state := v14 })
            pure .br10)
          | e => pure e)
        else (do
          pure .br10)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
      | .br10 => (do
        match ← ((do
          let i30 ← pure ((← get).state)
          let i31 ← pure (i30 == (1 : BitVec 32))
          if i31 then (do
            let i33 ← pure (← get).futex_deadline
            let i34 ← Zig.callC (Thread_Futex_Deadline_init p1)
            Zig.storeBytes i33 8 i34
            match ← ((do
              Zig.loop (Thread_ResetEvent_FutexImpl_waitUntilSet.loop37 p0 i33) Thread_ResetEvent_FutexImpl_waitUntilSet.again37) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
            | .br36 => (do
              pure .br29)
            | e => pure e)
          else (do
            pure .br29)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
        | .br29 => (do
          let i63 ← pure ((← get).state)
          let i64 ← pure (i63 == (2 : BitVec 32))
          let _i65 ← Zig.callRC (debug_assert i64)
          pure (.ret (.ok () : Except Zig.ErrName (Unit))))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit).run' { (default : Thread_ResetEvent_FutexImpl_waitUntilSetLocals) with futex_deadline := s33 }
  Zig.free s33
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Thread_ResetEvent_FutexImpl_waitLocals where
  deriving Inhabited

inductive Thread_ResetEvent_FutexImpl_waitExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br2

def Thread_ResetEvent_FutexImpl_wait (p0 : Zig.Ptr) (p1 : Option (BitVec 64)) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (p0)
      let i4 ← Zig.callC (Thread_ResetEvent_FutexImpl_isSet i3)
      let i5 ← pure (!i4)
      if i5 then (do
        let i7 ← Zig.callC (Thread_ResetEvent_FutexImpl_waitUntilSet p0 p1)
        pure (.ret i7))
      else (do
        pure .br2)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitLocals Thread_ResetEvent_FutexImpl_waitExit) with
    | .br2 => (do
      pure (.ret (.ok () : Except Zig.ErrName (Unit))))
    | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitLocals Thread_ResetEvent_FutexImpl_waitExit).run' (default : Thread_ResetEvent_FutexImpl_waitLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Thread_ResetEvent_setLocals where
  deriving Inhabited

inductive Thread_ResetEvent_setExit where
  | ret

def Thread_ResetEvent_set (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let _i2 ← Zig.callC (Thread_ResetEvent_FutexImpl_set i1)
    pure .ret) : Zig.CM Tgt Thread_ResetEvent_setLocals Thread_ResetEvent_setExit).run' (default : Thread_ResetEvent_setLocals)
  match e with
  | .ret => pure ()

structure Thread_ResetEvent_waitLocals where
  deriving Inhabited

inductive Thread_ResetEvent_waitExit where
  | ret
  | br4

def Thread_ResetEvent_wait (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let i2 ← Zig.callC (Thread_ResetEvent_FutexImpl_wait i1 none)
    let i3 ← pure (Zig.isNonErr i2)
    match ← ((do
      if i3 then (do
        pure .br4)
      else (do
        let i7 ← Zig.callRC (Zig.unwrapErr i2)
        if i7 == "Timeout" then (do
          let _i11 ← pure (i7)
          throw .panic)
        else (do
          throw .panic))) : Zig.CM Tgt Thread_ResetEvent_waitLocals Thread_ResetEvent_waitExit) with
    | .br4 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt Thread_ResetEvent_waitLocals Thread_ResetEvent_waitExit).run' (default : Thread_ResetEvent_waitLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Thread_WaitGroup_finishLocals where
  deriving Inhabited

inductive Thread_WaitGroup_finishExit where
  | ret
  | br2 (v : BitVec 64)
  | br10

def Thread_WaitGroup_finish (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    match ← ((do
      let i3 ← pure i1
      let i4 ← Zig.atomicRmwC Zig.RmwOp.sub false Zig.AtomicOrder.acqRel 8 i3 (2 : BitVec 64)
      pure (.br2 i4)) : Zig.CM Tgt Thread_WaitGroup_finishLocals Thread_WaitGroup_finishExit) with
    | .br2 v2 => (do
      let i6 ← Zig.divTrunc false v2 (2 : BitVec 64)
      let i7 ← pure (i6)
      let i8 ← pure (Zig.gt false i7 (0 : BitVec 64))
      let _i9 ← Zig.callRC (debug_assert i8)
      match ← ((do
        let i11 ← pure (v2)
        let i12 ← pure (i11 == (3 : BitVec 64))
        if i12 then (do
          let i14 ← Zig.callMC (Zig.ptrProject p0 (·.add 8))
          let _i15 ← Zig.callC (Thread_ResetEvent_set i14)
          pure .br10)
        else (do
          pure .br10)) : Zig.CM Tgt Thread_WaitGroup_finishLocals Thread_WaitGroup_finishExit) with
      | .br10 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_WaitGroup_finishLocals Thread_WaitGroup_finishExit).run' (default : Thread_WaitGroup_finishLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Thread_WaitGroup_startManyLocals where
  deriving Inhabited

inductive Thread_WaitGroup_startManyExit where
  | ret
  | br4 (v : BitVec 64)

def Thread_WaitGroup_startMany (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.mul false (2 : BitVec 64) p1
    match ← ((do
      let i5 ← pure i2
      let i6 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.relaxed 8 i5 i3
      pure (.br4 i6)) : Zig.CM Tgt Thread_WaitGroup_startManyLocals Thread_WaitGroup_startManyExit) with
    | .br4 v4 => (do
      let i8 ← Zig.divTrunc false v4 (2 : BitVec 64)
      let i9 ← pure (i8)
      let i10 ← pure (Zig.lt false i9 (9223372036854775807 : BitVec 64))
      let _i11 ← Zig.callRC (debug_assert i10)
      pure .ret)
    | e => pure e) : Zig.CM Tgt Thread_WaitGroup_startManyLocals Thread_WaitGroup_startManyExit).run' (default : Thread_WaitGroup_startManyLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Thread_WaitGroup_waitLocals where
  deriving Inhabited

inductive Thread_WaitGroup_waitExit where
  | ret
  | br2 (v : BitVec 64)
  | br10

def Thread_WaitGroup_wait (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    match ← ((do
      let i3 ← pure i1
      let i4 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.acquire 8 i3 (1 : BitVec 64)
      pure (.br2 i4)) : Zig.CM Tgt Thread_WaitGroup_waitLocals Thread_WaitGroup_waitExit) with
    | .br2 v2 => (do
      let i6 ← pure (v2 &&& (1 : BitVec 64))
      let i7 ← pure (i6)
      let i8 ← pure (i7 == (0 : BitVec 64))
      let _i9 ← Zig.callRC (debug_assert i8)
      match ← ((do
        let i11 ← Zig.divTrunc false v2 (2 : BitVec 64)
        let i12 ← pure (i11)
        let i13 ← pure (Zig.gt false i12 (0 : BitVec 64))
        if i13 then (do
          let i15 ← Zig.callMC (Zig.ptrProject p0 (·.add 8))
          let _i16 ← Zig.callC (Thread_ResetEvent_wait i15)
          pure .br10)
        else (do
          pure .br10)) : Zig.CM Tgt Thread_WaitGroup_waitLocals Thread_WaitGroup_waitExit) with
      | .br10 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_WaitGroup_waitLocals Thread_WaitGroup_waitExit).run' (default : Thread_WaitGroup_waitLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure math_sub__anon_2Locals where
  deriving Inhabited

inductive math_sub__anon_2Exit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br3

def math_sub__anon_2 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← pure (Zig.subWithOverflow true p0 p1)
    match ← ((do
      let i4 ← pure ((i2).2)
      let i5 ← pure (i4 != (0 : BitVec 1))
      if i5 then (do
        pure (.ret (.error "Overflow" : Except Zig.ErrName (BitVec 64))))
      else (do
        pure .br3)) : Zig.M math_sub__anon_2Locals math_sub__anon_2Exit) with
    | .br3 => (do
      let i9 ← pure ((i2).1)
      let i10 ← pure ((.ok i9) : Except Zig.ErrName (BitVec 64))
      pure (.ret i10))
    | e => pure e) : Zig.M math_sub__anon_2Locals math_sub__anon_2Exit).run' (default : math_sub__anon_2Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure math_sub__anon_3Locals where
  deriving Inhabited

inductive math_sub__anon_3Exit where
  | ret (v : Except Zig.ErrName (BitVec 8))
  | br3

def math_sub__anon_3 (p0 : BitVec 8) (p1 : BitVec 8) : Zig.Result (Except Zig.ErrName (BitVec 8)) := do
  let e ← ((do
    let i2 ← pure (Zig.subWithOverflow false p0 p1)
    match ← ((do
      let i4 ← pure ((i2).2)
      let i5 ← pure (i4 != (0 : BitVec 1))
      if i5 then (do
        pure (.ret (.error "Overflow" : Except Zig.ErrName (BitVec 8))))
      else (do
        pure .br3)) : Zig.M math_sub__anon_3Locals math_sub__anon_3Exit) with
    | .br3 => (do
      let i9 ← pure ((i2).1)
      let i10 ← pure ((.ok i9) : Except Zig.ErrName (BitVec 8))
      pure (.ret i10))
    | e => pure e) : Zig.M math_sub__anon_3Locals math_sub__anon_3Exit).run' (default : math_sub__anon_3Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure math_sub__anon_4Locals where
  deriving Inhabited

inductive math_sub__anon_4Exit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br3

def math_sub__anon_4 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← pure (Zig.subWithOverflow false p0 p1)
    match ← ((do
      let i4 ← pure ((i2).2)
      let i5 ← pure (i4 != (0 : BitVec 1))
      if i5 then (do
        pure (.ret (.error "Overflow" : Except Zig.ErrName (BitVec 64))))
      else (do
        pure .br3)) : Zig.M math_sub__anon_4Locals math_sub__anon_4Exit) with
    | .br3 => (do
      let i9 ← pure ((i2).1)
      let i10 ← pure ((.ok i9) : Except Zig.ErrName (BitVec 64))
      pure (.ret i10))
    | e => pure e) : Zig.M math_sub__anon_4Locals math_sub__anon_4Exit).run' (default : math_sub__anon_4Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure producerLocals where
  deriving Inhabited

inductive producerExit where
  | ret

def producer (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let _i2 ← Zig.callC (Thread_Mutex_lock i1)
    let i3 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
    Zig.store (α := BitVec 32) 4 i3 (7 : BitVec 32)
    let i5 ← Zig.callMC (Zig.ptrProject p0 (·.add 20))
    Zig.store (α := Bool) 1 i5 true
    let i7 ← pure p0
    let _i8 ← Zig.callC (Thread_Mutex_unlock i7)
    let i9 ← Zig.callMC (Zig.ptrProject p0 (·.add 4))
    let _i10 ← Zig.callC (Thread_Condition_signal i9)
    let i11 ← Zig.callMC (Zig.ptrProject p0 (·.add 12))
    let _i12 ← Zig.callC (Thread_ResetEvent_set i11)
    pure .ret) : Zig.CM Tgt producerLocals producerExit).run' (default : producerLocals)
  match e with
  | .ret => pure ()

structure handoffLocals where
  b : Zig.Ptr
  deriving Inhabited

inductive handoffExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br13
  | br11
  | rep12

def handoff.again12 : handoffExit → Bool
  | .rep12 => true
  | _ => false

def handoff.loop12 (i0 : Zig.Ptr) : Zig.CM Tgt handoffLocals handoffExit := do
  match ← ((do
    let i14 ← Zig.callMC (Zig.ptrProject i0 (·.add 20))
    let i15 ← Zig.load (Bool) 1 i14
    let i16 ← pure (!i15)
    if i16 then (do
      let i18 ← Zig.callMC (Zig.ptrProject i0 (·.add 4))
      let i19 ← pure i0
      let _i20 ← Zig.callC (Thread_Condition_wait i18 i19)
      pure .br13)
    else (do
      pure .br11)) : Zig.CM Tgt handoffLocals handoffExit) with
  | .br13 => (do
    pure .rep12)
  | e => pure e

def handoff  : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s0 ← Zig.allocStack 24 4
  let e ← ((do
    let i0 ← pure (← get).b
    Zig.store (α := Box) 4 i0 ({ m := ({ impl := ({ oul := ({ _os_unfair_lock_opaque := (0 : BitVec 32) } : c_darwin_os_unfair_lock) } : Thread_Mutex_DarwinImpl) } : Thread_Mutex), c := ({ impl := ({ state := ({ raw := (0 : BitVec 32) } : atomic_Value_u32), epoch := ({ raw := (0 : BitVec 32) } : atomic_Value_u32) } : Thread_Condition_FutexImpl) } : Thread_Condition), ready := false, done := ({ impl := ({ state := ({ raw := (0 : BitVec 32) } : atomic_Value_u32) } : Thread_ResetEvent_FutexImpl) } : Thread_ResetEvent), v := (0 : BitVec 32) } : Box)
    let i2 ← pure (i0)
    let i3 ← Zig.spawnC (Tgt.producer i2)
    match i3 with
    | .error _ => (do
      let i5 ← Zig.callRC (Zig.unwrapErr i3)
      let i6 ← pure (i5)
      let i7 ← pure ((.error i6) : Except Zig.ErrName (BitVec 32))
      pure (.ret i7))
    | .ok v4 => (do
      let i9 ← pure i0
      let _i10 ← Zig.callC (Thread_Mutex_lock i9)
      match ← ((do
        Zig.loop (handoff.loop12 i0) handoff.again12) : Zig.CM Tgt handoffLocals handoffExit) with
      | .br11 => (do
        let i24 ← Zig.callMC (Zig.ptrProject i0 (·.add 16))
        let i25 ← Zig.load (BitVec 32) 4 i24
        let i26 ← pure i0
        let _i27 ← Zig.callC (Thread_Mutex_unlock i26)
        let i28 ← Zig.callMC (Zig.ptrProject i0 (·.add 12))
        let _i29 ← Zig.callC (Thread_ResetEvent_wait i28)
        let _i30 ← Zig.joinC v4
        let i31 ← pure ((.ok i25) : Except Zig.ErrName (BitVec 32))
        pure (.ret i31))
      | e => pure e)) : Zig.CM Tgt handoffLocals handoffExit).run' { (default : handoffLocals) with b := s0 }
  Zig.free s0
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
      let i10 ← pure p0
      let _i11 ← Zig.callC (Thread_Mutex_lock i10)
      let i12 ← Zig.callMC (Zig.ptrProject p0 (·.add 4))
      let i13 ← Zig.load (BitVec 32) 4 i12
      let i14 ← Zig.add false i13 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 i12 i14
      let i16 ← pure p0
      let _i17 ← Zig.callC (Thread_Mutex_unlock i16)
      pure .br6)
    else (do
      pure .br3)) : Zig.CM Tgt workLocals workExit) with
  | .br6 => (do
    let i20 ← Zig.add false i5 (1 : BitVec 64)
    modify (fun s => { s with local1 := i20 })
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

def mutexCounter  : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s0 ← Zig.allocStack 8 4
  let e ← ((do
    let i0 ← pure (← get).c
    Zig.store (α := Counter) 4 i0 ({ m := ({ impl := ({ oul := ({ _os_unfair_lock_opaque := (0 : BitVec 32) } : c_darwin_os_unfair_lock) } : Thread_Mutex_DarwinImpl) } : Thread_Mutex), n := (0 : BitVec 32) } : Counter)
    let i2 ← pure (i0)
    let i3 ← Zig.spawnC (Tgt.work i2)
    match i3 with
    | .error _ => (do
      let i5 ← Zig.callRC (Zig.unwrapErr i3)
      let i6 ← pure (i5)
      let i7 ← pure ((.error i6) : Except Zig.ErrName (BitVec 32))
      pure (.ret i7))
    | .ok v4 => (do
      let _i9 ← Zig.callC (work i0)
      let _i10 ← Zig.joinC v4
      let i11 ← Zig.load (Counter) 4 i0
      let i12 ← pure ((i11).n)
      let i13 ← pure ((.ok i12) : Except Zig.ErrName (BitVec 32))
      pure (.ret i13))) : Zig.CM Tgt mutexCounterLocals mutexCounterExit).run' { (default : mutexCounterLocals) with c := s0 }
  Zig.free s0
  match e with
  | .ret v => pure v

structure taskLocals where
  deriving Inhabited

inductive taskExit where
  | ret

def task (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
    let _i2 ← Zig.callC (Thread_Mutex_lock i1)
    let i3 ← Zig.callMC (Zig.ptrProject p0 (·.add 20))
    let i4 ← Zig.load (BitVec 32) 4 i3
    let i5 ← Zig.add false i4 (1 : BitVec 32)
    Zig.store (α := BitVec 32) 4 i3 i5
    let i7 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
    let _i8 ← Zig.callC (Thread_Mutex_unlock i7)
    let i9 ← pure p0
    let _i10 ← Zig.callC (Thread_WaitGroup_finish i9)
    pure .ret) : Zig.CM Tgt taskLocals taskExit).run' (default : taskLocals)
  match e with
  | .ret => pure ()

structure waitGroupLocals where
  s : Zig.Ptr
  deriving Inhabited

inductive waitGroupExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def waitGroup  : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s0 ← Zig.allocStack 24 8
  let e ← ((do
    let i0 ← pure (← get).s
    Zig.store (α := Tally) 8 i0 ({ wg := ({ state := ({ raw := (0 : BitVec 64) } : atomic_Value_usize), event := ({ impl := ({ state := ({ raw := (0 : BitVec 32) } : atomic_Value_u32) } : Thread_ResetEvent_FutexImpl) } : Thread_ResetEvent) } : Thread_WaitGroup), m := ({ impl := ({ oul := ({ _os_unfair_lock_opaque := (0 : BitVec 32) } : c_darwin_os_unfair_lock) } : Thread_Mutex_DarwinImpl) } : Thread_Mutex), n := (0 : BitVec 32) } : Tally)
    let i2 ← pure i0
    let _i3 ← Zig.callC (Thread_WaitGroup_startMany i2 (2 : BitVec 64))
    let i4 ← pure (i0)
    let i5 ← Zig.spawnC (Tgt.task i4)
    match i5 with
    | .error _ => (do
      let i7 ← Zig.callRC (Zig.unwrapErr i5)
      let i8 ← pure (i7)
      let i9 ← pure ((.error i8) : Except Zig.ErrName (BitVec 32))
      pure (.ret i9))
    | .ok v6 => (do
      let i11 ← pure (i0)
      let i12 ← Zig.spawnC (Tgt.task i11)
      match i12 with
      | .error _ => (do
        let i14 ← Zig.callRC (Zig.unwrapErr i12)
        let _i15 ← Zig.joinC v6
        let i16 ← pure (i14)
        let i17 ← pure ((.error i16) : Except Zig.ErrName (BitVec 32))
        pure (.ret i17))
      | .ok v13 => (do
        let i19 ← pure i0
        let _i20 ← Zig.callC (Thread_WaitGroup_wait i19)
        let i21 ← Zig.load (Tally) 8 i0
        let i22 ← pure ((i21).n)
        let _i23 ← Zig.joinC v6
        let _i24 ← Zig.joinC v13
        let i25 ← pure ((.ok i22) : Except Zig.ErrName (BitVec 32))
        pure (.ret i25)))) : Zig.CM Tgt waitGroupLocals waitGroupExit).run' { (default : waitGroupLocals) with s := s0 }
  Zig.free s0
  match e with
  | .ret v => pure v

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .producer a => discard (producer a)
  | .work a => discard (work a)
  | .task a => discard (task a)

end Threadsync