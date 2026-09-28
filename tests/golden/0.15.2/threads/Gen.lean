import ZigLean


namespace Threads

structure SwapCtx where
  flag : Zig.Ptr
  val : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc SwapCtx where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.flag), (8, Zig.Enc.encode v.val)]
  decode bs := do pure { flag := ← Zig.Enc.decodeAt bs 0, val := ← Zig.Enc.decodeAt bs 8 }

structure RaceCtx where
  flag : Zig.Ptr
  val : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc RaceCtx where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.flag), (8, Zig.Enc.encode v.val)]
  decode bs := do pure { flag := ← Zig.Enc.decodeAt bs 0, val := ← Zig.Enc.decodeAt bs 8 }

structure mem_Allocator_VTable where
  alloc : Zig.Ptr
  resize : Zig.Ptr
  remap : Zig.Ptr
  free : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

structure Thread_PosixThreadImpl where
  handle : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

structure Thread_SpawnConfig where
  stack_size : BitVec 64
  allocator : Option (Zig.Allocator)
  deriving Repr, Inhabited, DecidableEq

structure CounterCtx where
  counter : Zig.Ptr
  n : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc CounterCtx where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.counter), (8, Zig.Enc.encode v.n)]
  decode bs := do pure { counter := ← Zig.Enc.decodeAt bs 0, n := ← Zig.Enc.decodeAt bs 8 }

inductive builtin_AtomicOrder where
  | unordered
  | monotonic
  | acquire
  | release
  | acq_rel
  | seq_cst
  deriving Repr, Inhabited, DecidableEq

def builtin_AtomicOrder.toBits : builtin_AtomicOrder → BitVec 3
  | .unordered => (0 : BitVec 3)
  | .monotonic => (1 : BitVec 3)
  | .acquire => (2 : BitVec 3)
  | .release => (3 : BitVec 3)
  | .acq_rel => (4 : BitVec 3)
  | .seq_cst => (5 : BitVec 3)

def builtin_AtomicOrder.ofInt? (v : Int) : Option builtin_AtomicOrder :=
  if v = 0 then some .unordered else if v = 1 then some .monotonic else if v = 2 then some .acquire else if v = 3 then some .release else if v = 4 then some .acq_rel else if v = 5 then some .seq_cst else none

def builtin_AtomicOrder.isNamed (_ : builtin_AtomicOrder) : Bool := true

structure atomic_Value_u32 where
  raw : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc atomic_Value_u32 where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.raw)]
  decode bs := do pure { raw := ← Zig.Enc.decodeAt bs 0 }

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

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

structure bumpLocals where
  i : BitVec 32
  deriving Inhabited

inductive bumpExit where
  | ret
  | br13 (v : BitVec 32)
  | br5
  | br3
  | rep4

def bump.again4 : bumpExit → Bool
  | .rep4 => true
  | _ => false

def bump.loop4 (p0 : Zig.Ptr) : Zig.MM bumpLocals bumpExit := do
  match ← ((do
    let i6 ← pure ((← get).i)
    let i7 ← pure (p0.add 8)
    let i8 ← Zig.load (BitVec 32) 4 i7
    let i9 ← pure (Zig.lt false i6 i8)
    if i9 then (do
      let i11 ← pure (p0.add 0)
      let i12 ← Zig.load (Zig.Ptr) 8 i11
      match ← ((do
        let i14 ← pure (i12.add 0)
        let i15 ← Zig.atomicRmw Zig.RmwOp.add false 4 i14 (1 : BitVec 32) (Zig.RmwOp.group Zig.RmwOp.add true)
        pure (.br13 i15)) : Zig.MM bumpLocals bumpExit) with
      | .br13 v13 => (do
        let i17 ← pure ((← get).i)
        let i18 ← Zig.add false i17 (1 : BitVec 32)
        modify (fun s => { s with i := i18 })
        pure .br5)
      | e => pure e)
    else (do
      pure .br3)) : Zig.MM bumpLocals bumpExit) with
  | .br5 => (do
    pure .rep4)
  | e => pure e

def bump (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (bump.loop4 p0) bump.again4) : Zig.MM bumpLocals bumpExit) with
    | .br3 => (do
      pure .ret)
    | e => pure e) : Zig.MM bumpLocals bumpExit).run' (default : bumpLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure parallelCounterLocals where
  counter : Zig.Ptr
  ctxs : Zig.Ptr
  local6 : BitVec 64
  handles : Zig.Ptr
  local27 : BitVec 64
  local51 : BitVec 64
  deriving Inhabited

inductive parallelCounterExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br11
  | br8
  | br32
  | br29
  | br56
  | br53
  | br68 (v : BitVec 32)
  | rep9
  | rep30
  | rep54

def parallelCounter.again54 : parallelCounterExit → Bool
  | .rep54 => true
  | _ => false

def parallelCounter.again30 : parallelCounterExit → Bool
  | .rep30 => true
  | _ => false

def parallelCounter.again9 : parallelCounterExit → Bool
  | .rep9 => true
  | _ => false

def parallelCounter.loop54 (i25 : Zig.Ptr) : Zig.MM parallelCounterLocals parallelCounterExit := do
  let i55 ← pure ((← get).local51)
  match ← ((do
    let i57 ← pure (i55)
    let i58 ← pure (Zig.lt false i57 (4 : BitVec 64))
    if i58 then (do
      let i60 ← Zig.callM (Zig.load (Zig.ThreadId) 8 (i25.elem 8 i55))
      let _i61 ← Zig.callM (Zig.Thread.join i60)
      pure .br56)
    else (do
      pure .br53)) : Zig.MM parallelCounterLocals parallelCounterExit) with
  | .br56 => (do
    let i64 ← Zig.add false i55 (1 : BitVec 64)
    modify (fun s => { s with local51 := i64 })
    pure .rep54)
  | e => pure e

def parallelCounter.loop30 (i4 : Zig.Ptr) (i25 : Zig.Ptr) : Zig.MM parallelCounterLocals parallelCounterExit := do
  let i31 ← pure ((← get).local27)
  match ← ((do
    let i33 ← pure (i31)
    let i34 ← pure (Zig.lt false i33 (4 : BitVec 64))
    if i34 then (do
      let i36 ← pure (i25.elem 8 i31)
      let i37 ← pure (i4.elem 16 i31)
      let i38 ← pure (i37)
      let i39 ← Zig.callM (Zig.Thread.spawn (bump i38))
      match i39 with
      | .error _ => (do
        let i41 ← Zig.callR (Zig.unwrapErr i39)
        let i42 ← pure (i41)
        let i43 ← pure ((.error i42) : Except Zig.ErrName (BitVec 32))
        pure (.ret i43))
      | .ok v40 => (do
        Zig.store (α := Zig.ThreadId) 8 i36 v40
        pure .br32))
    else (do
      pure .br29)) : Zig.MM parallelCounterLocals parallelCounterExit) with
  | .br32 => (do
    let i48 ← Zig.add false i31 (1 : BitVec 64)
    modify (fun s => { s with local27 := i48 })
    pure .rep30)
  | e => pure e

def parallelCounter.loop9 (p0 : BitVec 32) (i1 : Zig.Ptr) (i4 : Zig.Ptr) : Zig.MM parallelCounterLocals parallelCounterExit := do
  let i10 ← pure ((← get).local6)
  match ← ((do
    let i12 ← pure (i10)
    let i13 ← pure (Zig.lt false i12 (4 : BitVec 64))
    if i13 then (do
      let i15 ← pure (i4.elem 16 i10)
      let i16 ← pure (i15.add 0)
      Zig.store (α := Zig.Ptr) 8 i16 i1
      let i18 ← pure (i15.add 8)
      Zig.store (α := BitVec 32) 4 i18 p0
      pure .br11)
    else (do
      pure .br8)) : Zig.MM parallelCounterLocals parallelCounterExit) with
  | .br11 => (do
    let i22 ← Zig.add false i10 (1 : BitVec 64)
    modify (fun s => { s with local6 := i22 })
    pure .rep9)
  | e => pure e

def parallelCounter (p0 : BitVec 32) : Zig.MemM (Except Zig.ErrName (BitVec 32)) := do
  let s4 ← Zig.allocStack 64 8
  let s1 ← Zig.allocStack 4 4
  let s25 ← Zig.allocStack 32 8
  let e ← ((do
    let i1 ← pure (← get).counter
    let i2 ← Zig.callR (atomic_Value_u32_init (0 : BitVec 32))
    Zig.store (α := atomic_Value_u32) 4 i1 i2
    let i4 ← pure (← get).ctxs
    Zig.storeUndef (Vector (CounterCtx) 4) 8 i4
    modify (fun s => { s with local6 := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (parallelCounter.loop9 p0 i1 i4) parallelCounter.again9) : Zig.MM parallelCounterLocals parallelCounterExit) with
    | .br8 => (do
      let i25 ← pure (← get).handles
      Zig.storeUndef (Vector (Zig.ThreadId) 4) 8 i25
      modify (fun s => { s with local27 := (0 : BitVec 64) })
      match ← ((do
        Zig.loop (parallelCounter.loop30 i4 i25) parallelCounter.again30) : Zig.MM parallelCounterLocals parallelCounterExit) with
      | .br29 => (do
        modify (fun s => { s with local51 := (0 : BitVec 64) })
        match ← ((do
          Zig.loop (parallelCounter.loop54 i25) parallelCounter.again54) : Zig.MM parallelCounterLocals parallelCounterExit) with
        | .br53 => (do
          let i67 ← pure (i1)
          match ← ((do
            let i69 ← pure (i67.add 0)
            let i70 ← Zig.atomicLoad (n := 32) 4 i69
            pure (.br68 i70)) : Zig.MM parallelCounterLocals parallelCounterExit) with
          | .br68 v68 => (do
            let i72 ← pure ((.ok v68) : Except Zig.ErrName (BitVec 32))
            pure (.ret i72))
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM parallelCounterLocals parallelCounterExit).run' { (default : parallelCounterLocals) with ctxs := s4, counter := s1, handles := s25 }
  Zig.free s4
  Zig.free s1
  Zig.free s25
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure writeFlagLocals where
  deriving Inhabited

inductive writeFlagExit where
  | ret

def writeFlag (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i1 ← pure (p0.add 0)
    let i2 ← Zig.load (Zig.Ptr) 8 i1
    let i3 ← pure (p0.add 8)
    let i4 ← Zig.load (BitVec 32) 4 i3
    Zig.store (α := BitVec 32) 4 i2 i4
    pure .ret) : Zig.MM writeFlagLocals writeFlagExit).run' (default : writeFlagLocals)
  match e with
  | .ret => pure ()

structure raceLocals where
  flag : Zig.Ptr
  c1 : Zig.Ptr
  c2 : Zig.Ptr
  deriving Inhabited

inductive raceExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def race (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (Except Zig.ErrName (BitVec 32)) := do
  let s2 ← Zig.allocStack 4 4
  let s4 ← Zig.allocStack 16 8
  let s9 ← Zig.allocStack 16 8
  let e ← ((do
    let i2 ← pure (← get).flag
    Zig.store (α := BitVec 32) 4 i2 (0 : BitVec 32)
    let i4 ← pure (← get).c1
    let i5 ← pure (i4.add 0)
    Zig.store (α := Zig.Ptr) 8 i5 i2
    let i7 ← pure (i4.add 8)
    Zig.store (α := BitVec 32) 4 i7 p0
    let i9 ← pure (← get).c2
    let i10 ← pure (i9.add 0)
    Zig.store (α := Zig.Ptr) 8 i10 i2
    let i12 ← pure (i9.add 8)
    Zig.store (α := BitVec 32) 4 i12 p1
    let i14 ← pure (i4)
    let i15 ← Zig.callM (Zig.Thread.spawn (writeFlag i14))
    match i15 with
    | .error _ => (do
      let i17 ← Zig.callR (Zig.unwrapErr i15)
      let i18 ← pure (i17)
      let i19 ← pure ((.error i18) : Except Zig.ErrName (BitVec 32))
      pure (.ret i19))
    | .ok v16 => (do
      let i21 ← pure (i9)
      let i22 ← Zig.callM (Zig.Thread.spawn (writeFlag i21))
      match i22 with
      | .error _ => (do
        let i24 ← Zig.callR (Zig.unwrapErr i22)
        let i25 ← pure (i24)
        let i26 ← pure ((.error i25) : Except Zig.ErrName (BitVec 32))
        pure (.ret i26))
      | .ok v23 => (do
        let _i28 ← Zig.callM (Zig.Thread.join v16)
        let _i29 ← Zig.callM (Zig.Thread.join v23)
        let i30 ← Zig.load (BitVec 32) 4 i2
        let i31 ← pure ((.ok i30) : Except Zig.ErrName (BitVec 32))
        pure (.ret i31)))) : Zig.MM raceLocals raceExit).run' { (default : raceLocals) with flag := s2, c1 := s4, c2 := s9 }
  Zig.free s2
  Zig.free s4
  Zig.free s9
  match e with
  | .ret v => pure v

structure swapFlagLocals where
  deriving Inhabited

inductive swapFlagExit where
  | ret
  | br5 (v : BitVec 32)

def swapFlag (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i1 ← pure (p0.add 0)
    let i2 ← Zig.load (Zig.Ptr) 8 i1
    let i3 ← pure (p0.add 8)
    let i4 ← Zig.load (BitVec 32) 4 i3
    match ← ((do
      let i6 ← pure (i2.add 0)
      let i7 ← Zig.atomicRmw Zig.RmwOp.xchg false 4 i6 i4 (Zig.RmwOp.group Zig.RmwOp.xchg true)
      pure (.br5 i7)) : Zig.MM swapFlagLocals swapFlagExit) with
    | .br5 v5 => (do
      pure .ret)
    | e => pure e) : Zig.MM swapFlagLocals swapFlagExit).run' (default : swapFlagLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure xchgRaceLocals where
  flag : Zig.Ptr
  c1 : Zig.Ptr
  c2 : Zig.Ptr
  deriving Inhabited

inductive xchgRaceExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br32 (v : BitVec 32)

def xchgRace (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (Except Zig.ErrName (BitVec 32)) := do
  let s2 ← Zig.allocStack 4 4
  let s5 ← Zig.allocStack 16 8
  let s10 ← Zig.allocStack 16 8
  let e ← ((do
    let i2 ← pure (← get).flag
    let i3 ← Zig.callR (atomic_Value_u32_init (0 : BitVec 32))
    Zig.store (α := atomic_Value_u32) 4 i2 i3
    let i5 ← pure (← get).c1
    let i6 ← pure (i5.add 0)
    Zig.store (α := Zig.Ptr) 8 i6 i2
    let i8 ← pure (i5.add 8)
    Zig.store (α := BitVec 32) 4 i8 p0
    let i10 ← pure (← get).c2
    let i11 ← pure (i10.add 0)
    Zig.store (α := Zig.Ptr) 8 i11 i2
    let i13 ← pure (i10.add 8)
    Zig.store (α := BitVec 32) 4 i13 p1
    let i15 ← pure (i5)
    let i16 ← Zig.callM (Zig.Thread.spawn (swapFlag i15))
    match i16 with
    | .error _ => (do
      let i18 ← Zig.callR (Zig.unwrapErr i16)
      let i19 ← pure (i18)
      let i20 ← pure ((.error i19) : Except Zig.ErrName (BitVec 32))
      pure (.ret i20))
    | .ok v17 => (do
      let i22 ← pure (i10)
      let i23 ← Zig.callM (Zig.Thread.spawn (swapFlag i22))
      match i23 with
      | .error _ => (do
        let i25 ← Zig.callR (Zig.unwrapErr i23)
        let i26 ← pure (i25)
        let i27 ← pure ((.error i26) : Except Zig.ErrName (BitVec 32))
        pure (.ret i27))
      | .ok v24 => (do
        let _i29 ← Zig.callM (Zig.Thread.join v17)
        let _i30 ← Zig.callM (Zig.Thread.join v24)
        let i31 ← pure (i2)
        match ← ((do
          let i33 ← pure (i31.add 0)
          let i34 ← Zig.atomicLoad (n := 32) 4 i33
          pure (.br32 i34)) : Zig.MM xchgRaceLocals xchgRaceExit) with
        | .br32 v32 => (do
          let i36 ← pure ((.ok v32) : Except Zig.ErrName (BitVec 32))
          pure (.ret i36))
        | e => pure e))) : Zig.MM xchgRaceLocals xchgRaceExit).run' { (default : xchgRaceLocals) with flag := s2, c1 := s5, c2 := s10 }
  Zig.free s2
  Zig.free s5
  Zig.free s10
  match e with
  | .ret v => pure v
  | _ => throw .panic

end Threads