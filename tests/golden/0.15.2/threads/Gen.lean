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

inductive Phase where
  | idle
  | busy
  | done
  deriving Repr, Inhabited, DecidableEq

def Phase.toBits : Phase → BitVec 32
  | .idle => (0 : BitVec 32)
  | .busy => (1 : BitVec 32)
  | .done => (2 : BitVec 32)

def Phase.ofInt? (v : Int) : Option Phase :=
  if v = 0 then Option.some .idle else if v = 1 then Option.some .busy else if v = 2 then Option.some .done else Option.none

def Phase.isNamed (_ : Phase) : Bool := true

instance : Zig.Packed Phase 32 where
  toBits := Phase.toBits
  ofBits b := (Phase.ofInt? (Zig.val false b)).getD default
  valid b := (Phase.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc Phase where
  size := 4
  align := 4
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 32 ← Zig.Enc.decode bs
    match Phase.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

structure CounterCtx where
  counter : Zig.Ptr
  n : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc CounterCtx where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.counter), (8, Zig.Enc.encode v.n)]
  decode bs := do pure { counter := ← Zig.Enc.decodeAt bs 0, n := ← Zig.Enc.decodeAt bs 8 }

structure ClaimCtx where
  phase : Zig.Ptr
  wins : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc ClaimCtx where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.phase), (8, Zig.Enc.encode v.wins)]
  decode bs := do pure { phase := ← Zig.Enc.decodeAt bs 0, wins := ← Zig.Enc.decodeAt bs 8 }

structure atomic_Value_u32 where
  raw : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc atomic_Value_u32 where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.raw)]
  decode bs := do pure { raw := ← Zig.Enc.decodeAt bs 0 }

structure atomic_Value_threads_Phase where
  raw : Phase
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc atomic_Value_threads_Phase where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.raw)]
  decode bs := do pure { raw := ← Zig.Enc.decodeAt bs 0 }

structure Thread_SpawnConfig where
  stack_size : BitVec 64
  allocator : Option (Zig.Allocator)
  deriving Repr, Inhabited, DecidableEq

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

/-- The spawn targets of the program. -/
inductive Tgt where
  | claim (a : Zig.Ptr)
  | writeFlag (a : Zig.Ptr)
  | bump (a : Zig.Ptr)
  | swapFlag (a : Zig.Ptr)

structure atomic_Value_threads_Phase_initLocals where
  local1 : atomic_Value_threads_Phase
  deriving Inhabited

inductive atomic_Value_threads_Phase_initExit where
  | ret (v : atomic_Value_threads_Phase)

def atomic_Value_threads_Phase_init (p0 : Phase) : Zig.Result (atomic_Value_threads_Phase) := do
  let e ← ((do
    modify (fun s => { s with local1 := { s.local1 with raw := p0 } })
    pure (.ret (← get).local1)) : Zig.M atomic_Value_threads_Phase_initLocals atomic_Value_threads_Phase_initExit).run' (default : atomic_Value_threads_Phase_initLocals)
  match e with
  | .ret v => pure v

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

def bump.loop4 (p0 : Zig.Ptr) : Zig.CM Tgt bumpLocals bumpExit := do
  match ← ((do
    let i6 ← pure ((← get).i)
    let i7 ← Zig.callMC (Zig.ptrProject p0 (·.add 8))
    let i8 ← Zig.load (BitVec 32) 4 i7
    let i9 ← pure (Zig.lt false i6 i8)
    if i9 then (do
      let i11 ← pure p0
      let i12 ← Zig.load (Zig.Ptr) 8 i11
      match ← ((do
        let i14 ← pure i12
        let i15 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.seqCst 4 i14 (1 : BitVec 32)
        pure (.br13 i15)) : Zig.CM Tgt bumpLocals bumpExit) with
      | .br13 _v13 => (do
        let i17 ← pure ((← get).i)
        let i18 ← Zig.add false i17 (1 : BitVec 32)
        modify (fun s => { s with i := i18 })
        pure .br5)
      | e => pure e)
    else (do
      pure .br3)) : Zig.CM Tgt bumpLocals bumpExit) with
  | .br5 => (do
    pure .rep4)
  | e => pure e

def bump (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (bump.loop4 p0) bump.again4) : Zig.CM Tgt bumpLocals bumpExit) with
    | .br3 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt bumpLocals bumpExit).run' (default : bumpLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure claimLocals where
  deriving Inhabited

inductive claimExit where
  | ret
  | br4 (v : Option (Phase))
  | br12 (v : BitVec 32)
  | br1

def claim (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure p0
      let i3 ← Zig.load (Zig.Ptr) 8 i2
      match ← ((do
        let i5 ← pure i3
        let i6 ← Zig.cmpxchgAsC Zig.AtomicOrder.acqRel Zig.AtomicOrder.acquire 4 i5 Phase.idle Phase.busy
        pure (.br4 i6)) : Zig.CM Tgt claimLocals claimExit) with
      | .br4 v4 => (do
        let i8 ← pure ((v4).isNone)
        if i8 then (do
          let i10 ← Zig.callMC (Zig.ptrProject p0 (·.add 8))
          let i11 ← Zig.load (Zig.Ptr) 8 i10
          match ← ((do
            let i13 ← pure i11
            let i14 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.relaxed 4 i13 (1 : BitVec 32)
            pure (.br12 i14)) : Zig.CM Tgt claimLocals claimExit) with
          | .br12 _v12 => (do
            pure .br1)
          | e => pure e)
        else (do
          pure .br1))
      | e => pure e) : Zig.CM Tgt claimLocals claimExit) with
    | .br1 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt claimLocals claimExit).run' (default : claimLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure claimOnceLocals where
  phase : Zig.Ptr
  wins : Zig.Ptr
  ctx : Zig.Ptr
  deriving Inhabited

inductive claimOnceExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br29 (v : BitVec 32)
  | br34 (v : Phase)

def claimOnce  : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s0 ← Zig.allocStack 4 4
  let s3 ← Zig.allocStack 4 4
  let s6 ← Zig.allocStack 16 8
  let e ← ((do
    let i0 ← pure (← get).phase
    let i1 ← Zig.callRC (atomic_Value_threads_Phase_init Phase.idle)
    Zig.store (α := atomic_Value_threads_Phase) 4 i0 i1
    let i3 ← pure (← get).wins
    let i4 ← Zig.callRC (atomic_Value_u32_init (0 : BitVec 32))
    Zig.store (α := atomic_Value_u32) 4 i3 i4
    let i6 ← pure (← get).ctx
    let i7 ← pure i6
    Zig.store (α := Zig.Ptr) 8 i7 i0
    let i9 ← Zig.callMC (Zig.ptrProject i6 (·.add 8))
    Zig.store (α := Zig.Ptr) 8 i9 i3
    let i11 ← pure (i6)
    let i12 ← Zig.spawnC (Tgt.claim i11)
    match i12 with
    | .error _ => (do
      let i14 ← Zig.callRC (Zig.unwrapErr i12)
      let i15 ← pure (i14)
      let i16 ← pure ((.error i15) : Except Zig.ErrName (BitVec 32))
      pure (.ret i16))
    | .ok v13 => (do
      let i18 ← pure (i6)
      let i19 ← Zig.spawnC (Tgt.claim i18)
      match i19 with
      | .error _ => (do
        let i21 ← Zig.callRC (Zig.unwrapErr i19)
        let _i22 ← Zig.joinC v13
        let i23 ← pure (i21)
        let i24 ← pure ((.error i23) : Except Zig.ErrName (BitVec 32))
        pure (.ret i24))
      | .ok v20 => (do
        let _i26 ← Zig.joinC v13
        let _i27 ← Zig.joinC v20
        let i28 ← pure (i3)
        match ← ((do
          let i30 ← pure i28
          let i31 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.seqCst 4 i30
          pure (.br29 i31)) : Zig.CM Tgt claimOnceLocals claimOnceExit) with
        | .br29 v29 => (do
          let i33 ← pure (i0)
          match ← ((do
            let i35 ← pure i33
            let i36 ← Zig.atomicLoadAsC (Phase) Zig.AtomicOrder.seqCst 4 i35
            pure (.br34 i36)) : Zig.CM Tgt claimOnceLocals claimOnceExit) with
          | .br34 v34 => (do
            let i38 ← pure (Phase.toBits v34)
            let i39 ← Zig.add false v29 i38
            let i40 ← pure ((.ok i39) : Except Zig.ErrName (BitVec 32))
            pure (.ret i40))
          | e => pure e)
        | e => pure e))) : Zig.CM Tgt claimOnceLocals claimOnceExit).run' { (default : claimOnceLocals) with phase := s0, wins := s3, ctx := s6 }
  Zig.free s0
  Zig.free s3
  Zig.free s6
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure writeFlagLocals where
  deriving Inhabited

inductive writeFlagExit where
  | ret

def writeFlag (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let i2 ← Zig.load (Zig.Ptr) 8 i1
    let i3 ← Zig.callM (Zig.ptrProject p0 (·.add 8))
    let i4 ← Zig.load (BitVec 32) 4 i3
    Zig.store (α := BitVec 32) 4 i2 i4
    pure .ret) : Zig.MM writeFlagLocals writeFlagExit).run' (default : writeFlagLocals)
  match e with
  | .ret => pure ()

structure disjointLocals where
  x : Zig.Ptr
  y : Zig.Ptr
  c1 : Zig.Ptr
  c2 : Zig.Ptr
  deriving Inhabited

inductive disjointExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def disjoint (p0 : BitVec 32) (p1 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s2 ← Zig.allocStack 4 4
  let s4 ← Zig.allocStack 4 4
  let s6 ← Zig.allocStack 16 8
  let s11 ← Zig.allocStack 16 8
  let e ← ((do
    let i2 ← pure (← get).x
    Zig.store (α := BitVec 32) 4 i2 (0 : BitVec 32)
    let i4 ← pure (← get).y
    Zig.store (α := BitVec 32) 4 i4 (0 : BitVec 32)
    let i6 ← pure (← get).c1
    let i7 ← pure i6
    Zig.store (α := Zig.Ptr) 8 i7 i2
    let i9 ← Zig.callMC (Zig.ptrProject i6 (·.add 8))
    Zig.store (α := BitVec 32) 4 i9 p0
    let i11 ← pure (← get).c2
    let i12 ← pure i11
    Zig.store (α := Zig.Ptr) 8 i12 i4
    let i14 ← Zig.callMC (Zig.ptrProject i11 (·.add 8))
    Zig.store (α := BitVec 32) 4 i14 p1
    let i16 ← pure (i6)
    let i17 ← Zig.spawnC (Tgt.writeFlag i16)
    match i17 with
    | .error _ => (do
      let i19 ← Zig.callRC (Zig.unwrapErr i17)
      let i20 ← pure (i19)
      let i21 ← pure ((.error i20) : Except Zig.ErrName (BitVec 32))
      pure (.ret i21))
    | .ok v18 => (do
      let i23 ← pure (i11)
      let i24 ← Zig.spawnC (Tgt.writeFlag i23)
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
        let i33 ← Zig.load (BitVec 32) 4 i2
        let i34 ← Zig.load (BitVec 32) 4 i4
        let i35 ← pure (Zig.addWrap i33 i34)
        let i36 ← pure ((.ok i35) : Except Zig.ErrName (BitVec 32))
        pure (.ret i36)))) : Zig.CM Tgt disjointLocals disjointExit).run' { (default : disjointLocals) with x := s2, y := s4, c1 := s6, c2 := s11 }
  Zig.free s2
  Zig.free s4
  Zig.free s6
  Zig.free s11
  match e with
  | .ret v => pure v

structure parallelCounterLocals where
  counter : Zig.Ptr
  ctxs : Zig.Ptr
  local6 : BitVec 64
  handles : Zig.Ptr
  started : BitVec 64
  local29 : BitVec 64
  local44 : BitVec 64
  local85 : BitVec 64
  deriving Inhabited

inductive parallelCounterExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br11
  | br8
  | br51
  | br61
  | br58
  | br34
  | br31
  | br90
  | br87
  | br102 (v : BitVec 32)
  | rep9
  | rep59
  | rep32
  | rep88

def parallelCounter.again88 : parallelCounterExit → Bool
  | .rep88 => true
  | _ => false

def parallelCounter.again59 : parallelCounterExit → Bool
  | .rep59 => true
  | _ => false

def parallelCounter.again32 : parallelCounterExit → Bool
  | .rep32 => true
  | _ => false

def parallelCounter.again9 : parallelCounterExit → Bool
  | .rep9 => true
  | _ => false

def parallelCounter.loop88 (i25 : Zig.Ptr) : Zig.CM Tgt parallelCounterLocals parallelCounterExit := do
  let i89 ← pure ((← get).local85)
  match ← ((do
    let i91 ← pure (i89)
    let i92 ← pure (Zig.lt false i91 (4 : BitVec 64))
    if i92 then (do
      let i94 ← Zig.callMC (Zig.load (Zig.ThreadId) 8 (i25.elem 8 i89))
      let _i95 ← Zig.joinC i94
      pure .br90)
    else (do
      pure .br87)) : Zig.CM Tgt parallelCounterLocals parallelCounterExit) with
  | .br90 => (do
    let i98 ← Zig.add false i89 (1 : BitVec 64)
    modify (fun s => { s with local85 := i98 })
    pure .rep88)
  | e => pure e

def parallelCounter.loop59 (i56 : Zig.Slice) (i57 : BitVec 64) : Zig.CM Tgt parallelCounterLocals parallelCounterExit := do
  let i60 ← pure ((← get).local44)
  match ← ((do
    let i62 ← pure (i60)
    let i63 ← pure (i57)
    let i64 ← pure (Zig.lt false i62 i63)
    if i64 then (do
      let i66 ← Zig.callMC (Zig.checkIndex i56 i60 >>= fun _ => Zig.load (Zig.ThreadId) 8 (i56.ptr.elem 8 i60))
      let _i67 ← Zig.joinC i66
      pure .br61)
    else (do
      pure .br58)) : Zig.CM Tgt parallelCounterLocals parallelCounterExit) with
  | .br61 => (do
    let i70 ← Zig.add false i60 (1 : BitVec 64)
    modify (fun s => { s with local44 := i70 })
    pure .rep59)
  | e => pure e

def parallelCounter.loop32 (i4 : Zig.Ptr) (i25 : Zig.Ptr) : Zig.CM Tgt parallelCounterLocals parallelCounterExit := do
  let i33 ← pure ((← get).local29)
  match ← ((do
    let i35 ← pure (i33)
    let i36 ← pure (Zig.lt false i35 (4 : BitVec 64))
    if i36 then (do
      let i38 ← Zig.callMC (Zig.ptrProject i25 (·.elem 8 i33))
      let i39 ← Zig.callMC (Zig.ptrProject i4 (·.elem 16 i33))
      let i40 ← pure (i39)
      let i41 ← Zig.spawnC (Tgt.bump i40)
      match i41 with
      | .error _ => (do
        let i43 ← Zig.callRC (Zig.unwrapErr i41)
        modify (fun s => { s with local44 := (0 : BitVec 64) })
        let i46 ← pure ((← get).started)
        let i47 ← pure (i25)
        let i48 ← pure i47
        let i49 ← Zig.sub false i46 (0 : BitVec 64)
        let i50 ← pure (Zig.le false i46 (4 : BitVec 64))
        match ← ((do
          if i50 then (do
            pure .br51)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt parallelCounterLocals parallelCounterExit) with
        | .br51 => (do
          let i56 ← Zig.callMC (Zig.checkSliceEnd (4 : BitVec 64) (0 : BitVec 64) i49 0 >>= fun _ => pure (⟨i48, i49⟩ : Zig.Slice))
          let i57 ← pure i56.len
          match ← ((do
            Zig.loop (parallelCounter.loop59 i56 i57) parallelCounter.again59) : Zig.CM Tgt parallelCounterLocals parallelCounterExit) with
          | .br58 => (do
            let i73 ← pure (i43)
            let i74 ← pure ((.error i73) : Except Zig.ErrName (BitVec 32))
            pure (.ret i74))
          | e => pure e)
        | e => pure e)
      | .ok v42 => (do
        Zig.store (α := Zig.ThreadId) 8 i38 v42
        let i77 ← pure ((← get).started)
        let i78 ← Zig.add false i77 (1 : BitVec 64)
        modify (fun s => { s with started := i78 })
        pure .br34))
    else (do
      pure .br31)) : Zig.CM Tgt parallelCounterLocals parallelCounterExit) with
  | .br34 => (do
    let i82 ← Zig.add false i33 (1 : BitVec 64)
    modify (fun s => { s with local29 := i82 })
    pure .rep32)
  | e => pure e

def parallelCounter.loop9 (p0 : BitVec 32) (i1 : Zig.Ptr) (i4 : Zig.Ptr) : Zig.CM Tgt parallelCounterLocals parallelCounterExit := do
  let i10 ← pure ((← get).local6)
  match ← ((do
    let i12 ← pure (i10)
    let i13 ← pure (Zig.lt false i12 (4 : BitVec 64))
    if i13 then (do
      let i15 ← Zig.callMC (Zig.ptrProject i4 (·.elem 16 i10))
      let i16 ← pure i15
      Zig.store (α := Zig.Ptr) 8 i16 i1
      let i18 ← Zig.callMC (Zig.ptrProject i15 (·.add 8))
      Zig.store (α := BitVec 32) 4 i18 p0
      pure .br11)
    else (do
      pure .br8)) : Zig.CM Tgt parallelCounterLocals parallelCounterExit) with
  | .br11 => (do
    let i22 ← Zig.add false i10 (1 : BitVec 64)
    modify (fun s => { s with local6 := i22 })
    pure .rep9)
  | e => pure e

def parallelCounter (p0 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s4 ← Zig.allocStack 64 8
  let s1 ← Zig.allocStack 4 4
  let s25 ← Zig.allocStack 32 8
  let e ← ((do
    let i1 ← pure (← get).counter
    let i2 ← Zig.callRC (atomic_Value_u32_init (0 : BitVec 32))
    Zig.store (α := atomic_Value_u32) 4 i1 i2
    let i4 ← pure (← get).ctxs
    Zig.storeUndef (Vector (CounterCtx) 4) 8 i4
    modify (fun s => { s with local6 := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (parallelCounter.loop9 p0 i1 i4) parallelCounter.again9) : Zig.CM Tgt parallelCounterLocals parallelCounterExit) with
    | .br8 => (do
      let i25 ← pure (← get).handles
      Zig.storeUndef (Vector (Zig.ThreadId) 4) 8 i25
      modify (fun s => { s with started := (0 : BitVec 64) })
      modify (fun s => { s with local29 := (0 : BitVec 64) })
      match ← ((do
        Zig.loop (parallelCounter.loop32 i4 i25) parallelCounter.again32) : Zig.CM Tgt parallelCounterLocals parallelCounterExit) with
      | .br31 => (do
        modify (fun s => { s with local85 := (0 : BitVec 64) })
        match ← ((do
          Zig.loop (parallelCounter.loop88 i25) parallelCounter.again88) : Zig.CM Tgt parallelCounterLocals parallelCounterExit) with
        | .br87 => (do
          let i101 ← pure (i1)
          match ← ((do
            let i103 ← pure i101
            let i104 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.seqCst 4 i103
            pure (.br102 i104)) : Zig.CM Tgt parallelCounterLocals parallelCounterExit) with
          | .br102 v102 => (do
            let i106 ← pure ((.ok v102) : Except Zig.ErrName (BitVec 32))
            pure (.ret i106))
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt parallelCounterLocals parallelCounterExit).run' { (default : parallelCounterLocals) with ctxs := s4, counter := s1, handles := s25 }
  Zig.free s4
  Zig.free s1
  Zig.free s25
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure raceLocals where
  flag : Zig.Ptr
  c1 : Zig.Ptr
  c2 : Zig.Ptr
  deriving Inhabited

inductive raceExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def race (p0 : BitVec 32) (p1 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s2 ← Zig.allocStack 4 4
  let s4 ← Zig.allocStack 16 8
  let s9 ← Zig.allocStack 16 8
  let e ← ((do
    let i2 ← pure (← get).flag
    Zig.store (α := BitVec 32) 4 i2 (0 : BitVec 32)
    let i4 ← pure (← get).c1
    let i5 ← pure i4
    Zig.store (α := Zig.Ptr) 8 i5 i2
    let i7 ← Zig.callMC (Zig.ptrProject i4 (·.add 8))
    Zig.store (α := BitVec 32) 4 i7 p0
    let i9 ← pure (← get).c2
    let i10 ← pure i9
    Zig.store (α := Zig.Ptr) 8 i10 i2
    let i12 ← Zig.callMC (Zig.ptrProject i9 (·.add 8))
    Zig.store (α := BitVec 32) 4 i12 p1
    let i14 ← pure (i4)
    let i15 ← Zig.spawnC (Tgt.writeFlag i14)
    match i15 with
    | .error _ => (do
      let i17 ← Zig.callRC (Zig.unwrapErr i15)
      let i18 ← pure (i17)
      let i19 ← pure ((.error i18) : Except Zig.ErrName (BitVec 32))
      pure (.ret i19))
    | .ok v16 => (do
      let i21 ← pure (i9)
      let i22 ← Zig.spawnC (Tgt.writeFlag i21)
      match i22 with
      | .error _ => (do
        let i24 ← Zig.callRC (Zig.unwrapErr i22)
        let _i25 ← Zig.joinC v16
        let i26 ← pure (i24)
        let i27 ← pure ((.error i26) : Except Zig.ErrName (BitVec 32))
        pure (.ret i27))
      | .ok v23 => (do
        let _i29 ← Zig.joinC v16
        let _i30 ← Zig.joinC v23
        let i31 ← Zig.load (BitVec 32) 4 i2
        let i32 ← pure ((.ok i31) : Except Zig.ErrName (BitVec 32))
        pure (.ret i32)))) : Zig.CM Tgt raceLocals raceExit).run' { (default : raceLocals) with flag := s2, c1 := s4, c2 := s9 }
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

def swapFlag (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let i2 ← Zig.load (Zig.Ptr) 8 i1
    let i3 ← Zig.callMC (Zig.ptrProject p0 (·.add 8))
    let i4 ← Zig.load (BitVec 32) 4 i3
    match ← ((do
      let i6 ← pure i2
      let i7 ← Zig.atomicRmwC Zig.RmwOp.xchg false Zig.AtomicOrder.seqCst 4 i6 i4
      pure (.br5 i7)) : Zig.CM Tgt swapFlagLocals swapFlagExit) with
    | .br5 _v5 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt swapFlagLocals swapFlagExit).run' (default : swapFlagLocals)
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
  | br33 (v : BitVec 32)

def xchgRace (p0 : BitVec 32) (p1 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s2 ← Zig.allocStack 4 4
  let s5 ← Zig.allocStack 16 8
  let s10 ← Zig.allocStack 16 8
  let e ← ((do
    let i2 ← pure (← get).flag
    let i3 ← Zig.callRC (atomic_Value_u32_init (0 : BitVec 32))
    Zig.store (α := atomic_Value_u32) 4 i2 i3
    let i5 ← pure (← get).c1
    let i6 ← pure i5
    Zig.store (α := Zig.Ptr) 8 i6 i2
    let i8 ← Zig.callMC (Zig.ptrProject i5 (·.add 8))
    Zig.store (α := BitVec 32) 4 i8 p0
    let i10 ← pure (← get).c2
    let i11 ← pure i10
    Zig.store (α := Zig.Ptr) 8 i11 i2
    let i13 ← Zig.callMC (Zig.ptrProject i10 (·.add 8))
    Zig.store (α := BitVec 32) 4 i13 p1
    let i15 ← pure (i5)
    let i16 ← Zig.spawnC (Tgt.swapFlag i15)
    match i16 with
    | .error _ => (do
      let i18 ← Zig.callRC (Zig.unwrapErr i16)
      let i19 ← pure (i18)
      let i20 ← pure ((.error i19) : Except Zig.ErrName (BitVec 32))
      pure (.ret i20))
    | .ok v17 => (do
      let i22 ← pure (i10)
      let i23 ← Zig.spawnC (Tgt.swapFlag i22)
      match i23 with
      | .error _ => (do
        let i25 ← Zig.callRC (Zig.unwrapErr i23)
        let _i26 ← Zig.joinC v17
        let i27 ← pure (i25)
        let i28 ← pure ((.error i27) : Except Zig.ErrName (BitVec 32))
        pure (.ret i28))
      | .ok v24 => (do
        let _i30 ← Zig.joinC v17
        let _i31 ← Zig.joinC v24
        let i32 ← pure (i2)
        match ← ((do
          let i34 ← pure i32
          let i35 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.seqCst 4 i34
          pure (.br33 i35)) : Zig.CM Tgt xchgRaceLocals xchgRaceExit) with
        | .br33 v33 => (do
          let i37 ← pure ((.ok v33) : Except Zig.ErrName (BitVec 32))
          pure (.ret i37))
        | e => pure e))) : Zig.CM Tgt xchgRaceLocals xchgRaceExit).run' { (default : xchgRaceLocals) with flag := s2, c1 := s5, c2 := s10 }
  Zig.free s2
  Zig.free s5
  Zig.free s10
  match e with
  | .ret v => pure v
  | _ => throw .panic

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .claim a => discard (claim a)
  | .writeFlag a => discard (Zig.ConcM.liftMem (writeFlag a))
  | .bump a => discard (bump a)
  | .swapFlag a => discard (swapFlag a)

end Threads