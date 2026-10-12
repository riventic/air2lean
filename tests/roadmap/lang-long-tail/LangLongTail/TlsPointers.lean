-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace TlsPointers

structure Node where
  v : BitVec 32
  next : Option (Zig.Ptr)
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Node where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(8, Zig.Enc.encode v.v), (0, Zig.Enc.encode v.next)]
  decode bs := do pure { v := ← Zig.Enc.decodeAt bs 8, next := ← Zig.Enc.decodeAt bs 0 }

structure Thread_SpawnConfig where
  stack_size : BitVec 64
  allocator : Option (Zig.Allocator)
  deriving Repr, Inhabited, DecidableEq

/-- The memory at program start under the placement `σ`: block `k` is global `k`. The main thread's instance of a `threadlocal` global is its block (its TLS key). -/
def mem0 (σ : Zig.Placement) : Zig.Mem := (Zig.Mem.ofGlobals σ [
  -- 0: tls_pointers.current (threadlocal: the main thread's instance)
  (Zig.Enc.encode (none : Option (Zig.Ptr)), 8, .global),
  -- 1: tls_pointers.cursor (threadlocal: the main thread's instance)
  (Zig.Enc.encode ((⟨some 2, 0⟩ : Zig.Ptr) : Zig.Ptr), 8, .global),
  -- 2: tls_pointers.shared
  (Zig.Enc.encode (({ v := (5 : BitVec 32), next := none } : Node) : Node), 8, .global),
  -- 3: tls_pointers.name (threadlocal: the main thread's instance)
  (Zig.Enc.encode ((⟨(⟨some 4, 0⟩ : Zig.Ptr), (4 : BitVec 64)⟩ : Zig.Slice) : Zig.Slice), 8, .global),
  -- 4: a constant
  (Zig.Enc.encode ((#v[(109 : BitVec 8), (97 : BitVec 8), (105 : BitVec 8), (110 : BitVec 8), (0 : BitVec 8)] : Vector (BitVec 8) 5) : Vector (BitVec 8) 5), 1, .constGlobal),
  -- 5: a constant
  (Zig.Enc.encode ((#v[(109 : BitVec 8), (97 : BitVec 8), (105 : BitVec 8), (110 : BitVec 8), (45 : BitVec 8), (116 : BitVec 8), (104 : BitVec 8), (114 : BitVec 8), (101 : BitVec 8), (97 : BitVec 8), (100 : BitVec 8), (0 : BitVec 8)] : Vector (BitVec 8) 12) : Vector (BitVec 8) 12), 1, .constGlobal)]).mainTls #[0, 1, 3]

/-- The `threadlocal` globals: key, initial bytes and alignment. A spawned thread makes its own instance of each from these (`Zig.ConcM.tlsThread`). -/
def tlsInit : List (Zig.BlockId × Array Zig.Byte × Nat) := [
  -- tls_pointers.current
  (0, Zig.Enc.encode (none : Option (Zig.Ptr)), 8),
  -- tls_pointers.cursor
  (1, Zig.Enc.encode ((⟨some 2, 0⟩ : Zig.Ptr) : Zig.Ptr), 8),
  -- tls_pointers.name
  (3, Zig.Enc.encode ((⟨(⟨some 4, 0⟩ : Zig.Ptr), (4 : BitVec 64)⟩ : Zig.Slice) : Zig.Slice), 8)]

/-- The spawn targets of the program. -/
inductive Tgt where
  | leakSlot (a : Zig.Ptr)
  | worker (a : Zig.Ptr)

structure currentValueLocals where
  deriving Inhabited

inductive currentValueExit where
  | ret (v : BitVec 32)
  | br0 (v : Zig.Ptr)

def currentValue  : Zig.MemM (BitVec 32) := do
  let e ← ((do
    match ← ((do
      let i1 ← Zig.tlsPtr 0
      let i2 ← Zig.load (Option (Zig.Ptr)) 8 i1
      let i3 ← pure ((i2).isSome)
      if i3 then (do
        let i5 ← Zig.optPayload i2
        pure (.br0 i5))
      else (do
        pure (.ret (0 : BitVec 32)))) : Zig.MM currentValueLocals currentValueExit) with
    | .br0 v0 => (do
      let i8 ← Zig.callM (Zig.ptrProject v0 (·.add 8))
      let i9 ← Zig.load (BitVec 32) 4 i8
      pure (.ret i9))
    | e => pure e) : Zig.MM currentValueLocals currentValueExit).run' (default : currentValueLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure leakSlotLocals where
  mine : Zig.Ptr
  deriving Inhabited

inductive leakSlotExit where
  | ret

def leakSlot (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let s1 ← Zig.allocStack 16 8
  let e ← ((do
    let i1 ← pure (← get).mine
    let i2 ← Zig.callM (Zig.ptrProject i1 (·.add 8))
    Zig.store (α := BitVec 32) 4 i2 (9 : BitVec 32)
    let i4 ← pure i1
    Zig.store (α := Option (Zig.Ptr)) 8 i4 none
    let i6 ← Zig.tlsPtr 0
    let i7 ← pure (i1)
    Zig.store (α := Option (Zig.Ptr)) 8 i6 i7
    let i9 ← Zig.tlsPtr 0
    let i10 ← pure (i9)
    Zig.store (α := Option (Zig.Ptr)) 8 p0 i10
    pure .ret) : Zig.MM leakSlotLocals leakSlotExit).run' { (default : leakSlotLocals) with mine := s1 }
  Zig.free s1
  match e with
  | .ret => pure ()

structure leakedSlotLocals where
  p : Zig.Ptr
  deriving Inhabited

inductive leakedSlotExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br10 (v : Zig.Ptr)
  | br17 (v : Except Zig.ErrName (BitVec 32))

def leakedSlot  : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s0 ← Zig.allocStack 8 8
  let e ← ((do
    let i0 ← pure (← get).p
    Zig.store (α := Option (Zig.Ptr)) 8 i0 none
    let i2 ← pure (i0)
    let i3 ← Zig.spawnC (Tgt.leakSlot i2)
    match i3 with
    | .error _ => (do
      let i5 ← Zig.callRC (Zig.unwrapErr i3)
      let i6 ← pure (i5)
      let i7 ← pure ((.error i6) : Except Zig.ErrName (BitVec 32))
      pure (.ret i7))
    | .ok v4 => (do
      let _i9 ← Zig.joinC v4
      match ← ((do
        let i11 ← Zig.load (Option (Zig.Ptr)) 8 i0
        let i12 ← pure ((i11).isSome)
        if i12 then (do
          let i14 ← Zig.optPayload i11
          pure (.br10 i14))
        else (do
          pure (.ret (.ok (0 : BitVec 32) : Except Zig.ErrName (BitVec 32))))) : Zig.CM Tgt leakedSlotLocals leakedSlotExit) with
      | .br10 v10 => (do
        match ← ((do
          let i18 ← Zig.load (Option (Zig.Ptr)) 8 v10
          let i19 ← pure ((i18).isSome)
          if i19 then (do
            pure (.br17 (.ok (1 : BitVec 32) : Except Zig.ErrName (BitVec 32))))
          else (do
            pure (.br17 (.ok (2 : BitVec 32) : Except Zig.ErrName (BitVec 32))))) : Zig.CM Tgt leakedSlotLocals leakedSlotExit) with
        | .br17 v17 => (do
          pure (.ret v17))
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt leakedSlotLocals leakedSlotExit).run' { (default : leakedSlotLocals) with p := s0 }
  Zig.free s0
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mainOnlyLocals where
  «local» : Zig.Ptr
  deriving Inhabited

inductive mainOnlyExit where
  | ret (v : BitVec 32)
  | br20

def mainOnly (p0 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s1 ← Zig.allocStack 16 8
  let e ← ((do
    let i1 ← pure (← get).«local»
    let i2 ← Zig.callM (Zig.ptrProject i1 (·.add 8))
    Zig.store (α := BitVec 32) 4 i2 p0
    let i4 ← pure i1
    let i5 ← Zig.tlsPtr 1
    let i6 ← Zig.load (Zig.Ptr) 8 i5
    let i7 ← pure (i6)
    Zig.store (α := Option (Zig.Ptr)) 8 i4 i7
    let i9 ← Zig.callM (currentValue )
    let i10 ← Zig.tlsPtr 0
    let i11 ← pure (i1)
    Zig.store (α := Option (Zig.Ptr)) 8 i10 i11
    let i13 ← Zig.tlsPtr 1
    Zig.store (α := Zig.Ptr) 8 i13 i1
    let i15 ← Zig.callM (currentValue )
    let i16 ← Zig.tlsPtr 1
    let i17 ← Zig.load (Zig.Ptr) 8 i16
    let i18 ← pure i17
    let i19 ← (·.isSome) <$> Zig.load (Option (Zig.Ptr)) 8 i18
    match ← ((do
      if i19 then (do
        pure .br20)
      else (do
        throw .panic)) : Zig.MM mainOnlyLocals mainOnlyExit) with
    | .br20 => (do
      let i25 ← pure i18
      let i26 ← Zig.load (Zig.Ptr) 8 i25
      let i27 ← Zig.callM (Zig.ptrProject i26 (·.add 8))
      let i28 ← Zig.load (BitVec 32) 4 i27
      let i29 ← pure (Zig.addWrap i15 i28)
      let i30 ← Zig.tlsPtr 1
      Zig.store (α := Zig.Ptr) 8 i30 (⟨some 2, 0⟩ : Zig.Ptr)
      let i32 ← Zig.tlsPtr 0
      Zig.store (α := Option (Zig.Ptr)) 8 i32 none
      let i34 ← Zig.tlsPtr 3
      Zig.store (α := Zig.Slice) 8 i34 (⟨(⟨some 5, 0⟩ : Zig.Ptr), (11 : BitVec 64)⟩ : Zig.Slice)
      let i36 ← pure (Zig.addWrap i9 i29)
      let i37 ← Zig.tlsPtr 3
      let i38 ← Zig.callM (Zig.ptrProject i37 (·.add 8))
      let i39 ← Zig.load (BitVec 64) 8 i38
      let i40 ← Zig.intCast false false 32 i39
      let i41 ← pure (Zig.addWrap i36 i40)
      pure (.ret i41))
    | e => pure e) : Zig.MM mainOnlyLocals mainOnlyExit).run' { (default : mainOnlyLocals) with «local» := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure workerLocals where
  mine : Zig.Ptr
  deriving Inhabited

inductive workerExit where
  | ret

def worker (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let s1 ← Zig.allocStack 16 8
  let e ← ((do
    let i1 ← pure (← get).mine
    let i2 ← Zig.callM (Zig.ptrProject i1 (·.add 8))
    Zig.store (α := BitVec 32) 4 i2 (40 : BitVec 32)
    let i4 ← pure i1
    Zig.store (α := Option (Zig.Ptr)) 8 i4 none
    let i6 ← Zig.callM (currentValue )
    let i7 ← Zig.tlsPtr 0
    let i8 ← pure (i1)
    Zig.store (α := Option (Zig.Ptr)) 8 i7 i8
    let i10 ← Zig.mul false i6 (1000 : BitVec 32)
    let i11 ← Zig.callM (currentValue )
    let i12 ← Zig.add false i10 i11
    let i13 ← Zig.tlsPtr 1
    let i14 ← Zig.load (Zig.Ptr) 8 i13
    let i15 ← Zig.callM (Zig.ptrProject i14 (·.add 8))
    let i16 ← Zig.load (BitVec 32) 4 i15
    let i17 ← Zig.add false i12 i16
    let i18 ← Zig.tlsPtr 3
    let i19 ← Zig.callM (Zig.ptrProject i18 (·.add 8))
    let i20 ← Zig.load (BitVec 64) 8 i19
    let i21 ← Zig.intCast false false 32 i20
    let i22 ← Zig.add false i17 i21
    Zig.store (α := BitVec 32) 4 p0 i22
    let i24 ← Zig.tlsPtr 0
    Zig.store (α := Option (Zig.Ptr)) 8 i24 none
    pure .ret) : Zig.MM workerLocals workerExit).run' { (default : workerLocals) with mine := s1 }
  Zig.free s1
  match e with
  | .ret => pure ()

structure perThreadLocals where
  a : Zig.Ptr
  «local» : Zig.Ptr
  deriving Inhabited

inductive perThreadExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def perThread  : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s2 ← Zig.allocStack 16 8
  let s0 ← Zig.allocStack 4 4
  let e ← ((do
    let i0 ← pure (← get).a
    Zig.store (α := BitVec 32) 4 i0 (0 : BitVec 32)
    let i2 ← pure (← get).«local»
    let i3 ← Zig.callMC (Zig.ptrProject i2 (·.add 8))
    Zig.store (α := BitVec 32) 4 i3 (1 : BitVec 32)
    let i5 ← pure i2
    Zig.store (α := Option (Zig.Ptr)) 8 i5 none
    let i7 ← Zig.tlsPtr 0
    let i8 ← pure (i2)
    Zig.store (α := Option (Zig.Ptr)) 8 i7 i8
    let i10 ← pure (i0)
    let i11 ← Zig.spawnC (Tgt.worker i10)
    match i11 with
    | .error _ => (do
      let i13 ← Zig.callRC (Zig.unwrapErr i11)
      let i14 ← pure (i13)
      let i15 ← pure ((.error i14) : Except Zig.ErrName (BitVec 32))
      pure (.ret i15))
    | .ok v12 => (do
      let i17 ← Zig.callMC (currentValue )
      let _i18 ← Zig.joinC v12
      let i19 ← Zig.tlsPtr 0
      Zig.store (α := Option (Zig.Ptr)) 8 i19 none
      let i21 ← Zig.load (BitVec 32) 4 i0
      let i22 ← Zig.mul false i21 (100 : BitVec 32)
      let i23 ← Zig.add false i22 i17
      let i24 ← pure ((.ok i23) : Except Zig.ErrName (BitVec 32))
      pure (.ret i24))) : Zig.CM Tgt perThreadLocals perThreadExit).run' { (default : perThreadLocals) with «local» := s2, a := s0 }
  Zig.free s2
  Zig.free s0
  match e with
  | .ret v => pure v

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .leakSlot a => Zig.ConcM.tlsThread tlsInit (discard (Zig.ConcM.liftMem (leakSlot a)))
  | .worker a => Zig.ConcM.tlsThread tlsInit (discard (Zig.ConcM.liftMem (worker a)))

end TlsPointers