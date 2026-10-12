-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"}}
import ZigLean


namespace Conc

structure atomic_Value_u32 where
  raw : BitVec 32
  deriving Repr, Inhabited, DecidableEq

inductive Io_Threaded_Thread_Status__enum_1 where
  | none
  | parked
  | blocked
  | blocked_alertable
  | canceling
  | canceled
  | blocked_canceling
  | blocked_alertable_canceling
  deriving Repr, Inhabited, DecidableEq

def Io_Threaded_Thread_Status__enum_1.toBits : Io_Threaded_Thread_Status__enum_1 → BitVec 3
  | .none => (0 : BitVec 3)
  | .parked => (1 : BitVec 3)
  | .blocked => (3 : BitVec 3)
  | .blocked_alertable => (2 : BitVec 3)
  | .canceling => (6 : BitVec 3)
  | .canceled => (7 : BitVec 3)
  | .blocked_canceling => (5 : BitVec 3)
  | .blocked_alertable_canceling => (4 : BitVec 3)

def Io_Threaded_Thread_Status__enum_1.ofInt? (v : Int) : Option Io_Threaded_Thread_Status__enum_1 :=
  if v = 0 then Option.some .none else if v = 1 then Option.some .parked else if v = 3 then Option.some .blocked else if v = 2 then Option.some .blocked_alertable else if v = 6 then Option.some .canceling else if v = 7 then Option.some .canceled else if v = 5 then Option.some .blocked_canceling else if v = 4 then Option.some .blocked_alertable_canceling else Option.none

def Io_Threaded_Thread_Status__enum_1.isNamed (_ : Io_Threaded_Thread_Status__enum_1) : Bool := true

instance : Zig.Packed Io_Threaded_Thread_Status__enum_1 3 where
  toBits := Io_Threaded_Thread_Status__enum_1.toBits
  ofBits b := (Io_Threaded_Thread_Status__enum_1.ofInt? (Zig.val false b)).getD default
  valid b := (Io_Threaded_Thread_Status__enum_1.ofInt? (Zig.val false b)).isSome

structure Io_Threaded_AwaitableId where
  bits : BitVec 61
  deriving Repr, Inhabited, DecidableEq

def Io_Threaded_AwaitableId.null : Io_Threaded_AwaitableId := ⟨(0 : BitVec 61)⟩
def Io_Threaded_AwaitableId.all_ones : Io_Threaded_AwaitableId := ⟨(2305843009213693951 : BitVec 61)⟩

def Io_Threaded_AwaitableId.toBits (e : Io_Threaded_AwaitableId) : BitVec 61 := e.bits

def Io_Threaded_AwaitableId.ofInt? (v : Int) : Option Io_Threaded_AwaitableId :=
  if 0 ≤ v ∧ v ≤ 2305843009213693951 then Option.some ⟨BitVec.ofInt 61 v⟩ else Option.none

def Io_Threaded_AwaitableId.isNamed (e : Io_Threaded_AwaitableId) : Bool := e.bits == (0 : BitVec 61) || e.bits == (2305843009213693951 : BitVec 61)

instance : Zig.Packed Io_Threaded_AwaitableId 61 where
  toBits := Io_Threaded_AwaitableId.toBits
  ofBits b := ⟨b⟩

structure Io_Threaded_Thread_Status where
  cancelation : Io_Threaded_Thread_Status__enum_1
  awaitable : Io_Threaded_AwaitableId
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Io_Threaded_Thread_Status 64 where
  toBits v := ((Zig.Packed.toBits v.cancelation).setWidth 64 <<< 0) ||| ((Zig.Packed.toBits v.awaitable).setWidth 64 <<< 3)
  ofBits b := { cancelation := Zig.Packed.get b 0, awaitable := Zig.Packed.get b 3 }
  valid b := Zig.Packed.validAt (Io_Threaded_Thread_Status__enum_1) b 0 && Zig.Packed.validAt (Io_Threaded_AwaitableId) b 3

structure atomic_Value_Io_Threaded_Thread_Status where
  raw : Io_Threaded_Thread_Status
  deriving Repr, Inhabited, DecidableEq

inductive Io_Threaded_Future_Status__enum_1 where
  | pending
  | pending_awaited
  | pending_canceled
  | done
  deriving Repr, Inhabited, DecidableEq

def Io_Threaded_Future_Status__enum_1.toBits : Io_Threaded_Future_Status__enum_1 → BitVec 2
  | .pending => (0 : BitVec 2)
  | .pending_awaited => (1 : BitVec 2)
  | .pending_canceled => (3 : BitVec 2)
  | .done => (2 : BitVec 2)

def Io_Threaded_Future_Status__enum_1.ofInt? (v : Int) : Option Io_Threaded_Future_Status__enum_1 :=
  if v = 0 then Option.some .pending else if v = 1 then Option.some .pending_awaited else if v = 3 then Option.some .pending_canceled else if v = 2 then Option.some .done else Option.none

def Io_Threaded_Future_Status__enum_1.isNamed (_ : Io_Threaded_Future_Status__enum_1) : Bool := true

instance : Zig.Packed Io_Threaded_Future_Status__enum_1 2 where
  toBits := Io_Threaded_Future_Status__enum_1.toBits
  ofBits b := (Io_Threaded_Future_Status__enum_1.ofInt? (Zig.val false b)).getD default
  valid b := (Io_Threaded_Future_Status__enum_1.ofInt? (Zig.val false b)).isSome

structure Io_Threaded_Thread_PackedPtr where
  bits : BitVec 62
  deriving Repr, Inhabited, DecidableEq

def Io_Threaded_Thread_PackedPtr.null : Io_Threaded_Thread_PackedPtr := ⟨(0 : BitVec 62)⟩
def Io_Threaded_Thread_PackedPtr.all_ones : Io_Threaded_Thread_PackedPtr := ⟨(4611686018427387903 : BitVec 62)⟩

def Io_Threaded_Thread_PackedPtr.toBits (e : Io_Threaded_Thread_PackedPtr) : BitVec 62 := e.bits

def Io_Threaded_Thread_PackedPtr.ofInt? (v : Int) : Option Io_Threaded_Thread_PackedPtr :=
  if 0 ≤ v ∧ v ≤ 4611686018427387903 then Option.some ⟨BitVec.ofInt 62 v⟩ else Option.none

def Io_Threaded_Thread_PackedPtr.isNamed (e : Io_Threaded_Thread_PackedPtr) : Bool := e.bits == (0 : BitVec 62) || e.bits == (4611686018427387903 : BitVec 62)

instance : Zig.Packed Io_Threaded_Thread_PackedPtr 62 where
  toBits := Io_Threaded_Thread_PackedPtr.toBits
  ofBits b := ⟨b⟩

structure Io_Threaded_Future_Status where
  tag : Io_Threaded_Future_Status__enum_1
  thread : Io_Threaded_Thread_PackedPtr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Io_Threaded_Future_Status 64 where
  toBits v := ((Zig.Packed.toBits v.tag).setWidth 64 <<< 0) ||| ((Zig.Packed.toBits v.thread).setWidth 64 <<< 2)
  ofBits b := { tag := Zig.Packed.get b 0, thread := Zig.Packed.get b 2 }
  valid b := Zig.Packed.validAt (Io_Threaded_Future_Status__enum_1) b 0 && Zig.Packed.validAt (Io_Threaded_Thread_PackedPtr) b 2

structure atomic_Value_Io_Threaded_Future_Status where
  raw : Io_Threaded_Future_Status
  deriving Repr, Inhabited, DecidableEq

structure Thread_SpawnConfig where
  stack_size : BitVec 64
  allocator : Option (Zig.Allocator)
  deriving Repr, Inhabited, DecidableEq

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: concurrency.w32
  (Zig.Enc.encode ((0 : BitVec 32) : BitVec 32), 4, .global),
  -- 1: concurrency.w64
  (Zig.Enc.encode ((0 : BitVec 64) : BitVec 64), 8, .global),
  -- 2: concurrency.w16
  (Zig.Enc.encode ((0 : BitVec 16) : BitVec 16), 2, .global),
  -- 3: concurrency.wi
  (Zig.Enc.encode ((0 : BitVec 32) : BitVec 32), 4, .global)]

/-- The spawn targets of the program; fields are captured by value. -/
inductive Tgt where
  | adder (a : (Zig.Ptr) × (BitVec 32))

/-- The child protocol obligation for the complete captured tuple. Pointer
identities are copied; a proof must explicitly justify ownership transfer or sharing. -/
abbrev Tgt.spawnInit {γ : Type} (P : Zig.Conc.Proto Tgt γ) (target : Tgt) (ghost : γ) : Prop :=
  P.init target ghost

/-- Each captured field in source order. A value is copied and carries no ownership;
a pointer or slice copies only its identity, so a spawn proof must hand over or share its
region (`Zig.Conc.Capture.grant`). An `other` field's obligation cannot be discharged. -/
def Tgt.captures : Tgt → List Zig.Conc.Capture
  | .adder (capture0, _) => [.ptr capture0, .value]

structure atomic_Value_Io_Threaded_Future_Status_initLocals where
  local1 : atomic_Value_Io_Threaded_Future_Status
  deriving Inhabited

inductive atomic_Value_Io_Threaded_Future_Status_initExit where
  | ret (v : atomic_Value_Io_Threaded_Future_Status)

def atomic_Value_Io_Threaded_Future_Status_init (p0 : Io_Threaded_Future_Status) : Zig.Result (atomic_Value_Io_Threaded_Future_Status) := do
  let e ← ((do
    modify (fun s => { s with local1 := { s.local1 with raw := p0 } })
    pure (.ret (← get).local1)) : Zig.M atomic_Value_Io_Threaded_Future_Status_initLocals atomic_Value_Io_Threaded_Future_Status_initExit).run' (default : atomic_Value_Io_Threaded_Future_Status_initLocals)
  match e with
  | .ret v => pure v

structure atomic_Value_Io_Threaded_Thread_Status_initLocals where
  local1 : atomic_Value_Io_Threaded_Thread_Status
  deriving Inhabited

inductive atomic_Value_Io_Threaded_Thread_Status_initExit where
  | ret (v : atomic_Value_Io_Threaded_Thread_Status)

def atomic_Value_Io_Threaded_Thread_Status_init (p0 : Io_Threaded_Thread_Status) : Zig.Result (atomic_Value_Io_Threaded_Thread_Status) := do
  let e ← ((do
    modify (fun s => { s with local1 := { s.local1 with raw := p0 } })
    pure (.ret (← get).local1)) : Zig.M atomic_Value_Io_Threaded_Thread_Status_initLocals atomic_Value_Io_Threaded_Thread_Status_initExit).run' (default : atomic_Value_Io_Threaded_Thread_Status_initLocals)
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

structure adderLocals where
  i : BitVec 32
  deriving Inhabited

inductive adderExit where
  | ret
  | br6
  | br4
  | rep5

def adder.again5 : adderExit → Bool
  | .rep5 => true
  | _ => false

def adder.loop5 (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.CM Tgt adderLocals adderExit := do
  match ← ((do
    let i7 ← pure ((← get).i)
    let i8 ← pure (Zig.lt false i7 p1)
    if i8 then (do
      let _i10 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.seqCst 4 p0 (257 : BitVec 32)
      let i11 ← pure ((← get).i)
      let i12 ← Zig.add false i11 (1 : BitVec 32)
      modify (fun s => { s with i := i12 })
      pure .br6)
    else (do
      pure .br4)) : Zig.CM Tgt adderLocals adderExit) with
  | .br6 => (do
    pure .rep5)
  | e => pure e

def adder (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (adder.loop5 p0 p1) adder.again5) : Zig.CM Tgt adderLocals adderExit) with
    | .br4 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt adderLocals adderExit).run' (default : adderLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure bytesThenLoadLocals where
  deriving Inhabited

inductive bytesThenLoadExit where
  | ret (v : BitVec 32)

def bytesThenLoad (p0 : BitVec 8) (p1 : BitVec 8) (p2 : BitVec 8) (p3 : BitVec 8) : Zig.ConcM Tgt (BitVec 32) := do
  let e ← ((do
    Zig.store (α := BitVec 8) 1 (⟨some 0, 0⟩ : Zig.Ptr) p0
    Zig.store (α := BitVec 8) 1 (⟨some 0, 1⟩ : Zig.Ptr) p1
    Zig.store (α := BitVec 8) 1 (⟨some 0, 2⟩ : Zig.Ptr) p2
    Zig.store (α := BitVec 8) 1 (⟨some 0, 3⟩ : Zig.Ptr) p3
    let i8 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.seqCst 4 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i8)) : Zig.CM Tgt bytesThenLoadLocals bytesThenLoadExit).run' (default : bytesThenLoadLocals)
  match e with
  | .ret v => pure v

structure casSwapLocals where
  deriving Inhabited

inductive casSwapExit where
  | ret (v : BitVec 64)
  | br4 (v : BitVec 64)

def casSwap (p0 : BitVec 64) (p1 : BitVec 64) : Zig.ConcM Tgt (BitVec 64) := do
  let e ← ((do
    Zig.store (α := BitVec 64) 8 (⟨some 1, 0⟩ : Zig.Ptr) p0
    let i3 ← Zig.cmpxchgC Zig.AtomicOrder.seqCst Zig.AtomicOrder.seqCst 8 (⟨some 1, 0⟩ : Zig.Ptr) p0 p1
    match ← ((do
      let i5 ← pure ((i3).isNone)
      if i5 then (do
        let i7 ← Zig.load (BitVec 64) 8 (⟨some 1, 0⟩ : Zig.Ptr)
        pure (.br4 i7))
      else (do
        pure (.br4 (0 : BitVec 64)))) : Zig.CM Tgt casSwapLocals casSwapExit) with
    | .br4 v4 => (do
      pure (.ret v4))
    | e => pure e) : Zig.CM Tgt casSwapLocals casSwapExit).run' (default : casSwapLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heapWordLocals where
  deriving Inhabited

inductive heapWordExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

-- air2lean-premises: {"ALC-09":[0]}
def heapWord (p0 : Zig.Allocator) (p1 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let e ← ((do
    let i2 ← Zig.callMC (Zig.Allocator.create p0 4 4)
    match i2 with
    | .error _ => (do
      let i4 ← Zig.callRC (Zig.unwrapErr i2)
      let i5 ← pure (i4)
      let i6 ← pure ((.error i5) : Except Zig.ErrName (BitVec 32))
      pure (.ret i6))
    | .ok v3 => (do
      Zig.atomicStoreC Zig.AtomicOrder.seqCst 4 v3 p1
      let i9 ← pure (v3)
      let i10 ← Zig.callMC (Zig.load (BitVec 8) 1 (i9.elem 1 (0 : BitVec 64)))
      let i11 ← Zig.intCast false false 32 i10
      let i12 ← pure (Zig.shl i11 (24 : BitVec 5))
      let i13 ← Zig.callMC (Zig.load (BitVec 8) 1 (i9.elem 1 (3 : BitVec 64)))
      let i14 ← Zig.intCast false false 32 i13
      let i15 ← pure (i12 ||| i14)
      let _i16 ← Zig.callMC (Zig.Allocator.destroy p0 4 v3)
      let i17 ← pure ((.ok i15) : Except Zig.ErrName (BitVec 32))
      pure (.ret i17))) : Zig.CM Tgt heapWordLocals heapWordExit).run' (default : heapWordLocals)
  match e with
  | .ret v => pure v

structure rmwCarryByte0Locals where
  deriving Inhabited

inductive rmwCarryByte0Exit where
  | ret (v : BitVec 8)

def rmwCarryByte0 (p0 : BitVec 16) (p1 : BitVec 16) : Zig.ConcM Tgt (BitVec 8) := do
  let e ← ((do
    Zig.store (α := BitVec 16) 2 (⟨some 2, 0⟩ : Zig.Ptr) p0
    let _i3 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.seqCst 2 (⟨some 2, 0⟩ : Zig.Ptr) p1
    let i4 ← Zig.load (BitVec 8) 1 (⟨some 2, 0⟩ : Zig.Ptr)
    pure (.ret i4)) : Zig.CM Tgt rmwCarryByte0Locals rmwCarryByte0Exit).run' (default : rmwCarryByte0Locals)
  match e with
  | .ret v => pure v

structure rmwMaxLocals where
  deriving Inhabited

inductive rmwMaxExit where
  | ret (v : BitVec 32)

def rmwMax (p0 : BitVec 32) (p1 : BitVec 32) : Zig.ConcM Tgt (BitVec 32) := do
  let e ← ((do
    Zig.store (α := BitVec 32) 4 (⟨some 3, 0⟩ : Zig.Ptr) p0
    let _i3 ← Zig.atomicRmwC Zig.RmwOp.max true Zig.AtomicOrder.seqCst 4 (⟨some 3, 0⟩ : Zig.Ptr) p1
    let i4 ← Zig.load (BitVec 32) 4 (⟨some 3, 0⟩ : Zig.Ptr)
    pure (.ret i4)) : Zig.CM Tgt rmwMaxLocals rmwMaxExit).run' (default : rmwMaxLocals)
  match e with
  | .ret v => pure v

structure storeThenBytesLocals where
  deriving Inhabited

inductive storeThenBytesExit where
  | ret (v : BitVec 32)

def storeThenBytes (p0 : BitVec 32) : Zig.ConcM Tgt (BitVec 32) := do
  let e ← ((do
    Zig.atomicStoreC Zig.AtomicOrder.seqCst 4 (⟨some 0, 0⟩ : Zig.Ptr) p0
    let i2 ← Zig.load (BitVec 8) 1 (⟨some 0, 0⟩ : Zig.Ptr)
    let i3 ← Zig.intCast false false 32 i2
    let i4 ← pure (Zig.shl i3 (24 : BitVec 5))
    let i5 ← Zig.load (BitVec 8) 1 (⟨some 0, 1⟩ : Zig.Ptr)
    let i6 ← Zig.intCast false false 32 i5
    let i7 ← pure (Zig.shl i6 (16 : BitVec 5))
    let i8 ← pure (i4 ||| i7)
    let i9 ← Zig.load (BitVec 8) 1 (⟨some 0, 2⟩ : Zig.Ptr)
    let i10 ← Zig.intCast false false 32 i9
    let i11 ← pure (Zig.shl i10 (8 : BitVec 5))
    let i12 ← pure (i8 ||| i11)
    let i13 ← Zig.load (BitVec 8) 1 (⟨some 0, 3⟩ : Zig.Ptr)
    let i14 ← Zig.intCast false false 32 i13
    let i15 ← pure (i12 ||| i14)
    pure (.ret i15)) : Zig.CM Tgt storeThenBytesLocals storeThenBytesExit).run' (default : storeThenBytesLocals)
  match e with
  | .ret v => pure v

structure threadsAddLocals where
  c : Zig.Ptr
  deriving Inhabited

inductive threadsAddExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def threadsAdd (p0 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s1 ← Zig.allocStack 4 4
  let e ← ((do
    let i1 ← pure (← get).c
    Zig.store (α := BitVec 32) 4 i1 (16711680 : BitVec 32)
    let i3 ← pure (i1, p0)
    let i4 ← Zig.spawnC (Tgt.adder i3)
    match i4 with
    | .error _ => (do
      let i6 ← Zig.callRC (Zig.unwrapErr i4)
      let i7 ← pure (i6)
      let i8 ← pure ((.error i7) : Except Zig.ErrName (BitVec 32))
      pure (.ret i8))
    | .ok v5 => (do
      let i10 ← pure (i1, p0)
      let i11 ← Zig.spawnC (Tgt.adder i10)
      match i11 with
      | .error _ => (do
        let i13 ← Zig.callRC (Zig.unwrapErr i11)
        let i14 ← pure (i13)
        let i15 ← pure ((.error i14) : Except Zig.ErrName (BitVec 32))
        pure (.ret i15))
      | .ok v12 => (do
        let _i17 ← Zig.joinC v5
        let _i18 ← Zig.joinC v12
        let i19 ← pure (i1)
        let i20 ← Zig.callMC (Zig.load (BitVec 8) 1 (i19.elem 1 (0 : BitVec 64)))
        let i21 ← Zig.intCast false false 32 i20
        let i22 ← pure (Zig.shl i21 (24 : BitVec 5))
        let i23 ← pure (i1)
        let i24 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.seqCst 4 i23
        let i25 ← pure (i24 &&& (16777215 : BitVec 32))
        let i26 ← pure (i22 ||| i25)
        let i27 ← pure ((.ok i26) : Except Zig.ErrName (BitVec 32))
        pure (.ret i27)))) : Zig.CM Tgt threadsAddLocals threadsAddExit).run' { (default : threadsAddLocals) with c := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .adder a =>
    let (capture0, capture1) := a
    discard (adder capture0 capture1)

end Conc