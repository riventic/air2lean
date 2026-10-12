-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"arch8","endian":"big","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":[],"float_mode":"per-instruction","name":"abi64-be-v1","pointer_bits":64,"schema":12,"target_triple":"s390x-linux.5.10...6.16-musl","zig_version":"0.15.2"}}
import ZigLean


namespace Conc

open scoped Zig.BigEndian

structure atomic_Value_u32 where
  raw : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc atomic_Value_u32 where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.raw)]
  decode bs := do pure { raw := ← Zig.Enc.decodeAt bs 0 }

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
      let _i10 ← Zig.atomicRmwCOf .big Zig.RmwOp.add false Zig.AtomicOrder.seqCst 4 p0 (257 : BitVec 32)
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
    let i8 ← Zig.atomicLoadCOf .big (n := 32) Zig.AtomicOrder.seqCst 4 (⟨some 0, 0⟩ : Zig.Ptr)
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
    let i3 ← Zig.cmpxchgCOf .big Zig.AtomicOrder.seqCst Zig.AtomicOrder.seqCst 8 (⟨some 1, 0⟩ : Zig.Ptr) p0 p1
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

structure futexNoSleepLocals where
  word : Zig.Ptr
  deriving Inhabited

inductive futexNoSleepExit where
  | ret (v : BitVec 32)
  | br6 (v : BitVec 32)

def futexNoSleep  : Zig.ConcM Tgt (BitVec 32) := do
  let s0 ← Zig.allocStack 4 4
  let e ← ((do
    let i0 ← pure (← get).word
    let i1 ← Zig.callRC (atomic_Value_u32_init (16909060 : BitVec 32))
    Zig.store (α := atomic_Value_u32) 4 i0 i1
    let i3 ← pure (i0)
    let _i4 ← Zig.threadFutexWaitCOf .big i3 (67305985 : BitVec 32)
    let i5 ← pure (i0)
    match ← ((do
      let i7 ← pure i5
      let i8 ← Zig.atomicLoadCOf .big (n := 32) Zig.AtomicOrder.relaxed 4 i7
      pure (.br6 i8)) : Zig.CM Tgt futexNoSleepLocals futexNoSleepExit) with
    | .br6 v6 => (do
      pure (.ret v6))
    | e => pure e) : Zig.CM Tgt futexNoSleepLocals futexNoSleepExit).run' { (default : futexNoSleepLocals) with word := s0 }
  Zig.free s0
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
      Zig.atomicStoreCOf .big Zig.AtomicOrder.seqCst 4 v3 p1
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
    let _i3 ← Zig.atomicRmwCOf .big Zig.RmwOp.add false Zig.AtomicOrder.seqCst 2 (⟨some 2, 0⟩ : Zig.Ptr) p1
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
    let _i3 ← Zig.atomicRmwCOf .big Zig.RmwOp.max true Zig.AtomicOrder.seqCst 4 (⟨some 3, 0⟩ : Zig.Ptr) p1
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
    Zig.atomicStoreCOf .big Zig.AtomicOrder.seqCst 4 (⟨some 0, 0⟩ : Zig.Ptr) p0
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
        let i24 ← Zig.atomicLoadCOf .big (n := 32) Zig.AtomicOrder.seqCst 4 i23
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