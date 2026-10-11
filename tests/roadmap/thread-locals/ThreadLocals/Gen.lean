-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace ThreadLocals

structure Thread_SpawnConfig where
  stack_size : BitVec 64
  allocator : Option (Zig.Allocator)
  deriving Repr, Inhabited, DecidableEq

/-- The memory at program start under the placement `σ`: block `k` is global `k`. The main thread's instance of a `threadlocal` global is its block (its TLS key). -/
def mem0 (σ : Zig.Placement) : Zig.Mem := (Zig.Mem.ofGlobals σ [
  -- 0: thread_locals.counter (threadlocal: the main thread's instance)
  (Zig.Enc.encode ((7 : BitVec 32) : BitVec 32), 4, .global)]).mainTls #[0]

/-- The `threadlocal` globals: key, initial bytes and alignment. A spawned thread makes its own instance of each from these (`Zig.ConcM.tlsThread`). -/
def tlsInit : List (Zig.BlockId × Array Zig.Byte × Nat) := [
  -- thread_locals.counter
  (0, Zig.Enc.encode ((7 : BitVec 32) : BitVec 32), 4)]

/-- The spawn targets of the program. -/
inductive Tgt where
  | leak (a : Zig.Ptr)
  | bumpTwice (a : Zig.Ptr)

structure bumpTwiceLocals where
  deriving Inhabited

inductive bumpTwiceExit where
  | ret

def bumpTwice (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i1 ← Zig.tlsPtr 0
    let i2 ← Zig.load (BitVec 32) 4 i1
    let i3 ← Zig.add false i2 (1 : BitVec 32)
    Zig.store (α := BitVec 32) 4 i1 i3
    let i5 ← Zig.tlsPtr 0
    let i6 ← Zig.load (BitVec 32) 4 i5
    let i7 ← Zig.add false i6 (1 : BitVec 32)
    Zig.store (α := BitVec 32) 4 i5 i7
    let i9 ← Zig.tlsPtr 0
    let i10 ← Zig.load (BitVec 32) 4 i9
    Zig.store (α := BitVec 32) 4 p0 i10
    pure .ret) : Zig.MM bumpTwiceLocals bumpTwiceExit).run' (default : bumpTwiceLocals)
  match e with
  | .ret => pure ()

structure leakLocals where
  deriving Inhabited

inductive leakExit where
  | ret

def leak (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i1 ← Zig.tlsPtr 0
    Zig.store (α := Zig.Ptr) 8 p0 i1
    pure .ret) : Zig.MM leakLocals leakExit).run' (default : leakLocals)
  match e with
  | .ret => pure ()

structure leakedLocals where
  p : Zig.Ptr
  deriving Inhabited

inductive leakedExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def leaked  : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s0 ← Zig.allocStack 8 8
  let e ← ((do
    let i0 ← pure (← get).p
    Zig.storeUndef (Zig.Ptr) 8 i0
    let i2 ← pure (i0)
    let i3 ← Zig.spawnC (Tgt.leak i2)
    match i3 with
    | .error _ => (do
      let i5 ← Zig.callRC (Zig.unwrapErr i3)
      let i6 ← pure (i5)
      let i7 ← pure ((.error i6) : Except Zig.ErrName (BitVec 32))
      pure (.ret i7))
    | .ok v4 => (do
      let _i9 ← Zig.joinC v4
      let i10 ← Zig.load (Zig.Ptr) 8 i0
      let i11 ← Zig.load (BitVec 32) 4 i10
      let i12 ← pure ((.ok i11) : Except Zig.ErrName (BitVec 32))
      pure (.ret i12))) : Zig.CM Tgt leakedLocals leakedExit).run' { (default : leakedLocals) with p := s0 }
  Zig.free s0
  match e with
  | .ret v => pure v

structure twoCountersLocals where
  a : Zig.Ptr
  b : Zig.Ptr
  deriving Inhabited

inductive twoCountersExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def twoCounters  : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s0 ← Zig.allocStack 4 4
  let s2 ← Zig.allocStack 4 4
  let e ← ((do
    let i0 ← pure (← get).a
    Zig.store (α := BitVec 32) 4 i0 (0 : BitVec 32)
    let i2 ← pure (← get).b
    Zig.store (α := BitVec 32) 4 i2 (0 : BitVec 32)
    let i4 ← pure (i0)
    let i5 ← Zig.spawnC (Tgt.bumpTwice i4)
    match i5 with
    | .error _ => (do
      let i7 ← Zig.callRC (Zig.unwrapErr i5)
      let i8 ← pure (i7)
      let i9 ← pure ((.error i8) : Except Zig.ErrName (BitVec 32))
      pure (.ret i9))
    | .ok v6 => (do
      let i11 ← pure (i2)
      let i12 ← Zig.spawnC (Tgt.bumpTwice i11)
      match i12 with
      | .error _ => (do
        let i14 ← Zig.callRC (Zig.unwrapErr i12)
        let i15 ← pure (i14)
        let i16 ← pure ((.error i15) : Except Zig.ErrName (BitVec 32))
        pure (.ret i16))
      | .ok v13 => (do
        let i18 ← Zig.tlsPtr 0
        let i19 ← Zig.load (BitVec 32) 4 i18
        let i20 ← Zig.add false i19 (1 : BitVec 32)
        Zig.store (α := BitVec 32) 4 i18 i20
        let _i22 ← Zig.joinC v6
        let _i23 ← Zig.joinC v13
        let i24 ← Zig.load (BitVec 32) 4 i0
        let i25 ← Zig.mul false i24 (10000 : BitVec 32)
        let i26 ← Zig.load (BitVec 32) 4 i2
        let i27 ← Zig.mul false i26 (100 : BitVec 32)
        let i28 ← Zig.add false i25 i27
        let i29 ← Zig.tlsPtr 0
        let i30 ← Zig.load (BitVec 32) 4 i29
        let i31 ← Zig.add false i28 i30
        let i32 ← pure ((.ok i31) : Except Zig.ErrName (BitVec 32))
        pure (.ret i32)))) : Zig.CM Tgt twoCountersLocals twoCountersExit).run' { (default : twoCountersLocals) with a := s0, b := s2 }
  Zig.free s0
  Zig.free s2
  match e with
  | .ret v => pure v

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .leak a => Zig.ConcM.tlsThread tlsInit (discard (Zig.ConcM.liftMem (leak a)))
  | .bumpTwice a => Zig.ConcM.tlsThread tlsInit (discard (Zig.ConcM.liftMem (bumpTwice a)))

end ThreadLocals