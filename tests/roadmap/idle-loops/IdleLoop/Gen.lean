-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace IdleLoop

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

/-- The spawn targets of the program. -/
inductive Tgt where

structure idleLocals where
  deriving Inhabited

inductive idleExit where
  | ret
  | br7
  | br10
  | br3
  | br1
  | rep2

def idle.again2 : idleExit → Bool
  | .rep2 => true
  | _ => false

def idle.loop2 (p0 : Zig.Ptr) : Zig.CM Tgt idleLocals idleExit := do
  match ← ((do
    let i4 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.acquire 4 p0
    let i5 ← pure (i4 == (0 : BitVec 32))
    if i5 then (do
      match ← ((do
        let _i8 ← Zig.spinLoopHintC
        pure .br7) : Zig.CM Tgt idleLocals idleExit) with
      | .br7 => (do
        match ← ((do
          let i11 ← Zig.threadYieldC
          let i12 ← pure (Zig.isNonErr i11)
          if i12 then (do
            pure .br10)
          else (do
            let _i15 ← Zig.callRC (Zig.unwrapErr i11)
            pure .br10)) : Zig.CM Tgt idleLocals idleExit) with
        | .br10 => (do
          pure .br3)
        | e => pure e)
      | e => pure e)
    else (do
      pure .br1)) : Zig.CM Tgt idleLocals idleExit) with
  | .br3 => (do
    pure .rep2)
  | e => pure e

def idle (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    match ← ((do
      Zig.loop (idle.loop2 p0) idle.again2) : Zig.CM Tgt idleLocals idleExit) with
    | .br1 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt idleLocals idleExit).run' (default : idleLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit :=
  fun t => nomatch t

end IdleLoop