-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"}}
import ZigLean


namespace Ring

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure drainLocals where
  sum : BitVec 64
  deriving Inhabited

inductive drainExit where
  | ret (v : BitVec 64)
  | br15
  | br7
  | br5
  | rep6

def drain.again6 : drainExit → Bool
  | .rep6 => true
  | _ => false

def drain.loop6 (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : Zig.Ptr) : Zig.MM drainLocals drainExit := do
  match ← ((do
    let i8 ← Zig.load (BitVec 32) 4 p2
    let i9 ← pure (i8 != (0 : BitVec 32))
    if i9 then (do
      let i11 ← pure ((← get).sum)
      let i12 ← Zig.load (BitVec 32) 4 p1
      let i13 ← Zig.intCast false false 64 i12
      let i14 ← pure (Zig.lt false i13 (8 : BitVec 64))
      match ← ((do
        if i14 then (do
          pure .br15)
        else (do
          throw .outOfBounds)) : Zig.MM drainLocals drainExit) with
      | .br15 => (do
        let i20 ← Zig.callM (Zig.checkIndex (8 : BitVec 64) i13 >>= fun _ => Zig.load (BitVec 32) 4 (p0.elem 4 i13))
        let i21 ← Zig.intCast false false 64 i20
        let i22 ← Zig.add false i11 i21
        modify (fun s => { s with sum := i22 })
        let i24 ← Zig.load (BitVec 32) 4 p1
        let i25 ← Zig.add false i24 (1 : BitVec 32)
        let i26 ← Zig.rem false i25 (8 : BitVec 32)
        Zig.store (α := BitVec 32) 4 p1 i26
        let i28 ← Zig.load (BitVec 32) 4 p2
        let i29 ← Zig.sub false i28 (1 : BitVec 32)
        Zig.store (α := BitVec 32) 4 p2 i29
        pure .br7)
      | e => pure e)
    else (do
      pure .br5)) : Zig.MM drainLocals drainExit) with
  | .br7 => (do
    pure .rep6)
  | e => pure e

def drain (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : Zig.Ptr) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with sum := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (drain.loop6 p0 p1 p2) drain.again6) : Zig.MM drainLocals drainExit) with
    | .br5 => (do
      let i34 ← pure ((← get).sum)
      pure (.ret i34))
    | e => pure e) : Zig.MM drainLocals drainExit).run' (default : drainLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure pushLocals where
  deriving Inhabited

inductive pushExit where
  | ret (v : Bool)
  | br4
  | br16

def push (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : Zig.Ptr) (p3 : BitVec 32) : Zig.MemM (Bool) := do
  let e ← ((do
    match ← ((do
      let i5 ← Zig.load (BitVec 32) 4 p2
      let i6 ← pure (i5 == (8 : BitVec 32))
      if i6 then (do
        pure (.ret false))
      else (do
        pure .br4)) : Zig.MM pushLocals pushExit) with
    | .br4 => (do
      let i10 ← Zig.load (BitVec 32) 4 p1
      let i11 ← Zig.load (BitVec 32) 4 p2
      let i12 ← Zig.add false i10 i11
      let i13 ← Zig.rem false i12 (8 : BitVec 32)
      let i14 ← Zig.intCast false false 64 i13
      let i15 ← pure (Zig.lt false i14 (8 : BitVec 64))
      match ← ((do
        if i15 then (do
          pure .br16)
        else (do
          throw .outOfBounds)) : Zig.MM pushLocals pushExit) with
      | .br16 => (do
        let i21 ← Zig.callM (Zig.checkIndex (8 : BitVec 64) i14) >>= fun _ => Zig.callM (Zig.ptrProject p0 (·.elem 4 i14))
        Zig.store (α := BitVec 32) 4 i21 p3
        let i23 ← Zig.load (BitVec 32) 4 p2
        let i24 ← Zig.add false i23 (1 : BitVec 32)
        Zig.store (α := BitVec 32) 4 p2 i24
        pure (.ret true))
      | e => pure e)
    | e => pure e) : Zig.MM pushLocals pushExit).run' (default : pushLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end Ring