-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace Nested

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure pairsLocals where
  i : BitVec 32
  j : BitVec 32
  deriving Inhabited

inductive pairsExit where
  | ret
  | br15
  | br13
  | br10
  | br6
  | br4
  | rep14
  | rep5

def pairs.again14 : pairsExit → Bool
  | .rep14 => true
  | _ => false

def pairs.again5 : pairsExit → Bool
  | .rep5 => true
  | _ => false

def pairs.loop14 (p0 : Zig.Ptr) : Zig.MM pairsLocals pairsExit := do
  match ← ((do
    let i16 ← pure ((← get).j)
    let i17 ← pure ((← get).i)
    let i18 ← pure (Zig.lt false i16 i17)
    if i18 then (do
      let i20 ← Zig.load (BitVec 64) 8 p0
      let i21 ← Zig.add false i20 (1 : BitVec 64)
      Zig.store (α := BitVec 64) 8 p0 i21
      let i23 ← pure ((← get).j)
      let i24 ← Zig.add false i23 (1 : BitVec 32)
      modify (fun s => { s with j := i24 })
      pure .br15)
    else (do
      pure .br13)) : Zig.MM pairsLocals pairsExit) with
  | .br15 => (do
    pure .rep14)
  | e => pure e

def pairs.loop5 (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MM pairsLocals pairsExit := do
  match ← ((do
    let i7 ← pure ((← get).i)
    let i8 ← pure (Zig.lt false i7 p1)
    if i8 then (do
      match ← ((do
        modify (fun s => { s with j := (0 : BitVec 32) })
        match ← ((do
          Zig.loop (pairs.loop14 p0) pairs.again14) : Zig.MM pairsLocals pairsExit) with
        | .br13 => (do
          pure .br10)
        | e => pure e) : Zig.MM pairsLocals pairsExit) with
      | .br10 => (do
        let i30 ← pure ((← get).i)
        let i31 ← Zig.add false i30 (1 : BitVec 32)
        modify (fun s => { s with i := i31 })
        pure .br6)
      | e => pure e)
    else (do
      pure .br4)) : Zig.MM pairsLocals pairsExit) with
  | .br6 => (do
    pure .rep5)
  | e => pure e

def pairs (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (pairs.loop5 p0 p1) pairs.again5) : Zig.MM pairsLocals pairsExit) with
    | .br4 => (do
      pure .ret)
    | e => pure e) : Zig.MM pairsLocals pairsExit).run' (default : pairsLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

end Nested