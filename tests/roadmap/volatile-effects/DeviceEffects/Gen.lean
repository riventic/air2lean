-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
-- air2lean-device: {"device":"uart","registers":[{"access":"read","address":268435456,"bits":32,"name":"status"},{"access":"write","address":268435460,"bits":32,"name":"data"}],"schema":1,"semantics":"trace-oracle-v1"}
import ZigLean


namespace DeviceEffects

structure Uart where
  status : BitVec 32
  data : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Uart where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.status), (4, Zig.Enc.encode v.data)]
  decode bs := do pure { status := ← Zig.Enc.decodeAt bs 0, data := ← Zig.Enc.decodeAt bs 4 }

/-- The declared device `uart` (`--device-contract`, docs/volatile-effects.md, premise DEV-01): every volatile access is `Zig.vload`/`Zig.vstore` on this register map. -/
def air2lean_device : Zig.Device := { name := "uart", regs := [
  { name := "status", addr := 268435456, bits := 32, access := .read },
  { name := "data", addr := 268435460, bits := 32, access := .write }] }

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

structure clearStatusLocals where
  deriving Inhabited

inductive clearStatusExit where
  | ret

def clearStatus (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i1 ← pure (p0.add 0)
    let _i2 ← Zig.vload air2lean_device 32 4 i1
    pure .ret) : Zig.MM clearStatusLocals clearStatusExit).run' (default : clearStatusLocals)
  match e with
  | .ret => pure ()

structure putcLocals where
  deriving Inhabited

inductive putcExit where
  | ret
  | br4
  | br2
  | rep3

def putc.again3 : putcExit → Bool
  | .rep3 => true
  | _ => false

def putc.loop3 (p0 : Zig.Ptr) : Zig.MM putcLocals putcExit := do
  match ← ((do
    let i5 ← pure (p0.add 0)
    let i6 ← Zig.vload air2lean_device 32 4 i5
    let i7 ← pure (i6 &&& (1 : BitVec 32))
    let i8 ← pure (i7 == (0 : BitVec 32))
    if i8 then (do
      pure .br4)
    else (do
      pure .br2)) : Zig.MM putcLocals putcExit) with
  | .br4 => (do
    pure .rep3)
  | e => pure e

def putc (p0 : Zig.Ptr) (p1 : BitVec 8) : Zig.MemM (Unit) := do
  let e ← ((do
    match ← ((do
      Zig.loop (putc.loop3 p0) putc.again3) : Zig.MM putcLocals putcExit) with
    | .br2 => (do
      let i13 ← pure (p0.add 4)
      let i14 ← Zig.intCast false false 32 p1
      Zig.vstore air2lean_device 32 4 i13 i14
      pure .ret)
    | e => pure e) : Zig.MM putcLocals putcExit).run' (default : putcLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure sendThenStatusLocals where
  deriving Inhabited

inductive sendThenStatusExit where
  | ret (v : BitVec 32)

def sendThenStatus (p0 : Zig.Ptr) (p1 : BitVec 8) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i2 ← pure (p0.add 4)
    let i3 ← Zig.intCast false false 32 p1
    Zig.vstore air2lean_device 32 4 i2 i3
    let i5 ← pure (p0.add 0)
    let i6 ← Zig.vload air2lean_device 32 4 i5
    pure (.ret i6)) : Zig.MM sendThenStatusLocals sendThenStatusExit).run' (default : sendThenStatusLocals)
  match e with
  | .ret v => pure v

structure statusTwiceLocals where
  deriving Inhabited

inductive statusTwiceExit where
  | ret (v : BitVec 32)

def statusTwice (p0 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (p0.add 0)
    let i2 ← Zig.vload air2lean_device 32 4 i1
    let i3 ← pure (p0.add 0)
    let i4 ← Zig.vload air2lean_device 32 4 i3
    let i5 ← pure (i2 ^^^ i4)
    pure (.ret i5)) : Zig.MM statusTwiceLocals statusTwiceExit).run' (default : statusTwiceLocals)
  match e with
  | .ret v => pure v

structure writeAllLocals where
  local2 : BitVec 64
  deriving Inhabited

inductive writeAllExit where
  | ret
  | br8
  | br5
  | rep6

def writeAll.again6 : writeAllExit → Bool
  | .rep6 => true
  | _ => false

def writeAll.loop6 (p0 : Zig.Ptr) (p1 : Zig.Slice) (i4 : BitVec 64) : Zig.MM writeAllLocals writeAllExit := do
  let i7 ← pure ((← get).local2)
  match ← ((do
    let i9 ← pure (i7)
    let i10 ← pure (i4)
    let i11 ← pure (Zig.lt false i9 i10)
    if i11 then (do
      let i13 ← Zig.callM (Zig.checkIndex p1 i7 >>= fun _ => Zig.load (BitVec 8) 1 (p1.ptr.elem 1 i7))
      let _i14 ← Zig.callM (putc p0 i13)
      pure .br8)
    else (do
      pure .br5)) : Zig.MM writeAllLocals writeAllExit) with
  | .br8 => (do
    let i17 ← Zig.add false i7 (1 : BitVec 64)
    modify (fun s => { s with local2 := i17 })
    pure .rep6)
  | e => pure e

def writeAll (p0 : Zig.Ptr) (p1 : Zig.Slice) : Zig.MemM (Unit) := do
  let e ← ((do
    modify (fun s => { s with local2 := (0 : BitVec 64) })
    let i4 ← pure p1.len
    match ← ((do
      Zig.loop (writeAll.loop6 p0 p1 i4) writeAll.again6) : Zig.MM writeAllLocals writeAllExit) with
    | .br5 => (do
      pure .ret)
    | e => pure e) : Zig.MM writeAllLocals writeAllExit).run' (default : writeAllLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

end DeviceEffects