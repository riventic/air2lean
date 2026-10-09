-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace ExternCalls

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: a constant
  (Zig.Enc.encode ((#v[(101 : BitVec 8), (120 : BitVec 8), (116 : BitVec 8), (101 : BitVec 8), (114 : BitVec 8), (110 : BitVec 8), (32 : BitVec 8), (99 : BitVec 8), (97 : BitVec 8), (108 : BitVec 8), (108 : BitVec 8), (115 : BitVec 8), (0 : BitVec 8)] : Vector (BitVec 8) 13) : Vector (BitVec 8) 13), 1, .constGlobal),
  -- 1: a constant
  (Zig.Enc.encode ((#v[(104 : BitVec 8), (101 : BitVec 8), (108 : BitVec 8), (108 : BitVec 8), (111 : BitVec 8), (0 : BitVec 8)] : Vector (BitVec 8) 6) : Vector (BitVec 8) 6), 1, .constGlobal)]

structure libc_ref_memsetLocals where
  i : BitVec 64
  deriving Inhabited

inductive libc_ref_memsetExit where
  | ret (v : Zig.Ptr)
  | br9
  | br7
  | rep8

def libc_ref_memset.again8 : libc_ref_memsetExit → Bool
  | .rep8 => true
  | _ => false

def libc_ref_memset.loop8 (p0 : Zig.Ptr) (p2 : BitVec 64) (i4 : BitVec 8) : Zig.MM libc_ref_memsetLocals libc_ref_memsetExit := do
  match ← ((do
    let i10 ← pure ((← get).i)
    let i11 ← pure (i10)
    let i12 ← pure (p2)
    let i13 ← pure (Zig.lt false i11 i12)
    if i13 then (do
      let i15 ← pure ((← get).i)
      let i16 ← Zig.callM (Zig.ptrProject p0 (·.elem 1 i15))
      Zig.store (α := BitVec 8) 1 i16 i4
      let i18 ← pure ((← get).i)
      let i19 ← Zig.add false i18 (1 : BitVec 64)
      modify (fun s => { s with i := i19 })
      pure .br9)
    else (do
      pure .br7)) : Zig.MM libc_ref_memsetLocals libc_ref_memsetExit) with
  | .br9 => (do
    pure .rep8)
  | e => pure e

def libc_ref_memset (p0 : Zig.Ptr) (p1 : BitVec 32) (p2 : BitVec 64) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i3 ← pure (p1)
    let i4 ← pure (Zig.trunc 8 i3)
    modify (fun s => { s with i := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (libc_ref_memset.loop8 p0 p2 i4) libc_ref_memset.again8) : Zig.MM libc_ref_memsetLocals libc_ref_memsetExit) with
    | .br7 => (do
      pure (.ret p0))
    | e => pure e) : Zig.MM libc_ref_memsetLocals libc_ref_memsetExit).run' (default : libc_ref_memsetLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure fillSumLocals where
  buf : Zig.Ptr
  sum : BitVec 32
  local14 : BitVec 64
  deriving Inhabited

inductive fillSumExit where
  | ret (v : BitVec 32)
  | br4 (v : BitVec 64)
  | br20
  | br17
  | rep18

def fillSum.again18 : fillSumExit → Bool
  | .rep18 => true
  | _ => false

def fillSum.loop18 (i16 : Vector (BitVec 8) 16) : Zig.MM fillSumLocals fillSumExit := do
  let i19 ← pure ((← get).local14)
  match ← ((do
    let i21 ← pure (i19)
    let i22 ← pure (Zig.lt false i21 (16 : BitVec 64))
    if i22 then (do
      let i24 ← Zig.callR (Zig.vindex i16 i19)
      let i25 ← pure ((← get).sum)
      let i26 ← Zig.intCast false false 32 i24
      let i27 ← Zig.add false i25 i26
      modify (fun s => { s with sum := i27 })
      pure .br20)
    else (do
      pure .br17)) : Zig.MM fillSumLocals fillSumExit) with
  | .br20 => (do
    let i31 ← Zig.add false i19 (1 : BitVec 64)
    modify (fun s => { s with local14 := i31 })
    pure .rep18)
  | e => pure e

def fillSum (p0 : BitVec 64) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s2 ← Zig.allocStack 16 1
  let e ← ((do
    let i2 ← pure (← get).buf
    Zig.store (α := Vector (BitVec 8) 16) 1 i2 (#v[(1 : BitVec 8), (1 : BitVec 8), (1 : BitVec 8), (1 : BitVec 8), (1 : BitVec 8), (1 : BitVec 8), (1 : BitVec 8), (1 : BitVec 8), (1 : BitVec 8), (1 : BitVec 8), (1 : BitVec 8), (1 : BitVec 8), (1 : BitVec 8), (1 : BitVec 8), (1 : BitVec 8), (1 : BitVec 8)] : Vector (BitVec 8) 16)
    match ← ((do
      let i5 ← pure (p0)
      let i6 ← pure (Zig.gt false i5 (16 : BitVec 64))
      if i6 then (do
        pure (.br4 (16 : BitVec 64)))
      else (do
        pure (.br4 p0))) : Zig.MM fillSumLocals fillSumExit) with
    | .br4 v4 => (do
      let i10 ← pure (i2)
      let _i11 ← Zig.callM (libc_ref_memset i10 p1 v4)
      modify (fun s => { s with sum := (0 : BitVec 32) })
      modify (fun s => { s with local14 := (0 : BitVec 64) })
      let i16 ← Zig.load (Vector (BitVec 8) 16) 1 i2
      match ← ((do
        Zig.loop (fillSum.loop18 i16) fillSum.again18) : Zig.MM fillSumLocals fillSumExit) with
      | .br17 => (do
        let i34 ← pure ((← get).sum)
        pure (.ret i34))
      | e => pure e)
    | e => pure e) : Zig.MM fillSumLocals fillSumExit).run' { (default : fillSumLocals) with buf := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure libc_ref_strlenLocals where
  i : BitVec 64
  deriving Inhabited

inductive libc_ref_strlenExit where
  | ret (v : BitVec 64)
  | br5
  | br3
  | rep4

def libc_ref_strlen.again4 : libc_ref_strlenExit → Bool
  | .rep4 => true
  | _ => false

def libc_ref_strlen.loop4 (p0 : Zig.Ptr) : Zig.MM libc_ref_strlenLocals libc_ref_strlenExit := do
  match ← ((do
    let i6 ← pure ((← get).i)
    let i7 ← Zig.callM (Zig.load (BitVec 8) 1 (p0.elem 1 i6))
    let i8 ← pure (i7 != (0 : BitVec 8))
    if i8 then (do
      let i10 ← pure ((← get).i)
      let i11 ← Zig.add false i10 (1 : BitVec 64)
      modify (fun s => { s with i := i11 })
      pure .br5)
    else (do
      pure .br3)) : Zig.MM libc_ref_strlenLocals libc_ref_strlenExit) with
  | .br5 => (do
    pure .rep4)
  | e => pure e

def libc_ref_strlen (p0 : Zig.Ptr) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (libc_ref_strlen.loop4 p0) libc_ref_strlen.again4) : Zig.MM libc_ref_strlenLocals libc_ref_strlenExit) with
    | .br3 => (do
      let i16 ← pure ((← get).i)
      pure (.ret i16))
    | e => pure e) : Zig.MM libc_ref_strlenLocals libc_ref_strlenExit).run' (default : libc_ref_strlenLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure greetLenLocals where
  deriving Inhabited

inductive greetLenExit where
  | ret (v : BitVec 64)
  | br1 (v : Zig.Ptr)

def greetLen (p0 : BitVec 32) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure (p0 == (0 : BitVec 32))
      if i2 then (do
        pure (.br1 (⟨some 1, 0⟩ : Zig.Ptr)))
      else (do
        pure (.br1 (⟨some 0, 0⟩ : Zig.Ptr)))) : Zig.MM greetLenLocals greetLenExit) with
    | .br1 v1 => (do
      let i6 ← Zig.callM (libc_ref_strlen v1)
      pure (.ret i6))
    | e => pure e) : Zig.MM greetLenLocals greetLenExit).run' (default : greetLenLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end ExternCalls