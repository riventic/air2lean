-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace EscapedGlobals

structure Node where
  value : BitVec 32
  next : Option (Zig.Ptr)
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Node where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.value), (8, Zig.Enc.encode v.next)]
  decode bs := do pure { value := ← Zig.Enc.decodeAt bs 0, next := ← Zig.Enc.decodeAt bs 8 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: escaped.counter
  (Zig.Enc.encode ((10 : BitVec 32) : BitVec 32), 4, .global),
  -- 1: escaped.data
  (Zig.Enc.encode ((#v[(0 : BitVec 32), (0 : BitVec 32), (0 : BitVec 32), (0 : BitVec 32)] : Vector (BitVec 32) 4) : Vector (BitVec 32) 4), 4, .global),
  -- 2: escaped.pool
  (Zig.Enc.encode ((#v[({ value := (0 : BitVec 32), next := none } : Node), ({ value := (0 : BitVec 32), next := none } : Node), ({ value := (0 : BitVec 32), next := none } : Node), ({ value := (0 : BitVec 32), next := none } : Node)] : Vector (Node) 4) : Vector (Node) 4), 8, .global)]

structure counterBumpLocals where
  deriving Inhabited

inductive counterBumpExit where
  | ret (v : BitVec 32)

def counterBump (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i2 ← Zig.load (BitVec 32) 4 (⟨some 0, 0⟩ : Zig.Ptr)
    let i3 ← pure (p0 ^^^ p1)
    let i4 ← pure (Zig.addWrap i2 i3)
    Zig.store (α := BitVec 32) 4 (⟨some 0, 0⟩ : Zig.Ptr) i4
    let i6 ← Zig.load (BitVec 32) 4 (⟨some 0, 0⟩ : Zig.Ptr)
    Zig.store (α := BitVec 32) 4 (⟨some 0, 0⟩ : Zig.Ptr) i2
    pure (.ret i6)) : Zig.MM counterBumpLocals counterBumpExit).run' (default : counterBumpLocals)
  match e with
  | .ret v => pure v

structure dataAddrLocals where
  local2 : BitVec 64
  deriving Inhabited

inductive dataAddrExit where
  | ret (v : BitVec 32)
  | br7
  | br4
  | br24
  | br31
  | rep5

def dataAddr.again5 : dataAddrExit → Bool
  | .rep5 => true
  | _ => false

def dataAddr.loop5 (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MM dataAddrLocals dataAddrExit := do
  let i6 ← pure ((← get).local2)
  match ← ((do
    let i8 ← pure (i6)
    let i9 ← pure (Zig.lt false i8 (4 : BitVec 64))
    if i9 then (do
      let i11 ← Zig.callM (Zig.ptrProject (⟨some 1, 0⟩ : Zig.Ptr) (·.elem 4 i6))
      let i12 ← Zig.intCast false false 32 i6
      let i13 ← pure (Zig.mulWrap i12 p1)
      let i14 ← pure (Zig.addWrap p0 i13)
      Zig.store (α := BitVec 32) 4 i11 i14
      pure .br7)
    else (do
      pure .br4)) : Zig.MM dataAddrLocals dataAddrExit) with
  | .br7 => (do
    let i18 ← Zig.add false i6 (1 : BitVec 64)
    modify (fun s => { s with local2 := i18 })
    pure .rep5)
  | e => pure e

def dataAddr (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with local2 := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (dataAddr.loop5 p0 p1) dataAddr.again5) : Zig.MM dataAddrLocals dataAddrExit) with
    | .br4 => (do
      let i21 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr (⟨some 1, 4⟩ : Zig.Ptr))))
      let i22 ← Zig.add false i21 (4 : BitVec 64)
      let i23 ← pure (i22 != (0 : BitVec 64))
      match ← ((do
        if i23 then (do
          pure .br24)
        else (do
          throw .panic)) : Zig.MM dataAddrLocals dataAddrExit) with
      | .br24 => (do
        let i29 ← pure (i22 &&& (3 : BitVec 64))
        let i30 ← pure (i29 == (0 : BitVec 64))
        match ← ((do
          if i30 then (do
            pure .br31)
          else (do
            throw .panic)) : Zig.MM dataAddrLocals dataAddrExit) with
        | .br31 => (do
          let i36 ← Zig.callM (Zig.checkAddr 4 true (i22).toNat >>= fun _ => Zig.ptrFromAddr (i22).toNat)
          let i37 ← Zig.load (BitVec 32) 4 i36
          let i38 ← Zig.rem false i21 (4 : BitVec 64)
          let i39 ← pure (i38)
          let i40 ← pure (i39 == (0 : BitVec 64))
          let i41 ← pure (if i40 then 1 else 0 : BitVec 1)
          let i42 ← Zig.intCast false false 32 i41
          let i43 ← pure (Zig.addWrap i37 i42)
          pure (.ret i43))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM dataAddrLocals dataAddrExit).run' (default : dataAddrLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure poolListLocals where
  head : Option (Zig.Ptr)
  i : BitVec 32
  s : BitVec 32
  k : BitVec 32
  it : Option (Zig.Ptr)
  deriving Inhabited

inductive poolListExit where
  | ret (v : BitVec 32)
  | br15
  | br32
  | br8
  | br6
  | br55
  | br53
  | rep7
  | rep54

def poolList.again54 : poolListExit → Bool
  | .rep54 => true
  | _ => false

def poolList.again7 : poolListExit → Bool
  | .rep7 => true
  | _ => false

def poolList.loop54  : Zig.MM poolListLocals poolListExit := do
  match ← ((do
    let i56 ← pure ((← get).it)
    let i57 ← pure ((i56).isSome)
    if i57 then (do
      let i59 ← Zig.optPayload i56
      let i60 ← pure ((← get).s)
      let i61 ← pure i59
      let i62 ← Zig.load (BitVec 32) 8 i61
      let i63 ← pure ((← get).k)
      let i64 ← pure (Zig.mulWrap i62 i63)
      let i65 ← pure (Zig.addWrap i60 i64)
      modify (fun s => { s with s := i65 })
      let i67 ← pure ((← get).k)
      let i68 ← Zig.add false i67 (1 : BitVec 32)
      modify (fun s => { s with k := i68 })
      let i70 ← Zig.callM (Zig.ptrProject i59 (·.add 8))
      let i71 ← Zig.load (Option (Zig.Ptr)) 8 i70
      modify (fun s => { s with it := i71 })
      pure .br55)
    else (do
      pure .br53)) : Zig.MM poolListLocals poolListExit) with
  | .br55 => (do
    pure .rep54)
  | e => pure e

def poolList.loop7 (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MM poolListLocals poolListExit := do
  match ← ((do
    let i9 ← pure ((← get).i)
    let i10 ← pure (Zig.lt false i9 (4 : BitVec 32))
    if i10 then (do
      let i12 ← pure ((← get).i)
      let i13 ← Zig.intCast false false 64 i12
      let i14 ← pure (Zig.lt false i13 (4 : BitVec 64))
      match ← ((do
        if i14 then (do
          pure .br15)
        else (do
          throw .outOfBounds)) : Zig.MM poolListLocals poolListExit) with
      | .br15 => (do
        let i20 ← Zig.callM (Zig.ptrProject (⟨some 2, 0⟩ : Zig.Ptr) (·.elem 16 i13))
        let i21 ← pure i20
        let i22 ← pure ((← get).i)
        let i23 ← pure (Zig.mulWrap i22 p1)
        let i24 ← pure (Zig.addWrap p0 i23)
        Zig.store (α := BitVec 32) 8 i21 i24
        let i26 ← Zig.callM (Zig.ptrProject i20 (·.add 8))
        let i27 ← pure ((← get).head)
        Zig.store (α := Option (Zig.Ptr)) 8 i26 i27
        let i29 ← pure ((← get).i)
        let i30 ← Zig.intCast false false 64 i29
        let i31 ← pure (Zig.lt false i30 (4 : BitVec 64))
        match ← ((do
          if i31 then (do
            pure .br32)
          else (do
            throw .outOfBounds)) : Zig.MM poolListLocals poolListExit) with
        | .br32 => (do
          let i37 ← Zig.callM (Zig.ptrProject (⟨some 2, 0⟩ : Zig.Ptr) (·.elem 16 i30))
          let i38 ← pure (i37)
          modify (fun s => { s with head := i38 })
          let i40 ← pure ((← get).i)
          let i41 ← Zig.add false i40 (1 : BitVec 32)
          modify (fun s => { s with i := i41 })
          pure .br8)
        | e => pure e)
      | e => pure e)
    else (do
      pure .br6)) : Zig.MM poolListLocals poolListExit) with
  | .br8 => (do
    pure .rep7)
  | e => pure e

def poolList (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with head := none })
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (poolList.loop7 p0 p1) poolList.again7) : Zig.MM poolListLocals poolListExit) with
    | .br6 => (do
      modify (fun s => { s with s := (0 : BitVec 32) })
      modify (fun s => { s with k := (1 : BitVec 32) })
      let i51 ← pure ((← get).head)
      modify (fun s => { s with it := i51 })
      match ← ((do
        Zig.loop (poolList.loop54 ) poolList.again54) : Zig.MM poolListLocals poolListExit) with
      | .br53 => (do
        let i76 ← pure ((← get).s)
        pure (.ret i76))
      | e => pure e)
    | e => pure e) : Zig.MM poolListLocals poolListExit).run' (default : poolListLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end EscapedGlobals