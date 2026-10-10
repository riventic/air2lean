-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace PtrCasts

structure Tree where
  key : BitVec 32
  left : Zig.Ptr
  right : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Tree where
  size := 24
  align := 8
  encode v := Zig.Enc.fields 24 [(0, Zig.Enc.encode v.key), (8, (letI : Zig.Enc (Zig.Ptr) := Zig.nullablePtrEnc; Zig.Enc.encode v.left)), (16, (letI : Zig.Enc (Zig.Ptr) := Zig.nullablePtrEnc; Zig.Enc.encode v.right))]
  decode bs := do pure { key := ← Zig.Enc.decodeAt bs 0, left := ← (letI : Zig.Enc (Zig.Ptr) := Zig.nullablePtrEnc; Zig.Enc.decodeAt bs 8), right := ← (letI : Zig.Enc (Zig.Ptr) := Zig.nullablePtrEnc; Zig.Enc.decodeAt bs 16) }

structure Node where
  value : BitVec 32
  next : Option (Zig.Ptr)
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Node where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.value), (8, Zig.Enc.encode v.next)]
  decode bs := do pure { value := ← Zig.Enc.decodeAt bs 0, next := ← Zig.Enc.decodeAt bs 8 }

structure Ctx where
  sum : BitVec 32
  scale : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Ctx where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.sum), (4, Zig.Enc.encode v.scale)]
  decode bs := do pure { sum := ← Zig.Enc.decodeAt bs 0, scale := ← Zig.Enc.decodeAt bs 4 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure byteAsBoolLocals where
  x : Zig.Ptr
  deriving Inhabited

inductive byteAsBoolExit where
  | ret (v : BitVec 32)
  | br8 (v : BitVec 32)

def byteAsBool (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s2 ← Zig.allocStack 1 1
  let e ← ((do
    let i2 ← pure (← get).x
    let i3 ← pure (p0 ^^^ p1)
    let i4 ← pure (i3 ||| (2 : BitVec 32))
    let i5 ← pure (Zig.trunc 8 i4)
    Zig.store (α := BitVec 8) 1 i2 i5
    let i7 ← pure (i2)
    match ← ((do
      let i9 ← Zig.load (Bool) 1 i7
      if i9 then (do
        pure (.br8 (1 : BitVec 32)))
      else (do
        pure (.br8 (0 : BitVec 32)))) : Zig.MM byteAsBoolLocals byteAsBoolExit) with
    | .br8 v8 => (do
      pure (.ret v8))
    | e => pure e) : Zig.MM byteAsBoolLocals byteAsBoolExit).run' { (default : byteAsBoolLocals) with x := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure byteVectorCopyLocals where
  src : Zig.Ptr
  local4 : BitVec 64
  dst : Zig.Ptr
  sum : BitVec 32
  local32 : BitVec 64
  deriving Inhabited

inductive byteVectorCopyExit where
  | ret (v : BitVec 32)
  | br9
  | br6
  | br38
  | br35
  | rep7
  | rep36

def byteVectorCopy.again36 : byteVectorCopyExit → Bool
  | .rep36 => true
  | _ => false

def byteVectorCopy.again7 : byteVectorCopyExit → Bool
  | .rep7 => true
  | _ => false

def byteVectorCopy.loop36 (i34 : Vector (BitVec 8) 16) : Zig.MM byteVectorCopyLocals byteVectorCopyExit := do
  let i37 ← pure ((← get).local32)
  match ← ((do
    let i39 ← pure (i37)
    let i40 ← pure (Zig.lt false i39 (16 : BitVec 64))
    if i40 then (do
      let i42 ← Zig.callR (Zig.vindex i34 i37)
      let i43 ← pure ((← get).sum)
      let i44 ← Zig.intCast false false 32 i42
      let i45 ← pure (Zig.addWrap i43 i44)
      modify (fun s => { s with sum := i45 })
      pure .br38)
    else (do
      pure .br35)) : Zig.MM byteVectorCopyLocals byteVectorCopyExit) with
  | .br38 => (do
    let i49 ← Zig.add false i37 (1 : BitVec 64)
    modify (fun s => { s with local32 := i49 })
    pure .rep36)
  | e => pure e

def byteVectorCopy.loop7 (p0 : BitVec 32) (p1 : BitVec 32) (i2 : Zig.Ptr) : Zig.MM byteVectorCopyLocals byteVectorCopyExit := do
  let i8 ← pure ((← get).local4)
  match ← ((do
    let i10 ← pure (i8)
    let i11 ← pure (Zig.lt false i10 (16 : BitVec 64))
    if i11 then (do
      let i13 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 i8))
      let i14 ← Zig.intCast false false 32 i8
      let i15 ← pure (Zig.mulWrap p1 i14)
      let i16 ← pure (Zig.addWrap p0 i15)
      let i17 ← pure (Zig.trunc 8 i16)
      Zig.store (α := BitVec 8) 1 i13 i17
      pure .br9)
    else (do
      pure .br6)) : Zig.MM byteVectorCopyLocals byteVectorCopyExit) with
  | .br9 => (do
    let i21 ← Zig.add false i8 (1 : BitVec 64)
    modify (fun s => { s with local4 := i21 })
    pure .rep7)
  | e => pure e

def byteVectorCopy (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s2 ← Zig.allocStack 16 16
  let s24 ← Zig.allocStack 16 16
  let e ← ((do
    let i2 ← pure (← get).src
    Zig.storeUndef (Vector (BitVec 8) 16) 16 i2
    modify (fun s => { s with local4 := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (byteVectorCopy.loop7 p0 p1 i2) byteVectorCopy.again7) : Zig.MM byteVectorCopyLocals byteVectorCopyExit) with
    | .br6 => (do
      let i24 ← pure (← get).dst
      Zig.storeUndef (Vector (BitVec 8) 16) 16 i24
      let i26 ← pure (i2)
      let i27 ← pure (i24)
      let i28 ← Zig.load (Zig.Vec (BitVec 8) 16) 16 i26
      Zig.store (α := Zig.Vec (BitVec 8) 16) 16 i27 i28
      modify (fun s => { s with sum := (0 : BitVec 32) })
      modify (fun s => { s with local32 := (0 : BitVec 64) })
      let i34 ← Zig.load (Vector (BitVec 8) 16) 16 i24
      match ← ((do
        Zig.loop (byteVectorCopy.loop36 i34) byteVectorCopy.again36) : Zig.MM byteVectorCopyLocals byteVectorCopyExit) with
      | .br35 => (do
        let i52 ← pure ((← get).sum)
        pure (.ret i52))
      | e => pure e)
    | e => pure e) : Zig.MM byteVectorCopyLocals byteVectorCopyExit).run' { (default : byteVectorCopyLocals) with src := s2, dst := s24 }
  Zig.free s2
  Zig.free s24
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure byteViewLocals where
  w : Zig.Ptr
  s : BitVec 32
  i : BitVec 64
  deriving Inhabited

inductive byteViewExit where
  | ret (v : BitVec 32)
  | br12
  | br10
  | rep11

def byteView.again11 : byteViewExit → Bool
  | .rep11 => true
  | _ => false

def byteView.loop11 (i5 : Zig.Ptr) : Zig.MM byteViewLocals byteViewExit := do
  match ← ((do
    let i13 ← pure ((← get).i)
    let i14 ← pure (i13)
    let i15 ← pure (Zig.lt false i14 (4 : BitVec 64))
    if i15 then (do
      let i17 ← pure ((← get).s)
      let i18 ← pure (Zig.mulWrap i17 (31 : BitVec 32))
      let i19 ← pure ((← get).i)
      let i20 ← Zig.callM (Zig.load (BitVec 8) 1 (i5.elem 1 i19))
      let i21 ← Zig.intCast false false 32 i20
      let i22 ← pure (Zig.addWrap i18 i21)
      modify (fun s => { s with s := i22 })
      let i24 ← pure ((← get).i)
      let i25 ← Zig.add false i24 (1 : BitVec 64)
      modify (fun s => { s with i := i25 })
      pure .br12)
    else (do
      pure .br10)) : Zig.MM byteViewLocals byteViewExit) with
  | .br12 => (do
    pure .rep11)
  | e => pure e

def byteView (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s2 ← Zig.allocStack 4 4
  let e ← ((do
    let i2 ← pure (← get).w
    let i3 ← pure (Zig.addWrap p0 p1)
    Zig.store (α := BitVec 32) 4 i2 i3
    let i5 ← pure (i2)
    modify (fun s => { s with s := (0 : BitVec 32) })
    modify (fun s => { s with i := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (byteView.loop11 i5) byteView.again11) : Zig.MM byteViewLocals byteViewExit) with
    | .br10 => (do
      let i30 ← Zig.callM (Zig.ptrProjectNonnull i5 (·.elem 1 (1 : BitVec 64)))
      Zig.store (α := BitVec 8) 1 i30 (171 : BitVec 8)
      let i32 ← pure ((← get).s)
      let i33 ← Zig.load (BitVec 32) 4 i2
      let i34 ← pure (i32 ^^^ i33)
      pure (.ret i34))
    | e => pure e) : Zig.MM byteViewLocals byteViewExit).run' { (default : byteViewLocals) with w := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure listSumLocals where
  pool : Zig.Ptr
  head : Zig.Ptr
  i : BitVec 32
  link : Zig.Ptr
  s : BitVec 32
  k : BitVec 32
  it : Option (Zig.Ptr)
  deriving Inhabited

inductive listSumExit where
  | ret (v : BitVec 32)
  | br17
  | br34
  | br10
  | br8
  | br58
  | br52
  | br50
  | br84
  | br82
  | rep9
  | rep51
  | rep83

def listSum.again83 : listSumExit → Bool
  | .rep83 => true
  | _ => false

def listSum.again51 : listSumExit → Bool
  | .rep51 => true
  | _ => false

def listSum.again9 : listSumExit → Bool
  | .rep9 => true
  | _ => false

def listSum.loop83  : Zig.MM listSumLocals listSumExit := do
  match ← ((do
    let i85 ← pure ((← get).it)
    let i86 ← pure ((i85).isSome)
    if i86 then (do
      let i88 ← Zig.optPayload i85
      let i89 ← pure ((← get).s)
      let i90 ← pure i88
      let i91 ← Zig.load (BitVec 32) 8 i90
      let i92 ← pure ((← get).k)
      let i93 ← pure (Zig.mulWrap i91 i92)
      let i94 ← pure (Zig.addWrap i89 i93)
      modify (fun s => { s with s := i94 })
      let i96 ← pure ((← get).k)
      let i97 ← Zig.add false i96 (1 : BitVec 32)
      modify (fun s => { s with k := i97 })
      let i99 ← Zig.callM (Zig.ptrProject i88 (·.add 8))
      let i100 ← Zig.load (Option (Zig.Ptr)) 8 i99
      modify (fun s => { s with it := i100 })
      pure .br84)
    else (do
      pure .br82)) : Zig.MM listSumLocals listSumExit) with
  | .br84 => (do
    pure .rep83)
  | e => pure e

def listSum.loop51  : Zig.MM listSumLocals listSumExit := do
  match ← ((do
    let i53 ← pure ((← get).link)
    let i54 ← Zig.load (Option (Zig.Ptr)) 8 i53
    let i55 ← pure ((i54).isSome)
    if i55 then (do
      let i57 ← Zig.optPayload i54
      match ← ((do
        let i59 ← pure i57
        let i60 ← Zig.load (BitVec 32) 8 i59
        let i61 ← pure (i60 &&& (1 : BitVec 32))
        let i62 ← pure (i61 != (0 : BitVec 32))
        if i62 then (do
          let i64 ← pure ((← get).link)
          let i65 ← Zig.callM (Zig.ptrProject i57 (·.add 8))
          let i66 ← Zig.load (Option (Zig.Ptr)) 8 i65
          Zig.store (α := Option (Zig.Ptr)) 8 i64 i66
          pure .br58)
        else (do
          let i69 ← Zig.callM (Zig.ptrProject i57 (·.add 8))
          modify (fun s => { s with link := i69 })
          pure .br58)) : Zig.MM listSumLocals listSumExit) with
      | .br58 => (do
        pure .br52)
      | e => pure e)
    else (do
      pure .br50)) : Zig.MM listSumLocals listSumExit) with
  | .br52 => (do
    pure .rep51)
  | e => pure e

def listSum.loop9 (p0 : BitVec 32) (p1 : BitVec 32) (i2 : Zig.Ptr) (i4 : Zig.Ptr) : Zig.MM listSumLocals listSumExit := do
  match ← ((do
    let i11 ← pure ((← get).i)
    let i12 ← pure (Zig.lt false i11 (6 : BitVec 32))
    if i12 then (do
      let i14 ← pure ((← get).i)
      let i15 ← Zig.intCast false false 64 i14
      let i16 ← pure (Zig.lt false i15 (6 : BitVec 64))
      match ← ((do
        if i16 then (do
          pure .br17)
        else (do
          throw .outOfBounds)) : Zig.MM listSumLocals listSumExit) with
      | .br17 => (do
        let i22 ← Zig.callM (Zig.ptrProject i2 (·.elem 16 i15))
        let i23 ← pure i22
        let i24 ← pure ((← get).i)
        let i25 ← pure (Zig.mulWrap i24 p1)
        let i26 ← pure (Zig.addWrap p0 i25)
        Zig.store (α := BitVec 32) 8 i23 i26
        let i28 ← Zig.callM (Zig.ptrProject i22 (·.add 8))
        let i29 ← Zig.load (Option (Zig.Ptr)) 8 i4
        Zig.store (α := Option (Zig.Ptr)) 8 i28 i29
        let i31 ← pure ((← get).i)
        let i32 ← Zig.intCast false false 64 i31
        let i33 ← pure (Zig.lt false i32 (6 : BitVec 64))
        match ← ((do
          if i33 then (do
            pure .br34)
          else (do
            throw .outOfBounds)) : Zig.MM listSumLocals listSumExit) with
        | .br34 => (do
          let i39 ← Zig.callM (Zig.ptrProject i2 (·.elem 16 i32))
          let i40 ← pure (i39)
          Zig.store (α := Option (Zig.Ptr)) 8 i4 i40
          let i42 ← pure ((← get).i)
          let i43 ← Zig.add false i42 (1 : BitVec 32)
          modify (fun s => { s with i := i43 })
          pure .br10)
        | e => pure e)
      | e => pure e)
    else (do
      pure .br8)) : Zig.MM listSumLocals listSumExit) with
  | .br10 => (do
    pure .rep9)
  | e => pure e

def listSum (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s2 ← Zig.allocStack 96 8
  let s4 ← Zig.allocStack 8 8
  let e ← ((do
    let i2 ← pure (← get).pool
    Zig.storeUndef (Vector (Node) 6) 8 i2
    let i4 ← pure (← get).head
    Zig.store (α := Option (Zig.Ptr)) 8 i4 none
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (listSum.loop9 p0 p1 i2 i4) listSum.again9) : Zig.MM listSumLocals listSumExit) with
    | .br8 => (do
      modify (fun s => { s with link := i4 })
      match ← ((do
        Zig.loop (listSum.loop51 ) listSum.again51) : Zig.MM listSumLocals listSumExit) with
      | .br50 => (do
        modify (fun s => { s with s := (0 : BitVec 32) })
        modify (fun s => { s with k := (1 : BitVec 32) })
        let i80 ← Zig.load (Option (Zig.Ptr)) 8 i4
        modify (fun s => { s with it := i80 })
        match ← ((do
          Zig.loop (listSum.loop83 ) listSum.again83) : Zig.MM listSumLocals listSumExit) with
        | .br82 => (do
          let i105 ← pure ((← get).s)
          pure (.ret i105))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM listSumLocals listSumExit).run' { (default : listSumLocals) with pool := s2, head := s4 }
  Zig.free s2
  Zig.free s4
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure misalignedCheckedLocals where
  buf : Zig.Ptr
  deriving Inhabited

inductive misalignedCheckedExit where
  | ret (v : BitVec 32)
  | br23
  | br32

def misalignedChecked (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s2 ← Zig.allocStack 8 4
  let e ← ((do
    let i2 ← pure (← get).buf
    let i3 ← pure i2
    Zig.store (α := BitVec 8) 4 i3 (1 : BitVec 8)
    let i5 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (1 : BitVec 64)))
    Zig.store (α := BitVec 8) 1 i5 (2 : BitVec 8)
    let i7 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (2 : BitVec 64)))
    Zig.store (α := BitVec 8) 2 i7 (3 : BitVec 8)
    let i9 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (3 : BitVec 64)))
    Zig.store (α := BitVec 8) 1 i9 (4 : BitVec 8)
    let i11 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (4 : BitVec 64)))
    Zig.store (α := BitVec 8) 4 i11 (5 : BitVec 8)
    let i13 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (5 : BitVec 64)))
    Zig.store (α := BitVec 8) 1 i13 (6 : BitVec 8)
    let i15 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (6 : BitVec 64)))
    Zig.store (α := BitVec 8) 2 i15 (7 : BitVec 8)
    let i17 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (7 : BitVec 64)))
    Zig.store (α := BitVec 8) 1 i17 (8 : BitVec 8)
    let i19 ← pure (p0 &&& (1 : BitVec 32))
    let i20 ← pure (i19 ||| (1 : BitVec 32))
    let i21 ← Zig.intCast false false 64 i20
    let i22 ← pure (Zig.lt false i21 (8 : BitVec 64))
    match ← ((do
      if i22 then (do
        pure .br23)
      else (do
        throw .outOfBounds)) : Zig.MM misalignedCheckedLocals misalignedCheckedExit) with
    | .br23 => (do
      let i28 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 i21))
      let i29 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i28)))
      let i30 ← pure (i29 &&& (3 : BitVec 64))
      let i31 ← pure (i30 == (0 : BitVec 64))
      match ← ((do
        if i31 then (do
          pure .br32)
        else (do
          throw .panic)) : Zig.MM misalignedCheckedLocals misalignedCheckedExit) with
      | .br32 => (do
        let i37 ← Zig.callM (Zig.checkAlign 4 i28 >>= fun _ => pure i28)
        let i38 ← Zig.load (BitVec 32) 4 i37
        let i39 ← pure (Zig.addWrap i38 p1)
        pure (.ret i39))
      | e => pure e)
    | e => pure e) : Zig.MM misalignedCheckedLocals misalignedCheckedExit).run' { (default : misalignedCheckedLocals) with buf := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure misalignedUncheckedLocals where
  buf : Zig.Ptr
  deriving Inhabited

inductive misalignedUncheckedExit where
  | ret (v : BitVec 32)

def misalignedUnchecked (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s2 ← Zig.allocStack 8 4
  let e ← ((do
    let i2 ← pure (← get).buf
    let i3 ← pure i2
    Zig.store (α := BitVec 8) 4 i3 (1 : BitVec 8)
    let i5 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (1 : BitVec 64)))
    Zig.store (α := BitVec 8) 1 i5 (2 : BitVec 8)
    let i7 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (2 : BitVec 64)))
    Zig.store (α := BitVec 8) 2 i7 (3 : BitVec 8)
    let i9 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (3 : BitVec 64)))
    Zig.store (α := BitVec 8) 1 i9 (4 : BitVec 8)
    let i11 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (4 : BitVec 64)))
    Zig.store (α := BitVec 8) 4 i11 (5 : BitVec 8)
    let i13 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (5 : BitVec 64)))
    Zig.store (α := BitVec 8) 1 i13 (6 : BitVec 8)
    let i15 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (6 : BitVec 64)))
    Zig.store (α := BitVec 8) 2 i15 (7 : BitVec 8)
    let i17 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (7 : BitVec 64)))
    Zig.store (α := BitVec 8) 1 i17 (8 : BitVec 8)
    let i19 ← pure (p0 &&& (1 : BitVec 32))
    let i20 ← pure (i19 ||| (1 : BitVec 32))
    let i21 ← Zig.intCast false false 64 i20
    let i22 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 i21))
    let i23 ← Zig.callM (Zig.checkAlign 4 i22 >>= fun _ => pure i22)
    let i24 ← Zig.load (BitVec 32) 4 i23
    let i25 ← pure (Zig.addWrap i24 p1)
    pure (.ret i25)) : Zig.MM misalignedUncheckedLocals misalignedUncheckedExit).run' { (default : misalignedUncheckedLocals) with buf := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v

structure visitLocals where
  deriving Inhabited

inductive visitExit where
  | ret
  | br5

def visit (p0 : Option (Zig.Ptr)) (p1 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.optPtrAddr p0)))
    let i3 ← pure (i2 &&& (3 : BitVec 64))
    let i4 ← pure (i3 == (0 : BitVec 64))
    match ← ((do
      if i4 then (do
        pure .br5)
      else (do
        throw .panic)) : Zig.MM visitLocals visitExit) with
    | .br5 => (do
      let i10 ← pure (Zig.ptrOfOptional p0)
      let i11 ← pure i10
      let i12 ← Zig.load (BitVec 32) 4 i11
      let i13 ← Zig.callM (Zig.ptrProject i10 (·.add 4))
      let i14 ← Zig.load (BitVec 32) 4 i13
      let i15 ← pure (Zig.mulWrap p1 i14)
      let i16 ← pure (Zig.addWrap i12 i15)
      Zig.store (α := BitVec 32) 4 i11 i16
      pure .ret)
    | e => pure e) : Zig.MM visitLocals visitExit).run' (default : visitLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure opaqueContextLocals where
  c : Zig.Ptr
  i : BitVec 32
  deriving Inhabited

inductive opaqueContextExit where
  | ret (v : BitVec 32)
  | br11
  | br9
  | rep10

def opaqueContext.again10 : opaqueContextExit → Bool
  | .rep10 => true
  | _ => false

def opaqueContext.loop10 (p0 : BitVec 32) (i2 : Zig.Ptr) : Zig.MM opaqueContextLocals opaqueContextExit := do
  match ← ((do
    let i12 ← pure ((← get).i)
    let i13 ← pure (Zig.lt false i12 (4 : BitVec 32))
    if i13 then (do
      let i15 ← pure (i2)
      let i16 ← pure ((← get).i)
      let i17 ← pure (Zig.addWrap p0 i16)
      let _i18 ← Zig.callM (visit i15 i17)
      let i19 ← pure ((← get).i)
      let i20 ← Zig.add false i19 (1 : BitVec 32)
      modify (fun s => { s with i := i20 })
      pure .br11)
    else (do
      pure .br9)) : Zig.MM opaqueContextLocals opaqueContextExit) with
  | .br11 => (do
    pure .rep10)
  | e => pure e

def opaqueContext (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s2 ← Zig.allocStack 8 4
  let e ← ((do
    let i2 ← pure (← get).c
    let i3 ← pure (p1 &&& (7 : BitVec 32))
    let i4 ← Zig.add false i3 (1 : BitVec 32)
    let i5 ← pure { sum := (0 : BitVec 32), scale := i4 : Ctx }
    Zig.store (α := Ctx) 4 i2 i5
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (opaqueContext.loop10 p0 i2) opaqueContext.again10) : Zig.MM opaqueContextLocals opaqueContextExit) with
    | .br9 => (do
      let i25 ← pure i2
      let i26 ← Zig.load (BitVec 32) 4 i25
      pure (.ret i26))
    | e => pure e) : Zig.MM opaqueContextLocals opaqueContextExit).run' { (default : opaqueContextLocals) with c := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure pointerAsIntLocals where
  w : Zig.Ptr
  p : Zig.Ptr
  deriving Inhabited

inductive pointerAsIntExit where
  | ret (v : BitVec 32)

def pointerAsInt (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s2 ← Zig.allocStack 4 4
  let s5 ← Zig.allocStack 8 8
  let e ← ((do
    let i2 ← pure (← get).w
    let i3 ← pure (p0 ^^^ p1)
    Zig.store (α := BitVec 32) 4 i2 i3
    let i5 ← pure (← get).p
    Zig.store (α := Zig.Ptr) 8 i5 i2
    let i7 ← pure (i5)
    let i8 ← Zig.load (BitVec 64) 8 i7
    let i9 ← pure (Zig.trunc 32 i8)
    pure (.ret i9)) : Zig.MM pointerAsIntLocals pointerAsIntExit).run' { (default : pointerAsIntLocals) with w := s2, p := s5 }
  Zig.free s2
  Zig.free s5
  match e with
  | .ret v => pure v

structure readThroughLocals where
  deriving Inhabited

inductive readThroughExit where
  | ret (v : BitVec 32)
  | br4

def readThrough (p0 : Option (Zig.Ptr)) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.optPtrAddr p0)))
    let i2 ← pure (i1 &&& (3 : BitVec 64))
    let i3 ← pure (i2 == (0 : BitVec 64))
    match ← ((do
      if i3 then (do
        pure .br4)
      else (do
        throw .panic)) : Zig.MM readThroughLocals readThroughExit) with
    | .br4 => (do
      let i9 ← pure (Zig.ptrOfOptional p0)
      let i10 ← Zig.load (BitVec 32) 4 i9
      pure (.ret i10))
    | e => pure e) : Zig.MM readThroughLocals readThroughExit).run' (default : readThroughLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure treeSumLocals where
  deriving Inhabited

inductive treeSumExit where
  | ret (v : BitVec 32)
  | br2

mutual

def treeSum (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  Zig.enterFrame 0
  let e ← ((do
    match ← ((do
      let i3 ← Zig.callM (Zig.ptrIsNull p0)
      if i3 then (do
        pure (.ret (0 : BitVec 32)))
      else (do
        pure .br2)) : Zig.MM treeSumLocals treeSumExit) with
    | .br2 => (do
      let i7 ← pure p0
      let i8 ← Zig.load (BitVec 32) 8 i7
      let i9 ← pure (Zig.mulWrap i8 p1)
      let i10 ← Zig.callM (Zig.ptrProject p0 (·.add 8))
      let i11 ← (letI : Zig.Enc (Zig.Ptr) := Zig.nullablePtrEnc; Zig.load (Zig.Ptr) 8 i10)
      let i12 ← Zig.add false p1 (1 : BitVec 32)
      let i13 ← Zig.callM (treeSum i11 i12)
      let i14 ← pure (Zig.addWrap i9 i13)
      let i15 ← Zig.callM (Zig.ptrProject p0 (·.add 16))
      let i16 ← (letI : Zig.Enc (Zig.Ptr) := Zig.nullablePtrEnc; Zig.load (Zig.Ptr) 8 i15)
      let i17 ← Zig.add false p1 (1 : BitVec 32)
      let i18 ← Zig.callM (treeSum i16 i17)
      let i19 ← pure (Zig.addWrap i14 i18)
      pure (.ret i19))
    | e => pure e) : Zig.MM treeSumLocals treeSumExit).run' (default : treeSumLocals)
  Zig.leaveFrame 0
  match e with
  | .ret v => pure v
  | _ => throw .panic
partial_fixpoint

end

structure treeInsertLocals where
  nodes : Zig.Ptr
  root : Zig.Ptr
  i : BitVec 32
  slot : Zig.Ptr
  deriving Inhabited

inductive treeInsertExit where
  | ret (v : BitVec 32)
  | br22
  | br44 (v : Zig.Ptr)
  | br39
  | br37
  | br67
  | br14
  | br10
  | br8
  | rep38
  | rep9

def treeInsert.again38 : treeInsertExit → Bool
  | .rep38 => true
  | _ => false

def treeInsert.again9 : treeInsertExit → Bool
  | .rep9 => true
  | _ => false

def treeInsert.loop38 (i18 : BitVec 32) : Zig.MM treeInsertLocals treeInsertExit := do
  match ← ((do
    let i40 ← pure ((← get).slot)
    let i41 ← (letI : Zig.Enc (Zig.Ptr) := Zig.nullablePtrEnc; Zig.load (Zig.Ptr) 8 i40)
    let i42 ← Zig.callM (do pure (!(← Zig.ptrIsNull i41)))
    if i42 then (do
      match ← ((do
        let i45 ← pure ((← get).slot)
        let i46 ← (letI : Zig.Enc (Zig.Ptr) := Zig.nullablePtrEnc; Zig.load (Zig.Ptr) 8 i45)
        let i47 ← pure i46
        let i48 ← Zig.load (BitVec 32) 8 i47
        let i49 ← pure (Zig.lt false i18 i48)
        if i49 then (do
          let i51 ← pure ((← get).slot)
          let i52 ← (letI : Zig.Enc (Zig.Ptr) := Zig.nullablePtrEnc; Zig.load (Zig.Ptr) 8 i51)
          let i53 ← Zig.callM (Zig.ptrProject i52 (·.add 8))
          pure (.br44 i53))
        else (do
          let i55 ← pure ((← get).slot)
          let i56 ← (letI : Zig.Enc (Zig.Ptr) := Zig.nullablePtrEnc; Zig.load (Zig.Ptr) 8 i55)
          let i57 ← Zig.callM (Zig.ptrProject i56 (·.add 16))
          pure (.br44 i57))) : Zig.MM treeInsertLocals treeInsertExit) with
      | .br44 v44 => (do
        modify (fun s => { s with slot := v44 })
        pure .br39)
      | e => pure e)
    else (do
      pure .br37)) : Zig.MM treeInsertLocals treeInsertExit) with
  | .br39 => (do
    pure .rep38)
  | e => pure e

def treeInsert.loop9 (p0 : BitVec 32) (p1 : BitVec 32) (i2 : Zig.Ptr) (i4 : Zig.Ptr) : Zig.MM treeInsertLocals treeInsertExit := do
  match ← ((do
    let i11 ← pure ((← get).i)
    let i12 ← pure (Zig.lt false i11 (5 : BitVec 32))
    if i12 then (do
      match ← ((do
        let i15 ← pure ((← get).i)
        let i16 ← pure (Zig.mulWrap i15 p1)
        let i17 ← pure (Zig.addWrap p0 i16)
        let i18 ← Zig.rem false i17 (97 : BitVec 32)
        let i19 ← pure ((← get).i)
        let i20 ← Zig.intCast false false 64 i19
        let i21 ← pure (Zig.lt false i20 (5 : BitVec 64))
        match ← ((do
          if i21 then (do
            pure .br22)
          else (do
            throw .outOfBounds)) : Zig.MM treeInsertLocals treeInsertExit) with
        | .br22 => (do
          let i27 ← Zig.callM (Zig.ptrProject i2 (·.elem 24 i20))
          let i28 ← pure i27
          Zig.store (α := BitVec 32) 8 i28 i18
          let i30 ← Zig.callM (Zig.ptrProject i27 (·.add 8))
          (letI : Zig.Enc (Zig.Ptr) := Zig.nullablePtrEnc; Zig.store (α := Zig.Ptr) 8 i30 Zig.Ptr.null)
          let i32 ← Zig.callM (Zig.ptrProject i27 (·.add 16))
          (letI : Zig.Enc (Zig.Ptr) := Zig.nullablePtrEnc; Zig.store (α := Zig.Ptr) 8 i32 Zig.Ptr.null)
          let i35 ← pure (i4)
          modify (fun s => { s with slot := i35 })
          match ← ((do
            Zig.loop (treeInsert.loop38 i18) treeInsert.again38) : Zig.MM treeInsertLocals treeInsertExit) with
          | .br37 => (do
            let i63 ← pure ((← get).slot)
            let i64 ← pure ((← get).i)
            let i65 ← Zig.intCast false false 64 i64
            let i66 ← pure (Zig.lt false i65 (5 : BitVec 64))
            match ← ((do
              if i66 then (do
                pure .br67)
              else (do
                throw .outOfBounds)) : Zig.MM treeInsertLocals treeInsertExit) with
            | .br67 => (do
              let i72 ← Zig.callM (Zig.ptrProject i2 (·.elem 24 i65))
              let i73 ← pure (i72)
              (letI : Zig.Enc (Zig.Ptr) := Zig.nullablePtrEnc; Zig.store (α := Zig.Ptr) 8 i63 i73)
              pure .br14)
            | e => pure e)
          | e => pure e)
        | e => pure e) : Zig.MM treeInsertLocals treeInsertExit) with
      | .br14 => (do
        let i76 ← pure ((← get).i)
        let i77 ← Zig.add false i76 (1 : BitVec 32)
        modify (fun s => { s with i := i77 })
        pure .br10)
      | e => pure e)
    else (do
      pure .br8)) : Zig.MM treeInsertLocals treeInsertExit) with
  | .br10 => (do
    pure .rep9)
  | e => pure e

def treeInsert (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s2 ← Zig.allocStack 120 8
  let s4 ← Zig.allocStack 8 8
  let e ← ((do
    let i2 ← pure (← get).nodes
    Zig.storeUndef (Vector (Tree) 5) 8 i2
    let i4 ← pure (← get).root
    (letI : Zig.Enc (Zig.Ptr) := Zig.nullablePtrEnc; Zig.store (α := Zig.Ptr) 8 i4 Zig.Ptr.null)
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (treeInsert.loop9 p0 p1 i2 i4) treeInsert.again9) : Zig.MM treeInsertLocals treeInsertExit) with
    | .br8 => (do
      let i82 ← (letI : Zig.Enc (Zig.Ptr) := Zig.nullablePtrEnc; Zig.load (Zig.Ptr) 8 i4)
      let i83 ← Zig.callM (treeSum i82 (1 : BitVec 32))
      pure (.ret i83))
    | e => pure e) : Zig.MM treeInsertLocals treeInsertExit).run' { (default : treeInsertLocals) with nodes := s2, root := s4 }
  Zig.free s2
  Zig.free s4
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure voidRoundTripLocals where
  w : Zig.Ptr
  pair : Zig.Ptr
  deriving Inhabited

inductive voidRoundTripExit where
  | ret (v : BitVec 32)
  | br9

def voidRoundTrip (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s2 ← Zig.allocStack 4 4
  let s18 ← Zig.allocStack 8 4
  let e ← ((do
    let i2 ← pure (← get).w
    let i3 ← pure (p0 ^^^ p1)
    Zig.store (α := BitVec 32) 4 i2 i3
    let i5 ← pure (i2)
    let i6 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.optPtrAddr i5)))
    let i7 ← pure (i6 &&& (3 : BitVec 64))
    let i8 ← pure (i7 == (0 : BitVec 64))
    match ← ((do
      if i8 then (do
        pure .br9)
      else (do
        throw .panic)) : Zig.MM voidRoundTripLocals voidRoundTripExit) with
    | .br9 => (do
      let i14 ← pure (Zig.ptrOfOptional i5)
      let i15 ← Zig.load (BitVec 32) 4 i14
      let i16 ← pure (Zig.addWrap i15 (7 : BitVec 32))
      Zig.store (α := BitVec 32) 4 i14 i16
      let i18 ← pure (← get).pair
      let i19 ← pure (#v[p0, p1] : Vector (BitVec 32) 2)
      Zig.store (α := Vector (BitVec 32) 2) 4 i18 i19
      let i21 ← Zig.callM (Zig.ptrProject i18 (·.elem 4 (1 : BitVec 64)))
      let i22 ← pure (i21)
      let i23 ← pure (i2)
      let i24 ← Zig.callM (readThrough i23)
      let i25 ← Zig.callM (readThrough i22)
      let i26 ← pure (Zig.mulWrap i25 (3 : BitVec 32))
      let i27 ← pure (Zig.addWrap i24 i26)
      pure (.ret i27))
    | e => pure e) : Zig.MM voidRoundTripLocals voidRoundTripExit).run' { (default : voidRoundTripLocals) with w := s2, pair := s18 }
  Zig.free s2
  Zig.free s18
  match e with
  | .ret v => pure v
  | _ => throw .panic

end PtrCasts