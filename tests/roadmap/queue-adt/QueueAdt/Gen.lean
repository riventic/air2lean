-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.1"}}
import ZigLean


namespace QueueAdt

structure Ring where
  items : Zig.Slice
  head : BitVec 64
  len : BitVec 64
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Ring where
  size := 32
  align := 8
  encode v := Zig.Enc.fields 32 [(0, Zig.Enc.encode v.items), (16, Zig.Enc.encode v.head), (24, Zig.Enc.encode v.len)]
  decode bs := do pure { items := ← Zig.Enc.decodeAt bs 0, head := ← Zig.Enc.decodeAt bs 16, len := ← Zig.Enc.decodeAt bs 24 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure Ring_countLocals where
  deriving Inhabited

inductive Ring_countExit where
  | ret (v : BitVec 64)

def Ring_count (p0 : Zig.Ptr) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.add 24))
    let i2 ← Zig.load (BitVec 64) 8 i1
    pure (.ret i2)) : Zig.MM Ring_countLocals Ring_countExit).run' (default : Ring_countLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Ring_count

structure Ring_initLocals where
  local1 : Ring
  deriving Inhabited

inductive Ring_initExit where
  | ret (v : Ring)

def Ring_init (p0 : Zig.Slice) : Zig.MemM (Ring) := do
  let e ← ((do
    modify (fun s => { s with local1 := { s.local1 with items := p0 } })
    modify (fun s => { s with local1 := { s.local1 with head := (0 : BitVec 64) } })
    modify (fun s => { s with local1 := { s.local1 with len := (0 : BitVec 64) } })
    pure (.ret (← get).local1)) : Zig.MM Ring_initLocals Ring_initExit).run' (default : Ring_initLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Ring_init

structure Ring_popLocals where
  deriving Inhabited

inductive Ring_popExit where
  | ret (v : Option (BitVec 32))
  | br1
  | br15
  | br25 (v : BitVec 64)

def Ring_pop (p0 : Zig.Ptr) : Zig.MemM (Option (BitVec 32)) := do
  let e ← ((do
    match ← ((do
      let i2 ← Zig.callM (Zig.ptrProject p0 (·.add 24))
      let i3 ← Zig.load (BitVec 64) 8 i2
      let i4 ← pure (i3)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret none))
      else (do
        pure .br1)) : Zig.MM Ring_popLocals Ring_popExit) with
    | .br1 => (do
      let i9 ← pure p0
      let i10 ← Zig.callM (Zig.ptrProject p0 (·.add 16))
      let i11 ← Zig.load (BitVec 64) 8 i10
      let i12 ← Zig.load (Zig.Slice) 8 i9
      let i13 ← pure i12.len
      let i14 ← pure (Zig.lt false i11 i13)
      match ← ((do
        if i14 then (do
          pure .br15)
        else (do
          throw .outOfBounds)) : Zig.MM Ring_popLocals Ring_popExit) with
      | .br15 => (do
        let i20 ← Zig.callM (Zig.checkIndex i12.len i11 >>= fun _ => Zig.load (BitVec 32) 4 (i12.ptr.elem 4 i11))
        let i21 ← Zig.callM (Zig.ptrProject p0 (·.add 16))
        let i22 ← Zig.load (BitVec 64) 8 i21
        let i23 ← Zig.add false i22 (1 : BitVec 64)
        let i24 ← Zig.callM (Zig.ptrProject p0 (·.add 16))
        match ← ((do
          let i26 ← pure p0
          let i27 ← Zig.callM (Zig.ptrProject i26 (·.add 8))
          let i28 ← Zig.load (BitVec 64) 8 i27
          let i29 ← pure (i23)
          let i30 ← pure (i28)
          let i31 ← pure (i29 == i30)
          if i31 then (do
            pure (.br25 (0 : BitVec 64)))
          else (do
            pure (.br25 i23))) : Zig.MM Ring_popLocals Ring_popExit) with
        | .br25 v25 => (do
          Zig.store (α := BitVec 64) 8 i24 v25
          let i36 ← Zig.callM (Zig.ptrProject p0 (·.add 24))
          let i37 ← Zig.load (BitVec 64) 8 i36
          let i38 ← Zig.sub false i37 (1 : BitVec 64)
          Zig.store (α := BitVec 64) 8 i36 i38
          let i40 ← pure (some i20)
          pure (.ret i40))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM Ring_popLocals Ring_popExit).run' (default : Ring_popLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Ring_pop

structure Ring_pushLocals where
  deriving Inhabited

inductive Ring_pushExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br5
  | br17 (v : BitVec 64)
  | br38

def Ring_push (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.callM (Zig.ptrProject i2 (·.add 8))
    let i4 ← Zig.load (BitVec 64) 8 i3
    match ← ((do
      let i6 ← Zig.callM (Zig.ptrProject p0 (·.add 24))
      let i7 ← Zig.load (BitVec 64) 8 i6
      let i8 ← pure (i7)
      let i9 ← pure (i4)
      let i10 ← pure (i8 == i9)
      if i10 then (do
        pure (.ret (.error "Full" : Except Zig.ErrName (Unit))))
      else (do
        pure .br5)) : Zig.MM Ring_pushLocals Ring_pushExit) with
    | .br5 => (do
      let i14 ← Zig.callM (Zig.ptrProject p0 (·.add 16))
      let i15 ← Zig.load (BitVec 64) 8 i14
      let i16 ← Zig.sub false i4 i15
      match ← ((do
        let i18 ← Zig.callM (Zig.ptrProject p0 (·.add 24))
        let i19 ← Zig.load (BitVec 64) 8 i18
        let i20 ← pure (i19)
        let i21 ← pure (i16)
        let i22 ← pure (Zig.lt false i20 i21)
        if i22 then (do
          let i24 ← Zig.callM (Zig.ptrProject p0 (·.add 16))
          let i25 ← Zig.load (BitVec 64) 8 i24
          let i26 ← Zig.callM (Zig.ptrProject p0 (·.add 24))
          let i27 ← Zig.load (BitVec 64) 8 i26
          let i28 ← Zig.add false i25 i27
          pure (.br17 i28))
        else (do
          let i30 ← Zig.callM (Zig.ptrProject p0 (·.add 24))
          let i31 ← Zig.load (BitVec 64) 8 i30
          let i32 ← Zig.sub false i31 i16
          pure (.br17 i32))) : Zig.MM Ring_pushLocals Ring_pushExit) with
      | .br17 v17 => (do
        let i34 ← pure p0
        let i35 ← Zig.load (Zig.Slice) 8 i34
        let i36 ← pure i35.len
        let i37 ← pure (Zig.lt false v17 i36)
        match ← ((do
          if i37 then (do
            pure .br38)
          else (do
            throw .outOfBounds)) : Zig.MM Ring_pushLocals Ring_pushExit) with
        | .br38 => (do
          let i43 ← Zig.callM (Zig.checkIndex i35.len v17) >>= fun _ => Zig.callM (Zig.ptrProject i35.ptr (·.elem 4 v17))
          Zig.store (α := BitVec 32) 4 i43 p1
          let i45 ← Zig.callM (Zig.ptrProject p0 (·.add 24))
          let i46 ← Zig.load (BitVec 64) 8 i45
          let i47 ← Zig.add false i46 (1 : BitVec 64)
          Zig.store (α := BitVec 64) 8 i45 i47
          pure (.ret (.ok () : Except Zig.ErrName (Unit))))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM Ring_pushLocals Ring_pushExit).run' (default : Ring_pushLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Ring_push

structure pushAllLocals where
  n : BitVec 64
  deriving Inhabited

inductive pushAllExit where
  | ret (v : BitVec 64)
  | br17
  | br13
  | br4
  | br6
  | rep5

def pushAll.again5 : pushAllExit → Bool
  | .rep5 => true
  | _ => false

def pushAll.loop5 (p0 : Zig.Ptr) (p1 : Zig.Slice) : Zig.MM pushAllLocals pushAllExit := do
  Zig.callM Zig.tick
  match ← ((do
    let i7 ← pure ((← get).n)
    let i8 ← pure p1.len
    let i9 ← pure (i7)
    let i10 ← pure (i8)
    let i11 ← pure (Zig.lt false i9 i10)
    if i11 then (do
      match ← ((do
        let i14 ← pure ((← get).n)
        let i15 ← pure p1.len
        let i16 ← pure (Zig.lt false i14 i15)
        match ← ((do
          if i16 then (do
            pure .br17)
          else (do
            throw .outOfBounds)) : Zig.MM pushAllLocals pushAllExit) with
        | .br17 => (do
          let i22 ← Zig.callM (Zig.checkIndex p1.len i14 >>= fun _ => Zig.load (BitVec 32) 4 (p1.ptr.elem 4 i14))
          let i23 ← Zig.callM (Ring_push p0 i22)
          let i24 ← pure (Zig.isNonErr i23)
          if i24 then (do
            pure .br13)
          else (do
            let _i27 ← Zig.callR (Zig.unwrapErr i23)
            pure .br4))
        | e => pure e) : Zig.MM pushAllLocals pushAllExit) with
      | .br13 => (do
        let i29 ← pure ((← get).n)
        let i30 ← Zig.add false i29 (1 : BitVec 64)
        modify (fun s => { s with n := i30 })
        pure .br6)
      | e => pure e)
    else (do
      pure .br4)) : Zig.MM pushAllLocals pushAllExit) with
  | .br6 => (do
    pure .rep5)
  | e => pure e

def pushAll (p0 : Zig.Ptr) (p1 : Zig.Slice) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with n := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (pushAll.loop5 p0 p1) pushAll.again5) : Zig.MM pushAllLocals pushAllExit) with
    | .br4 => (do
      let i35 ← pure ((← get).n)
      pure (.ret i35))
    | e => pure e) : Zig.MM pushAllLocals pushAllExit).run' (default : pushAllLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] pushAll.loop5 pushAll

structure rotateLocals where
  deriving Inhabited

inductive rotateExit where
  | ret
  | br6
  | br1

def rotate (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    match ← ((do
      let i2 ← Zig.callM (Ring_pop p0)
      let i3 ← pure ((i2).isSome)
      if i3 then (do
        let i5 ← Zig.optPayload i2
        match ← ((do
          let i7 ← Zig.callM (Ring_push p0 i5)
          let i8 ← pure (Zig.isNonErr i7)
          if i8 then (do
            pure .br6)
          else (do
            let i11 ← Zig.callR (Zig.unwrapErr i7)
            let _i12 ← pure (i11)
            throw .panic)) : Zig.MM rotateLocals rotateExit) with
        | .br6 => (do
          pure .br1)
        | e => pure e)
      else (do
        pure .br1)) : Zig.MM rotateLocals rotateExit) with
    | .br1 => (do
      pure .ret)
    | e => pure e) : Zig.MM rotateLocals rotateExit).run' (default : rotateLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] rotate

end QueueAdt