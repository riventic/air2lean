-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace ExternCalls.Abi

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: a constant
  (Zig.Enc.encode ((#v[(97 : BitVec 8), (98 : BitVec 8), (105 : BitVec 8), (32 : BitVec 8), (99 : BitVec 8), (97 : BitVec 8), (108 : BitVec 8), (108 : BitVec 8), (115 : BitVec 8), (0 : BitVec 8)] : Vector (BitVec 8) 10) : Vector (BitVec 8) 10), 1, .constGlobal),
  -- 1: a constant
  (Zig.Enc.encode ((#v[(104 : BitVec 8), (101 : BitVec 8), (108 : BitVec 8), (108 : BitVec 8), (111 : BitVec 8), (0 : BitVec 8)] : Vector (BitVec 8) 6) : Vector (BitVec 8) 6), 1, .constGlobal)]

structure abi_ref_fillLocals where
  local3 : Zig.Ptr
  i : BitVec 64
  deriving Inhabited

inductive abi_ref_fillExit where
  | ret (v : Option (Zig.Ptr))
  | br17
  | br10
  | br8
  | rep9

def abi_ref_fill.again9 : abi_ref_fillExit → Bool
  | .rep9 => true
  | _ => false

def abi_ref_fill.loop9 (p1 : BitVec 8) (p2 : BitVec 64) (i5 : Zig.Ptr) : Zig.MM abi_ref_fillLocals abi_ref_fillExit := do
  match ← ((do
    let i11 ← pure ((← get).i)
    let i12 ← pure (i11)
    let i13 ← pure (p2)
    let i14 ← pure (Zig.lt false i12 i13)
    if i14 then (do
      let i16 ← (·.isSome) <$> Zig.load (Option (Zig.Ptr)) 8 i5
      match ← ((do
        if i16 then (do
          pure .br17)
        else (do
          throw .panic)) : Zig.MM abi_ref_fillLocals abi_ref_fillExit) with
      | .br17 => (do
        let i22 ← pure i5
        let i23 ← pure ((← get).i)
        let i24 ← Zig.load (Zig.Ptr) 8 i22
        let i25 ← Zig.callM (Zig.ptrProject i24 (·.elem 1 i23))
        Zig.store (α := BitVec 8) 1 i25 p1
        let i27 ← pure ((← get).i)
        let i28 ← Zig.add false i27 (1 : BitVec 64)
        modify (fun s => { s with i := i28 })
        pure .br10)
      | e => pure e)
    else (do
      pure .br8)) : Zig.MM abi_ref_fillLocals abi_ref_fillExit) with
  | .br10 => (do
    pure .rep9)
  | e => pure e

def abi_ref_fill (p0 : Option (Zig.Ptr)) (p1 : BitVec 8) (p2 : BitVec 64) : Zig.MemM (Option (Zig.Ptr)) := do
  let s3 ← Zig.allocStack 8 8
  let e ← ((do
    let i3 ← pure (← get).local3
    Zig.store (α := Option (Zig.Ptr)) 8 i3 p0
    let i5 ← pure (i3)
    modify (fun s => { s with i := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (abi_ref_fill.loop9 p1 p2 i5) abi_ref_fill.again9) : Zig.MM abi_ref_fillLocals abi_ref_fillExit) with
    | .br8 => (do
      pure (.ret p0))
    | e => pure e) : Zig.MM abi_ref_fillLocals abi_ref_fillExit).run' { (default : abi_ref_fillLocals) with local3 := s3 }
  Zig.free s3
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure abi_abi_fill_abi_calls_fillSumLocals where
  deriving Inhabited

inductive abi_abi_fill_abi_calls_fillSumExit where
  | ret (v : Option (Zig.Ptr))

def abi_abi_fill_abi_calls_fillSum (p0 : Option (Zig.Ptr)) (p1 : BitVec 32) (p2 : BitVec 64) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    let i3 ← pure (p0)
    let i4 ← pure (Zig.ge true p1 (0 : BitVec 32))
    let i5 ← pure (Zig.le true p1 (255 : BitVec 32))
    let i6 ← pure (i4 && i5)
    if i6 then (do
      let i7 ← Zig.intCast true false 8 p1
      let i8 ← Zig.callM (abi_ref_fill i3 i7 p2)
      let i9 ← pure (i8)
      pure (.ret i9))
    else (do
      throw .illegal)) : Zig.MM abi_abi_fill_abi_calls_fillSumLocals abi_abi_fill_abi_calls_fillSumExit).run' (default : abi_abi_fill_abi_calls_fillSumLocals)
  match e with
  | .ret v => pure v

structure abi_ref_firstLocals where
  deriving Inhabited

inductive abi_ref_firstExit where
  | ret (v : BitVec 8)
  | br1 (v : Zig.Ptr)

def abi_ref_first (p0 : Option (Zig.Ptr)) : Zig.MemM (BitVec 8) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure ((p0).isSome)
      if i2 then (do
        let i4 ← Zig.optPayload p0
        pure (.br1 i4))
      else (do
        pure (.ret (0 : BitVec 8)))) : Zig.MM abi_ref_firstLocals abi_ref_firstExit) with
    | .br1 v1 => (do
      let i7 ← pure (v1)
      let i8 ← Zig.callM (Zig.load (BitVec 8) 1 (i7.elem 1 (0 : BitVec 64)))
      pure (.ret i8))
    | e => pure e) : Zig.MM abi_ref_firstLocals abi_ref_firstExit).run' (default : abi_ref_firstLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure abi_abi_first_abi_calls_firstAtLocals where
  deriving Inhabited

inductive abi_abi_first_abi_calls_firstAtExit where
  | ret (v : BitVec 8)

def abi_abi_first_abi_calls_firstAt (p0 : Option (Zig.Ptr)) : Zig.MemM (BitVec 8) := do
  let e ← ((do
    let i1 ← pure ((p0).isSome)
    if i1 then (do
      let i2 ← Zig.optPayload p0
      let i6 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i2)))
      let i7 ← pure (i6 &&& (15 : BitVec 64))
      let i8 ← pure (i7 == (0 : BitVec 64))
      if i8 then (do
        let i3 ← pure (p0)
        let i4 ← Zig.callM (abi_ref_first i3)
        pure (.ret i4))
      else (do
        throw .illegal))
    else (do
      let i11 ← pure (p0)
      let i12 ← Zig.callM (abi_ref_first i11)
      pure (.ret i12))) : Zig.MM abi_abi_first_abi_calls_firstAtLocals abi_abi_first_abi_calls_firstAtExit).run' (default : abi_abi_first_abi_calls_firstAtLocals)
  match e with
  | .ret v => pure v

structure abi_ref_lenLocals where
  i : BitVec 64
  deriving Inhabited

inductive abi_ref_lenExit where
  | ret (v : BitVec 64)
  | br5
  | br3
  | rep4

def abi_ref_len.again4 : abi_ref_lenExit → Bool
  | .rep4 => true
  | _ => false

def abi_ref_len.loop4 (p0 : Zig.Ptr) : Zig.MM abi_ref_lenLocals abi_ref_lenExit := do
  match ← ((do
    let i6 ← pure ((← get).i)
    let i7 ← Zig.callM (Zig.load (BitVec 8) 1 (p0.elem 1 i6))
    let i8 ← pure (i7)
    let i9 ← pure (i8 != (0 : BitVec 8))
    if i9 then (do
      let i11 ← pure ((← get).i)
      let i12 ← Zig.add false i11 (1 : BitVec 64)
      modify (fun s => { s with i := i12 })
      pure .br5)
    else (do
      pure .br3)) : Zig.MM abi_ref_lenLocals abi_ref_lenExit) with
  | .br5 => (do
    pure .rep4)
  | e => pure e

def abi_ref_len (p0 : Zig.Ptr) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (abi_ref_len.loop4 p0) abi_ref_len.again4) : Zig.MM abi_ref_lenLocals abi_ref_lenExit) with
    | .br3 => (do
      let i17 ← pure ((← get).i)
      pure (.ret i17))
    | e => pure e) : Zig.MM abi_ref_lenLocals abi_ref_lenExit).run' (default : abi_ref_lenLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure abi_abi_len_abi_calls_lenOfLocals where
  deriving Inhabited

inductive abi_abi_len_abi_calls_lenOfExit where
  | ret (v : BitVec 64)

def abi_abi_len_abi_calls_lenOf (p0 : Zig.Ptr) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
    let i2 ← pure (i1 != (0 : BitVec 64))
    if i2 then (do
      let i3 ← Zig.callM (Zig.ptrRequireNonNull p0)
      let i4 ← Zig.callM (abi_ref_len i3)
      pure (.ret i4))
    else (do
      throw .illegal)) : Zig.MM abi_abi_len_abi_calls_lenOfLocals abi_abi_len_abi_calls_lenOfExit).run' (default : abi_abi_len_abi_calls_lenOfLocals)
  match e with
  | .ret v => pure v

structure fillSumLocals where
  buf : Zig.Ptr
  sum : BitVec 32
  local15 : BitVec 64
  deriving Inhabited

inductive fillSumExit where
  | ret (v : BitVec 32)
  | br4 (v : BitVec 64)
  | br21
  | br18
  | rep19

def fillSum.again19 : fillSumExit → Bool
  | .rep19 => true
  | _ => false

def fillSum.loop19 (i17 : Vector (BitVec 8) 16) : Zig.MM fillSumLocals fillSumExit := do
  let i20 ← pure ((← get).local15)
  match ← ((do
    let i22 ← pure (i20)
    let i23 ← pure (Zig.lt false i22 (16 : BitVec 64))
    if i23 then (do
      let i25 ← Zig.callR (Zig.vindex i17 i20)
      let i26 ← pure ((← get).sum)
      let i27 ← Zig.intCast false false 32 i25
      let i28 ← Zig.add false i26 i27
      modify (fun s => { s with sum := i28 })
      pure .br21)
    else (do
      pure .br18)) : Zig.MM fillSumLocals fillSumExit) with
  | .br21 => (do
    let i32 ← Zig.add false i20 (1 : BitVec 64)
    modify (fun s => { s with local15 := i32 })
    pure .rep19)
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
      let i11 ← pure (some i10)
      let _i12 ← Zig.callM (abi_abi_fill_abi_calls_fillSum i11 p1 v4)
      modify (fun s => { s with sum := (0 : BitVec 32) })
      modify (fun s => { s with local15 := (0 : BitVec 64) })
      let i17 ← Zig.load (Vector (BitVec 8) 16) 1 i2
      match ← ((do
        Zig.loop (fillSum.loop19 i17) fillSum.again19) : Zig.MM fillSumLocals fillSumExit) with
      | .br18 => (do
        let i35 ← pure ((← get).sum)
        pure (.ret i35))
      | e => pure e)
    | e => pure e) : Zig.MM fillSumLocals fillSumExit).run' { (default : fillSumLocals) with buf := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure firstAtLocals where
  buf : Zig.Ptr
  local3 : BitVec 64
  deriving Inhabited

inductive firstAtExit where
  | ret (v : BitVec 8)
  | br8
  | br5
  | br26
  | br21 (v : Option (Zig.Ptr))
  | rep6

def firstAt.again6 : firstAtExit → Bool
  | .rep6 => true
  | _ => false

def firstAt.loop6 (i1 : Zig.Ptr) : Zig.MM firstAtLocals firstAtExit := do
  let i7 ← pure ((← get).local3)
  match ← ((do
    let i9 ← pure (i7)
    let i10 ← pure (Zig.lt false i9 (32 : BitVec 64))
    if i10 then (do
      let i12 ← Zig.callM (Zig.ptrProject i1 (·.elem 1 i7))
      let i13 ← Zig.add false i7 (1 : BitVec 64)
      let i14 ← Zig.intCast false false 8 i13
      Zig.store (α := BitVec 8) 1 i12 i14
      pure .br8)
    else (do
      pure .br5)) : Zig.MM firstAtLocals firstAtExit) with
  | .br8 => (do
    let i18 ← Zig.add false i7 (1 : BitVec 64)
    modify (fun s => { s with local3 := i18 })
    pure .rep6)
  | e => pure e

def firstAt (p0 : BitVec 64) : Zig.MemM (BitVec 8) := do
  let s1 ← Zig.allocStack 32 16
  let e ← ((do
    let i1 ← pure (← get).buf
    Zig.storeUndef (Vector (BitVec 8) 32) 16 i1
    modify (fun s => { s with local3 := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (firstAt.loop6 i1) firstAt.again6) : Zig.MM firstAtLocals firstAtExit) with
    | .br5 => (do
      match ← ((do
        let i22 ← pure (p0)
        let i23 ← pure (Zig.lt false i22 (32 : BitVec 64))
        if i23 then (do
          let i25 ← pure (Zig.lt false p0 (32 : BitVec 64))
          match ← ((do
            if i25 then (do
              pure .br26)
            else (do
              throw .outOfBounds)) : Zig.MM firstAtLocals firstAtExit) with
          | .br26 => (do
            let i31 ← Zig.callM (Zig.ptrProject i1 (·.elem 1 p0))
            let i32 ← pure (i31)
            let i33 ← pure (some i32)
            pure (.br21 i33))
          | e => pure e)
        else (do
          pure (.br21 none))) : Zig.MM firstAtLocals firstAtExit) with
      | .br21 v21 => (do
        let i36 ← Zig.callM (abi_abi_first_abi_calls_firstAt v21)
        pure (.ret i36))
      | e => pure e)
    | e => pure e) : Zig.MM firstAtLocals firstAtExit).run' { (default : firstAtLocals) with buf := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure lenOfLocals where
  deriving Inhabited

inductive lenOfExit where
  | ret (v : BitVec 64)
  | br1 (v : Zig.Ptr)

def lenOf (p0 : BitVec 32) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    match ← ((do
      if p0 == (0 : BitVec 32) then (do
        pure (.br1 (⟨some 1, 0⟩ : Zig.Ptr)))
      else (do
        if p0 == (1 : BitVec 32) then (do
          pure (.br1 (⟨some 0, 0⟩ : Zig.Ptr)))
        else (do
          pure (.br1 Zig.Ptr.null)))) : Zig.MM lenOfLocals lenOfExit) with
    | .br1 v1 => (do
      let i6 ← Zig.callM (abi_abi_len_abi_calls_lenOf v1)
      pure (.ret i6))
    | e => pure e) : Zig.MM lenOfLocals lenOfExit).run' (default : lenOfLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end ExternCalls.Abi