-- air2lean-profile: {"admission":"weak-exports","allocator_model":"translated","correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.1"}}
import ZigLean


namespace ExternAbi

structure mem_Alignment where
  bits : BitVec 6
  deriving Repr, Inhabited, DecidableEq

def mem_Alignment.«1» : mem_Alignment := ⟨(0 : BitVec 6)⟩
def mem_Alignment.«2» : mem_Alignment := ⟨(1 : BitVec 6)⟩
def mem_Alignment.«4» : mem_Alignment := ⟨(2 : BitVec 6)⟩
def mem_Alignment.«8» : mem_Alignment := ⟨(3 : BitVec 6)⟩
def mem_Alignment.«16» : mem_Alignment := ⟨(4 : BitVec 6)⟩
def mem_Alignment.«32» : mem_Alignment := ⟨(5 : BitVec 6)⟩
def mem_Alignment.«64» : mem_Alignment := ⟨(6 : BitVec 6)⟩

def mem_Alignment.toBits (e : mem_Alignment) : BitVec 6 := e.bits

def mem_Alignment.ofInt? (v : Int) : Option mem_Alignment :=
  if 0 ≤ v ∧ v ≤ 63 then Option.some ⟨BitVec.ofInt 6 v⟩ else Option.none

def mem_Alignment.isNamed (e : mem_Alignment) : Bool := e.bits == (0 : BitVec 6) || e.bits == (1 : BitVec 6) || e.bits == (2 : BitVec 6) || e.bits == (3 : BitVec 6) || e.bits == (4 : BitVec 6) || e.bits == (5 : BitVec 6) || e.bits == (6 : BitVec 6)

instance : Zig.Packed mem_Alignment 6 where
  toBits := mem_Alignment.toBits
  ofBits b := ⟨b⟩

instance : Zig.Enc mem_Alignment where
  size := 1
  align := 1
  encode v := (Zig.intEncExt .little false 6).encode v.toBits
  decode bs := do
    let b : BitVec 6 ← (Zig.intEncExt .little false 6).decode bs
    pure ⟨b⟩

structure zigc_c_malloc_Header where
  alignment : mem_Alignment
  size : BitVec 48
  canary : BitVec 10
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed zigc_c_malloc_Header 64 where
  toBits v := ((Zig.Packed.toBits v.alignment).setWidth 64 <<< 0) ||| ((Zig.Packed.toBits v.size).setWidth 64 <<< 6) ||| ((Zig.Packed.toBits v.canary).setWidth 64 <<< 54)
  ofBits b := { alignment := Zig.Packed.get b 0, size := Zig.Packed.get b 6, canary := Zig.Packed.get b 54 }
  valid b := Zig.Packed.validAt (mem_Alignment) b 0

instance : Zig.Enc zigc_c_malloc_Header where
  size := 8
  align := 8
  encode v := Zig.Enc.encode (Zig.Packed.toBits v)
  decode bs := do
    let b : BitVec 64 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

inductive math_Order where
  | gt
  | lt
  | eq
  deriving Repr, Inhabited, DecidableEq

def math_Order.toBits : math_Order → BitVec 2
  | .gt => (0 : BitVec 2)
  | .lt => (1 : BitVec 2)
  | .eq => (2 : BitVec 2)

def math_Order.ofInt? (v : Int) : Option math_Order :=
  if v = 0 then Option.some .gt else if v = 1 then Option.some .lt else if v = 2 then Option.some .eq else Option.none

def math_Order.isNamed (_ : math_Order) : Bool := true

instance : Zig.Packed math_Order 2 where
  toBits := math_Order.toBits
  ofBits b := (math_Order.ofInt? (Zig.val false b)).getD default
  valid b := (math_Order.ofInt? (Zig.val false b)).isSome

/-- The memory at program start under the placement `σ`: block `k` is global `k`. The words of `@returnAddress()` and of `undefined` pointers are `arbitrary` (`Mem.arbitrary`). -/
def mem0 (σ : Zig.Placement) (arbitrary : Array (BitVec 64) := #[]) : Zig.Mem := { Zig.Mem.ofGlobals σ [
  -- 0: a constant
  (Zig.Enc.encode ((#v[(98 : BitVec 8), (0 : BitVec 8)] : Vector (BitVec 8) 2) : Vector (BitVec 8) 2), 1, .constGlobal),
  -- 1: a constant
  (Zig.Enc.encode ((#v[(97 : BitVec 8), (98 : BitVec 8), (100 : BitVec 8), (0 : BitVec 8)] : Vector (BitVec 8) 4) : Vector (BitVec 8) 4), 1, .constGlobal),
  -- 2: a constant
  (Zig.Enc.encode ((#v[(97 : BitVec 8), (98 : BitVec 8), (99 : BitVec 8), (0 : BitVec 8)] : Vector (BitVec 8) 4) : Vector (BitVec 8) 4), 1, .constGlobal)] with arbitrary }

structure math_order__anon_bc8ac1e4f1baLocals where
  deriving Inhabited

inductive math_order__anon_bc8ac1e4f1baExit where
  | ret (v : math_Order)

def math_order__anon_bc8ac1e4f1ba (p0 : BitVec 8) (p1 : BitVec 8) : Zig.Result (math_Order) := do
  let e ← ((do
    let i2 ← pure (p0 == p1)
    if i2 then (do
      pure (.ret math_Order.eq))
    else (do
      let i5 ← pure (Zig.lt false p0 p1)
      if i5 then (do
        pure (.ret math_Order.lt))
      else (do
        let i8 ← pure (Zig.gt false p0 p1)
        if i8 then (do
          pure (.ret math_Order.gt))
        else (do
          throw .unreachable)))) : Zig.M math_order__anon_bc8ac1e4f1baLocals math_order__anon_bc8ac1e4f1baExit).run' (default : math_order__anon_bc8ac1e4f1baLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] math_order__anon_bc8ac1e4f1ba

structure mem_boundedOrderZ__anon_c47d7be5de32Locals where
  i : BitVec 64
  deriving Inhabited

inductive mem_boundedOrderZ__anon_c47d7be5de32Exit where
  | ret (v : math_Order)
  | br3
  | br18 (v : Bool)
  | br25 (v : Bool)
  | br12
  | br10
  | br40 (v : math_Order)
  | rep11

def mem_boundedOrderZ__anon_c47d7be5de32.again11 : mem_boundedOrderZ__anon_c47d7be5de32Exit → Bool
  | .rep11 => true
  | _ => false

def mem_boundedOrderZ__anon_c47d7be5de32.loop11 (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : BitVec 64) : Zig.MM mem_boundedOrderZ__anon_c47d7be5de32Locals mem_boundedOrderZ__anon_c47d7be5de32Exit := do
  Zig.callM Zig.tick
  match ← ((do
    let i13 ← pure ((← get).i)
    let i14 ← Zig.callM (Zig.load (BitVec 8) 1 (p0.elem 1 i13))
    let i15 ← pure ((← get).i)
    let i16 ← Zig.callM (Zig.load (BitVec 8) 1 (p1.elem 1 i15))
    let i17 ← pure (i14 == i16)
    match ← ((do
      if i17 then (do
        let i20 ← pure ((← get).i)
        let i21 ← Zig.callM (Zig.load (BitVec 8) 1 (p0.elem 1 i20))
        let i22 ← pure (i21 != (0 : BitVec 8))
        pure (.br18 i22))
      else (do
        pure (.br18 false))) : Zig.MM mem_boundedOrderZ__anon_c47d7be5de32Locals mem_boundedOrderZ__anon_c47d7be5de32Exit) with
    | .br18 v18 => (do
      match ← ((do
        if v18 then (do
          let i27 ← pure ((← get).i)
          let i28 ← pure (i27)
          let i29 ← pure (p2)
          let i30 ← pure (Zig.lt false i28 i29)
          pure (.br25 i30))
        else (do
          pure (.br25 false))) : Zig.MM mem_boundedOrderZ__anon_c47d7be5de32Locals mem_boundedOrderZ__anon_c47d7be5de32Exit) with
      | .br25 v25 => (do
        if v25 then (do
          let i34 ← pure ((← get).i)
          let i35 ← Zig.add false i34 (1 : BitVec 64)
          modify (fun s => { s with i := i35 })
          pure .br12)
        else (do
          pure .br10))
      | e => pure e)
    | e => pure e) : Zig.MM mem_boundedOrderZ__anon_c47d7be5de32Locals mem_boundedOrderZ__anon_c47d7be5de32Exit) with
  | .br12 => (do
    pure .rep11)
  | e => pure e

def mem_boundedOrderZ__anon_c47d7be5de32 (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : BitVec 64) : Zig.MemM (math_Order) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.callM (Zig.ptrEqAddr p0 p1)
      if i4 then (do
        pure (.ret math_Order.eq))
      else (do
        pure .br3)) : Zig.MM mem_boundedOrderZ__anon_c47d7be5de32Locals mem_boundedOrderZ__anon_c47d7be5de32Exit) with
    | .br3 => (do
      modify (fun s => { s with i := (0 : BitVec 64) })
      match ← ((do
        Zig.loop (mem_boundedOrderZ__anon_c47d7be5de32.loop11 p0 p1 p2) mem_boundedOrderZ__anon_c47d7be5de32.again11) : Zig.MM mem_boundedOrderZ__anon_c47d7be5de32Locals mem_boundedOrderZ__anon_c47d7be5de32Exit) with
      | .br10 => (do
        match ← ((do
          let i41 ← pure ((← get).i)
          let i42 ← pure (i41)
          let i43 ← pure (p2)
          let i44 ← pure (Zig.lt false i42 i43)
          if i44 then (do
            let i46 ← pure ((← get).i)
            let i47 ← Zig.callM (Zig.load (BitVec 8) 1 (p0.elem 1 i46))
            let i48 ← pure ((← get).i)
            let i49 ← Zig.callM (Zig.load (BitVec 8) 1 (p1.elem 1 i48))
            let i50 ← Zig.callR (math_order__anon_bc8ac1e4f1ba i47 i49)
            pure (.br40 i50))
          else (do
            pure (.br40 math_Order.eq))) : Zig.MM mem_boundedOrderZ__anon_c47d7be5de32Locals mem_boundedOrderZ__anon_c47d7be5de32Exit) with
        | .br40 v40 => (do
          pure (.ret v40))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM mem_boundedOrderZ__anon_c47d7be5de32Locals mem_boundedOrderZ__anon_c47d7be5de32Exit).run' (default : mem_boundedOrderZ__anon_c47d7be5de32Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_boundedOrderZ__anon_c47d7be5de32.loop11 mem_boundedOrderZ__anon_c47d7be5de32

structure zigc_c_string_strncmpLocals where
  deriving Inhabited

inductive zigc_c_string_strncmpExit where
  | ret (v : BitVec 32)
  | br6 (v : BitVec 32)

def zigc_c_string_strncmp (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : BitVec 64) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i3 ← pure (p0)
    let i4 ← pure (p1)
    let i5 ← Zig.callM (mem_boundedOrderZ__anon_c47d7be5de32 i3 i4 p2)
    match ← ((do
      match i5 with
      | .eq => (do
        pure (.br6 (0 : BitVec 32)))
      | .gt => (do
        pure (.br6 (1 : BitVec 32)))
      | .lt => (do
        pure (.br6 (-(1 : BitVec 32))))) : Zig.MM zigc_c_string_strncmpLocals zigc_c_string_strncmpExit) with
    | .br6 v6 => (do
      pure (.ret v6))
    | e => pure e) : Zig.MM zigc_c_string_strncmpLocals zigc_c_string_strncmpExit).run' (default : zigc_c_string_strncmpLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] zigc_c_string_strncmp

structure zigc_c_string_strcmpLocals where
  deriving Inhabited

inductive zigc_c_string_strcmpExit where
  | ret (v : BitVec 32)

def zigc_c_string_strcmp (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i2 ← Zig.callM (zigc_c_string_strncmp p0 p1 (18446744073709551615 : BitVec 64))
    pure (.ret i2)) : Zig.MM zigc_c_string_strcmpLocals zigc_c_string_strcmpExit).run' (default : zigc_c_string_strcmpLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] zigc_c_string_strcmp

structure cmp_caseLocals where
  k : BitVec 32
  s : Zig.Ptr
  t : Zig.Ptr
  deriving Inhabited

inductive cmp_caseExit where
  | ret (v : BitVec 32)

def cmp_case (p0 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s3 ← Zig.allocStack 4 1
  let s5 ← Zig.allocStack 3 1
  let e ← ((do
    modify (fun s => { s with k := p0 })
    let i3 ← pure (← get).s
    Zig.store (α := Vector (BitVec 8) 4) 1 i3 (#v[(97 : BitVec 8), (98 : BitVec 8), (99 : BitVec 8), (0 : BitVec 8)] : Vector (BitVec 8) 4)
    let i5 ← pure (← get).t
    Zig.store (α := Vector (BitVec 8) 3) 1 i5 (#v[(97 : BitVec 8), (98 : BitVec 8), (99 : BitVec 8)] : Vector (BitVec 8) 3)
    let i7 ← pure ((← get).k)
    if i7 == (0 : BitVec 32) then (do
      let i12 ← pure (i3)
      let i13 ← Zig.callM (zigc_c_string_strcmp (← Zig.callM (Zig.abiPtr ({ nonNull := true, align := 1, sentinel := some (0 : BitVec 8) } : Zig.AbiPtrReq) i12)) (← Zig.callM (Zig.abiPtr ({ nonNull := true, align := 1, sentinel := some (0 : BitVec 8) } : Zig.AbiPtrReq) (⟨some 2, 0⟩ : Zig.Ptr))))
      pure (.ret i13))
    else (do
      if i7 == (1 : BitVec 32) then (do
        let i15 ← pure (i3)
        let i16 ← Zig.callM (zigc_c_string_strcmp (← Zig.callM (Zig.abiPtr ({ nonNull := true, align := 1, sentinel := some (0 : BitVec 8) } : Zig.AbiPtrReq) i15)) (← Zig.callM (Zig.abiPtr ({ nonNull := true, align := 1, sentinel := some (0 : BitVec 8) } : Zig.AbiPtrReq) (⟨some 1, 0⟩ : Zig.Ptr))))
        pure (.ret i16))
      else (do
        if i7 == (2 : BitVec 32) then (do
          let i18 ← pure (i3)
          let i19 ← Zig.callM (zigc_c_string_strcmp (← Zig.callM (Zig.abiPtr ({ nonNull := true, align := 1, sentinel := some (0 : BitVec 8) } : Zig.AbiPtrReq) (⟨some 0, 0⟩ : Zig.Ptr))) (← Zig.callM (Zig.abiPtr ({ nonNull := true, align := 1, sentinel := some (0 : BitVec 8) } : Zig.AbiPtrReq) i18)))
          pure (.ret i19))
        else (do
          if i7 == (3 : BitVec 32) then (do
            let i21 ← pure (i5)
            let i22 ← Zig.callM (zigc_c_string_strcmp (← Zig.callM (Zig.abiPtr ({ nonNull := true, align := 1, sentinel := some (0 : BitVec 8) } : Zig.AbiPtrReq) i21)) (← Zig.callM (Zig.abiPtr ({ nonNull := true, align := 1, sentinel := some (0 : BitVec 8) } : Zig.AbiPtrReq) (⟨some 2, 0⟩ : Zig.Ptr))))
            pure (.ret i22))
          else (do
            let i9 ← pure (i3)
            let i10 ← Zig.callM (zigc_c_string_strcmp (← Zig.callM (Zig.abiPtr ({ nonNull := true, align := 1, sentinel := some (0 : BitVec 8) } : Zig.AbiPtrReq) Zig.Ptr.null)) (← Zig.callM (Zig.abiPtr ({ nonNull := true, align := 1, sentinel := some (0 : BitVec 8) } : Zig.AbiPtrReq) i9)))
            pure (.ret i10)))))) : Zig.MM cmp_caseLocals cmp_caseExit).run' { (default : cmp_caseLocals) with s := s3, t := s5 }
  Zig.free s5
  Zig.free s3
  match e with
  | .ret v => pure v

attribute [zig_run] cmp_case

structure mem_findSentinel__anon_583bd97c811cLocals where
  i : BitVec 64
  deriving Inhabited

inductive mem_findSentinel__anon_583bd97c811cExit where
  | ret (v : BitVec 64)
  | br5
  | br3
  | rep4

def mem_findSentinel__anon_583bd97c811c.again4 : mem_findSentinel__anon_583bd97c811cExit → Bool
  | .rep4 => true
  | _ => false

def mem_findSentinel__anon_583bd97c811c.loop4 (p0 : Zig.Ptr) : Zig.MM mem_findSentinel__anon_583bd97c811cLocals mem_findSentinel__anon_583bd97c811cExit := do
  Zig.callM Zig.tick
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
      pure .br3)) : Zig.MM mem_findSentinel__anon_583bd97c811cLocals mem_findSentinel__anon_583bd97c811cExit) with
  | .br5 => (do
    pure .rep4)
  | e => pure e

def mem_findSentinel__anon_583bd97c811c (p0 : Zig.Ptr) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (mem_findSentinel__anon_583bd97c811c.loop4 p0) mem_findSentinel__anon_583bd97c811c.again4) : Zig.MM mem_findSentinel__anon_583bd97c811cLocals mem_findSentinel__anon_583bd97c811cExit) with
    | .br3 => (do
      let i16 ← pure ((← get).i)
      pure (.ret i16))
    | e => pure e) : Zig.MM mem_findSentinel__anon_583bd97c811cLocals mem_findSentinel__anon_583bd97c811cExit).run' (default : mem_findSentinel__anon_583bd97c811cLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_findSentinel__anon_583bd97c811c.loop4 mem_findSentinel__anon_583bd97c811c

structure mem_len__anon_7a568c628d23Locals where
  deriving Inhabited

inductive mem_len__anon_7a568c628d23Exit where
  | ret (v : BitVec 64)
  | br1

def mem_len__anon_7a568c628d23 (p0 : Zig.Ptr) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    match ← ((do
      pure .br1) : Zig.MM mem_len__anon_7a568c628d23Locals mem_len__anon_7a568c628d23Exit) with
    | .br1 => (do
      let i3 ← Zig.callM (mem_findSentinel__anon_583bd97c811c p0)
      pure (.ret i3))
    | e => pure e) : Zig.MM mem_len__anon_7a568c628d23Locals mem_len__anon_7a568c628d23Exit).run' (default : mem_len__anon_7a568c628d23Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_len__anon_7a568c628d23

structure mem_findScalarLast__anon_5a66a6dc3ac7Locals where
  i : BitVec 64
  deriving Inhabited

inductive mem_findScalarLast__anon_5a66a6dc3ac7Exit where
  | ret (v : Option (BitVec 64))
  | br19
  | br15
  | br7
  | br5
  | rep6

def mem_findScalarLast__anon_5a66a6dc3ac7.again6 : mem_findScalarLast__anon_5a66a6dc3ac7Exit → Bool
  | .rep6 => true
  | _ => false

def mem_findScalarLast__anon_5a66a6dc3ac7.loop6 (p0 : Array (BitVec 8)) (p1 : BitVec 8) : Zig.M mem_findScalarLast__anon_5a66a6dc3ac7Locals mem_findScalarLast__anon_5a66a6dc3ac7Exit := do
  match ← ((do
    let i8 ← pure ((← get).i)
    let i9 ← pure (i8)
    let i10 ← pure (i9 != (0 : BitVec 64))
    if i10 then (do
      let i12 ← pure ((← get).i)
      let i13 ← Zig.sub false i12 (1 : BitVec 64)
      modify (fun s => { s with i := i13 })
      match ← ((do
        let i16 ← pure ((← get).i)
        let i17 ← pure (Zig.len p0)
        let i18 ← pure (Zig.lt false i16 i17)
        match ← ((do
          if i18 then (do
            pure .br19)
          else (do
            throw .outOfBounds)) : Zig.M mem_findScalarLast__anon_5a66a6dc3ac7Locals mem_findScalarLast__anon_5a66a6dc3ac7Exit) with
        | .br19 => (do
          let i24 ← Zig.call (Zig.index p0 i16)
          let i25 ← pure (i24 == p1)
          if i25 then (do
            let i27 ← pure ((← get).i)
            let i28 ← pure (some i27)
            pure (.ret i28))
          else (do
            pure .br15))
        | e => pure e) : Zig.M mem_findScalarLast__anon_5a66a6dc3ac7Locals mem_findScalarLast__anon_5a66a6dc3ac7Exit) with
      | .br15 => (do
        pure .br7)
      | e => pure e)
    else (do
      pure .br5)) : Zig.M mem_findScalarLast__anon_5a66a6dc3ac7Locals mem_findScalarLast__anon_5a66a6dc3ac7Exit) with
  | .br7 => (do
    pure .rep6)
  | e => pure e

def mem_findScalarLast__anon_5a66a6dc3ac7 (p0 : Array (BitVec 8)) (p1 : BitVec 8) : Zig.Result (Option (BitVec 64)) := do
  let e ← ((do
    let i3 ← pure (Zig.len p0)
    modify (fun s => { s with i := i3 })
    match ← ((do
      Zig.loop (mem_findScalarLast__anon_5a66a6dc3ac7.loop6 p0 p1) mem_findScalarLast__anon_5a66a6dc3ac7.again6) : Zig.M mem_findScalarLast__anon_5a66a6dc3ac7Locals mem_findScalarLast__anon_5a66a6dc3ac7Exit) with
    | .br5 => (do
      pure (.ret none))
    | e => pure e) : Zig.M mem_findScalarLast__anon_5a66a6dc3ac7Locals mem_findScalarLast__anon_5a66a6dc3ac7Exit).run' (default : mem_findScalarLast__anon_5a66a6dc3ac7Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_findScalarLast__anon_5a66a6dc3ac7.loop6 mem_findScalarLast__anon_5a66a6dc3ac7

structure zigc_c_string_strrchrLocals where
  deriving Inhabited

inductive zigc_c_string_strrchrExit where
  | ret (v : Option (Zig.Ptr))
  | br3 (v : BitVec 64)

def zigc_c_string_strrchr (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    let i2 ← pure (p0)
    match ← ((do
      let i4 ← Zig.callM (mem_len__anon_7a568c628d23 i2)
      let i5 ← Zig.add false i4 (1 : BitVec 64)
      let i6 ← pure i2
      let i7 ← Zig.sub false i5 (0 : BitVec 64) (safe := false)
      let i8 ← pure (⟨i6, i7⟩ : Zig.Slice)
      let i9 ← pure (p1)
      let i10 ← pure (Zig.trunc 8 i9)
      let i11 ← Zig.callR (mem_findScalarLast__anon_5a66a6dc3ac7 (← Zig.callM (Zig.readSlice (BitVec 8) 1 i8)) i10)
      let i12 ← pure ((i11).isSome)
      if i12 then (do
        let i14 ← Zig.optPayload i11
        pure (.br3 i14))
      else (do
        pure (.ret none))) : Zig.MM zigc_c_string_strrchrLocals zigc_c_string_strrchrExit) with
    | .br3 v3 => (do
      let _i17 ← Zig.callM (Zig.ptrProject p0 (·.elem 1 v3))
      let i18 ← Zig.callM (Zig.ptrProject p0 (·.elem 1 v3))
      let i19 ← pure (i18)
      let i20 ← pure (i19)
      pure (.ret i20))
    | e => pure e) : Zig.MM zigc_c_string_strrchrLocals zigc_c_string_strrchrExit).run' (default : zigc_c_string_strrchrLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] zigc_c_string_strrchr

structure last_caseLocals where
  k : BitVec 32
  c : BitVec 32
  words : Zig.Ptr
  p : Zig.Ptr
  deriving Inhabited

inductive last_caseExit where
  | ret (v : BitVec 64)
  | br9 (v : Zig.Ptr)
  | br37
  | br24 (v : BitVec 64)

def last_case (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 64) := do
  let s6 ← Zig.allocStack 17 1
  let e ← ((do
    modify (fun s => { s with k := p0 })
    modify (fun s => { s with c := p1 })
    let i6 ← pure (← get).words
    Zig.store (α := Vector (BitVec 8) 17) 1 i6 (#v[(97 : BitVec 8), (108 : BitVec 8), (112 : BitVec 8), (104 : BitVec 8), (97 : BitVec 8), (44 : BitVec 8), (98 : BitVec 8), (101 : BitVec 8), (116 : BitVec 8), (97 : BitVec 8), (44 : BitVec 8), (103 : BitVec 8), (97 : BitVec 8), (109 : BitVec 8), (109 : BitVec 8), (97 : BitVec 8), (0 : BitVec 8)] : Vector (BitVec 8) 17)
    match ← ((do
      let i10 ← pure ((← get).k)
      let i11 ← pure (i10)
      let i12 ← pure (i11 == (0 : BitVec 32))
      if i12 then (do
        let i14 ← pure (i6)
        let i15 ← pure (i14)
        pure (.br9 i15))
      else (do
        let i17 ← pure (i6)
        let i18 ← Zig.callM (Zig.ptrProject i17 (·.elem 1 (6 : BitVec 64)))
        let i19 ← pure (i18)
        pure (.br9 i19))) : Zig.MM last_caseLocals last_caseExit) with
    | .br9 v9 => (do
      let i21 ← pure ((← get).c)
      let i22 ← (Zig.callM (zigc_c_string_strrchr (← Zig.callM (Zig.abiPtr ({ nonNull := true, align := 1, sentinel := some (0 : BitVec 8) } : Zig.AbiPtrReq) v9)) i21) >>= fun r => Zig.callM (Zig.abiPtr ({ nonNull := false, align := 1, sentinel := none } : Zig.AbiPtrReq) (Zig.ptrOfOptional r)))
      modify (fun s => { s with p := i22 })
      match ← ((do
        let i25 ← pure ((← get).p)
        let i26 ← Zig.callM (do pure (!(← Zig.ptrIsNull i25)))
        if i26 then (do
          let i28 ← pure ((← get).p)
          let i29 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i28)))
          let i30 ← pure (i6)
          let i31 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i30)))
          let i32 ← pure (Zig.subWrap i29 i31)
          let i33 ← pure (i32)
          let i34 ← Zig.divTrunc true i33 (1 : BitVec 64)
          let i35 ← Zig.rem true i33 (1 : BitVec 64)
          let i36 ← pure (i35 == (0 : BitVec 64))
          match ← ((do
            if i36 then (do
              pure .br37)
            else (do
              throw .panic)) : Zig.MM last_caseLocals last_caseExit) with
          | .br37 => (do
            pure (.br24 i34))
          | e => pure e)
        else (do
          pure (.br24 (-(1 : BitVec 64))))) : Zig.MM last_caseLocals last_caseExit) with
      | .br24 v24 => (do
        pure (.ret v24))
      | e => pure e)
    | e => pure e) : Zig.MM last_caseLocals last_caseExit).run' { (default : last_caseLocals) with words := s6 }
  Zig.free s6
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] last_case

structure zigc_c_string_memrchrLocals where
  deriving Inhabited

inductive zigc_c_string_memrchrExit where
  | ret (v : Option (Zig.Ptr))
  | br4 (v : BitVec 64)

def zigc_c_string_memrchr (p0 : Zig.Ptr) (p1 : BitVec 32) (p2 : BitVec 64) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    let i3 ← pure (p0)
    match ← ((do
      let i5 ← pure i3
      let i6 ← Zig.sub false p2 (0 : BitVec 64) (safe := false)
      let i7 ← pure (⟨i5, i6⟩ : Zig.Slice)
      let i8 ← pure (p1)
      let i9 ← pure (Zig.trunc 8 i8)
      let i10 ← Zig.callR (mem_findScalarLast__anon_5a66a6dc3ac7 (← Zig.callM (Zig.readSlice (BitVec 8) 1 i7)) i9)
      let i11 ← pure ((i10).isSome)
      if i11 then (do
        let i13 ← Zig.optPayload i10
        pure (.br4 i13))
      else (do
        pure (.ret none))) : Zig.MM zigc_c_string_memrchrLocals zigc_c_string_memrchrExit) with
    | .br4 v4 => (do
      let _i16 ← Zig.callM (Zig.ptrProject i3 (·.elem 1 v4))
      let i17 ← Zig.callM (Zig.ptrProject i3 (·.elem 1 v4))
      let i18 ← pure (i17)
      let i19 ← pure (i18)
      let i20 ← pure (some i19)
      pure (.ret i20))
    | e => pure e) : Zig.MM zigc_c_string_memrchrLocals zigc_c_string_memrchrExit).run' (default : zigc_c_string_memrchrLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] zigc_c_string_memrchr

structure rfind_caseLocals where
  k : BitVec 32
  words : Zig.Ptr
  base : Option (Zig.Ptr)
  p : Zig.Ptr
  deriving Inhabited

inductive rfind_caseExit where
  | ret (v : BitVec 64)
  | br6 (v : Option (Zig.Ptr))
  | br18 (v : BitVec 64)
  | br42
  | br29 (v : BitVec 64)

def rfind_case (p0 : BitVec 32) : Zig.MemM (BitVec 64) := do
  let s3 ← Zig.allocStack 17 1
  let e ← ((do
    modify (fun s => { s with k := p0 })
    let i3 ← pure (← get).words
    Zig.store (α := Vector (BitVec 8) 17) 1 i3 (#v[(97 : BitVec 8), (108 : BitVec 8), (112 : BitVec 8), (104 : BitVec 8), (97 : BitVec 8), (44 : BitVec 8), (98 : BitVec 8), (101 : BitVec 8), (116 : BitVec 8), (97 : BitVec 8), (44 : BitVec 8), (103 : BitVec 8), (97 : BitVec 8), (109 : BitVec 8), (109 : BitVec 8), (97 : BitVec 8), (0 : BitVec 8)] : Vector (BitVec 8) 17)
    match ← ((do
      let i7 ← pure ((← get).k)
      let i8 ← pure (i7)
      let i9 ← pure (i8 == (0 : BitVec 32))
      if i9 then (do
        let i11 ← pure (i3)
        let i12 ← Zig.callM (Zig.ptrToOptional i11)
        pure (.br6 i12))
      else (do
        pure (.br6 none))) : Zig.MM rfind_caseLocals rfind_caseExit) with
    | .br6 v6 => (do
      modify (fun s => { s with base := v6 })
      let i17 ← pure ((← get).base)
      match ← ((do
        let i19 ← pure ((← get).k)
        let i20 ← pure (i19)
        let i21 ← pure (i20 == (0 : BitVec 32))
        if i21 then (do
          pure (.br18 (16 : BitVec 64)))
        else (do
          pure (.br18 (0 : BitVec 64)))) : Zig.MM rfind_caseLocals rfind_caseExit) with
      | .br18 v18 => (do
        let i25 ← pure (v18)
        let i26 ← Zig.callM (zigc_c_string_memrchr (← Zig.callM (Zig.abiPtr ({ nonNull := true, align := 1, sentinel := none } : Zig.AbiPtrReq) (Zig.ptrOfOptional i17))) (97 : BitVec 32) i25)
        let i27 ← pure (Zig.ptrOfOptional i26)
        modify (fun s => { s with p := i27 })
        match ← ((do
          let i30 ← pure ((← get).p)
          let i31 ← Zig.callM (do pure (!(← Zig.ptrIsNull i30)))
          if i31 then (do
            let i33 ← pure ((← get).p)
            let i34 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i33)))
            let i35 ← pure (i3)
            let i36 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i35)))
            let i37 ← pure (Zig.subWrap i34 i36)
            let i38 ← pure (i37)
            let i39 ← Zig.divTrunc true i38 (1 : BitVec 64)
            let i40 ← Zig.rem true i38 (1 : BitVec 64)
            let i41 ← pure (i40 == (0 : BitVec 64))
            match ← ((do
              if i41 then (do
                pure .br42)
              else (do
                throw .panic)) : Zig.MM rfind_caseLocals rfind_caseExit) with
            | .br42 => (do
              pure (.br29 i39))
            | e => pure e)
          else (do
            pure (.br29 (-(1 : BitVec 64))))) : Zig.MM rfind_caseLocals rfind_caseExit) with
        | .br29 v29 => (do
          pure (.ret v29))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM rfind_caseLocals rfind_caseExit).run' { (default : rfind_caseLocals) with words := s3 }
  Zig.free s3
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] rfind_case

structure debug_assertLocals where
  deriving Inhabited

inductive debug_assertExit where
  | ret
  | br1

def debug_assert (p0 : Bool) : Zig.Result (Unit) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure (!p0)
      if i2 then (do
        throw .unreachable)
      else (do
        pure .br1)) : Zig.M debug_assertLocals debug_assertExit) with
    | .br1 => (do
      pure .ret)
    | e => pure e) : Zig.M debug_assertLocals debug_assertExit).run' (default : debug_assertLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] debug_assert

structure zigc_c_malloc_Header_getLocals where
  deriving Inhabited

inductive zigc_c_malloc_Header_getExit where
  | ret (v : zigc_c_malloc_Header)

def zigc_c_malloc_Header_get (p0 : Zig.Ptr) : Zig.MemM (zigc_c_malloc_Header) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.elemSub 1 (8 : BitVec 64)))
    let i2 ← pure (i1)
    let i3 ← pure i2
    let i4 ← Zig.loadBits (BitVec 10) 8 8 54 i3
    let i5 ← pure (i4 == (569 : BitVec 10))
    let _i6 ← Zig.callR (debug_assert i5)
    let i7 ← Zig.load (zigc_c_malloc_Header) 8 i2
    pure (.ret i7)) : Zig.MM zigc_c_malloc_Header_getLocals zigc_c_malloc_Header_getExit).run' (default : zigc_c_malloc_Header_getLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] zigc_c_malloc_Header_get

structure zigc_c_malloc_malloc_usable_sizeLocals where
  deriving Inhabited

inductive zigc_c_malloc_malloc_usable_sizeExit where
  | ret (v : BitVec 64)
  | br1 (v : Zig.Ptr)

def zigc_c_malloc_malloc_usable_size (p0 : Option (Zig.Ptr)) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure ((p0).isSome)
      if i2 then (do
        let i4 ← Zig.optPayload p0
        pure (.br1 i4))
      else (do
        pure (.ret (0 : BitVec 64)))) : Zig.MM zigc_c_malloc_malloc_usable_sizeLocals zigc_c_malloc_malloc_usable_sizeExit) with
    | .br1 v1 => (do
      let i7 ← Zig.callM (zigc_c_malloc_Header_get v1)
      let i8 ← pure ((i7).size)
      let i9 ← Zig.intCast false false 64 i8 (safe := false)
      pure (.ret i9))
    | e => pure e) : Zig.MM zigc_c_malloc_malloc_usable_sizeLocals zigc_c_malloc_malloc_usable_sizeExit).run' (default : zigc_c_malloc_malloc_usable_sizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] zigc_c_malloc_malloc_usable_size

structure usable_caseLocals where
  k : BitVec 32
  size : BitVec 32
  block : Zig.Ptr
  base : Zig.Ptr
  deriving Inhabited

inductive usable_caseExit where
  | ret (v : BitVec 64)

def usable_case (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 64) := do
  let s6 ← Zig.allocStack 32 16
  let e ← ((do
    modify (fun s => { s with k := p0 })
    modify (fun s => { s with size := p1 })
    let i6 ← pure (← get).block
    let i7 ← pure ((← get).size)
    let i8 ← Zig.intCast false false 64 i7 (safe := false)
    let i9 ← pure (Zig.shl i8 (6 : BitVec 6))
    let i10 ← pure ((4 : BitVec 64) ||| i9)
    let i11 ← pure (i10 ||| (10250192751895248896 : BitVec 64))
    let i12 ← pure (#v[(0 : BitVec 64), i11, (0 : BitVec 64), (0 : BitVec 64)] : Vector (BitVec 64) 4)
    Zig.store (α := Vector (BitVec 64) 4) 16 i6 i12
    let i15 ← pure (i6)
    let i16 ← pure (i15)
    let i17 ← Zig.callM (Zig.ptrProject i16 (·.elem 1 (16 : BitVec 64)))
    modify (fun s => { s with base := i17 })
    let i19 ← pure ((← get).k)
    if i19 == (0 : BitVec 32) then (do
      let i27 ← Zig.callM (zigc_c_malloc_malloc_usable_size (← Zig.callM (Zig.abiPtrOpt ({ nonNull := false, align := 16, sentinel := none } : Zig.AbiPtrReq) (Zig.ptrOfOptional none))))
      let i28 ← pure (i27)
      pure (.ret i28))
    else (do
      if i19 == (1 : BitVec 32) then (do
        let i30 ← pure ((← get).base)
        let i31 ← Zig.callM (Zig.ptrToOptional i30)
        let i32 ← Zig.callM (zigc_c_malloc_malloc_usable_size (← Zig.callM (Zig.abiPtrOpt ({ nonNull := false, align := 16, sentinel := none } : Zig.AbiPtrReq) (Zig.ptrOfOptional i31))))
        let i33 ← pure (i32)
        pure (.ret i33))
      else (do
        let i21 ← pure ((← get).base)
        let i22 ← Zig.callM (Zig.ptrProject i21 (·.elem 1 (1 : BitVec 64)))
        let i23 ← Zig.callM (Zig.ptrToOptional i22)
        let i24 ← Zig.callM (zigc_c_malloc_malloc_usable_size (← Zig.callM (Zig.abiPtrOpt ({ nonNull := false, align := 16, sentinel := none } : Zig.AbiPtrReq) (Zig.ptrOfOptional i23))))
        let i25 ← pure (i24)
        pure (.ret i25)))) : Zig.MM usable_caseLocals usable_caseExit).run' { (default : usable_caseLocals) with block := s6 }
  Zig.free s6
  match e with
  | .ret v => pure v

attribute [zig_run] usable_case

end ExternAbi