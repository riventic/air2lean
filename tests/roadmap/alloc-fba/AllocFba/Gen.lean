-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace AllocFba.Gen

structure mem_Allocator_VTable where
  alloc : Zig.Ptr
  resize : Zig.Ptr
  remap : Zig.Ptr
  free : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc mem_Allocator_VTable where
  size := 32
  align := 8
  encode v := Zig.Enc.fields 32 [(0, Zig.Enc.encode v.alloc), (8, Zig.Enc.encode v.resize), (16, Zig.Enc.encode v.remap), (24, Zig.Enc.encode v.free)]
  decode bs := do pure { alloc := ← Zig.Enc.decodeAt bs 0, resize := ← Zig.Enc.decodeAt bs 8, remap := ← Zig.Enc.decodeAt bs 16, free := ← Zig.Enc.decodeAt bs 24 }

structure mem_Allocator where
  ptr : Zig.Ptr
  vtable : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc mem_Allocator where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.ptr), (8, Zig.Enc.encode v.vtable)]
  decode bs := do pure { ptr := ← Zig.Enc.decodeAt bs 0, vtable := ← Zig.Enc.decodeAt bs 8 }

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
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 6 ← Zig.Enc.decode bs
    pure ⟨b⟩

structure heap_FixedBufferAllocator where
  end_index : BitVec 64
  buffer : Zig.Slice
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc heap_FixedBufferAllocator where
  size := 24
  align := 8
  encode v := Zig.Enc.fields 24 [(0, Zig.Enc.encode v.end_index), (8, Zig.Enc.encode v.buffer)]
  decode bs := do pure { end_index := ← Zig.Enc.decodeAt bs 0, buffer := ← Zig.Enc.decodeAt bs 8 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: client.buffer
  (Array.replicate (Zig.Enc.size (Vector (BitVec 8) 16)) .undef, 1, .global),
  -- 1: heap.FixedBufferAllocator.alloc
  (#[.undef], 1, .constGlobal),
  -- 2: heap.FixedBufferAllocator.resize
  (#[.undef], 1, .constGlobal),
  -- 3: heap.FixedBufferAllocator.remap
  (#[.undef], 1, .constGlobal),
  -- 4: heap.FixedBufferAllocator.free
  (#[.undef], 1, .constGlobal),
  -- 5: a constant
  (Zig.Enc.encode (({ alloc := (⟨some 1, 0⟩ : Zig.Ptr), resize := (⟨some 2, 0⟩ : Zig.Ptr), remap := (⟨some 3, 0⟩ : Zig.Ptr), free := (⟨some 4, 0⟩ : Zig.Ptr) } : mem_Allocator_VTable) : mem_Allocator_VTable), 8, .constGlobal)]

structure heap_FixedBufferAllocator_initLocals where
  local1 : heap_FixedBufferAllocator
  deriving Inhabited

inductive heap_FixedBufferAllocator_initExit where
  | ret (v : heap_FixedBufferAllocator)

def heap_FixedBufferAllocator_init (p0 : Zig.Slice) : Zig.MemM (heap_FixedBufferAllocator) := do
  let e ← ((do
    modify (fun s => { s with local1 := { s.local1 with buffer := p0 } })
    modify (fun s => { s with local1 := { s.local1 with end_index := (0 : BitVec 64) } })
    pure (.ret (← get).local1)) : Zig.MM heap_FixedBufferAllocator_initLocals heap_FixedBufferAllocator_initExit).run' (default : heap_FixedBufferAllocator_initLocals)
  match e with
  | .ret v => pure v

structure heap_FixedBufferAllocator_allocatorLocals where
  local1 : mem_Allocator
  deriving Inhabited

inductive heap_FixedBufferAllocator_allocatorExit where
  | ret (v : mem_Allocator)

def heap_FixedBufferAllocator_allocator (p0 : Zig.Ptr) : Zig.MemM (mem_Allocator) := do
  let e ← ((do
    let i3 ← pure (p0)
    modify (fun s => { s with local1 := { s.local1 with ptr := i3 } })
    modify (fun s => { s with local1 := { s.local1 with vtable := (⟨some 5, 0⟩ : Zig.Ptr) } })
    pure (.ret (← get).local1)) : Zig.MM heap_FixedBufferAllocator_allocatorLocals heap_FixedBufferAllocator_allocatorExit).run' (default : heap_FixedBufferAllocator_allocatorLocals)
  match e with
  | .ret v => pure v

structure math_mul__anon_44faaf286c79Locals where
  deriving Inhabited

inductive math_mul__anon_44faaf286c79Exit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br3

def math_mul__anon_44faaf286c79 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← pure (Zig.mulWithOverflow false p0 p1)
    match ← ((do
      let i4 ← pure ((i2).2)
      let i5 ← pure (i4 != (0 : BitVec 1))
      if i5 then (do
        pure (.ret (.error "Overflow" : Except Zig.ErrName (BitVec 64))))
      else (do
        pure .br3)) : Zig.M math_mul__anon_44faaf286c79Locals math_mul__anon_44faaf286c79Exit) with
    | .br3 => (do
      let i9 ← pure ((i2).1)
      let i10 ← pure ((.ok i9) : Except Zig.ErrName (BitVec 64))
      pure (.ret i10))
    | e => pure e) : Zig.M math_mul__anon_44faaf286c79Locals math_mul__anon_44faaf286c79Exit).run' (default : math_mul__anon_44faaf286c79Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Alignment_toByteUnitsLocals where
  deriving Inhabited

inductive mem_Alignment_toByteUnitsExit where
  | ret (v : BitVec 64)

def mem_Alignment_toByteUnits (p0 : mem_Alignment) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← pure (mem_Alignment.toBits p0)
    let i2 ← pure (Zig.shl (1 : BitVec 64) i1)
    pure (.ret i2)) : Zig.M mem_Alignment_toByteUnitsLocals mem_Alignment_toByteUnitsExit).run' (default : mem_Alignment_toByteUnitsLocals)
  match e with
  | .ret v => pure v

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

structure math_isPowerOfTwo__anon_38853e1fe316Locals where
  deriving Inhabited

inductive math_isPowerOfTwo__anon_38853e1fe316Exit where
  | ret (v : Bool)

def math_isPowerOfTwo__anon_38853e1fe316 (p0 : BitVec 64) : Zig.Result (Bool) := do
  let e ← ((do
    let i1 ← pure (p0)
    let i2 ← pure (Zig.gt false i1 (0 : BitVec 64))
    let _i3 ← Zig.call (debug_assert i2)
    let i4 ← Zig.sub false p0 (1 : BitVec 64)
    let i5 ← pure (p0 &&& i4)
    let i6 ← pure (i5)
    let i7 ← pure (i6 == (0 : BitVec 64))
    pure (.ret i7)) : Zig.M math_isPowerOfTwo__anon_38853e1fe316Locals math_isPowerOfTwo__anon_38853e1fe316Exit).run' (default : math_isPowerOfTwo__anon_38853e1fe316Locals)
  match e with
  | .ret v => pure v

structure mem_isValidAlignGeneric__anon_32d5b5f10ec2Locals where
  deriving Inhabited

inductive mem_isValidAlignGeneric__anon_32d5b5f10ec2Exit where
  | ret (v : Bool)
  | br3 (v : Bool)

def mem_isValidAlignGeneric__anon_32d5b5f10ec2 (p0 : BitVec 64) : Zig.Result (Bool) := do
  let e ← ((do
    let i1 ← pure (p0)
    let i2 ← pure (Zig.gt false i1 (0 : BitVec 64))
    match ← ((do
      if i2 then (do
        let i5 ← Zig.call (math_isPowerOfTwo__anon_38853e1fe316 p0)
        pure (.br3 i5))
      else (do
        pure (.br3 false))) : Zig.M mem_isValidAlignGeneric__anon_32d5b5f10ec2Locals mem_isValidAlignGeneric__anon_32d5b5f10ec2Exit) with
    | .br3 v3 => (do
      pure (.ret v3))
    | e => pure e) : Zig.M mem_isValidAlignGeneric__anon_32d5b5f10ec2Locals mem_isValidAlignGeneric__anon_32d5b5f10ec2Exit).run' (default : mem_isValidAlignGeneric__anon_32d5b5f10ec2Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_isValidAlignLocals where
  deriving Inhabited

inductive mem_isValidAlignExit where
  | ret (v : Bool)

def mem_isValidAlign (p0 : BitVec 64) : Zig.Result (Bool) := do
  let e ← ((do
    let i1 ← Zig.call (mem_isValidAlignGeneric__anon_32d5b5f10ec2 p0)
    pure (.ret i1)) : Zig.M mem_isValidAlignLocals mem_isValidAlignExit).run' (default : mem_isValidAlignLocals)
  match e with
  | .ret v => pure v

structure mem_alignPointerOffset__anon_1fdb4fd23aeeLocals where
  ov : BitVec 64 × BitVec 1
  deriving Inhabited

inductive mem_alignPointerOffset__anon_1fdb4fd23aeeExit where
  | ret (v : Option (BitVec 64))
  | br4
  | br15
  | br31

def mem_alignPointerOffset__anon_1fdb4fd23aee (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (Option (BitVec 64)) := do
  let e ← ((do
    let i2 ← Zig.callR (mem_isValidAlign p1)
    let _i3 ← Zig.callR (debug_assert i2)
    match ← ((do
      let i5 ← pure (p1)
      let i6 ← pure (Zig.le false i5 (1 : BitVec 64))
      if i6 then (do
        pure (.ret (some (0 : BitVec 64))))
      else (do
        pure .br4)) : Zig.MM mem_alignPointerOffset__anon_1fdb4fd23aeeLocals mem_alignPointerOffset__anon_1fdb4fd23aeeExit) with
    | .br4 => (do
      let i10 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
      let i12 ← Zig.sub false p1 (1 : BitVec 64)
      let i13 ← pure (Zig.addWithOverflow false i10 i12)
      modify (fun s => { s with ov := i13 })
      match ← ((do
        let i17 ← pure (((← get).ov).snd)
        let i18 ← pure (i17 != (0 : BitVec 1))
        if i18 then (do
          pure (.ret none))
        else (do
          pure .br15)) : Zig.MM mem_alignPointerOffset__anon_1fdb4fd23aeeLocals mem_alignPointerOffset__anon_1fdb4fd23aeeExit) with
      | .br15 => (do
        let i23 ← pure (((← get).ov).fst)
        let i24 ← Zig.sub false p1 (1 : BitVec 64)
        let i25 ← pure (~~~i24)
        let i26 ← pure (i23 &&& i25)
        modify (fun s => { s with ov := { s.ov with fst := i26 } })
        let i29 ← pure (((← get).ov).fst)
        let i30 ← Zig.sub false i29 i10
        match ← ((do
          let i32 ← Zig.rem false i30 (1 : BitVec 64)
          let i33 ← pure (i32)
          let i34 ← pure (i33 != (0 : BitVec 64))
          if i34 then (do
            pure (.ret none))
          else (do
            pure .br31)) : Zig.MM mem_alignPointerOffset__anon_1fdb4fd23aeeLocals mem_alignPointerOffset__anon_1fdb4fd23aeeExit) with
        | .br31 => (do
          let i38 ← Zig.divTrunc false i30 (1 : BitVec 64)
          let i39 ← pure (some i38)
          pure (.ret i39))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM mem_alignPointerOffset__anon_1fdb4fd23aeeLocals mem_alignPointerOffset__anon_1fdb4fd23aeeExit).run' (default : mem_alignPointerOffset__anon_1fdb4fd23aeeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heap_FixedBufferAllocator_allocLocals where
  deriving Inhabited

inductive heap_FixedBufferAllocator_allocExit where
  | ret (v : Option (Zig.Ptr))
  | br7
  | br14 (v : BitVec 64)
  | br31

def heap_FixedBufferAllocator_alloc (p0 : Zig.Ptr) (p1 : BitVec 64) (p2 : mem_Alignment) (p3 : BitVec 64) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    let i4 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
    let i5 ← pure (i4 &&& (7 : BitVec 64))
    let i6 ← pure (i5 == (0 : BitVec 64))
    match ← ((do
      if i6 then (do
        pure .br7)
      else (do
        throw .panic)) : Zig.MM heap_FixedBufferAllocator_allocLocals heap_FixedBufferAllocator_allocExit) with
    | .br7 => (do
      let i12 ← Zig.callM (Zig.checkAlign 8 p0 >>= fun _ => pure p0)
      let i13 ← Zig.callR (mem_Alignment_toByteUnits p2)
      match ← ((do
        let i15 ← Zig.callM (Zig.ptrProject i12 (·.add 8))
        let i16 ← pure i15
        let i17 ← Zig.load (Zig.Ptr) 8 i16
        let i18 ← pure i12
        let i19 ← Zig.load (BitVec 64) 8 i18
        let i20 ← Zig.callM (Zig.ptrProject i17 (·.elem 1 i19))
        let i21 ← Zig.callM (mem_alignPointerOffset__anon_1fdb4fd23aee i20 i13)
        let i22 ← pure ((i21).isSome)
        if i22 then (do
          let i24 ← Zig.optPayload i21
          pure (.br14 i24))
        else (do
          pure (.ret none))) : Zig.MM heap_FixedBufferAllocator_allocLocals heap_FixedBufferAllocator_allocExit) with
      | .br14 v14 => (do
        let i27 ← pure i12
        let i28 ← Zig.load (BitVec 64) 8 i27
        let i29 ← Zig.add false i28 v14
        let i30 ← Zig.add false i29 p1
        match ← ((do
          let i32 ← Zig.callM (Zig.ptrProject i12 (·.add 8))
          let i33 ← Zig.callM (Zig.ptrProject i32 (·.add 8))
          let i34 ← Zig.load (BitVec 64) 8 i33
          let i35 ← pure (i30)
          let i36 ← pure (i34)
          let i37 ← pure (Zig.gt false i35 i36)
          if i37 then (do
            pure (.ret none))
          else (do
            pure .br31)) : Zig.MM heap_FixedBufferAllocator_allocLocals heap_FixedBufferAllocator_allocExit) with
        | .br31 => (do
          let i41 ← pure i12
          Zig.store (α := BitVec 64) 8 i41 i30
          let i43 ← Zig.callM (Zig.ptrProject i12 (·.add 8))
          let i44 ← pure i43
          let i45 ← Zig.load (Zig.Ptr) 8 i44
          let i46 ← Zig.callM (Zig.ptrProject i45 (·.elem 1 i29))
          let i47 ← pure (i46)
          pure (.ret i47))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM heap_FixedBufferAllocator_allocLocals heap_FixedBufferAllocator_allocExit).run' (default : heap_FixedBufferAllocator_allocLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bLocals where
  deriving Inhabited

inductive mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3
  | br10 (v : Option (Zig.Ptr))
  | br9 (v : Zig.Ptr)

def mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8b (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.MemM (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (⟨none, 18446744073709551615⟩ : Zig.Ptr) : Except Zig.ErrName (Zig.Ptr))))
      else (do
        pure .br3)) : Zig.MM mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bLocals mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bExit) with
    | .br3 => (do
      match ← ((do
        match ← ((do
          let i11 ← pure ((p0).vtable)
          let i12 ← pure i11
          let i13 ← Zig.load (Zig.Ptr) 8 i12
          let i14 ← pure ((p0).ptr)
          let i15 ← (if i13 == (⟨some 1, 0⟩ : Zig.Ptr) then Zig.callM (heap_FixedBufferAllocator_alloc i14 p1 mem_Alignment.«1» p2) else throw .illegal)
          pure (.br10 i15)) : Zig.MM mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bLocals mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bExit) with
        | .br10 v10 => (do
          let i17 ← pure ((v10).isSome)
          if i17 then (do
            let i19 ← Zig.optPayload v10
            pure (.br9 i19))
          else (do
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr)))))
        | e => pure e) : Zig.MM mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bLocals mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bExit) with
      | .br9 v9 => (do
        let i22 ← pure v9
        let i23 ← Zig.sub false p1 (0 : BitVec 64)
        let i24 ← pure (⟨i22, i23⟩ : Zig.Slice)
        let _i25 ← pure i24.len
        Zig.callM (Zig.memset (α := BitVec 8) 1 i24.ptr i24.len none)
        let i27 ← pure (v9)
        let i28 ← pure ((.ok i27) : Except Zig.ErrName (Zig.Ptr))
        pure (.ret i28))
      | e => pure e)
    | e => pure e) : Zig.MM mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bLocals mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bExit).run' (default : mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Locals where
  deriving Inhabited

inductive mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3 (v : BitVec 64)

def mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43 (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.MemM (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.callR (math_mul__anon_44faaf286c79 (1 : BitVec 64) p1)
      let i5 ← pure (Zig.isNonErr i4)
      if i5 then (do
        let i7 ← Zig.callR (Zig.unwrapPayload i4)
        pure (.br3 i7))
      else (do
        let _i9 ← Zig.callR (Zig.unwrapErr i4)
        pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr))))) : Zig.MM mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Locals mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Exit) with
    | .br3 v3 => (do
      let i11 ← Zig.callM (mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8b p0 v3 p2)
      pure (.ret i11))
    | e => pure e) : Zig.MM mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Locals mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Exit).run' (default : mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_alloc__anon_a8254a5f2b74Locals where
  deriving Inhabited

inductive mem_Allocator_alloc__anon_a8254a5f2b74Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br3 (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_alloc__anon_a8254a5f2b74 (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.MemM (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.callM Zig.returnAddress
    match ← ((do
      let i4 ← Zig.callM (mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43 p0 p1 i2)
      match i4 with
      | .error _ => (do
        let i6 ← Zig.callR (Zig.unwrapErr i4)
        let i7 ← pure ((.error i6) : Except Zig.ErrName (Zig.Slice))
        pure (.br3 i7))
      | .ok v5 => (do
        let i9 ← pure v5
        let i10 ← Zig.sub false p1 (0 : BitVec 64)
        let i11 ← pure (⟨i9, i10⟩ : Zig.Slice)
        let i12 ← pure ((.ok i11) : Except Zig.ErrName (Zig.Slice))
        pure (.br3 i12))) : Zig.MM mem_Allocator_alloc__anon_a8254a5f2b74Locals mem_Allocator_alloc__anon_a8254a5f2b74Exit) with
    | .br3 v3 => (do
      let i14 ← pure (v3)
      pure (.ret i14))
    | e => pure e) : Zig.MM mem_Allocator_alloc__anon_a8254a5f2b74Locals mem_Allocator_alloc__anon_a8254a5f2b74Exit).run' (default : mem_Allocator_alloc__anon_a8254a5f2b74Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_allocBytesWithAlignment__anon_4247f1fc6279Locals where
  deriving Inhabited

inductive mem_Allocator_allocBytesWithAlignment__anon_4247f1fc6279Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3
  | br10 (v : Option (Zig.Ptr))
  | br9 (v : Zig.Ptr)
  | br30

def mem_Allocator_allocBytesWithAlignment__anon_4247f1fc6279 (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.MemM (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (⟨none, 18446744073709551612⟩ : Zig.Ptr) : Except Zig.ErrName (Zig.Ptr))))
      else (do
        pure .br3)) : Zig.MM mem_Allocator_allocBytesWithAlignment__anon_4247f1fc6279Locals mem_Allocator_allocBytesWithAlignment__anon_4247f1fc6279Exit) with
    | .br3 => (do
      match ← ((do
        match ← ((do
          let i11 ← pure ((p0).vtable)
          let i12 ← pure i11
          let i13 ← Zig.load (Zig.Ptr) 8 i12
          let i14 ← pure ((p0).ptr)
          let i15 ← (if i13 == (⟨some 1, 0⟩ : Zig.Ptr) then Zig.callM (heap_FixedBufferAllocator_alloc i14 p1 mem_Alignment.«4» p2) else throw .illegal)
          pure (.br10 i15)) : Zig.MM mem_Allocator_allocBytesWithAlignment__anon_4247f1fc6279Locals mem_Allocator_allocBytesWithAlignment__anon_4247f1fc6279Exit) with
        | .br10 v10 => (do
          let i17 ← pure ((v10).isSome)
          if i17 then (do
            let i19 ← Zig.optPayload v10
            pure (.br9 i19))
          else (do
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr)))))
        | e => pure e) : Zig.MM mem_Allocator_allocBytesWithAlignment__anon_4247f1fc6279Locals mem_Allocator_allocBytesWithAlignment__anon_4247f1fc6279Exit) with
      | .br9 v9 => (do
        let i22 ← pure v9
        let i23 ← Zig.sub false p1 (0 : BitVec 64)
        let i24 ← pure (⟨i22, i23⟩ : Zig.Slice)
        let _i25 ← pure i24.len
        Zig.callM (Zig.memset (α := BitVec 8) 1 i24.ptr i24.len none)
        let i27 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr v9)))
        let i28 ← pure (i27 &&& (3 : BitVec 64))
        let i29 ← pure (i28 == (0 : BitVec 64))
        match ← ((do
          if i29 then (do
            pure .br30)
          else (do
            throw .panic)) : Zig.MM mem_Allocator_allocBytesWithAlignment__anon_4247f1fc6279Locals mem_Allocator_allocBytesWithAlignment__anon_4247f1fc6279Exit) with
        | .br30 => (do
          let i35 ← Zig.callM (Zig.checkAlign 4 v9 >>= fun _ => pure v9)
          let i36 ← pure ((.ok i35) : Except Zig.ErrName (Zig.Ptr))
          pure (.ret i36))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM mem_Allocator_allocBytesWithAlignment__anon_4247f1fc6279Locals mem_Allocator_allocBytesWithAlignment__anon_4247f1fc6279Exit).run' (default : mem_Allocator_allocBytesWithAlignment__anon_4247f1fc6279Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_allocWithSizeAndAlignment__anon_5c898506c1d8Locals where
  deriving Inhabited

inductive mem_Allocator_allocWithSizeAndAlignment__anon_5c898506c1d8Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3 (v : BitVec 64)

def mem_Allocator_allocWithSizeAndAlignment__anon_5c898506c1d8 (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.MemM (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.callR (math_mul__anon_44faaf286c79 (1 : BitVec 64) p1)
      let i5 ← pure (Zig.isNonErr i4)
      if i5 then (do
        let i7 ← Zig.callR (Zig.unwrapPayload i4)
        pure (.br3 i7))
      else (do
        let _i9 ← Zig.callR (Zig.unwrapErr i4)
        pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr))))) : Zig.MM mem_Allocator_allocWithSizeAndAlignment__anon_5c898506c1d8Locals mem_Allocator_allocWithSizeAndAlignment__anon_5c898506c1d8Exit) with
    | .br3 v3 => (do
      let i11 ← Zig.callM (mem_Allocator_allocBytesWithAlignment__anon_4247f1fc6279 p0 v3 p2)
      pure (.ret i11))
    | e => pure e) : Zig.MM mem_Allocator_allocWithSizeAndAlignment__anon_5c898506c1d8Locals mem_Allocator_allocWithSizeAndAlignment__anon_5c898506c1d8Exit).run' (default : mem_Allocator_allocWithSizeAndAlignment__anon_5c898506c1d8Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_alignedAlloc__anon_48ad47c7aa48Locals where
  deriving Inhabited

inductive mem_Allocator_alignedAlloc__anon_48ad47c7aa48Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br3 (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_alignedAlloc__anon_48ad47c7aa48 (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.MemM (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.callM Zig.returnAddress
    match ← ((do
      let i4 ← Zig.callM (mem_Allocator_allocWithSizeAndAlignment__anon_5c898506c1d8 p0 p1 i2)
      match i4 with
      | .error _ => (do
        let i6 ← Zig.callR (Zig.unwrapErr i4)
        let i7 ← pure ((.error i6) : Except Zig.ErrName (Zig.Slice))
        pure (.br3 i7))
      | .ok v5 => (do
        let i9 ← pure v5
        let i10 ← Zig.sub false p1 (0 : BitVec 64)
        let i11 ← pure (⟨i9, i10⟩ : Zig.Slice)
        let i12 ← pure ((.ok i11) : Except Zig.ErrName (Zig.Slice))
        pure (.br3 i12))) : Zig.MM mem_Allocator_alignedAlloc__anon_48ad47c7aa48Locals mem_Allocator_alignedAlloc__anon_48ad47c7aa48Exit) with
    | .br3 v3 => (do
      pure (.ret v3))
    | e => pure e) : Zig.MM mem_Allocator_alignedAlloc__anon_48ad47c7aa48Locals mem_Allocator_alignedAlloc__anon_48ad47c7aa48Exit).run' (default : mem_Allocator_alignedAlloc__anon_48ad47c7aa48Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_absorbSentinel__anon_7d261968039cLocals where
  deriving Inhabited

inductive mem_absorbSentinel__anon_7d261968039cExit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_7d261968039c (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret p0)) : Zig.MM mem_absorbSentinel__anon_7d261968039cLocals mem_absorbSentinel__anon_7d261968039cExit).run' (default : mem_absorbSentinel__anon_7d261968039cLocals)
  match e with
  | .ret v => pure v

structure mem_Alignment_fromByteUnitsLocals where
  deriving Inhabited

inductive mem_Alignment_fromByteUnitsExit where
  | ret (v : mem_Alignment)

def mem_Alignment_fromByteUnits (p0 : BitVec 64) : Zig.Result (mem_Alignment) := do
  let e ← ((do
    let i1 ← Zig.call (math_isPowerOfTwo__anon_38853e1fe316 p0)
    let _i2 ← Zig.call (debug_assert i1)
    let i3 ← pure (Zig.ctz 7 p0)
    let i4 ← Zig.enumOf (mem_Alignment.ofInt? (Zig.val false i3))
    pure (.ret i4)) : Zig.M mem_Alignment_fromByteUnitsLocals mem_Alignment_fromByteUnitsExit).run' (default : mem_Alignment_fromByteUnitsLocals)
  match e with
  | .ret v => pure v

structure heap_FixedBufferAllocator_sliceContainsSliceLocals where
  local2 : Zig.Slice
  local5 : Zig.Slice
  deriving Inhabited

inductive heap_FixedBufferAllocator_sliceContainsSliceExit where
  | ret (v : Bool)
  | br17 (v : Bool)

def heap_FixedBufferAllocator_sliceContainsSlice (p0 : Zig.Slice) (p1 : Zig.Slice) : Zig.MemM (Bool) := do
  let e ← ((do
    modify (fun s => { s with local2 := p0 })
    modify (fun s => { s with local5 := p1 })
    let i9 ← pure (((← get).local5).ptr)
    let i10 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i9)))
    let i12 ← pure (((← get).local2).ptr)
    let i13 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i12)))
    let i14 ← pure (i10)
    let i15 ← pure (i13)
    let i16 ← pure (Zig.ge false i14 i15)
    match ← ((do
      if i16 then (do
        let i20 ← pure (((← get).local5).ptr)
        let i21 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i20)))
        let i23 ← pure (((← get).local5).len)
        let i24 ← Zig.add false i21 i23
        let i26 ← pure (((← get).local2).ptr)
        let i27 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i26)))
        let i29 ← pure (((← get).local2).len)
        let i30 ← Zig.add false i27 i29
        let i31 ← pure (i24)
        let i32 ← pure (i30)
        let i33 ← pure (Zig.le false i31 i32)
        pure (.br17 i33))
      else (do
        pure (.br17 false))) : Zig.MM heap_FixedBufferAllocator_sliceContainsSliceLocals heap_FixedBufferAllocator_sliceContainsSliceExit) with
    | .br17 v17 => (do
      pure (.ret v17))
    | e => pure e) : Zig.MM heap_FixedBufferAllocator_sliceContainsSliceLocals heap_FixedBufferAllocator_sliceContainsSliceExit).run' (default : heap_FixedBufferAllocator_sliceContainsSliceLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heap_FixedBufferAllocator_ownsSliceLocals where
  deriving Inhabited

inductive heap_FixedBufferAllocator_ownsSliceExit where
  | ret (v : Bool)

def heap_FixedBufferAllocator_ownsSlice (p0 : Zig.Ptr) (p1 : Zig.Slice) : Zig.MemM (Bool) := do
  let e ← ((do
    let i2 ← Zig.callM (Zig.ptrProject p0 (·.add 8))
    let i3 ← Zig.load (Zig.Slice) 8 i2
    let i4 ← Zig.callM (heap_FixedBufferAllocator_sliceContainsSlice i3 p1)
    pure (.ret i4)) : Zig.MM heap_FixedBufferAllocator_ownsSliceLocals heap_FixedBufferAllocator_ownsSliceExit).run' (default : heap_FixedBufferAllocator_ownsSliceLocals)
  match e with
  | .ret v => pure v

structure heap_FixedBufferAllocator_isLastAllocationLocals where
  local2 : Zig.Slice
  deriving Inhabited

inductive heap_FixedBufferAllocator_isLastAllocationExit where
  | ret (v : Bool)

def heap_FixedBufferAllocator_isLastAllocation (p0 : Zig.Ptr) (p1 : Zig.Slice) : Zig.MemM (Bool) := do
  let e ← ((do
    modify (fun s => { s with local2 := p1 })
    let i6 ← pure (((← get).local2).ptr)
    let i8 ← pure (((← get).local2).len)
    let i9 ← Zig.callM (Zig.ptrProject i6 (·.elem 1 i8))
    let i10 ← Zig.callM (Zig.ptrProject p0 (·.add 8))
    let i11 ← pure i10
    let i12 ← Zig.load (Zig.Ptr) 8 i11
    let i13 ← pure p0
    let i14 ← Zig.load (BitVec 64) 8 i13
    let i15 ← Zig.callM (Zig.ptrProject i12 (·.elem 1 i14))
    let i16 ← Zig.callM (Zig.ptrEqAddr i9 i15)
    pure (.ret i16)) : Zig.MM heap_FixedBufferAllocator_isLastAllocationLocals heap_FixedBufferAllocator_isLastAllocationExit).run' (default : heap_FixedBufferAllocator_isLastAllocationLocals)
  match e with
  | .ret v => pure v

structure heap_FixedBufferAllocator_freeLocals where
  deriving Inhabited

inductive heap_FixedBufferAllocator_freeExit where
  | ret
  | br7
  | br15

def heap_FixedBufferAllocator_free (p0 : Zig.Ptr) (p1 : Zig.Slice) (p2 : mem_Alignment) (p3 : BitVec 64) : Zig.MemM (Unit) := do
  let e ← ((do
    let i4 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
    let i5 ← pure (i4 &&& (7 : BitVec 64))
    let i6 ← pure (i5 == (0 : BitVec 64))
    match ← ((do
      if i6 then (do
        pure .br7)
      else (do
        throw .panic)) : Zig.MM heap_FixedBufferAllocator_freeLocals heap_FixedBufferAllocator_freeExit) with
    | .br7 => (do
      let i12 ← Zig.callM (Zig.checkAlign 8 p0 >>= fun _ => pure p0)
      let i13 ← Zig.callM (heap_FixedBufferAllocator_ownsSlice i12 p1)
      let _i14 ← Zig.callR (debug_assert i13)
      match ← ((do
        let i16 ← Zig.callM (heap_FixedBufferAllocator_isLastAllocation i12 p1)
        if i16 then (do
          let i18 ← pure i12
          let i19 ← Zig.load (BitVec 64) 8 i18
          let i20 ← pure p1.len
          let i21 ← Zig.sub false i19 i20
          Zig.store (α := BitVec 64) 8 i18 i21
          pure .br15)
        else (do
          pure .br15)) : Zig.MM heap_FixedBufferAllocator_freeLocals heap_FixedBufferAllocator_freeExit) with
      | .br15 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.MM heap_FixedBufferAllocator_freeLocals heap_FixedBufferAllocator_freeExit).run' (default : heap_FixedBufferAllocator_freeLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure mem_Allocator_free__anon_fde0a0a56281Locals where
  deriving Inhabited

inductive mem_Allocator_free__anon_fde0a0a56281Exit where
  | ret
  | br4
  | br15

def mem_Allocator_free__anon_fde0a0a56281 (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← Zig.callM (mem_absorbSentinel__anon_7d261968039c p1)
    let i3 ← pure (i2)
    match ← ((do
      let i5 ← pure i3.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        pure .ret)
      else (do
        pure .br4)) : Zig.MM mem_Allocator_free__anon_fde0a0a56281Locals mem_Allocator_free__anon_fde0a0a56281Exit) with
    | .br4 => (do
      let _i11 ← pure i3.len
      Zig.callM (Zig.memset (α := BitVec 8) 1 i3.ptr i3.len none)
      let i13 ← Zig.callR (mem_Alignment_fromByteUnits (4 : BitVec 64))
      let i14 ← Zig.callM Zig.returnAddress
      match ← ((do
        let i16 ← pure ((p0).vtable)
        let i17 ← Zig.callM (Zig.ptrProject i16 (·.add 24))
        let i18 ← Zig.load (Zig.Ptr) 8 i17
        let i19 ← pure ((p0).ptr)
        let _i20 ← (if i18 == (⟨some 4, 0⟩ : Zig.Ptr) then Zig.callM (heap_FixedBufferAllocator_free i19 i3 i13 i14) else throw .illegal)
        pure .br15) : Zig.MM mem_Allocator_free__anon_fde0a0a56281Locals mem_Allocator_free__anon_fde0a0a56281Exit) with
      | .br15 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.MM mem_Allocator_free__anon_fde0a0a56281Locals mem_Allocator_free__anon_fde0a0a56281Exit).run' (default : mem_Allocator_free__anon_fde0a0a56281Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure fba_alignedLocals where
  fba : Zig.Ptr
  local21 : Zig.Slice
  deriving Inhabited

inductive fba_alignedExit where
  | ret (v : BitVec 64)
  | br5
  | br13 (v : Zig.Slice)

def fba_aligned (p0 : BitVec 64) : Zig.MemM (BitVec 64) := do
  let s1 ← Zig.allocStack 24 8
  let e ← ((do
    let i1 ← pure (← get).fba
    let i2 ← Zig.callM (heap_FixedBufferAllocator_init (⟨(⟨some 0, 0⟩ : Zig.Ptr), (12 : BitVec 64)⟩ : Zig.Slice))
    Zig.store (α := heap_FixedBufferAllocator) 8 i1 i2
    let i4 ← Zig.callM (heap_FixedBufferAllocator_allocator i1)
    match ← ((do
      let i6 ← Zig.callM (mem_Allocator_alloc__anon_a8254a5f2b74 i4 (1 : BitVec 64))
      let i7 ← pure (Zig.isNonErr i6)
      if i7 then (do
        let _i9 ← Zig.callR (Zig.unwrapPayload i6)
        pure .br5)
      else (do
        let _i11 ← Zig.callR (Zig.unwrapErr i6)
        pure (.ret (0 : BitVec 64)))) : Zig.MM fba_alignedLocals fba_alignedExit) with
    | .br5 => (do
      match ← ((do
        let i14 ← Zig.callM (mem_Allocator_alignedAlloc__anon_48ad47c7aa48 i4 p0)
        let i15 ← pure (Zig.isNonErr i14)
        if i15 then (do
          let i17 ← Zig.callR (Zig.unwrapPayload i14)
          pure (.br13 i17))
        else (do
          let _i19 ← Zig.callR (Zig.unwrapErr i14)
          pure (.ret (1 : BitVec 64)))) : Zig.MM fba_alignedLocals fba_alignedExit) with
      | .br13 v13 => (do
        modify (fun s => { s with local21 := v13 })
        let i25 ← pure (((← get).local21).ptr)
        let i26 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i25)))
        let i27 ← Zig.rem false i26 (4 : BitVec 64)
        let _i28 ← Zig.callM (mem_Allocator_free__anon_fde0a0a56281 i4 v13)
        let i30 ← pure (((← get).local21).len)
        let i31 ← Zig.add false i27 i30
        pure (.ret i31))
      | e => pure e)
    | e => pure e) : Zig.MM fba_alignedLocals fba_alignedExit).run' { (default : fba_alignedLocals) with fba := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_absorbSentinel__anon_7342b53a30edLocals where
  deriving Inhabited

inductive mem_absorbSentinel__anon_7342b53a30edExit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_7342b53a30ed (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret p0)) : Zig.MM mem_absorbSentinel__anon_7342b53a30edLocals mem_absorbSentinel__anon_7342b53a30edExit).run' (default : mem_absorbSentinel__anon_7342b53a30edLocals)
  match e with
  | .ret v => pure v

structure mem_Allocator_free__anon_1e60e7ef40f5Locals where
  deriving Inhabited

inductive mem_Allocator_free__anon_1e60e7ef40f5Exit where
  | ret
  | br4
  | br15

def mem_Allocator_free__anon_1e60e7ef40f5 (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← Zig.callM (mem_absorbSentinel__anon_7342b53a30ed p1)
    let i3 ← pure (i2)
    match ← ((do
      let i5 ← pure i3.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        pure .ret)
      else (do
        pure .br4)) : Zig.MM mem_Allocator_free__anon_1e60e7ef40f5Locals mem_Allocator_free__anon_1e60e7ef40f5Exit) with
    | .br4 => (do
      let _i11 ← pure i3.len
      Zig.callM (Zig.memset (α := BitVec 8) 1 i3.ptr i3.len none)
      let i13 ← Zig.callR (mem_Alignment_fromByteUnits (1 : BitVec 64))
      let i14 ← Zig.callM Zig.returnAddress
      match ← ((do
        let i16 ← pure ((p0).vtable)
        let i17 ← Zig.callM (Zig.ptrProject i16 (·.add 24))
        let i18 ← Zig.load (Zig.Ptr) 8 i17
        let i19 ← pure ((p0).ptr)
        let _i20 ← (if i18 == (⟨some 4, 0⟩ : Zig.Ptr) then Zig.callM (heap_FixedBufferAllocator_free i19 i3 i13 i14) else throw .illegal)
        pure .br15) : Zig.MM mem_Allocator_free__anon_1e60e7ef40f5Locals mem_Allocator_free__anon_1e60e7ef40f5Exit) with
      | .br15 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.MM mem_Allocator_free__anon_1e60e7ef40f5Locals mem_Allocator_free__anon_1e60e7ef40f5Exit).run' (default : mem_Allocator_free__anon_1e60e7ef40f5Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure heap_FixedBufferAllocator_resizeLocals where
  deriving Inhabited

inductive heap_FixedBufferAllocator_resizeExit where
  | ret (v : Bool)
  | br8
  | br20
  | br16
  | br30
  | br46

def heap_FixedBufferAllocator_resize (p0 : Zig.Ptr) (p1 : Zig.Slice) (p2 : mem_Alignment) (p3 : BitVec 64) (p4 : BitVec 64) : Zig.MemM (Bool) := do
  let e ← ((do
    let i5 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
    let i6 ← pure (i5 &&& (7 : BitVec 64))
    let i7 ← pure (i6 == (0 : BitVec 64))
    match ← ((do
      if i7 then (do
        pure .br8)
      else (do
        throw .panic)) : Zig.MM heap_FixedBufferAllocator_resizeLocals heap_FixedBufferAllocator_resizeExit) with
    | .br8 => (do
      let i13 ← Zig.callM (Zig.checkAlign 8 p0 >>= fun _ => pure p0)
      let i14 ← Zig.callM (heap_FixedBufferAllocator_ownsSlice i13 p1)
      let _i15 ← Zig.callR (debug_assert i14)
      match ← ((do
        let i17 ← Zig.callM (heap_FixedBufferAllocator_isLastAllocation i13 p1)
        let i18 ← pure (!i17)
        if i18 then (do
          match ← ((do
            let i21 ← pure p1.len
            let i22 ← pure (p3)
            let i23 ← pure (i21)
            let i24 ← pure (Zig.gt false i22 i23)
            if i24 then (do
              pure (.ret false))
            else (do
              pure .br20)) : Zig.MM heap_FixedBufferAllocator_resizeLocals heap_FixedBufferAllocator_resizeExit) with
          | .br20 => (do
            pure (.ret true))
          | e => pure e)
        else (do
          pure .br16)) : Zig.MM heap_FixedBufferAllocator_resizeLocals heap_FixedBufferAllocator_resizeExit) with
      | .br16 => (do
        match ← ((do
          let i31 ← pure p1.len
          let i32 ← pure (p3)
          let i33 ← pure (i31)
          let i34 ← pure (Zig.le false i32 i33)
          if i34 then (do
            let i36 ← pure p1.len
            let i37 ← Zig.sub false i36 p3
            let i38 ← pure i13
            let i39 ← Zig.load (BitVec 64) 8 i38
            let i40 ← Zig.sub false i39 i37
            Zig.store (α := BitVec 64) 8 i38 i40
            pure (.ret true))
          else (do
            pure .br30)) : Zig.MM heap_FixedBufferAllocator_resizeLocals heap_FixedBufferAllocator_resizeExit) with
        | .br30 => (do
          let i44 ← pure p1.len
          let i45 ← Zig.sub false p3 i44
          match ← ((do
            let i47 ← pure i13
            let i48 ← Zig.load (BitVec 64) 8 i47
            let i49 ← Zig.add false i45 i48
            let i50 ← Zig.callM (Zig.ptrProject i13 (·.add 8))
            let i51 ← Zig.callM (Zig.ptrProject i50 (·.add 8))
            let i52 ← Zig.load (BitVec 64) 8 i51
            let i53 ← pure (i49)
            let i54 ← pure (i52)
            let i55 ← pure (Zig.gt false i53 i54)
            if i55 then (do
              pure (.ret false))
            else (do
              pure .br46)) : Zig.MM heap_FixedBufferAllocator_resizeLocals heap_FixedBufferAllocator_resizeExit) with
          | .br46 => (do
            let i59 ← pure i13
            let i60 ← Zig.load (BitVec 64) 8 i59
            let i61 ← Zig.add false i60 i45
            Zig.store (α := BitVec 64) 8 i59 i61
            pure (.ret true))
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM heap_FixedBufferAllocator_resizeLocals heap_FixedBufferAllocator_resizeExit).run' (default : heap_FixedBufferAllocator_resizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heap_FixedBufferAllocator_remapLocals where
  local5 : Zig.Slice
  deriving Inhabited

inductive heap_FixedBufferAllocator_remapExit where
  | ret (v : Option (Zig.Ptr))
  | br8 (v : Option (Zig.Ptr))

def heap_FixedBufferAllocator_remap (p0 : Zig.Ptr) (p1 : Zig.Slice) (p2 : mem_Alignment) (p3 : BitVec 64) (p4 : BitVec 64) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    modify (fun s => { s with local5 := p1 })
    match ← ((do
      let i9 ← Zig.callM (heap_FixedBufferAllocator_resize p0 p1 p2 p3 p4)
      if i9 then (do
        let i12 ← pure (((← get).local5).ptr)
        let i13 ← pure (i12)
        pure (.br8 i13))
      else (do
        pure (.br8 none))) : Zig.MM heap_FixedBufferAllocator_remapLocals heap_FixedBufferAllocator_remapExit) with
    | .br8 v8 => (do
      pure (.ret v8))
    | e => pure e) : Zig.MM heap_FixedBufferAllocator_remapLocals heap_FixedBufferAllocator_remapExit).run' (default : heap_FixedBufferAllocator_remapLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals where
  deriving Inhabited

inductive mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br9 (v : Except Zig.ErrName (Zig.Slice))
  | br4
  | br23
  | br32 (v : BitVec 64)
  | br42 (v : Option (Zig.Ptr))
  | br40
  | br61 (v : Option (Zig.Ptr))
  | br59 (v : Zig.Ptr)
  | br87
  | br96
  | br108
  | br117

def mem_Allocator_reallocAdvanced__anon_0df1ef68623e (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) (p3 : BitVec 64) : Zig.MemM (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    match ← ((do
      let i5 ← pure p1.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        match ← ((do
          let i10 ← Zig.callM (mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43 p0 p2 p3)
          match i10 with
          | .error _ => (do
            let i12 ← Zig.callR (Zig.unwrapErr i10)
            let i13 ← pure ((.error i12) : Except Zig.ErrName (Zig.Slice))
            pure (.br9 i13))
          | .ok v11 => (do
            let i15 ← pure v11
            let i16 ← Zig.sub false p2 (0 : BitVec 64)
            let i17 ← pure (⟨i15, i16⟩ : Zig.Slice)
            let i18 ← pure ((.ok i17) : Except Zig.ErrName (Zig.Slice))
            pure (.br9 i18))) : Zig.MM mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
        | .br9 v9 => (do
          let i20 ← pure (v9)
          pure (.ret i20))
        | e => pure e)
      else (do
        pure .br4)) : Zig.MM mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
    | .br4 => (do
      match ← ((do
        let i24 ← pure (p2)
        let i25 ← pure (i24 == (0 : BitVec 64))
        if i25 then (do
          let _i27 ← Zig.callM (mem_Allocator_free__anon_1e60e7ef40f5 p0 p1)
          pure (.ret (.ok (⟨(⟨none, 18446744073709551615⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice) : Except Zig.ErrName (Zig.Slice))))
        else (do
          pure .br23)) : Zig.MM mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
      | .br23 => (do
        let i30 ← Zig.callM (mem_absorbSentinel__anon_7342b53a30ed p1)
        let i31 ← pure (i30)
        match ← ((do
          let i33 ← Zig.callR (math_mul__anon_44faaf286c79 (1 : BitVec 64) p2)
          let i34 ← pure (Zig.isNonErr i33)
          if i34 then (do
            let i36 ← Zig.callR (Zig.unwrapPayload i33)
            pure (.br32 i36))
          else (do
            let _i38 ← Zig.callR (Zig.unwrapErr i33)
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice))))) : Zig.MM mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
        | .br32 v32 => (do
          match ← ((do
            let i41 ← Zig.callR (mem_Alignment_fromByteUnits (1 : BitVec 64))
            match ← ((do
              let i43 ← pure ((p0).vtable)
              let i44 ← Zig.callM (Zig.ptrProject i43 (·.add 16))
              let i45 ← Zig.load (Zig.Ptr) 8 i44
              let i46 ← pure ((p0).ptr)
              let i47 ← (if i45 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callM (heap_FixedBufferAllocator_remap i46 i31 i41 v32 p3) else throw .illegal)
              pure (.br42 i47)) : Zig.MM mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
            | .br42 v42 => (do
              let i49 ← pure ((v42).isSome)
              if i49 then (do
                let i51 ← Zig.optPayload v42
                let i52 ← pure i51
                let i53 ← Zig.sub false v32 (0 : BitVec 64)
                let i54 ← pure (⟨i52, i53⟩ : Zig.Slice)
                let i55 ← pure (i54)
                let i56 ← pure ((.ok i55) : Except Zig.ErrName (Zig.Slice))
                pure (.ret i56))
              else (do
                pure .br40))
            | e => pure e) : Zig.MM mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
          | .br40 => (do
            match ← ((do
              let i60 ← Zig.callR (mem_Alignment_fromByteUnits (1 : BitVec 64))
              match ← ((do
                let i62 ← pure ((p0).vtable)
                let i63 ← pure i62
                let i64 ← Zig.load (Zig.Ptr) 8 i63
                let i65 ← pure ((p0).ptr)
                let i66 ← (if i64 == (⟨some 1, 0⟩ : Zig.Ptr) then Zig.callM (heap_FixedBufferAllocator_alloc i65 v32 i60 p3) else throw .illegal)
                pure (.br61 i66)) : Zig.MM mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
              | .br61 v61 => (do
                let i68 ← pure ((v61).isSome)
                if i68 then (do
                  let i70 ← Zig.optPayload v61
                  pure (.br59 i70))
                else (do
                  pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice)))))
              | e => pure e) : Zig.MM mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
            | .br59 v59 => (do
              let i73 ← pure i31.len
              let i74 ← pure (v32)
              let i75 ← pure (i73)
              let i76 ← pure (Zig.min false i74 i75)
              let i77 ← pure v59
              let i78 ← pure (i76)
              let i79 ← Zig.sub false i78 (0 : BitVec 64)
              let i80 ← pure (⟨i77, i79⟩ : Zig.Slice)
              let i81 ← pure i31.ptr
              let i82 ← pure i81
              let i83 ← pure (i76)
              let i84 ← Zig.sub false i83 (0 : BitVec 64)
              let i85 ← pure i31.len
              let i86 ← pure (Zig.le false i83 i85)
              match ← ((do
                if i86 then (do
                  pure .br87)
                else (do
                  throw .outOfBounds)) : Zig.MM mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
              | .br87 => (do
                let i92 ← Zig.callM (Zig.checkSliceEnd i31.len (0 : BitVec 64) i84 0 >>= fun _ => pure (⟨i82, i84⟩ : Zig.Slice))
                let i93 ← pure i80.len
                let i94 ← pure i92.len
                let i95 ← pure (i93 == i94)
                match ← ((do
                  if i95 then (do
                    pure .br96)
                  else (do
                    throw .panic)) : Zig.MM mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
                | .br96 => (do
                  let i101 ← pure i92.ptr
                  let i102 ← pure i80.ptr
                  let i103 ← Zig.callM (Zig.ptrProject i101 (·.elem 1 i93))
                  let i104 ← Zig.callM (Zig.ptrProject i102 (·.elem 1 i93))
                  let i105 ← Zig.callM (Zig.ptrLe i103 i102)
                  let i106 ← Zig.callM (Zig.ptrLe i104 i101)
                  let i107 ← pure (i105 || i106)
                  match ← ((do
                    if i107 then (do
                      pure .br108)
                    else (do
                      throw .panic)) : Zig.MM mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
                  | .br108 => (do
                    Zig.callM (Zig.memcpy 1 1 1 i80.ptr i101 i80.len i92.len)
                    let _i114 ← pure i31.len
                    Zig.callM (Zig.memset (α := BitVec 8) 1 i31.ptr i31.len none)
                    let i116 ← Zig.callR (mem_Alignment_fromByteUnits (1 : BitVec 64))
                    match ← ((do
                      let i118 ← pure ((p0).vtable)
                      let i119 ← Zig.callM (Zig.ptrProject i118 (·.add 24))
                      let i120 ← Zig.load (Zig.Ptr) 8 i119
                      let i121 ← pure ((p0).ptr)
                      let _i122 ← (if i120 == (⟨some 4, 0⟩ : Zig.Ptr) then Zig.callM (heap_FixedBufferAllocator_free i121 i31 i116 p3) else throw .illegal)
                      pure .br117) : Zig.MM mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
                    | .br117 => (do
                      let i124 ← pure v59
                      let i125 ← Zig.sub false v32 (0 : BitVec 64)
                      let i126 ← pure (⟨i124, i125⟩ : Zig.Slice)
                      let i127 ← pure (i126)
                      let i128 ← pure ((.ok i127) : Except Zig.ErrName (Zig.Slice))
                      pure (.ret i128))
                    | e => pure e)
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit).run' (default : mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_realloc__anon_af0c43114565Locals where
  deriving Inhabited

inductive mem_Allocator_realloc__anon_af0c43114565Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_realloc__anon_af0c43114565 (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.MemM (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.callM Zig.returnAddress
    let i4 ← Zig.callM (mem_Allocator_reallocAdvanced__anon_0df1ef68623e p0 p1 p2 i3)
    pure (.ret i4)) : Zig.MM mem_Allocator_realloc__anon_af0c43114565Locals mem_Allocator_realloc__anon_af0c43114565Exit).run' (default : mem_Allocator_realloc__anon_af0c43114565Locals)
  match e with
  | .ret v => pure v

structure heap_FixedBufferAllocator_resetLocals where
  deriving Inhabited

inductive heap_FixedBufferAllocator_resetExit where
  | ret

def heap_FixedBufferAllocator_reset (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    Zig.store (α := BitVec 64) 8 i1 (0 : BitVec 64)
    pure .ret) : Zig.MM heap_FixedBufferAllocator_resetLocals heap_FixedBufferAllocator_resetExit).run' (default : heap_FixedBufferAllocator_resetLocals)
  match e with
  | .ret => pure ()

structure fba_clientLocals where
  fba : Zig.Ptr
  deriving Inhabited

inductive fba_clientExit where
  | ret (v : BitVec 32)
  | br5 (v : Zig.Slice)
  | br15 (v : Zig.Slice)
  | br25
  | br33
  | br45
  | br54
  | br64
  | br74 (v : Zig.Slice)
  | br84
  | br93

def fba_client (p0 : BitVec 8) : Zig.MemM (BitVec 32) := do
  let s1 ← Zig.allocStack 24 8
  let e ← ((do
    let i1 ← pure (← get).fba
    let i2 ← Zig.callM (heap_FixedBufferAllocator_init (⟨(⟨some 0, 0⟩ : Zig.Ptr), (12 : BitVec 64)⟩ : Zig.Slice))
    Zig.store (α := heap_FixedBufferAllocator) 8 i1 i2
    let i4 ← Zig.callM (heap_FixedBufferAllocator_allocator i1)
    match ← ((do
      let i6 ← Zig.callM (mem_Allocator_alloc__anon_a8254a5f2b74 i4 (4 : BitVec 64))
      let i7 ← pure (Zig.isNonErr i6)
      if i7 then (do
        let i9 ← Zig.callR (Zig.unwrapPayload i6)
        pure (.br5 i9))
      else (do
        let _i11 ← Zig.callR (Zig.unwrapErr i6)
        pure (.ret (1 : BitVec 32)))) : Zig.MM fba_clientLocals fba_clientExit) with
    | .br5 v5 => (do
      let _i13 ← pure v5.len
      Zig.callM (Zig.memset (α := BitVec 8) 1 v5.ptr v5.len (some p0))
      match ← ((do
        let i16 ← Zig.callM (mem_Allocator_realloc__anon_af0c43114565 i4 v5 (8 : BitVec 64))
        let i17 ← pure (Zig.isNonErr i16)
        if i17 then (do
          let i19 ← Zig.callR (Zig.unwrapPayload i16)
          pure (.br15 i19))
        else (do
          let _i21 ← Zig.callR (Zig.unwrapErr i16)
          pure (.ret (2 : BitVec 32)))) : Zig.MM fba_clientLocals fba_clientExit) with
      | .br15 v15 => (do
        let i23 ← pure v15.len
        let i24 ← pure (Zig.lt false (7 : BitVec 64) i23)
        match ← ((do
          if i24 then (do
            pure .br25)
          else (do
            throw .outOfBounds)) : Zig.MM fba_clientLocals fba_clientExit) with
        | .br25 => (do
          let i30 ← Zig.callM (Zig.ptrProject v15.ptr (·.elem 1 (7 : BitVec 64)))
          let i31 ← pure (Zig.addWrap p0 (1 : BitVec 8))
          Zig.store (α := BitVec 8) 1 i30 i31
          match ← ((do
            let i34 ← Zig.callM (mem_Allocator_alloc__anon_a8254a5f2b74 i4 (64 : BitVec 64))
            let i35 ← pure (Zig.isNonErr i34)
            if i35 then (do
              let i37 ← Zig.callR (Zig.unwrapPayload i34)
              let _i38 ← Zig.callM (mem_Allocator_free__anon_1e60e7ef40f5 i4 i37)
              pure (.ret (3 : BitVec 32)))
            else (do
              let _i40 ← Zig.callR (Zig.unwrapErr i34)
              let _i41 ← Zig.callR (Zig.unwrapErr i34)
              pure .br33)) : Zig.MM fba_clientLocals fba_clientExit) with
          | .br33 => (do
            let i43 ← pure v15.len
            let i44 ← pure (Zig.lt false (0 : BitVec 64) i43)
            match ← ((do
              if i44 then (do
                pure .br45)
              else (do
                throw .outOfBounds)) : Zig.MM fba_clientLocals fba_clientExit) with
            | .br45 => (do
              let i50 ← Zig.callM (Zig.checkIndex v15 (0 : BitVec 64) >>= fun _ => Zig.load (BitVec 8) 1 (v15.ptr.elem 1 (0 : BitVec 64)))
              let i51 ← Zig.intCast false false 32 i50
              let i52 ← pure v15.len
              let i53 ← pure (Zig.lt false (3 : BitVec 64) i52)
              match ← ((do
                if i53 then (do
                  pure .br54)
                else (do
                  throw .outOfBounds)) : Zig.MM fba_clientLocals fba_clientExit) with
              | .br54 => (do
                let i59 ← Zig.callM (Zig.checkIndex v15 (3 : BitVec 64) >>= fun _ => Zig.load (BitVec 8) 1 (v15.ptr.elem 1 (3 : BitVec 64)))
                let i60 ← Zig.intCast false false 32 i59
                let i61 ← Zig.add false i51 i60
                let i62 ← pure v15.len
                let i63 ← pure (Zig.lt false (7 : BitVec 64) i62)
                match ← ((do
                  if i63 then (do
                    pure .br64)
                  else (do
                    throw .outOfBounds)) : Zig.MM fba_clientLocals fba_clientExit) with
                | .br64 => (do
                  let i69 ← Zig.callM (Zig.checkIndex v15 (7 : BitVec 64) >>= fun _ => Zig.load (BitVec 8) 1 (v15.ptr.elem 1 (7 : BitVec 64)))
                  let i70 ← Zig.intCast false false 32 i69
                  let i71 ← Zig.add false i61 i70
                  let _i72 ← Zig.callM (mem_Allocator_free__anon_1e60e7ef40f5 i4 v15)
                  let _i73 ← Zig.callM (heap_FixedBufferAllocator_reset i1)
                  match ← ((do
                    let i75 ← Zig.callM (mem_Allocator_alloc__anon_a8254a5f2b74 i4 (12 : BitVec 64))
                    let i76 ← pure (Zig.isNonErr i75)
                    if i76 then (do
                      let i78 ← Zig.callR (Zig.unwrapPayload i75)
                      pure (.br74 i78))
                    else (do
                      let _i80 ← Zig.callR (Zig.unwrapErr i75)
                      pure (.ret (4 : BitVec 32)))) : Zig.MM fba_clientLocals fba_clientExit) with
                  | .br74 v74 => (do
                    let i82 ← pure v74.len
                    let i83 ← pure (Zig.lt false (11 : BitVec 64) i82)
                    match ← ((do
                      if i83 then (do
                        pure .br84)
                      else (do
                        throw .outOfBounds)) : Zig.MM fba_clientLocals fba_clientExit) with
                    | .br84 => (do
                      let i89 ← Zig.callM (Zig.ptrProject v74.ptr (·.elem 1 (11 : BitVec 64)))
                      Zig.store (α := BitVec 8) 1 i89 p0
                      let i91 ← pure v74.len
                      let i92 ← pure (Zig.lt false (11 : BitVec 64) i91)
                      match ← ((do
                        if i92 then (do
                          pure .br93)
                        else (do
                          throw .outOfBounds)) : Zig.MM fba_clientLocals fba_clientExit) with
                      | .br93 => (do
                        let i98 ← Zig.callM (Zig.checkIndex v74 (11 : BitVec 64) >>= fun _ => Zig.load (BitVec 8) 1 (v74.ptr.elem 1 (11 : BitVec 64)))
                        Zig.store (α := BitVec 8) 1 (⟨some 0, 15⟩ : Zig.Ptr) i98
                        let _i100 ← Zig.callM (mem_Allocator_free__anon_1e60e7ef40f5 i4 v74)
                        pure (.ret i71))
                      | e => pure e)
                    | e => pure e)
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM fba_clientLocals fba_clientExit).run' { (default : fba_clientLocals) with fba := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_create__anon_8f6a81b88324Locals where
  deriving Inhabited

inductive mem_Allocator_create__anon_8f6a81b88324Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

def mem_Allocator_create__anon_8f6a81b88324 (p0 : mem_Allocator) : Zig.MemM (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    let i1 ← Zig.callM Zig.returnAddress
    let i2 ← Zig.callM (mem_Allocator_allocBytesWithAlignment__anon_4247f1fc6279 p0 (4 : BitVec 64) i1)
    match i2 with
    | .error _ => (do
      let i4 ← Zig.callR (Zig.unwrapErr i2)
      let i5 ← pure ((.error i4) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i5))
    | .ok v3 => (do
      let i7 ← pure (v3)
      let i8 ← pure ((.ok i7) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i8))) : Zig.MM mem_Allocator_create__anon_8f6a81b88324Locals mem_Allocator_create__anon_8f6a81b88324Exit).run' (default : mem_Allocator_create__anon_8f6a81b88324Locals)
  match e with
  | .ret v => pure v

structure mem_Allocator_destroy__anon_7fa4accb9a56Locals where
  deriving Inhabited

inductive mem_Allocator_destroy__anon_7fa4accb9a56Exit where
  | ret
  | br8

def mem_Allocator_destroy__anon_7fa4accb9a56 (p0 : mem_Allocator) (p1 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← pure (p1)
    let i3 ← pure i2
    let i4 ← pure (i3)
    let i5 ← pure (⟨i4, (4 : BitVec 64)⟩ : Zig.Slice)
    let i6 ← Zig.callR (mem_Alignment_fromByteUnits (4 : BitVec 64))
    let i7 ← Zig.callM Zig.returnAddress
    match ← ((do
      let i9 ← pure ((p0).vtable)
      let i10 ← Zig.callM (Zig.ptrProject i9 (·.add 24))
      let i11 ← Zig.load (Zig.Ptr) 8 i10
      let i12 ← pure ((p0).ptr)
      let _i13 ← (if i11 == (⟨some 4, 0⟩ : Zig.Ptr) then Zig.callM (heap_FixedBufferAllocator_free i12 i5 i6 i7) else throw .illegal)
      pure .br8) : Zig.MM mem_Allocator_destroy__anon_7fa4accb9a56Locals mem_Allocator_destroy__anon_7fa4accb9a56Exit) with
    | .br8 => (do
      pure .ret)
    | e => pure e) : Zig.MM mem_Allocator_destroy__anon_7fa4accb9a56Locals mem_Allocator_destroy__anon_7fa4accb9a56Exit).run' (default : mem_Allocator_destroy__anon_7fa4accb9a56Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure fba_createLocals where
  fba : Zig.Ptr
  deriving Inhabited

inductive fba_createExit where
  | ret (v : BitVec 32)
  | br5 (v : Zig.Ptr)

def fba_create (p0 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s1 ← Zig.allocStack 24 8
  let e ← ((do
    let i1 ← pure (← get).fba
    let i2 ← Zig.callM (heap_FixedBufferAllocator_init (⟨(⟨some 0, 0⟩ : Zig.Ptr), (12 : BitVec 64)⟩ : Zig.Slice))
    Zig.store (α := heap_FixedBufferAllocator) 8 i1 i2
    let i4 ← Zig.callM (heap_FixedBufferAllocator_allocator i1)
    match ← ((do
      let i6 ← Zig.callM (mem_Allocator_create__anon_8f6a81b88324 i4)
      let i7 ← pure (Zig.isNonErr i6)
      if i7 then (do
        let i9 ← Zig.callR (Zig.unwrapPayload i6)
        pure (.br5 i9))
      else (do
        let _i11 ← Zig.callR (Zig.unwrapErr i6)
        pure (.ret (0 : BitVec 32)))) : Zig.MM fba_createLocals fba_createExit) with
    | .br5 v5 => (do
      Zig.store (α := BitVec 32) 4 v5 p0
      let i14 ← Zig.load (BitVec 32) 4 v5
      let _i15 ← Zig.callM (mem_Allocator_destroy__anon_7fa4accb9a56 i4 v5)
      pure (.ret i14))
    | e => pure e) : Zig.MM fba_createLocals fba_createExit).run' { (default : fba_createLocals) with fba := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_dupe__anon_63991a21d32cLocals where
  deriving Inhabited

inductive mem_Allocator_dupe__anon_63991a21d32cExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br11
  | br23

def mem_Allocator_dupe__anon_63991a21d32c (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.MemM (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← pure p1.len
    let i3 ← Zig.callM (mem_Allocator_alloc__anon_a8254a5f2b74 p0 i2)
    match i3 with
    | .error _ => (do
      let i5 ← Zig.callR (Zig.unwrapErr i3)
      let i6 ← pure ((.error i5) : Except Zig.ErrName (Zig.Slice))
      pure (.ret i6))
    | .ok v4 => (do
      let i8 ← pure v4.len
      let i9 ← pure p1.len
      let i10 ← pure (i8 == i9)
      match ← ((do
        if i10 then (do
          pure .br11)
        else (do
          throw .panic)) : Zig.MM mem_Allocator_dupe__anon_63991a21d32cLocals mem_Allocator_dupe__anon_63991a21d32cExit) with
      | .br11 => (do
        let i16 ← pure p1.ptr
        let i17 ← pure v4.ptr
        let i18 ← Zig.callM (Zig.ptrProject i16 (·.elem 1 i8))
        let i19 ← Zig.callM (Zig.ptrProject i17 (·.elem 1 i8))
        let i20 ← Zig.callM (Zig.ptrLe i18 i17)
        let i21 ← Zig.callM (Zig.ptrLe i19 i16)
        let i22 ← pure (i20 || i21)
        match ← ((do
          if i22 then (do
            pure .br23)
          else (do
            throw .panic)) : Zig.MM mem_Allocator_dupe__anon_63991a21d32cLocals mem_Allocator_dupe__anon_63991a21d32cExit) with
        | .br23 => (do
          Zig.callM (Zig.memcpy 1 1 1 v4.ptr i16 v4.len p1.len)
          let i29 ← pure ((.ok v4) : Except Zig.ErrName (Zig.Slice))
          pure (.ret i29))
        | e => pure e)
      | e => pure e)) : Zig.MM mem_Allocator_dupe__anon_63991a21d32cLocals mem_Allocator_dupe__anon_63991a21d32cExit).run' (default : mem_Allocator_dupe__anon_63991a21d32cLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure fba_dupeLocals where
  fba : Zig.Ptr
  local8 : Zig.Ptr
  deriving Inhabited

inductive fba_dupeExit where
  | ret (v : BitVec 8)
  | br11 (v : Zig.Slice)
  | br22

def fba_dupe (p0 : BitVec 8) : Zig.MemM (BitVec 8) := do
  let s1 ← Zig.allocStack 24 8
  let s8 ← Zig.allocStack 3 1
  let e ← ((do
    let i1 ← pure (← get).fba
    let i2 ← Zig.callM (heap_FixedBufferAllocator_init (⟨(⟨some 0, 0⟩ : Zig.Ptr), (12 : BitVec 64)⟩ : Zig.Slice))
    Zig.store (α := heap_FixedBufferAllocator) 8 i1 i2
    let i4 ← Zig.callM (heap_FixedBufferAllocator_allocator i1)
    let i5 ← pure (Zig.addWrap p0 (1 : BitVec 8))
    let i6 ← pure (Zig.addWrap p0 (2 : BitVec 8))
    let i7 ← pure (#v[p0, i5, i6] : Vector (BitVec 8) 3)
    let i8 ← pure (← get).local8
    Zig.store (α := Vector (BitVec 8) 3) 1 i8 i7
    let i10 ← pure (i8)
    match ← ((do
      let i12 ← pure (⟨i10, (3 : BitVec 64)⟩ : Zig.Slice)
      let i13 ← Zig.callM (mem_Allocator_dupe__anon_63991a21d32c i4 i12)
      let i14 ← pure (Zig.isNonErr i13)
      if i14 then (do
        let i16 ← Zig.callR (Zig.unwrapPayload i13)
        pure (.br11 i16))
      else (do
        let _i18 ← Zig.callR (Zig.unwrapErr i13)
        pure (.ret (0 : BitVec 8)))) : Zig.MM fba_dupeLocals fba_dupeExit) with
    | .br11 v11 => (do
      let i20 ← pure v11.len
      let i21 ← pure (Zig.lt false (2 : BitVec 64) i20)
      match ← ((do
        if i21 then (do
          pure .br22)
        else (do
          throw .outOfBounds)) : Zig.MM fba_dupeLocals fba_dupeExit) with
      | .br22 => (do
        let i27 ← Zig.callM (Zig.checkIndex v11 (2 : BitVec 64) >>= fun _ => Zig.load (BitVec 8) 1 (v11.ptr.elem 1 (2 : BitVec 64)))
        let _i28 ← Zig.callM (mem_Allocator_free__anon_1e60e7ef40f5 i4 v11)
        pure (.ret i27))
      | e => pure e)
    | e => pure e) : Zig.MM fba_dupeLocals fba_dupeExit).run' { (default : fba_dupeLocals) with fba := s1, local8 := s8 }
  Zig.free s1
  Zig.free s8
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure fba_realloc_moveLocals where
  fba : Zig.Ptr
  deriving Inhabited

inductive fba_realloc_moveExit where
  | ret (v : BitVec 8)
  | br5 (v : Zig.Slice)
  | br15
  | br22
  | br30 (v : Zig.Slice)
  | br40

def fba_realloc_move (p0 : BitVec 8) : Zig.MemM (BitVec 8) := do
  let s1 ← Zig.allocStack 24 8
  let e ← ((do
    let i1 ← pure (← get).fba
    let i2 ← Zig.callM (heap_FixedBufferAllocator_init (⟨(⟨some 0, 0⟩ : Zig.Ptr), (12 : BitVec 64)⟩ : Zig.Slice))
    Zig.store (α := heap_FixedBufferAllocator) 8 i1 i2
    let i4 ← Zig.callM (heap_FixedBufferAllocator_allocator i1)
    match ← ((do
      let i6 ← Zig.callM (mem_Allocator_alloc__anon_a8254a5f2b74 i4 (2 : BitVec 64))
      let i7 ← pure (Zig.isNonErr i6)
      if i7 then (do
        let i9 ← Zig.callR (Zig.unwrapPayload i6)
        pure (.br5 i9))
      else (do
        let _i11 ← Zig.callR (Zig.unwrapErr i6)
        pure (.ret (0 : BitVec 8)))) : Zig.MM fba_realloc_moveLocals fba_realloc_moveExit) with
    | .br5 v5 => (do
      let i13 ← pure v5.len
      let i14 ← pure (Zig.lt false (0 : BitVec 64) i13)
      match ← ((do
        if i14 then (do
          pure .br15)
        else (do
          throw .outOfBounds)) : Zig.MM fba_realloc_moveLocals fba_realloc_moveExit) with
      | .br15 => (do
        let i20 ← pure v5.ptr
        Zig.store (α := BitVec 8) 1 i20 p0
        match ← ((do
          let i23 ← Zig.callM (mem_Allocator_alloc__anon_a8254a5f2b74 i4 (1 : BitVec 64))
          let i24 ← pure (Zig.isNonErr i23)
          if i24 then (do
            let _i26 ← Zig.callR (Zig.unwrapPayload i23)
            pure .br22)
          else (do
            let _i28 ← Zig.callR (Zig.unwrapErr i23)
            pure (.ret (1 : BitVec 8)))) : Zig.MM fba_realloc_moveLocals fba_realloc_moveExit) with
        | .br22 => (do
          match ← ((do
            let i31 ← Zig.callM (mem_Allocator_realloc__anon_af0c43114565 i4 v5 (4 : BitVec 64))
            let i32 ← pure (Zig.isNonErr i31)
            if i32 then (do
              let i34 ← Zig.callR (Zig.unwrapPayload i31)
              pure (.br30 i34))
            else (do
              let _i36 ← Zig.callR (Zig.unwrapErr i31)
              pure (.ret (2 : BitVec 8)))) : Zig.MM fba_realloc_moveLocals fba_realloc_moveExit) with
          | .br30 v30 => (do
            let i38 ← pure v30.len
            let i39 ← pure (Zig.lt false (0 : BitVec 64) i38)
            match ← ((do
              if i39 then (do
                pure .br40)
              else (do
                throw .outOfBounds)) : Zig.MM fba_realloc_moveLocals fba_realloc_moveExit) with
            | .br40 => (do
              let i45 ← Zig.callM (Zig.checkIndex v30 (0 : BitVec 64) >>= fun _ => Zig.load (BitVec 8) 1 (v30.ptr.elem 1 (0 : BitVec 64)))
              pure (.ret i45))
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM fba_realloc_moveLocals fba_realloc_moveExit).run' { (default : fba_realloc_moveLocals) with fba := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_allocWithOptionsRetAddr__anon_f1027707f9a6Locals where
  deriving Inhabited

inductive mem_Allocator_allocWithOptionsRetAddr__anon_f1027707f9a6Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br4 (v : Except Zig.ErrName (Zig.Slice))
  | br21
  | br34
  | br42

def mem_Allocator_allocWithOptionsRetAddr__anon_f1027707f9a6 (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.MemM (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.add false p1 (1 : BitVec 64)
    match ← ((do
      let i5 ← Zig.callM (mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43 p0 i3 p2)
      match i5 with
      | .error _ => (do
        let i7 ← Zig.callR (Zig.unwrapErr i5)
        let i8 ← pure ((.error i7) : Except Zig.ErrName (Zig.Slice))
        pure (.br4 i8))
      | .ok v6 => (do
        let i10 ← pure v6
        let i11 ← Zig.sub false i3 (0 : BitVec 64)
        let i12 ← pure (⟨i10, i11⟩ : Zig.Slice)
        let i13 ← pure ((.ok i12) : Except Zig.ErrName (Zig.Slice))
        pure (.br4 i13))) : Zig.MM mem_Allocator_allocWithOptionsRetAddr__anon_f1027707f9a6Locals mem_Allocator_allocWithOptionsRetAddr__anon_f1027707f9a6Exit) with
    | .br4 v4 => (do
      match v4 with
      | .error _ => (do
        let i16 ← Zig.callR (Zig.unwrapErr v4)
        let i17 ← pure ((.error i16) : Except Zig.ErrName (Zig.Slice))
        pure (.ret i17))
      | .ok v15 => (do
        let i19 ← pure v15.len
        let i20 ← pure (Zig.lt false p1 i19)
        match ← ((do
          if i20 then (do
            pure .br21)
          else (do
            throw .outOfBounds)) : Zig.MM mem_Allocator_allocWithOptionsRetAddr__anon_f1027707f9a6Locals mem_Allocator_allocWithOptionsRetAddr__anon_f1027707f9a6Exit) with
        | .br21 => (do
          let i26 ← Zig.callM (Zig.ptrProject v15.ptr (·.elem 1 p1))
          Zig.store (α := BitVec 8) 1 i26 (7 : BitVec 8)
          let i28 ← pure v15.ptr
          let i29 ← pure i28
          let i30 ← Zig.sub false p1 (0 : BitVec 64)
          let i31 ← pure v15.len
          let i32 ← Zig.add false p1 (1 : BitVec 64)
          let i33 ← pure (Zig.le false i32 i31)
          match ← ((do
            if i33 then (do
              pure .br34)
            else (do
              throw .outOfBounds)) : Zig.MM mem_Allocator_allocWithOptionsRetAddr__anon_f1027707f9a6Locals mem_Allocator_allocWithOptionsRetAddr__anon_f1027707f9a6Exit) with
          | .br34 => (do
            let i39 ← Zig.callM (Zig.checkSliceEnd v15.len (0 : BitVec 64) i30 1 >>= fun _ => pure (⟨i29, i30⟩ : Zig.Slice))
            let i40 ← Zig.callM (Zig.checkSentinelIndex i39 i30 >>= fun _ => Zig.load (BitVec 8) 1 (i39.ptr.elem 1 i30))
            let i41 ← pure ((7 : BitVec 8) == i40)
            match ← ((do
              if i41 then (do
                pure .br42)
              else (do
                throw .panic)) : Zig.MM mem_Allocator_allocWithOptionsRetAddr__anon_f1027707f9a6Locals mem_Allocator_allocWithOptionsRetAddr__anon_f1027707f9a6Exit) with
            | .br42 => (do
              let i47 ← pure ((.ok i39) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i47))
            | e => pure e)
          | e => pure e)
        | e => pure e))
    | e => pure e) : Zig.MM mem_Allocator_allocWithOptionsRetAddr__anon_f1027707f9a6Locals mem_Allocator_allocWithOptionsRetAddr__anon_f1027707f9a6Exit).run' (default : mem_Allocator_allocWithOptionsRetAddr__anon_f1027707f9a6Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_allocSentinel__anon_79cb42d26607Locals where
  deriving Inhabited

inductive mem_Allocator_allocSentinel__anon_79cb42d26607Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_allocSentinel__anon_79cb42d26607 (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.MemM (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.callM Zig.returnAddress
    let i3 ← Zig.callM (mem_Allocator_allocWithOptionsRetAddr__anon_f1027707f9a6 p0 p1 i2)
    let i4 ← pure (i3)
    pure (.ret i4)) : Zig.MM mem_Allocator_allocSentinel__anon_79cb42d26607Locals mem_Allocator_allocSentinel__anon_79cb42d26607Exit).run' (default : mem_Allocator_allocSentinel__anon_79cb42d26607Locals)
  match e with
  | .ret v => pure v

structure mem_absorbSentinel__anon_5ea1d913f4ddLocals where
  local1 : Zig.Slice
  deriving Inhabited

inductive mem_absorbSentinel__anon_5ea1d913f4ddExit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_5ea1d913f4dd (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    modify (fun s => { s with local1 := p0 })
    let i6 ← pure (((← get).local1).len)
    let i7 ← Zig.add false i6 (1 : BitVec 64)
    let i8 ← pure (((← get).local1).ptr)
    let i9 ← pure i8
    let i10 ← Zig.sub false i7 (0 : BitVec 64)
    let i11 ← pure (⟨i9, i10⟩ : Zig.Slice)
    pure (.ret i11)) : Zig.MM mem_absorbSentinel__anon_5ea1d913f4ddLocals mem_absorbSentinel__anon_5ea1d913f4ddExit).run' (default : mem_absorbSentinel__anon_5ea1d913f4ddLocals)
  match e with
  | .ret v => pure v

structure mem_Allocator_free__anon_4cd0e3a7c1bfLocals where
  deriving Inhabited

inductive mem_Allocator_free__anon_4cd0e3a7c1bfExit where
  | ret
  | br4
  | br15

def mem_Allocator_free__anon_4cd0e3a7c1bf (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← Zig.callM (mem_absorbSentinel__anon_5ea1d913f4dd p1)
    let i3 ← pure (i2)
    match ← ((do
      let i5 ← pure i3.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        pure .ret)
      else (do
        pure .br4)) : Zig.MM mem_Allocator_free__anon_4cd0e3a7c1bfLocals mem_Allocator_free__anon_4cd0e3a7c1bfExit) with
    | .br4 => (do
      let _i11 ← pure i3.len
      Zig.callM (Zig.memset (α := BitVec 8) 1 i3.ptr i3.len none)
      let i13 ← Zig.callR (mem_Alignment_fromByteUnits (1 : BitVec 64))
      let i14 ← Zig.callM Zig.returnAddress
      match ← ((do
        let i16 ← pure ((p0).vtable)
        let i17 ← Zig.callM (Zig.ptrProject i16 (·.add 24))
        let i18 ← Zig.load (Zig.Ptr) 8 i17
        let i19 ← pure ((p0).ptr)
        let _i20 ← (if i18 == (⟨some 4, 0⟩ : Zig.Ptr) then Zig.callM (heap_FixedBufferAllocator_free i19 i3 i13 i14) else throw .illegal)
        pure .br15) : Zig.MM mem_Allocator_free__anon_4cd0e3a7c1bfLocals mem_Allocator_free__anon_4cd0e3a7c1bfExit) with
      | .br15 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.MM mem_Allocator_free__anon_4cd0e3a7c1bfLocals mem_Allocator_free__anon_4cd0e3a7c1bfExit).run' (default : mem_Allocator_free__anon_4cd0e3a7c1bfLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure fba_sentinelLocals where
  fba : Zig.Ptr
  deriving Inhabited

inductive fba_sentinelExit where
  | ret (v : BitVec 8)
  | br5 (v : Zig.Slice)
  | br15

def fba_sentinel (p0 : BitVec 64) : Zig.MemM (BitVec 8) := do
  let s1 ← Zig.allocStack 24 8
  let e ← ((do
    let i1 ← pure (← get).fba
    let i2 ← Zig.callM (heap_FixedBufferAllocator_init (⟨(⟨some 0, 0⟩ : Zig.Ptr), (12 : BitVec 64)⟩ : Zig.Slice))
    Zig.store (α := heap_FixedBufferAllocator) 8 i1 i2
    let i4 ← Zig.callM (heap_FixedBufferAllocator_allocator i1)
    match ← ((do
      let i6 ← Zig.callM (mem_Allocator_allocSentinel__anon_79cb42d26607 i4 p0)
      let i7 ← pure (Zig.isNonErr i6)
      if i7 then (do
        let i9 ← Zig.callR (Zig.unwrapPayload i6)
        pure (.br5 i9))
      else (do
        let _i11 ← Zig.callR (Zig.unwrapErr i6)
        pure (.ret (0 : BitVec 8)))) : Zig.MM fba_sentinelLocals fba_sentinelExit) with
    | .br5 v5 => (do
      let i13 ← pure v5.len
      let i14 ← pure (Zig.le false p0 i13)
      match ← ((do
        if i14 then (do
          pure .br15)
        else (do
          throw .outOfBounds)) : Zig.MM fba_sentinelLocals fba_sentinelExit) with
      | .br15 => (do
        let i20 ← Zig.callM (Zig.checkSentinelIndex v5 p0 >>= fun _ => Zig.load (BitVec 8) 1 (v5.ptr.elem 1 p0))
        let _i21 ← Zig.callM (mem_Allocator_free__anon_4cd0e3a7c1bf i4 v5)
        pure (.ret i20))
      | e => pure e)
    | e => pure e) : Zig.MM fba_sentinelLocals fba_sentinelExit).run' { (default : fba_sentinelLocals) with fba := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v
  | _ => throw .panic

end AllocFba.Gen