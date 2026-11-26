-- air2lean-profile: {"allocator_model":"translated","correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.4.19...6.13.4-musl","zig_version":"0.14.1"}}
-- air2lean-interfaces: {"ext":[{"field":"call0","type":"fn (*anyopaque, usize, mem.Alignment, usize) ?[*]u8"},{"field":"call1","type":"fn (*anyopaque, []u8, mem.Alignment, usize, usize) ?[*]u8"},{"field":"call2","type":"fn (*anyopaque, []u8, mem.Alignment, usize) void"}],"interfaces":[{"contract":"Zig.Full.CAllocSpec","interface":"std.mem.Allocator","premise":"EXT-05","struct":"mem.Allocator.VTable"}]}
import ZigLean


namespace Lists.Open

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

structure Node where
  val : BitVec 32
  next : Option (Zig.Ptr)
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Node where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(8, Zig.Enc.encode v.val), (0, Zig.Enc.encode v.next)]
  decode bs := do pure { val := ← Zig.Enc.decodeAt bs 8, next := ← Zig.Enc.decodeAt bs 0 }

structure array_list_ArrayListAlignedUnmanaged_u32_null where
  items : Zig.Slice
  capacity : BitVec 64
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc array_list_ArrayListAlignedUnmanaged_u32_null where
  size := 24
  align := 8
  encode v := Zig.Enc.fields 24 [(0, Zig.Enc.encode v.items), (16, Zig.Enc.encode v.capacity)]
  decode bs := do pure { items := ← Zig.Enc.decodeAt bs 0, capacity := ← Zig.Enc.decodeAt bs 16 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. The words of `@returnAddress()` and of `undefined` pointers are `arbitrary` (`Mem.arbitrary`). -/
def mem0 (σ : Zig.Placement) (arbitrary : Array (BitVec 64) := #[]) : Zig.Mem := { Zig.Mem.ofGlobals σ [
  -- 0: a constant
  (Zig.Enc.encode ((#v[] : Vector (BitVec 32) 0) : Vector (BitVec 32) 0), 4, .constGlobal),
  -- 1: a constant
  (Zig.Enc.encode ((#v[] : Vector (BitVec 8) 0) : Vector (BitVec 8) 0), 1, .constGlobal)] with arbitrary }

/-- The spawn targets of the program. -/
inductive Tgt where

/-- The environment's implementations of the open interfaces (`docs/interfaces.md`,
premise EXT-05): `call<i> f args` runs the environment's function at `f`, a pointer that is no
function of the program. -/
class Ext where
  /-- `fn (*anyopaque, usize, mem.Alignment, usize) ?[*]u8` -/
  call0 : Zig.Ptr → (Zig.Ptr) → (BitVec 64) → (mem_Alignment) → (BitVec 64) → Zig.ConcM Tgt (Option (Zig.Ptr))
  /-- `fn (*anyopaque, []u8, mem.Alignment, usize, usize) ?[*]u8` -/
  call1 : Zig.Ptr → (Zig.Ptr) → (Zig.Slice) → (mem_Alignment) → (BitVec 64) → (BitVec 64) → Zig.ConcM Tgt (Option (Zig.Ptr))
  /-- `fn (*anyopaque, []u8, mem.Alignment, usize) void` -/
  call2 : Zig.Ptr → (Zig.Ptr) → (Zig.Slice) → (mem_Alignment) → (BitVec 64) → Zig.ConcM Tgt (Unit)

/-- The closed program's environment: no function besides the program's. -/
@[reducible] def Ext.closed : Ext where
  call0 _ _ _ _ _ := throw .illegal
  call1 _ _ _ _ _ _ := throw .illegal
  call2 _ _ _ _ _ := throw .illegal

structure array_list_ArrayListAlignedUnmanaged_u32_null_growCapacityLocals where
  new : BitVec 64
  deriving Inhabited

inductive array_list_ArrayListAlignedUnmanaged_u32_null_growCapacityExit where
  | ret (v : BitVec 64)
  | br11
  | rep4

def array_list_ArrayListAlignedUnmanaged_u32_null_growCapacity.again4 : array_list_ArrayListAlignedUnmanaged_u32_null_growCapacityExit → Bool
  | .rep4 => true
  | _ => false

def array_list_ArrayListAlignedUnmanaged_u32_null_growCapacity.loop4 (p1 : BitVec 64) : Zig.M array_list_ArrayListAlignedUnmanaged_u32_null_growCapacityLocals array_list_ArrayListAlignedUnmanaged_u32_null_growCapacityExit := do
  let i5 ← pure ((← get).new)
  let i6 ← pure ((← get).new)
  let i7 ← Zig.divTrunc false i6 (2 : BitVec 64)
  let i8 ← Zig.add false i7 (32 : BitVec 64)
  let i9 ← pure (Zig.addSat false i5 i8)
  modify (fun s => { s with new := i9 })
  match ← ((do
    let i12 ← pure ((← get).new)
    let i13 ← pure (i12)
    let i14 ← pure (p1)
    let i15 ← pure (Zig.ge false i13 i14)
    if i15 then (do
      let i17 ← pure ((← get).new)
      pure (.ret i17))
    else (do
      pure .br11)) : Zig.M array_list_ArrayListAlignedUnmanaged_u32_null_growCapacityLocals array_list_ArrayListAlignedUnmanaged_u32_null_growCapacityExit) with
  | .br11 => (do
    pure .rep4)
  | e => pure e

def array_list_ArrayListAlignedUnmanaged_u32_null_growCapacity (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with new := p0 })
    Zig.loop (array_list_ArrayListAlignedUnmanaged_u32_null_growCapacity.loop4 p1) array_list_ArrayListAlignedUnmanaged_u32_null_growCapacity.again4) : Zig.M array_list_ArrayListAlignedUnmanaged_u32_null_growCapacityLocals array_list_ArrayListAlignedUnmanaged_u32_null_growCapacityExit).run' (default : array_list_ArrayListAlignedUnmanaged_u32_null_growCapacityLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] array_list_ArrayListAlignedUnmanaged_u32_null_growCapacity.loop4 array_list_ArrayListAlignedUnmanaged_u32_null_growCapacity

structure array_list_ArrayListAlignedUnmanaged_u32_null_allocatedSliceLocals where
  local1 : array_list_ArrayListAlignedUnmanaged_u32_null
  deriving Inhabited

inductive array_list_ArrayListAlignedUnmanaged_u32_null_allocatedSliceExit where
  | ret (v : Zig.Slice)

def array_list_ArrayListAlignedUnmanaged_u32_null_allocatedSlice (p0 : array_list_ArrayListAlignedUnmanaged_u32_null) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    modify (fun s => { s with local1 := p0 })
    let i6 ← pure ((p0).capacity)
    let i7 ← pure ((((← get).local1).items).ptr)
    let i8 ← pure i7
    let i9 ← pure (⟨i8, i6⟩ : Zig.Slice)
    pure (.ret i9)) : Zig.MM array_list_ArrayListAlignedUnmanaged_u32_null_allocatedSliceLocals array_list_ArrayListAlignedUnmanaged_u32_null_allocatedSliceExit).run' (default : array_list_ArrayListAlignedUnmanaged_u32_null_allocatedSliceLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] array_list_ArrayListAlignedUnmanaged_u32_null_allocatedSlice

structure mem_sliceAsBytes__anon_aaa6efc5c520Locals where
  deriving Inhabited

inductive mem_sliceAsBytes__anon_aaa6efc5c520Exit where
  | ret (v : Zig.Slice)
  | br8
  | br7
  | br5 (v : Bool)
  | br1

def mem_sliceAsBytes__anon_aaa6efc5c520 (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure p0.len
      let i3 ← pure (i2)
      let i4 ← pure (i3 == (0 : BitVec 64))
      match ← ((do
        if i4 then (do
          match ← ((do
            match ← ((do
              pure .br8) : Zig.MM mem_sliceAsBytes__anon_aaa6efc5c520Locals mem_sliceAsBytes__anon_aaa6efc5c520Exit) with
            | .br8 => (do
              pure .br7)
            | e => pure e) : Zig.MM mem_sliceAsBytes__anon_aaa6efc5c520Locals mem_sliceAsBytes__anon_aaa6efc5c520Exit) with
          | .br7 => (do
            pure (.br5 true))
          | e => pure e)
        else (do
          pure (.br5 false))) : Zig.MM mem_sliceAsBytes__anon_aaa6efc5c520Locals mem_sliceAsBytes__anon_aaa6efc5c520Exit) with
      | .br5 v5 => (do
        if v5 then (do
          pure (.ret (⟨(⟨some 1, 0⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice)))
        else (do
          pure .br1))
      | e => pure e) : Zig.MM mem_sliceAsBytes__anon_aaa6efc5c520Locals mem_sliceAsBytes__anon_aaa6efc5c520Exit) with
    | .br1 => (do
      let i16 ← pure p0.ptr
      let i17 ← pure (i16)
      let i18 ← pure p0.len
      let i19 ← Zig.mul false i18 (4 : BitVec 64)
      let i20 ← pure i17
      let i21 ← pure (⟨i20, i19⟩ : Zig.Slice)
      pure (.ret i21))
    | e => pure e) : Zig.MM mem_sliceAsBytes__anon_aaa6efc5c520Locals mem_sliceAsBytes__anon_aaa6efc5c520Exit).run' (default : mem_sliceAsBytes__anon_aaa6efc5c520Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_sliceAsBytes__anon_aaa6efc5c520

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

attribute [zig_run] math_isPowerOfTwo__anon_38853e1fe316

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

attribute [zig_run] mem_Alignment_fromByteUnits

structure mem_Allocator_free__anon_10fd68fdc68dLocals where
  deriving Inhabited

inductive mem_Allocator_free__anon_10fd68fdc68dExit where
  | ret
  | br4
  | br6
  | br22

def mem_Allocator_free__anon_10fd68fdc68d [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_sliceAsBytes__anon_aaa6efc5c520 p1)
    let i3 ← pure i2.len
    match ← ((do
      pure .br4) : Zig.CM Tgt mem_Allocator_free__anon_10fd68fdc68dLocals mem_Allocator_free__anon_10fd68fdc68dExit) with
    | .br4 => (do
      match ← ((do
        let i7 ← pure (i3)
        let i8 ← pure (i7 == (0 : BitVec 64))
        if i8 then (do
          pure .ret)
        else (do
          pure .br6)) : Zig.CM Tgt mem_Allocator_free__anon_10fd68fdc68dLocals mem_Allocator_free__anon_10fd68fdc68dExit) with
      | .br6 => (do
        let i12 ← pure i2.ptr
        let i13 ← pure (i12)
        let i14 ← pure i13
        let i15 ← pure (⟨i14, i3⟩ : Zig.Slice)
        Zig.callMC (Zig.memset (α := BitVec 8) 4 i15.ptr i15.len none)
        let i17 ← pure i13
        let i18 ← pure (⟨i17, i3⟩ : Zig.Slice)
        let i19 ← pure (i18)
        let i20 ← Zig.callRC (mem_Alignment_fromByteUnits (4 : BitVec 64))
        let i21 ← Zig.callMC Zig.returnAddress
        match ← ((do
          let i23 ← pure ((p0).vtable)
          let i24 ← Zig.callMC (Zig.ptrProject i23 (·.add 24))
          let i25 ← Zig.load (Zig.Ptr) 8 i24
          let i26 ← pure ((p0).ptr)
          let _i27 ← (Zig.callC (Zig.extCall (Ext.call2 i25 i26 i19 i20 i21)))
          pure .br22) : Zig.CM Tgt mem_Allocator_free__anon_10fd68fdc68dLocals mem_Allocator_free__anon_10fd68fdc68dExit) with
        | .br22 => (do
          pure .ret)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_10fd68fdc68dLocals mem_Allocator_free__anon_10fd68fdc68dExit).run' (default : mem_Allocator_free__anon_10fd68fdc68dLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_10fd68fdc68d

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

attribute [zig_run] math_mul__anon_44faaf286c79

structure mem_bytesAsSlice__anon_15c06f9c2e5fLocals where
  deriving Inhabited

inductive mem_bytesAsSlice__anon_15c06f9c2e5fExit where
  | ret (v : Zig.Slice)
  | br5 (v : Bool)
  | br1
  | br18

def mem_bytesAsSlice__anon_15c06f9c2e5f (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure p0.len
      let i3 ← pure (i2)
      let i4 ← pure (i3 == (0 : BitVec 64))
      match ← ((do
        if i4 then (do
          pure (.br5 true))
        else (do
          pure (.br5 false))) : Zig.MM mem_bytesAsSlice__anon_15c06f9c2e5fLocals mem_bytesAsSlice__anon_15c06f9c2e5fExit) with
      | .br5 v5 => (do
        if v5 then (do
          pure (.ret (⟨(⟨some 0, 0⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice)))
        else (do
          pure .br1))
      | e => pure e) : Zig.MM mem_bytesAsSlice__anon_15c06f9c2e5fLocals mem_bytesAsSlice__anon_15c06f9c2e5fExit) with
    | .br1 => (do
      let i12 ← pure p0.ptr
      let i13 ← pure (i12)
      let i14 ← pure p0.len
      let i15 ← Zig.divTrunc false i14 (4 : BitVec 64)
      let i16 ← Zig.rem false i14 (4 : BitVec 64)
      let i17 ← pure (i16 == (0 : BitVec 64))
      match ← ((do
        if i17 then (do
          pure .br18)
        else (do
          throw .panic)) : Zig.MM mem_bytesAsSlice__anon_15c06f9c2e5fLocals mem_bytesAsSlice__anon_15c06f9c2e5fExit) with
      | .br18 => (do
        let i23 ← pure i13
        let i24 ← pure (⟨i23, i15⟩ : Zig.Slice)
        pure (.ret i24))
      | e => pure e)
    | e => pure e) : Zig.MM mem_bytesAsSlice__anon_15c06f9c2e5fLocals mem_bytesAsSlice__anon_15c06f9c2e5fExit).run' (default : mem_bytesAsSlice__anon_15c06f9c2e5fLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_bytesAsSlice__anon_15c06f9c2e5f

structure mem_Allocator_remap__anon_fdce5ddbfdcfLocals where
  deriving Inhabited

inductive mem_Allocator_remap__anon_fdce5ddbfdcfExit where
  | ret (v : Option (Zig.Slice))
  | br3
  | br16
  | br24 (v : BitVec 64)
  | br36 (v : Option (Zig.Ptr))
  | br32 (v : Zig.Ptr)
  | br57

def mem_Allocator_remap__anon_fdce5ddbfdcf [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Option (Zig.Slice)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p2)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        let _i7 ← Zig.callC (mem_Allocator_free__anon_10fd68fdc68d p0 p1)
        let i8 ← pure p1.ptr
        let i9 ← pure i8
        let i10 ← pure (i9)
        let _i11 ← pure p1.len
        let i12 ← pure (⟨i10, (0 : BitVec 64)⟩ : Zig.Slice)
        let i13 ← pure (some i12)
        pure (.ret i13))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_remap__anon_fdce5ddbfdcfLocals mem_Allocator_remap__anon_fdce5ddbfdcfExit) with
    | .br3 => (do
      match ← ((do
        let i17 ← pure p1.len
        let i18 ← pure (i17)
        let i19 ← pure (i18 == (0 : BitVec 64))
        if i19 then (do
          pure (.ret none))
        else (do
          pure .br16)) : Zig.CM Tgt mem_Allocator_remap__anon_fdce5ddbfdcfLocals mem_Allocator_remap__anon_fdce5ddbfdcfExit) with
      | .br16 => (do
        let i23 ← Zig.callMC (mem_sliceAsBytes__anon_aaa6efc5c520 p1)
        match ← ((do
          let i25 ← Zig.callRC (math_mul__anon_44faaf286c79 (4 : BitVec 64) p2)
          let i26 ← pure (Zig.isNonErr i25)
          if i26 then (do
            let i28 ← Zig.callRC (Zig.unwrapPayload i25)
            pure (.br24 i28))
          else (do
            let _i30 ← Zig.callRC (Zig.unwrapErr i25)
            pure (.ret none))) : Zig.CM Tgt mem_Allocator_remap__anon_fdce5ddbfdcfLocals mem_Allocator_remap__anon_fdce5ddbfdcfExit) with
        | .br24 v24 => (do
          match ← ((do
            let i33 ← pure (i23)
            let i34 ← Zig.callRC (mem_Alignment_fromByteUnits (4 : BitVec 64))
            let i35 ← Zig.callMC Zig.returnAddress
            match ← ((do
              let i37 ← pure ((p0).vtable)
              let i38 ← Zig.callMC (Zig.ptrProject i37 (·.add 16))
              let i39 ← Zig.load (Zig.Ptr) 8 i38
              let i40 ← pure ((p0).ptr)
              let i41 ← (Zig.callC (Zig.extCall (Ext.call1 i39 i40 i33 i34 v24 i35)))
              pure (.br36 i41)) : Zig.CM Tgt mem_Allocator_remap__anon_fdce5ddbfdcfLocals mem_Allocator_remap__anon_fdce5ddbfdcfExit) with
            | .br36 v36 => (do
              let i43 ← pure ((v36).isSome)
              if i43 then (do
                let i45 ← Zig.optPayload v36
                pure (.br32 i45))
              else (do
                pure (.ret none)))
            | e => pure e) : Zig.CM Tgt mem_Allocator_remap__anon_fdce5ddbfdcfLocals mem_Allocator_remap__anon_fdce5ddbfdcfExit) with
          | .br32 v32 => (do
            let i48 ← pure v32
            let i49 ← pure (⟨i48, v24⟩ : Zig.Slice)
            let i50 ← pure i49.ptr
            let i51 ← pure i49.len
            let i52 ← pure (i51 == (0 : BitVec 64))
            let i53 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i50)))
            let i54 ← pure (i53 &&& (3 : BitVec 64))
            let i55 ← pure (i54 == (0 : BitVec 64))
            let i56 ← pure (i52 || i55)
            match ← ((do
              if i56 then (do
                pure .br57)
              else (do
                throw .panic)) : Zig.CM Tgt mem_Allocator_remap__anon_fdce5ddbfdcfLocals mem_Allocator_remap__anon_fdce5ddbfdcfExit) with
            | .br57 => (do
              let i62 ← Zig.callMC (Zig.checkAlign 4 i49.ptr >>= fun _ => pure i49)
              let i63 ← Zig.callMC (mem_bytesAsSlice__anon_15c06f9c2e5f i62)
              let i64 ← pure (some i63)
              pure (.ret i64))
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_remap__anon_fdce5ddbfdcfLocals mem_Allocator_remap__anon_fdce5ddbfdcfExit).run' (default : mem_Allocator_remap__anon_fdce5ddbfdcfLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_remap__anon_fdce5ddbfdcf

structure mem_Allocator_allocBytesWithAlignment__anon_2887ccb70571Locals where
  deriving Inhabited

inductive mem_Allocator_allocBytesWithAlignment__anon_2887ccb70571Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3
  | br11 (v : Option (Zig.Ptr))
  | br9 (v : Zig.Ptr)
  | br29

def mem_Allocator_allocBytesWithAlignment__anon_2887ccb70571 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (⟨none, 18446744073709551612⟩ : Zig.Ptr) : Except Zig.ErrName (Zig.Ptr))))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_2887ccb70571Locals mem_Allocator_allocBytesWithAlignment__anon_2887ccb70571Exit) with
    | .br3 => (do
      match ← ((do
        let i10 ← Zig.callRC (mem_Alignment_fromByteUnits (4 : BitVec 64))
        match ← ((do
          let i12 ← pure ((p0).vtable)
          let i13 ← pure i12
          let i14 ← Zig.load (Zig.Ptr) 8 i13
          let i15 ← pure ((p0).ptr)
          let i16 ← (Zig.callC (Zig.extCall (Ext.call0 i14 i15 p1 i10 p2)))
          pure (.br11 i16)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_2887ccb70571Locals mem_Allocator_allocBytesWithAlignment__anon_2887ccb70571Exit) with
        | .br11 v11 => (do
          let i18 ← pure ((v11).isSome)
          if i18 then (do
            let i20 ← Zig.optPayload v11
            pure (.br9 i20))
          else (do
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr)))))
        | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_2887ccb70571Locals mem_Allocator_allocBytesWithAlignment__anon_2887ccb70571Exit) with
      | .br9 v9 => (do
        let i23 ← pure v9
        let i24 ← pure (⟨i23, p1⟩ : Zig.Slice)
        Zig.callMC (Zig.memset (α := BitVec 8) 1 i24.ptr i24.len none)
        let i26 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr v9)))
        let i27 ← pure (i26 &&& (3 : BitVec 64))
        let i28 ← pure (i27 == (0 : BitVec 64))
        match ← ((do
          if i28 then (do
            pure .br29)
          else (do
            throw .panic)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_2887ccb70571Locals mem_Allocator_allocBytesWithAlignment__anon_2887ccb70571Exit) with
        | .br29 => (do
          let i34 ← Zig.callMC (Zig.checkAlign 4 v9 >>= fun _ => pure v9)
          let i35 ← pure ((.ok i34) : Except Zig.ErrName (Zig.Ptr))
          pure (.ret i35))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_2887ccb70571Locals mem_Allocator_allocBytesWithAlignment__anon_2887ccb70571Exit).run' (default : mem_Allocator_allocBytesWithAlignment__anon_2887ccb70571Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocBytesWithAlignment__anon_2887ccb70571

structure mem_Allocator_allocWithSizeAndAlignment__anon_b94e527e9fd8Locals where
  deriving Inhabited

inductive mem_Allocator_allocWithSizeAndAlignment__anon_b94e527e9fd8Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3 (v : BitVec 64)

def mem_Allocator_allocWithSizeAndAlignment__anon_b94e527e9fd8 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.callRC (math_mul__anon_44faaf286c79 (4 : BitVec 64) p1)
      let i5 ← pure (Zig.isNonErr i4)
      if i5 then (do
        let i7 ← Zig.callRC (Zig.unwrapPayload i4)
        pure (.br3 i7))
      else (do
        let _i9 ← Zig.callRC (Zig.unwrapErr i4)
        pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr))))) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_b94e527e9fd8Locals mem_Allocator_allocWithSizeAndAlignment__anon_b94e527e9fd8Exit) with
    | .br3 v3 => (do
      let i11 ← Zig.callC (mem_Allocator_allocBytesWithAlignment__anon_2887ccb70571 p0 v3 p2)
      pure (.ret i11))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_b94e527e9fd8Locals mem_Allocator_allocWithSizeAndAlignment__anon_b94e527e9fd8Exit).run' (default : mem_Allocator_allocWithSizeAndAlignment__anon_b94e527e9fd8Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocWithSizeAndAlignment__anon_b94e527e9fd8

structure mem_Allocator_alignedAlloc__anon_867b1b77a8edLocals where
  deriving Inhabited

inductive mem_Allocator_alignedAlloc__anon_867b1b77a8edExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br3 (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_alignedAlloc__anon_867b1b77a8ed [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.callMC Zig.returnAddress
    match ← ((do
      let i4 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_b94e527e9fd8 p0 p1 i2)
      match i4 with
      | .error _ => (do
        let i6 ← Zig.callRC (Zig.unwrapErr i4)
        let i7 ← pure ((.error i6) : Except Zig.ErrName (Zig.Slice))
        pure (.br3 i7))
      | .ok v5 => (do
        let i9 ← pure (v5)
        let i10 ← pure i9
        let i11 ← pure (⟨i10, p1⟩ : Zig.Slice)
        let i12 ← pure ((.ok i11) : Except Zig.ErrName (Zig.Slice))
        pure (.br3 i12))) : Zig.CM Tgt mem_Allocator_alignedAlloc__anon_867b1b77a8edLocals mem_Allocator_alignedAlloc__anon_867b1b77a8edExit) with
    | .br3 v3 => (do
      pure (.ret v3))
    | e => pure e) : Zig.CM Tgt mem_Allocator_alignedAlloc__anon_867b1b77a8edLocals mem_Allocator_alignedAlloc__anon_867b1b77a8edExit).run' (default : mem_Allocator_alignedAlloc__anon_867b1b77a8edLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_alignedAlloc__anon_867b1b77a8ed

structure array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPreciseLocals where
  deriving Inhabited

inductive array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPreciseExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br3
  | br14
  | br39
  | br50
  | br62

def array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPrecise [Ext] (p0 : Zig.Ptr) (p1 : mem_Allocator) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
      let i5 ← Zig.load (BitVec 64) 8 i4
      let i6 ← pure (i5)
      let i7 ← pure (p2)
      let i8 ← pure (Zig.ge false i6 i7)
      if i8 then (do
        pure (.ret (.ok () : Except Zig.ErrName (Unit))))
      else (do
        pure .br3)) : Zig.CM Tgt array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPreciseLocals array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPreciseExit) with
    | .br3 => (do
      let i12 ← Zig.load (array_list_ArrayListAlignedUnmanaged_u32_null) 8 p0
      let i13 ← Zig.callMC (array_list_ArrayListAlignedUnmanaged_u32_null_allocatedSlice i12)
      match ← ((do
        let i15 ← Zig.callC (mem_Allocator_remap__anon_fdce5ddbfdcf p1 i13 p2)
        let i16 ← pure ((i15).isSome)
        if i16 then (do
          let i18 ← Zig.optPayload i15
          let i19 ← pure p0
          let i20 ← pure i19
          let i21 ← pure i18.ptr
          Zig.store (α := Zig.Ptr) 8 i20 i21
          let i23 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
          let i24 ← pure i18.len
          Zig.store (α := BitVec 64) 8 i23 i24
          pure .br14)
        else (do
          let i27 ← Zig.callC (mem_Allocator_alignedAlloc__anon_867b1b77a8ed p1 p2)
          match i27 with
          | .error _ => (do
            let i29 ← Zig.callRC (Zig.unwrapErr i27)
            let i30 ← pure ((.error i29) : Except Zig.ErrName (Unit))
            pure (.ret i30))
          | .ok v28 => (do
            let i32 ← pure p0
            let i33 ← Zig.load (Zig.Slice) 8 i32
            let i34 ← pure i33.len
            let i35 ← pure v28.ptr
            let i36 ← pure i35
            let i37 ← pure v28.len
            let i38 ← pure (Zig.le false i34 i37)
            match ← ((do
              if i38 then (do
                pure .br39)
              else (do
                throw .outOfBounds)) : Zig.CM Tgt array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPreciseLocals array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPreciseExit) with
            | .br39 => (do
              let i44 ← Zig.callMC (Zig.checkSliceEnd v28.len (0 : BitVec 64) i34 0 >>= fun _ => pure (⟨i36, i34⟩ : Zig.Slice))
              let i45 ← pure p0
              let i46 ← Zig.load (Zig.Slice) 8 i45
              let i47 ← pure i44.len
              let i48 ← pure i46.len
              let i49 ← pure (i47 == i48)
              match ← ((do
                if i49 then (do
                  pure .br50)
                else (do
                  throw .panic)) : Zig.CM Tgt array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPreciseLocals array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPreciseExit) with
              | .br50 => (do
                let i55 ← pure i46.ptr
                let i56 ← pure i44.ptr
                let i57 ← Zig.callMC (Zig.ptrProject i55 (·.elem 4 i47))
                let i58 ← Zig.callMC (Zig.ptrProject i56 (·.elem 4 i47))
                let i59 ← Zig.callMC (Zig.ptrLe i57 i56)
                let i60 ← Zig.callMC (Zig.ptrLe i58 i55)
                let i61 ← pure (i59 || i60)
                match ← ((do
                  if i61 then (do
                    pure .br62)
                  else (do
                    throw .panic)) : Zig.CM Tgt array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPreciseLocals array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPreciseExit) with
                | .br62 => (do
                  Zig.callMC (Zig.memcpy 4 4 4 i44.ptr i55 i44.len i46.len)
                  let _i68 ← Zig.callC (mem_Allocator_free__anon_10fd68fdc68d p1 i13)
                  let i69 ← pure p0
                  let i70 ← pure i69
                  let i71 ← pure v28.ptr
                  Zig.store (α := Zig.Ptr) 8 i70 i71
                  let i73 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
                  let i74 ← pure v28.len
                  Zig.store (α := BitVec 64) 8 i73 i74
                  pure .br14)
                | e => pure e)
              | e => pure e)
            | e => pure e))) : Zig.CM Tgt array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPreciseLocals array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPreciseExit) with
      | .br14 => (do
        pure (.ret (.ok () : Except Zig.ErrName (Unit))))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPreciseLocals array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPreciseExit).run' (default : array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPreciseLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPrecise

structure array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityLocals where
  deriving Inhabited

inductive array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br3

def array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacity [Ext] (p0 : Zig.Ptr) (p1 : mem_Allocator) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
      let i5 ← Zig.load (BitVec 64) 8 i4
      let i6 ← pure (i5)
      let i7 ← pure (p2)
      let i8 ← pure (Zig.ge false i6 i7)
      if i8 then (do
        pure (.ret (.ok () : Except Zig.ErrName (Unit))))
      else (do
        pure .br3)) : Zig.CM Tgt array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityLocals array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityExit) with
    | .br3 => (do
      let i12 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
      let i13 ← Zig.load (BitVec 64) 8 i12
      let i14 ← Zig.callRC (array_list_ArrayListAlignedUnmanaged_u32_null_growCapacity i13 p2)
      let i15 ← Zig.callC (array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityPrecise p0 p1 i14)
      pure (.ret i15))
    | e => pure e) : Zig.CM Tgt array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityLocals array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityExit).run' (default : array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacityLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacity

structure array_list_ArrayListAlignedUnmanaged_u32_null_addOneAssumeCapacityLocals where
  deriving Inhabited

inductive array_list_ArrayListAlignedUnmanaged_u32_null_addOneAssumeCapacityExit where
  | ret (v : Zig.Ptr)
  | br23

def array_list_ArrayListAlignedUnmanaged_u32_null_addOneAssumeCapacity (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← pure p0
    let i2 ← Zig.load (Zig.Slice) 8 i1
    let i3 ← pure i2.len
    let i4 ← Zig.callM (Zig.ptrProject p0 (·.add 16))
    let i5 ← Zig.load (BitVec 64) 8 i4
    let i6 ← pure (i3)
    let i7 ← pure (i5)
    let i8 ← pure (Zig.lt false i6 i7)
    let _i9 ← Zig.callR (debug_assert i8)
    let i10 ← pure p0
    let i11 ← Zig.callM (Zig.ptrProject i10 (·.add 8))
    let i12 ← Zig.load (BitVec 64) 8 i11
    let i13 ← Zig.add false i12 (1 : BitVec 64)
    Zig.store (α := BitVec 64) 8 i11 i13
    let i15 ← pure p0
    let i16 ← pure p0
    let i17 ← Zig.load (Zig.Slice) 8 i16
    let i18 ← pure i17.len
    let i19 ← Zig.sub false i18 (1 : BitVec 64)
    let i20 ← Zig.load (Zig.Slice) 8 i15
    let i21 ← pure i20.len
    let i22 ← pure (Zig.lt false i19 i21)
    match ← ((do
      if i22 then (do
        pure .br23)
      else (do
        throw .outOfBounds)) : Zig.MM array_list_ArrayListAlignedUnmanaged_u32_null_addOneAssumeCapacityLocals array_list_ArrayListAlignedUnmanaged_u32_null_addOneAssumeCapacityExit) with
    | .br23 => (do
      let i28 ← Zig.callM (Zig.checkIndex i20.len i19) >>= fun _ => Zig.callM (Zig.ptrProject i20.ptr (·.elem 4 i19))
      pure (.ret i28))
    | e => pure e) : Zig.MM array_list_ArrayListAlignedUnmanaged_u32_null_addOneAssumeCapacityLocals array_list_ArrayListAlignedUnmanaged_u32_null_addOneAssumeCapacityExit).run' (default : array_list_ArrayListAlignedUnmanaged_u32_null_addOneAssumeCapacityLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] array_list_ArrayListAlignedUnmanaged_u32_null_addOneAssumeCapacity

structure array_list_ArrayListAlignedUnmanaged_u32_null_addOneLocals where
  deriving Inhabited

inductive array_list_ArrayListAlignedUnmanaged_u32_null_addOneExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

def array_list_ArrayListAlignedUnmanaged_u32_null_addOne [Ext] (p0 : Zig.Ptr) (p1 : mem_Allocator) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.load (Zig.Slice) 8 i2
    let i4 ← pure i3.len
    let i5 ← Zig.add false i4 (1 : BitVec 64)
    let i6 ← Zig.callC (array_list_ArrayListAlignedUnmanaged_u32_null_ensureTotalCapacity p0 p1 i5)
    match i6 with
    | .error _ => (do
      let i8 ← Zig.callRC (Zig.unwrapErr i6)
      let i9 ← pure ((.error i8) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i9))
    | .ok _v7 => (do
      let i11 ← Zig.callMC (array_list_ArrayListAlignedUnmanaged_u32_null_addOneAssumeCapacity p0)
      let i12 ← pure ((.ok i11) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i12))) : Zig.CM Tgt array_list_ArrayListAlignedUnmanaged_u32_null_addOneLocals array_list_ArrayListAlignedUnmanaged_u32_null_addOneExit).run' (default : array_list_ArrayListAlignedUnmanaged_u32_null_addOneLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] array_list_ArrayListAlignedUnmanaged_u32_null_addOne

structure array_list_ArrayListAlignedUnmanaged_u32_null_appendLocals where
  deriving Inhabited

inductive array_list_ArrayListAlignedUnmanaged_u32_null_appendExit where
  | ret (v : Except Zig.ErrName (Unit))

def array_list_ArrayListAlignedUnmanaged_u32_null_append [Ext] (p0 : Zig.Ptr) (p1 : mem_Allocator) (p2 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    let i3 ← Zig.callC (array_list_ArrayListAlignedUnmanaged_u32_null_addOne p0 p1)
    match i3 with
    | .error _ => (do
      let i5 ← Zig.callRC (Zig.unwrapErr i3)
      let i6 ← pure ((.error i5) : Except Zig.ErrName (Unit))
      pure (.ret i6))
    | .ok v4 => (do
      Zig.store (α := BitVec 32) 4 v4 p2
      pure (.ret (.ok () : Except Zig.ErrName (Unit))))) : Zig.CM Tgt array_list_ArrayListAlignedUnmanaged_u32_null_appendLocals array_list_ArrayListAlignedUnmanaged_u32_null_appendExit).run' (default : array_list_ArrayListAlignedUnmanaged_u32_null_appendLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] array_list_ArrayListAlignedUnmanaged_u32_null_append

structure array_list_ArrayListAlignedUnmanaged_u32_null_clearAndFreeLocals where
  deriving Inhabited

inductive array_list_ArrayListAlignedUnmanaged_u32_null_clearAndFreeExit where
  | ret

def array_list_ArrayListAlignedUnmanaged_u32_null_clearAndFree [Ext] (p0 : Zig.Ptr) (p1 : mem_Allocator) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.load (array_list_ArrayListAlignedUnmanaged_u32_null) 8 p0
    let i3 ← Zig.callMC (array_list_ArrayListAlignedUnmanaged_u32_null_allocatedSlice i2)
    let _i4 ← Zig.callC (mem_Allocator_free__anon_10fd68fdc68d p1 i3)
    let i5 ← pure p0
    let i6 ← Zig.callMC (Zig.ptrProject i5 (·.add 8))
    Zig.store (α := BitVec 64) 8 i6 (0 : BitVec 64)
    let i8 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
    Zig.store (α := BitVec 64) 8 i8 (0 : BitVec 64)
    pure .ret) : Zig.CM Tgt array_list_ArrayListAlignedUnmanaged_u32_null_clearAndFreeLocals array_list_ArrayListAlignedUnmanaged_u32_null_clearAndFreeExit).run' (default : array_list_ArrayListAlignedUnmanaged_u32_null_clearAndFreeLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] array_list_ArrayListAlignedUnmanaged_u32_null_clearAndFree

structure array_list_ArrayListAlignedUnmanaged_u32_null_deinitLocals where
  deriving Inhabited

inductive array_list_ArrayListAlignedUnmanaged_u32_null_deinitExit where
  | ret

def array_list_ArrayListAlignedUnmanaged_u32_null_deinit [Ext] (p0 : Zig.Ptr) (p1 : mem_Allocator) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.load (array_list_ArrayListAlignedUnmanaged_u32_null) 8 p0
    let i3 ← Zig.callMC (array_list_ArrayListAlignedUnmanaged_u32_null_allocatedSlice i2)
    let _i4 ← Zig.callC (mem_Allocator_free__anon_10fd68fdc68d p1 i3)
    Zig.storeUndef (array_list_ArrayListAlignedUnmanaged_u32_null) 8 p0
    pure .ret) : Zig.CM Tgt array_list_ArrayListAlignedUnmanaged_u32_null_deinitLocals array_list_ArrayListAlignedUnmanaged_u32_null_deinitExit).run' (default : array_list_ArrayListAlignedUnmanaged_u32_null_deinitLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] array_list_ArrayListAlignedUnmanaged_u32_null_deinit

structure array_list_ArrayListAlignedUnmanaged_u32_null_toOwnedSliceLocals where
  deriving Inhabited

inductive array_list_ArrayListAlignedUnmanaged_u32_null_toOwnedSliceExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br4
  | br29
  | br41

def array_list_ArrayListAlignedUnmanaged_u32_null_toOwnedSlice [Ext] (p0 : Zig.Ptr) (p1 : mem_Allocator) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.load (array_list_ArrayListAlignedUnmanaged_u32_null) 8 p0
    let i3 ← Zig.callMC (array_list_ArrayListAlignedUnmanaged_u32_null_allocatedSlice i2)
    match ← ((do
      let i5 ← pure p0
      let i6 ← Zig.load (Zig.Slice) 8 i5
      let i7 ← pure i6.len
      let i8 ← Zig.callC (mem_Allocator_remap__anon_fdce5ddbfdcf p1 i3 i7)
      let i9 ← pure ((i8).isSome)
      if i9 then (do
        let i11 ← Zig.optPayload i8
        Zig.store (α := array_list_ArrayListAlignedUnmanaged_u32_null) 8 p0 ({ items := (⟨(⟨some 0, 0⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice), capacity := (0 : BitVec 64) } : array_list_ArrayListAlignedUnmanaged_u32_null)
        let i13 ← pure ((.ok i11) : Except Zig.ErrName (Zig.Slice))
        pure (.ret i13))
      else (do
        pure .br4)) : Zig.CM Tgt array_list_ArrayListAlignedUnmanaged_u32_null_toOwnedSliceLocals array_list_ArrayListAlignedUnmanaged_u32_null_toOwnedSliceExit) with
    | .br4 => (do
      let i16 ← pure p0
      let i17 ← Zig.load (Zig.Slice) 8 i16
      let i18 ← pure i17.len
      let i19 ← Zig.callC (mem_Allocator_alignedAlloc__anon_867b1b77a8ed p1 i18)
      match i19 with
      | .error _ => (do
        let i21 ← Zig.callRC (Zig.unwrapErr i19)
        let i22 ← pure ((.error i21) : Except Zig.ErrName (Zig.Slice))
        pure (.ret i22))
      | .ok v20 => (do
        let i24 ← pure p0
        let i25 ← Zig.load (Zig.Slice) 8 i24
        let i26 ← pure v20.len
        let i27 ← pure i25.len
        let i28 ← pure (i26 == i27)
        match ← ((do
          if i28 then (do
            pure .br29)
          else (do
            throw .panic)) : Zig.CM Tgt array_list_ArrayListAlignedUnmanaged_u32_null_toOwnedSliceLocals array_list_ArrayListAlignedUnmanaged_u32_null_toOwnedSliceExit) with
        | .br29 => (do
          let i34 ← pure i25.ptr
          let i35 ← pure v20.ptr
          let i36 ← Zig.callMC (Zig.ptrProject i34 (·.elem 4 i26))
          let i37 ← Zig.callMC (Zig.ptrProject i35 (·.elem 4 i26))
          let i38 ← Zig.callMC (Zig.ptrLe i36 i35)
          let i39 ← Zig.callMC (Zig.ptrLe i37 i34)
          let i40 ← pure (i38 || i39)
          match ← ((do
            if i40 then (do
              pure .br41)
            else (do
              throw .panic)) : Zig.CM Tgt array_list_ArrayListAlignedUnmanaged_u32_null_toOwnedSliceLocals array_list_ArrayListAlignedUnmanaged_u32_null_toOwnedSliceExit) with
          | .br41 => (do
            Zig.callMC (Zig.memcpy 4 4 4 v20.ptr i34 v20.len i25.len)
            let _i47 ← Zig.callC (array_list_ArrayListAlignedUnmanaged_u32_null_clearAndFree p0 p1)
            let i48 ← pure ((.ok v20) : Except Zig.ErrName (Zig.Slice))
            pure (.ret i48))
          | e => pure e)
        | e => pure e))
    | e => pure e) : Zig.CM Tgt array_list_ArrayListAlignedUnmanaged_u32_null_toOwnedSliceLocals array_list_ArrayListAlignedUnmanaged_u32_null_toOwnedSliceExit).run' (default : array_list_ArrayListAlignedUnmanaged_u32_null_toOwnedSliceLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] array_list_ArrayListAlignedUnmanaged_u32_null_toOwnedSlice

structure evensLocals where
  list : Zig.Ptr
  local4 : BitVec 64
  deriving Inhabited

inductive evensExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br16
  | br10
  | br7
  | rep8

def evens.again8 : evensExit → Bool
  | .rep8 => true
  | _ => false

def evens.loop8 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (i2 : Zig.Ptr) (i6 : BitVec 64) : Zig.CM Tgt evensLocals evensExit := do
  Zig.callMC Zig.tick
  let i9 ← pure ((← get).local4)
  match ← ((do
    let i11 ← pure (i9)
    let i12 ← pure (i6)
    let i13 ← pure (Zig.lt false i11 i12)
    if i13 then (do
      let i15 ← Zig.callMC (Zig.checkIndex p1.len i9 >>= fun _ => Zig.load (BitVec 32) 4 (p1.ptr.elem 4 i9))
      match ← ((do
        let i17 ← Zig.rem false i15 (2 : BitVec 32)
        let i18 ← pure (i17 == (0 : BitVec 32))
        if i18 then (do
          let i20 ← Zig.callC (array_list_ArrayListAlignedUnmanaged_u32_null_append i2 p0 i15)
          match i20 with
          | .error _ => (do
            let i22 ← Zig.callRC (Zig.unwrapErr i20)
            let _i23 ← Zig.callC (array_list_ArrayListAlignedUnmanaged_u32_null_deinit i2 p0)
            let i24 ← pure (i22)
            let i25 ← pure ((.error i24) : Except Zig.ErrName (Zig.Slice))
            pure (.ret i25))
          | .ok _v21 => (do
            pure .br16))
        else (do
          pure .br16)) : Zig.CM Tgt evensLocals evensExit) with
      | .br16 => (do
        pure .br10)
      | e => pure e)
    else (do
      pure .br7)) : Zig.CM Tgt evensLocals evensExit) with
  | .br10 => (do
    let i31 ← Zig.add false i9 (1 : BitVec 64) (safe := false)
    modify (fun s => { s with local4 := i31 })
    pure .rep8)
  | e => pure e

def evens [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s2 ← Zig.allocStack 24 8
  let e ← ((do
    let i2 ← pure (← get).list
    Zig.store (α := array_list_ArrayListAlignedUnmanaged_u32_null) 8 i2 ({ items := (⟨(⟨some 0, 0⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice), capacity := (0 : BitVec 64) } : array_list_ArrayListAlignedUnmanaged_u32_null)
    modify (fun s => { s with local4 := (0 : BitVec 64) })
    let i6 ← pure p1.len
    match ← ((do
      Zig.loop (evens.loop8 p0 p1 i2 i6) evens.again8) : Zig.CM Tgt evensLocals evensExit) with
    | .br7 => (do
      let i34 ← Zig.callC (array_list_ArrayListAlignedUnmanaged_u32_null_toOwnedSlice i2 p0)
      let i35 ← pure (Zig.isNonErr i34)
      if i35 then (do
        let i37 ← pure (i34)
        pure (.ret i37))
      else (do
        let _i39 ← Zig.callC (array_list_ArrayListAlignedUnmanaged_u32_null_deinit i2 p0)
        let i40 ← pure (i34)
        pure (.ret i40)))
    | e => pure e) : Zig.CM Tgt evensLocals evensExit).run' { (default : evensLocals) with list := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] evens.loop8 evens

structure mem_Allocator_destroy__anon_a9add1f02861Locals where
  deriving Inhabited

inductive mem_Allocator_destroy__anon_a9add1f02861Exit where
  | ret
  | br8

def mem_Allocator_destroy__anon_a9add1f02861 [Ext] (p0 : mem_Allocator) (p1 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← pure (p1)
    let i3 ← pure i2
    let i4 ← pure (i3)
    let i5 ← pure (⟨i4, (16 : BitVec 64)⟩ : Zig.Slice)
    let i6 ← Zig.callRC (mem_Alignment_fromByteUnits (8 : BitVec 64))
    let i7 ← Zig.callMC Zig.returnAddress
    match ← ((do
      let i9 ← pure ((p0).vtable)
      let i10 ← Zig.callMC (Zig.ptrProject i9 (·.add 24))
      let i11 ← Zig.load (Zig.Ptr) 8 i10
      let i12 ← pure ((p0).ptr)
      let _i13 ← (Zig.callC (Zig.extCall (Ext.call2 i11 i12 i5 i6 i7)))
      pure .br8) : Zig.CM Tgt mem_Allocator_destroy__anon_a9add1f02861Locals mem_Allocator_destroy__anon_a9add1f02861Exit) with
    | .br8 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt mem_Allocator_destroy__anon_a9add1f02861Locals mem_Allocator_destroy__anon_a9add1f02861Exit).run' (default : mem_Allocator_destroy__anon_a9add1f02861Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_destroy__anon_a9add1f02861

structure freeAllLocals where
  p : Option (Zig.Ptr)
  deriving Inhabited

inductive freeAllExit where
  | ret
  | br6
  | br4
  | rep5

def freeAll.again5 : freeAllExit → Bool
  | .rep5 => true
  | _ => false

def freeAll.loop5 [Ext] (p0 : mem_Allocator) : Zig.CM Tgt freeAllLocals freeAllExit := do
  Zig.callMC Zig.tick
  match ← ((do
    let i7 ← pure ((← get).p)
    let i8 ← pure ((i7).isSome)
    if i8 then (do
      let i10 ← Zig.optPayload i7
      let i11 ← pure i10
      let i12 ← Zig.load (Option (Zig.Ptr)) 8 i11
      modify (fun s => { s with p := i12 })
      let _i14 ← Zig.callC (mem_Allocator_destroy__anon_a9add1f02861 p0 i10)
      pure .br6)
    else (do
      pure .br4)) : Zig.CM Tgt freeAllLocals freeAllExit) with
  | .br6 => (do
    pure .rep5)
  | e => pure e

def freeAll [Ext] (p0 : mem_Allocator) (p1 : Option (Zig.Ptr)) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    modify (fun s => { s with p := p1 })
    match ← ((do
      Zig.loop (freeAll.loop5 p0) freeAll.again5) : Zig.CM Tgt freeAllLocals freeAllExit) with
    | .br4 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt freeAllLocals freeAllExit).run' (default : freeAllLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] freeAll.loop5 freeAll

structure mem_Allocator_allocBytesWithAlignment__anon_0ac18f6d9740Locals where
  deriving Inhabited

inductive mem_Allocator_allocBytesWithAlignment__anon_0ac18f6d9740Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3
  | br11 (v : Option (Zig.Ptr))
  | br9 (v : Zig.Ptr)
  | br29

def mem_Allocator_allocBytesWithAlignment__anon_0ac18f6d9740 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (⟨none, 18446744073709551608⟩ : Zig.Ptr) : Except Zig.ErrName (Zig.Ptr))))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_0ac18f6d9740Locals mem_Allocator_allocBytesWithAlignment__anon_0ac18f6d9740Exit) with
    | .br3 => (do
      match ← ((do
        let i10 ← Zig.callRC (mem_Alignment_fromByteUnits (8 : BitVec 64))
        match ← ((do
          let i12 ← pure ((p0).vtable)
          let i13 ← pure i12
          let i14 ← Zig.load (Zig.Ptr) 8 i13
          let i15 ← pure ((p0).ptr)
          let i16 ← (Zig.callC (Zig.extCall (Ext.call0 i14 i15 p1 i10 p2)))
          pure (.br11 i16)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_0ac18f6d9740Locals mem_Allocator_allocBytesWithAlignment__anon_0ac18f6d9740Exit) with
        | .br11 v11 => (do
          let i18 ← pure ((v11).isSome)
          if i18 then (do
            let i20 ← Zig.optPayload v11
            pure (.br9 i20))
          else (do
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr)))))
        | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_0ac18f6d9740Locals mem_Allocator_allocBytesWithAlignment__anon_0ac18f6d9740Exit) with
      | .br9 v9 => (do
        let i23 ← pure v9
        let i24 ← pure (⟨i23, p1⟩ : Zig.Slice)
        Zig.callMC (Zig.memset (α := BitVec 8) 1 i24.ptr i24.len none)
        let i26 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr v9)))
        let i27 ← pure (i26 &&& (7 : BitVec 64))
        let i28 ← pure (i27 == (0 : BitVec 64))
        match ← ((do
          if i28 then (do
            pure .br29)
          else (do
            throw .panic)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_0ac18f6d9740Locals mem_Allocator_allocBytesWithAlignment__anon_0ac18f6d9740Exit) with
        | .br29 => (do
          let i34 ← Zig.callMC (Zig.checkAlign 8 v9 >>= fun _ => pure v9)
          let i35 ← pure ((.ok i34) : Except Zig.ErrName (Zig.Ptr))
          pure (.ret i35))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_0ac18f6d9740Locals mem_Allocator_allocBytesWithAlignment__anon_0ac18f6d9740Exit).run' (default : mem_Allocator_allocBytesWithAlignment__anon_0ac18f6d9740Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocBytesWithAlignment__anon_0ac18f6d9740

structure mem_Allocator_create__anon_48603a336c43Locals where
  deriving Inhabited

inductive mem_Allocator_create__anon_48603a336c43Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

def mem_Allocator_create__anon_48603a336c43 [Ext] (p0 : mem_Allocator) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    let i1 ← Zig.callMC Zig.returnAddress
    let i2 ← Zig.callC (mem_Allocator_allocBytesWithAlignment__anon_0ac18f6d9740 p0 (16 : BitVec 64) i1)
    match i2 with
    | .error _ => (do
      let i4 ← Zig.callRC (Zig.unwrapErr i2)
      let i5 ← pure ((.error i4) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i5))
    | .ok v3 => (do
      let i7 ← pure (v3)
      let i8 ← pure ((.ok i7) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i8))) : Zig.CM Tgt mem_Allocator_create__anon_48603a336c43Locals mem_Allocator_create__anon_48603a336c43Exit).run' (default : mem_Allocator_create__anon_48603a336c43Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_create__anon_48603a336c43

structure pushLocals where
  deriving Inhabited

inductive pushExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

def push [Ext] (p0 : mem_Allocator) (p1 : Option (Zig.Ptr)) (p2 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    let i3 ← Zig.callC (mem_Allocator_create__anon_48603a336c43 p0)
    match i3 with
    | .error _ => (do
      let i5 ← Zig.callRC (Zig.unwrapErr i3)
      let i6 ← pure (i5)
      let i7 ← pure ((.error i6) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i7))
    | .ok v4 => (do
      let i9 ← Zig.callMC (Zig.ptrProject v4 (·.add 8))
      Zig.store (α := BitVec 32) 4 i9 p2
      let i11 ← pure v4
      Zig.store (α := Option (Zig.Ptr)) 8 i11 p1
      let i13 ← pure ((.ok v4) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i13))) : Zig.CM Tgt pushLocals pushExit).run' (default : pushLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] push

structure reverseLocals where
  prev : Option (Zig.Ptr)
  cur : Option (Zig.Ptr)
  deriving Inhabited

inductive reverseExit where
  | ret (v : Option (Zig.Ptr))
  | br7
  | br5
  | rep6

def reverse.again6 : reverseExit → Bool
  | .rep6 => true
  | _ => false

def reverse.loop6  : Zig.MM reverseLocals reverseExit := do
  Zig.callM Zig.tick
  match ← ((do
    let i8 ← pure ((← get).cur)
    let i9 ← pure ((i8).isSome)
    if i9 then (do
      let i11 ← Zig.optPayload i8
      let i12 ← pure i11
      let i13 ← Zig.load (Option (Zig.Ptr)) 8 i12
      modify (fun s => { s with cur := i13 })
      let i15 ← pure i11
      let i16 ← pure ((← get).prev)
      Zig.store (α := Option (Zig.Ptr)) 8 i15 i16
      let i18 ← pure (i11)
      modify (fun s => { s with prev := i18 })
      pure .br7)
    else (do
      pure .br5)) : Zig.MM reverseLocals reverseExit) with
  | .br7 => (do
    pure .rep6)
  | e => pure e

def reverse (p0 : Option (Zig.Ptr)) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    modify (fun s => { s with prev := none })
    modify (fun s => { s with cur := p0 })
    match ← ((do
      Zig.loop (reverse.loop6 ) reverse.again6) : Zig.MM reverseLocals reverseExit) with
    | .br5 => (do
      let i23 ← pure ((← get).prev)
      pure (.ret i23))
    | e => pure e) : Zig.MM reverseLocals reverseExit).run' (default : reverseLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] reverse.loop6 reverse

structure sumLocals where
  s : BitVec 64
  p : Option (Zig.Ptr)
  deriving Inhabited

inductive sumExit where
  | ret (v : BitVec 64)
  | br7
  | br5
  | rep6

def sum.again6 : sumExit → Bool
  | .rep6 => true
  | _ => false

def sum.loop6  : Zig.MM sumLocals sumExit := do
  Zig.callM Zig.tick
  match ← ((do
    let i8 ← pure ((← get).p)
    let i9 ← pure ((i8).isSome)
    if i9 then (do
      let i11 ← Zig.optPayload i8
      let i12 ← pure ((← get).s)
      let i13 ← Zig.callM (Zig.ptrProject i11 (·.add 8))
      let i14 ← Zig.load (BitVec 32) 4 i13
      let i15 ← Zig.intCast false false 64 i14 (safe := false)
      let i16 ← Zig.add false i12 i15
      modify (fun s => { s with s := i16 })
      let i18 ← pure i11
      let i19 ← Zig.load (Option (Zig.Ptr)) 8 i18
      let i20 ← pure (i19)
      modify (fun s => { s with p := i20 })
      pure .br7)
    else (do
      pure .br5)) : Zig.MM sumLocals sumExit) with
  | .br7 => (do
    pure .rep6)
  | e => pure e

def sum (p0 : Option (Zig.Ptr)) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with s := (0 : BitVec 64) })
    modify (fun s => { s with p := p0 })
    match ← ((do
      Zig.loop (sum.loop6 ) sum.again6) : Zig.MM sumLocals sumExit) with
    | .br5 => (do
      let i25 ← pure ((← get).s)
      pure (.ret i25))
    | e => pure e) : Zig.MM sumLocals sumExit).run' (default : sumLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] sum.loop6 sum

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch [Ext] : Tgt → Zig.ConcM Tgt Unit :=
  fun t => nomatch t

attribute [zig_run] dispatch

end Lists.Open