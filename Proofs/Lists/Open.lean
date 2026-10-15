-- air2lean-profile: {"allocator_model":"translated","correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"}}
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

structure debug_SafetyLock_State__enum_1 where
  bits : BitVec 64
  deriving Repr, Inhabited, DecidableEq

def debug_SafetyLock_State__enum_1.unlocked : debug_SafetyLock_State__enum_1 := ⟨(0 : BitVec 64)⟩
def debug_SafetyLock_State__enum_1.exclusive : debug_SafetyLock_State__enum_1 := ⟨(18446744073709551615 : BitVec 64)⟩

def debug_SafetyLock_State__enum_1.toBits (e : debug_SafetyLock_State__enum_1) : BitVec 64 := e.bits

def debug_SafetyLock_State__enum_1.ofInt? (v : Int) : Option debug_SafetyLock_State__enum_1 :=
  if 0 ≤ v ∧ v ≤ 18446744073709551615 then Option.some ⟨BitVec.ofInt 64 v⟩ else Option.none

def debug_SafetyLock_State__enum_1.isNamed (e : debug_SafetyLock_State__enum_1) : Bool := e.bits == (0 : BitVec 64) || e.bits == (18446744073709551615 : BitVec 64)

instance : Zig.Packed debug_SafetyLock_State__enum_1 64 where
  toBits := debug_SafetyLock_State__enum_1.toBits
  ofBits b := ⟨b⟩

instance : Zig.Enc debug_SafetyLock_State__enum_1 where
  size := 8
  align := 8
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 64 ← Zig.Enc.decode bs
    pure ⟨b⟩

structure debug_SafetyLock where
  state : debug_SafetyLock_State__enum_1
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc debug_SafetyLock where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.state)]
  decode bs := do pure { state := ← Zig.Enc.decodeAt bs 0 }

structure array_list_Aligned_u32_null where
  items : Zig.Slice
  capacity : BitVec 64
  pointer_stability : debug_SafetyLock
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc array_list_Aligned_u32_null where
  size := 32
  align := 8
  encode v := Zig.Enc.fields 32 [(0, Zig.Enc.encode v.items), (16, Zig.Enc.encode v.capacity), (24, Zig.Enc.encode v.pointer_stability)]
  decode bs := do pure { items := ← Zig.Enc.decodeAt bs 0, capacity := ← Zig.Enc.decodeAt bs 16, pointer_stability := ← Zig.Enc.decodeAt bs 24 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. The words of `@returnAddress()` and of `undefined` pointers are `arbitrary` (`Mem.arbitrary`). -/
def mem0 (σ : Zig.Placement) (arbitrary : Array (BitVec 64) := #[]) : Zig.Mem := { Zig.Mem.ofGlobals σ [
  -- 0: a constant
  (Zig.Enc.encode ((#v[] : Vector (BitVec 32) 0) : Vector (BitVec 32) 0), 4, .constGlobal)] with arbitrary }

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

structure array_list_Aligned_u32_null_growCapacityLocals where
  deriving Inhabited

inductive array_list_Aligned_u32_null_growCapacityExit where
  | ret (v : BitVec 64)

def array_list_Aligned_u32_null_growCapacity (p0 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.divTrunc false p0 (2 : BitVec 64)
    let i2 ← Zig.add false i1 (32 : BitVec 64)
    let i3 ← pure (Zig.addSat false p0 i2)
    pure (.ret i3)) : Zig.M array_list_Aligned_u32_null_growCapacityLocals array_list_Aligned_u32_null_growCapacityExit).run' (default : array_list_Aligned_u32_null_growCapacityLocals)
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

structure debug_SafetyLock_assertUnlockedLocals where
  deriving Inhabited

inductive debug_SafetyLock_assertUnlockedExit where
  | ret

def debug_SafetyLock_assertUnlocked (p0 : debug_SafetyLock) : Zig.Result (Unit) := do
  let e ← ((do
    let i1 ← pure ((p0).state)
    let i2 ← pure (i1 == debug_SafetyLock_State__enum_1.unlocked)
    let _i3 ← Zig.call (debug_assert i2)
    pure .ret) : Zig.M debug_SafetyLock_assertUnlockedLocals debug_SafetyLock_assertUnlockedExit).run' (default : debug_SafetyLock_assertUnlockedLocals)
  match e with
  | .ret => pure ()

structure array_list_Aligned_u32_null_allocatedSliceLocals where
  local1 : array_list_Aligned_u32_null
  deriving Inhabited

inductive array_list_Aligned_u32_null_allocatedSliceExit where
  | ret (v : Zig.Slice)

def array_list_Aligned_u32_null_allocatedSlice (p0 : array_list_Aligned_u32_null) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    modify (fun s => { s with local1 := p0 })
    let i7 ← pure (((← get).local1).capacity)
    let i8 ← pure ((((← get).local1).items).ptr)
    let i9 ← pure i8
    let i10 ← Zig.sub false i7 (0 : BitVec 64) (safe := false)
    let i11 ← pure (⟨i9, i10⟩ : Zig.Slice)
    pure (.ret i11)) : Zig.MM array_list_Aligned_u32_null_allocatedSliceLocals array_list_Aligned_u32_null_allocatedSliceExit).run' (default : array_list_Aligned_u32_null_allocatedSliceLocals)
  match e with
  | .ret v => pure v

structure mem_absorbSentinel__anon_6f5b4b6f7cb0Locals where
  deriving Inhabited

inductive mem_absorbSentinel__anon_6f5b4b6f7cb0Exit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_6f5b4b6f7cb0 (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret p0)) : Zig.MM mem_absorbSentinel__anon_6f5b4b6f7cb0Locals mem_absorbSentinel__anon_6f5b4b6f7cb0Exit).run' (default : mem_absorbSentinel__anon_6f5b4b6f7cb0Locals)
  match e with
  | .ret v => pure v

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

structure mem_Alignment_fromByteUnitsLocals where
  deriving Inhabited

inductive mem_Alignment_fromByteUnitsExit where
  | ret (v : mem_Alignment)

def mem_Alignment_fromByteUnits (p0 : BitVec 64) : Zig.Result (mem_Alignment) := do
  let e ← ((do
    let i1 ← Zig.call (math_isPowerOfTwo__anon_38853e1fe316 p0)
    let _i2 ← Zig.call (debug_assert i1)
    let i3 ← pure (Zig.ctz 7 p0)
    let i4 ← Zig.intCast false false 6 i3
    let i5 ← Zig.enumOf (mem_Alignment.ofInt? (Zig.val false i4))
    pure (.ret i5)) : Zig.M mem_Alignment_fromByteUnitsLocals mem_Alignment_fromByteUnitsExit).run' (default : mem_Alignment_fromByteUnitsLocals)
  match e with
  | .ret v => pure v

structure mem_Allocator_free__anon_10fd68fdc68dLocals where
  deriving Inhabited

inductive mem_Allocator_free__anon_10fd68fdc68dExit where
  | ret
  | br8
  | br19

def mem_Allocator_free__anon_10fd68fdc68d [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_6f5b4b6f7cb0 p1)
    let i3 ← pure i2.ptr
    let i4 ← pure i2.len
    let i5 ← Zig.mul false i4 (4 : BitVec 64) (safe := false)
    let i6 ← pure (i3)
    let i7 ← pure (⟨i6, i5⟩ : Zig.Slice)
    match ← ((do
      let i9 ← pure i7.len
      let i10 ← pure (i9)
      let i11 ← pure (i10 == (0 : BitVec 64))
      if i11 then (do
        pure .ret)
      else (do
        pure .br8)) : Zig.CM Tgt mem_Allocator_free__anon_10fd68fdc68dLocals mem_Allocator_free__anon_10fd68fdc68dExit) with
    | .br8 => (do
      let _i15 ← pure i7.len
      Zig.callMC (Zig.memset (α := BitVec 8) 1 i7.ptr i7.len none)
      let i17 ← Zig.callRC (mem_Alignment_fromByteUnits (4 : BitVec 64))
      let i18 ← Zig.callMC Zig.returnAddress
      match ← ((do
        let i20 ← pure ((p0).vtable)
        let i21 ← Zig.callMC (Zig.ptrProject i20 (·.add 24))
        let i22 ← Zig.load (Zig.Ptr) 8 i21
        let i23 ← pure ((p0).ptr)
        let _i24 ← (Zig.callC (Zig.extCall (Ext.call2 i22 i23 i7 i17 i18)))
        pure .br19) : Zig.CM Tgt mem_Allocator_free__anon_10fd68fdc68dLocals mem_Allocator_free__anon_10fd68fdc68dExit) with
      | .br19 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_10fd68fdc68dLocals mem_Allocator_free__anon_10fd68fdc68dExit).run' (default : mem_Allocator_free__anon_10fd68fdc68dLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

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

structure mem_Allocator_remap__anon_fdce5ddbfdcfLocals where
  deriving Inhabited

inductive mem_Allocator_remap__anon_fdce5ddbfdcfExit where
  | ret (v : Option (Zig.Slice))
  | br3
  | br16
  | br29 (v : BitVec 64)
  | br40 (v : Option (Zig.Ptr))
  | br37 (v : Zig.Ptr)
  | br62
  | br69

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
        let i23 ← Zig.callMC (mem_absorbSentinel__anon_6f5b4b6f7cb0 p1)
        let i24 ← pure i23.ptr
        let i25 ← pure i23.len
        let i26 ← Zig.mul false i25 (4 : BitVec 64) (safe := false)
        let i27 ← pure (i24)
        let i28 ← pure (⟨i27, i26⟩ : Zig.Slice)
        match ← ((do
          let i30 ← Zig.callRC (math_mul__anon_44faaf286c79 (4 : BitVec 64) p2)
          let i31 ← pure (Zig.isNonErr i30)
          if i31 then (do
            let i33 ← Zig.callRC (Zig.unwrapPayload i30)
            pure (.br29 i33))
          else (do
            let _i35 ← Zig.callRC (Zig.unwrapErr i30)
            pure (.ret none))) : Zig.CM Tgt mem_Allocator_remap__anon_fdce5ddbfdcfLocals mem_Allocator_remap__anon_fdce5ddbfdcfExit) with
        | .br29 v29 => (do
          match ← ((do
            let i38 ← Zig.callRC (mem_Alignment_fromByteUnits (4 : BitVec 64))
            let i39 ← Zig.callMC Zig.returnAddress
            match ← ((do
              let i41 ← pure ((p0).vtable)
              let i42 ← Zig.callMC (Zig.ptrProject i41 (·.add 16))
              let i43 ← Zig.load (Zig.Ptr) 8 i42
              let i44 ← pure ((p0).ptr)
              let i45 ← (Zig.callC (Zig.extCall (Ext.call1 i43 i44 i28 i38 v29 i39)))
              pure (.br40 i45)) : Zig.CM Tgt mem_Allocator_remap__anon_fdce5ddbfdcfLocals mem_Allocator_remap__anon_fdce5ddbfdcfExit) with
            | .br40 v40 => (do
              let i47 ← pure ((v40).isSome)
              if i47 then (do
                let i49 ← Zig.optPayload v40
                pure (.br37 i49))
              else (do
                pure (.ret none)))
            | e => pure e) : Zig.CM Tgt mem_Allocator_remap__anon_fdce5ddbfdcfLocals mem_Allocator_remap__anon_fdce5ddbfdcfExit) with
          | .br37 v37 => (do
            let i52 ← pure v37
            let i53 ← Zig.sub false v29 (0 : BitVec 64) (safe := false)
            let i54 ← pure (⟨i52, i53⟩ : Zig.Slice)
            let i55 ← pure i54.ptr
            let i56 ← pure i54.len
            let i57 ← pure (i56 == (0 : BitVec 64))
            let i58 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i55)))
            let i59 ← pure (i58 &&& (3 : BitVec 64))
            let i60 ← pure (i59 == (0 : BitVec 64))
            let i61 ← pure (i57 || i60)
            match ← ((do
              if i61 then (do
                pure .br62)
              else (do
                throw .panic)) : Zig.CM Tgt mem_Allocator_remap__anon_fdce5ddbfdcfLocals mem_Allocator_remap__anon_fdce5ddbfdcfExit) with
            | .br62 => (do
              let i67 ← Zig.rem false i56 (4 : BitVec 64)
              let i68 ← pure (i67 == (0 : BitVec 64))
              match ← ((do
                if i68 then (do
                  pure .br69)
                else (do
                  throw .panic)) : Zig.CM Tgt mem_Allocator_remap__anon_fdce5ddbfdcfLocals mem_Allocator_remap__anon_fdce5ddbfdcfExit) with
              | .br69 => (do
                let i74 ← Zig.divExact false i56 (4 : BitVec 64)
                let i75 ← pure (i55)
                let i76 ← pure (⟨i75, i74⟩ : Zig.Slice)
                pure (.ret i76))
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_remap__anon_fdce5ddbfdcfLocals mem_Allocator_remap__anon_fdce5ddbfdcfExit).run' (default : mem_Allocator_remap__anon_fdce5ddbfdcfLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_allocBytesAligned__anon_c9141768de1aLocals where
  deriving Inhabited

inductive mem_Allocator_allocBytesAligned__anon_c9141768de1aExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3
  | br10 (v : Option (Zig.Ptr))
  | br9 (v : Zig.Ptr)
  | br30

def mem_Allocator_allocBytesAligned__anon_c9141768de1a [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (⟨none, 18446744073709551612⟩ : Zig.Ptr) : Except Zig.ErrName (Zig.Ptr))))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_c9141768de1aLocals mem_Allocator_allocBytesAligned__anon_c9141768de1aExit) with
    | .br3 => (do
      match ← ((do
        match ← ((do
          let i11 ← pure ((p0).vtable)
          let i12 ← pure i11
          let i13 ← Zig.load (Zig.Ptr) 8 i12
          let i14 ← pure ((p0).ptr)
          let i15 ← (Zig.callC (Zig.extCall (Ext.call0 i13 i14 p1 mem_Alignment.«4» p2)))
          pure (.br10 i15)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_c9141768de1aLocals mem_Allocator_allocBytesAligned__anon_c9141768de1aExit) with
        | .br10 v10 => (do
          let i17 ← pure ((v10).isSome)
          if i17 then (do
            let i19 ← Zig.optPayload v10
            pure (.br9 i19))
          else (do
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr)))))
        | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_c9141768de1aLocals mem_Allocator_allocBytesAligned__anon_c9141768de1aExit) with
      | .br9 v9 => (do
        let i22 ← pure v9
        let i23 ← Zig.sub false p1 (0 : BitVec 64) (safe := false)
        let i24 ← pure (⟨i22, i23⟩ : Zig.Slice)
        let _i25 ← pure i24.len
        Zig.callMC (Zig.memset (α := BitVec 8) 1 i24.ptr i24.len none)
        let i27 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr v9)))
        let i28 ← pure (i27 &&& (3 : BitVec 64))
        let i29 ← pure (i28 == (0 : BitVec 64))
        match ← ((do
          if i29 then (do
            pure .br30)
          else (do
            throw .panic)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_c9141768de1aLocals mem_Allocator_allocBytesAligned__anon_c9141768de1aExit) with
        | .br30 => (do
          let i35 ← Zig.callMC (Zig.checkAlign 4 v9 >>= fun _ => pure v9)
          let i36 ← pure ((.ok i35) : Except Zig.ErrName (Zig.Ptr))
          pure (.ret i36))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_c9141768de1aLocals mem_Allocator_allocBytesAligned__anon_c9141768de1aExit).run' (default : mem_Allocator_allocBytesAligned__anon_c9141768de1aLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_allocWithSizeAndAlignment__anon_7f4b76fbd810Locals where
  deriving Inhabited

inductive mem_Allocator_allocWithSizeAndAlignment__anon_7f4b76fbd810Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3 (v : BitVec 64)

def mem_Allocator_allocWithSizeAndAlignment__anon_7f4b76fbd810 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.callRC (math_mul__anon_44faaf286c79 (4 : BitVec 64) p1)
      let i5 ← pure (Zig.isNonErr i4)
      if i5 then (do
        let i7 ← Zig.callRC (Zig.unwrapPayload i4)
        pure (.br3 i7))
      else (do
        let _i9 ← Zig.callRC (Zig.unwrapErr i4)
        pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr))))) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_7f4b76fbd810Locals mem_Allocator_allocWithSizeAndAlignment__anon_7f4b76fbd810Exit) with
    | .br3 v3 => (do
      let i11 ← Zig.callC (mem_Allocator_allocBytesAligned__anon_c9141768de1a p0 v3 p2)
      pure (.ret i11))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_7f4b76fbd810Locals mem_Allocator_allocWithSizeAndAlignment__anon_7f4b76fbd810Exit).run' (default : mem_Allocator_allocWithSizeAndAlignment__anon_7f4b76fbd810Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_alignedAlloc__anon_0b20c0554625Locals where
  deriving Inhabited

inductive mem_Allocator_alignedAlloc__anon_0b20c0554625Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br3 (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_alignedAlloc__anon_0b20c0554625 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.callMC Zig.returnAddress
    match ← ((do
      let i4 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_7f4b76fbd810 p0 p1 i2)
      match i4 with
      | .error _ => (do
        let i6 ← Zig.callRC (Zig.unwrapErr i4)
        let i7 ← pure ((.error i6) : Except Zig.ErrName (Zig.Slice))
        pure (.br3 i7))
      | .ok v5 => (do
        let i9 ← pure (v5)
        let i10 ← pure i9
        let i11 ← Zig.sub false p1 (0 : BitVec 64) (safe := false)
        let i12 ← pure (⟨i10, i11⟩ : Zig.Slice)
        let i13 ← pure ((.ok i12) : Except Zig.ErrName (Zig.Slice))
        pure (.br3 i13))) : Zig.CM Tgt mem_Allocator_alignedAlloc__anon_0b20c0554625Locals mem_Allocator_alignedAlloc__anon_0b20c0554625Exit) with
    | .br3 v3 => (do
      pure (.ret v3))
    | e => pure e) : Zig.CM Tgt mem_Allocator_alignedAlloc__anon_0b20c0554625Locals mem_Allocator_alignedAlloc__anon_0b20c0554625Exit).run' (default : mem_Allocator_alignedAlloc__anon_0b20c0554625Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure array_list_Aligned_u32_null_ensureTotalCapacityPreciseLocals where
  local22 : Zig.Slice
  local40 : Zig.Slice
  deriving Inhabited

inductive array_list_Aligned_u32_null_ensureTotalCapacityPreciseExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br6
  | br17
  | br52
  | br63
  | br75

def array_list_Aligned_u32_null_ensureTotalCapacityPrecise [Ext] (p0 : Zig.Ptr) (p1 : mem_Allocator) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    let i3 ← Zig.callMC (Zig.ptrProject p0 (·.add 24))
    let i4 ← Zig.load (debug_SafetyLock) 8 i3
    let _i5 ← Zig.callRC (debug_SafetyLock_assertUnlocked i4)
    match ← ((do
      let i7 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
      let i8 ← Zig.load (BitVec 64) 8 i7
      let i9 ← pure (i8)
      let i10 ← pure (p2)
      let i11 ← pure (Zig.ge false i9 i10)
      if i11 then (do
        pure (.ret (.ok () : Except Zig.ErrName (Unit))))
      else (do
        pure .br6)) : Zig.CM Tgt array_list_Aligned_u32_null_ensureTotalCapacityPreciseLocals array_list_Aligned_u32_null_ensureTotalCapacityPreciseExit) with
    | .br6 => (do
      let i15 ← Zig.load (array_list_Aligned_u32_null) 8 p0
      let i16 ← Zig.callMC (array_list_Aligned_u32_null_allocatedSlice i15)
      match ← ((do
        let i18 ← Zig.callC (mem_Allocator_remap__anon_fdce5ddbfdcf p1 i16 p2)
        let i19 ← pure ((i18).isSome)
        if i19 then (do
          let i21 ← Zig.optPayload i18
          modify (fun s => { s with local22 := i21 })
          let i25 ← pure p0
          let i26 ← pure i25
          let i28 ← pure (((← get).local22).ptr)
          Zig.store (α := Zig.Ptr) 8 i26 i28
          let i30 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
          let i32 ← pure (((← get).local22).len)
          Zig.store (α := BitVec 64) 8 i30 i32
          pure .br17)
        else (do
          let i35 ← Zig.callC (mem_Allocator_alignedAlloc__anon_0b20c0554625 p1 p2)
          match i35 with
          | .error _ => (do
            let i37 ← Zig.callRC (Zig.unwrapErr i35)
            let i38 ← pure ((.error i37) : Except Zig.ErrName (Unit))
            pure (.ret i38))
          | .ok v36 => (do
            modify (fun s => { s with local40 := v36 })
            let i43 ← pure p0
            let i44 ← Zig.callMC (Zig.ptrProject i43 (·.add 8))
            let i45 ← Zig.load (BitVec 64) 8 i44
            let i46 ← pure ((← get).local40)
            let i47 ← pure i46.ptr
            let i48 ← pure i47
            let i49 ← Zig.sub false i45 (0 : BitVec 64) (safe := false)
            let i50 ← pure i46.len
            let i51 ← pure (Zig.le false i45 i50)
            match ← ((do
              if i51 then (do
                pure .br52)
              else (do
                throw .outOfBounds)) : Zig.CM Tgt array_list_Aligned_u32_null_ensureTotalCapacityPreciseLocals array_list_Aligned_u32_null_ensureTotalCapacityPreciseExit) with
            | .br52 => (do
              let i57 ← Zig.callMC (Zig.checkSliceEnd i46.len (0 : BitVec 64) i49 0 >>= fun _ => pure (⟨i48, i49⟩ : Zig.Slice))
              let i58 ← pure p0
              let i59 ← Zig.load (Zig.Slice) 8 i58
              let i60 ← pure i57.len
              let i61 ← pure i59.len
              let i62 ← pure (i60 == i61)
              match ← ((do
                if i62 then (do
                  pure .br63)
                else (do
                  throw .panic)) : Zig.CM Tgt array_list_Aligned_u32_null_ensureTotalCapacityPreciseLocals array_list_Aligned_u32_null_ensureTotalCapacityPreciseExit) with
              | .br63 => (do
                let i68 ← pure i59.ptr
                let i69 ← pure i57.ptr
                let i70 ← Zig.callMC (Zig.ptrProject i68 (·.elem 4 i60))
                let i71 ← Zig.callMC (Zig.ptrProject i69 (·.elem 4 i60))
                let i72 ← Zig.callMC (Zig.ptrLe i70 i69)
                let i73 ← Zig.callMC (Zig.ptrLe i71 i68)
                let i74 ← pure (i72 || i73)
                match ← ((do
                  if i74 then (do
                    pure .br75)
                  else (do
                    throw .panic)) : Zig.CM Tgt array_list_Aligned_u32_null_ensureTotalCapacityPreciseLocals array_list_Aligned_u32_null_ensureTotalCapacityPreciseExit) with
                | .br75 => (do
                  Zig.callMC (Zig.memcpy 4 4 4 i57.ptr i68 i57.len i59.len)
                  let _i81 ← Zig.callC (mem_Allocator_free__anon_10fd68fdc68d p1 i16)
                  let i82 ← pure p0
                  let i83 ← pure i82
                  let i85 ← pure (((← get).local40).ptr)
                  let i86 ← pure (i85)
                  Zig.store (α := Zig.Ptr) 8 i83 i86
                  let i88 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
                  let i90 ← pure (((← get).local40).len)
                  Zig.store (α := BitVec 64) 8 i88 i90
                  pure .br17)
                | e => pure e)
              | e => pure e)
            | e => pure e))) : Zig.CM Tgt array_list_Aligned_u32_null_ensureTotalCapacityPreciseLocals array_list_Aligned_u32_null_ensureTotalCapacityPreciseExit) with
      | .br17 => (do
        pure (.ret (.ok () : Except Zig.ErrName (Unit))))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt array_list_Aligned_u32_null_ensureTotalCapacityPreciseLocals array_list_Aligned_u32_null_ensureTotalCapacityPreciseExit).run' (default : array_list_Aligned_u32_null_ensureTotalCapacityPreciseLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure array_list_Aligned_u32_null_ensureTotalCapacityLocals where
  deriving Inhabited

inductive array_list_Aligned_u32_null_ensureTotalCapacityExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br3

def array_list_Aligned_u32_null_ensureTotalCapacity [Ext] (p0 : Zig.Ptr) (p1 : mem_Allocator) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
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
        pure .br3)) : Zig.CM Tgt array_list_Aligned_u32_null_ensureTotalCapacityLocals array_list_Aligned_u32_null_ensureTotalCapacityExit) with
    | .br3 => (do
      let i12 ← Zig.callRC (array_list_Aligned_u32_null_growCapacity p2)
      let i13 ← Zig.callC (array_list_Aligned_u32_null_ensureTotalCapacityPrecise p0 p1 i12)
      pure (.ret i13))
    | e => pure e) : Zig.CM Tgt array_list_Aligned_u32_null_ensureTotalCapacityLocals array_list_Aligned_u32_null_ensureTotalCapacityExit).run' (default : array_list_Aligned_u32_null_ensureTotalCapacityLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure array_list_Aligned_u32_null_addOneAssumeCapacityLocals where
  deriving Inhabited

inductive array_list_Aligned_u32_null_addOneAssumeCapacityExit where
  | ret (v : Zig.Ptr)
  | br23

def array_list_Aligned_u32_null_addOneAssumeCapacity (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← pure p0
    let i2 ← Zig.callM (Zig.ptrProject i1 (·.add 8))
    let i3 ← Zig.load (BitVec 64) 8 i2
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
    let i17 ← Zig.callM (Zig.ptrProject i16 (·.add 8))
    let i18 ← Zig.load (BitVec 64) 8 i17
    let i19 ← Zig.sub false i18 (1 : BitVec 64)
    let i20 ← Zig.load (Zig.Slice) 8 i15
    let i21 ← pure i20.len
    let i22 ← pure (Zig.lt false i19 i21)
    match ← ((do
      if i22 then (do
        pure .br23)
      else (do
        throw .outOfBounds)) : Zig.MM array_list_Aligned_u32_null_addOneAssumeCapacityLocals array_list_Aligned_u32_null_addOneAssumeCapacityExit) with
    | .br23 => (do
      let i28 ← Zig.callM (Zig.checkIndex i20.len i19) >>= fun _ => Zig.callM (Zig.ptrProject i20.ptr (·.elem 4 i19))
      pure (.ret i28))
    | e => pure e) : Zig.MM array_list_Aligned_u32_null_addOneAssumeCapacityLocals array_list_Aligned_u32_null_addOneAssumeCapacityExit).run' (default : array_list_Aligned_u32_null_addOneAssumeCapacityLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure array_list_Aligned_u32_null_addOneLocals where
  deriving Inhabited

inductive array_list_Aligned_u32_null_addOneExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

def array_list_Aligned_u32_null_addOne [Ext] (p0 : Zig.Ptr) (p1 : mem_Allocator) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.callMC (Zig.ptrProject i2 (·.add 8))
    let i4 ← Zig.load (BitVec 64) 8 i3
    let i5 ← Zig.add false i4 (1 : BitVec 64)
    let i6 ← Zig.callC (array_list_Aligned_u32_null_ensureTotalCapacity p0 p1 i5)
    match i6 with
    | .error _ => (do
      let i8 ← Zig.callRC (Zig.unwrapErr i6)
      let i9 ← pure ((.error i8) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i9))
    | .ok _v7 => (do
      let i11 ← Zig.callMC (array_list_Aligned_u32_null_addOneAssumeCapacity p0)
      let i12 ← pure ((.ok i11) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i12))) : Zig.CM Tgt array_list_Aligned_u32_null_addOneLocals array_list_Aligned_u32_null_addOneExit).run' (default : array_list_Aligned_u32_null_addOneLocals)
  match e with
  | .ret v => pure v

structure array_list_Aligned_u32_null_appendLocals where
  deriving Inhabited

inductive array_list_Aligned_u32_null_appendExit where
  | ret (v : Except Zig.ErrName (Unit))

def array_list_Aligned_u32_null_append [Ext] (p0 : Zig.Ptr) (p1 : mem_Allocator) (p2 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    let i3 ← Zig.callC (array_list_Aligned_u32_null_addOne p0 p1)
    match i3 with
    | .error _ => (do
      let i5 ← Zig.callRC (Zig.unwrapErr i3)
      let i6 ← pure ((.error i5) : Except Zig.ErrName (Unit))
      pure (.ret i6))
    | .ok v4 => (do
      Zig.store (α := BitVec 32) 4 v4 p2
      pure (.ret (.ok () : Except Zig.ErrName (Unit))))) : Zig.CM Tgt array_list_Aligned_u32_null_appendLocals array_list_Aligned_u32_null_appendExit).run' (default : array_list_Aligned_u32_null_appendLocals)
  match e with
  | .ret v => pure v

structure array_list_Aligned_u32_null_clearAndFreeLocals where
  deriving Inhabited

inductive array_list_Aligned_u32_null_clearAndFreeExit where
  | ret

def array_list_Aligned_u32_null_clearAndFree [Ext] (p0 : Zig.Ptr) (p1 : mem_Allocator) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (Zig.ptrProject p0 (·.add 24))
    let i3 ← Zig.load (debug_SafetyLock) 8 i2
    let _i4 ← Zig.callRC (debug_SafetyLock_assertUnlocked i3)
    let i5 ← Zig.load (array_list_Aligned_u32_null) 8 p0
    let i6 ← Zig.callMC (array_list_Aligned_u32_null_allocatedSlice i5)
    let _i7 ← Zig.callC (mem_Allocator_free__anon_10fd68fdc68d p1 i6)
    let i8 ← pure p0
    let i9 ← Zig.callMC (Zig.ptrProject i8 (·.add 8))
    Zig.store (α := BitVec 64) 8 i9 (0 : BitVec 64)
    let i11 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
    Zig.store (α := BitVec 64) 8 i11 (0 : BitVec 64)
    pure .ret) : Zig.CM Tgt array_list_Aligned_u32_null_clearAndFreeLocals array_list_Aligned_u32_null_clearAndFreeExit).run' (default : array_list_Aligned_u32_null_clearAndFreeLocals)
  match e with
  | .ret => pure ()

structure array_list_Aligned_u32_null_deinitLocals where
  deriving Inhabited

inductive array_list_Aligned_u32_null_deinitExit where
  | ret

def array_list_Aligned_u32_null_deinit [Ext] (p0 : Zig.Ptr) (p1 : mem_Allocator) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (Zig.ptrProject p0 (·.add 24))
    let i3 ← Zig.load (debug_SafetyLock) 8 i2
    let _i4 ← Zig.callRC (debug_SafetyLock_assertUnlocked i3)
    let i5 ← Zig.load (array_list_Aligned_u32_null) 8 p0
    let i6 ← Zig.callMC (array_list_Aligned_u32_null_allocatedSlice i5)
    let _i7 ← Zig.callC (mem_Allocator_free__anon_10fd68fdc68d p1 i6)
    Zig.storeUndef (array_list_Aligned_u32_null) 8 p0
    pure .ret) : Zig.CM Tgt array_list_Aligned_u32_null_deinitLocals array_list_Aligned_u32_null_deinitExit).run' (default : array_list_Aligned_u32_null_deinitLocals)
  match e with
  | .ret => pure ()

structure array_list_Aligned_u32_null_toOwnedSliceLocals where
  deriving Inhabited

inductive array_list_Aligned_u32_null_toOwnedSliceExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br7
  | br32
  | br44

def array_list_Aligned_u32_null_toOwnedSlice [Ext] (p0 : Zig.Ptr) (p1 : mem_Allocator) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.load (array_list_Aligned_u32_null) 8 p0
    let i3 ← Zig.callMC (array_list_Aligned_u32_null_allocatedSlice i2)
    let i4 ← Zig.callMC (Zig.ptrProject p0 (·.add 24))
    let i5 ← Zig.load (debug_SafetyLock) 8 i4
    let _i6 ← Zig.callRC (debug_SafetyLock_assertUnlocked i5)
    match ← ((do
      let i8 ← pure p0
      let i9 ← Zig.callMC (Zig.ptrProject i8 (·.add 8))
      let i10 ← Zig.load (BitVec 64) 8 i9
      let i11 ← Zig.callC (mem_Allocator_remap__anon_fdce5ddbfdcf p1 i3 i10)
      let i12 ← pure ((i11).isSome)
      if i12 then (do
        let i14 ← Zig.optPayload i11
        Zig.store (α := array_list_Aligned_u32_null) 8 p0 ({ items := (⟨(⟨some 0, 0⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice), capacity := (0 : BitVec 64), pointer_stability := ({ state := debug_SafetyLock_State__enum_1.unlocked } : debug_SafetyLock) } : array_list_Aligned_u32_null)
        let i16 ← pure ((.ok i14) : Except Zig.ErrName (Zig.Slice))
        pure (.ret i16))
      else (do
        pure .br7)) : Zig.CM Tgt array_list_Aligned_u32_null_toOwnedSliceLocals array_list_Aligned_u32_null_toOwnedSliceExit) with
    | .br7 => (do
      let i19 ← pure p0
      let i20 ← Zig.callMC (Zig.ptrProject i19 (·.add 8))
      let i21 ← Zig.load (BitVec 64) 8 i20
      let i22 ← Zig.callC (mem_Allocator_alignedAlloc__anon_0b20c0554625 p1 i21)
      match i22 with
      | .error _ => (do
        let i24 ← Zig.callRC (Zig.unwrapErr i22)
        let i25 ← pure ((.error i24) : Except Zig.ErrName (Zig.Slice))
        pure (.ret i25))
      | .ok v23 => (do
        let i27 ← pure p0
        let i28 ← Zig.load (Zig.Slice) 8 i27
        let i29 ← pure v23.len
        let i30 ← pure i28.len
        let i31 ← pure (i29 == i30)
        match ← ((do
          if i31 then (do
            pure .br32)
          else (do
            throw .panic)) : Zig.CM Tgt array_list_Aligned_u32_null_toOwnedSliceLocals array_list_Aligned_u32_null_toOwnedSliceExit) with
        | .br32 => (do
          let i37 ← pure i28.ptr
          let i38 ← pure v23.ptr
          let i39 ← Zig.callMC (Zig.ptrProject i37 (·.elem 4 i29))
          let i40 ← Zig.callMC (Zig.ptrProject i38 (·.elem 4 i29))
          let i41 ← Zig.callMC (Zig.ptrLe i39 i38)
          let i42 ← Zig.callMC (Zig.ptrLe i40 i37)
          let i43 ← pure (i41 || i42)
          match ← ((do
            if i43 then (do
              pure .br44)
            else (do
              throw .panic)) : Zig.CM Tgt array_list_Aligned_u32_null_toOwnedSliceLocals array_list_Aligned_u32_null_toOwnedSliceExit) with
          | .br44 => (do
            Zig.callMC (Zig.memcpy 4 4 4 v23.ptr i37 v23.len i28.len)
            let _i50 ← Zig.callC (array_list_Aligned_u32_null_clearAndFree p0 p1)
            let i51 ← pure (v23)
            let i52 ← pure ((.ok i51) : Except Zig.ErrName (Zig.Slice))
            pure (.ret i52))
          | e => pure e)
        | e => pure e))
    | e => pure e) : Zig.CM Tgt array_list_Aligned_u32_null_toOwnedSliceLocals array_list_Aligned_u32_null_toOwnedSliceExit).run' (default : array_list_Aligned_u32_null_toOwnedSliceLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

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
          let i20 ← Zig.callC (array_list_Aligned_u32_null_append i2 p0 i15)
          match i20 with
          | .error _ => (do
            let i22 ← Zig.callRC (Zig.unwrapErr i20)
            let _i23 ← Zig.callC (array_list_Aligned_u32_null_deinit i2 p0)
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
  let s2 ← Zig.allocStack 32 8
  let e ← ((do
    let i2 ← pure (← get).list
    Zig.store (α := array_list_Aligned_u32_null) 8 i2 ({ items := (⟨(⟨some 0, 0⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice), capacity := (0 : BitVec 64), pointer_stability := ({ state := debug_SafetyLock_State__enum_1.unlocked } : debug_SafetyLock) } : array_list_Aligned_u32_null)
    modify (fun s => { s with local4 := (0 : BitVec 64) })
    let i6 ← pure p1.len
    match ← ((do
      Zig.loop (evens.loop8 p0 p1 i2 i6) evens.again8) : Zig.CM Tgt evensLocals evensExit) with
    | .br7 => (do
      let i34 ← Zig.callC (array_list_Aligned_u32_null_toOwnedSlice i2 p0)
      let i35 ← pure (Zig.isNonErr i34)
      if i35 then (do
        let i37 ← pure (i34)
        pure (.ret i37))
      else (do
        let _i39 ← Zig.callC (array_list_Aligned_u32_null_deinit i2 p0)
        let i40 ← pure (i34)
        pure (.ret i40)))
    | e => pure e) : Zig.CM Tgt evensLocals evensExit).run' { (default : evensLocals) with list := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v
  | _ => throw .panic

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

structure mem_Allocator_allocBytesAligned__anon_caf344927ceaLocals where
  deriving Inhabited

inductive mem_Allocator_allocBytesAligned__anon_caf344927ceaExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3
  | br10 (v : Option (Zig.Ptr))
  | br9 (v : Zig.Ptr)
  | br30

def mem_Allocator_allocBytesAligned__anon_caf344927cea [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (⟨none, 18446744073709551608⟩ : Zig.Ptr) : Except Zig.ErrName (Zig.Ptr))))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_caf344927ceaLocals mem_Allocator_allocBytesAligned__anon_caf344927ceaExit) with
    | .br3 => (do
      match ← ((do
        match ← ((do
          let i11 ← pure ((p0).vtable)
          let i12 ← pure i11
          let i13 ← Zig.load (Zig.Ptr) 8 i12
          let i14 ← pure ((p0).ptr)
          let i15 ← (Zig.callC (Zig.extCall (Ext.call0 i13 i14 p1 mem_Alignment.«8» p2)))
          pure (.br10 i15)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_caf344927ceaLocals mem_Allocator_allocBytesAligned__anon_caf344927ceaExit) with
        | .br10 v10 => (do
          let i17 ← pure ((v10).isSome)
          if i17 then (do
            let i19 ← Zig.optPayload v10
            pure (.br9 i19))
          else (do
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr)))))
        | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_caf344927ceaLocals mem_Allocator_allocBytesAligned__anon_caf344927ceaExit) with
      | .br9 v9 => (do
        let i22 ← pure v9
        let i23 ← Zig.sub false p1 (0 : BitVec 64) (safe := false)
        let i24 ← pure (⟨i22, i23⟩ : Zig.Slice)
        let _i25 ← pure i24.len
        Zig.callMC (Zig.memset (α := BitVec 8) 1 i24.ptr i24.len none)
        let i27 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr v9)))
        let i28 ← pure (i27 &&& (7 : BitVec 64))
        let i29 ← pure (i28 == (0 : BitVec 64))
        match ← ((do
          if i29 then (do
            pure .br30)
          else (do
            throw .panic)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_caf344927ceaLocals mem_Allocator_allocBytesAligned__anon_caf344927ceaExit) with
        | .br30 => (do
          let i35 ← Zig.callMC (Zig.checkAlign 8 v9 >>= fun _ => pure v9)
          let i36 ← pure ((.ok i35) : Except Zig.ErrName (Zig.Ptr))
          pure (.ret i36))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_caf344927ceaLocals mem_Allocator_allocBytesAligned__anon_caf344927ceaExit).run' (default : mem_Allocator_allocBytesAligned__anon_caf344927ceaLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_create__anon_48603a336c43Locals where
  local11 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_create__anon_48603a336c43Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br2 (v : Except Zig.ErrName (Zig.Ptr))

def mem_Allocator_create__anon_48603a336c43 [Ext] (p0 : mem_Allocator) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let s11 ← Zig.allocStack 16 8
  let e ← ((do
    let i1 ← Zig.callMC Zig.returnAddress
    match ← ((do
      let i3 ← Zig.callC (mem_Allocator_allocBytesAligned__anon_caf344927cea p0 (16 : BitVec 64) i1)
      match i3 with
      | .error _ => (do
        let i5 ← Zig.callRC (Zig.unwrapErr i3)
        let i6 ← pure ((.error i5) : Except Zig.ErrName (Zig.Ptr))
        pure (.br2 i6))
      | .ok v4 => (do
        let i8 ← pure (v4)
        let i9 ← pure ((.ok i8) : Except Zig.ErrName (Zig.Ptr))
        pure (.br2 i9))) : Zig.CM Tgt mem_Allocator_create__anon_48603a336c43Locals mem_Allocator_create__anon_48603a336c43Exit) with
    | .br2 v2 => (do
      let i11 ← pure (← get).local11
      (letI : Zig.Enc (Except Zig.ErrName (Zig.Ptr)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Ptr))); Zig.store (α := Except Zig.ErrName (Zig.Ptr)) 8 i11 v2)
      let i13 ← pure (i11)
      let i14 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Ptr)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Ptr))); Zig.load (Except Zig.ErrName (Zig.Ptr)) 8 i13)
      pure (.ret i14))
    | e => pure e) : Zig.CM Tgt mem_Allocator_create__anon_48603a336c43Locals mem_Allocator_create__anon_48603a336c43Exit).run' { (default : mem_Allocator_create__anon_48603a336c43Locals) with local11 := s11 }
  Zig.free s11
  match e with
  | .ret v => pure v
  | _ => throw .panic

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

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch [Ext] : Tgt → Zig.ConcM Tgt Unit :=
  fun t => nomatch t

end Lists.Open