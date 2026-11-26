-- air2lean-profile: {"allocator_model":"translated","correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.1"}}
-- air2lean-interfaces: {"ext":[{"field":"call0","type":"fn (*anyopaque, usize, mem.Alignment, usize) ?[*]u8"},{"field":"call1","type":"fn (*anyopaque, []u8, mem.Alignment, usize, usize) ?[*]u8"},{"field":"call2","type":"fn (*anyopaque, []u8, mem.Alignment, usize) void"}],"interfaces":[{"contract":"Zig.Full.CAllocSpec","interface":"std.mem.Allocator","premise":"EXT-05","struct":"mem.Allocator.VTable"}]}
import ZigLean


namespace Interfaces.Kinds

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

/-- The memory at program start under the placement `σ`: block `k` is global `k`. The words of `@returnAddress()` and of `undefined` pointers are `arbitrary` (`Mem.arbitrary`). -/
def mem0 (σ : Zig.Placement) (arbitrary : Array (BitVec 64) := #[]) : Zig.Mem := { Zig.Mem.ofGlobals σ [] with arbitrary }

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

attribute [zig_run] mem_Allocator_allocBytesAligned__anon_caf344927cea

structure mem_Allocator_allocWithSizeAndAlignment__anon_9971196370c5Locals where
  deriving Inhabited

inductive mem_Allocator_allocWithSizeAndAlignment__anon_9971196370c5Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3 (v : BitVec 64)

def mem_Allocator_allocWithSizeAndAlignment__anon_9971196370c5 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.callRC (math_mul__anon_44faaf286c79 (8 : BitVec 64) p1)
      let i5 ← pure (Zig.isNonErr i4)
      if i5 then (do
        let i7 ← Zig.callRC (Zig.unwrapPayload i4)
        pure (.br3 i7))
      else (do
        let _i9 ← Zig.callRC (Zig.unwrapErr i4)
        pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr))))) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_9971196370c5Locals mem_Allocator_allocWithSizeAndAlignment__anon_9971196370c5Exit) with
    | .br3 v3 => (do
      let i11 ← Zig.callC (mem_Allocator_allocBytesAligned__anon_caf344927cea p0 v3 p2)
      pure (.ret i11))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_9971196370c5Locals mem_Allocator_allocWithSizeAndAlignment__anon_9971196370c5Exit).run' (default : mem_Allocator_allocWithSizeAndAlignment__anon_9971196370c5Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocWithSizeAndAlignment__anon_9971196370c5

structure mem_absorbSentinel__anon_a60d7c314ff0Locals where
  deriving Inhabited

inductive mem_absorbSentinel__anon_a60d7c314ff0Exit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_a60d7c314ff0 (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret p0)) : Zig.MM mem_absorbSentinel__anon_a60d7c314ff0Locals mem_absorbSentinel__anon_a60d7c314ff0Exit).run' (default : mem_absorbSentinel__anon_a60d7c314ff0Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_absorbSentinel__anon_a60d7c314ff0

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
    let i4 ← Zig.intCast false false 6 i3
    let i5 ← Zig.enumOf (mem_Alignment.ofInt? (Zig.val false i4))
    pure (.ret i5)) : Zig.M mem_Alignment_fromByteUnitsLocals mem_Alignment_fromByteUnitsExit).run' (default : mem_Alignment_fromByteUnitsLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Alignment_fromByteUnits

structure mem_Allocator_free__anon_61cb689082faLocals where
  deriving Inhabited

inductive mem_Allocator_free__anon_61cb689082faExit where
  | ret
  | br8
  | br19

def mem_Allocator_free__anon_61cb689082fa [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_a60d7c314ff0 p1)
    let i3 ← pure i2.ptr
    let i4 ← pure i2.len
    let i5 ← Zig.mul false i4 (8 : BitVec 64) (safe := false)
    let i6 ← pure (i3)
    let i7 ← pure (⟨i6, i5⟩ : Zig.Slice)
    match ← ((do
      let i9 ← pure i7.len
      let i10 ← pure (i9)
      let i11 ← pure (i10 == (0 : BitVec 64))
      if i11 then (do
        pure .ret)
      else (do
        pure .br8)) : Zig.CM Tgt mem_Allocator_free__anon_61cb689082faLocals mem_Allocator_free__anon_61cb689082faExit) with
    | .br8 => (do
      let _i15 ← pure i7.len
      Zig.callMC (Zig.memset (α := BitVec 8) 1 i7.ptr i7.len none)
      let i17 ← Zig.callRC (mem_Alignment_fromByteUnits (8 : BitVec 64))
      let i18 ← Zig.callMC Zig.returnAddress
      match ← ((do
        let i20 ← pure ((p0).vtable)
        let i21 ← Zig.callMC (Zig.ptrProject i20 (·.add 24))
        let i22 ← Zig.load (Zig.Ptr) 8 i21
        let i23 ← pure ((p0).ptr)
        let _i24 ← (Zig.callC (Zig.extCall (Ext.call2 i22 i23 i7 i17 i18)))
        pure .br19) : Zig.CM Tgt mem_Allocator_free__anon_61cb689082faLocals mem_Allocator_free__anon_61cb689082faExit) with
      | .br19 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_61cb689082faLocals mem_Allocator_free__anon_61cb689082faExit).run' (default : mem_Allocator_free__anon_61cb689082faLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_61cb689082fa

structure mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals where
  deriving Inhabited

inductive mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br9 (v : Except Zig.ErrName (Zig.Slice))
  | br4
  | br23
  | br36 (v : BitVec 64)
  | br46 (v : Option (Zig.Ptr))
  | br66
  | br73
  | br44
  | br86 (v : Option (Zig.Ptr))
  | br84 (v : Zig.Ptr)
  | br112
  | br121
  | br133
  | br142
  | br159
  | br166

def mem_Allocator_reallocAdvanced__anon_c61a2607b47f [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) (p3 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    match ← ((do
      let i5 ← pure p1.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        match ← ((do
          let i10 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_9971196370c5 p0 p2 p3)
          match i10 with
          | .error _ => (do
            let i12 ← Zig.callRC (Zig.unwrapErr i10)
            let i13 ← pure ((.error i12) : Except Zig.ErrName (Zig.Slice))
            pure (.br9 i13))
          | .ok v11 => (do
            let i15 ← pure (v11)
            let i16 ← pure i15
            let i17 ← Zig.sub false p2 (0 : BitVec 64) (safe := false)
            let i18 ← pure (⟨i16, i17⟩ : Zig.Slice)
            let i19 ← pure ((.ok i18) : Except Zig.ErrName (Zig.Slice))
            pure (.br9 i19))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit) with
        | .br9 v9 => (do
          pure (.ret v9))
        | e => pure e)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit) with
    | .br4 => (do
      match ← ((do
        let i24 ← pure (p2)
        let i25 ← pure (i24 == (0 : BitVec 64))
        if i25 then (do
          let _i27 ← Zig.callC (mem_Allocator_free__anon_61cb689082fa p0 p1)
          pure (.ret (.ok (⟨(⟨none, 18446744073709551608⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice) : Except Zig.ErrName (Zig.Slice))))
        else (do
          pure .br23)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit) with
      | .br23 => (do
        let i30 ← Zig.callMC (mem_absorbSentinel__anon_a60d7c314ff0 p1)
        let i31 ← pure i30.ptr
        let i32 ← pure i30.len
        let i33 ← Zig.mul false i32 (8 : BitVec 64) (safe := false)
        let i34 ← pure (i31)
        let i35 ← pure (⟨i34, i33⟩ : Zig.Slice)
        match ← ((do
          let i37 ← Zig.callRC (math_mul__anon_44faaf286c79 (8 : BitVec 64) p2)
          let i38 ← pure (Zig.isNonErr i37)
          if i38 then (do
            let i40 ← Zig.callRC (Zig.unwrapPayload i37)
            pure (.br36 i40))
          else (do
            let _i42 ← Zig.callRC (Zig.unwrapErr i37)
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice))))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit) with
        | .br36 v36 => (do
          match ← ((do
            let i45 ← Zig.callRC (mem_Alignment_fromByteUnits (8 : BitVec 64))
            match ← ((do
              let i47 ← pure ((p0).vtable)
              let i48 ← Zig.callMC (Zig.ptrProject i47 (·.add 16))
              let i49 ← Zig.load (Zig.Ptr) 8 i48
              let i50 ← pure ((p0).ptr)
              let i51 ← (Zig.callC (Zig.extCall (Ext.call1 i49 i50 i35 i45 v36 p3)))
              pure (.br46 i51)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit) with
            | .br46 v46 => (do
              let i53 ← pure ((v46).isSome)
              if i53 then (do
                let i55 ← Zig.optPayload v46
                let i56 ← pure i55
                let i57 ← Zig.sub false v36 (0 : BitVec 64) (safe := false)
                let i58 ← pure (⟨i56, i57⟩ : Zig.Slice)
                let i59 ← pure i58.ptr
                let i60 ← pure i58.len
                let i61 ← pure (i60 == (0 : BitVec 64))
                let i62 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i59)))
                let i63 ← pure (i62 &&& (7 : BitVec 64))
                let i64 ← pure (i63 == (0 : BitVec 64))
                let i65 ← pure (i61 || i64)
                match ← ((do
                  if i65 then (do
                    pure .br66)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit) with
                | .br66 => (do
                  let i71 ← Zig.rem false i60 (8 : BitVec 64)
                  let i72 ← pure (i71 == (0 : BitVec 64))
                  match ← ((do
                    if i72 then (do
                      pure .br73)
                    else (do
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit) with
                  | .br73 => (do
                    let i78 ← Zig.divExact false i60 (8 : BitVec 64)
                    let i79 ← Zig.callMC (Zig.checkAlign 8 i59 >>= fun _ => pure i59)
                    let i80 ← pure (⟨i79, i78⟩ : Zig.Slice)
                    let i81 ← pure ((.ok i80) : Except Zig.ErrName (Zig.Slice))
                    pure (.ret i81))
                  | e => pure e)
                | e => pure e)
              else (do
                pure .br44))
            | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit) with
          | .br44 => (do
            match ← ((do
              let i85 ← Zig.callRC (mem_Alignment_fromByteUnits (8 : BitVec 64))
              match ← ((do
                let i87 ← pure ((p0).vtable)
                let i88 ← pure i87
                let i89 ← Zig.load (Zig.Ptr) 8 i88
                let i90 ← pure ((p0).ptr)
                let i91 ← (Zig.callC (Zig.extCall (Ext.call0 i89 i90 v36 i85 p3)))
                pure (.br86 i91)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit) with
              | .br86 v86 => (do
                let i93 ← pure ((v86).isSome)
                if i93 then (do
                  let i95 ← Zig.optPayload v86
                  pure (.br84 i95))
                else (do
                  pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice)))))
              | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit) with
            | .br84 v84 => (do
              let i98 ← pure i35.len
              let i99 ← pure (v36)
              let i100 ← pure (i98)
              let i101 ← pure (Zig.min false i99 i100)
              let i102 ← pure v84
              let i103 ← pure (i101)
              let i104 ← Zig.sub false i103 (0 : BitVec 64) (safe := false)
              let i105 ← pure (⟨i102, i104⟩ : Zig.Slice)
              let i106 ← pure i35.ptr
              let i107 ← pure i106
              let i108 ← pure (i101)
              let i109 ← Zig.sub false i108 (0 : BitVec 64) (safe := false)
              let i110 ← pure i35.len
              let i111 ← pure (Zig.le false i108 i110)
              match ← ((do
                if i111 then (do
                  pure .br112)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit) with
              | .br112 => (do
                let i117 ← Zig.callMC (Zig.checkSliceEnd i35.len (0 : BitVec 64) i109 0 >>= fun _ => pure (⟨i107, i109⟩ : Zig.Slice))
                let i118 ← pure i105.len
                let i119 ← pure i117.len
                let i120 ← pure (i118 == i119)
                match ← ((do
                  if i120 then (do
                    pure .br121)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit) with
                | .br121 => (do
                  let i126 ← pure i117.ptr
                  let i127 ← pure i105.ptr
                  let i128 ← Zig.callMC (Zig.ptrProject i126 (·.elem 1 i118))
                  let i129 ← Zig.callMC (Zig.ptrProject i127 (·.elem 1 i118))
                  let i130 ← Zig.callMC (Zig.ptrLe i128 i127)
                  let i131 ← Zig.callMC (Zig.ptrLe i129 i126)
                  let i132 ← pure (i130 || i131)
                  match ← ((do
                    if i132 then (do
                      pure .br133)
                    else (do
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit) with
                  | .br133 => (do
                    Zig.callMC (Zig.memcpy 1 1 1 i105.ptr i126 i105.len i117.len)
                    let _i139 ← pure i35.len
                    Zig.callMC (Zig.memset (α := BitVec 8) 1 i35.ptr i35.len none)
                    let i141 ← Zig.callRC (mem_Alignment_fromByteUnits (8 : BitVec 64))
                    match ← ((do
                      let i143 ← pure ((p0).vtable)
                      let i144 ← Zig.callMC (Zig.ptrProject i143 (·.add 24))
                      let i145 ← Zig.load (Zig.Ptr) 8 i144
                      let i146 ← pure ((p0).ptr)
                      let _i147 ← (Zig.callC (Zig.extCall (Ext.call2 i145 i146 i35 i141 p3)))
                      pure .br142) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit) with
                    | .br142 => (do
                      let i149 ← pure v84
                      let i150 ← Zig.sub false v36 (0 : BitVec 64) (safe := false)
                      let i151 ← pure (⟨i149, i150⟩ : Zig.Slice)
                      let i152 ← pure i151.ptr
                      let i153 ← pure i151.len
                      let i154 ← pure (i153 == (0 : BitVec 64))
                      let i155 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i152)))
                      let i156 ← pure (i155 &&& (7 : BitVec 64))
                      let i157 ← pure (i156 == (0 : BitVec 64))
                      let i158 ← pure (i154 || i157)
                      match ← ((do
                        if i158 then (do
                          pure .br159)
                        else (do
                          throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit) with
                      | .br159 => (do
                        let i164 ← Zig.rem false i153 (8 : BitVec 64)
                        let i165 ← pure (i164 == (0 : BitVec 64))
                        match ← ((do
                          if i165 then (do
                            pure .br166)
                          else (do
                            throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit) with
                        | .br166 => (do
                          let i171 ← Zig.divExact false i153 (8 : BitVec 64)
                          let i172 ← Zig.callMC (Zig.checkAlign 8 i152 >>= fun _ => pure i152)
                          let i173 ← pure (⟨i172, i171⟩ : Zig.Slice)
                          let i174 ← pure ((.ok i173) : Except Zig.ErrName (Zig.Slice))
                          pure (.ret i174))
                        | e => pure e)
                      | e => pure e)
                    | e => pure e)
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals mem_Allocator_reallocAdvanced__anon_c61a2607b47fExit).run' (default : mem_Allocator_reallocAdvanced__anon_c61a2607b47fLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_reallocAdvanced__anon_c61a2607b47f

structure mem_Allocator_realloc__anon_f17c619ddbc3Locals where
  deriving Inhabited

inductive mem_Allocator_realloc__anon_f17c619ddbc3Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_realloc__anon_f17c619ddbc3 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.callMC Zig.returnAddress
    let i4 ← Zig.callC (mem_Allocator_reallocAdvanced__anon_c61a2607b47f p0 p1 p2 i3)
    pure (.ret i4)) : Zig.CM Tgt mem_Allocator_realloc__anon_f17c619ddbc3Locals mem_Allocator_realloc__anon_f17c619ddbc3Exit).run' (default : mem_Allocator_realloc__anon_f17c619ddbc3Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_realloc__anon_f17c619ddbc3

structure Buf___u8_8_null_appendLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive Buf___u8_8_null_appendExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br27
  | br39
  | br55
  | br63

def Buf___u8_8_null_append [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : Option (Zig.Ptr)) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    modify (fun s => { s with local3 := p1 })
    let i8 ← pure (((← get).local3).len)
    let i9 ← Zig.add false i8 (1 : BitVec 64)
    let i10 ← pure (((← get).local3).ptr)
    let i11 ← pure i10
    let i12 ← Zig.sub false i9 (0 : BitVec 64) (safe := false)
    let i13 ← pure (⟨i11, i12⟩ : Zig.Slice)
    let i15 ← pure (((← get).local3).len)
    let i16 ← Zig.add false i15 (2 : BitVec 64)
    let i17 ← Zig.callC (mem_Allocator_realloc__anon_f17c619ddbc3 p0 i13 i16)
    match i17 with
    | .error _ => (do
      let i19 ← Zig.callRC (Zig.unwrapErr i17)
      let i20 ← pure (i19)
      let i21 ← pure ((.error i20) : Except Zig.ErrName (Zig.Slice))
      pure (.ret i21))
    | .ok v18 => (do
      let i24 ← pure (((← get).local3).len)
      let i25 ← pure v18.len
      let i26 ← pure (Zig.lt false i24 i25)
      match ← ((do
        if i26 then (do
          pure .br27)
        else (do
          throw .outOfBounds)) : Zig.CM Tgt Buf___u8_8_null_appendLocals Buf___u8_8_null_appendExit) with
      | .br27 => (do
        let i32 ← Zig.callMC (Zig.checkIndex v18.len i24) >>= fun _ => Zig.callMC (Zig.ptrProject v18.ptr (·.elem 8 i24))
        Zig.store (α := Option (Zig.Ptr)) 8 i32 p2
        let i35 ← pure (((← get).local3).len)
        let i36 ← Zig.add false i35 (1 : BitVec 64)
        let i37 ← pure v18.len
        let i38 ← pure (Zig.lt false i36 i37)
        match ← ((do
          if i38 then (do
            pure .br39)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt Buf___u8_8_null_appendLocals Buf___u8_8_null_appendExit) with
        | .br39 => (do
          let i44 ← Zig.callMC (Zig.checkIndex v18.len i36) >>= fun _ => Zig.callMC (Zig.ptrProject v18.ptr (·.elem 8 i36))
          Zig.store (α := Option (Zig.Ptr)) 8 i44 none
          let i47 ← pure (((← get).local3).len)
          let i48 ← Zig.add false i47 (1 : BitVec 64)
          let i49 ← pure v18.ptr
          let i50 ← pure i49
          let i51 ← Zig.sub false i48 (0 : BitVec 64) (safe := false)
          let i52 ← pure v18.len
          let i53 ← Zig.add false i48 (1 : BitVec 64)
          let i54 ← pure (Zig.le false i53 i52)
          match ← ((do
            if i54 then (do
              pure .br55)
            else (do
              throw .outOfBounds)) : Zig.CM Tgt Buf___u8_8_null_appendLocals Buf___u8_8_null_appendExit) with
          | .br55 => (do
            let i60 ← Zig.callMC (Zig.checkSliceEnd v18.len (0 : BitVec 64) i51 1 >>= fun _ => pure (⟨i50, i51⟩ : Zig.Slice))
            let i61 ← Zig.callMC (Zig.checkSentinelIndex i60.len i51 >>= fun _ => Zig.load (Option (Zig.Ptr)) 8 (i60.ptr.elem 8 i51))
            let i62 ← Zig.callMC (Zig.optPtrEqAddr none i61)
            match ← ((do
              if i62 then (do
                pure .br63)
              else (do
                throw .panic)) : Zig.CM Tgt Buf___u8_8_null_appendLocals Buf___u8_8_null_appendExit) with
            | .br63 => (do
              let i68 ← pure ((.ok i60) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i68))
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf___u8_8_null_appendLocals Buf___u8_8_null_appendExit).run' (default : Buf___u8_8_null_appendLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf___u8_8_null_append

structure mem_Allocator_allocWithOptionsRetAddr__anon_c43d30dd137eLocals where
  deriving Inhabited

inductive mem_Allocator_allocWithOptionsRetAddr__anon_c43d30dd137eExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br4 (v : Except Zig.ErrName (Zig.Slice))
  | br22
  | br35
  | br43

def mem_Allocator_allocWithOptionsRetAddr__anon_c43d30dd137e [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.add false p1 (1 : BitVec 64)
    match ← ((do
      let i5 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_9971196370c5 p0 i3 p2)
      match i5 with
      | .error _ => (do
        let i7 ← Zig.callRC (Zig.unwrapErr i5)
        let i8 ← pure ((.error i7) : Except Zig.ErrName (Zig.Slice))
        pure (.br4 i8))
      | .ok v6 => (do
        let i10 ← pure (v6)
        let i11 ← pure i10
        let i12 ← Zig.sub false i3 (0 : BitVec 64) (safe := false)
        let i13 ← pure (⟨i11, i12⟩ : Zig.Slice)
        let i14 ← pure ((.ok i13) : Except Zig.ErrName (Zig.Slice))
        pure (.br4 i14))) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_c43d30dd137eLocals mem_Allocator_allocWithOptionsRetAddr__anon_c43d30dd137eExit) with
    | .br4 v4 => (do
      match v4 with
      | .error _ => (do
        let i17 ← Zig.callRC (Zig.unwrapErr v4)
        let i18 ← pure ((.error i17) : Except Zig.ErrName (Zig.Slice))
        pure (.ret i18))
      | .ok v16 => (do
        let i20 ← pure v16.len
        let i21 ← pure (Zig.lt false p1 i20)
        match ← ((do
          if i21 then (do
            pure .br22)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_c43d30dd137eLocals mem_Allocator_allocWithOptionsRetAddr__anon_c43d30dd137eExit) with
        | .br22 => (do
          let i27 ← Zig.callMC (Zig.checkIndex v16.len p1) >>= fun _ => Zig.callMC (Zig.ptrProject v16.ptr (·.elem 8 p1))
          Zig.store (α := Option (Zig.Ptr)) 8 i27 none
          let i29 ← pure v16.ptr
          let i30 ← pure i29
          let i31 ← Zig.sub false p1 (0 : BitVec 64) (safe := false)
          let i32 ← pure v16.len
          let i33 ← Zig.add false p1 (1 : BitVec 64)
          let i34 ← pure (Zig.le false i33 i32)
          match ← ((do
            if i34 then (do
              pure .br35)
            else (do
              throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_c43d30dd137eLocals mem_Allocator_allocWithOptionsRetAddr__anon_c43d30dd137eExit) with
          | .br35 => (do
            let i40 ← Zig.callMC (Zig.checkSliceEnd v16.len (0 : BitVec 64) i31 1 >>= fun _ => pure (⟨i30, i31⟩ : Zig.Slice))
            let i41 ← Zig.callMC (Zig.checkSentinelIndex i40.len i31 >>= fun _ => Zig.load (Option (Zig.Ptr)) 8 (i40.ptr.elem 8 i31))
            let i42 ← Zig.callMC (Zig.optPtrEqAddr none i41)
            match ← ((do
              if i42 then (do
                pure .br43)
              else (do
                throw .panic)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_c43d30dd137eLocals mem_Allocator_allocWithOptionsRetAddr__anon_c43d30dd137eExit) with
            | .br43 => (do
              let i48 ← pure ((.ok i40) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i48))
            | e => pure e)
          | e => pure e)
        | e => pure e))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_c43d30dd137eLocals mem_Allocator_allocWithOptionsRetAddr__anon_c43d30dd137eExit).run' (default : mem_Allocator_allocWithOptionsRetAddr__anon_c43d30dd137eLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocWithOptionsRetAddr__anon_c43d30dd137e

structure mem_Allocator_allocSentinel__anon_131423843e79Locals where
  local4 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_allocSentinel__anon_131423843e79Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_allocSentinel__anon_131423843e79 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s4 ← Zig.allocStack 24 8
  let e ← ((do
    let i2 ← Zig.callMC Zig.returnAddress
    let i3 ← Zig.callC (mem_Allocator_allocWithOptionsRetAddr__anon_c43d30dd137e p0 p1 i2)
    let i4 ← pure (← get).local4
    (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i4 i3)
    let i6 ← pure (i4)
    let i7 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i6)
    pure (.ret i7)) : Zig.CM Tgt mem_Allocator_allocSentinel__anon_131423843e79Locals mem_Allocator_allocSentinel__anon_131423843e79Exit).run' { (default : mem_Allocator_allocSentinel__anon_131423843e79Locals) with local4 := s4 }
  Zig.free s4
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_allocSentinel__anon_131423843e79

structure Buf___u8_8_null_makeLocals where
  local3 : Zig.Ptr
  deriving Inhabited

inductive Buf___u8_8_null_makeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def Buf___u8_8_null_make [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s3 ← Zig.allocStack 24 8
  let e ← ((do
    let i2 ← Zig.callC (mem_Allocator_allocSentinel__anon_131423843e79 p0 p1)
    let i3 ← pure (← get).local3
    (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i3 i2)
    let i5 ← pure (i3)
    let i6 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i5)
    pure (.ret i6)) : Zig.CM Tgt Buf___u8_8_null_makeLocals Buf___u8_8_null_makeExit).run' { (default : Buf___u8_8_null_makeLocals) with local3 := s3 }
  Zig.free s3
  match e with
  | .ret v => pure v

attribute [zig_run] Buf___u8_8_null_make

structure mem_absorbSentinel__anon_4502a2daf4b9Locals where
  local1 : Zig.Slice
  deriving Inhabited

inductive mem_absorbSentinel__anon_4502a2daf4b9Exit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_4502a2daf4b9 (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    modify (fun s => { s with local1 := p0 })
    let i6 ← pure (((← get).local1).len)
    let i7 ← Zig.add false i6 (1 : BitVec 64)
    let i8 ← pure (((← get).local1).ptr)
    let i9 ← pure i8
    let i10 ← Zig.sub false i7 (0 : BitVec 64) (safe := false)
    let i11 ← pure (⟨i9, i10⟩ : Zig.Slice)
    pure (.ret i11)) : Zig.MM mem_absorbSentinel__anon_4502a2daf4b9Locals mem_absorbSentinel__anon_4502a2daf4b9Exit).run' (default : mem_absorbSentinel__anon_4502a2daf4b9Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_absorbSentinel__anon_4502a2daf4b9

structure mem_Allocator_free__anon_030fe58d1647Locals where
  deriving Inhabited

inductive mem_Allocator_free__anon_030fe58d1647Exit where
  | ret
  | br8
  | br19

def mem_Allocator_free__anon_030fe58d1647 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_4502a2daf4b9 p1)
    let i3 ← pure i2.ptr
    let i4 ← pure i2.len
    let i5 ← Zig.mul false i4 (8 : BitVec 64) (safe := false)
    let i6 ← pure (i3)
    let i7 ← pure (⟨i6, i5⟩ : Zig.Slice)
    match ← ((do
      let i9 ← pure i7.len
      let i10 ← pure (i9)
      let i11 ← pure (i10 == (0 : BitVec 64))
      if i11 then (do
        pure .ret)
      else (do
        pure .br8)) : Zig.CM Tgt mem_Allocator_free__anon_030fe58d1647Locals mem_Allocator_free__anon_030fe58d1647Exit) with
    | .br8 => (do
      let _i15 ← pure i7.len
      Zig.callMC (Zig.memset (α := BitVec 8) 1 i7.ptr i7.len none)
      let i17 ← Zig.callRC (mem_Alignment_fromByteUnits (8 : BitVec 64))
      let i18 ← Zig.callMC Zig.returnAddress
      match ← ((do
        let i20 ← pure ((p0).vtable)
        let i21 ← Zig.callMC (Zig.ptrProject i20 (·.add 24))
        let i22 ← Zig.load (Zig.Ptr) 8 i21
        let i23 ← pure ((p0).ptr)
        let _i24 ← (Zig.callC (Zig.extCall (Ext.call2 i22 i23 i7 i17 i18)))
        pure .br19) : Zig.CM Tgt mem_Allocator_free__anon_030fe58d1647Locals mem_Allocator_free__anon_030fe58d1647Exit) with
      | .br19 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_030fe58d1647Locals mem_Allocator_free__anon_030fe58d1647Exit).run' (default : mem_Allocator_free__anon_030fe58d1647Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_030fe58d1647

structure Buf___u8_8_null_releaseLocals where
  deriving Inhabited

inductive Buf___u8_8_null_releaseExit where
  | ret

def Buf___u8_8_null_release [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let _i2 ← Zig.callC (mem_Allocator_free__anon_030fe58d1647 p0 p1)
    pure .ret) : Zig.CM Tgt Buf___u8_8_null_releaseLocals Buf___u8_8_null_releaseExit).run' (default : Buf___u8_8_null_releaseLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Buf___u8_8_null_release

structure Buf___u8_8_null_resizeLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive Buf___u8_8_null_resizeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br23
  | br36
  | br44

def Buf___u8_8_null_resize [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    modify (fun s => { s with local3 := p1 })
    let i8 ← pure (((← get).local3).len)
    let i9 ← Zig.add false i8 (1 : BitVec 64)
    let i10 ← pure (((← get).local3).ptr)
    let i11 ← pure i10
    let i12 ← Zig.sub false i9 (0 : BitVec 64) (safe := false)
    let i13 ← pure (⟨i11, i12⟩ : Zig.Slice)
    let i14 ← Zig.add false p2 (1 : BitVec 64)
    let i15 ← Zig.callC (mem_Allocator_realloc__anon_f17c619ddbc3 p0 i13 i14)
    match i15 with
    | .error _ => (do
      let i17 ← Zig.callRC (Zig.unwrapErr i15)
      let i18 ← pure (i17)
      let i19 ← pure ((.error i18) : Except Zig.ErrName (Zig.Slice))
      pure (.ret i19))
    | .ok v16 => (do
      let i21 ← pure v16.len
      let i22 ← pure (Zig.lt false p2 i21)
      match ← ((do
        if i22 then (do
          pure .br23)
        else (do
          throw .outOfBounds)) : Zig.CM Tgt Buf___u8_8_null_resizeLocals Buf___u8_8_null_resizeExit) with
      | .br23 => (do
        let i28 ← Zig.callMC (Zig.checkIndex v16.len p2) >>= fun _ => Zig.callMC (Zig.ptrProject v16.ptr (·.elem 8 p2))
        Zig.store (α := Option (Zig.Ptr)) 8 i28 none
        let i30 ← pure v16.ptr
        let i31 ← pure i30
        let i32 ← Zig.sub false p2 (0 : BitVec 64) (safe := false)
        let i33 ← pure v16.len
        let i34 ← Zig.add false p2 (1 : BitVec 64)
        let i35 ← pure (Zig.le false i34 i33)
        match ← ((do
          if i35 then (do
            pure .br36)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt Buf___u8_8_null_resizeLocals Buf___u8_8_null_resizeExit) with
        | .br36 => (do
          let i41 ← Zig.callMC (Zig.checkSliceEnd v16.len (0 : BitVec 64) i32 1 >>= fun _ => pure (⟨i31, i32⟩ : Zig.Slice))
          let i42 ← Zig.callMC (Zig.checkSentinelIndex i41.len i32 >>= fun _ => Zig.load (Option (Zig.Ptr)) 8 (i41.ptr.elem 8 i32))
          let i43 ← Zig.callMC (Zig.optPtrEqAddr none i42)
          match ← ((do
            if i43 then (do
              pure .br44)
            else (do
              throw .panic)) : Zig.CM Tgt Buf___u8_8_null_resizeLocals Buf___u8_8_null_resizeExit) with
          | .br44 => (do
            let i49 ← pure ((.ok i41) : Except Zig.ErrName (Zig.Slice))
            pure (.ret i49))
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf___u8_8_null_resizeLocals Buf___u8_8_null_resizeExit).run' (default : Buf___u8_8_null_resizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf___u8_8_null_resize

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

attribute [zig_run] mem_Allocator_allocBytesAligned__anon_c9141768de1a

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

attribute [zig_run] mem_Allocator_allocWithSizeAndAlignment__anon_7f4b76fbd810

structure mem_absorbSentinel__anon_5bbe05701efeLocals where
  deriving Inhabited

inductive mem_absorbSentinel__anon_5bbe05701efeExit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_5bbe05701efe (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret p0)) : Zig.MM mem_absorbSentinel__anon_5bbe05701efeLocals mem_absorbSentinel__anon_5bbe05701efeExit).run' (default : mem_absorbSentinel__anon_5bbe05701efeLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_absorbSentinel__anon_5bbe05701efe

structure mem_Allocator_free__anon_1a7ab5e46014Locals where
  deriving Inhabited

inductive mem_Allocator_free__anon_1a7ab5e46014Exit where
  | ret
  | br8
  | br19

def mem_Allocator_free__anon_1a7ab5e46014 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_5bbe05701efe p1)
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
        pure .br8)) : Zig.CM Tgt mem_Allocator_free__anon_1a7ab5e46014Locals mem_Allocator_free__anon_1a7ab5e46014Exit) with
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
        pure .br19) : Zig.CM Tgt mem_Allocator_free__anon_1a7ab5e46014Locals mem_Allocator_free__anon_1a7ab5e46014Exit) with
      | .br19 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_1a7ab5e46014Locals mem_Allocator_free__anon_1a7ab5e46014Exit).run' (default : mem_Allocator_free__anon_1a7ab5e46014Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_1a7ab5e46014

structure mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals where
  deriving Inhabited

inductive mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br9 (v : Except Zig.ErrName (Zig.Slice))
  | br4
  | br23
  | br36 (v : BitVec 64)
  | br46 (v : Option (Zig.Ptr))
  | br66
  | br73
  | br44
  | br86 (v : Option (Zig.Ptr))
  | br84 (v : Zig.Ptr)
  | br112
  | br121
  | br133
  | br142
  | br159
  | br166

def mem_Allocator_reallocAdvanced__anon_928a37eaea4c [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) (p3 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    match ← ((do
      let i5 ← pure p1.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        match ← ((do
          let i10 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_7f4b76fbd810 p0 p2 p3)
          match i10 with
          | .error _ => (do
            let i12 ← Zig.callRC (Zig.unwrapErr i10)
            let i13 ← pure ((.error i12) : Except Zig.ErrName (Zig.Slice))
            pure (.br9 i13))
          | .ok v11 => (do
            let i15 ← pure (v11)
            let i16 ← pure i15
            let i17 ← Zig.sub false p2 (0 : BitVec 64) (safe := false)
            let i18 ← pure (⟨i16, i17⟩ : Zig.Slice)
            let i19 ← pure ((.ok i18) : Except Zig.ErrName (Zig.Slice))
            pure (.br9 i19))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit) with
        | .br9 v9 => (do
          pure (.ret v9))
        | e => pure e)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit) with
    | .br4 => (do
      match ← ((do
        let i24 ← pure (p2)
        let i25 ← pure (i24 == (0 : BitVec 64))
        if i25 then (do
          let _i27 ← Zig.callC (mem_Allocator_free__anon_1a7ab5e46014 p0 p1)
          pure (.ret (.ok (⟨(⟨none, 18446744073709551612⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice) : Except Zig.ErrName (Zig.Slice))))
        else (do
          pure .br23)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit) with
      | .br23 => (do
        let i30 ← Zig.callMC (mem_absorbSentinel__anon_5bbe05701efe p1)
        let i31 ← pure i30.ptr
        let i32 ← pure i30.len
        let i33 ← Zig.mul false i32 (4 : BitVec 64) (safe := false)
        let i34 ← pure (i31)
        let i35 ← pure (⟨i34, i33⟩ : Zig.Slice)
        match ← ((do
          let i37 ← Zig.callRC (math_mul__anon_44faaf286c79 (4 : BitVec 64) p2)
          let i38 ← pure (Zig.isNonErr i37)
          if i38 then (do
            let i40 ← Zig.callRC (Zig.unwrapPayload i37)
            pure (.br36 i40))
          else (do
            let _i42 ← Zig.callRC (Zig.unwrapErr i37)
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice))))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit) with
        | .br36 v36 => (do
          match ← ((do
            let i45 ← Zig.callRC (mem_Alignment_fromByteUnits (4 : BitVec 64))
            match ← ((do
              let i47 ← pure ((p0).vtable)
              let i48 ← Zig.callMC (Zig.ptrProject i47 (·.add 16))
              let i49 ← Zig.load (Zig.Ptr) 8 i48
              let i50 ← pure ((p0).ptr)
              let i51 ← (Zig.callC (Zig.extCall (Ext.call1 i49 i50 i35 i45 v36 p3)))
              pure (.br46 i51)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit) with
            | .br46 v46 => (do
              let i53 ← pure ((v46).isSome)
              if i53 then (do
                let i55 ← Zig.optPayload v46
                let i56 ← pure i55
                let i57 ← Zig.sub false v36 (0 : BitVec 64) (safe := false)
                let i58 ← pure (⟨i56, i57⟩ : Zig.Slice)
                let i59 ← pure i58.ptr
                let i60 ← pure i58.len
                let i61 ← pure (i60 == (0 : BitVec 64))
                let i62 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i59)))
                let i63 ← pure (i62 &&& (3 : BitVec 64))
                let i64 ← pure (i63 == (0 : BitVec 64))
                let i65 ← pure (i61 || i64)
                match ← ((do
                  if i65 then (do
                    pure .br66)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit) with
                | .br66 => (do
                  let i71 ← Zig.rem false i60 (4 : BitVec 64)
                  let i72 ← pure (i71 == (0 : BitVec 64))
                  match ← ((do
                    if i72 then (do
                      pure .br73)
                    else (do
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit) with
                  | .br73 => (do
                    let i78 ← Zig.divExact false i60 (4 : BitVec 64)
                    let i79 ← Zig.callMC (Zig.checkAlign 4 i59 >>= fun _ => pure i59)
                    let i80 ← pure (⟨i79, i78⟩ : Zig.Slice)
                    let i81 ← pure ((.ok i80) : Except Zig.ErrName (Zig.Slice))
                    pure (.ret i81))
                  | e => pure e)
                | e => pure e)
              else (do
                pure .br44))
            | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit) with
          | .br44 => (do
            match ← ((do
              let i85 ← Zig.callRC (mem_Alignment_fromByteUnits (4 : BitVec 64))
              match ← ((do
                let i87 ← pure ((p0).vtable)
                let i88 ← pure i87
                let i89 ← Zig.load (Zig.Ptr) 8 i88
                let i90 ← pure ((p0).ptr)
                let i91 ← (Zig.callC (Zig.extCall (Ext.call0 i89 i90 v36 i85 p3)))
                pure (.br86 i91)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit) with
              | .br86 v86 => (do
                let i93 ← pure ((v86).isSome)
                if i93 then (do
                  let i95 ← Zig.optPayload v86
                  pure (.br84 i95))
                else (do
                  pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice)))))
              | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit) with
            | .br84 v84 => (do
              let i98 ← pure i35.len
              let i99 ← pure (v36)
              let i100 ← pure (i98)
              let i101 ← pure (Zig.min false i99 i100)
              let i102 ← pure v84
              let i103 ← pure (i101)
              let i104 ← Zig.sub false i103 (0 : BitVec 64) (safe := false)
              let i105 ← pure (⟨i102, i104⟩ : Zig.Slice)
              let i106 ← pure i35.ptr
              let i107 ← pure i106
              let i108 ← pure (i101)
              let i109 ← Zig.sub false i108 (0 : BitVec 64) (safe := false)
              let i110 ← pure i35.len
              let i111 ← pure (Zig.le false i108 i110)
              match ← ((do
                if i111 then (do
                  pure .br112)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit) with
              | .br112 => (do
                let i117 ← Zig.callMC (Zig.checkSliceEnd i35.len (0 : BitVec 64) i109 0 >>= fun _ => pure (⟨i107, i109⟩ : Zig.Slice))
                let i118 ← pure i105.len
                let i119 ← pure i117.len
                let i120 ← pure (i118 == i119)
                match ← ((do
                  if i120 then (do
                    pure .br121)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit) with
                | .br121 => (do
                  let i126 ← pure i117.ptr
                  let i127 ← pure i105.ptr
                  let i128 ← Zig.callMC (Zig.ptrProject i126 (·.elem 1 i118))
                  let i129 ← Zig.callMC (Zig.ptrProject i127 (·.elem 1 i118))
                  let i130 ← Zig.callMC (Zig.ptrLe i128 i127)
                  let i131 ← Zig.callMC (Zig.ptrLe i129 i126)
                  let i132 ← pure (i130 || i131)
                  match ← ((do
                    if i132 then (do
                      pure .br133)
                    else (do
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit) with
                  | .br133 => (do
                    Zig.callMC (Zig.memcpy 1 1 1 i105.ptr i126 i105.len i117.len)
                    let _i139 ← pure i35.len
                    Zig.callMC (Zig.memset (α := BitVec 8) 1 i35.ptr i35.len none)
                    let i141 ← Zig.callRC (mem_Alignment_fromByteUnits (4 : BitVec 64))
                    match ← ((do
                      let i143 ← pure ((p0).vtable)
                      let i144 ← Zig.callMC (Zig.ptrProject i143 (·.add 24))
                      let i145 ← Zig.load (Zig.Ptr) 8 i144
                      let i146 ← pure ((p0).ptr)
                      let _i147 ← (Zig.callC (Zig.extCall (Ext.call2 i145 i146 i35 i141 p3)))
                      pure .br142) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit) with
                    | .br142 => (do
                      let i149 ← pure v84
                      let i150 ← Zig.sub false v36 (0 : BitVec 64) (safe := false)
                      let i151 ← pure (⟨i149, i150⟩ : Zig.Slice)
                      let i152 ← pure i151.ptr
                      let i153 ← pure i151.len
                      let i154 ← pure (i153 == (0 : BitVec 64))
                      let i155 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i152)))
                      let i156 ← pure (i155 &&& (3 : BitVec 64))
                      let i157 ← pure (i156 == (0 : BitVec 64))
                      let i158 ← pure (i154 || i157)
                      match ← ((do
                        if i158 then (do
                          pure .br159)
                        else (do
                          throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit) with
                      | .br159 => (do
                        let i164 ← Zig.rem false i153 (4 : BitVec 64)
                        let i165 ← pure (i164 == (0 : BitVec 64))
                        match ← ((do
                          if i165 then (do
                            pure .br166)
                          else (do
                            throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit) with
                        | .br166 => (do
                          let i171 ← Zig.divExact false i153 (4 : BitVec 64)
                          let i172 ← Zig.callMC (Zig.checkAlign 4 i152 >>= fun _ => pure i152)
                          let i173 ← pure (⟨i172, i171⟩ : Zig.Slice)
                          let i174 ← pure ((.ok i173) : Except Zig.ErrName (Zig.Slice))
                          pure (.ret i174))
                        | e => pure e)
                      | e => pure e)
                    | e => pure e)
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals mem_Allocator_reallocAdvanced__anon_928a37eaea4cExit).run' (default : mem_Allocator_reallocAdvanced__anon_928a37eaea4cLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_reallocAdvanced__anon_928a37eaea4c

structure mem_Allocator_realloc__anon_49e4e5fd8358Locals where
  deriving Inhabited

inductive mem_Allocator_realloc__anon_49e4e5fd8358Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_realloc__anon_49e4e5fd8358 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.callMC Zig.returnAddress
    let i4 ← Zig.callC (mem_Allocator_reallocAdvanced__anon_928a37eaea4c p0 p1 p2 i3)
    pure (.ret i4)) : Zig.CM Tgt mem_Allocator_realloc__anon_49e4e5fd8358Locals mem_Allocator_realloc__anon_49e4e5fd8358Exit).run' (default : mem_Allocator_realloc__anon_49e4e5fd8358Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_realloc__anon_49e4e5fd8358

structure Buf_f32_4_0_appendLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive Buf_f32_4_0_appendExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br27
  | br39
  | br55
  | br63

def Buf_f32_4_0_append [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : Zig.F32) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    modify (fun s => { s with local3 := p1 })
    let i8 ← pure (((← get).local3).len)
    let i9 ← Zig.add false i8 (1 : BitVec 64)
    let i10 ← pure (((← get).local3).ptr)
    let i11 ← pure i10
    let i12 ← Zig.sub false i9 (0 : BitVec 64) (safe := false)
    let i13 ← pure (⟨i11, i12⟩ : Zig.Slice)
    let i15 ← pure (((← get).local3).len)
    let i16 ← Zig.add false i15 (2 : BitVec 64)
    let i17 ← Zig.callC (mem_Allocator_realloc__anon_49e4e5fd8358 p0 i13 i16)
    match i17 with
    | .error _ => (do
      let i19 ← Zig.callRC (Zig.unwrapErr i17)
      let i20 ← pure (i19)
      let i21 ← pure ((.error i20) : Except Zig.ErrName (Zig.Slice))
      pure (.ret i21))
    | .ok v18 => (do
      let i24 ← pure (((← get).local3).len)
      let i25 ← pure v18.len
      let i26 ← pure (Zig.lt false i24 i25)
      match ← ((do
        if i26 then (do
          pure .br27)
        else (do
          throw .outOfBounds)) : Zig.CM Tgt Buf_f32_4_0_appendLocals Buf_f32_4_0_appendExit) with
      | .br27 => (do
        let i32 ← Zig.callMC (Zig.checkIndex v18.len i24) >>= fun _ => Zig.callMC (Zig.ptrProject v18.ptr (·.elem 4 i24))
        Zig.store (α := Zig.F32) 4 i32 p2
        let i35 ← pure (((← get).local3).len)
        let i36 ← Zig.add false i35 (1 : BitVec 64)
        let i37 ← pure v18.len
        let i38 ← pure (Zig.lt false i36 i37)
        match ← ((do
          if i38 then (do
            pure .br39)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt Buf_f32_4_0_appendLocals Buf_f32_4_0_appendExit) with
        | .br39 => (do
          let i44 ← Zig.callMC (Zig.checkIndex v18.len i36) >>= fun _ => Zig.callMC (Zig.ptrProject v18.ptr (·.elem 4 i36))
          Zig.store (α := Zig.F32) 4 i44 (Zig.Float.ofBits (0 : BitVec 32) : Zig.F32)
          let i47 ← pure (((← get).local3).len)
          let i48 ← Zig.add false i47 (1 : BitVec 64)
          let i49 ← pure v18.ptr
          let i50 ← pure i49
          let i51 ← Zig.sub false i48 (0 : BitVec 64) (safe := false)
          let i52 ← pure v18.len
          let i53 ← Zig.add false i48 (1 : BitVec 64)
          let i54 ← pure (Zig.le false i53 i52)
          match ← ((do
            if i54 then (do
              pure .br55)
            else (do
              throw .outOfBounds)) : Zig.CM Tgt Buf_f32_4_0_appendLocals Buf_f32_4_0_appendExit) with
          | .br55 => (do
            let i60 ← Zig.callMC (Zig.checkSliceEnd v18.len (0 : BitVec 64) i51 1 >>= fun _ => pure (⟨i50, i51⟩ : Zig.Slice))
            let i61 ← Zig.callMC (Zig.checkSentinelIndex i60.len i51 >>= fun _ => Zig.load (Zig.F32) 4 (i60.ptr.elem 4 i51))
            let i62 ← pure (Zig.Float.eq (Zig.Float.ofBits (0 : BitVec 32) : Zig.F32) i61)
            match ← ((do
              if i62 then (do
                pure .br63)
              else (do
                throw .panic)) : Zig.CM Tgt Buf_f32_4_0_appendLocals Buf_f32_4_0_appendExit) with
            | .br63 => (do
              let i68 ← pure ((.ok i60) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i68))
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf_f32_4_0_appendLocals Buf_f32_4_0_appendExit).run' (default : Buf_f32_4_0_appendLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_f32_4_0_append

structure mem_Allocator_allocWithOptionsRetAddr__anon_8dadbb0f7e6eLocals where
  deriving Inhabited

inductive mem_Allocator_allocWithOptionsRetAddr__anon_8dadbb0f7e6eExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br4 (v : Except Zig.ErrName (Zig.Slice))
  | br22
  | br35
  | br43

def mem_Allocator_allocWithOptionsRetAddr__anon_8dadbb0f7e6e [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.add false p1 (1 : BitVec 64)
    match ← ((do
      let i5 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_7f4b76fbd810 p0 i3 p2)
      match i5 with
      | .error _ => (do
        let i7 ← Zig.callRC (Zig.unwrapErr i5)
        let i8 ← pure ((.error i7) : Except Zig.ErrName (Zig.Slice))
        pure (.br4 i8))
      | .ok v6 => (do
        let i10 ← pure (v6)
        let i11 ← pure i10
        let i12 ← Zig.sub false i3 (0 : BitVec 64) (safe := false)
        let i13 ← pure (⟨i11, i12⟩ : Zig.Slice)
        let i14 ← pure ((.ok i13) : Except Zig.ErrName (Zig.Slice))
        pure (.br4 i14))) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_8dadbb0f7e6eLocals mem_Allocator_allocWithOptionsRetAddr__anon_8dadbb0f7e6eExit) with
    | .br4 v4 => (do
      match v4 with
      | .error _ => (do
        let i17 ← Zig.callRC (Zig.unwrapErr v4)
        let i18 ← pure ((.error i17) : Except Zig.ErrName (Zig.Slice))
        pure (.ret i18))
      | .ok v16 => (do
        let i20 ← pure v16.len
        let i21 ← pure (Zig.lt false p1 i20)
        match ← ((do
          if i21 then (do
            pure .br22)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_8dadbb0f7e6eLocals mem_Allocator_allocWithOptionsRetAddr__anon_8dadbb0f7e6eExit) with
        | .br22 => (do
          let i27 ← Zig.callMC (Zig.checkIndex v16.len p1) >>= fun _ => Zig.callMC (Zig.ptrProject v16.ptr (·.elem 4 p1))
          Zig.store (α := Zig.F32) 4 i27 (Zig.Float.ofBits (0 : BitVec 32) : Zig.F32)
          let i29 ← pure v16.ptr
          let i30 ← pure i29
          let i31 ← Zig.sub false p1 (0 : BitVec 64) (safe := false)
          let i32 ← pure v16.len
          let i33 ← Zig.add false p1 (1 : BitVec 64)
          let i34 ← pure (Zig.le false i33 i32)
          match ← ((do
            if i34 then (do
              pure .br35)
            else (do
              throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_8dadbb0f7e6eLocals mem_Allocator_allocWithOptionsRetAddr__anon_8dadbb0f7e6eExit) with
          | .br35 => (do
            let i40 ← Zig.callMC (Zig.checkSliceEnd v16.len (0 : BitVec 64) i31 1 >>= fun _ => pure (⟨i30, i31⟩ : Zig.Slice))
            let i41 ← Zig.callMC (Zig.checkSentinelIndex i40.len i31 >>= fun _ => Zig.load (Zig.F32) 4 (i40.ptr.elem 4 i31))
            let i42 ← pure (Zig.Float.eq (Zig.Float.ofBits (0 : BitVec 32) : Zig.F32) i41)
            match ← ((do
              if i42 then (do
                pure .br43)
              else (do
                throw .panic)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_8dadbb0f7e6eLocals mem_Allocator_allocWithOptionsRetAddr__anon_8dadbb0f7e6eExit) with
            | .br43 => (do
              let i48 ← pure ((.ok i40) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i48))
            | e => pure e)
          | e => pure e)
        | e => pure e))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_8dadbb0f7e6eLocals mem_Allocator_allocWithOptionsRetAddr__anon_8dadbb0f7e6eExit).run' (default : mem_Allocator_allocWithOptionsRetAddr__anon_8dadbb0f7e6eLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocWithOptionsRetAddr__anon_8dadbb0f7e6e

structure mem_Allocator_allocSentinel__anon_39ca3fb2a5a4Locals where
  local4 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_allocSentinel__anon_39ca3fb2a5a4Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_allocSentinel__anon_39ca3fb2a5a4 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s4 ← Zig.allocStack 24 8
  let e ← ((do
    let i2 ← Zig.callMC Zig.returnAddress
    let i3 ← Zig.callC (mem_Allocator_allocWithOptionsRetAddr__anon_8dadbb0f7e6e p0 p1 i2)
    let i4 ← pure (← get).local4
    (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i4 i3)
    let i6 ← pure (i4)
    let i7 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i6)
    pure (.ret i7)) : Zig.CM Tgt mem_Allocator_allocSentinel__anon_39ca3fb2a5a4Locals mem_Allocator_allocSentinel__anon_39ca3fb2a5a4Exit).run' { (default : mem_Allocator_allocSentinel__anon_39ca3fb2a5a4Locals) with local4 := s4 }
  Zig.free s4
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_allocSentinel__anon_39ca3fb2a5a4

structure Buf_f32_4_0_makeLocals where
  local3 : Zig.Ptr
  deriving Inhabited

inductive Buf_f32_4_0_makeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def Buf_f32_4_0_make [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s3 ← Zig.allocStack 24 8
  let e ← ((do
    let i2 ← Zig.callC (mem_Allocator_allocSentinel__anon_39ca3fb2a5a4 p0 p1)
    let i3 ← pure (← get).local3
    (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i3 i2)
    let i5 ← pure (i3)
    let i6 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i5)
    pure (.ret i6)) : Zig.CM Tgt Buf_f32_4_0_makeLocals Buf_f32_4_0_makeExit).run' { (default : Buf_f32_4_0_makeLocals) with local3 := s3 }
  Zig.free s3
  match e with
  | .ret v => pure v

attribute [zig_run] Buf_f32_4_0_make

structure mem_absorbSentinel__anon_0f79a66dddd2Locals where
  local1 : Zig.Slice
  deriving Inhabited

inductive mem_absorbSentinel__anon_0f79a66dddd2Exit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_0f79a66dddd2 (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    modify (fun s => { s with local1 := p0 })
    let i6 ← pure (((← get).local1).len)
    let i7 ← Zig.add false i6 (1 : BitVec 64)
    let i8 ← pure (((← get).local1).ptr)
    let i9 ← pure i8
    let i10 ← Zig.sub false i7 (0 : BitVec 64) (safe := false)
    let i11 ← pure (⟨i9, i10⟩ : Zig.Slice)
    pure (.ret i11)) : Zig.MM mem_absorbSentinel__anon_0f79a66dddd2Locals mem_absorbSentinel__anon_0f79a66dddd2Exit).run' (default : mem_absorbSentinel__anon_0f79a66dddd2Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_absorbSentinel__anon_0f79a66dddd2

structure mem_Allocator_free__anon_af4b77de30f4Locals where
  deriving Inhabited

inductive mem_Allocator_free__anon_af4b77de30f4Exit where
  | ret
  | br8
  | br19

def mem_Allocator_free__anon_af4b77de30f4 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_0f79a66dddd2 p1)
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
        pure .br8)) : Zig.CM Tgt mem_Allocator_free__anon_af4b77de30f4Locals mem_Allocator_free__anon_af4b77de30f4Exit) with
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
        pure .br19) : Zig.CM Tgt mem_Allocator_free__anon_af4b77de30f4Locals mem_Allocator_free__anon_af4b77de30f4Exit) with
      | .br19 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_af4b77de30f4Locals mem_Allocator_free__anon_af4b77de30f4Exit).run' (default : mem_Allocator_free__anon_af4b77de30f4Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_af4b77de30f4

structure Buf_f32_4_0_releaseLocals where
  deriving Inhabited

inductive Buf_f32_4_0_releaseExit where
  | ret

def Buf_f32_4_0_release [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let _i2 ← Zig.callC (mem_Allocator_free__anon_af4b77de30f4 p0 p1)
    pure .ret) : Zig.CM Tgt Buf_f32_4_0_releaseLocals Buf_f32_4_0_releaseExit).run' (default : Buf_f32_4_0_releaseLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Buf_f32_4_0_release

structure Buf_f32_4_0_resizeLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive Buf_f32_4_0_resizeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br23
  | br36
  | br44

def Buf_f32_4_0_resize [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    modify (fun s => { s with local3 := p1 })
    let i8 ← pure (((← get).local3).len)
    let i9 ← Zig.add false i8 (1 : BitVec 64)
    let i10 ← pure (((← get).local3).ptr)
    let i11 ← pure i10
    let i12 ← Zig.sub false i9 (0 : BitVec 64) (safe := false)
    let i13 ← pure (⟨i11, i12⟩ : Zig.Slice)
    let i14 ← Zig.add false p2 (1 : BitVec 64)
    let i15 ← Zig.callC (mem_Allocator_realloc__anon_49e4e5fd8358 p0 i13 i14)
    match i15 with
    | .error _ => (do
      let i17 ← Zig.callRC (Zig.unwrapErr i15)
      let i18 ← pure (i17)
      let i19 ← pure ((.error i18) : Except Zig.ErrName (Zig.Slice))
      pure (.ret i19))
    | .ok v16 => (do
      let i21 ← pure v16.len
      let i22 ← pure (Zig.lt false p2 i21)
      match ← ((do
        if i22 then (do
          pure .br23)
        else (do
          throw .outOfBounds)) : Zig.CM Tgt Buf_f32_4_0_resizeLocals Buf_f32_4_0_resizeExit) with
      | .br23 => (do
        let i28 ← Zig.callMC (Zig.checkIndex v16.len p2) >>= fun _ => Zig.callMC (Zig.ptrProject v16.ptr (·.elem 4 p2))
        Zig.store (α := Zig.F32) 4 i28 (Zig.Float.ofBits (0 : BitVec 32) : Zig.F32)
        let i30 ← pure v16.ptr
        let i31 ← pure i30
        let i32 ← Zig.sub false p2 (0 : BitVec 64) (safe := false)
        let i33 ← pure v16.len
        let i34 ← Zig.add false p2 (1 : BitVec 64)
        let i35 ← pure (Zig.le false i34 i33)
        match ← ((do
          if i35 then (do
            pure .br36)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt Buf_f32_4_0_resizeLocals Buf_f32_4_0_resizeExit) with
        | .br36 => (do
          let i41 ← Zig.callMC (Zig.checkSliceEnd v16.len (0 : BitVec 64) i32 1 >>= fun _ => pure (⟨i31, i32⟩ : Zig.Slice))
          let i42 ← Zig.callMC (Zig.checkSentinelIndex i41.len i32 >>= fun _ => Zig.load (Zig.F32) 4 (i41.ptr.elem 4 i32))
          let i43 ← pure (Zig.Float.eq (Zig.Float.ofBits (0 : BitVec 32) : Zig.F32) i42)
          match ← ((do
            if i43 then (do
              pure .br44)
            else (do
              throw .panic)) : Zig.CM Tgt Buf_f32_4_0_resizeLocals Buf_f32_4_0_resizeExit) with
          | .br44 => (do
            let i49 ← pure ((.ok i41) : Except Zig.ErrName (Zig.Slice))
            pure (.ret i49))
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf_f32_4_0_resizeLocals Buf_f32_4_0_resizeExit).run' (default : Buf_f32_4_0_resizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_f32_4_0_resize

structure mem_Allocator_allocBytesAligned__anon_332dbb1df1a8Locals where
  deriving Inhabited

inductive mem_Allocator_allocBytesAligned__anon_332dbb1df1a8Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3
  | br10 (v : Option (Zig.Ptr))
  | br9 (v : Zig.Ptr)
  | br30

def mem_Allocator_allocBytesAligned__anon_332dbb1df1a8 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (⟨none, 18446744073709551600⟩ : Zig.Ptr) : Except Zig.ErrName (Zig.Ptr))))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_332dbb1df1a8Locals mem_Allocator_allocBytesAligned__anon_332dbb1df1a8Exit) with
    | .br3 => (do
      match ← ((do
        match ← ((do
          let i11 ← pure ((p0).vtable)
          let i12 ← pure i11
          let i13 ← Zig.load (Zig.Ptr) 8 i12
          let i14 ← pure ((p0).ptr)
          let i15 ← (Zig.callC (Zig.extCall (Ext.call0 i13 i14 p1 mem_Alignment.«16» p2)))
          pure (.br10 i15)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_332dbb1df1a8Locals mem_Allocator_allocBytesAligned__anon_332dbb1df1a8Exit) with
        | .br10 v10 => (do
          let i17 ← pure ((v10).isSome)
          if i17 then (do
            let i19 ← Zig.optPayload v10
            pure (.br9 i19))
          else (do
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr)))))
        | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_332dbb1df1a8Locals mem_Allocator_allocBytesAligned__anon_332dbb1df1a8Exit) with
      | .br9 v9 => (do
        let i22 ← pure v9
        let i23 ← Zig.sub false p1 (0 : BitVec 64) (safe := false)
        let i24 ← pure (⟨i22, i23⟩ : Zig.Slice)
        let _i25 ← pure i24.len
        Zig.callMC (Zig.memset (α := BitVec 8) 1 i24.ptr i24.len none)
        let i27 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr v9)))
        let i28 ← pure (i27 &&& (15 : BitVec 64))
        let i29 ← pure (i28 == (0 : BitVec 64))
        match ← ((do
          if i29 then (do
            pure .br30)
          else (do
            throw .panic)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_332dbb1df1a8Locals mem_Allocator_allocBytesAligned__anon_332dbb1df1a8Exit) with
        | .br30 => (do
          let i35 ← Zig.callMC (Zig.checkAlign 16 v9 >>= fun _ => pure v9)
          let i36 ← pure ((.ok i35) : Except Zig.ErrName (Zig.Ptr))
          pure (.ret i36))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_332dbb1df1a8Locals mem_Allocator_allocBytesAligned__anon_332dbb1df1a8Exit).run' (default : mem_Allocator_allocBytesAligned__anon_332dbb1df1a8Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocBytesAligned__anon_332dbb1df1a8

structure mem_Allocator_allocWithSizeAndAlignment__anon_de1f00c497caLocals where
  deriving Inhabited

inductive mem_Allocator_allocWithSizeAndAlignment__anon_de1f00c497caExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3 (v : BitVec 64)

def mem_Allocator_allocWithSizeAndAlignment__anon_de1f00c497ca [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.callRC (math_mul__anon_44faaf286c79 (2 : BitVec 64) p1)
      let i5 ← pure (Zig.isNonErr i4)
      if i5 then (do
        let i7 ← Zig.callRC (Zig.unwrapPayload i4)
        pure (.br3 i7))
      else (do
        let _i9 ← Zig.callRC (Zig.unwrapErr i4)
        pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr))))) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_de1f00c497caLocals mem_Allocator_allocWithSizeAndAlignment__anon_de1f00c497caExit) with
    | .br3 v3 => (do
      let i11 ← Zig.callC (mem_Allocator_allocBytesAligned__anon_332dbb1df1a8 p0 v3 p2)
      pure (.ret i11))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_de1f00c497caLocals mem_Allocator_allocWithSizeAndAlignment__anon_de1f00c497caExit).run' (default : mem_Allocator_allocWithSizeAndAlignment__anon_de1f00c497caLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocWithSizeAndAlignment__anon_de1f00c497ca

structure mem_absorbSentinel__anon_30541d8bf7f7Locals where
  deriving Inhabited

inductive mem_absorbSentinel__anon_30541d8bf7f7Exit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_30541d8bf7f7 (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret p0)) : Zig.MM mem_absorbSentinel__anon_30541d8bf7f7Locals mem_absorbSentinel__anon_30541d8bf7f7Exit).run' (default : mem_absorbSentinel__anon_30541d8bf7f7Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_absorbSentinel__anon_30541d8bf7f7

structure mem_Allocator_free__anon_41d335cc856aLocals where
  deriving Inhabited

inductive mem_Allocator_free__anon_41d335cc856aExit where
  | ret
  | br8
  | br19

def mem_Allocator_free__anon_41d335cc856a [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_30541d8bf7f7 p1)
    let i3 ← pure i2.ptr
    let i4 ← pure i2.len
    let i5 ← Zig.mul false i4 (2 : BitVec 64) (safe := false)
    let i6 ← pure (i3)
    let i7 ← pure (⟨i6, i5⟩ : Zig.Slice)
    match ← ((do
      let i9 ← pure i7.len
      let i10 ← pure (i9)
      let i11 ← pure (i10 == (0 : BitVec 64))
      if i11 then (do
        pure .ret)
      else (do
        pure .br8)) : Zig.CM Tgt mem_Allocator_free__anon_41d335cc856aLocals mem_Allocator_free__anon_41d335cc856aExit) with
    | .br8 => (do
      let _i15 ← pure i7.len
      Zig.callMC (Zig.memset (α := BitVec 8) 1 i7.ptr i7.len none)
      let i17 ← Zig.callRC (mem_Alignment_fromByteUnits (16 : BitVec 64))
      let i18 ← Zig.callMC Zig.returnAddress
      match ← ((do
        let i20 ← pure ((p0).vtable)
        let i21 ← Zig.callMC (Zig.ptrProject i20 (·.add 24))
        let i22 ← Zig.load (Zig.Ptr) 8 i21
        let i23 ← pure ((p0).ptr)
        let _i24 ← (Zig.callC (Zig.extCall (Ext.call2 i22 i23 i7 i17 i18)))
        pure .br19) : Zig.CM Tgt mem_Allocator_free__anon_41d335cc856aLocals mem_Allocator_free__anon_41d335cc856aExit) with
      | .br19 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_41d335cc856aLocals mem_Allocator_free__anon_41d335cc856aExit).run' (default : mem_Allocator_free__anon_41d335cc856aLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_41d335cc856a

structure mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals where
  deriving Inhabited

inductive mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br9 (v : Except Zig.ErrName (Zig.Slice))
  | br4
  | br23
  | br36 (v : BitVec 64)
  | br46 (v : Option (Zig.Ptr))
  | br66
  | br73
  | br44
  | br86 (v : Option (Zig.Ptr))
  | br84 (v : Zig.Ptr)
  | br112
  | br121
  | br133
  | br142
  | br159
  | br166

def mem_Allocator_reallocAdvanced__anon_bbf7731c5936 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) (p3 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    match ← ((do
      let i5 ← pure p1.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        match ← ((do
          let i10 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_de1f00c497ca p0 p2 p3)
          match i10 with
          | .error _ => (do
            let i12 ← Zig.callRC (Zig.unwrapErr i10)
            let i13 ← pure ((.error i12) : Except Zig.ErrName (Zig.Slice))
            pure (.br9 i13))
          | .ok v11 => (do
            let i15 ← pure (v11)
            let i16 ← pure i15
            let i17 ← Zig.sub false p2 (0 : BitVec 64) (safe := false)
            let i18 ← pure (⟨i16, i17⟩ : Zig.Slice)
            let i19 ← pure ((.ok i18) : Except Zig.ErrName (Zig.Slice))
            pure (.br9 i19))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit) with
        | .br9 v9 => (do
          pure (.ret v9))
        | e => pure e)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit) with
    | .br4 => (do
      match ← ((do
        let i24 ← pure (p2)
        let i25 ← pure (i24 == (0 : BitVec 64))
        if i25 then (do
          let _i27 ← Zig.callC (mem_Allocator_free__anon_41d335cc856a p0 p1)
          pure (.ret (.ok (⟨(⟨none, 18446744073709551600⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice) : Except Zig.ErrName (Zig.Slice))))
        else (do
          pure .br23)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit) with
      | .br23 => (do
        let i30 ← Zig.callMC (mem_absorbSentinel__anon_30541d8bf7f7 p1)
        let i31 ← pure i30.ptr
        let i32 ← pure i30.len
        let i33 ← Zig.mul false i32 (2 : BitVec 64) (safe := false)
        let i34 ← pure (i31)
        let i35 ← pure (⟨i34, i33⟩ : Zig.Slice)
        match ← ((do
          let i37 ← Zig.callRC (math_mul__anon_44faaf286c79 (2 : BitVec 64) p2)
          let i38 ← pure (Zig.isNonErr i37)
          if i38 then (do
            let i40 ← Zig.callRC (Zig.unwrapPayload i37)
            pure (.br36 i40))
          else (do
            let _i42 ← Zig.callRC (Zig.unwrapErr i37)
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice))))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit) with
        | .br36 v36 => (do
          match ← ((do
            let i45 ← Zig.callRC (mem_Alignment_fromByteUnits (16 : BitVec 64))
            match ← ((do
              let i47 ← pure ((p0).vtable)
              let i48 ← Zig.callMC (Zig.ptrProject i47 (·.add 16))
              let i49 ← Zig.load (Zig.Ptr) 8 i48
              let i50 ← pure ((p0).ptr)
              let i51 ← (Zig.callC (Zig.extCall (Ext.call1 i49 i50 i35 i45 v36 p3)))
              pure (.br46 i51)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit) with
            | .br46 v46 => (do
              let i53 ← pure ((v46).isSome)
              if i53 then (do
                let i55 ← Zig.optPayload v46
                let i56 ← pure i55
                let i57 ← Zig.sub false v36 (0 : BitVec 64) (safe := false)
                let i58 ← pure (⟨i56, i57⟩ : Zig.Slice)
                let i59 ← pure i58.ptr
                let i60 ← pure i58.len
                let i61 ← pure (i60 == (0 : BitVec 64))
                let i62 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i59)))
                let i63 ← pure (i62 &&& (15 : BitVec 64))
                let i64 ← pure (i63 == (0 : BitVec 64))
                let i65 ← pure (i61 || i64)
                match ← ((do
                  if i65 then (do
                    pure .br66)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit) with
                | .br66 => (do
                  let i71 ← Zig.rem false i60 (2 : BitVec 64)
                  let i72 ← pure (i71 == (0 : BitVec 64))
                  match ← ((do
                    if i72 then (do
                      pure .br73)
                    else (do
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit) with
                  | .br73 => (do
                    let i78 ← Zig.divExact false i60 (2 : BitVec 64)
                    let i79 ← Zig.callMC (Zig.checkAlign 16 i59 >>= fun _ => pure i59)
                    let i80 ← pure (⟨i79, i78⟩ : Zig.Slice)
                    let i81 ← pure ((.ok i80) : Except Zig.ErrName (Zig.Slice))
                    pure (.ret i81))
                  | e => pure e)
                | e => pure e)
              else (do
                pure .br44))
            | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit) with
          | .br44 => (do
            match ← ((do
              let i85 ← Zig.callRC (mem_Alignment_fromByteUnits (16 : BitVec 64))
              match ← ((do
                let i87 ← pure ((p0).vtable)
                let i88 ← pure i87
                let i89 ← Zig.load (Zig.Ptr) 8 i88
                let i90 ← pure ((p0).ptr)
                let i91 ← (Zig.callC (Zig.extCall (Ext.call0 i89 i90 v36 i85 p3)))
                pure (.br86 i91)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit) with
              | .br86 v86 => (do
                let i93 ← pure ((v86).isSome)
                if i93 then (do
                  let i95 ← Zig.optPayload v86
                  pure (.br84 i95))
                else (do
                  pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice)))))
              | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit) with
            | .br84 v84 => (do
              let i98 ← pure i35.len
              let i99 ← pure (v36)
              let i100 ← pure (i98)
              let i101 ← pure (Zig.min false i99 i100)
              let i102 ← pure v84
              let i103 ← pure (i101)
              let i104 ← Zig.sub false i103 (0 : BitVec 64) (safe := false)
              let i105 ← pure (⟨i102, i104⟩ : Zig.Slice)
              let i106 ← pure i35.ptr
              let i107 ← pure i106
              let i108 ← pure (i101)
              let i109 ← Zig.sub false i108 (0 : BitVec 64) (safe := false)
              let i110 ← pure i35.len
              let i111 ← pure (Zig.le false i108 i110)
              match ← ((do
                if i111 then (do
                  pure .br112)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit) with
              | .br112 => (do
                let i117 ← Zig.callMC (Zig.checkSliceEnd i35.len (0 : BitVec 64) i109 0 >>= fun _ => pure (⟨i107, i109⟩ : Zig.Slice))
                let i118 ← pure i105.len
                let i119 ← pure i117.len
                let i120 ← pure (i118 == i119)
                match ← ((do
                  if i120 then (do
                    pure .br121)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit) with
                | .br121 => (do
                  let i126 ← pure i117.ptr
                  let i127 ← pure i105.ptr
                  let i128 ← Zig.callMC (Zig.ptrProject i126 (·.elem 1 i118))
                  let i129 ← Zig.callMC (Zig.ptrProject i127 (·.elem 1 i118))
                  let i130 ← Zig.callMC (Zig.ptrLe i128 i127)
                  let i131 ← Zig.callMC (Zig.ptrLe i129 i126)
                  let i132 ← pure (i130 || i131)
                  match ← ((do
                    if i132 then (do
                      pure .br133)
                    else (do
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit) with
                  | .br133 => (do
                    Zig.callMC (Zig.memcpy 1 1 1 i105.ptr i126 i105.len i117.len)
                    let _i139 ← pure i35.len
                    Zig.callMC (Zig.memset (α := BitVec 8) 1 i35.ptr i35.len none)
                    let i141 ← Zig.callRC (mem_Alignment_fromByteUnits (16 : BitVec 64))
                    match ← ((do
                      let i143 ← pure ((p0).vtable)
                      let i144 ← Zig.callMC (Zig.ptrProject i143 (·.add 24))
                      let i145 ← Zig.load (Zig.Ptr) 8 i144
                      let i146 ← pure ((p0).ptr)
                      let _i147 ← (Zig.callC (Zig.extCall (Ext.call2 i145 i146 i35 i141 p3)))
                      pure .br142) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit) with
                    | .br142 => (do
                      let i149 ← pure v84
                      let i150 ← Zig.sub false v36 (0 : BitVec 64) (safe := false)
                      let i151 ← pure (⟨i149, i150⟩ : Zig.Slice)
                      let i152 ← pure i151.ptr
                      let i153 ← pure i151.len
                      let i154 ← pure (i153 == (0 : BitVec 64))
                      let i155 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i152)))
                      let i156 ← pure (i155 &&& (15 : BitVec 64))
                      let i157 ← pure (i156 == (0 : BitVec 64))
                      let i158 ← pure (i154 || i157)
                      match ← ((do
                        if i158 then (do
                          pure .br159)
                        else (do
                          throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit) with
                      | .br159 => (do
                        let i164 ← Zig.rem false i153 (2 : BitVec 64)
                        let i165 ← pure (i164 == (0 : BitVec 64))
                        match ← ((do
                          if i165 then (do
                            pure .br166)
                          else (do
                            throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit) with
                        | .br166 => (do
                          let i171 ← Zig.divExact false i153 (2 : BitVec 64)
                          let i172 ← Zig.callMC (Zig.checkAlign 16 i152 >>= fun _ => pure i152)
                          let i173 ← pure (⟨i172, i171⟩ : Zig.Slice)
                          let i174 ← pure ((.ok i173) : Except Zig.ErrName (Zig.Slice))
                          pure (.ret i174))
                        | e => pure e)
                      | e => pure e)
                    | e => pure e)
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals mem_Allocator_reallocAdvanced__anon_bbf7731c5936Exit).run' (default : mem_Allocator_reallocAdvanced__anon_bbf7731c5936Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_reallocAdvanced__anon_bbf7731c5936

structure mem_Allocator_realloc__anon_c129341ebc17Locals where
  deriving Inhabited

inductive mem_Allocator_realloc__anon_c129341ebc17Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_realloc__anon_c129341ebc17 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.callMC Zig.returnAddress
    let i4 ← Zig.callC (mem_Allocator_reallocAdvanced__anon_bbf7731c5936 p0 p1 p2 i3)
    pure (.ret i4)) : Zig.CM Tgt mem_Allocator_realloc__anon_c129341ebc17Locals mem_Allocator_realloc__anon_c129341ebc17Exit).run' (default : mem_Allocator_realloc__anon_c129341ebc17Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_realloc__anon_c129341ebc17

structure Buf_u16_16_0_appendLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive Buf_u16_16_0_appendExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br27
  | br39
  | br55
  | br63

def Buf_u16_16_0_append [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 16) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    modify (fun s => { s with local3 := p1 })
    let i8 ← pure (((← get).local3).len)
    let i9 ← Zig.add false i8 (1 : BitVec 64)
    let i10 ← pure (((← get).local3).ptr)
    let i11 ← pure i10
    let i12 ← Zig.sub false i9 (0 : BitVec 64) (safe := false)
    let i13 ← pure (⟨i11, i12⟩ : Zig.Slice)
    let i15 ← pure (((← get).local3).len)
    let i16 ← Zig.add false i15 (2 : BitVec 64)
    let i17 ← Zig.callC (mem_Allocator_realloc__anon_c129341ebc17 p0 i13 i16)
    match i17 with
    | .error _ => (do
      let i19 ← Zig.callRC (Zig.unwrapErr i17)
      let i20 ← pure (i19)
      let i21 ← pure ((.error i20) : Except Zig.ErrName (Zig.Slice))
      pure (.ret i21))
    | .ok v18 => (do
      let i24 ← pure (((← get).local3).len)
      let i25 ← pure v18.len
      let i26 ← pure (Zig.lt false i24 i25)
      match ← ((do
        if i26 then (do
          pure .br27)
        else (do
          throw .outOfBounds)) : Zig.CM Tgt Buf_u16_16_0_appendLocals Buf_u16_16_0_appendExit) with
      | .br27 => (do
        let i32 ← Zig.callMC (Zig.checkIndex v18.len i24) >>= fun _ => Zig.callMC (Zig.ptrProject v18.ptr (·.elem 2 i24))
        Zig.store (α := BitVec 16) 2 i32 p2
        let i35 ← pure (((← get).local3).len)
        let i36 ← Zig.add false i35 (1 : BitVec 64)
        let i37 ← pure v18.len
        let i38 ← pure (Zig.lt false i36 i37)
        match ← ((do
          if i38 then (do
            pure .br39)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt Buf_u16_16_0_appendLocals Buf_u16_16_0_appendExit) with
        | .br39 => (do
          let i44 ← Zig.callMC (Zig.checkIndex v18.len i36) >>= fun _ => Zig.callMC (Zig.ptrProject v18.ptr (·.elem 2 i36))
          Zig.store (α := BitVec 16) 2 i44 (0 : BitVec 16)
          let i47 ← pure (((← get).local3).len)
          let i48 ← Zig.add false i47 (1 : BitVec 64)
          let i49 ← pure v18.ptr
          let i50 ← pure i49
          let i51 ← Zig.sub false i48 (0 : BitVec 64) (safe := false)
          let i52 ← pure v18.len
          let i53 ← Zig.add false i48 (1 : BitVec 64)
          let i54 ← pure (Zig.le false i53 i52)
          match ← ((do
            if i54 then (do
              pure .br55)
            else (do
              throw .outOfBounds)) : Zig.CM Tgt Buf_u16_16_0_appendLocals Buf_u16_16_0_appendExit) with
          | .br55 => (do
            let i60 ← Zig.callMC (Zig.checkSliceEnd v18.len (0 : BitVec 64) i51 1 >>= fun _ => pure (⟨i50, i51⟩ : Zig.Slice))
            let i61 ← Zig.callMC (Zig.checkSentinelIndex i60.len i51 >>= fun _ => Zig.load (BitVec 16) 2 (i60.ptr.elem 2 i51))
            let i62 ← pure ((0 : BitVec 16) == i61)
            match ← ((do
              if i62 then (do
                pure .br63)
              else (do
                throw .panic)) : Zig.CM Tgt Buf_u16_16_0_appendLocals Buf_u16_16_0_appendExit) with
            | .br63 => (do
              let i68 ← pure ((.ok i60) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i68))
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf_u16_16_0_appendLocals Buf_u16_16_0_appendExit).run' (default : Buf_u16_16_0_appendLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u16_16_0_append

structure mem_Allocator_allocWithOptionsRetAddr__anon_375b6fbf2ca8Locals where
  deriving Inhabited

inductive mem_Allocator_allocWithOptionsRetAddr__anon_375b6fbf2ca8Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br4 (v : Except Zig.ErrName (Zig.Slice))
  | br22
  | br35
  | br43

def mem_Allocator_allocWithOptionsRetAddr__anon_375b6fbf2ca8 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.add false p1 (1 : BitVec 64)
    match ← ((do
      let i5 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_de1f00c497ca p0 i3 p2)
      match i5 with
      | .error _ => (do
        let i7 ← Zig.callRC (Zig.unwrapErr i5)
        let i8 ← pure ((.error i7) : Except Zig.ErrName (Zig.Slice))
        pure (.br4 i8))
      | .ok v6 => (do
        let i10 ← pure (v6)
        let i11 ← pure i10
        let i12 ← Zig.sub false i3 (0 : BitVec 64) (safe := false)
        let i13 ← pure (⟨i11, i12⟩ : Zig.Slice)
        let i14 ← pure ((.ok i13) : Except Zig.ErrName (Zig.Slice))
        pure (.br4 i14))) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_375b6fbf2ca8Locals mem_Allocator_allocWithOptionsRetAddr__anon_375b6fbf2ca8Exit) with
    | .br4 v4 => (do
      match v4 with
      | .error _ => (do
        let i17 ← Zig.callRC (Zig.unwrapErr v4)
        let i18 ← pure ((.error i17) : Except Zig.ErrName (Zig.Slice))
        pure (.ret i18))
      | .ok v16 => (do
        let i20 ← pure v16.len
        let i21 ← pure (Zig.lt false p1 i20)
        match ← ((do
          if i21 then (do
            pure .br22)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_375b6fbf2ca8Locals mem_Allocator_allocWithOptionsRetAddr__anon_375b6fbf2ca8Exit) with
        | .br22 => (do
          let i27 ← Zig.callMC (Zig.checkIndex v16.len p1) >>= fun _ => Zig.callMC (Zig.ptrProject v16.ptr (·.elem 2 p1))
          Zig.store (α := BitVec 16) 2 i27 (0 : BitVec 16)
          let i29 ← pure v16.ptr
          let i30 ← pure i29
          let i31 ← Zig.sub false p1 (0 : BitVec 64) (safe := false)
          let i32 ← pure v16.len
          let i33 ← Zig.add false p1 (1 : BitVec 64)
          let i34 ← pure (Zig.le false i33 i32)
          match ← ((do
            if i34 then (do
              pure .br35)
            else (do
              throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_375b6fbf2ca8Locals mem_Allocator_allocWithOptionsRetAddr__anon_375b6fbf2ca8Exit) with
          | .br35 => (do
            let i40 ← Zig.callMC (Zig.checkSliceEnd v16.len (0 : BitVec 64) i31 1 >>= fun _ => pure (⟨i30, i31⟩ : Zig.Slice))
            let i41 ← Zig.callMC (Zig.checkSentinelIndex i40.len i31 >>= fun _ => Zig.load (BitVec 16) 2 (i40.ptr.elem 2 i31))
            let i42 ← pure ((0 : BitVec 16) == i41)
            match ← ((do
              if i42 then (do
                pure .br43)
              else (do
                throw .panic)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_375b6fbf2ca8Locals mem_Allocator_allocWithOptionsRetAddr__anon_375b6fbf2ca8Exit) with
            | .br43 => (do
              let i48 ← pure ((.ok i40) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i48))
            | e => pure e)
          | e => pure e)
        | e => pure e))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_375b6fbf2ca8Locals mem_Allocator_allocWithOptionsRetAddr__anon_375b6fbf2ca8Exit).run' (default : mem_Allocator_allocWithOptionsRetAddr__anon_375b6fbf2ca8Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocWithOptionsRetAddr__anon_375b6fbf2ca8

structure mem_Allocator_allocWithOptions__anon_6a25d32edb06Locals where
  deriving Inhabited

inductive mem_Allocator_allocWithOptions__anon_6a25d32edb06Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_allocWithOptions__anon_6a25d32edb06 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.callMC Zig.returnAddress
    let i3 ← Zig.callC (mem_Allocator_allocWithOptionsRetAddr__anon_375b6fbf2ca8 p0 p1 i2)
    pure (.ret i3)) : Zig.CM Tgt mem_Allocator_allocWithOptions__anon_6a25d32edb06Locals mem_Allocator_allocWithOptions__anon_6a25d32edb06Exit).run' (default : mem_Allocator_allocWithOptions__anon_6a25d32edb06Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_allocWithOptions__anon_6a25d32edb06

structure Buf_u16_16_0_makeLocals where
  deriving Inhabited

inductive Buf_u16_16_0_makeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def Buf_u16_16_0_make [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.callC (mem_Allocator_allocWithOptions__anon_6a25d32edb06 p0 p1)
    let i3 ← pure (i2)
    pure (.ret i3)) : Zig.CM Tgt Buf_u16_16_0_makeLocals Buf_u16_16_0_makeExit).run' (default : Buf_u16_16_0_makeLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Buf_u16_16_0_make

structure mem_absorbSentinel__anon_da87bd5769a8Locals where
  local1 : Zig.Slice
  deriving Inhabited

inductive mem_absorbSentinel__anon_da87bd5769a8Exit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_da87bd5769a8 (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    modify (fun s => { s with local1 := p0 })
    let i6 ← pure (((← get).local1).len)
    let i7 ← Zig.add false i6 (1 : BitVec 64)
    let i8 ← pure (((← get).local1).ptr)
    let i9 ← pure i8
    let i10 ← Zig.sub false i7 (0 : BitVec 64) (safe := false)
    let i11 ← pure (⟨i9, i10⟩ : Zig.Slice)
    pure (.ret i11)) : Zig.MM mem_absorbSentinel__anon_da87bd5769a8Locals mem_absorbSentinel__anon_da87bd5769a8Exit).run' (default : mem_absorbSentinel__anon_da87bd5769a8Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_absorbSentinel__anon_da87bd5769a8

structure mem_Allocator_free__anon_a2c4c1310d94Locals where
  deriving Inhabited

inductive mem_Allocator_free__anon_a2c4c1310d94Exit where
  | ret
  | br8
  | br19

def mem_Allocator_free__anon_a2c4c1310d94 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_da87bd5769a8 p1)
    let i3 ← pure i2.ptr
    let i4 ← pure i2.len
    let i5 ← Zig.mul false i4 (2 : BitVec 64) (safe := false)
    let i6 ← pure (i3)
    let i7 ← pure (⟨i6, i5⟩ : Zig.Slice)
    match ← ((do
      let i9 ← pure i7.len
      let i10 ← pure (i9)
      let i11 ← pure (i10 == (0 : BitVec 64))
      if i11 then (do
        pure .ret)
      else (do
        pure .br8)) : Zig.CM Tgt mem_Allocator_free__anon_a2c4c1310d94Locals mem_Allocator_free__anon_a2c4c1310d94Exit) with
    | .br8 => (do
      let _i15 ← pure i7.len
      Zig.callMC (Zig.memset (α := BitVec 8) 1 i7.ptr i7.len none)
      let i17 ← Zig.callRC (mem_Alignment_fromByteUnits (16 : BitVec 64))
      let i18 ← Zig.callMC Zig.returnAddress
      match ← ((do
        let i20 ← pure ((p0).vtable)
        let i21 ← Zig.callMC (Zig.ptrProject i20 (·.add 24))
        let i22 ← Zig.load (Zig.Ptr) 8 i21
        let i23 ← pure ((p0).ptr)
        let _i24 ← (Zig.callC (Zig.extCall (Ext.call2 i22 i23 i7 i17 i18)))
        pure .br19) : Zig.CM Tgt mem_Allocator_free__anon_a2c4c1310d94Locals mem_Allocator_free__anon_a2c4c1310d94Exit) with
      | .br19 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_a2c4c1310d94Locals mem_Allocator_free__anon_a2c4c1310d94Exit).run' (default : mem_Allocator_free__anon_a2c4c1310d94Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_a2c4c1310d94

structure Buf_u16_16_0_releaseLocals where
  deriving Inhabited

inductive Buf_u16_16_0_releaseExit where
  | ret

def Buf_u16_16_0_release [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let _i2 ← Zig.callC (mem_Allocator_free__anon_a2c4c1310d94 p0 p1)
    pure .ret) : Zig.CM Tgt Buf_u16_16_0_releaseLocals Buf_u16_16_0_releaseExit).run' (default : Buf_u16_16_0_releaseLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Buf_u16_16_0_release

structure Buf_u16_16_0_resizeLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive Buf_u16_16_0_resizeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br23
  | br36
  | br44

def Buf_u16_16_0_resize [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    modify (fun s => { s with local3 := p1 })
    let i8 ← pure (((← get).local3).len)
    let i9 ← Zig.add false i8 (1 : BitVec 64)
    let i10 ← pure (((← get).local3).ptr)
    let i11 ← pure i10
    let i12 ← Zig.sub false i9 (0 : BitVec 64) (safe := false)
    let i13 ← pure (⟨i11, i12⟩ : Zig.Slice)
    let i14 ← Zig.add false p2 (1 : BitVec 64)
    let i15 ← Zig.callC (mem_Allocator_realloc__anon_c129341ebc17 p0 i13 i14)
    match i15 with
    | .error _ => (do
      let i17 ← Zig.callRC (Zig.unwrapErr i15)
      let i18 ← pure (i17)
      let i19 ← pure ((.error i18) : Except Zig.ErrName (Zig.Slice))
      pure (.ret i19))
    | .ok v16 => (do
      let i21 ← pure v16.len
      let i22 ← pure (Zig.lt false p2 i21)
      match ← ((do
        if i22 then (do
          pure .br23)
        else (do
          throw .outOfBounds)) : Zig.CM Tgt Buf_u16_16_0_resizeLocals Buf_u16_16_0_resizeExit) with
      | .br23 => (do
        let i28 ← Zig.callMC (Zig.checkIndex v16.len p2) >>= fun _ => Zig.callMC (Zig.ptrProject v16.ptr (·.elem 2 p2))
        Zig.store (α := BitVec 16) 2 i28 (0 : BitVec 16)
        let i30 ← pure v16.ptr
        let i31 ← pure i30
        let i32 ← Zig.sub false p2 (0 : BitVec 64) (safe := false)
        let i33 ← pure v16.len
        let i34 ← Zig.add false p2 (1 : BitVec 64)
        let i35 ← pure (Zig.le false i34 i33)
        match ← ((do
          if i35 then (do
            pure .br36)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt Buf_u16_16_0_resizeLocals Buf_u16_16_0_resizeExit) with
        | .br36 => (do
          let i41 ← Zig.callMC (Zig.checkSliceEnd v16.len (0 : BitVec 64) i32 1 >>= fun _ => pure (⟨i31, i32⟩ : Zig.Slice))
          let i42 ← Zig.callMC (Zig.checkSentinelIndex i41.len i32 >>= fun _ => Zig.load (BitVec 16) 2 (i41.ptr.elem 2 i32))
          let i43 ← pure ((0 : BitVec 16) == i42)
          match ← ((do
            if i43 then (do
              pure .br44)
            else (do
              throw .panic)) : Zig.CM Tgt Buf_u16_16_0_resizeLocals Buf_u16_16_0_resizeExit) with
          | .br44 => (do
            let i49 ← pure ((.ok i41) : Except Zig.ErrName (Zig.Slice))
            pure (.ret i49))
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf_u16_16_0_resizeLocals Buf_u16_16_0_resizeExit).run' (default : Buf_u16_16_0_resizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u16_16_0_resize

structure mem_Allocator_allocBytesAligned__anon_0618802aa46aLocals where
  deriving Inhabited

inductive mem_Allocator_allocBytesAligned__anon_0618802aa46aExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3
  | br10 (v : Option (Zig.Ptr))
  | br9 (v : Zig.Ptr)

def mem_Allocator_allocBytesAligned__anon_0618802aa46a [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (⟨none, 18446744073709551615⟩ : Zig.Ptr) : Except Zig.ErrName (Zig.Ptr))))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_0618802aa46aLocals mem_Allocator_allocBytesAligned__anon_0618802aa46aExit) with
    | .br3 => (do
      match ← ((do
        match ← ((do
          let i11 ← pure ((p0).vtable)
          let i12 ← pure i11
          let i13 ← Zig.load (Zig.Ptr) 8 i12
          let i14 ← pure ((p0).ptr)
          let i15 ← (Zig.callC (Zig.extCall (Ext.call0 i13 i14 p1 mem_Alignment.«1» p2)))
          pure (.br10 i15)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_0618802aa46aLocals mem_Allocator_allocBytesAligned__anon_0618802aa46aExit) with
        | .br10 v10 => (do
          let i17 ← pure ((v10).isSome)
          if i17 then (do
            let i19 ← Zig.optPayload v10
            pure (.br9 i19))
          else (do
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr)))))
        | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_0618802aa46aLocals mem_Allocator_allocBytesAligned__anon_0618802aa46aExit) with
      | .br9 v9 => (do
        let i22 ← pure v9
        let i23 ← Zig.sub false p1 (0 : BitVec 64) (safe := false)
        let i24 ← pure (⟨i22, i23⟩ : Zig.Slice)
        let _i25 ← pure i24.len
        Zig.callMC (Zig.memset (α := BitVec 8) 1 i24.ptr i24.len none)
        let i27 ← pure (v9)
        let i28 ← pure ((.ok i27) : Except Zig.ErrName (Zig.Ptr))
        pure (.ret i28))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_0618802aa46aLocals mem_Allocator_allocBytesAligned__anon_0618802aa46aExit).run' (default : mem_Allocator_allocBytesAligned__anon_0618802aa46aLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocBytesAligned__anon_0618802aa46a

structure mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Locals where
  deriving Inhabited

inductive mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3 (v : BitVec 64)

def mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.callRC (math_mul__anon_44faaf286c79 (1 : BitVec 64) p1)
      let i5 ← pure (Zig.isNonErr i4)
      if i5 then (do
        let i7 ← Zig.callRC (Zig.unwrapPayload i4)
        pure (.br3 i7))
      else (do
        let _i9 ← Zig.callRC (Zig.unwrapErr i4)
        pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr))))) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Locals mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Exit) with
    | .br3 v3 => (do
      let i11 ← Zig.callC (mem_Allocator_allocBytesAligned__anon_0618802aa46a p0 v3 p2)
      pure (.ret i11))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Locals mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Exit).run' (default : mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43

structure mem_absorbSentinel__anon_8ef8ffcd60ecLocals where
  deriving Inhabited

inductive mem_absorbSentinel__anon_8ef8ffcd60ecExit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_8ef8ffcd60ec (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret p0)) : Zig.MM mem_absorbSentinel__anon_8ef8ffcd60ecLocals mem_absorbSentinel__anon_8ef8ffcd60ecExit).run' (default : mem_absorbSentinel__anon_8ef8ffcd60ecLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_absorbSentinel__anon_8ef8ffcd60ec

structure mem_Allocator_free__anon_bb76a5a4c9e4Locals where
  deriving Inhabited

inductive mem_Allocator_free__anon_bb76a5a4c9e4Exit where
  | ret
  | br4
  | br15

def mem_Allocator_free__anon_bb76a5a4c9e4 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_8ef8ffcd60ec p1)
    let i3 ← pure (i2)
    match ← ((do
      let i5 ← pure i3.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        pure .ret)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_free__anon_bb76a5a4c9e4Locals mem_Allocator_free__anon_bb76a5a4c9e4Exit) with
    | .br4 => (do
      let _i11 ← pure i3.len
      Zig.callMC (Zig.memset (α := BitVec 8) 1 i3.ptr i3.len none)
      let i13 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
      let i14 ← Zig.callMC Zig.returnAddress
      match ← ((do
        let i16 ← pure ((p0).vtable)
        let i17 ← Zig.callMC (Zig.ptrProject i16 (·.add 24))
        let i18 ← Zig.load (Zig.Ptr) 8 i17
        let i19 ← pure ((p0).ptr)
        let _i20 ← (Zig.callC (Zig.extCall (Ext.call2 i18 i19 i3 i13 i14)))
        pure .br15) : Zig.CM Tgt mem_Allocator_free__anon_bb76a5a4c9e4Locals mem_Allocator_free__anon_bb76a5a4c9e4Exit) with
      | .br15 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_bb76a5a4c9e4Locals mem_Allocator_free__anon_bb76a5a4c9e4Exit).run' (default : mem_Allocator_free__anon_bb76a5a4c9e4Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_bb76a5a4c9e4

structure mem_Allocator_reallocAdvanced__anon_32dbc0401d86Locals where
  deriving Inhabited

inductive mem_Allocator_reallocAdvanced__anon_32dbc0401d86Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br9 (v : Except Zig.ErrName (Zig.Slice))
  | br4
  | br22
  | br31 (v : BitVec 64)
  | br41 (v : Option (Zig.Ptr))
  | br39
  | br60 (v : Option (Zig.Ptr))
  | br58 (v : Zig.Ptr)
  | br86
  | br95
  | br107
  | br116

def mem_Allocator_reallocAdvanced__anon_32dbc0401d86 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) (p3 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    match ← ((do
      let i5 ← pure p1.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        match ← ((do
          let i10 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43 p0 p2 p3)
          match i10 with
          | .error _ => (do
            let i12 ← Zig.callRC (Zig.unwrapErr i10)
            let i13 ← pure ((.error i12) : Except Zig.ErrName (Zig.Slice))
            pure (.br9 i13))
          | .ok v11 => (do
            let i15 ← pure v11
            let i16 ← Zig.sub false p2 (0 : BitVec 64) (safe := false)
            let i17 ← pure (⟨i15, i16⟩ : Zig.Slice)
            let i18 ← pure ((.ok i17) : Except Zig.ErrName (Zig.Slice))
            pure (.br9 i18))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_32dbc0401d86Locals mem_Allocator_reallocAdvanced__anon_32dbc0401d86Exit) with
        | .br9 v9 => (do
          pure (.ret v9))
        | e => pure e)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_32dbc0401d86Locals mem_Allocator_reallocAdvanced__anon_32dbc0401d86Exit) with
    | .br4 => (do
      match ← ((do
        let i23 ← pure (p2)
        let i24 ← pure (i23 == (0 : BitVec 64))
        if i24 then (do
          let _i26 ← Zig.callC (mem_Allocator_free__anon_bb76a5a4c9e4 p0 p1)
          pure (.ret (.ok (⟨(⟨none, 18446744073709551615⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice) : Except Zig.ErrName (Zig.Slice))))
        else (do
          pure .br22)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_32dbc0401d86Locals mem_Allocator_reallocAdvanced__anon_32dbc0401d86Exit) with
      | .br22 => (do
        let i29 ← Zig.callMC (mem_absorbSentinel__anon_8ef8ffcd60ec p1)
        let i30 ← pure (i29)
        match ← ((do
          let i32 ← Zig.callRC (math_mul__anon_44faaf286c79 (1 : BitVec 64) p2)
          let i33 ← pure (Zig.isNonErr i32)
          if i33 then (do
            let i35 ← Zig.callRC (Zig.unwrapPayload i32)
            pure (.br31 i35))
          else (do
            let _i37 ← Zig.callRC (Zig.unwrapErr i32)
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice))))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_32dbc0401d86Locals mem_Allocator_reallocAdvanced__anon_32dbc0401d86Exit) with
        | .br31 v31 => (do
          match ← ((do
            let i40 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
            match ← ((do
              let i42 ← pure ((p0).vtable)
              let i43 ← Zig.callMC (Zig.ptrProject i42 (·.add 16))
              let i44 ← Zig.load (Zig.Ptr) 8 i43
              let i45 ← pure ((p0).ptr)
              let i46 ← (Zig.callC (Zig.extCall (Ext.call1 i44 i45 i30 i40 v31 p3)))
              pure (.br41 i46)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_32dbc0401d86Locals mem_Allocator_reallocAdvanced__anon_32dbc0401d86Exit) with
            | .br41 v41 => (do
              let i48 ← pure ((v41).isSome)
              if i48 then (do
                let i50 ← Zig.optPayload v41
                let i51 ← pure i50
                let i52 ← Zig.sub false v31 (0 : BitVec 64) (safe := false)
                let i53 ← pure (⟨i51, i52⟩ : Zig.Slice)
                let i54 ← pure (i53)
                let i55 ← pure ((.ok i54) : Except Zig.ErrName (Zig.Slice))
                pure (.ret i55))
              else (do
                pure .br39))
            | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_32dbc0401d86Locals mem_Allocator_reallocAdvanced__anon_32dbc0401d86Exit) with
          | .br39 => (do
            match ← ((do
              let i59 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
              match ← ((do
                let i61 ← pure ((p0).vtable)
                let i62 ← pure i61
                let i63 ← Zig.load (Zig.Ptr) 8 i62
                let i64 ← pure ((p0).ptr)
                let i65 ← (Zig.callC (Zig.extCall (Ext.call0 i63 i64 v31 i59 p3)))
                pure (.br60 i65)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_32dbc0401d86Locals mem_Allocator_reallocAdvanced__anon_32dbc0401d86Exit) with
              | .br60 v60 => (do
                let i67 ← pure ((v60).isSome)
                if i67 then (do
                  let i69 ← Zig.optPayload v60
                  pure (.br58 i69))
                else (do
                  pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice)))))
              | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_32dbc0401d86Locals mem_Allocator_reallocAdvanced__anon_32dbc0401d86Exit) with
            | .br58 v58 => (do
              let i72 ← pure i30.len
              let i73 ← pure (v31)
              let i74 ← pure (i72)
              let i75 ← pure (Zig.min false i73 i74)
              let i76 ← pure v58
              let i77 ← pure (i75)
              let i78 ← Zig.sub false i77 (0 : BitVec 64) (safe := false)
              let i79 ← pure (⟨i76, i78⟩ : Zig.Slice)
              let i80 ← pure i30.ptr
              let i81 ← pure i80
              let i82 ← pure (i75)
              let i83 ← Zig.sub false i82 (0 : BitVec 64) (safe := false)
              let i84 ← pure i30.len
              let i85 ← pure (Zig.le false i82 i84)
              match ← ((do
                if i85 then (do
                  pure .br86)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_32dbc0401d86Locals mem_Allocator_reallocAdvanced__anon_32dbc0401d86Exit) with
              | .br86 => (do
                let i91 ← Zig.callMC (Zig.checkSliceEnd i30.len (0 : BitVec 64) i83 0 >>= fun _ => pure (⟨i81, i83⟩ : Zig.Slice))
                let i92 ← pure i79.len
                let i93 ← pure i91.len
                let i94 ← pure (i92 == i93)
                match ← ((do
                  if i94 then (do
                    pure .br95)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_32dbc0401d86Locals mem_Allocator_reallocAdvanced__anon_32dbc0401d86Exit) with
                | .br95 => (do
                  let i100 ← pure i91.ptr
                  let i101 ← pure i79.ptr
                  let i102 ← Zig.callMC (Zig.ptrProject i100 (·.elem 1 i92))
                  let i103 ← Zig.callMC (Zig.ptrProject i101 (·.elem 1 i92))
                  let i104 ← Zig.callMC (Zig.ptrLe i102 i101)
                  let i105 ← Zig.callMC (Zig.ptrLe i103 i100)
                  let i106 ← pure (i104 || i105)
                  match ← ((do
                    if i106 then (do
                      pure .br107)
                    else (do
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_32dbc0401d86Locals mem_Allocator_reallocAdvanced__anon_32dbc0401d86Exit) with
                  | .br107 => (do
                    Zig.callMC (Zig.memcpy 1 1 1 i79.ptr i100 i79.len i91.len)
                    let _i113 ← pure i30.len
                    Zig.callMC (Zig.memset (α := BitVec 8) 1 i30.ptr i30.len none)
                    let i115 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
                    match ← ((do
                      let i117 ← pure ((p0).vtable)
                      let i118 ← Zig.callMC (Zig.ptrProject i117 (·.add 24))
                      let i119 ← Zig.load (Zig.Ptr) 8 i118
                      let i120 ← pure ((p0).ptr)
                      let _i121 ← (Zig.callC (Zig.extCall (Ext.call2 i119 i120 i30 i115 p3)))
                      pure .br116) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_32dbc0401d86Locals mem_Allocator_reallocAdvanced__anon_32dbc0401d86Exit) with
                    | .br116 => (do
                      let i123 ← pure v58
                      let i124 ← Zig.sub false v31 (0 : BitVec 64) (safe := false)
                      let i125 ← pure (⟨i123, i124⟩ : Zig.Slice)
                      let i126 ← pure (i125)
                      let i127 ← pure ((.ok i126) : Except Zig.ErrName (Zig.Slice))
                      pure (.ret i127))
                    | e => pure e)
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_32dbc0401d86Locals mem_Allocator_reallocAdvanced__anon_32dbc0401d86Exit).run' (default : mem_Allocator_reallocAdvanced__anon_32dbc0401d86Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_reallocAdvanced__anon_32dbc0401d86

structure mem_Allocator_realloc__anon_5031d4b18b8eLocals where
  deriving Inhabited

inductive mem_Allocator_realloc__anon_5031d4b18b8eExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_realloc__anon_5031d4b18b8e [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.callMC Zig.returnAddress
    let i4 ← Zig.callC (mem_Allocator_reallocAdvanced__anon_32dbc0401d86 p0 p1 p2 i3)
    pure (.ret i4)) : Zig.CM Tgt mem_Allocator_realloc__anon_5031d4b18b8eLocals mem_Allocator_realloc__anon_5031d4b18b8eExit).run' (default : mem_Allocator_realloc__anon_5031d4b18b8eLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_realloc__anon_5031d4b18b8e

structure Buf_u8_1_255_appendLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive Buf_u8_1_255_appendExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br27
  | br39
  | br55
  | br63

def Buf_u8_1_255_append [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 8) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    modify (fun s => { s with local3 := p1 })
    let i8 ← pure (((← get).local3).len)
    let i9 ← Zig.add false i8 (1 : BitVec 64)
    let i10 ← pure (((← get).local3).ptr)
    let i11 ← pure i10
    let i12 ← Zig.sub false i9 (0 : BitVec 64) (safe := false)
    let i13 ← pure (⟨i11, i12⟩ : Zig.Slice)
    let i15 ← pure (((← get).local3).len)
    let i16 ← Zig.add false i15 (2 : BitVec 64)
    let i17 ← Zig.callC (mem_Allocator_realloc__anon_5031d4b18b8e p0 i13 i16)
    match i17 with
    | .error _ => (do
      let i19 ← Zig.callRC (Zig.unwrapErr i17)
      let i20 ← pure (i19)
      let i21 ← pure ((.error i20) : Except Zig.ErrName (Zig.Slice))
      pure (.ret i21))
    | .ok v18 => (do
      let i24 ← pure (((← get).local3).len)
      let i25 ← pure v18.len
      let i26 ← pure (Zig.lt false i24 i25)
      match ← ((do
        if i26 then (do
          pure .br27)
        else (do
          throw .outOfBounds)) : Zig.CM Tgt Buf_u8_1_255_appendLocals Buf_u8_1_255_appendExit) with
      | .br27 => (do
        let i32 ← Zig.callMC (Zig.checkIndex v18.len i24) >>= fun _ => Zig.callMC (Zig.ptrProject v18.ptr (·.elem 1 i24))
        Zig.store (α := BitVec 8) 1 i32 p2
        let i35 ← pure (((← get).local3).len)
        let i36 ← Zig.add false i35 (1 : BitVec 64)
        let i37 ← pure v18.len
        let i38 ← pure (Zig.lt false i36 i37)
        match ← ((do
          if i38 then (do
            pure .br39)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt Buf_u8_1_255_appendLocals Buf_u8_1_255_appendExit) with
        | .br39 => (do
          let i44 ← Zig.callMC (Zig.checkIndex v18.len i36) >>= fun _ => Zig.callMC (Zig.ptrProject v18.ptr (·.elem 1 i36))
          Zig.store (α := BitVec 8) 1 i44 (255 : BitVec 8)
          let i47 ← pure (((← get).local3).len)
          let i48 ← Zig.add false i47 (1 : BitVec 64)
          let i49 ← pure v18.ptr
          let i50 ← pure i49
          let i51 ← Zig.sub false i48 (0 : BitVec 64) (safe := false)
          let i52 ← pure v18.len
          let i53 ← Zig.add false i48 (1 : BitVec 64)
          let i54 ← pure (Zig.le false i53 i52)
          match ← ((do
            if i54 then (do
              pure .br55)
            else (do
              throw .outOfBounds)) : Zig.CM Tgt Buf_u8_1_255_appendLocals Buf_u8_1_255_appendExit) with
          | .br55 => (do
            let i60 ← Zig.callMC (Zig.checkSliceEnd v18.len (0 : BitVec 64) i51 1 >>= fun _ => pure (⟨i50, i51⟩ : Zig.Slice))
            let i61 ← Zig.callMC (Zig.checkSentinelIndex i60.len i51 >>= fun _ => Zig.load (BitVec 8) 1 (i60.ptr.elem 1 i51))
            let i62 ← pure ((255 : BitVec 8) == i61)
            match ← ((do
              if i62 then (do
                pure .br63)
              else (do
                throw .panic)) : Zig.CM Tgt Buf_u8_1_255_appendLocals Buf_u8_1_255_appendExit) with
            | .br63 => (do
              let i68 ← pure ((.ok i60) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i68))
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf_u8_1_255_appendLocals Buf_u8_1_255_appendExit).run' (default : Buf_u8_1_255_appendLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u8_1_255_append

structure mem_Allocator_allocWithOptionsRetAddr__anon_207db0a67bb1Locals where
  deriving Inhabited

inductive mem_Allocator_allocWithOptionsRetAddr__anon_207db0a67bb1Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br4 (v : Except Zig.ErrName (Zig.Slice))
  | br21
  | br34
  | br42

def mem_Allocator_allocWithOptionsRetAddr__anon_207db0a67bb1 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.add false p1 (1 : BitVec 64)
    match ← ((do
      let i5 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43 p0 i3 p2)
      match i5 with
      | .error _ => (do
        let i7 ← Zig.callRC (Zig.unwrapErr i5)
        let i8 ← pure ((.error i7) : Except Zig.ErrName (Zig.Slice))
        pure (.br4 i8))
      | .ok v6 => (do
        let i10 ← pure v6
        let i11 ← Zig.sub false i3 (0 : BitVec 64) (safe := false)
        let i12 ← pure (⟨i10, i11⟩ : Zig.Slice)
        let i13 ← pure ((.ok i12) : Except Zig.ErrName (Zig.Slice))
        pure (.br4 i13))) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_207db0a67bb1Locals mem_Allocator_allocWithOptionsRetAddr__anon_207db0a67bb1Exit) with
    | .br4 v4 => (do
      match v4 with
      | .error _ => (do
        let i16 ← Zig.callRC (Zig.unwrapErr v4)
        let i17 ← pure ((.error i16) : Except Zig.ErrName (Zig.Slice))
        pure (.ret i17))
      | .ok v15 => (do
        let i19 ← pure v15.len
        let i20 ← pure (Zig.lt false p1 i19)
        match ← ((do
          if i20 then (do
            pure .br21)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_207db0a67bb1Locals mem_Allocator_allocWithOptionsRetAddr__anon_207db0a67bb1Exit) with
        | .br21 => (do
          let i26 ← Zig.callMC (Zig.checkIndex v15.len p1) >>= fun _ => Zig.callMC (Zig.ptrProject v15.ptr (·.elem 1 p1))
          Zig.store (α := BitVec 8) 1 i26 (255 : BitVec 8)
          let i28 ← pure v15.ptr
          let i29 ← pure i28
          let i30 ← Zig.sub false p1 (0 : BitVec 64) (safe := false)
          let i31 ← pure v15.len
          let i32 ← Zig.add false p1 (1 : BitVec 64)
          let i33 ← pure (Zig.le false i32 i31)
          match ← ((do
            if i33 then (do
              pure .br34)
            else (do
              throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_207db0a67bb1Locals mem_Allocator_allocWithOptionsRetAddr__anon_207db0a67bb1Exit) with
          | .br34 => (do
            let i39 ← Zig.callMC (Zig.checkSliceEnd v15.len (0 : BitVec 64) i30 1 >>= fun _ => pure (⟨i29, i30⟩ : Zig.Slice))
            let i40 ← Zig.callMC (Zig.checkSentinelIndex i39.len i30 >>= fun _ => Zig.load (BitVec 8) 1 (i39.ptr.elem 1 i30))
            let i41 ← pure ((255 : BitVec 8) == i40)
            match ← ((do
              if i41 then (do
                pure .br42)
              else (do
                throw .panic)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_207db0a67bb1Locals mem_Allocator_allocWithOptionsRetAddr__anon_207db0a67bb1Exit) with
            | .br42 => (do
              let i47 ← pure ((.ok i39) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i47))
            | e => pure e)
          | e => pure e)
        | e => pure e))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_207db0a67bb1Locals mem_Allocator_allocWithOptionsRetAddr__anon_207db0a67bb1Exit).run' (default : mem_Allocator_allocWithOptionsRetAddr__anon_207db0a67bb1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocWithOptionsRetAddr__anon_207db0a67bb1

structure mem_Allocator_allocSentinel__anon_97678a214f72Locals where
  local4 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_allocSentinel__anon_97678a214f72Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_allocSentinel__anon_97678a214f72 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s4 ← Zig.allocStack 24 8
  let e ← ((do
    let i2 ← Zig.callMC Zig.returnAddress
    let i3 ← Zig.callC (mem_Allocator_allocWithOptionsRetAddr__anon_207db0a67bb1 p0 p1 i2)
    let i4 ← pure (← get).local4
    (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i4 i3)
    let i6 ← pure (i4)
    let i7 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i6)
    pure (.ret i7)) : Zig.CM Tgt mem_Allocator_allocSentinel__anon_97678a214f72Locals mem_Allocator_allocSentinel__anon_97678a214f72Exit).run' { (default : mem_Allocator_allocSentinel__anon_97678a214f72Locals) with local4 := s4 }
  Zig.free s4
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_allocSentinel__anon_97678a214f72

structure Buf_u8_1_255_makeLocals where
  local3 : Zig.Ptr
  deriving Inhabited

inductive Buf_u8_1_255_makeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def Buf_u8_1_255_make [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s3 ← Zig.allocStack 24 8
  let e ← ((do
    let i2 ← Zig.callC (mem_Allocator_allocSentinel__anon_97678a214f72 p0 p1)
    let i3 ← pure (← get).local3
    (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i3 i2)
    let i5 ← pure (i3)
    let i6 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i5)
    pure (.ret i6)) : Zig.CM Tgt Buf_u8_1_255_makeLocals Buf_u8_1_255_makeExit).run' { (default : Buf_u8_1_255_makeLocals) with local3 := s3 }
  Zig.free s3
  match e with
  | .ret v => pure v

attribute [zig_run] Buf_u8_1_255_make

structure mem_absorbSentinel__anon_cd37df708c8eLocals where
  local1 : Zig.Slice
  deriving Inhabited

inductive mem_absorbSentinel__anon_cd37df708c8eExit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_cd37df708c8e (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    modify (fun s => { s with local1 := p0 })
    let i6 ← pure (((← get).local1).len)
    let i7 ← Zig.add false i6 (1 : BitVec 64)
    let i8 ← pure (((← get).local1).ptr)
    let i9 ← pure i8
    let i10 ← Zig.sub false i7 (0 : BitVec 64) (safe := false)
    let i11 ← pure (⟨i9, i10⟩ : Zig.Slice)
    pure (.ret i11)) : Zig.MM mem_absorbSentinel__anon_cd37df708c8eLocals mem_absorbSentinel__anon_cd37df708c8eExit).run' (default : mem_absorbSentinel__anon_cd37df708c8eLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_absorbSentinel__anon_cd37df708c8e

structure mem_Allocator_free__anon_fe989e6b0260Locals where
  deriving Inhabited

inductive mem_Allocator_free__anon_fe989e6b0260Exit where
  | ret
  | br4
  | br15

def mem_Allocator_free__anon_fe989e6b0260 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_cd37df708c8e p1)
    let i3 ← pure (i2)
    match ← ((do
      let i5 ← pure i3.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        pure .ret)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_free__anon_fe989e6b0260Locals mem_Allocator_free__anon_fe989e6b0260Exit) with
    | .br4 => (do
      let _i11 ← pure i3.len
      Zig.callMC (Zig.memset (α := BitVec 8) 1 i3.ptr i3.len none)
      let i13 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
      let i14 ← Zig.callMC Zig.returnAddress
      match ← ((do
        let i16 ← pure ((p0).vtable)
        let i17 ← Zig.callMC (Zig.ptrProject i16 (·.add 24))
        let i18 ← Zig.load (Zig.Ptr) 8 i17
        let i19 ← pure ((p0).ptr)
        let _i20 ← (Zig.callC (Zig.extCall (Ext.call2 i18 i19 i3 i13 i14)))
        pure .br15) : Zig.CM Tgt mem_Allocator_free__anon_fe989e6b0260Locals mem_Allocator_free__anon_fe989e6b0260Exit) with
      | .br15 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_fe989e6b0260Locals mem_Allocator_free__anon_fe989e6b0260Exit).run' (default : mem_Allocator_free__anon_fe989e6b0260Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_fe989e6b0260

structure Buf_u8_1_255_releaseLocals where
  deriving Inhabited

inductive Buf_u8_1_255_releaseExit where
  | ret

def Buf_u8_1_255_release [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let _i2 ← Zig.callC (mem_Allocator_free__anon_fe989e6b0260 p0 p1)
    pure .ret) : Zig.CM Tgt Buf_u8_1_255_releaseLocals Buf_u8_1_255_releaseExit).run' (default : Buf_u8_1_255_releaseLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Buf_u8_1_255_release

structure Buf_u8_1_255_resizeLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive Buf_u8_1_255_resizeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br23
  | br36
  | br44

def Buf_u8_1_255_resize [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    modify (fun s => { s with local3 := p1 })
    let i8 ← pure (((← get).local3).len)
    let i9 ← Zig.add false i8 (1 : BitVec 64)
    let i10 ← pure (((← get).local3).ptr)
    let i11 ← pure i10
    let i12 ← Zig.sub false i9 (0 : BitVec 64) (safe := false)
    let i13 ← pure (⟨i11, i12⟩ : Zig.Slice)
    let i14 ← Zig.add false p2 (1 : BitVec 64)
    let i15 ← Zig.callC (mem_Allocator_realloc__anon_5031d4b18b8e p0 i13 i14)
    match i15 with
    | .error _ => (do
      let i17 ← Zig.callRC (Zig.unwrapErr i15)
      let i18 ← pure (i17)
      let i19 ← pure ((.error i18) : Except Zig.ErrName (Zig.Slice))
      pure (.ret i19))
    | .ok v16 => (do
      let i21 ← pure v16.len
      let i22 ← pure (Zig.lt false p2 i21)
      match ← ((do
        if i22 then (do
          pure .br23)
        else (do
          throw .outOfBounds)) : Zig.CM Tgt Buf_u8_1_255_resizeLocals Buf_u8_1_255_resizeExit) with
      | .br23 => (do
        let i28 ← Zig.callMC (Zig.checkIndex v16.len p2) >>= fun _ => Zig.callMC (Zig.ptrProject v16.ptr (·.elem 1 p2))
        Zig.store (α := BitVec 8) 1 i28 (255 : BitVec 8)
        let i30 ← pure v16.ptr
        let i31 ← pure i30
        let i32 ← Zig.sub false p2 (0 : BitVec 64) (safe := false)
        let i33 ← pure v16.len
        let i34 ← Zig.add false p2 (1 : BitVec 64)
        let i35 ← pure (Zig.le false i34 i33)
        match ← ((do
          if i35 then (do
            pure .br36)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt Buf_u8_1_255_resizeLocals Buf_u8_1_255_resizeExit) with
        | .br36 => (do
          let i41 ← Zig.callMC (Zig.checkSliceEnd v16.len (0 : BitVec 64) i32 1 >>= fun _ => pure (⟨i31, i32⟩ : Zig.Slice))
          let i42 ← Zig.callMC (Zig.checkSentinelIndex i41.len i32 >>= fun _ => Zig.load (BitVec 8) 1 (i41.ptr.elem 1 i32))
          let i43 ← pure ((255 : BitVec 8) == i42)
          match ← ((do
            if i43 then (do
              pure .br44)
            else (do
              throw .panic)) : Zig.CM Tgt Buf_u8_1_255_resizeLocals Buf_u8_1_255_resizeExit) with
          | .br44 => (do
            let i49 ← pure ((.ok i41) : Except Zig.ErrName (Zig.Slice))
            pure (.ret i49))
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf_u8_1_255_resizeLocals Buf_u8_1_255_resizeExit).run' (default : Buf_u8_1_255_resizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u8_1_255_resize

structure mem_Allocator_alloc__anon_a8254a5f2b74Locals where
  local14 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_alloc__anon_a8254a5f2b74Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br3 (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_alloc__anon_a8254a5f2b74 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s14 ← Zig.allocStack 24 8
  let e ← ((do
    let i2 ← Zig.callMC Zig.returnAddress
    match ← ((do
      let i4 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43 p0 p1 i2)
      match i4 with
      | .error _ => (do
        let i6 ← Zig.callRC (Zig.unwrapErr i4)
        let i7 ← pure ((.error i6) : Except Zig.ErrName (Zig.Slice))
        pure (.br3 i7))
      | .ok v5 => (do
        let i9 ← pure v5
        let i10 ← Zig.sub false p1 (0 : BitVec 64) (safe := false)
        let i11 ← pure (⟨i9, i10⟩ : Zig.Slice)
        let i12 ← pure ((.ok i11) : Except Zig.ErrName (Zig.Slice))
        pure (.br3 i12))) : Zig.CM Tgt mem_Allocator_alloc__anon_a8254a5f2b74Locals mem_Allocator_alloc__anon_a8254a5f2b74Exit) with
    | .br3 v3 => (do
      let i14 ← pure (← get).local14
      (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i14 v3)
      let i16 ← pure (i14)
      let i17 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i16)
      pure (.ret i17))
    | e => pure e) : Zig.CM Tgt mem_Allocator_alloc__anon_a8254a5f2b74Locals mem_Allocator_alloc__anon_a8254a5f2b74Exit).run' { (default : mem_Allocator_alloc__anon_a8254a5f2b74Locals) with local14 := s14 }
  Zig.free s14
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_alloc__anon_a8254a5f2b74

structure mem_Allocator_dupeSentinel__anon_294b7c9823bdLocals where
  deriving Inhabited

inductive mem_Allocator_dupeSentinel__anon_294b7c9823bdExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br15
  | br24
  | br36
  | br45
  | br59
  | br67

def mem_Allocator_dupeSentinel__anon_294b7c9823bd [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← pure p1.len
    let i3 ← Zig.add false i2 (1 : BitVec 64)
    let i4 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 p0 i3)
    match i4 with
    | .error _ => (do
      let i6 ← Zig.callRC (Zig.unwrapErr i4)
      let i7 ← pure ((.error i6) : Except Zig.ErrName (Zig.Slice))
      pure (.ret i7))
    | .ok v5 => (do
      let i9 ← pure p1.len
      let i10 ← pure v5.ptr
      let i11 ← pure i10
      let i12 ← Zig.sub false i9 (0 : BitVec 64) (safe := false)
      let i13 ← pure v5.len
      let i14 ← pure (Zig.le false i9 i13)
      match ← ((do
        if i14 then (do
          pure .br15)
        else (do
          throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_dupeSentinel__anon_294b7c9823bdLocals mem_Allocator_dupeSentinel__anon_294b7c9823bdExit) with
      | .br15 => (do
        let i20 ← Zig.callMC (Zig.checkSliceEnd v5.len (0 : BitVec 64) i12 0 >>= fun _ => pure (⟨i11, i12⟩ : Zig.Slice))
        let i21 ← pure i20.len
        let i22 ← pure p1.len
        let i23 ← pure (i21 == i22)
        match ← ((do
          if i23 then (do
            pure .br24)
          else (do
            throw .panic)) : Zig.CM Tgt mem_Allocator_dupeSentinel__anon_294b7c9823bdLocals mem_Allocator_dupeSentinel__anon_294b7c9823bdExit) with
        | .br24 => (do
          let i29 ← pure p1.ptr
          let i30 ← pure i20.ptr
          let i31 ← Zig.callMC (Zig.ptrProject i29 (·.elem 1 i21))
          let i32 ← Zig.callMC (Zig.ptrProject i30 (·.elem 1 i21))
          let i33 ← Zig.callMC (Zig.ptrLe i31 i30)
          let i34 ← Zig.callMC (Zig.ptrLe i32 i29)
          let i35 ← pure (i33 || i34)
          match ← ((do
            if i35 then (do
              pure .br36)
            else (do
              throw .panic)) : Zig.CM Tgt mem_Allocator_dupeSentinel__anon_294b7c9823bdLocals mem_Allocator_dupeSentinel__anon_294b7c9823bdExit) with
          | .br36 => (do
            Zig.callMC (Zig.memcpy 1 1 1 i20.ptr i29 i20.len p1.len)
            let i42 ← pure p1.len
            let i43 ← pure v5.len
            let i44 ← pure (Zig.lt false i42 i43)
            match ← ((do
              if i44 then (do
                pure .br45)
              else (do
                throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_dupeSentinel__anon_294b7c9823bdLocals mem_Allocator_dupeSentinel__anon_294b7c9823bdExit) with
            | .br45 => (do
              let i50 ← Zig.callMC (Zig.checkIndex v5.len i42) >>= fun _ => Zig.callMC (Zig.ptrProject v5.ptr (·.elem 1 i42))
              Zig.store (α := BitVec 8) 1 i50 (0 : BitVec 8)
              let i52 ← pure p1.len
              let i53 ← pure v5.ptr
              let i54 ← pure i53
              let i55 ← Zig.sub false i52 (0 : BitVec 64) (safe := false)
              let i56 ← pure v5.len
              let i57 ← Zig.add false i52 (1 : BitVec 64)
              let i58 ← pure (Zig.le false i57 i56)
              match ← ((do
                if i58 then (do
                  pure .br59)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_dupeSentinel__anon_294b7c9823bdLocals mem_Allocator_dupeSentinel__anon_294b7c9823bdExit) with
              | .br59 => (do
                let i64 ← Zig.callMC (Zig.checkSliceEnd v5.len (0 : BitVec 64) i55 1 >>= fun _ => pure (⟨i54, i55⟩ : Zig.Slice))
                let i65 ← Zig.callMC (Zig.checkSentinelIndex i64.len i55 >>= fun _ => Zig.load (BitVec 8) 1 (i64.ptr.elem 1 i55))
                let i66 ← pure ((0 : BitVec 8) == i65)
                match ← ((do
                  if i66 then (do
                    pure .br67)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_dupeSentinel__anon_294b7c9823bdLocals mem_Allocator_dupeSentinel__anon_294b7c9823bdExit) with
                | .br67 => (do
                  let i72 ← pure ((.ok i64) : Except Zig.ErrName (Zig.Slice))
                  pure (.ret i72))
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt mem_Allocator_dupeSentinel__anon_294b7c9823bdLocals mem_Allocator_dupeSentinel__anon_294b7c9823bdExit).run' (default : mem_Allocator_dupeSentinel__anon_294b7c9823bdLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_dupeSentinel__anon_294b7c9823bd

structure copyLocals where
  deriving Inhabited

inductive copyExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def copy [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.callC (mem_Allocator_dupeSentinel__anon_294b7c9823bd p0 p1)
    let i3 ← pure (i2)
    pure (.ret i3)) : Zig.CM Tgt copyLocals copyExit).run' (default : copyLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] copy

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch [Ext] : Tgt → Zig.ConcM Tgt Unit :=
  fun t => nomatch t

attribute [zig_run] dispatch

end Interfaces.Kinds