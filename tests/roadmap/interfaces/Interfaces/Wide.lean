-- air2lean-profile: {"allocator_model":"translated","correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.1"}}
-- air2lean-interfaces: {"ext":[{"field":"call0","type":"fn (*anyopaque, usize, mem.Alignment, usize) ?[*]u8"},{"field":"call1","type":"fn (*anyopaque, []u8, mem.Alignment, usize, usize) ?[*]u8"},{"field":"call2","type":"fn (*anyopaque, []u8, mem.Alignment, usize) void"}],"interfaces":[{"contract":"Zig.Full.CAllocSpec","interface":"std.mem.Allocator","premise":"EXT-05","struct":"mem.Allocator.VTable"}]}
import ZigLean


namespace Interfaces.Wide

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

structure mem_Allocator_allocBytesAligned__anon_99a2f0789fbdLocals where
  deriving Inhabited

inductive mem_Allocator_allocBytesAligned__anon_99a2f0789fbdExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3
  | br10 (v : Option (Zig.Ptr))
  | br9 (v : Zig.Ptr)
  | br30

def mem_Allocator_allocBytesAligned__anon_99a2f0789fbd [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (⟨none, 18446744073709551614⟩ : Zig.Ptr) : Except Zig.ErrName (Zig.Ptr))))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_99a2f0789fbdLocals mem_Allocator_allocBytesAligned__anon_99a2f0789fbdExit) with
    | .br3 => (do
      match ← ((do
        match ← ((do
          let i11 ← pure ((p0).vtable)
          let i12 ← pure i11
          let i13 ← Zig.load (Zig.Ptr) 8 i12
          let i14 ← pure ((p0).ptr)
          let i15 ← (Zig.callC (Zig.extCall (Ext.call0 i13 i14 p1 mem_Alignment.«2» p2)))
          pure (.br10 i15)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_99a2f0789fbdLocals mem_Allocator_allocBytesAligned__anon_99a2f0789fbdExit) with
        | .br10 v10 => (do
          let i17 ← pure ((v10).isSome)
          if i17 then (do
            let i19 ← Zig.optPayload v10
            pure (.br9 i19))
          else (do
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr)))))
        | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_99a2f0789fbdLocals mem_Allocator_allocBytesAligned__anon_99a2f0789fbdExit) with
      | .br9 v9 => (do
        let i22 ← pure v9
        let i23 ← Zig.sub false p1 (0 : BitVec 64) (safe := false)
        let i24 ← pure (⟨i22, i23⟩ : Zig.Slice)
        let _i25 ← pure i24.len
        Zig.callMC (Zig.memset (α := BitVec 8) 1 i24.ptr i24.len none)
        let i27 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr v9)))
        let i28 ← pure (i27 &&& (1 : BitVec 64))
        let i29 ← pure (i28 == (0 : BitVec 64))
        match ← ((do
          if i29 then (do
            pure .br30)
          else (do
            throw .panic)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_99a2f0789fbdLocals mem_Allocator_allocBytesAligned__anon_99a2f0789fbdExit) with
        | .br30 => (do
          let i35 ← Zig.callMC (Zig.checkAlign 2 v9 >>= fun _ => pure v9)
          let i36 ← pure ((.ok i35) : Except Zig.ErrName (Zig.Ptr))
          pure (.ret i36))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_99a2f0789fbdLocals mem_Allocator_allocBytesAligned__anon_99a2f0789fbdExit).run' (default : mem_Allocator_allocBytesAligned__anon_99a2f0789fbdLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocBytesAligned__anon_99a2f0789fbd

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

structure mem_Allocator_allocWithOptionsRetAddr__anon_60efb1dccf03Locals where
  deriving Inhabited

inductive mem_Allocator_allocWithOptionsRetAddr__anon_60efb1dccf03Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br4 (v : Except Zig.ErrName (Zig.Slice))
  | br22
  | br35
  | br43

def mem_Allocator_allocWithOptionsRetAddr__anon_60efb1dccf03 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
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
        pure (.br4 i14))) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_60efb1dccf03Locals mem_Allocator_allocWithOptionsRetAddr__anon_60efb1dccf03Exit) with
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
            throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_60efb1dccf03Locals mem_Allocator_allocWithOptionsRetAddr__anon_60efb1dccf03Exit) with
        | .br22 => (do
          let i27 ← Zig.callMC (Zig.checkIndex v16.len p1) >>= fun _ => Zig.callMC (Zig.ptrProject v16.ptr (·.elem 8 p1))
          Zig.store (α := BitVec 64) 8 i27 (0 : BitVec 64)
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
              throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_60efb1dccf03Locals mem_Allocator_allocWithOptionsRetAddr__anon_60efb1dccf03Exit) with
          | .br35 => (do
            let i40 ← Zig.callMC (Zig.checkSliceEnd v16.len (0 : BitVec 64) i31 1 >>= fun _ => pure (⟨i30, i31⟩ : Zig.Slice))
            let i41 ← Zig.callMC (Zig.checkSentinelIndex i40.len i31 >>= fun _ => Zig.load (BitVec 64) 8 (i40.ptr.elem 8 i31))
            let i42 ← pure ((0 : BitVec 64) == i41)
            match ← ((do
              if i42 then (do
                pure .br43)
              else (do
                throw .panic)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_60efb1dccf03Locals mem_Allocator_allocWithOptionsRetAddr__anon_60efb1dccf03Exit) with
            | .br43 => (do
              let i48 ← pure ((.ok i40) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i48))
            | e => pure e)
          | e => pure e)
        | e => pure e))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_60efb1dccf03Locals mem_Allocator_allocWithOptionsRetAddr__anon_60efb1dccf03Exit).run' (default : mem_Allocator_allocWithOptionsRetAddr__anon_60efb1dccf03Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocWithOptionsRetAddr__anon_60efb1dccf03

structure mem_Allocator_allocSentinel__anon_569668752178Locals where
  local4 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_allocSentinel__anon_569668752178Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_allocSentinel__anon_569668752178 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s4 ← Zig.allocStack 24 8
  let e ← ((do
    let i2 ← Zig.callMC Zig.returnAddress
    let i3 ← Zig.callC (mem_Allocator_allocWithOptionsRetAddr__anon_60efb1dccf03 p0 p1 i2)
    let i4 ← pure (← get).local4
    (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i4 i3)
    let i6 ← pure (i4)
    let i7 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i6)
    pure (.ret i7)) : Zig.CM Tgt mem_Allocator_allocSentinel__anon_569668752178Locals mem_Allocator_allocSentinel__anon_569668752178Exit).run' { (default : mem_Allocator_allocSentinel__anon_569668752178Locals) with local4 := s4 }
  Zig.free s4
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_allocSentinel__anon_569668752178

structure mem_Allocator_allocWithSizeAndAlignment__anon_e3d53c154a1bLocals where
  deriving Inhabited

inductive mem_Allocator_allocWithSizeAndAlignment__anon_e3d53c154a1bExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3 (v : BitVec 64)

def mem_Allocator_allocWithSizeAndAlignment__anon_e3d53c154a1b [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.callRC (math_mul__anon_44faaf286c79 (2 : BitVec 64) p1)
      let i5 ← pure (Zig.isNonErr i4)
      if i5 then (do
        let i7 ← Zig.callRC (Zig.unwrapPayload i4)
        pure (.br3 i7))
      else (do
        let _i9 ← Zig.callRC (Zig.unwrapErr i4)
        pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr))))) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_e3d53c154a1bLocals mem_Allocator_allocWithSizeAndAlignment__anon_e3d53c154a1bExit) with
    | .br3 v3 => (do
      let i11 ← Zig.callC (mem_Allocator_allocBytesAligned__anon_99a2f0789fbd p0 v3 p2)
      pure (.ret i11))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_e3d53c154a1bLocals mem_Allocator_allocWithSizeAndAlignment__anon_e3d53c154a1bExit).run' (default : mem_Allocator_allocWithSizeAndAlignment__anon_e3d53c154a1bLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocWithSizeAndAlignment__anon_e3d53c154a1b

structure mem_Allocator_allocWithOptionsRetAddr__anon_a1da89f8b5c5Locals where
  deriving Inhabited

inductive mem_Allocator_allocWithOptionsRetAddr__anon_a1da89f8b5c5Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br4 (v : Except Zig.ErrName (Zig.Slice))
  | br22
  | br35
  | br43

def mem_Allocator_allocWithOptionsRetAddr__anon_a1da89f8b5c5 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.add false p1 (1 : BitVec 64)
    match ← ((do
      let i5 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_e3d53c154a1b p0 i3 p2)
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
        pure (.br4 i14))) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_a1da89f8b5c5Locals mem_Allocator_allocWithOptionsRetAddr__anon_a1da89f8b5c5Exit) with
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
            throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_a1da89f8b5c5Locals mem_Allocator_allocWithOptionsRetAddr__anon_a1da89f8b5c5Exit) with
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
              throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_a1da89f8b5c5Locals mem_Allocator_allocWithOptionsRetAddr__anon_a1da89f8b5c5Exit) with
          | .br35 => (do
            let i40 ← Zig.callMC (Zig.checkSliceEnd v16.len (0 : BitVec 64) i31 1 >>= fun _ => pure (⟨i30, i31⟩ : Zig.Slice))
            let i41 ← Zig.callMC (Zig.checkSentinelIndex i40.len i31 >>= fun _ => Zig.load (BitVec 16) 2 (i40.ptr.elem 2 i31))
            let i42 ← pure ((0 : BitVec 16) == i41)
            match ← ((do
              if i42 then (do
                pure .br43)
              else (do
                throw .panic)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_a1da89f8b5c5Locals mem_Allocator_allocWithOptionsRetAddr__anon_a1da89f8b5c5Exit) with
            | .br43 => (do
              let i48 ← pure ((.ok i40) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i48))
            | e => pure e)
          | e => pure e)
        | e => pure e))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_a1da89f8b5c5Locals mem_Allocator_allocWithOptionsRetAddr__anon_a1da89f8b5c5Exit).run' (default : mem_Allocator_allocWithOptionsRetAddr__anon_a1da89f8b5c5Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocWithOptionsRetAddr__anon_a1da89f8b5c5

structure mem_Allocator_allocSentinel__anon_8437b5dedaa0Locals where
  local4 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_allocSentinel__anon_8437b5dedaa0Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_allocSentinel__anon_8437b5dedaa0 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s4 ← Zig.allocStack 24 8
  let e ← ((do
    let i2 ← Zig.callMC Zig.returnAddress
    let i3 ← Zig.callC (mem_Allocator_allocWithOptionsRetAddr__anon_a1da89f8b5c5 p0 p1 i2)
    let i4 ← pure (← get).local4
    (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i4 i3)
    let i6 ← pure (i4)
    let i7 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i6)
    pure (.ret i7)) : Zig.CM Tgt mem_Allocator_allocSentinel__anon_8437b5dedaa0Locals mem_Allocator_allocSentinel__anon_8437b5dedaa0Exit).run' { (default : mem_Allocator_allocSentinel__anon_8437b5dedaa0Locals) with local4 := s4 }
  Zig.free s4
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_allocSentinel__anon_8437b5dedaa0

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

structure mem_Allocator_allocWithOptionsRetAddr__anon_e27387733d94Locals where
  deriving Inhabited

inductive mem_Allocator_allocWithOptionsRetAddr__anon_e27387733d94Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br4 (v : Except Zig.ErrName (Zig.Slice))
  | br22
  | br35
  | br43

def mem_Allocator_allocWithOptionsRetAddr__anon_e27387733d94 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
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
        pure (.br4 i14))) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_e27387733d94Locals mem_Allocator_allocWithOptionsRetAddr__anon_e27387733d94Exit) with
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
            throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_e27387733d94Locals mem_Allocator_allocWithOptionsRetAddr__anon_e27387733d94Exit) with
        | .br22 => (do
          let i27 ← Zig.callMC (Zig.checkIndex v16.len p1) >>= fun _ => Zig.callMC (Zig.ptrProject v16.ptr (·.elem 4 p1))
          Zig.store (α := BitVec 32) 4 i27 (0 : BitVec 32)
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
              throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_e27387733d94Locals mem_Allocator_allocWithOptionsRetAddr__anon_e27387733d94Exit) with
          | .br35 => (do
            let i40 ← Zig.callMC (Zig.checkSliceEnd v16.len (0 : BitVec 64) i31 1 >>= fun _ => pure (⟨i30, i31⟩ : Zig.Slice))
            let i41 ← Zig.callMC (Zig.checkSentinelIndex i40.len i31 >>= fun _ => Zig.load (BitVec 32) 4 (i40.ptr.elem 4 i31))
            let i42 ← pure ((0 : BitVec 32) == i41)
            match ← ((do
              if i42 then (do
                pure .br43)
              else (do
                throw .panic)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_e27387733d94Locals mem_Allocator_allocWithOptionsRetAddr__anon_e27387733d94Exit) with
            | .br43 => (do
              let i48 ← pure ((.ok i40) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i48))
            | e => pure e)
          | e => pure e)
        | e => pure e))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_e27387733d94Locals mem_Allocator_allocWithOptionsRetAddr__anon_e27387733d94Exit).run' (default : mem_Allocator_allocWithOptionsRetAddr__anon_e27387733d94Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocWithOptionsRetAddr__anon_e27387733d94

structure mem_Allocator_allocSentinel__anon_c8aadc923bc9Locals where
  local4 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_allocSentinel__anon_c8aadc923bc9Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_allocSentinel__anon_c8aadc923bc9 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s4 ← Zig.allocStack 24 8
  let e ← ((do
    let i2 ← Zig.callMC Zig.returnAddress
    let i3 ← Zig.callC (mem_Allocator_allocWithOptionsRetAddr__anon_e27387733d94 p0 p1 i2)
    let i4 ← pure (← get).local4
    (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i4 i3)
    let i6 ← pure (i4)
    let i7 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i6)
    pure (.ret i7)) : Zig.CM Tgt mem_Allocator_allocSentinel__anon_c8aadc923bc9Locals mem_Allocator_allocSentinel__anon_c8aadc923bc9Exit).run' { (default : mem_Allocator_allocSentinel__anon_c8aadc923bc9Locals) with local4 := s4 }
  Zig.free s4
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_allocSentinel__anon_c8aadc923bc9

structure mem_absorbSentinel__anon_6f5b4b6f7cb0Locals where
  deriving Inhabited

inductive mem_absorbSentinel__anon_6f5b4b6f7cb0Exit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_6f5b4b6f7cb0 (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret p0)) : Zig.MM mem_absorbSentinel__anon_6f5b4b6f7cb0Locals mem_absorbSentinel__anon_6f5b4b6f7cb0Exit).run' (default : mem_absorbSentinel__anon_6f5b4b6f7cb0Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_absorbSentinel__anon_6f5b4b6f7cb0

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

attribute [zig_run] mem_Allocator_free__anon_10fd68fdc68d

structure mem_absorbSentinel__anon_5c5a1474fdd7Locals where
  local1 : Zig.Slice
  deriving Inhabited

inductive mem_absorbSentinel__anon_5c5a1474fdd7Exit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_5c5a1474fdd7 (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    modify (fun s => { s with local1 := p0 })
    let i6 ← pure (((← get).local1).len)
    let i7 ← Zig.add false i6 (1 : BitVec 64)
    let i8 ← pure (((← get).local1).ptr)
    let i9 ← pure i8
    let i10 ← Zig.sub false i7 (0 : BitVec 64) (safe := false)
    let i11 ← pure (⟨i9, i10⟩ : Zig.Slice)
    pure (.ret i11)) : Zig.MM mem_absorbSentinel__anon_5c5a1474fdd7Locals mem_absorbSentinel__anon_5c5a1474fdd7Exit).run' (default : mem_absorbSentinel__anon_5c5a1474fdd7Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_absorbSentinel__anon_5c5a1474fdd7

structure mem_Allocator_free__anon_85944fd5a0ebLocals where
  deriving Inhabited

inductive mem_Allocator_free__anon_85944fd5a0ebExit where
  | ret
  | br8
  | br19

def mem_Allocator_free__anon_85944fd5a0eb [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_5c5a1474fdd7 p1)
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
        pure .br8)) : Zig.CM Tgt mem_Allocator_free__anon_85944fd5a0ebLocals mem_Allocator_free__anon_85944fd5a0ebExit) with
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
        pure .br19) : Zig.CM Tgt mem_Allocator_free__anon_85944fd5a0ebLocals mem_Allocator_free__anon_85944fd5a0ebExit) with
      | .br19 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_85944fd5a0ebLocals mem_Allocator_free__anon_85944fd5a0ebExit).run' (default : mem_Allocator_free__anon_85944fd5a0ebLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_85944fd5a0eb

structure mem_absorbSentinel__anon_c36359dfe78dLocals where
  deriving Inhabited

inductive mem_absorbSentinel__anon_c36359dfe78dExit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_c36359dfe78d (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret p0)) : Zig.MM mem_absorbSentinel__anon_c36359dfe78dLocals mem_absorbSentinel__anon_c36359dfe78dExit).run' (default : mem_absorbSentinel__anon_c36359dfe78dLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_absorbSentinel__anon_c36359dfe78d

structure mem_Allocator_free__anon_906bba868805Locals where
  deriving Inhabited

inductive mem_Allocator_free__anon_906bba868805Exit where
  | ret
  | br8
  | br19

def mem_Allocator_free__anon_906bba868805 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_c36359dfe78d p1)
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
        pure .br8)) : Zig.CM Tgt mem_Allocator_free__anon_906bba868805Locals mem_Allocator_free__anon_906bba868805Exit) with
    | .br8 => (do
      let _i15 ← pure i7.len
      Zig.callMC (Zig.memset (α := BitVec 8) 1 i7.ptr i7.len none)
      let i17 ← Zig.callRC (mem_Alignment_fromByteUnits (2 : BitVec 64))
      let i18 ← Zig.callMC Zig.returnAddress
      match ← ((do
        let i20 ← pure ((p0).vtable)
        let i21 ← Zig.callMC (Zig.ptrProject i20 (·.add 24))
        let i22 ← Zig.load (Zig.Ptr) 8 i21
        let i23 ← pure ((p0).ptr)
        let _i24 ← (Zig.callC (Zig.extCall (Ext.call2 i22 i23 i7 i17 i18)))
        pure .br19) : Zig.CM Tgt mem_Allocator_free__anon_906bba868805Locals mem_Allocator_free__anon_906bba868805Exit) with
      | .br19 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_906bba868805Locals mem_Allocator_free__anon_906bba868805Exit).run' (default : mem_Allocator_free__anon_906bba868805Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_906bba868805

structure mem_absorbSentinel__anon_a765238f74e0Locals where
  local1 : Zig.Slice
  deriving Inhabited

inductive mem_absorbSentinel__anon_a765238f74e0Exit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_a765238f74e0 (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    modify (fun s => { s with local1 := p0 })
    let i6 ← pure (((← get).local1).len)
    let i7 ← Zig.add false i6 (1 : BitVec 64)
    let i8 ← pure (((← get).local1).ptr)
    let i9 ← pure i8
    let i10 ← Zig.sub false i7 (0 : BitVec 64) (safe := false)
    let i11 ← pure (⟨i9, i10⟩ : Zig.Slice)
    pure (.ret i11)) : Zig.MM mem_absorbSentinel__anon_a765238f74e0Locals mem_absorbSentinel__anon_a765238f74e0Exit).run' (default : mem_absorbSentinel__anon_a765238f74e0Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_absorbSentinel__anon_a765238f74e0

structure mem_Allocator_free__anon_dddca57af15bLocals where
  deriving Inhabited

inductive mem_Allocator_free__anon_dddca57af15bExit where
  | ret
  | br8
  | br19

def mem_Allocator_free__anon_dddca57af15b [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_a765238f74e0 p1)
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
        pure .br8)) : Zig.CM Tgt mem_Allocator_free__anon_dddca57af15bLocals mem_Allocator_free__anon_dddca57af15bExit) with
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
        pure .br19) : Zig.CM Tgt mem_Allocator_free__anon_dddca57af15bLocals mem_Allocator_free__anon_dddca57af15bExit) with
      | .br19 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_dddca57af15bLocals mem_Allocator_free__anon_dddca57af15bExit).run' (default : mem_Allocator_free__anon_dddca57af15bLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_dddca57af15b

structure mem_absorbSentinel__anon_d8dc5dff15e7Locals where
  local1 : Zig.Slice
  deriving Inhabited

inductive mem_absorbSentinel__anon_d8dc5dff15e7Exit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_d8dc5dff15e7 (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    modify (fun s => { s with local1 := p0 })
    let i6 ← pure (((← get).local1).len)
    let i7 ← Zig.add false i6 (1 : BitVec 64)
    let i8 ← pure (((← get).local1).ptr)
    let i9 ← pure i8
    let i10 ← Zig.sub false i7 (0 : BitVec 64) (safe := false)
    let i11 ← pure (⟨i9, i10⟩ : Zig.Slice)
    pure (.ret i11)) : Zig.MM mem_absorbSentinel__anon_d8dc5dff15e7Locals mem_absorbSentinel__anon_d8dc5dff15e7Exit).run' (default : mem_absorbSentinel__anon_d8dc5dff15e7Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_absorbSentinel__anon_d8dc5dff15e7

structure mem_Allocator_free__anon_ef346418a252Locals where
  deriving Inhabited

inductive mem_Allocator_free__anon_ef346418a252Exit where
  | ret
  | br8
  | br19

def mem_Allocator_free__anon_ef346418a252 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_d8dc5dff15e7 p1)
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
        pure .br8)) : Zig.CM Tgt mem_Allocator_free__anon_ef346418a252Locals mem_Allocator_free__anon_ef346418a252Exit) with
    | .br8 => (do
      let _i15 ← pure i7.len
      Zig.callMC (Zig.memset (α := BitVec 8) 1 i7.ptr i7.len none)
      let i17 ← Zig.callRC (mem_Alignment_fromByteUnits (2 : BitVec 64))
      let i18 ← Zig.callMC Zig.returnAddress
      match ← ((do
        let i20 ← pure ((p0).vtable)
        let i21 ← Zig.callMC (Zig.ptrProject i20 (·.add 24))
        let i22 ← Zig.load (Zig.Ptr) 8 i21
        let i23 ← pure ((p0).ptr)
        let _i24 ← (Zig.callC (Zig.extCall (Ext.call2 i22 i23 i7 i17 i18)))
        pure .br19) : Zig.CM Tgt mem_Allocator_free__anon_ef346418a252Locals mem_Allocator_free__anon_ef346418a252Exit) with
      | .br19 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_ef346418a252Locals mem_Allocator_free__anon_ef346418a252Exit).run' (default : mem_Allocator_free__anon_ef346418a252Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_ef346418a252

structure mem_absorbSentinel__anon_4b1b5a8230f7Locals where
  deriving Inhabited

inductive mem_absorbSentinel__anon_4b1b5a8230f7Exit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_4b1b5a8230f7 (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret p0)) : Zig.MM mem_absorbSentinel__anon_4b1b5a8230f7Locals mem_absorbSentinel__anon_4b1b5a8230f7Exit).run' (default : mem_absorbSentinel__anon_4b1b5a8230f7Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_absorbSentinel__anon_4b1b5a8230f7

structure mem_Allocator_free__anon_f1de31ec7442Locals where
  deriving Inhabited

inductive mem_Allocator_free__anon_f1de31ec7442Exit where
  | ret
  | br8
  | br19

def mem_Allocator_free__anon_f1de31ec7442 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_4b1b5a8230f7 p1)
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
        pure .br8)) : Zig.CM Tgt mem_Allocator_free__anon_f1de31ec7442Locals mem_Allocator_free__anon_f1de31ec7442Exit) with
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
        pure .br19) : Zig.CM Tgt mem_Allocator_free__anon_f1de31ec7442Locals mem_Allocator_free__anon_f1de31ec7442Exit) with
      | .br19 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_f1de31ec7442Locals mem_Allocator_free__anon_f1de31ec7442Exit).run' (default : mem_Allocator_free__anon_f1de31ec7442Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_f1de31ec7442

structure mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals where
  local21 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br9 (v : Except Zig.ErrName (Zig.Slice))
  | br4
  | br27
  | br40 (v : BitVec 64)
  | br50 (v : Option (Zig.Ptr))
  | br70
  | br77
  | br48
  | br90 (v : Option (Zig.Ptr))
  | br88 (v : Zig.Ptr)
  | br116
  | br125
  | br137
  | br146
  | br163
  | br170

def mem_Allocator_reallocAdvanced__anon_1b00930347b4 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) (p3 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s21 ← Zig.allocStack 24 8
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
            pure (.br9 i19))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit) with
        | .br9 v9 => (do
          let i21 ← pure (← get).local21
          (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i21 v9)
          let i23 ← pure (i21)
          let i24 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i23)
          pure (.ret i24))
        | e => pure e)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit) with
    | .br4 => (do
      match ← ((do
        let i28 ← pure (p2)
        let i29 ← pure (i28 == (0 : BitVec 64))
        if i29 then (do
          let _i31 ← Zig.callC (mem_Allocator_free__anon_f1de31ec7442 p0 p1)
          pure (.ret (.ok (⟨(⟨none, 18446744073709551608⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice) : Except Zig.ErrName (Zig.Slice))))
        else (do
          pure .br27)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit) with
      | .br27 => (do
        let i34 ← Zig.callMC (mem_absorbSentinel__anon_4b1b5a8230f7 p1)
        let i35 ← pure i34.ptr
        let i36 ← pure i34.len
        let i37 ← Zig.mul false i36 (8 : BitVec 64) (safe := false)
        let i38 ← pure (i35)
        let i39 ← pure (⟨i38, i37⟩ : Zig.Slice)
        match ← ((do
          let i41 ← Zig.callRC (math_mul__anon_44faaf286c79 (8 : BitVec 64) p2)
          let i42 ← pure (Zig.isNonErr i41)
          if i42 then (do
            let i44 ← Zig.callRC (Zig.unwrapPayload i41)
            pure (.br40 i44))
          else (do
            let _i46 ← Zig.callRC (Zig.unwrapErr i41)
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice))))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit) with
        | .br40 v40 => (do
          match ← ((do
            let i49 ← Zig.callRC (mem_Alignment_fromByteUnits (8 : BitVec 64))
            match ← ((do
              let i51 ← pure ((p0).vtable)
              let i52 ← Zig.callMC (Zig.ptrProject i51 (·.add 16))
              let i53 ← Zig.load (Zig.Ptr) 8 i52
              let i54 ← pure ((p0).ptr)
              let i55 ← (Zig.callC (Zig.extCall (Ext.call1 i53 i54 i39 i49 v40 p3)))
              pure (.br50 i55)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit) with
            | .br50 v50 => (do
              let i57 ← pure ((v50).isSome)
              if i57 then (do
                let i59 ← Zig.optPayload v50
                let i60 ← pure i59
                let i61 ← Zig.sub false v40 (0 : BitVec 64) (safe := false)
                let i62 ← pure (⟨i60, i61⟩ : Zig.Slice)
                let i63 ← pure i62.ptr
                let i64 ← pure i62.len
                let i65 ← pure (i64 == (0 : BitVec 64))
                let i66 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i63)))
                let i67 ← pure (i66 &&& (7 : BitVec 64))
                let i68 ← pure (i67 == (0 : BitVec 64))
                let i69 ← pure (i65 || i68)
                match ← ((do
                  if i69 then (do
                    pure .br70)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit) with
                | .br70 => (do
                  let i75 ← Zig.rem false i64 (8 : BitVec 64)
                  let i76 ← pure (i75 == (0 : BitVec 64))
                  match ← ((do
                    if i76 then (do
                      pure .br77)
                    else (do
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit) with
                  | .br77 => (do
                    let i82 ← Zig.divExact false i64 (8 : BitVec 64)
                    let i83 ← Zig.callMC (Zig.checkAlign 8 i63 >>= fun _ => pure i63)
                    let i84 ← pure (⟨i83, i82⟩ : Zig.Slice)
                    let i85 ← pure ((.ok i84) : Except Zig.ErrName (Zig.Slice))
                    pure (.ret i85))
                  | e => pure e)
                | e => pure e)
              else (do
                pure .br48))
            | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit) with
          | .br48 => (do
            match ← ((do
              let i89 ← Zig.callRC (mem_Alignment_fromByteUnits (8 : BitVec 64))
              match ← ((do
                let i91 ← pure ((p0).vtable)
                let i92 ← pure i91
                let i93 ← Zig.load (Zig.Ptr) 8 i92
                let i94 ← pure ((p0).ptr)
                let i95 ← (Zig.callC (Zig.extCall (Ext.call0 i93 i94 v40 i89 p3)))
                pure (.br90 i95)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit) with
              | .br90 v90 => (do
                let i97 ← pure ((v90).isSome)
                if i97 then (do
                  let i99 ← Zig.optPayload v90
                  pure (.br88 i99))
                else (do
                  pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice)))))
              | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit) with
            | .br88 v88 => (do
              let i102 ← pure i39.len
              let i103 ← pure (v40)
              let i104 ← pure (i102)
              let i105 ← pure (Zig.min false i103 i104)
              let i106 ← pure v88
              let i107 ← pure (i105)
              let i108 ← Zig.sub false i107 (0 : BitVec 64) (safe := false)
              let i109 ← pure (⟨i106, i108⟩ : Zig.Slice)
              let i110 ← pure i39.ptr
              let i111 ← pure i110
              let i112 ← pure (i105)
              let i113 ← Zig.sub false i112 (0 : BitVec 64) (safe := false)
              let i114 ← pure i39.len
              let i115 ← pure (Zig.le false i112 i114)
              match ← ((do
                if i115 then (do
                  pure .br116)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit) with
              | .br116 => (do
                let i121 ← Zig.callMC (Zig.checkSliceEnd i39.len (0 : BitVec 64) i113 0 >>= fun _ => pure (⟨i111, i113⟩ : Zig.Slice))
                let i122 ← pure i109.len
                let i123 ← pure i121.len
                let i124 ← pure (i122 == i123)
                match ← ((do
                  if i124 then (do
                    pure .br125)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit) with
                | .br125 => (do
                  let i130 ← pure i121.ptr
                  let i131 ← pure i109.ptr
                  let i132 ← Zig.callMC (Zig.ptrProject i130 (·.elem 1 i122))
                  let i133 ← Zig.callMC (Zig.ptrProject i131 (·.elem 1 i122))
                  let i134 ← Zig.callMC (Zig.ptrLe i132 i131)
                  let i135 ← Zig.callMC (Zig.ptrLe i133 i130)
                  let i136 ← pure (i134 || i135)
                  match ← ((do
                    if i136 then (do
                      pure .br137)
                    else (do
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit) with
                  | .br137 => (do
                    Zig.callMC (Zig.memcpy 1 1 1 i109.ptr i130 i109.len i121.len)
                    let _i143 ← pure i39.len
                    Zig.callMC (Zig.memset (α := BitVec 8) 1 i39.ptr i39.len none)
                    let i145 ← Zig.callRC (mem_Alignment_fromByteUnits (8 : BitVec 64))
                    match ← ((do
                      let i147 ← pure ((p0).vtable)
                      let i148 ← Zig.callMC (Zig.ptrProject i147 (·.add 24))
                      let i149 ← Zig.load (Zig.Ptr) 8 i148
                      let i150 ← pure ((p0).ptr)
                      let _i151 ← (Zig.callC (Zig.extCall (Ext.call2 i149 i150 i39 i145 p3)))
                      pure .br146) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit) with
                    | .br146 => (do
                      let i153 ← pure v88
                      let i154 ← Zig.sub false v40 (0 : BitVec 64) (safe := false)
                      let i155 ← pure (⟨i153, i154⟩ : Zig.Slice)
                      let i156 ← pure i155.ptr
                      let i157 ← pure i155.len
                      let i158 ← pure (i157 == (0 : BitVec 64))
                      let i159 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i156)))
                      let i160 ← pure (i159 &&& (7 : BitVec 64))
                      let i161 ← pure (i160 == (0 : BitVec 64))
                      let i162 ← pure (i158 || i161)
                      match ← ((do
                        if i162 then (do
                          pure .br163)
                        else (do
                          throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit) with
                      | .br163 => (do
                        let i168 ← Zig.rem false i157 (8 : BitVec 64)
                        let i169 ← pure (i168 == (0 : BitVec 64))
                        match ← ((do
                          if i169 then (do
                            pure .br170)
                          else (do
                            throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit) with
                        | .br170 => (do
                          let i175 ← Zig.divExact false i157 (8 : BitVec 64)
                          let i176 ← Zig.callMC (Zig.checkAlign 8 i156 >>= fun _ => pure i156)
                          let i177 ← pure (⟨i176, i175⟩ : Zig.Slice)
                          let i178 ← pure ((.ok i177) : Except Zig.ErrName (Zig.Slice))
                          pure (.ret i178))
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
    | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals mem_Allocator_reallocAdvanced__anon_1b00930347b4Exit).run' { (default : mem_Allocator_reallocAdvanced__anon_1b00930347b4Locals) with local21 := s21 }
  Zig.free s21
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_reallocAdvanced__anon_1b00930347b4

structure mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals where
  local21 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br9 (v : Except Zig.ErrName (Zig.Slice))
  | br4
  | br27
  | br40 (v : BitVec 64)
  | br50 (v : Option (Zig.Ptr))
  | br70
  | br77
  | br48
  | br90 (v : Option (Zig.Ptr))
  | br88 (v : Zig.Ptr)
  | br116
  | br125
  | br137
  | br146
  | br163
  | br170

def mem_Allocator_reallocAdvanced__anon_37f73f8446a2 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) (p3 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s21 ← Zig.allocStack 24 8
  let e ← ((do
    match ← ((do
      let i5 ← pure p1.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        match ← ((do
          let i10 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_e3d53c154a1b p0 p2 p3)
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
            pure (.br9 i19))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit) with
        | .br9 v9 => (do
          let i21 ← pure (← get).local21
          (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i21 v9)
          let i23 ← pure (i21)
          let i24 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i23)
          pure (.ret i24))
        | e => pure e)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit) with
    | .br4 => (do
      match ← ((do
        let i28 ← pure (p2)
        let i29 ← pure (i28 == (0 : BitVec 64))
        if i29 then (do
          let _i31 ← Zig.callC (mem_Allocator_free__anon_906bba868805 p0 p1)
          pure (.ret (.ok (⟨(⟨none, 18446744073709551614⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice) : Except Zig.ErrName (Zig.Slice))))
        else (do
          pure .br27)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit) with
      | .br27 => (do
        let i34 ← Zig.callMC (mem_absorbSentinel__anon_c36359dfe78d p1)
        let i35 ← pure i34.ptr
        let i36 ← pure i34.len
        let i37 ← Zig.mul false i36 (2 : BitVec 64) (safe := false)
        let i38 ← pure (i35)
        let i39 ← pure (⟨i38, i37⟩ : Zig.Slice)
        match ← ((do
          let i41 ← Zig.callRC (math_mul__anon_44faaf286c79 (2 : BitVec 64) p2)
          let i42 ← pure (Zig.isNonErr i41)
          if i42 then (do
            let i44 ← Zig.callRC (Zig.unwrapPayload i41)
            pure (.br40 i44))
          else (do
            let _i46 ← Zig.callRC (Zig.unwrapErr i41)
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice))))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit) with
        | .br40 v40 => (do
          match ← ((do
            let i49 ← Zig.callRC (mem_Alignment_fromByteUnits (2 : BitVec 64))
            match ← ((do
              let i51 ← pure ((p0).vtable)
              let i52 ← Zig.callMC (Zig.ptrProject i51 (·.add 16))
              let i53 ← Zig.load (Zig.Ptr) 8 i52
              let i54 ← pure ((p0).ptr)
              let i55 ← (Zig.callC (Zig.extCall (Ext.call1 i53 i54 i39 i49 v40 p3)))
              pure (.br50 i55)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit) with
            | .br50 v50 => (do
              let i57 ← pure ((v50).isSome)
              if i57 then (do
                let i59 ← Zig.optPayload v50
                let i60 ← pure i59
                let i61 ← Zig.sub false v40 (0 : BitVec 64) (safe := false)
                let i62 ← pure (⟨i60, i61⟩ : Zig.Slice)
                let i63 ← pure i62.ptr
                let i64 ← pure i62.len
                let i65 ← pure (i64 == (0 : BitVec 64))
                let i66 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i63)))
                let i67 ← pure (i66 &&& (1 : BitVec 64))
                let i68 ← pure (i67 == (0 : BitVec 64))
                let i69 ← pure (i65 || i68)
                match ← ((do
                  if i69 then (do
                    pure .br70)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit) with
                | .br70 => (do
                  let i75 ← Zig.rem false i64 (2 : BitVec 64)
                  let i76 ← pure (i75 == (0 : BitVec 64))
                  match ← ((do
                    if i76 then (do
                      pure .br77)
                    else (do
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit) with
                  | .br77 => (do
                    let i82 ← Zig.divExact false i64 (2 : BitVec 64)
                    let i83 ← Zig.callMC (Zig.checkAlign 2 i63 >>= fun _ => pure i63)
                    let i84 ← pure (⟨i83, i82⟩ : Zig.Slice)
                    let i85 ← pure ((.ok i84) : Except Zig.ErrName (Zig.Slice))
                    pure (.ret i85))
                  | e => pure e)
                | e => pure e)
              else (do
                pure .br48))
            | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit) with
          | .br48 => (do
            match ← ((do
              let i89 ← Zig.callRC (mem_Alignment_fromByteUnits (2 : BitVec 64))
              match ← ((do
                let i91 ← pure ((p0).vtable)
                let i92 ← pure i91
                let i93 ← Zig.load (Zig.Ptr) 8 i92
                let i94 ← pure ((p0).ptr)
                let i95 ← (Zig.callC (Zig.extCall (Ext.call0 i93 i94 v40 i89 p3)))
                pure (.br90 i95)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit) with
              | .br90 v90 => (do
                let i97 ← pure ((v90).isSome)
                if i97 then (do
                  let i99 ← Zig.optPayload v90
                  pure (.br88 i99))
                else (do
                  pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice)))))
              | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit) with
            | .br88 v88 => (do
              let i102 ← pure i39.len
              let i103 ← pure (v40)
              let i104 ← pure (i102)
              let i105 ← pure (Zig.min false i103 i104)
              let i106 ← pure v88
              let i107 ← pure (i105)
              let i108 ← Zig.sub false i107 (0 : BitVec 64) (safe := false)
              let i109 ← pure (⟨i106, i108⟩ : Zig.Slice)
              let i110 ← pure i39.ptr
              let i111 ← pure i110
              let i112 ← pure (i105)
              let i113 ← Zig.sub false i112 (0 : BitVec 64) (safe := false)
              let i114 ← pure i39.len
              let i115 ← pure (Zig.le false i112 i114)
              match ← ((do
                if i115 then (do
                  pure .br116)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit) with
              | .br116 => (do
                let i121 ← Zig.callMC (Zig.checkSliceEnd i39.len (0 : BitVec 64) i113 0 >>= fun _ => pure (⟨i111, i113⟩ : Zig.Slice))
                let i122 ← pure i109.len
                let i123 ← pure i121.len
                let i124 ← pure (i122 == i123)
                match ← ((do
                  if i124 then (do
                    pure .br125)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit) with
                | .br125 => (do
                  let i130 ← pure i121.ptr
                  let i131 ← pure i109.ptr
                  let i132 ← Zig.callMC (Zig.ptrProject i130 (·.elem 1 i122))
                  let i133 ← Zig.callMC (Zig.ptrProject i131 (·.elem 1 i122))
                  let i134 ← Zig.callMC (Zig.ptrLe i132 i131)
                  let i135 ← Zig.callMC (Zig.ptrLe i133 i130)
                  let i136 ← pure (i134 || i135)
                  match ← ((do
                    if i136 then (do
                      pure .br137)
                    else (do
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit) with
                  | .br137 => (do
                    Zig.callMC (Zig.memcpy 1 1 1 i109.ptr i130 i109.len i121.len)
                    let _i143 ← pure i39.len
                    Zig.callMC (Zig.memset (α := BitVec 8) 1 i39.ptr i39.len none)
                    let i145 ← Zig.callRC (mem_Alignment_fromByteUnits (2 : BitVec 64))
                    match ← ((do
                      let i147 ← pure ((p0).vtable)
                      let i148 ← Zig.callMC (Zig.ptrProject i147 (·.add 24))
                      let i149 ← Zig.load (Zig.Ptr) 8 i148
                      let i150 ← pure ((p0).ptr)
                      let _i151 ← (Zig.callC (Zig.extCall (Ext.call2 i149 i150 i39 i145 p3)))
                      pure .br146) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit) with
                    | .br146 => (do
                      let i153 ← pure v88
                      let i154 ← Zig.sub false v40 (0 : BitVec 64) (safe := false)
                      let i155 ← pure (⟨i153, i154⟩ : Zig.Slice)
                      let i156 ← pure i155.ptr
                      let i157 ← pure i155.len
                      let i158 ← pure (i157 == (0 : BitVec 64))
                      let i159 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i156)))
                      let i160 ← pure (i159 &&& (1 : BitVec 64))
                      let i161 ← pure (i160 == (0 : BitVec 64))
                      let i162 ← pure (i158 || i161)
                      match ← ((do
                        if i162 then (do
                          pure .br163)
                        else (do
                          throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit) with
                      | .br163 => (do
                        let i168 ← Zig.rem false i157 (2 : BitVec 64)
                        let i169 ← pure (i168 == (0 : BitVec 64))
                        match ← ((do
                          if i169 then (do
                            pure .br170)
                          else (do
                            throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit) with
                        | .br170 => (do
                          let i175 ← Zig.divExact false i157 (2 : BitVec 64)
                          let i176 ← Zig.callMC (Zig.checkAlign 2 i156 >>= fun _ => pure i156)
                          let i177 ← pure (⟨i176, i175⟩ : Zig.Slice)
                          let i178 ← pure ((.ok i177) : Except Zig.ErrName (Zig.Slice))
                          pure (.ret i178))
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
    | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals mem_Allocator_reallocAdvanced__anon_37f73f8446a2Exit).run' { (default : mem_Allocator_reallocAdvanced__anon_37f73f8446a2Locals) with local21 := s21 }
  Zig.free s21
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_reallocAdvanced__anon_37f73f8446a2

structure mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals where
  local21 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br9 (v : Except Zig.ErrName (Zig.Slice))
  | br4
  | br27
  | br40 (v : BitVec 64)
  | br50 (v : Option (Zig.Ptr))
  | br70
  | br77
  | br48
  | br90 (v : Option (Zig.Ptr))
  | br88 (v : Zig.Ptr)
  | br116
  | br125
  | br137
  | br146
  | br163
  | br170

def mem_Allocator_reallocAdvanced__anon_f9642f2d8f58 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) (p3 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s21 ← Zig.allocStack 24 8
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
            pure (.br9 i19))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit) with
        | .br9 v9 => (do
          let i21 ← pure (← get).local21
          (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i21 v9)
          let i23 ← pure (i21)
          let i24 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i23)
          pure (.ret i24))
        | e => pure e)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit) with
    | .br4 => (do
      match ← ((do
        let i28 ← pure (p2)
        let i29 ← pure (i28 == (0 : BitVec 64))
        if i29 then (do
          let _i31 ← Zig.callC (mem_Allocator_free__anon_10fd68fdc68d p0 p1)
          pure (.ret (.ok (⟨(⟨none, 18446744073709551612⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice) : Except Zig.ErrName (Zig.Slice))))
        else (do
          pure .br27)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit) with
      | .br27 => (do
        let i34 ← Zig.callMC (mem_absorbSentinel__anon_6f5b4b6f7cb0 p1)
        let i35 ← pure i34.ptr
        let i36 ← pure i34.len
        let i37 ← Zig.mul false i36 (4 : BitVec 64) (safe := false)
        let i38 ← pure (i35)
        let i39 ← pure (⟨i38, i37⟩ : Zig.Slice)
        match ← ((do
          let i41 ← Zig.callRC (math_mul__anon_44faaf286c79 (4 : BitVec 64) p2)
          let i42 ← pure (Zig.isNonErr i41)
          if i42 then (do
            let i44 ← Zig.callRC (Zig.unwrapPayload i41)
            pure (.br40 i44))
          else (do
            let _i46 ← Zig.callRC (Zig.unwrapErr i41)
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice))))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit) with
        | .br40 v40 => (do
          match ← ((do
            let i49 ← Zig.callRC (mem_Alignment_fromByteUnits (4 : BitVec 64))
            match ← ((do
              let i51 ← pure ((p0).vtable)
              let i52 ← Zig.callMC (Zig.ptrProject i51 (·.add 16))
              let i53 ← Zig.load (Zig.Ptr) 8 i52
              let i54 ← pure ((p0).ptr)
              let i55 ← (Zig.callC (Zig.extCall (Ext.call1 i53 i54 i39 i49 v40 p3)))
              pure (.br50 i55)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit) with
            | .br50 v50 => (do
              let i57 ← pure ((v50).isSome)
              if i57 then (do
                let i59 ← Zig.optPayload v50
                let i60 ← pure i59
                let i61 ← Zig.sub false v40 (0 : BitVec 64) (safe := false)
                let i62 ← pure (⟨i60, i61⟩ : Zig.Slice)
                let i63 ← pure i62.ptr
                let i64 ← pure i62.len
                let i65 ← pure (i64 == (0 : BitVec 64))
                let i66 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i63)))
                let i67 ← pure (i66 &&& (3 : BitVec 64))
                let i68 ← pure (i67 == (0 : BitVec 64))
                let i69 ← pure (i65 || i68)
                match ← ((do
                  if i69 then (do
                    pure .br70)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit) with
                | .br70 => (do
                  let i75 ← Zig.rem false i64 (4 : BitVec 64)
                  let i76 ← pure (i75 == (0 : BitVec 64))
                  match ← ((do
                    if i76 then (do
                      pure .br77)
                    else (do
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit) with
                  | .br77 => (do
                    let i82 ← Zig.divExact false i64 (4 : BitVec 64)
                    let i83 ← Zig.callMC (Zig.checkAlign 4 i63 >>= fun _ => pure i63)
                    let i84 ← pure (⟨i83, i82⟩ : Zig.Slice)
                    let i85 ← pure ((.ok i84) : Except Zig.ErrName (Zig.Slice))
                    pure (.ret i85))
                  | e => pure e)
                | e => pure e)
              else (do
                pure .br48))
            | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit) with
          | .br48 => (do
            match ← ((do
              let i89 ← Zig.callRC (mem_Alignment_fromByteUnits (4 : BitVec 64))
              match ← ((do
                let i91 ← pure ((p0).vtable)
                let i92 ← pure i91
                let i93 ← Zig.load (Zig.Ptr) 8 i92
                let i94 ← pure ((p0).ptr)
                let i95 ← (Zig.callC (Zig.extCall (Ext.call0 i93 i94 v40 i89 p3)))
                pure (.br90 i95)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit) with
              | .br90 v90 => (do
                let i97 ← pure ((v90).isSome)
                if i97 then (do
                  let i99 ← Zig.optPayload v90
                  pure (.br88 i99))
                else (do
                  pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice)))))
              | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit) with
            | .br88 v88 => (do
              let i102 ← pure i39.len
              let i103 ← pure (v40)
              let i104 ← pure (i102)
              let i105 ← pure (Zig.min false i103 i104)
              let i106 ← pure v88
              let i107 ← pure (i105)
              let i108 ← Zig.sub false i107 (0 : BitVec 64) (safe := false)
              let i109 ← pure (⟨i106, i108⟩ : Zig.Slice)
              let i110 ← pure i39.ptr
              let i111 ← pure i110
              let i112 ← pure (i105)
              let i113 ← Zig.sub false i112 (0 : BitVec 64) (safe := false)
              let i114 ← pure i39.len
              let i115 ← pure (Zig.le false i112 i114)
              match ← ((do
                if i115 then (do
                  pure .br116)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit) with
              | .br116 => (do
                let i121 ← Zig.callMC (Zig.checkSliceEnd i39.len (0 : BitVec 64) i113 0 >>= fun _ => pure (⟨i111, i113⟩ : Zig.Slice))
                let i122 ← pure i109.len
                let i123 ← pure i121.len
                let i124 ← pure (i122 == i123)
                match ← ((do
                  if i124 then (do
                    pure .br125)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit) with
                | .br125 => (do
                  let i130 ← pure i121.ptr
                  let i131 ← pure i109.ptr
                  let i132 ← Zig.callMC (Zig.ptrProject i130 (·.elem 1 i122))
                  let i133 ← Zig.callMC (Zig.ptrProject i131 (·.elem 1 i122))
                  let i134 ← Zig.callMC (Zig.ptrLe i132 i131)
                  let i135 ← Zig.callMC (Zig.ptrLe i133 i130)
                  let i136 ← pure (i134 || i135)
                  match ← ((do
                    if i136 then (do
                      pure .br137)
                    else (do
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit) with
                  | .br137 => (do
                    Zig.callMC (Zig.memcpy 1 1 1 i109.ptr i130 i109.len i121.len)
                    let _i143 ← pure i39.len
                    Zig.callMC (Zig.memset (α := BitVec 8) 1 i39.ptr i39.len none)
                    let i145 ← Zig.callRC (mem_Alignment_fromByteUnits (4 : BitVec 64))
                    match ← ((do
                      let i147 ← pure ((p0).vtable)
                      let i148 ← Zig.callMC (Zig.ptrProject i147 (·.add 24))
                      let i149 ← Zig.load (Zig.Ptr) 8 i148
                      let i150 ← pure ((p0).ptr)
                      let _i151 ← (Zig.callC (Zig.extCall (Ext.call2 i149 i150 i39 i145 p3)))
                      pure .br146) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit) with
                    | .br146 => (do
                      let i153 ← pure v88
                      let i154 ← Zig.sub false v40 (0 : BitVec 64) (safe := false)
                      let i155 ← pure (⟨i153, i154⟩ : Zig.Slice)
                      let i156 ← pure i155.ptr
                      let i157 ← pure i155.len
                      let i158 ← pure (i157 == (0 : BitVec 64))
                      let i159 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i156)))
                      let i160 ← pure (i159 &&& (3 : BitVec 64))
                      let i161 ← pure (i160 == (0 : BitVec 64))
                      let i162 ← pure (i158 || i161)
                      match ← ((do
                        if i162 then (do
                          pure .br163)
                        else (do
                          throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit) with
                      | .br163 => (do
                        let i168 ← Zig.rem false i157 (4 : BitVec 64)
                        let i169 ← pure (i168 == (0 : BitVec 64))
                        match ← ((do
                          if i169 then (do
                            pure .br170)
                          else (do
                            throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit) with
                        | .br170 => (do
                          let i175 ← Zig.divExact false i157 (4 : BitVec 64)
                          let i176 ← Zig.callMC (Zig.checkAlign 4 i156 >>= fun _ => pure i156)
                          let i177 ← pure (⟨i176, i175⟩ : Zig.Slice)
                          let i178 ← pure ((.ok i177) : Except Zig.ErrName (Zig.Slice))
                          pure (.ret i178))
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
    | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Exit).run' { (default : mem_Allocator_reallocAdvanced__anon_f9642f2d8f58Locals) with local21 := s21 }
  Zig.free s21
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_reallocAdvanced__anon_f9642f2d8f58

structure mem_Allocator_realloc__anon_0848537da7a2Locals where
  deriving Inhabited

inductive mem_Allocator_realloc__anon_0848537da7a2Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_realloc__anon_0848537da7a2 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.callMC Zig.returnAddress
    let i4 ← Zig.callC (mem_Allocator_reallocAdvanced__anon_37f73f8446a2 p0 p1 p2 i3)
    pure (.ret i4)) : Zig.CM Tgt mem_Allocator_realloc__anon_0848537da7a2Locals mem_Allocator_realloc__anon_0848537da7a2Exit).run' (default : mem_Allocator_realloc__anon_0848537da7a2Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_realloc__anon_0848537da7a2

structure mem_Allocator_realloc__anon_c895a53644a2Locals where
  deriving Inhabited

inductive mem_Allocator_realloc__anon_c895a53644a2Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_realloc__anon_c895a53644a2 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.callMC Zig.returnAddress
    let i4 ← Zig.callC (mem_Allocator_reallocAdvanced__anon_f9642f2d8f58 p0 p1 p2 i3)
    pure (.ret i4)) : Zig.CM Tgt mem_Allocator_realloc__anon_c895a53644a2Locals mem_Allocator_realloc__anon_c895a53644a2Exit).run' (default : mem_Allocator_realloc__anon_c895a53644a2Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_realloc__anon_c895a53644a2

structure mem_Allocator_realloc__anon_db3a5630f4fcLocals where
  deriving Inhabited

inductive mem_Allocator_realloc__anon_db3a5630f4fcExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_realloc__anon_db3a5630f4fc [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.callMC Zig.returnAddress
    let i4 ← Zig.callC (mem_Allocator_reallocAdvanced__anon_1b00930347b4 p0 p1 p2 i3)
    pure (.ret i4)) : Zig.CM Tgt mem_Allocator_realloc__anon_db3a5630f4fcLocals mem_Allocator_realloc__anon_db3a5630f4fcExit).run' (default : mem_Allocator_realloc__anon_db3a5630f4fcLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_realloc__anon_db3a5630f4fc

structure Buf_u16_appendLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive Buf_u16_appendExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br27
  | br39
  | br55
  | br63

def Buf_u16_append [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 16) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
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
    let i17 ← Zig.callC (mem_Allocator_realloc__anon_0848537da7a2 p0 i13 i16)
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
          throw .outOfBounds)) : Zig.CM Tgt Buf_u16_appendLocals Buf_u16_appendExit) with
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
            throw .outOfBounds)) : Zig.CM Tgt Buf_u16_appendLocals Buf_u16_appendExit) with
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
              throw .outOfBounds)) : Zig.CM Tgt Buf_u16_appendLocals Buf_u16_appendExit) with
          | .br55 => (do
            let i60 ← Zig.callMC (Zig.checkSliceEnd v18.len (0 : BitVec 64) i51 1 >>= fun _ => pure (⟨i50, i51⟩ : Zig.Slice))
            let i61 ← Zig.callMC (Zig.checkSentinelIndex i60.len i51 >>= fun _ => Zig.load (BitVec 16) 2 (i60.ptr.elem 2 i51))
            let i62 ← pure ((0 : BitVec 16) == i61)
            match ← ((do
              if i62 then (do
                pure .br63)
              else (do
                throw .panic)) : Zig.CM Tgt Buf_u16_appendLocals Buf_u16_appendExit) with
            | .br63 => (do
              let i68 ← pure ((.ok i60) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i68))
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf_u16_appendLocals Buf_u16_appendExit).run' (default : Buf_u16_appendLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u16_append

structure Buf_u16_makeLocals where
  deriving Inhabited

inductive Buf_u16_makeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def Buf_u16_make [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.callC (mem_Allocator_allocSentinel__anon_8437b5dedaa0 p0 p1)
    let i3 ← pure (i2)
    pure (.ret i3)) : Zig.CM Tgt Buf_u16_makeLocals Buf_u16_makeExit).run' (default : Buf_u16_makeLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Buf_u16_make

structure Buf_u16_releaseLocals where
  deriving Inhabited

inductive Buf_u16_releaseExit where
  | ret

def Buf_u16_release [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let _i2 ← Zig.callC (mem_Allocator_free__anon_ef346418a252 p0 p1)
    pure .ret) : Zig.CM Tgt Buf_u16_releaseLocals Buf_u16_releaseExit).run' (default : Buf_u16_releaseLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Buf_u16_release

structure Buf_u16_resizeLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive Buf_u16_resizeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br23
  | br36
  | br44

def Buf_u16_resize [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    modify (fun s => { s with local3 := p1 })
    let i8 ← pure (((← get).local3).len)
    let i9 ← Zig.add false i8 (1 : BitVec 64)
    let i10 ← pure (((← get).local3).ptr)
    let i11 ← pure i10
    let i12 ← Zig.sub false i9 (0 : BitVec 64) (safe := false)
    let i13 ← pure (⟨i11, i12⟩ : Zig.Slice)
    let i14 ← Zig.add false p2 (1 : BitVec 64)
    let i15 ← Zig.callC (mem_Allocator_realloc__anon_0848537da7a2 p0 i13 i14)
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
          throw .outOfBounds)) : Zig.CM Tgt Buf_u16_resizeLocals Buf_u16_resizeExit) with
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
            throw .outOfBounds)) : Zig.CM Tgt Buf_u16_resizeLocals Buf_u16_resizeExit) with
        | .br36 => (do
          let i41 ← Zig.callMC (Zig.checkSliceEnd v16.len (0 : BitVec 64) i32 1 >>= fun _ => pure (⟨i31, i32⟩ : Zig.Slice))
          let i42 ← Zig.callMC (Zig.checkSentinelIndex i41.len i32 >>= fun _ => Zig.load (BitVec 16) 2 (i41.ptr.elem 2 i32))
          let i43 ← pure ((0 : BitVec 16) == i42)
          match ← ((do
            if i43 then (do
              pure .br44)
            else (do
              throw .panic)) : Zig.CM Tgt Buf_u16_resizeLocals Buf_u16_resizeExit) with
          | .br44 => (do
            let i49 ← pure ((.ok i41) : Except Zig.ErrName (Zig.Slice))
            pure (.ret i49))
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf_u16_resizeLocals Buf_u16_resizeExit).run' (default : Buf_u16_resizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u16_resize

structure Buf_u32_appendLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive Buf_u32_appendExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br27
  | br39
  | br55
  | br63

def Buf_u32_append [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
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
    let i17 ← Zig.callC (mem_Allocator_realloc__anon_c895a53644a2 p0 i13 i16)
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
          throw .outOfBounds)) : Zig.CM Tgt Buf_u32_appendLocals Buf_u32_appendExit) with
      | .br27 => (do
        let i32 ← Zig.callMC (Zig.checkIndex v18.len i24) >>= fun _ => Zig.callMC (Zig.ptrProject v18.ptr (·.elem 4 i24))
        Zig.store (α := BitVec 32) 4 i32 p2
        let i35 ← pure (((← get).local3).len)
        let i36 ← Zig.add false i35 (1 : BitVec 64)
        let i37 ← pure v18.len
        let i38 ← pure (Zig.lt false i36 i37)
        match ← ((do
          if i38 then (do
            pure .br39)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt Buf_u32_appendLocals Buf_u32_appendExit) with
        | .br39 => (do
          let i44 ← Zig.callMC (Zig.checkIndex v18.len i36) >>= fun _ => Zig.callMC (Zig.ptrProject v18.ptr (·.elem 4 i36))
          Zig.store (α := BitVec 32) 4 i44 (0 : BitVec 32)
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
              throw .outOfBounds)) : Zig.CM Tgt Buf_u32_appendLocals Buf_u32_appendExit) with
          | .br55 => (do
            let i60 ← Zig.callMC (Zig.checkSliceEnd v18.len (0 : BitVec 64) i51 1 >>= fun _ => pure (⟨i50, i51⟩ : Zig.Slice))
            let i61 ← Zig.callMC (Zig.checkSentinelIndex i60.len i51 >>= fun _ => Zig.load (BitVec 32) 4 (i60.ptr.elem 4 i51))
            let i62 ← pure ((0 : BitVec 32) == i61)
            match ← ((do
              if i62 then (do
                pure .br63)
              else (do
                throw .panic)) : Zig.CM Tgt Buf_u32_appendLocals Buf_u32_appendExit) with
            | .br63 => (do
              let i68 ← pure ((.ok i60) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i68))
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf_u32_appendLocals Buf_u32_appendExit).run' (default : Buf_u32_appendLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u32_append

structure Buf_u32_makeLocals where
  deriving Inhabited

inductive Buf_u32_makeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def Buf_u32_make [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.callC (mem_Allocator_allocSentinel__anon_c8aadc923bc9 p0 p1)
    let i3 ← pure (i2)
    pure (.ret i3)) : Zig.CM Tgt Buf_u32_makeLocals Buf_u32_makeExit).run' (default : Buf_u32_makeLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Buf_u32_make

structure Buf_u32_releaseLocals where
  deriving Inhabited

inductive Buf_u32_releaseExit where
  | ret

def Buf_u32_release [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let _i2 ← Zig.callC (mem_Allocator_free__anon_85944fd5a0eb p0 p1)
    pure .ret) : Zig.CM Tgt Buf_u32_releaseLocals Buf_u32_releaseExit).run' (default : Buf_u32_releaseLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Buf_u32_release

structure Buf_u32_resizeLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive Buf_u32_resizeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br23
  | br36
  | br44

def Buf_u32_resize [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    modify (fun s => { s with local3 := p1 })
    let i8 ← pure (((← get).local3).len)
    let i9 ← Zig.add false i8 (1 : BitVec 64)
    let i10 ← pure (((← get).local3).ptr)
    let i11 ← pure i10
    let i12 ← Zig.sub false i9 (0 : BitVec 64) (safe := false)
    let i13 ← pure (⟨i11, i12⟩ : Zig.Slice)
    let i14 ← Zig.add false p2 (1 : BitVec 64)
    let i15 ← Zig.callC (mem_Allocator_realloc__anon_c895a53644a2 p0 i13 i14)
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
          throw .outOfBounds)) : Zig.CM Tgt Buf_u32_resizeLocals Buf_u32_resizeExit) with
      | .br23 => (do
        let i28 ← Zig.callMC (Zig.checkIndex v16.len p2) >>= fun _ => Zig.callMC (Zig.ptrProject v16.ptr (·.elem 4 p2))
        Zig.store (α := BitVec 32) 4 i28 (0 : BitVec 32)
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
            throw .outOfBounds)) : Zig.CM Tgt Buf_u32_resizeLocals Buf_u32_resizeExit) with
        | .br36 => (do
          let i41 ← Zig.callMC (Zig.checkSliceEnd v16.len (0 : BitVec 64) i32 1 >>= fun _ => pure (⟨i31, i32⟩ : Zig.Slice))
          let i42 ← Zig.callMC (Zig.checkSentinelIndex i41.len i32 >>= fun _ => Zig.load (BitVec 32) 4 (i41.ptr.elem 4 i32))
          let i43 ← pure ((0 : BitVec 32) == i42)
          match ← ((do
            if i43 then (do
              pure .br44)
            else (do
              throw .panic)) : Zig.CM Tgt Buf_u32_resizeLocals Buf_u32_resizeExit) with
          | .br44 => (do
            let i49 ← pure ((.ok i41) : Except Zig.ErrName (Zig.Slice))
            pure (.ret i49))
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf_u32_resizeLocals Buf_u32_resizeExit).run' (default : Buf_u32_resizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u32_resize

structure Buf_u64_appendLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive Buf_u64_appendExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br27
  | br39
  | br55
  | br63

def Buf_u64_append [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
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
    let i17 ← Zig.callC (mem_Allocator_realloc__anon_db3a5630f4fc p0 i13 i16)
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
          throw .outOfBounds)) : Zig.CM Tgt Buf_u64_appendLocals Buf_u64_appendExit) with
      | .br27 => (do
        let i32 ← Zig.callMC (Zig.checkIndex v18.len i24) >>= fun _ => Zig.callMC (Zig.ptrProject v18.ptr (·.elem 8 i24))
        Zig.store (α := BitVec 64) 8 i32 p2
        let i35 ← pure (((← get).local3).len)
        let i36 ← Zig.add false i35 (1 : BitVec 64)
        let i37 ← pure v18.len
        let i38 ← pure (Zig.lt false i36 i37)
        match ← ((do
          if i38 then (do
            pure .br39)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt Buf_u64_appendLocals Buf_u64_appendExit) with
        | .br39 => (do
          let i44 ← Zig.callMC (Zig.checkIndex v18.len i36) >>= fun _ => Zig.callMC (Zig.ptrProject v18.ptr (·.elem 8 i36))
          Zig.store (α := BitVec 64) 8 i44 (0 : BitVec 64)
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
              throw .outOfBounds)) : Zig.CM Tgt Buf_u64_appendLocals Buf_u64_appendExit) with
          | .br55 => (do
            let i60 ← Zig.callMC (Zig.checkSliceEnd v18.len (0 : BitVec 64) i51 1 >>= fun _ => pure (⟨i50, i51⟩ : Zig.Slice))
            let i61 ← Zig.callMC (Zig.checkSentinelIndex i60.len i51 >>= fun _ => Zig.load (BitVec 64) 8 (i60.ptr.elem 8 i51))
            let i62 ← pure ((0 : BitVec 64) == i61)
            match ← ((do
              if i62 then (do
                pure .br63)
              else (do
                throw .panic)) : Zig.CM Tgt Buf_u64_appendLocals Buf_u64_appendExit) with
            | .br63 => (do
              let i68 ← pure ((.ok i60) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i68))
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf_u64_appendLocals Buf_u64_appendExit).run' (default : Buf_u64_appendLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u64_append

structure Buf_u64_makeLocals where
  deriving Inhabited

inductive Buf_u64_makeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def Buf_u64_make [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.callC (mem_Allocator_allocSentinel__anon_569668752178 p0 p1)
    let i3 ← pure (i2)
    pure (.ret i3)) : Zig.CM Tgt Buf_u64_makeLocals Buf_u64_makeExit).run' (default : Buf_u64_makeLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] Buf_u64_make

structure Buf_u64_releaseLocals where
  deriving Inhabited

inductive Buf_u64_releaseExit where
  | ret

def Buf_u64_release [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let _i2 ← Zig.callC (mem_Allocator_free__anon_dddca57af15b p0 p1)
    pure .ret) : Zig.CM Tgt Buf_u64_releaseLocals Buf_u64_releaseExit).run' (default : Buf_u64_releaseLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] Buf_u64_release

structure Buf_u64_resizeLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive Buf_u64_resizeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br23
  | br36
  | br44

def Buf_u64_resize [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    modify (fun s => { s with local3 := p1 })
    let i8 ← pure (((← get).local3).len)
    let i9 ← Zig.add false i8 (1 : BitVec 64)
    let i10 ← pure (((← get).local3).ptr)
    let i11 ← pure i10
    let i12 ← Zig.sub false i9 (0 : BitVec 64) (safe := false)
    let i13 ← pure (⟨i11, i12⟩ : Zig.Slice)
    let i14 ← Zig.add false p2 (1 : BitVec 64)
    let i15 ← Zig.callC (mem_Allocator_realloc__anon_db3a5630f4fc p0 i13 i14)
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
          throw .outOfBounds)) : Zig.CM Tgt Buf_u64_resizeLocals Buf_u64_resizeExit) with
      | .br23 => (do
        let i28 ← Zig.callMC (Zig.checkIndex v16.len p2) >>= fun _ => Zig.callMC (Zig.ptrProject v16.ptr (·.elem 8 p2))
        Zig.store (α := BitVec 64) 8 i28 (0 : BitVec 64)
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
            throw .outOfBounds)) : Zig.CM Tgt Buf_u64_resizeLocals Buf_u64_resizeExit) with
        | .br36 => (do
          let i41 ← Zig.callMC (Zig.checkSliceEnd v16.len (0 : BitVec 64) i32 1 >>= fun _ => pure (⟨i31, i32⟩ : Zig.Slice))
          let i42 ← Zig.callMC (Zig.checkSentinelIndex i41.len i32 >>= fun _ => Zig.load (BitVec 64) 8 (i41.ptr.elem 8 i32))
          let i43 ← pure ((0 : BitVec 64) == i42)
          match ← ((do
            if i43 then (do
              pure .br44)
            else (do
              throw .panic)) : Zig.CM Tgt Buf_u64_resizeLocals Buf_u64_resizeExit) with
          | .br44 => (do
            let i49 ← pure ((.ok i41) : Except Zig.ErrName (Zig.Slice))
            pure (.ret i49))
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf_u64_resizeLocals Buf_u64_resizeExit).run' (default : Buf_u64_resizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u64_resize

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch [Ext] : Tgt → Zig.ConcM Tgt Unit :=
  fun t => nomatch t

attribute [zig_run] dispatch

end Interfaces.Wide