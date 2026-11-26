-- air2lean-profile: {"allocator_model":"translated","correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.1"}}
-- air2lean-interfaces: {"ext":[{"field":"call0","type":"fn (*anyopaque, usize, mem.Alignment, usize) ?[*]u8"},{"field":"call1","type":"fn (*anyopaque, []u8, mem.Alignment, usize, usize) bool"},{"field":"call2","type":"fn (*anyopaque, []u8, mem.Alignment, usize, usize) ?[*]u8"},{"field":"call3","type":"fn (*anyopaque, []u8, mem.Alignment, usize) void"}],"interfaces":[{"contract":"Zig.Full.CAllocSpec","interface":"std.mem.Allocator","premise":"EXT-05","struct":"mem.Allocator.VTable"}]}
import ZigLean


namespace Interfaces.Grow

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
  /-- `fn (*anyopaque, []u8, mem.Alignment, usize, usize) bool` -/
  call1 : Zig.Ptr → (Zig.Ptr) → (Zig.Slice) → (mem_Alignment) → (BitVec 64) → (BitVec 64) → Zig.ConcM Tgt (Bool)
  /-- `fn (*anyopaque, []u8, mem.Alignment, usize, usize) ?[*]u8` -/
  call2 : Zig.Ptr → (Zig.Ptr) → (Zig.Slice) → (mem_Alignment) → (BitVec 64) → (BitVec 64) → Zig.ConcM Tgt (Option (Zig.Ptr))
  /-- `fn (*anyopaque, []u8, mem.Alignment, usize) void` -/
  call3 : Zig.Ptr → (Zig.Ptr) → (Zig.Slice) → (mem_Alignment) → (BitVec 64) → Zig.ConcM Tgt (Unit)

/-- The closed program's environment: no function besides the program's. -/
@[reducible] def Ext.closed : Ext where
  call0 _ _ _ _ _ := throw .illegal
  call1 _ _ _ _ _ _ := throw .illegal
  call2 _ _ _ _ _ _ := throw .illegal
  call3 _ _ _ _ _ := throw .illegal

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
        let _i24 ← (Zig.callC (Zig.extCall (Ext.call3 i22 i23 i7 i17 i18)))
        pure .br19) : Zig.CM Tgt mem_Allocator_free__anon_85944fd5a0ebLocals mem_Allocator_free__anon_85944fd5a0ebExit) with
      | .br19 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_85944fd5a0ebLocals mem_Allocator_free__anon_85944fd5a0ebExit).run' (default : mem_Allocator_free__anon_85944fd5a0ebLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_85944fd5a0eb

structure mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals where
  local21 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit where
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

def mem_Allocator_reallocAdvanced__anon_0e4c9b513eeb [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) (p3 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
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
            pure (.br9 i19))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit) with
        | .br9 v9 => (do
          let i21 ← pure (← get).local21
          (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i21 v9)
          let i23 ← pure (i21)
          let i24 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i23)
          pure (.ret i24))
        | e => pure e)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit) with
    | .br4 => (do
      match ← ((do
        let i28 ← pure (p2)
        let i29 ← pure (i28 == (0 : BitVec 64))
        if i29 then (do
          let _i31 ← Zig.callC (mem_Allocator_free__anon_85944fd5a0eb p0 p1)
          pure (.ret (.ok (⟨(⟨none, 18446744073709551612⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice) : Except Zig.ErrName (Zig.Slice))))
        else (do
          pure .br27)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit) with
      | .br27 => (do
        let i34 ← Zig.callMC (mem_absorbSentinel__anon_5c5a1474fdd7 p1)
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
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice))))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit) with
        | .br40 v40 => (do
          match ← ((do
            let i49 ← Zig.callRC (mem_Alignment_fromByteUnits (4 : BitVec 64))
            match ← ((do
              let i51 ← pure ((p0).vtable)
              let i52 ← Zig.callMC (Zig.ptrProject i51 (·.add 16))
              let i53 ← Zig.load (Zig.Ptr) 8 i52
              let i54 ← pure ((p0).ptr)
              let i55 ← (Zig.callC (Zig.extCall (Ext.call2 i53 i54 i39 i49 v40 p3)))
              pure (.br50 i55)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit) with
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
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit) with
                | .br70 => (do
                  let i75 ← Zig.rem false i64 (4 : BitVec 64)
                  let i76 ← pure (i75 == (0 : BitVec 64))
                  match ← ((do
                    if i76 then (do
                      pure .br77)
                    else (do
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit) with
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
            | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit) with
          | .br48 => (do
            match ← ((do
              let i89 ← Zig.callRC (mem_Alignment_fromByteUnits (4 : BitVec 64))
              match ← ((do
                let i91 ← pure ((p0).vtable)
                let i92 ← pure i91
                let i93 ← Zig.load (Zig.Ptr) 8 i92
                let i94 ← pure ((p0).ptr)
                let i95 ← (Zig.callC (Zig.extCall (Ext.call0 i93 i94 v40 i89 p3)))
                pure (.br90 i95)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit) with
              | .br90 v90 => (do
                let i97 ← pure ((v90).isSome)
                if i97 then (do
                  let i99 ← Zig.optPayload v90
                  pure (.br88 i99))
                else (do
                  pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice)))))
              | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit) with
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
                  throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit) with
              | .br116 => (do
                let i121 ← Zig.callMC (Zig.checkSliceEnd i39.len (0 : BitVec 64) i113 0 >>= fun _ => pure (⟨i111, i113⟩ : Zig.Slice))
                let i122 ← pure i109.len
                let i123 ← pure i121.len
                let i124 ← pure (i122 == i123)
                match ← ((do
                  if i124 then (do
                    pure .br125)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit) with
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
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit) with
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
                      let _i151 ← (Zig.callC (Zig.extCall (Ext.call3 i149 i150 i39 i145 p3)))
                      pure .br146) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit) with
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
                          throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit) with
                      | .br163 => (do
                        let i168 ← Zig.rem false i157 (4 : BitVec 64)
                        let i169 ← pure (i168 == (0 : BitVec 64))
                        match ← ((do
                          if i169 then (do
                            pure .br170)
                          else (do
                            throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit) with
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
    | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals mem_Allocator_reallocAdvanced__anon_0e4c9b513eebExit).run' { (default : mem_Allocator_reallocAdvanced__anon_0e4c9b513eebLocals) with local21 := s21 }
  Zig.free s21
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_reallocAdvanced__anon_0e4c9b513eeb

structure mem_Allocator_realloc__anon_9cee5a678d80Locals where
  deriving Inhabited

inductive mem_Allocator_realloc__anon_9cee5a678d80Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_realloc__anon_9cee5a678d80 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.callMC Zig.returnAddress
    let i4 ← Zig.callC (mem_Allocator_reallocAdvanced__anon_0e4c9b513eeb p0 p1 p2 i3)
    pure (.ret i4)) : Zig.CM Tgt mem_Allocator_realloc__anon_9cee5a678d80Locals mem_Allocator_realloc__anon_9cee5a678d80Exit).run' (default : mem_Allocator_realloc__anon_9cee5a678d80Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_realloc__anon_9cee5a678d80

structure Buf_u32_appendLocals where
  deriving Inhabited

inductive Buf_u32_appendExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br14
  | br25
  | br40
  | br48

def Buf_u32_append [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← pure p1.len
    let i4 ← Zig.add false i3 (2 : BitVec 64)
    let i5 ← Zig.callC (mem_Allocator_realloc__anon_9cee5a678d80 p0 p1 i4)
    match i5 with
    | .error _ => (do
      let i7 ← Zig.callRC (Zig.unwrapErr i5)
      let i8 ← pure (i7)
      let i9 ← pure ((.error i8) : Except Zig.ErrName (Zig.Slice))
      pure (.ret i9))
    | .ok v6 => (do
      let i11 ← pure p1.len
      let i12 ← pure v6.len
      let i13 ← pure (Zig.lt false i11 i12)
      match ← ((do
        if i13 then (do
          pure .br14)
        else (do
          throw .outOfBounds)) : Zig.CM Tgt Buf_u32_appendLocals Buf_u32_appendExit) with
      | .br14 => (do
        let i19 ← Zig.callMC (Zig.checkIndex v6.len i11) >>= fun _ => Zig.callMC (Zig.ptrProject v6.ptr (·.elem 4 i11))
        Zig.store (α := BitVec 32) 4 i19 p2
        let i21 ← pure p1.len
        let i22 ← Zig.add false i21 (1 : BitVec 64)
        let i23 ← pure v6.len
        let i24 ← pure (Zig.lt false i22 i23)
        match ← ((do
          if i24 then (do
            pure .br25)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt Buf_u32_appendLocals Buf_u32_appendExit) with
        | .br25 => (do
          let i30 ← Zig.callMC (Zig.checkIndex v6.len i22) >>= fun _ => Zig.callMC (Zig.ptrProject v6.ptr (·.elem 4 i22))
          Zig.store (α := BitVec 32) 4 i30 (0 : BitVec 32)
          let i32 ← pure p1.len
          let i33 ← Zig.add false i32 (1 : BitVec 64)
          let i34 ← pure v6.ptr
          let i35 ← pure i34
          let i36 ← Zig.sub false i33 (0 : BitVec 64) (safe := false)
          let i37 ← pure v6.len
          let i38 ← Zig.add false i33 (1 : BitVec 64)
          let i39 ← pure (Zig.le false i38 i37)
          match ← ((do
            if i39 then (do
              pure .br40)
            else (do
              throw .outOfBounds)) : Zig.CM Tgt Buf_u32_appendLocals Buf_u32_appendExit) with
          | .br40 => (do
            let i45 ← Zig.callMC (Zig.checkSliceEnd v6.len (0 : BitVec 64) i36 1 >>= fun _ => pure (⟨i35, i36⟩ : Zig.Slice))
            let i46 ← Zig.callMC (Zig.checkSentinelIndex i45.len i36 >>= fun _ => Zig.load (BitVec 32) 4 (i45.ptr.elem 4 i36))
            let i47 ← pure ((0 : BitVec 32) == i46)
            match ← ((do
              if i47 then (do
                pure .br48)
              else (do
                throw .panic)) : Zig.CM Tgt Buf_u32_appendLocals Buf_u32_appendExit) with
            | .br48 => (do
              let i53 ← pure ((.ok i45) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i53))
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf_u32_appendLocals Buf_u32_appendExit).run' (default : Buf_u32_appendLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u32_append

structure mem_Allocator_resize__anon_d87227067220Locals where
  deriving Inhabited

inductive mem_Allocator_resize__anon_d87227067220Exit where
  | ret (v : Bool)
  | br3
  | br10
  | br23 (v : BitVec 64)
  | br33 (v : Bool)

def mem_Allocator_resize__anon_d87227067220 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p2)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        let _i7 ← Zig.callC (mem_Allocator_free__anon_85944fd5a0eb p0 p1)
        pure (.ret true))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_resize__anon_d87227067220Locals mem_Allocator_resize__anon_d87227067220Exit) with
    | .br3 => (do
      match ← ((do
        let i11 ← pure p1.len
        let i12 ← pure (i11)
        let i13 ← pure (i12 == (0 : BitVec 64))
        if i13 then (do
          pure (.ret false))
        else (do
          pure .br10)) : Zig.CM Tgt mem_Allocator_resize__anon_d87227067220Locals mem_Allocator_resize__anon_d87227067220Exit) with
      | .br10 => (do
        let i17 ← Zig.callMC (mem_absorbSentinel__anon_5c5a1474fdd7 p1)
        let i18 ← pure i17.ptr
        let i19 ← pure i17.len
        let i20 ← Zig.mul false i19 (4 : BitVec 64) (safe := false)
        let i21 ← pure (i18)
        let i22 ← pure (⟨i21, i20⟩ : Zig.Slice)
        match ← ((do
          let i24 ← Zig.callRC (math_mul__anon_44faaf286c79 (4 : BitVec 64) p2)
          let i25 ← pure (Zig.isNonErr i24)
          if i25 then (do
            let i27 ← Zig.callRC (Zig.unwrapPayload i24)
            pure (.br23 i27))
          else (do
            let _i29 ← Zig.callRC (Zig.unwrapErr i24)
            pure (.ret false))) : Zig.CM Tgt mem_Allocator_resize__anon_d87227067220Locals mem_Allocator_resize__anon_d87227067220Exit) with
        | .br23 v23 => (do
          let i31 ← Zig.callRC (mem_Alignment_fromByteUnits (4 : BitVec 64))
          let i32 ← Zig.callMC Zig.returnAddress
          match ← ((do
            let i34 ← pure ((p0).vtable)
            let i35 ← Zig.callMC (Zig.ptrProject i34 (·.add 8))
            let i36 ← Zig.load (Zig.Ptr) 8 i35
            let i37 ← pure ((p0).ptr)
            let i38 ← (Zig.callC (Zig.extCall (Ext.call1 i36 i37 i22 i31 v23 i32)))
            pure (.br33 i38)) : Zig.CM Tgt mem_Allocator_resize__anon_d87227067220Locals mem_Allocator_resize__anon_d87227067220Exit) with
          | .br33 v33 => (do
            pure (.ret v33))
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_resize__anon_d87227067220Locals mem_Allocator_resize__anon_d87227067220Exit).run' (default : mem_Allocator_resize__anon_d87227067220Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_resize__anon_d87227067220

structure Buf_u32_fitLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive Buf_u32_fitExit where
  | ret (v : Bool)
  | br6

def Buf_u32_fit [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    modify (fun s => { s with local3 := p1 })
    match ← ((do
      let i7 ← Zig.add false p2 (1 : BitVec 64)
      let i8 ← Zig.callC (mem_Allocator_resize__anon_d87227067220 p0 p1 i7)
      let i9 ← pure (!i8)
      if i9 then (do
        pure (.ret false))
      else (do
        pure .br6)) : Zig.CM Tgt Buf_u32_fitLocals Buf_u32_fitExit) with
    | .br6 => (do
      let i14 ← pure (((← get).local3).ptr)
      let i15 ← Zig.callMC (Zig.ptrProject i14 (·.elem 4 p2))
      Zig.store (α := BitVec 32) 4 i15 (0 : BitVec 32)
      pure (.ret true))
    | e => pure e) : Zig.CM Tgt Buf_u32_fitLocals Buf_u32_fitExit).run' (default : Buf_u32_fitLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u32_fit

structure mem_Allocator_remap__anon_b5ccb0b97340Locals where
  deriving Inhabited

inductive mem_Allocator_remap__anon_b5ccb0b97340Exit where
  | ret (v : Option (Zig.Slice))
  | br3
  | br17
  | br30 (v : BitVec 64)
  | br41 (v : Option (Zig.Ptr))
  | br38 (v : Zig.Ptr)
  | br63
  | br70

def mem_Allocator_remap__anon_b5ccb0b97340 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Option (Zig.Slice)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p2)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        let _i7 ← Zig.callC (mem_Allocator_free__anon_85944fd5a0eb p0 p1)
        let i8 ← pure p1.ptr
        let i9 ← pure i8
        let i10 ← pure (i9)
        let i11 ← pure p1.len
        let _i12 ← Zig.add false i11 (1 : BitVec 64)
        let i13 ← pure (⟨i10, (0 : BitVec 64)⟩ : Zig.Slice)
        let i14 ← pure (some i13)
        pure (.ret i14))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_remap__anon_b5ccb0b97340Locals mem_Allocator_remap__anon_b5ccb0b97340Exit) with
    | .br3 => (do
      match ← ((do
        let i18 ← pure p1.len
        let i19 ← pure (i18)
        let i20 ← pure (i19 == (0 : BitVec 64))
        if i20 then (do
          pure (.ret none))
        else (do
          pure .br17)) : Zig.CM Tgt mem_Allocator_remap__anon_b5ccb0b97340Locals mem_Allocator_remap__anon_b5ccb0b97340Exit) with
      | .br17 => (do
        let i24 ← Zig.callMC (mem_absorbSentinel__anon_5c5a1474fdd7 p1)
        let i25 ← pure i24.ptr
        let i26 ← pure i24.len
        let i27 ← Zig.mul false i26 (4 : BitVec 64) (safe := false)
        let i28 ← pure (i25)
        let i29 ← pure (⟨i28, i27⟩ : Zig.Slice)
        match ← ((do
          let i31 ← Zig.callRC (math_mul__anon_44faaf286c79 (4 : BitVec 64) p2)
          let i32 ← pure (Zig.isNonErr i31)
          if i32 then (do
            let i34 ← Zig.callRC (Zig.unwrapPayload i31)
            pure (.br30 i34))
          else (do
            let _i36 ← Zig.callRC (Zig.unwrapErr i31)
            pure (.ret none))) : Zig.CM Tgt mem_Allocator_remap__anon_b5ccb0b97340Locals mem_Allocator_remap__anon_b5ccb0b97340Exit) with
        | .br30 v30 => (do
          match ← ((do
            let i39 ← Zig.callRC (mem_Alignment_fromByteUnits (4 : BitVec 64))
            let i40 ← Zig.callMC Zig.returnAddress
            match ← ((do
              let i42 ← pure ((p0).vtable)
              let i43 ← Zig.callMC (Zig.ptrProject i42 (·.add 16))
              let i44 ← Zig.load (Zig.Ptr) 8 i43
              let i45 ← pure ((p0).ptr)
              let i46 ← (Zig.callC (Zig.extCall (Ext.call2 i44 i45 i29 i39 v30 i40)))
              pure (.br41 i46)) : Zig.CM Tgt mem_Allocator_remap__anon_b5ccb0b97340Locals mem_Allocator_remap__anon_b5ccb0b97340Exit) with
            | .br41 v41 => (do
              let i48 ← pure ((v41).isSome)
              if i48 then (do
                let i50 ← Zig.optPayload v41
                pure (.br38 i50))
              else (do
                pure (.ret none)))
            | e => pure e) : Zig.CM Tgt mem_Allocator_remap__anon_b5ccb0b97340Locals mem_Allocator_remap__anon_b5ccb0b97340Exit) with
          | .br38 v38 => (do
            let i53 ← pure v38
            let i54 ← Zig.sub false v30 (0 : BitVec 64) (safe := false)
            let i55 ← pure (⟨i53, i54⟩ : Zig.Slice)
            let i56 ← pure i55.ptr
            let i57 ← pure i55.len
            let i58 ← pure (i57 == (0 : BitVec 64))
            let i59 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i56)))
            let i60 ← pure (i59 &&& (3 : BitVec 64))
            let i61 ← pure (i60 == (0 : BitVec 64))
            let i62 ← pure (i58 || i61)
            match ← ((do
              if i62 then (do
                pure .br63)
              else (do
                throw .panic)) : Zig.CM Tgt mem_Allocator_remap__anon_b5ccb0b97340Locals mem_Allocator_remap__anon_b5ccb0b97340Exit) with
            | .br63 => (do
              let i68 ← Zig.rem false i57 (4 : BitVec 64)
              let i69 ← pure (i68 == (0 : BitVec 64))
              match ← ((do
                if i69 then (do
                  pure .br70)
                else (do
                  throw .panic)) : Zig.CM Tgt mem_Allocator_remap__anon_b5ccb0b97340Locals mem_Allocator_remap__anon_b5ccb0b97340Exit) with
              | .br70 => (do
                let i75 ← Zig.divExact false i57 (4 : BitVec 64)
                let i76 ← Zig.callMC (Zig.checkAlign 4 i56 >>= fun _ => pure i56)
                let i77 ← pure (⟨i76, i75⟩ : Zig.Slice)
                pure (.ret i77))
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_remap__anon_b5ccb0b97340Locals mem_Allocator_remap__anon_b5ccb0b97340Exit).run' (default : mem_Allocator_remap__anon_b5ccb0b97340Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_remap__anon_b5ccb0b97340

structure Buf_u32_moveLocals where
  deriving Inhabited

inductive Buf_u32_moveExit where
  | ret (v : Option (Zig.Slice))
  | br3 (v : Zig.Slice)
  | br13
  | br26
  | br34

def Buf_u32_move [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Option (Zig.Slice)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.add false p2 (1 : BitVec 64)
      let i5 ← Zig.callC (mem_Allocator_remap__anon_b5ccb0b97340 p0 p1 i4)
      let i6 ← pure ((i5).isSome)
      if i6 then (do
        let i8 ← Zig.optPayload i5
        pure (.br3 i8))
      else (do
        pure (.ret none))) : Zig.CM Tgt Buf_u32_moveLocals Buf_u32_moveExit) with
    | .br3 v3 => (do
      let i11 ← pure v3.len
      let i12 ← pure (Zig.lt false p2 i11)
      match ← ((do
        if i12 then (do
          pure .br13)
        else (do
          throw .outOfBounds)) : Zig.CM Tgt Buf_u32_moveLocals Buf_u32_moveExit) with
      | .br13 => (do
        let i18 ← Zig.callMC (Zig.checkIndex v3.len p2) >>= fun _ => Zig.callMC (Zig.ptrProject v3.ptr (·.elem 4 p2))
        Zig.store (α := BitVec 32) 4 i18 (0 : BitVec 32)
        let i20 ← pure v3.ptr
        let i21 ← pure i20
        let i22 ← Zig.sub false p2 (0 : BitVec 64) (safe := false)
        let i23 ← pure v3.len
        let i24 ← Zig.add false p2 (1 : BitVec 64)
        let i25 ← pure (Zig.le false i24 i23)
        match ← ((do
          if i25 then (do
            pure .br26)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt Buf_u32_moveLocals Buf_u32_moveExit) with
        | .br26 => (do
          let i31 ← Zig.callMC (Zig.checkSliceEnd v3.len (0 : BitVec 64) i22 1 >>= fun _ => pure (⟨i21, i22⟩ : Zig.Slice))
          let i32 ← Zig.callMC (Zig.checkSentinelIndex i31.len i22 >>= fun _ => Zig.load (BitVec 32) 4 (i31.ptr.elem 4 i22))
          let i33 ← pure ((0 : BitVec 32) == i32)
          match ← ((do
            if i33 then (do
              pure .br34)
            else (do
              throw .panic)) : Zig.CM Tgt Buf_u32_moveLocals Buf_u32_moveExit) with
          | .br34 => (do
            let i39 ← pure (some i31)
            pure (.ret i39))
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Buf_u32_moveLocals Buf_u32_moveExit).run' (default : Buf_u32_moveLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u32_move

structure Buf_u32_resizeLocals where
  deriving Inhabited

inductive Buf_u32_resizeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br12
  | br25
  | br33

def Buf_u32_resize [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.add false p2 (1 : BitVec 64)
    let i4 ← Zig.callC (mem_Allocator_realloc__anon_9cee5a678d80 p0 p1 i3)
    match i4 with
    | .error _ => (do
      let i6 ← Zig.callRC (Zig.unwrapErr i4)
      let i7 ← pure (i6)
      let i8 ← pure ((.error i7) : Except Zig.ErrName (Zig.Slice))
      pure (.ret i8))
    | .ok v5 => (do
      let i10 ← pure v5.len
      let i11 ← pure (Zig.lt false p2 i10)
      match ← ((do
        if i11 then (do
          pure .br12)
        else (do
          throw .outOfBounds)) : Zig.CM Tgt Buf_u32_resizeLocals Buf_u32_resizeExit) with
      | .br12 => (do
        let i17 ← Zig.callMC (Zig.checkIndex v5.len p2) >>= fun _ => Zig.callMC (Zig.ptrProject v5.ptr (·.elem 4 p2))
        Zig.store (α := BitVec 32) 4 i17 (0 : BitVec 32)
        let i19 ← pure v5.ptr
        let i20 ← pure i19
        let i21 ← Zig.sub false p2 (0 : BitVec 64) (safe := false)
        let i22 ← pure v5.len
        let i23 ← Zig.add false p2 (1 : BitVec 64)
        let i24 ← pure (Zig.le false i23 i22)
        match ← ((do
          if i24 then (do
            pure .br25)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt Buf_u32_resizeLocals Buf_u32_resizeExit) with
        | .br25 => (do
          let i30 ← Zig.callMC (Zig.checkSliceEnd v5.len (0 : BitVec 64) i21 1 >>= fun _ => pure (⟨i20, i21⟩ : Zig.Slice))
          let i31 ← Zig.callMC (Zig.checkSentinelIndex i30.len i21 >>= fun _ => Zig.load (BitVec 32) 4 (i30.ptr.elem 4 i21))
          let i32 ← pure ((0 : BitVec 32) == i31)
          match ← ((do
            if i32 then (do
              pure .br33)
            else (do
              throw .panic)) : Zig.CM Tgt Buf_u32_resizeLocals Buf_u32_resizeExit) with
          | .br33 => (do
            let i38 ← pure ((.ok i30) : Except Zig.ErrName (Zig.Slice))
            pure (.ret i38))
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf_u32_resizeLocals Buf_u32_resizeExit).run' (default : Buf_u32_resizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u32_resize

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

structure mem_absorbSentinel__anon_2445b0d558b2Locals where
  local1 : Zig.Slice
  deriving Inhabited

inductive mem_absorbSentinel__anon_2445b0d558b2Exit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_2445b0d558b2 (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    modify (fun s => { s with local1 := p0 })
    let i6 ← pure (((← get).local1).len)
    let i7 ← Zig.add false i6 (1 : BitVec 64)
    let i8 ← pure (((← get).local1).ptr)
    let i9 ← pure i8
    let i10 ← Zig.sub false i7 (0 : BitVec 64) (safe := false)
    let i11 ← pure (⟨i9, i10⟩ : Zig.Slice)
    pure (.ret i11)) : Zig.MM mem_absorbSentinel__anon_2445b0d558b2Locals mem_absorbSentinel__anon_2445b0d558b2Exit).run' (default : mem_absorbSentinel__anon_2445b0d558b2Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_absorbSentinel__anon_2445b0d558b2

structure mem_Allocator_free__anon_0ba161b45e0aLocals where
  deriving Inhabited

inductive mem_Allocator_free__anon_0ba161b45e0aExit where
  | ret
  | br4
  | br15

def mem_Allocator_free__anon_0ba161b45e0a [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_2445b0d558b2 p1)
    let i3 ← pure (i2)
    match ← ((do
      let i5 ← pure i3.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        pure .ret)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_free__anon_0ba161b45e0aLocals mem_Allocator_free__anon_0ba161b45e0aExit) with
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
        let _i20 ← (Zig.callC (Zig.extCall (Ext.call3 i18 i19 i3 i13 i14)))
        pure .br15) : Zig.CM Tgt mem_Allocator_free__anon_0ba161b45e0aLocals mem_Allocator_free__anon_0ba161b45e0aExit) with
      | .br15 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_0ba161b45e0aLocals mem_Allocator_free__anon_0ba161b45e0aExit).run' (default : mem_Allocator_free__anon_0ba161b45e0aLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_0ba161b45e0a

structure mem_Allocator_reallocAdvanced__anon_b1876625f38fLocals where
  local20 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_reallocAdvanced__anon_b1876625f38fExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br9 (v : Except Zig.ErrName (Zig.Slice))
  | br4
  | br26
  | br35 (v : BitVec 64)
  | br45 (v : Option (Zig.Ptr))
  | br43
  | br64 (v : Option (Zig.Ptr))
  | br62 (v : Zig.Ptr)
  | br90
  | br99
  | br111
  | br120

def mem_Allocator_reallocAdvanced__anon_b1876625f38f [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) (p3 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s20 ← Zig.allocStack 24 8
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
            pure (.br9 i18))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_b1876625f38fLocals mem_Allocator_reallocAdvanced__anon_b1876625f38fExit) with
        | .br9 v9 => (do
          let i20 ← pure (← get).local20
          (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i20 v9)
          let i22 ← pure (i20)
          let i23 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i22)
          pure (.ret i23))
        | e => pure e)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_b1876625f38fLocals mem_Allocator_reallocAdvanced__anon_b1876625f38fExit) with
    | .br4 => (do
      match ← ((do
        let i27 ← pure (p2)
        let i28 ← pure (i27 == (0 : BitVec 64))
        if i28 then (do
          let _i30 ← Zig.callC (mem_Allocator_free__anon_0ba161b45e0a p0 p1)
          pure (.ret (.ok (⟨(⟨none, 18446744073709551615⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice) : Except Zig.ErrName (Zig.Slice))))
        else (do
          pure .br26)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_b1876625f38fLocals mem_Allocator_reallocAdvanced__anon_b1876625f38fExit) with
      | .br26 => (do
        let i33 ← Zig.callMC (mem_absorbSentinel__anon_2445b0d558b2 p1)
        let i34 ← pure (i33)
        match ← ((do
          let i36 ← Zig.callRC (math_mul__anon_44faaf286c79 (1 : BitVec 64) p2)
          let i37 ← pure (Zig.isNonErr i36)
          if i37 then (do
            let i39 ← Zig.callRC (Zig.unwrapPayload i36)
            pure (.br35 i39))
          else (do
            let _i41 ← Zig.callRC (Zig.unwrapErr i36)
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice))))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_b1876625f38fLocals mem_Allocator_reallocAdvanced__anon_b1876625f38fExit) with
        | .br35 v35 => (do
          match ← ((do
            let i44 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
            match ← ((do
              let i46 ← pure ((p0).vtable)
              let i47 ← Zig.callMC (Zig.ptrProject i46 (·.add 16))
              let i48 ← Zig.load (Zig.Ptr) 8 i47
              let i49 ← pure ((p0).ptr)
              let i50 ← (Zig.callC (Zig.extCall (Ext.call2 i48 i49 i34 i44 v35 p3)))
              pure (.br45 i50)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_b1876625f38fLocals mem_Allocator_reallocAdvanced__anon_b1876625f38fExit) with
            | .br45 v45 => (do
              let i52 ← pure ((v45).isSome)
              if i52 then (do
                let i54 ← Zig.optPayload v45
                let i55 ← pure i54
                let i56 ← Zig.sub false v35 (0 : BitVec 64) (safe := false)
                let i57 ← pure (⟨i55, i56⟩ : Zig.Slice)
                let i58 ← pure (i57)
                let i59 ← pure ((.ok i58) : Except Zig.ErrName (Zig.Slice))
                pure (.ret i59))
              else (do
                pure .br43))
            | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_b1876625f38fLocals mem_Allocator_reallocAdvanced__anon_b1876625f38fExit) with
          | .br43 => (do
            match ← ((do
              let i63 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
              match ← ((do
                let i65 ← pure ((p0).vtable)
                let i66 ← pure i65
                let i67 ← Zig.load (Zig.Ptr) 8 i66
                let i68 ← pure ((p0).ptr)
                let i69 ← (Zig.callC (Zig.extCall (Ext.call0 i67 i68 v35 i63 p3)))
                pure (.br64 i69)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_b1876625f38fLocals mem_Allocator_reallocAdvanced__anon_b1876625f38fExit) with
              | .br64 v64 => (do
                let i71 ← pure ((v64).isSome)
                if i71 then (do
                  let i73 ← Zig.optPayload v64
                  pure (.br62 i73))
                else (do
                  pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice)))))
              | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_b1876625f38fLocals mem_Allocator_reallocAdvanced__anon_b1876625f38fExit) with
            | .br62 v62 => (do
              let i76 ← pure i34.len
              let i77 ← pure (v35)
              let i78 ← pure (i76)
              let i79 ← pure (Zig.min false i77 i78)
              let i80 ← pure v62
              let i81 ← pure (i79)
              let i82 ← Zig.sub false i81 (0 : BitVec 64) (safe := false)
              let i83 ← pure (⟨i80, i82⟩ : Zig.Slice)
              let i84 ← pure i34.ptr
              let i85 ← pure i84
              let i86 ← pure (i79)
              let i87 ← Zig.sub false i86 (0 : BitVec 64) (safe := false)
              let i88 ← pure i34.len
              let i89 ← pure (Zig.le false i86 i88)
              match ← ((do
                if i89 then (do
                  pure .br90)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_b1876625f38fLocals mem_Allocator_reallocAdvanced__anon_b1876625f38fExit) with
              | .br90 => (do
                let i95 ← Zig.callMC (Zig.checkSliceEnd i34.len (0 : BitVec 64) i87 0 >>= fun _ => pure (⟨i85, i87⟩ : Zig.Slice))
                let i96 ← pure i83.len
                let i97 ← pure i95.len
                let i98 ← pure (i96 == i97)
                match ← ((do
                  if i98 then (do
                    pure .br99)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_b1876625f38fLocals mem_Allocator_reallocAdvanced__anon_b1876625f38fExit) with
                | .br99 => (do
                  let i104 ← pure i95.ptr
                  let i105 ← pure i83.ptr
                  let i106 ← Zig.callMC (Zig.ptrProject i104 (·.elem 1 i96))
                  let i107 ← Zig.callMC (Zig.ptrProject i105 (·.elem 1 i96))
                  let i108 ← Zig.callMC (Zig.ptrLe i106 i105)
                  let i109 ← Zig.callMC (Zig.ptrLe i107 i104)
                  let i110 ← pure (i108 || i109)
                  match ← ((do
                    if i110 then (do
                      pure .br111)
                    else (do
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_b1876625f38fLocals mem_Allocator_reallocAdvanced__anon_b1876625f38fExit) with
                  | .br111 => (do
                    Zig.callMC (Zig.memcpy 1 1 1 i83.ptr i104 i83.len i95.len)
                    let _i117 ← pure i34.len
                    Zig.callMC (Zig.memset (α := BitVec 8) 1 i34.ptr i34.len none)
                    let i119 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
                    match ← ((do
                      let i121 ← pure ((p0).vtable)
                      let i122 ← Zig.callMC (Zig.ptrProject i121 (·.add 24))
                      let i123 ← Zig.load (Zig.Ptr) 8 i122
                      let i124 ← pure ((p0).ptr)
                      let _i125 ← (Zig.callC (Zig.extCall (Ext.call3 i123 i124 i34 i119 p3)))
                      pure .br120) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_b1876625f38fLocals mem_Allocator_reallocAdvanced__anon_b1876625f38fExit) with
                    | .br120 => (do
                      let i127 ← pure v62
                      let i128 ← Zig.sub false v35 (0 : BitVec 64) (safe := false)
                      let i129 ← pure (⟨i127, i128⟩ : Zig.Slice)
                      let i130 ← pure (i129)
                      let i131 ← pure ((.ok i130) : Except Zig.ErrName (Zig.Slice))
                      pure (.ret i131))
                    | e => pure e)
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_b1876625f38fLocals mem_Allocator_reallocAdvanced__anon_b1876625f38fExit).run' { (default : mem_Allocator_reallocAdvanced__anon_b1876625f38fLocals) with local20 := s20 }
  Zig.free s20
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_reallocAdvanced__anon_b1876625f38f

structure mem_Allocator_realloc__anon_585fc7d079faLocals where
  deriving Inhabited

inductive mem_Allocator_realloc__anon_585fc7d079faExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_realloc__anon_585fc7d079fa [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.callMC Zig.returnAddress
    let i4 ← Zig.callC (mem_Allocator_reallocAdvanced__anon_b1876625f38f p0 p1 p2 i3)
    pure (.ret i4)) : Zig.CM Tgt mem_Allocator_realloc__anon_585fc7d079faLocals mem_Allocator_realloc__anon_585fc7d079faExit).run' (default : mem_Allocator_realloc__anon_585fc7d079faLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_realloc__anon_585fc7d079fa

structure Buf_u8_appendLocals where
  deriving Inhabited

inductive Buf_u8_appendExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br14
  | br25
  | br40
  | br48

def Buf_u8_append [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 8) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← pure p1.len
    let i4 ← Zig.add false i3 (2 : BitVec 64)
    let i5 ← Zig.callC (mem_Allocator_realloc__anon_585fc7d079fa p0 p1 i4)
    match i5 with
    | .error _ => (do
      let i7 ← Zig.callRC (Zig.unwrapErr i5)
      let i8 ← pure (i7)
      let i9 ← pure ((.error i8) : Except Zig.ErrName (Zig.Slice))
      pure (.ret i9))
    | .ok v6 => (do
      let i11 ← pure p1.len
      let i12 ← pure v6.len
      let i13 ← pure (Zig.lt false i11 i12)
      match ← ((do
        if i13 then (do
          pure .br14)
        else (do
          throw .outOfBounds)) : Zig.CM Tgt Buf_u8_appendLocals Buf_u8_appendExit) with
      | .br14 => (do
        let i19 ← Zig.callMC (Zig.checkIndex v6.len i11) >>= fun _ => Zig.callMC (Zig.ptrProject v6.ptr (·.elem 1 i11))
        Zig.store (α := BitVec 8) 1 i19 p2
        let i21 ← pure p1.len
        let i22 ← Zig.add false i21 (1 : BitVec 64)
        let i23 ← pure v6.len
        let i24 ← pure (Zig.lt false i22 i23)
        match ← ((do
          if i24 then (do
            pure .br25)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt Buf_u8_appendLocals Buf_u8_appendExit) with
        | .br25 => (do
          let i30 ← Zig.callMC (Zig.checkIndex v6.len i22) >>= fun _ => Zig.callMC (Zig.ptrProject v6.ptr (·.elem 1 i22))
          Zig.store (α := BitVec 8) 1 i30 (0 : BitVec 8)
          let i32 ← pure p1.len
          let i33 ← Zig.add false i32 (1 : BitVec 64)
          let i34 ← pure v6.ptr
          let i35 ← pure i34
          let i36 ← Zig.sub false i33 (0 : BitVec 64) (safe := false)
          let i37 ← pure v6.len
          let i38 ← Zig.add false i33 (1 : BitVec 64)
          let i39 ← pure (Zig.le false i38 i37)
          match ← ((do
            if i39 then (do
              pure .br40)
            else (do
              throw .outOfBounds)) : Zig.CM Tgt Buf_u8_appendLocals Buf_u8_appendExit) with
          | .br40 => (do
            let i45 ← Zig.callMC (Zig.checkSliceEnd v6.len (0 : BitVec 64) i36 1 >>= fun _ => pure (⟨i35, i36⟩ : Zig.Slice))
            let i46 ← Zig.callMC (Zig.checkSentinelIndex i45.len i36 >>= fun _ => Zig.load (BitVec 8) 1 (i45.ptr.elem 1 i36))
            let i47 ← pure ((0 : BitVec 8) == i46)
            match ← ((do
              if i47 then (do
                pure .br48)
              else (do
                throw .panic)) : Zig.CM Tgt Buf_u8_appendLocals Buf_u8_appendExit) with
            | .br48 => (do
              let i53 ← pure ((.ok i45) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i53))
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf_u8_appendLocals Buf_u8_appendExit).run' (default : Buf_u8_appendLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u8_append

structure mem_Allocator_resize__anon_d7f27f70af0fLocals where
  deriving Inhabited

inductive mem_Allocator_resize__anon_d7f27f70af0fExit where
  | ret (v : Bool)
  | br3
  | br10
  | br19 (v : BitVec 64)
  | br29 (v : Bool)

def mem_Allocator_resize__anon_d7f27f70af0f [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p2)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        let _i7 ← Zig.callC (mem_Allocator_free__anon_0ba161b45e0a p0 p1)
        pure (.ret true))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_resize__anon_d7f27f70af0fLocals mem_Allocator_resize__anon_d7f27f70af0fExit) with
    | .br3 => (do
      match ← ((do
        let i11 ← pure p1.len
        let i12 ← pure (i11)
        let i13 ← pure (i12 == (0 : BitVec 64))
        if i13 then (do
          pure (.ret false))
        else (do
          pure .br10)) : Zig.CM Tgt mem_Allocator_resize__anon_d7f27f70af0fLocals mem_Allocator_resize__anon_d7f27f70af0fExit) with
      | .br10 => (do
        let i17 ← Zig.callMC (mem_absorbSentinel__anon_2445b0d558b2 p1)
        let i18 ← pure (i17)
        match ← ((do
          let i20 ← Zig.callRC (math_mul__anon_44faaf286c79 (1 : BitVec 64) p2)
          let i21 ← pure (Zig.isNonErr i20)
          if i21 then (do
            let i23 ← Zig.callRC (Zig.unwrapPayload i20)
            pure (.br19 i23))
          else (do
            let _i25 ← Zig.callRC (Zig.unwrapErr i20)
            pure (.ret false))) : Zig.CM Tgt mem_Allocator_resize__anon_d7f27f70af0fLocals mem_Allocator_resize__anon_d7f27f70af0fExit) with
        | .br19 v19 => (do
          let i27 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
          let i28 ← Zig.callMC Zig.returnAddress
          match ← ((do
            let i30 ← pure ((p0).vtable)
            let i31 ← Zig.callMC (Zig.ptrProject i30 (·.add 8))
            let i32 ← Zig.load (Zig.Ptr) 8 i31
            let i33 ← pure ((p0).ptr)
            let i34 ← (Zig.callC (Zig.extCall (Ext.call1 i32 i33 i18 i27 v19 i28)))
            pure (.br29 i34)) : Zig.CM Tgt mem_Allocator_resize__anon_d7f27f70af0fLocals mem_Allocator_resize__anon_d7f27f70af0fExit) with
          | .br29 v29 => (do
            pure (.ret v29))
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_resize__anon_d7f27f70af0fLocals mem_Allocator_resize__anon_d7f27f70af0fExit).run' (default : mem_Allocator_resize__anon_d7f27f70af0fLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_resize__anon_d7f27f70af0f

structure Buf_u8_fitLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive Buf_u8_fitExit where
  | ret (v : Bool)
  | br6

def Buf_u8_fit [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    modify (fun s => { s with local3 := p1 })
    match ← ((do
      let i7 ← Zig.add false p2 (1 : BitVec 64)
      let i8 ← Zig.callC (mem_Allocator_resize__anon_d7f27f70af0f p0 p1 i7)
      let i9 ← pure (!i8)
      if i9 then (do
        pure (.ret false))
      else (do
        pure .br6)) : Zig.CM Tgt Buf_u8_fitLocals Buf_u8_fitExit) with
    | .br6 => (do
      let i14 ← pure (((← get).local3).ptr)
      let i15 ← Zig.callMC (Zig.ptrProject i14 (·.elem 1 p2))
      Zig.store (α := BitVec 8) 1 i15 (0 : BitVec 8)
      pure (.ret true))
    | e => pure e) : Zig.CM Tgt Buf_u8_fitLocals Buf_u8_fitExit).run' (default : Buf_u8_fitLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u8_fit

structure mem_Allocator_remap__anon_3903ca12077fLocals where
  deriving Inhabited

inductive mem_Allocator_remap__anon_3903ca12077fExit where
  | ret (v : Option (Zig.Slice))
  | br3
  | br17
  | br26 (v : BitVec 64)
  | br37 (v : Option (Zig.Ptr))
  | br34 (v : Zig.Ptr)

def mem_Allocator_remap__anon_3903ca12077f [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Option (Zig.Slice)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p2)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        let _i7 ← Zig.callC (mem_Allocator_free__anon_0ba161b45e0a p0 p1)
        let i8 ← pure p1.ptr
        let i9 ← pure i8
        let i10 ← pure (i9)
        let i11 ← pure p1.len
        let _i12 ← Zig.add false i11 (1 : BitVec 64)
        let i13 ← pure (⟨i10, (0 : BitVec 64)⟩ : Zig.Slice)
        let i14 ← pure (some i13)
        pure (.ret i14))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_remap__anon_3903ca12077fLocals mem_Allocator_remap__anon_3903ca12077fExit) with
    | .br3 => (do
      match ← ((do
        let i18 ← pure p1.len
        let i19 ← pure (i18)
        let i20 ← pure (i19 == (0 : BitVec 64))
        if i20 then (do
          pure (.ret none))
        else (do
          pure .br17)) : Zig.CM Tgt mem_Allocator_remap__anon_3903ca12077fLocals mem_Allocator_remap__anon_3903ca12077fExit) with
      | .br17 => (do
        let i24 ← Zig.callMC (mem_absorbSentinel__anon_2445b0d558b2 p1)
        let i25 ← pure (i24)
        match ← ((do
          let i27 ← Zig.callRC (math_mul__anon_44faaf286c79 (1 : BitVec 64) p2)
          let i28 ← pure (Zig.isNonErr i27)
          if i28 then (do
            let i30 ← Zig.callRC (Zig.unwrapPayload i27)
            pure (.br26 i30))
          else (do
            let _i32 ← Zig.callRC (Zig.unwrapErr i27)
            pure (.ret none))) : Zig.CM Tgt mem_Allocator_remap__anon_3903ca12077fLocals mem_Allocator_remap__anon_3903ca12077fExit) with
        | .br26 v26 => (do
          match ← ((do
            let i35 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
            let i36 ← Zig.callMC Zig.returnAddress
            match ← ((do
              let i38 ← pure ((p0).vtable)
              let i39 ← Zig.callMC (Zig.ptrProject i38 (·.add 16))
              let i40 ← Zig.load (Zig.Ptr) 8 i39
              let i41 ← pure ((p0).ptr)
              let i42 ← (Zig.callC (Zig.extCall (Ext.call2 i40 i41 i25 i35 v26 i36)))
              pure (.br37 i42)) : Zig.CM Tgt mem_Allocator_remap__anon_3903ca12077fLocals mem_Allocator_remap__anon_3903ca12077fExit) with
            | .br37 v37 => (do
              let i44 ← pure ((v37).isSome)
              if i44 then (do
                let i46 ← Zig.optPayload v37
                pure (.br34 i46))
              else (do
                pure (.ret none)))
            | e => pure e) : Zig.CM Tgt mem_Allocator_remap__anon_3903ca12077fLocals mem_Allocator_remap__anon_3903ca12077fExit) with
          | .br34 v34 => (do
            let i49 ← pure v34
            let i50 ← Zig.sub false v26 (0 : BitVec 64) (safe := false)
            let i51 ← pure (⟨i49, i50⟩ : Zig.Slice)
            let i52 ← pure (i51)
            pure (.ret i52))
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_remap__anon_3903ca12077fLocals mem_Allocator_remap__anon_3903ca12077fExit).run' (default : mem_Allocator_remap__anon_3903ca12077fLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_remap__anon_3903ca12077f

structure Buf_u8_moveLocals where
  deriving Inhabited

inductive Buf_u8_moveExit where
  | ret (v : Option (Zig.Slice))
  | br3 (v : Zig.Slice)
  | br13
  | br26
  | br34

def Buf_u8_move [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Option (Zig.Slice)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.add false p2 (1 : BitVec 64)
      let i5 ← Zig.callC (mem_Allocator_remap__anon_3903ca12077f p0 p1 i4)
      let i6 ← pure ((i5).isSome)
      if i6 then (do
        let i8 ← Zig.optPayload i5
        pure (.br3 i8))
      else (do
        pure (.ret none))) : Zig.CM Tgt Buf_u8_moveLocals Buf_u8_moveExit) with
    | .br3 v3 => (do
      let i11 ← pure v3.len
      let i12 ← pure (Zig.lt false p2 i11)
      match ← ((do
        if i12 then (do
          pure .br13)
        else (do
          throw .outOfBounds)) : Zig.CM Tgt Buf_u8_moveLocals Buf_u8_moveExit) with
      | .br13 => (do
        let i18 ← Zig.callMC (Zig.checkIndex v3.len p2) >>= fun _ => Zig.callMC (Zig.ptrProject v3.ptr (·.elem 1 p2))
        Zig.store (α := BitVec 8) 1 i18 (0 : BitVec 8)
        let i20 ← pure v3.ptr
        let i21 ← pure i20
        let i22 ← Zig.sub false p2 (0 : BitVec 64) (safe := false)
        let i23 ← pure v3.len
        let i24 ← Zig.add false p2 (1 : BitVec 64)
        let i25 ← pure (Zig.le false i24 i23)
        match ← ((do
          if i25 then (do
            pure .br26)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt Buf_u8_moveLocals Buf_u8_moveExit) with
        | .br26 => (do
          let i31 ← Zig.callMC (Zig.checkSliceEnd v3.len (0 : BitVec 64) i22 1 >>= fun _ => pure (⟨i21, i22⟩ : Zig.Slice))
          let i32 ← Zig.callMC (Zig.checkSentinelIndex i31.len i22 >>= fun _ => Zig.load (BitVec 8) 1 (i31.ptr.elem 1 i22))
          let i33 ← pure ((0 : BitVec 8) == i32)
          match ← ((do
            if i33 then (do
              pure .br34)
            else (do
              throw .panic)) : Zig.CM Tgt Buf_u8_moveLocals Buf_u8_moveExit) with
          | .br34 => (do
            let i39 ← pure (some i31)
            pure (.ret i39))
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Buf_u8_moveLocals Buf_u8_moveExit).run' (default : Buf_u8_moveLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u8_move

structure Buf_u8_resizeLocals where
  deriving Inhabited

inductive Buf_u8_resizeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br12
  | br25
  | br33

def Buf_u8_resize [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.add false p2 (1 : BitVec 64)
    let i4 ← Zig.callC (mem_Allocator_realloc__anon_585fc7d079fa p0 p1 i3)
    match i4 with
    | .error _ => (do
      let i6 ← Zig.callRC (Zig.unwrapErr i4)
      let i7 ← pure (i6)
      let i8 ← pure ((.error i7) : Except Zig.ErrName (Zig.Slice))
      pure (.ret i8))
    | .ok v5 => (do
      let i10 ← pure v5.len
      let i11 ← pure (Zig.lt false p2 i10)
      match ← ((do
        if i11 then (do
          pure .br12)
        else (do
          throw .outOfBounds)) : Zig.CM Tgt Buf_u8_resizeLocals Buf_u8_resizeExit) with
      | .br12 => (do
        let i17 ← Zig.callMC (Zig.checkIndex v5.len p2) >>= fun _ => Zig.callMC (Zig.ptrProject v5.ptr (·.elem 1 p2))
        Zig.store (α := BitVec 8) 1 i17 (0 : BitVec 8)
        let i19 ← pure v5.ptr
        let i20 ← pure i19
        let i21 ← Zig.sub false p2 (0 : BitVec 64) (safe := false)
        let i22 ← pure v5.len
        let i23 ← Zig.add false p2 (1 : BitVec 64)
        let i24 ← pure (Zig.le false i23 i22)
        match ← ((do
          if i24 then (do
            pure .br25)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt Buf_u8_resizeLocals Buf_u8_resizeExit) with
        | .br25 => (do
          let i30 ← Zig.callMC (Zig.checkSliceEnd v5.len (0 : BitVec 64) i21 1 >>= fun _ => pure (⟨i20, i21⟩ : Zig.Slice))
          let i31 ← Zig.callMC (Zig.checkSentinelIndex i30.len i21 >>= fun _ => Zig.load (BitVec 8) 1 (i30.ptr.elem 1 i21))
          let i32 ← pure ((0 : BitVec 8) == i31)
          match ← ((do
            if i32 then (do
              pure .br33)
            else (do
              throw .panic)) : Zig.CM Tgt Buf_u8_resizeLocals Buf_u8_resizeExit) with
          | .br33 => (do
            let i38 ← pure ((.ok i30) : Except Zig.ErrName (Zig.Slice))
            pure (.ret i38))
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt Buf_u8_resizeLocals Buf_u8_resizeExit).run' (default : Buf_u8_resizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] Buf_u8_resize

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch [Ext] : Tgt → Zig.ConcM Tgt Unit :=
  fun t => nomatch t

attribute [zig_run] dispatch

end Interfaces.Grow