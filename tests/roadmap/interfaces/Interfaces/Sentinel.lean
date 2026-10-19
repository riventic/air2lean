-- air2lean-profile: {"allocator_model":"translated","correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"}}
-- air2lean-interfaces: {"ext":[{"field":"call0","type":"fn (*anyopaque, usize, mem.Alignment, usize) ?[*]u8"},{"field":"call1","type":"fn (*anyopaque, []u8, mem.Alignment, usize, usize) ?[*]u8"},{"field":"call2","type":"fn (*anyopaque, []u8, mem.Alignment, usize) void"}],"interfaces":[{"contract":"Zig.Full.CAllocSpec","interface":"std.mem.Allocator","premise":"EXT-05","struct":"mem.Allocator.VTable"}]}
import ZigLean


namespace Interfaces.Sentinel

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

structure mem_Allocator_allocWithOptionsRetAddr__anon_e6e9421071c7Locals where
  deriving Inhabited

inductive mem_Allocator_allocWithOptionsRetAddr__anon_e6e9421071c7Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br4 (v : Except Zig.ErrName (Zig.Slice))
  | br21
  | br34
  | br42

def mem_Allocator_allocWithOptionsRetAddr__anon_e6e9421071c7 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
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
        pure (.br4 i13))) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_e6e9421071c7Locals mem_Allocator_allocWithOptionsRetAddr__anon_e6e9421071c7Exit) with
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
            throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_e6e9421071c7Locals mem_Allocator_allocWithOptionsRetAddr__anon_e6e9421071c7Exit) with
        | .br21 => (do
          let i26 ← Zig.callMC (Zig.checkIndex v15.len p1) >>= fun _ => Zig.callMC (Zig.ptrProject v15.ptr (·.elem 1 p1))
          Zig.store (α := BitVec 8) 1 i26 (0 : BitVec 8)
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
              throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_e6e9421071c7Locals mem_Allocator_allocWithOptionsRetAddr__anon_e6e9421071c7Exit) with
          | .br34 => (do
            let i39 ← Zig.callMC (Zig.checkSliceEnd v15.len (0 : BitVec 64) i30 1 >>= fun _ => pure (⟨i29, i30⟩ : Zig.Slice))
            let i40 ← Zig.callMC (Zig.checkSentinelIndex i39.len i30 >>= fun _ => Zig.load (BitVec 8) 1 (i39.ptr.elem 1 i30))
            let i41 ← pure ((0 : BitVec 8) == i40)
            match ← ((do
              if i41 then (do
                pure .br42)
              else (do
                throw .panic)) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_e6e9421071c7Locals mem_Allocator_allocWithOptionsRetAddr__anon_e6e9421071c7Exit) with
            | .br42 => (do
              let i47 ← pure ((.ok i39) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i47))
            | e => pure e)
          | e => pure e)
        | e => pure e))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithOptionsRetAddr__anon_e6e9421071c7Locals mem_Allocator_allocWithOptionsRetAddr__anon_e6e9421071c7Exit).run' (default : mem_Allocator_allocWithOptionsRetAddr__anon_e6e9421071c7Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_allocSentinel__anon_72739710ba98Locals where
  local4 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_allocSentinel__anon_72739710ba98Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_allocSentinel__anon_72739710ba98 [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s4 ← Zig.allocStack 24 8
  let e ← ((do
    let i2 ← Zig.callMC Zig.returnAddress
    let i3 ← Zig.callC (mem_Allocator_allocWithOptionsRetAddr__anon_e6e9421071c7 p0 p1 i2)
    let i4 ← pure (← get).local4
    (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i4 i3)
    let i6 ← pure (i4)
    let i7 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i6)
    pure (.ret i7)) : Zig.CM Tgt mem_Allocator_allocSentinel__anon_72739710ba98Locals mem_Allocator_allocSentinel__anon_72739710ba98Exit).run' { (default : mem_Allocator_allocSentinel__anon_72739710ba98Locals) with local4 := s4 }
  Zig.free s4
  match e with
  | .ret v => pure v

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
        let _i20 ← (Zig.callC (Zig.extCall (Ext.call2 i18 i19 i3 i13 i14)))
        pure .br15) : Zig.CM Tgt mem_Allocator_free__anon_0ba161b45e0aLocals mem_Allocator_free__anon_0ba161b45e0aExit) with
      | .br15 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_0ba161b45e0aLocals mem_Allocator_free__anon_0ba161b45e0aExit).run' (default : mem_Allocator_free__anon_0ba161b45e0aLocals)
  match e with
  | .ret => pure ()
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

def mem_Allocator_free__anon_1e60e7ef40f5 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_7342b53a30ed p1)
    let i3 ← pure (i2)
    match ← ((do
      let i5 ← pure i3.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        pure .ret)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_free__anon_1e60e7ef40f5Locals mem_Allocator_free__anon_1e60e7ef40f5Exit) with
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
        pure .br15) : Zig.CM Tgt mem_Allocator_free__anon_1e60e7ef40f5Locals mem_Allocator_free__anon_1e60e7ef40f5Exit) with
      | .br15 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_1e60e7ef40f5Locals mem_Allocator_free__anon_1e60e7ef40f5Exit).run' (default : mem_Allocator_free__anon_1e60e7ef40f5Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals where
  local20 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit where
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

def mem_Allocator_reallocAdvanced__anon_0df1ef68623e [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) (p3 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
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
            pure (.br9 i18))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
        | .br9 v9 => (do
          let i20 ← pure (← get).local20
          (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i20 v9)
          let i22 ← pure (i20)
          let i23 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i22)
          pure (.ret i23))
        | e => pure e)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
    | .br4 => (do
      match ← ((do
        let i27 ← pure (p2)
        let i28 ← pure (i27 == (0 : BitVec 64))
        if i28 then (do
          let _i30 ← Zig.callC (mem_Allocator_free__anon_1e60e7ef40f5 p0 p1)
          pure (.ret (.ok (⟨(⟨none, 18446744073709551615⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice) : Except Zig.ErrName (Zig.Slice))))
        else (do
          pure .br26)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
      | .br26 => (do
        let i33 ← Zig.callMC (mem_absorbSentinel__anon_7342b53a30ed p1)
        let i34 ← pure (i33)
        match ← ((do
          let i36 ← Zig.callRC (math_mul__anon_44faaf286c79 (1 : BitVec 64) p2)
          let i37 ← pure (Zig.isNonErr i36)
          if i37 then (do
            let i39 ← Zig.callRC (Zig.unwrapPayload i36)
            pure (.br35 i39))
          else (do
            let _i41 ← Zig.callRC (Zig.unwrapErr i36)
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice))))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
        | .br35 v35 => (do
          match ← ((do
            let i44 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
            match ← ((do
              let i46 ← pure ((p0).vtable)
              let i47 ← Zig.callMC (Zig.ptrProject i46 (·.add 16))
              let i48 ← Zig.load (Zig.Ptr) 8 i47
              let i49 ← pure ((p0).ptr)
              let i50 ← (Zig.callC (Zig.extCall (Ext.call1 i48 i49 i34 i44 v35 p3)))
              pure (.br45 i50)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
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
            | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
          | .br43 => (do
            match ← ((do
              let i63 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
              match ← ((do
                let i65 ← pure ((p0).vtable)
                let i66 ← pure i65
                let i67 ← Zig.load (Zig.Ptr) 8 i66
                let i68 ← pure ((p0).ptr)
                let i69 ← (Zig.callC (Zig.extCall (Ext.call0 i67 i68 v35 i63 p3)))
                pure (.br64 i69)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
              | .br64 v64 => (do
                let i71 ← pure ((v64).isSome)
                if i71 then (do
                  let i73 ← Zig.optPayload v64
                  pure (.br62 i73))
                else (do
                  pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice)))))
              | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
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
                  throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
              | .br90 => (do
                let i95 ← Zig.callMC (Zig.checkSliceEnd i34.len (0 : BitVec 64) i87 0 >>= fun _ => pure (⟨i85, i87⟩ : Zig.Slice))
                let i96 ← pure i83.len
                let i97 ← pure i95.len
                let i98 ← pure (i96 == i97)
                match ← ((do
                  if i98 then (do
                    pure .br99)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
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
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
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
                      let _i125 ← (Zig.callC (Zig.extCall (Ext.call2 i123 i124 i34 i119 p3)))
                      pure .br120) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
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
    | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit).run' { (default : mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals) with local20 := s20 }
  Zig.free s20
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_realloc__anon_af0c43114565Locals where
  deriving Inhabited

inductive mem_Allocator_realloc__anon_af0c43114565Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_realloc__anon_af0c43114565 [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.callMC Zig.returnAddress
    let i4 ← Zig.callC (mem_Allocator_reallocAdvanced__anon_0df1ef68623e p0 p1 p2 i3)
    pure (.ret i4)) : Zig.CM Tgt mem_Allocator_realloc__anon_af0c43114565Locals mem_Allocator_realloc__anon_af0c43114565Exit).run' (default : mem_Allocator_realloc__anon_af0c43114565Locals)
  match e with
  | .ret v => pure v

structure appendLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive appendExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br27
  | br39
  | br55
  | br63

def append [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 8) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
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
    let i17 ← Zig.callC (mem_Allocator_realloc__anon_af0c43114565 p0 i13 i16)
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
          throw .outOfBounds)) : Zig.CM Tgt appendLocals appendExit) with
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
            throw .outOfBounds)) : Zig.CM Tgt appendLocals appendExit) with
        | .br39 => (do
          let i44 ← Zig.callMC (Zig.checkIndex v18.len i36) >>= fun _ => Zig.callMC (Zig.ptrProject v18.ptr (·.elem 1 i36))
          Zig.store (α := BitVec 8) 1 i44 (0 : BitVec 8)
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
              throw .outOfBounds)) : Zig.CM Tgt appendLocals appendExit) with
          | .br55 => (do
            let i60 ← Zig.callMC (Zig.checkSliceEnd v18.len (0 : BitVec 64) i51 1 >>= fun _ => pure (⟨i50, i51⟩ : Zig.Slice))
            let i61 ← Zig.callMC (Zig.checkSentinelIndex i60.len i51 >>= fun _ => Zig.load (BitVec 8) 1 (i60.ptr.elem 1 i51))
            let i62 ← pure ((0 : BitVec 8) == i61)
            match ← ((do
              if i62 then (do
                pure .br63)
              else (do
                throw .panic)) : Zig.CM Tgt appendLocals appendExit) with
            | .br63 => (do
              let i68 ← pure ((.ok i60) : Except Zig.ErrName (Zig.Slice))
              pure (.ret i68))
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt appendLocals appendExit).run' (default : appendLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure makeLocals where
  deriving Inhabited

inductive makeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def make [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.callC (mem_Allocator_allocSentinel__anon_72739710ba98 p0 p1)
    let i3 ← pure (i2)
    pure (.ret i3)) : Zig.CM Tgt makeLocals makeExit).run' (default : makeLocals)
  match e with
  | .ret v => pure v

structure releaseLocals where
  deriving Inhabited

inductive releaseExit where
  | ret

def release [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let _i2 ← Zig.callC (mem_Allocator_free__anon_0ba161b45e0a p0 p1)
    pure .ret) : Zig.CM Tgt releaseLocals releaseExit).run' (default : releaseLocals)
  match e with
  | .ret => pure ()

structure resizeLocals where
  local3 : Zig.Slice
  deriving Inhabited

inductive resizeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br23
  | br36
  | br44

def resize [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    modify (fun s => { s with local3 := p1 })
    let i8 ← pure (((← get).local3).len)
    let i9 ← Zig.add false i8 (1 : BitVec 64)
    let i10 ← pure (((← get).local3).ptr)
    let i11 ← pure i10
    let i12 ← Zig.sub false i9 (0 : BitVec 64) (safe := false)
    let i13 ← pure (⟨i11, i12⟩ : Zig.Slice)
    let i14 ← Zig.add false p2 (1 : BitVec 64)
    let i15 ← Zig.callC (mem_Allocator_realloc__anon_af0c43114565 p0 i13 i14)
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
          throw .outOfBounds)) : Zig.CM Tgt resizeLocals resizeExit) with
      | .br23 => (do
        let i28 ← Zig.callMC (Zig.checkIndex v16.len p2) >>= fun _ => Zig.callMC (Zig.ptrProject v16.ptr (·.elem 1 p2))
        Zig.store (α := BitVec 8) 1 i28 (0 : BitVec 8)
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
            throw .outOfBounds)) : Zig.CM Tgt resizeLocals resizeExit) with
        | .br36 => (do
          let i41 ← Zig.callMC (Zig.checkSliceEnd v16.len (0 : BitVec 64) i32 1 >>= fun _ => pure (⟨i31, i32⟩ : Zig.Slice))
          let i42 ← Zig.callMC (Zig.checkSentinelIndex i41.len i32 >>= fun _ => Zig.load (BitVec 8) 1 (i41.ptr.elem 1 i32))
          let i43 ← pure ((0 : BitVec 8) == i42)
          match ← ((do
            if i43 then (do
              pure .br44)
            else (do
              throw .panic)) : Zig.CM Tgt resizeLocals resizeExit) with
          | .br44 => (do
            let i49 ← pure ((.ok i41) : Except Zig.ErrName (Zig.Slice))
            pure (.ret i49))
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.CM Tgt resizeLocals resizeExit).run' (default : resizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch [Ext] : Tgt → Zig.ConcM Tgt Unit :=
  fun t => nomatch t

end Interfaces.Sentinel