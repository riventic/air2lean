-- air2lean-profile: {"allocator_model":"translated","correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.1"}}
-- air2lean-interfaces: {"ext":[{"field":"call0","type":"fn (*anyopaque, usize, mem.Alignment, usize) ?[*]u8"},{"field":"call1","type":"fn (*anyopaque, []u8, mem.Alignment, usize, usize) bool"},{"field":"call2","type":"fn (*anyopaque, []u8, mem.Alignment, usize, usize) ?[*]u8"},{"field":"call3","type":"fn (*anyopaque, []u8, mem.Alignment, usize) void"}],"interfaces":[{"contract":"Zig.Full.CAllocSpec","interface":"std.mem.Allocator","premise":"EXT-05","struct":"mem.Allocator.VTable"}]}
import ZigLean


namespace Interfaces.Raw

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
        let _i24 ← (Zig.callC (Zig.extCall (Ext.call3 i22 i23 i7 i17 i18)))
        pure .br19) : Zig.CM Tgt mem_Allocator_free__anon_10fd68fdc68dLocals mem_Allocator_free__anon_10fd68fdc68dExit) with
      | .br19 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_10fd68fdc68dLocals mem_Allocator_free__anon_10fd68fdc68dExit).run' (default : mem_Allocator_free__anon_10fd68fdc68dLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_10fd68fdc68d

structure mem_Allocator_resize__anon_270641f5f95cLocals where
  deriving Inhabited

inductive mem_Allocator_resize__anon_270641f5f95cExit where
  | ret (v : Bool)
  | br3
  | br10
  | br23 (v : BitVec 64)
  | br33 (v : Bool)

def mem_Allocator_resize__anon_270641f5f95c [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p2)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        let _i7 ← Zig.callC (mem_Allocator_free__anon_10fd68fdc68d p0 p1)
        pure (.ret true))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_resize__anon_270641f5f95cLocals mem_Allocator_resize__anon_270641f5f95cExit) with
    | .br3 => (do
      match ← ((do
        let i11 ← pure p1.len
        let i12 ← pure (i11)
        let i13 ← pure (i12 == (0 : BitVec 64))
        if i13 then (do
          pure (.ret false))
        else (do
          pure .br10)) : Zig.CM Tgt mem_Allocator_resize__anon_270641f5f95cLocals mem_Allocator_resize__anon_270641f5f95cExit) with
      | .br10 => (do
        let i17 ← Zig.callMC (mem_absorbSentinel__anon_6f5b4b6f7cb0 p1)
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
            pure (.ret false))) : Zig.CM Tgt mem_Allocator_resize__anon_270641f5f95cLocals mem_Allocator_resize__anon_270641f5f95cExit) with
        | .br23 v23 => (do
          let i31 ← Zig.callRC (mem_Alignment_fromByteUnits (4 : BitVec 64))
          let i32 ← Zig.callMC Zig.returnAddress
          match ← ((do
            let i34 ← pure ((p0).vtable)
            let i35 ← Zig.callMC (Zig.ptrProject i34 (·.add 8))
            let i36 ← Zig.load (Zig.Ptr) 8 i35
            let i37 ← pure ((p0).ptr)
            let i38 ← (Zig.callC (Zig.extCall (Ext.call1 i36 i37 i22 i31 v23 i32)))
            pure (.br33 i38)) : Zig.CM Tgt mem_Allocator_resize__anon_270641f5f95cLocals mem_Allocator_resize__anon_270641f5f95cExit) with
          | .br33 v33 => (do
            pure (.ret v33))
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_resize__anon_270641f5f95cLocals mem_Allocator_resize__anon_270641f5f95cExit).run' (default : mem_Allocator_resize__anon_270641f5f95cLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_resize__anon_270641f5f95c

structure fitLocals where
  deriving Inhabited

inductive fitExit where
  | ret (v : Bool)
  | br4 (v : Bool)

def fit [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    let i3 ← Zig.callMC Zig.returnAddress
    match ← ((do
      let i5 ← pure ((p0).vtable)
      let i6 ← Zig.callMC (Zig.ptrProject i5 (·.add 8))
      let i7 ← Zig.load (Zig.Ptr) 8 i6
      let i8 ← pure ((p0).ptr)
      let i9 ← (Zig.callC (Zig.extCall (Ext.call1 i7 i8 p1 mem_Alignment.«4» p2 i3)))
      pure (.br4 i9)) : Zig.CM Tgt fitLocals fitExit) with
    | .br4 v4 => (do
      pure (.ret v4))
    | e => pure e) : Zig.CM Tgt fitLocals fitExit).run' (default : fitLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] fit

structure giveLocals where
  deriving Inhabited

inductive giveExit where
  | ret
  | br3

def give [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC Zig.returnAddress
    match ← ((do
      let i4 ← pure ((p0).vtable)
      let i5 ← Zig.callMC (Zig.ptrProject i4 (·.add 24))
      let i6 ← Zig.load (Zig.Ptr) 8 i5
      let i7 ← pure ((p0).ptr)
      let _i8 ← (Zig.callC (Zig.extCall (Ext.call3 i6 i7 p1 mem_Alignment.«4» i2)))
      pure .br3) : Zig.CM Tgt giveLocals giveExit) with
    | .br3 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt giveLocals giveExit).run' (default : giveLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] give

structure moveLocals where
  deriving Inhabited

inductive moveExit where
  | ret (v : Option (Zig.Ptr))
  | br4 (v : Option (Zig.Ptr))

def move [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Option (Zig.Ptr)) := do
  let e ← ((do
    let i3 ← Zig.callMC Zig.returnAddress
    match ← ((do
      let i5 ← pure ((p0).vtable)
      let i6 ← Zig.callMC (Zig.ptrProject i5 (·.add 16))
      let i7 ← Zig.load (Zig.Ptr) 8 i6
      let i8 ← pure ((p0).ptr)
      let i9 ← (Zig.callC (Zig.extCall (Ext.call2 i7 i8 p1 mem_Alignment.«4» p2 i3)))
      pure (.br4 i9)) : Zig.CM Tgt moveLocals moveExit) with
    | .br4 v4 => (do
      pure (.ret v4))
    | e => pure e) : Zig.CM Tgt moveLocals moveExit).run' (default : moveLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] move

structure refitLocals where
  deriving Inhabited

inductive refitExit where
  | ret (v : Bool)

def refit [Ext] (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    let i3 ← Zig.callC (mem_Allocator_resize__anon_270641f5f95c p0 p1 p2)
    pure (.ret i3)) : Zig.CM Tgt refitLocals refitExit).run' (default : refitLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] refit

structure takeLocals where
  deriving Inhabited

inductive takeExit where
  | ret (v : Option (Zig.Ptr))
  | br3 (v : Option (Zig.Ptr))

def take [Ext] (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Option (Zig.Ptr)) := do
  let e ← ((do
    let i2 ← Zig.callMC Zig.returnAddress
    match ← ((do
      let i4 ← pure ((p0).vtable)
      let i5 ← pure i4
      let i6 ← Zig.load (Zig.Ptr) 8 i5
      let i7 ← pure ((p0).ptr)
      let i8 ← (Zig.callC (Zig.extCall (Ext.call0 i6 i7 p1 mem_Alignment.«4» i2)))
      pure (.br3 i8)) : Zig.CM Tgt takeLocals takeExit) with
    | .br3 v3 => (do
      pure (.ret v3))
    | e => pure e) : Zig.CM Tgt takeLocals takeExit).run' (default : takeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] take

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch [Ext] : Tgt → Zig.ConcM Tgt Unit :=
  fun t => nomatch t

attribute [zig_run] dispatch

end Interfaces.Raw