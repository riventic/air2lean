-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace PointerWidth.X64

structure View where
  first : Zig.Ptr
  rest : Zig.Slice
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc View where
  size := 24
  align := 8
  encode v := Zig.Enc.fields 24 [(0, Zig.Enc.encode v.first), (8, Zig.Enc.encode v.rest)]
  decode bs := do pure { first := ← Zig.Enc.decodeAt bs 0, rest := ← Zig.Enc.decodeAt bs 8 }

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

structure atLocals where
  deriving Inhabited

inductive atExit where
  | ret (v : BitVec 32)
  | br4

def «at» (p0 : Array (BitVec 32)) (p1 : BitVec 64) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i2 ← pure (Zig.len p0)
    let i3 ← pure (Zig.lt false p1 i2)
    match ← ((do
      if i3 then (do
        pure .br4)
      else (do
        throw .outOfBounds)) : Zig.M atLocals atExit) with
    | .br4 => (do
      let i9 ← Zig.call (Zig.index p0 p1)
      pure (.ret i9))
    | e => pure e) : Zig.M atLocals atExit).run' (default : atLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure byteCountLocals where
  deriving Inhabited

inductive byteCountExit where
  | ret (v : Option (BitVec 64))
  | br2

def byteCount (p0 : BitVec 64) : Zig.Result (Option (BitVec 64)) := do
  let e ← ((do
    let i1 ← pure (Zig.mulWithOverflow false p0 (4 : BitVec 64))
    match ← ((do
      let i3 ← pure ((i1).2)
      let i4 ← pure (i3 != (0 : BitVec 1))
      if i4 then (do
        pure (.ret none))
      else (do
        pure .br2)) : Zig.M byteCountLocals byteCountExit) with
    | .br2 => (do
      let i8 ← pure ((i1).1)
      let i9 ← pure (some i8)
      pure (.ret i9))
    | e => pure e) : Zig.M byteCountLocals byteCountExit).run' (default : byteCountLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure copy4Locals where
  deriving Inhabited

inductive copy4Exit where
  | ret
  | br5
  | br19

def copy4 (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← pure (⟨p0, (4 : BitVec 64)⟩ : Zig.Slice)
    let i3 ← pure i2.len
    let i4 ← pure (i3 == (4 : BitVec 64))
    match ← ((do
      if i4 then (do
        pure .br5)
      else (do
        throw .panic)) : Zig.MM copy4Locals copy4Exit) with
    | .br5 => (do
      let i10 ← pure i2.ptr
      let i11 ← pure (i10)
      let i12 ← pure (i11)
      let i13 ← pure (p1)
      let i14 ← Zig.callM (Zig.ptrProject i13 (·.elem 1 (4 : BitVec 64)))
      let i15 ← Zig.callM (Zig.ptrProject i12 (·.elem 1 (4 : BitVec 64)))
      let i16 ← Zig.callM (Zig.ptrLe i14 i12)
      let i17 ← Zig.callM (Zig.ptrLe i15 p1)
      let i18 ← pure (i16 || i17)
      match ← ((do
        if i18 then (do
          pure .br19)
        else (do
          throw .panic)) : Zig.MM copy4Locals copy4Exit) with
      | .br19 => (do
        Zig.callM (Zig.memmove 1 1 1 i11 p1 (4 : BitVec 64))
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.MM copy4Locals copy4Exit).run' (default : copy4Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure offsetOfLocals where
  local2 : Zig.Slice
  deriving Inhabited

inductive offsetOfExit where
  | ret (v : BitVec 64)
  | br8

def offsetOf (p0 : Zig.Slice) (p1 : BitVec 64) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with local2 := p0 })
    let i5 ← pure ((← get).local2)
    let i6 ← pure i5.len
    let i7 ← pure (Zig.lt false p1 i6)
    match ← ((do
      if i7 then (do
        pure .br8)
      else (do
        throw .outOfBounds)) : Zig.MM offsetOfLocals offsetOfExit) with
    | .br8 => (do
      let i13 ← Zig.callM (Zig.ptrProject i5.ptr (·.elem 4 p1))
      let i14 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i13)))
      let i16 ← pure (((← get).local2).ptr)
      let i17 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i16)))
      let i18 ← Zig.sub false i14 i17
      pure (.ret i18))
    | e => pure e) : Zig.MM offsetOfLocals offsetOfExit).run' (default : offsetOfLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure releaseLocals where
  deriving Inhabited

inductive releaseExit where
  | ret

def release (p0 : Zig.Allocator) (p1 : Zig.Slice) : Zig.MemM (Unit) := do
  let e ← ((do
    let _i2 ← Zig.callM (Zig.Allocator.free p0 4 p1)
    pure .ret) : Zig.MM releaseLocals releaseExit).run' (default : releaseLocals)
  match e with
  | .ret => pure ()

structure restLenLocals where
  deriving Inhabited

inductive restLenExit where
  | ret (v : BitVec 64)

def restLen (p0 : Zig.Ptr) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.add 8))
    let i2 ← Zig.callM (Zig.ptrProject i1 (·.add 8))
    let i3 ← Zig.load (BitVec 64) 8 i2
    pure (.ret i3)) : Zig.MM restLenLocals restLenExit).run' (default : restLenLocals)
  match e with
  | .ret v => pure v

structure setFirstLocals where
  deriving Inhabited

inductive setFirstExit where
  | ret

def setFirst (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.load (Zig.Ptr) 8 i2
    Zig.store (α := BitVec 32) 4 i3 p1
    pure .ret) : Zig.MM setFirstLocals setFirstExit).run' (default : setFirstLocals)
  match e with
  | .ret => pure ()

structure succLocals where
  deriving Inhabited

inductive succExit where
  | ret (v : BitVec 64)

def succ (p0 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.add false p0 (1 : BitVec 64)
    pure (.ret i1)) : Zig.M succLocals succExit).run' (default : succLocals)
  match e with
  | .ret v => pure v

structure zerosLocals where
  deriving Inhabited

inductive zerosExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def zeros (p0 : Zig.Allocator) (p1 : BitVec 64) : Zig.MemM (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.callM (Zig.Allocator.alloc p0 4 4 p1)
    match i2 with
    | .error _ => (do
      let i4 ← Zig.callR (Zig.unwrapErr i2)
      let i5 ← pure (i4)
      let i6 ← pure ((.error i5) : Except Zig.ErrName (Zig.Slice))
      pure (.ret i6))
    | .ok v3 => (do
      let _i8 ← pure v3.len
      Zig.callM (Zig.memset (α := BitVec 32) 4 v3.ptr v3.len (some (0 : BitVec 32)))
      let i10 ← pure ((.ok v3) : Except Zig.ErrName (Zig.Slice))
      pure (.ret i10))) : Zig.MM zerosLocals zerosExit).run' (default : zerosLocals)
  match e with
  | .ret v => pure v

end PointerWidth.X64