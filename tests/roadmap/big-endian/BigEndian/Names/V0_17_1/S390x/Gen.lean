-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"arch11","endian":"big","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["dfp_packed_conversion","dfp_zoned_conversion","distinct_ops","enhanced_dat_2","execution_hint","fast_serialization","fp_extension","high_word","interlocked_access1","load_and_trap","load_and_zero_rightmost_byte","load_store_on_cond","load_store_on_cond_2","message_security_assist_extension3","message_security_assist_extension4","message_security_assist_extension5","miscellaneous_extensions","population_count","processor_assist","reset_reference_bits_multiple","transactional_execution","vector"],"float_mode":"per-instruction","name":"abi64-be-v1","pointer_bits":64,"schema":12,"target_triple":"s390x-linux.5.10...7.2-musl","zig_version":"0.17.1"}}
import ZigLean


namespace BigEndian.Names.V0_17_1.S390x

open scoped Zig.BigEndian

structure Level where
  bits : BitVec 16
  deriving Repr, Inhabited, DecidableEq

def Level.low : Level := ⟨(1 : BitVec 16)⟩
def Level.high : Level := ⟨(4660 : BitVec 16)⟩

def Level.toBits (e : Level) : BitVec 16 := e.bits

def Level.ofInt? (v : Int) : Option Level :=
  if 0 ≤ v ∧ v ≤ 65535 then Option.some ⟨BitVec.ofInt 16 v⟩ else Option.none

def Level.isNamed (e : Level) : Bool := e.bits == (1 : BitVec 16) || e.bits == (4660 : BitVec 16)

instance : Zig.Packed Level 16 where
  toBits := Level.toBits
  ofBits b := ⟨b⟩

inductive Color where
  | red
  | green
  | blue
  deriving Repr, Inhabited, DecidableEq

def Color.toBits : Color → BitVec 2
  | .red => (0 : BitVec 2)
  | .green => (1 : BitVec 2)
  | .blue => (2 : BitVec 2)

def Color.ofInt? (v : Int) : Option Color :=
  if v = 0 then Option.some .red else if v = 1 then Option.some .green else if v = 2 then Option.some .blue else Option.none

def Color.isNamed (_ : Color) : Bool := true

instance : Zig.Packed Color 2 where
  toBits := Color.toBits
  ofBits b := (Color.ofInt? (Zig.val false b)).getD default
  valid b := (Color.ofInt? (Zig.val false b)).isSome

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: the name of Color.red
  (Zig.Enc.encode (#v[114, 101, 100, 0] : Vector (BitVec 8) 4), 1, .constGlobal),
  -- 1: the name of Color.green
  (Zig.Enc.encode (#v[103, 114, 101, 101, 110, 0] : Vector (BitVec 8) 6), 1, .constGlobal),
  -- 2: the name of Color.blue
  (Zig.Enc.encode (#v[98, 108, 117, 101, 0] : Vector (BitVec 8) 5), 1, .constGlobal),
  -- 3: the name of Level.low
  (Zig.Enc.encode (#v[108, 111, 119, 0] : Vector (BitVec 8) 4), 1, .constGlobal),
  -- 4: the name of Level.high
  (Zig.Enc.encode (#v[104, 105, 103, 104, 0] : Vector (BitVec 8) 5), 1, .constGlobal),
  -- 5: the name of error.Empty
  (Zig.Enc.encode (#v[69, 109, 112, 116, 121, 0] : Vector (BitVec 8) 6), 1, .constGlobal),
  -- 6: the name of error.TooLong
  (Zig.Enc.encode (#v[84, 111, 111, 76, 111, 110, 103, 0] : Vector (BitVec 8) 8), 1, .constGlobal)]

def Color.tagName (e : Color) : Zig.Result Zig.Slice :=
  match e with
  | .red => pure ⟨⟨some 0, 0⟩, 3⟩
  | .green => pure ⟨⟨some 1, 0⟩, 5⟩
  | .blue => pure ⟨⟨some 2, 0⟩, 4⟩

def Level.tagName (e : Level) : Zig.Result Zig.Slice :=
  if e.toBits == (1 : BitVec 16) then pure ⟨⟨some 3, 0⟩, 3⟩ else
  if e.toBits == (4660 : BitVec 16) then pure ⟨⟨some 4, 0⟩, 4⟩ else
  throw .illegal

def errorNameOf (e : Zig.ErrName) : Zig.Result Zig.Slice :=
  if e = "Empty" then pure ⟨⟨some 5, 0⟩, 5⟩ else
  if e = "TooLong" then pure ⟨⟨some 6, 0⟩, 7⟩ else
  throw .unspecified

structure colorNameLocals where
  deriving Inhabited

inductive colorNameExit where
  | ret (v : Zig.Slice)
  | br2

def colorName (p0 : Color) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    let i1 ← pure (Color.isNamed p0)
    match ← ((do
      if i1 then (do
        pure .br2)
      else (do
        throw .panic)) : Zig.MM colorNameLocals colorNameExit) with
    | .br2 => (do
      let i7 ← Zig.callR (Color.tagName p0)
      pure (.ret i7))
    | e => pure e) : Zig.MM colorNameLocals colorNameExit).run' (default : colorNameLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] colorName

structure faultNameLocals where
  deriving Inhabited

inductive faultNameExit where
  | ret (v : Zig.Slice)

def faultName (p0 : Zig.ErrName) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    let i1 ← pure (p0)
    let i2 ← Zig.callR (errorNameOf i1)
    pure (.ret i2)) : Zig.MM faultNameLocals faultNameExit).run' (default : faultNameLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] faultName

structure levelNameLocals where
  deriving Inhabited

inductive levelNameExit where
  | ret (v : Zig.Slice)
  | br2

def levelName (p0 : Level) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    let i1 ← pure (Level.isNamed p0)
    match ← ((do
      if i1 then (do
        pure .br2)
      else (do
        throw .panic)) : Zig.MM levelNameLocals levelNameExit) with
    | .br2 => (do
      let i7 ← Zig.callR (Level.tagName p0)
      pure (.ret i7))
    | e => pure e) : Zig.MM levelNameLocals levelNameExit).run' (default : levelNameLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] levelName

structure nameByteLocals where
  deriving Inhabited

inductive nameByteExit where
  | ret (v : BitVec 8)
  | br3
  | br11

def nameByte (p0 : Color) (p1 : BitVec 64) : Zig.MemM (BitVec 8) := do
  let e ← ((do
    let i2 ← pure (Color.isNamed p0)
    match ← ((do
      if i2 then (do
        pure .br3)
      else (do
        throw .panic)) : Zig.MM nameByteLocals nameByteExit) with
    | .br3 => (do
      let i8 ← Zig.callR (Color.tagName p0)
      let i9 ← pure i8.len
      let i10 ← pure (Zig.le false p1 i9)
      match ← ((do
        if i10 then (do
          pure .br11)
        else (do
          throw .outOfBounds)) : Zig.MM nameByteLocals nameByteExit) with
      | .br11 => (do
        let i16 ← Zig.callM (Zig.checkSentinelIndex i8.len p1 >>= fun _ => Zig.load (BitVec 8) 1 (i8.ptr.elem 1 p1))
        pure (.ret i16))
      | e => pure e)
    | e => pure e) : Zig.MM nameByteLocals nameByteExit).run' (default : nameByteLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] nameByte

structure storedLenByteLocals where
  s : Zig.Ptr
  deriving Inhabited

inductive storedLenByteExit where
  | ret (v : BitVec 8)
  | br4
  | br15

def storedLenByte (p0 : Color) (p1 : BitVec 64) : Zig.MemM (BitVec 8) := do
  let s2 ← Zig.allocStack 16 8
  let e ← ((do
    let i2 ← pure (← get).s
    let i3 ← pure (Color.isNamed p0)
    match ← ((do
      if i3 then (do
        pure .br4)
      else (do
        throw .panic)) : Zig.MM storedLenByteLocals storedLenByteExit) with
    | .br4 => (do
      let i9 ← Zig.callR (Color.tagName p0)
      let i10 ← pure (i9)
      Zig.store (α := Zig.Slice) 8 i2 i10
      let i12 ← pure (i2)
      let i13 ← Zig.add false (8 : BitVec 64) p1
      let i14 ← pure (Zig.lt false i13 (16 : BitVec 64))
      match ← ((do
        if i14 then (do
          pure .br15)
        else (do
          throw .outOfBounds)) : Zig.MM storedLenByteLocals storedLenByteExit) with
      | .br15 => (do
        let i20 ← Zig.callM (Zig.checkIndex (16 : BitVec 64) i13 >>= fun _ => Zig.load (BitVec 8) 1 (i12.elem 1 i13))
        pure (.ret i20))
      | e => pure e)
    | e => pure e) : Zig.MM storedLenByteLocals storedLenByteExit).run' { (default : storedLenByteLocals) with s := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] storedLenByte

end BigEndian.Names.V0_17_1.S390x