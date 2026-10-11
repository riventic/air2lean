-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace ConstLocals

inductive UTag where
  | a
  | b
  deriving Repr, Inhabited, DecidableEq

def UTag.toBits : UTag → BitVec 1
  | .a => (0 : BitVec 1)
  | .b => (1 : BitVec 1)

def UTag.ofInt? (v : Int) : Option UTag :=
  if v = 0 then Option.some .a else if v = 1 then Option.some .b else Option.none

def UTag.isNamed (_ : UTag) : Bool := true

instance : Zig.Packed UTag 1 where
  toBits := UTag.toBits
  ofBits b := (UTag.ofInt? (Zig.val false b)).getD default
  valid b := (UTag.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc UTag where
  size := 1
  align := 1
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 1 ← Zig.Enc.decode bs
    match UTag.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

inductive U where
  | a (v : BitVec 32)
  | b (v : BitVec 32)
  | undef_a (v : BitVec 32) (written : List String)
  | undef_b (v : BitVec 32) (written : List String)
  deriving Repr, Inhabited, DecidableEq

def U.tag : U → UTag
  | .a _ => .a
  | .undef_a _ _ => .a
  | .b _ => .b
  | .undef_b _ _ => .b

def U.get_a : U → Zig.Result (BitVec 32)
  | .a v => pure v
  | .undef_a _ _ => throw .unspecified
  | _ => throw .panic

def U.modify_a (g : BitVec 32 → BitVec 32) : U → U
  | .a v => .a (g v)
  | .undef_a v w => .undef_a (g v) w
  | _ => .undef_a (g default) []

def U.setTag_a : U → U
  | .a v => .a v
  | .undef_a v w => .undef_a v w
  | _ => .undef_a default []

def U.set_a (v : BitVec 32) (_ : U) : U := .a v

def U.get_b : U → Zig.Result (BitVec 32)
  | .b v => pure v
  | .undef_b _ _ => throw .unspecified
  | _ => throw .panic

def U.modify_b (g : BitVec 32 → BitVec 32) : U → U
  | .b v => .b (g v)
  | .undef_b v w => .undef_b (g v) w
  | _ => .undef_b (g default) []

def U.setTag_b : U → U
  | .b v => .b v
  | .undef_b v w => .undef_b v w
  | _ => .undef_b default []

def U.set_b (v : BitVec 32) (_ : U) : U := .b v

instance : Zig.Enc U where
  size := 8
  align := 4
  encode v := match v with
    | .a x => Zig.Enc.fields 8 [(4, Zig.Enc.encode v.tag), (0, Zig.Enc.encode x)]
    | .b x => Zig.Enc.fields 8 [(4, Zig.Enc.encode v.tag), (0, Zig.Enc.encode x)]
    | .undef_a _ _ => Zig.Enc.fields 8 [(4, Zig.Enc.encode v.tag)]
    | .undef_b _ _ => Zig.Enc.fields 8 [(4, Zig.Enc.encode v.tag)]
  decode bs := do
    let t : UTag ← Zig.Enc.decodeAt bs 4
    match t with
    | .a => pure (.a (← Zig.Enc.decodeAt bs 0))
    | .b => pure (.b (← Zig.Enc.decodeAt bs 0))

inductive FTag where
  | a
  | b
  deriving Repr, Inhabited, DecidableEq

def FTag.toBits : FTag → BitVec 1
  | .a => (0 : BitVec 1)
  | .b => (1 : BitVec 1)

def FTag.ofInt? (v : Int) : Option FTag :=
  if v = 0 then Option.some .a else if v = 1 then Option.some .b else Option.none

def FTag.isNamed (_ : FTag) : Bool := true

instance : Zig.Packed FTag 1 where
  toBits := FTag.toBits
  ofBits b := (FTag.ofInt? (Zig.val false b)).getD default
  valid b := (FTag.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc FTag where
  size := 1
  align := 1
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 1 ← Zig.Enc.decode bs
    match FTag.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

inductive F where
  | a (v : BitVec 32)
  | b (v : BitVec 32)
  | undef_a (v : BitVec 32) (written : List String)
  | undef_b (v : BitVec 32) (written : List String)
  deriving Repr, Inhabited, DecidableEq

def F.tag : F → FTag
  | .a _ => .a
  | .undef_a _ _ => .a
  | .b _ => .b
  | .undef_b _ _ => .b

def F.get_a : F → Zig.Result (BitVec 32)
  | .a v => pure v
  | .undef_a _ _ => throw .unspecified
  | _ => throw .panic

def F.modify_a (g : BitVec 32 → BitVec 32) : F → F
  | .a v => .a (g v)
  | .undef_a v w => .undef_a (g v) w
  | _ => .undef_a (g default) []

def F.setTag_a : F → F
  | .a v => .a v
  | .undef_a v w => .undef_a v w
  | _ => .undef_a default []

def F.set_a (v : BitVec 32) (_ : F) : F := .a v

def F.get_b : F → Zig.Result (BitVec 32)
  | .b v => pure v
  | .undef_b _ _ => throw .unspecified
  | _ => throw .panic

def F.modify_b (g : BitVec 32 → BitVec 32) : F → F
  | .b v => .b (g v)
  | .undef_b v w => .undef_b (g v) w
  | _ => .undef_b (g default) []

def F.setTag_b : F → F
  | .b v => .b v
  | .undef_b v w => .undef_b v w
  | _ => .undef_b default []

def F.set_b (v : BitVec 32) (_ : F) : F := .b v

instance : Zig.Enc F where
  size := 8
  align := 4
  encode v := match v with
    | .a x => Zig.Enc.fields 8 [(4, Zig.Enc.encode v.tag), (0, Zig.Enc.encode x)]
    | .b x => Zig.Enc.fields 8 [(4, Zig.Enc.encode v.tag), (0, Zig.Enc.encode x)]
    | .undef_a _ _ => Zig.Enc.fields 8 [(4, Zig.Enc.encode v.tag)]
    | .undef_b _ _ => Zig.Enc.fields 8 [(4, Zig.Enc.encode v.tag)]
  decode bs := do
    let t : FTag ← Zig.Enc.decodeAt bs 4
    match t with
    | .a => pure (.a (← Zig.Enc.decodeAt bs 0))
    | .b => pure (.b (← Zig.Enc.decodeAt bs 0))

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: a constant
  (Zig.Enc.encode ((F.b (0 : BitVec 32)) : F), 4, .constGlobal),
  -- 1: a constant
  (Zig.Enc.encode ((U.b (-(7 : BitVec 32))) : U), 4, .constGlobal)]

structure bumpLocals where
  deriving Inhabited

inductive bumpExit where
  | ret

def bump (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i1 ← Zig.load (BitVec 32) 4 p0
    let i2 ← pure (Zig.addWrap i1 (1 : BitVec 32))
    Zig.store (α := BitVec 32) 4 p0 i2
    pure .ret) : Zig.MM bumpLocals bumpExit).run' (default : bumpLocals)
  match e with
  | .ret => pure ()

structure deadLocals where
  deriving Inhabited

inductive deadExit where
  | ret (v : BitVec 32)

def dead (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    pure (.ret (0 : BitVec 32))) : Zig.M deadLocals deadExit).run' (default : deadLocals)
  match e with
  | .ret v => pure v

structure readLocals where
  deriving Inhabited

inductive readExit where
  | ret (v : BitVec 32)
  | br4 (v : BitVec 32)

def read (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i2 ← Zig.load (U) 4 p0
    let i3 ← pure (U.tag i2)
    match ← ((do
      match i3 with
      | .a => (do
        let i8 ← Zig.callR (U.get_a i2)
        let i9 ← pure (Zig.addWrap i8 p1)
        pure (.br4 i9))
      | .b => (do
        let i11 ← Zig.callR (U.get_b i2)
        let i12 ← pure (i11)
        let i13 ← pure (Zig.addWrap i12 p1)
        pure (.br4 i13))) : Zig.MM readLocals readExit) with
    | .br4 v4 => (do
      pure (.ret v4))
    | e => pure e) : Zig.MM readLocals readExit).run' (default : readLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure liveLocals where
  deriving Inhabited

inductive liveExit where
  | ret (v : BitVec 32)

def live (p0 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.callM (read (⟨some 1, 0⟩ : Zig.Ptr) p0)
    pure (.ret i1)) : Zig.MM liveLocals liveExit).run' (default : liveLocals)
  match e with
  | .ret v => pure v

structure stackLocals where
  x : Zig.Ptr
  deriving Inhabited

inductive stackExit where
  | ret (v : BitVec 32)

def stack (p0 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s1 ← Zig.allocStack 4 4
  let e ← ((do
    let i1 ← pure (← get).x
    Zig.store (α := BitVec 32) 4 i1 p0
    let _i3 ← Zig.callM (bump i1)
    let i4 ← Zig.load (BitVec 32) 4 i1
    pure (.ret i4)) : Zig.MM stackLocals stackExit).run' { (default : stackLocals) with x := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

structure entryLocals where
  deriving Inhabited

inductive entryExit where
  | ret (v : BitVec 32)

def entry (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i2 ← Zig.callR (dead p0 p1)
    let i3 ← Zig.callM (live p0)
    let i4 ← pure (Zig.addWrap i2 i3)
    let i5 ← Zig.callM (stack p1)
    let i6 ← pure (Zig.addWrap i4 i5)
    pure (.ret i6)) : Zig.MM entryLocals entryExit).run' (default : entryLocals)
  match e with
  | .ret v => pure v

structure roundTripLocals where
  deriving Inhabited

inductive roundTripExit where
  | ret (v : BitVec 64)
  | br3
  | br10

def roundTrip (p0 : BitVec 64) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i1 ← pure (p0 ||| (4 : BitVec 64))
    let i2 ← pure (i1 != (0 : BitVec 64))
    match ← ((do
      if i2 then (do
        pure .br3)
      else (do
        throw .panic)) : Zig.MM roundTripLocals roundTripExit) with
    | .br3 => (do
      let i8 ← pure (i1 &&& (3 : BitVec 64))
      let i9 ← pure (i8 == (0 : BitVec 64))
      match ← ((do
        if i9 then (do
          pure .br10)
        else (do
          throw .panic)) : Zig.MM roundTripLocals roundTripExit) with
      | .br10 => (do
        let i15 ← Zig.callM (Zig.checkAddr 4 true (i1).toNat >>= fun _ => Zig.ptrFromAddr (i1).toNat)
        let i16 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i15)))
        let i17 ← pure (Zig.addWrap i16 (1 : BitVec 64))
        pure (.ret i17))
      | e => pure e)
    | e => pure e) : Zig.MM roundTripLocals roundTripExit).run' (default : roundTripLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end ConstLocals