-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.16-musl","zig_version":"0.15.2"}}
import ZigLean


namespace AutoItems

inductive TTag where
  | a
  | b
  deriving Repr, Inhabited, DecidableEq

def TTag.toBits : TTag → BitVec 1
  | .a => (0 : BitVec 1)
  | .b => (1 : BitVec 1)

def TTag.ofInt? (v : Int) : Option TTag :=
  if v = 0 then Option.some .a else if v = 1 then Option.some .b else Option.none

def TTag.isNamed (_ : TTag) : Bool := true

instance : Zig.Packed TTag 1 where
  toBits := TTag.toBits
  ofBits b := (TTag.ofInt? (Zig.val false b)).getD default
  valid b := (TTag.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc TTag where
  size := 1
  align := 1
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 1 ← Zig.Enc.decode bs
    match TTag.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

inductive T where
  | a (v : BitVec 16)
  | b (v : BitVec 8)
  | undef_a (v : BitVec 16) (written : List String)
  | undef_b (v : BitVec 8) (written : List String)
  deriving Repr, Inhabited, DecidableEq

def T.tag : T → TTag
  | .a _ => .a
  | .undef_a _ _ => .a
  | .b _ => .b
  | .undef_b _ _ => .b

def T.get_a : T → Zig.Result (BitVec 16)
  | .a v => pure v
  | .undef_a _ _ => throw .unspecified
  | _ => throw .illegal

def T.modify_a (g : BitVec 16 → BitVec 16) : T → T
  | .a v => .a (g v)
  | .undef_a v w => .undef_a (g v) w
  | _ => .undef_a (g default) []

def T.setTag_a : T → T
  | .a v => .a v
  | .undef_a v w => .undef_a v w
  | _ => .undef_a default []

def T.set_a (v : BitVec 16) (_ : T) : T := .a v

def T.get_b : T → Zig.Result (BitVec 8)
  | .b v => pure v
  | .undef_b _ _ => throw .unspecified
  | _ => throw .illegal

def T.modify_b (g : BitVec 8 → BitVec 8) : T → T
  | .b v => .b (g v)
  | .undef_b v w => .undef_b (g v) w
  | _ => .undef_b (g default) []

def T.setTag_b : T → T
  | .b v => .b v
  | .undef_b v w => .undef_b v w
  | _ => .undef_b default []

def T.set_b (v : BitVec 8) (_ : T) : T := .b v

instance : Zig.Enc T where
  size := 4
  align := 2
  encode v := match v with
    | .a x => Zig.Enc.fields 4 [(2, Zig.Enc.encode v.tag), (0, Zig.Enc.encode x)]
    | .b x => Zig.Enc.fields 4 [(2, Zig.Enc.encode v.tag), (0, Zig.Enc.encode x)]
    | .undef_a _ _ => Zig.Enc.fields 4 [(2, Zig.Enc.encode v.tag)]
    | .undef_b _ _ => Zig.Enc.fields 4 [(2, Zig.Enc.encode v.tag)]
  decode bs := do
    let t : TTag ← Zig.Enc.decodeAt bs 2
    match t with
    | .a => pure (.a (← Zig.Enc.decodeAt bs 0))
    | .b => pure (.b (← Zig.Enc.decodeAt bs 0))

structure S where
  a : BitVec 16
  b : BitVec 16
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc S where
  size := 4
  align := 2
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.a), (2, Zig.Enc.encode v.b)]
  decode bs := do pure { a := ← Zig.Enc.decodeAt bs 0, b := ← Zig.Enc.decodeAt bs 2 }

structure structB1Locals where
  deriving Inhabited

inductive structB1Exit where
  | ret (v : BitVec 16)

def structB1 (p0 : BitVec 64) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Vector (S) 2) (p0 : BitVec 64)
    let i2 ← Zig.call (Zig.vindex i1 (1 : BitVec 64))
    let i3 ← pure ((i2).b)
    pure (.ret i3)) : Zig.M structB1Locals structB1Exit).run' (default : structB1Locals)
  match e with
  | .ret v => pure v

structure structsToIntLocals where
  deriving Inhabited

inductive structsToIntExit where
  | ret (v : BitVec 64)

def structsToInt (p0 : Vector (S) 2) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.reprCast (BitVec 64) (p0 : Vector (S) 2)
    pure (.ret i1)) : Zig.M structsToIntLocals structsToIntExit).run' (default : structsToIntLocals)
  match e with
  | .ret v => pure v

structure unionPayload1Locals where
  deriving Inhabited

inductive unionPayload1Exit where
  | ret (v : BitVec 16)
  | br4 (v : BitVec 16)

def unionPayload1 (p0 : BitVec 64) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Vector (T) 2) (p0 : BitVec 64)
    let i2 ← Zig.call (Zig.vindex i1 (1 : BitVec 64))
    let i3 ← pure (T.tag i2)
    match ← ((do
      match i3 with
      | .a => (do
        let i8 ← Zig.call (T.get_a i2)
        pure (.br4 i8))
      | .b => (do
        let i10 ← Zig.call (T.get_b i2)
        let i11 ← Zig.intCast false false 16 i10 (safe := false)
        pure (.br4 i11))) : Zig.M unionPayload1Locals unionPayload1Exit) with
    | .br4 v4 => (do
      pure (.ret v4))
    | e => pure e) : Zig.M unionPayload1Locals unionPayload1Exit).run' (default : unionPayload1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure unionsToIntLocals where
  deriving Inhabited

inductive unionsToIntExit where
  | ret (v : BitVec 64)

def unionsToInt (p0 : Vector (T) 2) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.reprCast (BitVec 64) (p0 : Vector (T) 2)
    pure (.ret i1)) : Zig.M unionsToIntLocals unionsToIntExit).run' (default : unionsToIntLocals)
  match e with
  | .ret v => pure v

end AutoItems