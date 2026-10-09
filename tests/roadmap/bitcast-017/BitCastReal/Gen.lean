-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"}}
import ZigLean


namespace BitCastReal

structure P where
  foo : BitVec 5
  bar : BitVec 7
  baz : BitVec 3
  qux : Bool
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed P 16 where
  toBits v := ((Zig.Packed.toBits v.foo).setWidth 16 <<< 0) ||| ((Zig.Packed.toBits v.bar).setWidth 16 <<< 5) ||| ((Zig.Packed.toBits v.baz).setWidth 16 <<< 12) ||| ((Zig.Packed.toBits v.qux).setWidth 16 <<< 15)
  ofBits b := { foo := Zig.Packed.get b 0, bar := Zig.Packed.get b 5, baz := Zig.Packed.get b 12, qux := Zig.Packed.get b 15 }

inductive E where
  | a
  | b
  | c
  deriving Repr, Inhabited, DecidableEq

def E.toBits : E → BitVec 8
  | .a => (0 : BitVec 8)
  | .b => (1 : BitVec 8)
  | .c => (2 : BitVec 8)

def E.ofInt? (v : Int) : Option E :=
  if v = 0 then Option.some .a else if v = 1 then Option.some .b else if v = 2 then Option.some .c else Option.none

def E.isNamed (_ : E) : Bool := true

instance : Zig.Packed E 8 where
  toBits := E.toBits
  ofBits b := (E.ofInt? (Zig.val false b)).getD default
  valid b := (E.ofInt? (Zig.val false b)).isSome

structure boolsToIntLocals where
  deriving Inhabited

inductive boolsToIntExit where
  | ret (v : BitVec 16)

def boolsToInt (p0 : Zig.Vec (Bool) 16) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← (pure (Zig.BitCast.ofBools (p0).lanes) : Zig.Result (BitVec 16))
    pure (.ret i1)) : Zig.M boolsToIntLocals boolsToIntExit).run' (default : boolsToIntLocals)
  match e with
  | .ret v => pure v

structure bytesToIntLocals where
  deriving Inhabited

inductive bytesToIntExit where
  | ret (v : BitVec 32)

def bytesToInt (p0 : Vector (BitVec 8) 4) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← (pure (Zig.BitCast.ofLanes (p0)) : Zig.Result (BitVec 32))
    pure (.ret i1)) : Zig.M bytesToIntLocals bytesToIntExit).run' (default : bytesToIntLocals)
  match e with
  | .ret v => pure v

structure enumToSignedLocals where
  deriving Inhabited

inductive enumToSignedExit where
  | ret (v : BitVec 8)

def enumToSigned (p0 : E) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i1 ← (pure (E.toBits (p0)) : Zig.Result (BitVec 8))
    pure (.ret i1)) : Zig.M enumToSignedLocals enumToSignedExit).run' (default : enumToSignedLocals)
  match e with
  | .ret v => pure v

structure intToEnumLocals where
  deriving Inhabited

inductive intToEnumExit where
  | ret (v : E)

def intToEnum (p0 : BitVec 8) : Zig.Result (E) := do
  let e ← ((do
    let i1 ← Zig.enumOf (E.ofInt? (Zig.val false p0))
    pure (.ret i1)) : Zig.M intToEnumLocals intToEnumExit).run' (default : intToEnumLocals)
  match e with
  | .ret v => pure v

structure intToPaddedLocals where
  deriving Inhabited

inductive intToPaddedExit where
  | ret (v : Vector (BitVec 24) 2)

def intToPadded (p0 : BitVec 48) : Zig.Result (Vector (BitVec 24) 2) := do
  let e ← ((do
    let i1 ← (pure (Zig.BitCast.toLanes (n := 2) (w := 24) (p0)) : Zig.Result (Vector (BitVec 24) 2))
    pure (.ret i1)) : Zig.M intToPaddedLocals intToPaddedExit).run' (default : intToPaddedLocals)
  match e with
  | .ret v => pure v

structure intToVecLocals where
  deriving Inhabited

inductive intToVecExit where
  | ret (v : Zig.Vec (BitVec 5) 4)

def intToVec (p0 : BitVec 20) : Zig.Result (Zig.Vec (BitVec 5) 4) := do
  let e ← ((do
    let i1 ← (pure ⟨Zig.BitCast.toLanes (n := 4) (w := 5) (p0)⟩ : Zig.Result (Zig.Vec (BitVec 5) 4))
    pure (.ret i1)) : Zig.M intToVecLocals intToVecExit).run' (default : intToVecLocals)
  match e with
  | .ret v => pure v

structure packedToBitsLocals where
  deriving Inhabited

inductive packedToBitsExit where
  | ret (v : Vector (BitVec 1) 16)

def packedToBits (p0 : P) : Zig.Result (Vector (BitVec 1) 16) := do
  let e ← ((do
    let i1 ← (((pure (Zig.Packed.toBits (p0)) : Zig.Result (BitVec 16)) >>= fun bits => pure (Zig.BitCast.toLanes (n := 16) (w := 1) (bits))) : Zig.Result (Vector (BitVec 1) 16))
    pure (.ret i1)) : Zig.M packedToBitsLocals packedToBitsExit).run' (default : packedToBitsLocals)
  match e with
  | .ret v => pure v

structure paddedToIntLocals where
  deriving Inhabited

inductive paddedToIntExit where
  | ret (v : BitVec 48)

def paddedToInt (p0 : Vector (BitVec 24) 2) : Zig.Result (BitVec 48) := do
  let e ← ((do
    let i1 ← (pure (Zig.BitCast.ofLanes (p0)) : Zig.Result (BitVec 48))
    pure (.ret i1)) : Zig.M paddedToIntLocals paddedToIntExit).run' (default : paddedToIntLocals)
  match e with
  | .ret v => pure v

structure vecToArrayLocals where
  deriving Inhabited

inductive vecToArrayExit where
  | ret (v : Vector (BitVec 4) 5)

def vecToArray (p0 : Zig.Vec (BitVec 5) 4) : Zig.Result (Vector (BitVec 4) 5) := do
  let e ← ((do
    let i1 ← (((pure (Zig.BitCast.ofLanes (p0).lanes) : Zig.Result (BitVec 20)) >>= fun bits => pure (Zig.BitCast.toLanes (n := 5) (w := 4) (bits))) : Zig.Result (Vector (BitVec 4) 5))
    pure (.ret i1)) : Zig.M vecToArrayLocals vecToArrayExit).run' (default : vecToArrayLocals)
  match e with
  | .ret v => pure v

structure vecToIntLocals where
  deriving Inhabited

inductive vecToIntExit where
  | ret (v : BitVec 20)

def vecToInt (p0 : Zig.Vec (BitVec 5) 4) : Zig.Result (BitVec 20) := do
  let e ← ((do
    let i1 ← (pure (Zig.BitCast.ofLanes (p0).lanes) : Zig.Result (BitVec 20))
    pure (.ret i1)) : Zig.M vecToIntLocals vecToIntExit).run' (default : vecToIntLocals)
  match e with
  | .ret v => pure v

end BitCastReal