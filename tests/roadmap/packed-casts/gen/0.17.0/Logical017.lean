-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"}}
import ZigLean


namespace Logical017

structure Half where
  lo : BitVec 8
  hi : BitVec 8
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Half 16 where
  toBits v := ((Zig.Packed.toBits v.lo).setWidth 16 <<< 0) ||| ((Zig.Packed.toBits v.hi).setWidth 16 <<< 8)
  ofBits b := { lo := Zig.Packed.get b 0, hi := Zig.Packed.get b 8 }

instance : Zig.Enc Half where
  size := 2
  align := 2
  encode v := Zig.Enc.encode (Zig.Packed.toBits v)
  decode bs := do
    let b : BitVec 16 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

structure U where
  bytes : Vector Zig.Byte 2
  deriving Repr, Inhabited, DecidableEq

def U.get_i (u : U) : Zig.Result (BitVec 16) := Zig.PackedU.get (BitVec 16) u.bytes

def U.modify_i (g : BitVec 16 → BitVec 16) (u : U) : U :=
  ⟨Zig.PackedU.set u.bytes (g (Zig.Raw.getD (Zig.PackedU.get (BitVec 16) u.bytes)))⟩

def U.get_h (u : U) : Zig.Result (Zig.F16) := Zig.PackedU.get (Zig.F16) u.bytes

def U.modify_h (g : Zig.F16 → Zig.F16) (u : U) : U :=
  ⟨Zig.PackedU.set u.bytes (g (Zig.Raw.getD (Zig.PackedU.get (Zig.F16) u.bytes)))⟩

def U.get_p (u : U) : Zig.Result (Half) := Zig.PackedU.get (Half) u.bytes

def U.modify_p (g : Half → Half) (u : U) : U :=
  ⟨Zig.PackedU.set u.bytes (g (Zig.Raw.getD (Zig.PackedU.get (Half) u.bytes)))⟩

instance : Zig.Packed U 16 where
  toBits u := Zig.PackedU.bitsOf 16 u.bytes.toArray
  ofBits b := ⟨Zig.Raw.ofArray 2 (Zig.intBytes b)⟩
  mask u := Zig.PackedU.maskOf 16 u.bytes.toArray

instance : Zig.Enc U where
  size := 2
  align := 2
  encode v := v.bytes.toArray
  decode bs := pure ⟨Zig.Raw.ofArray 2 bs⟩

inductive Mode where
  | off
  | low
  | high
  deriving Repr, Inhabited, DecidableEq

def Mode.toBits : Mode → BitVec 2
  | .off => (0 : BitVec 2)
  | .low => (1 : BitVec 2)
  | .high => (2 : BitVec 2)

def Mode.ofInt? (v : Int) : Option Mode :=
  if v = 0 then Option.some .off else if v = 1 then Option.some .low else if v = 2 then Option.some .high else Option.none

def Mode.isNamed (_ : Mode) : Bool := true

instance : Zig.Packed Mode 2 where
  toBits := Mode.toBits
  ofBits b := (Mode.ofInt? (Zig.val false b)).getD default
  valid b := (Mode.ofInt? (Zig.val false b)).isSome

structure Nib where
  a : BitVec 2
  m : Mode
  b : BitVec 2
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Nib 6 where
  toBits v := ((Zig.Packed.toBits v.a).setWidth 6 <<< 0) ||| ((Zig.Packed.toBits v.m).setWidth 6 <<< 2) ||| ((Zig.Packed.toBits v.b).setWidth 6 <<< 4)
  ofBits b := { a := Zig.Packed.get b 0, m := Zig.Packed.get b 2, b := Zig.Packed.get b 4 }
  valid b := Zig.Packed.validAt (Mode) b 2

structure FH where
  lo : Zig.F16
  hi : BitVec 16
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed FH 32 where
  toBits v := ((Zig.Packed.toBits v.lo).setWidth 32 <<< 0) ||| ((Zig.Packed.toBits v.hi).setWidth 32 <<< 16)
  ofBits b := { lo := Zig.Packed.get b 0, hi := Zig.Packed.get b 16 }
  mask v := ((Zig.Packed.mask v.lo).setWidth 32 <<< 0) ||| ((BitVec.allOnes 16).setWidth 32 <<< 16)

structure fhToBytesLocals where
  deriving Inhabited

inductive fhToBytesExit where
  | ret (v : Vector (BitVec 8) 4)

def fhToBytes (p0 : FH) : Zig.Result (Vector (BitVec 8) 4) := do
  let e ← ((do
    let i1 ← (((Zig.Packed.toBits? (p0) : Zig.Result (BitVec 32)) >>= fun bits => pure (Zig.BitCast.toLanes (n := 4) (w := 8) (bits))) : Zig.Result (Vector (BitVec 8) 4))
    pure (.ret i1)) : Zig.M fhToBytesLocals fhToBytesExit).run' (default : fhToBytesLocals)
  match e with
  | .ret v => pure v

structure floatsToNestedLocals where
  deriving Inhabited

inductive floatsToNestedExit where
  | ret (v : Vector (Vector (BitVec 8) 2) 2)

def floatsToNested (p0 : Vector (Zig.F16) 2) : Zig.Result (Vector (Vector (BitVec 8) 2) 2) := do
  let e ← ((do
    let i1 ← (((Zig.Packed.toBits? (p0) : Zig.Result (BitVec 32)) >>= fun bits => Zig.Packed.ofBits? (α := Vector (Vector (BitVec 8) 2) 2) (bits)) : Zig.Result (Vector (Vector (BitVec 8) 2) 2))
    pure (.ret i1)) : Zig.M floatsToNestedLocals floatsToNestedExit).run' (default : floatsToNestedLocals)
  match e with
  | .ret v => pure v

structure halvesToVecLocals where
  deriving Inhabited

inductive halvesToVecExit where
  | ret (v : Zig.Vec (BitVec 8) 4)

def halvesToVec (p0 : Vector (Zig.F16) 2) : Zig.Result (Zig.Vec (BitVec 8) 4) := do
  let e ← ((do
    let i1 ← (((Zig.Packed.toBits? (p0) : Zig.Result (BitVec 32)) >>= fun bits => pure ⟨Zig.BitCast.toLanes (n := 4) (w := 8) (bits)⟩) : Zig.Result (Zig.Vec (BitVec 8) 4))
    pure (.ret i1)) : Zig.M halvesToVecLocals halvesToVecExit).run' (default : halvesToVecLocals)
  match e with
  | .ret v => pure v

structure intToModesLocals where
  deriving Inhabited

inductive intToModesExit where
  | ret (v : Vector (Mode) 4)

def intToModes (p0 : BitVec 8) : Zig.Result (Vector (Mode) 4) := do
  let e ← ((do
    let i1 ← (Zig.Packed.ofBits? (α := Vector (Mode) 4) (p0) : Zig.Result (Vector (Mode) 4))
    pure (.ret i1)) : Zig.M intToModesLocals intToModesExit).run' (default : intToModesLocals)
  match e with
  | .ret v => pure v

structure intToNestedLocals where
  deriving Inhabited

inductive intToNestedExit where
  | ret (v : Vector (Vector (BitVec 4) 3) 2)

def intToNested (p0 : BitVec 24) : Zig.Result (Vector (Vector (BitVec 4) 3) 2) := do
  let e ← ((do
    let i1 ← (Zig.Packed.ofBits? (α := Vector (Vector (BitVec 4) 3) 2) (p0) : Zig.Result (Vector (Vector (BitVec 4) 3) 2))
    pure (.ret i1)) : Zig.M intToNestedLocals intToNestedExit).run' (default : intToNestedLocals)
  match e with
  | .ret v => pure v

structure intToNibsLocals where
  deriving Inhabited

inductive intToNibsExit where
  | ret (v : Vector (Nib) 3)

def intToNibs (p0 : BitVec 18) : Zig.Result (Vector (Nib) 3) := do
  let e ← ((do
    let i1 ← (Zig.Packed.ofBits? (α := Vector (Nib) 3) (p0) : Zig.Result (Vector (Nib) 3))
    pure (.ret i1)) : Zig.M intToNibsLocals intToNibsExit).run' (default : intToNibsLocals)
  match e with
  | .ret v => pure v

structure modesToIntLocals where
  deriving Inhabited

inductive modesToIntExit where
  | ret (v : BitVec 8)

def modesToInt (p0 : Vector (Mode) 4) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i1 ← (Zig.Packed.toBits? (p0) : Zig.Result (BitVec 8))
    pure (.ret i1)) : Zig.M modesToIntLocals modesToIntExit).run' (default : modesToIntLocals)
  match e with
  | .ret v => pure v

structure nestedToIntLocals where
  deriving Inhabited

inductive nestedToIntExit where
  | ret (v : BitVec 24)

def nestedToInt (p0 : Vector (Vector (BitVec 4) 3) 2) : Zig.Result (BitVec 24) := do
  let e ← ((do
    let i1 ← (Zig.Packed.toBits? (p0) : Zig.Result (BitVec 24))
    pure (.ret i1)) : Zig.M nestedToIntLocals nestedToIntExit).run' (default : nestedToIntLocals)
  match e with
  | .ret v => pure v

structure nibblesToULocals where
  deriving Inhabited

inductive nibblesToUExit where
  | ret (v : U)

def nibblesToU (p0 : Vector (BitVec 4) 4) : Zig.Result (U) := do
  let e ← ((do
    let i1 ← (((pure (Zig.BitCast.ofLanes (p0)) : Zig.Result (BitVec 16)) >>= fun bits => Zig.Packed.ofBits? (α := U) (bits)) : Zig.Result (U))
    pure (.ret i1)) : Zig.M nibblesToULocals nibblesToUExit).run' (default : nibblesToULocals)
  match e with
  | .ret v => pure v

structure nibsToIntLocals where
  deriving Inhabited

inductive nibsToIntExit where
  | ret (v : BitVec 18)

def nibsToInt (p0 : Vector (Nib) 3) : Zig.Result (BitVec 18) := do
  let e ← ((do
    let i1 ← (Zig.Packed.toBits? (p0) : Zig.Result (BitVec 18))
    pure (.ret i1)) : Zig.M nibsToIntLocals nibsToIntExit).run' (default : nibsToIntLocals)
  match e with
  | .ret v => pure v

structure uToNibblesLocals where
  deriving Inhabited

inductive uToNibblesExit where
  | ret (v : Vector (BitVec 4) 4)

def uToNibbles (p0 : U) : Zig.Result (Vector (BitVec 4) 4) := do
  let e ← ((do
    let i1 ← (((Zig.Packed.toBits? (p0) : Zig.Result (BitVec 16)) >>= fun bits => pure (Zig.BitCast.toLanes (n := 4) (w := 4) (bits))) : Zig.Result (Vector (BitVec 4) 4))
    pure (.ret i1)) : Zig.M uToNibblesLocals uToNibblesExit).run' (default : uToNibblesLocals)
  match e with
  | .ret v => pure v

structure unionsToIntLocals where
  deriving Inhabited

inductive unionsToIntExit where
  | ret (v : BitVec 32)

def unionsToInt (p0 : Vector (U) 2) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← (Zig.Packed.toBits? (p0) : Zig.Result (BitVec 32))
    pure (.ret i1)) : Zig.M unionsToIntLocals unionsToIntExit).run' (default : unionsToIntLocals)
  match e with
  | .ret v => pure v

structure vecToHalvesLocals where
  deriving Inhabited

inductive vecToHalvesExit where
  | ret (v : Vector (Half) 2)

def vecToHalves (p0 : Zig.Vec (Zig.F16) 2) : Zig.Result (Vector (Half) 2) := do
  let e ← ((do
    let i1 ← (((Zig.Packed.toBits? (p0) : Zig.Result (BitVec 32)) >>= fun bits => Zig.Packed.ofBits? (α := Vector (Half) 2) (bits)) : Zig.Result (Vector (Half) 2))
    pure (.ret i1)) : Zig.M vecToHalvesLocals vecToHalvesExit).run' (default : vecToHalvesLocals)
  match e with
  | .ret v => pure v

end Logical017