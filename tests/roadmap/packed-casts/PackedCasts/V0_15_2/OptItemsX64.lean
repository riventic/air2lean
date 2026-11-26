-- air2lean-profile: {"admission":"unqualified-build-mode","correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_x86_64","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.16-musl","zig_version":"0.15.2"}}
import ZigLean


namespace PackedCasts.V0_15_2.OptItemsX64

structure S where
  a : BitVec 16
  b : BitVec 8
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc S where
  size := 4
  align := 2
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.a), (2, Zig.Enc.encode v.b)]
  decode bs := do pure { a := ← Zig.Enc.decodeAt bs 0, b := ← Zig.Enc.decodeAt bs 2 }

structure PS where
  lo : BitVec 4
  hi : BitVec 12
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed PS 16 where
  toBits v := ((Zig.Packed.toBits v.lo).setWidth 16 <<< 0) ||| ((Zig.Packed.toBits v.hi).setWidth 16 <<< 4)
  ofBits b := { lo := Zig.Packed.get b 0, hi := Zig.Packed.get b 4 }

instance : Zig.Enc PS where
  size := 2
  align := 2
  encode v := Zig.Enc.encode (Zig.Packed.toBits v)
  decode bs := do
    let b : BitVec 16 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

structure ES where
  a : BitVec 8
  b : BitVec 8
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc ES where
  size := 2
  align := 1
  encode v := Zig.Enc.fields 2 [(0, Zig.Enc.encode v.a), (1, Zig.Enc.encode v.b)]
  decode bs := do pure { a := ← Zig.Enc.decodeAt bs 0, b := ← Zig.Enc.decodeAt bs 1 }

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

instance : Zig.Enc E where
  size := 1
  align := 1
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 8 ← Zig.Enc.decode bs
    match E.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

structure arraysToIntLocals where
  deriving Inhabited

inductive arraysToIntExit where
  | ret (v : BitVec 64)

def arraysToInt (p0 : Vector (Option (Vector (BitVec 8) 3)) 2) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (Vector (BitVec 8) 3)) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (Vector (BitVec 8) 3)))); Zig.reprCast (BitVec 64) (p0 : Vector (Option (Vector (BitVec 8) 3)) 2))
    pure (.ret i1)) : Zig.M arraysToIntLocals arraysToIntExit).run' (default : arraysToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] arraysToInt

structure boolsToIntLocals where
  deriving Inhabited

inductive boolsToIntExit where
  | ret (v : BitVec 32)

def boolsToInt (p0 : Vector (Option (Bool)) 2) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (Bool)) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (Bool)))); Zig.reprCast (BitVec 32) (p0 : Vector (Option (Bool)) 2))
    pure (.ret i1)) : Zig.M boolsToIntLocals boolsToIntExit).run' (default : boolsToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] boolsToInt

structure enumsToIntLocals where
  deriving Inhabited

inductive enumsToIntExit where
  | ret (v : BitVec 32)

def enumsToInt (p0 : Vector (Option (E)) 2) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (E)) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (E)))); Zig.reprCast (BitVec 32) (p0 : Vector (Option (E)) 2))
    pure (.ret i1)) : Zig.M enumsToIntLocals enumsToIntExit).run' (default : enumsToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] enumsToInt

structure gridToIntLocals where
  deriving Inhabited

inductive gridToIntExit where
  | ret (v : BitVec 64)

def gridToInt (p0 : Vector (Vector (Option (BitVec 8)) 2) 2) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Vector (Option (BitVec 8)) 2) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (BitVec 8))))); Zig.reprCast (BitVec 64) (p0 : Vector (Vector (Option (BitVec 8)) 2) 2))
    pure (.ret i1)) : Zig.M gridToIntLocals gridToIntExit).run' (default : gridToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] gridToInt

structure intToArraysLocals where
  deriving Inhabited

inductive intToArraysExit where
  | ret (v : BitVec 32)
  | br2 (v : BitVec 32)

def intToArrays (p0 : BitVec 64) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (Vector (BitVec 8) 3)) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (Vector (BitVec 8) 3)))); Zig.reprCast (Vector (Option (Vector (BitVec 8) 3)) 2) (p0 : BitVec 64))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (1 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        let i7 ← (letI : Zig.Enc (BitVec 24) := Zig.intEncExt .little false 24; Zig.reprCast (BitVec 24) (i6 : Vector (BitVec 8) 3))
        let i8 ← Zig.intCast false false 32 i7 (safe := false)
        pure (.br2 i8))
      else (do
        pure (.br2 (16777216 : BitVec 32)))) : Zig.M intToArraysLocals intToArraysExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToArraysLocals intToArraysExit).run' (default : intToArraysLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToArrays

structure intToAutoLocals where
  deriving Inhabited

inductive intToAutoExit where
  | ret (v : BitVec 16)
  | br2 (v : BitVec 16)

def intToAuto (p0 : BitVec 96) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (BitVec 96) := Zig.intEncExt .little false 96; (letI : Zig.Enc (Vector (Option (S)) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (S)))); Zig.reprCast (Vector (Option (S)) 2) (p0 : BitVec 96)))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (1 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        let i7 ← pure ((i6).a)
        let i8 ← pure ((i6).b)
        let i9 ← Zig.intCast false false 16 i8 (safe := false)
        let i10 ← pure (Zig.addWrap i7 i9)
        pure (.br2 i10))
      else (do
        pure (.br2 (65535 : BitVec 16)))) : Zig.M intToAutoLocals intToAutoExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToAutoLocals intToAutoExit).run' (default : intToAutoLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToAuto

structure intToBoolsLocals where
  n : BitVec 8
  local4 : BitVec 64
  deriving Inhabited

inductive intToBoolsExit where
  | ret (v : BitVec 8)
  | br20 (v : BitVec 8)
  | br16 (v : BitVec 8)
  | br9
  | br6
  | rep7

def intToBools.again7 : intToBoolsExit → Bool
  | .rep7 => true
  | _ => false

def intToBools.loop7 (i1 : Vector (Option (Bool)) 2) : Zig.M intToBoolsLocals intToBoolsExit := do
  let i8 ← pure ((← get).local4)
  match ← ((do
    let i10 ← pure (i8)
    let i11 ← pure (Zig.lt false i10 (2 : BitVec 64))
    if i11 then (do
      let i13 ← Zig.call (Zig.vindex i1 i8)
      let i14 ← pure ((← get).n)
      let i15 ← Zig.mul false (3 : BitVec 8) i14
      match ← ((do
        let i17 ← pure ((i13).isSome)
        if i17 then (do
          let i19 ← Zig.optPayload i13
          match ← ((do
            if i19 then (do
              pure (.br20 (2 : BitVec 8)))
            else (do
              pure (.br20 (1 : BitVec 8)))) : Zig.M intToBoolsLocals intToBoolsExit) with
          | .br20 v20 => (do
            pure (.br16 v20))
          | e => pure e)
        else (do
          pure (.br16 (0 : BitVec 8)))) : Zig.M intToBoolsLocals intToBoolsExit) with
      | .br16 v16 => (do
        let i26 ← Zig.add false i15 v16
        modify (fun s => { s with n := i26 })
        pure .br9)
      | e => pure e)
    else (do
      pure .br6)) : Zig.M intToBoolsLocals intToBoolsExit) with
  | .br9 => (do
    let i30 ← Zig.add false i8 (1 : BitVec 64) (safe := false)
    modify (fun s => { s with local4 := i30 })
    pure .rep7)
  | e => pure e

def intToBools (p0 : BitVec 32) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (Bool)) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (Bool)))); Zig.reprCast (Vector (Option (Bool)) 2) (p0 : BitVec 32))
    modify (fun s => { s with n := (0 : BitVec 8) })
    modify (fun s => { s with local4 := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (intToBools.loop7 i1) intToBools.again7) : Zig.M intToBoolsLocals intToBoolsExit) with
    | .br6 => (do
      let i33 ← pure ((← get).n)
      pure (.ret i33))
    | e => pure e) : Zig.M intToBoolsLocals intToBoolsExit).run' (default : intToBoolsLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToBools.loop7 intToBools

structure intToEnumsLocals where
  deriving Inhabited

inductive intToEnumsExit where
  | ret (v : BitVec 8)
  | br2 (v : BitVec 8)

def intToEnums (p0 : BitVec 32) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (E)) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (E)))); Zig.reprCast (Vector (Option (E)) 2) (p0 : BitVec 32))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (1 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        let i7 ← pure (E.toBits i6)
        pure (.br2 i7))
      else (do
        pure (.br2 (255 : BitVec 8)))) : Zig.M intToEnumsLocals intToEnumsExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToEnumsLocals intToEnumsExit).run' (default : intToEnumsLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToEnums

structure intToExternLocals where
  deriving Inhabited

inductive intToExternExit where
  | ret (v : BitVec 16)
  | br2 (v : BitVec 16)

def intToExtern (p0 : BitVec 48) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (BitVec 48) := Zig.intEncExt .little false 48; (letI : Zig.Enc (Vector (Option (ES)) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (ES)))); Zig.reprCast (Vector (Option (ES)) 2) (p0 : BitVec 48)))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (1 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        let i7 ← pure ((i6).a)
        let i8 ← Zig.intCast false false 16 i7 (safe := false)
        let i9 ← pure (Zig.shl i8 (8 : BitVec 4))
        let i10 ← pure ((i6).b)
        let i11 ← Zig.intCast false false 16 i10 (safe := false)
        let i12 ← pure (i9 ||| i11)
        pure (.br2 i12))
      else (do
        pure (.br2 (65535 : BitVec 16)))) : Zig.M intToExternLocals intToExternExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToExternLocals intToExternExit).run' (default : intToExternLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToExtern

structure intToF128Locals where
  deriving Inhabited

inductive intToF128Exit where
  | ret (v : BitVec 128)
  | br2 (v : BitVec 128)

def intToF128 (p0 : BitVec 256) : Zig.Result (BitVec 128) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (Zig.F128)) 1) := Zig.Enc.vectorWith 1 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (Zig.F128)))); Zig.reprCast (Vector (Option (Zig.F128)) 1) (p0 : BitVec 256))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (0 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        let i7 ← Zig.Float.toBits? i6
        pure (.br2 i7))
      else (do
        pure (.br2 (0 : BitVec 128)))) : Zig.M intToF128Locals intToF128Exit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToF128Locals intToF128Exit).run' (default : intToF128Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToF128

structure intToF16Locals where
  deriving Inhabited

inductive intToF16Exit where
  | ret (v : BitVec 16)
  | br2 (v : BitVec 16)

def intToF16 (p0 : BitVec 32) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (Zig.F16)) 1) := Zig.Enc.vectorWith 1 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (Zig.F16)))); Zig.reprCast (Vector (Option (Zig.F16)) 1) (p0 : BitVec 32))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (0 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        let i7 ← Zig.Float.toBits? i6
        pure (.br2 i7))
      else (do
        pure (.br2 (0 : BitVec 16)))) : Zig.M intToF16Locals intToF16Exit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToF16Locals intToF16Exit).run' (default : intToF16Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToF16

structure intToF32Locals where
  deriving Inhabited

inductive intToF32Exit where
  | ret (v : BitVec 32)
  | br2 (v : BitVec 32)

def intToF32 (p0 : BitVec 64) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (Zig.F32)) 1) := Zig.Enc.vectorWith 1 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (Zig.F32)))); Zig.reprCast (Vector (Option (Zig.F32)) 1) (p0 : BitVec 64))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (0 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        let i7 ← Zig.Float.toBits? i6
        pure (.br2 i7))
      else (do
        pure (.br2 (0 : BitVec 32)))) : Zig.M intToF32Locals intToF32Exit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToF32Locals intToF32Exit).run' (default : intToF32Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToF32

structure intToF64Locals where
  deriving Inhabited

inductive intToF64Exit where
  | ret (v : BitVec 64)
  | br2 (v : BitVec 64)

def intToF64 (p0 : BitVec 128) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (Zig.F64)) 1) := Zig.Enc.vectorWith 1 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (Zig.F64)))); Zig.reprCast (Vector (Option (Zig.F64)) 1) (p0 : BitVec 128))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (0 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        let i7 ← Zig.Float.toBits? i6
        pure (.br2 i7))
      else (do
        pure (.br2 (0 : BitVec 64)))) : Zig.M intToF64Locals intToF64Exit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToF64Locals intToF64Exit).run' (default : intToF64Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToF64

structure intToF80Locals where
  deriving Inhabited

inductive intToF80Exit where
  | ret (v : BitVec 80)
  | br2 (v : BitVec 80)

def intToF80 (p0 : BitVec 256) : Zig.Result (BitVec 80) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (Zig.F80)) 1) := Zig.Enc.vectorWith 1 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (Zig.F80)))); Zig.reprCast (Vector (Option (Zig.F80)) 1) (p0 : BitVec 256))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (0 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        let i7 ← Zig.Float.toBits? i6
        pure (.br2 i7))
      else (do
        pure (.br2 (0 : BitVec 80)))) : Zig.M intToF80Locals intToF80Exit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToF80Locals intToF80Exit).run' (default : intToF80Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToF80

structure intToGridLocals where
  deriving Inhabited

inductive intToGridExit where
  | ret (v : BitVec 16)
  | br2 (v : BitVec 16)

def intToGrid (p0 : BitVec 64) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Vector (Option (BitVec 8)) 2) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (BitVec 8))))); Zig.reprCast (Vector (Vector (Option (BitVec 8)) 2) 2) (p0 : BitVec 64))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (1 : BitVec 64))
      let i4 ← Zig.call (Zig.vindex i3 (0 : BitVec 64))
      let i5 ← pure ((i4).isSome)
      if i5 then (do
        let i7 ← Zig.optPayload i4
        let i8 ← Zig.intCast false false 16 i7 (safe := false)
        pure (.br2 i8))
      else (do
        pure (.br2 (256 : BitVec 16)))) : Zig.M intToGridLocals intToGridExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToGridLocals intToGridExit).run' (default : intToGridLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToGrid

structure intToI8sLocals where
  deriving Inhabited

inductive intToI8sExit where
  | ret (v : BitVec 16)
  | br2 (v : BitVec 16)

def intToI8s (p0 : BitVec 32) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (BitVec 8)) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (BitVec 8)))); Zig.reprCast (Vector (Option (BitVec 8)) 2) (p0 : BitVec 32))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (1 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        let i7 ← Zig.intCast true true 16 i6 (safe := false)
        pure (.br2 i7))
      else (do
        pure (.br2 (256 : BitVec 16)))) : Zig.M intToI8sLocals intToI8sExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToI8sLocals intToI8sExit).run' (default : intToI8sLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToI8s

structure intToNestedLocals where
  deriving Inhabited

inductive intToNestedExit where
  | ret (v : BitVec 16)
  | br2 (v : Option (BitVec 8))
  | br9 (v : BitVec 16)

def intToNested (p0 : BitVec 48) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (BitVec 48) := Zig.intEncExt .little false 48; (letI : Zig.Enc (Vector (Option (Option (BitVec 8))) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (BitVec 8))))); Zig.reprCast (Vector (Option (Option (BitVec 8))) 2) (p0 : BitVec 48)))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (1 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        pure (.br2 i6))
      else (do
        pure (.ret (512 : BitVec 16)))) : Zig.M intToNestedLocals intToNestedExit) with
    | .br2 v2 => (do
      match ← ((do
        let i10 ← pure ((v2).isSome)
        if i10 then (do
          let i12 ← Zig.optPayload v2
          let i13 ← Zig.intCast false false 16 i12 (safe := false)
          pure (.br9 i13))
        else (do
          pure (.br9 (256 : BitVec 16)))) : Zig.M intToNestedLocals intToNestedExit) with
      | .br9 v9 => (do
        pure (.ret v9))
      | e => pure e)
    | e => pure e) : Zig.M intToNestedLocals intToNestedExit).run' (default : intToNestedLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToNested

structure intToPackedLocals where
  deriving Inhabited

inductive intToPackedExit where
  | ret (v : BitVec 16)
  | br2 (v : BitVec 16)

def intToPacked (p0 : BitVec 64) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (PS)) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (PS)))); Zig.reprCast (Vector (Option (PS)) 2) (p0 : BitVec 64))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (1 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        let i7 ← pure ((i6).hi)
        let i8 ← Zig.intCast false false 16 i7 (safe := false)
        pure (.br2 i8))
      else (do
        pure (.br2 (65535 : BitVec 16)))) : Zig.M intToPackedLocals intToPackedExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToPackedLocals intToPackedExit).run' (default : intToPackedLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToPacked

structure intToU128Locals where
  deriving Inhabited

inductive intToU128Exit where
  | ret (v : BitVec 128)
  | br2 (v : BitVec 128)

def intToU128 (p0 : BitVec 256) : Zig.Result (BitVec 128) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (BitVec 128)) 1) := Zig.Enc.vectorWith 1 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (BitVec 128)))); Zig.reprCast (Vector (Option (BitVec 128)) 1) (p0 : BitVec 256))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (0 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        pure (.br2 i6))
      else (do
        pure (.br2 (0 : BitVec 128)))) : Zig.M intToU128Locals intToU128Exit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToU128Locals intToU128Exit).run' (default : intToU128Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToU128

structure intToU12sLocals where
  deriving Inhabited

inductive intToU12sExit where
  | ret (v : BitVec 16)
  | br2 (v : BitVec 16)

def intToU12s (p0 : BitVec 64) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (BitVec 12)) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr (Zig.intEncExt .little false 12)); Zig.reprCast (Vector (Option (BitVec 12)) 2) (p0 : BitVec 64))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (0 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        let i7 ← Zig.intCast false false 16 i6 (safe := false)
        pure (.br2 i7))
      else (do
        pure (.br2 (4096 : BitVec 16)))) : Zig.M intToU12sLocals intToU12sExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToU12sLocals intToU12sExit).run' (default : intToU12sLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToU12s

structure intToU16sLocals where
  deriving Inhabited

inductive intToU16sExit where
  | ret (v : BitVec 32)
  | br2 (v : BitVec 32)

def intToU16s (p0 : BitVec 64) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (BitVec 16)) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (BitVec 16)))); Zig.reprCast (Vector (Option (BitVec 16)) 2) (p0 : BitVec 64))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (1 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        let i7 ← Zig.intCast false false 32 i6 (safe := false)
        pure (.br2 i7))
      else (do
        pure (.br2 (65536 : BitVec 32)))) : Zig.M intToU16sLocals intToU16sExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToU16sLocals intToU16sExit).run' (default : intToU16sLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToU16s

structure intToU24sLocals where
  deriving Inhabited

inductive intToU24sExit where
  | ret (v : BitVec 32)
  | br2 (v : BitVec 32)

def intToU24s (p0 : BitVec 128) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (BitVec 24)) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr (Zig.intEncExt .little false 24)); Zig.reprCast (Vector (Option (BitVec 24)) 2) (p0 : BitVec 128))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (1 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        let i7 ← Zig.intCast false false 32 i6 (safe := false)
        pure (.br2 i7))
      else (do
        pure (.br2 (16777216 : BitVec 32)))) : Zig.M intToU24sLocals intToU24sExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToU24sLocals intToU24sExit).run' (default : intToU24sLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToU24s

structure intToU64Locals where
  deriving Inhabited

inductive intToU64Exit where
  | ret (v : BitVec 64)
  | br2 (v : BitVec 64)

def intToU64 (p0 : BitVec 128) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (BitVec 64)) 1) := Zig.Enc.vectorWith 1 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (BitVec 64)))); Zig.reprCast (Vector (Option (BitVec 64)) 1) (p0 : BitVec 128))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (0 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        pure (.br2 i6))
      else (do
        pure (.br2 (0 : BitVec 64)))) : Zig.M intToU64Locals intToU64Exit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToU64Locals intToU64Exit).run' (default : intToU64Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToU64

structure intToU8sLocals where
  deriving Inhabited

inductive intToU8sExit where
  | ret (v : BitVec 16)
  | br2 (v : BitVec 16)

def intToU8s (p0 : BitVec 32) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (BitVec 8)) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (BitVec 8)))); Zig.reprCast (Vector (Option (BitVec 8)) 2) (p0 : BitVec 32))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (1 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        let i7 ← Zig.intCast false false 16 i6 (safe := false)
        pure (.br2 i7))
      else (do
        pure (.br2 (256 : BitVec 16)))) : Zig.M intToU8sLocals intToU8sExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToU8sLocals intToU8sExit).run' (default : intToU8sLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToU8s

structure intToVectorLocals where
  deriving Inhabited

inductive intToVectorExit where
  | ret (v : BitVec 32)
  | br2 (v : BitVec 32)

def intToVector (p0 : BitVec 256) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (Zig.Vec (BitVec 32) 4)) 1) := Zig.Enc.vectorWith 1 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (Zig.Vec (BitVec 32) 4)))); Zig.reprCast (Vector (Option (Zig.Vec (BitVec 32) 4)) 1) (p0 : BitVec 256))
    match ← ((do
      let i3 ← Zig.call (Zig.vindex i1 (0 : BitVec 64))
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        let i7 ← Zig.call (Zig.vindex i6.lanes (1 : BitVec 64))
        pure (.br2 i7))
      else (do
        pure (.br2 (0 : BitVec 32)))) : Zig.M intToVectorLocals intToVectorExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M intToVectorLocals intToVectorExit).run' (default : intToVectorLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToVector

structure intToZerosLocals where
  n : BitVec 8
  local4 : BitVec 64
  deriving Inhabited

inductive intToZerosExit where
  | ret (v : BitVec 8)
  | br14
  | br9
  | br6
  | rep7

def intToZeros.again7 : intToZerosExit → Bool
  | .rep7 => true
  | _ => false

def intToZeros.loop7 (i1 : Vector (Option (BitVec 0)) 4) : Zig.M intToZerosLocals intToZerosExit := do
  let i8 ← pure ((← get).local4)
  match ← ((do
    let i10 ← pure (i8)
    let i11 ← pure (Zig.lt false i10 (4 : BitVec 64))
    if i11 then (do
      let i13 ← Zig.call (Zig.vindex i1 i8)
      match ← ((do
        let i15 ← pure ((i13).isSome)
        if i15 then (do
          let i17 ← pure ((← get).n)
          let i18 ← Zig.add false i17 (1 : BitVec 8)
          modify (fun s => { s with n := i18 })
          pure .br14)
        else (do
          pure .br14)) : Zig.M intToZerosLocals intToZerosExit) with
      | .br14 => (do
        pure .br9)
      | e => pure e)
    else (do
      pure .br6)) : Zig.M intToZerosLocals intToZerosExit) with
  | .br9 => (do
    let i24 ← Zig.add false i8 (1 : BitVec 64) (safe := false)
    modify (fun s => { s with local4 := i24 })
    pure .rep7)
  | e => pure e

def intToZeros (p0 : BitVec 32) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (BitVec 0)) 4) := Zig.Enc.vectorWith 4 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (BitVec 0)))); Zig.reprCast (Vector (Option (BitVec 0)) 4) (p0 : BitVec 32))
    modify (fun s => { s with n := (0 : BitVec 8) })
    modify (fun s => { s with local4 := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (intToZeros.loop7 i1) intToZeros.again7) : Zig.M intToZerosLocals intToZerosExit) with
    | .br6 => (do
      let i27 ← pure ((← get).n)
      pure (.ret i27))
    | e => pure e) : Zig.M intToZerosLocals intToZerosExit).run' (default : intToZerosLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToZeros.loop7 intToZeros

structure nestedToIntLocals where
  deriving Inhabited

inductive nestedToIntExit where
  | ret (v : BitVec 48)

def nestedToInt (p0 : Vector (Option (Option (BitVec 8))) 2) : Zig.Result (BitVec 48) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (Option (BitVec 8))) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (BitVec 8))))); (letI : Zig.Enc (BitVec 48) := Zig.intEncExt .little false 48; Zig.reprCast (BitVec 48) (p0 : Vector (Option (Option (BitVec 8))) 2)))
    pure (.ret i1)) : Zig.M nestedToIntLocals nestedToIntExit).run' (default : nestedToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] nestedToInt

structure u16sToIntLocals where
  deriving Inhabited

inductive u16sToIntExit where
  | ret (v : BitVec 64)

def u16sToInt (p0 : Vector (Option (BitVec 16)) 2) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (BitVec 16)) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (BitVec 16)))); Zig.reprCast (BitVec 64) (p0 : Vector (Option (BitVec 16)) 2))
    pure (.ret i1)) : Zig.M u16sToIntLocals u16sToIntExit).run' (default : u16sToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] u16sToInt

structure u8sToIntLocals where
  deriving Inhabited

inductive u8sToIntExit where
  | ret (v : BitVec 32)

def u8sToInt (p0 : Vector (Option (BitVec 8)) 2) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (BitVec 8)) 2) := Zig.Enc.vectorWith 2 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (BitVec 8)))); Zig.reprCast (BitVec 32) (p0 : Vector (Option (BitVec 8)) 2))
    pure (.ret i1)) : Zig.M u8sToIntLocals u8sToIntExit).run' (default : u8sToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] u8sToInt

structure zerosToIntLocals where
  deriving Inhabited

inductive zerosToIntExit where
  | ret (v : BitVec 32)

def zerosToInt (p0 : Vector (Option (BitVec 0)) 4) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← (letI : Zig.Enc (Vector (Option (BitVec 0)) 4) := Zig.Enc.vectorWith 4 (Zig.Enc.optionRepr ((inferInstance : Zig.Enc (BitVec 0)))); Zig.reprCast (BitVec 32) (p0 : Vector (Option (BitVec 0)) 4))
    pure (.ret i1)) : Zig.M zerosToIntLocals zerosToIntExit).run' (default : zerosToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] zerosToInt

end PackedCasts.V0_15_2.OptItemsX64