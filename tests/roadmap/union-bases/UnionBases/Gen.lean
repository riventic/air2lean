-- air2lean-profile: {"admission":"unqualified-build-mode","correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_x86_64","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace UnionBases

inductive WideTag where
  | none
  | half
  | cells
  deriving Repr, Inhabited, DecidableEq

def WideTag.toBits : WideTag → BitVec 32
  | .none => (0 : BitVec 32)
  | .half => (1 : BitVec 32)
  | .cells => (2 : BitVec 32)

def WideTag.ofInt? (v : Int) : Option WideTag :=
  if v = 0 then Option.some .none else if v = 1 then Option.some .half else if v = 2 then Option.some .cells else Option.none

def WideTag.isNamed (_ : WideTag) : Bool := true

instance : Zig.Packed WideTag 32 where
  toBits := WideTag.toBits
  ofBits b := (WideTag.ofInt? (Zig.val false b)).getD default
  valid b := (WideTag.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc WideTag where
  size := 4
  align := 4
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 32 ← Zig.Enc.decode bs
    match WideTag.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

inductive Wide where
  | none
  | half (v : BitVec 16)
  | cells (v : Vector (BitVec 16) 3)
  | undef_half (v : BitVec 16) (written : List String)
  | undef_cells (v : Vector (BitVec 16) 3) (written : List String)
  deriving Repr, Inhabited, DecidableEq

def Wide.tag : Wide → WideTag
  | .none => .none
  | .half _ => .half
  | .undef_half _ _ => .half
  | .cells _ => .cells
  | .undef_cells _ _ => .cells

def Wide.get_none : Wide → Zig.Result (Unit)
  | .none => pure ()
  | _ => throw .panic

def Wide.modify_none (_g : Unit → Unit) : Wide → Wide
  | .none => .none
  | _ => .none

def Wide.setTag_none : Wide → Wide
  | .none => .none
  | _ => .none

def Wide.get_half : Wide → Zig.Result (BitVec 16)
  | .half v => pure v
  | .undef_half _ _ => throw .unspecified
  | _ => throw .panic

def Wide.modify_half (g : BitVec 16 → BitVec 16) : Wide → Wide
  | .half v => .half (g v)
  | .undef_half v w => .undef_half (g v) w
  | _ => .undef_half (g default) []

def Wide.setTag_half : Wide → Wide
  | .half v => .half v
  | .undef_half v w => .undef_half v w
  | _ => .undef_half default []

def Wide.set_half (v : BitVec 16) (_ : Wide) : Wide := .half v

def Wide.get_cells : Wide → Zig.Result (Vector (BitVec 16) 3)
  | .cells v => pure v
  | .undef_cells _ _ => throw .unspecified
  | _ => throw .panic

def Wide.modify_cells (g : Vector (BitVec 16) 3 → Vector (BitVec 16) 3) : Wide → Wide
  | .cells v => .cells (g v)
  | .undef_cells v w => .undef_cells (g v) w
  | _ => .undef_cells (g default) []

def Wide.setTag_cells : Wide → Wide
  | .cells v => .cells v
  | .undef_cells v w => .undef_cells v w
  | _ => .undef_cells default []

def Wide.set_cells (v : Vector (BitVec 16) 3) (_ : Wide) : Wide := .cells v

instance : Zig.Enc Wide where
  size := 12
  align := 4
  encode v := match v with
    | .none => Zig.Enc.fields 12 [(0, Zig.Enc.encode v.tag)]
    | .half x => Zig.Enc.fields 12 [(0, Zig.Enc.encode v.tag), (4, Zig.Enc.encode x)]
    | .cells x => Zig.Enc.fields 12 [(0, Zig.Enc.encode v.tag), (4, Zig.Enc.encode x)]
    | .undef_half _ _ => Zig.Enc.fields 12 [(0, Zig.Enc.encode v.tag)]
    | .undef_cells _ _ => Zig.Enc.fields 12 [(0, Zig.Enc.encode v.tag)]
  decode bs := do
    let t : WideTag ← Zig.Enc.decodeAt bs 0
    match t with
    | .none => pure .none
    | .half => pure (.half (← Zig.Enc.decodeAt bs 4))
    | .cells => pure (.cells (← Zig.Enc.decodeAt bs 4))

structure Pair where
  lo : BitVec 16
  hi : BitVec 16
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Pair where
  size := 4
  align := 2
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.lo), (2, Zig.Enc.encode v.hi)]
  decode bs := do pure { lo := ← Zig.Enc.decodeAt bs 0, hi := ← Zig.Enc.decodeAt bs 2 }

inductive OuterTag where
  | inner
  | none
  deriving Repr, Inhabited, DecidableEq

def OuterTag.toBits : OuterTag → BitVec 64
  | .inner => (0 : BitVec 64)
  | .none => (1 : BitVec 64)

def OuterTag.ofInt? (v : Int) : Option OuterTag :=
  if v = 0 then Option.some .inner else if v = 1 then Option.some .none else Option.none

def OuterTag.isNamed (_ : OuterTag) : Bool := true

instance : Zig.Packed OuterTag 64 where
  toBits := OuterTag.toBits
  ofBits b := (OuterTag.ofInt? (Zig.val false b)).getD default
  valid b := (OuterTag.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc OuterTag where
  size := 8
  align := 8
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 64 ← Zig.Enc.decode bs
    match OuterTag.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

inductive BareTag where
  | byte
  | pair
  deriving Repr, Inhabited, DecidableEq

def BareTag.toBits : BareTag → BitVec 1
  | .byte => (0 : BitVec 1)
  | .pair => (1 : BitVec 1)

def BareTag.ofInt? (v : Int) : Option BareTag :=
  if v = 0 then Option.some .byte else if v = 1 then Option.some .pair else Option.none

def BareTag.isNamed (_ : BareTag) : Bool := true

instance : Zig.Packed BareTag 1 where
  toBits := BareTag.toBits
  ofBits b := (BareTag.ofInt? (Zig.val false b)).getD default
  valid b := (BareTag.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc BareTag where
  size := 1
  align := 1
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 1 ← Zig.Enc.decode bs
    match BareTag.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

inductive Bare where
  | byte (v : BitVec 8)
  | pair (v : Vector (BitVec 8) 2)
  | undef_byte (v : BitVec 8) (written : List String)
  | undef_pair (v : Vector (BitVec 8) 2) (written : List String)
  deriving Repr, Inhabited, DecidableEq

def Bare.tag : Bare → BareTag
  | .byte _ => .byte
  | .undef_byte _ _ => .byte
  | .pair _ => .pair
  | .undef_pair _ _ => .pair

def Bare.get_byte : Bare → Zig.Result (BitVec 8)
  | .byte v => pure v
  | .undef_byte _ _ => throw .unspecified
  | _ => throw .panic

def Bare.modify_byte (g : BitVec 8 → BitVec 8) : Bare → Bare
  | .byte v => .byte (g v)
  | .undef_byte v w => .undef_byte (g v) w
  | _ => .undef_byte (g default) []

def Bare.setTag_byte : Bare → Bare
  | .byte v => .byte v
  | .undef_byte v w => .undef_byte v w
  | _ => .undef_byte default []

def Bare.set_byte (v : BitVec 8) (_ : Bare) : Bare := .byte v

def Bare.get_pair : Bare → Zig.Result (Vector (BitVec 8) 2)
  | .pair v => pure v
  | .undef_pair _ _ => throw .unspecified
  | _ => throw .panic

def Bare.modify_pair (g : Vector (BitVec 8) 2 → Vector (BitVec 8) 2) : Bare → Bare
  | .pair v => .pair (g v)
  | .undef_pair v w => .undef_pair (g v) w
  | _ => .undef_pair (g default) []

def Bare.setTag_pair : Bare → Bare
  | .pair v => .pair v
  | .undef_pair v w => .undef_pair v w
  | _ => .undef_pair default []

def Bare.set_pair (v : Vector (BitVec 8) 2) (_ : Bare) : Bare := .pair v

instance : Zig.Enc Bare where
  size := 3
  align := 1
  encode v := match v with
    | .byte x => Zig.Enc.fields 3 [(0, Zig.Enc.encode v.tag), (1, Zig.Enc.encode x)]
    | .pair x => Zig.Enc.fields 3 [(0, Zig.Enc.encode v.tag), (1, Zig.Enc.encode x)]
    | .undef_byte _ _ => Zig.Enc.fields 3 [(0, Zig.Enc.encode v.tag)]
    | .undef_pair _ _ => Zig.Enc.fields 3 [(0, Zig.Enc.encode v.tag)]
  decode bs := do
    let t : BareTag ← Zig.Enc.decodeAt bs 0
    match t with
    | .byte => pure (.byte (← Zig.Enc.decodeAt bs 1))
    | .pair => pure (.pair (← Zig.Enc.decodeAt bs 1))

structure Inner where
  a : BitVec 8
  bare : Bare
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Inner where
  size := 4
  align := 1
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.a), (1, Zig.Enc.encode v.bare)]
  decode bs := do pure { a := ← Zig.Enc.decodeAt bs 0, bare := ← Zig.Enc.decodeAt bs 1 }

inductive Outer where
  | inner (v : Inner)
  | none
  | undef_inner (v : Inner) (written : List String)
  deriving Repr, Inhabited, DecidableEq

def Outer.tag : Outer → OuterTag
  | .inner _ => .inner
  | .undef_inner _ _ => .inner
  | .none => .none

def Outer.get_inner : Outer → Zig.Result (Inner)
  | .inner v => pure v
  | .undef_inner _ _ => throw .unspecified
  | _ => throw .panic

def Outer.modify_inner (g : Inner → Inner) : Outer → Outer
  | .inner v => .inner (g v)
  | .undef_inner v w => .undef_inner (g v) w
  | _ => .undef_inner (g default) []

def Outer.setTag_inner : Outer → Outer
  | .inner v => .inner v
  | .undef_inner v w => .undef_inner v w
  | _ => .undef_inner default []

def Outer.set_inner (v : Inner) (_ : Outer) : Outer := .inner v

def Outer.setField_inner (k : String) (g : Inner → Inner) : Outer → Outer
  | .inner v => .inner (g v)
  | .undef_inner v w => if ["a", "bare"].all (k :: w).contains then .inner (g v) else .undef_inner (g v) (k :: w)
  | _ => if ["a", "bare"].all ([k]).contains then .inner (g default) else .undef_inner (g default) ([k])

def Outer.get_none : Outer → Zig.Result (Unit)
  | .none => pure ()
  | _ => throw .panic

def Outer.modify_none (_g : Unit → Unit) : Outer → Outer
  | .none => .none
  | _ => .none

def Outer.setTag_none : Outer → Outer
  | .none => .none
  | _ => .none

instance : Zig.Enc Outer where
  size := 16
  align := 8
  encode v := match v with
    | .inner x => Zig.Enc.fields 16 [(0, Zig.Enc.encode v.tag), (8, Zig.Enc.encode x)]
    | .none => Zig.Enc.fields 16 [(0, Zig.Enc.encode v.tag)]
    | .undef_inner _ _ => Zig.Enc.fields 16 [(0, Zig.Enc.encode v.tag)]
  decode bs := do
    let t : OuterTag ← Zig.Enc.decodeAt bs 0
    match t with
    | .inner => pure (.inner (← Zig.Enc.decodeAt bs 8))
    | .none => pure .none

inductive MixedTag where
  | res
  | raw
  deriving Repr, Inhabited, DecidableEq

def MixedTag.toBits : MixedTag → BitVec 32
  | .res => (0 : BitVec 32)
  | .raw => (1 : BitVec 32)

def MixedTag.ofInt? (v : Int) : Option MixedTag :=
  if v = 0 then Option.some .res else if v = 1 then Option.some .raw else Option.none

def MixedTag.isNamed (_ : MixedTag) : Bool := true

instance : Zig.Packed MixedTag 32 where
  toBits := MixedTag.toBits
  ofBits b := (MixedTag.ofInt? (Zig.val false b)).getD default
  valid b := (MixedTag.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc MixedTag where
  size := 4
  align := 4
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 32 ← Zig.Enc.decode bs
    match MixedTag.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

inductive Mixed where
  | res (v : Except Zig.ErrName (Vector (BitVec 8) 2))
  | raw (v : Vector (BitVec 8) 4)
  | undef_res (v : Except Zig.ErrName (Vector (BitVec 8) 2)) (written : List String)
  | undef_raw (v : Vector (BitVec 8) 4) (written : List String)
  deriving Repr, Inhabited, DecidableEq

def Mixed.tag : Mixed → MixedTag
  | .res _ => .res
  | .undef_res _ _ => .res
  | .raw _ => .raw
  | .undef_raw _ _ => .raw

def Mixed.get_res : Mixed → Zig.Result (Except Zig.ErrName (Vector (BitVec 8) 2))
  | .res v => pure v
  | .undef_res _ _ => throw .unspecified
  | _ => throw .panic

def Mixed.modify_res (g : Except Zig.ErrName (Vector (BitVec 8) 2) → Except Zig.ErrName (Vector (BitVec 8) 2)) : Mixed → Mixed
  | .res v => .res (g v)
  | .undef_res v w => .undef_res (g v) w
  | _ => .undef_res (g default) []

def Mixed.setTag_res : Mixed → Mixed
  | .res v => .res v
  | .undef_res v w => .undef_res v w
  | _ => .undef_res default []

def Mixed.set_res (v : Except Zig.ErrName (Vector (BitVec 8) 2)) (_ : Mixed) : Mixed := .res v

def Mixed.get_raw : Mixed → Zig.Result (Vector (BitVec 8) 4)
  | .raw v => pure v
  | .undef_raw _ _ => throw .unspecified
  | _ => throw .panic

def Mixed.modify_raw (g : Vector (BitVec 8) 4 → Vector (BitVec 8) 4) : Mixed → Mixed
  | .raw v => .raw (g v)
  | .undef_raw v w => .undef_raw (g v) w
  | _ => .undef_raw (g default) []

def Mixed.setTag_raw : Mixed → Mixed
  | .raw v => .raw v
  | .undef_raw v w => .undef_raw v w
  | _ => .undef_raw default []

def Mixed.set_raw (v : Vector (BitVec 8) 4) (_ : Mixed) : Mixed := .raw v

instance : Zig.Enc Mixed where
  size := 8
  align := 4
  encode v := match v with
    | .res x => Zig.Enc.fields 8 [(0, Zig.Enc.encode v.tag), (4, (letI : Zig.Enc (Except Zig.ErrName (Vector (BitVec 8) 2)) := Zig.errorUnionEnc (⟨#["Bad"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Vector (BitVec 8) 2))); Zig.Enc.encode x))]
    | .raw x => Zig.Enc.fields 8 [(0, Zig.Enc.encode v.tag), (4, Zig.Enc.encode x)]
    | .undef_res _ _ => Zig.Enc.fields 8 [(0, Zig.Enc.encode v.tag)]
    | .undef_raw _ _ => Zig.Enc.fields 8 [(0, Zig.Enc.encode v.tag)]
  decode bs := do
    let t : MixedTag ← Zig.Enc.decodeAt bs 0
    match t with
    | .res => pure (.res (← (letI : Zig.Enc (Except Zig.ErrName (Vector (BitVec 8) 2)) := Zig.errorUnionEnc (⟨#["Bad"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Vector (BitVec 8) 2))); Zig.Enc.decodeAt bs 4)))
    | .raw => pure (.raw (← Zig.Enc.decodeAt bs 4))

inductive LowTag where
  | wide
  | pair
  deriving Repr, Inhabited, DecidableEq

def LowTag.toBits : LowTag → BitVec 1
  | .wide => (0 : BitVec 1)
  | .pair => (1 : BitVec 1)

def LowTag.ofInt? (v : Int) : Option LowTag :=
  if v = 0 then Option.some .wide else if v = 1 then Option.some .pair else Option.none

def LowTag.isNamed (_ : LowTag) : Bool := true

instance : Zig.Packed LowTag 1 where
  toBits := LowTag.toBits
  ofBits b := (LowTag.ofInt? (Zig.val false b)).getD default
  valid b := (LowTag.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc LowTag where
  size := 1
  align := 1
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 1 ← Zig.Enc.decode bs
    match LowTag.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

inductive Low where
  | wide (v : BitVec 64)
  | pair (v : Vector (BitVec 8) 2)
  | undef_wide (v : BitVec 64) (written : List String)
  | undef_pair (v : Vector (BitVec 8) 2) (written : List String)
  deriving Repr, Inhabited, DecidableEq

def Low.tag : Low → LowTag
  | .wide _ => .wide
  | .undef_wide _ _ => .wide
  | .pair _ => .pair
  | .undef_pair _ _ => .pair

def Low.get_wide : Low → Zig.Result (BitVec 64)
  | .wide v => pure v
  | .undef_wide _ _ => throw .unspecified
  | _ => throw .panic

def Low.modify_wide (g : BitVec 64 → BitVec 64) : Low → Low
  | .wide v => .wide (g v)
  | .undef_wide v w => .undef_wide (g v) w
  | _ => .undef_wide (g default) []

def Low.setTag_wide : Low → Low
  | .wide v => .wide v
  | .undef_wide v w => .undef_wide v w
  | _ => .undef_wide default []

def Low.set_wide (v : BitVec 64) (_ : Low) : Low := .wide v

def Low.get_pair : Low → Zig.Result (Vector (BitVec 8) 2)
  | .pair v => pure v
  | .undef_pair _ _ => throw .unspecified
  | _ => throw .panic

def Low.modify_pair (g : Vector (BitVec 8) 2 → Vector (BitVec 8) 2) : Low → Low
  | .pair v => .pair (g v)
  | .undef_pair v w => .undef_pair (g v) w
  | _ => .undef_pair (g default) []

def Low.setTag_pair : Low → Low
  | .pair v => .pair v
  | .undef_pair v w => .undef_pair v w
  | _ => .undef_pair default []

def Low.set_pair (v : Vector (BitVec 8) 2) (_ : Low) : Low := .pair v

instance : Zig.Enc Low where
  size := 16
  align := 8
  encode v := match v with
    | .wide x => Zig.Enc.fields 16 [(8, Zig.Enc.encode v.tag), (0, Zig.Enc.encode x)]
    | .pair x => Zig.Enc.fields 16 [(8, Zig.Enc.encode v.tag), (0, Zig.Enc.encode x)]
    | .undef_wide _ _ => Zig.Enc.fields 16 [(8, Zig.Enc.encode v.tag)]
    | .undef_pair _ _ => Zig.Enc.fields 16 [(8, Zig.Enc.encode v.tag)]
  decode bs := do
    let t : LowTag ← Zig.Enc.decodeAt bs 8
    match t with
    | .wide => pure (.wide (← Zig.Enc.decodeAt bs 0))
    | .pair => pure (.pair (← Zig.Enc.decodeAt bs 0))

structure Ext where
  bytes : Vector Zig.Byte 4
  deriving Repr, Inhabited, DecidableEq

def Ext.get_word (u : Ext) : Zig.Result (BitVec 32) := Zig.Raw.get (BitVec 32) u.bytes

def Ext.modify_word (g : BitVec 32 → BitVec 32) (u : Ext) : Ext :=
  ⟨Zig.Raw.set u.bytes (g (Zig.Raw.getD (Zig.Raw.get (BitVec 32) u.bytes)))⟩

def Ext.get_pair (u : Ext) : Zig.Result (Pair) := Zig.Raw.get (Pair) u.bytes

def Ext.modify_pair (g : Pair → Pair) (u : Ext) : Ext :=
  ⟨Zig.Raw.set u.bytes (g (Zig.Raw.getD (Zig.Raw.get (Pair) u.bytes)))⟩

def Ext.get_bytes (u : Ext) : Zig.Result (Vector (BitVec 8) 4) := Zig.Raw.get (Vector (BitVec 8) 4) u.bytes

def Ext.modify_bytes (g : Vector (BitVec 8) 4 → Vector (BitVec 8) 4) (u : Ext) : Ext :=
  ⟨Zig.Raw.set u.bytes (g (Zig.Raw.getD (Zig.Raw.get (Vector (BitVec 8) 4) u.bytes)))⟩

instance : Zig.Enc Ext where
  size := 4
  align := 4
  encode v := v.bytes.toArray
  decode bs := pure ⟨Zig.Raw.ofArray 4 bs⟩

structure Holder where
  head : BitVec 32
  ext : Ext
  wide : Wide
  low : Low
  bare : Bare
  outer : Outer
  maybe : Option (Wide)
  res : Except Zig.ErrName (Ext)
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Holder where
  size := 80
  align := 8
  encode v := Zig.Enc.fields 80 [(32, Zig.Enc.encode v.head), (36, Zig.Enc.encode v.ext), (40, Zig.Enc.encode v.wide), (0, Zig.Enc.encode v.low), (76, Zig.Enc.encode v.bare), (16, Zig.Enc.encode v.outer), (52, Zig.Enc.encode v.maybe), (68, (letI : Zig.Enc (Except Zig.ErrName (Ext)) := Zig.errorUnionEnc (⟨#["Bad"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Ext))); Zig.Enc.encode v.res))]
  decode bs := do pure { head := ← Zig.Enc.decodeAt bs 32, ext := ← Zig.Enc.decodeAt bs 36, wide := ← Zig.Enc.decodeAt bs 40, low := ← Zig.Enc.decodeAt bs 0, bare := ← Zig.Enc.decodeAt bs 76, outer := ← Zig.Enc.decodeAt bs 16, maybe := ← Zig.Enc.decodeAt bs 52, res := ← (letI : Zig.Enc (Except Zig.ErrName (Ext)) := Zig.errorUnionEnc (⟨#["Bad"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Ext))); Zig.Enc.decodeAt bs 68) }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: union_bases.table
  (Zig.Enc.encode (({ head := (1 : BitVec 32), ext := (⟨Zig.Raw.init 4 ((#v[(17 : BitVec 8), (34 : BitVec 8), (51 : BitVec 8), (68 : BitVec 8)] : Vector (BitVec 8) 4) : Vector (BitVec 8) 4)⟩ : Ext), wide := (Wide.cells (#v[(100 : BitVec 16), (101 : BitVec 16), (102 : BitVec 16)] : Vector (BitVec 16) 3)), low := (Low.pair (#v[(30 : BitVec 8), (31 : BitVec 8)] : Vector (BitVec 8) 2)), bare := (Bare.pair (#v[(40 : BitVec 8), (41 : BitVec 8)] : Vector (BitVec 8) 2)), outer := (Outer.inner ({ a := (50 : BitVec 8), bare := (Bare.pair (#v[(51 : BitVec 8), (52 : BitVec 8)] : Vector (BitVec 8) 2)) } : Inner)), maybe := (some (Wide.cells (#v[(200 : BitVec 16), (201 : BitVec 16), (202 : BitVec 16)] : Vector (BitVec 16) 3))), res := (.ok (⟨Zig.Raw.init 4 ((16909060 : BitVec 32) : BitVec 32)⟩ : Ext) : Except Zig.ErrName (Ext)) } : Holder) : Holder), 4, .constGlobal),
  -- 1: union_bases.mixed
  (Zig.Enc.encode ((Mixed.raw (#v[(60 : BitVec 8), (61 : BitVec 8), (62 : BitVec 8), (63 : BitVec 8)] : Vector (BitVec 8) 4)) : Mixed), 1, .constGlobal)]

structure barePairPtrLocals where
  deriving Inhabited

inductive barePairPtrExit where
  | ret (v : Zig.Ptr)

def barePairPtr  : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    pure (.ret (⟨some 0, 78⟩ : Zig.Ptr))) : Zig.MM barePairPtrLocals barePairPtrExit).run' (default : barePairPtrLocals)
  match e with
  | .ret v => pure v

structure extBytePtrLocals where
  deriving Inhabited

inductive extBytePtrExit where
  | ret (v : Zig.Ptr)

def extBytePtr  : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    pure (.ret (⟨some 0, 38⟩ : Zig.Ptr))) : Zig.MM extBytePtrLocals extBytePtrExit).run' (default : extBytePtrLocals)
  match e with
  | .ret v => pure v

structure extHiPtrLocals where
  deriving Inhabited

inductive extHiPtrExit where
  | ret (v : Zig.Ptr)

def extHiPtr  : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    pure (.ret (⟨some 0, 38⟩ : Zig.Ptr))) : Zig.MM extHiPtrLocals extHiPtrExit).run' (default : extHiPtrLocals)
  match e with
  | .ret v => pure v

structure extWordPtrLocals where
  deriving Inhabited

inductive extWordPtrExit where
  | ret (v : Zig.Ptr)

def extWordPtr  : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    pure (.ret (⟨some 0, 36⟩ : Zig.Ptr))) : Zig.MM extWordPtrLocals extWordPtrExit).run' (default : extWordPtrLocals)
  match e with
  | .ret v => pure v

structure lowPairPtrLocals where
  deriving Inhabited

inductive lowPairPtrExit where
  | ret (v : Zig.Ptr)

def lowPairPtr  : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    pure (.ret (⟨some 0, 1⟩ : Zig.Ptr))) : Zig.MM lowPairPtrLocals lowPairPtrExit).run' (default : lowPairPtrLocals)
  match e with
  | .ret v => pure v

structure maybeCellPtrLocals where
  deriving Inhabited

inductive maybeCellPtrExit where
  | ret (v : Zig.Ptr)

def maybeCellPtr  : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    pure (.ret (⟨some 0, 58⟩ : Zig.Ptr))) : Zig.MM maybeCellPtrLocals maybeCellPtrExit).run' (default : maybeCellPtrLocals)
  match e with
  | .ret v => pure v

structure mixedHighPtrLocals where
  deriving Inhabited

inductive mixedHighPtrExit where
  | ret (v : Zig.Ptr)

def mixedHighPtr  : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    pure (.ret (⟨some 1, 7⟩ : Zig.Ptr))) : Zig.MM mixedHighPtrLocals mixedHighPtrExit).run' (default : mixedHighPtrLocals)
  match e with
  | .ret v => pure v

structure mixedLowPtrLocals where
  deriving Inhabited

inductive mixedLowPtrExit where
  | ret (v : Zig.Ptr)

def mixedLowPtr  : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    pure (.ret (⟨some 1, 5⟩ : Zig.Ptr))) : Zig.MM mixedLowPtrLocals mixedLowPtrExit).run' (default : mixedLowPtrLocals)
  match e with
  | .ret v => pure v

structure outerPairPtrLocals where
  deriving Inhabited

inductive outerPairPtrExit where
  | ret (v : Zig.Ptr)

def outerPairPtr  : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    pure (.ret (⟨some 0, 27⟩ : Zig.Ptr))) : Zig.MM outerPairPtrLocals outerPairPtrExit).run' (default : outerPairPtrLocals)
  match e with
  | .ret v => pure v

structure projectBareLocals where
  deriving Inhabited

inductive projectBareExit where
  | ret (v : Zig.Ptr)
  | br5

def projectBare (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.add 76))
    let i2 ← Zig.load (Bare) 1 i1
    let i3 ← pure (Bare.tag i2)
    let i4 ← pure (i3 == BareTag.pair)
    match ← ((do
      if i4 then (do
        pure .br5)
      else (do
        throw .panic)) : Zig.MM projectBareLocals projectBareExit) with
    | .br5 => (do
      let i10 ← Zig.callM (Zig.ptrProject i1 (·.add 1))
      let i11 ← Zig.callM (Zig.ptrProject i10 (·.elem 1 (1 : BitVec 64)))
      pure (.ret i11))
    | e => pure e) : Zig.MM projectBareLocals projectBareExit).run' (default : projectBareLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure projectWideLocals where
  deriving Inhabited

inductive projectWideExit where
  | ret (v : Zig.Ptr)
  | br5

def projectWide (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.add 40))
    let i2 ← Zig.load (Wide) 4 i1
    let i3 ← pure (Wide.tag i2)
    let i4 ← pure (i3 == WideTag.cells)
    match ← ((do
      if i4 then (do
        pure .br5)
      else (do
        throw .panic)) : Zig.MM projectWideLocals projectWideExit) with
    | .br5 => (do
      let i10 ← Zig.callM (Zig.ptrProject i1 (·.add 4))
      let i11 ← Zig.callM (Zig.ptrProject i10 (·.elem 2 (2 : BitVec 64)))
      pure (.ret i11))
    | e => pure e) : Zig.MM projectWideLocals projectWideExit).run' (default : projectWideLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure readExtByteLocals where
  deriving Inhabited

inductive readExtByteExit where
  | ret (v : BitVec 8)
  | br2

def readExtByte (p0 : BitVec 64) : Zig.MemM (BitVec 8) := do
  let e ← ((do
    let i1 ← pure (Zig.lt false p0 (4 : BitVec 64))
    match ← ((do
      if i1 then (do
        pure .br2)
      else (do
        throw .outOfBounds)) : Zig.MM readExtByteLocals readExtByteExit) with
    | .br2 => (do
      let i7 ← Zig.callM (Zig.load (BitVec 8) 1 ((⟨some 0, 36⟩ : Zig.Ptr).elem 1 p0))
      pure (.ret i7))
    | e => pure e) : Zig.MM readExtByteLocals readExtByteExit).run' (default : readExtByteLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure readWideCellLocals where
  deriving Inhabited

inductive readWideCellExit where
  | ret (v : BitVec 16)
  | br2

def readWideCell (p0 : BitVec 64) : Zig.MemM (BitVec 16) := do
  let e ← ((do
    let i1 ← pure (Zig.lt false p0 (3 : BitVec 64))
    match ← ((do
      if i1 then (do
        pure .br2)
      else (do
        throw .outOfBounds)) : Zig.MM readWideCellLocals readWideCellExit) with
    | .br2 => (do
      let i7 ← Zig.callM (Zig.load (BitVec 16) 2 ((⟨some 0, 44⟩ : Zig.Ptr).elem 2 p0))
      pure (.ret i7))
    | e => pure e) : Zig.MM readWideCellLocals readWideCellExit).run' (default : readWideCellLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure resBytePtrLocals where
  deriving Inhabited

inductive resBytePtrExit where
  | ret (v : Zig.Ptr)

def resBytePtr  : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    pure (.ret (⟨some 0, 71⟩ : Zig.Ptr))) : Zig.MM resBytePtrLocals resBytePtrExit).run' (default : resBytePtrLocals)
  match e with
  | .ret v => pure v

structure wideCellPtrLocals where
  deriving Inhabited

inductive wideCellPtrExit where
  | ret (v : Zig.Ptr)

def wideCellPtr  : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    pure (.ret (⟨some 0, 48⟩ : Zig.Ptr))) : Zig.MM wideCellPtrLocals wideCellPtrExit).run' (default : wideCellPtrLocals)
  match e with
  | .ret v => pure v

structure wideSliceLocals where
  deriving Inhabited

inductive wideSliceExit where
  | ret (v : Zig.Slice)

def wideSlice  : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret (⟨(⟨some 0, 46⟩ : Zig.Ptr), (2 : BitVec 64)⟩ : Zig.Slice))) : Zig.MM wideSliceLocals wideSliceExit).run' (default : wideSliceLocals)
  match e with
  | .ret v => pure v

end UnionBases