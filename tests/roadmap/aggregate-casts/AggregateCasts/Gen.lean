-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"unverified","backend":"unverified","build_mode":"unverified","cpu":"unverified","endian":"little","error_layout":"reference-model","error_set_bits":16,"error_tracing":null,"export_stage":"unverified","features":[],"float_mode":"unverified","name":"legacy-abi64-le","pointer_bits":64,"schema":11,"target_triple":"unverified","zig_version":"0.16.0"}}
import ZigLean


namespace AggregateCasts

structure Word where
  bytes : Vector Zig.Byte 4
  deriving Repr, Inhabited, DecidableEq

def Word.get_int (u : Word) : Zig.Result (BitVec 32) := Zig.Raw.get (BitVec 32) u.bytes

def Word.modify_int (g : BitVec 32 → BitVec 32) (u : Word) : Word :=
  ⟨Zig.Raw.set u.bytes (g (Zig.Raw.getD (Zig.Raw.get (BitVec 32) u.bytes)))⟩

def Word.get_bytes (u : Word) : Zig.Result (Vector (BitVec 8) 4) := Zig.Raw.get (Vector (BitVec 8) 4) u.bytes

def Word.modify_bytes (g : Vector (BitVec 8) 4 → Vector (BitVec 8) 4) (u : Word) : Word :=
  ⟨Zig.Raw.set u.bytes (g (Zig.Raw.getD (Zig.Raw.get (Vector (BitVec 8) 4) u.bytes)))⟩

instance : Zig.Enc Word where
  size := 4
  align := 4
  encode v := v.bytes.toArray
  decode bs := pure ⟨Zig.Raw.ofArray 4 bs⟩

structure Short where
  bytes : Vector Zig.Byte 4
  deriving Repr, Inhabited, DecidableEq

def Short.get_a (u : Short) : Zig.Result (BitVec 8) := Zig.Raw.get (BitVec 8) u.bytes

def Short.modify_a (g : BitVec 8 → BitVec 8) (u : Short) : Short :=
  ⟨Zig.Raw.set u.bytes (g (Zig.Raw.getD (Zig.Raw.get (BitVec 8) u.bytes)))⟩

def Short.get_b (u : Short) : Zig.Result (BitVec 32) := Zig.Raw.get (BitVec 32) u.bytes

def Short.modify_b (g : BitVec 32 → BitVec 32) (u : Short) : Short :=
  ⟨Zig.Raw.set u.bytes (g (Zig.Raw.getD (Zig.Raw.get (BitVec 32) u.bytes)))⟩

instance : Zig.Enc Short where
  size := 4
  align := 4
  encode v := v.bytes.toArray
  decode bs := pure ⟨Zig.Raw.ofArray 4 bs⟩

structure Pair where
  a : BitVec 32
  b : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Pair where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.a), (4, Zig.Enc.encode v.b)]
  decode bs := do pure { a := ← Zig.Enc.decodeAt bs 0, b := ← Zig.Enc.decodeAt bs 4 }

structure Padded where
  a : BitVec 8
  b : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Padded where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.a), (4, Zig.Enc.encode v.b)]
  decode bs := do pure { a := ← Zig.Enc.decodeAt bs 0, b := ← Zig.Enc.decodeAt bs 4 }

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

structure bytesToPaddedLocals where
  deriving Inhabited

inductive bytesToPaddedExit where
  | ret (v : Padded)

def bytesToPadded (p0 : Vector (BitVec 8) 8) : Zig.Result (Padded) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Padded) (p0 : Vector (BitVec 8) 8)
    pure (.ret i1)) : Zig.M bytesToPaddedLocals bytesToPaddedExit).run' (default : bytesToPaddedLocals)
  match e with
  | .ret v => pure v

structure bytesToU32Locals where
  deriving Inhabited

inductive bytesToU32Exit where
  | ret (v : BitVec 32)

def bytesToU32 (p0 : Vector (BitVec 8) 4) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.reprCast (BitVec 32) (p0 : Vector (BitVec 8) 4)
    pure (.ret i1)) : Zig.M bytesToU32Locals bytesToU32Exit).run' (default : bytesToU32Locals)
  match e with
  | .ret v => pure v

structure optAddrLocals where
  deriving Inhabited

inductive optAddrExit where
  | ret (v : BitVec 64)

def optAddr (p0 : Option (Zig.Ptr)) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.optPtrAddr p0)))
    pure (.ret i1)) : Zig.MM optAddrLocals optAddrExit).run' (default : optAddrLocals)
  match e with
  | .ret v => pure v

structure optFromAddrLocals where
  deriving Inhabited

inductive optFromAddrExit where
  | ret (v : Option (Zig.Ptr))

def optFromAddr (p0 : BitVec 64) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.optPtrFromAddr (p0).toNat)
    pure (.ret i1)) : Zig.MM optFromAddrLocals optFromAddrExit).run' (default : optFromAddrLocals)
  match e with
  | .ret v => pure v

structure optUnwrapLocals where
  deriving Inhabited

inductive optUnwrapExit where
  | ret (v : Zig.Ptr)

def optUnwrap (p0 : Option (Zig.Ptr)) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.optPtrUnwrap p0
    pure (.ret i1)) : Zig.MM optUnwrapLocals optUnwrapExit).run' (default : optUnwrapLocals)
  match e with
  | .ret v => pure v

structure paddedToBytesLocals where
  deriving Inhabited

inductive paddedToBytesExit where
  | ret (v : Vector (BitVec 8) 8)

def paddedToBytes (p0 : Padded) : Zig.Result (Vector (BitVec 8) 8) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Vector (BitVec 8) 8) (p0 : Padded)
    pure (.ret i1)) : Zig.M paddedToBytesLocals paddedToBytesExit).run' (default : paddedToBytesLocals)
  match e with
  | .ret v => pure v

structure pairToU64Locals where
  deriving Inhabited

inductive pairToU64Exit where
  | ret (v : BitVec 64)

def pairToU64 (p0 : Pair) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.reprCast (BitVec 64) (p0 : Pair)
    pure (.ret i1)) : Zig.M pairToU64Locals pairToU64Exit).run' (default : pairToU64Locals)
  match e with
  | .ret v => pure v

structure ptrWrapLocals where
  deriving Inhabited

inductive ptrWrapExit where
  | ret (v : Option (Zig.Ptr))

def ptrWrap (p0 : Zig.Ptr) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    let i1 ← pure (p0)
    pure (.ret i1)) : Zig.MM ptrWrapLocals ptrWrapExit).run' (default : ptrWrapLocals)
  match e with
  | .ret v => pure v

structure shortToU32Locals where
  deriving Inhabited

inductive shortToU32Exit where
  | ret (v : BitVec 32)

def shortToU32 (p0 : Short) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.reprCast (BitVec 32) (p0 : Short)
    pure (.ret i1)) : Zig.M shortToU32Locals shortToU32Exit).run' (default : shortToU32Locals)
  match e with
  | .ret v => pure v

structure u24x2ToU56Locals where
  deriving Inhabited

inductive u24x2ToU56Exit where
  | ret (v : BitVec 56)

def u24x2ToU56 (p0 : Vector (BitVec 24) 2) : Zig.Result (BitVec 56) := do
  let e ← ((do
    let i1 ← Zig.reprCast (BitVec 56) (p0 : Vector (BitVec 24) 2)
    pure (.ret i1)) : Zig.M u24x2ToU56Locals u24x2ToU56Exit).run' (default : u24x2ToU56Locals)
  match e with
  | .ret v => pure v

structure u32ToBytesLocals where
  deriving Inhabited

inductive u32ToBytesExit where
  | ret (v : Vector (BitVec 8) 4)

def u32ToBytes (p0 : BitVec 32) : Zig.Result (Vector (BitVec 8) 4) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Vector (BitVec 8) 4) (p0 : BitVec 32)
    pure (.ret i1)) : Zig.M u32ToBytesLocals u32ToBytesExit).run' (default : u32ToBytesLocals)
  match e with
  | .ret v => pure v

structure u32ToWordLocals where
  deriving Inhabited

inductive u32ToWordExit where
  | ret (v : Word)

def u32ToWord (p0 : BitVec 32) : Zig.Result (Word) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Word) (p0 : BitVec 32)
    pure (.ret i1)) : Zig.M u32ToWordLocals u32ToWordExit).run' (default : u32ToWordLocals)
  match e with
  | .ret v => pure v

structure u56ToU24x2Locals where
  deriving Inhabited

inductive u56ToU24x2Exit where
  | ret (v : Vector (BitVec 24) 2)

def u56ToU24x2 (p0 : BitVec 56) : Zig.Result (Vector (BitVec 24) 2) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Vector (BitVec 24) 2) (p0 : BitVec 56)
    pure (.ret i1)) : Zig.M u56ToU24x2Locals u56ToU24x2Exit).run' (default : u56ToU24x2Locals)
  match e with
  | .ret v => pure v

structure u64ToPairLocals where
  deriving Inhabited

inductive u64ToPairExit where
  | ret (v : Pair)

def u64ToPair (p0 : BitVec 64) : Zig.Result (Pair) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Pair) (p0 : BitVec 64)
    pure (.ret i1)) : Zig.M u64ToPairLocals u64ToPairExit).run' (default : u64ToPairLocals)
  match e with
  | .ret v => pure v

end AggregateCasts