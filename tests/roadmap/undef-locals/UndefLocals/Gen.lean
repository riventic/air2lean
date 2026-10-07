-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"unverified","backend":"unverified","build_mode":"unverified","cpu":"unverified","endian":"little","error_layout":"reference-model","error_set_bits":16,"error_tracing":null,"export_stage":"unverified","features":[],"float_mode":"unverified","name":"legacy-abi64-le","pointer_bits":64,"schema":11,"target_triple":"unverified","zig_version":"0.16.0"}}
import ZigLean


namespace UndefLocals

structure Pair where
  a : BitVec 32
  b : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Pair where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.a), (4, Zig.Enc.encode v.b)]
  decode bs := do pure { a := ← Zig.Enc.decodeAt bs 0, b := ← Zig.Enc.decodeAt bs 4 }

structure branchOutLocals where
  x : Zig.Bytes (BitVec 32)
  deriving Inhabited

inductive branchOutExit where
  | ret (v : BitVec 32)
  | br3
  | br5

def branchOut (p0 : Bool) : Zig.Result (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with x := Zig.Bytes.set s.x 0 ((0 : BitVec 32) : BitVec 32) })
    match ← ((do
      modify (fun s => { s with x := Zig.Bytes.setUndef (BitVec 32) s.x 0 })
      match ← ((do
        if p0 then (do
          pure .br3)
        else (do
          pure .br5)) : Zig.M branchOutLocals branchOutExit) with
      | .br5 => (do
        modify (fun s => { s with x := Zig.Bytes.set s.x 0 ((5 : BitVec 32) : BitVec 32) })
        pure .br3)
      | e => pure e) : Zig.M branchOutLocals branchOutExit) with
    | .br3 => (do
      let i11 ← Zig.Bytes.get (BitVec 32) (← get).x 0
      let i12 ← pure (Zig.addWrap i11 (1 : BitVec 32))
      pure (.ret i12))
    | e => pure e) : Zig.M branchOutLocals branchOutExit).run' { (default : branchOutLocals) with x := Zig.Bytes.undef (BitVec 32) }
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure condWriteLocals where
  x : Zig.Bytes (BitVec 32)
  deriving Inhabited

inductive condWriteExit where
  | ret (v : BitVec 32)
  | br3

def condWrite (p0 : Bool) : Zig.Result (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with x := Zig.Bytes.setUndef (BitVec 32) s.x 0 })
    match ← ((do
      if p0 then (do
        modify (fun s => { s with x := Zig.Bytes.set s.x 0 ((5 : BitVec 32) : BitVec 32) })
        pure .br3)
      else (do
        pure .br3)) : Zig.M condWriteLocals condWriteExit) with
    | .br3 => (do
      let i8 ← Zig.Bytes.get (BitVec 32) (← get).x 0
      let i9 ← pure (Zig.addWrap i8 (1 : BitVec 32))
      pure (.ret i9))
    | e => pure e) : Zig.M condWriteLocals condWriteExit).run' { (default : condWriteLocals) with x := Zig.Bytes.undef (BitVec 32) }
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mkLocals where
  s : Zig.Bytes (Pair)
  deriving Inhabited

inductive mkExit where
  | ret (v : Zig.Bytes (Pair))

def mk  : Zig.Result (Zig.Bytes (Pair)) := do
  let e ← ((do
    modify (fun s => { s with s := Zig.Bytes.setUndef (Pair) s.s 0 })
    modify (fun s => { s with s := Zig.Bytes.set s.s 0 ((1 : BitVec 32) : BitVec 32) })
    let i4 ← pure (← get).s
    pure (.ret i4)) : Zig.M mkLocals mkExit).run' { (default : mkLocals) with s := Zig.Bytes.undef (Pair) }
  match e with
  | .ret v => pure v

structure copyALocals where
  deriving Inhabited

inductive copyAExit where
  | ret (v : BitVec 32)

def copyA  : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i0 ← Zig.call (mk )
    let i1 ← Zig.Bytes.get (BitVec 32) i0 0
    pure (.ret i1)) : Zig.M copyALocals copyAExit).run' (default : copyALocals)
  match e with
  | .ret v => pure v

structure copyBLocals where
  deriving Inhabited

inductive copyBExit where
  | ret (v : BitVec 32)

def copyB  : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i0 ← Zig.call (mk )
    let i1 ← Zig.Bytes.get (BitVec 32) i0 4
    pure (.ret i1)) : Zig.M copyBLocals copyBExit).run' (default : copyBLocals)
  match e with
  | .ret v => pure v

structure fieldALocals where
  s : Zig.Bytes (Pair)
  deriving Inhabited

inductive fieldAExit where
  | ret (v : BitVec 32)

def fieldA  : Zig.Result (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with s := Zig.Bytes.setUndef (Pair) s.s 0 })
    modify (fun s => { s with s := Zig.Bytes.set s.s 0 ((1 : BitVec 32) : BitVec 32) })
    let i5 ← Zig.Bytes.get (BitVec 32) (← get).s 0
    pure (.ret i5)) : Zig.M fieldALocals fieldAExit).run' { (default : fieldALocals) with s := Zig.Bytes.undef (Pair) }
  match e with
  | .ret v => pure v

structure fieldBLocals where
  s : Zig.Bytes (Pair)
  deriving Inhabited

inductive fieldBExit where
  | ret (v : BitVec 32)

def fieldB  : Zig.Result (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with s := Zig.Bytes.setUndef (Pair) s.s 0 })
    modify (fun s => { s with s := Zig.Bytes.set s.s 0 ((1 : BitVec 32) : BitVec 32) })
    let i5 ← Zig.Bytes.get (BitVec 32) (← get).s 4
    pure (.ret i5)) : Zig.M fieldBLocals fieldBExit).run' { (default : fieldBLocals) with s := Zig.Bytes.undef (Pair) }
  match e with
  | .ret v => pure v

structure wholeReadLocals where
  x : Zig.Bytes (BitVec 32)
  deriving Inhabited

inductive wholeReadExit where
  | ret (v : BitVec 32)

def wholeRead  : Zig.Result (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with x := Zig.Bytes.setUndef (BitVec 32) s.x 0 })
    let i2 ← Zig.Bytes.get (BitVec 32) (← get).x 0
    let i3 ← pure (Zig.addWrap i2 (1 : BitVec 32))
    pure (.ret i3)) : Zig.M wholeReadLocals wholeReadExit).run' { (default : wholeReadLocals) with x := Zig.Bytes.undef (BitVec 32) }
  match e with
  | .ret v => pure v

structure writtenReadLocals where
  x : BitVec 32
  deriving Inhabited

inductive writtenReadExit where
  | ret (v : BitVec 32)

def writtenRead  : Zig.Result (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with x := (0#32) })
    modify (fun s => { s with x := (5 : BitVec 32) })
    let i3 ← pure ((← get).x)
    let i4 ← pure (Zig.addWrap i3 (1 : BitVec 32))
    pure (.ret i4)) : Zig.M writtenReadLocals writtenReadExit).run' (default : writtenReadLocals)
  match e with
  | .ret v => pure v

end UndefLocals