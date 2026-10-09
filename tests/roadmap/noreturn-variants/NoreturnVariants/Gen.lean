-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace NoreturnVariants

inductive Kind where
  | x
  | gone
  | y
  deriving Repr, Inhabited, DecidableEq

def Kind.toBits : Kind → BitVec 8
  | .x => (3 : BitVec 8)
  | .gone => (7 : BitVec 8)
  | .y => (9 : BitVec 8)

def Kind.ofInt? (v : Int) : Option Kind :=
  if v = 3 then Option.some .x else if v = 7 then Option.some .gone else if v = 9 then Option.some .y else Option.none

def Kind.isNamed (_ : Kind) : Bool := true

instance : Zig.Packed Kind 8 where
  toBits := Kind.toBits
  ofBits b := (Kind.ofInt? (Zig.val false b)).getD default
  valid b := (Kind.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc Kind where
  size := 1
  align := 1
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 8 ← Zig.Enc.decode bs
    match Kind.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

inductive V where
  | x (v : BitVec 16)
  | y
  deriving Repr, Inhabited, DecidableEq

def V.tag : V → Kind
  | .x _ => .x
  | .y => .y

def V.get_x : V → Zig.Result (BitVec 16)
  | .x v => pure v
  | _ => throw .panic

def V.modify_x (g : BitVec 16 → BitVec 16) : V → V
  | .x v => .x (g v)
  | _ => .x (g default)

def V.setTag_x : V → V
  | .x v => .x v
  | _ => .x default

def V.get_y : V → Zig.Result (Unit)
  | .y => pure ()
  | _ => throw .panic

def V.modify_y (_g : Unit → Unit) : V → V
  | .y => .y
  | _ => .y

def V.setTag_y : V → V
  | .y => .y
  | _ => .y

instance : Zig.Enc V where
  size := 4
  align := 2
  encode v := match v with
    | .x x => Zig.Enc.fields 4 [(2, Zig.Enc.encode v.tag), (0, Zig.Enc.encode x)]
    | .y => Zig.Enc.fields 4 [(2, Zig.Enc.encode v.tag)]
  decode bs := do
    let t : Kind ← Zig.Enc.decodeAt bs 2
    match t with
    | .x => pure (.x (← Zig.Enc.decodeAt bs 0))
    | .gone => throw .illegal
    | .y => pure .y

inductive UTag where
  | a
  | b
  | c
  deriving Repr, Inhabited, DecidableEq

def UTag.toBits : UTag → BitVec 2
  | .a => (0 : BitVec 2)
  | .b => (1 : BitVec 2)
  | .c => (2 : BitVec 2)

def UTag.ofInt? (v : Int) : Option UTag :=
  if v = 0 then Option.some .a else if v = 1 then Option.some .b else if v = 2 then Option.some .c else Option.none

def UTag.isNamed (_ : UTag) : Bool := true

instance : Zig.Packed UTag 2 where
  toBits := UTag.toBits
  ofBits b := (UTag.ofInt? (Zig.val false b)).getD default
  valid b := (UTag.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc UTag where
  size := 1
  align := 1
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 2 ← Zig.Enc.decode bs
    match UTag.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

inductive U where
  | a (v : BitVec 8)
  | c (v : BitVec 32)
  deriving Repr, Inhabited, DecidableEq

def U.tag : U → UTag
  | .a _ => .a
  | .c _ => .c

def U.get_a : U → Zig.Result (BitVec 8)
  | .a v => pure v
  | _ => throw .panic

def U.modify_a (g : BitVec 8 → BitVec 8) : U → U
  | .a v => .a (g v)
  | _ => .a (g default)

def U.setTag_a : U → U
  | .a v => .a v
  | _ => .a default

def U.get_c : U → Zig.Result (BitVec 32)
  | .c v => pure v
  | _ => throw .panic

def U.modify_c (g : BitVec 32 → BitVec 32) : U → U
  | .c v => .c (g v)
  | _ => .c (g default)

def U.setTag_c : U → U
  | .c v => .c v
  | _ => .c default

instance : Zig.Enc U where
  size := 8
  align := 4
  encode v := match v with
    | .a x => Zig.Enc.fields 8 [(4, Zig.Enc.encode v.tag), (0, Zig.Enc.encode x)]
    | .c x => Zig.Enc.fields 8 [(4, Zig.Enc.encode v.tag), (0, Zig.Enc.encode x)]
  decode bs := do
    let t : UTag ← Zig.Enc.decodeAt bs 4
    match t with
    | .a => pure (.a (← Zig.Enc.decodeAt bs 0))
    | .b => throw .illegal
    | .c => pure (.c (← Zig.Enc.decodeAt bs 0))

inductive OneTag where
  | never
  | only
  deriving Repr, Inhabited, DecidableEq

def OneTag.toBits : OneTag → BitVec 1
  | .never => (0 : BitVec 1)
  | .only => (1 : BitVec 1)

def OneTag.ofInt? (v : Int) : Option OneTag :=
  if v = 0 then Option.some .never else if v = 1 then Option.some .only else Option.none

def OneTag.isNamed (_ : OneTag) : Bool := true

instance : Zig.Packed OneTag 1 where
  toBits := OneTag.toBits
  ofBits b := (OneTag.ofInt? (Zig.val false b)).getD default
  valid b := (OneTag.ofInt? (Zig.val false b)).isSome

inductive One where
  | only (v : BitVec 16)
  deriving Repr, Inhabited, DecidableEq

def One.tag : One → OneTag
  | .only _ => .only

def One.get_only : One → Zig.Result (BitVec 16)
  | .only v => pure v

def One.modify_only (g : BitVec 16 → BitVec 16) : One → One
  | .only v => .only (g v)

def One.setTag_only : One → One
  | .only v => .only v

inductive Io_Terminal_ModeTag where
  | no_color
  | escape_codes
  | windows_api
  deriving Repr, Inhabited, DecidableEq

def Io_Terminal_ModeTag.toBits : Io_Terminal_ModeTag → BitVec 2
  | .no_color => (0 : BitVec 2)
  | .escape_codes => (1 : BitVec 2)
  | .windows_api => (2 : BitVec 2)

def Io_Terminal_ModeTag.ofInt? (v : Int) : Option Io_Terminal_ModeTag :=
  if v = 0 then Option.some .no_color else if v = 1 then Option.some .escape_codes else if v = 2 then Option.some .windows_api else Option.none

def Io_Terminal_ModeTag.isNamed (_ : Io_Terminal_ModeTag) : Bool := true

instance : Zig.Packed Io_Terminal_ModeTag 2 where
  toBits := Io_Terminal_ModeTag.toBits
  ofBits b := (Io_Terminal_ModeTag.ofInt? (Zig.val false b)).getD default
  valid b := (Io_Terminal_ModeTag.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc Io_Terminal_ModeTag where
  size := 1
  align := 1
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 2 ← Zig.Enc.decode bs
    match Io_Terminal_ModeTag.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

inductive Io_Terminal_Mode where
  | no_color
  | escape_codes
  deriving Repr, Inhabited, DecidableEq

def Io_Terminal_Mode.tag : Io_Terminal_Mode → Io_Terminal_ModeTag
  | .no_color => .no_color
  | .escape_codes => .escape_codes

def Io_Terminal_Mode.get_no_color : Io_Terminal_Mode → Zig.Result (Unit)
  | .no_color => pure ()
  | _ => throw .panic

def Io_Terminal_Mode.modify_no_color (_g : Unit → Unit) : Io_Terminal_Mode → Io_Terminal_Mode
  | .no_color => .no_color
  | _ => .no_color

def Io_Terminal_Mode.setTag_no_color : Io_Terminal_Mode → Io_Terminal_Mode
  | .no_color => .no_color
  | _ => .no_color

def Io_Terminal_Mode.get_escape_codes : Io_Terminal_Mode → Zig.Result (Unit)
  | .escape_codes => pure ()
  | _ => throw .panic

def Io_Terminal_Mode.modify_escape_codes (_g : Unit → Unit) : Io_Terminal_Mode → Io_Terminal_Mode
  | .escape_codes => .escape_codes
  | _ => .escape_codes

def Io_Terminal_Mode.setTag_escape_codes : Io_Terminal_Mode → Io_Terminal_Mode
  | .escape_codes => .escape_codes
  | _ => .escape_codes

instance : Zig.Enc Io_Terminal_Mode where
  size := 1
  align := 1
  encode v := match v with
    | .no_color => Zig.Enc.fields 1 [(0, Zig.Enc.encode v.tag)]
    | .escape_codes => Zig.Enc.fields 1 [(0, Zig.Enc.encode v.tag)]
  decode bs := do
    let t : Io_Terminal_ModeTag ← Zig.Enc.decodeAt bs 0
    match t with
    | .no_color => pure .no_color
    | .escape_codes => pure .escape_codes
    | .windows_api => throw .illegal

structure Holder where
  mode : Io_Terminal_Mode
  n : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Holder where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(4, Zig.Enc.encode v.mode), (0, Zig.Enc.encode v.n)]
  decode bs := do pure { mode := ← Zig.Enc.decodeAt bs 4, n := ← Zig.Enc.decodeAt bs 0 }

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

structure get_air2lean1Locals where
  deriving Inhabited

inductive get_air2lean1Exit where
  | ret (v : BitVec 32)
  | br2 (v : BitVec 32)

def get_air2lean1 (p0 : U) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (U.tag p0)
    match ← ((do
      match i1 with
      | .a => (do
        let i6 ← Zig.call (U.get_a p0)
        let i7 ← Zig.intCast false false 32 i6
        pure (.br2 i7))
      | .b => (do
        throw .unreachable)
      | .c => (do
        let i10 ← Zig.call (U.get_c p0)
        pure (.br2 i10))) : Zig.M get_air2lean1Locals get_air2lean1Exit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M get_air2lean1Locals get_air2lean1Exit).run' (default : get_air2lean1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure bumpLocals where
  deriving Inhabited

inductive bumpExit where
  | ret

def bump (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i1 ← Zig.load (U) 4 p0
    let i2 ← Zig.callR (get_air2lean1 i1)
    let i3 ← Zig.add false i2 (1 : BitVec 32)
    Zig.store (α := UTag) 1 (p0.add 4) UTag.c
    let i5 ← pure (p0.add 0)
    Zig.store (α := BitVec 32) 4 i5 i3
    pure .ret) : Zig.MM bumpLocals bumpExit).run' (default : bumpLocals)
  match e with
  | .ret => pure ()

structure isColorLocals where
  deriving Inhabited

inductive isColorExit where
  | ret (v : Bool)
  | br2 (v : Bool)
  | br5

def isColor (p0 : Io_Terminal_Mode) : Zig.Result (Bool) := do
  let e ← ((do
    let i1 ← pure (Io_Terminal_Mode.tag p0)
    match ← ((do
      if i1 == Io_Terminal_ModeTag.escape_codes then (do
        pure (.br2 true))
      else (do
        let i4 ← pure (Io_Terminal_ModeTag.isNamed i1)
        match ← ((do
          if i4 then (do
            pure .br5)
          else (do
            throw .panic)) : Zig.M isColorLocals isColorExit) with
        | .br5 => (do
          pure (.br2 false))
        | e => pure e)) : Zig.M isColorLocals isColorExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M isColorLocals isColorExit).run' (default : isColorLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure colorOfLocals where
  deriving Inhabited

inductive colorOfExit where
  | ret (v : Bool)
  | br1 (v : Io_Terminal_Mode)

def colorOf (p0 : BitVec 8) : Zig.Result (Bool) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure (p0 == (1 : BitVec 8))
      if i2 then (do
        pure (.br1 Io_Terminal_Mode.escape_codes))
      else (do
        pure (.br1 Io_Terminal_Mode.no_color))) : Zig.M colorOfLocals colorOfExit) with
    | .br1 v1 => (do
      let i6 ← Zig.call (isColor v1)
      pure (.ret i6))
    | e => pure e) : Zig.M colorOfLocals colorOfExit).run' (default : colorOfLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure holderColorLocals where
  deriving Inhabited

inductive holderColorExit where
  | ret (v : Bool)

def holderColor (p0 : Zig.Ptr) : Zig.MemM (Bool) := do
  let e ← ((do
    let i1 ← pure (p0.add 4)
    let i2 ← Zig.load (Io_Terminal_Mode) 1 i1
    let i3 ← Zig.callR (isColor i2)
    pure (.ret i3)) : Zig.MM holderColorLocals holderColorExit).run' (default : holderColorLocals)
  match e with
  | .ret v => pure v

structure setModeLocals where
  deriving Inhabited

inductive setModeExit where
  | ret
  | br3 (v : Io_Terminal_Mode)

def setMode (p0 : Zig.Ptr) (p1 : Bool) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← pure (p0.add 4)
    match ← ((do
      if p1 then (do
        pure (.br3 Io_Terminal_Mode.escape_codes))
      else (do
        pure (.br3 Io_Terminal_Mode.no_color))) : Zig.MM setModeLocals setModeExit) with
    | .br3 v3 => (do
      Zig.store (α := Io_Terminal_Mode) 1 i2 v3
      pure .ret)
    | e => pure e) : Zig.MM setModeLocals setModeExit).run' (default : setModeLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure holderRoundTripLocals where
  h : Zig.Ptr
  deriving Inhabited

inductive holderRoundTripExit where
  | ret (v : BitVec 32)
  | br8 (v : BitVec 32)

def holderRoundTrip (p0 : Bool) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s2 ← Zig.allocStack 8 4
  let e ← ((do
    let i2 ← pure (← get).h
    let i3 ← pure (i2.add 4)
    Zig.store (α := Io_Terminal_Mode) 1 i3 Io_Terminal_Mode.no_color
    let i5 ← pure (i2.add 0)
    Zig.store (α := BitVec 32) 4 i5 p1
    let _i7 ← Zig.callM (setMode i2 p0)
    match ← ((do
      let i9 ← pure (i2)
      let i10 ← Zig.callM (holderColor i9)
      if i10 then (do
        let i12 ← pure (i2.add 0)
        let i13 ← Zig.load (BitVec 32) 4 i12
        let i14 ← Zig.add false i13 (1 : BitVec 32)
        pure (.br8 i14))
      else (do
        let i16 ← pure (i2.add 0)
        let i17 ← Zig.load (BitVec 32) 4 i16
        pure (.br8 i17))) : Zig.MM holderRoundTripLocals holderRoundTripExit) with
    | .br8 v8 => (do
      pure (.ret v8))
    | e => pure e) : Zig.MM holderRoundTripLocals holderRoundTripExit).run' { (default : holderRoundTripLocals) with h := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mkLocals where
  local1 : U
  deriving Inhabited

inductive mkExit where
  | ret (v : U)

def mk (p0 : BitVec 8) : Zig.Result (U) := do
  let e ← ((do
    modify (fun s => { s with local1 := (U.setTag_a s.local1) })
    modify (fun s => { s with local1 := (U.modify_a (fun _ => p0) s.local1) })
    pure (.ret (← get).local1)) : Zig.M mkLocals mkExit).run' (default : mkLocals)
  match e with
  | .ret v => pure v

structure readULocals where
  deriving Inhabited

inductive readUExit where
  | ret (v : BitVec 32)

def readU (p0 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.load (U) 4 p0
    let i2 ← Zig.callR (get_air2lean1 i1)
    pure (.ret i2)) : Zig.MM readULocals readUExit).run' (default : readULocals)
  match e with
  | .ret v => pure v

structure memRoundTripLocals where
  u : Zig.Ptr
  deriving Inhabited

inductive memRoundTripExit where
  | ret (v : BitVec 32)

def memRoundTrip (p0 : BitVec 8) : Zig.MemM (BitVec 32) := do
  let s1 ← Zig.allocStack 8 4
  let e ← ((do
    let i1 ← pure (← get).u
    let i2 ← Zig.callR (mk p0)
    Zig.store (α := U) 4 i1 i2
    let _i4 ← Zig.callM (bump i1)
    let _i5 ← Zig.callM (bump i1)
    let i6 ← pure (i1)
    let i7 ← Zig.callM (readU i6)
    pure (.ret i7)) : Zig.MM memRoundTripLocals memRoundTripExit).run' { (default : memRoundTripLocals) with u := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

structure mkVLocals where
  local1 : V
  deriving Inhabited

inductive mkVExit where
  | ret (v : V)
  | br2

def mkV (p0 : BitVec 16) : Zig.Result (V) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (p0 == (0 : BitVec 16))
      if i3 then (do
        modify (fun s => { s with local1 := V.y })
        pure .br2)
      else (do
        modify (fun s => { s with local1 := (V.setTag_x s.local1) })
        modify (fun s => { s with local1 := (V.modify_x (fun _ => p0) s.local1) })
        pure .br2)) : Zig.M mkVLocals mkVExit) with
    | .br2 => (do
      let _i11 ← pure ((← get).local1)
      pure (.ret (← get).local1))
    | e => pure e) : Zig.M mkVLocals mkVExit).run' (default : mkVLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure vValueLocals where
  deriving Inhabited

inductive vValueExit where
  | ret (v : BitVec 16)
  | br2 (v : BitVec 16)

def vValue (p0 : V) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← pure (V.tag p0)
    match ← ((do
      match i1 with
      | .x => (do
        let i6 ← Zig.call (V.get_x p0)
        pure (.br2 i6))
      | .gone => (do
        throw .unreachable)
      | .y => (do
        pure (.br2 (0 : BitVec 16)))) : Zig.M vValueLocals vValueExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M vValueLocals vValueExit).run' (default : vValueLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure readVLocals where
  deriving Inhabited

inductive readVExit where
  | ret (v : BitVec 16)

def readV (p0 : Zig.Ptr) : Zig.MemM (BitVec 16) := do
  let e ← ((do
    let i1 ← Zig.load (V) 2 p0
    let i2 ← Zig.callR (vValue i1)
    pure (.ret i2)) : Zig.MM readVLocals readVExit).run' (default : readVLocals)
  match e with
  | .ret v => pure v

structure memVLocals where
  v : Zig.Ptr
  deriving Inhabited

inductive memVExit where
  | ret (v : BitVec 16)

def memV (p0 : BitVec 16) : Zig.MemM (BitVec 16) := do
  let s1 ← Zig.allocStack 4 2
  let e ← ((do
    let i1 ← pure (← get).v
    let i2 ← Zig.callR (mkV p0)
    Zig.store (α := V) 2 i1 i2
    let i4 ← pure (i1)
    let i5 ← Zig.callM (readV i4)
    pure (.ret i5)) : Zig.MM memVLocals memVExit).run' { (default : memVLocals) with v := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

structure oneValueLocals where
  deriving Inhabited

inductive oneValueExit where
  | ret (v : BitVec 16)
  | br1 (v : BitVec 16)

def oneValue (p0 : One) : Zig.Result (BitVec 16) := do
  let e ← ((do
    match ← ((do
      let i2 ← Zig.call (One.get_only p0)
      pure (.br1 i2)) : Zig.M oneValueLocals oneValueExit) with
    | .br1 v1 => (do
      pure (.ret v1))
    | e => pure e) : Zig.M oneValueLocals oneValueExit).run' (default : oneValueLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure oneRoundTripLocals where
  local1 : One
  deriving Inhabited

inductive oneRoundTripExit where
  | ret (v : BitVec 16)

def oneRoundTrip (p0 : BitVec 16) : Zig.Result (BitVec 16) := do
  let e ← ((do
    modify (fun s => { s with local1 := (One.setTag_only s.local1) })
    modify (fun s => { s with local1 := (One.modify_only (fun _ => p0) s.local1) })
    let i6 ← pure ((← get).local1)
    let i7 ← Zig.call (oneValue i6)
    pure (.ret i7)) : Zig.M oneRoundTripLocals oneRoundTripExit).run' (default : oneRoundTripLocals)
  match e with
  | .ret v => pure v

structure roundTripLocals where
  u : U
  deriving Inhabited

inductive roundTripExit where
  | ret (v : BitVec 32)

def roundTrip (p0 : BitVec 8) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i2 ← Zig.call (mk p0)
    modify (fun s => { s with u := i2 })
    modify (fun s => { s with u := (U.setTag_c s.u) })
    let i6 ← Zig.intCast false false 32 p0
    let i7 ← Zig.add false i6 (1 : BitVec 32)
    modify (fun s => { s with u := (U.modify_c (fun _ => i7) s.u) })
    let i9 ← pure ((← get).u)
    let i10 ← Zig.call (get_air2lean1 i9)
    pure (.ret i10)) : Zig.M roundTripLocals roundTripExit).run' (default : roundTripLocals)
  match e with
  | .ret v => pure v

structure vTagLocals where
  deriving Inhabited

inductive vTagExit where
  | ret (v : BitVec 8)

def vTag (p0 : BitVec 16) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i1 ← Zig.call (mkV p0)
    let i2 ← pure (V.tag i1)
    let i3 ← pure (Kind.toBits i2)
    pure (.ret i3)) : Zig.M vTagLocals vTagExit).run' (default : vTagLocals)
  match e with
  | .ret v => pure v

end NoreturnVariants