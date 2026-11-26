-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"none","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"lime1","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["bulk_memory_opt","call_indirect_overlong","extended_const","multivalue","mutable_globals","nontrapping_fptoint","sign_ext"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":32,"schema":12,"target_triple":"wasm32-freestanding-none","zig_version":"0.17.1"}}
import ZigLean


namespace PointerWidth.CInts.V0_17_1.Wasm32

open scoped Zig.Wasm32

structure Sizes where
  i : BitVec 32
  u : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Sizes where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.i), (4, Zig.Enc.encode v.u)]
  decode bs := do pure { i := ← Zig.Enc.decodeAt bs 0, u := ← Zig.Enc.decodeAt bs 4 }

structure Rec where
  a : BitVec 32
  b : BitVec 32
  c : BitVec 16
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Rec where
  size := 12
  align := 4
  encode v := Zig.Enc.fields 12 [(0, Zig.Enc.encode v.a), (4, Zig.Enc.encode v.b), (8, Zig.Enc.encode v.c)]
  decode bs := do pure { a := ← Zig.Enc.decodeAt bs 0, b := ← Zig.Enc.decodeAt bs 4, c := ← Zig.Enc.decodeAt bs 8 }

structure Mixed where
  c : BitVec 8
  ll : BitVec 64
  us : BitVec 16
  ul : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Mixed where
  size := 24
  align := 8
  encode v := Zig.Enc.fields 24 [(0, Zig.Enc.encode v.c), (8, Zig.Enc.encode v.ll), (16, Zig.Enc.encode v.us), (20, Zig.Enc.encode v.ul)]
  decode bs := do pure { c := ← Zig.Enc.decodeAt bs 0, ll := ← Zig.Enc.decodeAt bs 8, us := ← Zig.Enc.decodeAt bs 16, ul := ← Zig.Enc.decodeAt bs 20 }

structure Ld where
  tag : BitVec 8
  v : Zig.F128
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Ld where
  size := 32
  align := 16
  encode v := Zig.Enc.fields 32 [(0, Zig.Enc.encode v.tag), (16, Zig.Enc.encode v.v)]
  decode bs := do pure { tag := ← Zig.Enc.decodeAt bs 0, v := ← Zig.Enc.decodeAt bs 16 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure charSuccLocals where
  deriving Inhabited

inductive charSuccExit where
  | ret (v : BitVec 8)

def charSucc (p0 : BitVec 8) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i1 ← Zig.add true p0 (1 : BitVec 8)
    pure (.ret i1)) : Zig.M charSuccLocals charSuccExit).run' (default : charSuccLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] charSucc

structure intSuccLocals where
  deriving Inhabited

inductive intSuccExit where
  | ret (v : BitVec 32)

def intSucc (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.add true p0 (1 : BitVec 32)
    pure (.ret i1)) : Zig.M intSuccLocals intSuccExit).run' (default : intSuccLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] intSucc

structure intToLongLocals where
  deriving Inhabited

inductive intToLongExit where
  | ret (v : BitVec 32)

def intToLong (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (p0)
    pure (.ret i1)) : Zig.M intToLongLocals intToLongExit).run' (default : intToLongLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] intToLong

structure isizeNegLocals where
  deriving Inhabited

inductive isizeNegExit where
  | ret (v : BitVec 32)

def isizeNeg (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.sub true (0 : BitVec 32) p0
    pure (.ret i1)) : Zig.M isizeNegLocals isizeNegExit).run' (default : isizeNegLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] isizeNeg

structure isizeSuccLocals where
  deriving Inhabited

inductive isizeSuccExit where
  | ret (v : BitVec 32)

def isizeSucc (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.add true p0 (1 : BitVec 32)
    pure (.ret i1)) : Zig.M isizeSuccLocals isizeSuccExit).run' (default : isizeSuccLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] isizeSucc

structure ldAddLocals where
  deriving Inhabited

inductive ldAddExit where
  | ret (v : Zig.F128)

def ldAdd (p0 : Zig.F128) (p1 : Zig.F128) : Zig.Result (Zig.F128) := do
  let e ← ((do
    let i2 ← pure (Zig.Float.add p0 p1)
    pure (.ret i2)) : Zig.M ldAddLocals ldAddExit).run' (default : ldAddLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] ldAdd

structure ldVLocals where
  deriving Inhabited

inductive ldVExit where
  | ret (v : Zig.F128)

def ldV (p0 : Zig.Ptr) : Zig.MemM (Zig.F128) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.add 16))
    let i2 ← Zig.load (Zig.F128) 16 i1
    pure (.ret i2)) : Zig.MM ldVLocals ldVExit).run' (default : ldVLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] ldV

structure longBitsLocals where
  deriving Inhabited

inductive longBitsExit where
  | ret (v : BitVec 32)

def longBits (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (p0)
    pure (.ret i1)) : Zig.M longBitsLocals longBitsExit).run' (default : longBitsLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] longBits

structure longOfIsizeLocals where
  deriving Inhabited

inductive longOfIsizeExit where
  | ret (v : BitVec 32)

def longOfIsize (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (p0)
    pure (.ret i1)) : Zig.M longOfIsizeLocals longOfIsizeExit).run' (default : longOfIsizeLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] longOfIsize

structure longSuccLocals where
  deriving Inhabited

inductive longSuccExit where
  | ret (v : BitVec 32)

def longSucc (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.add true p0 (1 : BitVec 32)
    pure (.ret i1)) : Zig.M longSuccLocals longSuccExit).run' (default : longSuccLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] longSucc

structure longToIntLocals where
  deriving Inhabited

inductive longToIntExit where
  | ret (v : BitVec 32)

def longToInt (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.intCast true true 32 p0
    pure (.ret i1)) : Zig.M longToIntLocals longToIntExit).run' (default : longToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] longToInt

structure longlongSuccLocals where
  deriving Inhabited

inductive longlongSuccExit where
  | ret (v : BitVec 64)

def longlongSucc (p0 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.add true p0 (1 : BitVec 64)
    pure (.ret i1)) : Zig.M longlongSuccLocals longlongSuccExit).run' (default : longlongSuccLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] longlongSucc

structure mixedLlLocals where
  deriving Inhabited

inductive mixedLlExit where
  | ret (v : BitVec 64)

def mixedLl (p0 : Zig.Ptr) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.add 8))
    let i2 ← Zig.load (BitVec 64) 8 i1
    pure (.ret i2)) : Zig.MM mixedLlLocals mixedLlExit).run' (default : mixedLlLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] mixedLl

structure mixedUlLocals where
  deriving Inhabited

inductive mixedUlExit where
  | ret (v : BitVec 32)

def mixedUl (p0 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.add 20))
    let i2 ← Zig.load (BitVec 32) 4 i1
    pure (.ret i2)) : Zig.MM mixedUlLocals mixedUlExit).run' (default : mixedUlLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] mixedUl

structure recBLocals where
  deriving Inhabited

inductive recBExit where
  | ret (v : BitVec 32)

def recB (p0 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.add 4))
    let i2 ← Zig.load (BitVec 32) 4 i1
    pure (.ret i2)) : Zig.MM recBLocals recBExit).run' (default : recBLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] recB

structure recCLocals where
  deriving Inhabited

inductive recCExit where
  | ret (v : BitVec 16)

def recC (p0 : Zig.Ptr) : Zig.MemM (BitVec 16) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.add 8))
    let i2 ← Zig.load (BitVec 16) 4 i1
    pure (.ret i2)) : Zig.MM recCLocals recCExit).run' (default : recCLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] recC

structure setMixedUsLocals where
  deriving Inhabited

inductive setMixedUsExit where
  | ret

def setMixedUs (p0 : Zig.Ptr) (p1 : BitVec 16) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← Zig.callM (Zig.ptrProject p0 (·.add 16))
    Zig.store (α := BitVec 16) 8 i2 p1
    pure .ret) : Zig.MM setMixedUsLocals setMixedUsExit).run' (default : setMixedUsLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] setMixedUs

structure shortSuccLocals where
  deriving Inhabited

inductive shortSuccExit where
  | ret (v : BitVec 16)

def shortSucc (p0 : BitVec 16) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← Zig.add true p0 (1 : BitVec 16)
    pure (.ret i1)) : Zig.M shortSuccLocals shortSuccExit).run' (default : shortSuccLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] shortSucc

structure sizesULocals where
  deriving Inhabited

inductive sizesUExit where
  | ret (v : BitVec 32)

def sizesU (p0 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.add 4))
    let i2 ← Zig.load (BitVec 32) 4 i1
    pure (.ret i2)) : Zig.MM sizesULocals sizesUExit).run' (default : sizesULocals)
  match e with
  | .ret v => pure v

attribute [zig_run] sizesU

structure uintSuccLocals where
  deriving Inhabited

inductive uintSuccExit where
  | ret (v : BitVec 32)

def uintSucc (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.add false p0 (1 : BitVec 32)
    pure (.ret i1)) : Zig.M uintSuccLocals uintSuccExit).run' (default : uintSuccLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] uintSucc

structure ulongMulLocals where
  deriving Inhabited

inductive ulongMulExit where
  | ret (v : Option (BitVec 32))
  | br3

def ulongMul (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (Option (BitVec 32)) := do
  let e ← ((do
    let i2 ← pure (Zig.mulWithOverflow false p0 p1)
    match ← ((do
      let i4 ← pure ((i2).2)
      let i5 ← pure (i4 != (0 : BitVec 1))
      if i5 then (do
        pure (.ret none))
      else (do
        pure .br3)) : Zig.M ulongMulLocals ulongMulExit) with
    | .br3 => (do
      let i9 ← pure ((i2).1)
      let i10 ← pure (some i9)
      pure (.ret i10))
    | e => pure e) : Zig.M ulongMulLocals ulongMulExit).run' (default : ulongMulLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] ulongMul

structure ulongSuccLocals where
  deriving Inhabited

inductive ulongSuccExit where
  | ret (v : BitVec 32)

def ulongSucc (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.add false p0 (1 : BitVec 32)
    pure (.ret i1)) : Zig.M ulongSuccLocals ulongSuccExit).run' (default : ulongSuccLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] ulongSucc

structure ulonglongSuccLocals where
  deriving Inhabited

inductive ulonglongSuccExit where
  | ret (v : BitVec 64)

def ulonglongSucc (p0 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.add false p0 (1 : BitVec 64)
    pure (.ret i1)) : Zig.M ulonglongSuccLocals ulonglongSuccExit).run' (default : ulonglongSuccLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] ulonglongSucc

structure ushortSuccLocals where
  deriving Inhabited

inductive ushortSuccExit where
  | ret (v : BitVec 16)

def ushortSucc (p0 : BitVec 16) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← Zig.add false p0 (1 : BitVec 16)
    pure (.ret i1)) : Zig.M ushortSuccLocals ushortSuccExit).run' (default : ushortSuccLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] ushortSucc

end PointerWidth.CInts.V0_17_1.Wasm32