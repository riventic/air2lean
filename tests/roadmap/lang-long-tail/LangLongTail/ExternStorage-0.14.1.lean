-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.4.19...6.13.4-musl","zig_version":"0.14.1"}}
import ZigLean


namespace ExternStorage

structure Node where
  v : BitVec 32
  next : Option (Zig.Ptr)
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Node where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.v), (8, Zig.Enc.encode v.next)]
  decode bs := do pure { v := ← Zig.Enc.decodeAt bs 0, next := ← Zig.Enc.decodeAt bs 8 }

/-- External initial state: the initial value of each `extern` global, which this program does not define. Fields follow block (initialization) order. Contract: the external definition holds a valid encoding of the field's type before the program starts; any other assumption about external storage is a hypothesis on this value. -/
structure ExternInit where
  /-- Block 0: `ext_counter` (`var`, writable). -/
  ext_counter : BitVec 32
  /-- Block 1: `ext_name` (`const`, read-only). -/
  ext_name : Zig.Ptr
  /-- Block 2: `ext_head` (`var`, writable). -/
  ext_head : Option (Zig.Ptr)
  /-- Block 4: `ext_slot` (`var`, writable). -/
  ext_slot : Zig.Ptr
  /-- External storage: block 5 + `i` is `storage[i]`, after the program's globals. A pointer field may point into it, into a program global or nowhere; any assumption about where is a hypothesis on this value. -/
  storage : List Zig.ExternBlock

/-- The memory at program start under the placement `σ`: block `k` is global `k`. Blocks are added in order; an `extern` block holds its `ext` field, never a default. -/
def mem0 (σ : Zig.Placement) (ext : ExternInit) : Zig.Mem := Zig.Mem.ofGlobals σ ([
  -- 0: ext_counter (extern: initial value `ext.ext_counter`)
  (Zig.Enc.encode (ext.ext_counter : BitVec 32), 4, .global),
  -- 1: ext_name (extern: initial value `ext.ext_name`)
  (Zig.Enc.encode (ext.ext_name : Zig.Ptr), 8, .constGlobal),
  -- 2: ext_head (extern: initial value `ext.ext_head`)
  (Zig.Enc.encode (ext.ext_head : Option (Zig.Ptr)), 8, .global),
  -- 3: extern_storage.local_node
  (Zig.Enc.encode (({ v := (100 : BitVec 32), next := none } : Node) : Node), 8, .global),
  -- 4: ext_slot (extern: initial value `ext.ext_slot`)
  (Zig.Enc.encode (ext.ext_slot : Zig.Ptr), 8, .global)] ++ ext.storage.map Zig.ExternBlock.global)

structure counterLocals where
  deriving Inhabited

inductive counterExit where
  | ret (v : BitVec 32)

def counter  : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i0 ← Zig.load (BitVec 32) 4 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i0)) : Zig.MM counterLocals counterExit).run' (default : counterLocals)
  match e with
  | .ret v => pure v

structure nameLenLocals where
  i : BitVec 32
  deriving Inhabited

inductive nameLenExit where
  | ret (v : BitVec 32)
  | br4
  | br2
  | rep3

def nameLen.again3 : nameLenExit → Bool
  | .rep3 => true
  | _ => false

def nameLen.loop3  : Zig.MM nameLenLocals nameLenExit := do
  match ← ((do
    let i5 ← Zig.load (Zig.Ptr) 8 (⟨some 1, 0⟩ : Zig.Ptr)
    let i6 ← pure ((← get).i)
    let i7 ← Zig.intCast false false 64 i6
    let i8 ← Zig.callM (Zig.load (BitVec 8) 1 (i5.elem 1 i7))
    let i9 ← pure (i8 != (0 : BitVec 8))
    if i9 then (do
      let i11 ← pure ((← get).i)
      let i12 ← Zig.add false i11 (1 : BitVec 32)
      modify (fun s => { s with i := i12 })
      pure .br4)
    else (do
      pure .br2)) : Zig.MM nameLenLocals nameLenExit) with
  | .br4 => (do
    pure .rep3)
  | e => pure e

def nameLen  : Zig.MemM (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (nameLen.loop3 ) nameLen.again3) : Zig.MM nameLenLocals nameLenExit) with
    | .br2 => (do
      let i17 ← pure ((← get).i)
      pure (.ret i17))
    | e => pure e) : Zig.MM nameLenLocals nameLenExit).run' (default : nameLenLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure sumListLocals where
  n : Option (Zig.Ptr)
  s : BitVec 32
  deriving Inhabited

inductive sumListExit where
  | ret (v : BitVec 32)
  | br7
  | br5
  | rep6

def sumList.again6 : sumListExit → Bool
  | .rep6 => true
  | _ => false

def sumList.loop6  : Zig.MM sumListLocals sumListExit := do
  match ← ((do
    let i8 ← pure ((← get).n)
    let i9 ← pure ((i8).isSome)
    if i9 then (do
      let i11 ← Zig.optPayload i8
      let i12 ← pure ((← get).s)
      let i13 ← pure i11
      let i14 ← Zig.load (BitVec 32) 8 i13
      let i15 ← pure (Zig.addWrap i12 i14)
      modify (fun s => { s with s := i15 })
      let i17 ← Zig.callM (Zig.ptrProject i11 (·.add 8))
      let i18 ← Zig.load (Option (Zig.Ptr)) 8 i17
      modify (fun s => { s with n := i18 })
      pure .br7)
    else (do
      pure .br5)) : Zig.MM sumListLocals sumListExit) with
  | .br7 => (do
    pure .rep6)
  | e => pure e

def sumList  : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.load (Option (Zig.Ptr)) 8 (⟨some 2, 0⟩ : Zig.Ptr)
    modify (fun s => { s with n := i1 })
    modify (fun s => { s with s := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (sumList.loop6 ) sumList.again6) : Zig.MM sumListLocals sumListExit) with
    | .br5 => (do
      let i23 ← pure ((← get).s)
      pure (.ret i23))
    | e => pure e) : Zig.MM sumListLocals sumListExit).run' (default : sumListLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure pushLocalLocals where
  deriving Inhabited

inductive pushLocalExit where
  | ret (v : BitVec 32)

def pushLocal  : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i0 ← Zig.load (Option (Zig.Ptr)) 8 (⟨some 2, 0⟩ : Zig.Ptr)
    Zig.store (α := Option (Zig.Ptr)) 8 (⟨some 3, 8⟩ : Zig.Ptr) i0
    Zig.store (α := Option (Zig.Ptr)) 8 (⟨some 2, 0⟩ : Zig.Ptr) (some (⟨some 3, 0⟩ : Zig.Ptr))
    let i3 ← Zig.load (Zig.Ptr) 8 (⟨some 4, 0⟩ : Zig.Ptr)
    let i4 ← Zig.load (BitVec 32) 4 i3
    let i5 ← pure (Zig.addWrap i4 (1 : BitVec 32))
    Zig.store (α := BitVec 32) 4 i3 i5
    let i7 ← Zig.load (BitVec 32) 4 (⟨some 0, 0⟩ : Zig.Ptr)
    let i8 ← pure (Zig.addWrap i7 (1 : BitVec 32))
    Zig.store (α := BitVec 32) 4 (⟨some 0, 0⟩ : Zig.Ptr) i8
    let i10 ← Zig.callM (sumList )
    pure (.ret i10)) : Zig.MM pushLocalLocals pushLocalExit).run' (default : pushLocalLocals)
  match e with
  | .ret v => pure v

structure slotValueLocals where
  deriving Inhabited

inductive slotValueExit where
  | ret (v : BitVec 32)

def slotValue  : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i0 ← Zig.load (Zig.Ptr) 8 (⟨some 4, 0⟩ : Zig.Ptr)
    let i1 ← Zig.load (BitVec 32) 4 i0
    pure (.ret i1)) : Zig.MM slotValueLocals slotValueExit).run' (default : slotValueLocals)
  match e with
  | .ret v => pure v

end ExternStorage