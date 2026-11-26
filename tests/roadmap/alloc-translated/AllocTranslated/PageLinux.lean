-- air2lean-profile: {"allocator_model":"translated","correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.1"}}
import ZigLean


namespace AllocTranslated.PageLinux

structure os_linux_PROT__struct_1 where
  READ : Bool
  WRITE : Bool
  EXEC : Bool
  SEM : Bool
  __ : BitVec 20
  GROWSDOWN : Bool
  GROWSUP : Bool
  ___ : BitVec 6
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed os_linux_PROT__struct_1 32 where
  toBits v := ((Zig.Packed.toBits v.READ).setWidth 32 <<< 0) ||| ((Zig.Packed.toBits v.WRITE).setWidth 32 <<< 1) ||| ((Zig.Packed.toBits v.EXEC).setWidth 32 <<< 2) ||| ((Zig.Packed.toBits v.SEM).setWidth 32 <<< 3) ||| ((Zig.Packed.toBits v.__).setWidth 32 <<< 4) ||| ((Zig.Packed.toBits v.GROWSDOWN).setWidth 32 <<< 24) ||| ((Zig.Packed.toBits v.GROWSUP).setWidth 32 <<< 25) ||| ((Zig.Packed.toBits v.___).setWidth 32 <<< 26)
  ofBits b := { READ := Zig.Packed.get b 0, WRITE := Zig.Packed.get b 1, EXEC := Zig.Packed.get b 2, SEM := Zig.Packed.get b 3, __ := Zig.Packed.get b 4, GROWSDOWN := Zig.Packed.get b 24, GROWSUP := Zig.Packed.get b 25, ___ := Zig.Packed.get b 26 }

structure os_linux_MREMAP where
  MAYMOVE : Bool
  FIXED : Bool
  DONTUNMAP : Bool
  «_» : BitVec 29
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed os_linux_MREMAP 32 where
  toBits v := ((Zig.Packed.toBits v.MAYMOVE).setWidth 32 <<< 0) ||| ((Zig.Packed.toBits v.FIXED).setWidth 32 <<< 1) ||| ((Zig.Packed.toBits v.DONTUNMAP).setWidth 32 <<< 2) ||| ((Zig.Packed.toBits v.«_»).setWidth 32 <<< 3)
  ofBits b := { MAYMOVE := Zig.Packed.get b 0, FIXED := Zig.Packed.get b 1, DONTUNMAP := Zig.Packed.get b 2, «_» := Zig.Packed.get b 3 }

inductive os_linux_MAP_TYPE where
  | SHARED
  | PRIVATE
  | SHARED_VALIDATE
  | DROPPABLE
  deriving Repr, Inhabited, DecidableEq

def os_linux_MAP_TYPE.toBits : os_linux_MAP_TYPE → BitVec 4
  | .SHARED => (1 : BitVec 4)
  | .PRIVATE => (2 : BitVec 4)
  | .SHARED_VALIDATE => (3 : BitVec 4)
  | .DROPPABLE => (8 : BitVec 4)

def os_linux_MAP_TYPE.ofInt? (v : Int) : Option os_linux_MAP_TYPE :=
  if v = 1 then Option.some .SHARED else if v = 2 then Option.some .PRIVATE else if v = 3 then Option.some .SHARED_VALIDATE else if v = 8 then Option.some .DROPPABLE else Option.none

def os_linux_MAP_TYPE.isNamed (_ : os_linux_MAP_TYPE) : Bool := true

instance : Zig.Packed os_linux_MAP_TYPE 4 where
  toBits := os_linux_MAP_TYPE.toBits
  ofBits b := (os_linux_MAP_TYPE.ofInt? (Zig.val false b)).getD default
  valid b := (os_linux_MAP_TYPE.ofInt? (Zig.val false b)).isSome

structure os_linux_MAP__struct_1 where
  TYPE : os_linux_MAP_TYPE
  FIXED : Bool
  ANONYMOUS : Bool
  «32BIT» : Bool
  _7 : BitVec 1
  GROWSDOWN : Bool
  _9 : BitVec 2
  DENYWRITE : Bool
  EXECUTABLE : Bool
  LOCKED : Bool
  NORESERVE : Bool
  POPULATE : Bool
  NONBLOCK : Bool
  STACK : Bool
  HUGETLB : Bool
  SYNC : Bool
  FIXED_NOREPLACE : Bool
  _21 : BitVec 5
  UNINITIALIZED : Bool
  «_» : BitVec 5
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed os_linux_MAP__struct_1 32 where
  toBits v := ((Zig.Packed.toBits v.TYPE).setWidth 32 <<< 0) ||| ((Zig.Packed.toBits v.FIXED).setWidth 32 <<< 4) ||| ((Zig.Packed.toBits v.ANONYMOUS).setWidth 32 <<< 5) ||| ((Zig.Packed.toBits v.«32BIT»).setWidth 32 <<< 6) ||| ((Zig.Packed.toBits v._7).setWidth 32 <<< 7) ||| ((Zig.Packed.toBits v.GROWSDOWN).setWidth 32 <<< 8) ||| ((Zig.Packed.toBits v._9).setWidth 32 <<< 9) ||| ((Zig.Packed.toBits v.DENYWRITE).setWidth 32 <<< 11) ||| ((Zig.Packed.toBits v.EXECUTABLE).setWidth 32 <<< 12) ||| ((Zig.Packed.toBits v.LOCKED).setWidth 32 <<< 13) ||| ((Zig.Packed.toBits v.NORESERVE).setWidth 32 <<< 14) ||| ((Zig.Packed.toBits v.POPULATE).setWidth 32 <<< 15) ||| ((Zig.Packed.toBits v.NONBLOCK).setWidth 32 <<< 16) ||| ((Zig.Packed.toBits v.STACK).setWidth 32 <<< 17) ||| ((Zig.Packed.toBits v.HUGETLB).setWidth 32 <<< 18) ||| ((Zig.Packed.toBits v.SYNC).setWidth 32 <<< 19) ||| ((Zig.Packed.toBits v.FIXED_NOREPLACE).setWidth 32 <<< 20) ||| ((Zig.Packed.toBits v._21).setWidth 32 <<< 21) ||| ((Zig.Packed.toBits v.UNINITIALIZED).setWidth 32 <<< 26) ||| ((Zig.Packed.toBits v.«_»).setWidth 32 <<< 27)
  ofBits b := { TYPE := Zig.Packed.get b 0, FIXED := Zig.Packed.get b 4, ANONYMOUS := Zig.Packed.get b 5, «32BIT» := Zig.Packed.get b 6, _7 := Zig.Packed.get b 7, GROWSDOWN := Zig.Packed.get b 8, _9 := Zig.Packed.get b 9, DENYWRITE := Zig.Packed.get b 11, EXECUTABLE := Zig.Packed.get b 12, LOCKED := Zig.Packed.get b 13, NORESERVE := Zig.Packed.get b 14, POPULATE := Zig.Packed.get b 15, NONBLOCK := Zig.Packed.get b 16, STACK := Zig.Packed.get b 17, HUGETLB := Zig.Packed.get b 18, SYNC := Zig.Packed.get b 19, FIXED_NOREPLACE := Zig.Packed.get b 20, _21 := Zig.Packed.get b 21, UNINITIALIZED := Zig.Packed.get b 26, «_» := Zig.Packed.get b 27 }
  valid b := Zig.Packed.validAt (os_linux_MAP_TYPE) b 0

structure mem_Allocator_VTable where
  alloc : Zig.Ptr
  resize : Zig.Ptr
  remap : Zig.Ptr
  free : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc mem_Allocator_VTable where
  size := 32
  align := 8
  encode v := Zig.Enc.fields 32 [(0, Zig.Enc.encode v.alloc), (8, Zig.Enc.encode v.resize), (16, Zig.Enc.encode v.remap), (24, Zig.Enc.encode v.free)]
  decode bs := do pure { alloc := ← Zig.Enc.decodeAt bs 0, resize := ← Zig.Enc.decodeAt bs 8, remap := ← Zig.Enc.decodeAt bs 16, free := ← Zig.Enc.decodeAt bs 24 }

structure mem_Allocator where
  ptr : Zig.Ptr
  vtable : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc mem_Allocator where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.ptr), (8, Zig.Enc.encode v.vtable)]
  decode bs := do pure { ptr := ← Zig.Enc.decodeAt bs 0, vtable := ← Zig.Enc.decodeAt bs 8 }

structure mem_Alignment where
  bits : BitVec 6
  deriving Repr, Inhabited, DecidableEq

def mem_Alignment.«1» : mem_Alignment := ⟨(0 : BitVec 6)⟩
def mem_Alignment.«2» : mem_Alignment := ⟨(1 : BitVec 6)⟩
def mem_Alignment.«4» : mem_Alignment := ⟨(2 : BitVec 6)⟩
def mem_Alignment.«8» : mem_Alignment := ⟨(3 : BitVec 6)⟩
def mem_Alignment.«16» : mem_Alignment := ⟨(4 : BitVec 6)⟩
def mem_Alignment.«32» : mem_Alignment := ⟨(5 : BitVec 6)⟩
def mem_Alignment.«64» : mem_Alignment := ⟨(6 : BitVec 6)⟩

def mem_Alignment.toBits (e : mem_Alignment) : BitVec 6 := e.bits

def mem_Alignment.ofInt? (v : Int) : Option mem_Alignment :=
  if 0 ≤ v ∧ v ≤ 63 then Option.some ⟨BitVec.ofInt 6 v⟩ else Option.none

def mem_Alignment.isNamed (e : mem_Alignment) : Bool := e.bits == (0 : BitVec 6) || e.bits == (1 : BitVec 6) || e.bits == (2 : BitVec 6) || e.bits == (3 : BitVec 6) || e.bits == (4 : BitVec 6) || e.bits == (5 : BitVec 6) || e.bits == (6 : BitVec 6)

instance : Zig.Packed mem_Alignment 6 where
  toBits := mem_Alignment.toBits
  ofBits b := ⟨b⟩

instance : Zig.Enc mem_Alignment where
  size := 1
  align := 1
  encode v := (Zig.intEncExt .little false 6).encode v.toBits
  decode bs := do
    let b : BitVec 6 ← (Zig.intEncExt .little false 6).decode bs
    pure ⟨b⟩

/-- The memory at program start under the placement `σ`: block `k` is global `k`. The words of `@returnAddress()` and of `undefined` pointers are `arbitrary` (`Mem.arbitrary`). -/
def mem0 (σ : Zig.Placement) (arbitrary : Array (BitVec 64) := #[]) : Zig.Mem := { Zig.Mem.ofGlobals σ [
  -- 0: heap.PageAllocator.addr_hint
  (Zig.Enc.encode (none : Option (Zig.Ptr)), 8, .global),
  -- 1: heap.PageAllocator.vtable
  (Zig.Enc.encode (({ alloc := (⟨some 2, 0⟩ : Zig.Ptr), resize := (⟨some 3, 0⟩ : Zig.Ptr), remap := (⟨some 4, 0⟩ : Zig.Ptr), free := (⟨some 5, 0⟩ : Zig.Ptr) } : mem_Allocator_VTable) : mem_Allocator_VTable), 8, .constGlobal),
  -- 2: heap.PageAllocator.alloc
  (#[.undef], 1, .constGlobal),
  -- 3: heap.PageAllocator.resize
  (#[.undef], 1, .constGlobal),
  -- 4: heap.PageAllocator.remap
  (#[.undef], 1, .constGlobal),
  -- 5: heap.PageAllocator.free
  (#[.undef], 1, .constGlobal)] with arbitrary }

/-- The spawn targets of the program. -/
inductive Tgt where

structure debug_assertLocals where
  deriving Inhabited

inductive debug_assertExit where
  | ret
  | br1

def debug_assert (p0 : Bool) : Zig.Result (Unit) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure (!p0)
      if i2 then (do
        throw .unreachable)
      else (do
        pure .br1)) : Zig.M debug_assertLocals debug_assertExit) with
    | .br1 => (do
      pure .ret)
    | e => pure e) : Zig.M debug_assertLocals debug_assertExit).run' (default : debug_assertLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] debug_assert

structure mem_Alignment_toByteUnitsLocals where
  deriving Inhabited

inductive mem_Alignment_toByteUnitsExit where
  | ret (v : BitVec 64)

def mem_Alignment_toByteUnits (p0 : mem_Alignment) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← pure (mem_Alignment.toBits p0)
    let i2 ← pure (Zig.shl (1 : BitVec 64) i1)
    pure (.ret i2)) : Zig.M mem_Alignment_toByteUnitsLocals mem_Alignment_toByteUnitsExit).run' (default : mem_Alignment_toByteUnitsLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Alignment_toByteUnits

structure math_isPowerOfTwo__anon_38853e1fe316Locals where
  deriving Inhabited

inductive math_isPowerOfTwo__anon_38853e1fe316Exit where
  | ret (v : Bool)

def math_isPowerOfTwo__anon_38853e1fe316 (p0 : BitVec 64) : Zig.Result (Bool) := do
  let e ← ((do
    let i1 ← pure (p0)
    let i2 ← pure (Zig.gt false i1 (0 : BitVec 64))
    let _i3 ← Zig.call (debug_assert i2)
    let i4 ← Zig.sub false p0 (1 : BitVec 64)
    let i5 ← pure (p0 &&& i4)
    let i6 ← pure (i5)
    let i7 ← pure (i6 == (0 : BitVec 64))
    pure (.ret i7)) : Zig.M math_isPowerOfTwo__anon_38853e1fe316Locals math_isPowerOfTwo__anon_38853e1fe316Exit).run' (default : math_isPowerOfTwo__anon_38853e1fe316Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] math_isPowerOfTwo__anon_38853e1fe316

structure mem_isValidAlignGeneric__anon_32d5b5f10ec2Locals where
  deriving Inhabited

inductive mem_isValidAlignGeneric__anon_32d5b5f10ec2Exit where
  | ret (v : Bool)
  | br3 (v : Bool)

def mem_isValidAlignGeneric__anon_32d5b5f10ec2 (p0 : BitVec 64) : Zig.Result (Bool) := do
  let e ← ((do
    let i1 ← pure (p0)
    let i2 ← pure (Zig.gt false i1 (0 : BitVec 64))
    match ← ((do
      if i2 then (do
        let i5 ← Zig.call (math_isPowerOfTwo__anon_38853e1fe316 p0)
        pure (.br3 i5))
      else (do
        pure (.br3 false))) : Zig.M mem_isValidAlignGeneric__anon_32d5b5f10ec2Locals mem_isValidAlignGeneric__anon_32d5b5f10ec2Exit) with
    | .br3 v3 => (do
      pure (.ret v3))
    | e => pure e) : Zig.M mem_isValidAlignGeneric__anon_32d5b5f10ec2Locals mem_isValidAlignGeneric__anon_32d5b5f10ec2Exit).run' (default : mem_isValidAlignGeneric__anon_32d5b5f10ec2Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_isValidAlignGeneric__anon_32d5b5f10ec2

structure mem_alignBackward__anon_f056e98f6fd2Locals where
  deriving Inhabited

inductive mem_alignBackward__anon_f056e98f6fd2Exit where
  | ret (v : BitVec 64)

def mem_alignBackward__anon_f056e98f6fd2 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← Zig.call (mem_isValidAlignGeneric__anon_32d5b5f10ec2 p1)
    let _i3 ← Zig.call (debug_assert i2)
    let i4 ← Zig.sub false p1 (1 : BitVec 64)
    let i5 ← pure (~~~i4)
    let i6 ← pure (p0 &&& i5)
    pure (.ret i6)) : Zig.M mem_alignBackward__anon_f056e98f6fd2Locals mem_alignBackward__anon_f056e98f6fd2Exit).run' (default : mem_alignBackward__anon_f056e98f6fd2Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_alignBackward__anon_f056e98f6fd2

structure mem_alignForward__anon_589277751031Locals where
  deriving Inhabited

inductive mem_alignForward__anon_589277751031Exit where
  | ret (v : BitVec 64)

def mem_alignForward__anon_589277751031 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← Zig.call (mem_isValidAlignGeneric__anon_32d5b5f10ec2 p1)
    let _i3 ← Zig.call (debug_assert i2)
    let i4 ← Zig.sub false p1 (1 : BitVec 64)
    let i5 ← Zig.add false p0 i4
    let i6 ← Zig.call (mem_alignBackward__anon_f056e98f6fd2 i5 p1)
    pure (.ret i6)) : Zig.M mem_alignForward__anon_589277751031Locals mem_alignForward__anon_589277751031Exit).run' (default : mem_alignForward__anon_589277751031Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_alignForward__anon_589277751031

structure mem_isValidAlignLocals where
  deriving Inhabited

inductive mem_isValidAlignExit where
  | ret (v : Bool)

def mem_isValidAlign (p0 : BitVec 64) : Zig.Result (Bool) := do
  let e ← ((do
    let i1 ← Zig.call (mem_isValidAlignGeneric__anon_32d5b5f10ec2 p0)
    pure (.ret i1)) : Zig.M mem_isValidAlignLocals mem_isValidAlignExit).run' (default : mem_isValidAlignLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_isValidAlign

structure mem_alignPointerOffset__anon_7004c05f4892Locals where
  ov : BitVec 64 × BitVec 1
  deriving Inhabited

inductive mem_alignPointerOffset__anon_7004c05f4892Exit where
  | ret (v : Option (BitVec 64))
  | br4
  | br15
  | br31

def mem_alignPointerOffset__anon_7004c05f4892 (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (Option (BitVec 64)) := do
  let e ← ((do
    let i2 ← Zig.callR (mem_isValidAlign p1)
    let _i3 ← Zig.callR (debug_assert i2)
    match ← ((do
      let i5 ← pure (p1)
      let i6 ← pure (Zig.le false i5 (4096 : BitVec 64))
      if i6 then (do
        pure (.ret (some (0 : BitVec 64))))
      else (do
        pure .br4)) : Zig.MM mem_alignPointerOffset__anon_7004c05f4892Locals mem_alignPointerOffset__anon_7004c05f4892Exit) with
    | .br4 => (do
      let i10 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
      let i12 ← Zig.sub false p1 (1 : BitVec 64)
      let i13 ← pure (Zig.addWithOverflow false i10 i12)
      modify (fun s => { s with ov := i13 })
      match ← ((do
        let i17 ← pure (((← get).ov).snd)
        let i18 ← pure (i17 != (0 : BitVec 1))
        if i18 then (do
          pure (.ret none))
        else (do
          pure .br15)) : Zig.MM mem_alignPointerOffset__anon_7004c05f4892Locals mem_alignPointerOffset__anon_7004c05f4892Exit) with
      | .br15 => (do
        let i23 ← pure (((← get).ov).fst)
        let i24 ← Zig.sub false p1 (1 : BitVec 64)
        let i25 ← pure (~~~i24)
        let i26 ← pure (i23 &&& i25)
        modify (fun s => { s with ov := { s.ov with fst := i26 } })
        let i29 ← pure (((← get).ov).fst)
        let i30 ← Zig.sub false i29 i10
        match ← ((do
          let i32 ← Zig.rem false i30 (1 : BitVec 64)
          let i33 ← pure (i32)
          let i34 ← pure (i33 != (0 : BitVec 64))
          if i34 then (do
            pure (.ret none))
          else (do
            pure .br31)) : Zig.MM mem_alignPointerOffset__anon_7004c05f4892Locals mem_alignPointerOffset__anon_7004c05f4892Exit) with
        | .br31 => (do
          let i38 ← Zig.divTrunc false i30 (1 : BitVec 64)
          let i39 ← pure (some i38)
          pure (.ret i39))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM mem_alignPointerOffset__anon_7004c05f4892Locals mem_alignPointerOffset__anon_7004c05f4892Exit).run' (default : mem_alignPointerOffset__anon_7004c05f4892Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_alignPointerOffset__anon_7004c05f4892

structure mem_alignPointer__anon_53311c568cf7Locals where
  deriving Inhabited

inductive mem_alignPointer__anon_53311c568cf7Exit where
  | ret (v : Option (Zig.Ptr))
  | br2 (v : BitVec 64)
  | br13

def mem_alignPointer__anon_53311c568cf7 (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i3 ← Zig.callM (mem_alignPointerOffset__anon_7004c05f4892 p0 p1)
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        pure (.br2 i6))
      else (do
        pure (.ret none))) : Zig.MM mem_alignPointer__anon_53311c568cf7Locals mem_alignPointer__anon_53311c568cf7Exit) with
    | .br2 v2 => (do
      let i9 ← Zig.callM (Zig.ptrProject p0 (·.elem 1 v2))
      let i10 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i9)))
      let i11 ← pure (i10 &&& (4095 : BitVec 64))
      let i12 ← pure (i11 == (0 : BitVec 64))
      match ← ((do
        if i12 then (do
          pure .br13)
        else (do
          throw .panic)) : Zig.MM mem_alignPointer__anon_53311c568cf7Locals mem_alignPointer__anon_53311c568cf7Exit) with
      | .br13 => (do
        let i18 ← Zig.callM (Zig.checkAlign 4096 i9 >>= fun _ => pure i9)
        pure (.ret i18))
      | e => pure e)
    | e => pure e) : Zig.MM mem_alignPointer__anon_53311c568cf7Locals mem_alignPointer__anon_53311c568cf7Exit).run' (default : mem_alignPointer__anon_53311c568cf7Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_alignPointer__anon_53311c568cf7

structure heap_PageAllocator_mapLocals where
  local14 : Option (Zig.Ptr)
  local15 : Option (Zig.Ptr)
  local53 : Zig.Slice
  deriving Inhabited

inductive heap_PageAllocator_mapExit where
  | ret (v : Option (Zig.Ptr))
  | br2
  | br4
  | br16
  | br18
  | br33
  | br44 (v : Zig.Slice)
  | br60
  | br82
  | br72
  | br100
  | br114
  | br93
  | br123

def heap_PageAllocator_map (p0 : BitVec 64) (p1 : mem_Alignment) : Zig.ConcM Tgt (Option (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      pure .br2) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
    | .br2 => (do
      match ← ((do
        let i5 ← pure (p0)
        let i6 ← pure (Zig.ge false i5 (18446744073709547519 : BitVec 64))
        if i6 then (do
          pure (.ret none))
        else (do
          pure .br4)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
      | .br4 => (do
        let i10 ← Zig.callRC (mem_Alignment_toByteUnits p1)
        let i11 ← Zig.callRC (mem_alignForward__anon_589277751031 p0 (4096 : BitVec 64))
        let i12 ← pure (Zig.subSat false i10 (4096 : BitVec 64))
        let i13 ← Zig.add false i11 i12
        match ← ((do
          let i17 ← Zig.atomicLoadUnorderedEncC (Option (Zig.Ptr)) 8 (⟨some 0, 0⟩ : Zig.Ptr)
          match ← ((do
            let i19 ← pure ((i17).isNone)
            if i19 then (do
              modify (fun s => { s with local14 := none })
              modify (fun s => { s with local15 := none })
              pure .br16)
            else (do
              pure .br18)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
          | .br18 => (do
            let i25 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.optPtrAddr i17)))
            let i26 ← pure (Zig.subWrap i25 i11)
            let i27 ← Zig.sub false i10 (1 : BitVec 64)
            let i28 ← pure (~~~i27)
            let i29 ← pure (i26 &&& i28)
            let i30 ← pure (Zig.subWrap i29 i12)
            let i31 ← pure (i30 &&& (4095 : BitVec 64))
            let i32 ← pure (i31 == (0 : BitVec 64))
            match ← ((do
              if i32 then (do
                pure .br33)
              else (do
                throw .panic)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
            | .br33 => (do
              let i38 ← Zig.callMC (Zig.checkAddr 4096 false (i30).toNat >>= fun _ => Zig.optPtrFromAddr (i30).toNat)
              modify (fun s => { s with local14 := i17 })
              modify (fun s => { s with local15 := i38 })
              pure .br16)
            | e => pure e)
          | e => pure e) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
        | .br16 => (do
          match ← ((do
            let i45 ← pure ((← get).local15)
            let i46 ← Zig.callMC (Zig.Os.mmap Zig.Os.Target.linux i45 i13 (Zig.Packed.toBits (Zig.Packed.ofBits (3 : BitVec 32) : os_linux_PROT__struct_1)) (Zig.Packed.toBits (Zig.Packed.ofBits (34 : BitVec 32) : os_linux_MAP__struct_1)) (-(1 : BitVec 32)) (0 : BitVec 64))
            let i47 ← pure (Zig.isNonErr i46)
            if i47 then (do
              let i49 ← Zig.callRC (Zig.unwrapPayload i46)
              pure (.br44 i49))
            else (do
              let _i51 ← Zig.callRC (Zig.unwrapErr i46)
              pure (.ret none))) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
          | .br44 v44 => (do
            modify (fun s => { s with local53 := v44 })
            let i57 ← pure (((← get).local53).ptr)
            let i58 ← Zig.callMC (mem_alignPointer__anon_53311c568cf7 i57 i10)
            let i59 ← pure ((i58).isSome)
            match ← ((do
              if i59 then (do
                pure .br60)
              else (do
                throw .panic)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
            | .br60 => (do
              let i65 ← Zig.optPayload i58
              let i67 ← pure (((← get).local53).ptr)
              let i68 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i65)))
              let i69 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i67)))
              let i70 ← pure (Zig.subWrap i68 i69)
              let i71 ← Zig.divExact false i70 (1 : BitVec 64)
              match ← ((do
                let i73 ← pure (i71)
                let i74 ← pure (i73 != (0 : BitVec 64))
                if i74 then (do
                  let i76 ← pure ((← get).local53)
                  let i77 ← pure i76.ptr
                  let i78 ← pure i77
                  let i79 ← Zig.sub false i71 (0 : BitVec 64) (safe := false)
                  let i80 ← pure i76.len
                  let i81 ← pure (Zig.le false i71 i80)
                  match ← ((do
                    if i81 then (do
                      pure .br82)
                    else (do
                      throw .outOfBounds)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
                  | .br82 => (do
                    let i87 ← Zig.callMC (Zig.checkSliceEnd i76.len (0 : BitVec 64) i79 0 >>= fun _ => pure (⟨i78, i79⟩ : Zig.Slice))
                    let i88 ← pure (i87)
                    let _i89 ← Zig.callMC (Zig.Os.munmap Zig.Os.Target.linux i88)
                    pure .br72)
                  | e => pure e)
                else (do
                  pure .br72)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
              | .br72 => (do
                let i92 ← Zig.sub false i13 i71
                match ← ((do
                  let i94 ← pure (i92)
                  let i95 ← pure (i11)
                  let i96 ← pure (Zig.gt false i94 i95)
                  if i96 then (do
                    let i98 ← Zig.callMC (Zig.ptrProject i65 (·.elem 1 i11))
                    let i99 ← pure (Zig.le false i11 i92)
                    match ← ((do
                      if i99 then (do
                        pure .br100)
                      else (do
                        throw .outOfBounds)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
                    | .br100 => (do
                      let i105 ← Zig.sub false i92 i11 (safe := false)
                      let i106 ← pure (⟨i98, i105⟩ : Zig.Slice)
                      let i107 ← pure i106.ptr
                      let i108 ← pure i106.len
                      let i109 ← pure (i108 == (0 : BitVec 64))
                      let i110 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i107)))
                      let i111 ← pure (i110 &&& (4095 : BitVec 64))
                      let i112 ← pure (i111 == (0 : BitVec 64))
                      let i113 ← pure (i109 || i112)
                      match ← ((do
                        if i113 then (do
                          pure .br114)
                        else (do
                          throw .panic)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
                      | .br114 => (do
                        let i119 ← Zig.callMC (Zig.checkAlign 4096 i106.ptr >>= fun _ => pure i106)
                        let _i120 ← Zig.callMC (Zig.Os.munmap Zig.Os.Target.linux i119)
                        pure .br93)
                      | e => pure e)
                    | e => pure e)
                  else (do
                    pure .br93)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
                | .br93 => (do
                  match ← ((do
                    let i124 ← pure i65
                    let i125 ← pure ((← get).local14)
                    let i126 ← pure (i124)
                    let _i127 ← Zig.cmpxchgPtrC (α := Option (Zig.Ptr)) Zig.AtomicOrder.relaxed Zig.AtomicOrder.relaxed 8 (⟨some 0, 0⟩ : Zig.Ptr) i125 i126
                    pure .br123) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
                  | .br123 => (do
                    let i129 ← pure (i65)
                    pure (.ret i129))
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit).run' (default : heap_PageAllocator_mapLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] heap_PageAllocator_map

structure heap_PageAllocator_allocLocals where
  deriving Inhabited

inductive heap_PageAllocator_allocExit where
  | ret (v : Option (Zig.Ptr))

def heap_PageAllocator_alloc (p0 : Zig.Ptr) (p1 : BitVec 64) (p2 : mem_Alignment) (p3 : BitVec 64) : Zig.ConcM Tgt (Option (Zig.Ptr)) := do
  let e ← ((do
    let i4 ← pure (p1)
    let i5 ← pure (Zig.gt false i4 (0 : BitVec 64))
    let _i6 ← Zig.callRC (debug_assert i5)
    let i7 ← Zig.callC (heap_PageAllocator_map p1 p2)
    pure (.ret i7)) : Zig.CM Tgt heap_PageAllocator_allocLocals heap_PageAllocator_allocExit).run' (default : heap_PageAllocator_allocLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] heap_PageAllocator_alloc

structure heap_PageAllocator_unmapLocals where
  local1 : Zig.Slice
  deriving Inhabited

inductive heap_PageAllocator_unmapExit where
  | ret
  | br7
  | br4

def heap_PageAllocator_unmap (p0 : Zig.Slice) : Zig.MemM (Unit) := do
  let e ← ((do
    modify (fun s => { s with local1 := p0 })
    match ← ((do
      let i6 ← pure (((← get).local1).len)
      match ← ((do
        pure .br7) : Zig.MM heap_PageAllocator_unmapLocals heap_PageAllocator_unmapExit) with
      | .br7 => (do
        let i9 ← Zig.callR (mem_alignForward__anon_589277751031 i6 (4096 : BitVec 64))
        let i11 ← pure (((← get).local1).ptr)
        let i12 ← pure i11
        let i13 ← Zig.sub false i9 (0 : BitVec 64) (safe := false)
        let i14 ← pure (⟨i12, i13⟩ : Zig.Slice)
        let i15 ← pure (i14)
        let _i16 ← Zig.callM (Zig.Os.munmap Zig.Os.Target.linux i15)
        pure .br4)
      | e => pure e) : Zig.MM heap_PageAllocator_unmapLocals heap_PageAllocator_unmapExit) with
    | .br4 => (do
      pure .ret)
    | e => pure e) : Zig.MM heap_PageAllocator_unmapLocals heap_PageAllocator_unmapExit).run' (default : heap_PageAllocator_unmapLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] heap_PageAllocator_unmap

structure heap_PageAllocator_freeLocals where
  deriving Inhabited

inductive heap_PageAllocator_freeExit where
  | ret
  | br11

def heap_PageAllocator_free (p0 : Zig.Ptr) (p1 : Zig.Slice) (p2 : mem_Alignment) (p3 : BitVec 64) : Zig.MemM (Unit) := do
  let e ← ((do
    let i4 ← pure p1.ptr
    let i5 ← pure p1.len
    let i6 ← pure (i5 == (0 : BitVec 64))
    let i7 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i4)))
    let i8 ← pure (i7 &&& (4095 : BitVec 64))
    let i9 ← pure (i8 == (0 : BitVec 64))
    let i10 ← pure (i6 || i9)
    match ← ((do
      if i10 then (do
        pure .br11)
      else (do
        throw .panic)) : Zig.MM heap_PageAllocator_freeLocals heap_PageAllocator_freeExit) with
    | .br11 => (do
      let i16 ← Zig.callM (Zig.checkAlign 4096 p1.ptr >>= fun _ => pure p1)
      let _i17 ← Zig.callM (heap_PageAllocator_unmap i16)
      pure .ret)
    | e => pure e) : Zig.MM heap_PageAllocator_freeLocals heap_PageAllocator_freeExit).run' (default : heap_PageAllocator_freeLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] heap_PageAllocator_free

structure heap_PageAllocator_reallocLocals where
  local17 : Zig.Slice
  local57 : Zig.Slice
  deriving Inhabited

inductive heap_PageAllocator_reallocExit where
  | ret (v : Option (Zig.Ptr))
  | br11
  | br20
  | br22
  | br33
  | br45 (v : Zig.Slice)
  | br43
  | br84
  | br65

def heap_PageAllocator_realloc (p0 : Zig.Slice) (p1 : mem_Alignment) (p2 : BitVec 64) (p3 : Bool) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    let i4 ← pure p0.ptr
    let i5 ← pure p0.len
    let i6 ← pure (i5 == (0 : BitVec 64))
    let i7 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i4)))
    let i8 ← pure (i7 &&& (4095 : BitVec 64))
    let i9 ← pure (i8 == (0 : BitVec 64))
    let i10 ← pure (i6 || i9)
    match ← ((do
      if i10 then (do
        pure .br11)
      else (do
        throw .panic)) : Zig.MM heap_PageAllocator_reallocLocals heap_PageAllocator_reallocExit) with
    | .br11 => (do
      let i16 ← Zig.callM (Zig.checkAlign 4096 p0.ptr >>= fun _ => pure p0)
      modify (fun s => { s with local17 := i16 })
      match ← ((do
        pure .br20) : Zig.MM heap_PageAllocator_reallocLocals heap_PageAllocator_reallocExit) with
      | .br20 => (do
        match ← ((do
          let i23 ← Zig.callR (mem_Alignment_toByteUnits p1)
          let i24 ← pure (i23)
          let i25 ← pure (Zig.gt false i24 (4096 : BitVec 64))
          if i25 then (do
            pure (.ret none))
          else (do
            pure .br22)) : Zig.MM heap_PageAllocator_reallocLocals heap_PageAllocator_reallocExit) with
        | .br22 => (do
          let i29 ← Zig.callR (mem_alignForward__anon_589277751031 p2 (4096 : BitVec 64))
          let i31 ← pure (((← get).local17).len)
          let i32 ← Zig.callR (mem_alignForward__anon_589277751031 i31 (4096 : BitVec 64))
          match ← ((do
            let i34 ← pure (i29)
            let i35 ← pure (i32)
            let i36 ← pure (i34 == i35)
            if i36 then (do
              let i39 ← pure (((← get).local17).ptr)
              let i40 ← pure (i39)
              pure (.ret i40))
            else (do
              pure .br33)) : Zig.MM heap_PageAllocator_reallocLocals heap_PageAllocator_reallocExit) with
          | .br33 => (do
            match ← ((do
              if p3 then (do
                match ← ((do
                  let i47 ← pure (((← get).local17).ptr)
                  let i48 ← pure (i47)
                  let i49 ← pure { MAYMOVE := p3, FIXED := false, DONTUNMAP := false, «_» := (0 : BitVec 29) : os_linux_MREMAP }
                  let i50 ← Zig.callM (Zig.Os.mremap Zig.Os.Target.linux i48 i32 i29 (Zig.Packed.toBits i49) none)
                  let i51 ← pure (Zig.isNonErr i50)
                  if i51 then (do
                    let i53 ← Zig.callR (Zig.unwrapPayload i50)
                    pure (.br45 i53))
                  else (do
                    let _i55 ← Zig.callR (Zig.unwrapErr i50)
                    pure (.ret none))) : Zig.MM heap_PageAllocator_reallocLocals heap_PageAllocator_reallocExit) with
                | .br45 v45 => (do
                  modify (fun s => { s with local57 := v45 })
                  let i61 ← pure (((← get).local57).ptr)
                  let i62 ← pure (i61)
                  pure (.ret i62))
                | e => pure e)
              else (do
                pure .br43)) : Zig.MM heap_PageAllocator_reallocLocals heap_PageAllocator_reallocExit) with
            | .br43 => (do
              match ← ((do
                let i66 ← pure (i29)
                let i67 ← pure (i32)
                let i68 ← pure (Zig.lt false i66 i67)
                if i68 then (do
                  let i71 ← pure (((← get).local17).ptr)
                  let i72 ← Zig.callM (Zig.ptrProject i71 (·.elem 1 i29))
                  let i73 ← Zig.sub false i32 i29
                  let i74 ← pure i72
                  let i75 ← Zig.sub false i73 (0 : BitVec 64) (safe := false)
                  let i76 ← pure (⟨i74, i75⟩ : Zig.Slice)
                  let i77 ← pure i76.ptr
                  let i78 ← pure i76.len
                  let i79 ← pure (i78 == (0 : BitVec 64))
                  let i80 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i77)))
                  let i81 ← pure (i80 &&& (4095 : BitVec 64))
                  let i82 ← pure (i81 == (0 : BitVec 64))
                  let i83 ← pure (i79 || i82)
                  match ← ((do
                    if i83 then (do
                      pure .br84)
                    else (do
                      throw .panic)) : Zig.MM heap_PageAllocator_reallocLocals heap_PageAllocator_reallocExit) with
                  | .br84 => (do
                    let i89 ← Zig.callM (Zig.checkAlign 4096 i76.ptr >>= fun _ => pure i76)
                    let _i90 ← Zig.callM (Zig.Os.munmap Zig.Os.Target.linux i89)
                    let i92 ← pure (((← get).local17).ptr)
                    let i93 ← pure (i92)
                    pure (.ret i93))
                  | e => pure e)
                else (do
                  pure .br65)) : Zig.MM heap_PageAllocator_reallocLocals heap_PageAllocator_reallocExit) with
              | .br65 => (do
                pure (.ret none))
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM heap_PageAllocator_reallocLocals heap_PageAllocator_reallocExit).run' (default : heap_PageAllocator_reallocLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] heap_PageAllocator_realloc

structure heap_PageAllocator_remapLocals where
  deriving Inhabited

inductive heap_PageAllocator_remapExit where
  | ret (v : Option (Zig.Ptr))

def heap_PageAllocator_remap (p0 : Zig.Ptr) (p1 : Zig.Slice) (p2 : mem_Alignment) (p3 : BitVec 64) (p4 : BitVec 64) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    let i5 ← Zig.callM (heap_PageAllocator_realloc p1 p2 p3 true)
    pure (.ret i5)) : Zig.MM heap_PageAllocator_remapLocals heap_PageAllocator_remapExit).run' (default : heap_PageAllocator_remapLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] heap_PageAllocator_remap

structure heap_PageAllocator_resizeLocals where
  deriving Inhabited

inductive heap_PageAllocator_resizeExit where
  | ret (v : Bool)

def heap_PageAllocator_resize (p0 : Zig.Ptr) (p1 : Zig.Slice) (p2 : mem_Alignment) (p3 : BitVec 64) (p4 : BitVec 64) : Zig.MemM (Bool) := do
  let e ← ((do
    let i5 ← Zig.callM (heap_PageAllocator_realloc p1 p2 p3 false)
    let i6 ← pure ((i5).isSome)
    pure (.ret i6)) : Zig.MM heap_PageAllocator_resizeLocals heap_PageAllocator_resizeExit).run' (default : heap_PageAllocator_resizeLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] heap_PageAllocator_resize

structure math_mul__anon_44faaf286c79Locals where
  deriving Inhabited

inductive math_mul__anon_44faaf286c79Exit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br3

def math_mul__anon_44faaf286c79 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← pure (Zig.mulWithOverflow false p0 p1)
    match ← ((do
      let i4 ← pure ((i2).2)
      let i5 ← pure (i4 != (0 : BitVec 1))
      if i5 then (do
        pure (.ret (.error "Overflow" : Except Zig.ErrName (BitVec 64))))
      else (do
        pure .br3)) : Zig.M math_mul__anon_44faaf286c79Locals math_mul__anon_44faaf286c79Exit) with
    | .br3 => (do
      let i9 ← pure ((i2).1)
      let i10 ← pure ((.ok i9) : Except Zig.ErrName (BitVec 64))
      pure (.ret i10))
    | e => pure e) : Zig.M math_mul__anon_44faaf286c79Locals math_mul__anon_44faaf286c79Exit).run' (default : math_mul__anon_44faaf286c79Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] math_mul__anon_44faaf286c79

structure mem_Alignment_fromByteUnitsLocals where
  deriving Inhabited

inductive mem_Alignment_fromByteUnitsExit where
  | ret (v : mem_Alignment)

def mem_Alignment_fromByteUnits (p0 : BitVec 64) : Zig.Result (mem_Alignment) := do
  let e ← ((do
    let i1 ← Zig.call (math_isPowerOfTwo__anon_38853e1fe316 p0)
    let _i2 ← Zig.call (debug_assert i1)
    let i3 ← pure (Zig.ctz 7 p0)
    let i4 ← Zig.intCast false false 6 i3
    let i5 ← Zig.enumOf (mem_Alignment.ofInt? (Zig.val false i4))
    pure (.ret i5)) : Zig.M mem_Alignment_fromByteUnitsLocals mem_Alignment_fromByteUnitsExit).run' (default : mem_Alignment_fromByteUnitsLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Alignment_fromByteUnits

structure mem_Allocator_allocBytesAligned__anon_0618802aa46aLocals where
  deriving Inhabited

inductive mem_Allocator_allocBytesAligned__anon_0618802aa46aExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3
  | br10 (v : Option (Zig.Ptr))
  | br9 (v : Zig.Ptr)

def mem_Allocator_allocBytesAligned__anon_0618802aa46a (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (⟨none, 18446744073709551615⟩ : Zig.Ptr) : Except Zig.ErrName (Zig.Ptr))))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_0618802aa46aLocals mem_Allocator_allocBytesAligned__anon_0618802aa46aExit) with
    | .br3 => (do
      match ← ((do
        match ← ((do
          let i11 ← pure ((p0).vtable)
          let i12 ← pure i11
          let i13 ← Zig.load (Zig.Ptr) 8 i12
          let i14 ← pure ((p0).ptr)
          let i15 ← (if i13 == (⟨some 2, 0⟩ : Zig.Ptr) then Zig.callC (heap_PageAllocator_alloc i14 p1 mem_Alignment.«1» p2) else throw .illegal)
          pure (.br10 i15)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_0618802aa46aLocals mem_Allocator_allocBytesAligned__anon_0618802aa46aExit) with
        | .br10 v10 => (do
          let i17 ← pure ((v10).isSome)
          if i17 then (do
            let i19 ← Zig.optPayload v10
            pure (.br9 i19))
          else (do
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr)))))
        | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_0618802aa46aLocals mem_Allocator_allocBytesAligned__anon_0618802aa46aExit) with
      | .br9 v9 => (do
        let i22 ← pure v9
        let i23 ← Zig.sub false p1 (0 : BitVec 64) (safe := false)
        let i24 ← pure (⟨i22, i23⟩ : Zig.Slice)
        let _i25 ← pure i24.len
        Zig.callMC (Zig.memset (α := BitVec 8) 1 i24.ptr i24.len none)
        let i27 ← pure (v9)
        let i28 ← pure ((.ok i27) : Except Zig.ErrName (Zig.Ptr))
        pure (.ret i28))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_0618802aa46aLocals mem_Allocator_allocBytesAligned__anon_0618802aa46aExit).run' (default : mem_Allocator_allocBytesAligned__anon_0618802aa46aLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocBytesAligned__anon_0618802aa46a

structure mem_Allocator_allocBytesAligned__anon_c9141768de1aLocals where
  deriving Inhabited

inductive mem_Allocator_allocBytesAligned__anon_c9141768de1aExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3
  | br10 (v : Option (Zig.Ptr))
  | br9 (v : Zig.Ptr)
  | br30

def mem_Allocator_allocBytesAligned__anon_c9141768de1a (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (⟨none, 18446744073709551612⟩ : Zig.Ptr) : Except Zig.ErrName (Zig.Ptr))))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_c9141768de1aLocals mem_Allocator_allocBytesAligned__anon_c9141768de1aExit) with
    | .br3 => (do
      match ← ((do
        match ← ((do
          let i11 ← pure ((p0).vtable)
          let i12 ← pure i11
          let i13 ← Zig.load (Zig.Ptr) 8 i12
          let i14 ← pure ((p0).ptr)
          let i15 ← (if i13 == (⟨some 2, 0⟩ : Zig.Ptr) then Zig.callC (heap_PageAllocator_alloc i14 p1 mem_Alignment.«4» p2) else throw .illegal)
          pure (.br10 i15)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_c9141768de1aLocals mem_Allocator_allocBytesAligned__anon_c9141768de1aExit) with
        | .br10 v10 => (do
          let i17 ← pure ((v10).isSome)
          if i17 then (do
            let i19 ← Zig.optPayload v10
            pure (.br9 i19))
          else (do
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr)))))
        | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_c9141768de1aLocals mem_Allocator_allocBytesAligned__anon_c9141768de1aExit) with
      | .br9 v9 => (do
        let i22 ← pure v9
        let i23 ← Zig.sub false p1 (0 : BitVec 64) (safe := false)
        let i24 ← pure (⟨i22, i23⟩ : Zig.Slice)
        let _i25 ← pure i24.len
        Zig.callMC (Zig.memset (α := BitVec 8) 1 i24.ptr i24.len none)
        let i27 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr v9)))
        let i28 ← pure (i27 &&& (3 : BitVec 64))
        let i29 ← pure (i28 == (0 : BitVec 64))
        match ← ((do
          if i29 then (do
            pure .br30)
          else (do
            throw .panic)) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_c9141768de1aLocals mem_Allocator_allocBytesAligned__anon_c9141768de1aExit) with
        | .br30 => (do
          let i35 ← Zig.callMC (Zig.checkAlign 4 v9 >>= fun _ => pure v9)
          let i36 ← pure ((.ok i35) : Except Zig.ErrName (Zig.Ptr))
          pure (.ret i36))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesAligned__anon_c9141768de1aLocals mem_Allocator_allocBytesAligned__anon_c9141768de1aExit).run' (default : mem_Allocator_allocBytesAligned__anon_c9141768de1aLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocBytesAligned__anon_c9141768de1a

structure mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Locals where
  deriving Inhabited

inductive mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3 (v : BitVec 64)

def mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43 (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.callRC (math_mul__anon_44faaf286c79 (1 : BitVec 64) p1)
      let i5 ← pure (Zig.isNonErr i4)
      if i5 then (do
        let i7 ← Zig.callRC (Zig.unwrapPayload i4)
        pure (.br3 i7))
      else (do
        let _i9 ← Zig.callRC (Zig.unwrapErr i4)
        pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr))))) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Locals mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Exit) with
    | .br3 v3 => (do
      let i11 ← Zig.callC (mem_Allocator_allocBytesAligned__anon_0618802aa46a p0 v3 p2)
      pure (.ret i11))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Locals mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Exit).run' (default : mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43

structure mem_Allocator_alloc__anon_a8254a5f2b74Locals where
  local14 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_alloc__anon_a8254a5f2b74Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br3 (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_alloc__anon_a8254a5f2b74 (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s14 ← Zig.allocStack 24 8
  let e ← ((do
    let i2 ← Zig.callMC Zig.returnAddress
    match ← ((do
      let i4 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43 p0 p1 i2)
      match i4 with
      | .error _ => (do
        let i6 ← Zig.callRC (Zig.unwrapErr i4)
        let i7 ← pure ((.error i6) : Except Zig.ErrName (Zig.Slice))
        pure (.br3 i7))
      | .ok v5 => (do
        let i9 ← pure v5
        let i10 ← Zig.sub false p1 (0 : BitVec 64) (safe := false)
        let i11 ← pure (⟨i9, i10⟩ : Zig.Slice)
        let i12 ← pure ((.ok i11) : Except Zig.ErrName (Zig.Slice))
        pure (.br3 i12))) : Zig.CM Tgt mem_Allocator_alloc__anon_a8254a5f2b74Locals mem_Allocator_alloc__anon_a8254a5f2b74Exit) with
    | .br3 v3 => (do
      let i14 ← pure (← get).local14
      (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i14 v3)
      let i16 ← pure (i14)
      let i17 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i16)
      pure (.ret i17))
    | e => pure e) : Zig.CM Tgt mem_Allocator_alloc__anon_a8254a5f2b74Locals mem_Allocator_alloc__anon_a8254a5f2b74Exit).run' { (default : mem_Allocator_alloc__anon_a8254a5f2b74Locals) with local14 := s14 }
  Zig.free s14
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_alloc__anon_a8254a5f2b74

structure mem_Allocator_create__anon_8f6a81b88324Locals where
  local11 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_create__anon_8f6a81b88324Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br2 (v : Except Zig.ErrName (Zig.Ptr))

def mem_Allocator_create__anon_8f6a81b88324 (p0 : mem_Allocator) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let s11 ← Zig.allocStack 16 8
  let e ← ((do
    let i1 ← Zig.callMC Zig.returnAddress
    match ← ((do
      let i3 ← Zig.callC (mem_Allocator_allocBytesAligned__anon_c9141768de1a p0 (4 : BitVec 64) i1)
      match i3 with
      | .error _ => (do
        let i5 ← Zig.callRC (Zig.unwrapErr i3)
        let i6 ← pure ((.error i5) : Except Zig.ErrName (Zig.Ptr))
        pure (.br2 i6))
      | .ok v4 => (do
        let i8 ← pure (v4)
        let i9 ← pure ((.ok i8) : Except Zig.ErrName (Zig.Ptr))
        pure (.br2 i9))) : Zig.CM Tgt mem_Allocator_create__anon_8f6a81b88324Locals mem_Allocator_create__anon_8f6a81b88324Exit) with
    | .br2 v2 => (do
      let i11 ← pure (← get).local11
      (letI : Zig.Enc (Except Zig.ErrName (Zig.Ptr)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Ptr))); Zig.store (α := Except Zig.ErrName (Zig.Ptr)) 8 i11 v2)
      let i13 ← pure (i11)
      let i14 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Ptr)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Ptr))); Zig.load (Except Zig.ErrName (Zig.Ptr)) 8 i13)
      pure (.ret i14))
    | e => pure e) : Zig.CM Tgt mem_Allocator_create__anon_8f6a81b88324Locals mem_Allocator_create__anon_8f6a81b88324Exit).run' { (default : mem_Allocator_create__anon_8f6a81b88324Locals) with local11 := s11 }
  Zig.free s11
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_create__anon_8f6a81b88324

structure mem_Allocator_destroy__anon_7fa4accb9a56Locals where
  deriving Inhabited

inductive mem_Allocator_destroy__anon_7fa4accb9a56Exit where
  | ret
  | br8

def mem_Allocator_destroy__anon_7fa4accb9a56 (p0 : mem_Allocator) (p1 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← pure (p1)
    let i3 ← pure i2
    let i4 ← pure (i3)
    let i5 ← pure (⟨i4, (4 : BitVec 64)⟩ : Zig.Slice)
    let i6 ← Zig.callR (mem_Alignment_fromByteUnits (4 : BitVec 64))
    let i7 ← Zig.callM Zig.returnAddress
    match ← ((do
      let i9 ← pure ((p0).vtable)
      let i10 ← Zig.callM (Zig.ptrProject i9 (·.add 24))
      let i11 ← Zig.load (Zig.Ptr) 8 i10
      let i12 ← pure ((p0).ptr)
      let _i13 ← (if i11 == (⟨some 5, 0⟩ : Zig.Ptr) then Zig.callM (heap_PageAllocator_free i12 i5 i6 i7) else throw .illegal)
      pure .br8) : Zig.MM mem_Allocator_destroy__anon_7fa4accb9a56Locals mem_Allocator_destroy__anon_7fa4accb9a56Exit) with
    | .br8 => (do
      pure .ret)
    | e => pure e) : Zig.MM mem_Allocator_destroy__anon_7fa4accb9a56Locals mem_Allocator_destroy__anon_7fa4accb9a56Exit).run' (default : mem_Allocator_destroy__anon_7fa4accb9a56Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_destroy__anon_7fa4accb9a56

structure mem_absorbSentinel__anon_7342b53a30edLocals where
  deriving Inhabited

inductive mem_absorbSentinel__anon_7342b53a30edExit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_7342b53a30ed (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret p0)) : Zig.MM mem_absorbSentinel__anon_7342b53a30edLocals mem_absorbSentinel__anon_7342b53a30edExit).run' (default : mem_absorbSentinel__anon_7342b53a30edLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_absorbSentinel__anon_7342b53a30ed

structure mem_Allocator_free__anon_1e60e7ef40f5Locals where
  deriving Inhabited

inductive mem_Allocator_free__anon_1e60e7ef40f5Exit where
  | ret
  | br4
  | br15

def mem_Allocator_free__anon_1e60e7ef40f5 (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← Zig.callM (mem_absorbSentinel__anon_7342b53a30ed p1)
    let i3 ← pure (i2)
    match ← ((do
      let i5 ← pure i3.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        pure .ret)
      else (do
        pure .br4)) : Zig.MM mem_Allocator_free__anon_1e60e7ef40f5Locals mem_Allocator_free__anon_1e60e7ef40f5Exit) with
    | .br4 => (do
      let _i11 ← pure i3.len
      Zig.callM (Zig.memset (α := BitVec 8) 1 i3.ptr i3.len none)
      let i13 ← Zig.callR (mem_Alignment_fromByteUnits (1 : BitVec 64))
      let i14 ← Zig.callM Zig.returnAddress
      match ← ((do
        let i16 ← pure ((p0).vtable)
        let i17 ← Zig.callM (Zig.ptrProject i16 (·.add 24))
        let i18 ← Zig.load (Zig.Ptr) 8 i17
        let i19 ← pure ((p0).ptr)
        let _i20 ← (if i18 == (⟨some 5, 0⟩ : Zig.Ptr) then Zig.callM (heap_PageAllocator_free i19 i3 i13 i14) else throw .illegal)
        pure .br15) : Zig.MM mem_Allocator_free__anon_1e60e7ef40f5Locals mem_Allocator_free__anon_1e60e7ef40f5Exit) with
      | .br15 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.MM mem_Allocator_free__anon_1e60e7ef40f5Locals mem_Allocator_free__anon_1e60e7ef40f5Exit).run' (default : mem_Allocator_free__anon_1e60e7ef40f5Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

attribute [zig_run] mem_Allocator_free__anon_1e60e7ef40f5

structure mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals where
  local20 : Zig.Ptr
  deriving Inhabited

inductive mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br9 (v : Except Zig.ErrName (Zig.Slice))
  | br4
  | br26
  | br35 (v : BitVec 64)
  | br45 (v : Option (Zig.Ptr))
  | br43
  | br64 (v : Option (Zig.Ptr))
  | br62 (v : Zig.Ptr)
  | br90
  | br99
  | br111
  | br120

def mem_Allocator_reallocAdvanced__anon_0df1ef68623e (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) (p3 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let s20 ← Zig.allocStack 24 8
  let e ← ((do
    match ← ((do
      let i5 ← pure p1.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        match ← ((do
          let i10 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43 p0 p2 p3)
          match i10 with
          | .error _ => (do
            let i12 ← Zig.callRC (Zig.unwrapErr i10)
            let i13 ← pure ((.error i12) : Except Zig.ErrName (Zig.Slice))
            pure (.br9 i13))
          | .ok v11 => (do
            let i15 ← pure v11
            let i16 ← Zig.sub false p2 (0 : BitVec 64) (safe := false)
            let i17 ← pure (⟨i15, i16⟩ : Zig.Slice)
            let i18 ← pure ((.ok i17) : Except Zig.ErrName (Zig.Slice))
            pure (.br9 i18))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
        | .br9 v9 => (do
          let i20 ← pure (← get).local20
          (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.store (α := Except Zig.ErrName (Zig.Slice)) 8 i20 v9)
          let i22 ← pure (i20)
          let i23 ← (letI : Zig.Enc (Except Zig.ErrName (Zig.Slice)) := Zig.errorUnionEnc (⟨#["OutOfMemory"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (Zig.Slice))); Zig.load (Except Zig.ErrName (Zig.Slice)) 8 i22)
          pure (.ret i23))
        | e => pure e)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
    | .br4 => (do
      match ← ((do
        let i27 ← pure (p2)
        let i28 ← pure (i27 == (0 : BitVec 64))
        if i28 then (do
          let _i30 ← Zig.callMC (mem_Allocator_free__anon_1e60e7ef40f5 p0 p1)
          pure (.ret (.ok (⟨(⟨none, 18446744073709551615⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice) : Except Zig.ErrName (Zig.Slice))))
        else (do
          pure .br26)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
      | .br26 => (do
        let i33 ← Zig.callMC (mem_absorbSentinel__anon_7342b53a30ed p1)
        let i34 ← pure (i33)
        match ← ((do
          let i36 ← Zig.callRC (math_mul__anon_44faaf286c79 (1 : BitVec 64) p2)
          let i37 ← pure (Zig.isNonErr i36)
          if i37 then (do
            let i39 ← Zig.callRC (Zig.unwrapPayload i36)
            pure (.br35 i39))
          else (do
            let _i41 ← Zig.callRC (Zig.unwrapErr i36)
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice))))) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
        | .br35 v35 => (do
          match ← ((do
            let i44 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
            match ← ((do
              let i46 ← pure ((p0).vtable)
              let i47 ← Zig.callMC (Zig.ptrProject i46 (·.add 16))
              let i48 ← Zig.load (Zig.Ptr) 8 i47
              let i49 ← pure ((p0).ptr)
              let i50 ← (if i48 == (⟨some 4, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_remap i49 i34 i44 v35 p3) else throw .illegal)
              pure (.br45 i50)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
            | .br45 v45 => (do
              let i52 ← pure ((v45).isSome)
              if i52 then (do
                let i54 ← Zig.optPayload v45
                let i55 ← pure i54
                let i56 ← Zig.sub false v35 (0 : BitVec 64) (safe := false)
                let i57 ← pure (⟨i55, i56⟩ : Zig.Slice)
                let i58 ← pure (i57)
                let i59 ← pure ((.ok i58) : Except Zig.ErrName (Zig.Slice))
                pure (.ret i59))
              else (do
                pure .br43))
            | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
          | .br43 => (do
            match ← ((do
              let i63 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
              match ← ((do
                let i65 ← pure ((p0).vtable)
                let i66 ← pure i65
                let i67 ← Zig.load (Zig.Ptr) 8 i66
                let i68 ← pure ((p0).ptr)
                let i69 ← (if i67 == (⟨some 2, 0⟩ : Zig.Ptr) then Zig.callC (heap_PageAllocator_alloc i68 v35 i63 p3) else throw .illegal)
                pure (.br64 i69)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
              | .br64 v64 => (do
                let i71 ← pure ((v64).isSome)
                if i71 then (do
                  let i73 ← Zig.optPayload v64
                  pure (.br62 i73))
                else (do
                  pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Slice)))))
              | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
            | .br62 v62 => (do
              let i76 ← pure i34.len
              let i77 ← pure (v35)
              let i78 ← pure (i76)
              let i79 ← pure (Zig.min false i77 i78)
              let i80 ← pure v62
              let i81 ← pure (i79)
              let i82 ← Zig.sub false i81 (0 : BitVec 64) (safe := false)
              let i83 ← pure (⟨i80, i82⟩ : Zig.Slice)
              let i84 ← pure i34.ptr
              let i85 ← pure i84
              let i86 ← pure (i79)
              let i87 ← Zig.sub false i86 (0 : BitVec 64) (safe := false)
              let i88 ← pure i34.len
              let i89 ← pure (Zig.le false i86 i88)
              match ← ((do
                if i89 then (do
                  pure .br90)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
              | .br90 => (do
                let i95 ← Zig.callMC (Zig.checkSliceEnd i34.len (0 : BitVec 64) i87 0 >>= fun _ => pure (⟨i85, i87⟩ : Zig.Slice))
                let i96 ← pure i83.len
                let i97 ← pure i95.len
                let i98 ← pure (i96 == i97)
                match ← ((do
                  if i98 then (do
                    pure .br99)
                  else (do
                    throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
                | .br99 => (do
                  let i104 ← pure i95.ptr
                  let i105 ← pure i83.ptr
                  let i106 ← Zig.callMC (Zig.ptrProject i104 (·.elem 1 i96))
                  let i107 ← Zig.callMC (Zig.ptrProject i105 (·.elem 1 i96))
                  let i108 ← Zig.callMC (Zig.ptrLe i106 i105)
                  let i109 ← Zig.callMC (Zig.ptrLe i107 i104)
                  let i110 ← pure (i108 || i109)
                  match ← ((do
                    if i110 then (do
                      pure .br111)
                    else (do
                      throw .panic)) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
                  | .br111 => (do
                    Zig.callMC (Zig.memcpy 1 1 1 i83.ptr i104 i83.len i95.len)
                    let _i117 ← pure i34.len
                    Zig.callMC (Zig.memset (α := BitVec 8) 1 i34.ptr i34.len none)
                    let i119 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
                    match ← ((do
                      let i121 ← pure ((p0).vtable)
                      let i122 ← Zig.callMC (Zig.ptrProject i121 (·.add 24))
                      let i123 ← Zig.load (Zig.Ptr) 8 i122
                      let i124 ← pure ((p0).ptr)
                      let _i125 ← (if i123 == (⟨some 5, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_free i124 i34 i119 p3) else throw .illegal)
                      pure .br120) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit) with
                    | .br120 => (do
                      let i127 ← pure v62
                      let i128 ← Zig.sub false v35 (0 : BitVec 64) (safe := false)
                      let i129 ← pure (⟨i127, i128⟩ : Zig.Slice)
                      let i130 ← pure (i129)
                      let i131 ← pure ((.ok i130) : Except Zig.ErrName (Zig.Slice))
                      pure (.ret i131))
                    | e => pure e)
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals mem_Allocator_reallocAdvanced__anon_0df1ef68623eExit).run' { (default : mem_Allocator_reallocAdvanced__anon_0df1ef68623eLocals) with local20 := s20 }
  Zig.free s20
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_reallocAdvanced__anon_0df1ef68623e

structure mem_Allocator_realloc__anon_af0c43114565Locals where
  deriving Inhabited

inductive mem_Allocator_realloc__anon_af0c43114565Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_realloc__anon_af0c43114565 (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i3 ← Zig.callMC Zig.returnAddress
    let i4 ← Zig.callC (mem_Allocator_reallocAdvanced__anon_0df1ef68623e p0 p1 p2 i3)
    pure (.ret i4)) : Zig.CM Tgt mem_Allocator_realloc__anon_af0c43114565Locals mem_Allocator_realloc__anon_af0c43114565Exit).run' (default : mem_Allocator_realloc__anon_af0c43114565Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] mem_Allocator_realloc__anon_af0c43114565

structure mem_Allocator_remap__anon_e29e4a94db2bLocals where
  deriving Inhabited

inductive mem_Allocator_remap__anon_e29e4a94db2bExit where
  | ret (v : Option (Zig.Slice))
  | br3
  | br16
  | br25 (v : BitVec 64)
  | br36 (v : Option (Zig.Ptr))
  | br33 (v : Zig.Ptr)

def mem_Allocator_remap__anon_e29e4a94db2b (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.MemM (Option (Zig.Slice)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p2)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        let _i7 ← Zig.callM (mem_Allocator_free__anon_1e60e7ef40f5 p0 p1)
        let i8 ← pure p1.ptr
        let i9 ← pure i8
        let i10 ← pure (i9)
        let _i11 ← pure p1.len
        let i12 ← pure (⟨i10, (0 : BitVec 64)⟩ : Zig.Slice)
        let i13 ← pure (some i12)
        pure (.ret i13))
      else (do
        pure .br3)) : Zig.MM mem_Allocator_remap__anon_e29e4a94db2bLocals mem_Allocator_remap__anon_e29e4a94db2bExit) with
    | .br3 => (do
      match ← ((do
        let i17 ← pure p1.len
        let i18 ← pure (i17)
        let i19 ← pure (i18 == (0 : BitVec 64))
        if i19 then (do
          pure (.ret none))
        else (do
          pure .br16)) : Zig.MM mem_Allocator_remap__anon_e29e4a94db2bLocals mem_Allocator_remap__anon_e29e4a94db2bExit) with
      | .br16 => (do
        let i23 ← Zig.callM (mem_absorbSentinel__anon_7342b53a30ed p1)
        let i24 ← pure (i23)
        match ← ((do
          let i26 ← Zig.callR (math_mul__anon_44faaf286c79 (1 : BitVec 64) p2)
          let i27 ← pure (Zig.isNonErr i26)
          if i27 then (do
            let i29 ← Zig.callR (Zig.unwrapPayload i26)
            pure (.br25 i29))
          else (do
            let _i31 ← Zig.callR (Zig.unwrapErr i26)
            pure (.ret none))) : Zig.MM mem_Allocator_remap__anon_e29e4a94db2bLocals mem_Allocator_remap__anon_e29e4a94db2bExit) with
        | .br25 v25 => (do
          match ← ((do
            let i34 ← Zig.callR (mem_Alignment_fromByteUnits (1 : BitVec 64))
            let i35 ← Zig.callM Zig.returnAddress
            match ← ((do
              let i37 ← pure ((p0).vtable)
              let i38 ← Zig.callM (Zig.ptrProject i37 (·.add 16))
              let i39 ← Zig.load (Zig.Ptr) 8 i38
              let i40 ← pure ((p0).ptr)
              let i41 ← (if i39 == (⟨some 4, 0⟩ : Zig.Ptr) then Zig.callM (heap_PageAllocator_remap i40 i24 i34 v25 i35) else throw .illegal)
              pure (.br36 i41)) : Zig.MM mem_Allocator_remap__anon_e29e4a94db2bLocals mem_Allocator_remap__anon_e29e4a94db2bExit) with
            | .br36 v36 => (do
              let i43 ← pure ((v36).isSome)
              if i43 then (do
                let i45 ← Zig.optPayload v36
                pure (.br33 i45))
              else (do
                pure (.ret none)))
            | e => pure e) : Zig.MM mem_Allocator_remap__anon_e29e4a94db2bLocals mem_Allocator_remap__anon_e29e4a94db2bExit) with
          | .br33 v33 => (do
            let i48 ← pure v33
            let i49 ← Zig.sub false v25 (0 : BitVec 64) (safe := false)
            let i50 ← pure (⟨i48, i49⟩ : Zig.Slice)
            let i51 ← pure (i50)
            pure (.ret i51))
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM mem_Allocator_remap__anon_e29e4a94db2bLocals mem_Allocator_remap__anon_e29e4a94db2bExit).run' (default : mem_Allocator_remap__anon_e29e4a94db2bLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_remap__anon_e29e4a94db2b

structure mem_Allocator_resize__anon_ec6bca265858Locals where
  deriving Inhabited

inductive mem_Allocator_resize__anon_ec6bca265858Exit where
  | ret (v : Bool)
  | br3
  | br10
  | br19 (v : BitVec 64)
  | br29 (v : Bool)

def mem_Allocator_resize__anon_ec6bca265858 (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.MemM (Bool) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p2)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        let _i7 ← Zig.callM (mem_Allocator_free__anon_1e60e7ef40f5 p0 p1)
        pure (.ret true))
      else (do
        pure .br3)) : Zig.MM mem_Allocator_resize__anon_ec6bca265858Locals mem_Allocator_resize__anon_ec6bca265858Exit) with
    | .br3 => (do
      match ← ((do
        let i11 ← pure p1.len
        let i12 ← pure (i11)
        let i13 ← pure (i12 == (0 : BitVec 64))
        if i13 then (do
          pure (.ret false))
        else (do
          pure .br10)) : Zig.MM mem_Allocator_resize__anon_ec6bca265858Locals mem_Allocator_resize__anon_ec6bca265858Exit) with
      | .br10 => (do
        let i17 ← Zig.callM (mem_absorbSentinel__anon_7342b53a30ed p1)
        let i18 ← pure (i17)
        match ← ((do
          let i20 ← Zig.callR (math_mul__anon_44faaf286c79 (1 : BitVec 64) p2)
          let i21 ← pure (Zig.isNonErr i20)
          if i21 then (do
            let i23 ← Zig.callR (Zig.unwrapPayload i20)
            pure (.br19 i23))
          else (do
            let _i25 ← Zig.callR (Zig.unwrapErr i20)
            pure (.ret false))) : Zig.MM mem_Allocator_resize__anon_ec6bca265858Locals mem_Allocator_resize__anon_ec6bca265858Exit) with
        | .br19 v19 => (do
          let i27 ← Zig.callR (mem_Alignment_fromByteUnits (1 : BitVec 64))
          let i28 ← Zig.callM Zig.returnAddress
          match ← ((do
            let i30 ← pure ((p0).vtable)
            let i31 ← Zig.callM (Zig.ptrProject i30 (·.add 8))
            let i32 ← Zig.load (Zig.Ptr) 8 i31
            let i33 ← pure ((p0).ptr)
            let i34 ← (if i32 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callM (heap_PageAllocator_resize i33 i18 i27 v19 i28) else throw .illegal)
            pure (.br29 i34)) : Zig.MM mem_Allocator_resize__anon_ec6bca265858Locals mem_Allocator_resize__anon_ec6bca265858Exit) with
          | .br29 v29 => (do
            pure (.ret v29))
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM mem_Allocator_resize__anon_ec6bca265858Locals mem_Allocator_resize__anon_ec6bca265858Exit).run' (default : mem_Allocator_resize__anon_ec6bca265858Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] mem_Allocator_resize__anon_ec6bca265858

structure patternLocals where
  deriving Inhabited

inductive patternExit where
  | ret (v : BitVec 8)

def pattern (p0 : BitVec 64) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i1 ← pure (Zig.mulWrap p0 (31 : BitVec 64))
    let i2 ← pure (Zig.addWrap i1 (7 : BitVec 64))
    let i3 ← pure (Zig.trunc 8 i2)
    pure (.ret i3)) : Zig.M patternLocals patternExit).run' (default : patternLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] pattern

structure keptLocals where
  local1 : BitVec 64
  deriving Inhabited

inductive keptExit where
  | ret (v : Bool)
  | br13
  | br7
  | br4
  | rep5

def kept.again5 : keptExit → Bool
  | .rep5 => true
  | _ => false

def kept.loop5 (p0 : Array (BitVec 8)) (i3 : BitVec 64) : Zig.M keptLocals keptExit := do
  let i6 ← pure ((← get).local1)
  match ← ((do
    let i8 ← pure (i6)
    let i9 ← pure (i3)
    let i10 ← pure (Zig.lt false i8 i9)
    if i10 then (do
      let i12 ← Zig.call (Zig.index p0 i6)
      match ← ((do
        let i14 ← Zig.call (pattern i6)
        let i15 ← pure (i12 != i14)
        if i15 then (do
          pure (.ret false))
        else (do
          pure .br13)) : Zig.M keptLocals keptExit) with
      | .br13 => (do
        pure .br7)
      | e => pure e)
    else (do
      pure .br4)) : Zig.M keptLocals keptExit) with
  | .br7 => (do
    let i21 ← Zig.add false i6 (1 : BitVec 64) (safe := false)
    modify (fun s => { s with local1 := i21 })
    pure .rep5)
  | e => pure e

def kept (p0 : Array (BitVec 8)) : Zig.Result (Bool) := do
  let e ← ((do
    modify (fun s => { s with local1 := (0 : BitVec 64) })
    let i3 ← pure (Zig.len p0)
    match ← ((do
      Zig.loop (kept.loop5 p0 i3) kept.again5) : Zig.M keptLocals keptExit) with
    | .br4 => (do
      pure (.ret true))
    | e => pure e) : Zig.M keptLocals keptExit).run' (default : keptLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] kept.loop5 kept

structure growLocals where
  local4 : Zig.Slice
  got : Option (Zig.Slice)
  local36 : Zig.Slice
  r : BitVec 64
  deriving Inhabited

inductive growExit where
  | ret (v : BitVec 64)
  | br14
  | br20 (v : Option (Zig.Slice))
  | br41
  | br65
  | br54
  | br83
  | br95
  | br90
  | br31
  | br112 (v : BitVec 64)
  | br122

def grow (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) (p3 : BitVec 8) : Zig.ConcM Tgt (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with local4 := p1 })
    let i8 ← pure (((← get).local4).ptr)
    let i9 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i8)))
    let i11 ← pure (((← get).local4).len)
    modify (fun s => { s with got := none })
    match ← ((do
      let i15 ← pure (p3 == (0 : BitVec 8))
      if i15 then (do
        let i17 ← Zig.callMC (mem_Allocator_remap__anon_e29e4a94db2b p0 p1 p2)
        modify (fun s => { s with got := i17 })
        pure .br14)
      else (do
        match ← ((do
          let i21 ← Zig.callC (mem_Allocator_realloc__anon_af0c43114565 p0 p1 p2)
          let i22 ← pure (Zig.isNonErr i21)
          if i22 then (do
            let i24 ← Zig.callRC (Zig.unwrapPayload i21)
            let i25 ← pure (some i24)
            pure (.br20 i25))
          else (do
            let _i27 ← Zig.callRC (Zig.unwrapErr i21)
            pure (.br20 none))) : Zig.CM Tgt growLocals growExit) with
        | .br20 v20 => (do
          modify (fun s => { s with got := v20 })
          pure .br14)
        | e => pure e)) : Zig.CM Tgt growLocals growExit) with
    | .br14 => (do
      match ← ((do
        let i32 ← pure ((← get).got)
        let i33 ← pure ((i32).isSome)
        if i33 then (do
          let i35 ← Zig.optPayload i32
          modify (fun s => { s with local36 := i35 })
          modify (fun s => { s with r := (1 : BitVec 64) })
          match ← ((do
            let i43 ← pure (((← get).local36).ptr)
            let i44 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i43)))
            let i45 ← pure (i44)
            let i46 ← pure (i9)
            let i47 ← pure (i45 != i46)
            if i47 then (do
              let i49 ← pure ((← get).r)
              let i50 ← pure (i49 ||| (2 : BitVec 64))
              modify (fun s => { s with r := i50 })
              pure .br41)
            else (do
              pure .br41)) : Zig.CM Tgt growLocals growExit) with
          | .br41 => (do
            match ← ((do
              let i55 ← pure (i11)
              let i56 ← pure (p2)
              let i57 ← pure (Zig.min false i55 i56)
              let i58 ← pure ((← get).local36)
              let i59 ← pure i58.ptr
              let i60 ← pure i59
              let i61 ← pure (i57)
              let i62 ← Zig.sub false i61 (0 : BitVec 64) (safe := false)
              let i63 ← pure i58.len
              let i64 ← pure (Zig.le false i61 i63)
              match ← ((do
                if i64 then (do
                  pure .br65)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt growLocals growExit) with
              | .br65 => (do
                let i70 ← Zig.callMC (Zig.checkSliceEnd i58.len (0 : BitVec 64) i62 0 >>= fun _ => pure (⟨i60, i62⟩ : Zig.Slice))
                let i71 ← pure (i70)
                let i72 ← Zig.callRC (kept (← Zig.callMC (Zig.readSlice (BitVec 8) 1 i71)))
                if i72 then (do
                  let i74 ← pure ((← get).r)
                  let i75 ← pure (i74 ||| (4 : BitVec 64))
                  modify (fun s => { s with r := i75 })
                  pure .br54)
                else (do
                  pure .br54))
              | e => pure e) : Zig.CM Tgt growLocals growExit) with
            | .br54 => (do
              let i79 ← Zig.sub false p2 (1 : BitVec 64)
              let i80 ← pure ((← get).local36)
              let i81 ← pure i80.len
              let i82 ← pure (Zig.lt false i79 i81)
              match ← ((do
                if i82 then (do
                  pure .br83)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt growLocals growExit) with
              | .br83 => (do
                let i88 ← Zig.callMC (Zig.checkIndex i80.len i79) >>= fun _ => Zig.callMC (Zig.ptrProject i80.ptr (·.elem 1 i79))
                Zig.store (α := BitVec 8) 1 i88 (165 : BitVec 8)
                match ← ((do
                  let i91 ← Zig.sub false p2 (1 : BitVec 64)
                  let i92 ← pure ((← get).local36)
                  let i93 ← pure i92.len
                  let i94 ← pure (Zig.lt false i91 i93)
                  match ← ((do
                    if i94 then (do
                      pure .br95)
                    else (do
                      throw .outOfBounds)) : Zig.CM Tgt growLocals growExit) with
                  | .br95 => (do
                    let i100 ← Zig.callMC (Zig.checkIndex i92.len i91 >>= fun _ => Zig.load (BitVec 8) 1 (i92.ptr.elem 1 i91))
                    let i101 ← pure (i100 == (165 : BitVec 8))
                    if i101 then (do
                      let i103 ← pure ((← get).r)
                      let i104 ← pure (i103 ||| (8 : BitVec 64))
                      modify (fun s => { s with r := i104 })
                      pure .br90)
                    else (do
                      pure .br90))
                  | e => pure e) : Zig.CM Tgt growLocals growExit) with
                | .br90 => (do
                  let _i108 ← Zig.callMC (mem_Allocator_free__anon_1e60e7ef40f5 p0 i35)
                  let i109 ← pure ((← get).r)
                  pure (.ret i109))
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        else (do
          pure .br31)) : Zig.CM Tgt growLocals growExit) with
      | .br31 => (do
        match ← ((do
          let i113 ← pure (p1)
          let i114 ← Zig.callRC (kept (← Zig.callMC (Zig.readSlice (BitVec 8) 1 i113)))
          if i114 then (do
            pure (.br112 (4 : BitVec 64)))
          else (do
            pure (.br112 (0 : BitVec 64)))) : Zig.CM Tgt growLocals growExit) with
        | .br112 v112 => (do
          let i118 ← Zig.sub false i11 (1 : BitVec 64)
          let i119 ← pure ((← get).local4)
          let i120 ← pure i119.len
          let i121 ← pure (Zig.lt false i118 i120)
          match ← ((do
            if i121 then (do
              pure .br122)
            else (do
              throw .outOfBounds)) : Zig.CM Tgt growLocals growExit) with
          | .br122 => (do
            let i127 ← Zig.callMC (Zig.checkIndex i119.len i118) >>= fun _ => Zig.callMC (Zig.ptrProject i119.ptr (·.elem 1 i118))
            Zig.store (α := BitVec 8) 1 i127 (165 : BitVec 8)
            let _i129 ← Zig.callMC (mem_Allocator_free__anon_1e60e7ef40f5 p0 p1)
            pure (.ret v112))
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt growLocals growExit).run' (default : growLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] grow

structure page_createLocals where
  deriving Inhabited

inductive page_createExit where
  | ret (v : BitVec 32)
  | br1 (v : Zig.Ptr)

def page_create (p0 : BitVec 32) : Zig.ConcM Tgt (BitVec 32) := do
  let e ← ((do
    match ← ((do
      let i2 ← Zig.callC (mem_Allocator_create__anon_8f6a81b88324 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator))
      let i3 ← pure (Zig.isNonErr i2)
      if i3 then (do
        let i5 ← Zig.callRC (Zig.unwrapPayload i2)
        pure (.br1 i5))
      else (do
        let _i7 ← Zig.callRC (Zig.unwrapErr i2)
        pure (.ret (0 : BitVec 32)))) : Zig.CM Tgt page_createLocals page_createExit) with
    | .br1 v1 => (do
      Zig.store (α := BitVec 32) 4 v1 p0
      let i10 ← Zig.load (BitVec 32) 4 v1
      let _i11 ← Zig.callMC (mem_Allocator_destroy__anon_7fa4accb9a56 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) v1)
      pure (.ret i10))
    | e => pure e) : Zig.CM Tgt page_createLocals page_createExit).run' (default : page_createLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] page_create

structure page_growLocals where
  s : Zig.Slice
  local43 : BitVec 64
  deriving Inhabited

inductive page_growExit where
  | ret (v : BitVec 64)
  | br5 (v : Zig.Slice)
  | br19
  | br34
  | br14
  | br50
  | br47
  | rep48

def page_grow.again48 : page_growExit → Bool
  | .rep48 => true
  | _ => false

def page_grow.loop48 (i45 : Zig.Slice) (i46 : BitVec 64) : Zig.CM Tgt page_growLocals page_growExit := do
  Zig.callMC Zig.tick
  let i49 ← pure ((← get).local43)
  match ← ((do
    let i51 ← pure (i49)
    let i52 ← pure (i46)
    let i53 ← pure (Zig.lt false i51 i52)
    if i53 then (do
      let i55 ← Zig.callMC (Zig.checkIndex i45.len i49) >>= fun _ => Zig.callMC (Zig.ptrProject i45.ptr (·.elem 1 i49))
      let i56 ← Zig.callRC (pattern i49)
      Zig.store (α := BitVec 8) 1 i55 i56
      pure .br50)
    else (do
      pure .br47)) : Zig.CM Tgt page_growLocals page_growExit) with
  | .br50 => (do
    let i60 ← Zig.add false i49 (1 : BitVec 64) (safe := false)
    modify (fun s => { s with local43 := i60 })
    pure .rep48)
  | e => pure e

def page_grow (p0 : BitVec 64) (p1 : BitVec 64) (p2 : BitVec 64) (p3 : BitVec 8) : Zig.ConcM Tgt (BitVec 64) := do
  let e ← ((do
    match ← ((do
      let i6 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) p0)
      let i7 ← pure (Zig.isNonErr i6)
      if i7 then (do
        let i9 ← Zig.callRC (Zig.unwrapPayload i6)
        pure (.br5 i9))
      else (do
        let _i11 ← Zig.callRC (Zig.unwrapErr i6)
        pure (.ret (32 : BitVec 64)))) : Zig.CM Tgt page_growLocals page_growExit) with
    | .br5 v5 => (do
      modify (fun s => { s with s := v5 })
      match ← ((do
        let i15 ← pure (p1)
        let i16 ← pure (p0)
        let i17 ← pure (Zig.lt false i15 i16)
        if i17 then (do
          match ← ((do
            let i20 ← pure ((← get).s)
            let i21 ← Zig.callMC (mem_Allocator_resize__anon_ec6bca265858 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) i20 p1)
            let i22 ← pure (!i21)
            if i22 then (do
              let i24 ← pure ((← get).s)
              let _i25 ← Zig.callMC (mem_Allocator_free__anon_1e60e7ef40f5 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) i24)
              pure (.ret (64 : BitVec 64)))
            else (do
              pure .br19)) : Zig.CM Tgt page_growLocals page_growExit) with
          | .br19 => (do
            let i28 ← pure ((← get).s)
            let i29 ← pure i28.ptr
            let i30 ← pure i29
            let i31 ← Zig.sub false p1 (0 : BitVec 64) (safe := false)
            let i32 ← pure i28.len
            let i33 ← pure (Zig.le false p1 i32)
            match ← ((do
              if i33 then (do
                pure .br34)
              else (do
                throw .outOfBounds)) : Zig.CM Tgt page_growLocals page_growExit) with
            | .br34 => (do
              let i39 ← Zig.callMC (Zig.checkSliceEnd i28.len (0 : BitVec 64) i31 0 >>= fun _ => pure (⟨i30, i31⟩ : Zig.Slice))
              modify (fun s => { s with s := i39 })
              pure .br14)
            | e => pure e)
          | e => pure e)
        else (do
          pure .br14)) : Zig.CM Tgt page_growLocals page_growExit) with
      | .br14 => (do
        modify (fun s => { s with local43 := (0 : BitVec 64) })
        let i45 ← pure ((← get).s)
        let i46 ← pure i45.len
        match ← ((do
          Zig.loop (page_grow.loop48 i45 i46) page_grow.again48) : Zig.CM Tgt page_growLocals page_growExit) with
        | .br47 => (do
          let i63 ← pure ((← get).s)
          let i64 ← Zig.callC (grow ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) i63 p2 p3)
          pure (.ret i64))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt page_growLocals page_growExit).run' (default : page_growLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] page_grow.loop48 page_grow

structure page_grow_blockedLocals where
  local10 : Zig.Slice
  local22 : Zig.Slice
  lo : Zig.Slice
  hi : Zig.Slice
  local44 : BitVec 64
  r : BitVec 64
  same : Bool
  local81 : BitVec 64
  deriving Inhabited

inductive page_grow_blockedExit where
  | ret (v : BitVec 64)
  | br2 (v : Zig.Slice)
  | br13 (v : Zig.Slice)
  | br29
  | br51
  | br48
  | br94
  | br88
  | br85
  | br105
  | rep49
  | rep86

def page_grow_blocked.again86 : page_grow_blockedExit → Bool
  | .rep86 => true
  | _ => false

def page_grow_blocked.again49 : page_grow_blockedExit → Bool
  | .rep49 => true
  | _ => false

def page_grow_blocked.loop86 (i83 : Zig.Slice) (i84 : BitVec 64) : Zig.CM Tgt page_grow_blockedLocals page_grow_blockedExit := do
  Zig.callMC Zig.tick
  let i87 ← pure ((← get).local81)
  match ← ((do
    let i89 ← pure (i87)
    let i90 ← pure (i84)
    let i91 ← pure (Zig.lt false i89 i90)
    if i91 then (do
      let i93 ← Zig.callMC (Zig.checkIndex i83.len i87 >>= fun _ => Zig.load (BitVec 8) 1 (i83.ptr.elem 1 i87))
      match ← ((do
        let i95 ← pure (i93 != (90 : BitVec 8))
        if i95 then (do
          modify (fun s => { s with same := false })
          pure .br94)
        else (do
          pure .br94)) : Zig.CM Tgt page_grow_blockedLocals page_grow_blockedExit) with
      | .br94 => (do
        pure .br88)
      | e => pure e)
    else (do
      pure .br85)) : Zig.CM Tgt page_grow_blockedLocals page_grow_blockedExit) with
  | .br88 => (do
    let i102 ← Zig.add false i87 (1 : BitVec 64) (safe := false)
    modify (fun s => { s with local81 := i102 })
    pure .rep86)
  | e => pure e

def page_grow_blocked.loop49 (i46 : Zig.Slice) (i47 : BitVec 64) : Zig.CM Tgt page_grow_blockedLocals page_grow_blockedExit := do
  Zig.callMC Zig.tick
  let i50 ← pure ((← get).local44)
  match ← ((do
    let i52 ← pure (i50)
    let i53 ← pure (i47)
    let i54 ← pure (Zig.lt false i52 i53)
    if i54 then (do
      let i56 ← Zig.callMC (Zig.checkIndex i46.len i50) >>= fun _ => Zig.callMC (Zig.ptrProject i46.ptr (·.elem 1 i50))
      let i57 ← Zig.callRC (pattern i50)
      Zig.store (α := BitVec 8) 1 i56 i57
      pure .br51)
    else (do
      pure .br48)) : Zig.CM Tgt page_grow_blockedLocals page_grow_blockedExit) with
  | .br51 => (do
    let i61 ← Zig.add false i50 (1 : BitVec 64) (safe := false)
    modify (fun s => { s with local44 := i61 })
    pure .rep49)
  | e => pure e

def page_grow_blocked (p0 : BitVec 64) (p1 : BitVec 8) : Zig.ConcM Tgt (BitVec 64) := do
  let e ← ((do
    match ← ((do
      let i3 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) p0)
      let i4 ← pure (Zig.isNonErr i3)
      if i4 then (do
        let i6 ← Zig.callRC (Zig.unwrapPayload i3)
        pure (.br2 i6))
      else (do
        let _i8 ← Zig.callRC (Zig.unwrapErr i3)
        pure (.ret (32 : BitVec 64)))) : Zig.CM Tgt page_grow_blockedLocals page_grow_blockedExit) with
    | .br2 v2 => (do
      modify (fun s => { s with local10 := v2 })
      match ← ((do
        let i14 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) p0)
        let i15 ← pure (Zig.isNonErr i14)
        if i15 then (do
          let i17 ← Zig.callRC (Zig.unwrapPayload i14)
          pure (.br13 i17))
        else (do
          let _i19 ← Zig.callRC (Zig.unwrapErr i14)
          let _i20 ← Zig.callMC (mem_Allocator_free__anon_1e60e7ef40f5 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) v2)
          pure (.ret (32 : BitVec 64)))) : Zig.CM Tgt page_grow_blockedLocals page_grow_blockedExit) with
      | .br13 v13 => (do
        modify (fun s => { s with local22 := v13 })
        modify (fun s => { s with lo := v2 })
        modify (fun s => { s with hi := v13 })
        match ← ((do
          let i31 ← pure (((← get).local22).ptr)
          let i32 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i31)))
          let i34 ← pure (((← get).local10).ptr)
          let i35 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i34)))
          let i36 ← pure (i32)
          let i37 ← pure (i35)
          let i38 ← pure (Zig.lt false i36 i37)
          if i38 then (do
            modify (fun s => { s with lo := v13 })
            modify (fun s => { s with hi := v2 })
            pure .br29)
          else (do
            pure .br29)) : Zig.CM Tgt page_grow_blockedLocals page_grow_blockedExit) with
        | .br29 => (do
          modify (fun s => { s with local44 := (0 : BitVec 64) })
          let i46 ← pure ((← get).lo)
          let i47 ← pure i46.len
          match ← ((do
            Zig.loop (page_grow_blocked.loop49 i46 i47) page_grow_blocked.again49) : Zig.CM Tgt page_grow_blockedLocals page_grow_blockedExit) with
          | .br48 => (do
            let i64 ← pure ((← get).hi)
            let _i65 ← pure i64.len
            Zig.callMC (Zig.memset (α := BitVec 8) 1 i64.ptr i64.len (some (90 : BitVec 8)))
            let i68 ← pure ((← get).lo)
            let i70 ← pure (((← get).hi).ptr)
            let i71 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i70)))
            let i73 ← pure (((← get).lo).ptr)
            let i74 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i73)))
            let i75 ← Zig.sub false i71 i74
            let i76 ← Zig.add false i75 (1 : BitVec 64)
            let i77 ← Zig.callC (grow ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) i68 i76 p1)
            modify (fun s => { s with r := i77 })
            modify (fun s => { s with same := true })
            modify (fun s => { s with local81 := (0 : BitVec 64) })
            let i83 ← pure ((← get).hi)
            let i84 ← pure i83.len
            match ← ((do
              Zig.loop (page_grow_blocked.loop86 i83 i84) page_grow_blocked.again86) : Zig.CM Tgt page_grow_blockedLocals page_grow_blockedExit) with
            | .br85 => (do
              match ← ((do
                let i106 ← pure ((← get).same)
                if i106 then (do
                  let i108 ← pure ((← get).r)
                  let i109 ← pure (i108 ||| (16 : BitVec 64))
                  modify (fun s => { s with r := i109 })
                  pure .br105)
                else (do
                  pure .br105)) : Zig.CM Tgt page_grow_blockedLocals page_grow_blockedExit) with
              | .br105 => (do
                let i113 ← pure ((← get).hi)
                let _i114 ← Zig.callMC (mem_Allocator_free__anon_1e60e7ef40f5 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) i113)
                let i115 ← pure ((← get).r)
                pure (.ret i115))
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt page_grow_blockedLocals page_grow_blockedExit).run' (default : page_grow_blockedLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] page_grow_blocked.loop86 page_grow_blocked.loop49 page_grow_blocked

structure page_grow_staleLocals where
  local10 : Zig.Slice
  local22 : Zig.Slice
  lo : Zig.Slice
  hi : Zig.Slice
  got : Option (Zig.Slice)
  r : BitVec 64
  local90 : Zig.Slice
  deriving Inhabited

inductive page_grow_staleExit where
  | ret (v : BitVec 64)
  | br2 (v : Zig.Slice)
  | br13 (v : Zig.Slice)
  | br29
  | br47
  | br64
  | br71 (v : Option (Zig.Slice))
  | br107
  | br93
  | br85

def page_grow_stale (p0 : BitVec 64) (p1 : BitVec 8) : Zig.ConcM Tgt (BitVec 64) := do
  let e ← ((do
    match ← ((do
      let i3 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) p0)
      let i4 ← pure (Zig.isNonErr i3)
      if i4 then (do
        let i6 ← Zig.callRC (Zig.unwrapPayload i3)
        pure (.br2 i6))
      else (do
        let _i8 ← Zig.callRC (Zig.unwrapErr i3)
        pure (.ret (0 : BitVec 64)))) : Zig.CM Tgt page_grow_staleLocals page_grow_staleExit) with
    | .br2 v2 => (do
      modify (fun s => { s with local10 := v2 })
      match ← ((do
        let i14 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) p0)
        let i15 ← pure (Zig.isNonErr i14)
        if i15 then (do
          let i17 ← Zig.callRC (Zig.unwrapPayload i14)
          pure (.br13 i17))
        else (do
          let _i19 ← Zig.callRC (Zig.unwrapErr i14)
          let _i20 ← Zig.callMC (mem_Allocator_free__anon_1e60e7ef40f5 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) v2)
          pure (.ret (0 : BitVec 64)))) : Zig.CM Tgt page_grow_staleLocals page_grow_staleExit) with
      | .br13 v13 => (do
        modify (fun s => { s with local22 := v13 })
        modify (fun s => { s with lo := v2 })
        modify (fun s => { s with hi := v13 })
        match ← ((do
          let i31 ← pure (((← get).local22).ptr)
          let i32 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i31)))
          let i34 ← pure (((← get).local10).ptr)
          let i35 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i34)))
          let i36 ← pure (i32)
          let i37 ← pure (i35)
          let i38 ← pure (Zig.lt false i36 i37)
          if i38 then (do
            modify (fun s => { s with lo := v13 })
            modify (fun s => { s with hi := v2 })
            pure .br29)
          else (do
            pure .br29)) : Zig.CM Tgt page_grow_staleLocals page_grow_staleExit) with
        | .br29 => (do
          let i44 ← pure ((← get).lo)
          let i45 ← pure i44.len
          let i46 ← pure (Zig.lt false (0 : BitVec 64) i45)
          match ← ((do
            if i46 then (do
              pure .br47)
            else (do
              throw .outOfBounds)) : Zig.CM Tgt page_grow_staleLocals page_grow_staleExit) with
          | .br47 => (do
            let i52 ← Zig.callMC (Zig.checkIndex i44.len (0 : BitVec 64)) >>= fun _ => pure i44.ptr
            Zig.store (α := BitVec 8) 1 i52 (7 : BitVec 8)
            let i55 ← pure (((← get).hi).ptr)
            let i56 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i55)))
            let i58 ← pure (((← get).lo).ptr)
            let i59 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i58)))
            let i60 ← Zig.sub false i56 i59
            let i61 ← Zig.add false i60 (1 : BitVec 64)
            modify (fun s => { s with got := none })
            match ← ((do
              let i65 ← pure (p1 == (0 : BitVec 8))
              if i65 then (do
                let i67 ← pure ((← get).lo)
                let i68 ← Zig.callMC (mem_Allocator_remap__anon_e29e4a94db2b ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) i67 i61)
                modify (fun s => { s with got := i68 })
                pure .br64)
              else (do
                match ← ((do
                  let i72 ← pure ((← get).lo)
                  let i73 ← Zig.callC (mem_Allocator_realloc__anon_af0c43114565 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) i72 i61)
                  let i74 ← pure (Zig.isNonErr i73)
                  if i74 then (do
                    let i76 ← Zig.callRC (Zig.unwrapPayload i73)
                    let i77 ← pure (some i76)
                    pure (.br71 i77))
                  else (do
                    let _i79 ← Zig.callRC (Zig.unwrapErr i73)
                    pure (.br71 none))) : Zig.CM Tgt page_grow_staleLocals page_grow_staleExit) with
                | .br71 v71 => (do
                  modify (fun s => { s with got := v71 })
                  pure .br64)
                | e => pure e)) : Zig.CM Tgt page_grow_staleLocals page_grow_staleExit) with
            | .br64 => (do
              modify (fun s => { s with r := (0 : BitVec 64) })
              match ← ((do
                let i86 ← pure ((← get).got)
                let i87 ← pure ((i86).isSome)
                if i87 then (do
                  let i89 ← Zig.optPayload i86
                  modify (fun s => { s with local90 := i89 })
                  match ← ((do
                    let i95 ← pure (((← get).local90).ptr)
                    let i96 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i95)))
                    let i98 ← pure (((← get).lo).ptr)
                    let i99 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i98)))
                    let i100 ← pure (i96)
                    let i101 ← pure (i99)
                    let i102 ← pure (i100 != i101)
                    if i102 then (do
                      let i104 ← pure ((← get).lo)
                      let i105 ← pure i104.len
                      let i106 ← pure (Zig.lt false (0 : BitVec 64) i105)
                      match ← ((do
                        if i106 then (do
                          pure .br107)
                        else (do
                          throw .outOfBounds)) : Zig.CM Tgt page_grow_staleLocals page_grow_staleExit) with
                      | .br107 => (do
                        let i112 ← Zig.callMC (Zig.checkIndex i104.len (0 : BitVec 64) >>= fun _ => Zig.load (BitVec 8) 1 (i104.ptr.elem 1 (0 : BitVec 64)))
                        let i113 ← Zig.intCast false false 64 i112 (safe := false)
                        let i114 ← Zig.add false i113 (1 : BitVec 64)
                        modify (fun s => { s with r := i114 })
                        pure .br93)
                      | e => pure e)
                    else (do
                      pure .br93)) : Zig.CM Tgt page_grow_staleLocals page_grow_staleExit) with
                  | .br93 => (do
                    let _i118 ← Zig.callMC (mem_Allocator_free__anon_1e60e7ef40f5 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) i89)
                    pure .br85)
                  | e => pure e)
                else (do
                  let i120 ← pure ((← get).lo)
                  let _i121 ← Zig.callMC (mem_Allocator_free__anon_1e60e7ef40f5 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) i120)
                  pure .br85)) : Zig.CM Tgt page_grow_staleLocals page_grow_staleExit) with
              | .br85 => (do
                let i123 ← pure ((← get).hi)
                let _i124 ← Zig.callMC (mem_Allocator_free__anon_1e60e7ef40f5 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) i123)
                let i125 ← pure ((← get).r)
                pure (.ret i125))
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt page_grow_staleLocals page_grow_staleExit).run' (default : page_grow_staleLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] page_grow_stale

structure page_resizeLocals where
  local10 : Zig.Slice
  deriving Inhabited

inductive page_resizeExit where
  | ret (v : Bool)
  | br2 (v : Zig.Slice)
  | br14

def page_resize (p0 : BitVec 64) (p1 : BitVec 64) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    match ← ((do
      let i3 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) p0)
      let i4 ← pure (Zig.isNonErr i3)
      if i4 then (do
        let i6 ← Zig.callRC (Zig.unwrapPayload i3)
        pure (.br2 i6))
      else (do
        let _i8 ← Zig.callRC (Zig.unwrapErr i3)
        pure (.ret false))) : Zig.CM Tgt page_resizeLocals page_resizeExit) with
    | .br2 v2 => (do
      modify (fun s => { s with local10 := v2 })
      let i13 ← Zig.callMC (mem_Allocator_resize__anon_ec6bca265858 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) v2 p1)
      match ← ((do
        if i13 then (do
          let i17 ← pure (((← get).local10).ptr)
          let i18 ← pure i17
          let i19 ← Zig.sub false p1 (0 : BitVec 64) (safe := false)
          let i20 ← pure (⟨i18, i19⟩ : Zig.Slice)
          let _i21 ← Zig.callMC (mem_Allocator_free__anon_1e60e7ef40f5 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) i20)
          pure .br14)
        else (do
          let _i23 ← Zig.callMC (mem_Allocator_free__anon_1e60e7ef40f5 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) v2)
          pure .br14)) : Zig.CM Tgt page_resizeLocals page_resizeExit) with
      | .br14 => (do
        pure (.ret i13))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt page_resizeLocals page_resizeExit).run' (default : page_resizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] page_resize

structure page_sumLocals where
  sum : BitVec 64
  local13 : BitVec 64
  deriving Inhabited

inductive page_sumExit where
  | ret (v : BitVec 64)
  | br1 (v : Zig.Slice)
  | br19
  | br16
  | rep17

def page_sum.again17 : page_sumExit → Bool
  | .rep17 => true
  | _ => false

def page_sum.loop17 (i1 : Zig.Slice) (i15 : BitVec 64) : Zig.CM Tgt page_sumLocals page_sumExit := do
  Zig.callMC Zig.tick
  let i18 ← pure ((← get).local13)
  match ← ((do
    let i20 ← pure (i18)
    let i21 ← pure (i15)
    let i22 ← pure (Zig.lt false i20 i21)
    if i22 then (do
      let i24 ← Zig.callMC (Zig.checkIndex i1.len i18 >>= fun _ => Zig.load (BitVec 8) 1 (i1.ptr.elem 1 i18))
      let i25 ← pure ((← get).sum)
      let i26 ← Zig.intCast false false 64 i24 (safe := false)
      let i27 ← Zig.add false i25 i26
      modify (fun s => { s with sum := i27 })
      pure .br19)
    else (do
      pure .br16)) : Zig.CM Tgt page_sumLocals page_sumExit) with
  | .br19 => (do
    let i31 ← Zig.add false i18 (1 : BitVec 64) (safe := false)
    modify (fun s => { s with local13 := i31 })
    pure .rep17)
  | e => pure e

def page_sum (p0 : BitVec 64) : Zig.ConcM Tgt (BitVec 64) := do
  let e ← ((do
    match ← ((do
      let i2 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) p0)
      let i3 ← pure (Zig.isNonErr i2)
      if i3 then (do
        let i5 ← Zig.callRC (Zig.unwrapPayload i2)
        pure (.br1 i5))
      else (do
        let _i7 ← Zig.callRC (Zig.unwrapErr i2)
        pure (.ret (0 : BitVec 64)))) : Zig.CM Tgt page_sumLocals page_sumExit) with
    | .br1 v1 => (do
      let _i9 ← pure v1.len
      Zig.callMC (Zig.memset (α := BitVec 8) 1 v1.ptr v1.len (some (1 : BitVec 8)))
      modify (fun s => { s with sum := (0 : BitVec 64) })
      modify (fun s => { s with local13 := (0 : BitVec 64) })
      let i15 ← pure v1.len
      match ← ((do
        Zig.loop (page_sum.loop17 v1 i15) page_sum.again17) : Zig.CM Tgt page_sumLocals page_sumExit) with
      | .br16 => (do
        let i34 ← pure ((← get).sum)
        let _i35 ← Zig.callMC (mem_Allocator_free__anon_1e60e7ef40f5 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) v1)
        pure (.ret i34))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt page_sumLocals page_sumExit).run' (default : page_sumLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] page_sum.loop17 page_sum

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit :=
  fun t => nomatch t

attribute [zig_run] dispatch

end AllocTranslated.PageLinux