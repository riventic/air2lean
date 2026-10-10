-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace AllocArena.ArenaLinux

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
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 6 ← Zig.Enc.decode bs
    pure ⟨b⟩

structure heap_FixedBufferAllocator where
  end_index : BitVec 64
  buffer : Zig.Slice
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc heap_FixedBufferAllocator where
  size := 24
  align := 8
  encode v := Zig.Enc.fields 24 [(0, Zig.Enc.encode v.end_index), (8, Zig.Enc.encode v.buffer)]
  decode bs := do pure { end_index := ← Zig.Enc.decodeAt bs 0, buffer := ← Zig.Enc.decodeAt bs 8 }

structure heap_ArenaAllocator_State where
  used_list : Option (Zig.Ptr)
  free_list : Option (Zig.Ptr)
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc heap_ArenaAllocator_State where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.used_list), (8, Zig.Enc.encode v.free_list)]
  decode bs := do pure { used_list := ← Zig.Enc.decodeAt bs 0, free_list := ← Zig.Enc.decodeAt bs 8 }

inductive heap_ArenaAllocator_ResetModeTag where
  | free_all
  | retain_capacity
  | retain_with_limit
  deriving Repr, Inhabited, DecidableEq

def heap_ArenaAllocator_ResetModeTag.toBits : heap_ArenaAllocator_ResetModeTag → BitVec 2
  | .free_all => (0 : BitVec 2)
  | .retain_capacity => (1 : BitVec 2)
  | .retain_with_limit => (2 : BitVec 2)

def heap_ArenaAllocator_ResetModeTag.ofInt? (v : Int) : Option heap_ArenaAllocator_ResetModeTag :=
  if v = 0 then Option.some .free_all else if v = 1 then Option.some .retain_capacity else if v = 2 then Option.some .retain_with_limit else Option.none

def heap_ArenaAllocator_ResetModeTag.isNamed (_ : heap_ArenaAllocator_ResetModeTag) : Bool := true

instance : Zig.Packed heap_ArenaAllocator_ResetModeTag 2 where
  toBits := heap_ArenaAllocator_ResetModeTag.toBits
  ofBits b := (heap_ArenaAllocator_ResetModeTag.ofInt? (Zig.val false b)).getD default
  valid b := (heap_ArenaAllocator_ResetModeTag.ofInt? (Zig.val false b)).isSome

inductive heap_ArenaAllocator_ResetMode where
  | free_all
  | retain_capacity
  | retain_with_limit (v : BitVec 64)
  deriving Repr, Inhabited, DecidableEq

def heap_ArenaAllocator_ResetMode.tag : heap_ArenaAllocator_ResetMode → heap_ArenaAllocator_ResetModeTag
  | .free_all => .free_all
  | .retain_capacity => .retain_capacity
  | .retain_with_limit _ => .retain_with_limit

def heap_ArenaAllocator_ResetMode.get_free_all : heap_ArenaAllocator_ResetMode → Zig.Result (Unit)
  | .free_all => pure ()
  | _ => throw .panic

def heap_ArenaAllocator_ResetMode.modify_free_all (_g : Unit → Unit) : heap_ArenaAllocator_ResetMode → heap_ArenaAllocator_ResetMode
  | .free_all => .free_all
  | _ => .free_all

def heap_ArenaAllocator_ResetMode.setTag_free_all : heap_ArenaAllocator_ResetMode → heap_ArenaAllocator_ResetMode
  | .free_all => .free_all
  | _ => .free_all

def heap_ArenaAllocator_ResetMode.get_retain_capacity : heap_ArenaAllocator_ResetMode → Zig.Result (Unit)
  | .retain_capacity => pure ()
  | _ => throw .panic

def heap_ArenaAllocator_ResetMode.modify_retain_capacity (_g : Unit → Unit) : heap_ArenaAllocator_ResetMode → heap_ArenaAllocator_ResetMode
  | .retain_capacity => .retain_capacity
  | _ => .retain_capacity

def heap_ArenaAllocator_ResetMode.setTag_retain_capacity : heap_ArenaAllocator_ResetMode → heap_ArenaAllocator_ResetMode
  | .retain_capacity => .retain_capacity
  | _ => .retain_capacity

def heap_ArenaAllocator_ResetMode.get_retain_with_limit : heap_ArenaAllocator_ResetMode → Zig.Result (BitVec 64)
  | .retain_with_limit v => pure v
  | _ => throw .panic

def heap_ArenaAllocator_ResetMode.modify_retain_with_limit (g : BitVec 64 → BitVec 64) : heap_ArenaAllocator_ResetMode → heap_ArenaAllocator_ResetMode
  | .retain_with_limit v => .retain_with_limit (g v)
  | _ => .retain_with_limit (g default)

def heap_ArenaAllocator_ResetMode.setTag_retain_with_limit : heap_ArenaAllocator_ResetMode → heap_ArenaAllocator_ResetMode
  | .retain_with_limit v => .retain_with_limit v
  | _ => .retain_with_limit default

inductive heap_ArenaAllocator_PushResultTag where
  | success
  | failure
  deriving Repr, Inhabited, DecidableEq

def heap_ArenaAllocator_PushResultTag.toBits : heap_ArenaAllocator_PushResultTag → BitVec 1
  | .success => (0 : BitVec 1)
  | .failure => (1 : BitVec 1)

def heap_ArenaAllocator_PushResultTag.ofInt? (v : Int) : Option heap_ArenaAllocator_PushResultTag :=
  if v = 0 then Option.some .success else if v = 1 then Option.some .failure else Option.none

def heap_ArenaAllocator_PushResultTag.isNamed (_ : heap_ArenaAllocator_PushResultTag) : Bool := true

instance : Zig.Packed heap_ArenaAllocator_PushResultTag 1 where
  toBits := heap_ArenaAllocator_PushResultTag.toBits
  ofBits b := (heap_ArenaAllocator_PushResultTag.ofInt? (Zig.val false b)).getD default
  valid b := (heap_ArenaAllocator_PushResultTag.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc heap_ArenaAllocator_PushResultTag where
  size := 1
  align := 1
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 1 ← Zig.Enc.decode bs
    match heap_ArenaAllocator_PushResultTag.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

inductive heap_ArenaAllocator_PushResult where
  | success
  | failure (v : Option (Zig.Ptr))
  deriving Repr, Inhabited, DecidableEq

def heap_ArenaAllocator_PushResult.tag : heap_ArenaAllocator_PushResult → heap_ArenaAllocator_PushResultTag
  | .success => .success
  | .failure _ => .failure

def heap_ArenaAllocator_PushResult.get_success : heap_ArenaAllocator_PushResult → Zig.Result (Unit)
  | .success => pure ()
  | _ => throw .panic

def heap_ArenaAllocator_PushResult.modify_success (_g : Unit → Unit) : heap_ArenaAllocator_PushResult → heap_ArenaAllocator_PushResult
  | .success => .success
  | _ => .success

def heap_ArenaAllocator_PushResult.setTag_success : heap_ArenaAllocator_PushResult → heap_ArenaAllocator_PushResult
  | .success => .success
  | _ => .success

def heap_ArenaAllocator_PushResult.get_failure : heap_ArenaAllocator_PushResult → Zig.Result (Option (Zig.Ptr))
  | .failure v => pure v
  | _ => throw .panic

def heap_ArenaAllocator_PushResult.modify_failure (g : Option (Zig.Ptr) → Option (Zig.Ptr)) : heap_ArenaAllocator_PushResult → heap_ArenaAllocator_PushResult
  | .failure v => .failure (g v)
  | _ => .failure (g default)

def heap_ArenaAllocator_PushResult.setTag_failure : heap_ArenaAllocator_PushResult → heap_ArenaAllocator_PushResult
  | .failure v => .failure v
  | _ => .failure default

instance : Zig.Enc heap_ArenaAllocator_PushResult where
  size := 16
  align := 8
  encode v := match v with
    | .success => Zig.Enc.fields 16 [(8, Zig.Enc.encode v.tag)]
    | .failure x => Zig.Enc.fields 16 [(8, Zig.Enc.encode v.tag), (0, Zig.Enc.encode x)]
  decode bs := do
    let t : heap_ArenaAllocator_PushResultTag ← Zig.Enc.decodeAt bs 8
    match t with
    | .success => pure .success
    | .failure => pure (.failure (← Zig.Enc.decodeAt bs 0))

structure heap_ArenaAllocator_Node_Size where
  resizing : Bool
  «_» : BitVec 63
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed heap_ArenaAllocator_Node_Size 64 where
  toBits v := ((Zig.Packed.toBits v.resizing).setWidth 64 <<< 0) ||| ((Zig.Packed.toBits v.«_»).setWidth 64 <<< 1)
  ofBits b := { resizing := Zig.Packed.get b 0, «_» := Zig.Packed.get b 1 }

instance : Zig.Enc heap_ArenaAllocator_Node_Size where
  size := 8
  align := 8
  encode v := Zig.Enc.encode (Zig.Packed.toBits v)
  decode bs := do
    let b : BitVec 64 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

structure heap_ArenaAllocator_Node where
  size : heap_ArenaAllocator_Node_Size
  end_index : BitVec 64
  next : Option (Zig.Ptr)
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc heap_ArenaAllocator_Node where
  size := 24
  align := 8
  encode v := Zig.Enc.fields 24 [(0, Zig.Enc.encode v.size), (8, Zig.Enc.encode v.end_index), (16, Zig.Enc.encode v.next)]
  decode bs := do pure { size := ← Zig.Enc.decodeAt bs 0, end_index := ← Zig.Enc.decodeAt bs 8, next := ← Zig.Enc.decodeAt bs 16 }

structure heap_ArenaAllocator where
  child_allocator : mem_Allocator
  state : heap_ArenaAllocator_State
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc heap_ArenaAllocator where
  size := 32
  align := 8
  encode v := Zig.Enc.fields 32 [(0, Zig.Enc.encode v.child_allocator), (16, Zig.Enc.encode v.state)]
  decode bs := do pure { child_allocator := ← Zig.Enc.decodeAt bs 0, state := ← Zig.Enc.decodeAt bs 16 }

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals [
  -- 0: heap.PageAllocator.vtable
  (Zig.Enc.encode (({ alloc := (⟨some 2, 0⟩ : Zig.Ptr), resize := (⟨some 3, 0⟩ : Zig.Ptr), remap := (⟨some 4, 0⟩ : Zig.Ptr), free := (⟨some 5, 0⟩ : Zig.Ptr) } : mem_Allocator_VTable) : mem_Allocator_VTable), 8, .constGlobal),
  -- 1: arena.buffer
  (Array.replicate (Zig.Enc.size (Vector (BitVec 8) 4096)) .undef, 1, .global),
  -- 2: heap.PageAllocator.alloc
  (#[.undef], 1, .constGlobal),
  -- 3: heap.PageAllocator.resize
  (#[.undef], 1, .constGlobal),
  -- 4: heap.PageAllocator.remap
  (#[.undef], 1, .constGlobal),
  -- 5: heap.PageAllocator.free
  (#[.undef], 1, .constGlobal),
  -- 6: heap.ArenaAllocator.alloc
  (#[.undef], 1, .constGlobal),
  -- 7: heap.ArenaAllocator.resize
  (#[.undef], 1, .constGlobal),
  -- 8: heap.ArenaAllocator.remap
  (#[.undef], 1, .constGlobal),
  -- 9: heap.ArenaAllocator.free
  (#[.undef], 1, .constGlobal),
  -- 10: heap.FixedBufferAllocator.alloc
  (#[.undef], 1, .constGlobal),
  -- 11: heap.FixedBufferAllocator.resize
  (#[.undef], 1, .constGlobal),
  -- 12: heap.FixedBufferAllocator.remap
  (#[.undef], 1, .constGlobal),
  -- 13: heap.FixedBufferAllocator.free
  (#[.undef], 1, .constGlobal),
  -- 14: heap.PageAllocator.addr_hint
  (Zig.Enc.encode (none : Option (Zig.Ptr)), 8, .global),
  -- 15: a constant
  (Zig.Enc.encode (({ alloc := (⟨some 6, 0⟩ : Zig.Ptr), resize := (⟨some 7, 0⟩ : Zig.Ptr), remap := (⟨some 8, 0⟩ : Zig.Ptr), free := (⟨some 9, 0⟩ : Zig.Ptr) } : mem_Allocator_VTable) : mem_Allocator_VTable), 8, .constGlobal),
  -- 16: a constant
  (Zig.Enc.encode (({ alloc := (⟨some 10, 0⟩ : Zig.Ptr), resize := (⟨some 11, 0⟩ : Zig.Ptr), remap := (⟨some 12, 0⟩ : Zig.Ptr), free := (⟨some 13, 0⟩ : Zig.Ptr) } : mem_Allocator_VTable) : mem_Allocator_VTable), 8, .constGlobal)]

/-- The spawn targets of the program. -/
inductive Tgt where

structure heap_ArenaAllocator_State_promoteLocals where
  local2 : heap_ArenaAllocator
  deriving Inhabited

inductive heap_ArenaAllocator_State_promoteExit where
  | ret (v : heap_ArenaAllocator)

def heap_ArenaAllocator_State_promote (p0 : heap_ArenaAllocator_State) (p1 : mem_Allocator) : Zig.MemM (heap_ArenaAllocator) := do
  let e ← ((do
    modify (fun s => { s with local2 := { s.local2 with child_allocator := p1 } })
    modify (fun s => { s with local2 := { s.local2 with state := p0 } })
    pure (.ret (← get).local2)) : Zig.MM heap_ArenaAllocator_State_promoteLocals heap_ArenaAllocator_State_promoteExit).run' (default : heap_ArenaAllocator_State_promoteLocals)
  match e with
  | .ret v => pure v

structure heap_ArenaAllocator_initLocals where
  deriving Inhabited

inductive heap_ArenaAllocator_initExit where
  | ret (v : heap_ArenaAllocator)

def heap_ArenaAllocator_init (p0 : mem_Allocator) : Zig.MemM (heap_ArenaAllocator) := do
  let e ← ((do
    let i1 ← Zig.callM (heap_ArenaAllocator_State_promote ({ used_list := none, free_list := none } : heap_ArenaAllocator_State) p0)
    pure (.ret i1)) : Zig.MM heap_ArenaAllocator_initLocals heap_ArenaAllocator_initExit).run' (default : heap_ArenaAllocator_initLocals)
  match e with
  | .ret v => pure v

structure heap_ArenaAllocator_allocatorLocals where
  local1 : mem_Allocator
  deriving Inhabited

inductive heap_ArenaAllocator_allocatorExit where
  | ret (v : mem_Allocator)

def heap_ArenaAllocator_allocator (p0 : Zig.Ptr) : Zig.MemM (mem_Allocator) := do
  let e ← ((do
    let i3 ← pure (p0)
    modify (fun s => { s with local1 := { s.local1 with ptr := i3 } })
    modify (fun s => { s with local1 := { s.local1 with vtable := (⟨some 15, 0⟩ : Zig.Ptr) } })
    pure (.ret (← get).local1)) : Zig.MM heap_ArenaAllocator_allocatorLocals heap_ArenaAllocator_allocatorExit).run' (default : heap_ArenaAllocator_allocatorLocals)
  match e with
  | .ret v => pure v

structure mem_absorbSentinel__anon_1Locals where
  deriving Inhabited

inductive mem_absorbSentinel__anon_1Exit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_1 (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret p0)) : Zig.MM mem_absorbSentinel__anon_1Locals mem_absorbSentinel__anon_1Exit).run' (default : mem_absorbSentinel__anon_1Locals)
  match e with
  | .ret v => pure v

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

structure math_isPowerOfTwo__anon_1Locals where
  deriving Inhabited

inductive math_isPowerOfTwo__anon_1Exit where
  | ret (v : Bool)

def math_isPowerOfTwo__anon_1 (p0 : BitVec 64) : Zig.Result (Bool) := do
  let e ← ((do
    let i1 ← pure (p0)
    let i2 ← pure (Zig.gt false i1 (0 : BitVec 64))
    let _i3 ← Zig.call (debug_assert i2)
    let i4 ← Zig.sub false p0 (1 : BitVec 64)
    let i5 ← pure (p0 &&& i4)
    let i6 ← pure (i5)
    let i7 ← pure (i6 == (0 : BitVec 64))
    pure (.ret i7)) : Zig.M math_isPowerOfTwo__anon_1Locals math_isPowerOfTwo__anon_1Exit).run' (default : math_isPowerOfTwo__anon_1Locals)
  match e with
  | .ret v => pure v

structure mem_Alignment_fromByteUnitsLocals where
  deriving Inhabited

inductive mem_Alignment_fromByteUnitsExit where
  | ret (v : mem_Alignment)

def mem_Alignment_fromByteUnits (p0 : BitVec 64) : Zig.Result (mem_Alignment) := do
  let e ← ((do
    let i1 ← Zig.call (math_isPowerOfTwo__anon_1 p0)
    let _i2 ← Zig.call (debug_assert i1)
    let i3 ← pure (Zig.ctz 7 p0)
    let i4 ← Zig.enumOf (mem_Alignment.ofInt? (Zig.val false i3))
    pure (.ret i4)) : Zig.M mem_Alignment_fromByteUnitsLocals mem_Alignment_fromByteUnitsExit).run' (default : mem_Alignment_fromByteUnitsLocals)
  match e with
  | .ret v => pure v

structure mem_isValidAlignGeneric__anon_1Locals where
  deriving Inhabited

inductive mem_isValidAlignGeneric__anon_1Exit where
  | ret (v : Bool)
  | br3 (v : Bool)

def mem_isValidAlignGeneric__anon_1 (p0 : BitVec 64) : Zig.Result (Bool) := do
  let e ← ((do
    let i1 ← pure (p0)
    let i2 ← pure (Zig.gt false i1 (0 : BitVec 64))
    match ← ((do
      if i2 then (do
        let i5 ← Zig.call (math_isPowerOfTwo__anon_1 p0)
        pure (.br3 i5))
      else (do
        pure (.br3 false))) : Zig.M mem_isValidAlignGeneric__anon_1Locals mem_isValidAlignGeneric__anon_1Exit) with
    | .br3 v3 => (do
      pure (.ret v3))
    | e => pure e) : Zig.M mem_isValidAlignGeneric__anon_1Locals mem_isValidAlignGeneric__anon_1Exit).run' (default : mem_isValidAlignGeneric__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_alignBackward__anon_1Locals where
  deriving Inhabited

inductive mem_alignBackward__anon_1Exit where
  | ret (v : BitVec 64)

def mem_alignBackward__anon_1 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← Zig.call (mem_isValidAlignGeneric__anon_1 p1)
    let _i3 ← Zig.call (debug_assert i2)
    let i4 ← Zig.sub false p1 (1 : BitVec 64)
    let i5 ← pure (~~~i4)
    let i6 ← pure (p0 &&& i5)
    pure (.ret i6)) : Zig.M mem_alignBackward__anon_1Locals mem_alignBackward__anon_1Exit).run' (default : mem_alignBackward__anon_1Locals)
  match e with
  | .ret v => pure v

structure mem_alignForward__anon_1Locals where
  deriving Inhabited

inductive mem_alignForward__anon_1Exit where
  | ret (v : BitVec 64)

def mem_alignForward__anon_1 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← Zig.call (mem_isValidAlignGeneric__anon_1 p1)
    let _i3 ← Zig.call (debug_assert i2)
    let i4 ← Zig.sub false p1 (1 : BitVec 64)
    let i5 ← Zig.add false p0 i4
    let i6 ← Zig.call (mem_alignBackward__anon_1 i5 p1)
    pure (.ret i6)) : Zig.M mem_alignForward__anon_1Locals mem_alignForward__anon_1Exit).run' (default : mem_alignForward__anon_1Locals)
  match e with
  | .ret v => pure v

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
        let i9 ← Zig.callR (mem_alignForward__anon_1 i6 (4096 : BitVec 64))
        let i11 ← pure (((← get).local1).ptr)
        let i12 ← pure (i11.elem 1 (0 : BitVec 64))
        let i13 ← Zig.sub false i9 (0 : BitVec 64)
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
      let i16 ← pure (p1)
      let _i17 ← Zig.callM (heap_PageAllocator_unmap i16)
      pure .ret)
    | e => pure e) : Zig.MM heap_PageAllocator_freeLocals heap_PageAllocator_freeExit).run' (default : heap_PageAllocator_freeLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure heap_ArenaAllocator_loadFirstNodeLocals where
  deriving Inhabited

inductive heap_ArenaAllocator_loadFirstNodeExit where
  | ret (v : Option (Zig.Ptr))

def heap_ArenaAllocator_loadFirstNode (p0 : Zig.Ptr) : Zig.ConcM Tgt (Option (Zig.Ptr)) := do
  let e ← ((do
    let i1 ← pure (p0.add 16)
    let i2 ← pure (i1.add 0)
    let i3 ← pure (i2)
    let i4 ← Zig.atomicLoadPtrC (Option (Zig.Ptr)) Zig.AtomicOrder.acquire 8 i3
    pure (.ret i4)) : Zig.CM Tgt heap_ArenaAllocator_loadFirstNodeLocals heap_ArenaAllocator_loadFirstNodeExit).run' (default : heap_ArenaAllocator_loadFirstNodeLocals)
  match e with
  | .ret v => pure v

structure heap_ArenaAllocator_freeLocals where
  local4 : Zig.Slice
  deriving Inhabited

inductive heap_ArenaAllocator_freeExit where
  | ret
  | br10
  | br23
  | br34

def heap_ArenaAllocator_free (p0 : Zig.Ptr) (p1 : Zig.Slice) (p2 : mem_Alignment) (p3 : BitVec 64) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    modify (fun s => { s with local4 := p1 })
    let i7 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
    let i8 ← pure (i7 &&& (7 : BitVec 64))
    let i9 ← pure (i8 == (0 : BitVec 64))
    match ← ((do
      if i9 then (do
        pure .br10)
      else (do
        throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_freeLocals heap_ArenaAllocator_freeExit) with
    | .br10 => (do
      let i15 ← pure (p0)
      let i17 ← pure (((← get).local4).len)
      let i18 ← pure (i17)
      let i19 ← pure (Zig.gt false i18 (0 : BitVec 64))
      let _i20 ← Zig.callRC (debug_assert i19)
      let i21 ← Zig.callC (heap_ArenaAllocator_loadFirstNode i15)
      let i22 ← pure ((i21).isSome)
      match ← ((do
        if i22 then (do
          pure .br23)
        else (do
          throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_freeLocals heap_ArenaAllocator_freeExit) with
      | .br23 => (do
        let i28 ← Zig.optPayload i21
        let i29 ← pure (i28)
        let i30 ← pure (i29.elem 1 (24 : BitVec 64))
        let i31 ← pure (i28.add 8)
        let i32 ← pure (i31)
        let i33 ← Zig.atomicLoadC (n := 64) Zig.AtomicOrder.relaxed 8 i32
        match ← ((do
          let i35 ← pure (i30.elem 1 i33)
          let i37 ← pure (((← get).local4).ptr)
          let i39 ← pure (((← get).local4).len)
          let i40 ← pure (i37.elem 1 i39)
          let i41 ← pure (i35 != i40)
          if i41 then (do
            pure .ret)
          else (do
            pure .br34)) : Zig.CM Tgt heap_ArenaAllocator_freeLocals heap_ArenaAllocator_freeExit) with
        | .br34 => (do
          let i46 ← pure (((← get).local4).len)
          let i47 ← Zig.sub false i33 i46
          let i48 ← pure (i30.elem 1 i47)
          let i50 ← pure (((← get).local4).ptr)
          let i51 ← pure (i48 == i50)
          let _i52 ← Zig.callRC (debug_assert i51)
          let i53 ← pure (i28.add 8)
          let _i54 ← Zig.cmpxchgC Zig.AtomicOrder.release Zig.AtomicOrder.relaxed 8 i53 i33 i47
          pure .ret)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_freeLocals heap_ArenaAllocator_freeExit).run' (default : heap_ArenaAllocator_freeLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure heap_FixedBufferAllocator_sliceContainsSliceLocals where
  local2 : Zig.Slice
  local5 : Zig.Slice
  deriving Inhabited

inductive heap_FixedBufferAllocator_sliceContainsSliceExit where
  | ret (v : Bool)
  | br17 (v : Bool)

def heap_FixedBufferAllocator_sliceContainsSlice (p0 : Zig.Slice) (p1 : Zig.Slice) : Zig.MemM (Bool) := do
  let e ← ((do
    modify (fun s => { s with local2 := p0 })
    modify (fun s => { s with local5 := p1 })
    let i9 ← pure (((← get).local5).ptr)
    let i10 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i9)))
    let i12 ← pure (((← get).local2).ptr)
    let i13 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i12)))
    let i14 ← pure (i10)
    let i15 ← pure (i13)
    let i16 ← pure (Zig.ge false i14 i15)
    match ← ((do
      if i16 then (do
        let i20 ← pure (((← get).local5).ptr)
        let i21 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i20)))
        let i23 ← pure (((← get).local5).len)
        let i24 ← Zig.add false i21 i23
        let i26 ← pure (((← get).local2).ptr)
        let i27 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i26)))
        let i29 ← pure (((← get).local2).len)
        let i30 ← Zig.add false i27 i29
        let i31 ← pure (i24)
        let i32 ← pure (i30)
        let i33 ← pure (Zig.le false i31 i32)
        pure (.br17 i33))
      else (do
        pure (.br17 false))) : Zig.MM heap_FixedBufferAllocator_sliceContainsSliceLocals heap_FixedBufferAllocator_sliceContainsSliceExit) with
    | .br17 v17 => (do
      pure (.ret v17))
    | e => pure e) : Zig.MM heap_FixedBufferAllocator_sliceContainsSliceLocals heap_FixedBufferAllocator_sliceContainsSliceExit).run' (default : heap_FixedBufferAllocator_sliceContainsSliceLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heap_FixedBufferAllocator_ownsSliceLocals where
  deriving Inhabited

inductive heap_FixedBufferAllocator_ownsSliceExit where
  | ret (v : Bool)

def heap_FixedBufferAllocator_ownsSlice (p0 : Zig.Ptr) (p1 : Zig.Slice) : Zig.MemM (Bool) := do
  let e ← ((do
    let i2 ← pure (p0.add 8)
    let i3 ← Zig.load (Zig.Slice) 8 i2
    let i4 ← Zig.callM (heap_FixedBufferAllocator_sliceContainsSlice i3 p1)
    pure (.ret i4)) : Zig.MM heap_FixedBufferAllocator_ownsSliceLocals heap_FixedBufferAllocator_ownsSliceExit).run' (default : heap_FixedBufferAllocator_ownsSliceLocals)
  match e with
  | .ret v => pure v

structure heap_FixedBufferAllocator_isLastAllocationLocals where
  local2 : Zig.Slice
  deriving Inhabited

inductive heap_FixedBufferAllocator_isLastAllocationExit where
  | ret (v : Bool)

def heap_FixedBufferAllocator_isLastAllocation (p0 : Zig.Ptr) (p1 : Zig.Slice) : Zig.MemM (Bool) := do
  let e ← ((do
    modify (fun s => { s with local2 := p1 })
    let i6 ← pure (((← get).local2).ptr)
    let i8 ← pure (((← get).local2).len)
    let i9 ← pure (i6.elem 1 i8)
    let i10 ← pure (p0.add 8)
    let i11 ← pure (i10.add 0)
    let i12 ← Zig.load (Zig.Ptr) 8 i11
    let i13 ← pure (p0.add 0)
    let i14 ← Zig.load (BitVec 64) 8 i13
    let i15 ← pure (i12.elem 1 i14)
    let i16 ← pure (i9 == i15)
    pure (.ret i16)) : Zig.MM heap_FixedBufferAllocator_isLastAllocationLocals heap_FixedBufferAllocator_isLastAllocationExit).run' (default : heap_FixedBufferAllocator_isLastAllocationLocals)
  match e with
  | .ret v => pure v

structure heap_FixedBufferAllocator_freeLocals where
  deriving Inhabited

inductive heap_FixedBufferAllocator_freeExit where
  | ret
  | br7
  | br15

def heap_FixedBufferAllocator_free (p0 : Zig.Ptr) (p1 : Zig.Slice) (p2 : mem_Alignment) (p3 : BitVec 64) : Zig.MemM (Unit) := do
  let e ← ((do
    let i4 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
    let i5 ← pure (i4 &&& (7 : BitVec 64))
    let i6 ← pure (i5 == (0 : BitVec 64))
    match ← ((do
      if i6 then (do
        pure .br7)
      else (do
        throw .panic)) : Zig.MM heap_FixedBufferAllocator_freeLocals heap_FixedBufferAllocator_freeExit) with
    | .br7 => (do
      let i12 ← pure (p0)
      let i13 ← Zig.callM (heap_FixedBufferAllocator_ownsSlice i12 p1)
      let _i14 ← Zig.callR (debug_assert i13)
      match ← ((do
        let i16 ← Zig.callM (heap_FixedBufferAllocator_isLastAllocation i12 p1)
        if i16 then (do
          let i18 ← pure (i12.add 0)
          let i19 ← Zig.load (BitVec 64) 8 i18
          let i20 ← pure p1.len
          let i21 ← Zig.sub false i19 i20
          Zig.store (α := BitVec 64) 8 i18 i21
          pure .br15)
        else (do
          pure .br15)) : Zig.MM heap_FixedBufferAllocator_freeLocals heap_FixedBufferAllocator_freeExit) with
      | .br15 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.MM heap_FixedBufferAllocator_freeLocals heap_FixedBufferAllocator_freeExit).run' (default : heap_FixedBufferAllocator_freeLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure mem_Allocator_free__anon_1Locals where
  deriving Inhabited

inductive mem_Allocator_free__anon_1Exit where
  | ret
  | br4
  | br15

def mem_Allocator_free__anon_1 (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_1 p1)
    let i3 ← pure (i2)
    match ← ((do
      let i5 ← pure i3.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        pure .ret)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_free__anon_1Locals mem_Allocator_free__anon_1Exit) with
    | .br4 => (do
      let _i11 ← pure i3.len
      Zig.callMC (Zig.memset (α := BitVec 8) 1 i3.ptr i3.len none)
      let i13 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
      let i14 ← Zig.callMC Zig.returnAddress
      match ← ((do
        let i16 ← pure ((p0).vtable)
        let i17 ← pure (i16.add 24)
        let i18 ← Zig.load (Zig.Ptr) 8 i17
        let i19 ← pure ((p0).ptr)
        let _i20 ← (if i18 == (⟨some 5, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_free i19 i3 i13 i14) else if i18 == (⟨some 9, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_free i19 i3 i13 i14) else if i18 == (⟨some 13, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_free i19 i3 i13 i14) else throw .illegal)
        pure .br15) : Zig.CM Tgt mem_Allocator_free__anon_1Locals mem_Allocator_free__anon_1Exit) with
      | .br15 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_1Locals mem_Allocator_free__anon_1Exit).run' (default : mem_Allocator_free__anon_1Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure arena_foreign_freeLocals where
  arena : Zig.Ptr
  deriving Inhabited

inductive arena_foreign_freeExit where
  | ret

def arena_foreign_free  : Zig.ConcM Tgt (Unit) := do
  let s0 ← Zig.allocStack 32 8
  let e ← ((do
    let i0 ← pure (← get).arena
    let i1 ← Zig.callMC (heap_ArenaAllocator_init ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 0, 0⟩ : Zig.Ptr) } : mem_Allocator))
    Zig.store (α := heap_ArenaAllocator) 8 i0 i1
    let i3 ← Zig.callMC (heap_ArenaAllocator_allocator i0)
    let _i4 ← Zig.callC (mem_Allocator_free__anon_1 i3 (⟨(⟨some 1, 0⟩ : Zig.Ptr), (8 : BitVec 64)⟩ : Zig.Slice))
    pure .ret) : Zig.CM Tgt arena_foreign_freeLocals arena_foreign_freeExit).run' { (default : arena_foreign_freeLocals) with arena := s0 }
  Zig.free s0
  match e with
  | .ret => pure ()

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

structure mem_isValidAlignLocals where
  deriving Inhabited

inductive mem_isValidAlignExit where
  | ret (v : Bool)

def mem_isValidAlign (p0 : BitVec 64) : Zig.Result (Bool) := do
  let e ← ((do
    let i1 ← Zig.call (mem_isValidAlignGeneric__anon_1 p0)
    pure (.ret i1)) : Zig.M mem_isValidAlignLocals mem_isValidAlignExit).run' (default : mem_isValidAlignLocals)
  match e with
  | .ret v => pure v

structure mem_alignPointerOffset__anon_2Locals where
  ov : BitVec 64 × BitVec 1
  deriving Inhabited

inductive mem_alignPointerOffset__anon_2Exit where
  | ret (v : Option (BitVec 64))
  | br4
  | br15
  | br31

def mem_alignPointerOffset__anon_2 (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (Option (BitVec 64)) := do
  let e ← ((do
    let i2 ← Zig.callR (mem_isValidAlign p1)
    let _i3 ← Zig.callR (debug_assert i2)
    match ← ((do
      let i5 ← pure (p1)
      let i6 ← pure (Zig.le false i5 (4096 : BitVec 64))
      if i6 then (do
        pure (.ret (some (0 : BitVec 64))))
      else (do
        pure .br4)) : Zig.MM mem_alignPointerOffset__anon_2Locals mem_alignPointerOffset__anon_2Exit) with
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
          pure .br15)) : Zig.MM mem_alignPointerOffset__anon_2Locals mem_alignPointerOffset__anon_2Exit) with
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
            pure .br31)) : Zig.MM mem_alignPointerOffset__anon_2Locals mem_alignPointerOffset__anon_2Exit) with
        | .br31 => (do
          let i38 ← Zig.divTrunc false i30 (1 : BitVec 64)
          let i39 ← pure (some i38)
          pure (.ret i39))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM mem_alignPointerOffset__anon_2Locals mem_alignPointerOffset__anon_2Exit).run' (default : mem_alignPointerOffset__anon_2Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_alignPointer__anon_1Locals where
  deriving Inhabited

inductive mem_alignPointer__anon_1Exit where
  | ret (v : Option (Zig.Ptr))
  | br2 (v : BitVec 64)
  | br13

def mem_alignPointer__anon_1 (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i3 ← Zig.callM (mem_alignPointerOffset__anon_2 p0 p1)
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        pure (.br2 i6))
      else (do
        pure (.ret none))) : Zig.MM mem_alignPointer__anon_1Locals mem_alignPointer__anon_1Exit) with
    | .br2 v2 => (do
      let i9 ← pure (p0.elem 1 v2)
      let i10 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i9)))
      let i11 ← pure (i10 &&& (4095 : BitVec 64))
      let i12 ← pure (i11 == (0 : BitVec 64))
      match ← ((do
        if i12 then (do
          pure .br13)
        else (do
          throw .panic)) : Zig.MM mem_alignPointer__anon_1Locals mem_alignPointer__anon_1Exit) with
      | .br13 => (do
        let i18 ← pure (i9)
        pure (.ret i18))
      | e => pure e)
    | e => pure e) : Zig.MM mem_alignPointer__anon_1Locals mem_alignPointer__anon_1Exit).run' (default : mem_alignPointer__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

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
        let i11 ← Zig.callRC (mem_alignForward__anon_1 p0 (4096 : BitVec 64))
        let i12 ← pure (Zig.subSat false i10 (4096 : BitVec 64))
        let i13 ← Zig.add false i11 i12
        match ← ((do
          let i17 ← Zig.atomicLoadUnorderedEncC (Option (Zig.Ptr)) 8 (⟨some 14, 0⟩ : Zig.Ptr)
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
              let i38 ← Zig.callMC (Zig.optPtrFromAddr (i30).toNat)
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
            let i58 ← Zig.callMC (mem_alignPointer__anon_1 i57 i10)
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
                  let i78 ← pure (i77.elem 1 (0 : BitVec 64))
                  let i79 ← Zig.sub false i71 (0 : BitVec 64)
                  let i80 ← pure i76.len
                  let i81 ← pure (Zig.le false i71 i80)
                  match ← ((do
                    if i81 then (do
                      pure .br82)
                    else (do
                      throw .outOfBounds)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
                  | .br82 => (do
                    let i87 ← pure (⟨i78, i79⟩ : Zig.Slice)
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
                    let i98 ← pure (i65.elem 1 i11)
                    let i99 ← pure (Zig.le false i11 i92)
                    match ← ((do
                      if i99 then (do
                        pure .br100)
                      else (do
                        throw .outOfBounds)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
                    | .br100 => (do
                      let i105 ← Zig.sub false i92 i11
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
                        let i119 ← pure (i106)
                        let _i120 ← Zig.callMC (Zig.Os.munmap Zig.Os.Target.linux i119)
                        pure .br93)
                      | e => pure e)
                    | e => pure e)
                  else (do
                    pure .br93)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
                | .br93 => (do
                  match ← ((do
                    let i124 ← pure (i65.elem 1 (0 : BitVec 64))
                    let i125 ← pure ((← get).local14)
                    let i126 ← pure (i124)
                    let _i127 ← Zig.cmpxchgPtrC (α := Option (Zig.Ptr)) Zig.AtomicOrder.relaxed Zig.AtomicOrder.relaxed 8 (⟨some 14, 0⟩ : Zig.Ptr) i125 i126
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

structure heap_ArenaAllocator_Node_Size_toIntLocals where
  int : heap_ArenaAllocator_Node_Size
  deriving Inhabited

inductive heap_ArenaAllocator_Node_Size_toIntExit where
  | ret (v : BitVec 64)

def heap_ArenaAllocator_Node_Size_toInt (p0 : heap_ArenaAllocator_Node_Size) : Zig.Result (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with int := p0 })
    modify (fun s => { s with int := { s.int with resizing := false } })
    let i5 ← pure ((← get).int)
    let i6 ← pure (Zig.Packed.toBits i5)
    pure (.ret i6)) : Zig.M heap_ArenaAllocator_Node_Size_toIntLocals heap_ArenaAllocator_Node_Size_toIntExit).run' (default : heap_ArenaAllocator_Node_Size_toIntLocals)
  match e with
  | .ret v => pure v

structure heap_ArenaAllocator_Node_loadBufLocals where
  deriving Inhabited

inductive heap_ArenaAllocator_Node_loadBufExit where
  | ret (v : Zig.Slice)
  | br13
  | br21

def heap_ArenaAllocator_Node_loadBuf (p0 : Zig.Ptr) : Zig.ConcM Tgt (Zig.Slice) := do
  let e ← ((do
    let i1 ← pure (p0.add 0)
    let i2 ← pure (i1)
    let i3 ← Zig.atomicLoadAsC (heap_ArenaAllocator_Node_Size) Zig.AtomicOrder.relaxed 8 i2
    let i4 ← pure (p0)
    let i5 ← Zig.callRC (heap_ArenaAllocator_Node_Size_toInt i3)
    let i6 ← pure (i4.elem 1 (0 : BitVec 64))
    let i7 ← Zig.sub false i5 (0 : BitVec 64)
    let i8 ← pure (⟨i6, i7⟩ : Zig.Slice)
    let i9 ← pure i8.ptr
    let i10 ← pure (i9.elem 1 (24 : BitVec 64))
    let i11 ← pure i8.len
    let i12 ← pure (Zig.le false (24 : BitVec 64) i11)
    match ← ((do
      if i12 then (do
        pure .br13)
      else (do
        throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_Node_loadBufLocals heap_ArenaAllocator_Node_loadBufExit) with
    | .br13 => (do
      let i18 ← Zig.sub false i11 (24 : BitVec 64)
      let i19 ← pure i8.len
      let i20 ← pure (Zig.le false i11 i19)
      match ← ((do
        if i20 then (do
          pure .br21)
        else (do
          throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_Node_loadBufLocals heap_ArenaAllocator_Node_loadBufExit) with
      | .br21 => (do
        let i26 ← pure (⟨i10, i18⟩ : Zig.Slice)
        pure (.ret i26))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_Node_loadBufLocals heap_ArenaAllocator_Node_loadBufExit).run' (default : heap_ArenaAllocator_Node_loadBufLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Alignment_forwardLocals where
  deriving Inhabited

inductive mem_Alignment_forwardExit where
  | ret (v : BitVec 64)

def mem_Alignment_forward (p0 : mem_Alignment) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← pure (mem_Alignment.toBits p0)
    let i3 ← pure (Zig.shl (1 : BitVec 64) i2)
    let i4 ← Zig.sub false i3 (1 : BitVec 64)
    let i5 ← Zig.add false p1 i4
    let i6 ← pure (~~~i4)
    let i7 ← pure (i5 &&& i6)
    pure (.ret i7)) : Zig.M mem_Alignment_forwardLocals mem_Alignment_forwardExit).run' (default : mem_Alignment_forwardLocals)
  match e with
  | .ret v => pure v

structure heap_ArenaAllocator_alignedIndexLocals where
  deriving Inhabited

inductive heap_ArenaAllocator_alignedIndexExit where
  | ret (v : BitVec 64)

def heap_ArenaAllocator_alignedIndex (p0 : Zig.Ptr) (p1 : BitVec 64) (p2 : mem_Alignment) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i3 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
    let i4 ← pure (Zig.addWrap i3 p1)
    let i5 ← Zig.callR (mem_Alignment_forward p2 i4)
    let i6 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
    let i7 ← pure (Zig.subWrap i5 i6)
    pure (.ret i7)) : Zig.MM heap_ArenaAllocator_alignedIndexLocals heap_ArenaAllocator_alignedIndexExit).run' (default : heap_ArenaAllocator_alignedIndexLocals)
  match e with
  | .ret v => pure v

structure heap_ArenaAllocator_pushFreeListLocals where
  deriving Inhabited

inductive heap_ArenaAllocator_pushFreeListExit where
  | ret
  | br20
  | br18
  | rep19

def heap_ArenaAllocator_pushFreeList.again19 : heap_ArenaAllocator_pushFreeListExit → Bool
  | .rep19 => true
  | _ => false

def heap_ArenaAllocator_pushFreeList.loop19 (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : Zig.Ptr) : Zig.CM Tgt heap_ArenaAllocator_pushFreeListLocals heap_ArenaAllocator_pushFreeListExit := do
  match ← ((do
    let i21 ← pure (p0.add 16)
    let i22 ← pure (i21.add 8)
    let i23 ← pure (p2.add 16)
    let i24 ← Zig.load (Option (Zig.Ptr)) 8 i23
    let i25 ← pure (p1)
    let i26 ← Zig.cmpxchgWeakPtrC (α := Option (Zig.Ptr)) Zig.AtomicOrder.release Zig.AtomicOrder.relaxed 8 i22 i24 i25
    let i27 ← pure ((i26).isSome)
    if i27 then (do
      let i29 ← Zig.optPayload i26
      let i30 ← pure (p2.add 16)
      Zig.store (α := Option (Zig.Ptr)) 8 i30 i29
      pure .br20)
    else (do
      pure .br18)) : Zig.CM Tgt heap_ArenaAllocator_pushFreeListLocals heap_ArenaAllocator_pushFreeListExit) with
  | .br20 => (do
    pure .rep19)
  | e => pure e

def heap_ArenaAllocator_pushFreeList (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i3 ← pure (p2.add 16)
    let i4 ← Zig.load (Option (Zig.Ptr)) 8 i3
    let i5 ← pure (p1)
    let i6 ← pure (i5 != i4)
    let _i7 ← Zig.callRC (debug_assert i6)
    let i8 ← pure (p1.add 16)
    let i9 ← Zig.load (Option (Zig.Ptr)) 8 i8
    let i10 ← pure (p1)
    let i11 ← pure (i10 != i9)
    let _i12 ← Zig.callRC (debug_assert i11)
    let i13 ← pure (p2.add 16)
    let i14 ← Zig.load (Option (Zig.Ptr)) 8 i13
    let i15 ← pure (p2)
    let i16 ← pure (i15 != i14)
    let _i17 ← Zig.callRC (debug_assert i16)
    match ← ((do
      Zig.loop (heap_ArenaAllocator_pushFreeList.loop19 p0 p1 p2) heap_ArenaAllocator_pushFreeList.again19) : Zig.CM Tgt heap_ArenaAllocator_pushFreeListLocals heap_ArenaAllocator_pushFreeListExit) with
    | .br18 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_pushFreeListLocals heap_ArenaAllocator_pushFreeListExit).run' (default : heap_ArenaAllocator_pushFreeListLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure heap_ArenaAllocator_Node_beginResizeLocals where
  deriving Inhabited

inductive heap_ArenaAllocator_Node_beginResizeExit where
  | ret (v : Option (Zig.Slice))
  | br3

def heap_ArenaAllocator_Node_beginResize (p0 : Zig.Ptr) : Zig.ConcM Tgt (Option (Zig.Slice)) := do
  let e ← ((do
    let i1 ← pure (p0.add 0)
    let i2 ← Zig.atomicRmwAsC Zig.RmwOp.or Zig.AtomicOrder.acquire 8 i1 (Zig.Packed.ofBits (1 : BitVec 64) : heap_ArenaAllocator_Node_Size)
    match ← ((do
      let i4 ← pure ((i2).resizing)
      if i4 then (do
        pure (.ret none))
      else (do
        pure .br3)) : Zig.CM Tgt heap_ArenaAllocator_Node_beginResizeLocals heap_ArenaAllocator_Node_beginResizeExit) with
    | .br3 => (do
      let i8 ← pure (p0)
      let i9 ← Zig.callRC (heap_ArenaAllocator_Node_Size_toInt i2)
      let i10 ← pure (i8.elem 1 (0 : BitVec 64))
      let i11 ← Zig.sub false i9 (0 : BitVec 64)
      let i12 ← pure (⟨i10, i11⟩ : Zig.Slice)
      let i13 ← pure (some i12)
      pure (.ret i13))
    | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_Node_beginResizeLocals heap_ArenaAllocator_Node_beginResizeExit).run' (default : heap_ArenaAllocator_Node_beginResizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heap_ArenaAllocator_Node_Size_fromIntLocals where
  deriving Inhabited

inductive heap_ArenaAllocator_Node_Size_fromIntExit where
  | ret (v : heap_ArenaAllocator_Node_Size)

def heap_ArenaAllocator_Node_Size_fromInt (p0 : BitVec 64) : Zig.Result (heap_ArenaAllocator_Node_Size) := do
  let e ← ((do
    let i1 ← pure (p0)
    let i2 ← pure (Zig.ge false i1 (24 : BitVec 64))
    let _i3 ← Zig.call (debug_assert i2)
    let i4 ← Zig.Packed.ofBits? (α := heap_ArenaAllocator_Node_Size) p0
    let i5 ← pure ((i4).resizing)
    let i6 ← pure (!i5)
    let _i7 ← Zig.call (debug_assert i6)
    pure (.ret i4)) : Zig.M heap_ArenaAllocator_Node_Size_fromIntLocals heap_ArenaAllocator_Node_Size_fromIntExit).run' (default : heap_ArenaAllocator_Node_Size_fromIntLocals)
  match e with
  | .ret v => pure v

structure heap_ArenaAllocator_Node_endResizeLocals where
  deriving Inhabited

inductive heap_ArenaAllocator_Node_endResizeExit where
  | ret

def heap_ArenaAllocator_Node_endResize (p0 : Zig.Ptr) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i3 ← pure (p1)
    let i4 ← pure (p2)
    let i5 ← pure (Zig.ge false i3 i4)
    let _i6 ← Zig.callRC (debug_assert i5)
    let i7 ← pure (p0.add 0)
    let i8 ← pure (i7)
    let i9 ← Zig.atomicLoadUnorderedAsC (heap_ArenaAllocator_Node_Size) 8 i8
    let i10 ← Zig.callRC (heap_ArenaAllocator_Node_Size_toInt i9)
    let i11 ← pure (i10)
    let i12 ← pure (p2)
    let i13 ← pure (i11 == i12)
    let _i14 ← Zig.callRC (debug_assert i13)
    let i15 ← pure (p0.add 0)
    let i16 ← Zig.callRC (heap_ArenaAllocator_Node_Size_fromInt p1)
    Zig.atomicStoreAsC Zig.AtomicOrder.release 8 i15 i16
    pure .ret) : Zig.CM Tgt heap_ArenaAllocator_Node_endResizeLocals heap_ArenaAllocator_Node_endResizeExit).run' (default : heap_ArenaAllocator_Node_endResizeLocals)
  match e with
  | .ret => pure ()

structure heap_ArenaAllocator_stealFreeListLocals where
  deriving Inhabited

inductive heap_ArenaAllocator_stealFreeListExit where
  | ret (v : Option (Zig.Ptr))

def heap_ArenaAllocator_stealFreeList (p0 : Zig.Ptr) : Zig.ConcM Tgt (Option (Zig.Ptr)) := do
  let e ← ((do
    let i1 ← pure (p0.add 16)
    let i2 ← pure (i1.add 8)
    let i3 ← Zig.atomicXchgPtrC (α := Option (Zig.Ptr)) Zig.AtomicOrder.acquire 8 i2 none
    pure (.ret i3)) : Zig.CM Tgt heap_ArenaAllocator_stealFreeListLocals heap_ArenaAllocator_stealFreeListExit).run' (default : heap_ArenaAllocator_stealFreeListLocals)
  match e with
  | .ret v => pure v

structure heap_ArenaAllocator_Node_allocatedSliceUnsafeLocals where
  deriving Inhabited

inductive heap_ArenaAllocator_Node_allocatedSliceUnsafeExit where
  | ret (v : Zig.Slice)

def heap_ArenaAllocator_Node_allocatedSliceUnsafe (p0 : Zig.Ptr) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    let i1 ← pure (p0)
    let i2 ← pure (p0.add 0)
    let i3 ← Zig.load (heap_ArenaAllocator_Node_Size) 8 i2
    let i4 ← Zig.callR (heap_ArenaAllocator_Node_Size_toInt i3)
    let i5 ← pure (i1.elem 1 (0 : BitVec 64))
    let i6 ← Zig.sub false i4 (0 : BitVec 64)
    let i7 ← pure (⟨i5, i6⟩ : Zig.Slice)
    pure (.ret i7)) : Zig.MM heap_ArenaAllocator_Node_allocatedSliceUnsafeLocals heap_ArenaAllocator_Node_allocatedSliceUnsafeExit).run' (default : heap_ArenaAllocator_Node_allocatedSliceUnsafeLocals)
  match e with
  | .ret v => pure v

structure heap_ArenaAllocator_tryPushNodeLocals where
  local16 : heap_ArenaAllocator_PushResult
  deriving Inhabited

inductive heap_ArenaAllocator_tryPushNodeExit where
  | ret (v : heap_ArenaAllocator_PushResult)

def heap_ArenaAllocator_tryPushNode (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.ConcM Tgt (heap_ArenaAllocator_PushResult) := do
  let e ← ((do
    let i2 ← pure (p1.add 16)
    let i3 ← Zig.load (Option (Zig.Ptr)) 8 i2
    let i4 ← pure (p1)
    let i5 ← pure (i4 != i3)
    let _i6 ← Zig.callRC (debug_assert i5)
    let i7 ← pure (p0.add 16)
    let i8 ← pure (i7.add 0)
    let i9 ← pure (p1.add 16)
    let i10 ← Zig.load (Option (Zig.Ptr)) 8 i9
    let i11 ← pure (p1)
    let i12 ← Zig.cmpxchgPtrC (α := Option (Zig.Ptr)) Zig.AtomicOrder.release Zig.AtomicOrder.acquire 8 i8 i10 i11
    let i13 ← pure ((i12).isSome)
    if i13 then (do
      let i15 ← Zig.optPayload i12
      modify (fun s => { s with local16 := (heap_ArenaAllocator_PushResult.setTag_failure s.local16) })
      modify (fun s => { s with local16 := (heap_ArenaAllocator_PushResult.modify_failure (fun _ => i15) s.local16) })
      pure (.ret (← get).local16))
    else (do
      pure (.ret heap_ArenaAllocator_PushResult.success))) : Zig.CM Tgt heap_ArenaAllocator_tryPushNodeLocals heap_ArenaAllocator_tryPushNodeExit).run' (default : heap_ArenaAllocator_tryPushNodeLocals)
  match e with
  | .ret v => pure v

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
      let i16 ← pure (p0)
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
          let i29 ← Zig.callR (mem_alignForward__anon_1 p2 (4096 : BitVec 64))
          let i31 ← pure (((← get).local17).len)
          let i32 ← Zig.callR (mem_alignForward__anon_1 i31 (4096 : BitVec 64))
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
                  let i72 ← pure (i71.elem 1 i29)
                  let i73 ← Zig.sub false i32 i29
                  let i74 ← pure (i72.elem 1 (0 : BitVec 64))
                  let i75 ← Zig.sub false i73 (0 : BitVec 64)
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
                    let i89 ← pure (i76)
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

structure heap_ArenaAllocator_resizeLocals where
  local5 : Zig.Slice
  deriving Inhabited

inductive heap_ArenaAllocator_resizeExit where
  | ret (v : Bool)
  | br11
  | br27
  | br38
  | br54
  | br75

def heap_ArenaAllocator_resize (p0 : Zig.Ptr) (p1 : Zig.Slice) (p2 : mem_Alignment) (p3 : BitVec 64) (p4 : BitVec 64) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    modify (fun s => { s with local5 := p1 })
    let i8 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
    let i9 ← pure (i8 &&& (7 : BitVec 64))
    let i10 ← pure (i9 == (0 : BitVec 64))
    match ← ((do
      if i10 then (do
        pure .br11)
      else (do
        throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_resizeLocals heap_ArenaAllocator_resizeExit) with
    | .br11 => (do
      let i16 ← pure (p0)
      let i18 ← pure (((← get).local5).len)
      let i19 ← pure (i18)
      let i20 ← pure (Zig.gt false i19 (0 : BitVec 64))
      let _i21 ← Zig.callRC (debug_assert i20)
      let i22 ← pure (p3)
      let i23 ← pure (Zig.gt false i22 (0 : BitVec 64))
      let _i24 ← Zig.callRC (debug_assert i23)
      let i25 ← Zig.callC (heap_ArenaAllocator_loadFirstNode i16)
      let i26 ← pure ((i25).isSome)
      match ← ((do
        if i26 then (do
          pure .br27)
        else (do
          throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_resizeLocals heap_ArenaAllocator_resizeExit) with
      | .br27 => (do
        let i32 ← Zig.optPayload i25
        let i33 ← pure (i32)
        let i34 ← pure (i33.elem 1 (24 : BitVec 64))
        let i35 ← pure (i32.add 8)
        let i36 ← pure (i35)
        let i37 ← Zig.atomicLoadC (n := 64) Zig.AtomicOrder.relaxed 8 i36
        match ← ((do
          let i39 ← pure (i34.elem 1 i37)
          let i41 ← pure (((← get).local5).ptr)
          let i43 ← pure (((← get).local5).len)
          let i44 ← pure (i41.elem 1 i43)
          let i45 ← pure (i39 != i44)
          if i45 then (do
            let i48 ← pure (((← get).local5).len)
            let i49 ← pure (p3)
            let i50 ← pure (i48)
            let i51 ← pure (Zig.le false i49 i50)
            pure (.ret i51))
          else (do
            pure .br38)) : Zig.CM Tgt heap_ArenaAllocator_resizeLocals heap_ArenaAllocator_resizeExit) with
        | .br38 => (do
          match ← ((do
            let i56 ← pure (((← get).local5).len)
            let i57 ← pure (p3)
            let i58 ← pure (i56)
            let i59 ← pure (Zig.le false i57 i58)
            if i59 then (do
              let i62 ← pure (((← get).local5).len)
              let i63 ← Zig.sub false i62 p3
              let i64 ← Zig.sub false i37 i63
              let i65 ← pure (i34.elem 1 i64)
              let i67 ← pure (((← get).local5).ptr)
              let i68 ← pure (i67.elem 1 p3)
              let i69 ← pure (i65 == i68)
              let _i70 ← Zig.callRC (debug_assert i69)
              let i71 ← pure (i32.add 8)
              let _i72 ← Zig.cmpxchgC Zig.AtomicOrder.release Zig.AtomicOrder.relaxed 8 i71 i37 i64
              pure (.ret true))
            else (do
              pure .br54)) : Zig.CM Tgt heap_ArenaAllocator_resizeLocals heap_ArenaAllocator_resizeExit) with
          | .br54 => (do
            match ← ((do
              let i76 ← Zig.callC (heap_ArenaAllocator_Node_loadBuf i32)
              let i77 ← pure i76.len
              let i78 ← pure (Zig.subSat false i77 i37)
              let i80 ← pure (((← get).local5).len)
              let i81 ← Zig.sub false p3 i80
              let i82 ← pure (i78)
              let i83 ← pure (i81)
              let i84 ← pure (Zig.ge false i82 i83)
              if i84 then (do
                let i87 ← pure (((← get).local5).len)
                let i88 ← Zig.sub false p3 i87
                let i89 ← Zig.add false i37 i88
                let i90 ← pure (i34.elem 1 i89)
                let i92 ← pure (((← get).local5).ptr)
                let i93 ← pure (i92.elem 1 p3)
                let i94 ← pure (i90 == i93)
                let _i95 ← Zig.callRC (debug_assert i94)
                let i96 ← pure (i32.add 8)
                let i97 ← Zig.cmpxchgC Zig.AtomicOrder.acquire Zig.AtomicOrder.relaxed 8 i96 i37 i89
                let i98 ← pure ((i97).isNone)
                pure (.ret i98))
              else (do
                pure .br75)) : Zig.CM Tgt heap_ArenaAllocator_resizeLocals heap_ArenaAllocator_resizeExit) with
            | .br75 => (do
              pure (.ret false))
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_resizeLocals heap_ArenaAllocator_resizeExit).run' (default : heap_ArenaAllocator_resizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heap_FixedBufferAllocator_resizeLocals where
  deriving Inhabited

inductive heap_FixedBufferAllocator_resizeExit where
  | ret (v : Bool)
  | br8
  | br20
  | br16
  | br30
  | br46

def heap_FixedBufferAllocator_resize (p0 : Zig.Ptr) (p1 : Zig.Slice) (p2 : mem_Alignment) (p3 : BitVec 64) (p4 : BitVec 64) : Zig.MemM (Bool) := do
  let e ← ((do
    let i5 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
    let i6 ← pure (i5 &&& (7 : BitVec 64))
    let i7 ← pure (i6 == (0 : BitVec 64))
    match ← ((do
      if i7 then (do
        pure .br8)
      else (do
        throw .panic)) : Zig.MM heap_FixedBufferAllocator_resizeLocals heap_FixedBufferAllocator_resizeExit) with
    | .br8 => (do
      let i13 ← pure (p0)
      let i14 ← Zig.callM (heap_FixedBufferAllocator_ownsSlice i13 p1)
      let _i15 ← Zig.callR (debug_assert i14)
      match ← ((do
        let i17 ← Zig.callM (heap_FixedBufferAllocator_isLastAllocation i13 p1)
        let i18 ← pure (!i17)
        if i18 then (do
          match ← ((do
            let i21 ← pure p1.len
            let i22 ← pure (p3)
            let i23 ← pure (i21)
            let i24 ← pure (Zig.gt false i22 i23)
            if i24 then (do
              pure (.ret false))
            else (do
              pure .br20)) : Zig.MM heap_FixedBufferAllocator_resizeLocals heap_FixedBufferAllocator_resizeExit) with
          | .br20 => (do
            pure (.ret true))
          | e => pure e)
        else (do
          pure .br16)) : Zig.MM heap_FixedBufferAllocator_resizeLocals heap_FixedBufferAllocator_resizeExit) with
      | .br16 => (do
        match ← ((do
          let i31 ← pure p1.len
          let i32 ← pure (p3)
          let i33 ← pure (i31)
          let i34 ← pure (Zig.le false i32 i33)
          if i34 then (do
            let i36 ← pure p1.len
            let i37 ← Zig.sub false i36 p3
            let i38 ← pure (i13.add 0)
            let i39 ← Zig.load (BitVec 64) 8 i38
            let i40 ← Zig.sub false i39 i37
            Zig.store (α := BitVec 64) 8 i38 i40
            pure (.ret true))
          else (do
            pure .br30)) : Zig.MM heap_FixedBufferAllocator_resizeLocals heap_FixedBufferAllocator_resizeExit) with
        | .br30 => (do
          let i44 ← pure p1.len
          let i45 ← Zig.sub false p3 i44
          match ← ((do
            let i47 ← pure (i13.add 0)
            let i48 ← Zig.load (BitVec 64) 8 i47
            let i49 ← Zig.add false i45 i48
            let i50 ← pure (i13.add 8)
            let i51 ← pure (i50.add 8)
            let i52 ← Zig.load (BitVec 64) 8 i51
            let i53 ← pure (i49)
            let i54 ← pure (i52)
            let i55 ← pure (Zig.gt false i53 i54)
            if i55 then (do
              pure (.ret false))
            else (do
              pure .br46)) : Zig.MM heap_FixedBufferAllocator_resizeLocals heap_FixedBufferAllocator_resizeExit) with
          | .br46 => (do
            let i59 ← pure (i13.add 0)
            let i60 ← Zig.load (BitVec 64) 8 i59
            let i61 ← Zig.add false i60 i45
            Zig.store (α := BitVec 64) 8 i59 i61
            pure (.ret true))
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM heap_FixedBufferAllocator_resizeLocals heap_FixedBufferAllocator_resizeExit).run' (default : heap_FixedBufferAllocator_resizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_alignPointerOffset__anon_1Locals where
  ov : BitVec 64 × BitVec 1
  deriving Inhabited

inductive mem_alignPointerOffset__anon_1Exit where
  | ret (v : Option (BitVec 64))
  | br4
  | br15
  | br31

def mem_alignPointerOffset__anon_1 (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (Option (BitVec 64)) := do
  let e ← ((do
    let i2 ← Zig.callR (mem_isValidAlign p1)
    let _i3 ← Zig.callR (debug_assert i2)
    match ← ((do
      let i5 ← pure (p1)
      let i6 ← pure (Zig.le false i5 (1 : BitVec 64))
      if i6 then (do
        pure (.ret (some (0 : BitVec 64))))
      else (do
        pure .br4)) : Zig.MM mem_alignPointerOffset__anon_1Locals mem_alignPointerOffset__anon_1Exit) with
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
          pure .br15)) : Zig.MM mem_alignPointerOffset__anon_1Locals mem_alignPointerOffset__anon_1Exit) with
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
            pure .br31)) : Zig.MM mem_alignPointerOffset__anon_1Locals mem_alignPointerOffset__anon_1Exit) with
        | .br31 => (do
          let i38 ← Zig.divTrunc false i30 (1 : BitVec 64)
          let i39 ← pure (some i38)
          pure (.ret i39))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM mem_alignPointerOffset__anon_1Locals mem_alignPointerOffset__anon_1Exit).run' (default : mem_alignPointerOffset__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heap_FixedBufferAllocator_allocLocals where
  deriving Inhabited

inductive heap_FixedBufferAllocator_allocExit where
  | ret (v : Option (Zig.Ptr))
  | br7
  | br14 (v : BitVec 64)
  | br31

def heap_FixedBufferAllocator_alloc (p0 : Zig.Ptr) (p1 : BitVec 64) (p2 : mem_Alignment) (p3 : BitVec 64) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    let i4 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
    let i5 ← pure (i4 &&& (7 : BitVec 64))
    let i6 ← pure (i5 == (0 : BitVec 64))
    match ← ((do
      if i6 then (do
        pure .br7)
      else (do
        throw .panic)) : Zig.MM heap_FixedBufferAllocator_allocLocals heap_FixedBufferAllocator_allocExit) with
    | .br7 => (do
      let i12 ← pure (p0)
      let i13 ← Zig.callR (mem_Alignment_toByteUnits p2)
      match ← ((do
        let i15 ← pure (i12.add 8)
        let i16 ← pure (i15.add 0)
        let i17 ← Zig.load (Zig.Ptr) 8 i16
        let i18 ← pure (i12.add 0)
        let i19 ← Zig.load (BitVec 64) 8 i18
        let i20 ← pure (i17.elem 1 i19)
        let i21 ← Zig.callM (mem_alignPointerOffset__anon_1 i20 i13)
        let i22 ← pure ((i21).isSome)
        if i22 then (do
          let i24 ← Zig.optPayload i21
          pure (.br14 i24))
        else (do
          pure (.ret none))) : Zig.MM heap_FixedBufferAllocator_allocLocals heap_FixedBufferAllocator_allocExit) with
      | .br14 v14 => (do
        let i27 ← pure (i12.add 0)
        let i28 ← Zig.load (BitVec 64) 8 i27
        let i29 ← Zig.add false i28 v14
        let i30 ← Zig.add false i29 p1
        match ← ((do
          let i32 ← pure (i12.add 8)
          let i33 ← pure (i32.add 8)
          let i34 ← Zig.load (BitVec 64) 8 i33
          let i35 ← pure (i30)
          let i36 ← pure (i34)
          let i37 ← pure (Zig.gt false i35 i36)
          if i37 then (do
            pure (.ret none))
          else (do
            pure .br31)) : Zig.MM heap_FixedBufferAllocator_allocLocals heap_FixedBufferAllocator_allocExit) with
        | .br31 => (do
          let i41 ← pure (i12.add 0)
          Zig.store (α := BitVec 64) 8 i41 i30
          let i43 ← pure (i12.add 8)
          let i44 ← pure (i43.add 0)
          let i45 ← Zig.load (Zig.Ptr) 8 i44
          let i46 ← pure (i45.elem 1 i29)
          let i47 ← pure (i46)
          pure (.ret i47))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM heap_FixedBufferAllocator_allocLocals heap_FixedBufferAllocator_allocExit).run' (default : heap_FixedBufferAllocator_allocLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heap_ArenaAllocator_allocLocals where
  cur_first_node : Option (Zig.Ptr)
  cur_new_node : Option (Zig.Ptr)
  local23 : Option (Zig.Ptr)
  local24 : BitVec 64
  local36 : Zig.Slice
  local93 : Zig.Slice
  local127 : Zig.Slice
  size : BitVec 64
  local153 : Zig.Slice
  local233 : Zig.Slice
  local270 : Zig.Ptr
  local271 : Zig.Ptr
  local272 : Zig.Ptr
  local273 : Option (Zig.Ptr)
  best_fit_prev : Option (Zig.Ptr)
  best_fit : Option (Zig.Ptr)
  best_fit_diff : BitVec 64
  it_prev : Option (Zig.Ptr)
  it : Option (Zig.Ptr)
  local318 : Zig.Slice
  local376 : BitVec 64
  local377 : Bool
  local399 : Zig.Slice
  local544 : Zig.Slice
  local656 : Zig.Slice
  local696 : Zig.Slice
  deriving Inhabited

inductive heap_ArenaAllocator_allocExit where
  | ret (v : Option (Zig.Ptr))
  | br7
  | br26 (v : Zig.Ptr)
  | br25
  | br53
  | br66
  | br87
  | br98
  | br113 (v : Zig.Ptr)
  | br112
  | br120 (v : Zig.Slice)
  | br139
  | br147
  | br22
  | br165
  | br181
  | br184 (v : Bool)
  | br208
  | br216
  | br227
  | br242
  | br193
  | br178
  | br263 (v : Zig.Ptr)
  | br262
  | br304
  | br312
  | br328
  | br293
  | br288
  | br286
  | br353
  | br362
  | br274
  | br385
  | br393
  | br378
  | br428
  | br431 (v : Bool)
  | br423
  | br416
  | br456
  | br464
  | br488
  | br497 (v : Option (Zig.Ptr))
  | br507 (v : Option (Zig.Ptr))
  | br523
  | br518
  | br538
  | br549
  | br570 (v : Zig.Ptr)
  | br571
  | br578 (v : heap_ArenaAllocator_Node_Size)
  | br594
  | br597 (v : Option (Zig.Ptr))
  | br590 (v : Zig.Ptr)
  | br608
  | br622
  | br642
  | br650
  | br690
  | br701
  | br679
  | rep287
  | rep21

def heap_ArenaAllocator_alloc.again287 : heap_ArenaAllocator_allocExit → Bool
  | .rep287 => true
  | _ => false

def heap_ArenaAllocator_alloc.again21 : heap_ArenaAllocator_allocExit → Bool
  | .rep21 => true
  | _ => false

mutual

def heap_ArenaAllocator_alloc.loop287 (p1 : BitVec 64) (p2 : mem_Alignment) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit := do
  match ← ((do
    let i289 ← pure ((← get).it)
    let i290 ← pure ((i289).isSome)
    if i290 then (do
      let i292 ← Zig.optPayload i289
      match ← ((do
        let i294 ← pure (i292.add 0)
        let i295 ← pure (i294.add 0)
        let i296 ← Zig.loadBits (Bool) 8 8 0 i295
        let i297 ← pure (!i296)
        let _i298 ← Zig.callRC (debug_assert i297)
        let i299 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe i292)
        let i300 ← pure i299.ptr
        let i301 ← pure (i300.elem 1 (24 : BitVec 64))
        let i302 ← pure i299.len
        let i303 ← pure (Zig.le false (24 : BitVec 64) i302)
        match ← ((do
          if i303 then (do
            pure .br304)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
        | .br304 => (do
          let i309 ← Zig.sub false i302 (24 : BitVec 64)
          let i310 ← pure i299.len
          let i311 ← pure (Zig.le false i302 i310)
          match ← ((do
            if i311 then (do
              pure .br312)
            else (do
              throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
          | .br312 => (do
            let i317 ← pure (⟨i301, i309⟩ : Zig.Slice)
            modify (fun s => { s with local318 := i317 })
            let i322 ← pure (((← get).local318).ptr)
            let i323 ← Zig.callMC (heap_ArenaAllocator_alignedIndex i322 (0 : BitVec 64) p2)
            let i324 ← Zig.add false i323 p1
            let i326 ← pure (((← get).local318).len)
            let i327 ← pure (Zig.subSat false i324 i326)
            match ← ((do
              let i329 ← pure ((← get).best_fit_diff)
              let i330 ← pure (i327)
              let i331 ← pure (i329)
              let i332 ← pure (Zig.lt false i330 i331)
              if i332 then (do
                let i334 ← pure ((← get).it_prev)
                modify (fun s => { s with best_fit_prev := i334 })
                let i336 ← pure (i292)
                modify (fun s => { s with best_fit := i336 })
                modify (fun s => { s with best_fit_diff := i327 })
                pure .br328)
              else (do
                pure .br328)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
            | .br328 => (do
              pure .br293)
            | e => pure e)
          | e => pure e)
        | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
      | .br293 => (do
        let i342 ← pure (i292)
        modify (fun s => { s with it_prev := i342 })
        let i344 ← pure (i292.add 16)
        let i345 ← Zig.load (Option (Zig.Ptr)) 8 i344
        modify (fun s => { s with it := i345 })
        pure .br288)
      | e => pure e)
    else (do
      pure .br286)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
  | .br288 => (do
    pure .rep287)
  | e => pure e
partial_fixpoint

def heap_ArenaAllocator_alloc.loop21 (p1 : BitVec 64) (p2 : mem_Alignment) (i12 : Zig.Ptr) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit := do
  match ← ((do
    match ← ((do
      match ← ((do
        let i27 ← pure ((← get).cur_first_node)
        let i28 ← pure ((i27).isSome)
        if i28 then (do
          let i30 ← Zig.optPayload i27
          pure (.br26 i30))
        else (do
          modify (fun s => { s with local23 := none })
          modify (fun s => { s with local24 := (0 : BitVec 64) })
          pure .br25)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
      | .br26 v26 => (do
        let i35 ← Zig.callC (heap_ArenaAllocator_Node_loadBuf v26)
        modify (fun s => { s with local36 := i35 })
        let i39 ← Zig.callRC (mem_Alignment_toByteUnits p2)
        let i40 ← Zig.add false p1 i39
        let i41 ← Zig.sub false i40 (1 : BitVec 64)
        let i42 ← pure (v26.add 8)
        let i43 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.acquire 8 i42 i41
        let i45 ← pure (((← get).local36).ptr)
        let i46 ← Zig.callMC (heap_ArenaAllocator_alignedIndex i45 i43 p2)
        let i47 ← Zig.add false i43 i41
        let i48 ← Zig.add false i46 p1
        let i49 ← pure (i47)
        let i50 ← pure (i48)
        let i51 ← pure (Zig.ge false i49 i50)
        let _i52 ← Zig.callRC (debug_assert i51)
        match ← ((do
          let i54 ← Zig.add false i43 i41
          let i55 ← Zig.add false i46 p1
          let i56 ← pure (i54)
          let i57 ← pure (i55)
          let i58 ← pure (i56 != i57)
          if i58 then (do
            let i60 ← pure (v26.add 8)
            let i61 ← Zig.add false i43 i41
            let i62 ← Zig.add false i46 p1
            let _i63 ← Zig.cmpxchgC Zig.AtomicOrder.relaxed Zig.AtomicOrder.relaxed 8 i60 i61 i62
            pure .br53)
          else (do
            pure .br53)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
        | .br53 => (do
          match ← ((do
            let i67 ← Zig.add false i46 p1
            let i69 ← pure (((← get).local36).len)
            let i70 ← pure (i67)
            let i71 ← pure (i69)
            let i72 ← pure (Zig.gt false i70 i71)
            if i72 then (do
              let i74 ← pure (v26)
              modify (fun s => { s with local23 := i74 })
              let i77 ← pure (((← get).local36).len)
              modify (fun s => { s with local24 := i77 })
              pure .br25)
            else (do
              pure .br66)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
          | .br66 => (do
            let i81 ← pure ((← get).local36)
            let i82 ← pure i81.ptr
            let i83 ← pure (i82.elem 1 i46)
            let i84 ← Zig.add false i46 p1
            let i85 ← pure i81.len
            let i86 ← pure (Zig.le false i84 i85)
            match ← ((do
              if i86 then (do
                pure .br87)
              else (do
                throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
            | .br87 => (do
              let i92 ← pure (⟨i83, p1⟩ : Zig.Slice)
              modify (fun s => { s with local93 := i92 })
              let i97 ← pure (((← get).local93).ptr)
              match ← ((do
                let i99 ← pure ((← get).cur_new_node)
                let i100 ← pure ((i99).isSome)
                if i100 then (do
                  let i102 ← Zig.optPayload i99
                  let i103 ← pure (i102.add 16)
                  Zig.store (α := Option (Zig.Ptr)) 8 i103 none
                  let _i105 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i102 i102)
                  pure .br98)
                else (do
                  pure .br98)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
              | .br98 => (do
                let i108 ← pure (i97)
                pure (.ret i108))
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
    | .br25 => (do
      match ← ((do
        match ← ((do
          let i114 ← pure ((← get).local23)
          let i115 ← pure ((i114).isSome)
          if i115 then (do
            let i117 ← Zig.optPayload i114
            pure (.br113 i117))
          else (do
            pure .br112)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
        | .br113 v113 => (do
          match ← ((do
            let i121 ← Zig.callC (heap_ArenaAllocator_Node_beginResize v113)
            let i122 ← pure ((i121).isSome)
            if i122 then (do
              let i124 ← Zig.optPayload i121
              pure (.br120 i124))
            else (do
              pure .br112)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
          | .br120 v120 => (do
            modify (fun s => { s with local127 := v120 })
            let i132 ← pure (((← get).local127).len)
            modify (fun s => { s with size := i132 })
            let i134 ← pure ((← get).local127)
            let i135 ← pure i134.ptr
            let i136 ← pure (i135.elem 1 (24 : BitVec 64))
            let i137 ← pure i134.len
            let i138 ← pure (Zig.le false (24 : BitVec 64) i137)
            match ← ((do
              if i138 then (do
                pure .br139)
              else (do
                throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
            | .br139 => (do
              let i144 ← Zig.sub false i137 (24 : BitVec 64)
              let i145 ← pure i134.len
              let i146 ← pure (Zig.le false i137 i145)
              match ← ((do
                if i146 then (do
                  pure .br147)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
              | .br147 => (do
                let i152 ← pure (⟨i136, i144⟩ : Zig.Slice)
                modify (fun s => { s with local153 := i152 })
                let i156 ← pure (v113.add 8)
                let i157 ← pure (i156)
                let i158 ← Zig.atomicLoadC (n := 64) Zig.AtomicOrder.relaxed 8 i157
                let i160 ← pure (((← get).local153).ptr)
                let i161 ← Zig.callMC (heap_ArenaAllocator_alignedIndex i160 i158 p2)
                let i162 ← Zig.add false (24 : BitVec 64) i161
                let i163 ← Zig.add false i162 p1
                let i164 ← Zig.callRC (mem_alignForward__anon_1 i163 (2 : BitVec 64))
                match ← ((do
                  let i167 ← pure (((← get).local127).len)
                  let i168 ← pure (i164)
                  let i169 ← pure (i167)
                  let i170 ← pure (Zig.le false i168 i169)
                  if i170 then (do
                    let i172 ← pure ((← get).size)
                    let i174 ← pure (((← get).local127).len)
                    let _i175 ← Zig.callC (heap_ArenaAllocator_Node_endResize v113 i172 i174)
                    pure .br22)
                  else (do
                    pure .br165)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br165 => (do
                  match ← ((do
                    let i179 ← pure (i12.add 0)
                    let i180 ← Zig.load (mem_Allocator) 8 i179
                    match ← ((do
                      pure .br181) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br181 => (do
                      let i183 ← Zig.callMC Zig.returnAddress
                      match ← ((do
                        let i185 ← pure ((i180).vtable)
                        let i186 ← pure (i185.add 8)
                        let i187 ← Zig.load (Zig.Ptr) 8 i186
                        let i188 ← pure ((i180).ptr)
                        let i189 ← (if i187 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_resize i188 v120 mem_Alignment.«8» i164 i183) else if i187 == (⟨some 7, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_resize i188 v120 mem_Alignment.«8» i164 i183) else if i187 == (⟨some 11, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_resize i188 v120 mem_Alignment.«8» i164 i183) else throw .illegal)
                        pure (.br184 i189)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                      | .br184 v184 => (do
                        if v184 then (do
                          modify (fun s => { s with size := i164 })
                          match ← ((do
                            let i194 ← pure (v113.add 8)
                            let i195 ← Zig.add false i161 p1
                            let i196 ← Zig.cmpxchgC Zig.AtomicOrder.acquire Zig.AtomicOrder.relaxed 8 i194 i158 i195
                            let i197 ← pure ((i196).isNone)
                            if i197 then (do
                              let i200 ← pure (((← get).local127).ptr)
                              let i201 ← pure (i200.elem 1 (0 : BitVec 64))
                              let i202 ← Zig.sub false i164 (0 : BitVec 64)
                              let i203 ← pure (⟨i201, i202⟩ : Zig.Slice)
                              let i204 ← pure i203.ptr
                              let i205 ← pure (i204.elem 1 (24 : BitVec 64))
                              let i206 ← pure i203.len
                              let i207 ← pure (Zig.le false (24 : BitVec 64) i206)
                              match ← ((do
                                if i207 then (do
                                  pure .br208)
                                else (do
                                  throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                              | .br208 => (do
                                let i213 ← Zig.sub false i206 (24 : BitVec 64)
                                let i214 ← pure i203.len
                                let i215 ← pure (Zig.le false i206 i214)
                                match ← ((do
                                  if i215 then (do
                                    pure .br216)
                                  else (do
                                    throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                | .br216 => (do
                                  let i221 ← pure (⟨i205, i213⟩ : Zig.Slice)
                                  let i222 ← pure i221.ptr
                                  let i223 ← pure (i222.elem 1 i161)
                                  let i224 ← Zig.add false i161 p1
                                  let i225 ← pure i221.len
                                  let i226 ← pure (Zig.le false i224 i225)
                                  match ← ((do
                                    if i226 then (do
                                      pure .br227)
                                    else (do
                                      throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                  | .br227 => (do
                                    let i232 ← pure (⟨i223, p1⟩ : Zig.Slice)
                                    modify (fun s => { s with local233 := i232 })
                                    let i237 ← pure (((← get).local233).ptr)
                                    let i238 ← pure ((← get).size)
                                    let i240 ← pure (((← get).local127).len)
                                    let _i241 ← Zig.callC (heap_ArenaAllocator_Node_endResize v113 i238 i240)
                                    match ← ((do
                                      let i243 ← pure ((← get).cur_new_node)
                                      let i244 ← pure ((i243).isSome)
                                      if i244 then (do
                                        let i246 ← Zig.optPayload i243
                                        let i247 ← pure (i246.add 16)
                                        Zig.store (α := Option (Zig.Ptr)) 8 i247 none
                                        let _i249 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i246 i246)
                                        pure .br242)
                                      else (do
                                        pure .br242)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                    | .br242 => (do
                                      let i252 ← pure (i237)
                                      pure (.ret i252))
                                    | e => pure e)
                                  | e => pure e)
                                | e => pure e)
                              | e => pure e)
                            else (do
                              pure .br193)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                          | .br193 => (do
                            pure .br178)
                          | e => pure e)
                        else (do
                          pure .br178))
                      | e => pure e)
                    | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br178 => (do
                    let i257 ← pure ((← get).size)
                    let i259 ← pure (((← get).local127).len)
                    let _i260 ← Zig.callC (heap_ArenaAllocator_Node_endResize v113 i257 i259)
                    pure .br112)
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
      | .br112 => (do
        match ← ((do
          match ← ((do
            let i264 ← Zig.callC (heap_ArenaAllocator_stealFreeList i12)
            let i265 ← pure ((i264).isSome)
            if i265 then (do
              let i267 ← Zig.optPayload i264
              pure (.br263 i267))
            else (do
              pure .br262)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
          | .br263 v263 => (do
            match ← ((do
              modify (fun s => { s with best_fit_prev := none })
              modify (fun s => { s with best_fit := none })
              modify (fun s => { s with best_fit_diff := (18446744073709551615 : BitVec 64) })
              modify (fun s => { s with it_prev := none })
              let i284 ← pure (v263)
              modify (fun s => { s with it := i284 })
              match ← ((do
                Zig.loop (heap_ArenaAllocator_alloc.loop287 p1 p2) heap_ArenaAllocator_alloc.again287) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
              | .br286 => (do
                modify (fun s => { s with local270 := v263 })
                let i351 ← pure ((← get).it_prev)
                let i352 ← pure ((i351).isSome)
                match ← ((do
                  if i352 then (do
                    pure .br353)
                  else (do
                    throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br353 => (do
                  let i358 ← Zig.optPayload i351
                  modify (fun s => { s with local271 := i358 })
                  let i360 ← pure ((← get).best_fit)
                  let i361 ← pure ((i360).isSome)
                  match ← ((do
                    if i361 then (do
                      pure .br362)
                    else (do
                      throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br362 => (do
                    let i367 ← Zig.optPayload i360
                    modify (fun s => { s with local272 := i367 })
                    let i369 ← pure ((← get).best_fit_prev)
                    modify (fun s => { s with local273 := i369 })
                    pure .br274)
                  | e => pure e)
                | e => pure e)
              | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
            | .br274 => (do
              match ← ((do
                let i379 ← pure ((← get).local272)
                let i380 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe i379)
                let i381 ← pure i380.ptr
                let i382 ← pure (i381.elem 1 (24 : BitVec 64))
                let i383 ← pure i380.len
                let i384 ← pure (Zig.le false (24 : BitVec 64) i383)
                match ← ((do
                  if i384 then (do
                    pure .br385)
                  else (do
                    throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br385 => (do
                  let i390 ← Zig.sub false i383 (24 : BitVec 64)
                  let i391 ← pure i380.len
                  let i392 ← pure (Zig.le false i383 i391)
                  match ← ((do
                    if i392 then (do
                      pure .br393)
                    else (do
                      throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br393 => (do
                    let i398 ← pure (⟨i382, i390⟩ : Zig.Slice)
                    modify (fun s => { s with local399 := i398 })
                    let i403 ← pure (((← get).local399).ptr)
                    let i404 ← Zig.callMC (heap_ArenaAllocator_alignedIndex i403 (0 : BitVec 64) p2)
                    modify (fun s => { s with local376 := i404 })
                    let i406 ← Zig.add false i404 p1
                    let i408 ← pure (((← get).local399).len)
                    let i409 ← pure (i406)
                    let i410 ← pure (i408)
                    let i411 ← pure (Zig.gt false i409 i410)
                    modify (fun s => { s with local377 := i411 })
                    pure .br378)
                  | e => pure e)
                | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
              | .br378 => (do
                match ← ((do
                  let i417 ← pure ((← get).local377)
                  if i417 then (do
                    let i419 ← pure ((← get).local376)
                    let i420 ← Zig.add false (24 : BitVec 64) i419
                    let i421 ← Zig.add false i420 p1
                    let i422 ← Zig.callRC (mem_alignForward__anon_1 i421 (2 : BitVec 64))
                    match ← ((do
                      let i424 ← pure (i12.add 0)
                      let i425 ← Zig.load (mem_Allocator) 8 i424
                      let i426 ← pure ((← get).local272)
                      let i427 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe i426)
                      match ← ((do
                        pure .br428) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                      | .br428 => (do
                        let i430 ← Zig.callMC Zig.returnAddress
                        match ← ((do
                          let i432 ← pure ((i425).vtable)
                          let i433 ← pure (i432.add 8)
                          let i434 ← Zig.load (Zig.Ptr) 8 i433
                          let i435 ← pure ((i425).ptr)
                          let i436 ← (if i434 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_resize i435 i427 mem_Alignment.«8» i422 i430) else if i434 == (⟨some 7, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_resize i435 i427 mem_Alignment.«8» i422 i430) else if i434 == (⟨some 11, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_resize i435 i427 mem_Alignment.«8» i422 i430) else throw .illegal)
                          pure (.br431 i436)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                        | .br431 v431 => (do
                          if v431 then (do
                            let i439 ← pure ((← get).local272)
                            let i440 ← pure (i439.add 0)
                            let i441 ← Zig.callRC (heap_ArenaAllocator_Node_Size_fromInt i422)
                            Zig.store (α := heap_ArenaAllocator_Node_Size) 8 i440 i441
                            pure .br423)
                          else (do
                            let i444 ← pure ((← get).local270)
                            let i445 ← pure ((← get).local271)
                            let _i446 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i444 i445)
                            pure .br262))
                        | e => pure e)
                      | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br423 => (do
                      pure .br416)
                    | e => pure e)
                  else (do
                    pure .br416)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br416 => (do
                  let i450 ← pure ((← get).local272)
                  let i451 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe i450)
                  let i452 ← pure i451.ptr
                  let i453 ← pure (i452.elem 1 (24 : BitVec 64))
                  let i454 ← pure i451.len
                  let i455 ← pure (Zig.le false (24 : BitVec 64) i454)
                  match ← ((do
                    if i455 then (do
                      pure .br456)
                    else (do
                      throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br456 => (do
                    let i461 ← Zig.sub false i454 (24 : BitVec 64)
                    let i462 ← pure i451.len
                    let i463 ← pure (Zig.le false i454 i462)
                    match ← ((do
                      if i463 then (do
                        pure .br464)
                      else (do
                        throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br464 => (do
                      let i469 ← pure (⟨i453, i461⟩ : Zig.Slice)
                      let i470 ← pure ((← get).local272)
                      let i471 ← pure (i470.add 16)
                      let i472 ← Zig.load (Option (Zig.Ptr)) 8 i471
                      let i473 ← pure ((← get).local272)
                      let i474 ← pure (i473.add 8)
                      let i475 ← pure ((← get).local376)
                      let i476 ← Zig.add false i475 p1
                      Zig.store (α := BitVec 64) 8 i474 i476
                      let i478 ← pure ((← get).local272)
                      let i479 ← pure (i478.add 16)
                      let i480 ← pure ((← get).local23)
                      Zig.store (α := Option (Zig.Ptr)) 8 i479 i480
                      let i482 ← pure ((← get).local272)
                      let i483 ← Zig.callC (heap_ArenaAllocator_tryPushNode i12 i482)
                      let i484 ← pure (heap_ArenaAllocator_PushResult.tag i483)
                      match i484 with
                      | .success => (do
                        match ← ((do
                          let i489 ← pure ((← get).local273)
                          let i490 ← pure ((i489).isSome)
                          if i490 then (do
                            let i492 ← Zig.optPayload i489
                            let i493 ← pure (i492.add 16)
                            Zig.store (α := Option (Zig.Ptr)) 8 i493 i472
                            pure .br488)
                          else (do
                            pure .br488)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                        | .br488 => (do
                          match ← ((do
                            let i498 ← pure ((← get).local272)
                            let i499 ← pure ((← get).local270)
                            let i500 ← pure (i498 == i499)
                            if i500 then (do
                              pure (.br497 i472))
                            else (do
                              let i503 ← pure ((← get).local270)
                              ((do
                                let i505 ← pure (i503)
                                pure (.br497 i505)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit))) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                          | .br497 v497 => (do
                            match ← ((do
                              let i508 ← pure ((← get).local272)
                              let i509 ← pure ((← get).local271)
                              let i510 ← pure (i508 == i509)
                              if i510 then (do
                                let i512 ← pure ((← get).local273)
                                pure (.br507 i512))
                              else (do
                                let i514 ← pure ((← get).local271)
                                ((do
                                  let i516 ← pure (i514)
                                  pure (.br507 i516)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit))) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                            | .br507 v507 => (do
                              match ← ((do
                                let i519 ← pure ((v497).isSome)
                                if i519 then (do
                                  let i521 ← Zig.optPayload v497
                                  let i522 ← pure ((v507).isSome)
                                  match ← ((do
                                    if i522 then (do
                                      pure .br523)
                                    else (do
                                      throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                  | .br523 => (do
                                    let i528 ← Zig.optPayload v507
                                    let _i529 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i521 i528)
                                    pure .br518)
                                  | e => pure e)
                                else (do
                                  pure .br518)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                              | .br518 => (do
                                let i532 ← pure ((← get).local376)
                                let i533 ← pure i469.ptr
                                let i534 ← pure (i533.elem 1 i532)
                                let i535 ← Zig.add false i532 p1
                                let i536 ← pure i469.len
                                let i537 ← pure (Zig.le false i535 i536)
                                match ← ((do
                                  if i537 then (do
                                    pure .br538)
                                  else (do
                                    throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                | .br538 => (do
                                  let i543 ← pure (⟨i534, p1⟩ : Zig.Slice)
                                  modify (fun s => { s with local544 := i543 })
                                  let i548 ← pure (((← get).local544).ptr)
                                  match ← ((do
                                    let i550 ← pure ((← get).cur_new_node)
                                    let i551 ← pure ((i550).isSome)
                                    if i551 then (do
                                      let i553 ← Zig.optPayload i550
                                      let i554 ← pure (i553.add 16)
                                      Zig.store (α := Option (Zig.Ptr)) 8 i554 none
                                      let _i556 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i553 i553)
                                      pure .br549)
                                    else (do
                                      pure .br549)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                  | .br549 => (do
                                    let i559 ← pure (i548)
                                    pure (.ret i559))
                                  | e => pure e)
                                | e => pure e)
                              | e => pure e)
                            | e => pure e)
                          | e => pure e)
                        | e => pure e)
                      | .failure => (do
                        let i561 ← Zig.callRC (heap_ArenaAllocator_PushResult.get_failure i483)
                        let i562 ← pure ((← get).local272)
                        let i563 ← pure (i562.add 16)
                        Zig.store (α := Option (Zig.Ptr)) 8 i563 i472
                        let i565 ← pure ((← get).local270)
                        let i566 ← pure ((← get).local271)
                        let _i567 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i565 i566)
                        modify (fun s => { s with cur_first_node := i561 })
                        pure .br22))
                    | e => pure e)
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
        | .br262 => (do
          match ← ((do
            match ← ((do
              let i572 ← pure ((← get).cur_new_node)
              let i573 ← pure ((i572).isSome)
              if i573 then (do
                let i575 ← Zig.optPayload i572
                pure (.br570 i575))
              else (do
                pure .br571)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
            | .br571 => (do
              match ← ((do
                let i579 ← Zig.callRC (mem_Alignment_toByteUnits p2)
                let i580 ← Zig.add false (24 : BitVec 64) i579
                let i581 ← Zig.add false i580 p1
                let i582 ← pure ((← get).local24)
                let i583 ← Zig.add false i582 i581
                let i584 ← Zig.add false i583 (16 : BitVec 64)
                let i585 ← Zig.divTrunc false i584 (2 : BitVec 64)
                let i586 ← Zig.add false i584 i585
                let i587 ← Zig.callRC (mem_alignForward__anon_1 i586 (2 : BitVec 64))
                let i588 ← Zig.callRC (heap_ArenaAllocator_Node_Size_fromInt i587)
                pure (.br578 i588)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
              | .br578 v578 => (do
                match ← ((do
                  let i591 ← pure (i12.add 0)
                  let i592 ← Zig.load (mem_Allocator) 8 i591
                  let i593 ← Zig.callRC (heap_ArenaAllocator_Node_Size_toInt v578)
                  match ← ((do
                    pure .br594) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br594 => (do
                    let i596 ← Zig.callMC Zig.returnAddress
                    match ← ((do
                      let i598 ← pure ((i592).vtable)
                      let i599 ← pure (i598.add 0)
                      let i600 ← Zig.load (Zig.Ptr) 8 i599
                      let i601 ← pure ((i592).ptr)
                      let i602 ← (if i600 == (⟨some 2, 0⟩ : Zig.Ptr) then Zig.callC (heap_PageAllocator_alloc i601 i593 mem_Alignment.«8» i596) else if i600 == (⟨some 6, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_alloc i601 i593 mem_Alignment.«8» i596) else if i600 == (⟨some 10, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_alloc i601 i593 mem_Alignment.«8» i596) else throw .illegal)
                      pure (.br597 i602)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br597 v597 => (do
                      let i604 ← pure ((v597).isSome)
                      if i604 then (do
                        let i606 ← Zig.optPayload v597
                        pure (.br590 i606))
                      else (do
                        match ← ((do
                          let i609 ← pure ((← get).cur_new_node)
                          let i610 ← pure ((i609).isSome)
                          if i610 then (do
                            let i612 ← Zig.optPayload i609
                            let i613 ← pure (i612.add 16)
                            Zig.store (α := Option (Zig.Ptr)) 8 i613 none
                            let _i615 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i612 i612)
                            pure .br608)
                          else (do
                            pure .br608)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                        | .br608 => (do
                          pure (.ret none))
                        | e => pure e))
                    | e => pure e)
                  | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br590 v590 => (do
                  let i619 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr v590)))
                  let i620 ← pure (i619 &&& (7 : BitVec 64))
                  let i621 ← pure (i620 == (0 : BitVec 64))
                  match ← ((do
                    if i621 then (do
                      pure .br622)
                    else (do
                      throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br622 => (do
                    let i627 ← pure (v590)
                    let i628 ← pure (i627.add 0)
                    Zig.store (α := heap_ArenaAllocator_Node_Size) 8 i628 v578
                    let i630 ← pure (i627.add 8)
                    Zig.storeUndef (BitVec 64) 8 i630
                    let i632 ← pure (i627.add 16)
                    Zig.storeUndef (Option (Zig.Ptr)) 8 i632
                    let i634 ← pure (i627)
                    modify (fun s => { s with cur_new_node := i634 })
                    pure (.br570 i627))
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
          | .br570 v570 => (do
            let i637 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe v570)
            let i638 ← pure i637.ptr
            let i639 ← pure (i638.elem 1 (24 : BitVec 64))
            let i640 ← pure i637.len
            let i641 ← pure (Zig.le false (24 : BitVec 64) i640)
            match ← ((do
              if i641 then (do
                pure .br642)
              else (do
                throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
            | .br642 => (do
              let i647 ← Zig.sub false i640 (24 : BitVec 64)
              let i648 ← pure i637.len
              let i649 ← pure (Zig.le false i640 i648)
              match ← ((do
                if i649 then (do
                  pure .br650)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
              | .br650 => (do
                let i655 ← pure (⟨i639, i647⟩ : Zig.Slice)
                modify (fun s => { s with local656 := i655 })
                let i660 ← pure (((← get).local656).ptr)
                let i661 ← Zig.callMC (heap_ArenaAllocator_alignedIndex i660 (0 : BitVec 64) p2)
                let i662 ← pure (v570.add 0)
                let i663 ← Zig.load (heap_ArenaAllocator_Node_Size) 8 i662
                let i664 ← Zig.callRC (heap_ArenaAllocator_Node_Size_toInt i663)
                let i665 ← Zig.add false (24 : BitVec 64) i661
                let i666 ← Zig.add false i665 p1
                let i667 ← pure (i664)
                let i668 ← pure (i666)
                let i669 ← pure (Zig.ge false i667 i668)
                let _i670 ← Zig.callRC (debug_assert i669)
                let i671 ← pure (v570.add 8)
                let i672 ← Zig.add false i661 p1
                Zig.store (α := BitVec 64) 8 i671 i672
                let i674 ← pure (v570.add 16)
                let i675 ← pure ((← get).local23)
                Zig.store (α := Option (Zig.Ptr)) 8 i674 i675
                let i677 ← Zig.callC (heap_ArenaAllocator_tryPushNode i12 v570)
                let i678 ← pure (heap_ArenaAllocator_PushResult.tag i677)
                match ← ((do
                  match i678 with
                  | .success => (do
                    modify (fun s => { s with cur_new_node := none })
                    let i684 ← pure ((← get).local656)
                    let i685 ← pure i684.ptr
                    let i686 ← pure (i685.elem 1 i661)
                    let i687 ← Zig.add false i661 p1
                    let i688 ← pure i684.len
                    let i689 ← pure (Zig.le false i687 i688)
                    match ← ((do
                      if i689 then (do
                        pure .br690)
                      else (do
                        throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br690 => (do
                      let i695 ← pure (⟨i686, p1⟩ : Zig.Slice)
                      modify (fun s => { s with local696 := i695 })
                      let i700 ← pure (((← get).local696).ptr)
                      match ← ((do
                        let i702 ← pure ((← get).cur_new_node)
                        let i703 ← pure ((i702).isSome)
                        if i703 then (do
                          let i705 ← Zig.optPayload i702
                          let i706 ← pure (i705.add 16)
                          Zig.store (α := Option (Zig.Ptr)) 8 i706 none
                          let _i708 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i705 i705)
                          pure .br701)
                        else (do
                          pure .br701)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                      | .br701 => (do
                        let i711 ← pure (i700)
                        pure (.ret i711))
                      | e => pure e)
                    | e => pure e)
                  | .failure => (do
                    let i713 ← Zig.callRC (heap_ArenaAllocator_PushResult.get_failure i677)
                    modify (fun s => { s with cur_first_node := i713 })
                    pure .br679)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br679 => (do
                  pure .br22)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
  | .br22 => (do
    pure .rep21)
  | e => pure e
partial_fixpoint

def heap_ArenaAllocator_alloc (p0 : Zig.Ptr) (p1 : BitVec 64) (p2 : mem_Alignment) (p3 : BitVec 64) : Zig.ConcM Tgt (Option (Zig.Ptr)) := do
  let e ← ((do
    let i4 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
    let i5 ← pure (i4 &&& (7 : BitVec 64))
    let i6 ← pure (i5 == (0 : BitVec 64))
    match ← ((do
      if i6 then (do
        pure .br7)
      else (do
        throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
    | .br7 => (do
      let i12 ← pure (p0)
      let i13 ← pure (p1)
      let i14 ← pure (Zig.gt false i13 (0 : BitVec 64))
      let _i15 ← Zig.callRC (debug_assert i14)
      let i17 ← Zig.callC (heap_ArenaAllocator_loadFirstNode i12)
      modify (fun s => { s with cur_first_node := i17 })
      modify (fun s => { s with cur_new_node := none })
      Zig.loop (heap_ArenaAllocator_alloc.loop21 p1 p2 i12) heap_ArenaAllocator_alloc.again21)
    | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit).run' (default : heap_ArenaAllocator_allocLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic
partial_fixpoint

end

structure mem_Allocator_allocBytesWithAlignment__anon_1Locals where
  deriving Inhabited

inductive mem_Allocator_allocBytesWithAlignment__anon_1Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3
  | br10 (v : Option (Zig.Ptr))
  | br9 (v : Zig.Ptr)
  | br30

def mem_Allocator_allocBytesWithAlignment__anon_1 (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (⟨none, 18446744073709551608⟩ : Zig.Ptr) : Except Zig.ErrName (Zig.Ptr))))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_1Locals mem_Allocator_allocBytesWithAlignment__anon_1Exit) with
    | .br3 => (do
      match ← ((do
        match ← ((do
          let i11 ← pure ((p0).vtable)
          let i12 ← pure (i11.add 0)
          let i13 ← Zig.load (Zig.Ptr) 8 i12
          let i14 ← pure ((p0).ptr)
          let i15 ← (if i13 == (⟨some 2, 0⟩ : Zig.Ptr) then Zig.callC (heap_PageAllocator_alloc i14 p1 mem_Alignment.«8» p2) else if i13 == (⟨some 6, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_alloc i14 p1 mem_Alignment.«8» p2) else if i13 == (⟨some 10, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_alloc i14 p1 mem_Alignment.«8» p2) else throw .illegal)
          pure (.br10 i15)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_1Locals mem_Allocator_allocBytesWithAlignment__anon_1Exit) with
        | .br10 v10 => (do
          let i17 ← pure ((v10).isSome)
          if i17 then (do
            let i19 ← Zig.optPayload v10
            pure (.br9 i19))
          else (do
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr)))))
        | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_1Locals mem_Allocator_allocBytesWithAlignment__anon_1Exit) with
      | .br9 v9 => (do
        let i22 ← pure (v9.elem 1 (0 : BitVec 64))
        let i23 ← Zig.sub false p1 (0 : BitVec 64)
        let i24 ← pure (⟨i22, i23⟩ : Zig.Slice)
        let _i25 ← pure i24.len
        Zig.callMC (Zig.memset (α := BitVec 8) 1 i24.ptr i24.len none)
        let i27 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr v9)))
        let i28 ← pure (i27 &&& (7 : BitVec 64))
        let i29 ← pure (i28 == (0 : BitVec 64))
        match ← ((do
          if i29 then (do
            pure .br30)
          else (do
            throw .panic)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_1Locals mem_Allocator_allocBytesWithAlignment__anon_1Exit) with
        | .br30 => (do
          let i35 ← pure (v9)
          let i36 ← pure ((.ok i35) : Except Zig.ErrName (Zig.Ptr))
          pure (.ret i36))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_1Locals mem_Allocator_allocBytesWithAlignment__anon_1Exit).run' (default : mem_Allocator_allocBytesWithAlignment__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_create__anon_1Locals where
  deriving Inhabited

inductive mem_Allocator_create__anon_1Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

def mem_Allocator_create__anon_1 (p0 : mem_Allocator) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    let i1 ← Zig.callMC Zig.returnAddress
    let i2 ← Zig.callC (mem_Allocator_allocBytesWithAlignment__anon_1 p0 (8 : BitVec 64) i1)
    match i2 with
    | .error _ => (do
      let i4 ← Zig.callRC (Zig.unwrapErr i2)
      let i5 ← pure ((.error i4) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i5))
    | .ok v3 => (do
      let i7 ← pure (v3)
      let i8 ← pure ((.ok i7) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i8))) : Zig.CM Tgt mem_Allocator_create__anon_1Locals mem_Allocator_create__anon_1Exit).run' (default : mem_Allocator_create__anon_1Locals)
  match e with
  | .ret v => pure v

structure heap_ArenaAllocator_deinitLocals where
  local1 : BitVec 64
  it : Option (Zig.Ptr)
  deriving Inhabited

inductive heap_ArenaAllocator_deinitExit where
  | ret
  | br30
  | br33
  | br20
  | br18
  | br11
  | br8
  | rep19
  | rep9

def heap_ArenaAllocator_deinit.again19 : heap_ArenaAllocator_deinitExit → Bool
  | .rep19 => true
  | _ => false

def heap_ArenaAllocator_deinit.again9 : heap_ArenaAllocator_deinitExit → Bool
  | .rep9 => true
  | _ => false

def heap_ArenaAllocator_deinit.loop19 (p0 : heap_ArenaAllocator) : Zig.CM Tgt heap_ArenaAllocator_deinitLocals heap_ArenaAllocator_deinitExit := do
  match ← ((do
    let i21 ← pure ((← get).it)
    let i22 ← pure ((i21).isSome)
    if i22 then (do
      let i24 ← Zig.optPayload i21
      let i25 ← pure (i24.add 16)
      let i26 ← Zig.load (Option (Zig.Ptr)) 8 i25
      modify (fun s => { s with it := i26 })
      let i28 ← pure ((p0).child_allocator)
      let i29 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe i24)
      match ← ((do
        pure .br30) : Zig.CM Tgt heap_ArenaAllocator_deinitLocals heap_ArenaAllocator_deinitExit) with
      | .br30 => (do
        let i32 ← Zig.callMC Zig.returnAddress
        match ← ((do
          let i34 ← pure ((i28).vtable)
          let i35 ← pure (i34.add 24)
          let i36 ← Zig.load (Zig.Ptr) 8 i35
          let i37 ← pure ((i28).ptr)
          let _i38 ← (if i36 == (⟨some 5, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_free i37 i29 mem_Alignment.«8» i32) else if i36 == (⟨some 9, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_free i37 i29 mem_Alignment.«8» i32) else if i36 == (⟨some 13, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_free i37 i29 mem_Alignment.«8» i32) else throw .illegal)
          pure .br33) : Zig.CM Tgt heap_ArenaAllocator_deinitLocals heap_ArenaAllocator_deinitExit) with
        | .br33 => (do
          pure .br20)
        | e => pure e)
      | e => pure e)
    else (do
      pure .br18)) : Zig.CM Tgt heap_ArenaAllocator_deinitLocals heap_ArenaAllocator_deinitExit) with
  | .br20 => (do
    pure .rep19)
  | e => pure e

def heap_ArenaAllocator_deinit.loop9 (p0 : heap_ArenaAllocator) (i7 : Vector (Option (Zig.Ptr)) 2) : Zig.CM Tgt heap_ArenaAllocator_deinitLocals heap_ArenaAllocator_deinitExit := do
  let i10 ← pure ((← get).local1)
  match ← ((do
    let i12 ← pure (i10)
    let i13 ← pure (Zig.lt false i12 (2 : BitVec 64))
    if i13 then (do
      let i15 ← Zig.callRC (Zig.vindex i7 i10)
      modify (fun s => { s with it := i15 })
      match ← ((do
        Zig.loop (heap_ArenaAllocator_deinit.loop19 p0) heap_ArenaAllocator_deinit.again19) : Zig.CM Tgt heap_ArenaAllocator_deinitLocals heap_ArenaAllocator_deinitExit) with
      | .br18 => (do
        pure .br11)
      | e => pure e)
    else (do
      pure .br8)) : Zig.CM Tgt heap_ArenaAllocator_deinitLocals heap_ArenaAllocator_deinitExit) with
  | .br11 => (do
    let i45 ← Zig.add false i10 (1 : BitVec 64)
    modify (fun s => { s with local1 := i45 })
    pure .rep9)
  | e => pure e

def heap_ArenaAllocator_deinit (p0 : heap_ArenaAllocator) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    modify (fun s => { s with local1 := (0 : BitVec 64) })
    let i3 ← pure ((p0).state)
    let i4 ← pure ((i3).used_list)
    let i5 ← pure ((p0).state)
    let i6 ← pure ((i5).free_list)
    let i7 ← pure (#v[i4, i6] : Vector (Option (Zig.Ptr)) 2)
    match ← ((do
      Zig.loop (heap_ArenaAllocator_deinit.loop9 p0 i7) heap_ArenaAllocator_deinit.again9) : Zig.CM Tgt heap_ArenaAllocator_deinitLocals heap_ArenaAllocator_deinitExit) with
    | .br8 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_deinitLocals heap_ArenaAllocator_deinitExit).run' (default : heap_ArenaAllocator_deinitLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure math_mul__anon_1Locals where
  deriving Inhabited

inductive math_mul__anon_1Exit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br3

def math_mul__anon_1 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← pure (Zig.mulWithOverflow false p0 p1)
    match ← ((do
      let i4 ← pure ((i2).2)
      let i5 ← pure (i4 != (0 : BitVec 1))
      if i5 then (do
        pure (.ret (.error "Overflow" : Except Zig.ErrName (BitVec 64))))
      else (do
        pure .br3)) : Zig.M math_mul__anon_1Locals math_mul__anon_1Exit) with
    | .br3 => (do
      let i9 ← pure ((i2).1)
      let i10 ← pure ((.ok i9) : Except Zig.ErrName (BitVec 64))
      pure (.ret i10))
    | e => pure e) : Zig.M math_mul__anon_1Locals math_mul__anon_1Exit).run' (default : math_mul__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_allocBytesWithAlignment__anon_2Locals where
  deriving Inhabited

inductive mem_Allocator_allocBytesWithAlignment__anon_2Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3
  | br10 (v : Option (Zig.Ptr))
  | br9 (v : Zig.Ptr)

def mem_Allocator_allocBytesWithAlignment__anon_2 (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (⟨none, 18446744073709551615⟩ : Zig.Ptr) : Except Zig.ErrName (Zig.Ptr))))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_2Locals mem_Allocator_allocBytesWithAlignment__anon_2Exit) with
    | .br3 => (do
      match ← ((do
        match ← ((do
          let i11 ← pure ((p0).vtable)
          let i12 ← pure (i11.add 0)
          let i13 ← Zig.load (Zig.Ptr) 8 i12
          let i14 ← pure ((p0).ptr)
          let i15 ← (if i13 == (⟨some 2, 0⟩ : Zig.Ptr) then Zig.callC (heap_PageAllocator_alloc i14 p1 mem_Alignment.«1» p2) else if i13 == (⟨some 6, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_alloc i14 p1 mem_Alignment.«1» p2) else if i13 == (⟨some 10, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_alloc i14 p1 mem_Alignment.«1» p2) else throw .illegal)
          pure (.br10 i15)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_2Locals mem_Allocator_allocBytesWithAlignment__anon_2Exit) with
        | .br10 v10 => (do
          let i17 ← pure ((v10).isSome)
          if i17 then (do
            let i19 ← Zig.optPayload v10
            pure (.br9 i19))
          else (do
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr)))))
        | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_2Locals mem_Allocator_allocBytesWithAlignment__anon_2Exit) with
      | .br9 v9 => (do
        let i22 ← pure (v9.elem 1 (0 : BitVec 64))
        let i23 ← Zig.sub false p1 (0 : BitVec 64)
        let i24 ← pure (⟨i22, i23⟩ : Zig.Slice)
        let _i25 ← pure i24.len
        Zig.callMC (Zig.memset (α := BitVec 8) 1 i24.ptr i24.len none)
        let i27 ← pure (v9)
        let i28 ← pure ((.ok i27) : Except Zig.ErrName (Zig.Ptr))
        pure (.ret i28))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_2Locals mem_Allocator_allocBytesWithAlignment__anon_2Exit).run' (default : mem_Allocator_allocBytesWithAlignment__anon_2Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_allocWithSizeAndAlignment__anon_1Locals where
  deriving Inhabited

inductive mem_Allocator_allocWithSizeAndAlignment__anon_1Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3 (v : BitVec 64)

def mem_Allocator_allocWithSizeAndAlignment__anon_1 (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.callRC (math_mul__anon_1 (1 : BitVec 64) p1)
      let i5 ← pure (Zig.isNonErr i4)
      if i5 then (do
        let i7 ← Zig.callRC (Zig.unwrapPayload i4)
        pure (.br3 i7))
      else (do
        let _i9 ← Zig.callRC (Zig.unwrapErr i4)
        pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr))))) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_1Locals mem_Allocator_allocWithSizeAndAlignment__anon_1Exit) with
    | .br3 v3 => (do
      let i11 ← Zig.callC (mem_Allocator_allocBytesWithAlignment__anon_2 p0 v3 p2)
      pure (.ret i11))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_1Locals mem_Allocator_allocWithSizeAndAlignment__anon_1Exit).run' (default : mem_Allocator_allocWithSizeAndAlignment__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_alloc__anon_1Locals where
  deriving Inhabited

inductive mem_Allocator_alloc__anon_1Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br3 (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_alloc__anon_1 (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.callMC Zig.returnAddress
    match ← ((do
      let i4 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_1 p0 p1 i2)
      match i4 with
      | .error _ => (do
        let i6 ← Zig.callRC (Zig.unwrapErr i4)
        let i7 ← pure ((.error i6) : Except Zig.ErrName (Zig.Slice))
        pure (.br3 i7))
      | .ok v5 => (do
        let i9 ← pure (v5.elem 1 (0 : BitVec 64))
        let i10 ← Zig.sub false p1 (0 : BitVec 64)
        let i11 ← pure (⟨i9, i10⟩ : Zig.Slice)
        let i12 ← pure ((.ok i11) : Except Zig.ErrName (Zig.Slice))
        pure (.br3 i12))) : Zig.CM Tgt mem_Allocator_alloc__anon_1Locals mem_Allocator_alloc__anon_1Exit) with
    | .br3 v3 => (do
      let i14 ← pure (v3)
      pure (.ret i14))
    | e => pure e) : Zig.CM Tgt mem_Allocator_alloc__anon_1Locals mem_Allocator_alloc__anon_1Exit).run' (default : mem_Allocator_alloc__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure arena_pageLocals where
  arena : Zig.Ptr
  deriving Inhabited

inductive arena_pageExit where
  | ret (v : BitVec 64)
  | br5 (v : Zig.Ptr)
  | br17 (v : Zig.Slice)
  | br32

def arena_page (p0 : BitVec 64) : Zig.ConcM Tgt (BitVec 64) := do
  let s1 ← Zig.allocStack 32 8
  let e ← ((do
    let i1 ← pure (← get).arena
    let i2 ← Zig.callMC (heap_ArenaAllocator_init ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 0, 0⟩ : Zig.Ptr) } : mem_Allocator))
    Zig.store (α := heap_ArenaAllocator) 8 i1 i2
    let i4 ← Zig.callMC (heap_ArenaAllocator_allocator i1)
    match ← ((do
      let i6 ← Zig.callC (mem_Allocator_create__anon_1 i4)
      let i7 ← pure (Zig.isNonErr i6)
      if i7 then (do
        let i9 ← Zig.callRC (Zig.unwrapPayload i6)
        pure (.br5 i9))
      else (do
        let _i11 ← Zig.callRC (Zig.unwrapErr i6)
        let i12 ← Zig.load (heap_ArenaAllocator) 8 i1
        let _i13 ← Zig.callC (heap_ArenaAllocator_deinit i12)
        pure (.ret (0 : BitVec 64)))) : Zig.CM Tgt arena_pageLocals arena_pageExit) with
    | .br5 v5 => (do
      let i15 ← pure (p0)
      Zig.store (α := BitVec 64) 8 v5 i15
      match ← ((do
        let i18 ← Zig.callC (mem_Allocator_alloc__anon_1 i4 p0)
        let i19 ← pure (Zig.isNonErr i18)
        if i19 then (do
          let i21 ← Zig.callRC (Zig.unwrapPayload i18)
          pure (.br17 i21))
        else (do
          let _i23 ← Zig.callRC (Zig.unwrapErr i18)
          let i24 ← Zig.load (heap_ArenaAllocator) 8 i1
          let _i25 ← Zig.callC (heap_ArenaAllocator_deinit i24)
          pure (.ret (1 : BitVec 64)))) : Zig.CM Tgt arena_pageLocals arena_pageExit) with
      | .br17 v17 => (do
        let _i27 ← pure v17.len
        Zig.callMC (Zig.memset (α := BitVec 8) 1 v17.ptr v17.len (some (2 : BitVec 8)))
        let i29 ← Zig.load (BitVec 64) 8 v5
        let i30 ← pure v17.len
        let i31 ← pure (Zig.lt false (0 : BitVec 64) i30)
        match ← ((do
          if i31 then (do
            pure .br32)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt arena_pageLocals arena_pageExit) with
        | .br32 => (do
          let i37 ← Zig.callMC (Zig.load (BitVec 8) 1 (v17.ptr.elem 1 (0 : BitVec 64)))
          let i38 ← Zig.intCast false false 64 i37
          let i39 ← Zig.add false i29 i38
          let i40 ← Zig.load (heap_ArenaAllocator) 8 i1
          let _i41 ← Zig.callC (heap_ArenaAllocator_deinit i40)
          pure (.ret i39))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt arena_pageLocals arena_pageExit).run' { (default : arena_pageLocals) with arena := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heap_FixedBufferAllocator_initLocals where
  local1 : heap_FixedBufferAllocator
  deriving Inhabited

inductive heap_FixedBufferAllocator_initExit where
  | ret (v : heap_FixedBufferAllocator)

def heap_FixedBufferAllocator_init (p0 : Zig.Slice) : Zig.MemM (heap_FixedBufferAllocator) := do
  let e ← ((do
    modify (fun s => { s with local1 := { s.local1 with buffer := p0 } })
    modify (fun s => { s with local1 := { s.local1 with end_index := (0 : BitVec 64) } })
    pure (.ret (← get).local1)) : Zig.MM heap_FixedBufferAllocator_initLocals heap_FixedBufferAllocator_initExit).run' (default : heap_FixedBufferAllocator_initLocals)
  match e with
  | .ret v => pure v

structure heap_FixedBufferAllocator_allocatorLocals where
  local1 : mem_Allocator
  deriving Inhabited

inductive heap_FixedBufferAllocator_allocatorExit where
  | ret (v : mem_Allocator)

def heap_FixedBufferAllocator_allocator (p0 : Zig.Ptr) : Zig.MemM (mem_Allocator) := do
  let e ← ((do
    let i3 ← pure (p0)
    modify (fun s => { s with local1 := { s.local1 with ptr := i3 } })
    modify (fun s => { s with local1 := { s.local1 with vtable := (⟨some 16, 0⟩ : Zig.Ptr) } })
    pure (.ret (← get).local1)) : Zig.MM heap_FixedBufferAllocator_allocatorLocals heap_FixedBufferAllocator_allocatorExit).run' (default : heap_FixedBufferAllocator_allocatorLocals)
  match e with
  | .ret v => pure v

structure heap_ArenaAllocator_countListCapacityLocals where
  capacity : BitVec 64
  it : Option (Zig.Ptr)
  deriving Inhabited

inductive heap_ArenaAllocator_countListCapacityExit where
  | ret (v : BitVec 64)
  | br7
  | br5
  | rep6

def heap_ArenaAllocator_countListCapacity.again6 : heap_ArenaAllocator_countListCapacityExit → Bool
  | .rep6 => true
  | _ => false

def heap_ArenaAllocator_countListCapacity.loop6  : Zig.MM heap_ArenaAllocator_countListCapacityLocals heap_ArenaAllocator_countListCapacityExit := do
  match ← ((do
    let i8 ← pure ((← get).it)
    let i9 ← pure ((i8).isSome)
    if i9 then (do
      let i11 ← Zig.optPayload i8
      let i12 ← pure ((← get).capacity)
      let i13 ← pure (i11.add 0)
      let i14 ← Zig.load (heap_ArenaAllocator_Node_Size) 8 i13
      let i15 ← Zig.callR (heap_ArenaAllocator_Node_Size_toInt i14)
      let i16 ← Zig.sub false i15 (24 : BitVec 64)
      let i17 ← Zig.add false i12 i16
      modify (fun s => { s with capacity := i17 })
      let i19 ← pure (i11.add 16)
      let i20 ← Zig.load (Option (Zig.Ptr)) 8 i19
      modify (fun s => { s with it := i20 })
      pure .br7)
    else (do
      pure .br5)) : Zig.MM heap_ArenaAllocator_countListCapacityLocals heap_ArenaAllocator_countListCapacityExit) with
  | .br7 => (do
    pure .rep6)
  | e => pure e

def heap_ArenaAllocator_countListCapacity (p0 : Option (Zig.Ptr)) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with capacity := (0 : BitVec 64) })
    modify (fun s => { s with it := p0 })
    match ← ((do
      Zig.loop (heap_ArenaAllocator_countListCapacity.loop6 ) heap_ArenaAllocator_countListCapacity.again6) : Zig.MM heap_ArenaAllocator_countListCapacityLocals heap_ArenaAllocator_countListCapacityExit) with
    | .br5 => (do
      let i25 ← pure ((← get).capacity)
      pure (.ret i25))
    | e => pure e) : Zig.MM heap_ArenaAllocator_countListCapacityLocals heap_ArenaAllocator_countListCapacityExit).run' (default : heap_ArenaAllocator_countListCapacityLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heap_ArenaAllocator_resetLocals where
  ok : Bool
  local55 : BitVec 64
  it : Option (Zig.Ptr)
  deriving Inhabited

inductive heap_ArenaAllocator_resetExit where
  | ret (v : Bool)
  | br3 (v : Option (BitVec 64))
  | br12
  | br29 (v : BitVec 64)
  | br40 (v : BitVec 64)
  | br77 (v : Zig.Ptr)
  | br87
  | br96
  | br99
  | br79
  | br68
  | br118
  | br121
  | br112
  | br135
  | br146
  | br149 (v : Bool)
  | br143
  | br164
  | br167 (v : Option (Zig.Ptr))
  | br161 (v : Zig.Ptr)
  | br182
  | br185
  | br195
  | br65
  | rep78
  | rep66

def heap_ArenaAllocator_reset.again78 : heap_ArenaAllocator_resetExit → Bool
  | .rep78 => true
  | _ => false

def heap_ArenaAllocator_reset.again66 : heap_ArenaAllocator_resetExit → Bool
  | .rep66 => true
  | _ => false

def heap_ArenaAllocator_reset.loop78 (p0 : Zig.Ptr) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit := do
  match ← ((do
    let i80 ← pure ((← get).it)
    let i81 ← pure ((i80).isSome)
    if i81 then (do
      let i83 ← Zig.optPayload i80
      let i84 ← pure (i83.add 16)
      let i85 ← Zig.load (Option (Zig.Ptr)) 8 i84
      modify (fun s => { s with it := i85 })
      match ← ((do
        let i88 ← pure ((← get).it)
        let i89 ← pure ((i88).isNone)
        if i89 then (do
          pure (.br77 i83))
        else (do
          pure .br87)) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
      | .br87 => (do
        let i93 ← pure (p0.add 0)
        let i94 ← Zig.load (mem_Allocator) 8 i93
        let i95 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe i83)
        match ← ((do
          pure .br96) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
        | .br96 => (do
          let i98 ← Zig.callMC Zig.returnAddress
          match ← ((do
            let i100 ← pure ((i94).vtable)
            let i101 ← pure (i100.add 24)
            let i102 ← Zig.load (Zig.Ptr) 8 i101
            let i103 ← pure ((i94).ptr)
            let _i104 ← (if i102 == (⟨some 5, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_free i103 i95 mem_Alignment.«8» i98) else if i102 == (⟨some 9, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_free i103 i95 mem_Alignment.«8» i98) else if i102 == (⟨some 13, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_free i103 i95 mem_Alignment.«8» i98) else throw .illegal)
            pure .br99) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
          | .br99 => (do
            pure .br79)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    else (do
      pure .br68)) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
  | .br79 => (do
    pure .rep78)
  | e => pure e

def heap_ArenaAllocator_reset.loop66 (p0 : Zig.Ptr) (i61 : Vector (Zig.Ptr) 2) (i64 : Vector (BitVec 64) 2) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit := do
  let i67 ← pure ((← get).local55)
  match ← ((do
    let i69 ← pure (i67)
    let i70 ← pure (Zig.lt false i69 (2 : BitVec 64))
    if i70 then (do
      let i72 ← Zig.callRC (Zig.vindex i61 i67)
      let i73 ← Zig.callRC (Zig.vindex i64 i67)
      let i75 ← Zig.load (Option (Zig.Ptr)) 8 i72
      modify (fun s => { s with it := i75 })
      match ← ((do
        Zig.loop (heap_ArenaAllocator_reset.loop78 p0) heap_ArenaAllocator_reset.again78) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
      | .br77 v77 => (do
        let i109 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe v77)
        let i110 ← Zig.add false (24 : BitVec 64) i73
        let i111 ← Zig.callRC (mem_alignBackward__anon_1 i110 (2 : BitVec 64))
        match ← ((do
          let i113 ← pure (i111)
          let i114 ← pure (i113 == (24 : BitVec 64))
          if i114 then (do
            let i116 ← pure (p0.add 0)
            let i117 ← Zig.load (mem_Allocator) 8 i116
            match ← ((do
              pure .br118) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
            | .br118 => (do
              let i120 ← Zig.callMC Zig.returnAddress
              match ← ((do
                let i122 ← pure ((i117).vtable)
                let i123 ← pure (i122.add 24)
                let i124 ← Zig.load (Zig.Ptr) 8 i123
                let i125 ← pure ((i117).ptr)
                let _i126 ← (if i124 == (⟨some 5, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_free i125 i109 mem_Alignment.«8» i120) else if i124 == (⟨some 9, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_free i125 i109 mem_Alignment.«8» i120) else if i124 == (⟨some 13, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_free i125 i109 mem_Alignment.«8» i120) else throw .illegal)
                pure .br121) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
              | .br121 => (do
                Zig.store (α := Option (Zig.Ptr)) 8 i72 none
                pure .br68)
              | e => pure e)
            | e => pure e)
          else (do
            pure .br112)) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
        | .br112 => (do
          let i131 ← pure (v77.add 8)
          Zig.store (α := BitVec 64) 8 i131 (0 : BitVec 64)
          let i133 ← pure (v77)
          Zig.store (α := Option (Zig.Ptr)) 8 i72 i133
          match ← ((do
            let i136 ← pure i109.len
            let i137 ← pure (i136)
            let i138 ← pure (i111)
            let i139 ← pure (i137 == i138)
            if i139 then (do
              pure .br68)
            else (do
              pure .br135)) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
          | .br135 => (do
            match ← ((do
              let i144 ← pure (p0.add 0)
              let i145 ← Zig.load (mem_Allocator) 8 i144
              match ← ((do
                pure .br146) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
              | .br146 => (do
                let i148 ← Zig.callMC Zig.returnAddress
                match ← ((do
                  let i150 ← pure ((i145).vtable)
                  let i151 ← pure (i150.add 8)
                  let i152 ← Zig.load (Zig.Ptr) 8 i151
                  let i153 ← pure ((i145).ptr)
                  let i154 ← (if i152 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_resize i153 i109 mem_Alignment.«8» i111 i148) else if i152 == (⟨some 7, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_resize i153 i109 mem_Alignment.«8» i111 i148) else if i152 == (⟨some 11, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_resize i153 i109 mem_Alignment.«8» i111 i148) else throw .illegal)
                  pure (.br149 i154)) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
                | .br149 v149 => (do
                  if v149 then (do
                    let i157 ← pure (v77.add 0)
                    let i158 ← Zig.callRC (heap_ArenaAllocator_Node_Size_fromInt i111)
                    Zig.store (α := heap_ArenaAllocator_Node_Size) 8 i157 i158
                    pure .br143)
                  else (do
                    match ← ((do
                      let i162 ← pure (p0.add 0)
                      let i163 ← Zig.load (mem_Allocator) 8 i162
                      match ← ((do
                        pure .br164) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
                      | .br164 => (do
                        let i166 ← Zig.callMC Zig.returnAddress
                        match ← ((do
                          let i168 ← pure ((i163).vtable)
                          let i169 ← pure (i168.add 0)
                          let i170 ← Zig.load (Zig.Ptr) 8 i169
                          let i171 ← pure ((i163).ptr)
                          let i172 ← (if i170 == (⟨some 2, 0⟩ : Zig.Ptr) then Zig.callC (heap_PageAllocator_alloc i171 i111 mem_Alignment.«8» i166) else if i170 == (⟨some 6, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_alloc i171 i111 mem_Alignment.«8» i166) else if i170 == (⟨some 10, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_alloc i171 i111 mem_Alignment.«8» i166) else throw .illegal)
                          pure (.br167 i172)) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
                        | .br167 v167 => (do
                          let i174 ← pure ((v167).isSome)
                          if i174 then (do
                            let i176 ← Zig.optPayload v167
                            pure (.br161 i176))
                          else (do
                            modify (fun s => { s with ok := false })
                            pure .br68))
                        | e => pure e)
                      | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
                    | .br161 v161 => (do
                      let i180 ← pure (p0.add 0)
                      let i181 ← Zig.load (mem_Allocator) 8 i180
                      match ← ((do
                        pure .br182) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
                      | .br182 => (do
                        let i184 ← Zig.callMC Zig.returnAddress
                        match ← ((do
                          let i186 ← pure ((i181).vtable)
                          let i187 ← pure (i186.add 24)
                          let i188 ← Zig.load (Zig.Ptr) 8 i187
                          let i189 ← pure ((i181).ptr)
                          let _i190 ← (if i188 == (⟨some 5, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_free i189 i109 mem_Alignment.«8» i184) else if i188 == (⟨some 9, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_free i189 i109 mem_Alignment.«8» i184) else if i188 == (⟨some 13, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_free i189 i109 mem_Alignment.«8» i184) else throw .illegal)
                          pure .br185) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
                        | .br185 => (do
                          let i192 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr v161)))
                          let i193 ← pure (i192 &&& (7 : BitVec 64))
                          let i194 ← pure (i193 == (0 : BitVec 64))
                          match ← ((do
                            if i194 then (do
                              pure .br195)
                            else (do
                              throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
                          | .br195 => (do
                            let i200 ← pure (v161)
                            let i201 ← pure (i200.add 0)
                            let i202 ← Zig.callRC (heap_ArenaAllocator_Node_Size_fromInt i111)
                            Zig.store (α := heap_ArenaAllocator_Node_Size) 8 i201 i202
                            let i204 ← pure (i200.add 8)
                            Zig.store (α := BitVec 64) 8 i204 (0 : BitVec 64)
                            let i206 ← pure (i200.add 16)
                            Zig.store (α := Option (Zig.Ptr)) 8 i206 none
                            let i208 ← pure (i200)
                            Zig.store (α := Option (Zig.Ptr)) 8 i72 i208
                            pure .br143)
                          | e => pure e)
                        | e => pure e)
                      | e => pure e)
                    | e => pure e))
                | e => pure e)
              | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
            | .br143 => (do
              pure .br68)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    else (do
      pure .br65)) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
  | .br68 => (do
    let i213 ← Zig.add false i67 (1 : BitVec 64)
    modify (fun s => { s with local55 := i213 })
    pure .rep66)
  | e => pure e

def heap_ArenaAllocator_reset (p0 : Zig.Ptr) (p1 : heap_ArenaAllocator_ResetMode) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    let i2 ← pure (heap_ArenaAllocator_ResetMode.tag p1)
    match ← ((do
      match i2 with
      | .retain_capacity => (do
        pure (.br3 none))
      | .retain_with_limit => (do
        let i8 ← Zig.callRC (heap_ArenaAllocator_ResetMode.get_retain_with_limit p1)
        let i9 ← pure (some i8)
        pure (.br3 i9))
      | .free_all => (do
        pure (.br3 (some (0 : BitVec 64))))) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
    | .br3 v3 => (do
      match ← ((do
        let i13 ← pure (v3 == (some (0 : BitVec 64)))
        if i13 then (do
          let i15 ← Zig.load (heap_ArenaAllocator) 8 p0
          let _i16 ← Zig.callC (heap_ArenaAllocator_deinit i15)
          let i17 ← pure (p0.add 16)
          Zig.store (α := heap_ArenaAllocator_State) 8 i17 ({ used_list := none, free_list := none } : heap_ArenaAllocator_State)
          pure (.ret true))
        else (do
          pure .br12)) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
      | .br12 => (do
        let i21 ← pure (p0.add 16)
        let i22 ← pure (i21.add 0)
        let i23 ← Zig.load (Option (Zig.Ptr)) 8 i22
        let i24 ← Zig.callMC (heap_ArenaAllocator_countListCapacity i23)
        let i25 ← pure (p0.add 16)
        let i26 ← pure (i25.add 8)
        let i27 ← Zig.load (Option (Zig.Ptr)) 8 i26
        let i28 ← Zig.callMC (heap_ArenaAllocator_countListCapacity i27)
        match ← ((do
          let i30 ← pure ((v3).isSome)
          if i30 then (do
            let i32 ← Zig.optPayload v3
            let i33 ← pure (i32)
            let i34 ← pure (i24)
            let i35 ← pure (Zig.min false i33 i34)
            pure (.br29 i35))
          else (do
            ((do
              let i38 ← pure (i24)
              pure (.br29 i38)) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit))) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
        | .br29 v29 => (do
          match ← ((do
            let i41 ← pure ((v3).isSome)
            if i41 then (do
              let i43 ← Zig.optPayload v3
              let i44 ← pure (v29)
              let i45 ← Zig.sub false i43 i44
              let i46 ← pure (i45)
              let i47 ← pure (i28)
              let i48 ← pure (Zig.min false i46 i47)
              pure (.br40 i48))
            else (do
              ((do
                let i51 ← pure (i28)
                pure (.br40 i51)) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit))) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
          | .br40 v40 => (do
            modify (fun s => { s with ok := true })
            modify (fun s => { s with local55 := (0 : BitVec 64) })
            let i57 ← pure (p0.add 16)
            let i58 ← pure (i57.add 0)
            let i59 ← pure (p0.add 16)
            let i60 ← pure (i59.add 8)
            let i61 ← pure (#v[i58, i60] : Vector (Zig.Ptr) 2)
            let i62 ← pure (v29)
            let i63 ← pure (v40)
            let i64 ← pure (#v[i62, i63] : Vector (BitVec 64) 2)
            match ← ((do
              Zig.loop (heap_ArenaAllocator_reset.loop66 p0 i61 i64) heap_ArenaAllocator_reset.again66) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
            | .br65 => (do
              let i216 ← pure ((← get).ok)
              pure (.ret i216))
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit).run' (default : heap_ArenaAllocator_resetLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heap_ArenaAllocator_queryCapacityLocals where
  capacity : BitVec 64
  local3 : BitVec 64
  deriving Inhabited

inductive heap_ArenaAllocator_queryCapacityExit where
  | ret (v : BitVec 64)
  | br13
  | br10
  | rep11

def heap_ArenaAllocator_queryCapacity.again11 : heap_ArenaAllocator_queryCapacityExit → Bool
  | .rep11 => true
  | _ => false

def heap_ArenaAllocator_queryCapacity.loop11 (i9 : Vector (Option (Zig.Ptr)) 2) : Zig.MM heap_ArenaAllocator_queryCapacityLocals heap_ArenaAllocator_queryCapacityExit := do
  let i12 ← pure ((← get).local3)
  match ← ((do
    let i14 ← pure (i12)
    let i15 ← pure (Zig.lt false i14 (2 : BitVec 64))
    if i15 then (do
      let i17 ← Zig.callR (Zig.vindex i9 i12)
      let i18 ← pure ((← get).capacity)
      let i19 ← Zig.callM (heap_ArenaAllocator_countListCapacity i17)
      let i20 ← Zig.add false i18 i19
      modify (fun s => { s with capacity := i20 })
      pure .br13)
    else (do
      pure .br10)) : Zig.MM heap_ArenaAllocator_queryCapacityLocals heap_ArenaAllocator_queryCapacityExit) with
  | .br13 => (do
    let i24 ← Zig.add false i12 (1 : BitVec 64)
    modify (fun s => { s with local3 := i24 })
    pure .rep11)
  | e => pure e

def heap_ArenaAllocator_queryCapacity (p0 : heap_ArenaAllocator) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with capacity := (0 : BitVec 64) })
    modify (fun s => { s with local3 := (0 : BitVec 64) })
    let i5 ← pure ((p0).state)
    let i6 ← pure ((i5).used_list)
    let i7 ← pure ((p0).state)
    let i8 ← pure ((i7).free_list)
    let i9 ← pure (#v[i6, i8] : Vector (Option (Zig.Ptr)) 2)
    match ← ((do
      Zig.loop (heap_ArenaAllocator_queryCapacity.loop11 i9) heap_ArenaAllocator_queryCapacity.again11) : Zig.MM heap_ArenaAllocator_queryCapacityLocals heap_ArenaAllocator_queryCapacityExit) with
    | .br10 => (do
      let i27 ← pure ((← get).capacity)
      pure (.ret i27))
    | e => pure e) : Zig.MM heap_ArenaAllocator_queryCapacityLocals heap_ArenaAllocator_queryCapacityExit).run' (default : heap_ArenaAllocator_queryCapacityLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure arena_resetLocals where
  fba : Zig.Ptr
  arena : Zig.Ptr
  deriving Inhabited

inductive arena_resetExit where
  | ret (v : BitVec 64)
  | br10
  | br20
  | br30 (v : heap_ArenaAllocator_ResetMode)
  | br35 (v : Zig.Slice)

def arena_reset (p0 : BitVec 64) (p1 : Bool) : Zig.ConcM Tgt (BitVec 64) := do
  let s2 ← Zig.allocStack 24 8
  let s5 ← Zig.allocStack 32 8
  let e ← ((do
    let i2 ← pure (← get).fba
    let i3 ← Zig.callMC (heap_FixedBufferAllocator_init (⟨(⟨some 1, 0⟩ : Zig.Ptr), (4096 : BitVec 64)⟩ : Zig.Slice))
    Zig.store (α := heap_FixedBufferAllocator) 8 i2 i3
    let i5 ← pure (← get).arena
    let i6 ← Zig.callMC (heap_FixedBufferAllocator_allocator i2)
    let i7 ← Zig.callMC (heap_ArenaAllocator_init i6)
    Zig.store (α := heap_ArenaAllocator) 8 i5 i7
    let i9 ← Zig.callMC (heap_ArenaAllocator_allocator i5)
    match ← ((do
      let i11 ← Zig.callC (mem_Allocator_alloc__anon_1 i9 p0)
      let i12 ← pure (Zig.isNonErr i11)
      if i12 then (do
        let _i14 ← Zig.callRC (Zig.unwrapPayload i11)
        pure .br10)
      else (do
        let _i16 ← Zig.callRC (Zig.unwrapErr i11)
        let i17 ← Zig.load (heap_ArenaAllocator) 8 i5
        let _i18 ← Zig.callC (heap_ArenaAllocator_deinit i17)
        pure (.ret (0 : BitVec 64)))) : Zig.CM Tgt arena_resetLocals arena_resetExit) with
    | .br10 => (do
      match ← ((do
        let i21 ← Zig.callC (mem_Allocator_alloc__anon_1 i9 p0)
        let i22 ← pure (Zig.isNonErr i21)
        if i22 then (do
          let _i24 ← Zig.callRC (Zig.unwrapPayload i21)
          pure .br20)
        else (do
          let _i26 ← Zig.callRC (Zig.unwrapErr i21)
          let i27 ← Zig.load (heap_ArenaAllocator) 8 i5
          let _i28 ← Zig.callC (heap_ArenaAllocator_deinit i27)
          pure (.ret (1 : BitVec 64)))) : Zig.CM Tgt arena_resetLocals arena_resetExit) with
      | .br20 => (do
        match ← ((do
          if p1 then (do
            pure (.br30 heap_ArenaAllocator_ResetMode.retain_capacity))
          else (do
            pure (.br30 heap_ArenaAllocator_ResetMode.free_all))) : Zig.CM Tgt arena_resetLocals arena_resetExit) with
        | .br30 v30 => (do
          let i34 ← Zig.callC (heap_ArenaAllocator_reset i5 v30)
          match ← ((do
            let i36 ← Zig.callC (mem_Allocator_alloc__anon_1 i9 p0)
            let i37 ← pure (Zig.isNonErr i36)
            if i37 then (do
              let i39 ← Zig.callRC (Zig.unwrapPayload i36)
              pure (.br35 i39))
            else (do
              let _i41 ← Zig.callRC (Zig.unwrapErr i36)
              let i42 ← Zig.load (heap_ArenaAllocator) 8 i5
              let _i43 ← Zig.callC (heap_ArenaAllocator_deinit i42)
              pure (.ret (2 : BitVec 64)))) : Zig.CM Tgt arena_resetLocals arena_resetExit) with
          | .br35 v35 => (do
            let i45 ← pure (if i34 then 1 else 0 : BitVec 1)
            let i46 ← pure v35.len
            let i47 ← Zig.mul false (2 : BitVec 64) i46
            let i48 ← Zig.intCast false false 64 i45
            let i49 ← Zig.add false i48 i47
            let i50 ← Zig.load (heap_ArenaAllocator) 8 i5
            let i51 ← Zig.callMC (heap_ArenaAllocator_queryCapacity i50)
            let i52 ← Zig.mul false (4 : BitVec 64) i51
            let i53 ← Zig.add false i49 i52
            let i54 ← Zig.load (heap_ArenaAllocator) 8 i5
            let _i55 ← Zig.callC (heap_ArenaAllocator_deinit i54)
            pure (.ret i53))
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt arena_resetLocals arena_resetExit).run' { (default : arena_resetLocals) with fba := s2, arena := s5 }
  Zig.free s2
  Zig.free s5
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_resize__anon_1Locals where
  deriving Inhabited

inductive mem_Allocator_resize__anon_1Exit where
  | ret (v : Bool)
  | br3
  | br10
  | br19 (v : BitVec 64)
  | br29 (v : Bool)

def mem_Allocator_resize__anon_1 (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p2)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        let _i7 ← Zig.callC (mem_Allocator_free__anon_1 p0 p1)
        pure (.ret true))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_resize__anon_1Locals mem_Allocator_resize__anon_1Exit) with
    | .br3 => (do
      match ← ((do
        let i11 ← pure p1.len
        let i12 ← pure (i11)
        let i13 ← pure (i12 == (0 : BitVec 64))
        if i13 then (do
          pure (.ret false))
        else (do
          pure .br10)) : Zig.CM Tgt mem_Allocator_resize__anon_1Locals mem_Allocator_resize__anon_1Exit) with
      | .br10 => (do
        let i17 ← Zig.callMC (mem_absorbSentinel__anon_1 p1)
        let i18 ← pure (i17)
        match ← ((do
          let i20 ← Zig.callRC (math_mul__anon_1 (1 : BitVec 64) p2)
          let i21 ← pure (Zig.isNonErr i20)
          if i21 then (do
            let i23 ← Zig.callRC (Zig.unwrapPayload i20)
            pure (.br19 i23))
          else (do
            let _i25 ← Zig.callRC (Zig.unwrapErr i20)
            pure (.ret false))) : Zig.CM Tgt mem_Allocator_resize__anon_1Locals mem_Allocator_resize__anon_1Exit) with
        | .br19 v19 => (do
          let i27 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
          let i28 ← Zig.callMC Zig.returnAddress
          match ← ((do
            let i30 ← pure ((p0).vtable)
            let i31 ← pure (i30.add 8)
            let i32 ← Zig.load (Zig.Ptr) 8 i31
            let i33 ← pure ((p0).ptr)
            let i34 ← (if i32 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_resize i33 i18 i27 v19 i28) else if i32 == (⟨some 7, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_resize i33 i18 i27 v19 i28) else if i32 == (⟨some 11, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_resize i33 i18 i27 v19 i28) else throw .illegal)
            pure (.br29 i34)) : Zig.CM Tgt mem_Allocator_resize__anon_1Locals mem_Allocator_resize__anon_1Exit) with
          | .br29 v29 => (do
            pure (.ret v29))
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_resize__anon_1Locals mem_Allocator_resize__anon_1Exit).run' (default : mem_Allocator_resize__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure arena_resizeLocals where
  fba : Zig.Ptr
  arena : Zig.Ptr
  deriving Inhabited

inductive arena_resizeExit where
  | ret (v : Bool)
  | br10 (v : Zig.Slice)

def arena_resize (p0 : BitVec 64) (p1 : BitVec 64) : Zig.ConcM Tgt (Bool) := do
  let s2 ← Zig.allocStack 24 8
  let s5 ← Zig.allocStack 32 8
  let e ← ((do
    let i2 ← pure (← get).fba
    let i3 ← Zig.callMC (heap_FixedBufferAllocator_init (⟨(⟨some 1, 0⟩ : Zig.Ptr), (4096 : BitVec 64)⟩ : Zig.Slice))
    Zig.store (α := heap_FixedBufferAllocator) 8 i2 i3
    let i5 ← pure (← get).arena
    let i6 ← Zig.callMC (heap_FixedBufferAllocator_allocator i2)
    let i7 ← Zig.callMC (heap_ArenaAllocator_init i6)
    Zig.store (α := heap_ArenaAllocator) 8 i5 i7
    let i9 ← Zig.callMC (heap_ArenaAllocator_allocator i5)
    match ← ((do
      let i11 ← Zig.callC (mem_Allocator_alloc__anon_1 i9 p0)
      let i12 ← pure (Zig.isNonErr i11)
      if i12 then (do
        let i14 ← Zig.callRC (Zig.unwrapPayload i11)
        pure (.br10 i14))
      else (do
        let _i16 ← Zig.callRC (Zig.unwrapErr i11)
        let i17 ← Zig.load (heap_ArenaAllocator) 8 i5
        let _i18 ← Zig.callC (heap_ArenaAllocator_deinit i17)
        pure (.ret false))) : Zig.CM Tgt arena_resizeLocals arena_resizeExit) with
    | .br10 v10 => (do
      let i20 ← Zig.callC (mem_Allocator_resize__anon_1 i9 v10 p1)
      let i21 ← Zig.load (heap_ArenaAllocator) 8 i5
      let _i22 ← Zig.callC (heap_ArenaAllocator_deinit i21)
      pure (.ret i20))
    | e => pure e) : Zig.CM Tgt arena_resizeLocals arena_resizeExit).run' { (default : arena_resizeLocals) with fba := s2, arena := s5 }
  Zig.free s2
  Zig.free s5
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure arena_sumLocals where
  fba : Zig.Ptr
  arena : Zig.Ptr
  sum : BitVec 64
  local23 : BitVec 64
  deriving Inhabited

inductive arena_sumExit where
  | ret (v : BitVec 64)
  | br9 (v : Zig.Slice)
  | br29
  | br26
  | rep27

def arena_sum.again27 : arena_sumExit → Bool
  | .rep27 => true
  | _ => false

def arena_sum.loop27 (i9 : Zig.Slice) (i25 : BitVec 64) : Zig.CM Tgt arena_sumLocals arena_sumExit := do
  let i28 ← pure ((← get).local23)
  match ← ((do
    let i30 ← pure (i28)
    let i31 ← pure (i25)
    let i32 ← pure (Zig.lt false i30 i31)
    if i32 then (do
      let i34 ← Zig.callMC (Zig.load (BitVec 8) 1 (i9.ptr.elem 1 i28))
      let i35 ← pure ((← get).sum)
      let i36 ← Zig.intCast false false 64 i34
      let i37 ← Zig.add false i35 i36
      modify (fun s => { s with sum := i37 })
      pure .br29)
    else (do
      pure .br26)) : Zig.CM Tgt arena_sumLocals arena_sumExit) with
  | .br29 => (do
    let i41 ← Zig.add false i28 (1 : BitVec 64)
    modify (fun s => { s with local23 := i41 })
    pure .rep27)
  | e => pure e

def arena_sum (p0 : BitVec 64) : Zig.ConcM Tgt (BitVec 64) := do
  let s1 ← Zig.allocStack 24 8
  let s4 ← Zig.allocStack 32 8
  let e ← ((do
    let i1 ← pure (← get).fba
    let i2 ← Zig.callMC (heap_FixedBufferAllocator_init (⟨(⟨some 1, 0⟩ : Zig.Ptr), (4096 : BitVec 64)⟩ : Zig.Slice))
    Zig.store (α := heap_FixedBufferAllocator) 8 i1 i2
    let i4 ← pure (← get).arena
    let i5 ← Zig.callMC (heap_FixedBufferAllocator_allocator i1)
    let i6 ← Zig.callMC (heap_ArenaAllocator_init i5)
    Zig.store (α := heap_ArenaAllocator) 8 i4 i6
    let i8 ← Zig.callMC (heap_ArenaAllocator_allocator i4)
    match ← ((do
      let i10 ← Zig.callC (mem_Allocator_alloc__anon_1 i8 p0)
      let i11 ← pure (Zig.isNonErr i10)
      if i11 then (do
        let i13 ← Zig.callRC (Zig.unwrapPayload i10)
        pure (.br9 i13))
      else (do
        let _i15 ← Zig.callRC (Zig.unwrapErr i10)
        let i16 ← Zig.load (heap_ArenaAllocator) 8 i4
        let _i17 ← Zig.callC (heap_ArenaAllocator_deinit i16)
        pure (.ret (0 : BitVec 64)))) : Zig.CM Tgt arena_sumLocals arena_sumExit) with
    | .br9 v9 => (do
      let _i19 ← pure v9.len
      Zig.callMC (Zig.memset (α := BitVec 8) 1 v9.ptr v9.len (some (1 : BitVec 8)))
      modify (fun s => { s with sum := (0 : BitVec 64) })
      modify (fun s => { s with local23 := (0 : BitVec 64) })
      let i25 ← pure v9.len
      match ← ((do
        Zig.loop (arena_sum.loop27 v9 i25) arena_sum.again27) : Zig.CM Tgt arena_sumLocals arena_sumExit) with
      | .br26 => (do
        let _i44 ← Zig.callC (mem_Allocator_free__anon_1 i8 v9)
        let i45 ← pure ((← get).sum)
        let i46 ← Zig.load (heap_ArenaAllocator) 8 i4
        let _i47 ← Zig.callC (heap_ArenaAllocator_deinit i46)
        pure (.ret i45))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt arena_sumLocals arena_sumExit).run' { (default : arena_sumLocals) with fba := s1, arena := s4 }
  Zig.free s1
  Zig.free s4
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heap_ArenaAllocator_remapLocals where
  local5 : Zig.Slice
  deriving Inhabited

inductive heap_ArenaAllocator_remapExit where
  | ret (v : Option (Zig.Ptr))
  | br8 (v : Option (Zig.Ptr))

def heap_ArenaAllocator_remap (p0 : Zig.Ptr) (p1 : Zig.Slice) (p2 : mem_Alignment) (p3 : BitVec 64) (p4 : BitVec 64) : Zig.ConcM Tgt (Option (Zig.Ptr)) := do
  let e ← ((do
    modify (fun s => { s with local5 := p1 })
    match ← ((do
      let i9 ← Zig.callC (heap_ArenaAllocator_resize p0 p1 p2 p3 p4)
      if i9 then (do
        let i12 ← pure (((← get).local5).ptr)
        let i13 ← pure (i12)
        pure (.br8 i13))
      else (do
        pure (.br8 none))) : Zig.CM Tgt heap_ArenaAllocator_remapLocals heap_ArenaAllocator_remapExit) with
    | .br8 v8 => (do
      pure (.ret v8))
    | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_remapLocals heap_ArenaAllocator_remapExit).run' (default : heap_ArenaAllocator_remapLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heap_FixedBufferAllocator_remapLocals where
  local5 : Zig.Slice
  deriving Inhabited

inductive heap_FixedBufferAllocator_remapExit where
  | ret (v : Option (Zig.Ptr))
  | br8 (v : Option (Zig.Ptr))

def heap_FixedBufferAllocator_remap (p0 : Zig.Ptr) (p1 : Zig.Slice) (p2 : mem_Alignment) (p3 : BitVec 64) (p4 : BitVec 64) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    modify (fun s => { s with local5 := p1 })
    match ← ((do
      let i9 ← Zig.callM (heap_FixedBufferAllocator_resize p0 p1 p2 p3 p4)
      if i9 then (do
        let i12 ← pure (((← get).local5).ptr)
        let i13 ← pure (i12)
        pure (.br8 i13))
      else (do
        pure (.br8 none))) : Zig.MM heap_FixedBufferAllocator_remapLocals heap_FixedBufferAllocator_remapExit) with
    | .br8 v8 => (do
      pure (.ret v8))
    | e => pure e) : Zig.MM heap_FixedBufferAllocator_remapLocals heap_FixedBufferAllocator_remapExit).run' (default : heap_FixedBufferAllocator_remapLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

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

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit :=
  fun t => nomatch t

end AllocArena.ArenaLinux