-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace AllocArena.ArenaFixedLinux

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
  | undef_retain_with_limit (v : BitVec 64) (written : List String)
  deriving Repr, Inhabited, DecidableEq

def heap_ArenaAllocator_ResetMode.tag : heap_ArenaAllocator_ResetMode → heap_ArenaAllocator_ResetModeTag
  | .free_all => .free_all
  | .retain_capacity => .retain_capacity
  | .retain_with_limit _ => .retain_with_limit
  | .undef_retain_with_limit _ _ => .retain_with_limit

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
  | .undef_retain_with_limit _ _ => throw .unspecified
  | _ => throw .panic

def heap_ArenaAllocator_ResetMode.modify_retain_with_limit (g : BitVec 64 → BitVec 64) : heap_ArenaAllocator_ResetMode → heap_ArenaAllocator_ResetMode
  | .retain_with_limit v => .retain_with_limit (g v)
  | .undef_retain_with_limit v w => .undef_retain_with_limit (g v) w
  | _ => .undef_retain_with_limit (g default) []

def heap_ArenaAllocator_ResetMode.setTag_retain_with_limit : heap_ArenaAllocator_ResetMode → heap_ArenaAllocator_ResetMode
  | .retain_with_limit v => .retain_with_limit v
  | .undef_retain_with_limit v w => .undef_retain_with_limit v w
  | _ => .undef_retain_with_limit default []

def heap_ArenaAllocator_ResetMode.set_retain_with_limit (v : BitVec 64) (_ : heap_ArenaAllocator_ResetMode) : heap_ArenaAllocator_ResetMode := .retain_with_limit v

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
  | undef_failure (v : Option (Zig.Ptr)) (written : List String)
  deriving Repr, Inhabited, DecidableEq

def heap_ArenaAllocator_PushResult.tag : heap_ArenaAllocator_PushResult → heap_ArenaAllocator_PushResultTag
  | .success => .success
  | .failure _ => .failure
  | .undef_failure _ _ => .failure

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
  | .undef_failure _ _ => throw .unspecified
  | _ => throw .panic

def heap_ArenaAllocator_PushResult.modify_failure (g : Option (Zig.Ptr) → Option (Zig.Ptr)) : heap_ArenaAllocator_PushResult → heap_ArenaAllocator_PushResult
  | .failure v => .failure (g v)
  | .undef_failure v w => .undef_failure (g v) w
  | _ => .undef_failure (g default) []

def heap_ArenaAllocator_PushResult.setTag_failure : heap_ArenaAllocator_PushResult → heap_ArenaAllocator_PushResult
  | .failure v => .failure v
  | .undef_failure v w => .undef_failure v w
  | _ => .undef_failure default []

def heap_ArenaAllocator_PushResult.set_failure (v : Option (Zig.Ptr)) (_ : heap_ArenaAllocator_PushResult) : heap_ArenaAllocator_PushResult := .failure v

instance : Zig.Enc heap_ArenaAllocator_PushResult where
  size := 16
  align := 8
  encode v := match v with
    | .success => Zig.Enc.fields 16 [(8, Zig.Enc.encode v.tag)]
    | .failure x => Zig.Enc.fields 16 [(8, Zig.Enc.encode v.tag), (0, Zig.Enc.encode x)]
    | .undef_failure _ _ => Zig.Enc.fields 16 [(8, Zig.Enc.encode v.tag)]
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

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
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
  -- 6: arena.node_buf
  (Array.replicate (Zig.Enc.size (Vector (BitVec 64) 8)) .undef, 8, .global),
  -- 7: arena.small
  (Array.replicate (Zig.Enc.size (Vector (BitVec 8) 256)) .undef, 1, .global),
  -- 8: heap.ArenaAllocator.alloc
  (#[.undef], 1, .constGlobal),
  -- 9: heap.ArenaAllocator.resize
  (#[.undef], 1, .constGlobal),
  -- 10: heap.ArenaAllocator.remap
  (#[.undef], 1, .constGlobal),
  -- 11: heap.ArenaAllocator.free
  (#[.undef], 1, .constGlobal),
  -- 12: heap.FixedBufferAllocator.alloc
  (#[.undef], 1, .constGlobal),
  -- 13: heap.FixedBufferAllocator.resize
  (#[.undef], 1, .constGlobal),
  -- 14: heap.FixedBufferAllocator.remap
  (#[.undef], 1, .constGlobal),
  -- 15: heap.FixedBufferAllocator.free
  (#[.undef], 1, .constGlobal),
  -- 16: heap.PageAllocator.addr_hint
  (Zig.Enc.encode (none : Option (Zig.Ptr)), 8, .global),
  -- 17: a constant
  (Zig.Enc.encode (({ alloc := (⟨some 8, 0⟩ : Zig.Ptr), resize := (⟨some 9, 0⟩ : Zig.Ptr), remap := (⟨some 10, 0⟩ : Zig.Ptr), free := (⟨some 11, 0⟩ : Zig.Ptr) } : mem_Allocator_VTable) : mem_Allocator_VTable), 8, .constGlobal),
  -- 18: a constant
  (Zig.Enc.encode (({ alloc := (⟨some 12, 0⟩ : Zig.Ptr), resize := (⟨some 13, 0⟩ : Zig.Ptr), remap := (⟨some 14, 0⟩ : Zig.Ptr), free := (⟨some 15, 0⟩ : Zig.Ptr) } : mem_Allocator_VTable) : mem_Allocator_VTable), 8, .constGlobal)]

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
    modify (fun s => { s with local1 := { s.local1 with vtable := (⟨some 17, 0⟩ : Zig.Ptr) } })
    pure (.ret (← get).local1)) : Zig.MM heap_ArenaAllocator_allocatorLocals heap_ArenaAllocator_allocatorExit).run' (default : heap_ArenaAllocator_allocatorLocals)
  match e with
  | .ret v => pure v

structure mem_absorbSentinel__anon_7342b53a30edLocals where
  deriving Inhabited

inductive mem_absorbSentinel__anon_7342b53a30edExit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_7342b53a30ed (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret p0)) : Zig.MM mem_absorbSentinel__anon_7342b53a30edLocals mem_absorbSentinel__anon_7342b53a30edExit).run' (default : mem_absorbSentinel__anon_7342b53a30edLocals)
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

structure mem_Alignment_fromByteUnitsLocals where
  deriving Inhabited

inductive mem_Alignment_fromByteUnitsExit where
  | ret (v : mem_Alignment)

def mem_Alignment_fromByteUnits (p0 : BitVec 64) : Zig.Result (mem_Alignment) := do
  let e ← ((do
    let i1 ← Zig.call (math_isPowerOfTwo__anon_38853e1fe316 p0)
    let _i2 ← Zig.call (debug_assert i1)
    let i3 ← pure (Zig.ctz 7 p0)
    let i4 ← Zig.enumOf (mem_Alignment.ofInt? (Zig.val false i3))
    pure (.ret i4)) : Zig.M mem_Alignment_fromByteUnitsLocals mem_Alignment_fromByteUnitsExit).run' (default : mem_Alignment_fromByteUnitsLocals)
  match e with
  | .ret v => pure v

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
      let i16 ← Zig.callM (Zig.checkAlign 4096 p1.ptr >>= fun _ => pure p1)
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
    let i1 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
    let i2 ← pure i1
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
      let i15 ← Zig.callMC (Zig.checkAlign 8 p0 >>= fun _ => pure p0)
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
        let i30 ← Zig.callMC (Zig.ptrProject i29 (·.elem 1 (24 : BitVec 64)))
        let i31 ← Zig.callMC (Zig.ptrProject i28 (·.add 8))
        let i32 ← pure (i31)
        let i33 ← Zig.atomicLoadC (n := 64) Zig.AtomicOrder.relaxed 8 i32
        match ← ((do
          let i35 ← Zig.callMC (Zig.ptrProject i30 (·.elem 1 i33))
          let i37 ← pure (((← get).local4).ptr)
          let i39 ← pure (((← get).local4).len)
          let i40 ← Zig.callMC (Zig.ptrProject i37 (·.elem 1 i39))
          let i41 ← Zig.callMC (do pure (!(← Zig.ptrEqAddr i35 i40)))
          if i41 then (do
            pure .ret)
          else (do
            pure .br34)) : Zig.CM Tgt heap_ArenaAllocator_freeLocals heap_ArenaAllocator_freeExit) with
        | .br34 => (do
          let i46 ← pure (((← get).local4).len)
          let i47 ← Zig.sub false i33 i46
          let i48 ← Zig.callMC (Zig.ptrProject i30 (·.elem 1 i47))
          let i50 ← pure (((← get).local4).ptr)
          let i51 ← Zig.callMC (Zig.ptrEqAddr i48 i50)
          let _i52 ← Zig.callRC (debug_assert i51)
          let i53 ← Zig.callMC (Zig.ptrProject i28 (·.add 8))
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
    let i2 ← Zig.callM (Zig.ptrProject p0 (·.add 8))
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
    let i9 ← Zig.callM (Zig.ptrProject i6 (·.elem 1 i8))
    let i10 ← Zig.callM (Zig.ptrProject p0 (·.add 8))
    let i11 ← pure i10
    let i12 ← Zig.load (Zig.Ptr) 8 i11
    let i13 ← pure p0
    let i14 ← Zig.load (BitVec 64) 8 i13
    let i15 ← Zig.callM (Zig.ptrProject i12 (·.elem 1 i14))
    let i16 ← Zig.callM (Zig.ptrEqAddr i9 i15)
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
      let i12 ← Zig.callM (Zig.checkAlign 8 p0 >>= fun _ => pure p0)
      let i13 ← Zig.callM (heap_FixedBufferAllocator_ownsSlice i12 p1)
      let _i14 ← Zig.callR (debug_assert i13)
      match ← ((do
        let i16 ← Zig.callM (heap_FixedBufferAllocator_isLastAllocation i12 p1)
        if i16 then (do
          let i18 ← pure i12
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

structure mem_Allocator_free__anon_1e60e7ef40f5Locals where
  deriving Inhabited

inductive mem_Allocator_free__anon_1e60e7ef40f5Exit where
  | ret
  | br4
  | br15

def mem_Allocator_free__anon_1e60e7ef40f5 (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_7342b53a30ed p1)
    let i3 ← pure (i2)
    match ← ((do
      let i5 ← pure i3.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        pure .ret)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_free__anon_1e60e7ef40f5Locals mem_Allocator_free__anon_1e60e7ef40f5Exit) with
    | .br4 => (do
      let _i11 ← pure i3.len
      Zig.callMC (Zig.memset (α := BitVec 8) 1 i3.ptr i3.len none)
      let i13 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
      let i14 ← Zig.callMC Zig.returnAddress
      match ← ((do
        let i16 ← pure ((p0).vtable)
        let i17 ← Zig.callMC (Zig.ptrProject i16 (·.add 24))
        let i18 ← Zig.load (Zig.Ptr) 8 i17
        let i19 ← pure ((p0).ptr)
        let _i20 ← (if i18 == (⟨some 5, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_free i19 i3 i13 i14) else if i18 == (⟨some 11, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_free i19 i3 i13 i14) else if i18 == (⟨some 15, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_free i19 i3 i13 i14) else throw .illegal)
        pure .br15) : Zig.CM Tgt mem_Allocator_free__anon_1e60e7ef40f5Locals mem_Allocator_free__anon_1e60e7ef40f5Exit) with
      | .br15 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_1e60e7ef40f5Locals mem_Allocator_free__anon_1e60e7ef40f5Exit).run' (default : mem_Allocator_free__anon_1e60e7ef40f5Locals)
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
    let _i4 ← Zig.callC (mem_Allocator_free__anon_1e60e7ef40f5 i3 (⟨(⟨some 1, 0⟩ : Zig.Ptr), (8 : BitVec 64)⟩ : Zig.Slice))
    pure .ret) : Zig.CM Tgt arena_foreign_freeLocals arena_foreign_freeExit).run' { (default : arena_foreign_freeLocals) with arena := s0 }
  Zig.free s0
  match e with
  | .ret => pure ()

structure arena_oob_freeLocals where
  arena : Zig.Ptr
  deriving Inhabited

inductive arena_oob_freeExit where
  | ret

def arena_oob_free  : Zig.ConcM Tgt (Unit) := do
  let s0 ← Zig.allocStack 32 8
  let e ← ((do
    let i0 ← pure (← get).arena
    let i1 ← Zig.callMC (heap_ArenaAllocator_init ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 0, 0⟩ : Zig.Ptr) } : mem_Allocator))
    Zig.store (α := heap_ArenaAllocator) 8 i0 i1
    Zig.store (α := heap_ArenaAllocator_Node_Size) 8 (⟨some 6, 0⟩ : Zig.Ptr) (Zig.Packed.ofBits (64 : BitVec 64) : heap_ArenaAllocator_Node_Size)
    Zig.store (α := BitVec 64) 8 (⟨some 6, 8⟩ : Zig.Ptr) (1000 : BitVec 64)
    Zig.store (α := Option (Zig.Ptr)) 8 (⟨some 6, 16⟩ : Zig.Ptr) none
    let i6 ← Zig.callMC (Zig.ptrProject i0 (·.add 16))
    let i7 ← pure i6
    Zig.store (α := Option (Zig.Ptr)) 8 i7 (some (⟨some 6, 0⟩ : Zig.Ptr))
    let i9 ← Zig.callMC (heap_ArenaAllocator_allocator i0)
    let _i10 ← Zig.callC (mem_Allocator_free__anon_1e60e7ef40f5 i9 (⟨(⟨some 1, 0⟩ : Zig.Ptr), (8 : BitVec 64)⟩ : Zig.Slice))
    pure .ret) : Zig.CM Tgt arena_oob_freeLocals arena_oob_freeExit).run' { (default : arena_oob_freeLocals) with arena := s0 }
  Zig.free s0
  match e with
  | .ret => pure ()

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
    modify (fun s => { s with local1 := { s.local1 with vtable := (⟨some 18, 0⟩ : Zig.Ptr) } })
    pure (.ret (← get).local1)) : Zig.MM heap_FixedBufferAllocator_allocatorLocals heap_FixedBufferAllocator_allocatorExit).run' (default : heap_FixedBufferAllocator_allocatorLocals)
  match e with
  | .ret v => pure v

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
    let i1 ← Zig.call (mem_isValidAlignGeneric__anon_32d5b5f10ec2 p0)
    pure (.ret i1)) : Zig.M mem_isValidAlignLocals mem_isValidAlignExit).run' (default : mem_isValidAlignLocals)
  match e with
  | .ret v => pure v

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
        let i18 ← pure (i9)
        pure (.ret i18))
      | e => pure e)
    | e => pure e) : Zig.MM mem_alignPointer__anon_53311c568cf7Locals mem_alignPointer__anon_53311c568cf7Exit).run' (default : mem_alignPointer__anon_53311c568cf7Locals)
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
        let i11 ← Zig.callRC (mem_alignForward__anon_589277751031 p0 (4096 : BitVec 64))
        let i12 ← pure (Zig.subSat false i10 (4096 : BitVec 64))
        let i13 ← Zig.add false i11 i12
        match ← ((do
          let i17 ← Zig.atomicLoadUnorderedEncC (Option (Zig.Ptr)) 8 (⟨some 16, 0⟩ : Zig.Ptr)
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
                  let i79 ← Zig.sub false i71 (0 : BitVec 64)
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
                    let _i127 ← Zig.cmpxchgPtrC (α := Option (Zig.Ptr)) Zig.AtomicOrder.relaxed Zig.AtomicOrder.relaxed 8 (⟨some 16, 0⟩ : Zig.Ptr) i125 i126
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
    let i1 ← pure p0
    let i2 ← pure (i1)
    let i3 ← Zig.atomicLoadAsC (heap_ArenaAllocator_Node_Size) Zig.AtomicOrder.relaxed 8 i2
    let i4 ← pure (p0)
    let i5 ← Zig.callRC (heap_ArenaAllocator_Node_Size_toInt i3)
    let i6 ← pure i4
    let i7 ← Zig.sub false i5 (0 : BitVec 64)
    let i8 ← pure (⟨i6, i7⟩ : Zig.Slice)
    let i9 ← pure i8.ptr
    let i10 ← Zig.callMC (Zig.ptrProject i9 (·.elem 1 (24 : BitVec 64)))
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
        let i26 ← Zig.callMC (Zig.checkSliceEnd i8.len (24 : BitVec 64) i18 0 >>= fun _ => pure (⟨i10, i18⟩ : Zig.Slice))
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
    let i21 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
    let i22 ← Zig.callMC (Zig.ptrProject i21 (·.add 8))
    let i23 ← Zig.callMC (Zig.ptrProject p2 (·.add 16))
    let i24 ← Zig.load (Option (Zig.Ptr)) 8 i23
    let i25 ← pure (p1)
    let i26 ← Zig.cmpxchgWeakPtrC (α := Option (Zig.Ptr)) Zig.AtomicOrder.release Zig.AtomicOrder.relaxed 8 i22 i24 i25
    let i27 ← pure ((i26).isSome)
    if i27 then (do
      let i29 ← Zig.optPayload i26
      let i30 ← Zig.callMC (Zig.ptrProject p2 (·.add 16))
      Zig.store (α := Option (Zig.Ptr)) 8 i30 i29
      pure .br20)
    else (do
      pure .br18)) : Zig.CM Tgt heap_ArenaAllocator_pushFreeListLocals heap_ArenaAllocator_pushFreeListExit) with
  | .br20 => (do
    pure .rep19)
  | e => pure e

def heap_ArenaAllocator_pushFreeList (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i3 ← Zig.callMC (Zig.ptrProject p2 (·.add 16))
    let i4 ← Zig.load (Option (Zig.Ptr)) 8 i3
    let i5 ← pure (p1)
    let i6 ← Zig.callMC (do pure (!(← Zig.optPtrEqAddr i5 i4)))
    let _i7 ← Zig.callRC (debug_assert i6)
    let i8 ← Zig.callMC (Zig.ptrProject p1 (·.add 16))
    let i9 ← Zig.load (Option (Zig.Ptr)) 8 i8
    let i10 ← pure (p1)
    let i11 ← Zig.callMC (do pure (!(← Zig.optPtrEqAddr i10 i9)))
    let _i12 ← Zig.callRC (debug_assert i11)
    let i13 ← Zig.callMC (Zig.ptrProject p2 (·.add 16))
    let i14 ← Zig.load (Option (Zig.Ptr)) 8 i13
    let i15 ← pure (p2)
    let i16 ← Zig.callMC (do pure (!(← Zig.optPtrEqAddr i15 i14)))
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
    let i1 ← pure p0
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
      let i10 ← pure i8
      let i11 ← Zig.sub false i9 (0 : BitVec 64)
      let i12 ← pure (⟨i10, i11⟩ : Zig.Slice)
      let i13 ← pure (some i12)
      pure (.ret i13))
    | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_Node_beginResizeLocals heap_ArenaAllocator_Node_beginResizeExit).run' (default : heap_ArenaAllocator_Node_beginResizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure math_add__anon_23f0cc3a812cLocals where
  deriving Inhabited

inductive math_add__anon_23f0cc3a812cExit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br3

def math_add__anon_23f0cc3a812c (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← pure (Zig.addWithOverflow false p0 p1)
    match ← ((do
      let i4 ← pure ((i2).2)
      let i5 ← pure (i4 != (0 : BitVec 1))
      if i5 then (do
        pure (.ret (.error "Overflow" : Except Zig.ErrName (BitVec 64))))
      else (do
        pure .br3)) : Zig.M math_add__anon_23f0cc3a812cLocals math_add__anon_23f0cc3a812cExit) with
    | .br3 => (do
      let i9 ← pure ((i2).1)
      let i10 ← pure ((.ok i9) : Except Zig.ErrName (BitVec 64))
      pure (.ret i10))
    | e => pure e) : Zig.M math_add__anon_23f0cc3a812cLocals math_add__anon_23f0cc3a812cExit).run' (default : math_add__anon_23f0cc3a812cLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heap_ArenaAllocator_nodeSizeForLocals where
  deriving Inhabited

inductive heap_ArenaAllocator_nodeSizeForExit where
  | ret (v : Option (BitVec 64))
  | br2 (v : BitVec 64)
  | br10 (v : BitVec 64)

def heap_ArenaAllocator_nodeSizeFor (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (Option (BitVec 64)) := do
  let e ← ((do
    match ← ((do
      let i3 ← Zig.call (math_add__anon_23f0cc3a812c p0 p1)
      let i4 ← pure (Zig.isNonErr i3)
      if i4 then (do
        let i6 ← Zig.call (Zig.unwrapPayload i3)
        pure (.br2 i6))
      else (do
        let _i8 ← Zig.call (Zig.unwrapErr i3)
        pure (.ret none))) : Zig.M heap_ArenaAllocator_nodeSizeForLocals heap_ArenaAllocator_nodeSizeForExit) with
    | .br2 v2 => (do
      match ← ((do
        let i11 ← Zig.call (math_add__anon_23f0cc3a812c v2 (1 : BitVec 64))
        let i12 ← pure (Zig.isNonErr i11)
        if i12 then (do
          let i14 ← Zig.call (Zig.unwrapPayload i11)
          pure (.br10 i14))
        else (do
          let _i16 ← Zig.call (Zig.unwrapErr i11)
          pure (.ret none))) : Zig.M heap_ArenaAllocator_nodeSizeForLocals heap_ArenaAllocator_nodeSizeForExit) with
      | .br10 v10 => (do
        let i18 ← Zig.call (mem_alignBackward__anon_f056e98f6fd2 v10 (2 : BitVec 64))
        let i19 ← pure (some i18)
        pure (.ret i19))
      | e => pure e)
    | e => pure e) : Zig.M heap_ArenaAllocator_nodeSizeForLocals heap_ArenaAllocator_nodeSizeForExit).run' (default : heap_ArenaAllocator_nodeSizeForLocals)
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
    let i7 ← pure p0
    let i8 ← pure (i7)
    let i9 ← Zig.atomicLoadUnorderedAsC (heap_ArenaAllocator_Node_Size) 8 i8
    let i10 ← Zig.callRC (heap_ArenaAllocator_Node_Size_toInt i9)
    let i11 ← pure (i10)
    let i12 ← pure (p2)
    let i13 ← pure (i11 == i12)
    let _i14 ← Zig.callRC (debug_assert i13)
    let i15 ← pure p0
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
    let i1 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
    let i2 ← Zig.callMC (Zig.ptrProject i1 (·.add 8))
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
    let i2 ← pure p0
    let i3 ← Zig.load (heap_ArenaAllocator_Node_Size) 8 i2
    let i4 ← Zig.callR (heap_ArenaAllocator_Node_Size_toInt i3)
    let i5 ← pure i1
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
    let i2 ← Zig.callMC (Zig.ptrProject p1 (·.add 16))
    let i3 ← Zig.load (Option (Zig.Ptr)) 8 i2
    let i4 ← pure (p1)
    let i5 ← Zig.callMC (do pure (!(← Zig.optPtrEqAddr i4 i3)))
    let _i6 ← Zig.callRC (debug_assert i5)
    let i7 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
    let i8 ← pure i7
    let i9 ← Zig.callMC (Zig.ptrProject p1 (·.add 16))
    let i10 ← Zig.load (Option (Zig.Ptr)) 8 i9
    let i11 ← pure (p1)
    let i12 ← Zig.cmpxchgPtrC (α := Option (Zig.Ptr)) Zig.AtomicOrder.release Zig.AtomicOrder.acquire 8 i8 i10 i11
    let i13 ← pure ((i12).isSome)
    if i13 then (do
      let i15 ← Zig.optPayload i12
      modify (fun s => { s with local16 := (heap_ArenaAllocator_PushResult.setTag_failure s.local16) })
      modify (fun s => { s with local16 := (heap_ArenaAllocator_PushResult.set_failure (i15) s.local16) })
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
      let i16 ← Zig.callMC (Zig.checkAlign 8 p0 >>= fun _ => pure p0)
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
        let i34 ← Zig.callMC (Zig.ptrProject i33 (·.elem 1 (24 : BitVec 64)))
        let i35 ← Zig.callMC (Zig.ptrProject i32 (·.add 8))
        let i36 ← pure (i35)
        let i37 ← Zig.atomicLoadC (n := 64) Zig.AtomicOrder.relaxed 8 i36
        match ← ((do
          let i39 ← Zig.callMC (Zig.ptrProject i34 (·.elem 1 i37))
          let i41 ← pure (((← get).local5).ptr)
          let i43 ← pure (((← get).local5).len)
          let i44 ← Zig.callMC (Zig.ptrProject i41 (·.elem 1 i43))
          let i45 ← Zig.callMC (do pure (!(← Zig.ptrEqAddr i39 i44)))
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
              let i65 ← Zig.callMC (Zig.ptrProject i34 (·.elem 1 i64))
              let i67 ← pure (((← get).local5).ptr)
              let i68 ← Zig.callMC (Zig.ptrProject i67 (·.elem 1 p3))
              let i69 ← Zig.callMC (Zig.ptrEqAddr i65 i68)
              let _i70 ← Zig.callRC (debug_assert i69)
              let i71 ← Zig.callMC (Zig.ptrProject i32 (·.add 8))
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
                let i90 ← Zig.callMC (Zig.ptrProject i34 (·.elem 1 i89))
                let i92 ← pure (((← get).local5).ptr)
                let i93 ← Zig.callMC (Zig.ptrProject i92 (·.elem 1 p3))
                let i94 ← Zig.callMC (Zig.ptrEqAddr i90 i93)
                let _i95 ← Zig.callRC (debug_assert i94)
                let i96 ← Zig.callMC (Zig.ptrProject i32 (·.add 8))
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
      let i13 ← Zig.callM (Zig.checkAlign 8 p0 >>= fun _ => pure p0)
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
            let i38 ← pure i13
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
            let i47 ← pure i13
            let i48 ← Zig.load (BitVec 64) 8 i47
            let i49 ← Zig.add false i45 i48
            let i50 ← Zig.callM (Zig.ptrProject i13 (·.add 8))
            let i51 ← Zig.callM (Zig.ptrProject i50 (·.add 8))
            let i52 ← Zig.load (BitVec 64) 8 i51
            let i53 ← pure (i49)
            let i54 ← pure (i52)
            let i55 ← pure (Zig.gt false i53 i54)
            if i55 then (do
              pure (.ret false))
            else (do
              pure .br46)) : Zig.MM heap_FixedBufferAllocator_resizeLocals heap_FixedBufferAllocator_resizeExit) with
          | .br46 => (do
            let i59 ← pure i13
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

structure mem_alignPointerOffset__anon_1fdb4fd23aeeLocals where
  ov : BitVec 64 × BitVec 1
  deriving Inhabited

inductive mem_alignPointerOffset__anon_1fdb4fd23aeeExit where
  | ret (v : Option (BitVec 64))
  | br4
  | br15
  | br31

def mem_alignPointerOffset__anon_1fdb4fd23aee (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (Option (BitVec 64)) := do
  let e ← ((do
    let i2 ← Zig.callR (mem_isValidAlign p1)
    let _i3 ← Zig.callR (debug_assert i2)
    match ← ((do
      let i5 ← pure (p1)
      let i6 ← pure (Zig.le false i5 (1 : BitVec 64))
      if i6 then (do
        pure (.ret (some (0 : BitVec 64))))
      else (do
        pure .br4)) : Zig.MM mem_alignPointerOffset__anon_1fdb4fd23aeeLocals mem_alignPointerOffset__anon_1fdb4fd23aeeExit) with
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
          pure .br15)) : Zig.MM mem_alignPointerOffset__anon_1fdb4fd23aeeLocals mem_alignPointerOffset__anon_1fdb4fd23aeeExit) with
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
            pure .br31)) : Zig.MM mem_alignPointerOffset__anon_1fdb4fd23aeeLocals mem_alignPointerOffset__anon_1fdb4fd23aeeExit) with
        | .br31 => (do
          let i38 ← Zig.divTrunc false i30 (1 : BitVec 64)
          let i39 ← pure (some i38)
          pure (.ret i39))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM mem_alignPointerOffset__anon_1fdb4fd23aeeLocals mem_alignPointerOffset__anon_1fdb4fd23aeeExit).run' (default : mem_alignPointerOffset__anon_1fdb4fd23aeeLocals)
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
      let i12 ← Zig.callM (Zig.checkAlign 8 p0 >>= fun _ => pure p0)
      let i13 ← Zig.callR (mem_Alignment_toByteUnits p2)
      match ← ((do
        let i15 ← Zig.callM (Zig.ptrProject i12 (·.add 8))
        let i16 ← pure i15
        let i17 ← Zig.load (Zig.Ptr) 8 i16
        let i18 ← pure i12
        let i19 ← Zig.load (BitVec 64) 8 i18
        let i20 ← Zig.callM (Zig.ptrProject i17 (·.elem 1 i19))
        let i21 ← Zig.callM (mem_alignPointerOffset__anon_1fdb4fd23aee i20 i13)
        let i22 ← pure ((i21).isSome)
        if i22 then (do
          let i24 ← Zig.optPayload i21
          pure (.br14 i24))
        else (do
          pure (.ret none))) : Zig.MM heap_FixedBufferAllocator_allocLocals heap_FixedBufferAllocator_allocExit) with
      | .br14 v14 => (do
        let i27 ← pure i12
        let i28 ← Zig.load (BitVec 64) 8 i27
        let i29 ← Zig.add false i28 v14
        let i30 ← Zig.add false i29 p1
        match ← ((do
          let i32 ← Zig.callM (Zig.ptrProject i12 (·.add 8))
          let i33 ← Zig.callM (Zig.ptrProject i32 (·.add 8))
          let i34 ← Zig.load (BitVec 64) 8 i33
          let i35 ← pure (i30)
          let i36 ← pure (i34)
          let i37 ← pure (Zig.gt false i35 i36)
          if i37 then (do
            pure (.ret none))
          else (do
            pure .br31)) : Zig.MM heap_FixedBufferAllocator_allocLocals heap_FixedBufferAllocator_allocExit) with
        | .br31 => (do
          let i41 ← pure i12
          Zig.store (α := BitVec 64) 8 i41 i30
          let i43 ← Zig.callM (Zig.ptrProject i12 (·.add 8))
          let i44 ← pure i43
          let i45 ← Zig.load (Zig.Ptr) 8 i44
          let i46 ← Zig.callM (Zig.ptrProject i45 (·.elem 1 i29))
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
  local33 : Option (Zig.Ptr)
  local34 : BitVec 64
  local46 : Zig.Slice
  local132 : Zig.Slice
  local166 : Zig.Slice
  size : BitVec 64
  local192 : Zig.Slice
  local281 : Zig.Slice
  local318 : Zig.Ptr
  local319 : Zig.Ptr
  local320 : Zig.Ptr
  local321 : Option (Zig.Ptr)
  best_fit_prev : Option (Zig.Ptr)
  best_fit : Option (Zig.Ptr)
  best_fit_diff : BitVec 64
  it_prev : Option (Zig.Ptr)
  it : Option (Zig.Ptr)
  local366 : Zig.Slice
  local424 : BitVec 64
  local425 : Bool
  local447 : Zig.Slice
  local619 : Zig.Slice
  local780 : Zig.Slice
  local820 : Zig.Slice
  deriving Inhabited

inductive heap_ArenaAllocator_allocExit where
  | ret (v : Option (Zig.Ptr))
  | br7
  | br16
  | br36 (v : Zig.Ptr)
  | br35
  | br49
  | br80 (v : Bool)
  | br74
  | br107
  | br126
  | br137
  | br152 (v : Zig.Ptr)
  | br151
  | br159 (v : Zig.Slice)
  | br178
  | br186
  | br201 (v : BitVec 64)
  | br32
  | br213
  | br229
  | br232 (v : Bool)
  | br256
  | br264
  | br275
  | br290
  | br241
  | br226
  | br311 (v : Zig.Ptr)
  | br310
  | br352
  | br360
  | br376
  | br341
  | br336
  | br334
  | br401
  | br410
  | br322
  | br433
  | br441
  | br459 (v : Bool)
  | br426
  | br487
  | br490
  | br497 (v : Bool)
  | br481 (v : Bool)
  | br510
  | br479
  | br473
  | br531
  | br539
  | br563
  | br572 (v : Option (Zig.Ptr))
  | br582 (v : Option (Zig.Ptr))
  | br598
  | br593
  | br613
  | br624
  | br645 (v : Zig.Ptr)
  | br646
  | br654 (v : BitVec 64)
  | br663
  | br674 (v : BitVec 64)
  | br683
  | br694 (v : BitVec 64)
  | br701
  | br653 (v : heap_ArenaAllocator_Node_Size)
  | br718
  | br721 (v : Option (Zig.Ptr))
  | br714 (v : Zig.Ptr)
  | br732
  | br746
  | br766
  | br774
  | br814
  | br825
  | br803
  | rep335
  | rep31

def heap_ArenaAllocator_alloc.again335 : heap_ArenaAllocator_allocExit → Bool
  | .rep335 => true
  | _ => false

def heap_ArenaAllocator_alloc.again31 : heap_ArenaAllocator_allocExit → Bool
  | .rep31 => true
  | _ => false

mutual

def heap_ArenaAllocator_alloc.loop335 (p1 : BitVec 64) (p2 : mem_Alignment) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit := do
  match ← ((do
    let i337 ← pure ((← get).it)
    let i338 ← pure ((i337).isSome)
    if i338 then (do
      let i340 ← Zig.optPayload i337
      match ← ((do
        let i342 ← pure i340
        let i343 ← pure i342
        let i344 ← Zig.loadBits (Bool) 8 8 0 i343
        let i345 ← pure (!i344)
        let _i346 ← Zig.callRC (debug_assert i345)
        let i347 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe i340)
        let i348 ← pure i347.ptr
        let i349 ← Zig.callMC (Zig.ptrProject i348 (·.elem 1 (24 : BitVec 64)))
        let i350 ← pure i347.len
        let i351 ← pure (Zig.le false (24 : BitVec 64) i350)
        match ← ((do
          if i351 then (do
            pure .br352)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
        | .br352 => (do
          let i357 ← Zig.sub false i350 (24 : BitVec 64)
          let i358 ← pure i347.len
          let i359 ← pure (Zig.le false i350 i358)
          match ← ((do
            if i359 then (do
              pure .br360)
            else (do
              throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
          | .br360 => (do
            let i365 ← Zig.callMC (Zig.checkSliceEnd i347.len (24 : BitVec 64) i357 0 >>= fun _ => pure (⟨i349, i357⟩ : Zig.Slice))
            modify (fun s => { s with local366 := i365 })
            let i370 ← pure (((← get).local366).ptr)
            let i371 ← Zig.callMC (heap_ArenaAllocator_alignedIndex i370 (0 : BitVec 64) p2)
            let i372 ← pure (Zig.addSat false i371 p1)
            let i374 ← pure (((← get).local366).len)
            let i375 ← pure (Zig.subSat false i372 i374)
            match ← ((do
              let i377 ← pure ((← get).best_fit_diff)
              let i378 ← pure (i375)
              let i379 ← pure (i377)
              let i380 ← pure (Zig.lt false i378 i379)
              if i380 then (do
                let i382 ← pure ((← get).it_prev)
                modify (fun s => { s with best_fit_prev := i382 })
                let i384 ← pure (i340)
                modify (fun s => { s with best_fit := i384 })
                modify (fun s => { s with best_fit_diff := i375 })
                pure .br376)
              else (do
                pure .br376)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
            | .br376 => (do
              pure .br341)
            | e => pure e)
          | e => pure e)
        | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
      | .br341 => (do
        let i390 ← pure (i340)
        modify (fun s => { s with it_prev := i390 })
        let i392 ← Zig.callMC (Zig.ptrProject i340 (·.add 16))
        let i393 ← Zig.load (Option (Zig.Ptr)) 8 i392
        modify (fun s => { s with it := i393 })
        pure .br336)
      | e => pure e)
    else (do
      pure .br334)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
  | .br336 => (do
    pure .rep335)
  | e => pure e
partial_fixpoint

def heap_ArenaAllocator_alloc.loop31 (p1 : BitVec 64) (p2 : mem_Alignment) (i12 : Zig.Ptr) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit := do
  match ← ((do
    match ← ((do
      match ← ((do
        let i37 ← pure ((← get).cur_first_node)
        let i38 ← pure ((i37).isSome)
        if i38 then (do
          let i40 ← Zig.optPayload i37
          pure (.br36 i40))
        else (do
          modify (fun s => { s with local33 := none })
          modify (fun s => { s with local34 := (0 : BitVec 64) })
          pure .br35)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
      | .br36 v36 => (do
        let i45 ← Zig.callC (heap_ArenaAllocator_Node_loadBuf v36)
        modify (fun s => { s with local46 := i45 })
        match ← ((do
          let i50 ← Zig.callRC (mem_Alignment_toByteUnits p2)
          let i51 ← Zig.add false p1 i50
          let i52 ← Zig.sub false i51 (1 : BitVec 64)
          let i54 ← pure (((← get).local46).len)
          let i55 ← pure (i52)
          let i56 ← pure (i54)
          let i57 ← pure (Zig.gt false i55 i56)
          if i57 then (do
            let i59 ← pure (v36)
            modify (fun s => { s with local33 := i59 })
            let i62 ← pure (((← get).local46).len)
            modify (fun s => { s with local34 := i62 })
            pure .br35)
          else (do
            pure .br49)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
        | .br49 => (do
          let i66 ← Zig.callRC (mem_Alignment_toByteUnits p2)
          let i67 ← Zig.add false p1 i66
          let i68 ← Zig.sub false i67 (1 : BitVec 64)
          let i69 ← Zig.callMC (Zig.ptrProject v36 (·.add 8))
          let i70 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.acquire 8 i69 i68
          let i72 ← pure (((← get).local46).ptr)
          let i73 ← Zig.callMC (heap_ArenaAllocator_alignedIndex i72 i70 p2)
          match ← ((do
            let i76 ← pure (((← get).local46).len)
            let i77 ← pure (i73)
            let i78 ← pure (i76)
            let i79 ← pure (Zig.gt false i77 i78)
            match ← ((do
              if i79 then (do
                pure (.br80 true))
              else (do
                let i84 ← pure (((← get).local46).len)
                let i85 ← Zig.sub false i84 i73
                let i86 ← pure (p1)
                let i87 ← pure (i85)
                let i88 ← pure (Zig.gt false i86 i87)
                pure (.br80 i88))) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
            | .br80 v80 => (do
              if v80 then (do
                let i91 ← Zig.callMC (Zig.ptrProject v36 (·.add 8))
                let i92 ← pure (Zig.addWrap i70 i68)
                let _i93 ← Zig.cmpxchgC Zig.AtomicOrder.relaxed Zig.AtomicOrder.relaxed 8 i91 i92 i70
                let i94 ← pure (v36)
                modify (fun s => { s with local33 := i94 })
                let i97 ← pure (((← get).local46).len)
                modify (fun s => { s with local34 := i97 })
                pure .br35)
              else (do
                pure .br74))
            | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
          | .br74 => (do
            let i101 ← Zig.add false i70 i68
            let i102 ← Zig.add false i73 p1
            let i103 ← pure (i101)
            let i104 ← pure (i102)
            let i105 ← pure (Zig.ge false i103 i104)
            let _i106 ← Zig.callRC (debug_assert i105)
            match ← ((do
              let i108 ← Zig.add false i70 i68
              let i109 ← Zig.add false i73 p1
              let i110 ← pure (i108)
              let i111 ← pure (i109)
              let i112 ← pure (i110 != i111)
              if i112 then (do
                let i114 ← Zig.callMC (Zig.ptrProject v36 (·.add 8))
                let i115 ← Zig.add false i70 i68
                let i116 ← Zig.add false i73 p1
                let _i117 ← Zig.cmpxchgC Zig.AtomicOrder.relaxed Zig.AtomicOrder.relaxed 8 i114 i115 i116
                pure .br107)
              else (do
                pure .br107)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
            | .br107 => (do
              let i120 ← pure ((← get).local46)
              let i121 ← pure i120.ptr
              let i122 ← Zig.callMC (Zig.ptrProject i121 (·.elem 1 i73))
              let i123 ← Zig.add false i73 p1
              let i124 ← pure i120.len
              let i125 ← pure (Zig.le false i123 i124)
              match ← ((do
                if i125 then (do
                  pure .br126)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
              | .br126 => (do
                let i131 ← Zig.callMC (Zig.checkSliceEnd i120.len i73 p1 0 >>= fun _ => pure (⟨i122, p1⟩ : Zig.Slice))
                modify (fun s => { s with local132 := i131 })
                let i136 ← pure (((← get).local132).ptr)
                match ← ((do
                  let i138 ← pure ((← get).cur_new_node)
                  let i139 ← pure ((i138).isSome)
                  if i139 then (do
                    let i141 ← Zig.optPayload i138
                    let i142 ← Zig.callMC (Zig.ptrProject i141 (·.add 16))
                    Zig.store (α := Option (Zig.Ptr)) 8 i142 none
                    let _i144 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i141 i141)
                    pure .br137)
                  else (do
                    pure .br137)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br137 => (do
                  let i147 ← pure (i136)
                  pure (.ret i147))
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
    | .br35 => (do
      match ← ((do
        match ← ((do
          let i153 ← pure ((← get).local33)
          let i154 ← pure ((i153).isSome)
          if i154 then (do
            let i156 ← Zig.optPayload i153
            pure (.br152 i156))
          else (do
            pure .br151)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
        | .br152 v152 => (do
          match ← ((do
            let i160 ← Zig.callC (heap_ArenaAllocator_Node_beginResize v152)
            let i161 ← pure ((i160).isSome)
            if i161 then (do
              let i163 ← Zig.optPayload i160
              pure (.br159 i163))
            else (do
              pure .br151)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
          | .br159 v159 => (do
            modify (fun s => { s with local166 := v159 })
            let i171 ← pure (((← get).local166).len)
            modify (fun s => { s with size := i171 })
            let i173 ← pure ((← get).local166)
            let i174 ← pure i173.ptr
            let i175 ← Zig.callMC (Zig.ptrProject i174 (·.elem 1 (24 : BitVec 64)))
            let i176 ← pure i173.len
            let i177 ← pure (Zig.le false (24 : BitVec 64) i176)
            match ← ((do
              if i177 then (do
                pure .br178)
              else (do
                throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
            | .br178 => (do
              let i183 ← Zig.sub false i176 (24 : BitVec 64)
              let i184 ← pure i173.len
              let i185 ← pure (Zig.le false i176 i184)
              match ← ((do
                if i185 then (do
                  pure .br186)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
              | .br186 => (do
                let i191 ← Zig.callMC (Zig.checkSliceEnd i173.len (24 : BitVec 64) i183 0 >>= fun _ => pure (⟨i175, i183⟩ : Zig.Slice))
                modify (fun s => { s with local192 := i191 })
                let i195 ← Zig.callMC (Zig.ptrProject v152 (·.add 8))
                let i196 ← pure (i195)
                let i197 ← Zig.atomicLoadC (n := 64) Zig.AtomicOrder.relaxed 8 i196
                let i199 ← pure (((← get).local192).ptr)
                let i200 ← Zig.callMC (heap_ArenaAllocator_alignedIndex i199 i197 p2)
                match ← ((do
                  let i202 ← Zig.add false (24 : BitVec 64) i200
                  let i203 ← Zig.callRC (heap_ArenaAllocator_nodeSizeFor i202 p1)
                  let i204 ← pure ((i203).isSome)
                  if i204 then (do
                    let i206 ← Zig.optPayload i203
                    pure (.br201 i206))
                  else (do
                    let i208 ← pure ((← get).size)
                    let i210 ← pure (((← get).local166).len)
                    let _i211 ← Zig.callC (heap_ArenaAllocator_Node_endResize v152 i208 i210)
                    pure .br151)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br201 v201 => (do
                  match ← ((do
                    let i215 ← pure (((← get).local166).len)
                    let i216 ← pure (v201)
                    let i217 ← pure (i215)
                    let i218 ← pure (Zig.le false i216 i217)
                    if i218 then (do
                      let i220 ← pure ((← get).size)
                      let i222 ← pure (((← get).local166).len)
                      let _i223 ← Zig.callC (heap_ArenaAllocator_Node_endResize v152 i220 i222)
                      pure .br32)
                    else (do
                      pure .br213)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br213 => (do
                    match ← ((do
                      let i227 ← pure i12
                      let i228 ← Zig.load (mem_Allocator) 8 i227
                      match ← ((do
                        pure .br229) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                      | .br229 => (do
                        let i231 ← Zig.callMC Zig.returnAddress
                        match ← ((do
                          let i233 ← pure ((i228).vtable)
                          let i234 ← Zig.callMC (Zig.ptrProject i233 (·.add 8))
                          let i235 ← Zig.load (Zig.Ptr) 8 i234
                          let i236 ← pure ((i228).ptr)
                          let i237 ← (if i235 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_resize i236 v159 mem_Alignment.«8» v201 i231) else if i235 == (⟨some 9, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_resize i236 v159 mem_Alignment.«8» v201 i231) else if i235 == (⟨some 13, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_resize i236 v159 mem_Alignment.«8» v201 i231) else throw .illegal)
                          pure (.br232 i237)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                        | .br232 v232 => (do
                          if v232 then (do
                            modify (fun s => { s with size := v201 })
                            match ← ((do
                              let i242 ← Zig.callMC (Zig.ptrProject v152 (·.add 8))
                              let i243 ← Zig.add false i200 p1
                              let i244 ← Zig.cmpxchgC Zig.AtomicOrder.acquire Zig.AtomicOrder.relaxed 8 i242 i197 i243
                              let i245 ← pure ((i244).isNone)
                              if i245 then (do
                                let i248 ← pure (((← get).local166).ptr)
                                let i249 ← pure i248
                                let i250 ← Zig.sub false v201 (0 : BitVec 64)
                                let i251 ← pure (⟨i249, i250⟩ : Zig.Slice)
                                let i252 ← pure i251.ptr
                                let i253 ← Zig.callMC (Zig.ptrProject i252 (·.elem 1 (24 : BitVec 64)))
                                let i254 ← pure i251.len
                                let i255 ← pure (Zig.le false (24 : BitVec 64) i254)
                                match ← ((do
                                  if i255 then (do
                                    pure .br256)
                                  else (do
                                    throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                | .br256 => (do
                                  let i261 ← Zig.sub false i254 (24 : BitVec 64)
                                  let i262 ← pure i251.len
                                  let i263 ← pure (Zig.le false i254 i262)
                                  match ← ((do
                                    if i263 then (do
                                      pure .br264)
                                    else (do
                                      throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                  | .br264 => (do
                                    let i269 ← Zig.callMC (Zig.checkSliceEnd i251.len (24 : BitVec 64) i261 0 >>= fun _ => pure (⟨i253, i261⟩ : Zig.Slice))
                                    let i270 ← pure i269.ptr
                                    let i271 ← Zig.callMC (Zig.ptrProject i270 (·.elem 1 i200))
                                    let i272 ← Zig.add false i200 p1
                                    let i273 ← pure i269.len
                                    let i274 ← pure (Zig.le false i272 i273)
                                    match ← ((do
                                      if i274 then (do
                                        pure .br275)
                                      else (do
                                        throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                    | .br275 => (do
                                      let i280 ← Zig.callMC (Zig.checkSliceEnd i269.len i200 p1 0 >>= fun _ => pure (⟨i271, p1⟩ : Zig.Slice))
                                      modify (fun s => { s with local281 := i280 })
                                      let i285 ← pure (((← get).local281).ptr)
                                      let i286 ← pure ((← get).size)
                                      let i288 ← pure (((← get).local166).len)
                                      let _i289 ← Zig.callC (heap_ArenaAllocator_Node_endResize v152 i286 i288)
                                      match ← ((do
                                        let i291 ← pure ((← get).cur_new_node)
                                        let i292 ← pure ((i291).isSome)
                                        if i292 then (do
                                          let i294 ← Zig.optPayload i291
                                          let i295 ← Zig.callMC (Zig.ptrProject i294 (·.add 16))
                                          Zig.store (α := Option (Zig.Ptr)) 8 i295 none
                                          let _i297 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i294 i294)
                                          pure .br290)
                                        else (do
                                          pure .br290)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                      | .br290 => (do
                                        let i300 ← pure (i285)
                                        pure (.ret i300))
                                      | e => pure e)
                                    | e => pure e)
                                  | e => pure e)
                                | e => pure e)
                              else (do
                                pure .br241)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                            | .br241 => (do
                              pure .br226)
                            | e => pure e)
                          else (do
                            pure .br226))
                        | e => pure e)
                      | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br226 => (do
                      let i305 ← pure ((← get).size)
                      let i307 ← pure (((← get).local166).len)
                      let _i308 ← Zig.callC (heap_ArenaAllocator_Node_endResize v152 i305 i307)
                      pure .br151)
                    | e => pure e)
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
      | .br151 => (do
        match ← ((do
          match ← ((do
            let i312 ← Zig.callC (heap_ArenaAllocator_stealFreeList i12)
            let i313 ← pure ((i312).isSome)
            if i313 then (do
              let i315 ← Zig.optPayload i312
              pure (.br311 i315))
            else (do
              pure .br310)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
          | .br311 v311 => (do
            match ← ((do
              modify (fun s => { s with best_fit_prev := none })
              modify (fun s => { s with best_fit := none })
              modify (fun s => { s with best_fit_diff := (18446744073709551615 : BitVec 64) })
              modify (fun s => { s with it_prev := none })
              let i332 ← pure (v311)
              modify (fun s => { s with it := i332 })
              match ← ((do
                Zig.loop (heap_ArenaAllocator_alloc.loop335 p1 p2) heap_ArenaAllocator_alloc.again335) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
              | .br334 => (do
                modify (fun s => { s with local318 := v311 })
                let i399 ← pure ((← get).it_prev)
                let i400 ← pure ((i399).isSome)
                match ← ((do
                  if i400 then (do
                    pure .br401)
                  else (do
                    throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br401 => (do
                  let i406 ← Zig.optPayload i399
                  modify (fun s => { s with local319 := i406 })
                  let i408 ← pure ((← get).best_fit)
                  let i409 ← pure ((i408).isSome)
                  match ← ((do
                    if i409 then (do
                      pure .br410)
                    else (do
                      throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br410 => (do
                    let i415 ← Zig.optPayload i408
                    modify (fun s => { s with local320 := i415 })
                    let i417 ← pure ((← get).best_fit_prev)
                    modify (fun s => { s with local321 := i417 })
                    pure .br322)
                  | e => pure e)
                | e => pure e)
              | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
            | .br322 => (do
              match ← ((do
                let i427 ← pure ((← get).local320)
                let i428 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe i427)
                let i429 ← pure i428.ptr
                let i430 ← Zig.callMC (Zig.ptrProject i429 (·.elem 1 (24 : BitVec 64)))
                let i431 ← pure i428.len
                let i432 ← pure (Zig.le false (24 : BitVec 64) i431)
                match ← ((do
                  if i432 then (do
                    pure .br433)
                  else (do
                    throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br433 => (do
                  let i438 ← Zig.sub false i431 (24 : BitVec 64)
                  let i439 ← pure i428.len
                  let i440 ← pure (Zig.le false i431 i439)
                  match ← ((do
                    if i440 then (do
                      pure .br441)
                    else (do
                      throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br441 => (do
                    let i446 ← Zig.callMC (Zig.checkSliceEnd i428.len (24 : BitVec 64) i438 0 >>= fun _ => pure (⟨i430, i438⟩ : Zig.Slice))
                    modify (fun s => { s with local447 := i446 })
                    let i451 ← pure (((← get).local447).ptr)
                    let i452 ← Zig.callMC (heap_ArenaAllocator_alignedIndex i451 (0 : BitVec 64) p2)
                    modify (fun s => { s with local424 := i452 })
                    let i455 ← pure (((← get).local447).len)
                    let i456 ← pure (i452)
                    let i457 ← pure (i455)
                    let i458 ← pure (Zig.gt false i456 i457)
                    match ← ((do
                      if i458 then (do
                        pure (.br459 true))
                      else (do
                        let i463 ← pure (((← get).local447).len)
                        let i464 ← Zig.sub false i463 i452
                        let i465 ← pure (p1)
                        let i466 ← pure (i464)
                        let i467 ← pure (Zig.gt false i465 i466)
                        pure (.br459 i467))) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br459 v459 => (do
                      modify (fun s => { s with local425 := v459 })
                      pure .br426)
                    | e => pure e)
                  | e => pure e)
                | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
              | .br426 => (do
                match ← ((do
                  let i474 ← pure ((← get).local425)
                  if i474 then (do
                    let i476 ← pure ((← get).local424)
                    let i477 ← Zig.add false (24 : BitVec 64) i476
                    let i478 ← Zig.callRC (heap_ArenaAllocator_nodeSizeFor i477 p1)
                    match ← ((do
                      let i480 ← pure ((i478).isSome)
                      match ← ((do
                        if i480 then (do
                          let i483 ← pure i12
                          let i484 ← Zig.load (mem_Allocator) 8 i483
                          let i485 ← pure ((← get).local320)
                          let i486 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe i485)
                          match ← ((do
                            pure .br487) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                          | .br487 => (do
                            let i489 ← pure ((i478).isSome)
                            match ← ((do
                              if i489 then (do
                                pure .br490)
                              else (do
                                throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                            | .br490 => (do
                              let i495 ← Zig.optPayload i478
                              let i496 ← Zig.callMC Zig.returnAddress
                              match ← ((do
                                let i498 ← pure ((i484).vtable)
                                let i499 ← Zig.callMC (Zig.ptrProject i498 (·.add 8))
                                let i500 ← Zig.load (Zig.Ptr) 8 i499
                                let i501 ← pure ((i484).ptr)
                                let i502 ← (if i500 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_resize i501 i486 mem_Alignment.«8» i495 i496) else if i500 == (⟨some 9, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_resize i501 i486 mem_Alignment.«8» i495 i496) else if i500 == (⟨some 13, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_resize i501 i486 mem_Alignment.«8» i495 i496) else throw .illegal)
                                pure (.br497 i502)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                              | .br497 v497 => (do
                                pure (.br481 v497))
                              | e => pure e)
                            | e => pure e)
                          | e => pure e)
                        else (do
                          pure (.br481 false))) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                      | .br481 v481 => (do
                        if v481 then (do
                          let i507 ← pure ((← get).local320)
                          let i508 ← pure i507
                          let i509 ← pure ((i478).isSome)
                          match ← ((do
                            if i509 then (do
                              pure .br510)
                            else (do
                              throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                          | .br510 => (do
                            let i515 ← Zig.optPayload i478
                            let i516 ← Zig.callRC (heap_ArenaAllocator_Node_Size_fromInt i515)
                            Zig.store (α := heap_ArenaAllocator_Node_Size) 8 i508 i516
                            pure .br479)
                          | e => pure e)
                        else (do
                          let i519 ← pure ((← get).local318)
                          let i520 ← pure ((← get).local319)
                          let _i521 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i519 i520)
                          pure .br310))
                      | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br479 => (do
                      pure .br473)
                    | e => pure e)
                  else (do
                    pure .br473)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br473 => (do
                  let i525 ← pure ((← get).local320)
                  let i526 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe i525)
                  let i527 ← pure i526.ptr
                  let i528 ← Zig.callMC (Zig.ptrProject i527 (·.elem 1 (24 : BitVec 64)))
                  let i529 ← pure i526.len
                  let i530 ← pure (Zig.le false (24 : BitVec 64) i529)
                  match ← ((do
                    if i530 then (do
                      pure .br531)
                    else (do
                      throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br531 => (do
                    let i536 ← Zig.sub false i529 (24 : BitVec 64)
                    let i537 ← pure i526.len
                    let i538 ← pure (Zig.le false i529 i537)
                    match ← ((do
                      if i538 then (do
                        pure .br539)
                      else (do
                        throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br539 => (do
                      let i544 ← Zig.callMC (Zig.checkSliceEnd i526.len (24 : BitVec 64) i536 0 >>= fun _ => pure (⟨i528, i536⟩ : Zig.Slice))
                      let i545 ← pure ((← get).local320)
                      let i546 ← Zig.callMC (Zig.ptrProject i545 (·.add 16))
                      let i547 ← Zig.load (Option (Zig.Ptr)) 8 i546
                      let i548 ← pure ((← get).local320)
                      let i549 ← Zig.callMC (Zig.ptrProject i548 (·.add 8))
                      let i550 ← pure ((← get).local424)
                      let i551 ← Zig.add false i550 p1
                      Zig.store (α := BitVec 64) 8 i549 i551
                      let i553 ← pure ((← get).local320)
                      let i554 ← Zig.callMC (Zig.ptrProject i553 (·.add 16))
                      let i555 ← pure ((← get).local33)
                      Zig.store (α := Option (Zig.Ptr)) 8 i554 i555
                      let i557 ← pure ((← get).local320)
                      let i558 ← Zig.callC (heap_ArenaAllocator_tryPushNode i12 i557)
                      let i559 ← pure (heap_ArenaAllocator_PushResult.tag i558)
                      match i559 with
                      | .success => (do
                        match ← ((do
                          let i564 ← pure ((← get).local321)
                          let i565 ← pure ((i564).isSome)
                          if i565 then (do
                            let i567 ← Zig.optPayload i564
                            let i568 ← Zig.callMC (Zig.ptrProject i567 (·.add 16))
                            Zig.store (α := Option (Zig.Ptr)) 8 i568 i547
                            pure .br563)
                          else (do
                            pure .br563)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                        | .br563 => (do
                          match ← ((do
                            let i573 ← pure ((← get).local320)
                            let i574 ← pure ((← get).local318)
                            let i575 ← Zig.callMC (Zig.ptrEqAddr i573 i574)
                            if i575 then (do
                              pure (.br572 i547))
                            else (do
                              let i578 ← pure ((← get).local318)
                              ((do
                                let i580 ← pure (i578)
                                pure (.br572 i580)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit))) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                          | .br572 v572 => (do
                            match ← ((do
                              let i583 ← pure ((← get).local320)
                              let i584 ← pure ((← get).local319)
                              let i585 ← Zig.callMC (Zig.ptrEqAddr i583 i584)
                              if i585 then (do
                                let i587 ← pure ((← get).local321)
                                pure (.br582 i587))
                              else (do
                                let i589 ← pure ((← get).local319)
                                ((do
                                  let i591 ← pure (i589)
                                  pure (.br582 i591)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit))) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                            | .br582 v582 => (do
                              match ← ((do
                                let i594 ← pure ((v572).isSome)
                                if i594 then (do
                                  let i596 ← Zig.optPayload v572
                                  let i597 ← pure ((v582).isSome)
                                  match ← ((do
                                    if i597 then (do
                                      pure .br598)
                                    else (do
                                      throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                  | .br598 => (do
                                    let i603 ← Zig.optPayload v582
                                    let _i604 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i596 i603)
                                    pure .br593)
                                  | e => pure e)
                                else (do
                                  pure .br593)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                              | .br593 => (do
                                let i607 ← pure ((← get).local424)
                                let i608 ← pure i544.ptr
                                let i609 ← Zig.callMC (Zig.ptrProject i608 (·.elem 1 i607))
                                let i610 ← Zig.add false i607 p1
                                let i611 ← pure i544.len
                                let i612 ← pure (Zig.le false i610 i611)
                                match ← ((do
                                  if i612 then (do
                                    pure .br613)
                                  else (do
                                    throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                | .br613 => (do
                                  let i618 ← Zig.callMC (Zig.checkSliceEnd i544.len i607 p1 0 >>= fun _ => pure (⟨i609, p1⟩ : Zig.Slice))
                                  modify (fun s => { s with local619 := i618 })
                                  let i623 ← pure (((← get).local619).ptr)
                                  match ← ((do
                                    let i625 ← pure ((← get).cur_new_node)
                                    let i626 ← pure ((i625).isSome)
                                    if i626 then (do
                                      let i628 ← Zig.optPayload i625
                                      let i629 ← Zig.callMC (Zig.ptrProject i628 (·.add 16))
                                      Zig.store (α := Option (Zig.Ptr)) 8 i629 none
                                      let _i631 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i628 i628)
                                      pure .br624)
                                    else (do
                                      pure .br624)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                  | .br624 => (do
                                    let i634 ← pure (i623)
                                    pure (.ret i634))
                                  | e => pure e)
                                | e => pure e)
                              | e => pure e)
                            | e => pure e)
                          | e => pure e)
                        | e => pure e)
                      | .failure => (do
                        let i636 ← Zig.callRC (heap_ArenaAllocator_PushResult.get_failure i558)
                        let i637 ← pure ((← get).local320)
                        let i638 ← Zig.callMC (Zig.ptrProject i637 (·.add 16))
                        Zig.store (α := Option (Zig.Ptr)) 8 i638 i547
                        let i640 ← pure ((← get).local318)
                        let i641 ← pure ((← get).local319)
                        let _i642 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i640 i641)
                        modify (fun s => { s with cur_first_node := i636 })
                        pure .br32))
                    | e => pure e)
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
        | .br310 => (do
          match ← ((do
            match ← ((do
              let i647 ← pure ((← get).cur_new_node)
              let i648 ← pure ((i647).isSome)
              if i648 then (do
                let i650 ← Zig.optPayload i647
                pure (.br645 i650))
              else (do
                pure .br646)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
            | .br646 => (do
              match ← ((do
                match ← ((do
                  let i655 ← Zig.callRC (mem_Alignment_toByteUnits p2)
                  let i656 ← Zig.add false (24 : BitVec 64) i655
                  let i657 ← Zig.callRC (math_add__anon_23f0cc3a812c i656 p1)
                  let i658 ← pure (Zig.isNonErr i657)
                  if i658 then (do
                    let i660 ← Zig.callRC (Zig.unwrapPayload i657)
                    pure (.br654 i660))
                  else (do
                    let _i662 ← Zig.callRC (Zig.unwrapErr i657)
                    match ← ((do
                      let i664 ← pure ((← get).cur_new_node)
                      let i665 ← pure ((i664).isSome)
                      if i665 then (do
                        let i667 ← Zig.optPayload i664
                        let i668 ← Zig.callMC (Zig.ptrProject i667 (·.add 16))
                        Zig.store (α := Option (Zig.Ptr)) 8 i668 none
                        let _i670 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i667 i667)
                        pure .br663)
                      else (do
                        pure .br663)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br663 => (do
                      pure (.ret none))
                    | e => pure e)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br654 v654 => (do
                  match ← ((do
                    let i675 ← pure ((← get).local34)
                    let i676 ← Zig.add false i675 (16 : BitVec 64)
                    let i677 ← Zig.callRC (math_add__anon_23f0cc3a812c i676 v654)
                    let i678 ← pure (Zig.isNonErr i677)
                    if i678 then (do
                      let i680 ← Zig.callRC (Zig.unwrapPayload i677)
                      pure (.br674 i680))
                    else (do
                      let _i682 ← Zig.callRC (Zig.unwrapErr i677)
                      match ← ((do
                        let i684 ← pure ((← get).cur_new_node)
                        let i685 ← pure ((i684).isSome)
                        if i685 then (do
                          let i687 ← Zig.optPayload i684
                          let i688 ← Zig.callMC (Zig.ptrProject i687 (·.add 16))
                          Zig.store (α := Option (Zig.Ptr)) 8 i688 none
                          let _i690 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i687 i687)
                          pure .br683)
                        else (do
                          pure .br683)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                      | .br683 => (do
                        pure (.ret none))
                      | e => pure e)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br674 v674 => (do
                    match ← ((do
                      let i695 ← Zig.divTrunc false v674 (2 : BitVec 64)
                      let i696 ← Zig.callRC (heap_ArenaAllocator_nodeSizeFor v674 i695)
                      let i697 ← pure ((i696).isSome)
                      if i697 then (do
                        let i699 ← Zig.optPayload i696
                        pure (.br694 i699))
                      else (do
                        match ← ((do
                          let i702 ← pure ((← get).cur_new_node)
                          let i703 ← pure ((i702).isSome)
                          if i703 then (do
                            let i705 ← Zig.optPayload i702
                            let i706 ← Zig.callMC (Zig.ptrProject i705 (·.add 16))
                            Zig.store (α := Option (Zig.Ptr)) 8 i706 none
                            let _i708 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i705 i705)
                            pure .br701)
                          else (do
                            pure .br701)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                        | .br701 => (do
                          pure (.ret none))
                        | e => pure e)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br694 v694 => (do
                      let i712 ← Zig.callRC (heap_ArenaAllocator_Node_Size_fromInt v694)
                      pure (.br653 i712))
                    | e => pure e)
                  | e => pure e)
                | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
              | .br653 v653 => (do
                match ← ((do
                  let i715 ← pure i12
                  let i716 ← Zig.load (mem_Allocator) 8 i715
                  let i717 ← Zig.callRC (heap_ArenaAllocator_Node_Size_toInt v653)
                  match ← ((do
                    pure .br718) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br718 => (do
                    let i720 ← Zig.callMC Zig.returnAddress
                    match ← ((do
                      let i722 ← pure ((i716).vtable)
                      let i723 ← pure i722
                      let i724 ← Zig.load (Zig.Ptr) 8 i723
                      let i725 ← pure ((i716).ptr)
                      let i726 ← (if i724 == (⟨some 2, 0⟩ : Zig.Ptr) then Zig.callC (heap_PageAllocator_alloc i725 i717 mem_Alignment.«8» i720) else if i724 == (⟨some 8, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_alloc i725 i717 mem_Alignment.«8» i720) else if i724 == (⟨some 12, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_alloc i725 i717 mem_Alignment.«8» i720) else throw .illegal)
                      pure (.br721 i726)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br721 v721 => (do
                      let i728 ← pure ((v721).isSome)
                      if i728 then (do
                        let i730 ← Zig.optPayload v721
                        pure (.br714 i730))
                      else (do
                        match ← ((do
                          let i733 ← pure ((← get).cur_new_node)
                          let i734 ← pure ((i733).isSome)
                          if i734 then (do
                            let i736 ← Zig.optPayload i733
                            let i737 ← Zig.callMC (Zig.ptrProject i736 (·.add 16))
                            Zig.store (α := Option (Zig.Ptr)) 8 i737 none
                            let _i739 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i736 i736)
                            pure .br732)
                          else (do
                            pure .br732)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                        | .br732 => (do
                          pure (.ret none))
                        | e => pure e))
                    | e => pure e)
                  | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br714 v714 => (do
                  let i743 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr v714)))
                  let i744 ← pure (i743 &&& (7 : BitVec 64))
                  let i745 ← pure (i744 == (0 : BitVec 64))
                  match ← ((do
                    if i745 then (do
                      pure .br746)
                    else (do
                      throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br746 => (do
                    let i751 ← Zig.callMC (Zig.checkAlign 8 v714 >>= fun _ => pure v714)
                    let i752 ← pure i751
                    Zig.store (α := heap_ArenaAllocator_Node_Size) 8 i752 v653
                    let i754 ← Zig.callMC (Zig.ptrProject i751 (·.add 8))
                    Zig.storeUndef (BitVec 64) 8 i754
                    let i756 ← Zig.callMC (Zig.ptrProject i751 (·.add 16))
                    Zig.storeUndef (Option (Zig.Ptr)) 8 i756
                    let i758 ← pure (i751)
                    modify (fun s => { s with cur_new_node := i758 })
                    pure (.br645 i751))
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
          | .br645 v645 => (do
            let i761 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe v645)
            let i762 ← pure i761.ptr
            let i763 ← Zig.callMC (Zig.ptrProject i762 (·.elem 1 (24 : BitVec 64)))
            let i764 ← pure i761.len
            let i765 ← pure (Zig.le false (24 : BitVec 64) i764)
            match ← ((do
              if i765 then (do
                pure .br766)
              else (do
                throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
            | .br766 => (do
              let i771 ← Zig.sub false i764 (24 : BitVec 64)
              let i772 ← pure i761.len
              let i773 ← pure (Zig.le false i764 i772)
              match ← ((do
                if i773 then (do
                  pure .br774)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
              | .br774 => (do
                let i779 ← Zig.callMC (Zig.checkSliceEnd i761.len (24 : BitVec 64) i771 0 >>= fun _ => pure (⟨i763, i771⟩ : Zig.Slice))
                modify (fun s => { s with local780 := i779 })
                let i784 ← pure (((← get).local780).ptr)
                let i785 ← Zig.callMC (heap_ArenaAllocator_alignedIndex i784 (0 : BitVec 64) p2)
                let i786 ← pure v645
                let i787 ← Zig.load (heap_ArenaAllocator_Node_Size) 8 i786
                let i788 ← Zig.callRC (heap_ArenaAllocator_Node_Size_toInt i787)
                let i789 ← Zig.add false (24 : BitVec 64) i785
                let i790 ← Zig.add false i789 p1
                let i791 ← pure (i788)
                let i792 ← pure (i790)
                let i793 ← pure (Zig.ge false i791 i792)
                let _i794 ← Zig.callRC (debug_assert i793)
                let i795 ← Zig.callMC (Zig.ptrProject v645 (·.add 8))
                let i796 ← Zig.add false i785 p1
                Zig.store (α := BitVec 64) 8 i795 i796
                let i798 ← Zig.callMC (Zig.ptrProject v645 (·.add 16))
                let i799 ← pure ((← get).local33)
                Zig.store (α := Option (Zig.Ptr)) 8 i798 i799
                let i801 ← Zig.callC (heap_ArenaAllocator_tryPushNode i12 v645)
                let i802 ← pure (heap_ArenaAllocator_PushResult.tag i801)
                match ← ((do
                  match i802 with
                  | .success => (do
                    modify (fun s => { s with cur_new_node := none })
                    let i808 ← pure ((← get).local780)
                    let i809 ← pure i808.ptr
                    let i810 ← Zig.callMC (Zig.ptrProject i809 (·.elem 1 i785))
                    let i811 ← Zig.add false i785 p1
                    let i812 ← pure i808.len
                    let i813 ← pure (Zig.le false i811 i812)
                    match ← ((do
                      if i813 then (do
                        pure .br814)
                      else (do
                        throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br814 => (do
                      let i819 ← Zig.callMC (Zig.checkSliceEnd i808.len i785 p1 0 >>= fun _ => pure (⟨i810, p1⟩ : Zig.Slice))
                      modify (fun s => { s with local820 := i819 })
                      let i824 ← pure (((← get).local820).ptr)
                      match ← ((do
                        let i826 ← pure ((← get).cur_new_node)
                        let i827 ← pure ((i826).isSome)
                        if i827 then (do
                          let i829 ← Zig.optPayload i826
                          let i830 ← Zig.callMC (Zig.ptrProject i829 (·.add 16))
                          Zig.store (α := Option (Zig.Ptr)) 8 i830 none
                          let _i832 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i829 i829)
                          pure .br825)
                        else (do
                          pure .br825)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                      | .br825 => (do
                        let i835 ← pure (i824)
                        pure (.ret i835))
                      | e => pure e)
                    | e => pure e)
                  | .failure => (do
                    let i837 ← Zig.callRC (heap_ArenaAllocator_PushResult.get_failure i801)
                    modify (fun s => { s with cur_first_node := i837 })
                    pure .br803)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br803 => (do
                  pure .br32)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
  | .br32 => (do
    pure .rep31)
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
      let i12 ← Zig.callMC (Zig.checkAlign 8 p0 >>= fun _ => pure p0)
      let i13 ← pure (p1)
      let i14 ← pure (Zig.gt false i13 (0 : BitVec 64))
      let _i15 ← Zig.callRC (debug_assert i14)
      match ← ((do
        let i17 ← Zig.callRC (mem_Alignment_toByteUnits p2)
        let i18 ← Zig.sub false i17 (1 : BitVec 64)
        let i19 ← Zig.sub false (18446744073709551615 : BitVec 64) i18
        let i20 ← pure (p1)
        let i21 ← pure (i19)
        let i22 ← pure (Zig.gt false i20 i21)
        if i22 then (do
          pure (.ret none))
        else (do
          pure .br16)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
      | .br16 => (do
        let i27 ← Zig.callC (heap_ArenaAllocator_loadFirstNode i12)
        modify (fun s => { s with cur_first_node := i27 })
        modify (fun s => { s with cur_new_node := none })
        Zig.loop (heap_ArenaAllocator_alloc.loop31 p1 p2 i12) heap_ArenaAllocator_alloc.again31)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit).run' (default : heap_ArenaAllocator_allocLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic
partial_fixpoint

end

structure mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bLocals where
  deriving Inhabited

inductive mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3
  | br10 (v : Option (Zig.Ptr))
  | br9 (v : Zig.Ptr)

def mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8b (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (⟨none, 18446744073709551615⟩ : Zig.Ptr) : Except Zig.ErrName (Zig.Ptr))))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bLocals mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bExit) with
    | .br3 => (do
      match ← ((do
        match ← ((do
          let i11 ← pure ((p0).vtable)
          let i12 ← pure i11
          let i13 ← Zig.load (Zig.Ptr) 8 i12
          let i14 ← pure ((p0).ptr)
          let i15 ← (if i13 == (⟨some 2, 0⟩ : Zig.Ptr) then Zig.callC (heap_PageAllocator_alloc i14 p1 mem_Alignment.«1» p2) else if i13 == (⟨some 8, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_alloc i14 p1 mem_Alignment.«1» p2) else if i13 == (⟨some 12, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_alloc i14 p1 mem_Alignment.«1» p2) else throw .illegal)
          pure (.br10 i15)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bLocals mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bExit) with
        | .br10 v10 => (do
          let i17 ← pure ((v10).isSome)
          if i17 then (do
            let i19 ← Zig.optPayload v10
            pure (.br9 i19))
          else (do
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr)))))
        | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bLocals mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bExit) with
      | .br9 v9 => (do
        let i22 ← pure v9
        let i23 ← Zig.sub false p1 (0 : BitVec 64)
        let i24 ← pure (⟨i22, i23⟩ : Zig.Slice)
        let _i25 ← pure i24.len
        Zig.callMC (Zig.memset (α := BitVec 8) 1 i24.ptr i24.len none)
        let i27 ← pure (v9)
        let i28 ← pure ((.ok i27) : Except Zig.ErrName (Zig.Ptr))
        pure (.ret i28))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bLocals mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bExit).run' (default : mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8bLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

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
      let i11 ← Zig.callC (mem_Allocator_allocBytesWithAlignment__anon_1446b3d5ad8b p0 v3 p2)
      pure (.ret i11))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Locals mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Exit).run' (default : mem_Allocator_allocWithSizeAndAlignment__anon_0aadb2616c43Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_alloc__anon_a8254a5f2b74Locals where
  deriving Inhabited

inductive mem_Allocator_alloc__anon_a8254a5f2b74Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br3 (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_alloc__anon_a8254a5f2b74 (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
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
        let i10 ← Zig.sub false p1 (0 : BitVec 64)
        let i11 ← pure (⟨i9, i10⟩ : Zig.Slice)
        let i12 ← pure ((.ok i11) : Except Zig.ErrName (Zig.Slice))
        pure (.br3 i12))) : Zig.CM Tgt mem_Allocator_alloc__anon_a8254a5f2b74Locals mem_Allocator_alloc__anon_a8254a5f2b74Exit) with
    | .br3 v3 => (do
      let i14 ← pure (v3)
      pure (.ret i14))
    | e => pure e) : Zig.CM Tgt mem_Allocator_alloc__anon_a8254a5f2b74Locals mem_Allocator_alloc__anon_a8254a5f2b74Exit).run' (default : mem_Allocator_alloc__anon_a8254a5f2b74Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure arena_oom_freeLocals where
  fba : Zig.Ptr
  arena : Zig.Ptr
  deriving Inhabited

inductive arena_oom_freeExit where
  | ret (v : Bool)
  | br9 (v : Zig.Slice)
  | br17

def arena_oom_free (p0 : BitVec 64) : Zig.ConcM Tgt (Bool) := do
  let s1 ← Zig.allocStack 24 8
  let s4 ← Zig.allocStack 32 8
  let e ← ((do
    let i1 ← pure (← get).fba
    let i2 ← Zig.callMC (heap_FixedBufferAllocator_init (⟨(⟨some 7, 0⟩ : Zig.Ptr), (256 : BitVec 64)⟩ : Zig.Slice))
    Zig.store (α := heap_FixedBufferAllocator) 8 i1 i2
    let i4 ← pure (← get).arena
    let i5 ← Zig.callMC (heap_FixedBufferAllocator_allocator i1)
    let i6 ← Zig.callMC (heap_ArenaAllocator_init i5)
    Zig.store (α := heap_ArenaAllocator) 8 i4 i6
    let i8 ← Zig.callMC (heap_ArenaAllocator_allocator i4)
    match ← ((do
      let i10 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 i8 p0)
      let i11 ← pure (Zig.isNonErr i10)
      if i11 then (do
        let i13 ← Zig.callRC (Zig.unwrapPayload i10)
        pure (.br9 i13))
      else (do
        let _i15 ← Zig.callRC (Zig.unwrapErr i10)
        pure (.ret false))) : Zig.CM Tgt arena_oom_freeLocals arena_oom_freeExit) with
    | .br9 v9 => (do
      match ← ((do
        let i18 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 i8 (4096 : BitVec 64))
        let i19 ← pure (Zig.isNonErr i18)
        if i19 then (do
          let _i21 ← Zig.callRC (Zig.unwrapPayload i18)
          pure .br17)
        else (do
          let _i23 ← Zig.callRC (Zig.unwrapErr i18)
          pure .br17)) : Zig.CM Tgt arena_oom_freeLocals arena_oom_freeExit) with
      | .br17 => (do
        let _i25 ← Zig.callC (mem_Allocator_free__anon_1e60e7ef40f5 i8 v9)
        pure (.ret true))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt arena_oom_freeLocals arena_oom_freeExit).run' { (default : arena_oom_freeLocals) with fba := s1, arena := s4 }
  Zig.free s1
  Zig.free s4
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_allocBytesWithAlignment__anon_f686c272daf7Locals where
  deriving Inhabited

inductive mem_Allocator_allocBytesWithAlignment__anon_f686c272daf7Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3
  | br10 (v : Option (Zig.Ptr))
  | br9 (v : Zig.Ptr)
  | br30

def mem_Allocator_allocBytesWithAlignment__anon_f686c272daf7 (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (⟨none, 18446744073709551608⟩ : Zig.Ptr) : Except Zig.ErrName (Zig.Ptr))))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_f686c272daf7Locals mem_Allocator_allocBytesWithAlignment__anon_f686c272daf7Exit) with
    | .br3 => (do
      match ← ((do
        match ← ((do
          let i11 ← pure ((p0).vtable)
          let i12 ← pure i11
          let i13 ← Zig.load (Zig.Ptr) 8 i12
          let i14 ← pure ((p0).ptr)
          let i15 ← (if i13 == (⟨some 2, 0⟩ : Zig.Ptr) then Zig.callC (heap_PageAllocator_alloc i14 p1 mem_Alignment.«8» p2) else if i13 == (⟨some 8, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_alloc i14 p1 mem_Alignment.«8» p2) else if i13 == (⟨some 12, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_alloc i14 p1 mem_Alignment.«8» p2) else throw .illegal)
          pure (.br10 i15)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_f686c272daf7Locals mem_Allocator_allocBytesWithAlignment__anon_f686c272daf7Exit) with
        | .br10 v10 => (do
          let i17 ← pure ((v10).isSome)
          if i17 then (do
            let i19 ← Zig.optPayload v10
            pure (.br9 i19))
          else (do
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr)))))
        | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_f686c272daf7Locals mem_Allocator_allocBytesWithAlignment__anon_f686c272daf7Exit) with
      | .br9 v9 => (do
        let i22 ← pure v9
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
            throw .panic)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_f686c272daf7Locals mem_Allocator_allocBytesWithAlignment__anon_f686c272daf7Exit) with
        | .br30 => (do
          let i35 ← Zig.callMC (Zig.checkAlign 8 v9 >>= fun _ => pure v9)
          let i36 ← pure ((.ok i35) : Except Zig.ErrName (Zig.Ptr))
          pure (.ret i36))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_f686c272daf7Locals mem_Allocator_allocBytesWithAlignment__anon_f686c272daf7Exit).run' (default : mem_Allocator_allocBytesWithAlignment__anon_f686c272daf7Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_create__anon_496c6df2f4baLocals where
  deriving Inhabited

inductive mem_Allocator_create__anon_496c6df2f4baExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

def mem_Allocator_create__anon_496c6df2f4ba (p0 : mem_Allocator) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    let i1 ← Zig.callMC Zig.returnAddress
    let i2 ← Zig.callC (mem_Allocator_allocBytesWithAlignment__anon_f686c272daf7 p0 (8 : BitVec 64) i1)
    match i2 with
    | .error _ => (do
      let i4 ← Zig.callRC (Zig.unwrapErr i2)
      let i5 ← pure ((.error i4) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i5))
    | .ok v3 => (do
      let i7 ← pure (v3)
      let i8 ← pure ((.ok i7) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i8))) : Zig.CM Tgt mem_Allocator_create__anon_496c6df2f4baLocals mem_Allocator_create__anon_496c6df2f4baExit).run' (default : mem_Allocator_create__anon_496c6df2f4baLocals)
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
      let i25 ← Zig.callMC (Zig.ptrProject i24 (·.add 16))
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
          let i35 ← Zig.callMC (Zig.ptrProject i34 (·.add 24))
          let i36 ← Zig.load (Zig.Ptr) 8 i35
          let i37 ← pure ((i28).ptr)
          let _i38 ← (if i36 == (⟨some 5, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_free i37 i29 mem_Alignment.«8» i32) else if i36 == (⟨some 11, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_free i37 i29 mem_Alignment.«8» i32) else if i36 == (⟨some 15, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_free i37 i29 mem_Alignment.«8» i32) else throw .illegal)
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
      let i6 ← Zig.callC (mem_Allocator_create__anon_496c6df2f4ba i4)
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
        let i18 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 i4 p0)
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
          let i37 ← Zig.callMC (Zig.checkIndex v17 (0 : BitVec 64) >>= fun _ => Zig.load (BitVec 8) 1 (v17.ptr.elem 1 (0 : BitVec 64)))
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
      let i13 ← pure i11
      let i14 ← Zig.load (heap_ArenaAllocator_Node_Size) 8 i13
      let i15 ← Zig.callR (heap_ArenaAllocator_Node_Size_toInt i14)
      let i16 ← Zig.sub false i15 (24 : BitVec 64)
      let i17 ← Zig.add false i12 i16
      modify (fun s => { s with capacity := i17 })
      let i19 ← Zig.callM (Zig.ptrProject i11 (·.add 16))
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
      let i84 ← Zig.callMC (Zig.ptrProject i83 (·.add 16))
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
        let i93 ← pure p0
        let i94 ← Zig.load (mem_Allocator) 8 i93
        let i95 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe i83)
        match ← ((do
          pure .br96) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
        | .br96 => (do
          let i98 ← Zig.callMC Zig.returnAddress
          match ← ((do
            let i100 ← pure ((i94).vtable)
            let i101 ← Zig.callMC (Zig.ptrProject i100 (·.add 24))
            let i102 ← Zig.load (Zig.Ptr) 8 i101
            let i103 ← pure ((i94).ptr)
            let _i104 ← (if i102 == (⟨some 5, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_free i103 i95 mem_Alignment.«8» i98) else if i102 == (⟨some 11, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_free i103 i95 mem_Alignment.«8» i98) else if i102 == (⟨some 15, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_free i103 i95 mem_Alignment.«8» i98) else throw .illegal)
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
        let i111 ← Zig.callRC (mem_alignBackward__anon_f056e98f6fd2 i110 (2 : BitVec 64))
        match ← ((do
          let i113 ← pure (i111)
          let i114 ← pure (i113 == (24 : BitVec 64))
          if i114 then (do
            let i116 ← pure p0
            let i117 ← Zig.load (mem_Allocator) 8 i116
            match ← ((do
              pure .br118) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
            | .br118 => (do
              let i120 ← Zig.callMC Zig.returnAddress
              match ← ((do
                let i122 ← pure ((i117).vtable)
                let i123 ← Zig.callMC (Zig.ptrProject i122 (·.add 24))
                let i124 ← Zig.load (Zig.Ptr) 8 i123
                let i125 ← pure ((i117).ptr)
                let _i126 ← (if i124 == (⟨some 5, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_free i125 i109 mem_Alignment.«8» i120) else if i124 == (⟨some 11, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_free i125 i109 mem_Alignment.«8» i120) else if i124 == (⟨some 15, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_free i125 i109 mem_Alignment.«8» i120) else throw .illegal)
                pure .br121) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
              | .br121 => (do
                Zig.store (α := Option (Zig.Ptr)) 8 i72 none
                pure .br68)
              | e => pure e)
            | e => pure e)
          else (do
            pure .br112)) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
        | .br112 => (do
          let i131 ← Zig.callMC (Zig.ptrProject v77 (·.add 8))
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
              let i144 ← pure p0
              let i145 ← Zig.load (mem_Allocator) 8 i144
              match ← ((do
                pure .br146) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
              | .br146 => (do
                let i148 ← Zig.callMC Zig.returnAddress
                match ← ((do
                  let i150 ← pure ((i145).vtable)
                  let i151 ← Zig.callMC (Zig.ptrProject i150 (·.add 8))
                  let i152 ← Zig.load (Zig.Ptr) 8 i151
                  let i153 ← pure ((i145).ptr)
                  let i154 ← (if i152 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_resize i153 i109 mem_Alignment.«8» i111 i148) else if i152 == (⟨some 9, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_resize i153 i109 mem_Alignment.«8» i111 i148) else if i152 == (⟨some 13, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_resize i153 i109 mem_Alignment.«8» i111 i148) else throw .illegal)
                  pure (.br149 i154)) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
                | .br149 v149 => (do
                  if v149 then (do
                    let i157 ← pure v77
                    let i158 ← Zig.callRC (heap_ArenaAllocator_Node_Size_fromInt i111)
                    Zig.store (α := heap_ArenaAllocator_Node_Size) 8 i157 i158
                    pure .br143)
                  else (do
                    match ← ((do
                      let i162 ← pure p0
                      let i163 ← Zig.load (mem_Allocator) 8 i162
                      match ← ((do
                        pure .br164) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
                      | .br164 => (do
                        let i166 ← Zig.callMC Zig.returnAddress
                        match ← ((do
                          let i168 ← pure ((i163).vtable)
                          let i169 ← pure i168
                          let i170 ← Zig.load (Zig.Ptr) 8 i169
                          let i171 ← pure ((i163).ptr)
                          let i172 ← (if i170 == (⟨some 2, 0⟩ : Zig.Ptr) then Zig.callC (heap_PageAllocator_alloc i171 i111 mem_Alignment.«8» i166) else if i170 == (⟨some 8, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_alloc i171 i111 mem_Alignment.«8» i166) else if i170 == (⟨some 12, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_alloc i171 i111 mem_Alignment.«8» i166) else throw .illegal)
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
                      let i180 ← pure p0
                      let i181 ← Zig.load (mem_Allocator) 8 i180
                      match ← ((do
                        pure .br182) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
                      | .br182 => (do
                        let i184 ← Zig.callMC Zig.returnAddress
                        match ← ((do
                          let i186 ← pure ((i181).vtable)
                          let i187 ← Zig.callMC (Zig.ptrProject i186 (·.add 24))
                          let i188 ← Zig.load (Zig.Ptr) 8 i187
                          let i189 ← pure ((i181).ptr)
                          let _i190 ← (if i188 == (⟨some 5, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_free i189 i109 mem_Alignment.«8» i184) else if i188 == (⟨some 11, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_free i189 i109 mem_Alignment.«8» i184) else if i188 == (⟨some 15, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_free i189 i109 mem_Alignment.«8» i184) else throw .illegal)
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
                            let i200 ← Zig.callMC (Zig.checkAlign 8 v161 >>= fun _ => pure v161)
                            let i201 ← pure i200
                            let i202 ← Zig.callRC (heap_ArenaAllocator_Node_Size_fromInt i111)
                            Zig.store (α := heap_ArenaAllocator_Node_Size) 8 i201 i202
                            let i204 ← Zig.callMC (Zig.ptrProject i200 (·.add 8))
                            Zig.store (α := BitVec 64) 8 i204 (0 : BitVec 64)
                            let i206 ← Zig.callMC (Zig.ptrProject i200 (·.add 16))
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
          let i17 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
          Zig.store (α := heap_ArenaAllocator_State) 8 i17 ({ used_list := none, free_list := none } : heap_ArenaAllocator_State)
          pure (.ret true))
        else (do
          pure .br12)) : Zig.CM Tgt heap_ArenaAllocator_resetLocals heap_ArenaAllocator_resetExit) with
      | .br12 => (do
        let i21 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
        let i22 ← pure i21
        let i23 ← Zig.load (Option (Zig.Ptr)) 8 i22
        let i24 ← Zig.callMC (heap_ArenaAllocator_countListCapacity i23)
        let i25 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
        let i26 ← Zig.callMC (Zig.ptrProject i25 (·.add 8))
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
            let i57 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
            let i58 ← pure i57
            let i59 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
            let i60 ← Zig.callMC (Zig.ptrProject i59 (·.add 8))
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
      let i11 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 i9 p0)
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
        let i21 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 i9 p0)
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
            let i36 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 i9 p0)
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

structure mem_Allocator_resize__anon_ec6bca265858Locals where
  deriving Inhabited

inductive mem_Allocator_resize__anon_ec6bca265858Exit where
  | ret (v : Bool)
  | br3
  | br10
  | br19 (v : BitVec 64)
  | br29 (v : Bool)

def mem_Allocator_resize__anon_ec6bca265858 (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p2)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        let _i7 ← Zig.callC (mem_Allocator_free__anon_1e60e7ef40f5 p0 p1)
        pure (.ret true))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_resize__anon_ec6bca265858Locals mem_Allocator_resize__anon_ec6bca265858Exit) with
    | .br3 => (do
      match ← ((do
        let i11 ← pure p1.len
        let i12 ← pure (i11)
        let i13 ← pure (i12 == (0 : BitVec 64))
        if i13 then (do
          pure (.ret false))
        else (do
          pure .br10)) : Zig.CM Tgt mem_Allocator_resize__anon_ec6bca265858Locals mem_Allocator_resize__anon_ec6bca265858Exit) with
      | .br10 => (do
        let i17 ← Zig.callMC (mem_absorbSentinel__anon_7342b53a30ed p1)
        let i18 ← pure (i17)
        match ← ((do
          let i20 ← Zig.callRC (math_mul__anon_44faaf286c79 (1 : BitVec 64) p2)
          let i21 ← pure (Zig.isNonErr i20)
          if i21 then (do
            let i23 ← Zig.callRC (Zig.unwrapPayload i20)
            pure (.br19 i23))
          else (do
            let _i25 ← Zig.callRC (Zig.unwrapErr i20)
            pure (.ret false))) : Zig.CM Tgt mem_Allocator_resize__anon_ec6bca265858Locals mem_Allocator_resize__anon_ec6bca265858Exit) with
        | .br19 v19 => (do
          let i27 ← Zig.callRC (mem_Alignment_fromByteUnits (1 : BitVec 64))
          let i28 ← Zig.callMC Zig.returnAddress
          match ← ((do
            let i30 ← pure ((p0).vtable)
            let i31 ← Zig.callMC (Zig.ptrProject i30 (·.add 8))
            let i32 ← Zig.load (Zig.Ptr) 8 i31
            let i33 ← pure ((p0).ptr)
            let i34 ← (if i32 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_resize i33 i18 i27 v19 i28) else if i32 == (⟨some 9, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_resize i33 i18 i27 v19 i28) else if i32 == (⟨some 13, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_resize i33 i18 i27 v19 i28) else throw .illegal)
            pure (.br29 i34)) : Zig.CM Tgt mem_Allocator_resize__anon_ec6bca265858Locals mem_Allocator_resize__anon_ec6bca265858Exit) with
          | .br29 v29 => (do
            pure (.ret v29))
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_resize__anon_ec6bca265858Locals mem_Allocator_resize__anon_ec6bca265858Exit).run' (default : mem_Allocator_resize__anon_ec6bca265858Locals)
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
      let i11 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 i9 p0)
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
      let i20 ← Zig.callC (mem_Allocator_resize__anon_ec6bca265858 i9 v10 p1)
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
      let i34 ← Zig.callMC (Zig.checkIndex i9 i28 >>= fun _ => Zig.load (BitVec 8) 1 (i9.ptr.elem 1 i28))
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
      let i10 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 i8 p0)
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
        let _i44 ← Zig.callC (mem_Allocator_free__anon_1e60e7ef40f5 i8 v9)
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

structure arena_threeLocals where
  fba : Zig.Ptr
  arena : Zig.Ptr
  deriving Inhabited

inductive arena_threeExit where
  | ret (v : BitVec 64)
  | br9 (v : Zig.Slice)
  | br19 (v : Zig.Slice)
  | br29 (v : Zig.Slice)
  | br47
  | br56
  | br67

def arena_three (p0 : BitVec 64) : Zig.ConcM Tgt (BitVec 64) := do
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
      let i10 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 i8 p0)
      let i11 ← pure (Zig.isNonErr i10)
      if i11 then (do
        let i13 ← Zig.callRC (Zig.unwrapPayload i10)
        pure (.br9 i13))
      else (do
        let _i15 ← Zig.callRC (Zig.unwrapErr i10)
        let i16 ← Zig.load (heap_ArenaAllocator) 8 i4
        let _i17 ← Zig.callC (heap_ArenaAllocator_deinit i16)
        pure (.ret (0 : BitVec 64)))) : Zig.CM Tgt arena_threeLocals arena_threeExit) with
    | .br9 v9 => (do
      match ← ((do
        let i20 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 i8 p0)
        let i21 ← pure (Zig.isNonErr i20)
        if i21 then (do
          let i23 ← Zig.callRC (Zig.unwrapPayload i20)
          pure (.br19 i23))
        else (do
          let _i25 ← Zig.callRC (Zig.unwrapErr i20)
          let i26 ← Zig.load (heap_ArenaAllocator) 8 i4
          let _i27 ← Zig.callC (heap_ArenaAllocator_deinit i26)
          pure (.ret (1 : BitVec 64)))) : Zig.CM Tgt arena_threeLocals arena_threeExit) with
      | .br19 v19 => (do
        match ← ((do
          let i30 ← Zig.callC (mem_Allocator_alloc__anon_a8254a5f2b74 i8 p0)
          let i31 ← pure (Zig.isNonErr i30)
          if i31 then (do
            let i33 ← Zig.callRC (Zig.unwrapPayload i30)
            pure (.br29 i33))
          else (do
            let _i35 ← Zig.callRC (Zig.unwrapErr i30)
            let i36 ← Zig.load (heap_ArenaAllocator) 8 i4
            let _i37 ← Zig.callC (heap_ArenaAllocator_deinit i36)
            pure (.ret (2 : BitVec 64)))) : Zig.CM Tgt arena_threeLocals arena_threeExit) with
        | .br29 v29 => (do
          let _i39 ← pure v9.len
          Zig.callMC (Zig.memset (α := BitVec 8) 1 v9.ptr v9.len (some (1 : BitVec 8)))
          let _i41 ← pure v19.len
          Zig.callMC (Zig.memset (α := BitVec 8) 1 v19.ptr v19.len (some (2 : BitVec 8)))
          let _i43 ← pure v29.len
          Zig.callMC (Zig.memset (α := BitVec 8) 1 v29.ptr v29.len (some (3 : BitVec 8)))
          let i45 ← pure v9.len
          let i46 ← pure (Zig.lt false (0 : BitVec 64) i45)
          match ← ((do
            if i46 then (do
              pure .br47)
            else (do
              throw .outOfBounds)) : Zig.CM Tgt arena_threeLocals arena_threeExit) with
          | .br47 => (do
            let i52 ← Zig.callMC (Zig.checkIndex v9 (0 : BitVec 64) >>= fun _ => Zig.load (BitVec 8) 1 (v9.ptr.elem 1 (0 : BitVec 64)))
            let i53 ← Zig.intCast false false 64 i52
            let i54 ← pure v19.len
            let i55 ← pure (Zig.lt false (0 : BitVec 64) i54)
            match ← ((do
              if i55 then (do
                pure .br56)
              else (do
                throw .outOfBounds)) : Zig.CM Tgt arena_threeLocals arena_threeExit) with
            | .br56 => (do
              let i61 ← Zig.callMC (Zig.checkIndex v19 (0 : BitVec 64) >>= fun _ => Zig.load (BitVec 8) 1 (v19.ptr.elem 1 (0 : BitVec 64)))
              let i62 ← Zig.intCast false false 64 i61
              let i63 ← Zig.mul false (10 : BitVec 64) i62
              let i64 ← Zig.add false i53 i63
              let i65 ← pure v29.len
              let i66 ← pure (Zig.lt false (0 : BitVec 64) i65)
              match ← ((do
                if i66 then (do
                  pure .br67)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt arena_threeLocals arena_threeExit) with
              | .br67 => (do
                let i72 ← Zig.callMC (Zig.checkIndex v29 (0 : BitVec 64) >>= fun _ => Zig.load (BitVec 8) 1 (v29.ptr.elem 1 (0 : BitVec 64)))
                let i73 ← Zig.intCast false false 64 i72
                let i74 ← Zig.mul false (100 : BitVec 64) i73
                let i75 ← Zig.add false i64 i74
                let i76 ← Zig.load (heap_ArenaAllocator) 8 i4
                let _i77 ← Zig.callC (heap_ArenaAllocator_deinit i76)
                pure (.ret i75))
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt arena_threeLocals arena_threeExit).run' { (default : arena_threeLocals) with fba := s1, arena := s4 }
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

end AllocArena.ArenaFixedLinux