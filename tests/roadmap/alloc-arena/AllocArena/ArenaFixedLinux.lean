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
  -- 0: arena.small
  (Array.replicate (Zig.Enc.size (Vector (BitVec 8) 256)) .undef, 1, .global),
  -- 1: heap.PageAllocator.vtable
  (Zig.Enc.encode (({ alloc := (⟨some 3, 0⟩ : Zig.Ptr), resize := (⟨some 4, 0⟩ : Zig.Ptr), remap := (⟨some 5, 0⟩ : Zig.Ptr), free := (⟨some 6, 0⟩ : Zig.Ptr) } : mem_Allocator_VTable) : mem_Allocator_VTable), 8, .constGlobal),
  -- 2: arena.buffer
  (Array.replicate (Zig.Enc.size (Vector (BitVec 8) 4096)) .undef, 1, .global),
  -- 3: heap.PageAllocator.alloc
  (#[.undef], 1, .constGlobal),
  -- 4: heap.PageAllocator.resize
  (#[.undef], 1, .constGlobal),
  -- 5: heap.PageAllocator.remap
  (#[.undef], 1, .constGlobal),
  -- 6: heap.PageAllocator.free
  (#[.undef], 1, .constGlobal),
  -- 7: arena.node_buf
  (Array.replicate (Zig.Enc.size (Vector (BitVec 64) 8)) .undef, 8, .global),
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
  | br52
  | br68
  | br89

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
          let i39 ← Zig.callC (heap_ArenaAllocator_Node_loadBuf i32)
          let i40 ← pure i39.len
          let i41 ← pure (i37)
          let i42 ← pure (i40)
          let i43 ← pure (Zig.gt false i41 i42)
          if i43 then (do
            let i46 ← pure (((← get).local5).len)
            let i47 ← pure (p3)
            let i48 ← pure (i46)
            let i49 ← pure (Zig.le false i47 i48)
            pure (.ret i49))
          else (do
            pure .br38)) : Zig.CM Tgt heap_ArenaAllocator_resizeLocals heap_ArenaAllocator_resizeExit) with
        | .br38 => (do
          match ← ((do
            let i53 ← Zig.callMC (Zig.ptrProject i34 (·.elem 1 i37))
            let i55 ← pure (((← get).local5).ptr)
            let i57 ← pure (((← get).local5).len)
            let i58 ← Zig.callMC (Zig.ptrProject i55 (·.elem 1 i57))
            let i59 ← Zig.callMC (do pure (!(← Zig.ptrEqAddr i53 i58)))
            if i59 then (do
              let i62 ← pure (((← get).local5).len)
              let i63 ← pure (p3)
              let i64 ← pure (i62)
              let i65 ← pure (Zig.le false i63 i64)
              pure (.ret i65))
            else (do
              pure .br52)) : Zig.CM Tgt heap_ArenaAllocator_resizeLocals heap_ArenaAllocator_resizeExit) with
          | .br52 => (do
            match ← ((do
              let i70 ← pure (((← get).local5).len)
              let i71 ← pure (p3)
              let i72 ← pure (i70)
              let i73 ← pure (Zig.le false i71 i72)
              if i73 then (do
                let i76 ← pure (((← get).local5).len)
                let i77 ← Zig.sub false i76 p3
                let i78 ← Zig.sub false i37 i77
                let i79 ← Zig.callMC (Zig.ptrProject i34 (·.elem 1 i78))
                let i81 ← pure (((← get).local5).ptr)
                let i82 ← Zig.callMC (Zig.ptrProject i81 (·.elem 1 p3))
                let i83 ← Zig.callMC (Zig.ptrEqAddr i79 i82)
                let _i84 ← Zig.callRC (debug_assert i83)
                let i85 ← Zig.callMC (Zig.ptrProject i32 (·.add 8))
                let _i86 ← Zig.cmpxchgC Zig.AtomicOrder.release Zig.AtomicOrder.relaxed 8 i85 i37 i78
                pure (.ret true))
              else (do
                pure .br68)) : Zig.CM Tgt heap_ArenaAllocator_resizeLocals heap_ArenaAllocator_resizeExit) with
            | .br68 => (do
              match ← ((do
                let i90 ← Zig.callC (heap_ArenaAllocator_Node_loadBuf i32)
                let i91 ← pure i90.len
                let i92 ← pure (Zig.subSat false i91 i37)
                let i94 ← pure (((← get).local5).len)
                let i95 ← Zig.sub false p3 i94
                let i96 ← pure (i92)
                let i97 ← pure (i95)
                let i98 ← pure (Zig.ge false i96 i97)
                if i98 then (do
                  let i101 ← pure (((← get).local5).len)
                  let i102 ← Zig.sub false p3 i101
                  let i103 ← Zig.add false i37 i102
                  let i104 ← Zig.callMC (Zig.ptrProject i34 (·.elem 1 i103))
                  let i106 ← pure (((← get).local5).ptr)
                  let i107 ← Zig.callMC (Zig.ptrProject i106 (·.elem 1 p3))
                  let i108 ← Zig.callMC (Zig.ptrEqAddr i104 i107)
                  let _i109 ← Zig.callRC (debug_assert i108)
                  let i110 ← Zig.callMC (Zig.ptrProject i32 (·.add 8))
                  let i111 ← Zig.cmpxchgC Zig.AtomicOrder.acquire Zig.AtomicOrder.relaxed 8 i110 i37 i103
                  let i112 ← pure ((i111).isNone)
                  pure (.ret i112))
                else (do
                  pure .br89)) : Zig.CM Tgt heap_ArenaAllocator_resizeLocals heap_ArenaAllocator_resizeExit) with
              | .br89 => (do
                pure (.ret false))
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_resizeLocals heap_ArenaAllocator_resizeExit).run' (default : heap_ArenaAllocator_resizeLocals)
  match e with
  | .ret v => pure v
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
  local238 : Zig.Slice
  local321 : Zig.Slice
  local358 : Zig.Ptr
  local359 : Zig.Ptr
  local360 : Zig.Ptr
  local361 : Option (Zig.Ptr)
  best_fit_prev : Option (Zig.Ptr)
  best_fit : Option (Zig.Ptr)
  best_fit_diff : BitVec 64
  it_prev : Option (Zig.Ptr)
  it : Option (Zig.Ptr)
  local406 : Zig.Slice
  local464 : BitVec 64
  local465 : Bool
  local487 : Zig.Slice
  local659 : Zig.Slice
  local820 : Zig.Slice
  local860 : Zig.Slice
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
  | br232
  | br247
  | br220
  | br32
  | br213
  | br269
  | br272 (v : Bool)
  | br296
  | br304
  | br315
  | br330
  | br281
  | br266
  | br351 (v : Zig.Ptr)
  | br350
  | br392
  | br400
  | br416
  | br381
  | br376
  | br374
  | br441
  | br450
  | br362
  | br473
  | br481
  | br499 (v : Bool)
  | br466
  | br527
  | br530
  | br537 (v : Bool)
  | br521 (v : Bool)
  | br550
  | br519
  | br513
  | br571
  | br579
  | br603
  | br612 (v : Option (Zig.Ptr))
  | br622 (v : Option (Zig.Ptr))
  | br638
  | br633
  | br653
  | br664
  | br685 (v : Zig.Ptr)
  | br686
  | br694 (v : BitVec 64)
  | br703
  | br714 (v : BitVec 64)
  | br723
  | br734 (v : BitVec 64)
  | br741
  | br693 (v : heap_ArenaAllocator_Node_Size)
  | br758
  | br761 (v : Option (Zig.Ptr))
  | br754 (v : Zig.Ptr)
  | br772
  | br786
  | br806
  | br814
  | br854
  | br865
  | br843
  | rep375
  | rep31

def heap_ArenaAllocator_alloc.again375 : heap_ArenaAllocator_allocExit → Bool
  | .rep375 => true
  | _ => false

def heap_ArenaAllocator_alloc.again31 : heap_ArenaAllocator_allocExit → Bool
  | .rep31 => true
  | _ => false

mutual

def heap_ArenaAllocator_alloc.loop375 (p1 : BitVec 64) (p2 : mem_Alignment) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit := do
  match ← ((do
    let i377 ← pure ((← get).it)
    let i378 ← pure ((i377).isSome)
    if i378 then (do
      let i380 ← Zig.optPayload i377
      match ← ((do
        let i382 ← pure i380
        let i383 ← pure i382
        let i384 ← Zig.loadBits (Bool) 8 8 0 i383
        let i385 ← pure (!i384)
        let _i386 ← Zig.callRC (debug_assert i385)
        let i387 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe i380)
        let i388 ← pure i387.ptr
        let i389 ← Zig.callMC (Zig.ptrProject i388 (·.elem 1 (24 : BitVec 64)))
        let i390 ← pure i387.len
        let i391 ← pure (Zig.le false (24 : BitVec 64) i390)
        match ← ((do
          if i391 then (do
            pure .br392)
          else (do
            throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
        | .br392 => (do
          let i397 ← Zig.sub false i390 (24 : BitVec 64)
          let i398 ← pure i387.len
          let i399 ← pure (Zig.le false i390 i398)
          match ← ((do
            if i399 then (do
              pure .br400)
            else (do
              throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
          | .br400 => (do
            let i405 ← Zig.callMC (Zig.checkSliceEnd i387.len (24 : BitVec 64) i397 0 >>= fun _ => pure (⟨i389, i397⟩ : Zig.Slice))
            modify (fun s => { s with local406 := i405 })
            let i410 ← pure (((← get).local406).ptr)
            let i411 ← Zig.callMC (heap_ArenaAllocator_alignedIndex i410 (0 : BitVec 64) p2)
            let i412 ← pure (Zig.addSat false i411 p1)
            let i414 ← pure (((← get).local406).len)
            let i415 ← pure (Zig.subSat false i412 i414)
            match ← ((do
              let i417 ← pure ((← get).best_fit_diff)
              let i418 ← pure (i415)
              let i419 ← pure (i417)
              let i420 ← pure (Zig.lt false i418 i419)
              if i420 then (do
                let i422 ← pure ((← get).it_prev)
                modify (fun s => { s with best_fit_prev := i422 })
                let i424 ← pure (i380)
                modify (fun s => { s with best_fit := i424 })
                modify (fun s => { s with best_fit_diff := i415 })
                pure .br416)
              else (do
                pure .br416)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
            | .br416 => (do
              pure .br381)
            | e => pure e)
          | e => pure e)
        | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
      | .br381 => (do
        let i430 ← pure (i380)
        modify (fun s => { s with it_prev := i430 })
        let i432 ← Zig.callMC (Zig.ptrProject i380 (·.add 16))
        let i433 ← Zig.load (Option (Zig.Ptr)) 8 i432
        modify (fun s => { s with it := i433 })
        pure .br376)
      | e => pure e)
    else (do
      pure .br374)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
  | .br376 => (do
    pure .rep375)
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
                      match ← ((do
                        let i221 ← Zig.callMC (Zig.ptrProject v152 (·.add 8))
                        let i222 ← Zig.add false i200 p1
                        let i223 ← Zig.cmpxchgC Zig.AtomicOrder.acquire Zig.AtomicOrder.relaxed 8 i221 i197 i222
                        let i224 ← pure ((i223).isNone)
                        if i224 then (do
                          let i226 ← pure ((← get).local192)
                          let i227 ← pure i226.ptr
                          let i228 ← Zig.callMC (Zig.ptrProject i227 (·.elem 1 i200))
                          let i229 ← Zig.add false i200 p1
                          let i230 ← pure i226.len
                          let i231 ← pure (Zig.le false i229 i230)
                          match ← ((do
                            if i231 then (do
                              pure .br232)
                            else (do
                              throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                          | .br232 => (do
                            let i237 ← Zig.callMC (Zig.checkSliceEnd i226.len i200 p1 0 >>= fun _ => pure (⟨i228, p1⟩ : Zig.Slice))
                            modify (fun s => { s with local238 := i237 })
                            let i242 ← pure (((← get).local238).ptr)
                            let i243 ← pure ((← get).size)
                            let i245 ← pure (((← get).local166).len)
                            let _i246 ← Zig.callC (heap_ArenaAllocator_Node_endResize v152 i243 i245)
                            match ← ((do
                              let i248 ← pure ((← get).cur_new_node)
                              let i249 ← pure ((i248).isSome)
                              if i249 then (do
                                let i251 ← Zig.optPayload i248
                                let i252 ← Zig.callMC (Zig.ptrProject i251 (·.add 16))
                                Zig.store (α := Option (Zig.Ptr)) 8 i252 none
                                let _i254 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i251 i251)
                                pure .br247)
                              else (do
                                pure .br247)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                            | .br247 => (do
                              let i257 ← pure (i242)
                              pure (.ret i257))
                            | e => pure e)
                          | e => pure e)
                        else (do
                          pure .br220)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                      | .br220 => (do
                        let i260 ← pure ((← get).size)
                        let i262 ← pure (((← get).local166).len)
                        let _i263 ← Zig.callC (heap_ArenaAllocator_Node_endResize v152 i260 i262)
                        pure .br32)
                      | e => pure e)
                    else (do
                      pure .br213)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br213 => (do
                    match ← ((do
                      let i267 ← pure i12
                      let i268 ← Zig.load (mem_Allocator) 8 i267
                      match ← ((do
                        pure .br269) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                      | .br269 => (do
                        let i271 ← Zig.callMC Zig.returnAddress
                        match ← ((do
                          let i273 ← pure ((i268).vtable)
                          let i274 ← Zig.callMC (Zig.ptrProject i273 (·.add 8))
                          let i275 ← Zig.load (Zig.Ptr) 8 i274
                          let i276 ← pure ((i268).ptr)
                          let i277 ← (if i275 == (⟨some 4, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_resize i276 v159 mem_Alignment.«8» v201 i271) else if i275 == (⟨some 9, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_resize i276 v159 mem_Alignment.«8» v201 i271) else if i275 == (⟨some 13, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_resize i276 v159 mem_Alignment.«8» v201 i271) else throw .illegal)
                          pure (.br272 i277)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                        | .br272 v272 => (do
                          if v272 then (do
                            modify (fun s => { s with size := v201 })
                            match ← ((do
                              let i282 ← Zig.callMC (Zig.ptrProject v152 (·.add 8))
                              let i283 ← Zig.add false i200 p1
                              let i284 ← Zig.cmpxchgC Zig.AtomicOrder.acquire Zig.AtomicOrder.relaxed 8 i282 i197 i283
                              let i285 ← pure ((i284).isNone)
                              if i285 then (do
                                let i288 ← pure (((← get).local166).ptr)
                                let i289 ← pure i288
                                let i290 ← Zig.sub false v201 (0 : BitVec 64)
                                let i291 ← pure (⟨i289, i290⟩ : Zig.Slice)
                                let i292 ← pure i291.ptr
                                let i293 ← Zig.callMC (Zig.ptrProject i292 (·.elem 1 (24 : BitVec 64)))
                                let i294 ← pure i291.len
                                let i295 ← pure (Zig.le false (24 : BitVec 64) i294)
                                match ← ((do
                                  if i295 then (do
                                    pure .br296)
                                  else (do
                                    throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                | .br296 => (do
                                  let i301 ← Zig.sub false i294 (24 : BitVec 64)
                                  let i302 ← pure i291.len
                                  let i303 ← pure (Zig.le false i294 i302)
                                  match ← ((do
                                    if i303 then (do
                                      pure .br304)
                                    else (do
                                      throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                  | .br304 => (do
                                    let i309 ← Zig.callMC (Zig.checkSliceEnd i291.len (24 : BitVec 64) i301 0 >>= fun _ => pure (⟨i293, i301⟩ : Zig.Slice))
                                    let i310 ← pure i309.ptr
                                    let i311 ← Zig.callMC (Zig.ptrProject i310 (·.elem 1 i200))
                                    let i312 ← Zig.add false i200 p1
                                    let i313 ← pure i309.len
                                    let i314 ← pure (Zig.le false i312 i313)
                                    match ← ((do
                                      if i314 then (do
                                        pure .br315)
                                      else (do
                                        throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                    | .br315 => (do
                                      let i320 ← Zig.callMC (Zig.checkSliceEnd i309.len i200 p1 0 >>= fun _ => pure (⟨i311, p1⟩ : Zig.Slice))
                                      modify (fun s => { s with local321 := i320 })
                                      let i325 ← pure (((← get).local321).ptr)
                                      let i326 ← pure ((← get).size)
                                      let i328 ← pure (((← get).local166).len)
                                      let _i329 ← Zig.callC (heap_ArenaAllocator_Node_endResize v152 i326 i328)
                                      match ← ((do
                                        let i331 ← pure ((← get).cur_new_node)
                                        let i332 ← pure ((i331).isSome)
                                        if i332 then (do
                                          let i334 ← Zig.optPayload i331
                                          let i335 ← Zig.callMC (Zig.ptrProject i334 (·.add 16))
                                          Zig.store (α := Option (Zig.Ptr)) 8 i335 none
                                          let _i337 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i334 i334)
                                          pure .br330)
                                        else (do
                                          pure .br330)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                      | .br330 => (do
                                        let i340 ← pure (i325)
                                        pure (.ret i340))
                                      | e => pure e)
                                    | e => pure e)
                                  | e => pure e)
                                | e => pure e)
                              else (do
                                pure .br281)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                            | .br281 => (do
                              pure .br266)
                            | e => pure e)
                          else (do
                            pure .br266))
                        | e => pure e)
                      | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br266 => (do
                      let i345 ← pure ((← get).size)
                      let i347 ← pure (((← get).local166).len)
                      let _i348 ← Zig.callC (heap_ArenaAllocator_Node_endResize v152 i345 i347)
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
            let i352 ← Zig.callC (heap_ArenaAllocator_stealFreeList i12)
            let i353 ← pure ((i352).isSome)
            if i353 then (do
              let i355 ← Zig.optPayload i352
              pure (.br351 i355))
            else (do
              pure .br350)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
          | .br351 v351 => (do
            match ← ((do
              modify (fun s => { s with best_fit_prev := none })
              modify (fun s => { s with best_fit := none })
              modify (fun s => { s with best_fit_diff := (18446744073709551615 : BitVec 64) })
              modify (fun s => { s with it_prev := none })
              let i372 ← pure (v351)
              modify (fun s => { s with it := i372 })
              match ← ((do
                Zig.loop (heap_ArenaAllocator_alloc.loop375 p1 p2) heap_ArenaAllocator_alloc.again375) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
              | .br374 => (do
                modify (fun s => { s with local358 := v351 })
                let i439 ← pure ((← get).it_prev)
                let i440 ← pure ((i439).isSome)
                match ← ((do
                  if i440 then (do
                    pure .br441)
                  else (do
                    throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br441 => (do
                  let i446 ← Zig.optPayload i439
                  modify (fun s => { s with local359 := i446 })
                  let i448 ← pure ((← get).best_fit)
                  let i449 ← pure ((i448).isSome)
                  match ← ((do
                    if i449 then (do
                      pure .br450)
                    else (do
                      throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br450 => (do
                    let i455 ← Zig.optPayload i448
                    modify (fun s => { s with local360 := i455 })
                    let i457 ← pure ((← get).best_fit_prev)
                    modify (fun s => { s with local361 := i457 })
                    pure .br362)
                  | e => pure e)
                | e => pure e)
              | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
            | .br362 => (do
              match ← ((do
                let i467 ← pure ((← get).local360)
                let i468 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe i467)
                let i469 ← pure i468.ptr
                let i470 ← Zig.callMC (Zig.ptrProject i469 (·.elem 1 (24 : BitVec 64)))
                let i471 ← pure i468.len
                let i472 ← pure (Zig.le false (24 : BitVec 64) i471)
                match ← ((do
                  if i472 then (do
                    pure .br473)
                  else (do
                    throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br473 => (do
                  let i478 ← Zig.sub false i471 (24 : BitVec 64)
                  let i479 ← pure i468.len
                  let i480 ← pure (Zig.le false i471 i479)
                  match ← ((do
                    if i480 then (do
                      pure .br481)
                    else (do
                      throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br481 => (do
                    let i486 ← Zig.callMC (Zig.checkSliceEnd i468.len (24 : BitVec 64) i478 0 >>= fun _ => pure (⟨i470, i478⟩ : Zig.Slice))
                    modify (fun s => { s with local487 := i486 })
                    let i491 ← pure (((← get).local487).ptr)
                    let i492 ← Zig.callMC (heap_ArenaAllocator_alignedIndex i491 (0 : BitVec 64) p2)
                    modify (fun s => { s with local464 := i492 })
                    let i495 ← pure (((← get).local487).len)
                    let i496 ← pure (i492)
                    let i497 ← pure (i495)
                    let i498 ← pure (Zig.gt false i496 i497)
                    match ← ((do
                      if i498 then (do
                        pure (.br499 true))
                      else (do
                        let i503 ← pure (((← get).local487).len)
                        let i504 ← Zig.sub false i503 i492
                        let i505 ← pure (p1)
                        let i506 ← pure (i504)
                        let i507 ← pure (Zig.gt false i505 i506)
                        pure (.br499 i507))) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br499 v499 => (do
                      modify (fun s => { s with local465 := v499 })
                      pure .br466)
                    | e => pure e)
                  | e => pure e)
                | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
              | .br466 => (do
                match ← ((do
                  let i514 ← pure ((← get).local465)
                  if i514 then (do
                    let i516 ← pure ((← get).local464)
                    let i517 ← Zig.add false (24 : BitVec 64) i516
                    let i518 ← Zig.callRC (heap_ArenaAllocator_nodeSizeFor i517 p1)
                    match ← ((do
                      let i520 ← pure ((i518).isSome)
                      match ← ((do
                        if i520 then (do
                          let i523 ← pure i12
                          let i524 ← Zig.load (mem_Allocator) 8 i523
                          let i525 ← pure ((← get).local360)
                          let i526 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe i525)
                          match ← ((do
                            pure .br527) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                          | .br527 => (do
                            let i529 ← pure ((i518).isSome)
                            match ← ((do
                              if i529 then (do
                                pure .br530)
                              else (do
                                throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                            | .br530 => (do
                              let i535 ← Zig.optPayload i518
                              let i536 ← Zig.callMC Zig.returnAddress
                              match ← ((do
                                let i538 ← pure ((i524).vtable)
                                let i539 ← Zig.callMC (Zig.ptrProject i538 (·.add 8))
                                let i540 ← Zig.load (Zig.Ptr) 8 i539
                                let i541 ← pure ((i524).ptr)
                                let i542 ← (if i540 == (⟨some 4, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_resize i541 i526 mem_Alignment.«8» i535 i536) else if i540 == (⟨some 9, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_resize i541 i526 mem_Alignment.«8» i535 i536) else if i540 == (⟨some 13, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_resize i541 i526 mem_Alignment.«8» i535 i536) else throw .illegal)
                                pure (.br537 i542)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                              | .br537 v537 => (do
                                pure (.br521 v537))
                              | e => pure e)
                            | e => pure e)
                          | e => pure e)
                        else (do
                          pure (.br521 false))) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                      | .br521 v521 => (do
                        if v521 then (do
                          let i547 ← pure ((← get).local360)
                          let i548 ← pure i547
                          let i549 ← pure ((i518).isSome)
                          match ← ((do
                            if i549 then (do
                              pure .br550)
                            else (do
                              throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                          | .br550 => (do
                            let i555 ← Zig.optPayload i518
                            let i556 ← Zig.callRC (heap_ArenaAllocator_Node_Size_fromInt i555)
                            Zig.store (α := heap_ArenaAllocator_Node_Size) 8 i548 i556
                            pure .br519)
                          | e => pure e)
                        else (do
                          let i559 ← pure ((← get).local358)
                          let i560 ← pure ((← get).local359)
                          let _i561 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i559 i560)
                          pure .br350))
                      | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br519 => (do
                      pure .br513)
                    | e => pure e)
                  else (do
                    pure .br513)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br513 => (do
                  let i565 ← pure ((← get).local360)
                  let i566 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe i565)
                  let i567 ← pure i566.ptr
                  let i568 ← Zig.callMC (Zig.ptrProject i567 (·.elem 1 (24 : BitVec 64)))
                  let i569 ← pure i566.len
                  let i570 ← pure (Zig.le false (24 : BitVec 64) i569)
                  match ← ((do
                    if i570 then (do
                      pure .br571)
                    else (do
                      throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br571 => (do
                    let i576 ← Zig.sub false i569 (24 : BitVec 64)
                    let i577 ← pure i566.len
                    let i578 ← pure (Zig.le false i569 i577)
                    match ← ((do
                      if i578 then (do
                        pure .br579)
                      else (do
                        throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br579 => (do
                      let i584 ← Zig.callMC (Zig.checkSliceEnd i566.len (24 : BitVec 64) i576 0 >>= fun _ => pure (⟨i568, i576⟩ : Zig.Slice))
                      let i585 ← pure ((← get).local360)
                      let i586 ← Zig.callMC (Zig.ptrProject i585 (·.add 16))
                      let i587 ← Zig.load (Option (Zig.Ptr)) 8 i586
                      let i588 ← pure ((← get).local360)
                      let i589 ← Zig.callMC (Zig.ptrProject i588 (·.add 8))
                      let i590 ← pure ((← get).local464)
                      let i591 ← Zig.add false i590 p1
                      Zig.store (α := BitVec 64) 8 i589 i591
                      let i593 ← pure ((← get).local360)
                      let i594 ← Zig.callMC (Zig.ptrProject i593 (·.add 16))
                      let i595 ← pure ((← get).local33)
                      Zig.store (α := Option (Zig.Ptr)) 8 i594 i595
                      let i597 ← pure ((← get).local360)
                      let i598 ← Zig.callC (heap_ArenaAllocator_tryPushNode i12 i597)
                      let i599 ← pure (heap_ArenaAllocator_PushResult.tag i598)
                      match i599 with
                      | .success => (do
                        match ← ((do
                          let i604 ← pure ((← get).local361)
                          let i605 ← pure ((i604).isSome)
                          if i605 then (do
                            let i607 ← Zig.optPayload i604
                            let i608 ← Zig.callMC (Zig.ptrProject i607 (·.add 16))
                            Zig.store (α := Option (Zig.Ptr)) 8 i608 i587
                            pure .br603)
                          else (do
                            pure .br603)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                        | .br603 => (do
                          match ← ((do
                            let i613 ← pure ((← get).local360)
                            let i614 ← pure ((← get).local358)
                            let i615 ← Zig.callMC (Zig.ptrEqAddr i613 i614)
                            if i615 then (do
                              pure (.br612 i587))
                            else (do
                              let i618 ← pure ((← get).local358)
                              ((do
                                let i620 ← pure (i618)
                                pure (.br612 i620)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit))) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                          | .br612 v612 => (do
                            match ← ((do
                              let i623 ← pure ((← get).local360)
                              let i624 ← pure ((← get).local359)
                              let i625 ← Zig.callMC (Zig.ptrEqAddr i623 i624)
                              if i625 then (do
                                let i627 ← pure ((← get).local361)
                                pure (.br622 i627))
                              else (do
                                let i629 ← pure ((← get).local359)
                                ((do
                                  let i631 ← pure (i629)
                                  pure (.br622 i631)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit))) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                            | .br622 v622 => (do
                              match ← ((do
                                let i634 ← pure ((v612).isSome)
                                if i634 then (do
                                  let i636 ← Zig.optPayload v612
                                  let i637 ← pure ((v622).isSome)
                                  match ← ((do
                                    if i637 then (do
                                      pure .br638)
                                    else (do
                                      throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                  | .br638 => (do
                                    let i643 ← Zig.optPayload v622
                                    let _i644 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i636 i643)
                                    pure .br633)
                                  | e => pure e)
                                else (do
                                  pure .br633)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                              | .br633 => (do
                                let i647 ← pure ((← get).local464)
                                let i648 ← pure i584.ptr
                                let i649 ← Zig.callMC (Zig.ptrProject i648 (·.elem 1 i647))
                                let i650 ← Zig.add false i647 p1
                                let i651 ← pure i584.len
                                let i652 ← pure (Zig.le false i650 i651)
                                match ← ((do
                                  if i652 then (do
                                    pure .br653)
                                  else (do
                                    throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                | .br653 => (do
                                  let i658 ← Zig.callMC (Zig.checkSliceEnd i584.len i647 p1 0 >>= fun _ => pure (⟨i649, p1⟩ : Zig.Slice))
                                  modify (fun s => { s with local659 := i658 })
                                  let i663 ← pure (((← get).local659).ptr)
                                  match ← ((do
                                    let i665 ← pure ((← get).cur_new_node)
                                    let i666 ← pure ((i665).isSome)
                                    if i666 then (do
                                      let i668 ← Zig.optPayload i665
                                      let i669 ← Zig.callMC (Zig.ptrProject i668 (·.add 16))
                                      Zig.store (α := Option (Zig.Ptr)) 8 i669 none
                                      let _i671 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i668 i668)
                                      pure .br664)
                                    else (do
                                      pure .br664)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                                  | .br664 => (do
                                    let i674 ← pure (i663)
                                    pure (.ret i674))
                                  | e => pure e)
                                | e => pure e)
                              | e => pure e)
                            | e => pure e)
                          | e => pure e)
                        | e => pure e)
                      | .failure => (do
                        let i676 ← Zig.callRC (heap_ArenaAllocator_PushResult.get_failure i598)
                        let i677 ← pure ((← get).local360)
                        let i678 ← Zig.callMC (Zig.ptrProject i677 (·.add 16))
                        Zig.store (α := Option (Zig.Ptr)) 8 i678 i587
                        let i680 ← pure ((← get).local358)
                        let i681 ← pure ((← get).local359)
                        let _i682 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i680 i681)
                        modify (fun s => { s with cur_first_node := i676 })
                        pure .br32))
                    | e => pure e)
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
        | .br350 => (do
          match ← ((do
            match ← ((do
              let i687 ← pure ((← get).cur_new_node)
              let i688 ← pure ((i687).isSome)
              if i688 then (do
                let i690 ← Zig.optPayload i687
                pure (.br685 i690))
              else (do
                pure .br686)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
            | .br686 => (do
              match ← ((do
                match ← ((do
                  let i695 ← Zig.callRC (mem_Alignment_toByteUnits p2)
                  let i696 ← Zig.add false (24 : BitVec 64) i695
                  let i697 ← Zig.callRC (math_add__anon_23f0cc3a812c i696 p1)
                  let i698 ← pure (Zig.isNonErr i697)
                  if i698 then (do
                    let i700 ← Zig.callRC (Zig.unwrapPayload i697)
                    pure (.br694 i700))
                  else (do
                    let _i702 ← Zig.callRC (Zig.unwrapErr i697)
                    match ← ((do
                      let i704 ← pure ((← get).cur_new_node)
                      let i705 ← pure ((i704).isSome)
                      if i705 then (do
                        let i707 ← Zig.optPayload i704
                        let i708 ← Zig.callMC (Zig.ptrProject i707 (·.add 16))
                        Zig.store (α := Option (Zig.Ptr)) 8 i708 none
                        let _i710 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i707 i707)
                        pure .br703)
                      else (do
                        pure .br703)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br703 => (do
                      pure (.ret none))
                    | e => pure e)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br694 v694 => (do
                  match ← ((do
                    let i715 ← pure ((← get).local34)
                    let i716 ← Zig.add false i715 (16 : BitVec 64)
                    let i717 ← Zig.callRC (math_add__anon_23f0cc3a812c i716 v694)
                    let i718 ← pure (Zig.isNonErr i717)
                    if i718 then (do
                      let i720 ← Zig.callRC (Zig.unwrapPayload i717)
                      pure (.br714 i720))
                    else (do
                      let _i722 ← Zig.callRC (Zig.unwrapErr i717)
                      match ← ((do
                        let i724 ← pure ((← get).cur_new_node)
                        let i725 ← pure ((i724).isSome)
                        if i725 then (do
                          let i727 ← Zig.optPayload i724
                          let i728 ← Zig.callMC (Zig.ptrProject i727 (·.add 16))
                          Zig.store (α := Option (Zig.Ptr)) 8 i728 none
                          let _i730 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i727 i727)
                          pure .br723)
                        else (do
                          pure .br723)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                      | .br723 => (do
                        pure (.ret none))
                      | e => pure e)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br714 v714 => (do
                    match ← ((do
                      let i735 ← Zig.divTrunc false v714 (2 : BitVec 64)
                      let i736 ← Zig.callRC (heap_ArenaAllocator_nodeSizeFor v714 i735)
                      let i737 ← pure ((i736).isSome)
                      if i737 then (do
                        let i739 ← Zig.optPayload i736
                        pure (.br734 i739))
                      else (do
                        match ← ((do
                          let i742 ← pure ((← get).cur_new_node)
                          let i743 ← pure ((i742).isSome)
                          if i743 then (do
                            let i745 ← Zig.optPayload i742
                            let i746 ← Zig.callMC (Zig.ptrProject i745 (·.add 16))
                            Zig.store (α := Option (Zig.Ptr)) 8 i746 none
                            let _i748 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i745 i745)
                            pure .br741)
                          else (do
                            pure .br741)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                        | .br741 => (do
                          pure (.ret none))
                        | e => pure e)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br734 v734 => (do
                      let i752 ← Zig.callRC (heap_ArenaAllocator_Node_Size_fromInt v734)
                      pure (.br693 i752))
                    | e => pure e)
                  | e => pure e)
                | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
              | .br693 v693 => (do
                match ← ((do
                  let i755 ← pure i12
                  let i756 ← Zig.load (mem_Allocator) 8 i755
                  let i757 ← Zig.callRC (heap_ArenaAllocator_Node_Size_toInt v693)
                  match ← ((do
                    pure .br758) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br758 => (do
                    let i760 ← Zig.callMC Zig.returnAddress
                    match ← ((do
                      let i762 ← pure ((i756).vtable)
                      let i763 ← pure i762
                      let i764 ← Zig.load (Zig.Ptr) 8 i763
                      let i765 ← pure ((i756).ptr)
                      let i766 ← (if i764 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callC (heap_PageAllocator_alloc i765 i757 mem_Alignment.«8» i760) else if i764 == (⟨some 8, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_alloc i765 i757 mem_Alignment.«8» i760) else if i764 == (⟨some 12, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_alloc i765 i757 mem_Alignment.«8» i760) else throw .illegal)
                      pure (.br761 i766)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br761 v761 => (do
                      let i768 ← pure ((v761).isSome)
                      if i768 then (do
                        let i770 ← Zig.optPayload v761
                        pure (.br754 i770))
                      else (do
                        match ← ((do
                          let i773 ← pure ((← get).cur_new_node)
                          let i774 ← pure ((i773).isSome)
                          if i774 then (do
                            let i776 ← Zig.optPayload i773
                            let i777 ← Zig.callMC (Zig.ptrProject i776 (·.add 16))
                            Zig.store (α := Option (Zig.Ptr)) 8 i777 none
                            let _i779 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i776 i776)
                            pure .br772)
                          else (do
                            pure .br772)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                        | .br772 => (do
                          pure (.ret none))
                        | e => pure e))
                    | e => pure e)
                  | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br754 v754 => (do
                  let i783 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr v754)))
                  let i784 ← pure (i783 &&& (7 : BitVec 64))
                  let i785 ← pure (i784 == (0 : BitVec 64))
                  match ← ((do
                    if i785 then (do
                      pure .br786)
                    else (do
                      throw .panic)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                  | .br786 => (do
                    let i791 ← Zig.callMC (Zig.checkAlign 8 v754 >>= fun _ => pure v754)
                    let i792 ← pure i791
                    Zig.store (α := heap_ArenaAllocator_Node_Size) 8 i792 v693
                    let i794 ← Zig.callMC (Zig.ptrProject i791 (·.add 8))
                    Zig.storeUndef (BitVec 64) 8 i794
                    let i796 ← Zig.callMC (Zig.ptrProject i791 (·.add 16))
                    Zig.storeUndef (Option (Zig.Ptr)) 8 i796
                    let i798 ← pure (i791)
                    modify (fun s => { s with cur_new_node := i798 })
                    pure (.br685 i791))
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
          | .br685 v685 => (do
            let i801 ← Zig.callMC (heap_ArenaAllocator_Node_allocatedSliceUnsafe v685)
            let i802 ← pure i801.ptr
            let i803 ← Zig.callMC (Zig.ptrProject i802 (·.elem 1 (24 : BitVec 64)))
            let i804 ← pure i801.len
            let i805 ← pure (Zig.le false (24 : BitVec 64) i804)
            match ← ((do
              if i805 then (do
                pure .br806)
              else (do
                throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
            | .br806 => (do
              let i811 ← Zig.sub false i804 (24 : BitVec 64)
              let i812 ← pure i801.len
              let i813 ← pure (Zig.le false i804 i812)
              match ← ((do
                if i813 then (do
                  pure .br814)
                else (do
                  throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
              | .br814 => (do
                let i819 ← Zig.callMC (Zig.checkSliceEnd i801.len (24 : BitVec 64) i811 0 >>= fun _ => pure (⟨i803, i811⟩ : Zig.Slice))
                modify (fun s => { s with local820 := i819 })
                let i824 ← pure (((← get).local820).ptr)
                let i825 ← Zig.callMC (heap_ArenaAllocator_alignedIndex i824 (0 : BitVec 64) p2)
                let i826 ← pure v685
                let i827 ← Zig.load (heap_ArenaAllocator_Node_Size) 8 i826
                let i828 ← Zig.callRC (heap_ArenaAllocator_Node_Size_toInt i827)
                let i829 ← Zig.add false (24 : BitVec 64) i825
                let i830 ← Zig.add false i829 p1
                let i831 ← pure (i828)
                let i832 ← pure (i830)
                let i833 ← pure (Zig.ge false i831 i832)
                let _i834 ← Zig.callRC (debug_assert i833)
                let i835 ← Zig.callMC (Zig.ptrProject v685 (·.add 8))
                let i836 ← Zig.add false i825 p1
                Zig.store (α := BitVec 64) 8 i835 i836
                let i838 ← Zig.callMC (Zig.ptrProject v685 (·.add 16))
                let i839 ← pure ((← get).local33)
                Zig.store (α := Option (Zig.Ptr)) 8 i838 i839
                let i841 ← Zig.callC (heap_ArenaAllocator_tryPushNode i12 v685)
                let i842 ← pure (heap_ArenaAllocator_PushResult.tag i841)
                match ← ((do
                  match i842 with
                  | .success => (do
                    modify (fun s => { s with cur_new_node := none })
                    let i848 ← pure ((← get).local820)
                    let i849 ← pure i848.ptr
                    let i850 ← Zig.callMC (Zig.ptrProject i849 (·.elem 1 i825))
                    let i851 ← Zig.add false i825 p1
                    let i852 ← pure i848.len
                    let i853 ← pure (Zig.le false i851 i852)
                    match ← ((do
                      if i853 then (do
                        pure .br854)
                      else (do
                        throw .outOfBounds)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                    | .br854 => (do
                      let i859 ← Zig.callMC (Zig.checkSliceEnd i848.len i825 p1 0 >>= fun _ => pure (⟨i850, p1⟩ : Zig.Slice))
                      modify (fun s => { s with local860 := i859 })
                      let i864 ← pure (((← get).local860).ptr)
                      match ← ((do
                        let i866 ← pure ((← get).cur_new_node)
                        let i867 ← pure ((i866).isSome)
                        if i867 then (do
                          let i869 ← Zig.optPayload i866
                          let i870 ← Zig.callMC (Zig.ptrProject i869 (·.add 16))
                          Zig.store (α := Option (Zig.Ptr)) 8 i870 none
                          let _i872 ← Zig.callC (heap_ArenaAllocator_pushFreeList i12 i869 i869)
                          pure .br865)
                        else (do
                          pure .br865)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                      | .br865 => (do
                        let i875 ← pure (i864)
                        pure (.ret i875))
                      | e => pure e)
                    | e => pure e)
                  | .failure => (do
                    let i877 ← Zig.callRC (heap_ArenaAllocator_PushResult.get_failure i841)
                    modify (fun s => { s with cur_first_node := i877 })
                    pure .br843)) : Zig.CM Tgt heap_ArenaAllocator_allocLocals heap_ArenaAllocator_allocExit) with
                | .br843 => (do
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
          let i15 ← (if i13 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callC (heap_PageAllocator_alloc i14 p1 mem_Alignment.«8» p2) else if i13 == (⟨some 8, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_alloc i14 p1 mem_Alignment.«8» p2) else if i13 == (⟨some 12, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_alloc i14 p1 mem_Alignment.«8» p2) else throw .illegal)
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

structure mem_Allocator_allocWithSizeAndAlignment__anon_2d3c33bb31beLocals where
  deriving Inhabited

inductive mem_Allocator_allocWithSizeAndAlignment__anon_2d3c33bb31beExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3 (v : BitVec 64)

def mem_Allocator_allocWithSizeAndAlignment__anon_2d3c33bb31be (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.callRC (math_mul__anon_44faaf286c79 (1 : BitVec 64) p1)
      let i5 ← pure (Zig.isNonErr i4)
      if i5 then (do
        let i7 ← Zig.callRC (Zig.unwrapPayload i4)
        pure (.br3 i7))
      else (do
        let _i9 ← Zig.callRC (Zig.unwrapErr i4)
        pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr))))) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_2d3c33bb31beLocals mem_Allocator_allocWithSizeAndAlignment__anon_2d3c33bb31beExit) with
    | .br3 v3 => (do
      let i11 ← Zig.callC (mem_Allocator_allocBytesWithAlignment__anon_f686c272daf7 p0 v3 p2)
      pure (.ret i11))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_2d3c33bb31beLocals mem_Allocator_allocWithSizeAndAlignment__anon_2d3c33bb31beExit).run' (default : mem_Allocator_allocWithSizeAndAlignment__anon_2d3c33bb31beLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_alignedAlloc__anon_004dab4d837dLocals where
  deriving Inhabited

inductive mem_Allocator_alignedAlloc__anon_004dab4d837dExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br3 (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_alignedAlloc__anon_004dab4d837d (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.callMC Zig.returnAddress
    match ← ((do
      let i4 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_2d3c33bb31be p0 p1 i2)
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
        pure (.br3 i12))) : Zig.CM Tgt mem_Allocator_alignedAlloc__anon_004dab4d837dLocals mem_Allocator_alignedAlloc__anon_004dab4d837dExit) with
    | .br3 v3 => (do
      pure (.ret v3))
    | e => pure e) : Zig.CM Tgt mem_Allocator_alignedAlloc__anon_004dab4d837dLocals mem_Allocator_alignedAlloc__anon_004dab4d837dExit).run' (default : mem_Allocator_alignedAlloc__anon_004dab4d837dLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_absorbSentinel__anon_7169d0388e16Locals where
  deriving Inhabited

inductive mem_absorbSentinel__anon_7169d0388e16Exit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_7169d0388e16 (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret p0)) : Zig.MM mem_absorbSentinel__anon_7169d0388e16Locals mem_absorbSentinel__anon_7169d0388e16Exit).run' (default : mem_absorbSentinel__anon_7169d0388e16Locals)
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

structure heap_ArenaAllocator_freeLocals where
  local4 : Zig.Slice
  deriving Inhabited

inductive heap_ArenaAllocator_freeExit where
  | ret
  | br10
  | br23
  | br34
  | br43

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
          let i35 ← Zig.callC (heap_ArenaAllocator_Node_loadBuf i28)
          let i36 ← pure i35.len
          let i37 ← pure (i33)
          let i38 ← pure (i36)
          let i39 ← pure (Zig.gt false i37 i38)
          if i39 then (do
            pure .ret)
          else (do
            pure .br34)) : Zig.CM Tgt heap_ArenaAllocator_freeLocals heap_ArenaAllocator_freeExit) with
        | .br34 => (do
          match ← ((do
            let i44 ← Zig.callMC (Zig.ptrProject i30 (·.elem 1 i33))
            let i46 ← pure (((← get).local4).ptr)
            let i48 ← pure (((← get).local4).len)
            let i49 ← Zig.callMC (Zig.ptrProject i46 (·.elem 1 i48))
            let i50 ← Zig.callMC (do pure (!(← Zig.ptrEqAddr i44 i49)))
            if i50 then (do
              pure .ret)
            else (do
              pure .br43)) : Zig.CM Tgt heap_ArenaAllocator_freeLocals heap_ArenaAllocator_freeExit) with
          | .br43 => (do
            let i55 ← pure (((← get).local4).len)
            let i56 ← Zig.sub false i33 i55
            let i57 ← Zig.callMC (Zig.ptrProject i30 (·.elem 1 i56))
            let i59 ← pure (((← get).local4).ptr)
            let i60 ← Zig.callMC (Zig.ptrEqAddr i57 i59)
            let _i61 ← Zig.callRC (debug_assert i60)
            let i62 ← Zig.callMC (Zig.ptrProject i28 (·.add 8))
            let _i63 ← Zig.cmpxchgC Zig.AtomicOrder.release Zig.AtomicOrder.relaxed 8 i62 i33 i56
            pure .ret)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt heap_ArenaAllocator_freeLocals heap_ArenaAllocator_freeExit).run' (default : heap_ArenaAllocator_freeLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

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

structure mem_Allocator_free__anon_809fd7dfd3c9Locals where
  deriving Inhabited

inductive mem_Allocator_free__anon_809fd7dfd3c9Exit where
  | ret
  | br4
  | br15

def mem_Allocator_free__anon_809fd7dfd3c9 (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← Zig.callMC (mem_absorbSentinel__anon_7169d0388e16 p1)
    let i3 ← pure (i2)
    match ← ((do
      let i5 ← pure i3.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        pure .ret)
      else (do
        pure .br4)) : Zig.CM Tgt mem_Allocator_free__anon_809fd7dfd3c9Locals mem_Allocator_free__anon_809fd7dfd3c9Exit) with
    | .br4 => (do
      let _i11 ← pure i3.len
      Zig.callMC (Zig.memset (α := BitVec 8) 1 i3.ptr i3.len none)
      let i13 ← Zig.callRC (mem_Alignment_fromByteUnits (8 : BitVec 64))
      let i14 ← Zig.callMC Zig.returnAddress
      match ← ((do
        let i16 ← pure ((p0).vtable)
        let i17 ← Zig.callMC (Zig.ptrProject i16 (·.add 24))
        let i18 ← Zig.load (Zig.Ptr) 8 i17
        let i19 ← pure ((p0).ptr)
        let _i20 ← (if i18 == (⟨some 6, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_free i19 i3 i13 i14) else if i18 == (⟨some 11, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_free i19 i3 i13 i14) else if i18 == (⟨some 15, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_free i19 i3 i13 i14) else throw .illegal)
        pure .br15) : Zig.CM Tgt mem_Allocator_free__anon_809fd7dfd3c9Locals mem_Allocator_free__anon_809fd7dfd3c9Exit) with
      | .br15 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_free__anon_809fd7dfd3c9Locals mem_Allocator_free__anon_809fd7dfd3c9Exit).run' (default : mem_Allocator_free__anon_809fd7dfd3c9Locals)
  match e with
  | .ret => pure ()
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

structure arena_fitLocals where
  fba : Zig.Ptr
  arena : Zig.Ptr
  deriving Inhabited

inductive arena_fitExit where
  | ret (v : BitVec 64)
  | br9 (v : Zig.Slice)
  | br18 (v : Zig.Slice)

def arena_fit (p0 : BitVec 64) : Zig.ConcM Tgt (BitVec 64) := do
  let s1 ← Zig.allocStack 24 8
  let s4 ← Zig.allocStack 32 8
  let e ← ((do
    let i1 ← pure (← get).fba
    let i2 ← Zig.callMC (heap_FixedBufferAllocator_init (⟨(⟨some 0, 0⟩ : Zig.Ptr), (256 : BitVec 64)⟩ : Zig.Slice))
    Zig.store (α := heap_FixedBufferAllocator) 8 i1 i2
    let i4 ← pure (← get).arena
    let i5 ← Zig.callMC (heap_FixedBufferAllocator_allocator i1)
    let i6 ← Zig.callMC (heap_ArenaAllocator_init i5)
    Zig.store (α := heap_ArenaAllocator) 8 i4 i6
    let i8 ← Zig.callMC (heap_ArenaAllocator_allocator i4)
    match ← ((do
      let i10 ← Zig.callC (mem_Allocator_alignedAlloc__anon_004dab4d837d i8 (8 : BitVec 64))
      let i11 ← pure (Zig.isNonErr i10)
      if i11 then (do
        let i13 ← Zig.callRC (Zig.unwrapPayload i10)
        pure (.br9 i13))
      else (do
        let _i15 ← Zig.callRC (Zig.unwrapErr i10)
        pure (.ret (0 : BitVec 64)))) : Zig.CM Tgt arena_fitLocals arena_fitExit) with
    | .br9 v9 => (do
      let _i17 ← Zig.callC (mem_Allocator_free__anon_809fd7dfd3c9 i8 v9)
      match ← ((do
        let i19 ← Zig.callC (mem_Allocator_alignedAlloc__anon_004dab4d837d i8 p0)
        let i20 ← pure (Zig.isNonErr i19)
        if i20 then (do
          let i22 ← Zig.callRC (Zig.unwrapPayload i19)
          pure (.br18 i22))
        else (do
          let _i24 ← Zig.callRC (Zig.unwrapErr i19)
          pure (.ret (1 : BitVec 64)))) : Zig.CM Tgt arena_fitLocals arena_fitExit) with
      | .br18 v18 => (do
        let i26 ← pure v18.len
        let i27 ← Zig.load (heap_ArenaAllocator) 8 i4
        let i28 ← Zig.callMC (heap_ArenaAllocator_queryCapacity i27)
        let i29 ← Zig.mul false (1000 : BitVec 64) i28
        let i30 ← Zig.add false i26 i29
        pure (.ret i30))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt arena_fitLocals arena_fitExit).run' { (default : arena_fitLocals) with fba := s1, arena := s4 }
  Zig.free s1
  Zig.free s4
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_absorbSentinel__anon_7342b53a30edLocals where
  deriving Inhabited

inductive mem_absorbSentinel__anon_7342b53a30edExit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_7342b53a30ed (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret p0)) : Zig.MM mem_absorbSentinel__anon_7342b53a30edLocals mem_absorbSentinel__anon_7342b53a30edExit).run' (default : mem_absorbSentinel__anon_7342b53a30edLocals)
  match e with
  | .ret v => pure v

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
        let _i20 ← (if i18 == (⟨some 6, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_free i19 i3 i13 i14) else if i18 == (⟨some 11, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_free i19 i3 i13 i14) else if i18 == (⟨some 15, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_free i19 i3 i13 i14) else throw .illegal)
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
    let i1 ← Zig.callMC (heap_ArenaAllocator_init ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator))
    Zig.store (α := heap_ArenaAllocator) 8 i0 i1
    let i3 ← Zig.callMC (heap_ArenaAllocator_allocator i0)
    let _i4 ← Zig.callC (mem_Allocator_free__anon_1e60e7ef40f5 i3 (⟨(⟨some 2, 0⟩ : Zig.Ptr), (8 : BitVec 64)⟩ : Zig.Slice))
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
    let i1 ← Zig.callMC (heap_ArenaAllocator_init ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator))
    Zig.store (α := heap_ArenaAllocator) 8 i0 i1
    Zig.store (α := heap_ArenaAllocator_Node_Size) 8 (⟨some 7, 0⟩ : Zig.Ptr) (Zig.Packed.ofBits (64 : BitVec 64) : heap_ArenaAllocator_Node_Size)
    Zig.store (α := BitVec 64) 8 (⟨some 7, 8⟩ : Zig.Ptr) (1000 : BitVec 64)
    Zig.store (α := Option (Zig.Ptr)) 8 (⟨some 7, 16⟩ : Zig.Ptr) none
    let i6 ← Zig.callMC (Zig.ptrProject i0 (·.add 16))
    let i7 ← pure i6
    Zig.store (α := Option (Zig.Ptr)) 8 i7 (some (⟨some 7, 0⟩ : Zig.Ptr))
    let i9 ← Zig.callMC (heap_ArenaAllocator_allocator i0)
    let _i10 ← Zig.callC (mem_Allocator_free__anon_1e60e7ef40f5 i9 (⟨(⟨some 2, 0⟩ : Zig.Ptr), (8 : BitVec 64)⟩ : Zig.Slice))
    pure .ret) : Zig.CM Tgt arena_oob_freeLocals arena_oob_freeExit).run' { (default : arena_oob_freeLocals) with arena := s0 }
  Zig.free s0
  match e with
  | .ret => pure ()

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
          let i15 ← (if i13 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callC (heap_PageAllocator_alloc i14 p1 mem_Alignment.«1» p2) else if i13 == (⟨some 8, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_alloc i14 p1 mem_Alignment.«1» p2) else if i13 == (⟨some 12, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_alloc i14 p1 mem_Alignment.«1» p2) else throw .illegal)
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
    let i2 ← Zig.callMC (heap_FixedBufferAllocator_init (⟨(⟨some 0, 0⟩ : Zig.Ptr), (256 : BitVec 64)⟩ : Zig.Slice))
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
          let _i38 ← (if i36 == (⟨some 6, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_free i37 i29 mem_Alignment.«8» i32) else if i36 == (⟨some 11, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_free i37 i29 mem_Alignment.«8» i32) else if i36 == (⟨some 15, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_free i37 i29 mem_Alignment.«8» i32) else throw .illegal)
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
    let i2 ← Zig.callMC (heap_ArenaAllocator_init ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator))
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
            let _i104 ← (if i102 == (⟨some 6, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_free i103 i95 mem_Alignment.«8» i98) else if i102 == (⟨some 11, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_free i103 i95 mem_Alignment.«8» i98) else if i102 == (⟨some 15, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_free i103 i95 mem_Alignment.«8» i98) else throw .illegal)
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
                let _i126 ← (if i124 == (⟨some 6, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_free i125 i109 mem_Alignment.«8» i120) else if i124 == (⟨some 11, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_free i125 i109 mem_Alignment.«8» i120) else if i124 == (⟨some 15, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_free i125 i109 mem_Alignment.«8» i120) else throw .illegal)
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
                  let i154 ← (if i152 == (⟨some 4, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_resize i153 i109 mem_Alignment.«8» i111 i148) else if i152 == (⟨some 9, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_resize i153 i109 mem_Alignment.«8» i111 i148) else if i152 == (⟨some 13, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_resize i153 i109 mem_Alignment.«8» i111 i148) else throw .illegal)
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
                          let i172 ← (if i170 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callC (heap_PageAllocator_alloc i171 i111 mem_Alignment.«8» i166) else if i170 == (⟨some 8, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_alloc i171 i111 mem_Alignment.«8» i166) else if i170 == (⟨some 12, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_alloc i171 i111 mem_Alignment.«8» i166) else throw .illegal)
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
                          let _i190 ← (if i188 == (⟨some 6, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_free i189 i109 mem_Alignment.«8» i184) else if i188 == (⟨some 11, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_free i189 i109 mem_Alignment.«8» i184) else if i188 == (⟨some 15, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_free i189 i109 mem_Alignment.«8» i184) else throw .illegal)
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
    let i3 ← Zig.callMC (heap_FixedBufferAllocator_init (⟨(⟨some 2, 0⟩ : Zig.Ptr), (4096 : BitVec 64)⟩ : Zig.Slice))
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
            let i34 ← (if i32 == (⟨some 4, 0⟩ : Zig.Ptr) then Zig.callMC (heap_PageAllocator_resize i33 i18 i27 v19 i28) else if i32 == (⟨some 9, 0⟩ : Zig.Ptr) then Zig.callC (heap_ArenaAllocator_resize i33 i18 i27 v19 i28) else if i32 == (⟨some 13, 0⟩ : Zig.Ptr) then Zig.callMC (heap_FixedBufferAllocator_resize i33 i18 i27 v19 i28) else throw .illegal)
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
    let i3 ← Zig.callMC (heap_FixedBufferAllocator_init (⟨(⟨some 2, 0⟩ : Zig.Ptr), (4096 : BitVec 64)⟩ : Zig.Slice))
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
    let i2 ← Zig.callMC (heap_FixedBufferAllocator_init (⟨(⟨some 2, 0⟩ : Zig.Ptr), (4096 : BitVec 64)⟩ : Zig.Slice))
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
    let i2 ← Zig.callMC (heap_FixedBufferAllocator_init (⟨(⟨some 2, 0⟩ : Zig.Ptr), (4096 : BitVec 64)⟩ : Zig.Slice))
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