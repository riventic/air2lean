import ZigLean


namespace Threadsync

structure os_linux_timespec__struct_1 where
  sec : BitVec 64
  nsec : BitVec 64
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc os_linux_timespec__struct_1 where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.sec), (8, Zig.Enc.encode v.nsec)]
  decode bs := do pure { sec := ← Zig.Enc.decodeAt bs 0, nsec := ← Zig.Enc.decodeAt bs 8 }

structure time_Instant where
  timestamp : os_linux_timespec__struct_1
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc time_Instant where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.timestamp)]
  decode bs := do pure { timestamp := ← Zig.Enc.decodeAt bs 0 }

structure time_Timer where
  started : time_Instant
  previous : time_Instant
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc time_Timer where
  size := 32
  align := 8
  encode v := Zig.Enc.fields 32 [(0, Zig.Enc.encode v.started), (16, Zig.Enc.encode v.previous)]
  decode bs := do pure { started := ← Zig.Enc.decodeAt bs 0, previous := ← Zig.Enc.decodeAt bs 16 }

structure atomic_Value_usize where
  raw : BitVec 64
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc atomic_Value_usize where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.raw)]
  decode bs := do pure { raw := ← Zig.Enc.decodeAt bs 0 }

structure atomic_Value_u32 where
  raw : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc atomic_Value_u32 where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.raw)]
  decode bs := do pure { raw := ← Zig.Enc.decodeAt bs 0 }

structure Thread_ResetEvent_FutexImpl where
  state : atomic_Value_u32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Thread_ResetEvent_FutexImpl where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.state)]
  decode bs := do pure { state := ← Zig.Enc.decodeAt bs 0 }

structure Thread_ResetEvent where
  impl : Thread_ResetEvent_FutexImpl
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Thread_ResetEvent where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.impl)]
  decode bs := do pure { impl := ← Zig.Enc.decodeAt bs 0 }

structure Thread_WaitGroup where
  state : atomic_Value_usize
  event : Thread_ResetEvent
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Thread_WaitGroup where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.state), (8, Zig.Enc.encode v.event)]
  decode bs := do pure { state := ← Zig.Enc.decodeAt bs 0, event := ← Zig.Enc.decodeAt bs 8 }

structure Thread_Mutex_FutexImpl where
  state : atomic_Value_u32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Thread_Mutex_FutexImpl where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.state)]
  decode bs := do pure { state := ← Zig.Enc.decodeAt bs 0 }

structure Thread_Mutex where
  impl : Thread_Mutex_FutexImpl
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Thread_Mutex where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.impl)]
  decode bs := do pure { impl := ← Zig.Enc.decodeAt bs 0 }

structure Tally where
  wg : Thread_WaitGroup
  m : Thread_Mutex
  n : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Tally where
  size := 24
  align := 8
  encode v := Zig.Enc.fields 24 [(0, Zig.Enc.encode v.wg), (16, Zig.Enc.encode v.m), (20, Zig.Enc.encode v.n)]
  decode bs := do pure { wg := ← Zig.Enc.decodeAt bs 0, m := ← Zig.Enc.decodeAt bs 16, n := ← Zig.Enc.decodeAt bs 20 }

structure Counter where
  m : Thread_Mutex
  n : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Counter where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.m), (4, Zig.Enc.encode v.n)]
  decode bs := do pure { m := ← Zig.Enc.decodeAt bs 0, n := ← Zig.Enc.decodeAt bs 4 }

structure Thread_Condition_FutexImpl where
  state : atomic_Value_u32
  epoch : atomic_Value_u32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Thread_Condition_FutexImpl where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.state), (4, Zig.Enc.encode v.epoch)]
  decode bs := do pure { state := ← Zig.Enc.decodeAt bs 0, epoch := ← Zig.Enc.decodeAt bs 4 }

structure Thread_Condition where
  impl : Thread_Condition_FutexImpl
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Thread_Condition where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.impl)]
  decode bs := do pure { impl := ← Zig.Enc.decodeAt bs 0 }

structure Box where
  m : Thread_Mutex
  c : Thread_Condition
  ready : Bool
  done : Thread_ResetEvent
  v : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Box where
  size := 24
  align := 4
  encode v := Zig.Enc.fields 24 [(0, Zig.Enc.encode v.m), (4, Zig.Enc.encode v.c), (20, Zig.Enc.encode v.ready), (12, Zig.Enc.encode v.done), (16, Zig.Enc.encode v.v)]
  decode bs := do pure { m := ← Zig.Enc.decodeAt bs 0, c := ← Zig.Enc.decodeAt bs 4, ready := ← Zig.Enc.decodeAt bs 20, done := ← Zig.Enc.decodeAt bs 12, v := ← Zig.Enc.decodeAt bs 16 }

structure os_linux_clockid_t where
  bits : BitVec 32
  deriving Repr, Inhabited, DecidableEq

def os_linux_clockid_t.REALTIME : os_linux_clockid_t := ⟨(0 : BitVec 32)⟩
def os_linux_clockid_t.MONOTONIC : os_linux_clockid_t := ⟨(1 : BitVec 32)⟩
def os_linux_clockid_t.PROCESS_CPUTIME_ID : os_linux_clockid_t := ⟨(2 : BitVec 32)⟩
def os_linux_clockid_t.THREAD_CPUTIME_ID : os_linux_clockid_t := ⟨(3 : BitVec 32)⟩
def os_linux_clockid_t.MONOTONIC_RAW : os_linux_clockid_t := ⟨(4 : BitVec 32)⟩
def os_linux_clockid_t.REALTIME_COARSE : os_linux_clockid_t := ⟨(5 : BitVec 32)⟩
def os_linux_clockid_t.MONOTONIC_COARSE : os_linux_clockid_t := ⟨(6 : BitVec 32)⟩
def os_linux_clockid_t.BOOTTIME : os_linux_clockid_t := ⟨(7 : BitVec 32)⟩
def os_linux_clockid_t.REALTIME_ALARM : os_linux_clockid_t := ⟨(8 : BitVec 32)⟩
def os_linux_clockid_t.BOOTTIME_ALARM : os_linux_clockid_t := ⟨(9 : BitVec 32)⟩

def os_linux_clockid_t.toBits (e : os_linux_clockid_t) : BitVec 32 := e.bits

def os_linux_clockid_t.ofInt? (v : Int) : Option os_linux_clockid_t :=
  if 0 ≤ v ∧ v ≤ 4294967295 then Option.some ⟨BitVec.ofInt 32 v⟩ else Option.none

def os_linux_clockid_t.isNamed (e : os_linux_clockid_t) : Bool := e.bits == (0 : BitVec 32) || e.bits == (1 : BitVec 32) || e.bits == (2 : BitVec 32) || e.bits == (3 : BitVec 32) || e.bits == (4 : BitVec 32) || e.bits == (5 : BitVec 32) || e.bits == (6 : BitVec 32) || e.bits == (7 : BitVec 32) || e.bits == (8 : BitVec 32) || e.bits == (9 : BitVec 32)

instance : Zig.Packed os_linux_clockid_t 32 where
  toBits := os_linux_clockid_t.toBits
  ofBits b := ⟨b⟩

inductive os_linux_FUTEX_COMMAND where
  | WAIT
  | WAKE
  | FD
  | REQUEUE
  | CMP_REQUEUE
  | WAKE_OP
  | LOCK_PI
  | UNLOCK_PI
  | TRYLOCK_PI
  | WAIT_BITSET
  | WAKE_BITSET
  | WAIT_REQUEUE_PI
  | CMP_REQUEUE_PI
  deriving Repr, Inhabited, DecidableEq

def os_linux_FUTEX_COMMAND.toBits : os_linux_FUTEX_COMMAND → BitVec 7
  | .WAIT => (0 : BitVec 7)
  | .WAKE => (1 : BitVec 7)
  | .FD => (2 : BitVec 7)
  | .REQUEUE => (3 : BitVec 7)
  | .CMP_REQUEUE => (4 : BitVec 7)
  | .WAKE_OP => (5 : BitVec 7)
  | .LOCK_PI => (6 : BitVec 7)
  | .UNLOCK_PI => (7 : BitVec 7)
  | .TRYLOCK_PI => (8 : BitVec 7)
  | .WAIT_BITSET => (9 : BitVec 7)
  | .WAKE_BITSET => (10 : BitVec 7)
  | .WAIT_REQUEUE_PI => (11 : BitVec 7)
  | .CMP_REQUEUE_PI => (12 : BitVec 7)

def os_linux_FUTEX_COMMAND.ofInt? (v : Int) : Option os_linux_FUTEX_COMMAND :=
  if v = 0 then Option.some .WAIT else if v = 1 then Option.some .WAKE else if v = 2 then Option.some .FD else if v = 3 then Option.some .REQUEUE else if v = 4 then Option.some .CMP_REQUEUE else if v = 5 then Option.some .WAKE_OP else if v = 6 then Option.some .LOCK_PI else if v = 7 then Option.some .UNLOCK_PI else if v = 8 then Option.some .TRYLOCK_PI else if v = 9 then Option.some .WAIT_BITSET else if v = 10 then Option.some .WAKE_BITSET else if v = 11 then Option.some .WAIT_REQUEUE_PI else if v = 12 then Option.some .CMP_REQUEUE_PI else Option.none

def os_linux_FUTEX_COMMAND.isNamed (_ : os_linux_FUTEX_COMMAND) : Bool := true

instance : Zig.Packed os_linux_FUTEX_COMMAND 7 where
  toBits := os_linux_FUTEX_COMMAND.toBits
  ofBits b := (os_linux_FUTEX_COMMAND.ofInt? (Zig.val false b)).getD default
  valid b := (os_linux_FUTEX_COMMAND.ofInt? (Zig.val false b)).isSome

structure os_linux_FUTEX_OP where
  cmd : os_linux_FUTEX_COMMAND
  «private» : Bool
  realtime : Bool
  _reserved : BitVec 23
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed os_linux_FUTEX_OP 32 where
  toBits v := ((Zig.Packed.toBits v.cmd).setWidth 32 <<< 0) ||| ((Zig.Packed.toBits v.«private»).setWidth 32 <<< 7) ||| ((Zig.Packed.toBits v.realtime).setWidth 32 <<< 8) ||| ((Zig.Packed.toBits v._reserved).setWidth 32 <<< 9)
  ofBits b := { cmd := Zig.Packed.get b 0, «private» := Zig.Packed.get b 7, realtime := Zig.Packed.get b 8, _reserved := Zig.Packed.get b 9 }
  valid b := Zig.Packed.validAt (os_linux_FUTEX_COMMAND) b 0

structure os_linux_E__enum_1 where
  bits : BitVec 16
  deriving Repr, Inhabited, DecidableEq

def os_linux_E__enum_1.SUCCESS : os_linux_E__enum_1 := ⟨(0 : BitVec 16)⟩
def os_linux_E__enum_1.PERM : os_linux_E__enum_1 := ⟨(1 : BitVec 16)⟩
def os_linux_E__enum_1.NOENT : os_linux_E__enum_1 := ⟨(2 : BitVec 16)⟩
def os_linux_E__enum_1.SRCH : os_linux_E__enum_1 := ⟨(3 : BitVec 16)⟩
def os_linux_E__enum_1.INTR : os_linux_E__enum_1 := ⟨(4 : BitVec 16)⟩
def os_linux_E__enum_1.IO : os_linux_E__enum_1 := ⟨(5 : BitVec 16)⟩
def os_linux_E__enum_1.NXIO : os_linux_E__enum_1 := ⟨(6 : BitVec 16)⟩
def os_linux_E__enum_1.«2BIG» : os_linux_E__enum_1 := ⟨(7 : BitVec 16)⟩
def os_linux_E__enum_1.NOEXEC : os_linux_E__enum_1 := ⟨(8 : BitVec 16)⟩
def os_linux_E__enum_1.BADF : os_linux_E__enum_1 := ⟨(9 : BitVec 16)⟩
def os_linux_E__enum_1.CHILD : os_linux_E__enum_1 := ⟨(10 : BitVec 16)⟩
def os_linux_E__enum_1.AGAIN : os_linux_E__enum_1 := ⟨(11 : BitVec 16)⟩
def os_linux_E__enum_1.NOMEM : os_linux_E__enum_1 := ⟨(12 : BitVec 16)⟩
def os_linux_E__enum_1.ACCES : os_linux_E__enum_1 := ⟨(13 : BitVec 16)⟩
def os_linux_E__enum_1.FAULT : os_linux_E__enum_1 := ⟨(14 : BitVec 16)⟩
def os_linux_E__enum_1.NOTBLK : os_linux_E__enum_1 := ⟨(15 : BitVec 16)⟩
def os_linux_E__enum_1.BUSY : os_linux_E__enum_1 := ⟨(16 : BitVec 16)⟩
def os_linux_E__enum_1.EXIST : os_linux_E__enum_1 := ⟨(17 : BitVec 16)⟩
def os_linux_E__enum_1.XDEV : os_linux_E__enum_1 := ⟨(18 : BitVec 16)⟩
def os_linux_E__enum_1.NODEV : os_linux_E__enum_1 := ⟨(19 : BitVec 16)⟩
def os_linux_E__enum_1.NOTDIR : os_linux_E__enum_1 := ⟨(20 : BitVec 16)⟩
def os_linux_E__enum_1.ISDIR : os_linux_E__enum_1 := ⟨(21 : BitVec 16)⟩
def os_linux_E__enum_1.INVAL : os_linux_E__enum_1 := ⟨(22 : BitVec 16)⟩
def os_linux_E__enum_1.NFILE : os_linux_E__enum_1 := ⟨(23 : BitVec 16)⟩
def os_linux_E__enum_1.MFILE : os_linux_E__enum_1 := ⟨(24 : BitVec 16)⟩
def os_linux_E__enum_1.NOTTY : os_linux_E__enum_1 := ⟨(25 : BitVec 16)⟩
def os_linux_E__enum_1.TXTBSY : os_linux_E__enum_1 := ⟨(26 : BitVec 16)⟩
def os_linux_E__enum_1.FBIG : os_linux_E__enum_1 := ⟨(27 : BitVec 16)⟩
def os_linux_E__enum_1.NOSPC : os_linux_E__enum_1 := ⟨(28 : BitVec 16)⟩
def os_linux_E__enum_1.SPIPE : os_linux_E__enum_1 := ⟨(29 : BitVec 16)⟩
def os_linux_E__enum_1.ROFS : os_linux_E__enum_1 := ⟨(30 : BitVec 16)⟩
def os_linux_E__enum_1.MLINK : os_linux_E__enum_1 := ⟨(31 : BitVec 16)⟩
def os_linux_E__enum_1.PIPE : os_linux_E__enum_1 := ⟨(32 : BitVec 16)⟩
def os_linux_E__enum_1.DOM : os_linux_E__enum_1 := ⟨(33 : BitVec 16)⟩
def os_linux_E__enum_1.RANGE : os_linux_E__enum_1 := ⟨(34 : BitVec 16)⟩
def os_linux_E__enum_1.DEADLK : os_linux_E__enum_1 := ⟨(35 : BitVec 16)⟩
def os_linux_E__enum_1.NAMETOOLONG : os_linux_E__enum_1 := ⟨(36 : BitVec 16)⟩
def os_linux_E__enum_1.NOLCK : os_linux_E__enum_1 := ⟨(37 : BitVec 16)⟩
def os_linux_E__enum_1.NOSYS : os_linux_E__enum_1 := ⟨(38 : BitVec 16)⟩
def os_linux_E__enum_1.NOTEMPTY : os_linux_E__enum_1 := ⟨(39 : BitVec 16)⟩
def os_linux_E__enum_1.LOOP : os_linux_E__enum_1 := ⟨(40 : BitVec 16)⟩
def os_linux_E__enum_1.NOMSG : os_linux_E__enum_1 := ⟨(42 : BitVec 16)⟩
def os_linux_E__enum_1.IDRM : os_linux_E__enum_1 := ⟨(43 : BitVec 16)⟩
def os_linux_E__enum_1.CHRNG : os_linux_E__enum_1 := ⟨(44 : BitVec 16)⟩
def os_linux_E__enum_1.L2NSYNC : os_linux_E__enum_1 := ⟨(45 : BitVec 16)⟩
def os_linux_E__enum_1.L3HLT : os_linux_E__enum_1 := ⟨(46 : BitVec 16)⟩
def os_linux_E__enum_1.L3RST : os_linux_E__enum_1 := ⟨(47 : BitVec 16)⟩
def os_linux_E__enum_1.LNRNG : os_linux_E__enum_1 := ⟨(48 : BitVec 16)⟩
def os_linux_E__enum_1.UNATCH : os_linux_E__enum_1 := ⟨(49 : BitVec 16)⟩
def os_linux_E__enum_1.NOCSI : os_linux_E__enum_1 := ⟨(50 : BitVec 16)⟩
def os_linux_E__enum_1.L2HLT : os_linux_E__enum_1 := ⟨(51 : BitVec 16)⟩
def os_linux_E__enum_1.BADE : os_linux_E__enum_1 := ⟨(52 : BitVec 16)⟩
def os_linux_E__enum_1.BADR : os_linux_E__enum_1 := ⟨(53 : BitVec 16)⟩
def os_linux_E__enum_1.XFULL : os_linux_E__enum_1 := ⟨(54 : BitVec 16)⟩
def os_linux_E__enum_1.NOANO : os_linux_E__enum_1 := ⟨(55 : BitVec 16)⟩
def os_linux_E__enum_1.BADRQC : os_linux_E__enum_1 := ⟨(56 : BitVec 16)⟩
def os_linux_E__enum_1.BADSLT : os_linux_E__enum_1 := ⟨(57 : BitVec 16)⟩
def os_linux_E__enum_1.BFONT : os_linux_E__enum_1 := ⟨(59 : BitVec 16)⟩
def os_linux_E__enum_1.NOSTR : os_linux_E__enum_1 := ⟨(60 : BitVec 16)⟩
def os_linux_E__enum_1.NODATA : os_linux_E__enum_1 := ⟨(61 : BitVec 16)⟩
def os_linux_E__enum_1.TIME : os_linux_E__enum_1 := ⟨(62 : BitVec 16)⟩
def os_linux_E__enum_1.NOSR : os_linux_E__enum_1 := ⟨(63 : BitVec 16)⟩
def os_linux_E__enum_1.NONET : os_linux_E__enum_1 := ⟨(64 : BitVec 16)⟩
def os_linux_E__enum_1.NOPKG : os_linux_E__enum_1 := ⟨(65 : BitVec 16)⟩
def os_linux_E__enum_1.REMOTE : os_linux_E__enum_1 := ⟨(66 : BitVec 16)⟩
def os_linux_E__enum_1.NOLINK : os_linux_E__enum_1 := ⟨(67 : BitVec 16)⟩
def os_linux_E__enum_1.ADV : os_linux_E__enum_1 := ⟨(68 : BitVec 16)⟩
def os_linux_E__enum_1.SRMNT : os_linux_E__enum_1 := ⟨(69 : BitVec 16)⟩
def os_linux_E__enum_1.COMM : os_linux_E__enum_1 := ⟨(70 : BitVec 16)⟩
def os_linux_E__enum_1.PROTO : os_linux_E__enum_1 := ⟨(71 : BitVec 16)⟩
def os_linux_E__enum_1.MULTIHOP : os_linux_E__enum_1 := ⟨(72 : BitVec 16)⟩
def os_linux_E__enum_1.DOTDOT : os_linux_E__enum_1 := ⟨(73 : BitVec 16)⟩
def os_linux_E__enum_1.BADMSG : os_linux_E__enum_1 := ⟨(74 : BitVec 16)⟩
def os_linux_E__enum_1.OVERFLOW : os_linux_E__enum_1 := ⟨(75 : BitVec 16)⟩
def os_linux_E__enum_1.NOTUNIQ : os_linux_E__enum_1 := ⟨(76 : BitVec 16)⟩
def os_linux_E__enum_1.BADFD : os_linux_E__enum_1 := ⟨(77 : BitVec 16)⟩
def os_linux_E__enum_1.REMCHG : os_linux_E__enum_1 := ⟨(78 : BitVec 16)⟩
def os_linux_E__enum_1.LIBACC : os_linux_E__enum_1 := ⟨(79 : BitVec 16)⟩
def os_linux_E__enum_1.LIBBAD : os_linux_E__enum_1 := ⟨(80 : BitVec 16)⟩
def os_linux_E__enum_1.LIBSCN : os_linux_E__enum_1 := ⟨(81 : BitVec 16)⟩
def os_linux_E__enum_1.LIBMAX : os_linux_E__enum_1 := ⟨(82 : BitVec 16)⟩
def os_linux_E__enum_1.LIBEXEC : os_linux_E__enum_1 := ⟨(83 : BitVec 16)⟩
def os_linux_E__enum_1.ILSEQ : os_linux_E__enum_1 := ⟨(84 : BitVec 16)⟩
def os_linux_E__enum_1.RESTART : os_linux_E__enum_1 := ⟨(85 : BitVec 16)⟩
def os_linux_E__enum_1.STRPIPE : os_linux_E__enum_1 := ⟨(86 : BitVec 16)⟩
def os_linux_E__enum_1.USERS : os_linux_E__enum_1 := ⟨(87 : BitVec 16)⟩
def os_linux_E__enum_1.NOTSOCK : os_linux_E__enum_1 := ⟨(88 : BitVec 16)⟩
def os_linux_E__enum_1.DESTADDRREQ : os_linux_E__enum_1 := ⟨(89 : BitVec 16)⟩
def os_linux_E__enum_1.MSGSIZE : os_linux_E__enum_1 := ⟨(90 : BitVec 16)⟩
def os_linux_E__enum_1.PROTOTYPE : os_linux_E__enum_1 := ⟨(91 : BitVec 16)⟩
def os_linux_E__enum_1.NOPROTOOPT : os_linux_E__enum_1 := ⟨(92 : BitVec 16)⟩
def os_linux_E__enum_1.PROTONOSUPPORT : os_linux_E__enum_1 := ⟨(93 : BitVec 16)⟩
def os_linux_E__enum_1.SOCKTNOSUPPORT : os_linux_E__enum_1 := ⟨(94 : BitVec 16)⟩
def os_linux_E__enum_1.OPNOTSUPP : os_linux_E__enum_1 := ⟨(95 : BitVec 16)⟩
def os_linux_E__enum_1.PFNOSUPPORT : os_linux_E__enum_1 := ⟨(96 : BitVec 16)⟩
def os_linux_E__enum_1.AFNOSUPPORT : os_linux_E__enum_1 := ⟨(97 : BitVec 16)⟩
def os_linux_E__enum_1.ADDRINUSE : os_linux_E__enum_1 := ⟨(98 : BitVec 16)⟩
def os_linux_E__enum_1.ADDRNOTAVAIL : os_linux_E__enum_1 := ⟨(99 : BitVec 16)⟩
def os_linux_E__enum_1.NETDOWN : os_linux_E__enum_1 := ⟨(100 : BitVec 16)⟩
def os_linux_E__enum_1.NETUNREACH : os_linux_E__enum_1 := ⟨(101 : BitVec 16)⟩
def os_linux_E__enum_1.NETRESET : os_linux_E__enum_1 := ⟨(102 : BitVec 16)⟩
def os_linux_E__enum_1.CONNABORTED : os_linux_E__enum_1 := ⟨(103 : BitVec 16)⟩
def os_linux_E__enum_1.CONNRESET : os_linux_E__enum_1 := ⟨(104 : BitVec 16)⟩
def os_linux_E__enum_1.NOBUFS : os_linux_E__enum_1 := ⟨(105 : BitVec 16)⟩
def os_linux_E__enum_1.ISCONN : os_linux_E__enum_1 := ⟨(106 : BitVec 16)⟩
def os_linux_E__enum_1.NOTCONN : os_linux_E__enum_1 := ⟨(107 : BitVec 16)⟩
def os_linux_E__enum_1.SHUTDOWN : os_linux_E__enum_1 := ⟨(108 : BitVec 16)⟩
def os_linux_E__enum_1.TOOMANYREFS : os_linux_E__enum_1 := ⟨(109 : BitVec 16)⟩
def os_linux_E__enum_1.TIMEDOUT : os_linux_E__enum_1 := ⟨(110 : BitVec 16)⟩
def os_linux_E__enum_1.CONNREFUSED : os_linux_E__enum_1 := ⟨(111 : BitVec 16)⟩
def os_linux_E__enum_1.HOSTDOWN : os_linux_E__enum_1 := ⟨(112 : BitVec 16)⟩
def os_linux_E__enum_1.HOSTUNREACH : os_linux_E__enum_1 := ⟨(113 : BitVec 16)⟩
def os_linux_E__enum_1.ALREADY : os_linux_E__enum_1 := ⟨(114 : BitVec 16)⟩
def os_linux_E__enum_1.INPROGRESS : os_linux_E__enum_1 := ⟨(115 : BitVec 16)⟩
def os_linux_E__enum_1.STALE : os_linux_E__enum_1 := ⟨(116 : BitVec 16)⟩
def os_linux_E__enum_1.UCLEAN : os_linux_E__enum_1 := ⟨(117 : BitVec 16)⟩
def os_linux_E__enum_1.NOTNAM : os_linux_E__enum_1 := ⟨(118 : BitVec 16)⟩
def os_linux_E__enum_1.NAVAIL : os_linux_E__enum_1 := ⟨(119 : BitVec 16)⟩
def os_linux_E__enum_1.ISNAM : os_linux_E__enum_1 := ⟨(120 : BitVec 16)⟩
def os_linux_E__enum_1.REMOTEIO : os_linux_E__enum_1 := ⟨(121 : BitVec 16)⟩
def os_linux_E__enum_1.DQUOT : os_linux_E__enum_1 := ⟨(122 : BitVec 16)⟩
def os_linux_E__enum_1.NOMEDIUM : os_linux_E__enum_1 := ⟨(123 : BitVec 16)⟩
def os_linux_E__enum_1.MEDIUMTYPE : os_linux_E__enum_1 := ⟨(124 : BitVec 16)⟩
def os_linux_E__enum_1.CANCELED : os_linux_E__enum_1 := ⟨(125 : BitVec 16)⟩
def os_linux_E__enum_1.NOKEY : os_linux_E__enum_1 := ⟨(126 : BitVec 16)⟩
def os_linux_E__enum_1.KEYEXPIRED : os_linux_E__enum_1 := ⟨(127 : BitVec 16)⟩
def os_linux_E__enum_1.KEYREVOKED : os_linux_E__enum_1 := ⟨(128 : BitVec 16)⟩
def os_linux_E__enum_1.KEYREJECTED : os_linux_E__enum_1 := ⟨(129 : BitVec 16)⟩
def os_linux_E__enum_1.OWNERDEAD : os_linux_E__enum_1 := ⟨(130 : BitVec 16)⟩
def os_linux_E__enum_1.NOTRECOVERABLE : os_linux_E__enum_1 := ⟨(131 : BitVec 16)⟩
def os_linux_E__enum_1.RFKILL : os_linux_E__enum_1 := ⟨(132 : BitVec 16)⟩
def os_linux_E__enum_1.HWPOISON : os_linux_E__enum_1 := ⟨(133 : BitVec 16)⟩
def os_linux_E__enum_1.NSRNODATA : os_linux_E__enum_1 := ⟨(160 : BitVec 16)⟩
def os_linux_E__enum_1.NSRFORMERR : os_linux_E__enum_1 := ⟨(161 : BitVec 16)⟩
def os_linux_E__enum_1.NSRSERVFAIL : os_linux_E__enum_1 := ⟨(162 : BitVec 16)⟩
def os_linux_E__enum_1.NSRNOTFOUND : os_linux_E__enum_1 := ⟨(163 : BitVec 16)⟩
def os_linux_E__enum_1.NSRNOTIMP : os_linux_E__enum_1 := ⟨(164 : BitVec 16)⟩
def os_linux_E__enum_1.NSRREFUSED : os_linux_E__enum_1 := ⟨(165 : BitVec 16)⟩
def os_linux_E__enum_1.NSRBADQUERY : os_linux_E__enum_1 := ⟨(166 : BitVec 16)⟩
def os_linux_E__enum_1.NSRBADNAME : os_linux_E__enum_1 := ⟨(167 : BitVec 16)⟩
def os_linux_E__enum_1.NSRBADFAMILY : os_linux_E__enum_1 := ⟨(168 : BitVec 16)⟩
def os_linux_E__enum_1.NSRBADRESP : os_linux_E__enum_1 := ⟨(169 : BitVec 16)⟩
def os_linux_E__enum_1.NSRCONNREFUSED : os_linux_E__enum_1 := ⟨(170 : BitVec 16)⟩
def os_linux_E__enum_1.NSRTIMEOUT : os_linux_E__enum_1 := ⟨(171 : BitVec 16)⟩
def os_linux_E__enum_1.NSROF : os_linux_E__enum_1 := ⟨(172 : BitVec 16)⟩
def os_linux_E__enum_1.NSRFILE : os_linux_E__enum_1 := ⟨(173 : BitVec 16)⟩
def os_linux_E__enum_1.NSRNOMEM : os_linux_E__enum_1 := ⟨(174 : BitVec 16)⟩
def os_linux_E__enum_1.NSRDESTRUCTION : os_linux_E__enum_1 := ⟨(175 : BitVec 16)⟩
def os_linux_E__enum_1.NSRQUERYDOMAINTOOLONG : os_linux_E__enum_1 := ⟨(176 : BitVec 16)⟩
def os_linux_E__enum_1.NSRCNAMELOOP : os_linux_E__enum_1 := ⟨(177 : BitVec 16)⟩

def os_linux_E__enum_1.toBits (e : os_linux_E__enum_1) : BitVec 16 := e.bits

def os_linux_E__enum_1.ofInt? (v : Int) : Option os_linux_E__enum_1 :=
  if 0 ≤ v ∧ v ≤ 65535 then Option.some ⟨BitVec.ofInt 16 v⟩ else Option.none

def os_linux_E__enum_1.isNamed (e : os_linux_E__enum_1) : Bool := e.bits == (0 : BitVec 16) || e.bits == (1 : BitVec 16) || e.bits == (2 : BitVec 16) || e.bits == (3 : BitVec 16) || e.bits == (4 : BitVec 16) || e.bits == (5 : BitVec 16) || e.bits == (6 : BitVec 16) || e.bits == (7 : BitVec 16) || e.bits == (8 : BitVec 16) || e.bits == (9 : BitVec 16) || e.bits == (10 : BitVec 16) || e.bits == (11 : BitVec 16) || e.bits == (12 : BitVec 16) || e.bits == (13 : BitVec 16) || e.bits == (14 : BitVec 16) || e.bits == (15 : BitVec 16) || e.bits == (16 : BitVec 16) || e.bits == (17 : BitVec 16) || e.bits == (18 : BitVec 16) || e.bits == (19 : BitVec 16) || e.bits == (20 : BitVec 16) || e.bits == (21 : BitVec 16) || e.bits == (22 : BitVec 16) || e.bits == (23 : BitVec 16) || e.bits == (24 : BitVec 16) || e.bits == (25 : BitVec 16) || e.bits == (26 : BitVec 16) || e.bits == (27 : BitVec 16) || e.bits == (28 : BitVec 16) || e.bits == (29 : BitVec 16) || e.bits == (30 : BitVec 16) || e.bits == (31 : BitVec 16) || e.bits == (32 : BitVec 16) || e.bits == (33 : BitVec 16) || e.bits == (34 : BitVec 16) || e.bits == (35 : BitVec 16) || e.bits == (36 : BitVec 16) || e.bits == (37 : BitVec 16) || e.bits == (38 : BitVec 16) || e.bits == (39 : BitVec 16) || e.bits == (40 : BitVec 16) || e.bits == (42 : BitVec 16) || e.bits == (43 : BitVec 16) || e.bits == (44 : BitVec 16) || e.bits == (45 : BitVec 16) || e.bits == (46 : BitVec 16) || e.bits == (47 : BitVec 16) || e.bits == (48 : BitVec 16) || e.bits == (49 : BitVec 16) || e.bits == (50 : BitVec 16) || e.bits == (51 : BitVec 16) || e.bits == (52 : BitVec 16) || e.bits == (53 : BitVec 16) || e.bits == (54 : BitVec 16) || e.bits == (55 : BitVec 16) || e.bits == (56 : BitVec 16) || e.bits == (57 : BitVec 16) || e.bits == (59 : BitVec 16) || e.bits == (60 : BitVec 16) || e.bits == (61 : BitVec 16) || e.bits == (62 : BitVec 16) || e.bits == (63 : BitVec 16) || e.bits == (64 : BitVec 16) || e.bits == (65 : BitVec 16) || e.bits == (66 : BitVec 16) || e.bits == (67 : BitVec 16) || e.bits == (68 : BitVec 16) || e.bits == (69 : BitVec 16) || e.bits == (70 : BitVec 16) || e.bits == (71 : BitVec 16) || e.bits == (72 : BitVec 16) || e.bits == (73 : BitVec 16) || e.bits == (74 : BitVec 16) || e.bits == (75 : BitVec 16) || e.bits == (76 : BitVec 16) || e.bits == (77 : BitVec 16) || e.bits == (78 : BitVec 16) || e.bits == (79 : BitVec 16) || e.bits == (80 : BitVec 16) || e.bits == (81 : BitVec 16) || e.bits == (82 : BitVec 16) || e.bits == (83 : BitVec 16) || e.bits == (84 : BitVec 16) || e.bits == (85 : BitVec 16) || e.bits == (86 : BitVec 16) || e.bits == (87 : BitVec 16) || e.bits == (88 : BitVec 16) || e.bits == (89 : BitVec 16) || e.bits == (90 : BitVec 16) || e.bits == (91 : BitVec 16) || e.bits == (92 : BitVec 16) || e.bits == (93 : BitVec 16) || e.bits == (94 : BitVec 16) || e.bits == (95 : BitVec 16) || e.bits == (96 : BitVec 16) || e.bits == (97 : BitVec 16) || e.bits == (98 : BitVec 16) || e.bits == (99 : BitVec 16) || e.bits == (100 : BitVec 16) || e.bits == (101 : BitVec 16) || e.bits == (102 : BitVec 16) || e.bits == (103 : BitVec 16) || e.bits == (104 : BitVec 16) || e.bits == (105 : BitVec 16) || e.bits == (106 : BitVec 16) || e.bits == (107 : BitVec 16) || e.bits == (108 : BitVec 16) || e.bits == (109 : BitVec 16) || e.bits == (110 : BitVec 16) || e.bits == (111 : BitVec 16) || e.bits == (112 : BitVec 16) || e.bits == (113 : BitVec 16) || e.bits == (114 : BitVec 16) || e.bits == (115 : BitVec 16) || e.bits == (116 : BitVec 16) || e.bits == (117 : BitVec 16) || e.bits == (118 : BitVec 16) || e.bits == (119 : BitVec 16) || e.bits == (120 : BitVec 16) || e.bits == (121 : BitVec 16) || e.bits == (122 : BitVec 16) || e.bits == (123 : BitVec 16) || e.bits == (124 : BitVec 16) || e.bits == (125 : BitVec 16) || e.bits == (126 : BitVec 16) || e.bits == (127 : BitVec 16) || e.bits == (128 : BitVec 16) || e.bits == (129 : BitVec 16) || e.bits == (130 : BitVec 16) || e.bits == (131 : BitVec 16) || e.bits == (132 : BitVec 16) || e.bits == (133 : BitVec 16) || e.bits == (160 : BitVec 16) || e.bits == (161 : BitVec 16) || e.bits == (162 : BitVec 16) || e.bits == (163 : BitVec 16) || e.bits == (164 : BitVec 16) || e.bits == (165 : BitVec 16) || e.bits == (166 : BitVec 16) || e.bits == (167 : BitVec 16) || e.bits == (168 : BitVec 16) || e.bits == (169 : BitVec 16) || e.bits == (170 : BitVec 16) || e.bits == (171 : BitVec 16) || e.bits == (172 : BitVec 16) || e.bits == (173 : BitVec 16) || e.bits == (174 : BitVec 16) || e.bits == (175 : BitVec 16) || e.bits == (176 : BitVec 16) || e.bits == (177 : BitVec 16)

instance : Zig.Packed os_linux_E__enum_1 16 where
  toBits := os_linux_E__enum_1.toBits
  ofBits b := ⟨b⟩

inductive math_Order where
  | gt
  | lt
  | eq
  deriving Repr, Inhabited, DecidableEq

def math_Order.toBits : math_Order → BitVec 2
  | .gt => (0 : BitVec 2)
  | .lt => (1 : BitVec 2)
  | .eq => (2 : BitVec 2)

def math_Order.ofInt? (v : Int) : Option math_Order :=
  if v = 0 then Option.some .gt else if v = 1 then Option.some .lt else if v = 2 then Option.some .eq else Option.none

def math_Order.isNamed (_ : math_Order) : Bool := true

instance : Zig.Packed math_Order 2 where
  toBits := math_Order.toBits
  ofBits b := (math_Order.ofInt? (Zig.val false b)).getD default
  valid b := (math_Order.ofInt? (Zig.val false b)).isSome

structure Thread_SpawnConfig where
  stack_size : BitVec 64
  allocator : Option (Zig.Allocator)
  deriving Repr, Inhabited, DecidableEq

structure Thread_Futex_Deadline where
  timeout : Option (BitVec 64)
  started : time_Timer
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Thread_Futex_Deadline where
  size := 48
  align := 8
  encode v := Zig.Enc.fields 48 [(0, Zig.Enc.encode v.timeout), (16, Zig.Enc.encode v.started)]
  decode bs := do pure { timeout := ← Zig.Enc.decodeAt bs 0, started := ← Zig.Enc.decodeAt bs 16 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

/-- The spawn targets of the program. -/
inductive Tgt where
  | producer (a : Zig.Ptr)
  | work (a : Zig.Ptr)
  | task (a : Zig.Ptr)

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

structure Thread_Mutex_FutexImpl_unlockLocals where
  deriving Inhabited

inductive Thread_Mutex_FutexImpl_unlockExit where
  | ret
  | br2 (v : BitVec 32)
  | br8

def Thread_Mutex_FutexImpl_unlock (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  Zig.mutexOwnerCheck p0
  let e ← ((do
    let i1 ← pure p0
    match ← ((do
      let i3 ← pure i1
      let i4 ← Zig.atomicRmwC Zig.RmwOp.xchg false Zig.AtomicOrder.release 4 i3 (0 : BitVec 32)
      pure (.br2 i4)) : Zig.CM Tgt Thread_Mutex_FutexImpl_unlockLocals Thread_Mutex_FutexImpl_unlockExit) with
    | .br2 v2 => (do
      let i6 ← pure (v2 != (0 : BitVec 32))
      let _i7 ← Zig.callRC (debug_assert i6)
      match ← ((do
        let i9 ← pure (v2 == (3 : BitVec 32))
        if i9 then (do
          let i11 ← pure p0
          let i12 ← pure (i11)
          let _i13 ← Zig.threadFutexWakeC i12 (1 : BitVec 32)
          pure .br8)
        else (do
          pure .br8)) : Zig.CM Tgt Thread_Mutex_FutexImpl_unlockLocals Thread_Mutex_FutexImpl_unlockExit) with
      | .br8 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_Mutex_FutexImpl_unlockLocals Thread_Mutex_FutexImpl_unlockExit).run' (default : Thread_Mutex_FutexImpl_unlockLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Thread_Mutex_unlockLocals where
  deriving Inhabited

inductive Thread_Mutex_unlockExit where
  | ret

def Thread_Mutex_unlock (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let _i2 ← Zig.callC (Thread_Mutex_FutexImpl_unlock i1)
    pure .ret) : Zig.CM Tgt Thread_Mutex_unlockLocals Thread_Mutex_unlockExit).run' (default : Thread_Mutex_unlockLocals)
  match e with
  | .ret => pure ()

structure posix_errno__anon_c57b4435c781Locals where
  deriving Inhabited

inductive posix_errno__anon_c57b4435c781Exit where
  | ret (v : os_linux_E__enum_1)
  | br5 (v : Bool)
  | br2 (v : BitVec 64)

def posix_errno__anon_c57b4435c781 (p0 : BitVec 64) : Zig.Result (os_linux_E__enum_1) := do
  let e ← ((do
    let i1 ← pure (p0)
    match ← ((do
      let i3 ← pure (i1)
      let i4 ← pure (Zig.gt true i3 (-(4096 : BitVec 64)))
      match ← ((do
        if i4 then (do
          let i7 ← pure (i1)
          let i8 ← pure (Zig.lt true i7 (0 : BitVec 64))
          pure (.br5 i8))
        else (do
          pure (.br5 false))) : Zig.M posix_errno__anon_c57b4435c781Locals posix_errno__anon_c57b4435c781Exit) with
      | .br5 v5 => (do
        if v5 then (do
          let i12 ← Zig.sub true (0 : BitVec 64) i1
          pure (.br2 i12))
        else (do
          pure (.br2 (0 : BitVec 64))))
      | e => pure e) : Zig.M posix_errno__anon_c57b4435c781Locals posix_errno__anon_c57b4435c781Exit) with
    | .br2 v2 => (do
      let i15 ← Zig.enumOf (os_linux_E__enum_1.ofInt? (Zig.val true v2))
      pure (.ret i15))
    | e => pure e) : Zig.M posix_errno__anon_c57b4435c781Locals posix_errno__anon_c57b4435c781Exit).run' (default : posix_errno__anon_c57b4435c781Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure posix_unexpectedErrnoLocals where
  deriving Inhabited

inductive posix_unexpectedErrnoExit where
  | ret (v : Zig.ErrName)

def posix_unexpectedErrno (p0 : os_linux_E__enum_1) : Zig.Result (Zig.ErrName) := do
  let e ← ((do
    pure (.ret "Unexpected")) : Zig.M posix_unexpectedErrnoLocals posix_unexpectedErrnoExit).run' (default : posix_unexpectedErrnoLocals)
  match e with
  | .ret v => pure v

structure posix_clock_gettimeLocals where
  tp : Zig.Ptr
  deriving Inhabited

inductive posix_clock_gettimeExit where
  | ret (v : Except Zig.ErrName (os_linux_timespec__struct_1))

def posix_clock_gettime [Zig.Os.HasEnv] (p0 : os_linux_clockid_t) : Zig.ConcM Tgt (Except Zig.ErrName (os_linux_timespec__struct_1)) := do
  let s1 ← Zig.allocStack 16 8
  let e ← ((do
    let i1 ← pure (← get).tp
    Zig.storeUndef (os_linux_timespec__struct_1) 8 i1
    let i3 ← Zig.callC (Zig.Os.Linux.clock_gettime Zig.Os.HasEnv.env (os_linux_clockid_t.toBits p0) i1)
    let i4 ← Zig.callRC (posix_errno__anon_c57b4435c781 i3)
    if i4 == os_linux_E__enum_1.SUCCESS then (do
      let i10 ← Zig.load (os_linux_timespec__struct_1) 8 i1
      let i11 ← pure ((.ok i10) : Except Zig.ErrName (os_linux_timespec__struct_1))
      pure (.ret i11))
    else (do
      if i4 == os_linux_E__enum_1.FAULT then (do
        throw .unreachable)
      else (do
        if i4 == os_linux_E__enum_1.INVAL then (do
          pure (.ret (.error "UnsupportedClock" : Except Zig.ErrName (os_linux_timespec__struct_1))))
        else (do
          let i6 ← Zig.callRC (posix_unexpectedErrno i4)
          let i7 ← pure (i6)
          let i8 ← pure ((.error i7) : Except Zig.ErrName (os_linux_timespec__struct_1))
          pure (.ret i8))))) : Zig.CM Tgt posix_clock_gettimeLocals posix_clock_gettimeExit).run' { (default : posix_clock_gettimeLocals) with tp := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

structure time_Instant_nowLocals where
  local8 : Zig.Ptr
  deriving Inhabited

inductive time_Instant_nowExit where
  | ret (v : Except Zig.ErrName (time_Instant))
  | br0 (v : os_linux_timespec__struct_1)

def time_Instant_now [Zig.Os.HasEnv]  : Zig.ConcM Tgt (Except Zig.ErrName (time_Instant)) := do
  let s8 ← Zig.allocStack 24 8
  let e ← ((do
    match ← ((do
      let i1 ← Zig.callC (posix_clock_gettime os_linux_clockid_t.BOOTTIME)
      let i2 ← pure (Zig.isNonErr i1)
      if i2 then (do
        let i4 ← Zig.callRC (Zig.unwrapPayload i1)
        pure (.br0 i4))
      else (do
        let _i6 ← Zig.callRC (Zig.unwrapErr i1)
        pure (.ret (.error "Unsupported" : Except Zig.ErrName (time_Instant))))) : Zig.CM Tgt time_Instant_nowLocals time_Instant_nowExit) with
    | .br0 v0 => (do
      let i8 ← pure (← get).local8
      let i9 ← Zig.errSetOk (time_Instant) 8 i8
      let i10 ← pure i9
      Zig.store (α := os_linux_timespec__struct_1) 8 i10 v0
      pure (.ret (← (letI : Zig.Enc (Except Zig.ErrName (time_Instant)) := Zig.errorUnionEnc (⟨#["Unsupported"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (time_Instant))); Zig.load (Except Zig.ErrName (time_Instant)) 8 i8))))
    | e => pure e) : Zig.CM Tgt time_Instant_nowLocals time_Instant_nowExit).run' { (default : time_Instant_nowLocals) with local8 := s8 }
  Zig.free s8
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure time_Timer_startLocals where
  deriving Inhabited

inductive time_Timer_startExit where
  | ret (v : Except Zig.ErrName (time_Timer))
  | br0 (v : time_Instant)

def time_Timer_start [Zig.Os.HasEnv]  : Zig.ConcM Tgt (Except Zig.ErrName (time_Timer)) := do
  let e ← ((do
    match ← ((do
      let i1 ← Zig.callC (time_Instant_now )
      let i2 ← pure (Zig.isNonErr i1)
      if i2 then (do
        let i4 ← Zig.callRC (Zig.unwrapPayload i1)
        pure (.br0 i4))
      else (do
        let _i6 ← Zig.callRC (Zig.unwrapErr i1)
        pure (.ret (.error "TimerUnsupported" : Except Zig.ErrName (time_Timer))))) : Zig.CM Tgt time_Timer_startLocals time_Timer_startExit) with
    | .br0 v0 => (do
      let i8 ← pure { started := v0, previous := v0 : time_Timer }
      let i9 ← pure ((.ok i8) : Except Zig.ErrName (time_Timer))
      pure (.ret i9))
    | e => pure e) : Zig.CM Tgt time_Timer_startLocals time_Timer_startExit).run' (default : time_Timer_startLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Thread_Futex_Deadline_initLocals where
  deadline : Zig.Bytes (Thread_Futex_Deadline)
  deriving Inhabited

inductive Thread_Futex_Deadline_initExit where
  | ret (v : Zig.Bytes (Thread_Futex_Deadline))
  | br11 (v : time_Timer)
  | br5

def Thread_Futex_Deadline_init [Zig.Os.HasEnv] (p0 : Option (BitVec 64)) : Zig.ConcM Tgt (Zig.Bytes (Thread_Futex_Deadline)) := do
  let e ← ((do
    modify (fun s => { s with deadline := Zig.Bytes.setUndef (Thread_Futex_Deadline) s.deadline 0 })
    modify (fun s => { s with deadline := Zig.Bytes.set s.deadline 0 (p0 : Option (BitVec 64)) })
    match ← ((do
      let i6 ← pure (← get).deadline
      let i7 ← Zig.Bytes.get (Option (BitVec 64)) i6 0
      let i8 ← pure ((i7).isSome)
      if i8 then (do
        match ← ((do
          let i12 ← Zig.callC (time_Timer_start )
          let i13 ← pure (Zig.isNonErr i12)
          if i13 then (do
            let i15 ← Zig.callRC (Zig.unwrapPayload i12)
            pure (.br11 i15))
          else (do
            let i17 ← Zig.callRC (Zig.unwrapErr i12)
            let _i18 ← pure (i17)
            throw .panic)) : Zig.CM Tgt Thread_Futex_Deadline_initLocals Thread_Futex_Deadline_initExit) with
        | .br11 v11 => (do
          modify (fun s => { s with deadline := Zig.Bytes.set s.deadline 16 (v11 : time_Timer) })
          pure .br5)
        | e => pure e)
      else (do
        pure .br5)) : Zig.CM Tgt Thread_Futex_Deadline_initLocals Thread_Futex_Deadline_initExit) with
    | .br5 => (do
      let i24 ← pure (← get).deadline
      pure (.ret i24))
    | e => pure e) : Zig.CM Tgt Thread_Futex_Deadline_initLocals Thread_Futex_Deadline_initExit).run' { (default : Thread_Futex_Deadline_initLocals) with deadline := Zig.Bytes.undef (Thread_Futex_Deadline) }
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure math_order__anon_2e4ff451439dLocals where
  deriving Inhabited

inductive math_order__anon_2e4ff451439dExit where
  | ret (v : math_Order)

def math_order__anon_2e4ff451439d (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (math_Order) := do
  let e ← ((do
    let i2 ← pure (p0)
    let i3 ← pure (p1)
    let i4 ← pure (i2 == i3)
    if i4 then (do
      pure (.ret math_Order.eq))
    else (do
      let i7 ← pure (p0)
      let i8 ← pure (p1)
      let i9 ← pure (Zig.lt true i7 i8)
      if i9 then (do
        pure (.ret math_Order.lt))
      else (do
        let i12 ← pure (p0)
        let i13 ← pure (p1)
        let i14 ← pure (Zig.gt true i12 i13)
        if i14 then (do
          pure (.ret math_Order.gt))
        else (do
          throw .unreachable)))) : Zig.M math_order__anon_2e4ff451439dLocals math_order__anon_2e4ff451439dExit).run' (default : math_order__anon_2e4ff451439dLocals)
  match e with
  | .ret v => pure v

structure time_Instant_orderLocals where
  ord : math_Order
  deriving Inhabited

inductive time_Instant_orderExit where
  | ret (v : math_Order)
  | br9

def time_Instant_order (p0 : time_Instant) (p1 : time_Instant) : Zig.Result (math_Order) := do
  let e ← ((do
    let i3 ← pure ((p0).timestamp)
    let i4 ← pure ((i3).sec)
    let i5 ← pure ((p1).timestamp)
    let i6 ← pure ((i5).sec)
    let i7 ← Zig.call (math_order__anon_2e4ff451439d i4 i6)
    modify (fun s => { s with ord := i7 })
    match ← ((do
      let i10 ← pure ((← get).ord)
      let i11 ← pure (i10 == math_Order.eq)
      if i11 then (do
        let i13 ← pure ((p0).timestamp)
        let i14 ← pure ((i13).nsec)
        let i15 ← pure ((p1).timestamp)
        let i16 ← pure ((i15).nsec)
        let i17 ← Zig.call (math_order__anon_2e4ff451439d i14 i16)
        modify (fun s => { s with ord := i17 })
        pure .br9)
      else (do
        pure .br9)) : Zig.M time_Instant_orderLocals time_Instant_orderExit) with
    | .br9 => (do
      let i21 ← pure ((← get).ord)
      pure (.ret i21))
    | e => pure e) : Zig.M time_Instant_orderLocals time_Instant_orderExit).run' (default : time_Instant_orderLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure time_Timer_sampleLocals where
  deriving Inhabited

inductive time_Timer_sampleExit where
  | ret (v : time_Instant)
  | br1 (v : time_Instant)
  | br11

def time_Timer_sample [Zig.Os.HasEnv] (p0 : Zig.Ptr) : Zig.ConcM Tgt (time_Instant) := do
  let e ← ((do
    match ← ((do
      let i2 ← Zig.callC (time_Instant_now )
      let i3 ← pure (Zig.isNonErr i2)
      if i3 then (do
        let i5 ← Zig.callRC (Zig.unwrapPayload i2)
        pure (.br1 i5))
      else (do
        let i7 ← Zig.callRC (Zig.unwrapErr i2)
        let _i8 ← pure (i7)
        throw .panic)) : Zig.CM Tgt time_Timer_sampleLocals time_Timer_sampleExit) with
    | .br1 v1 => (do
      match ← ((do
        let i12 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
        let i13 ← Zig.load (time_Instant) 8 i12
        let i14 ← Zig.callRC (time_Instant_order v1 i13)
        let i15 ← pure (i14 == math_Order.gt)
        if i15 then (do
          let i17 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
          Zig.store (α := time_Instant) 8 i17 v1
          pure .br11)
        else (do
          pure .br11)) : Zig.CM Tgt time_Timer_sampleLocals time_Timer_sampleExit) with
      | .br11 => (do
        let i21 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
        let i22 ← Zig.load (time_Instant) 8 i21
        pure (.ret i22))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt time_Timer_sampleLocals time_Timer_sampleExit).run' (default : time_Timer_sampleLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure time_Instant_sinceLocals where
  deriving Inhabited

inductive time_Instant_sinceExit where
  | ret (v : BitVec 64)

def time_Instant_since (p0 : time_Instant) (p1 : time_Instant) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← pure ((p0).timestamp)
    let i3 ← pure ((i2).sec)
    let i4 ← pure ((p1).timestamp)
    let i5 ← pure ((i4).sec)
    let i6 ← Zig.sub true i3 i5
    let i7 ← Zig.intCast true false 64 i6
    let i8 ← Zig.mul false i7 (1000000000 : BitVec 64)
    let i9 ← pure ((p0).timestamp)
    let i10 ← pure ((i9).nsec)
    let i11 ← Zig.intCast true false 32 i10
    let i12 ← Zig.intCast false false 64 i11
    let i13 ← Zig.add false i8 i12
    let i14 ← pure ((p1).timestamp)
    let i15 ← pure ((i14).nsec)
    let i16 ← Zig.intCast true false 32 i15
    let i17 ← Zig.intCast false false 64 i16
    let i18 ← Zig.sub false i13 i17
    pure (.ret i18)) : Zig.M time_Instant_sinceLocals time_Instant_sinceExit).run' (default : time_Instant_sinceLocals)
  match e with
  | .ret v => pure v

structure time_Timer_readLocals where
  deriving Inhabited

inductive time_Timer_readExit where
  | ret (v : BitVec 64)

def time_Timer_read [Zig.Os.HasEnv] (p0 : Zig.Ptr) : Zig.ConcM Tgt (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.callC (time_Timer_sample p0)
    let i2 ← pure p0
    let i3 ← Zig.load (time_Instant) 8 i2
    let i4 ← Zig.callRC (time_Instant_since i1 i3)
    pure (.ret i4)) : Zig.CM Tgt time_Timer_readLocals time_Timer_readExit).run' (default : time_Timer_readLocals)
  match e with
  | .ret v => pure v

structure math_sub__anon_85a035d52c51Locals where
  deriving Inhabited

inductive math_sub__anon_85a035d52c51Exit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br3

def math_sub__anon_85a035d52c51 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← pure (Zig.subWithOverflow false p0 p1)
    match ← ((do
      let i4 ← pure ((i2).2)
      let i5 ← pure (i4 != (0 : BitVec 1))
      if i5 then (do
        pure (.ret (.error "Overflow" : Except Zig.ErrName (BitVec 64))))
      else (do
        pure .br3)) : Zig.M math_sub__anon_85a035d52c51Locals math_sub__anon_85a035d52c51Exit) with
    | .br3 => (do
      let i9 ← pure ((i2).1)
      let i10 ← pure ((.ok i9) : Except Zig.ErrName (BitVec 64))
      pure (.ret i10))
    | e => pure e) : Zig.M math_sub__anon_85a035d52c51Locals math_sub__anon_85a035d52c51Exit).run' (default : math_sub__anon_85a035d52c51Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure os_linux_errnoFromSyscallLocals where
  deriving Inhabited

inductive os_linux_errnoFromSyscallExit where
  | ret (v : os_linux_E__enum_1)
  | br5 (v : Bool)
  | br2 (v : BitVec 64)

def os_linux_errnoFromSyscall (p0 : BitVec 64) : Zig.Result (os_linux_E__enum_1) := do
  let e ← ((do
    let i1 ← pure (p0)
    match ← ((do
      let i3 ← pure (i1)
      let i4 ← pure (Zig.gt true i3 (-(4096 : BitVec 64)))
      match ← ((do
        if i4 then (do
          let i7 ← pure (i1)
          let i8 ← pure (Zig.lt true i7 (0 : BitVec 64))
          pure (.br5 i8))
        else (do
          pure (.br5 false))) : Zig.M os_linux_errnoFromSyscallLocals os_linux_errnoFromSyscallExit) with
      | .br5 v5 => (do
        if v5 then (do
          let i12 ← Zig.sub true (0 : BitVec 64) i1
          pure (.br2 i12))
        else (do
          pure (.br2 (0 : BitVec 64))))
      | e => pure e) : Zig.M os_linux_errnoFromSyscallLocals os_linux_errnoFromSyscallExit) with
    | .br2 v2 => (do
      let i15 ← Zig.enumOf (os_linux_E__enum_1.ofInt? (Zig.val true v2))
      pure (.ret i15))
    | e => pure e) : Zig.M os_linux_errnoFromSyscallLocals os_linux_errnoFromSyscallExit).run' (default : os_linux_errnoFromSyscallLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Thread_Futex_LinuxImpl_waitLocals where
  ts : Zig.Ptr
  deriving Inhabited

inductive Thread_Futex_LinuxImpl_waitExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br5
  | br21 (v : Option (Zig.Ptr))
  | br29

def Thread_Futex_LinuxImpl_wait (p0 : Zig.Ptr) (p1 : BitVec 32) (p2 : Option (BitVec 64)) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let s3 ← Zig.allocStack 16 8
  let e ← ((do
    let i3 ← pure (← get).ts
    Zig.storeUndef (os_linux_timespec__struct_1) 8 i3
    match ← ((do
      let i6 ← pure ((p2).isSome)
      if i6 then (do
        let i8 ← Zig.optPayload p2
        let i9 ← pure i3
        let i10 ← Zig.divTrunc false i8 (1000000000 : BitVec 64)
        let i11 ← Zig.intCast false true 64 i10
        Zig.store (α := BitVec 64) 8 i9 i11
        let i13 ← Zig.callMC (Zig.ptrProject i3 (·.add 8))
        let i14 ← Zig.rem false i8 (1000000000 : BitVec 64)
        let i15 ← Zig.intCast false true 64 i14
        Zig.store (α := BitVec 64) 8 i13 i15
        pure .br5)
      else (do
        pure .br5)) : Zig.CM Tgt Thread_Futex_LinuxImpl_waitLocals Thread_Futex_LinuxImpl_waitExit) with
    | .br5 => (do
      let i19 ← pure p0
      let i20 ← pure (i19)
      match ← ((do
        let i22 ← pure ((p2).isSome)
        if i22 then (do
          let i24 ← pure (i3)
          pure (.br21 i24))
        else (do
          pure (.br21 none))) : Zig.CM Tgt Thread_Futex_LinuxImpl_waitLocals Thread_Futex_LinuxImpl_waitExit) with
      | .br21 v21 => (do
        let i27 ← Zig.callC (Zig.Os.Linux.futex_4arg i20 (Zig.Packed.toBits ({ cmd := os_linux_FUTEX_COMMAND.WAIT, «private» := true, realtime := false, _reserved := (0 : BitVec 23) } : os_linux_FUTEX_OP)) p1 v21)
        let i28 ← Zig.callRC (os_linux_errnoFromSyscall i27)
        match ← ((do
          if i28 == os_linux_E__enum_1.SUCCESS then (do
            pure .br29)
          else (do
            if i28 == os_linux_E__enum_1.INTR then (do
              pure .br29)
            else (do
              if i28 == os_linux_E__enum_1.AGAIN then (do
                pure .br29)
              else (do
                if i28 == os_linux_E__enum_1.TIMEDOUT then (do
                  let i36 ← pure ((p2).isSome)
                  let _i37 ← Zig.callRC (debug_assert i36)
                  pure (.ret (.error "Timeout" : Except Zig.ErrName (Unit))))
                else (do
                  if i28 == os_linux_E__enum_1.INVAL then (do
                    pure .br29)
                  else (do
                    if i28 == os_linux_E__enum_1.FAULT then (do
                      throw .unreachable)
                    else (do
                      throw .unreachable))))))) : Zig.CM Tgt Thread_Futex_LinuxImpl_waitLocals Thread_Futex_LinuxImpl_waitExit) with
        | .br29 => (do
          pure (.ret (.ok () : Except Zig.ErrName (Unit))))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_Futex_LinuxImpl_waitLocals Thread_Futex_LinuxImpl_waitExit).run' { (default : Thread_Futex_LinuxImpl_waitLocals) with ts := s3 }
  Zig.free s3
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Thread_Futex_timedWaitLocals where
  deriving Inhabited

inductive Thread_Futex_timedWaitExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br7 (v : BitVec 32)
  | br6
  | br3

def Thread_Futex_timedWait (p0 : Zig.Ptr) (p1 : BitVec 32) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p2 == (0 : BitVec 64))
      if i4 then (do
        match ← ((do
          match ← ((do
            let i8 ← pure p0
            let i9 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.seqCst 4 i8
            pure (.br7 i9)) : Zig.CM Tgt Thread_Futex_timedWaitLocals Thread_Futex_timedWaitExit) with
          | .br7 v7 => (do
            let i11 ← pure (v7 != p1)
            if i11 then (do
              pure (.ret (.ok () : Except Zig.ErrName (Unit))))
            else (do
              pure .br6))
          | e => pure e) : Zig.CM Tgt Thread_Futex_timedWaitLocals Thread_Futex_timedWaitExit) with
        | .br6 => (do
          pure (.ret (.error "Timeout" : Except Zig.ErrName (Unit))))
        | e => pure e)
      else (do
        pure .br3)) : Zig.CM Tgt Thread_Futex_timedWaitLocals Thread_Futex_timedWaitExit) with
    | .br3 => (do
      let i17 ← pure (some p2)
      let i18 ← Zig.callC (Thread_Futex_LinuxImpl_wait p0 p1 i17)
      pure (.ret i18))
    | e => pure e) : Zig.CM Tgt Thread_Futex_timedWaitLocals Thread_Futex_timedWaitExit).run' (default : Thread_Futex_timedWaitLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Thread_Futex_Deadline_waitLocals where
  deriving Inhabited

inductive Thread_Futex_Deadline_waitExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br3 (v : BitVec 64)
  | br14 (v : BitVec 64)

def Thread_Futex_Deadline_wait [Zig.Os.HasEnv] (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure p0
      let i5 ← Zig.load (Option (BitVec 64)) 8 i4
      let i6 ← pure ((i5).isSome)
      if i6 then (do
        let i8 ← Zig.optPayload i5
        pure (.br3 i8))
      else (do
        let _i10 ← Zig.threadFutexWaitC p1 p2
        pure (.ret (.ok () : Except Zig.ErrName (Unit))))) : Zig.CM Tgt Thread_Futex_Deadline_waitLocals Thread_Futex_Deadline_waitExit) with
    | .br3 v3 => (do
      let i12 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
      let i13 ← Zig.callC (time_Timer_read i12)
      match ← ((do
        let i15 ← Zig.callRC (math_sub__anon_85a035d52c51 v3 i13)
        let i16 ← pure (Zig.isNonErr i15)
        if i16 then (do
          let i18 ← Zig.callRC (Zig.unwrapPayload i15)
          pure (.br14 i18))
        else (do
          let _i20 ← Zig.callRC (Zig.unwrapErr i15)
          pure (.br14 (0 : BitVec 64)))) : Zig.CM Tgt Thread_Futex_Deadline_waitLocals Thread_Futex_Deadline_waitExit) with
      | .br14 v14 => (do
        let i22 ← Zig.callC (Thread_Futex_timedWait p1 p2 v14)
        pure (.ret i22))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_Futex_Deadline_waitLocals Thread_Futex_Deadline_waitExit).run' (default : Thread_Futex_Deadline_waitLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Thread_Mutex_FutexImpl_tryLockLocals where
  deriving Inhabited

inductive Thread_Mutex_FutexImpl_tryLockExit where
  | ret (v : Bool)
  | br1
  | br5 (v : BitVec 32)
  | br4 (v : BitVec 1)

def Thread_Mutex_FutexImpl_tryLock (p0 : Zig.Ptr) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    match ← ((do
      pure .br1) : Zig.CM Tgt Thread_Mutex_FutexImpl_tryLockLocals Thread_Mutex_FutexImpl_tryLockExit) with
    | .br1 => (do
      let i3 ← pure p0
      match ← ((do
        match ← ((do
          let i6 ← pure i3
          let i7 ← Zig.atomicRmwC Zig.RmwOp.or false Zig.AtomicOrder.acquire 4 i6 (1 : BitVec 32)
          pure (.br5 i7)) : Zig.CM Tgt Thread_Mutex_FutexImpl_tryLockLocals Thread_Mutex_FutexImpl_tryLockExit) with
        | .br5 v5 => (do
          let i9 ← pure (v5 &&& (1 : BitVec 32))
          let i10 ← pure (i9 != (0 : BitVec 32))
          let i11 ← pure (if i10 then 1 else 0 : BitVec 1)
          pure (.br4 i11))
        | e => pure e) : Zig.CM Tgt Thread_Mutex_FutexImpl_tryLockLocals Thread_Mutex_FutexImpl_tryLockExit) with
      | .br4 v4 => (do
        let i13 ← pure (v4 == (0 : BitVec 1))
        pure (.ret i13))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_Mutex_FutexImpl_tryLockLocals Thread_Mutex_FutexImpl_tryLockExit).run' (default : Thread_Mutex_FutexImpl_tryLockLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Thread_Mutex_FutexImpl_lockSlowLocals where
  deriving Inhabited

inductive Thread_Mutex_FutexImpl_lockSlowExit where
  | ret
  | br4 (v : BitVec 32)
  | br1
  | br19 (v : BitVec 32)
  | br17
  | br15
  | rep16

def Thread_Mutex_FutexImpl_lockSlow.again16 : Thread_Mutex_FutexImpl_lockSlowExit → Bool
  | .rep16 => true
  | _ => false

def Thread_Mutex_FutexImpl_lockSlow.loop16 (p0 : Zig.Ptr) : Zig.CM Tgt Thread_Mutex_FutexImpl_lockSlowLocals Thread_Mutex_FutexImpl_lockSlowExit := do
  match ← ((do
    let i18 ← pure p0
    match ← ((do
      let i20 ← pure i18
      let i21 ← Zig.atomicRmwC Zig.RmwOp.xchg false Zig.AtomicOrder.acquire 4 i20 (3 : BitVec 32)
      pure (.br19 i21)) : Zig.CM Tgt Thread_Mutex_FutexImpl_lockSlowLocals Thread_Mutex_FutexImpl_lockSlowExit) with
    | .br19 v19 => (do
      let i23 ← pure (v19 != (0 : BitVec 32))
      if i23 then (do
        let i25 ← pure p0
        let i26 ← pure (i25)
        let _i27 ← Zig.threadFutexWaitC i26 (3 : BitVec 32)
        pure .br17)
      else (do
        pure .br15))
    | e => pure e) : Zig.CM Tgt Thread_Mutex_FutexImpl_lockSlowLocals Thread_Mutex_FutexImpl_lockSlowExit) with
  | .br17 => (do
    pure .rep16)
  | e => pure e

def Thread_Mutex_FutexImpl_lockSlow (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure p0
      let i3 ← pure (i2)
      match ← ((do
        let i5 ← pure i3
        let i6 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.relaxed 4 i5
        pure (.br4 i6)) : Zig.CM Tgt Thread_Mutex_FutexImpl_lockSlowLocals Thread_Mutex_FutexImpl_lockSlowExit) with
      | .br4 v4 => (do
        let i8 ← pure (v4 == (3 : BitVec 32))
        if i8 then (do
          let i10 ← pure p0
          let i11 ← pure (i10)
          let _i12 ← Zig.threadFutexWaitC i11 (3 : BitVec 32)
          pure .br1)
        else (do
          pure .br1))
      | e => pure e) : Zig.CM Tgt Thread_Mutex_FutexImpl_lockSlowLocals Thread_Mutex_FutexImpl_lockSlowExit) with
    | .br1 => (do
      match ← ((do
        Zig.loop (Thread_Mutex_FutexImpl_lockSlow.loop16 p0) Thread_Mutex_FutexImpl_lockSlow.again16) : Zig.CM Tgt Thread_Mutex_FutexImpl_lockSlowLocals Thread_Mutex_FutexImpl_lockSlowExit) with
      | .br15 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_Mutex_FutexImpl_lockSlowLocals Thread_Mutex_FutexImpl_lockSlowExit).run' (default : Thread_Mutex_FutexImpl_lockSlowLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Thread_Mutex_FutexImpl_lockLocals where
  deriving Inhabited

inductive Thread_Mutex_FutexImpl_lockExit where
  | ret
  | br1

def Thread_Mutex_FutexImpl_lock (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    match ← ((do
      let i2 ← Zig.callC (Thread_Mutex_FutexImpl_tryLock p0)
      let i3 ← pure (!i2)
      if i3 then (do
        let _i5 ← Zig.callC (Thread_Mutex_FutexImpl_lockSlow p0)
        pure .br1)
      else (do
        pure .br1)) : Zig.CM Tgt Thread_Mutex_FutexImpl_lockLocals Thread_Mutex_FutexImpl_lockExit) with
    | .br1 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt Thread_Mutex_FutexImpl_lockLocals Thread_Mutex_FutexImpl_lockExit).run' (default : Thread_Mutex_FutexImpl_lockLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Thread_Mutex_lockLocals where
  deriving Inhabited

inductive Thread_Mutex_lockExit where
  | ret

def Thread_Mutex_lock (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let _i2 ← Zig.callC (Thread_Mutex_FutexImpl_lock i1)
    pure .ret) : Zig.CM Tgt Thread_Mutex_lockLocals Thread_Mutex_lockExit).run' (default : Thread_Mutex_lockLocals)
  match e with
  | .ret => pure ()

structure Thread_Condition_FutexImpl_waitLocals where
  epoch : BitVec 32
  state : BitVec 32
  futex_deadline : Zig.Ptr
  deriving Inhabited

inductive Thread_Condition_FutexImpl_waitExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br6 (v : BitVec 32)
  | br13 (v : BitVec 32)
  | br35
  | br58 (v : Option (BitVec 32))
  | br55 (v : BitVec 32)
  | br51
  | br46
  | br44
  | br78 (v : Option (BitVec 32))
  | br75 (v : BitVec 32)
  | br43
  | br94 (v : BitVec 32)
  | br101 (v : BitVec 32)
  | br120 (v : Option (BitVec 32))
  | br117 (v : BitVec 32)
  | br113
  | br108
  | br106
  | rep45
  | rep42
  | rep107
  | rep29

def Thread_Condition_FutexImpl_wait.again107 : Thread_Condition_FutexImpl_waitExit → Bool
  | .rep107 => true
  | _ => false

def Thread_Condition_FutexImpl_wait.again45 : Thread_Condition_FutexImpl_waitExit → Bool
  | .rep45 => true
  | _ => false

def Thread_Condition_FutexImpl_wait.again42 : Thread_Condition_FutexImpl_waitExit → Bool
  | .rep42 => true
  | _ => false

def Thread_Condition_FutexImpl_wait.again29 : Thread_Condition_FutexImpl_waitExit → Bool
  | .rep29 => true
  | _ => false

def Thread_Condition_FutexImpl_wait.loop107 [Zig.Os.HasEnv] (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit := do
  match ← ((do
    let i109 ← pure ((← get).state)
    let i110 ← pure (i109 &&& (4294901760 : BitVec 32))
    let i111 ← pure (i110 != (0 : BitVec 32))
    if i111 then (do
      match ← ((do
        let i114 ← pure ((← get).state)
        let i115 ← Zig.sub false i114 (1 : BitVec 32)
        let i116 ← Zig.sub false i115 (65536 : BitVec 32)
        match ← ((do
          let i118 ← pure p0
          let i119 ← pure ((← get).state)
          match ← ((do
            let i121 ← pure i118
            let i122 ← Zig.cmpxchgWeakC Zig.AtomicOrder.acquire Zig.AtomicOrder.relaxed 4 i121 i119 i116
            pure (.br120 i122)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
          | .br120 v120 => (do
            let i124 ← pure ((v120).isSome)
            if i124 then (do
              let i126 ← Zig.optPayload v120
              pure (.br117 i126))
            else (do
              let _i128 ← Zig.callC (Thread_Mutex_lock p1)
              pure (.ret (.ok () : Except Zig.ErrName (Unit)))))
          | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
        | .br117 v117 => (do
          modify (fun s => { s with state := v117 })
          pure .br113)
        | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
      | .br113 => (do
        pure .br108)
      | e => pure e)
    else (do
      pure .br106)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
  | .br108 => (do
    pure .rep107)
  | e => pure e

def Thread_Condition_FutexImpl_wait.loop45 [Zig.Os.HasEnv] (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit := do
  match ← ((do
    let i47 ← pure ((← get).state)
    let i48 ← pure (i47 &&& (4294901760 : BitVec 32))
    let i49 ← pure (i48 != (0 : BitVec 32))
    if i49 then (do
      match ← ((do
        let i52 ← pure ((← get).state)
        let i53 ← Zig.sub false i52 (1 : BitVec 32)
        let i54 ← Zig.sub false i53 (65536 : BitVec 32)
        match ← ((do
          let i56 ← pure p0
          let i57 ← pure ((← get).state)
          match ← ((do
            let i59 ← pure i56
            let i60 ← Zig.cmpxchgWeakC Zig.AtomicOrder.acquire Zig.AtomicOrder.relaxed 4 i59 i57 i54
            pure (.br58 i60)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
          | .br58 v58 => (do
            let i62 ← pure ((v58).isSome)
            if i62 then (do
              let i64 ← Zig.optPayload v58
              pure (.br55 i64))
            else (do
              let _i66 ← Zig.callC (Thread_Mutex_lock p1)
              pure (.ret (.ok () : Except Zig.ErrName (Unit)))))
          | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
        | .br55 v55 => (do
          modify (fun s => { s with state := v55 })
          pure .br51)
        | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
      | .br51 => (do
        pure .br46)
      | e => pure e)
    else (do
      pure .br44)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
  | .br46 => (do
    pure .rep45)
  | e => pure e

def Thread_Condition_FutexImpl_wait.loop42 [Zig.Os.HasEnv] (p0 : Zig.Ptr) (p1 : Zig.Ptr) (i38 : Zig.ErrName) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit := do
  match ← ((do
    match ← ((do
      Zig.loop (Thread_Condition_FutexImpl_wait.loop45 p0 p1) Thread_Condition_FutexImpl_wait.again45) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
    | .br44 => (do
      let i73 ← pure ((← get).state)
      let i74 ← Zig.sub false i73 (1 : BitVec 32)
      match ← ((do
        let i76 ← pure p0
        let i77 ← pure ((← get).state)
        match ← ((do
          let i79 ← pure i76
          let i80 ← Zig.cmpxchgWeakC Zig.AtomicOrder.relaxed Zig.AtomicOrder.relaxed 4 i79 i77 i74
          pure (.br78 i80)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
        | .br78 v78 => (do
          let i82 ← pure ((v78).isSome)
          if i82 then (do
            let i84 ← Zig.optPayload v78
            pure (.br75 i84))
          else (do
            let _i86 ← Zig.callC (Thread_Mutex_lock p1)
            let i87 ← pure ((.error i38) : Except Zig.ErrName (Unit))
            pure (.ret i87)))
        | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
      | .br75 v75 => (do
        modify (fun s => { s with state := v75 })
        pure .br43)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
  | .br43 => (do
    pure .rep42)
  | e => pure e

def Thread_Condition_FutexImpl_wait.loop29 [Zig.Os.HasEnv] (p0 : Zig.Ptr) (p1 : Zig.Ptr) (i26 : Zig.Ptr) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit := do
  let i30 ← Zig.callMC (Zig.ptrProject p0 (·.add 4))
  let i31 ← pure (i30)
  let i32 ← pure ((← get).epoch)
  let i33 ← Zig.callC (Thread_Futex_Deadline_wait i26 i31 i32)
  let i34 ← pure (Zig.isNonErr i33)
  match ← ((do
    if i34 then (do
      pure .br35)
    else (do
      let i38 ← Zig.callRC (Zig.unwrapErr i33)
      if i38 == "Timeout" then (do
        Zig.loop (Thread_Condition_FutexImpl_wait.loop42 p0 p1 i38) Thread_Condition_FutexImpl_wait.again42)
      else (do
        throw .panic))) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
  | .br35 => (do
    let i92 ← Zig.callMC (Zig.ptrProject p0 (·.add 4))
    let i93 ← pure (i92)
    match ← ((do
      let i95 ← pure i93
      let i96 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.acquire 4 i95
      pure (.br94 i96)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
    | .br94 v94 => (do
      modify (fun s => { s with epoch := v94 })
      let i99 ← pure p0
      let i100 ← pure (i99)
      match ← ((do
        let i102 ← pure i100
        let i103 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.relaxed 4 i102
        pure (.br101 i103)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
      | .br101 v101 => (do
        modify (fun s => { s with state := v101 })
        match ← ((do
          Zig.loop (Thread_Condition_FutexImpl_wait.loop107 p0 p1) Thread_Condition_FutexImpl_wait.again107) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
        | .br106 => (do
          pure .rep29)
        | e => pure e)
      | e => pure e)
    | e => pure e)
  | e => pure e

def Thread_Condition_FutexImpl_wait [Zig.Os.HasEnv] (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : Option (BitVec 64)) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let s26 ← Zig.allocStack 48 8
  let e ← ((do
    let i4 ← Zig.callMC (Zig.ptrProject p0 (·.add 4))
    let i5 ← pure (i4)
    match ← ((do
      let i7 ← pure i5
      let i8 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.acquire 4 i7
      pure (.br6 i8)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
    | .br6 v6 => (do
      modify (fun s => { s with epoch := v6 })
      let i12 ← pure p0
      match ← ((do
        let i14 ← pure i12
        let i15 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.relaxed 4 i14 (1 : BitVec 32)
        pure (.br13 i15)) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit) with
      | .br13 v13 => (do
        modify (fun s => { s with state := v13 })
        let i18 ← pure ((← get).state)
        let i19 ← pure (i18 &&& (65535 : BitVec 32))
        let i20 ← pure (i19 != (65535 : BitVec 32))
        let _i21 ← Zig.callRC (debug_assert i20)
        let i22 ← pure ((← get).state)
        let i23 ← Zig.add false i22 (1 : BitVec 32)
        modify (fun s => { s with state := i23 })
        let _i25 ← Zig.callC (Thread_Mutex_unlock p1)
        let i26 ← pure (← get).futex_deadline
        let i27 ← Zig.callC (Thread_Futex_Deadline_init p2)
        Zig.storeBytes i26 8 i27
        Zig.loop (Thread_Condition_FutexImpl_wait.loop29 p0 p1 i26) Thread_Condition_FutexImpl_wait.again29)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_waitLocals Thread_Condition_FutexImpl_waitExit).run' { (default : Thread_Condition_FutexImpl_waitLocals) with futex_deadline := s26 }
  Zig.free s26
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals where
  state : BitVec 32
  deriving Inhabited

inductive Thread_Condition_FutexImpl_wake__anon_b3c587c57789Exit where
  | ret
  | br4 (v : BitVec 32)
  | br18
  | br28 (v : Option (BitVec 32))
  | br25 (v : BitVec 32)
  | br37 (v : BitVec 32)
  | br10
  | rep9

def Thread_Condition_FutexImpl_wake__anon_b3c587c57789.again9 : Thread_Condition_FutexImpl_wake__anon_b3c587c57789Exit → Bool
  | .rep9 => true
  | _ => false

def Thread_Condition_FutexImpl_wake__anon_b3c587c57789.loop9 (p0 : Zig.Ptr) : Zig.CM Tgt Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals Thread_Condition_FutexImpl_wake__anon_b3c587c57789Exit := do
  match ← ((do
    let i11 ← pure ((← get).state)
    let i12 ← pure (i11 &&& (65535 : BitVec 32))
    let i13 ← Zig.divTrunc false i12 (1 : BitVec 32)
    let i14 ← pure ((← get).state)
    let i15 ← pure (i14 &&& (4294901760 : BitVec 32))
    let i16 ← Zig.divTrunc false i15 (65536 : BitVec 32)
    let i17 ← Zig.sub false i13 i16
    match ← ((do
      let i19 ← pure (i17 == (0 : BitVec 32))
      if i19 then (do
        pure .ret)
      else (do
        pure .br18)) : Zig.CM Tgt Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals Thread_Condition_FutexImpl_wake__anon_b3c587c57789Exit) with
    | .br18 => (do
      let i23 ← pure ((← get).state)
      let i24 ← Zig.add false i23 (65536 : BitVec 32)
      match ← ((do
        let i26 ← pure p0
        let i27 ← pure ((← get).state)
        match ← ((do
          let i29 ← pure i26
          let i30 ← Zig.cmpxchgWeakC Zig.AtomicOrder.release Zig.AtomicOrder.relaxed 4 i29 i27 i24
          pure (.br28 i30)) : Zig.CM Tgt Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals Thread_Condition_FutexImpl_wake__anon_b3c587c57789Exit) with
        | .br28 v28 => (do
          let i32 ← pure ((v28).isSome)
          if i32 then (do
            let i34 ← Zig.optPayload v28
            pure (.br25 i34))
          else (do
            let i36 ← Zig.callMC (Zig.ptrProject p0 (·.add 4))
            match ← ((do
              let i38 ← pure i36
              let i39 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.release 4 i38 (1 : BitVec 32)
              pure (.br37 i39)) : Zig.CM Tgt Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals Thread_Condition_FutexImpl_wake__anon_b3c587c57789Exit) with
            | .br37 _v37 => (do
              let i41 ← Zig.callMC (Zig.ptrProject p0 (·.add 4))
              let i42 ← pure (i41)
              let _i43 ← Zig.threadFutexWakeC i42 (1 : BitVec 32)
              pure .ret)
            | e => pure e))
        | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals Thread_Condition_FutexImpl_wake__anon_b3c587c57789Exit) with
      | .br25 v25 => (do
        modify (fun s => { s with state := v25 })
        pure .br10)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals Thread_Condition_FutexImpl_wake__anon_b3c587c57789Exit) with
  | .br10 => (do
    pure .rep9)
  | e => pure e

def Thread_Condition_FutexImpl_wake__anon_b3c587c57789 (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← pure (i2)
    match ← ((do
      let i5 ← pure i3
      let i6 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.relaxed 4 i5
      pure (.br4 i6)) : Zig.CM Tgt Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals Thread_Condition_FutexImpl_wake__anon_b3c587c57789Exit) with
    | .br4 v4 => (do
      modify (fun s => { s with state := v4 })
      Zig.loop (Thread_Condition_FutexImpl_wake__anon_b3c587c57789.loop9 p0) Thread_Condition_FutexImpl_wake__anon_b3c587c57789.again9)
    | e => pure e) : Zig.CM Tgt Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals Thread_Condition_FutexImpl_wake__anon_b3c587c57789Exit).run' (default : Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Thread_Condition_signalLocals where
  deriving Inhabited

inductive Thread_Condition_signalExit where
  | ret

def Thread_Condition_signal (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let _i2 ← Zig.callC (Thread_Condition_FutexImpl_wake__anon_b3c587c57789 i1)
    pure .ret) : Zig.CM Tgt Thread_Condition_signalLocals Thread_Condition_signalExit).run' (default : Thread_Condition_signalLocals)
  match e with
  | .ret => pure ()

structure Thread_Condition_waitLocals where
  deriving Inhabited

inductive Thread_Condition_waitExit where
  | ret
  | br5

def Thread_Condition_wait [Zig.Os.HasEnv] (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.callC (Thread_Condition_FutexImpl_wait i2 p1 none)
    let i4 ← pure (Zig.isNonErr i3)
    match ← ((do
      if i4 then (do
        pure .br5)
      else (do
        let i8 ← Zig.callRC (Zig.unwrapErr i3)
        if i8 == "Timeout" then (do
          let _i12 ← pure (i8)
          throw .panic)
        else (do
          throw .panic))) : Zig.CM Tgt Thread_Condition_waitLocals Thread_Condition_waitExit) with
    | .br5 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt Thread_Condition_waitLocals Thread_Condition_waitExit).run' (default : Thread_Condition_waitLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Thread_ResetEvent_FutexImpl_isSetLocals where
  deriving Inhabited

inductive Thread_ResetEvent_FutexImpl_isSetExit where
  | ret (v : Bool)
  | br2 (v : BitVec 32)

def Thread_ResetEvent_FutexImpl_isSet (p0 : Zig.Ptr) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    let i1 ← pure p0
    match ← ((do
      let i3 ← pure i1
      let i4 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.acquire 4 i3
      pure (.br2 i4)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_isSetLocals Thread_ResetEvent_FutexImpl_isSetExit) with
    | .br2 v2 => (do
      let i6 ← pure (v2 == (2 : BitVec 32))
      pure (.ret i6))
    | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_isSetLocals Thread_ResetEvent_FutexImpl_isSetExit).run' (default : Thread_ResetEvent_FutexImpl_isSetLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Thread_ResetEvent_FutexImpl_setLocals where
  deriving Inhabited

inductive Thread_ResetEvent_FutexImpl_setExit where
  | ret
  | br4 (v : BitVec 32)
  | br1
  | br14 (v : BitVec 32)
  | br12

def Thread_ResetEvent_FutexImpl_set (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure p0
      let i3 ← pure (i2)
      match ← ((do
        let i5 ← pure i3
        let i6 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.relaxed 4 i5
        pure (.br4 i6)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_setLocals Thread_ResetEvent_FutexImpl_setExit) with
      | .br4 v4 => (do
        let i8 ← pure (v4 == (2 : BitVec 32))
        if i8 then (do
          pure .ret)
        else (do
          pure .br1))
      | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_setLocals Thread_ResetEvent_FutexImpl_setExit) with
    | .br1 => (do
      match ← ((do
        let i13 ← pure p0
        match ← ((do
          let i15 ← pure i13
          let i16 ← Zig.atomicRmwC Zig.RmwOp.xchg false Zig.AtomicOrder.release 4 i15 (2 : BitVec 32)
          pure (.br14 i16)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_setLocals Thread_ResetEvent_FutexImpl_setExit) with
        | .br14 v14 => (do
          let i18 ← pure (v14 == (1 : BitVec 32))
          if i18 then (do
            let i20 ← pure p0
            let i21 ← pure (i20)
            let _i22 ← Zig.threadFutexWakeC i21 (4294967295 : BitVec 32)
            pure .br12)
          else (do
            pure .br12))
        | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_setLocals Thread_ResetEvent_FutexImpl_setExit) with
      | .br12 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_setLocals Thread_ResetEvent_FutexImpl_setExit).run' (default : Thread_ResetEvent_FutexImpl_setLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Thread_ResetEvent_FutexImpl_waitUntilSetLocals where
  state : BitVec 32
  futex_deadline : Zig.Ptr
  deriving Inhabited

inductive Thread_ResetEvent_FutexImpl_waitUntilSetExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br5 (v : BitVec 32)
  | br17 (v : Option (BitVec 32))
  | br14 (v : BitVec 32)
  | br10
  | br44 (v : BitVec 32)
  | br36
  | br49
  | br38
  | br29
  | rep37

def Thread_ResetEvent_FutexImpl_waitUntilSet.again37 : Thread_ResetEvent_FutexImpl_waitUntilSetExit → Bool
  | .rep37 => true
  | _ => false

def Thread_ResetEvent_FutexImpl_waitUntilSet.loop37 [Zig.Os.HasEnv] (p0 : Zig.Ptr) (i33 : Zig.Ptr) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit := do
  match ← ((do
    let i39 ← pure p0
    let i40 ← pure (i39)
    let i41 ← Zig.callC (Thread_Futex_Deadline_wait i33 i40 (1 : BitVec 32))
    let i42 ← pure p0
    let i43 ← pure (i42)
    match ← ((do
      let i45 ← pure i43
      let i46 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.acquire 4 i45
      pure (.br44 i46)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
    | .br44 v44 => (do
      modify (fun s => { s with state := v44 })
      match ← ((do
        let i50 ← pure ((← get).state)
        let i51 ← pure (i50 != (1 : BitVec 32))
        if i51 then (do
          pure .br36)
        else (do
          pure .br49)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
      | .br49 => (do
        match i41 with
        | .error _ => (do
          let i56 ← Zig.callRC (Zig.unwrapErr i41)
          let i57 ← pure ((.error i56) : Except Zig.ErrName (Unit))
          pure (.ret i57))
        | .ok _v55 => (do
          pure .br38))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
  | .br38 => (do
    pure .rep37)
  | e => pure e

def Thread_ResetEvent_FutexImpl_waitUntilSet [Zig.Os.HasEnv] (p0 : Zig.Ptr) (p1 : Option (BitVec 64)) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let s33 ← Zig.allocStack 48 8
  let e ← ((do
    let i3 ← pure p0
    let i4 ← pure (i3)
    match ← ((do
      let i6 ← pure i4
      let i7 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.acquire 4 i6
      pure (.br5 i7)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
    | .br5 v5 => (do
      modify (fun s => { s with state := v5 })
      match ← ((do
        let i11 ← pure ((← get).state)
        let i12 ← pure (i11 == (0 : BitVec 32))
        if i12 then (do
          match ← ((do
            let i15 ← pure p0
            let i16 ← pure ((← get).state)
            match ← ((do
              let i18 ← pure i15
              let i19 ← Zig.cmpxchgC Zig.AtomicOrder.acquire Zig.AtomicOrder.acquire 4 i18 i16 (1 : BitVec 32)
              pure (.br17 i19)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
            | .br17 v17 => (do
              let i21 ← pure ((v17).isSome)
              if i21 then (do
                let i23 ← Zig.optPayload v17
                pure (.br14 i23))
              else (do
                pure (.br14 (1 : BitVec 32))))
            | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
          | .br14 v14 => (do
            modify (fun s => { s with state := v14 })
            pure .br10)
          | e => pure e)
        else (do
          pure .br10)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
      | .br10 => (do
        match ← ((do
          let i30 ← pure ((← get).state)
          let i31 ← pure (i30 == (1 : BitVec 32))
          if i31 then (do
            let i33 ← pure (← get).futex_deadline
            let i34 ← Zig.callC (Thread_Futex_Deadline_init p1)
            Zig.storeBytes i33 8 i34
            match ← ((do
              Zig.loop (Thread_ResetEvent_FutexImpl_waitUntilSet.loop37 p0 i33) Thread_ResetEvent_FutexImpl_waitUntilSet.again37) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
            | .br36 => (do
              pure .br29)
            | e => pure e)
          else (do
            pure .br29)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit) with
        | .br29 => (do
          let i63 ← pure ((← get).state)
          let i64 ← pure (i63 == (2 : BitVec 32))
          let _i65 ← Zig.callRC (debug_assert i64)
          pure (.ret (.ok () : Except Zig.ErrName (Unit))))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Thread_ResetEvent_FutexImpl_waitUntilSetExit).run' { (default : Thread_ResetEvent_FutexImpl_waitUntilSetLocals) with futex_deadline := s33 }
  Zig.free s33
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Thread_ResetEvent_FutexImpl_waitLocals where
  deriving Inhabited

inductive Thread_ResetEvent_FutexImpl_waitExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br2

def Thread_ResetEvent_FutexImpl_wait [Zig.Os.HasEnv] (p0 : Zig.Ptr) (p1 : Option (BitVec 64)) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (p0)
      let i4 ← Zig.callC (Thread_ResetEvent_FutexImpl_isSet i3)
      let i5 ← pure (!i4)
      if i5 then (do
        let i7 ← Zig.callC (Thread_ResetEvent_FutexImpl_waitUntilSet p0 p1)
        pure (.ret i7))
      else (do
        pure .br2)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitLocals Thread_ResetEvent_FutexImpl_waitExit) with
    | .br2 => (do
      pure (.ret (.ok () : Except Zig.ErrName (Unit))))
    | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_waitLocals Thread_ResetEvent_FutexImpl_waitExit).run' (default : Thread_ResetEvent_FutexImpl_waitLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Thread_ResetEvent_setLocals where
  deriving Inhabited

inductive Thread_ResetEvent_setExit where
  | ret

def Thread_ResetEvent_set (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let _i2 ← Zig.callC (Thread_ResetEvent_FutexImpl_set i1)
    pure .ret) : Zig.CM Tgt Thread_ResetEvent_setLocals Thread_ResetEvent_setExit).run' (default : Thread_ResetEvent_setLocals)
  match e with
  | .ret => pure ()

structure Thread_ResetEvent_waitLocals where
  deriving Inhabited

inductive Thread_ResetEvent_waitExit where
  | ret
  | br4

def Thread_ResetEvent_wait [Zig.Os.HasEnv] (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let i2 ← Zig.callC (Thread_ResetEvent_FutexImpl_wait i1 none)
    let i3 ← pure (Zig.isNonErr i2)
    match ← ((do
      if i3 then (do
        pure .br4)
      else (do
        let i7 ← Zig.callRC (Zig.unwrapErr i2)
        if i7 == "Timeout" then (do
          let _i11 ← pure (i7)
          throw .panic)
        else (do
          throw .panic))) : Zig.CM Tgt Thread_ResetEvent_waitLocals Thread_ResetEvent_waitExit) with
    | .br4 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt Thread_ResetEvent_waitLocals Thread_ResetEvent_waitExit).run' (default : Thread_ResetEvent_waitLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Thread_WaitGroup_finishLocals where
  deriving Inhabited

inductive Thread_WaitGroup_finishExit where
  | ret
  | br2 (v : BitVec 64)
  | br10

def Thread_WaitGroup_finish (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    match ← ((do
      let i3 ← pure i1
      let i4 ← Zig.atomicRmwC Zig.RmwOp.sub false Zig.AtomicOrder.acqRel 8 i3 (2 : BitVec 64)
      pure (.br2 i4)) : Zig.CM Tgt Thread_WaitGroup_finishLocals Thread_WaitGroup_finishExit) with
    | .br2 v2 => (do
      let i6 ← Zig.divTrunc false v2 (2 : BitVec 64)
      let i7 ← pure (i6)
      let i8 ← pure (Zig.gt false i7 (0 : BitVec 64))
      let _i9 ← Zig.callRC (debug_assert i8)
      match ← ((do
        let i11 ← pure (v2)
        let i12 ← pure (i11 == (3 : BitVec 64))
        if i12 then (do
          let i14 ← Zig.callMC (Zig.ptrProject p0 (·.add 8))
          let _i15 ← Zig.callC (Thread_ResetEvent_set i14)
          pure .br10)
        else (do
          pure .br10)) : Zig.CM Tgt Thread_WaitGroup_finishLocals Thread_WaitGroup_finishExit) with
      | .br10 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_WaitGroup_finishLocals Thread_WaitGroup_finishExit).run' (default : Thread_WaitGroup_finishLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Thread_WaitGroup_startManyLocals where
  deriving Inhabited

inductive Thread_WaitGroup_startManyExit where
  | ret
  | br4 (v : BitVec 64)

def Thread_WaitGroup_startMany (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.mul false (2 : BitVec 64) p1
    match ← ((do
      let i5 ← pure i2
      let i6 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.relaxed 8 i5 i3
      pure (.br4 i6)) : Zig.CM Tgt Thread_WaitGroup_startManyLocals Thread_WaitGroup_startManyExit) with
    | .br4 v4 => (do
      let i8 ← Zig.divTrunc false v4 (2 : BitVec 64)
      let i9 ← pure (i8)
      let i10 ← pure (Zig.lt false i9 (9223372036854775807 : BitVec 64))
      let _i11 ← Zig.callRC (debug_assert i10)
      pure .ret)
    | e => pure e) : Zig.CM Tgt Thread_WaitGroup_startManyLocals Thread_WaitGroup_startManyExit).run' (default : Thread_WaitGroup_startManyLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure Thread_WaitGroup_waitLocals where
  deriving Inhabited

inductive Thread_WaitGroup_waitExit where
  | ret
  | br2 (v : BitVec 64)
  | br10

def Thread_WaitGroup_wait [Zig.Os.HasEnv] (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    match ← ((do
      let i3 ← pure i1
      let i4 ← Zig.atomicRmwC Zig.RmwOp.add false Zig.AtomicOrder.acquire 8 i3 (1 : BitVec 64)
      pure (.br2 i4)) : Zig.CM Tgt Thread_WaitGroup_waitLocals Thread_WaitGroup_waitExit) with
    | .br2 v2 => (do
      let i6 ← pure (v2 &&& (1 : BitVec 64))
      let i7 ← pure (i6)
      let i8 ← pure (i7 == (0 : BitVec 64))
      let _i9 ← Zig.callRC (debug_assert i8)
      match ← ((do
        let i11 ← Zig.divTrunc false v2 (2 : BitVec 64)
        let i12 ← pure (i11)
        let i13 ← pure (Zig.gt false i12 (0 : BitVec 64))
        if i13 then (do
          let i15 ← Zig.callMC (Zig.ptrProject p0 (·.add 8))
          let _i16 ← Zig.callC (Thread_ResetEvent_wait i15)
          pure .br10)
        else (do
          pure .br10)) : Zig.CM Tgt Thread_WaitGroup_waitLocals Thread_WaitGroup_waitExit) with
      | .br10 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_WaitGroup_waitLocals Thread_WaitGroup_waitExit).run' (default : Thread_WaitGroup_waitLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure math_order__anon_88b814a058f5Locals where
  deriving Inhabited

inductive math_order__anon_88b814a058f5Exit where
  | ret (v : math_Order)

def math_order__anon_88b814a058f5 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (math_Order) := do
  let e ← ((do
    let i2 ← pure (p0 == p1)
    if i2 then (do
      pure (.ret math_Order.eq))
    else (do
      let i5 ← pure (Zig.lt false p0 p1)
      if i5 then (do
        pure (.ret math_Order.lt))
      else (do
        let i8 ← pure (Zig.gt false p0 p1)
        if i8 then (do
          pure (.ret math_Order.gt))
        else (do
          throw .unreachable)))) : Zig.M math_order__anon_88b814a058f5Locals math_order__anon_88b814a058f5Exit).run' (default : math_order__anon_88b814a058f5Locals)
  match e with
  | .ret v => pure v

structure math_sub__anon_2645c921d0aaLocals where
  deriving Inhabited

inductive math_sub__anon_2645c921d0aaExit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br3

def math_sub__anon_2645c921d0aa (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← pure (Zig.subWithOverflow true p0 p1)
    match ← ((do
      let i4 ← pure ((i2).2)
      let i5 ← pure (i4 != (0 : BitVec 1))
      if i5 then (do
        pure (.ret (.error "Overflow" : Except Zig.ErrName (BitVec 64))))
      else (do
        pure .br3)) : Zig.M math_sub__anon_2645c921d0aaLocals math_sub__anon_2645c921d0aaExit) with
    | .br3 => (do
      let i9 ← pure ((i2).1)
      let i10 ← pure ((.ok i9) : Except Zig.ErrName (BitVec 64))
      pure (.ret i10))
    | e => pure e) : Zig.M math_sub__anon_2645c921d0aaLocals math_sub__anon_2645c921d0aaExit).run' (default : math_sub__anon_2645c921d0aaLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure math_sub__anon_b9091a243743Locals where
  deriving Inhabited

inductive math_sub__anon_b9091a243743Exit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br3

def math_sub__anon_b9091a243743 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← pure (Zig.subWithOverflow false p0 p1)
    match ← ((do
      let i4 ← pure ((i2).2)
      let i5 ← pure (i4 != (0 : BitVec 1))
      if i5 then (do
        pure (.ret (.error "Overflow" : Except Zig.ErrName (BitVec 64))))
      else (do
        pure .br3)) : Zig.M math_sub__anon_b9091a243743Locals math_sub__anon_b9091a243743Exit) with
    | .br3 => (do
      let i9 ← pure ((i2).1)
      let i10 ← pure ((.ok i9) : Except Zig.ErrName (BitVec 64))
      pure (.ret i10))
    | e => pure e) : Zig.M math_sub__anon_b9091a243743Locals math_sub__anon_b9091a243743Exit).run' (default : math_sub__anon_b9091a243743Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure producerLocals where
  deriving Inhabited

inductive producerExit where
  | ret

def producer (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let _i2 ← Zig.callC (Thread_Mutex_lock i1)
    let i3 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
    Zig.store (α := BitVec 32) 4 i3 (7 : BitVec 32)
    let i5 ← Zig.callMC (Zig.ptrProject p0 (·.add 20))
    Zig.store (α := Bool) 1 i5 true
    let i7 ← pure p0
    let _i8 ← Zig.callC (Thread_Mutex_unlock i7)
    let i9 ← Zig.callMC (Zig.ptrProject p0 (·.add 4))
    let _i10 ← Zig.callC (Thread_Condition_signal i9)
    let i11 ← Zig.callMC (Zig.ptrProject p0 (·.add 12))
    let _i12 ← Zig.callC (Thread_ResetEvent_set i11)
    pure .ret) : Zig.CM Tgt producerLocals producerExit).run' (default : producerLocals)
  match e with
  | .ret => pure ()

structure handoffLocals where
  b : Zig.Ptr
  deriving Inhabited

inductive handoffExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br13
  | br11
  | rep12

def handoff.again12 : handoffExit → Bool
  | .rep12 => true
  | _ => false

def handoff.loop12 [Zig.Os.HasEnv] (i0 : Zig.Ptr) : Zig.CM Tgt handoffLocals handoffExit := do
  match ← ((do
    let i14 ← Zig.callMC (Zig.ptrProject i0 (·.add 20))
    let i15 ← Zig.load (Bool) 1 i14
    let i16 ← pure (!i15)
    if i16 then (do
      let i18 ← Zig.callMC (Zig.ptrProject i0 (·.add 4))
      let i19 ← pure i0
      let _i20 ← Zig.callC (Thread_Condition_wait i18 i19)
      pure .br13)
    else (do
      pure .br11)) : Zig.CM Tgt handoffLocals handoffExit) with
  | .br13 => (do
    pure .rep12)
  | e => pure e

def handoff [Zig.Os.HasEnv]  : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s0 ← Zig.allocStack 24 4
  let e ← ((do
    let i0 ← pure (← get).b
    Zig.store (α := Box) 4 i0 ({ m := ({ impl := ({ state := ({ raw := (0 : BitVec 32) } : atomic_Value_u32) } : Thread_Mutex_FutexImpl) } : Thread_Mutex), c := ({ impl := ({ state := ({ raw := (0 : BitVec 32) } : atomic_Value_u32), epoch := ({ raw := (0 : BitVec 32) } : atomic_Value_u32) } : Thread_Condition_FutexImpl) } : Thread_Condition), ready := false, done := ({ impl := ({ state := ({ raw := (0 : BitVec 32) } : atomic_Value_u32) } : Thread_ResetEvent_FutexImpl) } : Thread_ResetEvent), v := (0 : BitVec 32) } : Box)
    let i2 ← pure (i0)
    let i3 ← Zig.spawnC (Tgt.producer i2)
    match i3 with
    | .error _ => (do
      let i5 ← Zig.callRC (Zig.unwrapErr i3)
      let i6 ← pure (i5)
      let i7 ← pure ((.error i6) : Except Zig.ErrName (BitVec 32))
      pure (.ret i7))
    | .ok v4 => (do
      let i9 ← pure i0
      let _i10 ← Zig.callC (Thread_Mutex_lock i9)
      match ← ((do
        Zig.loop (handoff.loop12 i0) handoff.again12) : Zig.CM Tgt handoffLocals handoffExit) with
      | .br11 => (do
        let i24 ← Zig.callMC (Zig.ptrProject i0 (·.add 16))
        let i25 ← Zig.load (BitVec 32) 4 i24
        let i26 ← pure i0
        let _i27 ← Zig.callC (Thread_Mutex_unlock i26)
        let i28 ← Zig.callMC (Zig.ptrProject i0 (·.add 12))
        let _i29 ← Zig.callC (Thread_ResetEvent_wait i28)
        let _i30 ← Zig.joinC v4
        let i31 ← pure ((.ok i25) : Except Zig.ErrName (BitVec 32))
        pure (.ret i31))
      | e => pure e)) : Zig.CM Tgt handoffLocals handoffExit).run' { (default : handoffLocals) with b := s0 }
  Zig.free s0
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure workLocals where
  local1 : BitVec 64
  deriving Inhabited

inductive workExit where
  | ret
  | br6
  | br3
  | rep4

def work.again4 : workExit → Bool
  | .rep4 => true
  | _ => false

def work.loop4 (p0 : Zig.Ptr) : Zig.CM Tgt workLocals workExit := do
  let i5 ← pure ((← get).local1)
  match ← ((do
    let i7 ← pure (i5)
    let i8 ← pure (Zig.lt false i7 (2 : BitVec 64))
    if i8 then (do
      let i10 ← pure p0
      let _i11 ← Zig.callC (Thread_Mutex_lock i10)
      let i12 ← Zig.callMC (Zig.ptrProject p0 (·.add 4))
      let i13 ← Zig.load (BitVec 32) 4 i12
      let i14 ← Zig.add false i13 (1 : BitVec 32)
      Zig.store (α := BitVec 32) 4 i12 i14
      let i16 ← pure p0
      let _i17 ← Zig.callC (Thread_Mutex_unlock i16)
      pure .br6)
    else (do
      pure .br3)) : Zig.CM Tgt workLocals workExit) with
  | .br6 => (do
    let i20 ← Zig.add false i5 (1 : BitVec 64) (safe := false)
    modify (fun s => { s with local1 := i20 })
    pure .rep4)
  | e => pure e

def work (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    modify (fun s => { s with local1 := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (work.loop4 p0) work.again4) : Zig.CM Tgt workLocals workExit) with
    | .br3 => (do
      pure .ret)
    | e => pure e) : Zig.CM Tgt workLocals workExit).run' (default : workLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure mutexCounterLocals where
  c : Zig.Ptr
  deriving Inhabited

inductive mutexCounterExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def mutexCounter  : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s0 ← Zig.allocStack 8 4
  let e ← ((do
    let i0 ← pure (← get).c
    Zig.store (α := Counter) 4 i0 ({ m := ({ impl := ({ state := ({ raw := (0 : BitVec 32) } : atomic_Value_u32) } : Thread_Mutex_FutexImpl) } : Thread_Mutex), n := (0 : BitVec 32) } : Counter)
    let i2 ← pure (i0)
    let i3 ← Zig.spawnC (Tgt.work i2)
    match i3 with
    | .error _ => (do
      let i5 ← Zig.callRC (Zig.unwrapErr i3)
      let i6 ← pure (i5)
      let i7 ← pure ((.error i6) : Except Zig.ErrName (BitVec 32))
      pure (.ret i7))
    | .ok v4 => (do
      let _i9 ← Zig.callC (work i0)
      let _i10 ← Zig.joinC v4
      let i11 ← Zig.load (Counter) 4 i0
      let i12 ← pure ((i11).n)
      let i13 ← pure ((.ok i12) : Except Zig.ErrName (BitVec 32))
      pure (.ret i13))) : Zig.CM Tgt mutexCounterLocals mutexCounterExit).run' { (default : mutexCounterLocals) with c := s0 }
  Zig.free s0
  match e with
  | .ret v => pure v

structure taskLocals where
  deriving Inhabited

inductive taskExit where
  | ret

def task (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
    let _i2 ← Zig.callC (Thread_Mutex_lock i1)
    let i3 ← Zig.callMC (Zig.ptrProject p0 (·.add 20))
    let i4 ← Zig.load (BitVec 32) 4 i3
    let i5 ← Zig.add false i4 (1 : BitVec 32)
    Zig.store (α := BitVec 32) 4 i3 i5
    let i7 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
    let _i8 ← Zig.callC (Thread_Mutex_unlock i7)
    let i9 ← pure p0
    let _i10 ← Zig.callC (Thread_WaitGroup_finish i9)
    pure .ret) : Zig.CM Tgt taskLocals taskExit).run' (default : taskLocals)
  match e with
  | .ret => pure ()

structure waitGroupLocals where
  s : Zig.Ptr
  deriving Inhabited

inductive waitGroupExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def waitGroup [Zig.Os.HasEnv]  : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)) := do
  let s0 ← Zig.allocStack 24 8
  let e ← ((do
    let i0 ← pure (← get).s
    Zig.store (α := Tally) 8 i0 ({ wg := ({ state := ({ raw := (0 : BitVec 64) } : atomic_Value_usize), event := ({ impl := ({ state := ({ raw := (0 : BitVec 32) } : atomic_Value_u32) } : Thread_ResetEvent_FutexImpl) } : Thread_ResetEvent) } : Thread_WaitGroup), m := ({ impl := ({ state := ({ raw := (0 : BitVec 32) } : atomic_Value_u32) } : Thread_Mutex_FutexImpl) } : Thread_Mutex), n := (0 : BitVec 32) } : Tally)
    let i2 ← pure i0
    let _i3 ← Zig.callC (Thread_WaitGroup_startMany i2 (2 : BitVec 64))
    let i4 ← pure (i0)
    let i5 ← Zig.spawnC (Tgt.task i4)
    match i5 with
    | .error _ => (do
      let i7 ← Zig.callRC (Zig.unwrapErr i5)
      let i8 ← pure (i7)
      let i9 ← pure ((.error i8) : Except Zig.ErrName (BitVec 32))
      pure (.ret i9))
    | .ok v6 => (do
      let i11 ← pure (i0)
      let i12 ← Zig.spawnC (Tgt.task i11)
      match i12 with
      | .error _ => (do
        let i14 ← Zig.callRC (Zig.unwrapErr i12)
        let _i15 ← Zig.joinC v6
        let i16 ← pure (i14)
        let i17 ← pure ((.error i16) : Except Zig.ErrName (BitVec 32))
        pure (.ret i17))
      | .ok v13 => (do
        let i19 ← pure i0
        let _i20 ← Zig.callC (Thread_WaitGroup_wait i19)
        let i21 ← Zig.load (Tally) 8 i0
        let i22 ← pure ((i21).n)
        let _i23 ← Zig.joinC v6
        let _i24 ← Zig.joinC v13
        let i25 ← pure ((.ok i22) : Except Zig.ErrName (BitVec 32))
        pure (.ret i25)))) : Zig.CM Tgt waitGroupLocals waitGroupExit).run' { (default : waitGroupLocals) with s := s0 }
  Zig.free s0
  match e with
  | .ret v => pure v

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .producer a => discard (producer a)
  | .work a => discard (work a)
  | .task a => discard (task a)

end Threadsync