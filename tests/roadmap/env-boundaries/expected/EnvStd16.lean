-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
-- air2lean-models: {"assumptions":[],"bindings":[{"contract":"Zig.Env.Linux.closeContract","dependencies":[],"effects":"tracked","errors":["illegal"],"footprint":null,"implementation":"Zig.Env.Linux.close","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"},"proof":"Zig.Env.Linux.closeEvidence","signature":{"params":[{"children":[],"layout":{"align":4,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":4,"volatile":false},"type":"Air2Lean.Ty.int true 32"}],"return":{"children":[],"layout":{"align":8,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":8,"volatile":false},"type":"Air2Lean.Ty.int false 64"}},"symbol":"os.linux.close","termination":"total","trust":"proved-obligation"},{"contract":"Zig.Env.Linux.readContract","dependencies":[],"effects":"tracked","errors":["illegal"],"footprint":{"reads":[],"writes":[1]},"implementation":"Zig.Env.Linux.read","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"},"proof":"Zig.Env.Linux.readEvidence","signature":{"params":[{"children":[],"layout":{"align":4,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":4,"volatile":false},"type":"Air2Lean.Ty.int true 32"},{"children":[{"children":[],"layout":{"align":1,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":1,"volatile":false},"type":"Air2Lean.Ty.int false 8"}],"layout":{"align":8,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":1,"sentinel":false,"size":8,"volatile":false},"type":"Air2Lean.Ty.ptr \"many\" false 0"},{"children":[],"layout":{"align":8,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":8,"volatile":false},"type":"Air2Lean.Ty.int false 64"}],"return":{"children":[],"layout":{"align":8,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":8,"volatile":false},"type":"Air2Lean.Ty.int false 64"}},"symbol":"os.linux.read","termination":"total","trust":"proved-obligation"}],"qualification":"selected-sequential-direct-MemM-models","schema":1}
import ZigLean

import ZigLean.Env.Linux

import ZigLean.Env.Linux


namespace EnvStd16

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

def air2lean_model_0_contract : Zig.External.Contract ((BitVec 32)) (BitVec 64) := _root_.Zig.Env.Linux.closeContract

def air2lean_model_0 (p0 : BitVec 32) : Zig.MemM (BitVec 64) := _root_.Zig.Env.Linux.close p0

theorem air2lean_model_0_evidence : air2lean_model_0_contract.Holds .total [Zig.Error.illegal] .tracked _root_.Zig.Env.Linux.close := _root_.Zig.Env.Linux.closeEvidence

def air2lean_model_1_contract : Zig.External.Contract ((BitVec 32) × (Zig.Ptr) × (BitVec 64)) (BitVec 64) := _root_.Zig.Env.Linux.readContract

def air2lean_model_1 (p0 : BitVec 32) (p1 : Zig.Ptr) (p2 : BitVec 64) : Zig.MemM (BitVec 64) := _root_.Zig.Env.Linux.read (p0, p1, p2)

def air2lean_model_1_footprint : Zig.External.Footprint ((BitVec 32) × (Zig.Ptr) × (BitVec 64)) where
  reads := fun _ => []
  writes := fun args => [Zig.External.Region.block args.2.1]

theorem air2lean_model_1_evidence : air2lean_model_1_contract.Holds .total [Zig.Error.illegal] .tracked _root_.Zig.Env.Linux.read ∧ air2lean_model_1_contract.Respects air2lean_model_1_footprint := _root_.Zig.Env.Linux.readEvidence

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

structure os_linux_errnoLocals where
  deriving Inhabited

inductive os_linux_errnoExit where
  | ret (v : os_linux_E__enum_1)
  | br5 (v : Bool)
  | br2 (v : BitVec 64)

def os_linux_errno (p0 : BitVec 64) : Zig.Result (os_linux_E__enum_1) := do
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
          pure (.br5 false))) : Zig.M os_linux_errnoLocals os_linux_errnoExit) with
      | .br5 v5 => (do
        if v5 then (do
          let i12 ← Zig.sub true (0 : BitVec 64) i1
          pure (.br2 i12))
        else (do
          pure (.br2 (0 : BitVec 64))))
      | e => pure e) : Zig.M os_linux_errnoLocals os_linux_errnoExit) with
    | .br2 v2 => (do
      let i15 ← Zig.enumOf (os_linux_E__enum_1.ofInt? (Zig.val true v2))
      pure (.ret i15))
    | e => pure e) : Zig.M os_linux_errnoLocals os_linux_errnoExit).run' (default : os_linux_errnoLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure Io_Threaded_recoverableOsBugDetectedLocals where
  deriving Inhabited

inductive Io_Threaded_recoverableOsBugDetectedExit where
  | ret

def Io_Threaded_recoverableOsBugDetected  : Zig.Result (Unit) := do
  let e ← ((do
    pure .ret) : Zig.M Io_Threaded_recoverableOsBugDetectedLocals Io_Threaded_recoverableOsBugDetectedExit).run' (default : Io_Threaded_recoverableOsBugDetectedLocals)
  match e with
  | .ret => pure ()

structure Io_Threaded_closeFdLocals where
  deriving Inhabited

inductive Io_Threaded_closeFdExit where
  | ret
  | br3

def Io_Threaded_closeFd (p0 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    let i1 ← Zig.callM (air2lean_model_0 p0)
    let i2 ← Zig.callR (os_linux_errno i1)
    match ← ((do
      if i2 == os_linux_E__enum_1.BADF then (do
        let _i7 ← Zig.callR (Io_Threaded_recoverableOsBugDetected )
        pure .br3)
      else (do
        if i2 == os_linux_E__enum_1.SUCCESS || i2 == os_linux_E__enum_1.INTR then (do
          pure .br3)
        else (do
          let _i5 ← Zig.callR (Io_Threaded_recoverableOsBugDetected )
          pure .br3))) : Zig.MM Io_Threaded_closeFdLocals Io_Threaded_closeFdExit) with
    | .br3 => (do
      pure .ret)
    | e => pure e) : Zig.MM Io_Threaded_closeFdLocals Io_Threaded_closeFdExit).run' (default : Io_Threaded_closeFdLocals)
  match e with
  | .ret => pure ()
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

structure posix_readLocals where
  local2 : Zig.Slice
  deriving Inhabited

inductive posix_readExit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br5
  | br14
  | rep13

def posix_read.again13 : posix_readExit → Bool
  | .rep13 => true
  | _ => false

def posix_read.loop13 (p0 : BitVec 32) : Zig.MM posix_readLocals posix_readExit := do
  match ← ((do
    let i16 ← pure (((← get).local2).ptr)
    let i18 ← pure (((← get).local2).len)
    let i19 ← pure (i18)
    let i20 ← pure (Zig.min false (2147479552 : BitVec 64) i19)
    let i21 ← Zig.intCast false false 31 i20
    let i22 ← Zig.intCast false false 64 i21
    let i23 ← Zig.callM (air2lean_model_1 p0 i16 i22)
    let i24 ← Zig.callR (os_linux_errno i23)
    if i24 == os_linux_E__enum_1.SUCCESS then (do
      let i30 ← Zig.intCast false false 64 i23
      let i31 ← pure ((.ok i30) : Except Zig.ErrName (BitVec 64))
      pure (.ret i31))
    else (do
      if i24 == os_linux_E__enum_1.INTR then (do
        pure .br14)
      else (do
        if i24 == os_linux_E__enum_1.INVAL then (do
          throw .unreachable)
        else (do
          if i24 == os_linux_E__enum_1.FAULT then (do
            throw .unreachable)
          else (do
            if i24 == os_linux_E__enum_1.AGAIN then (do
              pure (.ret (.error "WouldBlock" : Except Zig.ErrName (BitVec 64))))
            else (do
              if i24 == os_linux_E__enum_1.CANCELED then (do
                pure (.ret (.error "Canceled" : Except Zig.ErrName (BitVec 64))))
              else (do
                if i24 == os_linux_E__enum_1.BADF then (do
                  pure (.ret (.error "Unexpected" : Except Zig.ErrName (BitVec 64))))
                else (do
                  if i24 == os_linux_E__enum_1.IO then (do
                    pure (.ret (.error "InputOutput" : Except Zig.ErrName (BitVec 64))))
                  else (do
                    if i24 == os_linux_E__enum_1.ISDIR then (do
                      pure (.ret (.error "IsDir" : Except Zig.ErrName (BitVec 64))))
                    else (do
                      if i24 == os_linux_E__enum_1.NOBUFS then (do
                        pure (.ret (.error "SystemResources" : Except Zig.ErrName (BitVec 64))))
                      else (do
                        if i24 == os_linux_E__enum_1.NOMEM then (do
                          pure (.ret (.error "SystemResources" : Except Zig.ErrName (BitVec 64))))
                        else (do
                          if i24 == os_linux_E__enum_1.NOTCONN then (do
                            pure (.ret (.error "SocketUnconnected" : Except Zig.ErrName (BitVec 64))))
                          else (do
                            if i24 == os_linux_E__enum_1.CONNRESET then (do
                              pure (.ret (.error "ConnectionResetByPeer" : Except Zig.ErrName (BitVec 64))))
                            else (do
                              if i24 == os_linux_E__enum_1.TIMEDOUT then (do
                                pure (.ret (.error "Unexpected" : Except Zig.ErrName (BitVec 64))))
                              else (do
                                let i26 ← Zig.callR (posix_unexpectedErrno i24)
                                let i27 ← pure (i26)
                                let i28 ← pure ((.error i27) : Except Zig.ErrName (BitVec 64))
                                pure (.ret i28)))))))))))))))) : Zig.MM posix_readLocals posix_readExit) with
  | .br14 => (do
    pure .rep13)
  | e => pure e

def posix_read (p0 : BitVec 32) (p1 : Zig.Slice) : Zig.MemM (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    modify (fun s => { s with local2 := p1 })
    match ← ((do
      let i7 ← pure (((← get).local2).len)
      let i8 ← pure (i7)
      let i9 ← pure (i8 == (0 : BitVec 64))
      if i9 then (do
        pure (.ret (.ok (0 : BitVec 64) : Except Zig.ErrName (BitVec 64))))
      else (do
        pure .br5)) : Zig.MM posix_readLocals posix_readExit) with
    | .br5 => (do
      Zig.loop (posix_read.loop13 p0) posix_read.again13)
    | e => pure e) : Zig.MM posix_readLocals posix_readExit).run' (default : posix_readLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure readCloseLocals where
  deriving Inhabited

inductive readCloseExit where
  | ret (v : Except Zig.ErrName (BitVec 64))

def readClose (p0 : BitVec 32) (p1 : Zig.Slice) : Zig.MemM (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← Zig.callM (posix_read p0 p1)
    let _i3 ← Zig.callM (Io_Threaded_closeFd p0)
    pure (.ret i2)) : Zig.MM readCloseLocals readCloseExit).run' (default : readCloseLocals)
  match e with
  | .ret v => pure v

end EnvStd16