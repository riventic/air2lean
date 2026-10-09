-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.16-musl","zig_version":"0.15.2"}}
-- air2lean-models: {"assumptions":[],"bindings":[{"contract":"Zig.Env.Linux.closeContract","dependencies":[],"effects":"tracked","errors":["illegal"],"footprint":null,"implementation":"Zig.Env.Linux.close","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.16-musl","zig_version":"0.15.2"},"proof":"Zig.Env.Linux.closeEvidence","signature":{"params":[{"children":[],"layout":{"align":4,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":4,"volatile":false},"type":"Air2Lean.Ty.int true 32"}],"return":{"children":[],"layout":{"align":8,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":8,"volatile":false},"type":"Air2Lean.Ty.int false 64"}},"symbol":"os.linux.close","termination":"total","trust":"proved-obligation"},{"contract":"Zig.Env.Linux.readContract","dependencies":[],"effects":"tracked","errors":["illegal"],"footprint":{"reads":[],"writes":[1]},"implementation":"Zig.Env.Linux.read","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.16-musl","zig_version":"0.15.2"},"proof":"Zig.Env.Linux.readEvidence","signature":{"params":[{"children":[],"layout":{"align":4,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":4,"volatile":false},"type":"Air2Lean.Ty.int true 32"},{"children":[{"children":[],"layout":{"align":1,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":1,"volatile":false},"type":"Air2Lean.Ty.int false 8"}],"layout":{"align":8,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":1,"sentinel":false,"size":8,"volatile":false},"type":"Air2Lean.Ty.ptr \"many\" false 0"},{"children":[],"layout":{"align":8,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":8,"volatile":false},"type":"Air2Lean.Ty.int false 64"}],"return":{"children":[],"layout":{"align":8,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":8,"volatile":false},"type":"Air2Lean.Ty.int false 64"}},"symbol":"os.linux.read","termination":"total","trust":"proved-obligation"},{"contract":"Zig.Env.Linux.writeContract","dependencies":[],"effects":"tracked","errors":["illegal","unspecified"],"footprint":{"reads":[1],"writes":[]},"implementation":"Zig.Env.Linux.write","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.16-musl","zig_version":"0.15.2"},"proof":"Zig.Env.Linux.writeEvidence","signature":{"params":[{"children":[],"layout":{"align":4,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":4,"volatile":false},"type":"Air2Lean.Ty.int true 32"},{"children":[{"children":[],"layout":{"align":1,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":1,"volatile":false},"type":"Air2Lean.Ty.int false 8"}],"layout":{"align":8,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":1,"sentinel":false,"size":8,"volatile":false},"type":"Air2Lean.Ty.ptr \"many\" true 0"},{"children":[],"layout":{"align":8,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":8,"volatile":false},"type":"Air2Lean.Ty.int false 64"}],"return":{"children":[],"layout":{"align":8,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":8,"volatile":false},"type":"Air2Lean.Ty.int false 64"}},"symbol":"os.linux.write","termination":"total","trust":"proved-obligation"}],"qualification":"selected-sequential-direct-MemM-models","schema":1}
import ZigLean

import ZigLean.Env.Linux

import ZigLean.Env.Linux

import ZigLean.Env.Linux


namespace EnvStd15

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

structure fs_File where
  handle : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc fs_File where
  size := 4
  align := 4
  encode v := Zig.Enc.fields 4 [(0, Zig.Enc.encode v.handle)]
  decode bs := do pure { handle := ← Zig.Enc.decodeAt bs 0 }

def air2lean_model_0_contract : Zig.External.Contract ((BitVec 32)) (BitVec 64) := _root_.Zig.Env.Linux.closeContract

def air2lean_model_0 (p0 : BitVec 32) : Zig.MemM (BitVec 64) := _root_.Zig.Env.Linux.close p0

theorem air2lean_model_0_evidence : air2lean_model_0_contract.Holds .total [Zig.Error.illegal] .tracked _root_.Zig.Env.Linux.close := _root_.Zig.Env.Linux.closeEvidence

def air2lean_model_1_contract : Zig.External.Contract ((BitVec 32) × (Zig.Ptr) × (BitVec 64)) (BitVec 64) := _root_.Zig.Env.Linux.readContract

def air2lean_model_1 (p0 : BitVec 32) (p1 : Zig.Ptr) (p2 : BitVec 64) : Zig.MemM (BitVec 64) := _root_.Zig.Env.Linux.read (p0, p1, p2)

def air2lean_model_1_footprint : Zig.External.Footprint ((BitVec 32) × (Zig.Ptr) × (BitVec 64)) where
  reads := fun _ => []
  writes := fun args => [Zig.External.Region.block args.2.1]

theorem air2lean_model_1_evidence : air2lean_model_1_contract.Holds .total [Zig.Error.illegal] .tracked _root_.Zig.Env.Linux.read ∧ air2lean_model_1_contract.Respects air2lean_model_1_footprint := _root_.Zig.Env.Linux.readEvidence

def air2lean_model_2_contract : Zig.External.Contract ((BitVec 32) × (Zig.Ptr) × (BitVec 64)) (BitVec 64) := _root_.Zig.Env.Linux.writeContract

def air2lean_model_2 (p0 : BitVec 32) (p1 : Zig.Ptr) (p2 : BitVec 64) : Zig.MemM (BitVec 64) := _root_.Zig.Env.Linux.write (p0, p1, p2)

def air2lean_model_2_footprint : Zig.External.Footprint ((BitVec 32) × (Zig.Ptr) × (BitVec 64)) where
  reads := fun args => [Zig.External.Region.block args.2.1]
  writes := fun _ => []

theorem air2lean_model_2_evidence : air2lean_model_2_contract.Holds .total [Zig.Error.illegal, Zig.Error.unspecified] .tracked _root_.Zig.Env.Linux.write ∧ air2lean_model_2_contract.Respects air2lean_model_2_footprint := _root_.Zig.Env.Linux.writeEvidence

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure posix_errno__anon_1Locals where
  deriving Inhabited

inductive posix_errno__anon_1Exit where
  | ret (v : os_linux_E__enum_1)
  | br5 (v : Bool)
  | br2 (v : BitVec 64)

def posix_errno__anon_1 (p0 : BitVec 64) : Zig.Result (os_linux_E__enum_1) := do
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
          pure (.br5 false))) : Zig.M posix_errno__anon_1Locals posix_errno__anon_1Exit) with
      | .br5 v5 => (do
        if v5 then (do
          let i12 ← Zig.sub true (0 : BitVec 64) i1
          pure (.br2 i12))
        else (do
          pure (.br2 (0 : BitVec 64))))
      | e => pure e) : Zig.M posix_errno__anon_1Locals posix_errno__anon_1Exit) with
    | .br2 v2 => (do
      let i15 ← Zig.enumOf (os_linux_E__enum_1.ofInt? (Zig.val true v2))
      pure (.ret i15))
    | e => pure e) : Zig.M posix_errno__anon_1Locals posix_errno__anon_1Exit).run' (default : posix_errno__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure posix_closeLocals where
  deriving Inhabited

inductive posix_closeExit where
  | ret

def posix_close (p0 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    let i1 ← Zig.callM (air2lean_model_0 p0)
    let i2 ← Zig.callR (posix_errno__anon_1 i1)
    if i2 == os_linux_E__enum_1.BADF then (do
      throw .unreachable)
    else (do
      if i2 == os_linux_E__enum_1.INTR then (do
        pure .ret)
      else (do
        pure .ret))) : Zig.MM posix_closeLocals posix_closeExit).run' (default : posix_closeLocals)
  match e with
  | .ret => pure ()

structure fs_File_closeLocals where
  deriving Inhabited

inductive fs_File_closeExit where
  | ret

def fs_File_close (p0 : fs_File) : Zig.MemM (Unit) := do
  let e ← ((do
    let i1 ← pure ((p0).handle)
    let _i2 ← Zig.callM (posix_close i1)
    pure .ret) : Zig.MM fs_File_closeLocals fs_File_closeExit).run' (default : fs_File_closeLocals)
  match e with
  | .ret => pure ()

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
  deriving Inhabited

inductive posix_readExit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br2
  | br10
  | rep9

def posix_read.again9 : posix_readExit → Bool
  | .rep9 => true
  | _ => false

def posix_read.loop9 (p0 : BitVec 32) (p1 : Zig.Slice) : Zig.MM posix_readLocals posix_readExit := do
  match ← ((do
    let i11 ← pure p1.ptr
    let i12 ← pure p1.len
    let i13 ← pure (i12)
    let i14 ← pure (Zig.min false (2147479552 : BitVec 64) i13)
    let i15 ← Zig.intCast false false 31 i14
    let i16 ← Zig.intCast false false 64 i15
    let i17 ← Zig.callM (air2lean_model_1 p0 i11 i16)
    let i18 ← Zig.callR (posix_errno__anon_1 i17)
    if i18 == os_linux_E__enum_1.SUCCESS then (do
      let i24 ← Zig.intCast false false 64 i17
      let i25 ← pure ((.ok i24) : Except Zig.ErrName (BitVec 64))
      pure (.ret i25))
    else (do
      if i18 == os_linux_E__enum_1.INTR then (do
        pure .br10)
      else (do
        if i18 == os_linux_E__enum_1.INVAL then (do
          throw .unreachable)
        else (do
          if i18 == os_linux_E__enum_1.FAULT then (do
            throw .unreachable)
          else (do
            if i18 == os_linux_E__enum_1.SRCH then (do
              pure (.ret (.error "ProcessNotFound" : Except Zig.ErrName (BitVec 64))))
            else (do
              if i18 == os_linux_E__enum_1.AGAIN then (do
                pure (.ret (.error "WouldBlock" : Except Zig.ErrName (BitVec 64))))
              else (do
                if i18 == os_linux_E__enum_1.CANCELED then (do
                  pure (.ret (.error "Canceled" : Except Zig.ErrName (BitVec 64))))
                else (do
                  if i18 == os_linux_E__enum_1.BADF then (do
                    pure (.ret (.error "NotOpenForReading" : Except Zig.ErrName (BitVec 64))))
                  else (do
                    if i18 == os_linux_E__enum_1.IO then (do
                      pure (.ret (.error "InputOutput" : Except Zig.ErrName (BitVec 64))))
                    else (do
                      if i18 == os_linux_E__enum_1.ISDIR then (do
                        pure (.ret (.error "IsDir" : Except Zig.ErrName (BitVec 64))))
                      else (do
                        if i18 == os_linux_E__enum_1.NOBUFS then (do
                          pure (.ret (.error "SystemResources" : Except Zig.ErrName (BitVec 64))))
                        else (do
                          if i18 == os_linux_E__enum_1.NOMEM then (do
                            pure (.ret (.error "SystemResources" : Except Zig.ErrName (BitVec 64))))
                          else (do
                            if i18 == os_linux_E__enum_1.NOTCONN then (do
                              pure (.ret (.error "SocketNotConnected" : Except Zig.ErrName (BitVec 64))))
                            else (do
                              if i18 == os_linux_E__enum_1.CONNRESET then (do
                                pure (.ret (.error "ConnectionResetByPeer" : Except Zig.ErrName (BitVec 64))))
                              else (do
                                if i18 == os_linux_E__enum_1.TIMEDOUT then (do
                                  pure (.ret (.error "ConnectionTimedOut" : Except Zig.ErrName (BitVec 64))))
                                else (do
                                  let i20 ← Zig.callR (posix_unexpectedErrno i18)
                                  let i21 ← pure (i20)
                                  let i22 ← pure ((.error i21) : Except Zig.ErrName (BitVec 64))
                                  pure (.ret i22))))))))))))))))) : Zig.MM posix_readLocals posix_readExit) with
  | .br10 => (do
    pure .rep9)
  | e => pure e

def posix_read (p0 : BitVec 32) (p1 : Zig.Slice) : Zig.MemM (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure p1.len
      let i4 ← pure (i3)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (0 : BitVec 64) : Except Zig.ErrName (BitVec 64))))
      else (do
        pure .br2)) : Zig.MM posix_readLocals posix_readExit) with
    | .br2 => (do
      Zig.loop (posix_read.loop9 p0 p1) posix_read.again9)
    | e => pure e) : Zig.MM posix_readLocals posix_readExit).run' (default : posix_readLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure fs_File_readLocals where
  deriving Inhabited

inductive fs_File_readExit where
  | ret (v : Except Zig.ErrName (BitVec 64))

def fs_File_read (p0 : fs_File) (p1 : Zig.Slice) : Zig.MemM (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← pure ((p0).handle)
    let i3 ← Zig.callM (posix_read i2 p1)
    pure (.ret i3)) : Zig.MM fs_File_readLocals fs_File_readExit).run' (default : fs_File_readLocals)
  match e with
  | .ret v => pure v

structure fs_File_readAllLocals where
  index : BitVec 64
  deriving Inhabited

inductive fs_File_readAllExit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br19
  | br27
  | br4
  | br38
  | br13
  | br6
  | rep5

def fs_File_readAll.again5 : fs_File_readAllExit → Bool
  | .rep5 => true
  | _ => false

def fs_File_readAll.loop5 (p0 : fs_File) (p1 : Zig.Slice) : Zig.MM fs_File_readAllLocals fs_File_readAllExit := do
  match ← ((do
    let i7 ← pure ((← get).index)
    let i8 ← pure p1.len
    let i9 ← pure (i7)
    let i10 ← pure (i8)
    let i11 ← pure (i9 != i10)
    if i11 then (do
      match ← ((do
        let i14 ← pure ((← get).index)
        let i15 ← pure p1.ptr
        let i16 ← pure (i15.elem 1 i14)
        let i17 ← pure p1.len
        let i18 ← pure (Zig.le false i14 i17)
        match ← ((do
          if i18 then (do
            pure .br19)
          else (do
            throw .outOfBounds)) : Zig.MM fs_File_readAllLocals fs_File_readAllExit) with
        | .br19 => (do
          let i24 ← Zig.sub false i17 i14
          let i25 ← pure p1.len
          let i26 ← pure (Zig.le false i17 i25)
          match ← ((do
            if i26 then (do
              pure .br27)
            else (do
              throw .outOfBounds)) : Zig.MM fs_File_readAllLocals fs_File_readAllExit) with
          | .br27 => (do
            let i32 ← Zig.callM (Zig.checkSliceEnd p1.len i14 i24 0 >>= fun _ => pure (⟨i16, i24⟩ : Zig.Slice))
            let i33 ← Zig.callM (fs_File_read p0 i32)
            match i33 with
            | .error _ => (do
              let i35 ← Zig.callR (Zig.unwrapErr i33)
              let i36 ← pure ((.error i35) : Except Zig.ErrName (BitVec 64))
              pure (.ret i36))
            | .ok v34 => (do
              match ← ((do
                let i39 ← pure (v34)
                let i40 ← pure (i39 == (0 : BitVec 64))
                if i40 then (do
                  pure .br4)
                else (do
                  pure .br38)) : Zig.MM fs_File_readAllLocals fs_File_readAllExit) with
              | .br38 => (do
                let i44 ← pure ((← get).index)
                let i45 ← Zig.add false i44 v34
                modify (fun s => { s with index := i45 })
                pure .br13)
              | e => pure e))
          | e => pure e)
        | e => pure e) : Zig.MM fs_File_readAllLocals fs_File_readAllExit) with
      | .br13 => (do
        pure .br6)
      | e => pure e)
    else (do
      pure .br4)) : Zig.MM fs_File_readAllLocals fs_File_readAllExit) with
  | .br6 => (do
    pure .rep5)
  | e => pure e

def fs_File_readAll (p0 : fs_File) (p1 : Zig.Slice) : Zig.MemM (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    modify (fun s => { s with index := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (fs_File_readAll.loop5 p0 p1) fs_File_readAll.again5) : Zig.MM fs_File_readAllLocals fs_File_readAllExit) with
    | .br4 => (do
      let i51 ← pure ((← get).index)
      let i52 ← pure ((.ok i51) : Except Zig.ErrName (BitVec 64))
      pure (.ret i52))
    | e => pure e) : Zig.MM fs_File_readAllLocals fs_File_readAllExit).run' (default : fs_File_readAllLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure posix_writeLocals where
  deriving Inhabited

inductive posix_writeExit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br2
  | br10
  | rep9

def posix_write.again9 : posix_writeExit → Bool
  | .rep9 => true
  | _ => false

def posix_write.loop9 (p0 : BitVec 32) (p1 : Zig.Slice) : Zig.MM posix_writeLocals posix_writeExit := do
  match ← ((do
    let i11 ← pure p1.ptr
    let i12 ← pure p1.len
    let i13 ← pure (i12)
    let i14 ← pure (Zig.min false (2147479552 : BitVec 64) i13)
    let i15 ← Zig.intCast false false 31 i14
    let i16 ← Zig.intCast false false 64 i15
    let i17 ← Zig.callM (air2lean_model_2 p0 i11 i16)
    let i18 ← Zig.callR (posix_errno__anon_1 i17)
    if i18 == os_linux_E__enum_1.SUCCESS then (do
      let i24 ← Zig.intCast false false 64 i17
      let i25 ← pure ((.ok i24) : Except Zig.ErrName (BitVec 64))
      pure (.ret i25))
    else (do
      if i18 == os_linux_E__enum_1.INTR then (do
        pure .br10)
      else (do
        if i18 == os_linux_E__enum_1.INVAL then (do
          pure (.ret (.error "InvalidArgument" : Except Zig.ErrName (BitVec 64))))
        else (do
          if i18 == os_linux_E__enum_1.FAULT then (do
            throw .unreachable)
          else (do
            if i18 == os_linux_E__enum_1.SRCH then (do
              pure (.ret (.error "ProcessNotFound" : Except Zig.ErrName (BitVec 64))))
            else (do
              if i18 == os_linux_E__enum_1.AGAIN then (do
                pure (.ret (.error "WouldBlock" : Except Zig.ErrName (BitVec 64))))
              else (do
                if i18 == os_linux_E__enum_1.BADF then (do
                  pure (.ret (.error "NotOpenForWriting" : Except Zig.ErrName (BitVec 64))))
                else (do
                  if i18 == os_linux_E__enum_1.DESTADDRREQ then (do
                    throw .unreachable)
                  else (do
                    if i18 == os_linux_E__enum_1.DQUOT then (do
                      pure (.ret (.error "DiskQuota" : Except Zig.ErrName (BitVec 64))))
                    else (do
                      if i18 == os_linux_E__enum_1.FBIG then (do
                        pure (.ret (.error "FileTooBig" : Except Zig.ErrName (BitVec 64))))
                      else (do
                        if i18 == os_linux_E__enum_1.IO then (do
                          pure (.ret (.error "InputOutput" : Except Zig.ErrName (BitVec 64))))
                        else (do
                          if i18 == os_linux_E__enum_1.NOSPC then (do
                            pure (.ret (.error "NoSpaceLeft" : Except Zig.ErrName (BitVec 64))))
                          else (do
                            if i18 == os_linux_E__enum_1.ACCES then (do
                              pure (.ret (.error "AccessDenied" : Except Zig.ErrName (BitVec 64))))
                            else (do
                              if i18 == os_linux_E__enum_1.PERM then (do
                                pure (.ret (.error "PermissionDenied" : Except Zig.ErrName (BitVec 64))))
                              else (do
                                if i18 == os_linux_E__enum_1.PIPE then (do
                                  pure (.ret (.error "BrokenPipe" : Except Zig.ErrName (BitVec 64))))
                                else (do
                                  if i18 == os_linux_E__enum_1.CONNRESET then (do
                                    pure (.ret (.error "ConnectionResetByPeer" : Except Zig.ErrName (BitVec 64))))
                                  else (do
                                    if i18 == os_linux_E__enum_1.BUSY then (do
                                      pure (.ret (.error "DeviceBusy" : Except Zig.ErrName (BitVec 64))))
                                    else (do
                                      if i18 == os_linux_E__enum_1.NXIO then (do
                                        pure (.ret (.error "NoDevice" : Except Zig.ErrName (BitVec 64))))
                                      else (do
                                        if i18 == os_linux_E__enum_1.MSGSIZE then (do
                                          pure (.ret (.error "MessageTooBig" : Except Zig.ErrName (BitVec 64))))
                                        else (do
                                          let i20 ← Zig.callR (posix_unexpectedErrno i18)
                                          let i21 ← pure (i20)
                                          let i22 ← pure ((.error i21) : Except Zig.ErrName (BitVec 64))
                                          pure (.ret i22))))))))))))))))))))) : Zig.MM posix_writeLocals posix_writeExit) with
  | .br10 => (do
    pure .rep9)
  | e => pure e

def posix_write (p0 : BitVec 32) (p1 : Zig.Slice) : Zig.MemM (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure p1.len
      let i4 ← pure (i3)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (0 : BitVec 64) : Except Zig.ErrName (BitVec 64))))
      else (do
        pure .br2)) : Zig.MM posix_writeLocals posix_writeExit) with
    | .br2 => (do
      Zig.loop (posix_write.loop9 p0 p1) posix_write.again9)
    | e => pure e) : Zig.MM posix_writeLocals posix_writeExit).run' (default : posix_writeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure fs_File_writeLocals where
  deriving Inhabited

inductive fs_File_writeExit where
  | ret (v : Except Zig.ErrName (BitVec 64))

def fs_File_write (p0 : fs_File) (p1 : Zig.Slice) : Zig.MemM (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← pure ((p0).handle)
    let i3 ← Zig.callM (posix_write i2 p1)
    pure (.ret i3)) : Zig.MM fs_File_writeLocals fs_File_writeExit).run' (default : fs_File_writeLocals)
  match e with
  | .ret v => pure v

structure fs_File_writeAllLocals where
  index : BitVec 64
  deriving Inhabited

inductive fs_File_writeAllExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br19
  | br27
  | br6
  | br4
  | rep5

def fs_File_writeAll.again5 : fs_File_writeAllExit → Bool
  | .rep5 => true
  | _ => false

def fs_File_writeAll.loop5 (p0 : fs_File) (p1 : Zig.Slice) : Zig.MM fs_File_writeAllLocals fs_File_writeAllExit := do
  match ← ((do
    let i7 ← pure ((← get).index)
    let i8 ← pure p1.len
    let i9 ← pure (i7)
    let i10 ← pure (i8)
    let i11 ← pure (Zig.lt false i9 i10)
    if i11 then (do
      let i13 ← pure ((← get).index)
      let i14 ← pure ((← get).index)
      let i15 ← pure p1.ptr
      let i16 ← pure (i15.elem 1 i14)
      let i17 ← pure p1.len
      let i18 ← pure (Zig.le false i14 i17)
      match ← ((do
        if i18 then (do
          pure .br19)
        else (do
          throw .outOfBounds)) : Zig.MM fs_File_writeAllLocals fs_File_writeAllExit) with
      | .br19 => (do
        let i24 ← Zig.sub false i17 i14
        let i25 ← pure p1.len
        let i26 ← pure (Zig.le false i17 i25)
        match ← ((do
          if i26 then (do
            pure .br27)
          else (do
            throw .outOfBounds)) : Zig.MM fs_File_writeAllLocals fs_File_writeAllExit) with
        | .br27 => (do
          let i32 ← Zig.callM (Zig.checkSliceEnd p1.len i14 i24 0 >>= fun _ => pure (⟨i16, i24⟩ : Zig.Slice))
          let i33 ← Zig.callM (fs_File_write p0 i32)
          match i33 with
          | .error _ => (do
            let i35 ← Zig.callR (Zig.unwrapErr i33)
            let i36 ← pure ((.error i35) : Except Zig.ErrName (Unit))
            pure (.ret i36))
          | .ok v34 => (do
            let i38 ← Zig.add false i13 v34
            modify (fun s => { s with index := i38 })
            pure .br6))
        | e => pure e)
      | e => pure e)
    else (do
      pure .br4)) : Zig.MM fs_File_writeAllLocals fs_File_writeAllExit) with
  | .br6 => (do
    pure .rep5)
  | e => pure e

def fs_File_writeAll (p0 : fs_File) (p1 : Zig.Slice) : Zig.MemM (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    modify (fun s => { s with index := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (fs_File_writeAll.loop5 p0 p1) fs_File_writeAll.again5) : Zig.MM fs_File_writeAllLocals fs_File_writeAllExit) with
    | .br4 => (do
      pure (.ret (.ok () : Except Zig.ErrName (Unit))))
    | e => pure e) : Zig.MM fs_File_writeAllLocals fs_File_writeAllExit).run' (default : fs_File_writeAllLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure readAllCloseLocals where
  deriving Inhabited

inductive readAllCloseExit where
  | ret (v : Except Zig.ErrName (BitVec 64))

def readAllClose (p0 : fs_File) (p1 : Zig.Slice) : Zig.MemM (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← Zig.callM (fs_File_readAll p0 p1)
    let _i3 ← Zig.callM (fs_File_close p0)
    pure (.ret i2)) : Zig.MM readAllCloseLocals readAllCloseExit).run' (default : readAllCloseLocals)
  match e with
  | .ret v => pure v

structure writeAllCloseLocals where
  deriving Inhabited

inductive writeAllCloseExit where
  | ret (v : Except Zig.ErrName (Unit))

def writeAllClose (p0 : fs_File) (p1 : Zig.Slice) : Zig.MemM (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    let i2 ← Zig.callM (fs_File_writeAll p0 p1)
    match i2 with
    | .error _ => (do
      let i4 ← Zig.callR (Zig.unwrapErr i2)
      let _i5 ← Zig.callM (fs_File_close p0)
      let i6 ← pure ((.error i4) : Except Zig.ErrName (Unit))
      pure (.ret i6))
    | .ok _v3 => (do
      let _i8 ← Zig.callM (fs_File_close p0)
      pure (.ret (.ok () : Except Zig.ErrName (Unit))))) : Zig.MM writeAllCloseLocals writeAllCloseExit).run' (default : writeAllCloseLocals)
  match e with
  | .ret v => pure v

end EnvStd15