-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":8,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"}}
import ZigLean


namespace ErrorInts

/-- The compilation's error numbering (the exporter's `error-table.air2lean`): code `i + 1` is `errorTable[i]`. -/
def errorTable : Array Zig.ErrName := #["PermissionDenied", "SystemResources", "Unsupported", "Unexpected", "DiskQuota", "FileTooBig", "InputOutput", "NoSpaceLeft", "DeviceBusy", "AccessDenied", "BrokenPipe", "NotOpenForWriting", "LockViolation", "WouldBlock", "NoDevice", "FileBusy", "Canceled", "Unimplemented", "CorruptedData", "EndOfStream", "ReadFailed", "Unseekable", "UnsupportedOperation", "EnvironmentVariableMissing", "UnrecognizedFormat", "OutOfMemory", "ConcurrencyUnavailable", "IsDir", "ConnectionResetByPeer", "NotOpenForReading", "SocketUnconnected", "ProcessFdQuotaExceeded", "SystemFdQuotaExceeded", "MessageOversize", "NetworkDown", "PortUnreachable", "ConnectionTimedOut", "NetworkUnreachable", "HostUnreachable", "ConnectionRefused", "AddressFamilyUnsupported", "FastOpenAlreadyInProgress", "SocketNotBound", "Timeout", "PathAlreadyExists", "SymLinkLoop", "LinkQuotaExceeded", "FileNotFound", "NotDir", "ReadOnlyFileSystem", "NetworkNotFound", "NameTooLong", "BadPathName", "PipeBusy", "AntivirusInterference", "FileLocksUnsupported", "Streaming", "OperationUnsupported", "FileSystem", "UnrecognizedVolume", "DirNotEmpty", "CrossDevice", "HardwareFailure", "NotLink", "UnsupportedReparsePointType", "NotTerminalDevice", "NonResizable", "LockedMemoryLimitExceeded", "ProcessNotFound", "CurrentDirUnlinked", "PathExceedsLimit", "InvalidWtf8", "InvalidExe", "InvalidBatchScriptArg", "ResourceLimitReached", "InvalidUserId", "InvalidProcessGroupId", "InvalidName", "ProcessAlreadyExec", "ClockUnavailable", "EntropyUnavailable", "AddressInUse", "AddressUnavailable", "ProtocolUnsupportedBySystem", "ProtocolUnsupportedByAddressFamily", "SocketModeUnsupported", "OptionUnsupported", "SocketNotListening", "ConnectionAborted", "BlockedByFirewall", "ProtocolFailure", "ConnectionPending", "InterfaceNotFound", "UnknownHostName", "ResolvConfParseFailed", "InvalidDnsARecord", "InvalidDnsAAAARecord", "InvalidDnsCnameRecord", "NameServerFailure", "NoAddressReturned", "DetectingNetworkConfigurationFailed", "WriteFailed", "Overflow", "InvalidDebugInfo", "MissingDebugInfo", "UnsupportedDebugInfo", "StreamTooLong", "NoSymtab", "NoStrtab", "BadSymtab", "TruncatedElfFile", "InvalidCompressedSection", "InvalidElfMagic", "InvalidElfVersion", "InvalidElfClass", "InvalidElfEndian", "MemoryMappingNotSupported", "CrcMismatch", "MappingAlreadyExists", "BadGzipHeader", "BadZlibHeader", "WrongGzipChecksum", "WrongGzipSize", "WrongZlibChecksum", "InvalidCode", "InvalidMatch", "WrongStoredBlockNlen", "InvalidBlockType", "InvalidDynamicBlockHeader", "OversubscribedHuffmanTree", "IncompleteHuffmanTree", "MissingEndOfBlockCode", "InvalidCharacter", "UnsupportedAddrSize", "UnimplementedUserOpcode", "InvalidOpcode", "InvalidOperation", "InvalidOperand", "InvalidRegister", "UnsupportedRegister", "UnsupportedDwarfVersion", "UnsupportedAugmentation", "IncompatibleRegisterSize", "UnimplementedExpressionCall", "UnimplementedOpcode", "UnimplementedTypedComparison", "UnimplementedTypeConversion", "UnknownExpressionOpcode", "IncompleteExpressionContext", "InvalidCFAOpcode", "InvalidExpression", "InvalidFrameBase", "InvalidIntegralTypeSize", "InvalidSubExpression", "InvalidTypeLength", "TruncatedIntegralType", "DivisionByZero", "WindowTooSmall", "Closed", "ParseFailed", "UnresolvedScope", "InvalidEnd", "Incomplete", "NonCanonical", "InvalidDnsPacket", "InvalidHostName", "SectionOversize", "ThreadQuotaExceeded", "Alpha", "Beta", "Gamma", "SizeTooSmall", "LimitTooBig", "InvalidSyscallParameters"]

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: the name of error.PermissionDenied
  (Zig.Enc.encode (#v[80, 101, 114, 109, 105, 115, 115, 105, 111, 110, 68, 101, 110, 105, 101, 100, 0] : Vector (BitVec 8) 17), 1, .constGlobal),
  -- 1: the name of error.SystemResources
  (Zig.Enc.encode (#v[83, 121, 115, 116, 101, 109, 82, 101, 115, 111, 117, 114, 99, 101, 115, 0] : Vector (BitVec 8) 16), 1, .constGlobal),
  -- 2: the name of error.Unsupported
  (Zig.Enc.encode (#v[85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 3: the name of error.Unexpected
  (Zig.Enc.encode (#v[85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 0] : Vector (BitVec 8) 11), 1, .constGlobal),
  -- 4: the name of error.DiskQuota
  (Zig.Enc.encode (#v[68, 105, 115, 107, 81, 117, 111, 116, 97, 0] : Vector (BitVec 8) 10), 1, .constGlobal),
  -- 5: the name of error.FileTooBig
  (Zig.Enc.encode (#v[70, 105, 108, 101, 84, 111, 111, 66, 105, 103, 0] : Vector (BitVec 8) 11), 1, .constGlobal),
  -- 6: the name of error.InputOutput
  (Zig.Enc.encode (#v[73, 110, 112, 117, 116, 79, 117, 116, 112, 117, 116, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 7: the name of error.NoSpaceLeft
  (Zig.Enc.encode (#v[78, 111, 83, 112, 97, 99, 101, 76, 101, 102, 116, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 8: the name of error.DeviceBusy
  (Zig.Enc.encode (#v[68, 101, 118, 105, 99, 101, 66, 117, 115, 121, 0] : Vector (BitVec 8) 11), 1, .constGlobal),
  -- 9: the name of error.AccessDenied
  (Zig.Enc.encode (#v[65, 99, 99, 101, 115, 115, 68, 101, 110, 105, 101, 100, 0] : Vector (BitVec 8) 13), 1, .constGlobal),
  -- 10: the name of error.BrokenPipe
  (Zig.Enc.encode (#v[66, 114, 111, 107, 101, 110, 80, 105, 112, 101, 0] : Vector (BitVec 8) 11), 1, .constGlobal),
  -- 11: the name of error.NotOpenForWriting
  (Zig.Enc.encode (#v[78, 111, 116, 79, 112, 101, 110, 70, 111, 114, 87, 114, 105, 116, 105, 110, 103, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 12: the name of error.LockViolation
  (Zig.Enc.encode (#v[76, 111, 99, 107, 86, 105, 111, 108, 97, 116, 105, 111, 110, 0] : Vector (BitVec 8) 14), 1, .constGlobal),
  -- 13: the name of error.WouldBlock
  (Zig.Enc.encode (#v[87, 111, 117, 108, 100, 66, 108, 111, 99, 107, 0] : Vector (BitVec 8) 11), 1, .constGlobal),
  -- 14: the name of error.NoDevice
  (Zig.Enc.encode (#v[78, 111, 68, 101, 118, 105, 99, 101, 0] : Vector (BitVec 8) 9), 1, .constGlobal),
  -- 15: the name of error.FileBusy
  (Zig.Enc.encode (#v[70, 105, 108, 101, 66, 117, 115, 121, 0] : Vector (BitVec 8) 9), 1, .constGlobal),
  -- 16: the name of error.Canceled
  (Zig.Enc.encode (#v[67, 97, 110, 99, 101, 108, 101, 100, 0] : Vector (BitVec 8) 9), 1, .constGlobal),
  -- 17: the name of error.Unimplemented
  (Zig.Enc.encode (#v[85, 110, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 0] : Vector (BitVec 8) 14), 1, .constGlobal),
  -- 18: the name of error.CorruptedData
  (Zig.Enc.encode (#v[67, 111, 114, 114, 117, 112, 116, 101, 100, 68, 97, 116, 97, 0] : Vector (BitVec 8) 14), 1, .constGlobal),
  -- 19: the name of error.EndOfStream
  (Zig.Enc.encode (#v[69, 110, 100, 79, 102, 83, 116, 114, 101, 97, 109, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 20: the name of error.ReadFailed
  (Zig.Enc.encode (#v[82, 101, 97, 100, 70, 97, 105, 108, 101, 100, 0] : Vector (BitVec 8) 11), 1, .constGlobal),
  -- 21: the name of error.Unseekable
  (Zig.Enc.encode (#v[85, 110, 115, 101, 101, 107, 97, 98, 108, 101, 0] : Vector (BitVec 8) 11), 1, .constGlobal),
  -- 22: the name of error.UnsupportedOperation
  (Zig.Enc.encode (#v[85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 79, 112, 101, 114, 97, 116, 105, 111, 110, 0] : Vector (BitVec 8) 21), 1, .constGlobal),
  -- 23: the name of error.EnvironmentVariableMissing
  (Zig.Enc.encode (#v[69, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 86, 97, 114, 105, 97, 98, 108, 101, 77, 105, 115, 115, 105, 110, 103, 0] : Vector (BitVec 8) 27), 1, .constGlobal),
  -- 24: the name of error.UnrecognizedFormat
  (Zig.Enc.encode (#v[85, 110, 114, 101, 99, 111, 103, 110, 105, 122, 101, 100, 70, 111, 114, 109, 97, 116, 0] : Vector (BitVec 8) 19), 1, .constGlobal),
  -- 25: the name of error.OutOfMemory
  (Zig.Enc.encode (#v[79, 117, 116, 79, 102, 77, 101, 109, 111, 114, 121, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 26: the name of error.ConcurrencyUnavailable
  (Zig.Enc.encode (#v[67, 111, 110, 99, 117, 114, 114, 101, 110, 99, 121, 85, 110, 97, 118, 97, 105, 108, 97, 98, 108, 101, 0] : Vector (BitVec 8) 23), 1, .constGlobal),
  -- 27: the name of error.IsDir
  (Zig.Enc.encode (#v[73, 115, 68, 105, 114, 0] : Vector (BitVec 8) 6), 1, .constGlobal),
  -- 28: the name of error.ConnectionResetByPeer
  (Zig.Enc.encode (#v[67, 111, 110, 110, 101, 99, 116, 105, 111, 110, 82, 101, 115, 101, 116, 66, 121, 80, 101, 101, 114, 0] : Vector (BitVec 8) 22), 1, .constGlobal),
  -- 29: the name of error.NotOpenForReading
  (Zig.Enc.encode (#v[78, 111, 116, 79, 112, 101, 110, 70, 111, 114, 82, 101, 97, 100, 105, 110, 103, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 30: the name of error.SocketUnconnected
  (Zig.Enc.encode (#v[83, 111, 99, 107, 101, 116, 85, 110, 99, 111, 110, 110, 101, 99, 116, 101, 100, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 31: the name of error.ProcessFdQuotaExceeded
  (Zig.Enc.encode (#v[80, 114, 111, 99, 101, 115, 115, 70, 100, 81, 117, 111, 116, 97, 69, 120, 99, 101, 101, 100, 101, 100, 0] : Vector (BitVec 8) 23), 1, .constGlobal),
  -- 32: the name of error.SystemFdQuotaExceeded
  (Zig.Enc.encode (#v[83, 121, 115, 116, 101, 109, 70, 100, 81, 117, 111, 116, 97, 69, 120, 99, 101, 101, 100, 101, 100, 0] : Vector (BitVec 8) 22), 1, .constGlobal),
  -- 33: the name of error.MessageOversize
  (Zig.Enc.encode (#v[77, 101, 115, 115, 97, 103, 101, 79, 118, 101, 114, 115, 105, 122, 101, 0] : Vector (BitVec 8) 16), 1, .constGlobal),
  -- 34: the name of error.NetworkDown
  (Zig.Enc.encode (#v[78, 101, 116, 119, 111, 114, 107, 68, 111, 119, 110, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 35: the name of error.PortUnreachable
  (Zig.Enc.encode (#v[80, 111, 114, 116, 85, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 0] : Vector (BitVec 8) 16), 1, .constGlobal),
  -- 36: the name of error.ConnectionTimedOut
  (Zig.Enc.encode (#v[67, 111, 110, 110, 101, 99, 116, 105, 111, 110, 84, 105, 109, 101, 100, 79, 117, 116, 0] : Vector (BitVec 8) 19), 1, .constGlobal),
  -- 37: the name of error.NetworkUnreachable
  (Zig.Enc.encode (#v[78, 101, 116, 119, 111, 114, 107, 85, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 0] : Vector (BitVec 8) 19), 1, .constGlobal),
  -- 38: the name of error.HostUnreachable
  (Zig.Enc.encode (#v[72, 111, 115, 116, 85, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 0] : Vector (BitVec 8) 16), 1, .constGlobal),
  -- 39: the name of error.ConnectionRefused
  (Zig.Enc.encode (#v[67, 111, 110, 110, 101, 99, 116, 105, 111, 110, 82, 101, 102, 117, 115, 101, 100, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 40: the name of error.AddressFamilyUnsupported
  (Zig.Enc.encode (#v[65, 100, 100, 114, 101, 115, 115, 70, 97, 109, 105, 108, 121, 85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 0] : Vector (BitVec 8) 25), 1, .constGlobal),
  -- 41: the name of error.FastOpenAlreadyInProgress
  (Zig.Enc.encode (#v[70, 97, 115, 116, 79, 112, 101, 110, 65, 108, 114, 101, 97, 100, 121, 73, 110, 80, 114, 111, 103, 114, 101, 115, 115, 0] : Vector (BitVec 8) 26), 1, .constGlobal),
  -- 42: the name of error.SocketNotBound
  (Zig.Enc.encode (#v[83, 111, 99, 107, 101, 116, 78, 111, 116, 66, 111, 117, 110, 100, 0] : Vector (BitVec 8) 15), 1, .constGlobal),
  -- 43: the name of error.Timeout
  (Zig.Enc.encode (#v[84, 105, 109, 101, 111, 117, 116, 0] : Vector (BitVec 8) 8), 1, .constGlobal),
  -- 44: the name of error.PathAlreadyExists
  (Zig.Enc.encode (#v[80, 97, 116, 104, 65, 108, 114, 101, 97, 100, 121, 69, 120, 105, 115, 116, 115, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 45: the name of error.SymLinkLoop
  (Zig.Enc.encode (#v[83, 121, 109, 76, 105, 110, 107, 76, 111, 111, 112, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 46: the name of error.LinkQuotaExceeded
  (Zig.Enc.encode (#v[76, 105, 110, 107, 81, 117, 111, 116, 97, 69, 120, 99, 101, 101, 100, 101, 100, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 47: the name of error.FileNotFound
  (Zig.Enc.encode (#v[70, 105, 108, 101, 78, 111, 116, 70, 111, 117, 110, 100, 0] : Vector (BitVec 8) 13), 1, .constGlobal),
  -- 48: the name of error.NotDir
  (Zig.Enc.encode (#v[78, 111, 116, 68, 105, 114, 0] : Vector (BitVec 8) 7), 1, .constGlobal),
  -- 49: the name of error.ReadOnlyFileSystem
  (Zig.Enc.encode (#v[82, 101, 97, 100, 79, 110, 108, 121, 70, 105, 108, 101, 83, 121, 115, 116, 101, 109, 0] : Vector (BitVec 8) 19), 1, .constGlobal),
  -- 50: the name of error.NetworkNotFound
  (Zig.Enc.encode (#v[78, 101, 116, 119, 111, 114, 107, 78, 111, 116, 70, 111, 117, 110, 100, 0] : Vector (BitVec 8) 16), 1, .constGlobal),
  -- 51: the name of error.NameTooLong
  (Zig.Enc.encode (#v[78, 97, 109, 101, 84, 111, 111, 76, 111, 110, 103, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 52: the name of error.BadPathName
  (Zig.Enc.encode (#v[66, 97, 100, 80, 97, 116, 104, 78, 97, 109, 101, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 53: the name of error.PipeBusy
  (Zig.Enc.encode (#v[80, 105, 112, 101, 66, 117, 115, 121, 0] : Vector (BitVec 8) 9), 1, .constGlobal),
  -- 54: the name of error.AntivirusInterference
  (Zig.Enc.encode (#v[65, 110, 116, 105, 118, 105, 114, 117, 115, 73, 110, 116, 101, 114, 102, 101, 114, 101, 110, 99, 101, 0] : Vector (BitVec 8) 22), 1, .constGlobal),
  -- 55: the name of error.FileLocksUnsupported
  (Zig.Enc.encode (#v[70, 105, 108, 101, 76, 111, 99, 107, 115, 85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 0] : Vector (BitVec 8) 21), 1, .constGlobal),
  -- 56: the name of error.Streaming
  (Zig.Enc.encode (#v[83, 116, 114, 101, 97, 109, 105, 110, 103, 0] : Vector (BitVec 8) 10), 1, .constGlobal),
  -- 57: the name of error.OperationUnsupported
  (Zig.Enc.encode (#v[79, 112, 101, 114, 97, 116, 105, 111, 110, 85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 0] : Vector (BitVec 8) 21), 1, .constGlobal),
  -- 58: the name of error.FileSystem
  (Zig.Enc.encode (#v[70, 105, 108, 101, 83, 121, 115, 116, 101, 109, 0] : Vector (BitVec 8) 11), 1, .constGlobal),
  -- 59: the name of error.UnrecognizedVolume
  (Zig.Enc.encode (#v[85, 110, 114, 101, 99, 111, 103, 110, 105, 122, 101, 100, 86, 111, 108, 117, 109, 101, 0] : Vector (BitVec 8) 19), 1, .constGlobal),
  -- 60: the name of error.DirNotEmpty
  (Zig.Enc.encode (#v[68, 105, 114, 78, 111, 116, 69, 109, 112, 116, 121, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 61: the name of error.CrossDevice
  (Zig.Enc.encode (#v[67, 114, 111, 115, 115, 68, 101, 118, 105, 99, 101, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 62: the name of error.HardwareFailure
  (Zig.Enc.encode (#v[72, 97, 114, 100, 119, 97, 114, 101, 70, 97, 105, 108, 117, 114, 101, 0] : Vector (BitVec 8) 16), 1, .constGlobal),
  -- 63: the name of error.NotLink
  (Zig.Enc.encode (#v[78, 111, 116, 76, 105, 110, 107, 0] : Vector (BitVec 8) 8), 1, .constGlobal),
  -- 64: the name of error.UnsupportedReparsePointType
  (Zig.Enc.encode (#v[85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 82, 101, 112, 97, 114, 115, 101, 80, 111, 105, 110, 116, 84, 121, 112, 101, 0] : Vector (BitVec 8) 28), 1, .constGlobal),
  -- 65: the name of error.NotTerminalDevice
  (Zig.Enc.encode (#v[78, 111, 116, 84, 101, 114, 109, 105, 110, 97, 108, 68, 101, 118, 105, 99, 101, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 66: the name of error.NonResizable
  (Zig.Enc.encode (#v[78, 111, 110, 82, 101, 115, 105, 122, 97, 98, 108, 101, 0] : Vector (BitVec 8) 13), 1, .constGlobal),
  -- 67: the name of error.LockedMemoryLimitExceeded
  (Zig.Enc.encode (#v[76, 111, 99, 107, 101, 100, 77, 101, 109, 111, 114, 121, 76, 105, 109, 105, 116, 69, 120, 99, 101, 101, 100, 101, 100, 0] : Vector (BitVec 8) 26), 1, .constGlobal),
  -- 68: the name of error.ProcessNotFound
  (Zig.Enc.encode (#v[80, 114, 111, 99, 101, 115, 115, 78, 111, 116, 70, 111, 117, 110, 100, 0] : Vector (BitVec 8) 16), 1, .constGlobal),
  -- 69: the name of error.CurrentDirUnlinked
  (Zig.Enc.encode (#v[67, 117, 114, 114, 101, 110, 116, 68, 105, 114, 85, 110, 108, 105, 110, 107, 101, 100, 0] : Vector (BitVec 8) 19), 1, .constGlobal),
  -- 70: the name of error.PathExceedsLimit
  (Zig.Enc.encode (#v[80, 97, 116, 104, 69, 120, 99, 101, 101, 100, 115, 76, 105, 109, 105, 116, 0] : Vector (BitVec 8) 17), 1, .constGlobal),
  -- 71: the name of error.InvalidWtf8
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 87, 116, 102, 56, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 72: the name of error.InvalidExe
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 69, 120, 101, 0] : Vector (BitVec 8) 11), 1, .constGlobal),
  -- 73: the name of error.InvalidBatchScriptArg
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 66, 97, 116, 99, 104, 83, 99, 114, 105, 112, 116, 65, 114, 103, 0] : Vector (BitVec 8) 22), 1, .constGlobal),
  -- 74: the name of error.ResourceLimitReached
  (Zig.Enc.encode (#v[82, 101, 115, 111, 117, 114, 99, 101, 76, 105, 109, 105, 116, 82, 101, 97, 99, 104, 101, 100, 0] : Vector (BitVec 8) 21), 1, .constGlobal),
  -- 75: the name of error.InvalidUserId
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 85, 115, 101, 114, 73, 100, 0] : Vector (BitVec 8) 14), 1, .constGlobal),
  -- 76: the name of error.InvalidProcessGroupId
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 80, 114, 111, 99, 101, 115, 115, 71, 114, 111, 117, 112, 73, 100, 0] : Vector (BitVec 8) 22), 1, .constGlobal),
  -- 77: the name of error.InvalidName
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 78, 97, 109, 101, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 78: the name of error.ProcessAlreadyExec
  (Zig.Enc.encode (#v[80, 114, 111, 99, 101, 115, 115, 65, 108, 114, 101, 97, 100, 121, 69, 120, 101, 99, 0] : Vector (BitVec 8) 19), 1, .constGlobal),
  -- 79: the name of error.ClockUnavailable
  (Zig.Enc.encode (#v[67, 108, 111, 99, 107, 85, 110, 97, 118, 97, 105, 108, 97, 98, 108, 101, 0] : Vector (BitVec 8) 17), 1, .constGlobal),
  -- 80: the name of error.EntropyUnavailable
  (Zig.Enc.encode (#v[69, 110, 116, 114, 111, 112, 121, 85, 110, 97, 118, 97, 105, 108, 97, 98, 108, 101, 0] : Vector (BitVec 8) 19), 1, .constGlobal),
  -- 81: the name of error.AddressInUse
  (Zig.Enc.encode (#v[65, 100, 100, 114, 101, 115, 115, 73, 110, 85, 115, 101, 0] : Vector (BitVec 8) 13), 1, .constGlobal),
  -- 82: the name of error.AddressUnavailable
  (Zig.Enc.encode (#v[65, 100, 100, 114, 101, 115, 115, 85, 110, 97, 118, 97, 105, 108, 97, 98, 108, 101, 0] : Vector (BitVec 8) 19), 1, .constGlobal),
  -- 83: the name of error.ProtocolUnsupportedBySystem
  (Zig.Enc.encode (#v[80, 114, 111, 116, 111, 99, 111, 108, 85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 66, 121, 83, 121, 115, 116, 101, 109, 0] : Vector (BitVec 8) 28), 1, .constGlobal),
  -- 84: the name of error.ProtocolUnsupportedByAddressFamily
  (Zig.Enc.encode (#v[80, 114, 111, 116, 111, 99, 111, 108, 85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 66, 121, 65, 100, 100, 114, 101, 115, 115, 70, 97, 109, 105, 108, 121, 0] : Vector (BitVec 8) 35), 1, .constGlobal),
  -- 85: the name of error.SocketModeUnsupported
  (Zig.Enc.encode (#v[83, 111, 99, 107, 101, 116, 77, 111, 100, 101, 85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 0] : Vector (BitVec 8) 22), 1, .constGlobal),
  -- 86: the name of error.OptionUnsupported
  (Zig.Enc.encode (#v[79, 112, 116, 105, 111, 110, 85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 87: the name of error.SocketNotListening
  (Zig.Enc.encode (#v[83, 111, 99, 107, 101, 116, 78, 111, 116, 76, 105, 115, 116, 101, 110, 105, 110, 103, 0] : Vector (BitVec 8) 19), 1, .constGlobal),
  -- 88: the name of error.ConnectionAborted
  (Zig.Enc.encode (#v[67, 111, 110, 110, 101, 99, 116, 105, 111, 110, 65, 98, 111, 114, 116, 101, 100, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 89: the name of error.BlockedByFirewall
  (Zig.Enc.encode (#v[66, 108, 111, 99, 107, 101, 100, 66, 121, 70, 105, 114, 101, 119, 97, 108, 108, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 90: the name of error.ProtocolFailure
  (Zig.Enc.encode (#v[80, 114, 111, 116, 111, 99, 111, 108, 70, 97, 105, 108, 117, 114, 101, 0] : Vector (BitVec 8) 16), 1, .constGlobal),
  -- 91: the name of error.ConnectionPending
  (Zig.Enc.encode (#v[67, 111, 110, 110, 101, 99, 116, 105, 111, 110, 80, 101, 110, 100, 105, 110, 103, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 92: the name of error.InterfaceNotFound
  (Zig.Enc.encode (#v[73, 110, 116, 101, 114, 102, 97, 99, 101, 78, 111, 116, 70, 111, 117, 110, 100, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 93: the name of error.UnknownHostName
  (Zig.Enc.encode (#v[85, 110, 107, 110, 111, 119, 110, 72, 111, 115, 116, 78, 97, 109, 101, 0] : Vector (BitVec 8) 16), 1, .constGlobal),
  -- 94: the name of error.ResolvConfParseFailed
  (Zig.Enc.encode (#v[82, 101, 115, 111, 108, 118, 67, 111, 110, 102, 80, 97, 114, 115, 101, 70, 97, 105, 108, 101, 100, 0] : Vector (BitVec 8) 22), 1, .constGlobal),
  -- 95: the name of error.InvalidDnsARecord
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 68, 110, 115, 65, 82, 101, 99, 111, 114, 100, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 96: the name of error.InvalidDnsAAAARecord
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 68, 110, 115, 65, 65, 65, 65, 82, 101, 99, 111, 114, 100, 0] : Vector (BitVec 8) 21), 1, .constGlobal),
  -- 97: the name of error.InvalidDnsCnameRecord
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 68, 110, 115, 67, 110, 97, 109, 101, 82, 101, 99, 111, 114, 100, 0] : Vector (BitVec 8) 22), 1, .constGlobal),
  -- 98: the name of error.NameServerFailure
  (Zig.Enc.encode (#v[78, 97, 109, 101, 83, 101, 114, 118, 101, 114, 70, 97, 105, 108, 117, 114, 101, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 99: the name of error.NoAddressReturned
  (Zig.Enc.encode (#v[78, 111, 65, 100, 100, 114, 101, 115, 115, 82, 101, 116, 117, 114, 110, 101, 100, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 100: the name of error.DetectingNetworkConfigurationFailed
  (Zig.Enc.encode (#v[68, 101, 116, 101, 99, 116, 105, 110, 103, 78, 101, 116, 119, 111, 114, 107, 67, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 70, 97, 105, 108, 101, 100, 0] : Vector (BitVec 8) 36), 1, .constGlobal),
  -- 101: the name of error.WriteFailed
  (Zig.Enc.encode (#v[87, 114, 105, 116, 101, 70, 97, 105, 108, 101, 100, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 102: the name of error.Overflow
  (Zig.Enc.encode (#v[79, 118, 101, 114, 102, 108, 111, 119, 0] : Vector (BitVec 8) 9), 1, .constGlobal),
  -- 103: the name of error.InvalidDebugInfo
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 68, 101, 98, 117, 103, 73, 110, 102, 111, 0] : Vector (BitVec 8) 17), 1, .constGlobal),
  -- 104: the name of error.MissingDebugInfo
  (Zig.Enc.encode (#v[77, 105, 115, 115, 105, 110, 103, 68, 101, 98, 117, 103, 73, 110, 102, 111, 0] : Vector (BitVec 8) 17), 1, .constGlobal),
  -- 105: the name of error.UnsupportedDebugInfo
  (Zig.Enc.encode (#v[85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 68, 101, 98, 117, 103, 73, 110, 102, 111, 0] : Vector (BitVec 8) 21), 1, .constGlobal),
  -- 106: the name of error.StreamTooLong
  (Zig.Enc.encode (#v[83, 116, 114, 101, 97, 109, 84, 111, 111, 76, 111, 110, 103, 0] : Vector (BitVec 8) 14), 1, .constGlobal),
  -- 107: the name of error.NoSymtab
  (Zig.Enc.encode (#v[78, 111, 83, 121, 109, 116, 97, 98, 0] : Vector (BitVec 8) 9), 1, .constGlobal),
  -- 108: the name of error.NoStrtab
  (Zig.Enc.encode (#v[78, 111, 83, 116, 114, 116, 97, 98, 0] : Vector (BitVec 8) 9), 1, .constGlobal),
  -- 109: the name of error.BadSymtab
  (Zig.Enc.encode (#v[66, 97, 100, 83, 121, 109, 116, 97, 98, 0] : Vector (BitVec 8) 10), 1, .constGlobal),
  -- 110: the name of error.TruncatedElfFile
  (Zig.Enc.encode (#v[84, 114, 117, 110, 99, 97, 116, 101, 100, 69, 108, 102, 70, 105, 108, 101, 0] : Vector (BitVec 8) 17), 1, .constGlobal),
  -- 111: the name of error.InvalidCompressedSection
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 67, 111, 109, 112, 114, 101, 115, 115, 101, 100, 83, 101, 99, 116, 105, 111, 110, 0] : Vector (BitVec 8) 25), 1, .constGlobal),
  -- 112: the name of error.InvalidElfMagic
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 69, 108, 102, 77, 97, 103, 105, 99, 0] : Vector (BitVec 8) 16), 1, .constGlobal),
  -- 113: the name of error.InvalidElfVersion
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 69, 108, 102, 86, 101, 114, 115, 105, 111, 110, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 114: the name of error.InvalidElfClass
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 69, 108, 102, 67, 108, 97, 115, 115, 0] : Vector (BitVec 8) 16), 1, .constGlobal),
  -- 115: the name of error.InvalidElfEndian
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 69, 108, 102, 69, 110, 100, 105, 97, 110, 0] : Vector (BitVec 8) 17), 1, .constGlobal),
  -- 116: the name of error.MemoryMappingNotSupported
  (Zig.Enc.encode (#v[77, 101, 109, 111, 114, 121, 77, 97, 112, 112, 105, 110, 103, 78, 111, 116, 83, 117, 112, 112, 111, 114, 116, 101, 100, 0] : Vector (BitVec 8) 26), 1, .constGlobal),
  -- 117: the name of error.CrcMismatch
  (Zig.Enc.encode (#v[67, 114, 99, 77, 105, 115, 109, 97, 116, 99, 104, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 118: the name of error.MappingAlreadyExists
  (Zig.Enc.encode (#v[77, 97, 112, 112, 105, 110, 103, 65, 108, 114, 101, 97, 100, 121, 69, 120, 105, 115, 116, 115, 0] : Vector (BitVec 8) 21), 1, .constGlobal),
  -- 119: the name of error.BadGzipHeader
  (Zig.Enc.encode (#v[66, 97, 100, 71, 122, 105, 112, 72, 101, 97, 100, 101, 114, 0] : Vector (BitVec 8) 14), 1, .constGlobal),
  -- 120: the name of error.BadZlibHeader
  (Zig.Enc.encode (#v[66, 97, 100, 90, 108, 105, 98, 72, 101, 97, 100, 101, 114, 0] : Vector (BitVec 8) 14), 1, .constGlobal),
  -- 121: the name of error.WrongGzipChecksum
  (Zig.Enc.encode (#v[87, 114, 111, 110, 103, 71, 122, 105, 112, 67, 104, 101, 99, 107, 115, 117, 109, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 122: the name of error.WrongGzipSize
  (Zig.Enc.encode (#v[87, 114, 111, 110, 103, 71, 122, 105, 112, 83, 105, 122, 101, 0] : Vector (BitVec 8) 14), 1, .constGlobal),
  -- 123: the name of error.WrongZlibChecksum
  (Zig.Enc.encode (#v[87, 114, 111, 110, 103, 90, 108, 105, 98, 67, 104, 101, 99, 107, 115, 117, 109, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 124: the name of error.InvalidCode
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 67, 111, 100, 101, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 125: the name of error.InvalidMatch
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 77, 97, 116, 99, 104, 0] : Vector (BitVec 8) 13), 1, .constGlobal),
  -- 126: the name of error.WrongStoredBlockNlen
  (Zig.Enc.encode (#v[87, 114, 111, 110, 103, 83, 116, 111, 114, 101, 100, 66, 108, 111, 99, 107, 78, 108, 101, 110, 0] : Vector (BitVec 8) 21), 1, .constGlobal),
  -- 127: the name of error.InvalidBlockType
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 66, 108, 111, 99, 107, 84, 121, 112, 101, 0] : Vector (BitVec 8) 17), 1, .constGlobal),
  -- 128: the name of error.InvalidDynamicBlockHeader
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 68, 121, 110, 97, 109, 105, 99, 66, 108, 111, 99, 107, 72, 101, 97, 100, 101, 114, 0] : Vector (BitVec 8) 26), 1, .constGlobal),
  -- 129: the name of error.OversubscribedHuffmanTree
  (Zig.Enc.encode (#v[79, 118, 101, 114, 115, 117, 98, 115, 99, 114, 105, 98, 101, 100, 72, 117, 102, 102, 109, 97, 110, 84, 114, 101, 101, 0] : Vector (BitVec 8) 26), 1, .constGlobal),
  -- 130: the name of error.IncompleteHuffmanTree
  (Zig.Enc.encode (#v[73, 110, 99, 111, 109, 112, 108, 101, 116, 101, 72, 117, 102, 102, 109, 97, 110, 84, 114, 101, 101, 0] : Vector (BitVec 8) 22), 1, .constGlobal),
  -- 131: the name of error.MissingEndOfBlockCode
  (Zig.Enc.encode (#v[77, 105, 115, 115, 105, 110, 103, 69, 110, 100, 79, 102, 66, 108, 111, 99, 107, 67, 111, 100, 101, 0] : Vector (BitVec 8) 22), 1, .constGlobal),
  -- 132: the name of error.InvalidCharacter
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 67, 104, 97, 114, 97, 99, 116, 101, 114, 0] : Vector (BitVec 8) 17), 1, .constGlobal),
  -- 133: the name of error.UnsupportedAddrSize
  (Zig.Enc.encode (#v[85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 65, 100, 100, 114, 83, 105, 122, 101, 0] : Vector (BitVec 8) 20), 1, .constGlobal),
  -- 134: the name of error.UnimplementedUserOpcode
  (Zig.Enc.encode (#v[85, 110, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 85, 115, 101, 114, 79, 112, 99, 111, 100, 101, 0] : Vector (BitVec 8) 24), 1, .constGlobal),
  -- 135: the name of error.InvalidOpcode
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 79, 112, 99, 111, 100, 101, 0] : Vector (BitVec 8) 14), 1, .constGlobal),
  -- 136: the name of error.InvalidOperation
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 79, 112, 101, 114, 97, 116, 105, 111, 110, 0] : Vector (BitVec 8) 17), 1, .constGlobal),
  -- 137: the name of error.InvalidOperand
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 79, 112, 101, 114, 97, 110, 100, 0] : Vector (BitVec 8) 15), 1, .constGlobal),
  -- 138: the name of error.InvalidRegister
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 82, 101, 103, 105, 115, 116, 101, 114, 0] : Vector (BitVec 8) 16), 1, .constGlobal),
  -- 139: the name of error.UnsupportedRegister
  (Zig.Enc.encode (#v[85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 82, 101, 103, 105, 115, 116, 101, 114, 0] : Vector (BitVec 8) 20), 1, .constGlobal),
  -- 140: the name of error.UnsupportedDwarfVersion
  (Zig.Enc.encode (#v[85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 68, 119, 97, 114, 102, 86, 101, 114, 115, 105, 111, 110, 0] : Vector (BitVec 8) 24), 1, .constGlobal),
  -- 141: the name of error.UnsupportedAugmentation
  (Zig.Enc.encode (#v[85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 65, 117, 103, 109, 101, 110, 116, 97, 116, 105, 111, 110, 0] : Vector (BitVec 8) 24), 1, .constGlobal),
  -- 142: the name of error.IncompatibleRegisterSize
  (Zig.Enc.encode (#v[73, 110, 99, 111, 109, 112, 97, 116, 105, 98, 108, 101, 82, 101, 103, 105, 115, 116, 101, 114, 83, 105, 122, 101, 0] : Vector (BitVec 8) 25), 1, .constGlobal),
  -- 143: the name of error.UnimplementedExpressionCall
  (Zig.Enc.encode (#v[85, 110, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 69, 120, 112, 114, 101, 115, 115, 105, 111, 110, 67, 97, 108, 108, 0] : Vector (BitVec 8) 28), 1, .constGlobal),
  -- 144: the name of error.UnimplementedOpcode
  (Zig.Enc.encode (#v[85, 110, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 79, 112, 99, 111, 100, 101, 0] : Vector (BitVec 8) 20), 1, .constGlobal),
  -- 145: the name of error.UnimplementedTypedComparison
  (Zig.Enc.encode (#v[85, 110, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 84, 121, 112, 101, 100, 67, 111, 109, 112, 97, 114, 105, 115, 111, 110, 0] : Vector (BitVec 8) 29), 1, .constGlobal),
  -- 146: the name of error.UnimplementedTypeConversion
  (Zig.Enc.encode (#v[85, 110, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 84, 121, 112, 101, 67, 111, 110, 118, 101, 114, 115, 105, 111, 110, 0] : Vector (BitVec 8) 28), 1, .constGlobal),
  -- 147: the name of error.UnknownExpressionOpcode
  (Zig.Enc.encode (#v[85, 110, 107, 110, 111, 119, 110, 69, 120, 112, 114, 101, 115, 115, 105, 111, 110, 79, 112, 99, 111, 100, 101, 0] : Vector (BitVec 8) 24), 1, .constGlobal),
  -- 148: the name of error.IncompleteExpressionContext
  (Zig.Enc.encode (#v[73, 110, 99, 111, 109, 112, 108, 101, 116, 101, 69, 120, 112, 114, 101, 115, 115, 105, 111, 110, 67, 111, 110, 116, 101, 120, 116, 0] : Vector (BitVec 8) 28), 1, .constGlobal),
  -- 149: the name of error.InvalidCFAOpcode
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 67, 70, 65, 79, 112, 99, 111, 100, 101, 0] : Vector (BitVec 8) 17), 1, .constGlobal),
  -- 150: the name of error.InvalidExpression
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 69, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 151: the name of error.InvalidFrameBase
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 70, 114, 97, 109, 101, 66, 97, 115, 101, 0] : Vector (BitVec 8) 17), 1, .constGlobal),
  -- 152: the name of error.InvalidIntegralTypeSize
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 73, 110, 116, 101, 103, 114, 97, 108, 84, 121, 112, 101, 83, 105, 122, 101, 0] : Vector (BitVec 8) 24), 1, .constGlobal),
  -- 153: the name of error.InvalidSubExpression
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 83, 117, 98, 69, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0] : Vector (BitVec 8) 21), 1, .constGlobal),
  -- 154: the name of error.InvalidTypeLength
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 84, 121, 112, 101, 76, 101, 110, 103, 116, 104, 0] : Vector (BitVec 8) 18), 1, .constGlobal),
  -- 155: the name of error.TruncatedIntegralType
  (Zig.Enc.encode (#v[84, 114, 117, 110, 99, 97, 116, 101, 100, 73, 110, 116, 101, 103, 114, 97, 108, 84, 121, 112, 101, 0] : Vector (BitVec 8) 22), 1, .constGlobal),
  -- 156: the name of error.DivisionByZero
  (Zig.Enc.encode (#v[68, 105, 118, 105, 115, 105, 111, 110, 66, 121, 90, 101, 114, 111, 0] : Vector (BitVec 8) 15), 1, .constGlobal),
  -- 157: the name of error.WindowTooSmall
  (Zig.Enc.encode (#v[87, 105, 110, 100, 111, 119, 84, 111, 111, 83, 109, 97, 108, 108, 0] : Vector (BitVec 8) 15), 1, .constGlobal),
  -- 158: the name of error.Closed
  (Zig.Enc.encode (#v[67, 108, 111, 115, 101, 100, 0] : Vector (BitVec 8) 7), 1, .constGlobal),
  -- 159: the name of error.ParseFailed
  (Zig.Enc.encode (#v[80, 97, 114, 115, 101, 70, 97, 105, 108, 101, 100, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 160: the name of error.UnresolvedScope
  (Zig.Enc.encode (#v[85, 110, 114, 101, 115, 111, 108, 118, 101, 100, 83, 99, 111, 112, 101, 0] : Vector (BitVec 8) 16), 1, .constGlobal),
  -- 161: the name of error.InvalidEnd
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 69, 110, 100, 0] : Vector (BitVec 8) 11), 1, .constGlobal),
  -- 162: the name of error.Incomplete
  (Zig.Enc.encode (#v[73, 110, 99, 111, 109, 112, 108, 101, 116, 101, 0] : Vector (BitVec 8) 11), 1, .constGlobal),
  -- 163: the name of error.NonCanonical
  (Zig.Enc.encode (#v[78, 111, 110, 67, 97, 110, 111, 110, 105, 99, 97, 108, 0] : Vector (BitVec 8) 13), 1, .constGlobal),
  -- 164: the name of error.InvalidDnsPacket
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 68, 110, 115, 80, 97, 99, 107, 101, 116, 0] : Vector (BitVec 8) 17), 1, .constGlobal),
  -- 165: the name of error.InvalidHostName
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 72, 111, 115, 116, 78, 97, 109, 101, 0] : Vector (BitVec 8) 16), 1, .constGlobal),
  -- 166: the name of error.SectionOversize
  (Zig.Enc.encode (#v[83, 101, 99, 116, 105, 111, 110, 79, 118, 101, 114, 115, 105, 122, 101, 0] : Vector (BitVec 8) 16), 1, .constGlobal),
  -- 167: the name of error.ThreadQuotaExceeded
  (Zig.Enc.encode (#v[84, 104, 114, 101, 97, 100, 81, 117, 111, 116, 97, 69, 120, 99, 101, 101, 100, 101, 100, 0] : Vector (BitVec 8) 20), 1, .constGlobal),
  -- 168: the name of error.Alpha
  (Zig.Enc.encode (#v[65, 108, 112, 104, 97, 0] : Vector (BitVec 8) 6), 1, .constGlobal),
  -- 169: the name of error.Beta
  (Zig.Enc.encode (#v[66, 101, 116, 97, 0] : Vector (BitVec 8) 5), 1, .constGlobal),
  -- 170: the name of error.Gamma
  (Zig.Enc.encode (#v[71, 97, 109, 109, 97, 0] : Vector (BitVec 8) 6), 1, .constGlobal),
  -- 171: the name of error.SizeTooSmall
  (Zig.Enc.encode (#v[83, 105, 122, 101, 84, 111, 111, 83, 109, 97, 108, 108, 0] : Vector (BitVec 8) 13), 1, .constGlobal),
  -- 172: the name of error.LimitTooBig
  (Zig.Enc.encode (#v[76, 105, 109, 105, 116, 84, 111, 111, 66, 105, 103, 0] : Vector (BitVec 8) 12), 1, .constGlobal),
  -- 173: the name of error.InvalidSyscallParameters
  (Zig.Enc.encode (#v[73, 110, 118, 97, 108, 105, 100, 83, 121, 115, 99, 97, 108, 108, 80, 97, 114, 97, 109, 101, 116, 101, 114, 115, 0] : Vector (BitVec 8) 25), 1, .constGlobal)]

def errorNameOf (e : Zig.ErrName) : Zig.Result Zig.Slice :=
  match errorTable.idxOf? e with
  | some k => pure ⟨⟨some (0 + k), 0⟩, BitVec.ofNat 64 e.utf8ByteSize⟩
  | none => throw .unspecified

structure backLocals where
  deriving Inhabited

inductive backExit where
  | ret (v : Zig.ErrName)
  | br4

def back (p0 : BitVec 8) : Zig.Result (Zig.ErrName) := do
  let e ← ((do
    let i1 ← pure (decide ((p0).toNat ≤ errorTable.size))
    let i2 ← pure (p0 != (0 : BitVec 8))
    let i3 ← pure (i1 && i2)
    match ← ((do
      if i3 then (do
        pure .br4)
      else (do
        throw .panic)) : Zig.M backLocals backExit) with
    | .br4 => (do
      let i9 ← Zig.call (Zig.errorFromIntIn errorTable p0)
      pure (.ret i9))
    | e => pure e) : Zig.M backLocals backExit).run' (default : backLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure codeLocals where
  deriving Inhabited

inductive codeExit where
  | ret (v : BitVec 8)

def code (p0 : Zig.ErrName) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i1 ← pure (p0)
    let i2 ← Zig.call (Zig.intFromErrorIn 8 errorTable i1)
    pure (.ret i2)) : Zig.M codeLocals codeExit).run' (default : codeLocals)
  match e with
  | .ret v => pure v

structure nameOfLocals where
  deriving Inhabited

inductive nameOfExit where
  | ret (v : Zig.Slice)
  | br4

def nameOf (p0 : BitVec 8) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    let i1 ← pure (decide ((p0).toNat ≤ errorTable.size))
    let i2 ← pure (p0 != (0 : BitVec 8))
    let i3 ← pure (i1 && i2)
    match ← ((do
      if i3 then (do
        pure .br4)
      else (do
        throw .panic)) : Zig.MM nameOfLocals nameOfExit) with
    | .br4 => (do
      let i9 ← Zig.callR (Zig.errorFromIntIn errorTable p0)
      let i10 ← Zig.callR (errorNameOf i9)
      let i11 ← pure (i10)
      pure (.ret i11))
    | e => pure e) : Zig.MM nameOfLocals nameOfExit).run' (default : nameOfLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure roundTripLocals where
  deriving Inhabited

inductive roundTripExit where
  | ret (v : Bool)
  | br6

def roundTrip (p0 : Zig.ErrName) : Zig.Result (Bool) := do
  let e ← ((do
    let i1 ← pure (p0)
    let i2 ← Zig.call (Zig.intFromErrorIn 8 errorTable i1)
    let i3 ← pure (decide ((i2).toNat ≤ errorTable.size))
    let i4 ← pure (i2 != (0 : BitVec 8))
    let i5 ← pure (i3 && i4)
    match ← ((do
      if i5 then (do
        pure .br6)
      else (do
        throw .panic)) : Zig.M roundTripLocals roundTripExit) with
    | .br6 => (do
      let i11 ← Zig.call (Zig.errorFromIntIn errorTable i2)
      let i12 ← pure (i11 == p0)
      pure (.ret i12))
    | e => pure e) : Zig.M roundTripLocals roundTripExit).run' (default : roundTripLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure viaMemoryLocals where
  cells : Zig.Ptr
  deriving Inhabited

inductive viaMemoryExit where
  | ret (v : Bool)
  | br15

def viaMemory (p0 : Zig.ErrName) : Zig.MemM (Bool) := do
  let s1 ← Zig.allocStack 2 1
  let e ← ((do
    let i1 ← pure (← get).cells
    let i2 ← pure i1
    let i3 ← pure (p0)
    let i4 ← Zig.callR (Zig.intFromErrorIn 8 errorTable i3)
    Zig.store (α := BitVec 8) 1 i2 i4
    let i6 ← Zig.callM (Zig.ptrProject i1 (·.elem 1 (1 : BitVec 64)))
    Zig.store (α := BitVec 8) 1 i6 (0 : BitVec 8)
    let i8 ← Zig.callM (Zig.ptrProject i1 (·.elem 1 (1 : BitVec 64)))
    let i9 ← Zig.callM (Zig.load (BitVec 8) 1 (i1.elem 1 (0 : BitVec 64)))
    Zig.store (α := BitVec 8) 1 i8 i9
    let i11 ← Zig.callM (Zig.load (BitVec 8) 1 (i1.elem 1 (1 : BitVec 64)))
    let i12 ← pure (decide ((i11).toNat ≤ errorTable.size))
    let i13 ← pure (i11 != (0 : BitVec 8))
    let i14 ← pure (i12 && i13)
    match ← ((do
      if i14 then (do
        pure .br15)
      else (do
        throw .panic)) : Zig.MM viaMemoryLocals viaMemoryExit) with
    | .br15 => (do
      let i20 ← Zig.callR (Zig.errorFromIntIn errorTable i11)
      let i21 ← pure (i20 == p0)
      pure (.ret i21))
    | e => pure e) : Zig.MM viaMemoryLocals viaMemoryExit).run' { (default : viaMemoryLocals) with cells := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v
  | _ => throw .panic

end ErrorInts