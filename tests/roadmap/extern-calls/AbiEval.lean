import ExternCalls.Abi

/-! The extern calls of `abi_calls.zig` bind through C ABI conversions to `abi_ref.zig`'s
`@export`s (`docs/air-json.md` §Extern calls) and evaluate to native Zig's results
(`abi_expected.txt`, from `abi_native.zig`). The conversions make a `c_int` outside `u8`, a
`null` for a non-null `[*:0]const c_char` and an address that is not a multiple of the
definition's alignment `.illegal` (an `unreachable` without a safety check), where the compiled
program has no defined behaviour. -/
namespace ExternCalls.AbiEval

private def run {α : Type} (m : Zig.MemM α) : Zig.Result α := m.run' (ExternCalls.Abi.mem0 .fresh)
private def ok {α : Type} (m : Zig.MemM α) : Option α := Option.bind (run m) Except.toOption
private def err {α : Type} (m : Zig.MemM α) : Option Zig.Error :=
  match run m with
  | some (.error e) => some e
  | _ => none

-- fillSum 0 7, 4 0, 16 255, 3 2
#guard ok (ExternCalls.Abi.fillSum 0#64 7#32) == some 16#32
#guard ok (ExternCalls.Abi.fillSum 4#64 0#32) == some 12#32
#guard ok (ExternCalls.Abi.fillSum 16#64 255#32) == some 4080#32
#guard ok (ExternCalls.Abi.fillSum 3#64 2#32) == some 19#32
-- lenOf 0, 1
#guard ok (ExternCalls.Abi.lenOf 0#32) == some 5#64
#guard ok (ExternCalls.Abi.lenOf 1#32) == some 9#64
-- firstAt 0, 16, 40: the definition's alignment 16, checked at the call (`null` passes).
#guard ok (ExternCalls.Abi.firstAt 0#64) == some 1#8
#guard ok (ExternCalls.Abi.firstAt 16#64) == some 17#8
#guard ok (ExternCalls.Abi.firstAt 40#64) == some 0#8
-- No defined behaviour: a byte outside `u8`, a `null` string.
#guard err (ExternCalls.Abi.fillSum 3#64 256#32) == some .illegal
#guard err (ExternCalls.Abi.fillSum 3#64 (-1 : BitVec 32)) == some .illegal
#guard err (ExternCalls.Abi.lenOf 2#32) == some .illegal
-- A pointer without the definition's alignment.
#guard err (ExternCalls.Abi.firstAt 1#64) == some .illegal
#guard err (ExternCalls.Abi.firstAt 24#64) == some .illegal

end ExternCalls.AbiEval
