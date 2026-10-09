import ExternCalls.Gen

/-! The translated extern calls evaluate to native Zig's results (`expected.txt`, from
`native.zig`): `memset`/`strlen` resolve to the translated `export fn` definitions of
`libc_ref.zig`. -/
namespace ExternCalls.Eval

private def successful {α : Type} (r : Zig.Result α) : Option α := Option.bind r Except.toOption
private def run {α : Type} (m : Zig.MemM α) : Option α := successful (m.run' (ExternCalls.mem0 .fresh))

-- fillSum 0 7, 4 0, 16 255, 20 -1, 3 258
#guard run (ExternCalls.fillSum 0#64 7#32) == some 16#32
#guard run (ExternCalls.fillSum 4#64 0#32) == some 12#32
#guard run (ExternCalls.fillSum 16#64 255#32) == some 4080#32
#guard run (ExternCalls.fillSum 20#64 (-1 : BitVec 32)) == some 4080#32
#guard run (ExternCalls.fillSum 3#64 258#32) == some 19#32
-- greetLen 0, 1
#guard run (ExternCalls.greetLen 0#32) == some 5#64
#guard run (ExternCalls.greetLen 1#32) == some 12#64

end ExternCalls.Eval
