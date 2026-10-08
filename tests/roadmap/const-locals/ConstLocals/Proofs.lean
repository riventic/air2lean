import ConstLocals.Gen
import FuzzS19.Gen

/-!
# Comptime-resolved locals: checks against the native results

`ConstLocals.Gen` is the retained translation of `air/0.16.0` (`const_locals.zig`). Sema put the
value of each comptime-known `const` local in a constant global (`mem0` blocks 0 and 1) and left
the local's dead `alloc` and stores as `bitcast`s of address 0, which the translation drops. Each
`#guard` is the value that `zig test const_locals.zig` checks natively. `FuzzS19.Gen` is the
retained translation of the original fuzz reproducer `fuzz_s19.zig`, whose `entry` returns 0.
-/

open ConstLocals Zig

namespace ConstLocalsChecks

/-- The value of a run from program start, if it returns. -/
def okNat {α : Type} (toNat : α → Nat) (r : Result α) : Option Nat :=
  match r.run with
  | some (.ok v) => some (toNat v)
  | _ => none

-- Block 1 is `live`'s local: the constant global of `U.b (-7)`, at a nonzero address.
#guard (mem0.blocks[1]?.map fun b => (b.bytes == Enc.encode (U.b (-(7 : BitVec 32))),
  b.align, b.kind == .constGlobal, decide (0 < b.addr))) == some (true, 4, true, true)
-- The shrunk fuzz case stays pointer-free (`Result`, no memory) and returns 0.
#guard okNat BitVec.toNat (dead 5 9) == some 0
-- A read through the pointer to `live`'s local, the global base `⟨some 1, 0⟩`, gives the
-- native value `@bitCast(@as(i32, -7)) +% 5`.
#guard okNat BitVec.toNat ((read (⟨some 1, 0⟩ : Ptr) 5).run' mem0) == some 4294967294
#guard okNat BitVec.toNat ((live 5).run' mem0) == some 4294967294
#guard okNat BitVec.toNat ((stack 9).run' mem0) == some 10
#guard okNat BitVec.toNat ((entry 5 9).run' mem0) == some 8
#guard okNat BitVec.toNat ((roundTrip 8).run' mem0) == some 13

-- The original reproducer: pointer-free, no `mem0`, returns 0 like the native build.
#guard okNat BitVec.toNat (FuzzS19.entry 3 4) == some 0

end ConstLocalsChecks
