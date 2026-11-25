import ExternAbi.Gen

/-! The C-ABI conversion at a bound extern call (X01, `ZigLean/Mem/Abi.lean`), on `abi.c` through
`zig translate-c` and Zig 0.17.1's libc. The defined cases evaluate to the native results
(`expected.txt`, from `native.zig` on x86_64-linux); each value the definition's type does not
admit is `.illegal`:

* `strcmp` (`[*c]const u8` → `[*:0]const c_char`): a buffer without a 0 byte in its object, and
  null;
* `memrchr` (`?*const anyopaque` → `*const anyopaque`): null;
* `malloc_usable_size` (`?*anyopaque` → `?[*]align(16) u8`): an address that 16 does not divide.

Null into `malloc_usable_size`'s optional parameter passes (case 0), and `strrchr`'s null result
becomes a null C pointer (`last_case 0 'z'`). -/
namespace ExternAbi.Eval

private def run {α : Type} (m : Zig.MemM α) : Option (Except Zig.Error α) :=
  (m.run' (ExternAbi.mem0 .fresh)).run

private def ok {α : Type} [BEq α] (m : Zig.MemM α) (v : α) : Bool :=
  match run m with
  | some (.ok x) => x == v
  | _ => false

private def illegal {α : Type} (m : Zig.MemM α) : Bool :=
  match run m with
  | some (.error .illegal) => true
  | _ => false

-- cmp_case 0 -1 1; 3: no sentinel, 4: null
#guard ok (ExternAbi.cmp_case 0#32) 0#32
#guard ok (ExternAbi.cmp_case 1#32) (-1 : BitVec 32)
#guard ok (ExternAbi.cmp_case 2#32) 1#32
#guard illegal (ExternAbi.cmp_case 3#32)
#guard illegal (ExternAbi.cmp_case 4#32)
-- last_case 10 -1 15 16
#guard ok (ExternAbi.last_case 0#32 44#32) 10#64
#guard ok (ExternAbi.last_case 0#32 122#32) (-1 : BitVec 64)
#guard ok (ExternAbi.last_case 1#32 97#32) 15#64
#guard ok (ExternAbi.last_case 0#32 0#32) 16#64
-- rfind_case 15; 1: null
#guard ok (ExternAbi.rfind_case 0#32) 15#64
#guard illegal (ExternAbi.rfind_case 1#32)
-- usable_case 0 100; 2: misaligned
#guard ok (ExternAbi.usable_case 0#32 7#32) 0#64
#guard ok (ExternAbi.usable_case 1#32 100#32) 100#64
#guard illegal (ExternAbi.usable_case 2#32 100#32)

end ExternAbi.Eval
