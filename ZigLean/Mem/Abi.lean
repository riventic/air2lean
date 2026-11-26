import ZigLean.Mem.Null

/-!
# The C-ABI conversion of a pointer at a bound extern call (X01)

An extern declaration and the program's definition of its symbol may type a pointer
differently where the C ABI agrees: `zig translate-c` declares `strcmp` with `[*c]const u8`
and `free` with `?*anyopaque`, and Zig's libc defines them with `[*:0]const c_char` and
`?[*]align(16) u8` (`docs/c-frontend.md` §libc boundary). Natively the value crosses the call
unchanged: a pointer is an address in a register. The model converts it once at the call
(`Air2Lean/Check.lean`'s `externAbiCall` chooses the forms and the requirements, `Emit.lean`
applies them): the source's form becomes a `Ptr` (`ptrOfOptional` for `?*T`, the pointer
itself for `*T`, `[*]T` and a C/allowzero pointer), `abiPtrCheck` checks what the target type
asserts about the value, and the target's form is made from it (`ptrToOptional` for `?*T`, the
pointer itself otherwise). These are the conversions of the cast rules (`ZigLean/Mem/Null.lean`);
`abiPtr_nonNull_eq`, `abiPtr_align_eq` and `abiPtrOpt_eq` state the agreement.

A value that the target type does not admit is illegal behaviour that nothing checks natively:
`.illegal`. The target type asserts
* non-null, for a single or many pointer (not optional, not C/allowzero);
* its alignment, where it is stricter than the source's (`?[*]align(16) u8`);
* its sentinel byte, where the source does not assert the same one (`[*:0]const c_char`): a
  byte of that value at or after the pointer in its live block (`Mem.sentinelFrom`).

A null value has no alignment or sentinel requirement. The test reads the block's bytes
without recording an access (natively nothing reads them at the call), so it changes no state
(`abiPtrCheck_run`). The sentinel test is conservative where the callee would stop earlier (a
`strcmp` that finds a difference before the end of an unterminated buffer): the model says
`.illegal` there, and native code does not fail.

This module holds the definitions that generated code runs; their theorems are in
`ZigLean/Mem/AbiLemmas.lean` (proof-only), so the runtime root does not import the memory lemmas.
-/

namespace Zig

/-- What a C-ABI conversion's target pointer type asserts about a value (`abiPtrCheck`):
`nonNull`, and for a non-null value its alignment (1 asserts nothing) and its sentinel byte. -/
structure AbiPtrReq where
  nonNull : Bool := false
  align : Nat := 1
  sentinel : Option (BitVec 8) := none
  deriving DecidableEq, Repr, Inhabited

/-- The byte `s` lies at or after `p` in `p`'s live block (at or above its first live offset):
the sentinel that a `[*:s]T` of `p` asserts, for an item of one byte. -/
def Mem.sentinelFrom (m : Mem) (p : Ptr) (s : BitVec 8) : Bool :=
  match p.block with
  | none => false
  | some b =>
    match m.blocks[b]? with
    | none => false
    | some blk =>
      blk.live && decide (0 ≤ p.off) && decide (blk.kind.mappedLo ≤ p.off.toNat) &&
        (blk.bytes.extract p.off.toNat blk.bytes.size).any (· == .int s)

/-- `p` satisfies `r` in `m` (module doc). `false` for a pointer into a block that does not
exist, whose address `ptrAddr` refuses too. -/
def Mem.abiPtrOk (m : Mem) (r : AbiPtrReq) (p : Ptr) : Bool :=
  match addrIn m.blocks p with
  | none => false
  | some a =>
    if a = 0 then !r.nonNull
    else decide (a % r.align = 0) && (r.sentinel.all (m.sentinelFrom p ·))

/-- The check of a C-ABI pointer conversion: `.illegal` unless the value satisfies the target
type's requirements (`Mem.abiPtrOk`). -/
def abiPtrCheck (r : AbiPtrReq) (p : Ptr) : MemM Unit := do
  unless (← get).abiPtrOk r p do throw .illegal

/-- A C-ABI conversion to a pointer that is not optional (`*T`, `[*]T`, `[*c]T`). -/
def abiPtr (r : AbiPtrReq) (p : Ptr) : MemM Ptr := do
  abiPtrCheck r p
  pure p

/-- A C-ABI conversion to an optional pointer (`?*T`, `?[*]T`): address zero is `none`. -/
def abiPtrOpt (r : AbiPtrReq) (p : Ptr) : MemM (Option Ptr) := do
  abiPtrCheck r p
  ptrToOptional p

end Zig
