import ZigLean.Sep.Full.Region
import ZigLean.Sep.Full.Const
import ZigLean.Bit

/-!
# The `std.mem.Allocator` wrappers over `FAllocSpec` (library `Full/Wrappers`)

The contracts of the `std.mem.Allocator` wrappers (`alloc`, `alignedAlloc`, `create`, `destroy`,
`free`, `dupe`, `allocSentinel`, `realloc`) are stated on the **generated** wrappers of a translated
program (`--allocator-model translated`), for every allocator invariant `I` with
`FAllocSpec L impl ctx I` of the allocator behind the `Allocator` value (`docs/alloc-spec.md`,
§The wrappers over `FAllocSpec`). There is no hand-written model of the wrappers: `fsym` walks
their generated code, with the allocator's `FAllocSpec` fields as the rules of the vtable calls.

This module is what such a proof needs beyond the step rules of `AutoRules`:

* the postconditions of the contracts, over an `FAllocInv` (`owned`, `allocResult`,
  `sliceResult`);
* the step rule (`@[fsym]`) of `@returnAddress()` (`returnAddress`); the byte operations on
  regions (`@memset`, item loads and stores, `@memcpy`, the pointer order of its aliasing check)
  are the region library's (`Full/Region`).
-/

namespace Zig
namespace Full

open FAssn

/-! ## Postconditions -/

namespace FAllocInv

variable (I : FAllocInv)

/-- The bytes `bs` at `p` that `I`'s allocator granted with alignment `2 ^ k`; nothing for zero
bytes (a zero-length allocation is the constant pointer of its alignment, no grant). -/
def owned (k : Nat) (p : Ptr) (bs : Array Byte) : FAssn :=
  if bs.size = 0 then emp else I.granted p k bs

/-- The result of an allocation of `n` bytes with alignment `2 ^ k` that returns a pointer: a
grant of `n` undefined bytes, or `error.OutOfMemory` and nothing. -/
def allocResult (k n : Nat) : Except ErrName Ptr → FAssn
  | .ok p => I.owned k p (Array.replicate n .undef)
  | .error e => ⟪e = "OutOfMemory"⟫

/-- The result of an allocation of `len` items of `n` bytes in all that returns a slice. -/
def sliceResult (k : Nat) (len : BitVec 64) (n : Nat) : Except ErrName Slice → FAssn
  | .ok s => ⟪s.len = len⟫ ⋆ I.owned k s.ptr (Array.replicate n .undef)
  | .error e => ⟪e = "OutOfMemory"⟫
theorem owned_zero {k : Nat} {p : Ptr} {bs : Array Byte} (h : bs.size = 0) : I.owned k p bs = emp := by
  simp [owned, h]

theorem owned_pos {k : Nat} {p : Ptr} {bs : Array Byte} (h : bs.size ≠ 0) :
    I.owned k p bs = I.granted p k bs := by
  simp [owned, h]

end FAllocInv

/-! ## Normalization of the wrappers' constants -/

theorem ctz_lit {n m : Nat} {a : BitVec n} {r : BitVec m} (h : decide (Zig.ctz m a = r) = true) :
    Zig.ctz m a = r := of_decide_eq_true h

open Lean Meta Simp in
/-- `@ctz` of a word literal (`mem.Alignment.fromByteUnits` of a constant alignment): its value. -/
simproc [fsym_norm] reduceLitCtz (Zig.ctz _ _) := fun e => do
  unless e.isAppOfArity ``Zig.ctz 3 do return .continue
  let args := e.getAppArgs
  let some m := (← instantiateMVars args[1]!).nat? | return .continue
  let some ⟨w, a⟩ ← getBitVecValue? args[2]! | return .continue
  let r := (List.range w).find? (fun i => a.toNat.testBit i) |>.getD w
  let rhs := toExpr (BitVec.ofNat m r)
  let hTy ← mkEq (← mkDecide (← mkEq e rhs)) (mkConst ``Bool.true)
  let pf := mkAppN (mkConst ``ctz_lit) #[mkNatLit w, mkNatLit m, args[2]!, rhs,
    ← mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true)) hTy]
  return .visit { expr := rhs, proof? := some pf }

open Lean Meta Simp in
/-- `enumOf` of a closed `Option` (a generated enum's `ofInt?` of a constant): `pure` of its
value, by evaluation. -/
dsimproc [fsym_norm] reduceEnumOfLit (Zig.enumOf _) := fun e => do
  unless e.isAppOfArity ``Zig.enumOf 2 do return .continue
  let o := e.appArg!
  if o.hasFVar || o.hasMVar then return .continue
  let o' ← whnfD o
  unless o'.isAppOfArity ``Option.some 2 do return .continue
  return .visit (← mkAppOptM ``Pure.pure #[mkConst ``Zig.Result, none, e.getAppArgs[0]!, o'.appArg!])

open Lean Meta Simp in
/-- `Zig.val` of a word literal (the `Int` that an enum's `ofInt?` gets): its value. -/
dsimproc [fsym_norm] reduceValLit (Zig.val _ _) := fun e => do
  unless e.isAppOfArity ``Zig.val 3 do return .continue
  let args := e.getAppArgs
  let some ⟨_, a⟩ ← getBitVecValue? args[2]! | return .continue
  let s := args[1]!
  let v : Int ← if s.isConstOf ``Bool.true then pure a.toInt
    else if s.isConstOf ``Bool.false then pure a.toNat else return .continue
  return .done (toExpr v)

/-! ## Facts -/

/-- A read-only typed value (a vtable entry): the block of its pointer, a nonnegative offset. -/
@[fsym_facts] theorem Auto.facts_cpts {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T} :
    Auto.AtomFacts (cpts p a v) ((∃ b, p.block = some b) ∧ 0 ≤ p.off) := by
  rintro r ⟨-, -, -, -, -, -, -, b, hb, h0, -⟩; exact ⟨⟨b, hb⟩, h0⟩

/-! ## Step rules -/

namespace FTotalTriple

variable {P : FAssn}

/-- **`@returnAddress()`** reads the oracle; every assertion stays. -/
@[fsym] theorem returnAddress : FTotalTriple P Zig.returnAddress (fun _ => P) :=
  FTotalTriple.of_run fun m r rF hh hp hs =>
    ⟨_, { m with arbitraryNext := m.arbitraryNext + 1 }, r, rfl,
      Holds.congrMem (m := m) (m' := { m with arbitraryNext := m.arbitraryNext + 1 }) rfl rfl hh, hp,
      ⟨⟨hs.1.single⟩, hs.2.1, hs.2.2⟩⟩

end FTotalTriple

end Full
end Zig
