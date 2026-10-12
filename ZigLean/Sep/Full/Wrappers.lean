import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Ops
import ZigLean.Sep.Full.AutoRules
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
* step rules (`@[fsym]`) for the commands of the wrappers' code that touch no allocator:
  `@returnAddress()` (`returnAddress`) and the `@memset(_, undefined)` of fresh memory
  (`memsetUndef`).
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

/-- `@memset` keeps every block (it stores into one live block). -/
theorem Keeps.memset {D : BlockId → Prop} {β : Type} [Enc β] (a : Nat) (p : Ptr) (n : BitVec 64)
    (v : Option β) : Keeps D (Zig.memset a p n v) := by
  unfold Zig.memset
  split
  · exact Keeps.pure' _
  · refine Keeps.bind (Keeps.of_keepsExt fun _ _ _ h => ?_) fun _ =>
      Keeps.bind (Keeps.of_keepsExt fun _ _ _ h => ?_) fun _ => Keeps.storeBytes _ _ _ _
    · obtain ⟨-, rfl⟩ := Conc.Proto.MemM.get_ok h; exact KeepsExt.refl _
    · obtain ⟨-, rfl⟩ := Conc.Proto.MemM.lift_ok h; exact KeepsExt.refl _

namespace FTotalTriple

variable {P : FAssn}

/-- **`@returnAddress()`** reads the oracle; every assertion stays. -/
@[fsym] theorem returnAddress : FTotalTriple P Zig.returnAddress (fun _ => P) :=
  FTotalTriple.of_run fun m r rF hh hp hs =>
    ⟨_, { m with arbitraryNext := m.arbitraryNext + 1 }, r, rfl,
      Holds.congrMem (m := m) (m' := { m with arbitraryNext := m.arbitraryNext + 1 }) rfl rfl hh, hp,
      ⟨⟨hs.1.single⟩, hs.2.1, hs.2.2⟩⟩

/-- A region whose cells carry some size label and some kind of `K`'s normal form: a size-free
form of `regionIn` (`SizeFree`), for lifting the region library's total triples. -/
private def regionAny (p : Ptr) (A S : Nat) (K : BlockKind) (a : Nat) (bs : Array Byte) : Assn :=
  fun h => ∃ A' S' K', (A' = A ∧ K'.norm = K.norm ∧ (A' + p.off.toNat) % a = 0 ∧ K' ≠ .constGlobal) ∧
    bytesAt p A' S' K' bs h

private theorem regionAny_sizeFree {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte} :
    SizeFree (fun _ => none) (regionAny p A S K a bs) :=
  SizeFree.bytesAt_ex fun _ _ K₀ _ K' ⟨h1, h2, h3, h4⟩ hk =>
    ⟨h1, hk.trans h2, h3, fun e => h4 (by
      have hn : K₀.norm = .constGlobal := by rw [← hk, e]; rfl
      clear h1 h2 h3 h4 hk e; revert hn; cases K₀ <;> simp [BlockKind.norm])⟩

private theorem regionAny_of {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte} {h : Heap}
    (hr : regionIn p A S K a bs h) : regionAny p A S K a bs h :=
  ⟨A, S, K, ⟨rfl, rfl, hr.1, hr.2.1⟩, hr.2.2⟩

/-- **`@memset(region, undefined)`** of all `n` bytes of a region: the region's bytes become
undefined (the `@memset` of `allocBytesWithAlignment` and of `free`). -/
@[fsym] theorem memsetUndef {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}
    {n : BitVec 64} (hn : n.toNat = bs.size) :
    FTotalTriple (up (regionIn p A S K a bs)) (Zig.memset (α := BitVec 8) 1 p n none)
      (fun _ => up (regionIn p A S K a (Array.replicate n.toNat .undef))) := by
  have ht : TotalTriple (regionAny p A S K a bs) (Zig.memset (α := BitVec 8) 1 p n none)
      (fun _ => regionAny p A S K a (Array.replicate n.toNat .undef)) := by
    intro m hP hF hd hm hp hst
    obtain ⟨A', S', K', ⟨rfl, hk, hal, hK⟩, hb⟩ := hp
    obtain ⟨v, m', hQ, hr, hd', hm', hq, hs'⟩ :=
      Region.memsetUndefIn (p := p) (A := A') (S := S') (K := K') (a := a) hn m hP hF hd hm ⟨hal, hK, hb⟩ hst
    exact ⟨v, m', hQ, hr, hd', hm', ⟨A', S', K', ⟨rfl, hk, hq.1, hq.2.1⟩, hq.2.2⟩, hs'⟩
  have hl := FTotalTriple.ofTotal_up ht (Tame.memset 1 p n none) regionAny_sizeFree
    (Keeps.memset 1 p n none)
  refine FTotalTriple.eupd_post (hl.pre fun r hr => up_imp (fun _ h => regionAny_of h) hr) fun _ => ?_
  intro m r rF hh hp hs
  obtain ⟨⟨A', S', K', ⟨rfl, hk, hal, hK⟩, hb⟩, hk2, hg⟩ := hp
  exact EUpd.relabel (S := S') (S' := S) hk.symm m r rF hh ⟨⟨hal, hK, hb⟩, hk2, hg⟩ hs

end FTotalTriple

end Full
end Zig
