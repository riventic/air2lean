import ZigLean.Mem.Basic

/-!
# Inline asm effect contract (A01, ASM-03)

The translator turns every accepted `assembly` instruction into an `opaque` pure function and an
explicit wrapper (`docs/generated-code.md` §Inline asm). The opaque's type is the contract: it
takes the register inputs and the old value of each read-write (`+r`, `+m`) output, and returns
one value per output. It cannot touch `Mem` or the locals. Every memory effect of the block is
in the wrapper:

1. `Zig.Asm.guard` over the memory locations that the block writes, when there are two or
   more (two lvalue outputs through memory pointers);
2. a load of each read-write output's location, in output order;
3. the opaque call;
4. a store of each lvalue output to its own location, in output order.

So the block writes exactly its declared locations (`Proofs/Asm/Effects.lean` proves the frame
rule) and reads only its declared inputs and read-write locations. Register and flag clobbers
(`cc`, `rax`, …) have no Lean-visible state. A `"memory"` clobber is rejected unless a reviewed
registry entry declares the block has no model-visible effect (`Air2Lean/Check.lean`'s
`asmPureRegistry`).

Two written locations that overlap make the result depend on the instructions' store order,
which the contract does not fix: `guard` throws `.unspecified` (the model chooses no order).
The translator rejects outright two outputs that write the same local.
-/

namespace Zig.Asm

/-- The `n` bytes at `p` and the `k` bytes at `q` share a byte. A pointer without a block shares
nothing (the access through it throws `.illegal` anyway). -/
def overlaps (p : Ptr) (n : Nat) (q : Ptr) (k : Nat) : Bool :=
  match p.block, q.block with
  | some b, some c => b == c && decide (p.off < q.off + k) && decide (q.off < p.off + n)
  | _, _ => false

/-- No two of the locations (pointer, byte size) overlap. -/
def disjoint : List (Ptr × Nat) → Bool
  | [] => true
  | (p, n) :: rest => rest.all (fun (q, k) => !overlaps p n q k) && disjoint rest

/-- The aliasing guard of one asm block: `.unspecified` when two of the locations that it writes
overlap, else nothing (no access is recorded; the stores that follow record theirs). -/
def guard (locs : List (Ptr × Nat)) : MemM Unit :=
  if disjoint locs then pure () else throw .unspecified

theorem guard_of_disjoint {locs : List (Ptr × Nat)} (h : disjoint locs = true) (m : Mem) :
    (guard locs).run m = pure ((), m) := by
  simp [guard, h, StateT.run, pure, StateT.pure, ExceptT.pure, ExceptT.mk]

theorem guard_of_overlap {locs : List (Ptr × Nat)} (h : disjoint locs = false) (m : Mem) :
    (guard locs).run m = throw .unspecified := by
  simp [guard, h, StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift, ExceptT.mk,
    bind, ExceptT.bind, ExceptT.bindCont]

/-- The same pointer twice always overlaps (nonzero sizes, a pointer with a block). -/
theorem disjoint_self {p : Ptr} {b : BlockId} (hb : p.block = some b) {n k : Nat} (hn : 0 < n)
    (hk : 0 < k) : disjoint [(p, n), (p, k)] = false := by
  simp [disjoint, overlaps, hb]
  omega

/-- Two locations in different blocks never overlap. -/
theorem disjoint_pair_of_block_ne {p q : Ptr} {b c : BlockId} (hp : p.block = some b)
    (hq : q.block = some c) (hbc : b ≠ c) (n k : Nat) : disjoint [(p, n), (q, k)] = true := by
  simp [disjoint, overlaps, hp, hq, hbc]

end Zig.Asm
