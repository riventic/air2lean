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

/-! ## Memory-region contracts (A01, premise ASM-06)

An allowlisted block whose instructions access memory through pointer operands (`rep stosb`,
`rep movsb`, with a `"memory"` clobber) declares each region it reads or writes: a pointer
operand and a byte length taken from an integer operand (`Air2Lean/AsmAllowlist.lean`'s
`AsmRegion`). The wrapper reads each read region (`readRegion`) before the opaque and passes the
bytes to it; after the alias guard over every written location, it writes each write region
(`writeRegion`) with the bytes the opaque returns. Each access is the model's checked access:
bounds, liveness, writability and races. A pointer output is its old value moved by an opaque
offset (`movePtr`): its block, so its provenance, is kept. -/

/-- The `n` bytes at `p`, read as one access; no access for `n = 0` (the instruction then
touches no memory, whatever `p` holds). -/
def readRegion (p : Ptr) (n : Nat) : MemM (Array Byte) :=
  if n = 0 then pure #[] else loadBytes p n 1

/-- `bs` cut or padded (`undef`) to exactly `n` bytes. -/
def fitBytes (n : Nat) (bs : Array Byte) : Array Byte :=
  (bs.extract 0 n) ++ Array.replicate (n - bs.size) .undef

theorem fitBytes_size (n : Nat) (bs : Array Byte) : (fitBytes n bs).size = n := by
  simp [fitBytes]; omega

/-- Write exactly `n` bytes at `p`: the opaque's bytes for this region, cut or padded to `n`. No
access for `n = 0`. -/
def writeRegion (p : Ptr) (n : Nat) (bs : Array Byte) : MemM Unit :=
  if n = 0 then pure () else storeBytes p 1 (fitBytes n bs)

/-- A pointer output: the old pointer moved by the opaque's signed offset. -/
def movePtr (p : Ptr) (delta : BitVec 64) : Ptr := p.add delta.toInt

/-! ## Environment reads (A01, premise ASM-05)

`rdtsc` and `rdrand` read state outside the model: a counter, an entropy source. An allowlisted
entry with `envRead` semantics makes each output a fresh query of the explicit oracle
`Mem.arbitrary` (`arbitraryWord`). Two reads are two queries, never one repeatable value; a
theorem about every initial `Mem` holds for every sequence of answers, so it claims nothing
about the counter's order or the randomness of the source. -/

/-- One environment-read output of width `w`: the next oracle word, cut to `w` bits. -/
def envWord (w : Nat) : MemM (BitVec w) := do
  pure ((← arbitraryWord).setWidth w)

theorem envWord_run (w : Nat) (m : Mem) :
    (envWord w).run m = pure ((m.arbitrary.getD m.arbitraryNext 0).setWidth w,
      { m with arbitraryNext := m.arbitraryNext + 1 }) := by
  simp [envWord, arbitraryWord, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, set, StateT.set, MonadStateOf.set, pure, StateT.pure, ExceptT.pure, ExceptT.mk,
    ExceptT.bind, ExceptT.bindCont]

end Zig.Asm
