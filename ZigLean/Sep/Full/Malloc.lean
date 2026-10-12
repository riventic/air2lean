import ZigLean.Os.Malloc
import ZigLean.Sep.Full.Block
import ZigLean.Sep.AllocSpec.Region

/-!
# macOS `malloc`/`free` in the full-state logic (premise OSM-02; proof-only)

The rules of the libc allocator model (`ZigLean/Os/Malloc.lean`, `docs/os-threads.md`), for every
failure policy and every slack (`Os.Env.mallocSlack`). Libc's `malloc` and `free` are OS
primitives of the trusted base, not an allocator model: the rules follow from the model heap's
`rawAlloc`/`poisonFree` rules (`Full/Block`).

* `FTotalTriple.malloc`: `malloc(n)`, `n > 0`, gives `null` and nothing, or a new heap block of
  `S ≥ n` undefined bytes at a 16-byte-aligned address with its full extent (`fmallocPost`).
* `FTotalTriple.mallocZero`: `malloc(0)`. macOS returns a fresh, freeable pointer to a 16-byte
  block (`malloc_size(malloc(0)) = 16` on aarch64-macos); the model gives `0 + mallocSlack i 0`
  bytes, so the slack covers it. The rule covers every slack: a block of `S > 0` bytes is owned as
  for `n > 0`; a block of no bytes is only a pointer to offset 0 of a new block, since the logic
  has no resource for a block without bytes (an extent needs a live byte). So `free(malloc(0))`
  is provable exactly when the slack is known to be positive; otherwise the client cannot free it
  (conservative, never unsound).
* `FTotalTriple.mfree`: `free(p)` of a whole heap block (offset 0) takes back its bytes and its
  extent; `FTotalTriple.mfreeNull`: `free(null)` does nothing.
* `Os.Darwin.free_dead`, `Os.Darwin.free_inner`: a double free and a free of an inner pointer are
  `.illegal` (facts of the OS model), with kernel-checked examples.

All rules are total: `rawAlloc` checks the room in the address space itself (`null` without
room), so `malloc` never throws.
-/

namespace Zig
namespace Full

open FAssn Os

/-- `malloc` is `rawAlloc` of the request plus the slack of this attempt. -/
theorem _root_.Zig.Os.Darwin.malloc_eq (env : Os.Env) (n : BitVec 64) (m : Mem) :
    (Darwin.malloc env n).run m =
      (rawAlloc (n.toNat + env.mallocSlack m.allocs n.toNat) Darwin.mallocAlign).run m := rfl

/-- What `malloc(n)` returns: `null` and nothing, or a new heap block of `S ≥ n` undefined bytes at
a 16-byte-aligned address, owned from offset 0 as a region with its full extent. -/
def fmallocPost (n : Nat) : Option Ptr → FAssn
  | none => emp
  | some p => FAssn.ex fun S : Nat => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ n ≤ S ∧ A % Darwin.mallocAlign = 0⟫ ⋆
        (up (regionIn p A S .heap Darwin.mallocAlign (Array.replicate S .undef)) ⋆ bext b S .heap)

/-- `malloc` from a memory `m`, as the `rawAlloc` of the slack that `m` decides. -/
theorem malloc_of_rawAlloc {Q : Option Ptr → FAssn} (env : Os.Env) (n : BitVec 64)
    (h : ∀ k, FTotalTriple emp (rawAlloc (n.toNat + env.mallocSlack k n.toNat) Darwin.mallocAlign) Q) :
    FTotalTriple emp (Darwin.malloc env n) Q :=
  FTotalTriple.of_runEq fun m _ _ hh _ hs =>
    ⟨_, m, Os.Darwin.malloc_eq env n m, hh, hs, h m.allocs⟩

/-- `rawAlloc` of `S ≥ n` bytes, `S > 0`, gives what `malloc(n)` returns. -/
theorem rawAlloc_fmalloc {n S : Nat} (hS : n ≤ S) (hpos : 0 < S) :
    FTotalTriple emp (rawAlloc S Darwin.mallocAlign) (fmallocPost n) :=
  (FTotalTriple.rawAlloc _ _ (by decide) hpos).post fun v r h => by
    cases v with
    | none => exact h
    | some p =>
      obtain ⟨A, b, h⟩ := h
      obtain ⟨⟨h1, h2, h3⟩, h⟩ := sep_lift.mp h
      refine ⟨S, A, b, sep_lift.mpr ⟨⟨h1, h2, hS, h3⟩, sep_mono_left (fun _ hu => ?_) h⟩⟩
      exact ⟨⟨by rw [h2]; simpa using h3, nofun, hu.1⟩, hu.2⟩

/-- **`malloc(n)`, `n > 0`** (total, every failure policy and slack): `null` and nothing, or a
new heap block of at least `n` bytes. -/
@[fsym] theorem FTotalTriple.malloc (env : Os.Env) (n : BitVec 64) (hn : 0 < n.toNat) :
    FTotalTriple emp (Darwin.malloc env n) (fmallocPost n.toNat) :=
  malloc_of_rawAlloc env n fun _ => rawAlloc_fmalloc (Nat.le_add_right _ _) (by omega)

/-- What `malloc(0)` returns: `null` and nothing, a block of `S > 0` bytes as `fmallocPost`, or a
pointer to offset 0 of a new block without bytes, which nothing owns (module doc). -/
def fmallocZeroPost : Option Ptr → FAssn
  | none => emp
  | some p => fun r => fmallocPost 0 (some p) r ∨ ⟪p.block.isSome ∧ p.off = 0⟫ r

/-- **`malloc(0)`** (total, every failure policy and slack): as `malloc(n)` when the slack gives
the block bytes, else a pointer to a new block without bytes (module doc). -/
theorem FTotalTriple.mallocZero (env : Os.Env) :
    FTotalTriple emp (Darwin.malloc env 0) fmallocZeroPost := by
  refine malloc_of_rawAlloc env 0 fun k => ?_
  generalize (0 : BitVec 64).toNat + env.mallocSlack k (0 : BitVec 64).toNat = s
  cases s with
  | zero =>
    refine (FTotalTriple.rawAllocZero _ (by decide)).post fun v r h => ?_
    cases v with
    | none => exact h.2
    | some p => exact .inr ⟨h.1 p rfl, h.2⟩
  | succ s =>
    refine (rawAlloc_fmalloc (n := 0) (Nat.zero_le _) (Nat.succ_pos s)).post fun v r h => ?_
    cases v with
    | none => exact h
    | some p => exact .inl h

/-- The live heap block that `p` points to the start of: the block of an owned whole heap block. -/
theorem heapBlockAt_run {m : Mem} {r rF : Res} {R : FAssn} {p : Ptr} {b : BlockId} {S : Nat}
    (hh : Holds m r rF) (h : (bext b S .heap ⋆ R) r) (hpb : p.block = some b) (h0 : p.off = 0) :
    ∃ blk, (Darwin.heapBlockAt p).run m = pure (blk, m) ∧ blk.bytes.size = S := by
  obtain ⟨blk, hb, hl, hsz, hK, -⟩ := hh.bauth h
  exact ⟨blk, by simp [Darwin.heapBlockAt, zig_unfold, hpb, hb, hl, hK, h0], hsz⟩

/-- **`free(p)` of a whole heap block** (total): its bytes (a region, any alignment label) and its
full extent go. -/
@[fsym] theorem FTotalTriple.mfree {p : Ptr} {A S a : Nat} {bs : Array Byte} {b : BlockId}
    (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) :
    FTotalTriple (up (regionIn p A S .heap a bs) ⋆ bext b S .heap) (Darwin.free (some p))
      (fun _ => emp) :=
  FTotalTriple.of_runEq fun m r rF hh hp hs => by
    obtain ⟨blk, hblk, hsz⟩ := heapBlockAt_run hh (sep_comm hp) hpb h0
    refine ⟨Zig.poisonFree p S, m, ?_, hh, hs, (FTotalTriple.poisonFree hpb hS h0).pre
      fun _ h => sep_mono_left (fun _ hu => ⟨hu.1.2.2, hu.2⟩) h⟩
    simp only [StateT.run] at hblk ⊢
    simp [Darwin.free, zig_unfold, hblk, hsz]

/-- **`free(null)`** does nothing. -/
@[fsym] theorem FTotalTriple.mfreeNull : FTotalTriple emp (Darwin.free none) (fun _ => emp) :=
  FTotalTriple.ret (Q := fun _ => emp) ()

/-- `free` of a pointer into a dead block (a double free, a free after a free) is `.illegal`. -/
theorem _root_.Zig.Os.Darwin.free_dead {m : Mem} {p : Ptr} {b : BlockId} {blk : Block} (hb : p.block = some b)
    (hblk : m.blocks[b]? = some blk) (hl : blk.live = false) :
    ((Darwin.free (some p)).run m).run = some (.error .illegal) := by
  simp [Darwin.free, Darwin.heapBlockAt, zig_unfold, hb, hblk, hl, ExceptT.run]

/-- `free` of a pointer that is not at offset 0 of its block is `.illegal`. -/
theorem _root_.Zig.Os.Darwin.free_inner {m : Mem} {p : Ptr} (h0 : p.off ≠ 0) :
    ((Darwin.free (some p)).run m).run = some (.error .illegal) := by
  simp only [Darwin.free, Darwin.heapBlockAt]
  cases hb : p.block with
  | none => simp [zig_unfold, ExceptT.run]
  | some b =>
    cases hblk : m.blocks[b]? with
    | none => simp [zig_unfold, hblk, ExceptT.run]
    | some blk => simp [zig_unfold, hblk, h0, ExceptT.run]

/-! ## Kernel-checked examples (`aarch64-macos`) -/

namespace MallocExamples

def isIllegal {α : Type} (c : MemM α) : Bool :=
  match (c.run {}).run with
  | some (.error .illegal) => true
  | _ => false

def returns {α : Type} (c : MemM α) : Bool :=
  match (c.run {}).run with
  | some (.ok _) => true
  | _ => false

def mallocOk (env : Os.Env) (n : BitVec 64) : MemM Ptr := do
  match ← Darwin.malloc env n with
  | some p => pure p
  | none => throw .panic

/-- A store into a fresh block returns. -/
example : returns (do let p ← mallocOk Os.Env.example 8; store 1 (p.add 7) (1 : BitVec 8)) = true := by
  decide +kernel

/-- A double free is illegal. -/
example : isIllegal (do let p ← mallocOk Os.Env.example 8; Darwin.free (some p); Darwin.free (some p)) =
    true := by
  decide +kernel

/-- Use after free is illegal. -/
example : isIllegal (do let p ← mallocOk Os.Env.example 8; Darwin.free (some p); load (BitVec 8) 1 p) =
    true := by
  decide +kernel

/-- Freeing an inner pointer, or a stack block, is illegal. -/
example : isIllegal (do let p ← mallocOk Os.Env.example 8; Darwin.free (some (p.add 1))) = true := by
  decide +kernel
example : isIllegal (do let p ← alloc .stack 8 8; Darwin.free (some p)) = true := by decide +kernel

/-- `malloc(0)` is a fresh, freeable pointer, with no slack (no bytes) and with macOS's 16 bytes. -/
example : returns (do let p ← mallocOk Os.Env.example 0; Darwin.free (some p)) = true := by
  decide +kernel
example : returns (do
    let p ← mallocOk { Os.Env.example with mallocSlack := fun _ _ => 16 } 0
    store 1 (p.add 15) (1 : BitVec 8); Darwin.free (some p)) = true := by
  decide +kernel

/-- A byte of a `malloc(0)` block without slack is out of bounds. -/
example : isIllegal (do let p ← mallocOk Os.Env.example 0; load (BitVec 8) 1 p) = true := by
  decide +kernel

end MallocExamples

end Full
end Zig
