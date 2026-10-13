import TryAliases.Gen
import TryPointers.AliasProofs

/-! Whole-union memory rules for the generated `twoPaths` and `resetOnError` definitions,
translated from the hand-written `try_aliases.*` AIR (compiler export pending).

* `twoPaths p p y`: one union reached through both pointer-try operands. Both results address
  the same payload; the write through the first is what the second reads.
* `twoPaths a b y` with separately owned unions: the write lands only in `a`, the read comes
  only from `b`. An error on either path writes nothing and returns that path's error.
* `resetOnError`: on error the error name is read before the `errdefer` overwrites the
  addressed union with `.ok fallback`; the returned error is the original one. Success
  returns the payload address and leaves the union unchanged.

The triples are total full-state ones, each proved by `fsym` on each shape of the unions; the
errors' membership in the declared domain is the one side goal it leaves. -/

open Zig
open scoped Zig
open Zig.Full Zig.Full.FAssn
open TryPointersAliasProofs

namespace TryAliasesProofs

/-! ## One union, two pointer paths -/

theorem twoPaths_same_owned (p : Ptr) (u : Except ErrName (BitVec 8)) (y : BitVec 8)
    (hdom : admitted u) :
    FTotalTriple (up (pts p 2 u)) (TryAliases.twoPaths p p y)
      (fun r => ⟪r = writeView y u⟫ ⋆ up (pts p 2 (writeView y u))) := by
  have hd := admitted_all hdom
  unfold TryAliases.twoPaths; cases u <;> fsym <;> exact hd

/-! ## Two separately owned unions -/

/-- The result of `twoPaths a b y`: the first error, else the second union's payload. -/
def twoResult : Except ErrName (BitVec 8) → Except ErrName (BitVec 8) → Except ErrName (BitVec 8)
  | .error e, _ => .error e
  | .ok _, .error e => .error e
  | .ok _, .ok z => .ok z

/-- The first union afterwards: written only when both pointer-tries succeed. -/
def firstAfter (y : BitVec 8) : Except ErrName (BitVec 8) → Except ErrName (BitVec 8) →
    Except ErrName (BitVec 8)
  | .ok _, .ok _ => .ok y
  | u, _ => u

theorem twoPaths_distinct_owned (a b : Ptr) (u w : Except ErrName (BitVec 8)) (y : BitVec 8)
    (hu : admitted u) (hw : admitted w) :
    FTotalTriple (up (pts a 2 u) ⋆ up (pts b 2 w)) (TryAliases.twoPaths a b y)
      (fun r => ⟪r = twoResult u w⟫ ⋆ (up (pts a 2 (firstAfter y u w)) ⋆ up (pts b 2 w))) := by
  have hu' := admitted_all hu
  have hw' := admitted_all hw
  unfold TryAliases.twoPaths; cases u <;> cases w <;> fsym <;> first | exact hu' | exact hw' | rfl

/-! ## errdefer rewriting the addressed union -/

/-- The union after `resetOnError p f`: overwritten with `.ok f` on the error path only. -/
def resetAfter (f : BitVec 8) : Except ErrName (BitVec 8) → Except ErrName (BitVec 8)
  | .ok x => .ok x
  | .error _ => .ok f

theorem resetOnError_owned (p : Ptr) (u : Except ErrName (BitVec 8)) (f : BitVec 8)
    (hdom : admitted u) :
    FTotalTriple (up (pts p 2 u)) (TryAliases.resetOnError p f)
      (fun r => ⟪r = tryView (BitVec 8) p u⟫ ⋆ up (pts p 2 (resetAfter f u))) := by
  have hd := admitted_all hdom
  unfold TryAliases.resetOnError; cases u <;> fsym <;> exact hd

end TryAliasesProofs
