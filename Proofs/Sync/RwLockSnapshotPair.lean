import Proofs.Sync.RwLockContract

/-!
# Snapshot-pair facts, pending generated-client integration

This file supplies the owned two-load WP boundary and literal result consequence used by
the proposed second client.
It is not a `Sched.run` specification or safety theorem for `rwLockSnapshotPair`.
The source client must first be exported and translated by the qualified ROOT workflow.
Then a client WP proof must establish that both loads retain the same protected count,
release the shared resource, join the writer, and reclaim the stack allocation.
-/

open Zig Zig.Conc Zig.Conc.Proto Sync Assn
open Sync.RwLockRead

namespace Sync.RwLockSnapshotPair

/-- Instantiation of the reusable same-hold contract for the second client's snapshot
fragment. This is a real ownership/WP source candidate, not yet a theorem of the new
exported `rwLockSnapshotPair`: its actual optimized definition is still pending. -/
abbrev snapshot_fragment_wp := @RwLockContract.held_pair_wp

/-- Two observations of the same protected count produce precisely the expected result set.
Equality of the observations is a premise, not an assumption inferred from two lock calls. -/
theorem result_of_same_snapshot {first second : Nat}
    (hfirst : first ≤ 2) (hsame : second = first) :
    BitVec.ofNat 32 (10 * first + second) = 0 ∨
    BitVec.ofNat 32 (10 * first + second) = 11 ∨
    BitVec.ofNat 32 (10 * first + second) = 22 := by
  subst second
  have h : first = 0 ∨ first = 1 ∨ first = 2 := by omega
  rcases h with rfl | rfl | rfl <;> simp

/-- Literal negative oracle for the planned split-acquisition interleaving: first 0,
second 1 yields 1, outside the same-hold result set. This is not a scheduler witness. -/
theorem split_snapshot_result_rejected :
    ¬ ((BitVec.ofNat 32 (10 * 0 + 1) = 0) ∨
       (BitVec.ofNat 32 (10 * 0 + 1) = 11) ∨
       (BitVec.ofNat 32 (10 * 0 + 1) = 22)) := by decide

end Sync.RwLockSnapshotPair
