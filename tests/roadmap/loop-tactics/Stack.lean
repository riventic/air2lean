import Proofs.Pointers.Gen
import ZigLean.Sep.Stack
import ZigLean.Sep.Witness
import ZigLean.RecTemplate
import ZigLean.Range

/-!
# Memory-backed recursion under the stack budget (P03, STK-01)

`Pointers.addDown acc n` (`examples/pointers/pointers.zig`) adds `n, n-1, …, 1` to `*acc` by
recursion. It uses memory, so its generated body charges a frame (`Zig.enterFrame 0`, 16 bytes)
on entry and releases it on return (MM-5). Under a stack budget a deep enough call throws
`.stackOverflow`; so no `TotalTriple` of it holds (`addDown_not_total`), and its total
correctness is a `TotalTripleStk` with the room it needs: `n + 1` frames (`addDown_total`).

The proof is the general machinery only: `rec_template` infers the measure `n.toNat` from the
recursive call and supplies the induction,
`sep_unfold`/`sep_step`/`sep_steps` walk the generated body (the frame bracket, the load, the
checked add, the store, the checked sub and the recursive call through `ih`), and the module
supplies the specification, the measure and the arithmetic facts of its checked operations.

On a memory without a budget (every generated `mem0`) the same theorem is the `TotalTriple`
conclusion (`addDown_unbudgeted`); that statement assumes STK-01 for the native stack, and the
need `(n + 1) * frameBase` is the model's estimate of the depth it assumes.
-/

namespace StackTest
open Zig Assn

/-- `n + (n - 1) + … + 1`. -/
def tri : Nat → Nat
  | 0 => 0
  | k + 1 => (k + 1) + tri k

/-- `addDown acc n` adds `tri n` to `*acc` (no overflow under the range premise) and needs room
for `n + 1` frames of `frameBase` bytes. -/
theorem addDown_total (acc : Ptr) : ∀ (n : BitVec 32) (v : BitVec 64),
    v.toNat + tri n.toNat < 2 ^ 64 →
    TotalTripleStk (pts acc 8 v) (Pointers.addDown acc n)
      (fun _ => pts acc 8 (BitVec.ofNat 64 (v.toNat + tri n.toNat))) ((n.toNat + 1) * frameBase) 0 := by
  -- The measure `n.toNat` is inferred from the recursive call `addDown acc (n - 1)`.
  rec_template _ unfolding Pointers.addDown
  intro v hfit
  sep_unfold
  sep_step
  by_cases hn0 : n = (0 : BitVec 32)
  · sep_unfold [beq_iff_eq, hn0]
    sep_step
    sep_ret
    intro h hp
    subst hn0
    simpa [tri] using hp
  · sep_unfold [beq_iff_eq, hn0]
    -- The facts of the checked operations: `n - 1` and `*acc + n` do not overflow.
    have hn : (n - 1).toNat = n.toNat - 1 := Zig.toNat_sub_one n hn0
    have hpos : 0 < n.toNat := Nat.pos_of_ne_zero fun h => hn0 (BitVec.eq_of_toNat_eq (by simpa using h))
    have htri : tri n.toNat = n.toNat + tri (n.toNat - 1) := by
      obtain ⟨k, hk⟩ : ∃ k, n.toNat = k + 1 := ⟨n.toNat - 1, by omega⟩
      rw [hk]; rfl
    have hw : (n.setWidth 64).toNat = n.toNat := Zig.toNat_setWidth_of_le (by decide)
    have hadd : Zig.add false v (n.setWidth 64) = pure (v + n.setWidth 64) :=
      Zig.add_unsigned_of_lt (by omega)
    have hsub : Zig.sub false n 1 = pure (n - 1) := Zig.sub_unsigned_of_le (by simp; omega)
    have hv : (v + n.setWidth 64).toNat = v.toNat + n.toNat := by
      rw [Zig.toNat_add_of_lt (by omega), hw]
    sep_steps [Zig.intCast_unsigned_widen n 64 (by decide), hadd, hsub]
    -- The recursive call: a smaller measure, and its `n` frames fit in the room that is left.
    sep_step using ih (n - 1) (by omega) (v + n.setWidth 64) (by rw [hv, hn]; omega)
    sep_step
    sep_ret
    intro h hp
    rw [hv, hn, show v.toNat + n.toNat + tri (n.toNat - 1) = v.toNat + tri n.toNat by omega] at hp
    exact sep_emp.mp hp

/-- Without a budget (`stackLimit = none`, every generated `mem0`) `addDown` returns the sum
and keeps the frame: the `TotalTriple` conclusion, which assumes STK-01 for the native stack. -/
theorem addDown_unbudgeted (acc : Ptr) (n : BitVec 32) (v : BitVec 64)
    (hfit : v.toNat + tri n.toNat < 2 ^ 64) {m : Mem} {hP hF : Heap} (hd : Heap.Disjoint hP hF)
    (hm : m.heap = hP ∪ hF) (hp : pts acc 8 v hP) (hs : m.Seq) (hl : m.stackLimit = none) :
    ∃ u m' hQ, (Pointers.addDown acc n).run m = pure (u, m') ∧ Heap.Disjoint hQ hF ∧
      m'.heap = hQ ∪ hF ∧ pts acc 8 (BitVec.ofNat 64 (v.toNat + tri n.toNat)) hQ ∧ m'.Seq :=
  (addDown_total acc n v hfit).unbudgeted hd hm hp hs hl

/-- The memory with `*p0 = v` and no room on the stack. -/
def noRoom (v : BitVec 64) : Mem := { Witness.mem1 (Enc.encode v) with stackLimit := some 0 }

/-- With no room for its first frame, `addDown` overflows, for every `n`. -/
theorem addDown_overflow (n : BitVec 32) (v : BitVec 64) :
    ((Pointers.addDown Witness.p0 n).run (noRoom v)).run = some (.error .stackOverflow) := by
  rw [Pointers.addDown.eq_1]
  exact enterFrame_bind_overflow rfl (by simp [noRoom, frameBase])

/-- So no `TotalTriple` of `addDown` holds, whatever the postcondition: its total correctness
needs the stack premise of `TotalTripleStk`. -/
theorem addDown_not_total (n : BitVec 32) (v : BitVec 64) (Q : Unit → Assn) :
    ¬ TotalTriple (pts Witness.p0 8 v) (Pointers.addDown Witness.p0 n) Q :=
  not_total_of_overflow (m := noRoom v) (Heap.disjoint_empty _)
    (by simp [noRoom, Witness.mem1]; rfl) (Witness.mem1_pts' v (by decide))
    ⟨(Witness.mem1_seq (Enc.encode v) .heap).single⟩ (addDown_overflow n v)

/-! ## Mutants of the frame bracket

The walk rejects a body that does not release its frame and a room one byte too small. -/

-- Mutant `frame-not-released`: a body that enters a frame and returns without `leaveFrame`.
example : True := by
  fail_if_success
    have : TotalTripleStk emp (enterFrame 0 >>= fun _ => pure ()) (fun _ => emp) (8 + frameBase) 0 := by
      sep_step
      sep_ret
  trivial

-- Mutant `room-one-byte-short`: the room does not hold the frame.
example : True := by
  fail_if_success
    have : TotalTripleStk emp (enterFrame 0 >>= fun _ => leaveFrame 0 >>= fun _ => pure ())
        (fun _ => emp) (frameBase - 1) 0 := by
      sep_step
      sep_step
      sep_ret
  trivial

-- The unmutated bracket: one frame of room.
example (P : Assn) : TotalTripleStk P (enterFrame 0 >>= fun _ => leaveFrame 0 >>= fun _ => pure ())
    (fun _ => P) frameBase 0 := by
  sep_step
  sep_step
  sep_ret

end StackTest

-- Only the standard axioms: no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`).
/-- info: 'StackTest.addDown_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StackTest.addDown_total

/-- info: 'StackTest.addDown_not_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StackTest.addDown_not_total
