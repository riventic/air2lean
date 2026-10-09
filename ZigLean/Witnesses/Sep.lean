import ZigLean.Sep
import ZigLean.Sep.Witness
import ZigLean.Sep.Array.Reassemble
import ZigLean.Sep.Cost
import ZigLean.Sep.LoopTemplate

/-!
# Non-vacuity and liveness witnesses: separation-logic rules

Concrete arguments, an admissible memory and (for a partial triple) a returning run for the
rules of `ZigLean/Sep/*.lean` (`docs/claim-strength.md`). A rule's run is evaluated by the
kernel on the memory (`ok_of_okb (by decide +kernel)`), or follows from the rule's total
version (`Live.of_total`) where the program is a `Zig.loop`: a `partial_fixpoint`, which the
kernel does not unfold.
-/

namespace Zig.Witness

open Assn

/-! ## `Triple` and `TotalTriple` (`ZigLean/Sep/Triple.lean`, `ZigLean/Sep/Total.lean`) -/

nonvacuity_witness TotalTriple.ret := ⟨Unit, fun _ => emp, (), Admit.emp⟩
nonvacuity_witness TotalTriple.of_run :=
  ⟨Unit, emp, fun _ => emp, pure (), TotalTriple.ret (Q := fun _ => emp) (), Admit.emp⟩
nonvacuity_witness TotalTriple.load :=
  ⟨BitVec 32, inferInstance, p0, 4, 0, by decide +kernel, Admit.of_heap pts32 (mem1_seq _ _)⟩
nonvacuity_witness TotalTriple.store :=
  ⟨BitVec 32, inferInstance, inferInstance, p0, 4, 0, by decide +kernel, 1,
    Admit.of_heap pts32 (mem1_seq _ _)⟩
nonvacuity_witness TotalTriple.arr_store :=
  ⟨BitVec 32, inferInstance, inferInstance, p0, [0], 4, 0, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide, 1, Admit.of_heap arr32 (mem1_seq _ _)⟩

/-- A loop whose body leaves at once. -/
abbrev exitBody : MM Unit Unit := pure ()

theorem exitBody_step (hF : Heap) (s : Unit) (n : Nat) (m : Mem) (h : Heap) (hd : Heap.Disjoint h hF)
    (hm : m.heap = h ∪ hF) (hi : emp h) (hs : m.Seq) :
    ∃ e s' m' h', (exitBody.run s).run m = pure ((e, s'), m') ∧ Heap.Disjoint h' hF ∧
      m'.heap = h' ∪ hF ∧ m'.Seq ∧
      if (fun _ : Unit => false) e then ∃ n' < n, (fun _ _ => emp) s' n' h'
      else (fun _ _ => emp : Unit → Unit → Assn) e s' h' :=
  ⟨(), s, m, h, rfl, hd, hm, hs, hi⟩

nonvacuity_witness TotalTriple.loop_ghost :=
  ⟨Unit, Unit, exitBody, fun _ => false, fun _ _ => emp, fun _ _ => emp, exitBody_step, (), 0,
    Admit.emp⟩

nonvacuity_witness Triple.ret := ⟨Unit, fun _ => emp, (), Admit.emp⟩
liveness_witness Triple.ret := ⟨Unit, fun _ => emp, (), Live.of_total (TotalTriple.ret (Q := fun _ => emp) ()) Admit.emp⟩
nonvacuity_witness Triple.of_run :=
  ⟨Unit, emp, fun _ => emp, pure (), TotalTriple.ret (Q := fun _ => emp) (), Admit.emp⟩
liveness_witness Triple.of_run :=
  ⟨Unit, emp, fun _ => emp, pure (), TotalTriple.ret (Q := fun _ => emp) (),
    Live.of_total (TotalTriple.ret (Q := fun _ => emp) ()) Admit.emp⟩
nonvacuity_witness Triple.load :=
  ⟨BitVec 32, inferInstance, p0, 4, 0, by decide +kernel, Admit.of_heap pts32 (mem1_seq _ _)⟩
liveness_witness Triple.load :=
  ⟨BitVec 32, inferInstance, p0, 4, 0, by decide +kernel,
    Live.of_total (TotalTriple.load (by decide +kernel)) (Admit.of_heap pts32 (mem1_seq _ _))⟩
nonvacuity_witness Triple.store :=
  ⟨BitVec 32, inferInstance, inferInstance, p0, 4, 0, by decide +kernel, 1,
    Admit.of_heap pts32 (mem1_seq _ _)⟩
liveness_witness Triple.store :=
  ⟨BitVec 32, inferInstance, inferInstance, p0, 4, 0, by decide +kernel, 1,
    Live.of_total (TotalTriple.store (by decide +kernel) 1) (Admit.of_heap pts32 (mem1_seq _ _))⟩

/-! ## Blocks and allocators -/

nonvacuity_witness alloc_run_eq := ⟨{}, .heap, 1, 1, trivial⟩

nonvacuity_witness Triple.alloc := ⟨.heap, 1, 1, by decide, Admit.emp⟩
liveness_witness Triple.alloc :=
  ⟨.heap, 1, 1, by decide, Live.of_empty rfl (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness Triple.free :=
  ⟨p0, 4096, 1, .heap, #[.undef], rfl, rfl, by decide, Admit.of_heap (byte1 _) (mem1_seq _ _)⟩
liveness_witness Triple.free :=
  ⟨p0, 4096, 1, .heap, #[.undef], rfl, rfl, by decide,
    Live.of_heap (byte1 _) (mem1_seq _ _) (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness Triple.create := ⟨⟨⟩, 1, 1, by decide, by decide, Admit.emp⟩
liveness_witness Triple.create :=
  ⟨⟨⟩, 1, 1, by decide, by decide, Live.of_empty rfl (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness Triple.destroy :=
  ⟨⟨⟩, p0, 4096, 1, #[.undef], rfl, rfl, by decide, Admit.of_heap (byte1 _) (mem1_seq _ _)⟩
liveness_witness Triple.destroy :=
  ⟨⟨⟩, p0, 4096, 1, #[.undef], rfl, rfl, by decide,
    Live.of_heap (byte1 _) (mem1_seq _ _) (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness Triple.freeSentinel :=
  ⟨⟨⟩, ⟨p0, 0⟩, 4096, 1, #[.undef], rfl, rfl, by decide, Admit.of_heap (byte1 _) (mem1_seq _ _)⟩
liveness_witness Triple.freeSentinel :=
  ⟨⟨⟩, ⟨p0, 0⟩, 4096, 1, #[.undef], rfl, rfl, by decide,
    Live.of_heap (byte1 _) (mem1_seq _ _) (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness Triple.vtableAlloc := ⟨⟨⟩, 1, 1, by decide, by decide, Admit.emp⟩
liveness_witness Triple.vtableAlloc :=
  ⟨⟨⟩, 1, 1, by decide, by decide, Live.of_empty rfl (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness rawBlock_run :=
  ⟨mem1 #[.undef], ⟨p0, 1⟩, 16, 0, blk #[.undef], by with_unfolding_all rfl, rfl, rfl, rfl,
    by decide, trivial⟩

nonvacuity_witness Triple.allocSentinel := ⟨⟨⟩, 1, 0, by decide, Admit.emp⟩
liveness_witness Triple.allocSentinel :=
  ⟨⟨⟩, 1, 0, by decide, Live.of_empty rfl (ok_of_okb (by decide +kernel))⟩

/-- An empty sentinel-terminated buffer: the sentinel `0` at `p0`. -/
theorem sentinel0 : sentinelBuf ⟨p0, 0⟩ 4096 (Enc.encode (0 : BitVec 8)) 0
    (mem1 (Enc.encode (0 : BitVec 8))).heap :=
  ⟨rfl, by decide +kernel, by decide +kernel, mem1_bytesAt' (by decide +kernel)⟩

nonvacuity_witness Triple.appendSentinel :=
  ⟨⟨⟩, ⟨p0, 0⟩, 1, 0, 4096, Enc.encode (0 : BitVec 8), by decide,
    Admit.of_heap sentinel0 (mem1_seq _ _)⟩
liveness_witness Triple.appendSentinel :=
  ⟨⟨⟩, ⟨p0, 0⟩, 1, 0, 4096, Enc.encode (0 : BitVec 8), by decide,
    Live.of_heap sentinel0 (mem1_seq _ _) (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness Triple.freeSentinelBuf :=
  ⟨⟨⟩, ⟨p0, 0⟩, 4096, Enc.encode (0 : BitVec 8), 0, Admit.of_heap sentinel0 (mem1_seq _ _)⟩
liveness_witness Triple.freeSentinelBuf :=
  ⟨⟨⟩, ⟨p0, 0⟩, 4096, Enc.encode (0 : BitVec 8), 0,
    Live.of_heap sentinel0 (mem1_seq _ _) (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness Triple.reallocSentinel :=
  ⟨⟨⟩, ⟨p0, 0⟩, 1, 0, 4096, Enc.encode (0 : BitVec 8), by decide, by decide,
    Admit.of_heap sentinel0 (mem1_seq _ _)⟩
liveness_witness Triple.reallocSentinel :=
  ⟨⟨⟩, ⟨p0, 0⟩, 1, 0, 4096, Enc.encode (0 : BitVec 8), by decide, by decide,
    Live.of_heap sentinel0 (mem1_seq _ _) (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness remapByteBuffer_default_run := ⟨{}, ⟨p0, 0⟩, 1, rfl, trivial⟩

/-- One heap byte with alignment 1, whose allocator remaps in place. -/
def remapMem : Mem :=
  { blocks := #[{ blk #[.undef] with align := 1 }], nextAddr := 4098,
    allocPolicy := { byteRemap := .inPlace } }

nonvacuity_witness remapByteBuffer_inPlace_run :=
  ⟨remapMem, ⟨p0, 1⟩, 0, { blk #[.undef] with align := 1 }, 1, rfl, by with_unfolding_all rfl, rfl,
    rfl, rfl, by decide, by decide +kernel, fun h => absurd h (by decide),
    noRace_of_singleThread (singleThread_empty rfl Nat.zero_lt_one) _ _ _ _, trivial⟩

/-! ## Owned allocators (`ZigLean/Sep/Owned.lean`) -/

/-- One live owned allocator, and the block of `mem1 w32`. -/
def ownedMem : Mem := { mem1 (Enc.encode (0 : BitVec 32)) with allocators := #[default] }

nonvacuity_witness Mem.resetOwned_access_other :=
  ⟨ownedMem, 0, p0, 4, 4, 0, blk (Enc.encode (0 : BitVec 32)), 0, by with_unfolding_all rfl,
    by decide, trivial⟩
nonvacuity_witness Owned.reset_run := ⟨ownedMem, 0, default, rfl, rfl, trivial⟩
nonvacuity_witness ownedState_run := ⟨ownedMem, 0, default, rfl, rfl, trivial⟩

/-! ## Arrays (`ZigLean/Sep/Array.lean`, `ZigLean/Sep/Array/Reassemble.lean`) -/

nonvacuity_witness Triple.arr_store_focus :=
  ⟨BitVec 32, inferInstance, inferInstance, p0, [0], 0, 4, emp, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide, 1, Admit.of_heap (sep_emp.mpr arr32) (mem1_seq _ _)⟩
liveness_witness Triple.arr_store_focus :=
  ⟨BitVec 32, inferInstance, inferInstance, p0, [0], 0, 4, emp, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide, 1,
    Live.of_heap (sep_emp.mpr arr32) (mem1_seq _ _) (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness Triple.arr_read :=
  ⟨BitVec 32, inferInstance, p0, [0], 0, by decide +kernel, by decide +kernel, by decide,
    Admit.of_heap arr32 (mem1_seq _ _)⟩
liveness_witness Triple.arr_read :=
  ⟨BitVec 32, inferInstance, p0, [0], 0, by decide +kernel, by decide +kernel, by decide,
    Live.of_heap arr32 (mem1_seq _ _) (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness Triple.arr_store_reassemble :=
  ⟨BitVec 32, inferInstance, inferInstance, p0, [0], 0, emp, by decide +kernel, by decide +kernel,
    by decide, 1, Admit.of_heap (sep_emp.mpr arr32) (mem1_seq _ _)⟩
liveness_witness Triple.arr_store_reassemble :=
  ⟨BitVec 32, inferInstance, inferInstance, p0, [0], 0, emp, by decide +kernel, by decide +kernel,
    by decide, 1, Live.of_heap (sep_emp.mpr arr32) (mem1_seq _ _) (ok_of_okb (by decide +kernel))⟩

/-! ## Discarded loads, error unions and `try` -/

theorem readable1 : readableBytes p0 1 1 (mem1 #[.undef]).heap :=
  ⟨4096, 1, .heap, #[.undef], by decide, rfl, byte1 _⟩

nonvacuity_witness Triple.loadDiscardBytes :=
  ⟨p0, 1, 1, by decide, Admit.of_heap readable1 (mem1_seq _ _)⟩
liveness_witness Triple.loadDiscardBytes :=
  ⟨p0, 1, 1, by decide, Live.of_heap readable1 (mem1_seq _ _) (ok_of_okb (by decide +kernel))⟩

/-- The `u8` error union `u` at `p0` (error code at 0, payload at 2). -/
theorem eu8 (u : Except ErrName (BitVec 8)) : pts p0 2 u (mem1 (Enc.encode u)).heap :=
  mem1_pts' u (by decide)

/-- The error tag of an `u8` error union without an error, at `p0`. -/
theorem tag8 : errorTag (BitVec 8) p0 2 none (mem1 (errBytes none)).heap :=
  ⟨4096, 2, .heap, by decide +kernel, mem1_bytesAt' rfl⟩

nonvacuity_witness Triple.tryPayloadPtr :=
  ⟨BitVec 8, inferInstance, p0, 2, none, Admit.of_heap tag8 (mem1_seq _ _)⟩
liveness_witness Triple.tryPayloadPtr :=
  ⟨BitVec 8, inferInstance, p0, 2, none,
    Live.of_heap tag8 (mem1_seq _ _) (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness Triple.errUnion_errCode :=
  ⟨BitVec 8, inferInstance, p0, 2, "A", by decide, by decide +kernel,
    Admit.of_heap (eu8 (.error "A")) (mem1_seq _ _)⟩
liveness_witness Triple.errUnion_errCode :=
  ⟨BitVec 8, inferInstance, p0, 2, "A", by decide, by decide +kernel,
    Live.of_heap (eu8 (.error "A")) (mem1_seq _ _) (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness Triple.errUnion_payload_load :=
  ⟨BitVec 8, inferInstance, p0, 2, 2, 0, by decide, by decide +kernel, by decide +kernel,
    Admit.of_heap (eu8 (.ok 0)) (mem1_seq _ _)⟩
liveness_witness Triple.errUnion_payload_load :=
  ⟨BitVec 8, inferInstance, p0, 2, 2, 0, by decide, by decide +kernel, by decide +kernel,
    Live.of_heap (eu8 (.ok 0)) (mem1_seq _ _) (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness Triple.errUnion_payload_store :=
  ⟨BitVec 8, inferInstance, inferInstance, p0, 2, 2, 0, by decide, by decide +kernel,
    by decide +kernel, 1, Admit.of_heap (eu8 (.ok 0)) (mem1_seq _ _)⟩
liveness_witness Triple.errUnion_payload_store :=
  ⟨BitVec 8, inferInstance, inferInstance, p0, 2, 2, 0, by decide, by decide +kernel,
    by decide +kernel, 1, Live.of_heap (eu8 (.ok 0)) (mem1_seq _ _) (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness Triple.errUnion_try :=
  ⟨BitVec 8, inferInstance, p0, 2, .ok 0, by decide, by decide +kernel,
    Admit.of_heap (eu8 (.ok 0)) (mem1_seq _ _)⟩
liveness_witness Triple.errUnion_try :=
  ⟨BitVec 8, inferInstance, p0, 2, .ok 0, by decide, by decide +kernel,
    Live.of_heap (eu8 (.ok 0)) (mem1_seq _ _) (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness Triple.tryAliasWriteRead :=
  ⟨BitVec 8, inferInstance, inferInstance, p0, 2, 2, .ok 0, by decide, by decide +kernel, by decide,
    by decide +kernel, by decide +kernel, 1, Admit.of_heap (eu8 (.ok 0)) (mem1_seq _ _)⟩
liveness_witness Triple.tryAliasWriteRead :=
  ⟨BitVec 8, inferInstance, inferInstance, p0, 2, 2, .ok 0, by decide, by decide +kernel, by decide,
    by decide +kernel, by decide +kernel, 1,
    Live.of_heap (eu8 (.ok 0)) (mem1_seq _ _) (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness requireErrorUnion.eq_1 := ⟨Unit, domA, (), trivial⟩

nonvacuity_witness errUnion_decode_write :=
  ⟨BitVec 8, inferInstance, inferInstance, Enc.encode (Except.ok 0 : Except ErrName (BitVec 8)), 0,
    LawfulEnc.size_encode _, LawfulEnc.decode_encode _, 1, trivial⟩

/-! ## Loops (`ZigLean/Sep/Cost.lean`, `ZigLean/Sep/LoopTemplate.lean`) -/

nonvacuity_witness LoopRuns.run :=
  ⟨Unit, Unit, exitBody, fun _ => false, (), {}, 1, (), (), {}, LoopRuns.exit rfl rfl, trivial⟩

/-- The template of a loop whose body leaves at once, with no bytes owned. -/
theorem exitTemplate :
    LoopTemplate exitBody (fun _ => false) (fun _ _ => emp) (fun _ _ => emp) :=
  ⟨fun s _ => TotalTriple.ret (Q := loopNext (fun _ => false) (fun _ _ => emp) (fun _ _ => emp) _)
    ((), s)⟩

nonvacuity_witness LoopTemplate.step :=
  ⟨Unit, Unit, exitBody, fun _ => false, fun _ _ => emp, fun _ _ => emp, exitTemplate, (), 0,
    Admit.emp⟩
nonvacuity_witness LoopTemplate.total :=
  ⟨Unit, Unit, exitBody, fun _ => false, fun _ _ => emp, fun _ _ => emp, exitTemplate, (),
    Admit.of_empty ⟨0, rfl⟩⟩
nonvacuity_witness LoopTemplate.partial :=
  ⟨Unit, Unit, exitBody, fun _ => false, fun _ _ => emp, fun _ _ => emp, exitTemplate, (),
    Admit.of_empty ⟨0, rfl⟩⟩
liveness_witness LoopTemplate.partial :=
  ⟨Unit, Unit, exitBody, fun _ => false, fun _ _ => emp, fun _ _ => emp, exitTemplate, (),
    Live.of_total (exitTemplate.total ()) (Admit.of_empty ⟨0, rfl⟩)⟩

nonvacuity_witness TotalTriple.loop_template :=
  ⟨Unit, Unit, exitBody, fun _ => false, (), emp, fun _ => emp, fun _ _ => emp, fun _ _ => emp,
    exitTemplate, fun _ h => ⟨0, h⟩, fun _ _ _ h => h, Admit.emp⟩
nonvacuity_witness Triple.loop_template :=
  ⟨Unit, Unit, exitBody, fun _ => false, (), emp, fun _ => emp, fun _ _ => emp, fun _ _ => emp,
    exitTemplate, fun _ h => ⟨0, h⟩, fun _ _ _ h => h, Admit.emp⟩
liveness_witness Triple.loop_template :=
  ⟨Unit, Unit, exitBody, fun _ => false, (), emp, fun _ => emp, fun _ _ => emp, fun _ _ => emp,
    exitTemplate, fun _ h => ⟨0, h⟩, fun _ _ _ h => h,
    Live.of_total (TotalTriple.loop_template (P := emp) (Q := fun _ => emp) _ _ exitTemplate
      (fun _ h => ⟨0, h⟩) (fun _ _ _ h => h)) Admit.emp⟩

end Zig.Witness
