import QueueAdt.Gen
import ZigLean.Sep.Full.AutoAll
import ZigLean.Sep.Full.Queue
import ZigLean.Sep.Full.Cost

/-!
# Clients of the queue contract, proved from the contract only (P04, P06)

`rotate`, `rotateShift` and `pushAll` are generated from `queue.zig`; their bodies call the
generated operations of `Ring` or `Shift`. Each theorem here is stated for **every** contract
over the operations its body calls (`S : QueueImpl Ptr (BitVec 32) Ring_push Ring_pop
Ring_count`, `ZigLean/Sep/Full/Queue.lean`): the proof has `S.Rep` as an opaque assertion and
`S.push_spec`, `S.pop_spec` as its only rules about the operations, so no proof here unfolds a
representation or an operation's body, and none imports an implementation's proof.
`QueueAdt/Instances.lean` instantiates them to the ring and to the shifting array.

* `rotate_spec`, `rotateShift_spec`: a rotation moves the front item to the back, and returns,
  in exactly the declared steps of its `pop` and its `push` (`rotateSteps`). Its `push` cannot
  fail (the `catch unreachable` is not reached): the `pop` left room.
* `pushAll_exact` (P06): **under the capacity premise `xs.length + ys.length ≤ C`**, `pushAll`
  of the slice `ys` pushes every item (it returns `ys.length` and the queue holds `xs ++ ys`),
  pays `ys.length + 1` credits and returns as many receipts: one loop-body run per item and the
  final test, for every implementation whose `push` runs no step (`QueueImpl.PushStepFree`).
  `pushAll_steps` reads it off a run (exactly `ys.length + 1` steps), and `pushAll_not_within`
  shows that it is tight (`ys.length` credits do not pay it); `pushAll_total` is the plain-mode
  statement.

The counts are steps of the model (loop-body runs, SEM-05), not CPU time.
-/

namespace QueueAdt
open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-! ## Client 1: `rotate` (on every implementation) -/

section Rotate

variable {H α : Type} {push : H → α → MemM (Except ErrName Unit)} {pop : H → MemM (Option α)}
  {len : H → MemM (BitVec 64)} (S : QueueImpl H α push pop len)

/-- The queue after a rotation: the front item is at the back. -/
def Rotated (h : H) (C : Nat) : List α → FAssn
  | [] => S.Rep h C []
  | x :: xs => S.Rep h C (xs ++ [x])

/-- The steps of a rotation, by the declared counts: the `pop`, and the `push` of the front
item to the rest. -/
def rotateSteps (C : Nat) : List α → Nat
  | [] => S.popSteps C []
  | x :: xs => S.popSteps C (x :: xs) + S.pushSteps C xs x

end Rotate

variable (S : QueueImpl Ptr (BitVec 32) Ring_push Ring_pop Ring_count)

/-- **`rotate`** moves the front item to the back, for every queue implementation over the
generated operations, in exactly the steps of its `pop` and its `push` (`rotateSteps`). Its
`push` cannot fail: the `pop` left room. -/
theorem rotate_spec (q : Ptr) (C : Nat) (xs : List (BitVec 32)) :
    FTotalTriple (S.Rep q C xs ⋆ credits (rotateSteps S C xs)) (rotate q)
      (fun _ => Rotated S q C xs ⋆ spent (rotateSteps S C xs)) := by
  unfold rotate
  cases xs <;> simp only [rotateSteps, Rotated, credits_add, spent_add] <;>
    fsym [S.push_spec, S.pop_spec]

/-- **`rotateShift`**, the same program over the operations of `Shift`, for every queue
implementation over them. -/
theorem rotateShift_spec (S : QueueImpl Ptr (BitVec 16) Shift_push Shift_pop Shift_count)
    (q : Ptr) (C : Nat) (xs : List (BitVec 16)) :
    FTotalTriple (S.Rep q C xs ⋆ credits (rotateSteps S C xs)) (rotateShift q)
      (fun _ => Rotated S q C xs ⋆ spent (rotateSteps S C xs)) := by
  unfold rotateShift
  cases xs <;> simp only [rotateSteps, Rotated, credits_add, spent_add] <;>
    fsym [S.push_spec, S.pop_spec]

/-! ## Client 2: `pushAll`, with its step count -/

variable (q : Ptr) (C : Nat) (xs ys : List (BitVec 32)) (vs : Slice)

/-- The invariant of `pushAll`'s loop with `n` items left: the first `s.n` items of `ys` are
pushed. -/
def pushInv (s : pushAllLocals) (n : Nat) : FAssn :=
  ⟪n = ys.length - s.n.toNat ∧ s.n.toNat ≤ ys.length⟫ ⋆
    (S.Rep q C (xs ++ ys.take s.n.toNat) ⋆ up (arr vs.ptr ys))

/-- The loop's exit: every item is pushed, and the counter is the slice's length. -/
def pushPost (r : pushAllExit × pushAllLocals) : FAssn :=
  ⟪r.1 = .br4 ∧ r.2.n = vs.len⟫ ⋆ (S.Rep q C (xs ++ ys) ⋆ up (arr vs.ptr ys))

attribute [local fsym_arith] List.length_take

/-- A repetition's update: the pushed item `ys[k]` extends the pushed prefix of `ys`. -/
theorem pushed_take_upd {k k' : Nat} (hk : k < ys.length) (hk' : k' = k + 1) :
    EUpd (S.Rep q C (xs ++ ys.take k ++ [ys[k]])) (S.Rep q C (xs ++ ys.take k')) :=
  EUpd.of_imp fun _ h => by
    have e : xs ++ ys.take k ++ [ys[k]] = xs ++ ys.take k' := by
      subst hk'
      rw [List.append_assoc, List.take_append_getElem hk]
    rw [← e]
    exact h

/-- The exit's update: the prefix of all items is `ys`. -/
theorem pushed_all_upd {k : Nat} (hk : ys.length ≤ k) :
    EUpd (S.Rep q C (xs ++ ys.take k)) (S.Rep q C (xs ++ ys)) :=
  EUpd.of_imp fun _ h => by
    rw [List.take_of_length_le hk] at h
    exact h

/-! The step count below is exact for every implementation whose `push` runs no step
(`QueueImpl.PushStepFree`): the loop's invariant would otherwise hold the credits of the pushes
left, and `fsym` does not split a `credits` atom at a call (engine ledger #T1). -/

section Counted

variable (h0 : S.PushStepFree) (hlen : vs.len.toNat = ys.length)
  (hroom : xs.length + ys.length ≤ C)
include h0 hlen hroom

/-- One run of the loop body: one credit, one receipt, one item pushed or the exit. -/
theorem pushAll_step (s : pushAllLocals) (n : Nat) :
    FTotalTriple (pushInv S q C xs ys vs s n ⋆ credits 1) ((pushAll.loop5 q vs).run s)
      (fun r => floopExact pushAll.again5 (pushInv S q C xs ys vs) (pushPost S q C xs ys vs) n r ⋆
        spent 1) := by
  unfold pushAll.loop5 pushInv
  fsym [S.push_spec_stepFree h0, pushed_take_upd S q C xs ys, pushed_all_upd S q C xs ys]

/-- **The generated loop of `pushAll` with its exact step count**: with room for every item it
exits after `ys.length + 1` body runs (one per item and the final test). -/
theorem pushAll_loop_exact {mb : Lean.Order.MonoBind (MM pushAllLocals)} (s : pushAllLocals)
    (hs : s.n = 0) :
    FTotalTriple ((S.Rep q C xs ⋆ up (arr vs.ptr ys)) ⋆ credits (ys.length + 1))
      ((@Zig.loop (MM pushAllLocals) _ _ mb _ (pushAll.loop5 q vs) pushAll.again5).run s)
      (fun r => (FAssn.ex fun t : pushAllLocals =>
        ⟪r = (.br4, t) ∧ t.n = vs.len⟫ ⋆ (S.Rep q C (xs ++ ys) ⋆ up (arr vs.ptr ys))) ⋆
          spent (ys.length + 1)) :=
  (FTotalTriple.loop_exact (pushAll_step S q C xs ys vs h0 hlen hroom) s ys.length).conseq
    (fun _ h => sep_mono_left (fun _ h => sep_lift.mpr ⟨by simp [hs], by simpa [hs] using h⟩) h)
    fun ⟨e, t⟩ _ h => sep_mono_left (fun _ h => by
      obtain ⟨⟨he, ht⟩, h⟩ := sep_lift.mp h
      exact ⟨t, sep_lift.mpr ⟨⟨by simp only at he; rw [he], ht⟩, h⟩⟩) h

/-- **`pushAll` with its exact step count, under the capacity premise** `xs.length + ys.length ≤
C`: every item of the slice is pushed, for `ys.length + 1` credits and as many receipts, for
every queue implementation. -/
theorem pushAll_exact :
    FTotalTriple ((S.Rep q C xs ⋆ up (arr vs.ptr ys)) ⋆ credits (ys.length + 1)) (pushAll q vs)
      (fun r => (⟪r = vs.len⟫ ⋆ (S.Rep q C (xs ++ ys) ⋆ up (arr vs.ptr ys))) ⋆
        spent (ys.length + 1)) := by
  unfold pushAll
  fsym [pushAll_loop_exact S q C xs ys vs h0 hlen hroom]

/-- `pushAll` in the plain mode (no meter), from the cost statement. -/
theorem pushAll_total :
    FTotalTriple ((S.Rep q C xs ⋆ up (arr vs.ptr ys)) ⋆ plain) (pushAll q vs)
      (fun r => ((⟪r = vs.len⟫ ⋆ (S.Rep q C (xs ++ ys) ⋆ up (arr vs.ptr ys))) ⋆
        spent (ys.length + 1)) ⋆ plain) :=
  (pushAll_exact S q C xs ys vs h0 hlen hroom).of_credits_plain

/-- **`pushAll` runs exactly `ys.length + 1` steps under the capacity premise**: from any
credit-free start `m` that holds the queue and the slice (`r`) and a frame `rF`, it returns the
slice's length after exactly that many steps, and the live bytes of its final memory are the
frame's and a part `r'` that holds the queue with every item pushed. -/
theorem pushAll_steps {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hl : (S.Rep q C xs ⋆ up (arr vs.ptr ys)) r)
    (hseq : m.FSeq) (hc : CreditFree r rF) :
    ∃ m', (pushAll q vs).run m = pure (vs.len, m') ∧ m'.ticks = m.ticks + (ys.length + 1) ∧
      ∃ r', FHeap.Disjoint r'.heap rF.heap ∧
        SMatch m' (r'.heap ∪ rF.heap) (r'.gh.add rF.gh).share ∧
        (S.Rep q C (xs ++ ys) ⋆ up (arr vs.ptr ys)) r' ∧ m'.FSeq := by
  obtain ⟨v, m', hr, ht, r', hd', hm, hq, hs'⟩ :=
    (pushAll_exact S q C xs ys vs h0 hlen hroom).ticks_eq_post hh hl hseq hc
  obtain ⟨rfl, hl'⟩ := sep_lift.mp hq
  exact ⟨m', hr, ht, r', hd', hm, hl', hs'⟩

/-- **The bound of `pushAll` is tight**: from any credit-free start that holds the queue and the
slice, `ys.length` credits do not pay it, whatever the postcondition. -/
theorem pushAll_not_within {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hl : (S.Rep q C xs ⋆ up (arr vs.ptr ys)) r)
    (hseq : m.FSeq) (hc : CreditFree r rF) (Q : BitVec 64 → FAssn) :
    ¬ FTotalTriple ((S.Rep q C xs ⋆ up (arr vs.ptr ys)) ⋆ credits ys.length) (pushAll q vs) Q :=
  FTotalTriple.not_fewer_credits (pushAll_exact S q C xs ys vs h0 hlen hroom) (Nat.lt_succ_self _)
    hh hl hseq hc

end Counted

end QueueAdt
