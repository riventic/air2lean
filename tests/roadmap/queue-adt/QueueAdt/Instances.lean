import QueueAdt.Ring
import QueueAdt.Clients

/-!
# The clients on the ring buffer (P04, P06)

The client theorems of `QueueAdt/Clients.lean`, each proved once for every queue contract over
the generated operations, at the ring buffer's instance `ringQueue` (`QueueAdt/Ring.lean`): the
statements about the generated program with its own representation predicate `ring`. Nothing is
proved again here.
-/

namespace QueueAdt
open Zig Zig.Full Zig.Full.FAssn

/-- `rotate` on the ring buffer moves the front item to the back. -/
theorem ring_rotate (q : Ptr) (C : Nat) (xs : List (BitVec 32)) :
    FTotalTriple (ring q C xs) (rotate q) (fun _ => Rotated ringQueue q C xs) :=
  rotate_spec ringQueue q C xs

/-- **`pushAll` on the ring buffer, under the capacity premise** `xs.length + ys.length ≤ C`:
every item is pushed, for `ys.length + 1` credits and as many receipts. -/
theorem ring_pushAll_exact (q : Ptr) (C : Nat) (xs ys : List (BitVec 32)) (vs : Slice)
    (hlen : vs.len.toNat = ys.length) (hroom : xs.length + ys.length ≤ C) :
    FTotalTriple ((ring q C xs ⋆ up (arr vs.ptr ys)) ⋆ credits (ys.length + 1)) (pushAll q vs)
      (fun r => (⟪r = vs.len⟫ ⋆ (ring q C (xs ++ ys) ⋆ up (arr vs.ptr ys))) ⋆
        spent (ys.length + 1)) :=
  pushAll_exact ringQueue q C xs ys vs hlen hroom

/-- `pushAll` on the ring buffer cannot be paid with `ys.length` credits. -/
theorem ring_pushAll_not_within (q : Ptr) (C : Nat) (xs ys : List (BitVec 32)) (vs : Slice)
    (hlen : vs.len.toNat = ys.length) (hroom : xs.length + ys.length ≤ C) {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hl : (ring q C xs ⋆ up (arr vs.ptr ys)) r) (hseq : m.FSeq)
    (hc : CreditFree r rF) (Q : BitVec 64 → FAssn) :
    ¬ FTotalTriple ((ring q C xs ⋆ up (arr vs.ptr ys)) ⋆ credits ys.length) (pushAll q vs) Q :=
  pushAll_not_within ringQueue q C xs ys vs hlen hroom hh hl hseq hc Q

end QueueAdt
