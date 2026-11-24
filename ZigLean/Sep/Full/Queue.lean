import ZigLean.Sep.Full.Logic

/-!
# A bounded FIFO queue: one contract for every implementation (P04, `docs/interfaces.md`)

`QueueImpl H α push pop len` is the contract of a bounded first-in-first-out queue of items of
type `α` behind handles of type `H`, in the full-state logic (`docs/sep-full-state.md`). It is
stated once, for every item type, handle type and implementation:

* `Rep h C xs` is the representation predicate: the queue at `h` has the capacity `C` and holds
  the abstract sequence `xs`, front first. Its memory layout is not part of the contract.
* `push_spec`: `push h v` puts `v` at the back when there is room (`xs.length < C`), and fails
  with an error and the same queue exactly when the queue is full (`QueueImpl.Pushed`).
* `pop_spec`: `pop h` returns the front item and leaves the rest, or `none` for the empty queue
  (`QueueImpl.Popped`).
* `len_spec`: `len h` returns the number of items, which is at most `C`.

The operations are parameters, not fields, so that a client that is generated code, whose body
names the generated operations, is stated for **every** contract over those operations
(`∀ S : QueueImpl Ptr (BitVec 32) Ring_push Ring_pop Ring_count, …`): its proof has `S.Rep` as an
opaque assertion and the three specifications as its only rules, so a change of the
representation or of an operation's body that still proves the contract changes no client proof.
A client that is a program over arbitrary operations quantifies them as well.

**Steps and stack.** The specifications are total (`FTotalTriple`) and their preconditions hold
the representation alone: an operation runs no step (`Zig.tick`: no loop-body run, no recursive
entry; `docs/sep-full-state.md` §Step ticks) and pushes no stack block, in either mode (credits
or plain). So the step count of a client is the count of its own loop-body runs, whatever the
implementation, and a cost bound of a client proved against this contract (`credits`/`spent`,
`ZigLean/Sep/Full/Cost.lean`) holds for every implementation. An implementation whose operations
loop is not an instance; it would need the operations' own credits in the contract.

The implementation `tests/roadmap/queue-adt` is a ring buffer over a caller's buffer (generated
from `queue.zig`); its clients `rotate` and `pushAll` are proved from the contract only.

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig
namespace Full

open FAssn

/-- The outcome of a `push` of `v` to the queue `xs` of capacity `C` at `h`: with room, the queue
holds `v` at the back; a full queue fails and is unchanged. The cases exclude each other, so a
caller that knows `xs.length < C` gets the success. -/
def QueueImpl.Pushed {H α : Type} (Rep : H → Nat → List α → FAssn) (h : H) (C : Nat) (xs : List α)
    (v : α) : Except ErrName Unit → FAssn
  | .ok _ => ⟪xs.length < C⟫ ⋆ Rep h C (xs ++ [v])
  | .error _ => ⟪xs.length = C⟫ ⋆ Rep h C xs

/-- The outcome of a `pop` from the queue `xs` of capacity `C` at `h`: the front item and the
rest, or `none` and the empty queue. A queue holds at most `C` items, so the rest has room. -/
def QueueImpl.Popped {H α : Type} (Rep : H → Nat → List α → FAssn) (h : H) (C : Nat) (xs : List α) :
    Option α → FAssn
  | none => ⟪xs = []⟫ ⋆ Rep h C []
  | some x => FAssn.ex fun xs' => ⟪xs = x :: xs' ∧ xs'.length < C⟫ ⋆ Rep h C xs'

/-- A verified bounded FIFO queue of items of type `α` behind handles of type `H`, with the
operations `push`, `pop` and `len` (module doc). -/
structure QueueImpl (H α : Type) (push : H → α → MemM (Except ErrName Unit))
    (pop : H → MemM (Option α)) (len : H → MemM (BitVec 64)) where
  /-- The queue at `h` has the capacity `C` and holds `xs`, front first. -/
  Rep : H → Nat → List α → FAssn
  /-- `push` puts `v` at the back, or fails on a full queue and changes nothing. It returns. -/
  push_spec : ∀ (h : H) (C : Nat) (xs : List α) (v : α),
    FTotalTriple (Rep h C xs) (push h v) (QueueImpl.Pushed Rep h C xs v)
  /-- `pop` takes the front item, or returns `none` for the empty queue. It returns. -/
  pop_spec : ∀ (h : H) (C : Nat) (xs : List α),
    FTotalTriple (Rep h C xs) (pop h) (QueueImpl.Popped Rep h C xs)
  /-- `len` returns the number of items, which is at most the capacity. It returns. -/
  len_spec : ∀ (h : H) (C : Nat) (xs : List α),
    FTotalTriple (Rep h C xs) (len h)
      (fun r => ⟪r.toNat = xs.length ∧ xs.length ≤ C⟫ ⋆ Rep h C xs)

end Full
end Zig
