import ZigLean.Sep.Full.Cost

/-!
# A bounded FIFO queue: one contract for every implementation (P04, `docs/interfaces.md`)

`QueueImpl H α push pop len` is the contract of a bounded first-in-first-out queue of items of
type `α` behind handles of type `H`, in the full-state logic (`docs/sep-full-state.md`). It is
stated once, for every item type, handle type and implementation:

* `Rep h C xs` is the representation predicate: the queue at `h` has the capacity `C` and holds
  the abstract sequence `xs`, front first. Its memory layout is not part of the contract.
* `pushSteps C xs v`, `popSteps C xs` and `lenSteps C xs` are the **declared step counts** of
  the operations: how many steps (`Zig.tick`: loop-body runs and recursive entries;
  `docs/sep-full-state.md` §Step ticks) the operation runs on the queue `xs` of capacity `C`.
  They are functions of the abstract state, so a client computes its own count from them without
  knowing the implementation.
* `push_spec`: `push h v` puts `v` at the back when there is room (`xs.length < C`), and fails
  with an error and the same queue exactly when the queue is full (`QueueImpl.Pushed`). It takes
  `pushSteps C xs v` credits and returns as many receipts.
* `pop_spec`: `pop h` returns the front item and leaves the rest, or `none` for the empty queue
  (`QueueImpl.Popped`), for `popSteps C xs` credits and as many receipts.
* `len_spec`: `len h` returns the number of items, which is at most `C`, for `lenSteps C xs`
  credits and as many receipts.

The operations are parameters, not fields, so that a client that is generated code, whose body
names the generated operations, is stated for **every** contract over those operations
(`∀ S : QueueImpl Ptr (BitVec 32) Ring_push Ring_pop Ring_count, …`): its proof has `S.Rep` as an
opaque assertion and the three specifications as its only rules, so a change of the
representation, of an operation's body or of its step count that still proves the contract
changes no client proof. A client that is a program over arbitrary operations quantifies them as
well.

**Steps.** The specifications are total (`FTotalTriple`) and exact in their steps: credits in,
the same number of receipts out (`ZigLean/Sep/Full/Cost.lean`: `FTotalTriple.ticks_eq`,
`not_fewer_credits`). So a client's cost bound that is stated against this contract is exact for
every implementation: the client's own loop-body runs plus the declared counts of the calls it
makes (`QueueImpl.pushAllSteps`: the calls of pushing a list in order). An operation that runs
no step declares 0 (`QueueImpl.ofStepFree`, from statements without credits by
`FTotalTriple.credits_zero_iff`). The count must be a function of `C`, `xs` and the item: an
implementation whose count depends on state that `Rep` hides (an amortized bound) is not an
instance.

**Stack.** The preconditions hold no stack resource and not the plain mode, so an operation
pushes no stack block. This is a limit of the contract, and the reason is the framework's stack
resource, not the queue: room on the stack is not a resource that splits (`docs/sep-full-state.md`
§Stack depth, "Why not splittable `room n` credits"). A function that needs `k` bytes is stated
at every depth of one thread under a budget, `∀ D, D + k ≤ S → FTotalTriple (cur t ⋆ sp t S D ⋆
P) …`, or in the plain mode (`⋆ plain`), and no assertion holds in both modes: `sp` does not
exist where `noStack` is held and `plain` cannot be made under a budget. A contract with a
declared stack need would have to fix one mode, and its clients would be proved for that mode
only, while a statement without either frames into both. A declared stack need therefore waits
for a room assertion of the library that both modes provide, with the push rules of `fsym` over
it (engine ledger `contract-stack-room`).

The implementations in `tests/roadmap/queue-adt` are a ring buffer of `u32` items (no step) and a
linear array of `u16` items whose `pop` moves the rest down (`popSteps C xs = xs.length`), both
over a caller's buffer and generated from `queue.zig`; the clients are proved from the contract
only.

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
operations `push`, `pop` and `len` and their declared step counts (module doc). -/
structure QueueImpl (H α : Type) (push : H → α → MemM (Except ErrName Unit))
    (pop : H → MemM (Option α)) (len : H → MemM (BitVec 64)) where
  /-- The queue at `h` has the capacity `C` and holds `xs`, front first. -/
  Rep : H → Nat → List α → FAssn
  /-- The steps of a `push` of `v` to the queue `xs` of capacity `C`. -/
  pushSteps : Nat → List α → α → Nat
  /-- The steps of a `pop` from the queue `xs` of capacity `C`. -/
  popSteps : Nat → List α → Nat
  /-- The steps of a `len` of the queue `xs` of capacity `C`. -/
  lenSteps : Nat → List α → Nat
  /-- `push` puts `v` at the back, or fails on a full queue and changes nothing. It returns,
  after exactly `pushSteps C xs v` steps. -/
  push_spec : ∀ (h : H) (C : Nat) (xs : List α) (v : α),
    FTotalTriple (Rep h C xs ⋆ credits (pushSteps C xs v)) (push h v)
      (fun r => QueueImpl.Pushed Rep h C xs v r ⋆ spent (pushSteps C xs v))
  /-- `pop` takes the front item, or returns `none` for the empty queue. It returns, after
  exactly `popSteps C xs` steps. -/
  pop_spec : ∀ (h : H) (C : Nat) (xs : List α),
    FTotalTriple (Rep h C xs ⋆ credits (popSteps C xs)) (pop h)
      (fun r => QueueImpl.Popped Rep h C xs r ⋆ spent (popSteps C xs))
  /-- `len` returns the number of items, which is at most the capacity. It returns, after
  exactly `lenSteps C xs` steps. -/
  len_spec : ∀ (h : H) (C : Nat) (xs : List α),
    FTotalTriple (Rep h C xs ⋆ credits (lenSteps C xs)) (len h)
      (fun r => (⟪r.toNat = xs.length ∧ xs.length ≤ C⟫ ⋆ Rep h C xs) ⋆ spent (lenSteps C xs))

namespace QueueImpl

variable {H α : Type} {push : H → α → MemM (Except ErrName Unit)} {pop : H → MemM (Option α)}
  {len : H → MemM (BitVec 64)}

/-- **A queue whose operations run no step**: from the three statements without credits, the
contract with every step count 0. -/
def ofStepFree (Rep : H → Nat → List α → FAssn)
    (hpush : ∀ (h : H) (C : Nat) (xs : List α) (v : α),
      FTotalTriple (Rep h C xs) (push h v) (Pushed Rep h C xs v))
    (hpop : ∀ (h : H) (C : Nat) (xs : List α),
      FTotalTriple (Rep h C xs) (pop h) (Popped Rep h C xs))
    (hlen : ∀ (h : H) (C : Nat) (xs : List α),
      FTotalTriple (Rep h C xs) (len h)
        (fun r => ⟪r.toNat = xs.length ∧ xs.length ≤ C⟫ ⋆ Rep h C xs)) :
    QueueImpl H α push pop len where
  Rep := Rep
  pushSteps _ _ _ := 0
  popSteps _ _ := 0
  lenSteps _ _ := 0
  push_spec h C xs v := FTotalTriple.credits_zero_iff.mpr (hpush h C xs v)
  pop_spec h C xs := FTotalTriple.credits_zero_iff.mpr (hpop h C xs)
  len_spec h C xs := FTotalTriple.credits_zero_iff.mpr (hlen h C xs)

variable (S : QueueImpl H α push pop len) (C : Nat)

/-- **The steps of pushing `ys` in order** to the queue `xs` of capacity `C`: the declared count
of each `push`, on the queue that the earlier ones left. -/
def pushAllSteps : List α → List α → Nat
  | _, [] => 0
  | xs, y :: ys => S.pushSteps C xs y + pushAllSteps (xs ++ [y]) ys

theorem pushAllSteps_append (xs as bs : List α) :
    S.pushAllSteps C xs (as ++ bs) = S.pushAllSteps C xs as + S.pushAllSteps C (xs ++ as) bs := by
  induction as generalizing xs with
  | nil => simp [pushAllSteps]
  | cons a as ih =>
    simp only [List.cons_append, pushAllSteps, ih, List.append_assoc, List.singleton_append,
      Nat.add_assoc]

/-- The pushes from the item `k` on: the push of `ys[k]`, then those from `k + 1` on. -/
theorem pushAllSteps_drop (xs : List α) {ys : List α} {k : Nat} (hk : k < ys.length) :
    S.pushAllSteps C (xs ++ ys.take k) (ys.drop k) =
      S.pushSteps C (xs ++ ys.take k) ys[k] +
        S.pushAllSteps C (xs ++ ys.take (k + 1)) (ys.drop (k + 1)) := by
  rw [List.drop_eq_getElem_cons hk]
  simp only [pushAllSteps]
  rw [List.append_assoc, List.take_append_getElem hk]

/-- The pushes of the first `k + 1` items: those of the first `k`, then the push of `ys[k]`. -/
theorem pushAllSteps_take (xs : List α) {ys : List α} {k : Nat} (hk : k < ys.length) :
    S.pushAllSteps C xs (ys.take (k + 1)) =
      S.pushAllSteps C xs (ys.take k) + S.pushSteps C (xs ++ ys.take k) ys[k] := by
  rw [← List.take_append_getElem hk, pushAllSteps_append]
  simp only [pushAllSteps, Nat.add_zero]

/-- Pushing to a queue whose `push` runs no step runs none. -/
theorem pushAllSteps_eq_zero (h0 : ∀ (c : Nat) (xs : List α) (v : α), S.pushSteps c xs v = 0)
    (xs ys : List α) : S.pushAllSteps C xs ys = 0 := by
  induction ys generalizing xs with
  | nil => simp only [pushAllSteps]
  | cons y ys ih => simp only [pushAllSteps, h0, ih, Nat.add_zero]

end QueueImpl

end Full
end Zig
