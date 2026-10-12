import DispatchTokenizer
import ZigLean.Sep.Full.Loop
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Arr
import ZigLean.Sep.Full.Strength

/-!
# Total correctness of a generated tokenizer state machine

`source.zig`'s `countTokens` is a labelled `switch` over `enum { start, ident, number, done }`
whose prongs `continue :sw` to the next state; the compiler-exported AIR is translated fresh
by `check.sh` into the module `DispatchTokenizer` (namespace `Tok`). The loop is `Zig.loop
(countTokens.loop10 i4) countTokens.again10`, with the selector in the locals field
`dispatchValue10`.

The proof is in the full-state logic (`ZigLean/Sep/Full/Loop.lean`, walked by `fsym`):

* `isAlpha_step`/`isDigit_step`: the generated classifiers agree with `alpha`/`digit` on all 256
  bytes (kernel evaluation), as rules for `fsym`.
* `step`: the step premise of the dispatch-loop rule `FTotalTriple.loop_dispatch`, by a case
  split on the selector and `fsym` (the byte load is the library's `FTotalTriple.arr_load`, the
  index check `checkIndex_of`). The invariant `inv` is indexed by the selector's state
  (`counted`); the measure combines the unread bytes and the state's rank lexicographically as
  `3 * unread + rank`: `start` consumes a byte or moves to `done`, `ident`/`number` consume a
  byte or move back to `start` (rank 2 to rank 1). What is left after the walk is the reference
  automaton `tokens` on the next byte.
* `loop_total`: the loop by `FTotalTriple.loop_dispatch`, as a rule for `fsym`.
* `countTokens_total`: for a buffer `p` holding the bytes `xs`, `countTokens p xs.length` returns
  (no panic, no divergence) `tokens .start xs` modulo `2 ^ 32` and leaves the buffer unchanged.
* `countTokens_total_legacy`: the legacy total triple on every `Mem.FSeq` memory, through
  `FTotalTriple.toTotal_on`.
-/

namespace Tok.Proof
open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

def alpha (c : BitVec 8) : Bool :=
  (97 ≤ c.toNat && c.toNat ≤ 122) || (65 ≤ c.toNat && c.toNat ≤ 90) || c.toNat == 95

def digit (c : BitVec 8) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

/-- The reference automaton: the tokens still to be counted from state `k` on input `cs`. -/
def tokens : State → List (BitVec 8) → Nat
  | .start, [] => 0
  | .start, c :: cs =>
    if alpha c then tokens .ident cs + 1 else if digit c then tokens .number cs + 1
    else tokens .start cs
  | .ident, [] => 0
  | .ident, c :: cs => if alpha c || digit c then tokens .ident cs else tokens .start cs
  | .number, [] => 0
  | .number, c :: cs =>
    if digit c then tokens .number cs else if alpha c then tokens .ident cs + 1
    else tokens .start cs
  | .done, _ => 0

-- "ab 12 c", "x1+22y_z;;9" and "": the native samples of source.zig.
example : tokens .start [97, 98, 32, 49, 50, 32, 99] = 3 := by decide
example : tokens .start [120, 49, 43, 50, 50, 121, 95, 122, 59, 59, 57] = 4 := by decide
example : tokens .start [] = 0 := by decide

/-! ## The classifiers -/

/-- A generated classifier returned `b`. -/
def agrees (r : Zig.Result Bool) (b : Bool) : Bool :=
  match r.run with
  | some (.ok v) => v == b
  | _ => false

theorem agrees_eq : ∀ {r : Zig.Result Bool} {b : Bool}, agrees r b = true → r = pure b
  | some (.ok _), _, h => by simp only [agrees, ExceptT.run, beq_iff_eq] at h; subst h; rfl
  | some (.error _), _, h => by simp [agrees, ExceptT.run] at h
  | none, _, h => by simp [agrees, ExceptT.run] at h

/-- The generated classifiers agree with `alpha`/`digit` on all 256 bytes (kernel evaluation). -/
theorem isAlpha_all : ∀ n : Fin 256, agrees (isAlpha (BitVec.ofFin n)) (alpha (BitVec.ofFin n)) := by
  decide +kernel

theorem isDigit_all : ∀ n : Fin 256, agrees (isDigit (BitVec.ofFin n)) (digit (BitVec.ofFin n)) := by
  decide +kernel

theorem isAlpha_step {P : FAssn} (c : BitVec 8) :
    FTotalTriple P (StateT.lift (isAlpha c) : MemM Bool) (fun r => ⟪r = alpha c⟫ ⋆ P) := by
  rw [agrees_eq (isAlpha_all c.toFin)]
  exact (FTotalTriple.ret (Q := fun r => ⟪r = alpha c⟫ ⋆ P) _).pre fun _ hp => sep_lift.mpr ⟨rfl, hp⟩

theorem isDigit_step {P : FAssn} (c : BitVec 8) :
    FTotalTriple P (StateT.lift (isDigit c) : MemM Bool) (fun r => ⟪r = digit c⟫ ⋆ P) := by
  rw [agrees_eq (isDigit_all c.toFin)]
  exact (FTotalTriple.ret (Q := fun r => ⟪r = digit c⟫ ⋆ P) _).pre fun _ hp => sep_lift.mpr ⟨rfl, hp⟩

/-! ## The loop -/

def rank : State → Nat
  | .done => 0
  | .start => 1
  | .ident => 2
  | .number => 2

/-- The count so far plus the tokens still ahead from state `k` is the answer (mod `2 ^ 32`);
at `done`, the count is the answer. -/
def counted (xs : List (BitVec 8)) (k : State) (i : BitVec 64) (count : BitVec 32) : Prop :=
  match k with
  | .done => count.toNat = tokens .start xs % 2 ^ 32
  | k => i.toNat ≤ xs.length ∧
    (count.toNat + tokens k (xs.drop i.toNat)) % 2 ^ 32 = tokens .start xs % 2 ^ 32

/-- The state-indexed invariant: the count of state `k`, and the buffer. -/
def inv (sl : Slice) (xs : List (BitVec 8)) (k : State) (s : countTokensLocals) : FAssn :=
  ⟪counted xs k s.i s.count⟫ ⋆ up (arr sl.ptr xs)

/-- The consumed data: the unread bytes. -/
def unread (xs : List (BitVec 8)) (s : countTokensLocals) : Nat := xs.length - s.i.toNat

def post (sl : Slice) (xs : List (BitVec 8)) (r : countTokensExit × countTokensLocals) : FAssn :=
  ⟪r.1 = .br9 ∧ r.2.count.toNat = tokens .start xs % 2 ^ 32⟫ ⋆ up (arr sl.ptr xs)

-- The ranks of the states are arithmetic facts for `fsym`.
attribute [local fsym_arith] rank

/-- One run of the body, in every state: the step premise of `FTotalTriple.loop_dispatch`. -/
theorem step (sl : Slice) (xs : List (BitVec 8)) (hlen : sl.len.toNat = xs.length)
    (s : countTokensLocals) :
    FTotalTriple (inv sl xs s.dispatchValue10 s) ((countTokens.loop10 sl).run s)
      (fun r => if countTokens.again10 r.1 then
          ⟪3 * unread xs r.2 + rank r.2.dispatchValue10 < 3 * unread xs s + rank s.dispatchValue10⟫ ⋆
            inv sl xs r.2.dispatchValue10 r.2
        else post sl xs r) := by
  obtain ⟨i, count, k⟩ := s
  unfold countTokens.loop10 inv unread post
  cases k <;> fsym [isAlpha_step, isDigit_step]
  -- left: the reference automaton on the byte at `i` (or at the end of the input)
  all_goals
    try simp only [counted] at *
    first
    | -- `start` at the end of the input: to `done`
      have h0 : xs.drop sl.len.toNat = [] := List.drop_eq_nil_of_le (by omega)
      simp_all [tokens, Nat.mod_eq_of_lt count.isLt]; done
    | obtain hlt | hge := Nat.lt_or_ge i.toNat xs.length
      · -- a byte is read
        rw [List.drop_eq_getElem_cons hlt] at *
        simp_all [tokens, addWrap, BitVec.toNat_add] <;> omega
      · first
        | exact absurd (BitVec.eq_of_toNat_eq (by omega)) ‹¬i = sl.len›
        | (have := ‹lt false i sl.len = true›; simp only [lt_false, decide_eq_true_eq] at this; omega)
        | -- `ident`/`number` at the end of the input: back to `start`
          have h0 : xs.drop i.toNat = [] := List.drop_eq_nil_of_le hge
          simp only [h0, tokens, Nat.add_zero] at *; omega

/-- The generated loop-switch, as a rule for `fsym`: from the start state with nothing counted
it exits with the token count. The loop's `MonoBind` proof is a parameter, so the rule's command
unifies with any elaboration of it. -/
theorem loop_total {mb : Lean.Order.MonoBind (MM countTokensLocals)} (sl : Slice)
    (xs : List (BitVec 8)) (hlen : sl.len.toNat = xs.length) (s : countTokensLocals)
    (hi : s.i = 0) (hc : s.count = 0) (hk : s.dispatchValue10 = .start) :
    FTotalTriple (up (arr sl.ptr xs))
      ((@Zig.loop (MM countTokensLocals) _ _ mb _ (countTokens.loop10 sl) countTokens.again10).run s)
      (fun r => FAssn.ex fun t : countTokensLocals =>
        ⟪r = (.br9, t) ∧ t.count.toNat = tokens .start xs % 2 ^ 32⟫ ⋆ up (arr sl.ptr xs)) :=
  (FTotalTriple.loop_dispatch (·.dispatchValue10) (inv sl xs) (unread xs) rank 3 (post sl xs)
    (step sl xs hlen) s).eupd
    (by unfold inv counted; simp only [hi, hc, hk]; fsym_entail; simp)
    |>.eupd_post fun ⟨e, t⟩ => EUpd.of_imp fun _ h => by
      obtain ⟨⟨he, ht⟩, h⟩ := sep_lift.mp h
      exact ⟨t, sep_lift.mpr ⟨⟨by simp only at he; rw [he], ht⟩, h⟩⟩

/-- `countTokens p n` over a buffer `p` of `n` bytes `xs` returns the number of tokens of `xs`
(mod `2 ^ 32`) and leaves the buffer unchanged. -/
theorem countTokens_total (p : Ptr) (xs : List (BitVec 8)) (hlen : xs.length < 2 ^ 64) :
    FTotalTriple (up (arr p xs)) (countTokens p (BitVec.ofNat 64 xs.length))
      (fun r => ⟪r.toNat = tokens .start xs % 2 ^ 32⟫ ⋆ up (arr p xs)) := by
  unfold countTokens
  fsym [loop_total]

/-- `countTokens_total` as the legacy total triple on every `Mem.FSeq` memory
(`FTotalTriple.toTotal_on`). -/
theorem countTokens_total_legacy (p : Ptr) (xs : List (BitVec 8)) (hlen : xs.length < 2 ^ 64) :
    TotalTripleIn Mem.FSeq (arr p xs) (countTokens p (BitVec.ofNat 64 xs.length))
      (fun r => ⌜r.toNat = tokens .start xs % 2 ^ 32⌝ ∗ arr p xs) :=
  FTotalTriple.toTotal_on ((countTokens_total p xs hlen).post fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.arr _ _)

end Tok.Proof

-- Only the standard axioms: no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`).
/-- info: 'Tok.Proof.countTokens_total_legacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tok.Proof.countTokens_total_legacy
