import DispatchTokenizer
import ZigLean.Sep.DispatchTemplate
import ZigLean.Range

/-!
# Total correctness of a generated tokenizer state machine

`source.zig`'s `countTokens` is a labelled `switch` over `enum { start, ident, number, done }`
whose prongs `continue :sw` to the next state; the compiler-exported AIR is translated fresh
by `check.sh` into the module `DispatchTokenizer` (namespace `Tok`). The loop is `Zig.loop (countTokens.loop10 i4)
countTokens.again10`, with the selector in the locals field `dispatchValue10`.

`countTokens_total`: for a buffer `p` holding the bytes `xs` (`arr p xs`), `countTokens p
xs.length` returns (no panic, no divergence) the number of identifier and number tokens of `xs`,
`tokens .start xs` modulo `2 ^ 32`, and leaves the buffer unchanged. The proof is the dispatch
template: one premise per state, the state-indexed invariant `inv`, and the lexicographic
measure (unread bytes, state rank): `start` consumes a byte or moves to `done`, `ident`/`number`
consume a byte or move back to `start` (rank 2 to rank 1).
-/

namespace Tok.Proof
open Zig Assn

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

/-- Leaving `ident`/`number` without consuming agrees with restarting on the same input. -/
theorem tokens_ident_leave (cs : List (BitVec 8))
    (h : ∀ c cs', cs = c :: cs' → ¬(alpha c || digit c) = true) :
    tokens .ident cs = tokens .start cs := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    have h := h c cs rfl
    simp only [Bool.or_eq_true, not_or] at h
    simp [tokens, h.1, h.2]

theorem tokens_number_leave (cs : List (BitVec 8))
    (h : ∀ c cs', cs = c :: cs' → ¬digit c = true) :
    tokens .number cs = tokens .start cs := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    have h := h c cs rfl
    by_cases ha : alpha c = true <;> simp [tokens, h, ha]

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

theorem isAlpha_eq (c : BitVec 8) : isAlpha c = pure (alpha c) := agrees_eq (isAlpha_all c.toFin)

theorem isDigit_eq (c : BitVec 8) : isDigit c = pure (digit c) := agrees_eq (isDigit_all c.toFin)

/-- A byte load from the buffer. -/
theorem byte_load {p : Ptr} {xs : List (BitVec 8)} {m : Mem} {h hF : Heap} {i : BitVec 64}
    (ha : arr p xs h) (hm : m.heap = h ∪ hF) (hst : m.Seq) (hi : i.toNat < xs.length) :
    ∃ m', (Zig.load (BitVec 8) 1 (p.elem 1 i)).run m = pure (xs[i.toNat], m') ∧
      m'.heap = h ∪ hF ∧ m'.Seq :=
  arr_load_run (T := BitVec 8) (a := 1) ha hm (by decide) (by decide) (by decide) hi hst

def rank : State → Nat
  | .done => 0
  | .start => 1
  | .ident => 2
  | .number => 2

/-- The count so far plus the tokens still ahead from state `k` is the answer (mod `2 ^ 32`). -/
def counted (xs : List (BitVec 8)) (k : State) (s : countTokensLocals) : Prop :=
  s.i.toNat ≤ xs.length ∧
    (s.count.toNat + tokens k (xs.drop s.i.toNat)) % 2 ^ 32 = tokens .start xs % 2 ^ 32

/-- The state-indexed invariant: the buffer, and the count of state `k`. -/
def inv (sl : Slice) (xs : List (BitVec 8)) (k : State) (s : countTokensLocals) : Assn :=
  ⌜match k with
    | .done => s.count.toNat = tokens .start xs % 2 ^ 32
    | k => counted xs k s⌝ ∗ arr sl.ptr xs

def μ (xs : List (BitVec 8)) (s : countTokensLocals) : Nat × Nat :=
  (xs.length - s.i.toNat, rank s.dispatchValue10)

def post (sl : Slice) (xs : List (BitVec 8)) (e : countTokensExit) (s : countTokensLocals) : Assn :=
  ⌜e = .br9 ∧ s.count.toNat = tokens .start xs % 2 ^ 32⌝ ∗ arr sl.ptr xs

abbrev next (sl : Slice) (xs : List (BitVec 8)) (s : countTokensLocals) :=
  dispatchNext countTokens.again10 (fun s => s.dispatchValue10) (inv sl xs) (μ xs) (post sl xs) s

/-- Facts about reading byte `i` of the buffer, shared by the consuming prongs. -/
theorem read_facts {sl : Slice} {xs : List (BitVec 8)} (hlen : sl.len.toNat = xs.length)
    {i : BitVec 64} (hlt : i.toNat < xs.length) :
    ¬18446744073709551615 ≤ i.toNat ∧ (i + 1).toNat = i.toNat + 1 ∧
      xs.drop i.toNat = xs[i.toNat] :: xs.drop (i.toNat + 1) := by
  have hfit : i.toNat + 1 < 2 ^ 64 := by have := sl.len.isLt; omega
  exact ⟨by omega, toNat_add_one i hfit, List.drop_eq_getElem_cons hlt⟩

theorem one32 : (1 : BitVec 32).toNat = 1 := rfl

/-- `start`: at the end move to `done`; otherwise consume a byte and enter its token state. -/
theorem step_start (sl : Slice) (xs : List (BitVec 8)) (hlen : sl.len.toNat = xs.length)
    (s : countTokensLocals) (hk : s.dispatchValue10 = .start) :
    TotalTriple (inv sl xs .start s) ((countTokens.loop10 sl).run s) (next sl xs s) := by
  apply TotalTriple.of_run
  intro m h hF hd hm hi hst
  obtain ⟨⟨hle, hc⟩, ha⟩ := sep_lift.mp hi
  obtain ⟨i, count, d⟩ := s
  simp only at hk hle hc
  subst hk
  by_cases hend : i = sl.len
  · refine ⟨(.dispatch10 .done, ⟨i, count, .done⟩), m, h, ?_, hd, hm, ?_, hst⟩
    · simp [countTokens.loop10, zig_unfold, hend]
    · refine dispatchNext_repeat rfl (DispatchLt.rank rfl (by simp [μ, rank])) (sep_lift.mpr ⟨?_, ha⟩)
      have hnil : xs.drop i.toNat = [] := List.drop_eq_nil_of_le (by rw [hend]; omega)
      simp only [hnil, tokens, Nat.add_zero] at hc
      simpa [Nat.mod_eq_of_lt count.isLt] using hc
  · have hlt : i.toNat < xs.length := by
      have : i.toNat ≠ sl.len.toNat := fun h => hend (BitVec.eq_of_toNat_eq h)
      omega
    obtain ⟨hnoOverflow, hi1, hdrop⟩ := read_facts hlen hlt
    obtain ⟨m1, hv, hm1, hst1⟩ := byte_load (i := i) ha hm hst hlt
    simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hv
    rw [hdrop] at hc
    have hlt' : i.toNat < sl.len.toNat := hlen ▸ hlt
    cases hA : alpha xs[i.toNat] <;> cases hD : digit xs[i.toNat]
    · refine ⟨(.dispatch10 .start, ⟨i + 1, count, .start⟩), m1, h, ?_, hd, hm1, ?_, hst1⟩
      · simp [countTokens.loop10, zig_unfold, hend, hlt', hv, hnoOverflow, isAlpha_eq, isDigit_eq, hA, hD]
      · refine dispatchNext_repeat rfl (DispatchLt.data ?_) (sep_lift.mpr ⟨?_, ha⟩)
        · simp only [μ, hi1]; omega
        · simp only [tokens, hA, hD, Bool.false_eq_true, ↓reduceIte] at hc
          exact ⟨by simp only [hi1]; omega, by simpa only [hi1] using hc⟩
    · refine ⟨(.dispatch10 .number, ⟨i + 1, count + 1, .number⟩), m1, h, ?_, hd, hm1, ?_, hst1⟩
      · simp [countTokens.loop10, zig_unfold, hend, hlt', hv, hnoOverflow, isAlpha_eq, isDigit_eq, hA, hD,
          Zig.addWrap]
      · refine dispatchNext_repeat rfl (DispatchLt.data ?_) (sep_lift.mpr ⟨?_, ha⟩)
        · simp only [μ, hi1]; omega
        · simp only [tokens, hA, hD, Bool.false_eq_true, ↓reduceIte] at hc
          refine ⟨by simp only [hi1]; omega, ?_⟩
          simp only [hi1, BitVec.toNat_add, one32]
          omega
    · refine ⟨(.dispatch10 .ident, ⟨i + 1, count + 1, .ident⟩), m1, h, ?_, hd, hm1, ?_, hst1⟩
      · simp [countTokens.loop10, zig_unfold, hend, hlt', hv, hnoOverflow, isAlpha_eq, isDigit_eq, hA,
          Zig.addWrap]
      · refine dispatchNext_repeat rfl (DispatchLt.data ?_) (sep_lift.mpr ⟨?_, ha⟩)
        · simp only [μ, hi1]; omega
        · simp only [tokens, hA, ↓reduceIte] at hc
          refine ⟨by simp only [hi1]; omega, ?_⟩
          simp only [hi1, BitVec.toNat_add, one32]
          omega
    · refine ⟨(.dispatch10 .ident, ⟨i + 1, count + 1, .ident⟩), m1, h, ?_, hd, hm1, ?_, hst1⟩
      · simp [countTokens.loop10, zig_unfold, hend, hlt', hv, hnoOverflow, isAlpha_eq, isDigit_eq, hA,
          Zig.addWrap]
      · refine dispatchNext_repeat rfl (DispatchLt.data ?_) (sep_lift.mpr ⟨?_, ha⟩)
        · simp only [μ, hi1]; omega
        · simp only [tokens, hA, ↓reduceIte] at hc
          refine ⟨by simp only [hi1]; omega, ?_⟩
          simp only [hi1, BitVec.toNat_add, one32]
          omega

/-- `ident`: consume an identifier byte, or move back to `start` without consuming. -/
theorem step_ident (sl : Slice) (xs : List (BitVec 8)) (hlen : sl.len.toNat = xs.length)
    (s : countTokensLocals) (hk : s.dispatchValue10 = .ident) :
    TotalTriple (inv sl xs .ident s) ((countTokens.loop10 sl).run s) (next sl xs s) := by
  apply TotalTriple.of_run
  intro m h hF hd hm hi hst
  obtain ⟨⟨hle, hc⟩, ha⟩ := sep_lift.mp hi
  obtain ⟨i, count, d⟩ := s
  simp only at hk hle hc
  subst hk
  by_cases hlt : i.toNat < xs.length
  · have hlt' : i.toNat < sl.len.toNat := hlen ▸ hlt
    obtain ⟨hnoOverflow, hi1, hdrop⟩ := read_facts hlen hlt
    obtain ⟨m1, hv, hm1, hst1⟩ := byte_load (i := i) ha hm hst hlt
    obtain ⟨m2, hv2, hm2, hst2⟩ := byte_load (i := i) ha hm1 hst1 hlt
    simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hv hv2
    rw [hdrop] at hc
    cases hA : alpha xs[i.toNat] <;> cases hD : digit xs[i.toNat]
    · -- Neither: the identifier ends here; `start` rereads this byte.
      refine ⟨(.dispatch10 .start, ⟨i, count, .start⟩), m2, h, ?_, hd, hm2, ?_, hst2⟩
      · simp [countTokens.loop10, zig_unfold, hlt', hv, hv2, isAlpha_eq, isDigit_eq, hA, hD]
      · refine dispatchNext_repeat rfl (DispatchLt.rank rfl (by simp [μ, rank])) (sep_lift.mpr ⟨?_, ha⟩)
        refine ⟨hle, ?_⟩
        rw [hdrop]
        simpa only [tokens, hA, hD, Bool.or_false, Bool.false_eq_true, ↓reduceIte] using hc
    · refine ⟨(.dispatch10 .ident, ⟨i + 1, count, .ident⟩), m2, h, ?_, hd, hm2, ?_, hst2⟩
      · simp [countTokens.loop10, zig_unfold, hlt', hv, hv2, hnoOverflow, isAlpha_eq, isDigit_eq, hA, hD]
      · refine dispatchNext_repeat rfl (DispatchLt.data ?_) (sep_lift.mpr ⟨?_, ha⟩)
        · simp only [μ, hi1]; omega
        · simp only [tokens, hA, hD, Bool.or_true, ↓reduceIte] at hc
          exact ⟨by simp only [hi1]; omega, by simpa only [hi1] using hc⟩
    all_goals
      refine ⟨(.dispatch10 .ident, ⟨i + 1, count, .ident⟩), m1, h, ?_, hd, hm1, ?_, hst1⟩
      · simp [countTokens.loop10, zig_unfold, hlt', hv, hnoOverflow, isAlpha_eq, hA]
      · refine dispatchNext_repeat rfl (DispatchLt.data ?_) (sep_lift.mpr ⟨?_, ha⟩)
        · simp only [μ, hi1]; omega
        · simp only [tokens, hA, Bool.true_or, ↓reduceIte] at hc
          exact ⟨by simp only [hi1]; omega, by simpa only [hi1] using hc⟩
  · have hge : i.toNat = xs.length := by omega
    have hge' : ¬ i.toNat < sl.len.toNat := by omega
    refine ⟨(.dispatch10 .start, ⟨i, count, .start⟩), m, h, ?_, hd, hm, ?_, hst⟩
    · simp [countTokens.loop10, zig_unfold, hge']
    · refine dispatchNext_repeat rfl (DispatchLt.rank rfl (by simp [μ, rank])) (sep_lift.mpr ⟨?_, ha⟩)
      have hnil : xs.drop i.toNat = [] := List.drop_eq_nil_of_le (by omega)
      refine ⟨hle, ?_⟩
      simp only [hnil, tokens] at hc ⊢
      exact hc

/-- `number`: consume a digit, or move back to `start` without consuming. -/
theorem step_number (sl : Slice) (xs : List (BitVec 8)) (hlen : sl.len.toNat = xs.length)
    (s : countTokensLocals) (hk : s.dispatchValue10 = .number) :
    TotalTriple (inv sl xs .number s) ((countTokens.loop10 sl).run s) (next sl xs s) := by
  apply TotalTriple.of_run
  intro m h hF hd hm hi hst
  obtain ⟨⟨hle, hc⟩, ha⟩ := sep_lift.mp hi
  obtain ⟨i, count, d⟩ := s
  simp only at hk hle hc
  subst hk
  by_cases hlt : i.toNat < xs.length
  · have hlt' : i.toNat < sl.len.toNat := hlen ▸ hlt
    obtain ⟨hnoOverflow, hi1, hdrop⟩ := read_facts hlen hlt
    obtain ⟨m1, hv, hm1, hst1⟩ := byte_load (i := i) ha hm hst hlt
    simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hv
    rw [hdrop] at hc
    cases hD : digit xs[i.toNat]
    · refine ⟨(.dispatch10 .start, ⟨i, count, .start⟩), m1, h, ?_, hd, hm1, ?_, hst1⟩
      · simp [countTokens.loop10, zig_unfold, hlt', hv, isDigit_eq, hD]
      · refine dispatchNext_repeat rfl (DispatchLt.rank rfl (by simp [μ, rank])) (sep_lift.mpr ⟨?_, ha⟩)
        refine ⟨hle, ?_⟩
        rw [hdrop]
        cases hA : alpha xs[i.toNat] <;>
          simpa only [tokens, hA, hD, Bool.false_eq_true, ↓reduceIte] using hc
    · refine ⟨(.dispatch10 .number, ⟨i + 1, count, .number⟩), m1, h, ?_, hd, hm1, ?_, hst1⟩
      · simp [countTokens.loop10, zig_unfold, hlt', hv, hnoOverflow, isDigit_eq, hD]
      · refine dispatchNext_repeat rfl (DispatchLt.data ?_) (sep_lift.mpr ⟨?_, ha⟩)
        · simp only [μ, hi1]; omega
        · simp only [tokens, hD, ↓reduceIte] at hc
          exact ⟨by simp only [hi1]; omega, by simpa only [hi1] using hc⟩
  · have hge' : ¬ i.toNat < sl.len.toNat := by omega
    refine ⟨(.dispatch10 .start, ⟨i, count, .start⟩), m, h, ?_, hd, hm, ?_, hst⟩
    · simp [countTokens.loop10, zig_unfold, hge']
    · refine dispatchNext_repeat rfl (DispatchLt.rank rfl (by simp [μ, rank])) (sep_lift.mpr ⟨?_, ha⟩)
      have hnil : xs.drop i.toNat = [] := List.drop_eq_nil_of_le (by omega)
      refine ⟨hle, ?_⟩
      simp only [hnil, tokens] at hc ⊢
      exact hc

/-- `done` leaves the loop with the answer. -/
theorem step_done (sl : Slice) (xs : List (BitVec 8)) (s : countTokensLocals)
    (hk : s.dispatchValue10 = .done) :
    TotalTriple (inv sl xs .done s) ((countTokens.loop10 sl).run s) (next sl xs s) := by
  apply TotalTriple.of_run
  intro m h hF hd hm hi hst
  obtain ⟨hc, ha⟩ := sep_lift.mp hi
  refine ⟨(.br9, s), m, h, ?_, hd, hm, dispatchNext_exit rfl (sep_lift.mpr ⟨⟨rfl, hc⟩, ha⟩), hst⟩
  simp [countTokens.loop10, zig_unfold, hk]

/-- The generated loop-switch, by the dispatch template: one premise per state. -/
theorem loop_total (sl : Slice) (xs : List (BitVec 8)) (hlen : sl.len.toNat = xs.length)
    (s : countTokensLocals) (h0 : s.i = 0) (hc : s.count = 0) (hk : s.dispatchValue10 = .start) :
    TotalTriple (arr sl.ptr xs) ((Zig.loop (countTokens.loop10 sl) countTokens.again10).run s)
      (fun r => post sl xs r.1 r.2) := by
  dispatch_template (inv sl xs) (μ xs) (post sl xs)
  case start => exact step_start sl xs hlen
  case ident => exact step_ident sl xs hlen
  case number => exact step_number sl xs hlen
  case done => exact step_done sl xs
  case entry =>
    intro h ha
    rw [hk]
    exact sep_lift.mpr ⟨⟨by simp [h0], by simp [h0, hc]⟩, ha⟩

/-- info: dispatch_template remaining premises (5):
  step.start : ∀ (s : countTokensLocals),
  s.dispatchValue10 = State.start →
    TotalTriple (inv sl xs State.start s) (StateT.run (countTokens.loop10 sl) s)
      (dispatchNext countTokens.again10 (fun s => s.dispatchValue10) (inv sl xs) (μ xs) (post sl xs) s)
  step.ident : ∀ (s : countTokensLocals),
  s.dispatchValue10 = State.ident →
    TotalTriple (inv sl xs State.ident s) (StateT.run (countTokens.loop10 sl) s)
      (dispatchNext countTokens.again10 (fun s => s.dispatchValue10) (inv sl xs) (μ xs) (post sl xs) s)
  step.number : ∀ (s : countTokensLocals),
  s.dispatchValue10 = State.number →
    TotalTriple (inv sl xs State.number s) (StateT.run (countTokens.loop10 sl) s)
      (dispatchNext countTokens.again10 (fun s => s.dispatchValue10) (inv sl xs) (μ xs) (post sl xs) s)
  step.done : ∀ (s : countTokensLocals),
  s.dispatchValue10 = State.done →
    TotalTriple (inv sl xs State.done s) (StateT.run (countTokens.loop10 sl) s)
      (dispatchNext countTokens.again10 (fun s => s.dispatchValue10) (inv sl xs) (μ xs) (post sl xs) s)
  entry : ∀ (h : Heap), arr sl.ptr xs h → inv sl xs s.dispatchValue10 s h -/
#guard_msgs in
-- The report on the generated machine: one premise per Zig enum state, plus the entry.
example (sl : Slice) (xs : List (BitVec 8)) (hlen : sl.len.toNat = xs.length)
    (s : countTokensLocals) (h0 : s.i = 0) (hc : s.count = 0) (hk : s.dispatchValue10 = .start) :
    TotalTriple (arr sl.ptr xs) ((Zig.loop (countTokens.loop10 sl) countTokens.again10).run s)
      (fun r => post sl xs r.1 r.2) := by
  dispatch_template? (inv sl xs) (μ xs) (post sl xs)
  case start => exact step_start sl xs hlen
  case ident => exact step_ident sl xs hlen
  case number => exact step_number sl xs hlen
  case done => exact step_done sl xs
  case entry =>
    intro h ha
    rw [hk]
    exact sep_lift.mpr ⟨⟨by simp [h0], by simp [h0, hc]⟩, ha⟩

/-- `countTokens p n` over a buffer `p` of `n` bytes `xs` returns the number of tokens of `xs`
(mod `2 ^ 32`) and leaves the buffer unchanged. -/
theorem countTokens_total (p : Ptr) (xs : List (BitVec 8)) (hlen : xs.length < 2 ^ 64) :
    TotalTriple (arr p xs) (countTokens p (BitVec.ofNat 64 xs.length))
      (fun r => ⌜r.toNat = tokens .start xs % 2 ^ 32⌝ ∗ arr p xs) := by
  have hp : p.elem 1 0 = p := by cases p; simp [Ptr.elem, Ptr.add]
  let sl : Slice := ⟨p.elem 1 0, BitVec.ofNat 64 xs.length - 0⟩
  have hsl : sl.len.toNat = xs.length := by simp [sl, Nat.mod_eq_of_lt hlen]
  apply TotalTriple.of_run
  intro m h hF hd hm ha hst
  let s0 : countTokensLocals := { (default : countTokensLocals) with
    i := 0, count := 0, dispatchValue10 := .start }
  obtain ⟨⟨e, s'⟩, m', h', hr, hd', hm', hpost, hst'⟩ :=
    loop_total sl xs hsl s0 rfl rfl rfl m h hF hd hm (by show arr (p.elem 1 0) xs h; rw [hp]; exact ha) hst
  obtain ⟨⟨rfl, hc⟩, ha'⟩ := sep_lift.mp hpost
  refine ⟨s'.count, m', h', ?_, hd', hm', sep_lift.mpr ⟨hc, by rw [← hp]; exact ha'⟩, hst'⟩
  simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hr
  simp [countTokens, zig_unfold, sl, s0] at hr ⊢
  simp [hr, zig_unfold, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.bind]

end Tok.Proof

-- Only the standard axioms: no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`).
/-- info: 'Tok.Proof.countTokens_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tok.Proof.countTokens_total
