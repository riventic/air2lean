import ZigLean.Sep.LoopTemplate
import ZigLean.Range

/-!
# Loop template and range-conversion regressions

A memory-free countdown exercises the template, its premise report, the partial-correctness
form, rejection of non-loop goals, and the measure requirement. The `zig_range` examples check
proof-producing BitVec/Int/Nat conversions and that an undischarged range premise remains.
-/

open Zig Assn

namespace LoopTemplateTest

/-- Count down the state; repeat while it was nonzero. -/
def countdown : MM Nat Bool := do
  let k ← get
  if k = 0 then pure false else do modify (· - 1); pure true

def inv (s n : Nat) : Assn := ⌜n = s⌝
def post (_ : Bool) (s : Nat) : Assn := ⌜s = 0⌝

theorem countdown_step : LoopTemplate countdown id inv post := by
  constructor
  intro s n
  apply TotalTriple.of_run
  intro m h hF hd hm ⟨hn, he⟩ hst
  subst hn he
  cases n with
  | zero =>
    exact ⟨(false, 0), m, Heap.empty, by simp [countdown, zig_unfold], hd, hm,
      loopNext_exit rfl ⟨rfl, rfl⟩, hst⟩
  | succ k =>
    exact ⟨(true, k), m, Heap.empty, by simp [countdown, zig_unfold], hd, hm,
      loopNext_repeat rfl (Nat.lt_succ_self k) ⟨rfl, rfl⟩, hst⟩

/-- info: loop_template remaining premises (3):
  step : LoopTemplate countdown id inv post
  entry : ∀ (h : Heap), ⌜True⌝ h → ∃ n, inv 5 n h
  exit : ∀ (e : Bool) (s' : Nat) (h : Heap), post e s' h → ⌜s' ≤ 0⌝ h -/
#guard_msgs in
-- The report lists each remaining premise; `exit` stays because the goal's postcondition differs.
example : TotalTriple ⌜True⌝ ((Zig.loop countdown id).run 5) (fun r => ⌜r.2 ≤ 0⌝) := by
  loop_template? inv post
  case step => exact countdown_step
  case entry => exact fun h ⟨_, he⟩ => ⟨5, rfl, he⟩
  case exit => exact fun _ _ _ ⟨hs, he⟩ => ⟨Nat.le_of_eq hs, he⟩

-- `exit` is discharged when the template's postcondition is the goal's; partial goals also work.
example (s : Nat) : Triple (inv s s) ((Zig.loop countdown id).run s) (fun r => post r.1 r.2) := by
  loop_template inv post
  case step => exact countdown_step
  case entry => exact fun h hi => ⟨s, hi⟩

-- A goal that is not about a generated loop is rejected.
example : TotalTriple emp (pure 0 : MemM Nat) (fun _ => emp) := by
  fail_if_success loop_template inv post
  exact TotalTriple.ret (Q := fun _ => emp) 0

/-- A body that always repeats. -/
def spin : MM Nat Bool := pure true

-- The measure is not optional: at measure `0` a repeating body cannot meet the step premise.
example (I : Nat → Nat → Assn) (Q : Bool → Nat → Assn) (m : Mem) (hP hF : Heap)
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hi : I 0 0 hP) (hs : m.Seq) :
    ¬ LoopTemplate spin id I Q := by
  intro t
  obtain ⟨⟨e, s'⟩, m', h', hr, -, -, hnext, -⟩ := t.step 0 0 m hP hF hd hm hi hs
  simp only [spin, StateT.run, pure, StateT.pure, ExceptT.pure, ExceptT.mk] at hr
  cases hr
  obtain ⟨n', hn'⟩ := hnext
  exact Nat.not_lt_zero _ (sep_lift.mp hn').1

end LoopTemplateTest

namespace RangeTest

example (a b : BitVec 8) (h : a.toNat + b.toNat < 200) :
    (a + b).toNat = a.toNat + b.toNat := by
  zig_range

example (a b : BitVec 64) (h : a.toNat + b.toNat < 2 ^ 64) : Zig.add false a b = pure (a + b) := by
  zig_range

example (a b : BitVec 32) (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat := by
  zig_range

example (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  zig_range

example (a : BitVec 16) (h : a.toNat < 100) : a.toInt = (a.toNat : Int) := by
  zig_range

example (k : Nat) (h : k < 256) : (BitVec.ofInt 8 (k : Int)).toNat = k := by
  zig_range

-- Narrowing `@intCast` succeeds in range, without evaluating the width.
example (a : BitVec 64) (h : a.toNat < 256) :
    Zig.intCast false false 8 a = pure (BitVec.ofNat 8 a.toNat) := by
  zig_range

-- Without a range premise, nothing is rewritten: the wrapping sum stays as it is.
example (a b : BitVec 8) : (a + b).toNat = (a.toNat + b.toNat) % 256 := by
  fail_if_success zig_range
  simp [BitVec.toNat_add]

-- A sum of at most 2 ^ 32 items of width 32 fits in 64 bits.
example (xs : List (BitVec 32)) (h : xs.length ≤ 2 ^ 32) :
    (xs.map BitVec.toNat).sum < 2 ^ 64 :=
  sum_toNat_lt (k := 32) xs h

end RangeTest
