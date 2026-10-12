import ZigLean.Sep.Bounded
import ZigLean.Sep.LoopTemplate
import ZigLean.Sep.Step

/-!
# Costs of loops that end, fail or diverge (P06)

`ZigLean/Sep/Cost.lean` counts the body runs of a loop that exits (`LoopRuns`). This file adds
the other two ways a run of `loop body again` can go, with the same unit (one body run, a model
count, SEM-05):

* **Failing runs.** `LoopFails body again s m k e`: the loop's `k`-th body run throws `e` after
  `k - 1` repeats. `LoopFails.run` is the loop's run (`throw e`), `LoopFails.unique` makes `k` and
  `e` functions of the start, and `LoopFails.not_runs` shows that such a loop has no counted exit.
  `LoopEnds` is the common form of an exit or a failure; `loopEnds_bound` bounds the body runs
  until either by a decreasing measure, so a statement can bound the work done before a failure
  (`FailsWithin`) without proving that the loop succeeds.
* **Diverging runs.** `LoopPrefix body again s m k s' m'`: `k` body runs that each repeat.
  `forever_prefix` builds a prefix of every length from an invariant that every body run keeps
  while repeating; `forever_no_end` shows that such a loop has no counted end (exit or failure)
  for any count, so its cost is unbounded and no `TotalTripleWithin` holds for any bound.
* `TotalTripleWithin.of_template`: a `LoopTemplate` (P03) at measure `n` bounds the loop by
  `n + 1` body runs, so a loop proved with the template gets its bound for free.
* `Fails P c e`: from every framed precondition, `c` throws `e`. `sep_step`/`sep_steps` walk such
  a goal as they walk a `TotalTriple` (loads, stores, array accesses, total rules for calls), and
  `Fails.throw_bind` ends it at the `throw`. `FailsWithin.of_fails` turns a failing body run into
  a failing loop after one body run.

The counts are model counts. Nothing relates them to time or native memory (SEM-05).
-/

namespace Zig

open Assn

variable {σ ε : Type} {body : MM σ ε} {again : ε → Bool}

/-! ## The bound of a templated loop -/

/-- A loop proved with `LoopTemplate` at measure `n` exits within `n + 1` body runs. -/
theorem TotalTripleWithin.of_template {inv : σ → Nat → Assn} {post : ε → σ → Assn}
    (t : LoopTemplate body again inv post) (s : σ) (n : Nat) :
    TotalTripleWithin (n + 1) (inv s n) body again s post := by
  apply TotalTripleWithin.of_ghost body again inv post _ s n
  intro hF s n m h hd hm hi hs
  obtain ⟨⟨e, s'⟩, m', h', hr, hd', hm', hnext, hs'⟩ := t.step s n m h hF hd hm hi hs
  refine ⟨e, s', m', h', hr, hd', hm', hs', ?_⟩
  cases ha : again e
  · simpa only [loopNext, ha, Bool.false_eq_true, ↓reduceIte] using hnext
  · simp only [loopNext, ha, ↓reduceIte] at hnext ⊢
    obtain ⟨n', hn'⟩ := hnext
    exact ⟨n', (sep_lift.mp hn').1, (sep_lift.mp hn').2⟩

/-! ## Failing runs -/

/-- The loop's `k`-th body run throws `e`; the `k - 1` runs before it repeat. -/
inductive LoopFails (body : MM σ ε) (again : ε → Bool) : σ → Mem → Nat → Error → Prop
  | now {s m e} : ((body.run s).run m).run = some (.error e) → LoopFails body again s m 1 e
  | next {s m e₁ s₁ m₁ k e} : (body.run s).run m = pure ((e₁, s₁), m₁) → again e₁ = true →
      LoopFails body again s₁ m₁ k e → LoopFails body again s m (k + 1) e

namespace LoopFails

/-- The failing count is the loop's run: it throws `e`. -/
theorem run {s : σ} {m : Mem} {k : Nat} {e : Error} (h : LoopFails body again s m k e) :
    (((loop body again).run s).run m).run = some (.error e) := by
  induction h with
  | now hb =>
    rw [loopMM_run]
    simp only [StateT.run_bind, ExceptT.run_bind, hb]
    rfl
  | next hb ha _ ih =>
    rw [loopMM_run]
    simp only [StateT.run_bind, ExceptT.run_bind]
    rw [show ((body.run _).run _).run = some (.ok ((_, _), _)) from congrArg ExceptT.run hb]
    simpa [ha] using ih

/-- The count and the error are functions of the start. -/
theorem unique {s : σ} {m : Mem} {k₁ k₂ : Nat} {e₁ e₂ : Error}
    (h₁ : LoopFails body again s m k₁ e₁) (h₂ : LoopFails body again s m k₂ e₂) :
    k₁ = k₂ ∧ e₁ = e₂ := by
  induction h₁ generalizing k₂ with
  | now hb =>
    cases h₂ with
    | now hb' => rw [hb] at hb'; cases hb'; exact ⟨rfl, rfl⟩
    | next hb' _ _ =>
      rw [show ((body.run _).run _).run = some (.ok ((_, _), _)) from congrArg ExceptT.run hb'] at hb
      cases hb
  | next hb ha _ ih =>
    cases h₂ with
    | now hb' =>
      rw [show ((body.run _).run _).run = some (.ok ((_, _), _)) from congrArg ExceptT.run hb] at hb'
      cases hb'
    | next hb' _ h' =>
      rw [hb] at hb'; simp only [pure, ExceptT.pure, ExceptT.mk] at hb'; cases hb'
      obtain ⟨rfl, rfl⟩ := ih h'
      exact ⟨rfl, rfl⟩

/-- A loop that fails has no counted exit. -/
theorem not_runs {s : σ} {m : Mem} {k : Nat} {e : Error} (h : LoopFails body again s m k e)
    {k' : Nat} {e' : ε} {s' : σ} {m' : Mem} : ¬ LoopRuns body again s m k' e' s' m' := by
  intro hr
  have h₁ := h.run
  rw [hr.run] at h₁
  cases h₁

end LoopFails

/-- A counted end of the loop: an exit (`LoopRuns`) or a failure (`LoopFails`) after `k` body
runs. -/
def LoopEnds (body : MM σ ε) (again : ε → Bool) (s : σ) (m : Mem) (k : Nat) : Prop :=
  (∃ e s' m', LoopRuns body again s m k e s' m') ∨ (∃ err, LoopFails body again s m k err)

/-- The work before an end is bounded by a measure: each body run either repeats with a smaller
measure, exits with `post`, or throws an error in `bad`. The loop ends within `n + 1` body runs,
and a failure is in `bad`. -/
theorem loopEnds_bound (body : MM σ ε) (again : ε → Bool)
    (inv : σ → Mem → Nat → Prop) (post : ε → σ → Mem → Prop) (bad : Error → Prop)
    (step : ∀ s m n, inv s m n →
      (∃ e s' m', (body.run s).run m = pure ((e, s'), m') ∧
        (if again e then ∃ n' < n, inv s' m' n' else post e s' m')) ∨
      (∃ err, ((body.run s).run m).run = some (.error err) ∧ bad err)) :
    ∀ s m n, inv s m n → ∃ k, k ≤ n + 1 ∧
      ((∃ e s' m', LoopRuns body again s m k e s' m' ∧ post e s' m') ∨
       (∃ err, LoopFails body again s m k err ∧ bad err)) := by
  intro s m n
  induction n using Nat.strongRecOn generalizing s m with
  | _ n ih =>
    intro hi
    rcases step s m n hi with ⟨e, s', m', hr, hn⟩ | ⟨err, hr, hbad⟩
    · cases ha : again e
      · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hn
        exact ⟨1, by omega, .inl ⟨e, s', m', .exit hr ha, hn⟩⟩
      · simp only [ha, ↓reduceIte] at hn
        obtain ⟨n', hlt, hi'⟩ := hn
        obtain ⟨k, hk, hend⟩ := ih n' hlt s' m' hi'
        refine ⟨k + 1, by omega, ?_⟩
        rcases hend with ⟨e₂, s₂, m₂, hl, hp⟩ | ⟨err, hf, hb⟩
        · exact .inl ⟨e₂, s₂, m₂, .next hr ha hl, hp⟩
        · exact .inr ⟨err, .next hr ha hf, hb⟩
    · exact ⟨1, by omega, .inr ⟨err, .now hr, hbad⟩⟩

/-- The loop from `s` fails, with an error in `bad`, within `B` body runs from every framed
precondition: a bound on the work done before the failure. (`loopEnds_bound` covers loops that
may either exit or fail.) -/
def FailsWithin (B : Nat) (P : Assn) (body : MM σ ε) (again : ε → Bool) (s : σ)
    (bad : Error → Prop) : Prop :=
  ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.Seq →
    ∃ k err, k ≤ B ∧ LoopFails body again s m k err ∧ bad err

/-- From every framed precondition, `c` throws `e`. -/
def Fails {α : Type} (P : Assn) (c : MemM α) (e : Error) : Prop :=
  ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.Seq → (c.run m).run = some (.error e)

namespace Fails

variable {α β : Type} {P P' R : Assn} {e : Error}

theorem pre {c : MemM β} (hp : ∀ h, P h → P' h) (t : Fails P' c e) : Fails P c e :=
  fun m hP hF hd hm hpre hs => t m hP hF hd hm (hp _ hpre) hs

theorem of_bind_pure {c : MemM β} (t : Fails P (c >>= pure) e) : Fails P c e := by
  simpa only [bind_pure] using t

/-- The walk ends at the `throw`. -/
theorem throw_bind (e : Error) {f : α → MemM β} : Fails P (throw e >>= f) e :=
  fun _ _ _ _ _ _ _ => rfl

theorem ex {γ : Type} {F : γ → Assn} {c : MemM β} (t : ∀ x, Fails (F x) c e) :
    Fails (Assn.ex F) c e := fun m hP hF hd hm ⟨x, hp⟩ hs => t x m hP hF hd hm hp hs

theorem lift {φ : Prop} {c : MemM β} (t : φ → Fails P c e) : Fails (⌜φ⌝ ∗ P) c e := by
  intro m hP hF hd hm hp hs
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact t hφ m hP hF hd hm hp hs

theorem ex_sep {γ : Type} {F : γ → Assn} {c : MemM β} (t : ∀ x, Fails (F x ∗ R) c e) :
    Fails (Assn.ex F ∗ R) c e :=
  pre (P' := Assn.ex fun x => F x ∗ R)
    (fun _ ⟨h₁, h₂, d, eq, ⟨x, hx⟩, hr⟩ => ⟨x, h₁, h₂, d, eq, hx, hr⟩) (ex t)

/-- A command with a total rule, framed by `R`; the rest fails. -/
theorem spec_bind {P₀ : Assn} {Q₀ : α → Assn} {c : MemM α} {f : α → MemM β}
    (rule : TotalTriple P₀ c Q₀) (k : ∀ r, Fails (Q₀ r ∗ R) (f r) e) :
    Fails (P₀ ∗ R) (c >>= f) e := by
  intro m hP hF hd hm hp hs
  obtain ⟨v, m', hQ, hr, hd', hm', hq, hs'⟩ := rule.frame (R := R) m hP hF hd hm hp hs
  have := k v m' hQ hF hd' hm' hq hs'
  rw [StateT.run_bind, ExceptT.run_bind, show (c.run m).run = some (.ok (v, m')) from
    congrArg ExceptT.run hr]
  exact this

theorem spec_bind_eq {P₀ P₁ : Assn} {c : MemM α} {v : α} {f : α → MemM β}
    (rule : TotalTriple P₀ c (fun r => ⌜r = v⌝ ∗ P₁)) (k : Fails (P₁ ∗ R) (f v) e) :
    Fails (P₀ ∗ R) (c >>= f) e :=
  spec_bind rule fun _ => pre (fun _ hp => sep_assoc hp) (lift (P := P₁ ∗ R) fun hr => hr ▸ k)

section Rules

variable {T : Type} [Enc T] {p : Ptr} {a : Nat}

theorem load_bind {v : T} {f : T → MemM β} (hn : 0 < Enc.size T)
    (k : Fails (pts p a v ∗ R) (f v) e) : Fails (pts p a v ∗ R) (Zig.load T a p >>= f) e :=
  spec_bind_eq (TotalTriple.load hn) k

theorem store_bind [LawfulEnc T] {v w : T} {f : Unit → MemM β} (hn : 0 < Enc.size T)
    (k : Fails (pts p a w ∗ R) (f ()) e) : Fails (pts p a v ∗ R) (Zig.store a p w >>= f) e :=
  spec_bind (TotalTriple.store hn w) fun () => k

theorem arr_load_bind {xs : List T} {i : BitVec 64} {f : T → MemM β}
    (hn : 0 < Enc.size T) (ha : a ∣ Enc.align T) (hs : Enc.align T ∣ Enc.size T)
    (hi : i.toNat < xs.length) (k : Fails (arr p xs ∗ R) (f xs[i.toNat]) e) :
    Fails (arr p xs ∗ R) (Zig.load T a (p.elem (Enc.size T) i) >>= f) e :=
  spec_bind_eq (TotalTriple.arr_load hn ha hs hi) k

theorem arr_store_bind [LawfulEnc T] {xs : List T} {i : BitVec 64} {w : T}
    {f : Unit → MemM β} (hn : 0 < Enc.size T) (ha : a ∣ Enc.align T)
    (hs : Enc.align T ∣ Enc.size T) (hi : i.toNat < xs.length)
    (k : Fails (arr p (xs.set i.toNat w) ∗ R) (f ()) e) :
    Fails (arr p xs ∗ R) (Zig.store a (p.elem (Enc.size T) i) w >>= f) e :=
  spec_bind (TotalTriple.arr_store hn ha hs hi w) fun () => k

theorem arr_ptrProject_bind {xs : List T} {i : BitVec 64} {f : Ptr → MemM β}
    (hi : i.toNat ≤ xs.length) (k : Fails (arr p xs ∗ R) (f (p.elem (Enc.size T) i)) e) :
    Fails (arr p xs ∗ R) (ptrProject p (·.elem (Enc.size T) i) >>= f) e :=
  spec_bind_eq (TotalTriple.arr_ptrProject hi) k

theorem arr_split_pre {xs : List T} {k : Nat} {c : MemM β} (hs : Enc.align T ∣ Enc.size T)
    (hk : k ≤ xs.length)
    (t : Fails ((arr p (xs.take k) ∗ arr (p.add (Enc.size T * k)) (xs.drop k)) ∗ R) c e) :
    Fails (arr p xs ∗ R) c e :=
  pre (fun _ => sep_mono (fun _ ha => arr_split ha hk hs) fun _ hr => hr) t

end Rules

end Fails

/-- A body run that fails is a loop that fails after one body run. -/
theorem FailsWithin.of_fails {P : Assn} {s : σ} {e : Error} {bad : Error → Prop}
    (t : Fails P (body.run s) e) (he : bad e) : FailsWithin 1 P body again s bad :=
  fun m hP hF hd hm hp hs => ⟨1, e, Nat.le_refl _, .now (t m hP hF hd hm hp hs), he⟩

/-- A failing bound refutes every success bound from the same inputs. -/
theorem FailsWithin.not_within {B B' : Nat} {P : Assn} {s : σ} {bad : Error → Prop}
    {Q : ε → σ → Assn} (h : FailsWithin B P body again s bad) {m : Mem} {hP hF : Heap}
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq) :
    ¬ TotalTripleWithin B' P body again s Q := by
  intro hw
  obtain ⟨_, _, _, hf, _⟩ := h m hP hF hd hm hp hs
  obtain ⟨_, _, _, _, _, _, hl, _⟩ := hw m hP hF hd hm hp hs
  exact hf.not_runs hl

/-! ## Diverging runs -/

/-- `k` body runs from `s`, `m`, each of which repeats, ending at `s'`, `m'`. -/
inductive LoopPrefix (body : MM σ ε) (again : ε → Bool) : σ → Mem → Nat → σ → Mem → Prop
  | zero {s m} : LoopPrefix body again s m 0 s m
  | next {s m e₁ s₁ m₁ k s' m'} : (body.run s).run m = pure ((e₁, s₁), m₁) → again e₁ = true →
      LoopPrefix body again s₁ m₁ k s' m' → LoopPrefix body again s m (k + 1) s' m'

/-- An invariant that every body run keeps while repeating gives a prefix of every length. -/
theorem forever_prefix (inv : σ → Mem → Prop)
    (step : ∀ s m, inv s m → ∃ e s' m', (body.run s).run m = pure ((e, s'), m') ∧
      again e = true ∧ inv s' m') :
    ∀ k s m, inv s m → ∃ s' m', LoopPrefix body again s m k s' m' := by
  intro k
  induction k with
  | zero => exact fun s m _ => ⟨s, m, .zero⟩
  | succ k ih =>
    intro s m hi
    obtain ⟨e, s₁, m₁, hr, ha, hi₁⟩ := step s m hi
    obtain ⟨s', m', hp⟩ := ih s₁ m₁ hi₁
    exact ⟨s', m', .next hr ha hp⟩

/-- Under such an invariant the loop has no counted end, for any count: its cost is unbounded. -/
theorem forever_no_end (inv : σ → Mem → Prop)
    (step : ∀ s m, inv s m → ∃ e s' m', (body.run s).run m = pure ((e, s'), m') ∧
      again e = true ∧ inv s' m') :
    ∀ k s m, inv s m → ¬ LoopEnds body again s m k := by
  intro k
  induction k with
  | zero =>
    intro s m _ h
    rcases h with ⟨_, _, _, hl⟩ | ⟨_, hf⟩
    · cases hl
    · cases hf
  | succ k ih =>
    intro s m hi h
    obtain ⟨e, s₁, m₁, hr, ha, hi₁⟩ := step s m hi
    rcases h with ⟨e', s', m', hl⟩ | ⟨err, hf⟩
    · cases hl with
      | exit hb ha' =>
        rw [hr] at hb; simp only [pure, ExceptT.pure, ExceptT.mk] at hb; cases hb
        rw [ha] at ha'; cases ha'
      | next hb _ hl' =>
        rw [hr] at hb; simp only [pure, ExceptT.pure, ExceptT.mk] at hb; cases hb
        exact ih s₁ m₁ hi₁ (.inl ⟨e', s', m', hl'⟩)
    · cases hf with
      | now hb =>
        rw [show ((body.run s).run m).run = some (.ok ((e, s₁), m₁)) from congrArg ExceptT.run hr]
          at hb
        cases hb
      | next hb _ hf' =>
        rw [hr] at hb; simp only [pure, ExceptT.pure, ExceptT.mk] at hb; cases hb
        exact ih s₁ m₁ hi₁ (.inr ⟨err, hf'⟩)

/-- So a diverging loop has no bounded triple, for any bound. -/
theorem forever_not_within (inv : σ → Mem → Prop)
    (step : ∀ s m, inv s m → ∃ e s' m', (body.run s).run m = pure ((e, s'), m') ∧
      again e = true ∧ inv s' m') {B : Nat} {P : Assn} {s : σ} {Q : ε → σ → Assn} {m : Mem}
    {hP hF : Heap} (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq)
    (hi : inv s m) : ¬ TotalTripleWithin B P body again s Q :=
  TotalTripleWithin.not_within_of_stuck hd hm hp hs fun k e s' m' hl =>
    forever_no_end inv step k s m hi (.inl ⟨e, s', m', hl⟩)

end Zig
