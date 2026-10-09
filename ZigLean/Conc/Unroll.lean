import ZigLean.Conc.Sched
import ZigLean.Conc.Call
import ZigLean.Conc.Witness

/-!
# Runs of programs with loops, by the kernel

`Zig.loop` is a `partial_fixpoint`: the least fixpoint of its unfolding, which the kernel does
not compute. `loopN body again k` is the loop cut after `k` runs of its body: `⊥` (no result)
where the loop would go on. It is below the loop (`loopN_le_loop`), so a result of the cut loop
is the loop's result.

`unroll_sched k` closes a goal `Witness.okVal (Sched.run dispatch fuel o main m₀) = some v`
about a program with loops: it builds the program and every thread with each `Zig.loop` cut
after `k` iterations (`Unroll.expand`), proves the cut program below the program
(`monotonicity`), and lets the kernel compute the cut run (`decide +kernel`). A run of the cut
program that has a result is a run of the program (`Sched.run_le`), so a goal that the kernel
decides is proved for the program; a cut loop that would need more than `k` iterations leaves
the run without a result and the goal fails. Not imported by `ZigLean.lean`; see
docs/proof-tools.md.
-/

namespace Zig

open Lean.Order

/-! ## The cut loop -/

section Loop

variable {m : Type → Type} [Monad m] [∀ α, CCPO (m α)] [MonoBind m] {ε : Type}

/-- `loop body again` cut after `k` iterations: `⊥` where the loop would go on. -/
noncomputable def loopN (body : m ε) (again : ε → Bool) : Nat → m ε
  | 0 => bot
  | k + 1 => do
    let e ← body
    if again e then loopN body again k else pure e

theorem loopN_le_loop (body : m ε) (again : ε → Bool) : ∀ k, loopN body again k ⊑ loop body again
  | 0 => bot_le _
  | k + 1 => by
    rw [loop.eq_1]
    apply MonoBind.bind_mono_right
    intro e
    split
    · exact loopN_le_loop body again k
    · exact PartialOrder.rel_refl

theorem monotone_loopN_body {γ : Type} [PartialOrder γ] (f : γ → m ε) (hf : monotone f)
    (again : ε → Bool) : ∀ k, monotone (fun x => loopN (f x) again k)
  | 0 => monotone_const _
  | k + 1 => by
    apply monotone_bind _ _ _ hf
    apply monotone_of_monotone_apply
    intro e
    split
    · exact monotone_loopN_body f hf again k
    · exact monotone_const _

/-- `loop` is monotone in its body (`Zig.monotone_loop` for any monad). -/
theorem monotone_loop_body {γ : Type} [PartialOrder γ] (f : γ → m ε) (hf : monotone f)
    (again : ε → Bool) : monotone (fun x => loop (f x) again) := by
  intro x₁ x₂ hx
  have hle : f x₁ ⊑ f x₂ := hf x₁ x₂ hx
  apply loop.fixpoint_induct (f x₁) again (motive := fun v => v ⊑ loop (f x₂) again)
  · exact fun _ hc h => csup_le hc h
  · intro l hl
    rw [loop.eq_1 (f x₂) again]
    apply PartialOrder.rel_trans (MonoBind.bind_mono_left hle)
    apply MonoBind.bind_mono_right
    intro e
    split
    · exact hl
    · exact PartialOrder.rel_refl

end Loop

namespace Unroll

/-- Which loop a program runs: the loop cut after some iterations, or the loop itself
(`approx ⊑ exact`). -/
inductive Sel where
  | approx
  | exact

instance instPartialOrderSel : PartialOrder Sel where
  rel x y := x = .approx ∨ x = y
  rel_refl := .inr rfl
  rel_trans := by
    rintro x y z (h | rfl) h' <;> first | exact .inl h | exact h'
  rel_antisymm := by
    rintro x y (rfl | rfl) (h | h) <;> first | rfl | exact h.symm

theorem approx_le : (Sel.approx ⊑ Sel.exact) := .inl rfl

variable {m : Type → Type} [Monad m] [∀ α, CCPO (m α)] [MonoBind m] {ε : Type}

/-- `Zig.loop` in a program built by `Unroll.expand`: cut after `k` iterations at `approx`,
the loop itself at `exact`. -/
noncomputable def loopSel (k : Nat) (s : Sel) (body : m ε) (again : ε → Bool) : m ε :=
  match s with
  | .approx => loopN body again k
  | .exact => loop body again

@[partial_fixpoint_monotone]
theorem monotone_loopSel {γ : Type} [PartialOrder γ] (k : Nat) (s : γ → Sel) (hs : monotone s)
    (f : γ → m ε) (hf : monotone f) (again : ε → Bool) :
    monotone (fun x => loopSel k (s x) (f x) again) := by
  intro x₁ x₂ hx
  show loopSel k (s x₁) (f x₁) again ⊑ loopSel k (s x₂) (f x₂) again
  apply PartialOrder.rel_trans (y := loopSel k (s x₁) (f x₂) again)
  · cases s x₁
    · exact monotone_loopN_body f hf again k x₁ x₂ hx
    · exact monotone_loop_body f hf again x₁ x₂ hx
  · rcases hs x₁ x₂ hx with h | h <;> rw [h]
    · cases s x₂
      · exact PartialOrder.rel_refl
      · exact loopN_le_loop _ _ k

/-- `discard` (a thread's result dropped by the dispatcher) is monotone. -/
@[partial_fixpoint_monotone]
theorem monotone_discard {γ α : Type} [PartialOrder γ] [LawfulMonad m] (f : γ → m α)
    (hf : monotone f) : monotone (fun x => Functor.discard (f x)) := by
  have h : ∀ x, Functor.discard (f x) = f x >>= fun _ => pure PUnit.unit := fun x => by
    simp only [Functor.discard, map_const, Function.comp_apply, map_eq_pure_bind]
  simp only [h]
  exact monotone_bind _ _ _ hf (monotone_const _)

/-! ## Cutting the loops of a program -/

open Lean Meta

/-- The definitions reachable from `roots` that run a `Zig.loop`, directly or through another
definition (a least fixpoint over the reachable definitions). -/
def loopRunners (roots : Array Name) : MetaM NameSet := do
  let env ← getEnv
  let mut uses : Std.HashMap Name (Array Name) := {}
  let mut todo := roots
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    unless uses.contains c do
      let used := match env.find? c with
        | some (.defnInfo d) => d.value.getUsedConstants
        | _ => #[]
      uses := uses.insert c used
      todo := todo ++ used
  let mut runs : NameSet := NameSet.empty.insert ``Zig.loop
  let mut changed := true
  while changed do
    changed := false
    for (c, used) in uses do
      if !runs.contains c && used.any runs.contains then
        runs := runs.insert c
        changed := true
  return runs

/-- `e` with every definition in `runs` unfolded and every `Zig.loop body again` replaced by
`loopSel k s body again`. -/
def expandCore (runs : NameSet) (k s : Expr) (e : Expr) : MetaM Expr :=
  Meta.transform e (skipConstInApp := true) (post := fun e => do
    let .const c ls := e.getAppFn | return .done e
    if c == ``Zig.loop then
      let args := e.getAppArgs
      unless args.size == 7 do throwError "unroll: `Zig.loop` applied to {args.size} arguments"
      return .done (mkAppN (.const ``loopSel []) #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!,
        k, s, args[5]!, args[6]!])
    unless runs.contains c do return .done e
    let some (.defnInfo d) := (← getEnv).find? c | throwError "unroll: {c} is not a definition"
    if d.value.getUsedConstants.contains ``Lean.Order.fix then
      throwError "unroll: {c} is a `partial_fixpoint`, which `unroll_sched` does not cut"
    return .visit ((d.value.instantiateLevelParams d.levelParams ls).beta e.getAppArgs))

/-- `monotone (fun s => c a₁ … aₙ)` with `c` unfolded: for a definition that takes a program as
an argument (a dispatcher with its std ops) and has no monotonicity lemma of its own. -/
def unfoldHead? (goal : MVarId) : MetaM (Option MVarId) := do
  let ty ← goal.getType
  let_expr monotone _ _ _ _ f := ty | return none
  let .lam n d body bi := f | return none
  let .const c ls := body.getAppFn | return none
  let some (.defnInfo info) := (← getEnv).find? c | return none
  if c.getRoot == `Lean then return none
  let body' := (info.value.instantiateLevelParams info.levelParams ls).beta body.getAppArgs
  return some (← goal.replaceTargetDefEq (mkApp ty.appFn! (.lam n d body' bi)))

/-- `Lean.Meta.Monotonicity.solveMono`, unfolding a definition where no rule applies. -/
def solveMono (goal : MVarId) : MetaM Unit := do
  let mut todo := [goal]
  while true do
    let g :: rest := todo | break
    let gs ← try Monotonicity.solveMonoStep (goal := g) catch ex => do
      let some g' ← unfoldHead? g | throw ex
      pure [g']
    todo := gs ++ rest

/-- `fun s => e'` where `e'` is `e` with its loops cut after `k` iterations at `s = approx`
(`expandCore`, unfolding the definitions in `runs`), and a proof that it is monotone. At `exact`
it is `e` (by unfolding). -/
def expand (runs : NameSet) (k : Nat) (e : Expr) : MetaM (Expr × Expr) := do
  let f ← withLocalDeclD `s (mkConst ``Sel) fun s => do
    mkLambdaFVars #[s] (← expandCore runs (mkNatLit k) s e)
  let ty ← inferType e
  let inst ← synthInstance (← mkAppM ``PartialOrder #[ty])
  let goal ← mkFreshExprMVar
    (← mkAppOptM ``monotone #[mkConst ``Sel, mkConst ``instPartialOrderSel, ty, inst, f])
  solveMono goal.mvarId!
  return (f, ← instantiateMVars goal)

end Unroll

/-! ## Runs of programs below each other -/

namespace Sched

variable {Tgt α : Type}

/-- A paused thread below another: the same depth and op, each rest below. -/
inductive PausedLe {β : Type} : Paused Tgt β → Paused Tgt β → Prop where
  | mk (d : Nat) (op : SyncOp Tgt) (k₁ k₂ : op.Resp → Mem → CoN Tgt (β × Mem) d)
      (h : ∀ r m, CoN.le (k₁ r m) (k₂ r m)) : PausedLe ⟨d, op, k₁⟩ ⟨d, op, k₂⟩

/-- A thread below another: both ended, or both paused, the first below. -/
inductive TSLe {β : Type} : TS Tgt β → TS Tgt β → Prop where
  | done : TSLe .done .done
  | paused {p₁ p₂ : Paused Tgt β} (h : PausedLe p₁ p₂) : TSLe (.paused p₁) (.paused p₂)

/-- A thread without its rest: what the scheduler looks at to pick a thread. -/
def TS.erase {β : Type} : TS Tgt β → TS Tgt β
  | .paused ⟨d, op, _⟩ => .paused ⟨d, op, fun _ _ => .leaf none⟩
  | .done => .done

theorem TSLe.erase {β : Type} {a b : TS Tgt β} (h : TSLe a b) : a.erase = b.erase := by
  cases h with
  | done => rfl
  | paused h => cases h; rfl

/-- A scheduler state below another: the same memory and step, each thread below. -/
structure StateLe (s₁ s₂ : State Tgt α) : Prop where
  main : TSLe s₁.main s₂.main
  size : s₁.kids.size = s₂.kids.size
  kids : ∀ i (h₁ : i < s₁.kids.size) (h₂ : i < s₂.kids.size), TSLe s₁.kids[i] s₂.kids[i]
  mem : s₁.mem = s₂.mem
  step : s₁.step = s₂.step

/-- A state without the rests of its threads and its trace. -/
def State.erase (s : State Tgt α) : State Tgt α :=
  { s with main := s.main.erase, kids := s.kids.map TS.erase, trace := #[] }

theorem StateLe.erase {s₁ s₂ : State Tgt α} (h : StateLe s₁ s₂) : s₁.erase = s₂.erase := by
  have hk : s₁.kids.map TS.erase = s₂.kids.map TS.erase :=
    Array.ext (by simp [h.size]) fun i h₁ h₂ => by
      simp only [Array.getElem_map]
      exact (h.kids i (by simpa using h₁) (by simpa using h₂)).erase
  simp only [State.erase, h.main.erase, hk, h.mem, h.step]

theorem isDone_erase (s : State Tgt α) (t : ThreadId) : s.erase.isDone t = s.isDone t := by
  rcases s with ⟨main, kids, mem, step, trace⟩
  unfold State.isDone State.erase
  split
  · cases main with
    | done => rfl
    | paused p => rfl
  · simp only [Array.getElem?_map]
    rcases kids[t - 1]? with _ | (_ | _) <;> rfl

theorem canGo_erase (s : State Tgt α) (t : ThreadId) (op : SyncOp Tgt) :
    canGo s.erase t op = canGo s t op := by
  cases op <;> simp only [canGo, isDone_erase] <;> rfl

theorem ready_erase (s : State Tgt α) : s.erase.ready = s.ready := by
  unfold State.ready
  simp only [canGo_erase]
  rcases s with ⟨main, kids, mem, step, trace⟩
  simp only [State.erase]
  congr 1
  · cases main with
    | done => rfl
    | paused p => rfl
  · rw [Array.zipIdx_map, Array.filterMap_map]
    congr 1
    funext ⟨ts, i⟩
    cases ts with
    | done => rfl
    | paused p => rfl

theorem anyRunning_erase (s : State Tgt α) : s.erase.anyRunning = s.anyRunning := by
  rcases s with ⟨main, kids, mem, step, trace⟩
  simp only [State.anyRunning, State.erase, Array.any_map]
  congr 1
  · cases main with
    | done => rfl
    | paused p => rfl
  · congr 1
    funext ts
    cases ts with
    | done => rfl
    | paused p => rfl

theorem StateLe.withMem {s₁ s₂ : State Tgt α} (h : StateLe s₁ s₂) (m : Mem) :
    StateLe { s₁ with mem := m } { s₂ with mem := m } :=
  ⟨h.main, h.size, h.kids, rfl, h.step⟩

/-- One turn's result below another's: no result, the same error, or the same value with each
thread and the state below. -/
def ResLe {β : Type} : Except (Option Error) (TS Tgt β × Option β × State Tgt α) →
    Except (Option Error) (TS Tgt β × Option β × State Tgt α) → Prop
  | .error none, _ => True
  | .error (some e), r => r = .error (some e)
  | .ok (ts₁, v₁, s₁), .ok (ts₂, v₂, s₂) => TSLe ts₁ ts₂ ∧ v₁ = v₂ ∧ StateLe s₁ s₂
  | .ok _, .error _ => False

theorem settle_le {β : Type} (t : ThreadId) {s₁ s₂ : State Tgt α} (hs : StateLe s₁ s₂) {n : Nat}
    {x₁ x₂ : CoN Tgt (β × Mem) n} (hx : CoN.le x₁ x₂) :
    ResLe (settle t s₁ x₁) (settle t s₂ x₂) := by
  cases hx with
  | bot => trivial
  | leaf r =>
    rcases r with e | ⟨v, m⟩
    · rfl
    · simp only [settle]
      rcases (Thread.checkJoinedByChild t |>.run m).run with _ | _ | ⟨_, m'⟩
      · trivial
      · rfl
      · exact ⟨.done, rfl, hs.withMem m'⟩
  | sync op m₀ k₁ k₂ h => exact ⟨.paused (.mk _ op k₁ k₂ h), rfl, hs.withMem m₀⟩

theorem choose_le {s₁ s₂ : State Tgt α} (hs : StateLe s₁ s₂) (o : Nat → Nat) (n : Nat) :
    (s₁.choose o n).1 = (s₂.choose o n).1 ∧ StateLe (s₁.choose o n).2 (s₂.choose o n).2 :=
  ⟨by simp [State.choose, hs.step], ⟨hs.main, hs.size, hs.kids, hs.mem, by simp [State.choose, hs.step]⟩⟩

theorem turnTrace_le {β : Type} {D₁ D₂ : Tgt → ConcM Tgt Unit}
    (hD : ∀ t n m, CoN.le (D₁ t n m) (D₂ t n m)) (fuel : Nat) (o : Nat → Nat) (t : ThreadId)
    {s₁ s₂ : State Tgt α} (hs : StateLe s₁ s₂) {p₁ p₂ : Paused Tgt β} (hp : PausedLe p₁ p₂) :
    ResLe (turnTrace D₁ fuel o t s₁ p₁).1 (turnTrace D₂ fuel o t s₂ p₂).1 := by
  rcases s₁ with ⟨main₁, kids₁, mem, step, tr₁⟩
  rcases s₂ with ⟨main₂, kids₂, mem₂, step₂, tr₂⟩
  obtain ⟨hm, hsz, hk, hmem, hstep⟩ := hs
  simp only at hm hsz hk hmem hstep
  subst hmem hstep
  have hs : ∀ m st tr₁ tr₂, StateLe (Tgt := Tgt) (α := α)
      { main := main₁, kids := kids₁, mem := m, step := st, trace := tr₁ }
      { main := main₂, kids := kids₂, mem := m, step := st, trace := tr₂ } :=
    fun _ _ _ _ => ⟨hm, hsz, hk, rfl, rfl⟩
  cases hp with
  | mk d op k₁ k₂ h =>
  cases op with
  | yield => exact settle_le t (hs _ _ _ _) (h _ _)
  | choose n => exact settle_le t (hs _ _ _ _) (h _ _)
  | pick count => exact settle_le t (hs _ _ _ _) (h _ _)
  | spawn tgt =>
    have hpush : ∀ m st tr₁ tr₂, StateLe (Tgt := Tgt) (α := α)
        { main := main₁, kids := kids₁.push (.paused ⟨fuel, .yield, fun _ m => D₁ tgt fuel m⟩),
          mem := m, step := st, trace := tr₁ }
        { main := main₂, kids := kids₂.push (.paused ⟨fuel, .yield, fun _ m => D₂ tgt fuel m⟩),
          mem := m, step := st, trace := tr₂ } := by
      refine fun _ _ _ _ => ⟨hm, by simp [hsz], fun i h₁ h₂ => ?_, rfl, rfl⟩
      simp only [Array.getElem_push]
      by_cases hi : i < kids₁.size
      · simp only [hi, hsz ▸ hi, ↓reduceDIte]
        exact hk i _ _
      · simp only [hi, hsz ▸ hi, ↓reduceDIte]
        exact .paused (.mk _ _ _ _ fun _ m => hD tgt fuel m)
    simp only [turnTrace, State.onMem]
    split
    · exact settle_le t (hpush _ _ _ _) (h _ _)
    · rfl
    · trivial
  | join tid =>
    simp only [turnTrace, State.onMem]
    split
    · exact settle_le t (hs _ _ _ _) (h _ _)
    · rfl
    · trivial
  | wait ptr e =>
    simp only [turnTrace, State.onMem]
    split
    · rename_i b _ _
      cases b
      · exact settle_le t (hs _ _ _ _) (h _ _)
      · exact ⟨.paused (.mk _ _ _ _ h), rfl, hs _ _ _ _⟩
    · rfl
    · trivial
  | wake ptr n =>
    simp only [turnTrace, State.onMem]
    split
    · exact settle_le t (hs _ _ _ _) (h _ _)
    · rfl
    · trivial

theorem StateLe.setKid {s₁ s₂ : State Tgt α} (hs : StateLe s₁ s₂) (j : Nat) {ts₁ ts₂ : TS Tgt Unit}
    (ht : TSLe ts₁ ts₂) : StateLe { s₁ with kids := s₁.kids.set! j ts₁ } { s₂ with kids := s₂.kids.set! j ts₂ } := by
  refine ⟨hs.main, by simp [hs.size], fun i h₁ h₂ => ?_, hs.mem, hs.step⟩
  simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] at h₁ h₂ ⊢
  rw [Array.getElem_setIfInBounds h₁, Array.getElem_setIfInBounds h₂]
  split
  · exact ht
  · exact hs.kids i h₁ h₂

theorem go_le {D₁ D₂ : Tgt → ConcM Tgt Unit} (hD : ∀ t n m, CoN.le (D₁ t n m) (D₂ t n m))
    (o : Nat → Nat) : ∀ (fuel : Nat) {s₁ s₂ : State Tgt α}, StateLe s₁ s₂ → ∀ {r},
      (go D₁ o fuel s₁).1 = some r → (go D₂ o fuel s₂).1 = some r
  | 0, _, _, _, _, h => by simp [go] at h
  | fuel + 1, s₁, s₂, hs, r, h => by
    have hr : s₁.ready = s₂.ready := by rw [← ready_erase, hs.erase, ready_erase]
    have ha : s₁.anyRunning = s₂.anyRunning := by rw [← anyRunning_erase, hs.erase, anyRunning_erase]
    obtain ⟨hc, hs'⟩ := choose_le hs o s₂.ready.size
    simp only [go] at h ⊢
    rw [hr, ha] at h
    split at h
    · rename_i hne
      simp only [hne, ↓reduceIte]
      exact h
    rename_i hne
    simp only [hne, ↓reduceIte]
    revert h hc hs'
    generalize s₁.choose o s₂.ready.size = c₁
    generalize s₂.choose o s₂.ready.size = c₂
    rcases c₁ with ⟨i, s₁'⟩
    rcases c₂ with ⟨i₂, s₂'⟩
    intro hc hs' h
    simp only at hc hs' h ⊢
    subst hc
    split at h
    · simp only [‹_ = 0›, ↓reduceIte]
      have hm := hs'.main
      revert h hm
      generalize s₁'.main = m₁
      generalize s₂'.main = m₂
      intro h hm
      cases hm with
      | done => exact h
      | @paused p₁ p₂ hp =>
        have ht := turnTrace_le hD fuel o 0 hs' hp
        simp only at h ⊢
        revert h ht
        generalize turnTrace D₁ fuel o 0 s₁' p₁ = x₁
        generalize turnTrace D₂ fuel o 0 s₂' p₂ = x₂
        rcases x₁ with ⟨(⟨_ | e⟩ | ⟨ts₁, (_ | v₁), t₁⟩), tr₁⟩ <;> intro h ht <;> simp only at h
        · simp [outOf] at h
        · simp only [ResLe] at ht
          rw [ht]
          exact h
        · rcases x₂ with ⟨(_ | ⟨ts₂, v₂, t₂⟩), tr₂⟩
          · exact ht.elim
          · obtain ⟨hts, hv, hst⟩ := ht
            subst hv
            exact go_le hD o fuel (s₁ := { t₁ with main := ts₁ }) (s₂ := { t₂ with main := ts₂ })
              ⟨hts, hst.size, hst.kids, hst.mem, hst.step⟩ h
        · rcases x₂ with ⟨(_ | ⟨ts₂, v₂, t₂⟩), tr₂⟩
          · exact ht.elim
          · obtain ⟨-, hv, hst⟩ := ht
            subst hv
            simp only [← hst.mem]
            exact h
    · simp only [‹¬_ = 0›, ↓reduceIte]
      rename_i t0
      obtain ⟨p₁, p₂, hk₁, hk₂, hp⟩ : ∃ p₁ p₂, s₁'.kids[s₂.ready[i]! - 1]? = some (.paused p₁) ∧
          s₂'.kids[s₂.ready[i]! - 1]? = some (.paused p₂) ∧ PausedLe p₁ p₂ := by
        revert h
        generalize s₂.ready[i]! - 1 = j
        intro h
        by_cases hj : j < s₁'.kids.size
        · have hj₂ : j < s₂'.kids.size := hs'.size ▸ hj
          have hkj := hs'.kids j hj hj₂
          rw [Array.getElem?_eq_getElem hj] at h ⊢
          rw [Array.getElem?_eq_getElem hj₂]
          revert h hkj
          generalize s₁'.kids[j] = k₁
          generalize s₂'.kids[j] = k₂
          intro h hkj
          cases hkj with
          | done => simp at h
          | @paused p₁ p₂ hp => exact ⟨p₁, p₂, rfl, rfl, hp⟩
        · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hj)] at h
          simp at h
      rw [hk₁] at h
      rw [hk₂]
      have ht := turnTrace_le hD fuel o (s₂.ready[i]!) hs' hp
      simp only at h ⊢
      revert h ht
      generalize turnTrace D₁ fuel o _ s₁' p₁ = x₁
      generalize turnTrace D₂ fuel o _ s₂' p₂ = x₂
      rcases x₁ with ⟨(⟨_ | e⟩ | ⟨ts₁, v₁, t₁⟩), tr₁⟩ <;> intro h ht <;> simp only at h
      · simp [outOf] at h
      · simp only [ResLe] at ht
        rw [ht]
        exact h
      · rcases x₂ with ⟨(_ | ⟨ts₂, v₂, t₂⟩), tr₂⟩
        · exact ht.elim
        · obtain ⟨hts, -, hst⟩ := ht
          exact go_le hD o fuel (hst.setKid _ hts) h

theorem runTrace_le {D₁ D₂ : Tgt → ConcM Tgt Unit} {P₁ P₂ : ConcM Tgt α} (hD : D₁ ⊑ D₂)
    (hP : P₁ ⊑ P₂) {fuel : Nat} {o : Nat → Nat} {m₀ : Mem} {r : Except Error (α × Mem)}
    (h : (runTrace D₁ fuel o P₁ m₀).1 = some r) : (runTrace D₂ fuel o P₂ m₀).1 = some r := by
  have hD' : ∀ t n m, CoN.le (D₁ t n m) (D₂ t n m) := fun t => hD t
  have hs := settle_le 0 (s₁ := (⟨.done, #[], { m₀ with current := 0 }, 0, #[]⟩ : State Tgt α))
    (s₂ := ⟨.done, #[], { m₀ with current := 0 }, 0, #[]⟩) ⟨.done, rfl, fun _ h => absurd h (by simp), rfl, rfl⟩
    (hP fuel { m₀ with current := 0 })
  simp only [runTrace] at h ⊢
  revert h hs
  generalize settle 0 _ (P₁ fuel _) = x₁
  generalize settle 0 _ (P₂ fuel _) = x₂
  rcases x₁ with (⟨_ | e⟩ | ⟨ts₁, (_ | v₁), t₁⟩) <;> intro h ht <;> simp only at h
  · simp [outOf] at h
  · simp only [ResLe] at ht
    rw [ht]
    exact h
  · rcases x₂ with (_ | ⟨ts₂, v₂, t₂⟩)
    · exact ht.elim
    · obtain ⟨hts, hv, hst⟩ := ht
      subst hv
      exact go_le hD' o fuel (s₁ := { t₁ with main := ts₁ }) (s₂ := { t₂ with main := ts₂ })
        ⟨hts, hst.size, hst.kids, hst.mem, hst.step⟩ h
  · rcases x₂ with (_ | ⟨ts₂, v₂, t₂⟩)
    · exact ht.elim
    · obtain ⟨-, hv, hst⟩ := ht
      subst hv
      simp only [← hst.mem]
      exact h

/-- **A run of a program below another is a run of it**: where every thread of the first
program has a result, the second has the same. -/
theorem run_le {D₁ D₂ : Tgt → ConcM Tgt Unit} {P₁ P₂ : ConcM Tgt α} (hD : D₁ ⊑ D₂)
    (hP : P₁ ⊑ P₂) {fuel : Nat} {o : Nat → Nat} {m₀ : Mem} {r : Except Error (α × Mem)}
    (h : (run D₁ fuel o P₁ m₀).run = some r) : (run D₂ fuel o P₂ m₀).run = some r :=
  runTrace_le hD hP h

theorem okVal_le {D₁ D₂ : Tgt → ConcM Tgt Unit} {P₁ P₂ : ConcM Tgt (Except ErrName (BitVec 32))}
    (hD : D₁ ⊑ D₂) (hP : P₁ ⊑ P₂) {fuel : Nat} {o : Nat → Nat} {m₀ : Mem} {v : Nat}
    (h : Witness.okVal (run D₁ fuel o P₁ m₀) = some v) : Witness.okVal (run D₂ fuel o P₂ m₀) = some v := by
  unfold Witness.okVal at h ⊢
  split at h
  · rename_i hr
    rw [run_le hD hP hr]
    exact h
  · contradiction

end Sched

end Zig

namespace Zig.Unroll

open Lean Meta Elab Tactic

/-- `unroll_sched k` proves `Witness.okVal (Sched.run dispatch fuel o main m₀) = some v`: it cuts
every loop of `dispatch` and `main` after `k` iterations (`expand`), reduces the goal to the run
of the cut program (`Sched.okVal_le`) and lets the kernel decide it (`decide +kernel`). -/
elab "unroll_sched " k:num : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some run := ty.find? (·.isAppOfArity ``Sched.run 7)
    | throwError "unroll_sched: the goal has no `Sched.run dispatch fuel o main m₀`"
  let args := run.getAppArgs
  let_expr Eq _ lhs _ := ty | throwError "unroll_sched: the goal is not an equation"
  unless lhs.isAppOfArity ``Witness.okVal 1 && lhs.appArg! == run do
    throwError "unroll_sched: expected `Witness.okVal (Sched.run …) = _`"
  let runs ← loopRunners (args[2]!.getUsedConstants ++ args[5]!.getUsedConstants)
  let (fD, hD) ← expand runs k.getNat args[2]!
  let (fP, hP) ← expand runs k.getNat args[5]!
  let approx := mkConst ``Sel.approx
  let le (h : Expr) := mkApp3 h approx (mkConst ``Sel.exact) (mkConst ``approx_le)
  let cut := mkAppN run.getAppFn (args.set! 2 (mkApp fD approx) |>.set! 5 (mkApp fP approx))
  let sub ← mkFreshExprSyntheticOpaqueMVar (ty.replace fun e => if e == run then some cut else none)
  let pf ← mkAppM ``Sched.okVal_le #[le hD, le hP, sub]
  unless ← isDefEq (← inferType pf) ty do
    throwError "unroll_sched: the cut program does not unfold to the program"
  goal.assign pf
  replaceMainGoal [sub.mvarId!]
  try evalTactic (← `(tactic| decide +kernel)) catch _ =>
    throwError "unroll_sched: the kernel does not compute the run with loops cut after {k.getNat} \
      iterations to the goal's value (another result or error, out of fuel, or a loop that needs \
      more iterations)"

end Zig.Unroll
