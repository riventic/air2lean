import Air2Lean.SemRewrite

/-!
# Dropping instructions preserves a function's execution

Five Canon rewrites drop instructions from a body: the dead-code passes
(`dropDeadAllocPlaceholders`, `dropDeadRuntimeLanePtrs`), `forwardReadOnlyCopies`, `itemReads`
and `dropTrueChecks`, each with the debug instructions that name a dropped one. This module
states once what dropping does to `Sem.execFunc`, for every function, every set `D` of
instruction IDs, every argument list, the full memory and every call oracle:

* `execFunc_dropDebug`: dropping debug instructions (`line`, `dbg`) is an **equality**;
* `execFunc_drop_le`: dropping, besides those, instructions that have no behaviour in `Sem`
  (`stuckIn`: Sema's address-0 placeholder of a comptime-resolved local and the pointer
  projections of a dropped instruction) is a **refinement**: wherever the function before the
  drop has a behaviour, the function after it has the same one (`⊑`, `Zig.Result`'s order,
  whose bottom is `Sem.stuck`).

The second is not an equality, and cannot be one: `Sem` gives the placeholder no meaning, so
the function before the drop is stuck where it reaches one, and the function after is not
(`tests/roadmap/air-semantics/CanonDrop.lean`).

The per-function obligation is the decidable `okBody`: every dropped instruction is debug
information (or, for the refinement, `stuckIn`), and every kept `alloc` is a register local
after the drop exactly when it was one before (`Sem.regAlloc` reads the whole body, so a dropped
use can change it). `CanonCertificate.dropBound` evaluates it.

These are compiler-correctness statements about `Sem`, not program judgments or premises.
-/

namespace Air2Lean.Drop

open Zig Air2Lean.Sem Lean.Order

/-! ## The drop -/

/-- Debug information: `Sem` gives it no effect and no value. -/
def isDebug : Op → Bool
  | .line _ | .dbg .. => true
  | _ => false

mutual

/-- `l` without the instructions whose ID is in `D`, nested bodies included. -/
def dropBody (D : InstId → Bool) : List Inst → List Inst
  | [] => []
  | i :: rest => if D i.id then dropBody D rest else dropInst D i :: dropBody D rest
termination_by l => (sizeOf l, 0)

def dropInst (D : InstId → Bool) (i : Inst) : Inst :=
  let op := match _h : i.op with
    | .block b => .block (dropBody D b.toList).toArray
    | .loop b => .loop (dropBody D b.toList).toArray
    | .condBr v t e => .condBr v (dropBody D t.toList).toArray (dropBody D e.toList).toArray
    | .switchBr v cs e => .switchBr v (dropCases D cs.toList).toArray (dropBody D e.toList).toArray
    | .loopSwitchBr v cs e =>
      .loopSwitchBr v (dropCases D cs.toList).toArray (dropBody D e.toList).toArray
    | .«try» v b => .«try» v (dropBody D b.toList).toArray
    | .tryPtr v b => .tryPtr v (dropBody D b.toList).toArray
    | op => op
  { id := i.id, ty := i.ty, op }
termination_by (sizeOf i, 1)
decreasing_by
  all_goals
    obtain ⟨id, ty, op⟩ := i
    simp only at _h
    subst _h
    simp_wf
    try simp only [sizeOf_toList]
    omega

def dropCases (D : InstId → Bool) : List SwitchCase → List SwitchCase
  | [] => []
  | sc :: more =>
    { items := sc.items, ranges := sc.ranges, body := (dropBody D sc.body.toList).toArray } ::
      dropCases D more
termination_by cs => (sizeOf cs, 0)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [sizeOf_toList]
  all_goals (try have := sizeOf_case_body sc); omega

end

/-- `f` without the instructions whose ID is in `D` (`Func.withBody`: everything but the body
reads the same, `SemRewrite`). -/
abbrev dropFunc (D : InstId → Bool) (f : Func) : Func :=
  f.withBody (dropBody D f.body.toList).toArray

/-! ## The per-function obligation -/

/-- An instruction that is stuck in every environment that binds no ID of `D`:

* a `bitcast` of an integer constant to a type that is no integer (Sema's placeholder for a
  comptime-resolved local, `Raw.dropDeadAllocPlaceholders`: an integer is no pointer operand);
* a pointer `bitcast`, field pointer or item pointer of an instruction in `D` (its operand has no
  value);
* a pointer to a slice's field, which `Sem` does not interpret (`Sem.outside?`). -/
def stuckIn (D : InstId → Bool) (f : Func) (ty : TyId) : Op → Bool
  | .bitcast _ (.int ..) => (intTy? f ty).isNone
  | .bitcast _ (.inst p) | .fieldPtr (.inst p) _ | .elemPtr (.inst p) _ => D p
  | .sliceFieldPtr .. => true
  | _ => false

section Ok
variable (strict : Bool) (D : InstId → Bool) (f f' : Func)

mutual

/-- The obligation of a drop from `f` to `f'`, on a body of `f`: every dropped instruction is
debug information or, unless `strict`, has no behaviour (`stuckIn`); every kept `alloc` is a
register local of `f'` exactly when it is one of `f`. -/
def okBody : List Inst → Bool
  | [] => true
  | i :: rest => okInst i && okBody rest
termination_by l => (sizeOf l, 0)

def okInst (i : Inst) : Bool :=
  if D i.id then isDebug i.op || (!strict && stuckIn D f i.ty i.op)
  else match _h : i.op with
    | .alloc => regAlloc f' i.id == regAlloc f i.id
    | .block b | .loop b | .«try» _ b => okBody b.toList
    | .condBr _ t e => okBody t.toList && okBody e.toList
    | .switchBr _ cs e => okCases cs.toList && okBody e.toList
    | _ => true
termination_by (sizeOf i, 1)
decreasing_by
  all_goals
    obtain ⟨id, ty, op⟩ := i
    simp only at _h
    subst _h
    simp_wf
    try simp only [sizeOf_toList]
    omega

def okCases : List SwitchCase → Bool
  | [] => true
  | sc :: more => okBody sc.body.toList && okCases more
termination_by l => (sizeOf l, 0)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [sizeOf_toList]
  all_goals (try have := sizeOf_case_body sc); omega

end

end Ok

/-- The obligation of dropping `D` from the whole function `f`. -/
def dropOk (strict : Bool) (D : InstId → Bool) (f : Func) : Bool :=
  okBody strict D f (dropFunc D f) f.body.toList

/-! ## Equality or refinement -/

/-- `x = y` when `strict`, else `x ⊑ y`: `y` has every behaviour of `x`. -/
def Rl (strict : Bool) {α : Type} [PartialOrder α] (x y : α) : Prop :=
  if strict then x = y else x ⊑ y

namespace Rl
variable {strict : Bool}

theorem refl {α : Type} [PartialOrder α] (x : α) : Rl strict x x := by
  cases strict
  · exact PartialOrder.rel_refl
  · exact rfl

theorem bind {m : Type → Type} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α β : Type}
    {x y : m α} {k₁ k₂ : α → m β} (hx : Rl strict x y) (hk : ∀ a, Rl strict (k₁ a) (k₂ a)) :
    Rl strict (x >>= k₁) (y >>= k₂) := by
  cases strict
  · exact PartialOrder.rel_trans (MonoBind.bind_mono_left hx) (MonoBind.bind_mono_right hk)
  · have hx : x = y := hx
    have hk : k₁ = k₂ := funext hk
    rw [hx, hk]
    exact rfl

theorem bind_right {m : Type → Type} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α β : Type}
    {x : m α} {k₁ k₂ : α → m β} (hk : ∀ a, Rl strict (k₁ a) (k₂ a)) :
    Rl strict (x >>= k₁) (x >>= k₂) :=
  bind (refl x) hk

theorem ite {α : Type} [PartialOrder α] {c : Prop} [Decidable c] {x₁ x₂ y₁ y₂ : α}
    (h₁ : Rl strict x₁ y₁) (h₂ : Rl strict x₂ y₂) :
    Rl strict (if c then x₁ else x₂) (if c then y₁ else y₂) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h₁
  · simp only [hc, ↓reduceIte]; exact h₂

theorem loop {ε : Type} {x y : SM ε} (again : ε → Bool) (h : Rl strict x y) :
    Rl strict (Zig.loop x again) (Zig.loop y again) := by
  cases strict
  · exact Zig.monotone_loopMM (fun x => x) again (fun _ _ h => h) x y h
  · have h : x = y := h
    rw [h]
    exact rfl

/-- A frame's run of related bodies. -/
theorem run {α : Type} {x y : SM α} (h : Rl strict x y) (fr : Frame) :
    Rl strict (x.run fr) (y.run fr) := by
  cases strict
  · exact h fr
  · have h : x = y := h
    rw [h]
    exact rfl

end Rl

/-- A stuck step is below every computation. -/
theorem stuck_le {α β : Type} (k : α → SM β) (y : SM β) :
    liftMem (StateT.lift (stuck : Result α)) >>= k ⊑ y :=
  fun _ _ => FlatOrder.rel.bot

/-! ## Stuck instructions -/

/-- The environment binds no ID of `D`. -/
def EnvD (D : InstId → Bool) (env : Env) : Prop := ∀ d, D d = true → env d = none

theorem EnvD.set {D : InstId → Bool} {env : Env} (h : EnvD D env) {id : InstId} (hid : D id = false)
    (t : TyId) (v : Value) : EnvD D (env.set id t v) := by
  intro d hd
  have hne : d ≠ id := fun e => by rw [e, hid] at hd; cases hd
  simp only [Env.set, hne, ↓reduceIte]
  exact h d hd

theorem constVal_run (f : Func) (v : Val) :
    (constVal f v).run = none ∨ ∃ w, (constVal f v).run = some (.ok w) := by
  cases v <;> simp only [constVal] <;> first
    | exact .inl rfl
    | exact .inr ⟨_, rfl⟩
    | (split <;> first | exact .inl rfl | exact .inr ⟨_, rfl⟩)

/-- An operand never panics: it has a value or is stuck. -/
theorem operand_run (f : Func) (env : Env) (v : Val) :
    (operand f env v).run = none ∨ ∃ w, (operand f env v).run = some (.ok w) := by
  have hmap : ∀ (g : Value → Value) (u : Val),
      (do pure (g (← constVal f u)) : Result Value).run = none ∨
        ∃ w, (do pure (g (← constVal f u)) : Result Value).run = some (.ok w) := by
    intro g u
    rcases constVal_run f u with h | ⟨w, h⟩
    · left; rw [ExceptT.run_bind, h]; rfl
    · right; exact ⟨g w, by rw [ExceptT.run_bind, h]; rfl⟩
  cases v <;> simp only [operand] <;> first
    | exact constVal_run f _
    | exact .inl rfl
    | (split <;> first | exact .inl rfl | exact .inr ⟨_, rfl⟩ | exact hmap _ _)

theorem indexOperand_run (f : Func) (env : Env) (v : Val) :
    (indexOperand f env v).run = none ∨ ∃ k, (indexOperand f env v).run = some (.ok k) := by
  unfold indexOperand
  rcases operand_run f env v with h | ⟨w, h⟩
  · left; rw [ExceptT.run_bind, h]; rfl
  · rw [ExceptT.run_bind, h]
    show (w.asInt 64).run = none ∨ ∃ k, (w.asInt 64).run = some (.ok k)
    cases w <;> simp only [Value.asInt] <;> first
      | exact .inl rfl
      | (split <;> first | exact .inl rfl | exact .inr ⟨_, rfl⟩)

/-- A step that never panics, followed by a stuck one, is stuck. -/
theorem bind_lift_stuck {α β : Type} {x : Result α}
    (hx : x.run = none ∨ ∃ a, x.run = some (.ok a)) (k : α → MemM β)
    (hk : ∀ a, k a = StateT.lift stuck) : (StateT.lift x : MemM α) >>= k = StateT.lift stuck := by
  have hk' : k = fun _ => StateT.lift stuck := funext hk
  subst hk'
  apply StateT.ext; intro m
  simp only [StateT.run_bind, StateT.run_lift]
  apply ExceptT.ext
  rcases hx with h | ⟨a, h⟩
  · simp only [ExceptT.run_bind, h]; rfl
  · simp only [ExceptT.run_bind, h]; rfl

theorem ptrOperand_int (f : Func) (env : Env) (t : TyId) (n : Int) :
    ptrOperand f env (.int t n) = stuck := by
  simp only [ptrOperand, operandTy, Val.constTy?, operand, constVal]
  cases tyOf f t <;> first | rfl | (cases f.plainPtr t <;> cases ptrAlignOf f t <;> rfl)

theorem ptrOperand_unbound (f : Func) {env : Env} {p : InstId} (h : env p = none) :
    ptrOperand f env (.inst p) = stuck := by
  simp only [ptrOperand, operandTy, h, Option.map_none]

theorem operand_unbound (f : Func) {env : Env} {p : InstId} (h : env p = none) :
    operand f env (.inst p) = stuck := by
  simp only [operand, h]

/-- A `stuckIn` instruction has no behaviour where no ID of `D` is bound. -/
theorem evalMem_stuck {D : InstId → Bool} {f : Func} {env : Env} (henv : EnvD D env) (id : InstId)
    {ty : TyId} {op : Op} (h : stuckIn D f ty op = true) :
    evalMem f env ⟨id, ty, op⟩ = StateT.lift stuck := by
  cases op
  case sliceFieldPtr len p => rfl
  case bitcast safe a =>
    cases a
    case int t n =>
      simp only [stuckIn, Option.isNone_iff_eq_none] at h
      simp only [evalMem, ptrOperand_int, evalPure, h]
      split <;> rfl
    case inst p =>
      simp only [stuckIn] at h
      simp only [evalMem, ptrOperand_unbound f (henv p h), evalPure, operand_unbound f (henv p h)]
      split
      · rfl
      · split <;> rfl
    all_goals simp [stuckIn] at h
  case fieldPtr base idx =>
    cases base
    case inst p =>
      simp only [stuckIn] at h
      simp only [evalMem, ptrOperand_unbound f (henv p h)]
      rfl
    all_goals simp [stuckIn] at h
  case elemPtr base idx =>
    cases base
    case inst p =>
      simp only [stuckIn] at h
      simp only [evalMem]
      refine bind_lift_stuck (indexOperand_run f env idx) _ fun k => ?_
      simp only [itemBase, operandTy, henv p h, Option.map_none]
      rfl
    all_goals simp [stuckIn] at h
  all_goals simp [stuckIn] at h

/-! ## The simulation -/

/-- `c` running the body `b`. -/
abbrev dctx (c : Ctx) (b : Array Inst) : Ctx := { c with func := c.func.withBody b }

theorem okBody_cons {strict : Bool} {D : InstId → Bool} {f f' : Func} {i : Inst} {rest : List Inst}
    (h : okBody strict D f f' (i :: rest) = true) :
    okInst strict D f f' i = true ∧ okBody strict D f f' rest = true := by
  simpa only [okBody, Bool.and_eq_true] using h

/-- What the obligation says of a dropped instruction. -/
theorem okInst_dropped {strict : Bool} {D : InstId → Bool} {f f' : Func} {id : InstId} {ty : TyId}
    {op : Op} (hD : D id = true) (h : okInst strict D f f' ⟨id, ty, op⟩ = true) :
    isDebug op = true ∨ (strict = false ∧ stuckIn D f ty op = true) := by
  unfold okInst at h
  simp only [hD, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h

theorem dropBody_drop {D : InstId → Bool} {i : Inst} (rest : List Inst) (hD : D i.id = true) :
    dropBody D (i :: rest) = dropBody D rest := by
  simp only [dropBody, hD, ↓reduceIte]

theorem dropBody_keep {D : InstId → Bool} {i : Inst} (rest : List Inst) (hD : D i.id = false) :
    dropBody D (i :: rest) = dropInst D i :: dropBody D rest := by
  simp only [dropBody, hD, Bool.false_eq_true, ↓reduceIte]

theorem Rl.iteration {strict : Bool} (c : Ctx) (b : Array Inst) {α : Type} {x y : SM α}
    (h : Rl strict x y) : Rl strict (iteration c x) (iteration (dctx c b) y) := by
  show Rl strict (Sem.iteration c x) (Sem.iteration c y)
  by_cases ht : c.prog.ticked c.func.name = true
  · simp only [Sem.iteration, ht, ↓reduceIte]
    exact Rl.bind_right fun _ => h
  · simp only [Sem.iteration, ht, Bool.false_eq_true, ↓reduceIte]
    exact h

section Sim
variable {strict : Bool} {D : InstId → Bool} (c : Ctx) (b : Array Inst)

/-- The body before the drop and the body after it, in the same environment and frame: equal
runs when only debug information is dropped (`strict`), else the run after has every behaviour
of the run before. -/
theorem execBody_drop : ∀ l env, EnvD D env →
    okBody strict D c.func (c.func.withBody b) l = true →
    Rl strict (execBody c l env) (execBody (dctx c b) (dropBody D l) env) := by
  apply execBody.induct c
    (motive2 := fun i rest env => EnvD D env →
      okBody strict D c.func (c.func.withBody b) (i :: rest) = true →
      Rl strict (execInst c i rest env) (execBody (dctx c b) (dropBody D (i :: rest)) env))
    (motive3 := fun s _ x cs el env => EnvD D env →
      okCases strict D c.func (c.func.withBody b) cs = true →
      okBody strict D c.func (c.func.withBody b) el.toList = true →
      Rl strict (execSwitch c s x cs el env)
        (execSwitch (dctx c b) s x (dropCases D cs) (dropBody D el.toList).toArray env))
    (motive4 := fun id body env => EnvD D env →
      okBody strict D c.func (c.func.withBody b) body.toList = true →
      Rl strict (execLoop c id body env)
        (execLoop (dctx c b) id (dropBody D body.toList).toArray env))
  case case1 => intro env _ _; simp only [dropBody, execBody]; exact Rl.refl _
  case case2 => intro i rest env ih henv hok; simp only [execBody]; exact ih henv hok
  case case27 =>
    intro s w x el env ih henv _ hel
    simp only [dropCases, execSwitch]
    exact ih henv hel
  case case28 =>
    intro s w x sc more el env ihb ihm henv hcs hel
    simp only [okCases, Bool.and_eq_true] at hcs
    simp only [dropCases, execSwitch, dctx, caseHit_withBody]
    exact Rl.bind_right fun hit => Rl.ite (ihb henv hcs.1) (ihm henv hcs.2 hel)
  case case29 =>
    intro id body env ih henv hok
    simp only [execLoop]
    exact Rl.loop _ (Rl.iteration c b (ih henv hok))
  case case3 =>
    intro i rest env index hop v hv ih henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst, dctx, hv]
      exact ih (henv.set hD _ _) hrest
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case4 =>
    intro i rest env index hop hv henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst, dctx, hv]
      exact Rl.refl _
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case5 =>
    intro i rest env body hop ihb ihr henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · unfold okInst at hi
      simp only [hD, Bool.false_eq_true, ↓reduceIte] at hi
      rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst]
      refine Rl.bind (ihb henv hi) fun e => ?_
      cases e with
      | br t v =>
        by_cases ht : t = id
        · subst ht
          simp only [↓reduceIte]
          exact ihr _ _ rfl (henv.set hD _ _) hrest
        · simp only [ht, ↓reduceIte]
          exact Rl.refl _
      | rep t => exact Rl.refl _
      | ret v => exact Rl.refl _
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case6 =>
    intro i rest env body hop ih henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · unfold okInst at hi
      simp only [hD, Bool.false_eq_true, ↓reduceIte] at hi
      rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst]
      exact ih henv hi
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case7 =>
    intro i rest env t v hop henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst, dctx, operand_withBody]
      exact Rl.refl _
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case8 =>
    intro i rest env t hop henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst]
      exact Rl.refl _
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case9 =>
    intro i rest env v hop henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst, dctx, operand_withBody]
      exact Rl.refl _
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case10 =>
    intro i rest env hop henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst]
      exact Rl.refl _
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case11 =>
    intro i rest env hop henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst]
      exact Rl.refl _
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case12 =>
    intro i rest env cv th el hop iht ihe henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · unfold okInst at hi
      simp only [hD, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hi
      rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst, dctx, operand_withBody]
      exact Rl.bind_right fun w => Rl.bind_right fun bv => Rl.ite (iht henv hi.1) (ihe henv hi.2)
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case13 =>
    intro i rest env v cs el hop ih henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · unfold okInst at hi
      simp only [hD, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hi
      rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst, dctx, operand_withBody]
      refine Rl.bind_right fun w => ?_
      cases w
      case int s n x => exact ih s n x henv hi.1 hi.2
      all_goals exact Rl.refl _
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case14 =>
    intro i rest env hop hr ih henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only at hr
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · unfold okInst at hi
      simp only [hD, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hi
      rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst, dctx, hi, hr, ↓reduceIte]
      exact Rl.bind_right fun _ => ih (henv.set hD _ _) hrest
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case15 =>
    intro i rest env hop hr size snd align ha hl ih henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only at hr ha hl
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · unfold okInst at hi
      simp only [hD, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hi
      rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst, dctx, hi, hr, Bool.false_eq_true, ↓reduceIte,
        pointee_withBody, layoutOf_withBody, ptrAlignOf_withBody, ha, hl]
      exact Rl.bind_right fun p => Rl.bind_right fun _ => ih p (henv.set hD _ _) hrest
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case16 =>
    intro i rest env hop hr hne henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only at hr hne
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · unfold okInst at hi
      simp only [hD, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hi
      rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst, dctx, hi, hr, Bool.false_eq_true, ↓reduceIte,
        pointee_withBody, layoutOf_withBody, ptrAlignOf_withBody]
      rcases h1 : (pointee? c.func ty).bind (layoutOf c.func) with _ | ⟨size, snd⟩ <;>
        rcases h2 : ptrAlignOf c.func ty with _ | align <;> (try simp only [h1, h2]) <;>
        first | exact Rl.refl _ | exact absurd h2 fun h => hne _ _ _ h1 h
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case17 =>
    intro i rest env p hop ih henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst, dctx, operand_withBody, evalMem_withBody, tyOf_withBody]
      exact Rl.bind_right fun v => ih v (henv.set hD _ _) hrest
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case18 =>
    intro i rest env p v hop ih henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst, dctx, operand_withBody, evalMem_withBody, cellVal_withBody]
      exact Rl.bind_right fun _ => ih (henv.set hD _ _) hrest
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case19 =>
    intro i rest env name nr sp args hop e he henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst, he]
      exact Rl.refl _
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case20 =>
    intro i rest env name nr sp args hop hn ih henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst, dctx, hn]
      exact Rl.bind_right fun vs => Rl.bind_right fun v => ih v (henv.set hD _ _) hrest
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case21 =>
    intro i rest env n hop ih henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst]
      exact ih henv hrest
    · rw [dropBody_drop rest hD]
      simp only [execInst]
      exact ih henv hrest
  case case22 =>
    intro i rest env n v hop ih henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst]
      exact ih henv hrest
    · rw [dropBody_drop rest hD]
      simp only [execInst]
      exact ih henv hrest
  case case23 =>
    intro i rest env v eb hop ihr ihe henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · unfold okInst at hi
      simp only [hD, Bool.false_eq_true, ↓reduceIte] at hi
      rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst, dctx, errUnionOperand_withBody]
      refine Rl.bind_right fun w => ?_
      cases w
      case errOk x => exact ihr x (henv.set hD _ _) hrest
      case errErr n => exact ihe henv hi
      all_goals exact Rl.refl _
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case24 =>
    intro i rest env k idx hop items hv ih henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst, dctx, hv, sliceOperand_withBody,
        indexOperand_withBody, itemLayout_withBody]
      refine Rl.bind_right fun sa => Rl.bind_right fun j => ?_
      cases hI : itemLayout c.func ty sa.2 with
      | none => exact Rl.refl _
      | some lay => exact Rl.bind_right fun v => ih v (henv.set hD _ _) hrest
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case25 =>
    intro i rest env k idx hop hv ih henv hok
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · rw [dropBody_keep rest hD]
      simp only [dropInst, execBody, execInst, dctx, hv, evalMem_withBody]
      exact Rl.bind_right fun v => ih v (henv.set hD _ _) hrest
    · rcases okInst_dropped hD hi with h | ⟨_, h⟩ <;> simp [isDebug, stuckIn] at h
  case case26 =>
    intro i rest env h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 ih henv hok
    obtain ⟨id, ty, op⟩ := i
    obtain ⟨hi, hrest⟩ := okBody_cons hok
    cases hD : D id
    · have ih' : ∀ v, Rl strict (execBody c rest (env.set id ty v))
          (execBody (dctx c b) (dropBody D rest) (env.set id ty v)) :=
        fun v => ih v (henv.set hD _ _) hrest
      rw [dropBody_keep rest hD]
      clear ih hok hi hrest henv
      cases op
      case call cv args =>
        cases cv <;> first
          | exact (h14 _ _ _ _ rfl).elim
          | (simp only [dropInst, execBody, execInst, dctx, evalMem_withBody]
             exact Rl.bind_right ih')
      case sliceElemVal sv idx =>
        cases sv <;> first
          | exact (h18 _ _ rfl).elim
          | (simp only [dropInst, execBody, execInst, dctx, evalMem_withBody]
             exact Rl.bind_right ih')
      case loopSwitchBr v cs el =>
        simp only [dropInst, execBody, execInst, dctx, evalMem_withBody]
        exact Rl.bind (Rl.refl _) ih'
      case tryPtr v eb =>
        simp only [dropInst, execBody, execInst, dctx, evalMem_withBody]
        exact Rl.bind (Rl.refl _) ih'
      all_goals first
        | exact (h1 _ rfl).elim | exact (h2 _ rfl).elim | exact (h3 _ rfl).elim
        | exact (h4 _ _ rfl).elim | exact (h5 _ rfl).elim | exact (h6 _ rfl).elim | exact (h7 rfl).elim
        | exact (h8 rfl).elim | exact (h9 _ _ _ rfl).elim | exact (h10 _ _ _ rfl).elim
        | exact (h11 rfl).elim | exact (h12 _ rfl).elim | exact (h13 _ _ rfl).elim
        | exact (h15 _ rfl).elim | exact (h16 _ _ rfl).elim | exact (h17 _ _ rfl).elim
        | (simp only [dropInst, execBody, execInst, dctx, evalMem_withBody]
           exact Rl.bind_right ih')
    · rcases okInst_dropped hD hi with h | ⟨hs, h⟩
      · cases op <;> first
          | exact (h15 _ rfl).elim | exact (h16 _ _ rfl).elim
          | (simp [isDebug] at h)
      · subst hs
        have hst := evalMem_stuck henv id h
        cases op <;> first
          | (simp [stuckIn] at h; done)
          | (simp only [execInst, hst]; exact stuck_le _ _)

end Sim

/-! ## Functions -/

/-- `execFunc` before and after a drop that meets its obligation. -/
theorem execFunc_drop {strict : Bool} {D : InstId → Bool} (prog : Prog) (o : Oracle) (f : Func)
    (args : List Value) (hok : dropOk strict D f = true) :
    Rl strict (execFunc prog o f args) (execFunc prog o (dropFunc D f) args) := by
  have hs := (execBody_drop (strict := strict) (D := D) ⟨prog, f, args, o, fun _ => none⟩
    (dropBody D f.body.toList).toArray f.body.toList (fun _ => none) (fun _ _ => rfl) hok).run {}
  simp only [execFunc, argsOk_withBody, show (dropFunc D f).params = f.params from rfl,
    show (dropFunc D f).name = f.name from rfl]
  by_cases h : argsOk f f.params.toList args = true
  · simp only [h, ↓reduceIte]
    have hk : Rl strict
        ((execBody ⟨prog, f, args, o, fun _ => none⟩ f.body.toList (fun _ => none)).run {} >>=
          fun (p : Exit × Frame) => (do
            p.2.blocks.forM Zig.free
            match p.1 with
            | .ret v => pure v
            | _ => StateT.lift stuck : MemM Value))
        ((execBody (dctx ⟨prog, f, args, o, fun _ => none⟩ (dropBody D f.body.toList).toArray)
            (dropBody D f.body.toList) (fun _ => none)).run {} >>=
          fun (p : Exit × Frame) => (do
            p.2.blocks.forM Zig.free
            match p.1 with
            | .ret v => pure v
            | _ => StateT.lift stuck : MemM Value)) :=
      Rl.bind hs fun _ => Rl.refl _
    by_cases ht : prog.entryTicked f.name = true
    · simp only [ht, ↓reduceIte]
      exact Rl.bind_right fun _ => hk
    · simp only [ht, Bool.false_eq_true, ↓reduceIte]
      exact hk
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact Rl.refl _

/-- **Dropping debug information preserves a function's execution** (V02, the debug
instructions that Canon's dropping rewrites remove): for every function, every set of
instruction IDs that names only `line` and `dbg` instructions and whose drop keeps each `alloc`'s
register classification (`dropOk true`), every argument list, the full memory and every oracle. -/
theorem execFunc_dropDebug {D : InstId → Bool} (prog : Prog) (o : Oracle) (f : Func)
    (args : List Value) (hok : dropOk true D f = true) :
    execFunc prog o (dropFunc D f) args = execFunc prog o f args :=
  (execFunc_drop prog o f args hok : execFunc prog o f args = _).symm

/-- **Dropping instructions without behaviour refines a function's execution** (V02, Canon
`dropDeadAllocPlaceholders`): for every function, every set of instruction IDs that names only
debug information and `stuckIn` instructions (`dropOk false`), every argument list, the full
memory and every oracle, the function after the drop has every behaviour of the function
before. It is no equality: the function before is stuck where it runs a dropped placeholder. -/
theorem execFunc_drop_le {D : InstId → Bool} (prog : Prog) (o : Oracle) (f : Func)
    (args : List Value) (hok : dropOk false D f = true) :
    execFunc prog o f args ⊑ execFunc prog o (dropFunc D f) args :=
  execFunc_drop prog o f args hok

/-- Where the function before the drop has a behaviour on the memory `m`, the function after
has the same. -/
theorem execFunc_drop_eq {D : InstId → Bool} (prog : Prog) (o : Oracle) (f : Func)
    (args : List Value) (hok : dropOk false D f = true) (m : Zig.Mem)
    (h : (execFunc prog o f args).run m ≠ stuck) :
    (execFunc prog o (dropFunc D f) args).run m = (execFunc prog o f args).run m :=
  (Result.eq_of_le (execFunc_drop_le prog o f args hok m) h).symm

end Air2Lean.Drop
