import Air2Lean.Sem
import ZigLean.Mem.Lemmas

/-!
# Pure-function slices: the view of a slice parameter

The translator passes a `[]const T` parameter of a function without memory as an `Array`: the
caller reads the items (`Zig.readSlice`) and the callee indexes the array (`Zig.index`). In AIR
the callee reads each item from memory itself (`slice_elem_val`). This file proves, once for every
function, that the two agree at the call boundary (`docs/air-semantics.md` §Pure-function slices):

* `execFuncV` runs a function with a *view* (`Ctx.view`): `slice_elem_val` of a viewed parameter
  takes the item from an array instead of memory, and the run does not touch memory. A certificate
  proves by normalization that this run is the generated definition.
* `execFunc_view`: for a function that reads memory only through viewed slices (`roFunc`), from a
  memory in which every viewed slice holds the view's items (`ArgsView`), `execFunc` gives the
  view's values and errors, and its memory is the starting memory up to read entries of the running
  thread in the footprint (`UpToReads`): the same blocks, threads and every other field.
* `holds_of_readSlice`: the items that `Zig.readSlice` reads are such a view. Its read covers every
  item, under the running thread, before the call, so a concurrent writer is still a race; the
  callee's own reads would only be a subset of it.

Nothing here is trusted: `Ctx.view` is `none` in `execFunc`, the meaning of AIR (SEM-06).
-/

namespace Air2Lean.Sem

open Zig

/-! ## Results related by a relation -/

/-- Two results agree: both have no behaviour, both throw the same error, or both return values
related by `R`. -/
def RelR {α β : Type} (R : α → β → Prop) (x : Result α) (y : Result β) : Prop :=
  match x.run, y.run with
  | none, none => True
  | some (.error e), some (.error e') => e = e'
  | some (.ok a), some (.ok b) => R a b
  | _, _ => False

theorem Result.run_bind' {α β : Type} (x : Result α) (f : α → Result β) :
    (x >>= f).run = match x.run with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok a) => (f a).run := by
  rw [ExceptT.run_bind]
  rcases x.run with _ | (e | a) <;> rfl

theorem relR_pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    RelR R (pure a) (pure b) := h

theorem relR_throw {α β : Type} {R : α → β → Prop} (e : Zig.Error) :
    RelR R (throw e : Result α) (throw e : Result β) := rfl

theorem relR_stuck {α β : Type} {R : α → β → Prop} : RelR R (stuck : Result α) (stuck : Result β) :=
  trivial

theorem relR_bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {x : Result α}
    {y : Result β} {f : α → Result γ} {g : β → Result δ} (h : RelR R x y)
    (hf : ∀ a b, R a b → RelR S (f a) (g b)) : RelR S (x >>= f) (y >>= g) := by
  unfold RelR at h ⊢
  rw [Result.run_bind', Result.run_bind']
  rcases hx : x.run with _ | (e | a) <;> rcases hy : y.run with _ | (e' | b) <;>
    simp only [hx, hy] at h ⊢
  · exact h
  · exact hf a b h

theorem relR_mono {α β : Type} {R S : α → β → Prop} {x : Result α} {y : Result β}
    (h : RelR R x y) (hRS : ∀ a b, R a b → S a b) : RelR S x y := by
  unfold RelR at h ⊢
  rcases hx : x.run with _ | (e | a) <;> rcases hy : y.run with _ | (e' | b) <;>
    simp only [hx, hy] at h ⊢
  · exact h
  · exact hRS a b h

/-- The first result has no behaviour, or the two agree. -/
def RelLe {α β : Type} (R : α → β → Prop) (x : Result α) (y : Result β) : Prop :=
  x.run = none ∨ RelR R x y

/-! ## Memories up to reads -/

/-- `m` is `m₀` after reads by its running thread: every field is `m₀`'s except the footprint,
which has more read entries of that thread, and that thread's own clock, which is larger. -/
structure UpToReads (m₀ m : Mem) : Prop where
  rest : { m with footprint := m₀.footprint, clocks := m₀.clocks } = m₀
  reads : ∃ rs : Array FootprintEntry, m.footprint = m₀.footprint ++ rs ∧
    ∀ e ∈ rs, e.tid = m₀.current ∧ e.kind = .read
  clocks : m.clocks = m₀.clocks.set! m₀.current (m.clocks[m₀.current]!)
  own : VClock.le (m₀.clocks[m₀.current]!) (m.clocks[m₀.current]!) = true

theorem VClock.le_iff (a b : VClock) : VClock.le a b = true ↔ ∀ i, a.get i ≤ b.get i := by
  unfold VClock.le
  rw [Array.all_eq_true]
  simp only [Array.size_range, Array.getElem_range, Nat.ble_eq]
  constructor
  · intro h i
    by_cases hi : i < Nat.max a.size b.size
    · exact h i hi
    · have h1 : a.size ≤ Nat.max a.size b.size := Nat.le_max_left _ _
      have h2 := Nat.not_lt.mp hi
      have : a.size ≤ i := Nat.le_trans h1 h2
      have ha : a.get i = 0 := by
        simp only [VClock.get, Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_eq_none (by omega)]; rfl
      rw [ha]; exact Nat.zero_le _
  · intro h i _; exact h i

theorem VClock.le_refl (a : VClock) : VClock.le a a = true :=
  (VClock.le_iff a a).2 fun _ => Nat.le_refl _

theorem VClock.le_trans {a b c : VClock} (h₁ : VClock.le a b = true) (h₂ : VClock.le b c = true) :
    VClock.le a c = true :=
  (VClock.le_iff a c).2 fun i => Nat.le_trans ((VClock.le_iff a b).1 h₁ i) ((VClock.le_iff b c).1 h₂ i)

theorem Array.set!_getElem!_self {α : Type} [Inhabited α] (xs : Array α) (i : Nat) :
    xs.set! i xs[i]! = xs := by
  rw [Array.set!_eq_setIfInBounds]
  unfold Array.setIfInBounds
  split
  · rename_i h; rw [getElem!_pos xs i h]; exact Array.set_getElem_self h
  · rfl

theorem UpToReads.refl (m : Mem) : UpToReads m m where
  rest := rfl
  reads := ⟨#[], by simp, by simp⟩
  clocks := (Array.set!_getElem!_self _ _).symm
  own := VClock.le_refl _

/-! ## Simulation of a run by its view -/

/-- A frame of a run with a view: no stack blocks, and no pointer in its registers. -/
def Value.noPtr : Value → Bool
  | .ptr _ => false
  | _ => true

def FrOk (fr : Frame) : Prop := fr.blocks = [] ∧ ∀ k v, fr.cells k = some v → v.noPtr = true

/-- The run `x` from a memory up to reads of `m₀` agrees with the run `y` from `m₀`: the same
values (which satisfy `P`) and frames (`FrOk`), `x`'s memory up to reads of `m₀`, `y`'s `m₀`. -/
def Sim {α : Type} (m₀ : Mem) (P : α → Prop) (x y : SM α) : Prop :=
  ∀ fr m, FrOk fr → UpToReads m₀ m →
    RelR (fun (p q : (α × Frame) × Mem) => p.1 = q.1 ∧ P p.1.1 ∧ FrOk p.1.2 ∧ UpToReads m₀ p.2 ∧ q.2 = m₀)
      ((x.run fr).run m) ((y.run fr).run m₀)

theorem sim_pure {α : Type} {m₀ : Mem} {P : α → Prop} {a : α} (h : P a) :
    Sim m₀ P (pure a) (pure a) := by
  intro fr m hfr hm
  exact relR_pure ⟨rfl, h, hfr, hm, rfl⟩

theorem sim_bind {α β : Type} {m₀ : Mem} {P : α → Prop} {Q : β → Prop} {x y : SM α}
    {f g : α → SM β} (hx : Sim m₀ P x y) (hf : ∀ a, P a → Sim m₀ Q (f a) (g a)) :
    Sim m₀ Q (x >>= f) (y >>= g) := by
  intro fr m hfr hm
  simp only [StateT.run_bind]
  apply relR_bind (hx fr m hfr hm)
  rintro ⟨⟨a, fr'⟩, m'⟩ ⟨⟨b, fr''⟩, m''⟩ ⟨h1, hP, hfr', hm', rfl⟩
  simp only [Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact hf a hP fr' m' hfr' hm'

/-- A step that does not touch memory or the frame. -/
theorem sim_liftR {α : Type} {m₀ : Mem} {P : α → Prop} (x : Result α)
    (h : ∀ a, x.run = some (.ok a) → P a) : Sim m₀ P (liftR x) (liftR x) := by
  intro fr m hfr hm
  simp only [liftR, StateT.run_lift, StateT.run_bind, StateT.run_pure]
  unfold RelR
  rw [Result.run_bind', Result.run_bind']
  rcases hx : x.run with _ | (e | a)
  · simp only [Result.run_bind', hx]
  · simp only [Result.run_bind', hx]
  · simp only [Result.run_bind', hx]
    exact ⟨rfl, h a hx, hfr, hm, rfl⟩

theorem sim_get {m₀ : Mem} {P : Frame → Prop} (h : ∀ fr, FrOk fr → P fr) :
    Sim m₀ P get get := by
  intro fr m hfr hm
  exact relR_pure ⟨rfl, h fr hfr, hfr, hm, rfl⟩

theorem sim_modify {m₀ : Mem} (g : Frame → Frame) (h : ∀ fr, FrOk fr → FrOk (g fr)) :
    Sim m₀ (fun _ => True) (modify g) (modify g) := by
  intro fr m hfr hm
  exact relR_pure ⟨rfl, trivial, h fr hfr, hm, rfl⟩

theorem sim_mono {α : Type} {m₀ : Mem} {P Q : α → Prop} {x y : SM α} (h : Sim m₀ P x y)
    (hPQ : ∀ a, P a → Q a) : Sim m₀ Q x y := by
  intro fr m hfr hm
  exact relR_mono (h fr m hfr hm) fun _ _ ⟨h1, hP, h3⟩ => ⟨h1, hPQ _ hP, h3⟩

section SimLoop
open Lean.Order

theorem admissible_imp {α : Type} [CCPO α] (H : Prop) {P : α → Prop} (h : admissible P) :
    admissible (fun x => H → P x) :=
  fun c hc hall hH => h c hc fun x hx => hall x hx hH

theorem relLe_adm {α β : Type} (R : α → β → Prop) (y : Result β) :
    admissible (fun x : Result α => RelLe R x y) := by
  apply admissible_flatOrder
  exact Or.inl rfl

theorem relR_of_relLe {α β : Type} {R : α → β → Prop} {x : Result α} {y : Result β}
    (h₁ : RelLe R x y) (h₂ : RelLe (fun b a => R a b) y x) : RelR R x y := by
  unfold RelLe RelR at *
  rcases hx : x.run with _ | (e | a) <;> rcases hy : y.run with _ | (e' | b) <;>
    simp only [hx, hy, reduceCtorEq, false_or, or_false, true_or] at h₁ h₂ ⊢
  all_goals first | trivial | exact h₁ | exact h₂.symm | exact h₂

theorem relLe_bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {x : Result α}
    {y : Result β} {f : α → Result γ} {g : β → Result δ} (h : RelR R x y)
    (hf : ∀ a b, R a b → RelLe S (f a) (g b)) : RelLe S (x >>= f) (y >>= g) := by
  unfold RelLe RelR at *
  rw [Result.run_bind', Result.run_bind']
  rcases hx : x.run with _ | (e | a) <;> rcases hy : y.run with _ | (e' | b) <;>
    simp only [hx, hy] at h ⊢
  · exact Or.inr trivial
  · exact Or.inr h
  · exact hf a b h

/-- One loop simulates the other when each iteration does (`Zig.loop`, by fixpoint induction on
either side). -/
theorem sim_loop {ε : Type} {m₀ : Mem} {P : ε → Prop} {b₁ b₂ : SM ε} (again : ε → Bool)
    (h : Sim m₀ P b₁ b₂) : Sim m₀ P (Zig.loop b₁ again) (Zig.loop b₂ again) := by
  let Q := fun (p q : (ε × Frame) × Mem) => p.1 = q.1 ∧ P p.1.1 ∧ FrOk p.1.2 ∧ UpToReads m₀ p.2 ∧ q.2 = m₀
  have hA : ∀ fr m, FrOk fr → UpToReads m₀ m →
      RelLe Q (((Zig.loop b₁ again).run fr).run m) (((Zig.loop b₂ again).run fr).run m₀) := by
    apply Zig.loop.fixpoint_induct b₁ again (motive := fun l => ∀ fr m, FrOk fr → UpToReads m₀ m →
      RelLe Q ((l.run fr).run m) (((Zig.loop b₂ again).run fr).run m₀))
    · apply admissible_pi; intro fr; apply admissible_pi; intro m
      apply admissible_imp; apply admissible_imp
      exact admissible_apply (fun _ (v : MemM (ε × Frame)) => RelLe Q (v m) _) fr
        (admissible_apply (fun _ (r : Result ((ε × Frame) × Zig.Mem)) => RelLe Q r _) m
          (relLe_adm Q _))
    · intro l hl fr m hfr hm
      rw [Zig.loop.eq_1 b₂ again]
      show RelLe Q (((b₁ >>= fun e => if again e then l else pure e).run fr).run m) _
      simp only [StateT.run_bind]
      apply relLe_bind (h fr m hfr hm)
      rintro ⟨⟨e, fr'⟩, m'⟩ ⟨⟨e', fr''⟩, m''⟩ ⟨h1, hP, hfr', hm', rfl⟩
      simp only [Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      dsimp only
      split
      · exact hl fr' m' hfr' hm'
      · exact Or.inr ⟨rfl, hP, hfr', hm', rfl⟩
  have hB : ∀ fr m, FrOk fr → UpToReads m₀ m →
      RelLe (fun q p => Q p q) (((Zig.loop b₂ again).run fr).run m₀)
        (((Zig.loop b₁ again).run fr).run m) := by
    intro fr m hfr hm
    revert fr m
    apply Zig.loop.fixpoint_induct b₂ again (motive := fun l => ∀ fr m, FrOk fr → UpToReads m₀ m →
      RelLe (fun q p => Q p q) ((l.run fr).run m₀) (((Zig.loop b₁ again).run fr).run m))
    · apply admissible_pi; intro fr; apply admissible_pi; intro m
      apply admissible_imp; apply admissible_imp
      exact admissible_apply (fun _ (v : MemM (ε × Frame)) => RelLe _ (v m₀) _) fr
        (admissible_apply (fun _ (r : Result ((ε × Frame) × Zig.Mem)) => RelLe _ r _) m₀
          (relLe_adm _ _))
    · intro l hl fr m hfr hm
      rw [Zig.loop.eq_1 b₁ again]
      show RelLe _ (((b₂ >>= fun e => if again e then l else pure e).run fr).run m₀) _
      simp only [StateT.run_bind]
      have hsym : RelR (fun q p => Q p q) (((b₂.run fr).run m₀)) ((b₁.run fr).run m) := by
        have := h fr m hfr hm
        unfold RelR at this ⊢
        rcases hx : ((b₁.run fr).run m).run with _ | (e | a) <;>
          rcases hy : ((b₂.run fr).run m₀).run with _ | (e' | b) <;>
          simp only [hx, hy] at this ⊢
        · exact this.symm
        · exact this
      apply relLe_bind hsym
      rintro ⟨⟨e₂, fr₂⟩, m₂⟩ ⟨⟨e₁, fr₁⟩, m₁⟩ ⟨h1, hP, hfr₁, hm₁, h5⟩
      dsimp only at h1 h5 hP hfr₁ hm₁
      subst h5
      simp only [Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      dsimp only
      split
      · exact hl fr₁ m₁ hfr₁ hm₁
      · exact Or.inr ⟨rfl, hP, hfr₁, hm₁, rfl⟩
  intro fr m hfr hm
  exact relR_of_relLe (hA fr m hfr hm) (hB fr m hfr hm)

end SimLoop

/-! ## Results that satisfy a predicate -/

/-- Every value that `x` returns satisfies `P`. -/
def OkR {α : Type} (P : α → Prop) (x : Result α) : Prop := ∀ a, x.run = some (.ok a) → P a

theorem okR_pure {α : Type} {P : α → Prop} {a : α} (h : P a) : OkR P (pure a) := by
  intro b hb; cases hb; exact h

theorem okR_stuck {α : Type} {P : α → Prop} : OkR P (stuck : Result α) := by
  intro b hb; cases hb

theorem okR_throw {α : Type} {P : α → Prop} {e : Zig.Error} : OkR P (throw e : Result α) := by
  intro b hb; cases hb

theorem okR_bind {α β : Type} {P : β → Prop} {x : Result α} {f : α → Result β}
    (h : ∀ a, OkR P (f a)) : OkR P (x >>= f) := by
  intro b hb
  obtain ⟨a, _, hf⟩ := Result.bind_ok hb
  exact h a b hf

theorem okR_map {α β : Type} {P : β → Prop} {x : Result α} {f : α → β} (h : ∀ a, P (f a)) :
    OkR P (f <$> x) := by
  rw [← bind_pure_comp]; exact okR_bind fun a => okR_pure (h a)

/-! ## Read-only functions -/

/-- The parameter index and type of the top-level `arg` instruction `k`. -/
def argAt (f : Func) (k : InstId) : Option (Nat × TyId) :=
  (f.body.toList.find? (·.id == k)).bind fun i => match i.op with
    | .arg idx => some (idx, i.ty)
    | _ => none

/-- An instruction of a function that reads memory only through viewed slices (`V`, items of type
`VT k`): an instruction whose id is viewed is its `arg`; every `alloc` is a register; no item
pointer or slice pointer; `slice_elem_val` only of a viewed slice; only safety-panic calls. -/
def roInst (f : Func) (V : InstId → Option (Array Value)) (VT : InstId → TyId) (i : Inst) : Bool :=
  (match V i.id, i.op with
    | some _, .arg idx => argAt f i.id == some (idx, i.ty)
    | some _, _ => false
    | none, _ => true) &&
  match i.op with
  | .alloc => regAlloc f i.id
  | .elemPtr .. | .slicePtr _ => false
  | .sliceElemVal (.inst k) _ => (V k).isSome && i.ty == VT k
  | .sliceElemVal .. => false
  | .call (.func n ..) _ => (panicOf? n).isSome
  | _ => true

mutual

def roBody (f : Func) (V : InstId → Option (Array Value)) (VT : InstId → TyId) : List Inst → Bool
  | [] => true
  | i :: rest => roNested f V VT i && roBody f V VT rest
termination_by l => (sizeOf l, 0)

def roNested (f : Func) (V : InstId → Option (Array Value)) (VT : InstId → TyId) (i : Inst) : Bool :=
  roInst f V VT i && match _h : i.op with
    | .block b | .loop b => roBody f V VT b.toList
    | .condBr _ t e => roBody f V VT t.toList && roBody f V VT e.toList
    | .switchBr _ cs e => roCases f V VT cs.toList && roBody f V VT e.toList
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

def roCases (f : Func) (V : InstId → Option (Array Value)) (VT : InstId → TyId) : List SwitchCase → Bool
  | [] => true
  | sc :: more => roBody f V VT sc.body.toList && roCases f V VT more
termination_by l => (sizeOf l, 0)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [sizeOf_toList]
  all_goals (try have := sizeOf_case_body sc); omega

end

/-- Reading item `j` of `s` as the AIR type `t` (the memory path of `slice_elem_val`, from a
memory up to reads of `m₀`) gives item `j` of `items`, or the same error, and leaves a memory up
to reads of `m₀`. -/
def Holds (m₀ : Mem) (f : Func) (t : TyId) (s : Zig.Slice) (a : Nat) (items : Array Value) : Prop :=
  ∀ size al j m, itemLayout f t a = some (size, al) → UpToReads m₀ m →
    RelR (fun (p : Value × Mem) (v : Value) => p.1 = v ∧ UpToReads m₀ p.2)
      ((do Zig.checkIndex s j; loadAs f t (s.ptr.elem size j) al).run m) (Zig.index items j)

/-- The arguments of a run with the view `V`: no pointers; each viewed `arg` is a slice that
holds the view's items in `m₀`, which are no pointers either. -/
def ArgsView (m₀ : Mem) (f : Func) (V : InstId → Option (Array Value)) (VT : InstId → TyId)
    (args : List Value) : Prop :=
  (∀ v ∈ args, v.noPtr = true) ∧
  ∀ k items idx t, V k = some items → argAt f k = some (idx, t) →
    ∃ s a, args[idx]? = some (.slice s) ∧ ptrAlignOf f t = some a ∧ Holds m₀ f (VT k) s a items ∧
      ∀ v ∈ items, v.noPtr = true

/-- The environment of a run with the view `V`: no pointers, and each viewed instruction holds its
argument. -/
def EnvOk (f : Func) (V : InstId → Option (Array Value)) (args : List Value) (env : Env) : Prop :=
  (∀ k t v, env k = some (t, v) → v.noPtr = true) ∧
  ∀ k items t v, V k = some items → env k = some (t, v) →
    ∃ idx, argAt f k = some (idx, t) ∧ args[idx]? = some v

def ExitOk : Exit → Prop
  | .br _ v | .ret v => v.noPtr = true
  | .rep _ => True

theorem EnvOk.set {f : Func} {V : InstId → Option (Array Value)} {args : List Value} {env : Env}
    (h : EnvOk f V args env) (id : InstId) (t : TyId) (v : Value) (hv : v.noPtr = true)
    (hV : V id = none) : EnvOk f V args (env.set id t v) := by
  refine ⟨fun k t' w hk => ?_, fun k items t' w hk he => ?_⟩
  · simp only [Env.set] at hk; split at hk
    · cases hk; exact hv
    · exact h.1 k t' w hk
  · simp only [Env.set] at he; split at he
    · subst_vars; rw [hV] at hk; cases hk
    · exact h.2 k items t' w hk he

theorem operand_noPtr {f : Func} {V : InstId → Option (Array Value)} {args : List Value} {env : Env}
    (h : EnvOk f V args env) (v : Val) : OkR (·.noPtr = true) (operand f env v) := by
  intro w hw
  cases v with
  | inst k =>
    simp only [operand] at hw
    cases hk : env k with
    | none => rw [hk] at hw; cases hw
    | some p => obtain ⟨t', u⟩ := p; rw [hk] at hw; cases hw; exact h.1 k t' w hk
  | int t n =>
    simp only [operand] at hw
    split at hw <;> cases hw; rfl
  | bool b => cases hw; rfl
  | void => cases hw; rfl
  | _ => cases hw

/-- Under `EnvOk` no operand is a pointer, so every access through one is stuck. -/
theorem ptrOperand_none {f : Func} {V : InstId → Option (Array Value)} {args : List Value} {env : Env}
    (h : EnvOk f V args env) (v : Val) : (ptrOperand f env v).run = none := by
  unfold ptrOperand
  split
  · rw [Result.run_bind']
    rcases ho : (operand f env v).run with _ | (e | w)
    · rfl
    · exfalso
      cases v <;> simp only [operand] at ho
      · split at ho <;> cases ho
      · split at ho <;> cases ho
      all_goals cases ho
    · have := operand_noPtr h v w ho
      cases w <;> simp only [Value.noPtr, Bool.false_eq_true] at this <;> (dsimp only; split <;> first | rfl | (exfalso; simp_all))
  · rfl

theorem relR_self {α : Type} {P : α → Prop} {r : Result α} (h : OkR P r) :
    RelR (fun a b => a = b ∧ P a) r r := by
  unfold RelR
  rcases hr : r.run with _ | (e | a)
  · trivial
  · rfl
  · exact ⟨rfl, h a hr⟩

/-- A computation in memory that does not touch it. -/
def MemFree {α : Type} (P : α → Prop) (x : MemM α) : Prop :=
  ∃ r : Result α, OkR P r ∧ ∀ m, x.run m = (fun a => (a, m)) <$> r

theorem sim_liftMem {α : Type} {m₀ : Mem} {P : α → Prop} {x : MemM α} (h : MemFree P x) :
    Sim m₀ P (liftMem x) (liftMem x) := by
  obtain ⟨r, hr, hx⟩ := h
  intro fr m hfr hm
  simp only [liftMem, StateT.run_lift, StateT.run_bind, StateT.run_pure, hx, bind_map_left]
  exact relR_bind (relR_self hr) fun a b ⟨hab, hP⟩ => by subst hab; exact relR_pure ⟨rfl, hP, hfr, hm, rfl⟩

theorem memFree_lift {α : Type} {P : α → Prop} {r : Result α} (h : OkR P r) :
    MemFree P (StateT.lift r) :=
  ⟨r, h, fun m => by simp only [StateT.run_lift]; rfl⟩

theorem memFree_none {α β : Type} {P : β → Prop} {r : Result α} (h : r.run = none)
    (g : α → MemM β) : MemFree P (StateT.lift r >>= g) := by
  refine ⟨stuck, okR_stuck, fun m => ?_⟩
  apply ExceptT.ext
  simp only [StateT.run_bind, StateT.run_lift, ExceptT.run_bind, h]
  rfl

theorem memFree_liftPure {α β : Type} {P : β → Prop} (r : Result α) (g : α → β) (h : ∀ a, P (g a)) :
    MemFree P (StateT.lift r >>= fun a => pure (g a)) :=
  ⟨g <$> r, okR_map h, fun m => by
    rw [StateT.run_bind, StateT.run_lift]
    simp only [StateT.run_pure, bind_assoc, pure_bind, bind_pure_comp, Functor.map_map, Function.comp_def]⟩

theorem evalPure_noPtr (f : Func) (env : Env) (i : Inst) : OkR (·.noPtr = true) (evalPure f env i) := by
  obtain ⟨id, ty, op⟩ := i
  cases op <;> simp only [evalPure] <;> (try unfold intBin) <;>
  repeat' (first
    | exact okR_stuck
    | exact okR_throw
    | ((with_reducible apply okR_pure); rfl)
    | ((with_reducible apply okR_bind); intro _)
    | split)

/-- The slice operand `.inst k`: the slice that `k` holds, at its type's alignment. -/
theorem sliceOperand_ok (f : Func) (env : Env) (k : InstId) :
    OkR (fun p : Zig.Slice × Nat => ∃ t, env k = some (t, .slice p.1) ∧ ptrAlignOf f t = some p.2)
      (sliceOperand f env (.inst k)) := by
  intro p hp
  unfold sliceOperand at hp
  cases hk : env k with
  | none => simp only [operandTy, hk, Option.map_none] at hp; cases hp
  | some q =>
    obtain ⟨t, u⟩ := q
    simp only [operandTy, hk, Option.map_some, operand, pure_bind] at hp
    revert hp
    cases f.plainSlice t <;> cases hpa : ptrAlignOf f t <;> cases u <;> intro hp <;>
      (try cases hp)
    exact ⟨t, rfl, hpa⟩

/-- `evalMem` of an operation other than an item pointer, slice pointer or item read does not
touch memory when no operand is a pointer (`EnvOk`). -/
theorem evalMem_memFree {f : Func} {V : InstId → Option (Array Value)} {args : List Value} {env : Env}
    (h : EnvOk f V args env) (i : Inst)
    (hop : match i.op with | .elemPtr .. | .slicePtr _ | .sliceElemVal .. => False | _ => True) :
    MemFree (·.noPtr = true) (evalMem f env i) := by
  obtain ⟨id, ty, op⟩ := i
  have hpure := evalPure_noPtr f env ⟨id, ty, op⟩
  cases op <;> simp only at hop <;> simp only [evalMem]
  all_goals first
    | exact memFree_lift hpure
    | exact memFree_none (ptrOperand_none h _) _
    | (split
       · exact memFree_none (ptrOperand_none h _) _
       · exact memFree_lift okR_stuck)
    | (split
       · exact memFree_liftPure _ _ fun _ => rfl
       · exact memFree_lift okR_stuck)
    | skip
  -- `cmp`: an operand is never a pointer, so the comparison is `evalPure`'s.
  rename_i op a b
  refine ⟨operand f env a >>= fun _ => evalPure f env ⟨id, ty, .cmp op a b⟩, okR_bind fun _ => hpure, fun m => ?_⟩
  simp only [StateT.run_bind, StateT.run_lift, map_bind, bind_assoc, pure_bind]
  apply bind_congr_ok _ (fun w : Value => w.noPtr = true) (operand_noPtr h a)
  intro w hw
  cases w <;> simp only [Value.noPtr, Bool.false_eq_true] at hw <;> simp only [StateT.run_lift] <;> rfl

theorem sim_stuck {α : Type} {m₀ : Mem} {P : α → Prop} {x y : SM α}
    (hx : ∀ fr m, ((x.run fr).run m).run = none) (hy : ∀ fr, ((y.run fr).run m₀).run = none) :
    Sim m₀ P x y := by
  intro fr m _ _
  unfold RelR; rw [hx, hy]; trivial

theorem liftMem_lift_bind {α β : Type} (x : Result α) (g : α → MemM β) :
    liftMem (StateT.lift x >>= g) = liftR x >>= fun a => liftMem (g a) := by
  simp only [liftMem, liftR]
  apply StateT.ext; intro fr
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]

/-- The memory read of a viewed item against the view's item (`Holds`). -/
theorem sim_read {m₀ : Mem} {x : MemM Value} {y : Result Value}
    (h : ∀ m, UpToReads m₀ m → RelR (fun (p : Value × Mem) v => p.1 = v ∧ UpToReads m₀ p.2) (x.run m) y)
    (hy : OkR (·.noPtr = true) y) : Sim m₀ (·.noPtr = true) (liftMem x) (liftR y) := by
  intro fr m hfr hm
  simp only [liftMem, liftR, StateT.run_lift, StateT.run_bind, StateT.run_pure]
  have hxy := h m hm
  unfold RelR at hxy ⊢
  rw [Result.run_bind', Result.run_bind', Result.run_bind']
  rcases hx : (x.run m).run with _ | (e | ⟨v, m'⟩) <;> rcases hyr : y.run with _ | (e' | w) <;>
    simp only [hx, hyr] at hxy ⊢
  · exact hxy
  · obtain ⟨rfl, hm'⟩ := hxy
    exact ⟨rfl, hy _ hyr, hfr, hm', rfl⟩

theorem FrOk.setCell {fr : Frame} (h : FrOk fr) (k : InstId) (v : Option Value)
    (hv : ∀ w, v = some w → w.noPtr = true) : FrOk (fr.setCell k v) := by
  refine ⟨h.1, fun j w hj => ?_⟩
  simp only [Frame.setCell_cells] at hj
  split at hj
  · exact hv w hj
  · exact h.2 j w hj

theorem EnvOk.set' {f : Func} {V : InstId → Option (Array Value)} {args : List Value} {env : Env}
    (h : EnvOk f V args env) (id : InstId) (t : TyId) (v : Value) (hv : v.noPtr = true)
    (hV : ∀ items, V id = some items → ∃ idx, argAt f id = some (idx, t) ∧ args[idx]? = some v) :
    EnvOk f V args (env.set id t v) := by
  refine ⟨fun k t' w hk => ?_, fun k items t' w hk he => ?_⟩
  · simp only [Env.set] at hk; split at hk
    · cases hk; exact hv
    · exact h.1 k t' w hk
  · simp only [Env.set] at he; split at he
    · subst_vars; cases he; exact hV items hk
    · exact h.2 k items t' w hk he

/-- The instruction `id` is not viewed unless it is an `arg`. -/
theorem roInst_view {f : Func} {V : InstId → Option (Array Value)} {VT : InstId → TyId} {id : InstId}
    {ty : TyId} {op : Op} (h : roInst f V VT ⟨id, ty, op⟩ = true) (hop : ∀ idx, op ≠ .arg idx) :
    V id = none := by
  unfold roInst at h
  cases hv : V id with
  | none => rfl
  | some items =>
    rw [hv] at h
    cases op <;> simp_all

/-- `roInst` of an instruction other than `alloc`, `elemPtr`, `slicePtr`, `slice_elem_val` and a
call, in `evalMem`'s terms. -/
theorem roInst_evalMem {f : Func} {V : InstId → Option (Array Value)} {VT : InstId → TyId} {i : Inst}
    (h : roInst f V VT i = true) (hs : ∀ k idx, i.op ≠ .sliceElemVal (.inst k) idx) :
    match i.op with | .elemPtr .. | .slicePtr _ | .sliceElemVal .. => False | _ => True := by
  obtain ⟨id, ty, op⟩ := i
  unfold roInst at h
  cases op <;> simp_all

theorem cellRead_ok {fr : Frame} (h : FrOk fr) (t : Ty) (k : InstId) :
    OkR (·.noPtr = true) (cellRead t (fr.cells k)) := by
  intro v hv
  unfold cellRead at hv
  split at hv
  · rename_i w hw
    split at hv
    · cases hv; exact h.2 k _ hw
    · cases hv
  · cases hv

theorem cellVal_ok {f : Func} {V : InstId → Option (Array Value)} {args : List Value} {env : Env}
    (h : EnvOk f V args env) (v : Val) :
    OkR (fun cv : Option Value => ∀ w, cv = some w → w.noPtr = true) (cellVal f env v) := by
  intro cv hcv w hw
  subst hw
  unfold cellVal at hcv
  split at hcv
  · cases hcv
  · have hb : (operand f env v >>= fun a => pure (some a)).run = some (.ok (some w)) := by
      rw [bind_pure_comp]; exact hcv
    obtain ⟨a, ha, hm⟩ := Result.bind_ok hb
    cases hm
    exact operand_noPtr h v _ ha

theorem liftR_stuck_bind {α β : Type} (k : α → SM β) : (liftR stuck : SM α) >>= k = liftR stuck := by
  apply StateT.ext; intro fr; apply StateT.ext; intro m
  simp only [liftR, StateT.run_bind, StateT.run_lift]
  rfl

/-- The `roInst` of an instruction in a nested body (`roNested`). -/
theorem roNested_inst {f : Func} {V : InstId → Option (Array Value)} {VT : InstId → TyId} {i : Inst}
    (h : roNested f V VT i = true) : roInst f V VT i = true := by
  unfold roNested at h; simp only [Bool.and_eq_true] at h; exact h.1

local macro "sim_ih" : tactic => `(tactic| first
  | assumption
  | (apply_assumption <;> first | assumption | simp_all [roBody, roNested, roCases]))

/-- The simulation: a body of a read-only function runs, from a memory up to reads of `m₀`, as its
view from `m₀` (`Sim`). -/
theorem execBody_view (m₀ : Mem) (f : Func) (args : List Value) (call : Oracle)
    (V : InstId → Option (Array Value)) (VT : InstId → TyId) (hargs : ArgsView m₀ f V VT args) :
    ∀ l env, roBody f V VT l = true → EnvOk f V args env →
      Sim m₀ ExitOk (execBody ⟨f, args, call, fun _ => none⟩ l env) (execBody ⟨f, args, call, V⟩ l env) := by
  apply execBody.induct ⟨f, args, call, fun _ => none⟩
    (motive2 := fun i rest env => roNested f V VT i = true → roBody f V VT rest = true →
      EnvOk f V args env →
      Sim m₀ ExitOk (execInst ⟨f, args, call, fun _ => none⟩ i rest env) (execInst ⟨f, args, call, V⟩ i rest env))
    (motive3 := fun s w x cs el env => roCases f V VT cs = true → roBody f V VT el.toList = true →
      EnvOk f V args env →
      Sim m₀ ExitOk (execSwitch ⟨f, args, call, fun _ => none⟩ s x cs el env)
        (execSwitch ⟨f, args, call, V⟩ s x cs el env))
    (motive4 := fun id body env => roBody f V VT body.toList = true → EnvOk f V args env →
      Sim m₀ ExitOk (execLoop ⟨f, args, call, fun _ => none⟩ id body env)
        (execLoop ⟨f, args, call, V⟩ id body env))
  case case1 =>
    intro env _ _
    simp only [execBody]
    exact sim_liftR _ fun _ h => by cases h
  case case2 =>
    intro i rest env ih hro henv
    simp only [roBody, Bool.and_eq_true] at hro
    simp only [execBody]
    exact ih hro.1 hro.2 henv
  case case26 =>
    intro s w x el env ih _ hel henv
    simp only [execSwitch]
    exact ih hel henv
  case case27 =>
    intro s w x sc more el env ihb ihm hc hel henv
    simp only [roCases, Bool.and_eq_true] at hc
    unfold execSwitch
    exact sim_bind (sim_liftR _ fun _ _ => trivial) fun b _ => by
      split
      · exact ihb hc.1 henv
      · exact ihm hc.2 hel henv
  case case28 =>
    intro id body env ih hb henv
    simp only [execLoop]
    exact sim_loop _ (ih hb henv)
  case case3 =>
    intro i rest env index hop v hv ih hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have hri := roNested_inst hro
    simp only at hv
    simp only [execInst, hv]
    refine ih hrest (henv.set' _ _ _ (hargs.1 v (List.mem_of_getElem? hv)) fun items hV => ?_)
    unfold roInst at hri
    simp only [hV, beq_iff_eq, Bool.and_true] at hri
    exact ⟨index, hri, hv⟩
  case case4 =>
    intro i rest env index hop hv hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only at hv
    simp only [execInst, hv]
    exact sim_liftR _ fun _ h => by cases h
  case case5 =>
    intro i rest env body hop ihb ihr hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have hri := roNested_inst hro
    simp only [roNested, Bool.and_eq_true] at hro
    simp only [execInst]
    refine sim_bind (ihb hro.2 henv) fun e he => ?_
    split
    · rename_i t v
      split
      · subst_vars
        exact ihr _ v rfl hrest (henv.set _ _ _ he (roInst_view hri (by simp)))
      · exact sim_pure he
    · exact sim_pure he
  case case6 =>
    intro i rest env body hop ih hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [roNested, Bool.and_eq_true] at hro
    simp only [execInst]
    exact ih hro.2 henv
  case case7 =>
    intro i rest env t v hop hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst]
    exact sim_bind (sim_liftR _ (operand_noPtr henv v)) fun w hw => sim_pure hw
  case case8 =>
    intro i rest env t hop hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst]
    exact sim_pure trivial
  case case9 =>
    intro i rest env v hop hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst]
    exact sim_bind (sim_liftR _ (operand_noPtr henv v)) fun w hw => sim_pure hw
  case case10 =>
    intro i rest env hop hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst]
    exact sim_liftR _ fun _ h => by cases h
  case case11 =>
    intro i rest env hop hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst]
    exact sim_liftR _ fun _ h => by cases h
  case case12 =>
    intro i rest env cv th el hop iht ihe hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [roNested, Bool.and_eq_true] at hro
    simp only [execInst]
    refine sim_bind (sim_liftR _ fun _ _ => trivial) fun w _ =>
      sim_bind (sim_liftR _ fun _ _ => trivial) fun b _ => ?_
    split
    · exact iht hro.2.1 henv
    · exact ihe hro.2.2 henv
  case case13 =>
    intro i rest env v cs el hop ih hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [roNested, Bool.and_eq_true] at hro
    simp only [execInst]
    refine sim_bind (sim_liftR _ fun _ _ => trivial) fun w _ => ?_
    cases w <;> dsimp only
    case int s w x => exact ih s w x hro.2.1 hro.2.2 henv
    all_goals exact sim_liftR _ fun _ h => by cases h
  case case14 =>
    intro i rest env hop hreg ih hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have hri := roNested_inst hro
    simp only at hreg
    simp only [execInst, hreg, ite_true]
    exact sim_bind (sim_modify _ fun fr h => h.setCell _ _ (by simp)) fun _ _ =>
      ih hrest (henv.set _ _ _ rfl (roInst_view hri (by simp)))
  case case15 =>
    intro i rest env hop hreg _ _ _ _ _ _ hro
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have hri := roNested_inst hro
    simp only at hreg
    simp [roInst, hreg] at hri
  case case16 =>
    intro i rest env hop hreg _ hro
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have hri := roNested_inst hro
    simp only at hreg
    simp [roInst, hreg] at hri
  case case17 =>
    intro i rest env p hop ih hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have hri := roNested_inst hro
    simp only [execInst]
    refine sim_bind (P := fun v => v.noPtr = true) ?_ fun v hv =>
      ih v hrest (henv.set _ _ _ hv (roInst_view hri (by simp)))
    refine sim_bind (sim_liftR _ (operand_noPtr henv p)) fun w _ => ?_
    cases w with
    | cell k =>
      exact sim_bind (sim_get (P := FrOk) fun _ h => h) fun fr hfr => sim_liftR _ (cellRead_ok hfr _ k)
    | _ => exact sim_liftMem (evalMem_memFree henv _ trivial)
  case case18 =>
    intro i rest env p v hop ih hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have hri := roNested_inst hro
    simp only [execInst]
    refine sim_bind (P := fun _ => True) ?_ fun _ _ =>
      ih hrest (henv.set _ _ _ rfl (roInst_view hri (by simp)))
    refine sim_bind (sim_liftR _ (operand_noPtr henv p)) fun w _ => ?_
    cases w with
    | cell k =>
      exact sim_bind (sim_liftR _ (cellVal_ok henv v)) fun cv hcv => sim_modify _ fun _ h => h.setCell k cv hcv
    | _ => exact sim_bind (sim_liftMem (evalMem_memFree henv _ trivial)) fun _ _ => sim_pure trivial
  case case19 =>
    intro i rest env name nr sp as hop e he hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst, he]
    exact sim_liftR _ fun _ h => by cases h
  case case20 =>
    intro i rest env name nr sp as hop he _ hro
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have hri := roNested_inst hro
    simp [roInst, he] at hri
  case case21 =>
    intro i rest env n hop ih hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst]
    exact ih hrest henv
  case case22 =>
    intro i rest env n v hop ih hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst]
    exact ih hrest henv
  case case23 =>
    intro i rest env k idx hop items hv
    simp at hv
  case case24 =>
    intro i rest env k idx hop _ ih hro hrest henv
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have hri := roNested_inst hro
    have hid := roInst_view hri (by simp)
    unfold roInst at hri
    simp only [hid, Bool.true_and, Bool.and_eq_true, Option.isSome_iff_exists, beq_iff_eq] at hri
    obtain ⟨⟨items, hVk⟩, hty⟩ := hri
    subst hty
    simp only [execInst, hVk, evalMem, liftMem_lift_bind, bind_assoc]
    refine sim_bind (sim_liftR _ (sliceOperand_ok f env k)) ?_
    rintro ⟨s, a⟩ ⟨t, hk, ha⟩
    have ⟨idx', harg, hidx⟩ := henv.2 k items t _ hVk hk
    obtain ⟨s', a', hs', ha', hholds, hitems⟩ := hargs.2 k items idx' t hVk harg
    rw [hidx] at hs'; cases hs'
    rw [ha] at ha'; cases ha'
    dsimp only
    refine sim_bind (sim_liftR _ fun _ _ => trivial) fun j _ => ?_
    cases hil : itemLayout f (VT k) a with
    | none =>
      dsimp only
      exact sim_stuck (fun _ _ => rfl) (fun _ => rfl)
    | some p =>
      obtain ⟨size, al⟩ := p
      dsimp only
      refine sim_bind (sim_read (fun m hm => hholds size al j m hil hm) ?_) fun v hv =>
        ih v hrest (henv.set _ _ _ hv hid)
      intro v hv
      unfold Zig.index at hv
      split at hv
      · cases hv; exact hitems _ (Array.getElem_mem _)
      · cases hv
  case case25 =>
    intro i rest env h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 ih hro hrest henv
    obtain ⟨id, ty, op⟩ := i
    have hri := roNested_inst hro
    have hop := roInst_evalMem hri fun k idx h => h17 k idx h
    have hid := roInst_view hri fun idx h => h1 idx h
    cases op
    all_goals first
      | exact (hop : False).elim
      | (exfalso; apply h1; rfl)
      | (exfalso; apply h2; rfl)
      | (exfalso; apply h3; rfl)
      | (exfalso; apply h4; rfl)
      | (exfalso; apply h5; rfl)
      | (exfalso; apply h6; rfl)
      | (exfalso; apply h7; rfl)
      | (exfalso; apply h8; rfl)
      | (exfalso; apply h9; rfl)
      | (exfalso; apply h10; rfl)
      | (exfalso; apply h11; rfl)
      | (exfalso; apply h12; rfl)
      | (exfalso; apply h13; rfl)
      | (exfalso; apply h14; rfl)
      | (exfalso; apply h15; rfl)
      | (exfalso; apply h16; rfl)
      | (exfalso; apply h17; rfl)
      | (simp only [execInst]
         exact sim_bind (sim_liftMem (evalMem_memFree henv _ hop)) fun v hv =>
           ih v hrest (henv.set _ _ _ hv hid))

/-! ## Functions -/

/-- `execFunc` with the view `view` (`Ctx.view`). Not the meaning of AIR: a certificate normalizes
it against the generated definition, and `execFunc_view` relates it to `execFunc`. -/
def execFuncV (call : Oracle) (view : InstId → Option (Array Value)) (f : Func) (args : List Value) :
    MemM Value :=
  if argsOk f f.params.toList args then do
    let (e, frame) ← (execBody ⟨f, args, call, view⟩ f.body.toList (fun _ => none)).run {}
    frame.blocks.forM Zig.free
    match e with
    | .ret v => pure v
    | _ => StateT.lift stuck
  else StateT.lift stuck

/-- A function that reads memory only through the viewed slices: `execFunc` from `m₀` gives the
values and errors of its view, and a memory up to reads of `m₀`; the view leaves `m₀`. -/
theorem execFunc_view (m₀ : Mem) (f : Func) (args : List Value) (call : Oracle)
    (V : InstId → Option (Array Value)) (VT : InstId → TyId)
    (hro : roBody f V VT f.body.toList = true) (hargs : ArgsView m₀ f V VT args) :
    RelR (fun (p q : Value × Mem) => p.1 = q.1 ∧ UpToReads m₀ p.2 ∧ q.2 = m₀)
      ((execFunc call f args).run m₀) ((execFuncV call V f args).run m₀) := by
  unfold execFunc execFuncV
  split
  · simp only [StateT.run_bind]
    have hsim := execBody_view m₀ f args call V VT hargs f.body.toList (fun _ => none) hro
      ⟨fun _ _ _ h => (by cases h), fun _ _ _ _ _ h => (by cases h)⟩ {} m₀
      ⟨rfl, fun _ _ h => (by cases h)⟩ (UpToReads.refl m₀)
    refine relR_bind hsim ?_
    rintro ⟨⟨e, fr⟩, m⟩ ⟨⟨e', fr'⟩, m'⟩ ⟨h1, _, hfr, hm, rfl⟩
    simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    dsimp only
    rw [hfr.1]
    simp only [Cert.free_nil, StateT.run_pure, pure_bind]
    cases e with
    | ret v => exact relR_pure ⟨rfl, hm, rfl⟩
    | _ => exact relR_stuck
  · exact relR_stuck

/-! ## The items that `Zig.readSlice` reads are a view -/

/-- No recorded access has observed an access of the running thread that it has not made yet: every
entry's component of the running thread is at most that thread's own clock. Every memory that a run
from `Mem.ofGlobals` reaches has this property (a thread's own component only grows, and another
thread learns it only through a fork, join or release edge). -/
def _root_.Zig.Mem.ClockWf (m : Mem) : Prop :=
  ∀ e ∈ m.footprint, e.clock.get m.current ≤ (m.clocks[m.current]!).get m.current

theorem VClock.get_bump (c : VClock) (t i : Nat) :
    (VClock.bump c t).get i = if i = t then c.get t + 1 else c.get i := by
  unfold VClock.bump VClock.get
  generalize hc' : (if t < c.size then c else c ++ Array.replicate (t + 1 - c.size) 0) = c'
  have hsz : t < c'.size := by
    subst hc'; split
    · assumption
    · simp only [Array.size_append, Array.size_replicate]; omega
  have hext : ∀ k : Nat, c'[k]?.getD 0 = c[k]?.getD 0 := by
    intro k
    subst hc'
    split
    · rfl
    · rw [Array.getElem?_append]
      split
      · rfl
      · rename_i hk
        rw [Array.getElem?_eq_none (xs := c) (by omega)]
        simp only [Array.getElem?_replicate]
        split <;> rfl
  show (c'.set! t (c'.getD t 0 + 1)).getD i 0 = _
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : i = t
  · subst h; simp only [↓reduceIte, hsz, Option.getD_some, hext]
  · simp only [Ne.symm h, ↓reduceIte, hext, h]

theorem VClock.le_bump_mono {a b : VClock} (t : Nat) (h : VClock.le a b = true) :
    VClock.le (VClock.bump a t) (VClock.bump b t) = true := by
  rw [VClock.le_iff] at h ⊢
  intro i
  rw [VClock.get_bump, VClock.get_bump]
  split
  · have := h t; omega
  · exact h i

theorem VClock.le_bump (a : VClock) (t : Nat) : VClock.le a (VClock.bump a t) = true := by
  rw [VClock.le_iff]; intro i; rw [VClock.get_bump]; split <;> (try subst_vars) <;> omega

theorem Result.map_ok_inv {α β : Type} {f : α → β} {x : Result α} {b : β}
    (h : (f <$> x).run = some (.ok b)) : ∃ a, x.run = some (.ok a) ∧ f a = b := by
  rw [← bind_pure_comp] at h
  obtain ⟨a, ha, hb⟩ := Result.bind_ok h
  cases hb
  exact ⟨a, ha, rfl⟩

/-- `mapM` of a lifted pure function over `Array.range n` in memory: the memory is unchanged and
each item is the function's value. -/
theorem mapM_range_ok {β : Type} (g : Nat → Result β) (n : Nat) (m m' : Mem) (arr : Array β)
    (h : (((Array.range n).mapM (fun i => (liftM (g i) : MemM β))).run m).run = some (.ok (arr, m'))) :
    m' = m ∧ arr.size = n ∧ ∀ j (hj : j < arr.size), (g j).run = some (.ok arr[j]) := by
  rw [Array.mapM_eq_mapM_toList, Array.toList_range, StateT.run_map] at h
  have hl : ∀ (l : List Nat) (r : List β) (m' : Mem),
      ((l.mapM (fun i => (liftM (g i) : MemM β))).run m).run = some (.ok (r, m')) →
      m' = m ∧ r.length = l.length ∧
        ∀ j (hj : j < l.length) (hj' : j < r.length), (g l[j]).run = some (.ok r[j]) := by
    intro l
    induction l with
    | nil =>
      intro r m' hr
      simp only [List.mapM_nil, StateT.run_pure] at hr
      cases hr
      exact ⟨rfl, rfl, fun j hj => absurd hj (by simp)⟩
    | cons x l ih =>
      intro r m' hr
      rw [List.mapM_cons] at hr
      simp only [StateT.run_bind, liftM, monadLift, MonadLift.monadLift, StateT.run_lift] at hr
      obtain ⟨⟨b, m₂⟩, hb, hr⟩ := Result.bind_ok hr
      obtain ⟨b', hb', hb2⟩ := Result.bind_ok hb
      cases hb2
      obtain ⟨⟨bs, m₃⟩, hbs, hr⟩ := Result.bind_ok hr
      cases hr
      obtain ⟨rfl, hlen, hall⟩ := ih bs m₃ hbs
      refine ⟨rfl, by simp [hlen], fun j hj hj' => ?_⟩
      cases j with
      | zero => simpa using hb'
      | succ j => simpa using hall j (by simp at hj; omega) (by simp at hj'; omega)
  obtain ⟨⟨r, m''⟩, hr, hm⟩ := Result.map_ok_inv h
  cases hm
  obtain ⟨rfl, hlen, hall⟩ := hl _ r _ hr
  simp only [List.length_range] at hlen
  refine ⟨rfl, by simp [hlen], fun j hj => ?_⟩
  simp only [List.size_toArray] at hj
  have := hall j (by simp only [List.length_range]; omega) hj
  simpa using this

theorem Array.getElem!_set!_self {α : Type} [Inhabited α] (xs : Array α) (t : Nat) (v : α) :
    (xs.set! t v)[t]! = if t < xs.size then v else xs[t]! := by
  rw [Array.set!_eq_setIfInBounds]
  split
  · rename_i h; rw [getElem!_pos _ t (by simpa using h)]; simp
  · rw [Array.setIfInBounds_eq_of_size_le (by omega)]

theorem UpToReads.blocks {m₀ m : Mem} (h : UpToReads m₀ m) : m.blocks = m₀.blocks := by
  have := congrArg Mem.blocks h.rest; exact this

theorem UpToReads.current {m₀ m : Mem} (h : UpToReads m₀ m) : m.current = m₀.current := by
  have := congrArg Mem.current h.rest; exact this

/-- `m` after a read of `n` bytes at `b`/`o`, recorded by its running thread (`recordAccess`). -/
def _root_.Zig.Mem.withRead (m : Mem) (b : BlockId) (o n : Nat) : Mem :=
  let t := m.current
  let c := VClock.bump (m.clocks[t]!) t
  { m with clocks := m.clocks.set! t c, footprint := m.footprint.push ⟨t, c, b, o, n, .read⟩ }

theorem UpToReads.solo {m₀ m : Mem} (h : UpToReads m₀ m) : m.solo = m₀.solo := by
  have h1 := congrArg Mem.current h.rest
  have h2 := congrArg Mem.threads h.rest
  simp only at h1 h2
  simp only [Mem.solo, h1, h2]

/-- A successful `loadBytes`: the access, the race check, the bytes and the new memory. -/
theorem loadBytes_ok {p : Ptr} {n al : Nat} {m m' : Mem} {bs : Array Byte}
    (h : ((loadBytes p n al).run m).run = some (.ok (bs, m'))) :
    ∃ b blk o, m.access p n al = pure (b, blk, o) ∧
      raceCheck m (VClock.bump (m.clocks[m.current]!) m.current) b o n .read = none ∧
      bs = blk.bytes.extract o (o + n) ∧ m' = m.withRead b o n := by
  simp only [loadBytes, recordAccess, StateT.run_bind, StateT.run_get, pure_bind, liftM, monadLift,
    MonadLift.monadLift, StateT.run_lift, bind_assoc] at h
  obtain ⟨⟨b, blk, o⟩, hacc, h⟩ := Result.bind_ok h
  split at h
  · obtain ⟨_, hx, _⟩ := Result.bind_ok h
    cases hx
  · rename_i hrc
    simp only [StateT.run_set, StateT.run_pure, pure_bind] at h
    cases h
    exact ⟨b, blk, o, hacc, hrc, rfl, rfl⟩

theorem loadBytes_run {p : Ptr} {n al : Nat} {m : Mem} {b : BlockId} {blk : Block} {o : Nat}
    (hacc : m.access p n al = pure (b, blk, o))
    (hrc : raceCheck m (VClock.bump (m.clocks[m.current]!) m.current) b o n .read = none) :
    (loadBytes p n al).run m = pure (blk.bytes.extract o (o + n), m.withRead b o n) := by
  simp only [loadBytes, recordAccess, StateT.run_bind, StateT.run_get, pure_bind, liftM, monadLift,
    MonadLift.monadLift, StateT.run_lift, bind_assoc, hacc, hrc, StateT.run_set, StateT.run_pure]
  rfl

theorem throw_ne_pure {α : Type} (e : Zig.Error) (a : α) : (throw e : Result α) ≠ pure a := by
  intro h; have := congrArg ExceptT.run h; cases this

theorem access_eq {m : Mem} {p : Ptr} {n al : Nat} {b : BlockId} {blk : Block} {o : Nat} :
    m.access p n al = pure (b, blk, o) ↔ p.block = some b ∧ m.blocks[b]? = some blk ∧
      (blk.live = true ∧ 0 ≤ p.off ∧ p.off + n ≤ blk.bytes.size ∧ (blk.addr + p.off.toNat) % al = 0) ∧
      o = p.off.toNat := by
  unfold Mem.access
  cases hpb : p.block with
  | none => simp only [reduceCtorEq, false_and, iff_false]; exact throw_ne_pure _ _
  | some b' =>
    cases hblk : m.blocks[b']? with
    | none =>
      simp only [hblk]
      constructor
      · intro h; exact absurd h (throw_ne_pure _ _)
      · rintro ⟨h1, h2, _⟩; cases h1; rw [hblk] at h2; cases h2
    | some blk' =>
      simp only [hblk]
      split
      · rename_i hc
        constructor
        · intro h; cases h; exact ⟨rfl, hblk, hc, rfl⟩
        · rintro ⟨h1, h2, _, h4⟩; cases h1; rw [hblk] at h2; cases h2; subst h4; rfl
      · rename_i hc
        constructor
        · intro h; cases h
        · rintro ⟨h1, h2, h3, _⟩; cases h1; rw [hblk] at h2; cases h2; exact absurd h3 hc

/-- An access of an item inside an accessed range. -/
theorem access_item {m : Mem} {p : Ptr} {L sz A al j : Nat} {b : BlockId} {blk : Block} {o : Nat}
    (hacc : m.access p (L * sz) A = pure (b, blk, o)) (hj : j < L) (hA : al ∣ A) (hal : al ∣ sz) :
    m.access (p.add (sz * j)) sz al = pure (b, blk, o + sz * j) := by
  obtain ⟨hb, hblk, ⟨hlive, h0, hend, hmod⟩, rfl⟩ := access_eq.1 hacc
  have hjL : sz * j + sz ≤ L * sz := by
    have : sz * (j + 1) ≤ sz * L := Nat.mul_le_mul_left sz hj
    rw [Nat.mul_comm L sz]; rw [Nat.mul_add, Nat.mul_one] at this; exact this
  have hoff : (p.off + (sz : Int) * (j : Int)).toNat = p.off.toNat + sz * j := by
    have : ((sz * j : Nat) : Int) = (sz : Int) * (j : Int) := by push_cast; rfl
    omega
  refine access_eq.2 ⟨hb, hblk, ⟨hlive, ?_, ?_, ?_⟩, ?_⟩
  · simp only [Ptr.add]; omega
  · simp only [Ptr.add]; push_cast at hend ⊢; omega
  · simp only [Ptr.add]
    rw [hoff, ← Nat.add_assoc]
    apply Nat.mod_eq_zero_of_dvd
    exact Nat.dvd_add (Nat.dvd_trans hA (Nat.dvd_of_mod_eq_zero hmod)) (Nat.dvd_mul_right_of_dvd hal j)
  · simp only [Ptr.add]; rw [hoff]

theorem access_congr {m m' : Mem} (h : m.blocks = m'.blocks) (p : Ptr) (n al : Nat) :
    m.access p n al = m'.access p n al := by
  unfold Mem.access; rw [h]

theorem Result.eq_pure_of_run {α : Type} {x : Result α} {a : α} (h : x.run = some (.ok a)) : x = pure a :=
  ExceptT.ext h

theorem load_run {α : Type} [Enc α] {m : Mem} {p : Ptr} {al : Nat} {b : BlockId} {blk : Block} {o : Nat}
    {v : α} (hacc : m.access p (Enc.size α) al = pure (b, blk, o))
    (hrc : raceCheck m (VClock.bump (m.clocks[m.current]!) m.current) b o (Enc.size α) .read = none)
    (hdec : (Enc.decode (blk.bytes.extract o (o + Enc.size α)) : Result α).run = some (.ok v)) :
    (Zig.load α al p).run m = pure (v, m.withRead b o (Enc.size α)) := by
  unfold Zig.load
  rw [StateT.run_bind, loadBytes_run hacc hrc]
  simp only [pure_bind, StateT.run_bind, StateT.run_get, liftM, monadLift, MonadLift.monadLift,
    StateT.run_lift, decodeLoad_of_decode (Result.eq_pure_of_run hdec)]

theorem Array.set!_set! {α : Type} (xs : Array α) (t : Nat) (a b : α) :
    (xs.set! t a).set! t b = xs.set! t b := by
  simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds]

theorem Array.set!_eq_set!_getElem! {α : Type} [Inhabited α] (xs : Array α) (t : Nat) (b : α) :
    xs.set! t b = xs.set! t ((xs.set! t b)[t]!) := by
  rw [Array.getElem!_set!_self]
  split
  · rfl
  · rename_i h
    simp only [Array.set!_eq_setIfInBounds]
    rw [Array.setIfInBounds_eq_of_size_le (by omega), Array.setIfInBounds_eq_of_size_le (by omega)]

theorem UpToReads.clocks_size {m₀ m : Mem} (h : UpToReads m₀ m) : m.clocks.size = m₀.clocks.size := by
  rw [h.clocks]; simp

theorem UpToReads.withRead {m₀ m : Mem} (h : UpToReads m₀ m) (b : BlockId) (o n : Nat) :
    UpToReads m₀ (m.withRead b o n) := by
  have hcur := h.current
  have hsize := h.clocks_size
  obtain ⟨rs, hfp, hrs⟩ := h.reads
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h.rest
  · refine ⟨rs.push ⟨m.current, VClock.bump (m.clocks[m.current]!) m.current, b, o, n, .read⟩, ?_, ?_⟩
    · simp only [Mem.withRead, hfp, Array.push_append]
    · intro e he
      simp only [Array.mem_push] at he
      rcases he with he | he
      · exact hrs e he
      · subst he; exact ⟨hcur, rfl⟩
  · simp only [Mem.withRead, hcur]
    rw [h.clocks, Array.set!_set!]
    exact Array.set!_eq_set!_getElem! _ _ _
  · simp only [Mem.withRead, hcur]
    rw [Array.getElem!_set!_self]
    split
    · exact VClock.le_trans (hcur ▸ h.own) (VClock.le_bump _ _)
    · exact hcur ▸ h.own

/-- A read of a sub-range of a range that `m₀`'s race check accepted is accepted in a memory up to
reads of `m₀` (`Mem.ClockWf`: no entry has seen an access of the running thread after `m₀`). -/
theorem raceCheck_sub {m₀ m : Mem} (hm : UpToReads m₀ m) (hwf : m₀.ClockWf) {b : BlockId} {o n o' n' : Nat}
    (h0 : raceCheck m₀ (VClock.bump (m₀.clocks[m₀.current]!) m₀.current) b o n .read = none)
    (hsub : o ≤ o' ∧ o' + n' ≤ o + n) :
    raceCheck m (VClock.bump (m.clocks[m.current]!) m.current) b o' n' .read = none := by
  unfold raceCheck at h0 ⊢
  rw [hm.solo]
  split
  · rfl
  · rename_i hsolo
    rw [if_neg hsolo] at h0
    obtain ⟨rs, hfp, hrs⟩ := hm.reads
    unfold raceAt at h0 ⊢
    rw [hfp, Array.findSome?_append, Option.or_eq_none_iff]
    simp only [Array.findSome?_eq_none_iff] at h0 ⊢
    have hcur := hm.current
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · have := h0 e he
      by_cases hr : racePair e.kind .read = none
      · split <;> simp_all
      · split
        · rename_i hc
          exfalso
          rw [if_pos] at this
          · exact hr this
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc ⊢
          obtain ⟨⟨⟨hb, h1⟩, h2⟩, hconc⟩ := hc
          refine ⟨⟨⟨hb, by omega⟩, by omega⟩, ?_⟩
          -- not concurrent with the earlier clock either
          unfold VClock.concurrent at hconc ⊢
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hconc ⊢
          have hwfe := hwf e he
          constructor
          · -- ¬ e ≤ bump c₀: else e ≤ c' (monotone)
            cases hle : VClock.le e.clock (VClock.bump (m₀.clocks[m₀.current]!) m₀.current)
            · rfl
            · exfalso
              have h1 : VClock.le (VClock.bump (m₀.clocks[m₀.current]!) m₀.current)
                  (VClock.bump (m.clocks[m.current]!) m.current) = true := by
                rw [hcur]; exact VClock.le_bump_mono _ hm.own
              rw [VClock.le_trans hle h1] at hconc; exact absurd hconc.1 (by simp)
          · -- ¬ bump c₀ ≤ e: its own component is past e's (`Mem.ClockWf`)
            cases hle : VClock.le (VClock.bump (m₀.clocks[m₀.current]!) m₀.current) e.clock
            · rfl
            · exfalso
              have := (VClock.le_iff _ _).1 hle m₀.current
              rw [VClock.get_bump, if_pos rfl] at this
              omega
        · rfl
    · obtain ⟨_, hk⟩ := hrs e he
      have : racePair e.kind .read = none := by rw [hk] <;> rfl
      split <;> simp_all

/-- The items that `Zig.readSlice` reads from `m₀` (a call's materialization of a `[]const T`
argument) are a view of the slice: every later item read of a memory up to reads of `m₀` gives
the same item (`Holds`). The read's memory is up to reads of `m₀` too. `hload` and `hlay`
connect the AIR item type with the `Enc` instance; a certificate proves them by evaluation. -/
theorem holds_of_readSlice {α : Type} [Enc α] {m₀ m₁ : Mem} {f : Func} {t : TyId} {s : Zig.Slice}
    {a A : Nat} {arr : Array α} (enc : α → Value)
    (hread : ((Zig.readSlice α A s).run m₀).run = some (.ok (arr, m₁)))
    (hwf : m₀.ClockWf)
    (hload : ∀ q al, loadAs f t q al = enc <$> Zig.load α al q)
    (hlay : ∀ size al, itemLayout f t a = some (size, al) →
      size = Enc.size α ∧ 0 < size ∧ al ∣ A ∧ al ∣ size) :
    Holds m₀ f t s a (arr.map enc) ∧ arr.size = s.len.toNat ∧ UpToReads m₀ m₁ := by
  -- An index at or past the length: `.illegal` on both sides.
  have hout : ∀ size al j m, ¬ j.toNat < s.len.toNat → arr.size = s.len.toNat →
      RelR (fun (p : Value × Mem) (v : Value) => p.1 = v ∧ UpToReads m₀ p.2)
        ((do Zig.checkIndex s j; loadAs f t (s.ptr.elem size j) al).run m) (Zig.index (arr.map enc) j) := by
    intro size al j m hj hsize
    have hidx : Zig.index (arr.map enc) j = throw .illegal := by
      unfold Zig.index; rw [dif_neg (by simp [hsize, hj])]
    rw [hidx]
    simp only [Zig.checkIndex, hj, ↓reduceIte, StateT.run_bind]
    rfl
  unfold Zig.readSlice at hread
  by_cases hL : s.len.toNat = 0
  · rw [if_pos hL] at hread
    simp only [StateT.run_pure] at hread
    cases hread
    have hsize : (#[] : Array α).size = s.len.toNat := by simp [hL]
    exact ⟨fun size al j m _ _ => hout size al j m (by omega) hsize, hsize, UpToReads.refl _⟩
  rw [if_neg hL] at hread
  by_cases hz : Enc.size α = 0
  · rw [if_pos hz] at hread
    simp only [StateT.run_bind, StateT.run_pure, pure_bind] at hread
    obtain ⟨rfl, hsize, _⟩ := mapM_range_ok _ _ _ _ _ hread
    refine ⟨fun size al j m hil _ => ?_, hsize, UpToReads.refl _⟩
    obtain ⟨rfl, hpos, _⟩ := hlay size al hil
    omega
  rw [if_neg hz] at hread
  simp only [StateT.run_bind] at hread
  obtain ⟨⟨bs, m'⟩, hlb, hmap⟩ := Result.bind_ok hread
  obtain ⟨b, blk, o, hacc, hrc, rfl, rfl⟩ := loadBytes_ok hlb
  obtain ⟨rfl, hsize, hdec⟩ := mapM_range_ok _ _ _ _ _ hmap
  refine ⟨?_, hsize, (UpToReads.refl m₀).withRead b o _⟩
  intro size al j m hil hm
  obtain ⟨rfl, hpos, hA, hal⟩ := hlay size al hil
  by_cases hj : j.toNat < s.len.toNat
  · have hj' : j.toNat < arr.size := by omega
    have hacc' : m.access (s.ptr.elem (Enc.size α) j) (Enc.size α) al = pure (b, blk, o + Enc.size α * j.toNat) := by
      rw [access_congr hm.blocks]
      exact access_item hacc hj hA hal
    have hjn : (j.toNat + 1) * Enc.size α ≤ s.len.toNat * Enc.size α := Nat.mul_le_mul_right _ hj
    have hrc' := raceCheck_sub hm hwf hrc
      (o' := o + Enc.size α * j.toNat) (n' := Enc.size α)
      ⟨Nat.le_add_right _ _, by rw [Nat.add_assoc, Nat.mul_comm (Enc.size α) j.toNat]; rw [Nat.add_mul, Nat.one_mul] at hjn; omega⟩
    have hd := hdec j.toNat hj'
    rw [Array.extract_extract] at hd
    have hmin : Min.min (o + (j.toNat + 1) * Enc.size α) (o + s.len.toNat * Enc.size α) =
        o + Enc.size α * j.toNat + Enc.size α := by
      rw [Nat.add_mul, Nat.one_mul] at hjn ⊢
      rw [Nat.mul_comm (Enc.size α)]
      generalize j.toNat * Enc.size α = P at hjn ⊢
      generalize s.len.toNat * Enc.size α = Q at hjn ⊢
      omega
    rw [hmin, Nat.mul_comm j.toNat] at hd
    have hidx : Zig.index (arr.map enc) j = pure (enc arr[j.toNat]) := by
      unfold Zig.index; rw [dif_pos (by simpa using hj')]; simp
    rw [hidx]
    simp only [Zig.checkIndex, hj, ↓reduceIte, StateT.run_bind, StateT.run_pure, pure_bind, hload,
      StateT.run_map, load_run hacc' hrc' hd]
    exact ⟨rfl, hm.withRead _ _ _⟩
  · exact hout _ _ j m hj hsize

end Air2Lean.Sem
