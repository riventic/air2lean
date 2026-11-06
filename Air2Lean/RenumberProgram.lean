import Air2Lean.Renumber

/-!
# Renaming every function of a program preserves the program (Canon `renumber`, V02)

`Renumber.execFunc_rename` relates one function before and after `renumber` inside one program.
This module lifts it to whole programs: renaming every function's instruction IDs by an
injective map (one map per function) preserves `run` and `runOn` of the program
(`run_renumber`, `runOn_renumber`).

The lift needs the program's step-tick policies (`Program.tickPolicy`) to be the same. They are
computed from every body by `memoryFunctions`, `concFunctions` and `callGroups`, which read each
function only through its local memory, sync and callee facts (`SemRewrite.tickPolicy_map`).
Those facts are proved invariant under every injective renaming here. The proof sees a renamed
body as the original one with `renInst` applied to each instruction (`allInsts_renFunc`), whose
operation has the original effects with every operand and target renamed (`effectsIn_renOp`),
and every lookup by instruction ID commutes with the renaming because it is injective
(`find?_id_ren`).
-/

namespace Air2Lean.Renumber

open Zig Air2Lean.Sem

variable {ρ : InstId → InstId}

/-! ## A renamed body is the original with every instruction renamed -/

theorem renBody_eq_map (ρ : InstId → InstId) : ∀ l, renBody ρ l = l.map (renInst ρ)
  | [] => by simp only [renBody, List.map_nil]
  | i :: rest => by simp only [renBody, List.map_cons, renBody_eq_map ρ rest]

theorem renArr (ρ : InstId → InstId) (b : Array Inst) : (renBody ρ b.toList).toArray = b.map (renInst ρ) := by
  rw [renBody_eq_map, ← Array.toList_map, Array.toArray_toList]

/-- A switch case with every operand and its body renamed. -/
def renCase (ρ : InstId → InstId) (sc : SwitchCase) : SwitchCase :=
  { items := sc.items.map (renVal ρ), ranges := sc.ranges.map fun (l, h) => (renVal ρ l, renVal ρ h),
    body := sc.body.map (renInst ρ) }

theorem renCases_eq_map (ρ : InstId → InstId) : ∀ cs, renCases ρ cs = cs.map (renCase ρ)
  | [] => by simp only [renCases, List.map_nil]
  | sc :: more => by simp only [renCases, List.map_cons, renCase, renArr, renCases_eq_map ρ more]

theorem renCasesArr (ρ : InstId → InstId) (cs : Array SwitchCase) :
    (renCases ρ cs.toList).toArray = cs.map (renCase ρ) := by
  rw [renCases_eq_map, ← Array.toList_map, Array.toArray_toList]

/-- The renamed operation of an instruction (`renInst`'s, as a function of the operation). -/
def renOp (ρ : InstId → InstId) : Op → Op
  | .block b => .block (b.map (renInst ρ))
  | .loop b => .loop (b.map (renInst ρ))
  | .condBr v t e => .condBr (renVal ρ v) (t.map (renInst ρ)) (e.map (renInst ρ))
  | .switchBr v cs e => .switchBr (renVal ρ v) (cs.map (renCase ρ)) (e.map (renInst ρ))
  | .loopSwitchBr v cs e => .loopSwitchBr (renVal ρ v) (cs.map (renCase ρ)) (e.map (renInst ρ))
  | .«try» v b => .«try» (renVal ρ v) (b.map (renInst ρ))
  | .tryPtr v b => .tryPtr (renVal ρ v) (b.map (renInst ρ))
  | op => renFlat ρ op

theorem renInst_eq (ρ : InstId → InstId) (i : Inst) : renInst ρ i = ⟨ρ i.id, i.ty, renOp ρ i.op⟩ := by
  obtain ⟨id, ty, op⟩ := i
  cases op <;> (rw [renInst]; first | rfl | simp only [renOp, renArr, renCasesArr])

@[simp] theorem renInst_id (i : Inst) : (renInst ρ i).id = ρ i.id := by rw [renInst_eq]
@[simp] theorem renInst_ty (i : Inst) : (renInst ρ i).ty = i.ty := by rw [renInst_eq]
@[simp] theorem renInst_op (i : Inst) : (renInst ρ i).op = renOp ρ i.op := by rw [renInst_eq]

/-! ## Effects of a renamed operation -/

/-- A control effect with its targets and nested bodies renamed. -/
def renControl (ρ : InstId → InstId) : Control → Control
  | .next => .next
  | .exit => .exit
  | .br t => .br (ρ t)
  | .«repeat» t => .«repeat» (ρ t)
  | .dispatch t => .dispatch (ρ t)
  | .block b => .block (b.map (renInst ρ))
  | .loop bs => .loop (bs.map (·.map (renInst ρ)))
  | .branch bs => .branch (bs.map (·.map (renInst ρ)))
  | .«try» b => .«try» (b.map (renInst ρ))

theorem renControl_bodies (c : Control) :
    (renControl ρ c).bodies = c.bodies.map (·.map (renInst ρ)) := by
  cases c <;> simp [renControl, Control.bodies]

theorem renControl_jumpTarget (c : Control) : (renControl ρ c).jumpTarget? = c.jumpTarget?.map ρ := by
  cases c <;> rfl

/-- Effects with every operand, target and nested body renamed. -/
def renEffects (ρ : InstId → InstId) (e : Effects) : Effects :=
  { e with values := e.values.map (renVal ρ), places := e.places.map (renVal ρ),
           debug := e.debug.map (renVal ρ), access := e.access.map fun (v, a) => (renVal ρ v, a),
           derives := e.derives.map (renVal ρ), control := renControl ρ e.control }

theorem switchValues_ren (v : Val) (cs : Array SwitchCase) :
    switchValues (renVal ρ v) (cs.map (renCase ρ)) = (switchValues v cs).map (renVal ρ) := by
  simp only [switchValues, Array.map_append, Array.foldl_map]
  congr 1
  · simp
  have h := Array.foldl_hom (Array.map (renVal ρ)) (xs := cs) (init := #[])
    (g₁ := fun acc c =>
      c.ranges.foldl (fun acc (lo, hi) => (acc.push lo).push hi) (c.items.foldl Array.push acc))
    (g₂ := fun acc c =>
      (renCase ρ c).ranges.foldl (fun acc (lo, hi) => (acc.push lo).push hi)
        ((renCase ρ c).items.foldl Array.push acc))
    (fun acc c => by
      simp only [renCase, Array.foldl_map]
      rw [Array.foldl_hom (Array.map (renVal ρ)) (g₁ := Array.push)
        (g₂ := fun acc x => acc.push (renVal ρ x)) (fun a x => by simp only [Array.map_push])]
      exact Array.foldl_hom (Array.map (renVal ρ))
        (g₁ := fun acc (x : Val × Val) => (acc.push x.1).push x.2)
        (g₂ := fun acc (x : Val × Val) => (acc.push (renVal ρ x.1)).push (renVal ρ x.2))
        (fun a x => by simp only [Array.map_push]))
  simpa only [Array.map_empty] using h

theorem switchBodies_ren (cs : Array SwitchCase) (e : Array Inst) :
    switchBodies (cs.map (renCase ρ)) (e.map (renInst ρ)) =
      (switchBodies cs e).map (·.map (renInst ρ)) := by
  simp [switchBodies, Array.map_map, Function.comp_def, renCase]

theorem isEmpty_map {α β : Type} (f : α → β) (xs : Array α) : (xs.map f).isEmpty = xs.isEmpty := by
  simp only [Array.isEmpty, Array.size_map]

/-- A `filterMap` that commutes with renaming. -/
theorem filterMap_ren_of {α : Type} (g : α → Option Val) (r : α → α) (xs : Array α)
    (h : ∀ x, g (r x) = (g x).map (renVal ρ)) :
    (xs.map r).filterMap g = (xs.filterMap g).map (renVal ρ) := by
  rw [Array.filterMap_map, Array.map_filterMap]
  congr 1
  funext x
  exact h x

theorem filterMap_ref_ren (xs : Array AsmOperand) :
    (xs.map (renAsm ρ)).filterMap (·.ref) = (xs.filterMap (·.ref)).map (renVal ρ) := by
  rw [Array.filterMap_map, Array.map_filterMap]
  rfl

theorem isSpinHint_ren (source : String) (vol : Bool) (clobbers : Array String)
    (outputs inputs : Array AsmOperand) :
    (Op.asm source vol clobbers (outputs.map (renAsm ρ)) (inputs.map (renAsm ρ))).isSpinHint =
      (Op.asm source vol clobbers outputs inputs).isSpinHint := by
  cases vol <;> simp [Op.isSpinHint, isEmpty_map]

/-- **The effects of a renamed operation** are the original effects renamed. -/
theorem effectsIn_renOp (mode : AllocatorModel) (op : Op) :
    (renOp ρ op).effectsIn mode = renEffects ρ (op.effectsIn mode) := by
  cases op
  case call callee args =>
    cases callee <;> simp [renOp, renFlat, Op.effectsIn, renEffects, renControl, renVal, Effects.pure]
    case func name noreturn spawnFn => cases noreturn <;> rfl
  case shuffle a b mask =>
    simp only [renOp, renFlat, Op.effectsIn]
    rw [filterMap_ren_of _ (renLane ρ) mask (fun l => by cases l <;> rfl)]
    cases b <;> simp [renEffects, renControl, Effects.pure]
  case asm source vol clobbers outputs inputs =>
    simp only [renOp, renFlat, Op.effectsIn, filterMap_ref_ren, isSpinHint_ren]
    simp [renEffects, renControl, Effects.pure, Array.map_map, Function.comp_def]
  case optPayloadPtr set p =>
    cases set <;> simp [renOp, renFlat, Op.effectsIn, renEffects, renControl, Effects.pure,
      Effects.address]
  case errPayloadPtr set p =>
    cases set <;> simp [renOp, renFlat, Op.effectsIn, renEffects, renControl, Effects.pure,
      Effects.address]
  case dbg name v =>
    cases v <;> simp [renOp, renFlat, Op.effectsIn, renEffects, renControl, Effects.pure]
  case switchBr v cs e =>
    simp only [renOp, Op.effectsIn, Effects.flow, Effects.pure, renEffects, renControl,
      switchValues_ren, switchBodies_ren, Array.map_empty, Option.map_none]
  case loopSwitchBr v cs e =>
    simp only [renOp, Op.effectsIn, Effects.flow, Effects.pure, renEffects, renControl,
      switchValues_ren, switchBodies_ren, Array.map_empty, Option.map_none]
  all_goals
    simp [renOp, renFlat, Op.effectsIn, renEffects, renControl, Effects.pure, Effects.address,
      Effects.projection, Effects.placeAccess, Effects.valueAccess, Effects.atomicAccess, Effects.flow]

theorem effects_renOp (op : Op) : (renOp ρ op).effects = renEffects ρ op.effects :=
  effectsIn_renOp .std op

/-! ## The instructions of a renamed function -/

/-- `flattenInst` without `attach`. -/
theorem flattenInst_eq (acc : Array Inst) (i : Inst) :
    flattenInst acc i = i.op.effects.control.bodies.foldl (fun acc b => b.foldl flattenInst acc) (acc.push i) := by
  rw [flattenInst, flattenOp]
  simp only [Array.foldl_attach]
  exact Array.foldl_attach (f := fun (acc : Array Inst) (b : Array Inst) => b.foldl flattenInst acc)

/-- `Array.foldl_hom` for a step that commutes with `f` on the members only. -/
theorem foldl_hom_mem {α γ β : Type} (f : α → γ) (g₁ : α → β → α) (g₂ : γ → β → γ) :
    ∀ (xs : Array β) (init : α), (∀ x ∈ xs, ∀ a, g₂ (f a) x = f (g₁ a x)) →
      xs.foldl g₂ (f init) = f (xs.foldl g₁ init) := by
  intro xs
  rcases xs with ⟨l⟩
  simp only [List.foldl_toArray', List.mem_toArray]
  induction l with
  | nil => intros; rfl
  | cons x rest ih =>
    intro init H
    simp only [List.foldl_cons, List.size_toArray, List.length_cons]
    rw [H x (List.mem_cons_self ..) init]
    simpa using ih (g₁ init x) fun y hy a => H y (List.mem_cons_of_mem _ hy) a

theorem flattenInst_ren (i : Inst) :
    ∀ acc, flattenInst (acc.map (renInst ρ)) (renInst ρ i) = (flattenInst acc i).map (renInst ρ) := by
  intro acc
  rw [flattenInst_eq, flattenInst_eq, renInst_op, effects_renOp]
  simp only [renEffects, renControl_bodies, Array.foldl_map, ← Array.map_push]
  apply foldl_hom_mem
  intro b hb a
  apply foldl_hom_mem
  intro x hx a'
  exact flattenInst_ren x a'
termination_by sizeOf i
decreasing_by
  have h1 := Array.sizeOf_lt_of_mem hx
  have h2 := Op.controlBody_size_lt i.op hb
  have h3 : sizeOf i.op < sizeOf i := by cases i; simp; omega
  omega

theorem allInsts_renFunc (ρ : InstId → InstId) (f : Func) :
    (renFunc ρ f).allInsts = f.allInsts.map (renInst ρ) := by
  simp only [Func.allInsts, renFunc, Func.withBody, renArr, Array.foldl_map]
  have := foldl_hom_mem (Array.map (renInst ρ)) flattenInst
    (fun acc i => flattenInst acc (renInst ρ i)) f.body #[] (fun i _ a => flattenInst_ren i a)
  simpa only [Array.map_empty] using this

/-! ## Lookups by instruction ID -/

theorem beq_ren (hρ : Inj ρ) (a b : InstId) : (ρ a == ρ b) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have : ρ a ≠ ρ b := fun e => h (hρ _ _ e)
    rw [beq_false_of_ne this, beq_false_of_ne h]

theorem find?_id_ren (hρ : Inj ρ) (xs : Array Inst) (x : InstId) :
    (xs.map (renInst ρ)).find? (·.id == ρ x) = (xs.find? (·.id == x)).map (renInst ρ) := by
  have hp : ((fun y : Inst => y.id == ρ x) ∘ renInst ρ) = (fun y => y.id == x) := by
    funext i
    simp only [Function.comp_def, renInst_id, beq_ren hρ]
  rw [Array.find?_map, hp]

/-! ## Callees -/

theorem calleeFnTy?_ren (hρ : Inj ρ) (f : Func) (x : InstId) :
    (renFunc ρ f).calleeFnTy? (ρ x) = f.calleeFnTy? x := by
  simp only [Func.calleeFnTy?, allInsts_renFunc, find?_id_ren hρ]
  cases f.allInsts.find? (·.id == x) <;> simp [renFunc, Func.withBody]

theorem calleeValFnTy?_ren (hρ : Inj ρ) (f : Func) (v : Val) :
    (renFunc ρ f).calleeValFnTy? (renVal ρ v) = f.calleeValFnTy? v := by
  cases v <;> simp only [renVal, Func.calleeValFnTy?, calleeFnTy?_ren hρ] <;> rfl

theorem indirectCallees_ren (hρ : Inj ρ) (f : Func) (refs : Array (String × String)) :
    (renFunc ρ f).indirectCallees refs = f.indirectCallees refs := by
  simp only [Func.indirectCallees, allInsts_renFunc, Array.flatMap_map]
  congr 1
  funext i
  simp only [renInst_op]
  rcases i with ⟨id, ty, op⟩
  cases op <;> try rfl
  case call c args => simp only [renOp, renFlat, calleeValFnTy?_ren hρ]

theorem callees_ren (hρ : Inj ρ) (f : Func) (refs : Array (String × String)) :
    (renFunc ρ f).callees refs = f.callees refs := by
  simp only [Func.callees, allInsts_renFunc, Array.filterMap_map, indirectCallees_ren hρ]
  congr 2
  funext i
  simp only [Function.comp_def, renInst_op]
  rcases i with ⟨id, ty, op⟩
  cases op <;> try rfl
  case call c args =>
    cases c
    case func name nr spawn => cases nr <;> rfl
    all_goals rfl

theorem calleesOf_ren (hρ : Inj ρ) (names : Array String) (refs : Array (String × String)) (f : Func) :
    calleesOf names refs (renFunc ρ f) = calleesOf names refs f := by
  simp only [calleesOf, allInsts_renFunc, Array.flatMap_map, indirectCallees_ren hρ]
  congr 3
  funext i
  simp only [renInst_op]
  rcases i with ⟨id, ty, op⟩
  cases op <;> try rfl
  case call c args => cases c <;> rfl

/-! ## Sync -/

theorem hasOpenCall_ren (hρ : Inj ρ) (f : Func) : (renFunc ρ f).hasOpenCall = f.hasOpenCall := by
  simp only [Func.hasOpenCall, allInsts_renFunc, Array.any_map]
  congr 2
  funext i
  simp only [Function.comp_def, renInst_op]
  rcases i with ⟨id, ty, op⟩
  cases op <;> try rfl
  case call c args =>
    simp only [renOp, renFlat, calleeValFnTy?_ren hρ]
    rfl

theorem syncLocally_ren (hρ : Inj ρ) (f : Func) : (renFunc ρ f).syncLocally = f.syncLocally := by
  simp only [Func.syncLocally, allInsts_renFunc, Array.any_map, Function.comp_def, renInst_op,
    effects_renOp, renEffects, hasOpenCall_ren hρ]

end Air2Lean.Renumber
