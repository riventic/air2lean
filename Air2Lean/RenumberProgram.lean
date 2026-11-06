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

/-! ## Memory -/

section Memory

theorem pointsToMem_ren (v : Val) : (renVal ρ v).pointsToMem = v.pointsToMem := by
  cases v with
  | optSome t w => simpa [renVal, Val.pointsToMem] using pointsToMem_ren w
  | errUnionOk t w => simpa [renVal, Val.pointsToMem] using pointsToMem_ren w
  | _ => simp [renVal, Val.pointsToMem]
termination_by sizeOf v
decreasing_by all_goals simp_wf; omega

theorem hasUndefExcept_ren (admit : TyId → Bool) (v : Val) :
    (renVal ρ v).hasUndefExcept admit = v.hasUndefExcept admit := by
  cases v with
  | optSome t w => simpa [renVal, Val.hasUndefExcept] using hasUndefExcept_ren admit w
  | errUnionOk t w => simpa [renVal, Val.hasUndefExcept] using hasUndefExcept_ren admit w
  | _ => simp [renVal, Val.hasUndefExcept]
termination_by sizeOf v
decreasing_by all_goals simp_wf; omega

theorem hasNestedUndef_ren (v : Val) : (renVal ρ v).hasNestedUndef = v.hasNestedUndef := by
  have h := hasUndefExcept_ren (ρ := ρ) (fun _ => false) v
  cases v <;> simp_all [renVal, Val.hasNestedUndef]

theorem constTy?_ren (v : Val) : (renVal ρ v).constTy? = v.constTy? := by
  cases v <;> rfl

theorem isUndef_ren (v : Val) : (renVal ρ v matches .undef _) = (v matches .undef _) := by
  cases v <;> rfl

theorem asmAllowEntry?_renOp (arch : String) (op : Op) :
    (renOp ρ op).asmAllowEntry? arch = op.asmAllowEntry? arch := by
  cases op <;> try rfl
  case asm source vol clobbers outputs inputs =>
    simp [renOp, renFlat, Op.asmAllowEntry?, asmConstraints, Array.map_map, Function.comp_def, renAsm]

theorem isDeviceAsm_renOp (arch : String) (op : Op) :
    (renOp ρ op).isDeviceAsm arch = op.isDeviceAsm arch := by
  cases op <;> try rfl
  case asm source vol clobbers outputs inputs =>
    have h := asmAllowEntry?_renOp (ρ := ρ) arch (.asm source vol clobbers outputs inputs)
    simp only [renOp, renFlat] at h ⊢
    simp only [Op.isDeviceAsm, h]

theorem isMemAsm_renOp (arch : String) (op : Op) : (renOp ρ op).isMemAsm arch = op.isMemAsm arch := by
  simp only [Op.isMemAsm, asmAllowEntry?_renOp]

theorem contains_ren (hρ : Inj ρ) (xs : Array InstId) (x : InstId) :
    (xs.map ρ).contains (ρ x) = xs.contains x := by
  simp only [Array.contains_map, beq_ren hρ]
  rfl

/-- `Array.foldl_hom` from the empty array, for a step that commutes with mapping `h` on the
members. -/
theorem foldl_hom_nil {α β γ : Type} (h : α → γ) (g₁ : Array α → β → Array α)
    (g₂ : Array γ → β → Array γ) (xs : Array β)
    (H : ∀ x ∈ xs, ∀ a, g₂ (a.map h) x = (g₁ a x).map h) :
    xs.foldl g₂ #[] = (xs.foldl g₁ #[]).map h := by
  have := foldl_hom_mem (Array.map h) g₁ g₂ xs #[] H
  simpa only [Array.map_empty] using this

/-- The renaming of an `(instruction, alloc)` pair. -/
abbrev ren2 (ρ : InstId → InstId) (p : InstId × InstId) : InstId × InstId := (ρ p.1, ρ p.2)

theorem find?_fst_ren (hρ : Inj ρ) (xs : Array (InstId × InstId)) (x : InstId) :
    (xs.map (ren2 ρ)).find? (·.1 == ρ x) = (xs.find? (·.1 == x)).map (ren2 ρ) := by
  have hp : ((fun y : InstId × InstId => y.1 == ρ x) ∘ ren2 ρ) = (fun y => y.1 == x) := by
    funext y
    simp only [Function.comp_def, ren2, beq_ren hρ]
  rw [Array.find?_map, hp]

theorem placeRoots_ren (hρ : Inj ρ) (insts : Array Inst) :
    placeRoots (insts.map (renInst ρ)) = (placeRoots insts).map (ren2 ρ) := by
  simp only [placeRoots, Array.foldl_map]
  apply foldl_hom_nil
  intro i hmem acc
  rcases i with ⟨id, ty, op⟩
  simp only [renInst_op, renInst_id]
  cases op
  case alloc => simp [renOp, renFlat, Array.map_push]
  case fieldPtr b n =>
    cases b
    case inst x =>
      simp only [renOp, renFlat, renVal, find?_fst_ren hρ]
      cases acc.find? (·.1 == x) <;> simp [Array.map_push]
    all_goals rfl
  case fieldParentPtr b n =>
    cases b
    case inst x =>
      simp only [renOp, renFlat, renVal, find?_fst_ren hρ]
      cases acc.find? (·.1 == x) <;> simp [Array.map_push]
    all_goals rfl
  case bitcast s b =>
    cases b
    case inst x =>
      simp only [renOp, renFlat, renVal, find?_fst_ren hρ]
      cases acc.find? (·.1 == x) <;> simp [Array.map_push]
    all_goals rfl
  case sliceFieldPtr l b =>
    cases b
    case inst x =>
      simp only [renOp, renFlat, renVal, find?_fst_ren hρ]
      cases acc.find? (·.1 == x) <;> simp [Array.map_push]
    all_goals rfl
  all_goals rfl

theorem placesOf_ren (hρ : Inj ρ) (roots : Array (InstId × InstId)) (a : InstId) :
    placesOf (roots.map (ren2 ρ)) (ρ a) = (placesOf roots a).map ρ := by
  simp only [placesOf, Array.filterMap_map, Array.map_filterMap]
  congr 1
  funext p
  simp only [Function.comp_def, ren2, beq_ren hρ]
  split <;> rfl

theorem placeOperands_renOp (op : Op) : placeOperands (renOp ρ op) = (placeOperands op).map (renVal ρ) := by
  simp only [placeOperands, effects_renOp, renEffects, Array.map_append]

theorem valueOperands_renOp (op : Op) : valueOperands (renOp ρ op) = (valueOperands op).map (renVal ρ) := by
  simp only [valueOperands, effects_renOp, renEffects]

theorem ptrOperands_renOp (op : Op) : ptrOperands (renOp ρ op) = (ptrOperands op).map (renVal ρ) := by
  simp only [ptrOperands, effects_renOp, renEffects]

/-- A fold over renamed operands that commutes with renaming its accumulator. -/
theorem foldl_ren_of (g₁ : Array InstId → Val → Array InstId) (g₂ : Array InstId → Val → Array InstId)
    (xs ys : Array Val) (acc : Array InstId) (hy : ys = xs.map (renVal ρ))
    (H : ∀ v a, g₂ (a.map ρ) (renVal ρ v) = (g₁ a v).map ρ) :
    ys.foldl g₂ (acc.map ρ) = (xs.foldl g₁ acc).map ρ := by
  subst hy
  rw [Array.foldl_map]
  exact Array.foldl_hom (Array.map ρ) (fun a v => H v a)

/-- Adding the root of an operand found by `roots.find?` commutes with renaming. -/
theorem push_root_ren (hρ : Inj ρ) (roots : Array (InstId × InstId)) (acc : Array InstId) (x : InstId) :
    (match ((roots.map (ren2 ρ)).find? (fun p : InstId × InstId => p.1 == ρ x)) with
      | some (_, r) => if (acc.map ρ).contains r then acc.map ρ else (acc.map ρ).push r
      | none => acc.map ρ) =
    (match roots.find? (fun p : InstId × InstId => p.1 == x) with
      | some (_, r) => if acc.contains r then acc else acc.push r
      | none => acc).map ρ := by
  rw [find?_fst_ren hρ]
  cases roots.find? (fun p : InstId × InstId => p.1 == x) with
  | none => rfl
  | some p =>
    obtain ⟨_, r⟩ := p
    simp only [Option.map_some, ren2, contains_ren hρ]
    split <;> simp [Array.map_push]

theorem usesEscapingAllocs_ren (hρ : Inj ρ) (f : Func) :
    usesEscapingAllocs (renFunc ρ f) = (usesEscapingAllocs f).map ρ := by
  simp only [usesEscapingAllocs, allInsts_renFunc, placeRoots_ren hρ, Array.foldl_map]
  apply foldl_hom_nil
  intro i hmem acc
  simp only [renInst_op, renInst_id, renInst_ty, valueOperands_renOp]
  refine foldl_ren_of _ _ _ _ acc ?_ ?_
  · rw [Array.map_append]
    congr 1
    rcases i with ⟨id, ty, op⟩
    cases op
    case store p v =>
      simp only [renOp, renFlat, hasNestedUndef_ren]
      cases v <;> cases p <;> simp [renVal, find?_id_ren hρ, Option.map_map, Function.comp_def, renFunc,
        Func.withBody, Option.bind_map, renInst_ty]
      all_goals (try split) <;> (try simp_all [renVal])
    case bitcast s v =>
      cases v
      case inst x =>
        simp only [renOp, renFlat, renVal, find?_id_ren hρ]
        cases f.allInsts.find? (·.id == x) <;> simp [renFunc, Func.withBody]
        all_goals (try split) <;> (try simp_all [renVal])
      all_goals simp [renOp, renFlat, renVal]
    all_goals simp [renOp, renFlat]
  · intro v a
    cases v
    case inst x => exact push_root_ren hρ _ a x
    all_goals rfl

theorem flatMap_congr_mem {α β : Type} {f g : α → Array β} :
    ∀ (xs : Array α), (∀ x ∈ xs, f x = g x) → xs.flatMap f = xs.flatMap g := by
  intro xs h
  rcases xs with ⟨l⟩
  simp only [List.mem_toArray] at h
  simp only [List.flatMap_toArray]
  congr 1
  induction l with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.flatMap_cons, h x (List.mem_cons_self ..),
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- `bodyLists` without `attach`. -/
theorem bodyLists_eq (b : Array Inst) :
    bodyLists b = #[b] ++ b.flatMap (fun i => i.op.effects.control.bodies.flatMap bodyLists) := by
  rw [bodyLists]
  congr 1
  rw [Array.flatMap_subtype (g := fun i => i.op.effects.control.bodies.flatMap bodyLists)
    (fun x _ => by
      dsimp only
      rw [Array.flatMap_subtype (g := bodyLists) (fun _ _ => rfl), Array.unattach_attach]),
    Array.unattach_attach]

theorem bodyLists_ren (b : Array Inst) :
    bodyLists (b.map (renInst ρ)) = (bodyLists b).map (·.map (renInst ρ)) := by
  rw [bodyLists_eq, bodyLists_eq, Array.map_append, Array.flatMap_map, Array.map_flatMap]
  congr 1
  · simp
  apply flatMap_congr_mem
  intro i hi
  simp only [renInst_op, effects_renOp, renEffects, renControl_bodies, Array.flatMap_map,
    Array.map_flatMap]
  apply flatMap_congr_mem
  intro n hn
  exact bodyLists_ren n
termination_by sizeOf b
decreasing_by
  have h1 := Array.sizeOf_lt_of_mem hi
  have h2 := Op.controlBody_size_lt i.op hn
  have h3 : sizeOf i.op < sizeOf i := by cases i; simp; omega
  omega

end Memory

end Air2Lean.Renumber
