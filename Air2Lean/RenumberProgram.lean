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
These facts are proved invariant under every injective renaming here (`usesMemoryLocally_ren`,
`syncLocally_ren`, `callees_ren`, `calleesOf_ren`). The proof sees a renamed body as the
original one with `renInst` applied to each instruction (`allInsts_renFunc`), whose operation
has the original effects with every operand and target renamed (`effectsIn_renOp`), and every
lookup by instruction ID commutes with the renaming because it is injective (`find?_id_ren`).
Each memory analysis (`placeRoots`, `deadUndefStores`, `escapingAllocs`, ...) is the original
one renamed, from one lemma per named instruction test of `Memory.lean`.
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
  case optPayloadPtr set p | errPayloadPtr set p =>
    cases set <;> simp [renOp, renFlat, Op.effectsIn, renEffects, renControl, Effects.pure,
      Effects.address]
  case dbg name v =>
    cases v <;> simp [renOp, renFlat, Op.effectsIn, renEffects, renControl, Effects.pure]
  case switchBr v cs e | loopSwitchBr v cs e =>
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

/-! ## Memory

Renaming keeps `Func.usesMemoryLocally`: each analysis it reads is the original one renamed. -/

section Memory

theorem pointsToMem_ren (v : Val) : (renVal ρ v).pointsToMem = v.pointsToMem := by
  cases v with
  | optSome t w => simpa [renVal, Val.pointsToMem] using pointsToMem_ren w
  | errUnionOk t w => simpa [renVal, Val.pointsToMem] using pointsToMem_ren w
  | _ => simp [renVal, Val.pointsToMem]
termination_by sizeOf v
decreasing_by all_goals simp_wf; omega

theorem hasUndefExcept_ren (allowed : TyId → Bool) (v : Val) :
    (renVal ρ v).hasUndefExcept allowed = v.hasUndefExcept allowed := by
  cases v with
  | optSome t w => simpa [renVal, Val.hasUndefExcept] using hasUndefExcept_ren allowed w
  | errUnionOk t w => simpa [renVal, Val.hasUndefExcept] using hasUndefExcept_ren allowed w
  | _ => simp [renVal, Val.hasUndefExcept]
termination_by sizeOf v
decreasing_by all_goals simp_wf; omega

theorem hasNestedUndef_ren (v : Val) : (renVal ρ v).hasNestedUndef = v.hasNestedUndef := by
  have h := hasUndefExcept_ren (ρ := ρ) (fun _ => false) v
  cases v <;> simp_all [renVal, Val.hasNestedUndef]

theorem constTy?_ren (v : Val) : (renVal ρ v).constTy? = v.constTy? := by
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

theorem flattenInst_nil_ren (j : Inst) :
    flattenInst #[] (renInst ρ j) = (flattenInst #[] j).map (renInst ρ) := by
  simpa only [Array.map_empty] using flattenInst_ren (ρ := ρ) j #[]

theorem renFunc_body (f : Func) : (renFunc ρ f).body = f.body.map (renInst ρ) := renArr ρ f.body

theorem isInst_ren (hρ : Inj ρ) (a : InstId) (v : Val) : (renVal ρ v).isInst (ρ a) = v.isInst a := by
  cases v <;> simp only [renVal, Val.isInst, beq_ren hρ]

theorem instIn_ren (hρ : Inj ρ) (ids : Array InstId) (v : Val) :
    (renVal ρ v).instIn (ids.map ρ) = v.instIn ids := by
  cases v <;> simp only [renVal, Val.instIn, contains_ren hρ]

theorem isUndef_ren (v : Val) : (renVal ρ v).isUndef = v.isUndef := by
  cases v <;> rfl

theorem isAlloc_renOp (op : Op) : (renOp ρ op).isAlloc = op.isAlloc := by
  cases op <;> rfl

theorem isDbg_renOp (op : Op) : (renOp ρ op).isDbg = op.isDbg := by
  cases op <;> rfl

theorem isUndefStore_renOp (op : Op) : (renOp ρ op).isUndefStore = op.isUndefStore := by
  cases op <;> try rfl
  case store p v => cases v <;> rfl

theorem leavesBody_ren (hρ : Inj ρ) (j : Inst) : (renInst ρ j).leavesBody = j.leavesBody := by
  simp only [Inst.leavesBody, flattenInst_nil_ren, Array.any_map, Function.comp_def, renInst_op,
    renInst_id, effects_renOp, renEffects, renControl_jumpTarget, Option.any_map, beq_ren hρ]

theorem usesPlaceOf_ren (hρ : Inj ρ) (ps : Array InstId) (j : Inst) :
    (renInst ρ j).usesPlaceOf (ps.map ρ) = j.usesPlaceOf ps := by
  simp only [Inst.usesPlaceOf, flattenInst_nil_ren, Array.any_map, Function.comp_def, renInst_op,
    isDbg_renOp, placeOperands_renOp, instIn_ren hρ]

theorem overwritesLocal_ren (hρ : Inj ρ) (ps : Array InstId) (a : InstId) (j : Inst) :
    (renInst ρ j).overwritesLocal (ps.map ρ) (ρ a) = j.overwritesLocal ps a := by
  rcases j with ⟨id, ty, op⟩
  simp only [Inst.overwritesLocal, renInst_op]
  cases op <;> try rfl
  case store p v => simp only [renOp, renFlat, isInst_ren hρ, isUndef_ren, hasNestedUndef_ren]
  case asm source vol clobbers outputs inputs =>
    simp only [renOp, renFlat, Array.any_map, Function.comp_def, renAsm, Option.any_map,
      isInst_ren hρ, instIn_ren hρ]

/-- **Renaming keeps the dead `undefined` stores**, renamed. -/
theorem deadUndefStores_ren (hρ : Inj ρ) (f : Func) :
    deadUndefStores (renFunc ρ f) = (deadUndefStores f).map ρ := by
  simp only [deadUndefStores, allInsts_renFunc, placeRoots_ren hρ, renFunc_body, bodyLists_ren,
    Array.foldl_map]
  apply foldl_hom_nil
  intro body _ acc
  rw [← Array.map_zipIdx, Array.foldl_map]
  apply foldl_hom_mem
  intro ⟨i, k⟩ _ a
  rcases i with ⟨id, ty, op⟩
  dsimp only [Prod.map, id]
  simp only [renInst_op, renInst_id]
  cases op <;> try rfl
  case store p v =>
    cases p <;> cases v <;> try rfl
    case inst.undef x t =>
      simp only [renOp, renFlat, renVal, Array.any_map, Function.comp_def, renInst_id, renInst_op,
        beq_ren hρ, isAlloc_renOp, placesOf_ren hρ, Array.size_map, ← Array.map_extract,
        Array.find?_map, usesPlaceOf_ren hρ, leavesBody_ren hρ, Option.any_map,
        overwritesLocal_ren hρ, apply_ite (Array.map ρ), Array.map_push]

/-- **Renaming keeps the observable `undefined` stores' allocs**, renamed. -/
theorem undefAllocs_ren (hρ : Inj ρ) (f : Func) :
    undefAllocs (renFunc ρ f) = (undefAllocs f).map ρ := by
  simp only [undefAllocs, allInsts_renFunc, Array.any_map, Function.comp_def, renInst_op,
    isUndefStore_renOp, placeRoots_ren hρ, deadUndefStores_ren hρ, apply_ite (Array.map ρ),
    Array.map_empty, Array.foldl_map]
  congr 1
  apply foldl_hom_nil
  intro i _ acc
  rcases i with ⟨id, ty, op⟩
  simp only [renInst_op, renInst_id]
  cases op <;> try rfl
  case store p v =>
    cases p <;> cases v <;> try rfl
    case inst.undef x t =>
      simp only [renOp, renFlat, renVal, contains_ren hρ, apply_ite (Array.map ρ)]
      congr 1
      exact push_root_ren hρ _ acc x

theorem renFunc_types (f : Func) : (renFunc ρ f).types = f.types := rfl
theorem renFunc_layouts (f : Func) : (renFunc ρ f).layouts = f.layouts := rfl

theorem instPtrChild?_ren (hρ : Inj ρ) (types : Array Ty) (insts : Array Inst) (x : InstId) :
    instPtrChild? types (insts.map (renInst ρ)) (ρ x) = instPtrChild? types insts x := by
  simp only [instPtrChild?, find?_id_ren hρ]
  cases insts.find? (·.id == x) <;> simp

theorem byteLocalUseOk_ren (hρ : Inj ρ) (f : Func) (insts : Array Inst) (ps : Array InstId)
    (i : Inst) :
    byteLocalUseOk (renFunc ρ f) (insts.map (renInst ρ)) (ps.map ρ) (renInst ρ i) =
      byteLocalUseOk f insts ps i := by
  rcases i with ⟨id, ty, op⟩
  simp only [byteLocalUseOk, renInst_op, renInst_ty, placeOperands_renOp, Array.any_map,
    Function.comp_def, instIn_ren hρ]
  congr 1
  cases op <;> try rfl
  case load p => simp only [renOp, renFlat, instIn_ren hρ]
  case store p v => simp only [renOp, renFlat, instIn_ren hρ]
  case fieldPtr p n =>
    cases p <;> try rfl
    case inst b =>
      simp only [renOp, renFlat, renVal, Val.instIn, contains_ren hρ, instPtrChild?_ren hρ,
        renFunc_types, renFunc_layouts]

theorem byteLocalOk_ren (hρ : Inj ρ) (f : Func) (insts : Array Inst) (roots : Array (InstId × InstId))
    (a : InstId) :
    byteLocalOk (renFunc ρ f) (insts.map (renInst ρ)) (roots.map (ren2 ρ)) (ρ a) =
      byteLocalOk f insts roots a := by
  simp only [byteLocalOk, placesOf_ren hρ, Array.all_map, Function.comp_def, byteLocalUseOk_ren hρ,
    instPtrChild?_ren hρ, renFunc_types]

/-- **Renaming keeps the escaping allocs**, renamed. -/
theorem escapingAllocs_ren (hρ : Inj ρ) (f : Func) :
    escapingAllocs (renFunc ρ f) = (escapingAllocs f).map ρ := by
  simp only [escapingAllocs, allInsts_renFunc, placeRoots_ren hρ, usesEscapingAllocs_ren hρ,
    undefAllocs_ren hρ, Array.filter_map, Function.comp_def, contains_ren hρ, byteLocalOk_ren hρ,
    Array.map_append]

theorem isPtrFromInt_ren (hρ : Inj ρ) (f : Func) (insts : Array Inst) (i : Inst) :
    (renFunc ρ f).isPtrFromInt (insts.map (renInst ρ)) (renInst ρ i) = f.isPtrFromInt insts i := by
  rcases i with ⟨id, ty, op⟩
  simp only [Func.isPtrFromInt, renInst_op, renInst_ty]
  cases op <;> try rfl
  case bitcast s v =>
    cases v <;> try rfl
    case inst x =>
      simp only [renOp, renFlat, renVal, find?_id_ren hρ]
      cases insts.find? (·.id == x) <;> rfl

theorem usesMemoryAt_ren (hρ : Inj ρ) (f : Func) (insts : Array Inst) (i : Inst) :
    (renFunc ρ f).usesMemoryAt (insts.map (renInst ρ)) (renInst ρ i) = f.usesMemoryAt insts i := by
  (simp only [Func.usesMemoryAt, renInst_op, renInst_ty, memoryOp, effectsIn_renOp, effects_renOp,
    renEffects, isDeviceAsm_renOp, isMemAsm_renOp, valueOperands_renOp, ptrOperands_renOp,
    ← Array.map_append, Array.any_map, Function.comp_def, pointsToMem_ren, hasUndefExcept_ren,
    isPtrFromInt_ren hρ]) <;> rfl

/-- **Renaming keeps a function's local memory use** (`Func.usesMemoryLocally`). -/
theorem usesMemoryLocally_ren (hρ : Inj ρ) (f : Func) :
    (renFunc ρ f).usesMemoryLocally = f.usesMemoryLocally := by
  (simp only [Func.usesMemoryLocally, escapingAllocs_ren hρ, isEmpty_map, allInsts_renFunc,
    Array.any_map, Function.comp_def, usesMemoryAt_ren hρ]) <;> rfl

end Memory

/-! ## The whole program -/

/-- **The tick policies of a renamed program** are the original ones: every renaming keeps a
function's local memory, sync and callee facts (proved above). -/
theorem tickPolicy_renumber (p q : Prog) (σ : Func → InstId → InstId) (hσ : ∀ f, Inj (σ f))
    (hq : q.funcs = p.funcs.map fun f => renFunc (σ f) f) (hm : q.models = p.models) (name : String) :
    q.tickPolicy name = p.tickPolicy name :=
  tickPolicy_map p q _ hq hm (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun f => usesMemoryLocally_ren (hσ f) f) (fun f => syncLocally_ren (hσ f) f) (fun f refs => callees_ren (hσ f) f refs)
    (fun names refs f => calleesOf_ren (hσ f) names refs f) name

/-- **Renaming every function of a program preserves the program** (V02, Canon `renumber`):
`q` is `p` with each function `f` renamed by an injective `σ f`. -/
theorem run_renumber (p q : Prog) (σ : Func → InstId → InstId) (hσ : ∀ f, Inj (σ f))
    (hq : q.funcs = p.funcs.map fun f => renFunc (σ f) f) (hm : q.models = p.models) :
    run q = run p :=
  run_map p q _ hq (fun _ => rfl) (tickPolicy_renumber p q σ hσ hq hm) fun o ho f args => by
    rcases ho with rfl | rfl <;> exact execFunc_rename (hσ f) q (run_cellFree _) f args

/-- `run_renumber` for a certified subprogram's semantics. -/
theorem runOn_renumber (p q : Prog) (names : List String) (σ : Func → InstId → InstId)
    (hσ : ∀ f, Inj (σ f)) (hq : q.funcs = p.funcs.map fun f => renFunc (σ f) f)
    (hm : q.models = p.models) :
    runOn q names = runOn p names :=
  runOn_map p q names _ hq (fun _ => rfl) (tickPolicy_renumber p q σ hσ hq hm) fun o ho f args => by
    rcases ho with rfl | rfl <;> exact execFunc_rename (hσ f) q (runOn_cellFree _ names) f args

end Air2Lean.Renumber
