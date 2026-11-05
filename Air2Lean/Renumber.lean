import Air2Lean.Sem

/-!
# Renaming instruction IDs preserves the AIR interpreter (Canon `renumber`, V02)

`Raw.renumber` gives every instruction a new ID and renames every operand, branch target and
nested body with it. `execFunc_rename` proves once, for every function, every injective
renaming `ρ`, every argument list and the full memory, that the renamed function has the same
execution as the original, under every call oracle that does not leak register-cell names
(`Oracle.CellFree`). The program's own least-fixpoint oracles (`run`, `runOn`) satisfy it
(`run_cellFree`, `runOn_cellFree`), so `runOn_rename` lifts the theorem to whole programs.

The contract is needed: an arbitrary oracle can return the value `.cell k`, the name of a
caller's register local, and renaming moves that local
(`tests/roadmap/air-semantics/RenumberOracle.lean`). It is not a premise about Zig: a callee
cannot name a caller's register local, and the semantics' own oracles never do.

The proof is a simulation. The renamed run's frame and SSA environment are the original ones
with every cell name mapped by `ρ` (`renFrame`, `renEnv`); a register local's address only
reaches `load` and `store` (`regAlloc`), so every other operand holds a value without cell
names (`InvEnv`), and both runs compute the same values. This is a statement about the
definitional semantics (SEM-06), not a new judgment or proof rule.
-/

namespace Air2Lean.Renumber

open Zig Air2Lean.Sem

/-! ## The renaming -/

/-- An injective renaming of instruction IDs. -/
def Inj (ρ : InstId → InstId) : Prop := ∀ a b, ρ a = ρ b → a = b

/-- An operand with its instruction reference renamed. `Raw.validateRefs` rejects an instruction
reference nested in a constant, so `Raw.renumber` renames only top-level references; renaming the
nested ones `clearOf` inspects too keeps the theorem free of that side condition. -/
def renVal (ρ : InstId → InstId) : Val → Val
  | .inst id => .inst (ρ id)
  | .optSome t v => .optSome t (renVal ρ v)
  | .errUnionOk t v => .errUnionOk t (renVal ρ v)
  | v => v

def renAsm (ρ : InstId → InstId) (o : AsmOperand) : AsmOperand := { o with ref := o.ref.map (renVal ρ) }

/-- Every operand and branch target of an operation renamed; the operations with nested bodies
are `renInst`'s. -/
def renFlat (ρ : InstId → InstId) : Op → Op
  | .arith op m a b => .arith op m (renVal ρ a) (renVal ρ b)
  | .div op a b => .div op (renVal ρ a) (renVal ρ b)
  | .divFloat a b => .divFloat (renVal ρ a) (renVal ρ b)
  | .minMax x a b => .minMax x (renVal ρ a) (renVal ρ b)
  | .withOverflow op a b => .withOverflow op (renVal ρ a) (renVal ρ b)
  | .shlWithOverflow a b => .shlWithOverflow (renVal ρ a) (renVal ρ b)
  | .countBits op a => .countBits op (renVal ρ a)
  | .permuteBits op a => .permuteBits op (renVal ρ a)
  | .splat a => .splat (renVal ρ a)
  | .select p a b => .select (renVal ρ p) (renVal ρ a) (renVal ρ b)
  | .reduce op a => .reduce op (renVal ρ a)
  | .shuffle a b mask => .shuffle (renVal ρ a) (b.map (renVal ρ)) mask
  | .bit op a b => .bit op (renVal ρ a) (renVal ρ b)
  | .not a => .not (renVal ρ a)
  | .neg a => .neg (renVal ρ a)
  | .abs a => .abs (renVal ρ a)
  | .shift op a b => .shift op (renVal ρ a) (renVal ρ b)
  | .cmp op a b => .cmp op (renVal ρ a) (renVal ρ b)
  | .boolAnd a b => .boolAnd (renVal ρ a) (renVal ρ b)
  | .boolOr a b => .boolOr (renVal ρ a) (renVal ρ b)
  | .intCast s a => .intCast s (renVal ρ a)
  | .trunc a => .trunc (renVal ρ a)
  | .bitcast s a => .bitcast s (renVal ρ a)
  | .floatRound op a => .floatRound op (renVal ρ a)
  | .sqrt a => .sqrt (renVal ρ a)
  | .libm op a => .libm op (renVal ρ a)
  | .mulAdd a b c => .mulAdd (renVal ρ a) (renVal ρ b) (renVal ρ c)
  | .floatConv a => .floatConv (renVal ρ a)
  | .floatFromInt a => .floatFromInt (renVal ρ a)
  | .intFromFloat s a => .intFromFloat s (renVal ρ a)
  | .isNull a => .isNull (renVal ρ a)
  | .isNonNull a => .isNonNull (renVal ρ a)
  | .optPayload a => .optPayload (renVal ρ a)
  | .wrapOptional a => .wrapOptional (renVal ρ a)
  | .isNullPtr x p => .isNullPtr x (renVal ρ p)
  | .optPayloadPtr x p => .optPayloadPtr x (renVal ρ p)
  | .isErrPtr x p => .isErrPtr x (renVal ρ p)
  | .errPayloadPtr x p => .errPayloadPtr x (renVal ρ p)
  | .errCodePtr p => .errCodePtr (renVal ρ p)
  | .isErr a => .isErr (renVal ρ a)
  | .isNonErr a => .isNonErr (renVal ρ a)
  | .errPayload a => .errPayload (renVal ρ a)
  | .errCode a => .errCode (renVal ρ a)
  | .wrapErrPayload a => .wrapErrPayload (renVal ρ a)
  | .wrapErr a => .wrapErr (renVal ρ a)
  | .isNamedEnum a => .isNamedEnum (renVal ρ a)
  | .unionTag a => .unionTag (renVal ρ a)
  | .unionInit n a => .unionInit n (renVal ρ a)
  | .fieldPtr b n => .fieldPtr (renVal ρ b) n
  | .fieldParentPtr p n => .fieldParentPtr (renVal ρ p) n
  | .setUnionTag p t => .setUnionTag (renVal ρ p) (renVal ρ t)
  | .retLoad p => .retLoad (renVal ρ p)
  | .load p => .load (renVal ρ p)
  | .store p v => .store (renVal ρ p) (renVal ρ v)
  | .atomicLoad p o => .atomicLoad (renVal ρ p) o
  | .atomicStore p v o => .atomicStore (renVal ρ p) (renVal ρ v) o
  | .atomicRmw op o p v => .atomicRmw op o (renVal ρ p) (renVal ρ v)
  | .cmpxchg w p e n s fl => .cmpxchg w (renVal ρ p) (renVal ρ e) (renVal ρ n) s fl
  | .sliceLen s => .sliceLen (renVal ρ s)
  | .sliceElemVal s i => .sliceElemVal (renVal ρ s) (renVal ρ i)
  | .ptrAdd s p n => .ptrAdd s (renVal ρ p) (renVal ρ n)
  | .elemPtr p i => .elemPtr (renVal ρ p) (renVal ρ i)
  | .ptrElemVal p i => .ptrElemVal (renVal ρ p) (renVal ρ i)
  | .arrayElemVal a i => .arrayElemVal (renVal ρ a) (renVal ρ i)
  | .slice p l => .slice (renVal ρ p) (renVal ρ l)
  | .slicePtr s => .slicePtr (renVal ρ s)
  | .arrayToSlice p => .arrayToSlice (renVal ρ p)
  | .sliceFieldPtr l p => .sliceFieldPtr l (renVal ρ p)
  | .memset d v => .memset (renVal ρ d) (renVal ρ v)
  | .memcpy m d s => .memcpy m (renVal ρ d) (renVal ρ s)
  | .tagName a => .tagName (renVal ρ a)
  | .errorName a => .errorName (renVal ρ a)
  | .errorsLenLe a => .errorsLenLe (renVal ρ a)
  | .vectorStoreElem p i v => .vectorStoreElem (renVal ρ p) (renVal ρ i) (renVal ρ v)
  | .structFieldVal s n => .structFieldVal (renVal ρ s) n
  | .aggregateInit es => .aggregateInit (es.map (renVal ρ))
  | .call c args => .call (renVal ρ c) (args.map (renVal ρ))
  | .br t v => .br (ρ t) (renVal ρ v)
  | .«repeat» t => .«repeat» (ρ t)
  | .switchDispatch t s => .switchDispatch (ρ t) (renVal ρ s)
  | .ret v => .ret (renVal ρ v)
  | .dbg n v => .dbg n (v.map (renVal ρ))
  | .asm src vol cl outs ins => .asm src vol cl (outs.map (renAsm ρ)) (ins.map (renAsm ρ))
  | op => op

mutual

/-- A body with every instruction ID, operand and branch target renamed, nested bodies
included. -/
def renBody (ρ : InstId → InstId) : List Inst → List Inst
  | [] => []
  | i :: rest => renInst ρ i :: renBody ρ rest
termination_by l => (sizeOf l, 0)

def renInst (ρ : InstId → InstId) (i : Inst) : Inst :=
  let op := match _h : i.op with
    | .block b => .block (renBody ρ b.toList).toArray
    | .loop b => .loop (renBody ρ b.toList).toArray
    | .condBr v t e => .condBr (renVal ρ v) (renBody ρ t.toList).toArray (renBody ρ e.toList).toArray
    | .switchBr v cs e =>
      .switchBr (renVal ρ v) (renCases ρ cs.toList).toArray (renBody ρ e.toList).toArray
    | .loopSwitchBr v cs e =>
      .loopSwitchBr (renVal ρ v) (renCases ρ cs.toList).toArray (renBody ρ e.toList).toArray
    | .«try» v b => .«try» (renVal ρ v) (renBody ρ b.toList).toArray
    | .tryPtr v b => .tryPtr (renVal ρ v) (renBody ρ b.toList).toArray
    | op => renFlat ρ op
  { id := ρ i.id, ty := i.ty, op }
termination_by (sizeOf i, 1)
decreasing_by
  all_goals
    obtain ⟨id, ty, op⟩ := i
    simp only at _h
    subst _h
    simp_wf
    try simp only [sizeOf_toList]
    omega

def renCases (ρ : InstId → InstId) : List SwitchCase → List SwitchCase
  | [] => []
  | sc :: more =>
    { items := sc.items.map (renVal ρ), ranges := sc.ranges.map fun (l, h) => (renVal ρ l, renVal ρ h),
      body := (renBody ρ sc.body.toList).toArray } :: renCases ρ more
termination_by cs => (sizeOf cs, 0)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [sizeOf_toList]
  all_goals (try have := sizeOf_case_body sc); omega

end

/-- `f` with its body renamed. -/
def renFunc (ρ : InstId → InstId) (f : Func) : Func :=
  { f with body := (renBody ρ f.body.toList).toArray }

/-! ## Register-cell names in values -/

/-- A value with every register-cell name renamed. -/
def renV (ρ : InstId → InstId) : Value → Value
  | .cell k => .cell (ρ k)
  | .optSome v => .optSome (renV ρ v)
  | .errOk v => .errOk (renV ρ v)
  | v => v

/-- A value that names no register cell. -/
def cellFree : Value → Bool
  | .cell _ => false
  | .optSome v | .errOk v => cellFree v
  | _ => true

theorem renV_of_cellFree (ρ : InstId → InstId) : ∀ {v : Value}, cellFree v = true → renV ρ v = v
  | .cell _, h => by simp [cellFree] at h
  | .optSome v, h => by simp only [cellFree] at h; simp only [renV, renV_of_cellFree ρ h]
  | .errOk v, h => by simp only [cellFree] at h; simp only [renV, renV_of_cellFree ρ h]
  | .int .., _ | .bool _, _ | .void, _ | .ptr _, _ | .slice _, _ | .optNone, _ | .errErr _, _
  | .errName _, _ => rfl

theorem cellFree_of_valOk : ∀ (t : Ty) (v : Value), valOk t v = true → cellFree v = true := by
  intro t v h
  cases v <;> first | rfl | (cases t <;> simp [valOk] at h)

theorem cellFree_of_valOkIn (f : Func) : ∀ n t v, valOkIn f n t v = true → cellFree v = true := by
  intro n
  induction n with
  | zero => intro t v h; simp [valOkIn] at h
  | succ n ih =>
    intro t v h
    simp only [valOkIn] at h
    split at h
    · rfl
    · simp only [Bool.and_eq_true] at h; simp only [cellFree]; exact ih _ _ h.2
    · simp only [cellFree]; exact ih _ _ h
    · rfl
    · rfl
    · exact cellFree_of_valOk _ _ h
    · simp at h

theorem cellFree_of_argsOk (f : Func) : ∀ ts args, argsOk f ts args = true → args.all cellFree = true
  | [], [], _ => rfl
  | t :: ts, v :: vs, h => by
    simp only [argsOk, Bool.and_eq_true] at h
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨cellFree_of_valOkIn f _ _ _ h.1, cellFree_of_argsOk f ts vs h.2⟩
  | [], _ :: _, h | _ :: _, [], h => by simp [argsOk] at h

/-! ## Results without cell names -/

/-- Every value `x` returns names no register cell. -/
def ROk {α : Type} (P : α → Prop) (x : Result α) : Prop := ∀ a, x.run = some (.ok a) → P a

/-- Every value `x` returns, from any memory, names no register cell. -/
def MOk {α : Type} (P : α → Prop) (x : MemM α) : Prop := ∀ m r, (x.run m).run = some (.ok r) → P r.1

/-- The oracle contract: on arguments without register-cell names, a call's value names no
register cell either. The semantics' own oracles satisfy it (`run_cellFree`); it is what an
external call model must also satisfy for `execFunc_rename` to apply to it. -/
def Oracle.CellFree (o : Oracle) : Prop :=
  ∀ name vs, vs.all cellFree = true → MOk (fun v => cellFree v = true) (o name vs)

/-- An exit's value names no register cell. -/
def exitFree : Exit → Prop
  | .br _ v | .ret v => cellFree v = true
  | .rep _ => True

/-- An exit with its target and its value's cell names renamed. -/
def renExit (ρ : InstId → InstId) : Exit → Exit
  | .br t v => .br (ρ t) (renV ρ v)
  | .rep t => .rep (ρ t)
  | .ret v => .ret (renV ρ v)

/-! ## The renamed run's frame and environment -/

open Classical in
/-- The frame of the renamed run: the cell of `ρ k` is the original cell `k`. -/
noncomputable def renFrame (ρ : InstId → InstId) (fr : Frame) : Frame :=
  { blocks := fr.blocks, cells := fun x => if h : ∃ k, ρ k = x then fr.cells h.choose else none }

open Classical in
/-- The SSA environment of the renamed run: `ρ j` holds `j`'s value, cell names renamed. -/
noncomputable def renEnv (ρ : InstId → InstId) (env : Env) : Env := fun x =>
  if h : ∃ j, ρ j = x then (env h.choose).map fun p => (p.1, renV ρ p.2) else none

/-- `env` with its values' cell names renamed (`renEnv` before the renaming of its IDs). -/
def renVals (ρ : InstId → InstId) (env : Env) : Env := fun j => (env j).map fun p => (p.1, renV ρ p.2)

section
variable {ρ : InstId → InstId} (hρ : Inj ρ)
include hρ

theorem choose_eq {k : InstId} (h : ∃ j, ρ j = ρ k) : h.choose = k := hρ _ _ h.choose_spec

theorem renFrame_cells (fr : Frame) (k : InstId) : (renFrame ρ fr).cells (ρ k) = fr.cells k := by
  simp only [renFrame, dif_pos (⟨k, rfl⟩ : ∃ j, ρ j = ρ k), choose_eq hρ]

theorem renFrame_setCell (fr : Frame) (k : InstId) (v : Option Value) :
    renFrame ρ (fr.setCell k v) = (renFrame ρ fr).setCell (ρ k) v := by
  simp only [renFrame, Frame.setCell, Frame.mk.injEq, true_and]
  funext x
  by_cases h : ∃ j, ρ j = x
  · obtain ⟨j, rfl⟩ := h
    simp only [dif_pos (⟨j, rfl⟩ : ∃ i, ρ i = ρ j), choose_eq hρ]
    by_cases hj : j = k
    · subst hj; simp
    · have : ρ j ≠ ρ k := fun e => hj (hρ _ _ e)
      simp [hj, this, dif_pos (⟨j, rfl⟩ : ∃ i, ρ i = ρ j), choose_eq hρ]
  · have hx : x ≠ ρ k := fun e => h ⟨k, e.symm⟩
    simp [dif_neg h, hx]

theorem renEnv_apply (env : Env) (j : InstId) :
    renEnv ρ env (ρ j) = (env j).map fun p => (p.1, renV ρ p.2) := by
  simp only [renEnv, dif_pos (⟨j, rfl⟩ : ∃ i, ρ i = ρ j), choose_eq hρ]

theorem renEnv_comp (env : Env) : (fun j => renEnv ρ env (ρ j)) = renVals ρ env := by
  funext j; exact renEnv_apply hρ env j

theorem renEnv_set (env : Env) (j : InstId) (t : TyId) (v : Value) :
    renEnv ρ (env.set j t v) = (renEnv ρ env).set (ρ j) t (renV ρ v) := by
  funext x
  simp only [renEnv, Env.set]
  by_cases h : ∃ i, ρ i = x
  · obtain ⟨i, rfl⟩ := h
    simp only [dif_pos (⟨i, rfl⟩ : ∃ k, ρ k = ρ i), choose_eq hρ]
    by_cases hi : i = j
    · subst hi; simp
    · have : ρ i ≠ ρ j := fun e => hi (hρ _ _ e)
      simp [hi, this, dif_pos (⟨i, rfl⟩ : ∃ k, ρ k = ρ i), choose_eq hρ]
  · have hx : x ≠ ρ j := fun e => h ⟨j, e.symm⟩
    simp [dif_neg h, hx]

end

theorem renFrame_empty (ρ : InstId → InstId) : renFrame ρ {} = {} := by
  simp only [renFrame]; congr; funext x; split <;> rfl

theorem renEnv_empty (ρ : InstId → InstId) : renEnv ρ (fun _ => none) = fun _ => none := by
  funext x; simp only [renEnv]; split <;> rfl

theorem renFrame_blocks (ρ : InstId → InstId) (fr : Frame) (b : List Zig.Ptr) :
    renFrame ρ { fr with blocks := b } = { renFrame ρ fr with blocks := b } := rfl

/-! ## Register locals are renamed with their allocations -/

theorem clearOf_ren {ρ : InstId → InstId} (hρ : Inj ρ) (a : InstId) :
    ∀ v : Val, clearOf (ρ a) (renVal ρ v) = clearOf a v
  | .inst b => by
    have e : (ρ b == ρ a) = (b == a) := by
      by_cases h : b = a
      · simp [h]
      · have : ρ b ≠ ρ a := fun e => h (hρ _ _ e)
        rw [beq_false_of_ne this, beq_false_of_ne h]
    simp only [renVal, clearOf, bne, e]
  | .optSome _ v | .errUnionOk _ v => by simp only [renVal, clearOf, clearOf_ren hρ a v]
  | .int .. | .float .. | .bool _ | .void | .undef _ | .func .. | .optNull _ | .err .. | .errUnionErr ..
  | .enumTag .. | .unionVal .. | .agg .. | .ptrConst .. | .ptrNull _ | .ptrOther .. | .ptrInt ..
  | .sliceConst .. => rfl

theorem renCases_all {ρ : InstId → InstId} (cs : List SwitchCase)
    (p : Array Val → Array (Val × Val) → Bool) :
    (renCases ρ cs).all (fun sc => p sc.items sc.ranges) =
      cs.all (fun sc => p (sc.items.map (renVal ρ)) (sc.ranges.map fun (l, h) => (renVal ρ l, renVal ρ h))) := by
  induction cs with
  | nil => simp only [renCases, List.all_nil]
  | cons sc more ih => simp only [renCases, List.all_cons, ih]

mutual

theorem regBody_ren {ρ : InstId → InstId} (hρ : Inj ρ) (a : InstId) (l : List Inst) :
    regBody (ρ a) (renBody ρ l) = regBody a l := by
  cases l with
  | nil => simp only [renBody, regBody]
  | cons i rest =>
    rw [renBody, regBody, regBody, regInst_ren hρ a i, regBody_ren hρ a rest]
termination_by (sizeOf l, 0)
decreasing_by all_goals simp_wf; omega

theorem regInst_ren {ρ : InstId → InstId} (hρ : Inj ρ) (a : InstId) (i : Inst) :
    regInst (ρ a) (renInst ρ i) = regInst a i := by
  obtain ⟨id, ty, op⟩ := i
  cases op <;> simp [renInst, renFlat, regInst, regUse, clearOf_ren hρ, List.all_map,
    Function.comp_def]
  case block b => exact regBody_ren hρ a b.toList
  case loop b => exact regBody_ren hρ a b.toList
  case condBr v t e => rw [regBody_ren hρ a t.toList, regBody_ren hρ a e.toList]
  case switchBr v cs e =>
    rw [regCases_ren hρ a cs.toList, regBody_ren hρ a e.toList,
      renCases_all cs.toList (fun items ranges =>
        items.all (clearOf (ρ a) ·) && ranges.all (fun x => clearOf (ρ a) x.1 && clearOf (ρ a) x.2))]
    simp [List.all_map, Function.comp_def, clearOf_ren hρ, Array.all_toList]
  case «try» v b => rw [regBody_ren hρ a b.toList]
termination_by (sizeOf i, 1)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [sizeOf_toList]
  all_goals omega

theorem regCases_ren {ρ : InstId → InstId} (hρ : Inj ρ) (a : InstId) (cs : List SwitchCase) :
    regCases (ρ a) (renCases ρ cs) = regCases a cs := by
  cases cs with
  | nil => simp only [renCases, regCases]
  | cons sc more =>
    rw [renCases, regCases, regCases, List.toList_toArray,
      regBody_ren hρ a sc.body.toList, regCases_ren hρ a more]
termination_by (sizeOf cs, 0)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [sizeOf_toList]
  all_goals (try have := sizeOf_case_body sc); omega

end

theorem regAlloc_ren {ρ : InstId → InstId} (hρ : Inj ρ) (f : Func) (a : InstId) :
    regAlloc (renFunc ρ f) (ρ a) = regAlloc f a := by
  simp only [regAlloc, renFunc, List.toList_toArray, regBody_ren hρ]

/-! ## Operands -/

theorem constVal_ren (ρ : InstId → InstId) (f : Func) (v : Val) :
    constVal f (renVal ρ v) = constVal f v := by
  cases v <;> rfl

theorem operand_ren {ρ : InstId → InstId} (hρ : Inj ρ) (f : Func) (env : Env) (v : Val) :
    operand f (renEnv ρ env) (renVal ρ v) = operand f (renVals ρ env) v := by
  cases v <;> simp only [renVal, operand, renEnv_apply hρ, renVals, constVal_ren]

theorem operandTy_ren {ρ : InstId → InstId} (hρ : Inj ρ) (env : Env) (v : Val) :
    operandTy (renEnv ρ env) (renVal ρ v) = operandTy env v := by
  cases v <;> simp [renVal, operandTy, renEnv_apply hρ, Option.map_map, Function.comp_def, Val.constTy?]

theorem operandTy_renVals (ρ : InstId → InstId) (env : Env) (v : Val) :
    operandTy (renVals ρ env) v = operandTy env v := by
  cases v <;> simp [operandTy, renVals, Option.map_map, Function.comp_def]

/-- The top-level operands that `evalPure`, `evalMem` and `execInst` read. -/
def topVals : Op → List Val
  | .arith _ _ a b | .div _ a b | .minMax _ a b | .bit _ a b | .cmp _ a b | .boolAnd a b
  | .boolOr a b | .ptrAdd _ a b | .elemPtr a b | .ptrElemVal a b | .sliceElemVal a b
  | .store a b => [a, b]
  | .not a | .intCast _ a | .trunc a | .bitcast _ a | .isNull a | .isNonNull a | .optPayload a
  | .wrapOptional a | .isErr a | .isNonErr a | .errPayload a | .errCode a | .wrapErrPayload a
  | .wrapErr a | .fieldPtr a _ | .load a | .sliceLen a | .slicePtr a | .condBr a _ _
  | .switchBr a _ _ | .«try» a _ | .ret a | .br _ a => [a]
  | .call c args => c :: args.toList
  | _ => []

/-- `E₁` holds at the renamed operand what `E₂` holds at the operand. -/
def Agree (ρ : InstId → InstId) (f : Func) (E₁ E₂ : Env) (v : Val) : Prop :=
  operand f E₁ (renVal ρ v) = operand f E₂ v ∧ operandTy E₁ (renVal ρ v) = operandTy E₂ v

/-- `evalPure` reads the environment only through its operands. -/
theorem evalPure_congr (ρ : InstId → InstId) (f : Func) (E₁ E₂ : Env) (id₁ id₂ : InstId) (ty : TyId)
    (op : Op) (h : ∀ v ∈ topVals op, Agree ρ f E₁ E₂ v) :
    evalPure f E₁ ⟨id₁, ty, renFlat ρ op⟩ = evalPure f E₂ ⟨id₂, ty, op⟩ := by
  cases op <;> simp only [topVals, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, Agree] at h <;> simp only [renFlat, evalPure, intBin, h]

theorem storeAs_congr {ρ : InstId → InstId} {f : Func} {E₁ E₂ : Env} {p : Zig.Ptr} {a : Nat} {v : Val}
    (h : Agree ρ f E₁ E₂ v) : storeAs f E₁ p a (renVal ρ v) = storeAs f E₂ p a v := by
  cases v <;> simp only [renVal, Agree] at h <;> simp only [renVal, storeAs, h.1]

/-- `evalMem` reads the environment only through its operands. -/
theorem evalMem_congr (ρ : InstId → InstId) (f : Func) (E₁ E₂ : Env) (id₁ id₂ : InstId) (ty : TyId)
    (op : Op) (h : ∀ v ∈ topVals op, Agree ρ f E₁ E₂ v) :
    evalMem f E₁ ⟨id₁, ty, renFlat ρ op⟩ = evalMem f E₂ ⟨id₂, ty, op⟩ := by
  cases op
  case store p v =>
    simp only [topVals, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true] at h
    simp only [renFlat, evalMem, ptrOperand, h.1.1, h.1.2, storeAs_congr h.2]
  all_goals
    simp only [topVals, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true, Agree] at h
    simp only [renFlat, evalMem, evalPure, intBin, ptrOperand, sliceOperand, indexOperand, itemBase, h]

/-! ## Values without cell names -/

theorem rok_bind {α β : Type} {P : β → Prop} {x : Result α} {k : α → Result β}
    (h : ∀ a, x.run = some (.ok a) → ROk P (k a)) : ROk P (x >>= k) := by
  intro r hr
  obtain ⟨a, ha, hk⟩ := Result.bind_ok hr
  exact h a ha r hk

theorem rok_pure {α : Type} {P : α → Prop} {a : α} (h : P a) : ROk P (pure a) := by
  intro r hr
  have e : (pure a : Result α).run = some (.ok a) := rfl
  rw [e] at hr; cases hr; exact h

theorem rok_stuck {α : Type} {P : α → Prop} : ROk P (stuck : Result α) := fun _ h => by cases h

theorem rok_throw {α : Type} {P : α → Prop} {e : Zig.Error} : ROk P (throw e : Result α) :=
  fun _ h => by cases h

theorem rok_optGet {w : Value} (h : cellFree w = true) : ROk (cellFree · = true) w.optGet := by
  cases w <;> first | exact rok_stuck | exact rok_throw | exact rok_pure h

theorem rok_errGet {w : Value} (h : cellFree w = true) : ROk (cellFree · = true) w.errGet := by
  cases w <;> first | exact rok_stuck | exact rok_throw | exact rok_pure h

theorem rok_errGetErr (w : Value) : ROk (cellFree · = true) w.errGetErr := by
  cases w <;> first | exact rok_stuck | exact rok_throw | exact rok_pure rfl

theorem rok_errWrap (w : Value) : ROk (cellFree · = true) w.errWrap := by
  cases w <;> first | exact rok_stuck | exact rok_pure rfl

theorem rok_constVal (f : Func) (v : Val) : ROk (cellFree · = true) (constVal f v) := by
  cases v <;> simp only [constVal] <;> (try split) <;> first | exact rok_stuck | exact rok_pure rfl

/-- In an environment whose operands hold values without cell names, `evalPure`'s value has
none. -/
theorem evalPure_cf (f : Func) (E : Env) (i : Inst)
    (h : ∀ v ∈ topVals i.op, ROk (cellFree · = true) (operand f E v)) :
    ROk (cellFree · = true) (evalPure f E i) := by
  obtain ⟨id, ty, op⟩ := i
  cases op <;> simp only [topVals, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true] at h <;> simp only [evalPure, intBin] <;>
  repeat' (first
    | with_reducible exact rok_stuck | with_reducible exact rok_throw
    | (with_reducible apply rok_bind; intro _ _)
    | split
    | exact rok_optGet (h _ ‹_›) | exact rok_errGet (h _ ‹_›)
    | exact rok_errGetErr _ | exact rok_errWrap _
    | exact rok_pure rfl
    | exact rok_pure (by simp only [cellFree]; exact h _ ‹_›))

theorem mok_bind {α β : Type} {P : β → Prop} {x : MemM α} {k : α → MemM β}
    (h : ∀ a, MOk P (k a)) : MOk P (x >>= k) := by
  intro m r hr
  rw [StateT.run_bind] at hr
  obtain ⟨p, _, hk⟩ := Result.bind_ok hr
  exact h p.1 _ _ hk

theorem mok_pure {α : Type} {P : α → Prop} {a : α} (h : P a) : MOk P (pure a) := by
  intro m r hr
  simp only [StateT.run_pure] at hr
  have e : (pure (a, m) : Result (α × Zig.Mem)).run = some (.ok (a, m)) := rfl
  rw [e] at hr; cases hr; exact h

theorem mok_lift {α : Type} {P : α → Prop} {x : Result α} (h : ROk P x) : MOk P (StateT.lift x) := by
  intro m r hr
  simp only [StateT.run_lift] at hr
  obtain ⟨a, ha, hk⟩ := Result.bind_ok hr
  have e : (pure (a, m) : Result (α × Zig.Mem)).run = some (.ok (a, m)) := rfl
  rw [e] at hk; cases hk; exact h a ha

/-- In an environment whose operands hold values without cell names, `evalMem`'s value has
none. -/
theorem evalMem_cf (f : Func) (E : Env) (i : Inst)
    (h : ∀ v ∈ topVals i.op, ROk (cellFree · = true) (operand f E v)) :
    MOk (cellFree · = true) (evalMem f E i) := by
  have hp := evalPure_cf f E i h
  obtain ⟨id, ty, op⟩ := i
  cases op <;> simp only [evalMem, loadAs] <;>
  repeat' (first
    | exact mok_lift hp | exact mok_lift rok_stuck | exact mok_pure rfl
    | (apply mok_bind; intro _)
    | split)

end Air2Lean.Renumber
