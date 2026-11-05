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
      simp [hj, this]
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
      simp [hi, this]
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
    simp [clearOf_ren hρ, Array.all_toList]
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

/-- When `evalPure`'s value has no cell names, neither has `evalMem`'s: its own arms load and
build integers, `bool`s and pointers. -/
theorem evalMem_cf (f : Func) (E : Env) (i : Inst) (hp : ROk (cellFree · = true) (evalPure f E i)) :
    MOk (cellFree · = true) (evalMem f E i) := by
  obtain ⟨id, ty, op⟩ := i
  cases op <;> simp only [evalMem, loadAs] <;>
  repeat' (first
    | exact mok_lift hp | exact mok_lift rok_stuck | exact mok_pure rfl
    | (apply mok_bind; intro _)
    | split)

/-! ## Register cells stay in their slots -/

/-- The SSA environment of a run: a register local's slot holds its own cell, every other slot a
value without cell names. -/
def InvEnv (f : Func) (env : Env) : Prop :=
  ∀ j t v, env j = some (t, v) → cellFree v = true ∨ (regAlloc f j = true ∧ v = .cell j)

/-- Every register local of `f` is a register local of the body `l` too. -/
def RegOk (f : Func) (l : List Inst) : Prop := ∀ a, regAlloc f a = true → regBody a l = true

theorem RegOk.cons {f : Func} {i : Inst} {rest : List Inst} (h : RegOk f (i :: rest)) :
    (∀ a, regAlloc f a = true → regInst a i = true) ∧ RegOk f rest :=
  ⟨fun a ha => by have := h a ha; simp only [regBody, Bool.and_eq_true] at this; exact this.1,
   fun a ha => by have := h a ha; simp only [regBody, Bool.and_eq_true] at this; exact this.2⟩

theorem regUse_of_regInst {a : InstId} {i : Inst} (h : regInst a i = true) : regUse a i.op = true := by
  rw [regInst, Bool.and_eq_true] at h; exact h.1

theorem InvEnv.set {f : Func} {env : Env} (h : InvEnv f env) (j : InstId) (t : TyId) {v : Value}
    (hv : cellFree v = true) : InvEnv f (env.set j t v) := by
  intro k t' w hk
  simp only [Env.set] at hk
  split at hk
  · cases hk; exact .inl hv
  · exact h k t' w hk

theorem InvEnv.setReg {f : Func} {env : Env} (h : InvEnv f env) {j : InstId} (hr : regAlloc f j = true)
    (t : TyId) : InvEnv f (env.set j t (.cell j)) := by
  intro k t' w hk
  simp only [Env.set] at hk
  split at hk
  · cases hk; subst_vars; exact .inr ⟨hr, rfl⟩
  · exact h k t' w hk

theorem topVals_clear {a : InstId} {op : Op} (h : regUse a op = true) (hl : ∀ p, op ≠ .load p)
    (hs : ∀ p v, op ≠ .store p v) : ∀ v ∈ topVals op, clearOf a v = true := by
  cases op
  case call cv args =>
    simp only [regUse, Bool.and_eq_true, List.all_eq_true] at h
    simp only [topVals, List.mem_cons]
    rintro v (rfl | hv)
    · exact h.1
    · exact h.2 v hv
  all_goals simp_all [regUse, topVals]

/-- A constant operand's value has no cell names. -/
theorem rok_operand_const (f : Func) (env : Env) (v : Val) (hv : ∀ j, v ≠ .inst j) :
    ROk (cellFree · = true) (operand f env v) := by
  cases v
  case inst j => exact absurd rfl (hv j)
  all_goals simp only [operand]
  all_goals repeat' (first
    | with_reducible exact rok_stuck | exact rok_constVal _ _
    | (with_reducible apply rok_bind; intro _ _)
    | split
    | exact rok_pure rfl
    | exact rok_pure (by simp only [cellFree]; exact rok_constVal _ _ _ ‹_›))

/-- An operand that no register local reaches holds the same value in both environments, without
cell names. -/
theorem operand_clear (ρ : InstId → InstId) {f : Func} {env : Env} (hinv : InvEnv f env) (v : Val)
    (hc : ∀ a, regAlloc f a = true → clearOf a v = true) :
    operand f (renVals ρ env) v = operand f env v ∧ ROk (cellFree · = true) (operand f env v) := by
  cases v
  case inst j =>
    simp only [operand, renVals]
    cases hj : env j with
    | none => exact ⟨rfl, rok_stuck⟩
    | some p =>
      obtain ⟨t, w⟩ := p
      have hw : cellFree w = true := by
        rcases hinv j t w hj with h | ⟨hr, _⟩
        · exact h
        · have := hc j hr; simp [clearOf] at this
      simp only [Option.map_some, renV_of_cellFree ρ hw]
      exact ⟨by trivial, rok_pure hw⟩
  all_goals exact ⟨rfl, rok_operand_const f env _ fun _ h => by cases h⟩

theorem operands_clear (ρ : InstId → InstId) {f : Func} {env : Env} (hinv : InvEnv f env) {op : Op}
    (hreg : ∀ a, regAlloc f a = true → regUse a op = true) (hl : ∀ p, op ≠ .load p)
    (hs : ∀ p v, op ≠ .store p v) :
    ∀ v ∈ topVals op, operand f (renVals ρ env) v = operand f env v ∧
      ROk (cellFree · = true) (operand f env v) :=
  fun v hv => operand_clear ρ hinv v fun a ha => topVals_clear (hreg a ha) hl hs v hv

theorem rok_mapM {f : Func} {env : Env} :
    ∀ (l : List Val), (∀ v ∈ l, ROk (cellFree · = true) (operand f env v)) →
      ROk (fun vs => vs.all cellFree = true) (l.mapM (operand f env))
  | [], _ => rok_pure rfl
  | v :: l, h => by
    simp only [List.mapM_cons]
    apply rok_bind; intro a ha
    apply rok_bind; intro as has
    apply rok_pure
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨h v (by simp) a ha, rok_mapM l (fun w hw => h w (by simp [hw])) as has⟩

theorem ok_liftMem {α : Type} {P : α → Prop} {x : MemM α} (h : MOk P x) : Ok P (liftMem x) := by
  intro s m r hr
  simp only [liftMem, StateT.run_lift, StateT.run_bind, StateT.run_pure] at hr
  obtain ⟨p, hp, hk⟩ := Result.bind_ok hr
  have e : (pure ((p.1, s), p.2) : Result ((α × Frame) × Zig.Mem)).run = some (.ok ((p.1, s), p.2)) := rfl
  rw [e] at hk; cases hk; exact h m p hp

theorem rok_cellRead (t : Ty) (v : Option Value) : ROk (cellFree · = true) (cellRead t v) := by
  cases v with
  | none => exact rok_throw
  | some v =>
    simp only [cellRead]; split
    · exact rok_pure (cellFree_of_valOk t v ‹_›)
    · exact rok_stuck

/-- `execInst`'s last arm: every operation without an arm of its own is `evalMem`'s. -/
theorem execInst_default {c : Ctx} {id : InstId} {ty : TyId} {op : Op} {rest : List Inst} {env : Env}
    (h1 : ∀ index, op ≠ .arg index) (h2 : ∀ b, op ≠ .block b) (h3 : ∀ b, op ≠ .loop b)
    (h4 : ∀ t v, op ≠ .br t v) (h5 : ∀ t, op ≠ .«repeat» t) (h6 : ∀ v, op ≠ .ret v)
    (h7 : op ≠ .unreach) (h8 : op ≠ .trap) (h9 : ∀ v t e, op ≠ .condBr v t e)
    (h10 : ∀ v cs e, op ≠ .switchBr v cs e) (h11 : op ≠ .alloc) (h12 : ∀ p, op ≠ .load p)
    (h13 : ∀ p v, op ≠ .store p v) (h14 : ∀ n r s args, op ≠ .call (.func n r s) args)
    (h15 : ∀ n, op ≠ .line n) (h16 : ∀ n v, op ≠ .dbg n v) (h17 : ∀ v b, op ≠ .«try» v b)
    (h18 : ∀ k idx, op ≠ .sliceElemVal (.inst k) idx) :
    execInst c ⟨id, ty, op⟩ rest env =
      liftMem (evalMem c.func env ⟨id, ty, op⟩) >>= fun v => execBody c rest (env.set id ty v) := by
  cases op
  case call cv args =>
    cases cv <;> first | exact (h14 _ _ _ _ rfl).elim | (rw [execInst] <;> rfl)
  case sliceElemVal sv idx =>
    cases sv <;> first | exact (h18 _ _ rfl).elim | (rw [execInst] <;> rfl)
  all_goals first
    | exact (h1 _ rfl).elim | exact (h2 _ rfl).elim | exact (h3 _ rfl).elim
    | exact (h4 _ _ rfl).elim | exact (h5 _ rfl).elim | exact (h6 _ rfl).elim | exact (h7 rfl).elim
    | exact (h8 rfl).elim | exact (h9 _ _ _ rfl).elim | exact (h10 _ _ _ rfl).elim
    | exact (h11 rfl).elim | exact (h12 _ rfl).elim | exact (h13 _ _ rfl).elim
    | exact (h15 _ rfl).elim | exact (h16 _ _ rfl).elim | exact (h17 _ _ rfl).elim
    | (rw [execInst] <;> rfl)

section Flow

variable {c : Ctx} (hcf : Oracle.CellFree c.call) (hargs : c.args.all cellFree = true)
  (hview : ∀ k, c.view k = none)
include hcf hargs hview

/-- A run never moves a register local's cell out of its slot: every exit's value has no cell
names. -/
theorem execBody_flow : ∀ l env, InvEnv c.func env → RegOk c.func l → Ok exitFree (execBody c l env) := by
  apply execBody.induct c
    (motive2 := fun i rest env => InvEnv c.func env → RegOk c.func (i :: rest) →
      Ok exitFree (execInst c i rest env))
    (motive3 := fun s _ x cs el env => InvEnv c.func env →
      (∀ a, regAlloc c.func a = true → regCases a cs = true ∧ regBody a el.toList = true) →
      Ok exitFree (execSwitch c s x cs el env))
    (motive4 := fun id body env => InvEnv c.func env → RegOk c.func body.toList →
      Ok (fun e => Exit.again id e = false ∧ exitFree e) (execLoop c id body env))
  case case1 => intro env _ _; simp only [execBody]; exact ok_stuck
  case case2 => intro i rest env ih hinv hreg; simp only [execBody]; exact ih hinv hreg
  case case27 =>
    intro s w x el env ih hinv hreg
    simp only [execSwitch]
    exact ih hinv fun a ha => by simpa [regBody] using (hreg a ha).2
  case case28 =>
    intro s w x sc more el env ihb ihm hinv hreg
    simp only [execSwitch]
    apply ok_bind; intro b
    apply ok_ite
    · exact ihb hinv fun a ha => by have := (hreg a ha).1; simp only [regCases, Bool.and_eq_true] at this; exact this.1
    · exact ihm hinv fun a ha => by
        have := hreg a ha; simp only [regCases, Bool.and_eq_true] at this; exact ⟨this.1.2, this.2⟩
  case case29 =>
    intro id body env ih hinv hreg
    simp only [execLoop]
    refine ok_loop (ok_iteration c (ok_mono (ih hinv hreg) ?_))
    intro e he
    cases e <;> simp_all [exitFree, Exit.again]
  case case3 =>
    intro i rest env index hop v hv ih hinv hreg
    have hc : cellFree v = true := List.all_eq_true.mp hargs v (List.mem_of_getElem? hv)
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst, hv]
    exact ih (hinv.set _ _ hc) (RegOk.cons hreg).2
  case case4 =>
    intro i rest env index hop hv _ _
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst, hv]; exact ok_stuck
  case case5 =>
    intro i rest env body hop ihb ihr hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨h1, h2⟩ := RegOk.cons hreg
    simp only [regInst, regUse, Bool.true_and] at h1
    simp only [execInst]
    refine ok_bind' (ihb hinv h1) fun e he => ?_
    split
    · rename_i t v
      split
      · subst_vars; exact ihr _ _ rfl (hinv.set _ _ he) h2
      · exact ok_pure he
    · exact ok_pure he
  case case6 =>
    intro i rest env body hop ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨h1, _⟩ := RegOk.cons hreg
    simp only [regInst, regUse, Bool.true_and] at h1
    simp only [execInst]
    exact ok_mono (ih hinv h1) fun e he => he.2
  case case7 =>
    intro i rest env t v hop hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have ho := operands_clear (fun x => x) hinv (op := .br t v)
      (fun a ha => regUse_of_regInst ((RegOk.cons hreg).1 a ha)) (by simp) (by simp)
    simp only [topVals, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true] at ho
    simp only [execInst]
    exact ok_bind' (ok_lift ho.2) fun x hx => ok_pure hx
  case case8 =>
    intro i rest env t hop _ _
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst]; exact ok_pure trivial
  case case9 =>
    intro i rest env v hop hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have ho := operands_clear (fun x => x) hinv (op := .ret v)
      (fun a ha => regUse_of_regInst ((RegOk.cons hreg).1 a ha)) (by simp) (by simp)
    simp only [topVals, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true] at ho
    simp only [execInst]
    exact ok_bind' (ok_lift ho.2) fun x hx => ok_pure hx
  case case10 =>
    intro i rest env hop _ _
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst]; exact ok_throw
  case case11 =>
    intro i rest env hop _ _
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst]; exact ok_throw
  case case12 =>
    intro i rest env cv th el hop iht ihe hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨h1, _⟩ := RegOk.cons hreg
    simp only [regInst, Bool.and_eq_true] at h1
    simp only [execInst]
    exact ok_bind fun _ => ok_bind fun _ => ok_ite (iht hinv fun a ha => (h1 a ha).2.1)
      (ihe hinv fun a ha => (h1 a ha).2.2)
  case case13 =>
    intro i rest env v cs el hop ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨h1, _⟩ := RegOk.cons hreg
    simp only [regInst, Bool.and_eq_true] at h1
    simp only [execInst]
    refine ok_bind fun x => ?_
    split
    · exact ih _ _ _ hinv fun a ha => (h1 a ha).2
    · exact ok_stuck
  case case14 =>
    intro i rest env hop hr ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst, hr, ite_true]
    exact ok_bind fun _ => ih (hinv.setReg hr _) (RegOk.cons hreg).2
  case case15 =>
    intro i rest env hop hr size snd align ha hl ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst, hr, Bool.false_eq_true, ite_false, ha, hl]
    exact ok_bind fun p => ok_bind fun _ => ih p (hinv.set _ _ rfl) (RegOk.cons hreg).2
  case case16 =>
    intro i rest env hop hr hne _ _
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst, hr, Bool.false_eq_true, ite_false]
    exact ok_stuck
  case case17 =>
    intro i rest env p hop ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst]
    refine ok_bind' (Q := (cellFree · = true)) ?_ fun v hv => ih v (hinv.set _ _ hv) (RegOk.cons hreg).2
    refine ok_bind fun w => ?_
    split
    · exact ok_bind fun _ => ok_lift (rok_cellRead _ _)
    · exact ok_liftMem (evalMem_cf _ _ _ rok_stuck)
  case case18 =>
    intro i rest env p v hop ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst]
    exact ok_bind fun _ => ih (hinv.set _ _ rfl) (RegOk.cons hreg).2
  case case19 =>
    intro i rest env name nr sp args hop e he _ _
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst, he]; exact ok_throw
  case case20 =>
    intro i rest env name nr sp args hop hn ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have ho := operands_clear (fun x => x) hinv (op := .call (.func name nr sp) args)
      (fun a ha => regUse_of_regInst ((RegOk.cons hreg).1 a ha)) (by simp) (by simp)
    simp only [execInst, hn]
    refine ok_bind' (ok_lift (rok_mapM args.toList fun v hv =>
      (ho v (List.mem_cons_of_mem _ hv)).2)) fun vs hvs => ?_
    exact ok_bind' (ok_liftMem (hcf name vs hvs)) fun v hv => ih v (hinv.set _ _ hv) (RegOk.cons hreg).2
  case case21 =>
    intro i rest env n hop ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst]; exact ih hinv (RegOk.cons hreg).2
  case case22 =>
    intro i rest env n v hop ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [execInst]; exact ih hinv (RegOk.cons hreg).2
  case case23 =>
    intro i rest env v eb hop ihr ihe hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨h1, h2⟩ := RegOk.cons hreg
    have ho := operands_clear (fun x => x) hinv (op := .«try» v eb)
      (fun a ha => regUse_of_regInst (h1 a ha)) (by simp) (by simp)
    simp only [regInst, Bool.and_eq_true] at h1
    simp only [execInst]
    refine ok_bind' (Q := (cellFree · = true)) (ok_lift ?_) fun w hw => ?_
    · unfold errUnionOperand
      split
      · exact (ho v (by simp [topVals])).2
      · exact rok_stuck
    · split
      · exact ihr _ (hinv.set _ _ hw) h2
      · exact ihe hinv fun a ha => (h1 a ha).2
      · exact ok_stuck
  case case24 =>
    intro i rest env k idx hop items hv _ _ _
    simp [hview] at hv
  case case25 =>
    intro i rest env k idx hop hv ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have ho := operands_clear (fun x => x) hinv (op := .sliceElemVal (.inst k) idx)
      (fun a ha => regUse_of_regInst ((RegOk.cons hreg).1 a ha)) (by simp) (by simp)
    simp only [execInst, hv]
    exact ok_bind' (ok_liftMem (evalMem_cf _ _ _ (evalPure_cf _ _ _ fun v hv => (ho v hv).2)))
      fun v hv => ih v (hinv.set _ _ hv) (RegOk.cons hreg).2
  case case26 =>
    intro i rest env h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 ih hinv hreg
    obtain ⟨id, ty, op⟩ := i
    have ho := operands_clear (fun x => x) hinv (op := op)
      (fun a ha => regUse_of_regInst ((RegOk.cons hreg).1 a ha)) (fun p e => h12 p e)
      (fun p v e => h13 p v e)
    rw [execInst_default (fun index e => h1 index e) (fun b e => h2 b e) (fun b e => h3 b e)
      (fun t v e => h4 t v e) (fun t e => h5 t e) (fun v e => h6 v e) (fun e => h7 e) (fun e => h8 e)
      (fun v t el e => h9 v t el e) (fun v cs el e => h10 v cs el e) (fun e => h11 e)
      (fun p e => h12 p e) (fun p v e => h13 p v e) (fun n r s a e => h14 n r s a e)
      (fun n e => h15 n e) (fun n v e => h16 n v e) (fun v b e => h17 v b e)
      (fun k idx e => h18 k idx e)]
    exact ok_bind' (ok_liftMem (evalMem_cf _ _ _ (evalPure_cf _ _ _ fun v hv => (ho v hv).2)))
      fun v hv => ih v (hinv.set _ _ hv) (RegOk.cons hreg).2

end Flow

/-! ## The renamed function reads the same types and layouts -/

section RenFunc
variable (ρ : InstId → InstId) (f : Func)

theorem operand_renFunc (env : Env) (v : Val) : operand (renFunc ρ f) env v = operand f env v := rfl

theorem cellVal_renFunc (env : Env) (v : Val) : cellVal (renFunc ρ f) env v = cellVal f env v := rfl

theorem errUnionOperand_renFunc (env : Env) (v : Val) :
    errUnionOperand (renFunc ρ f) env v = errUnionOperand f env v := rfl

theorem tyOf_renFunc (t : TyId) : tyOf (renFunc ρ f) t = tyOf f t := rfl

theorem pointee_renFunc (t : TyId) : pointee? (renFunc ρ f) t = pointee? f t := rfl

theorem layoutOf_renFunc : layoutOf (renFunc ρ f) = layoutOf f := rfl

theorem ptrAlignOf_renFunc (t : TyId) : ptrAlignOf (renFunc ρ f) t = ptrAlignOf f t := rfl

theorem caseHit_renFunc (env : Env) (s : Bool) {w : Nat} (x : BitVec w) (sc : SwitchCase) :
    caseHit (renFunc ρ f) env s x sc = caseHit f env s x sc := rfl

theorem evalMem_renFunc (env : Env) (i : Inst) : evalMem (renFunc ρ f) env i = evalMem f env i := by
  obtain ⟨id, ty, op⟩ := i
  cases op <;> rfl

theorem valOkIn_renFunc (n : Nat) (t : TyId) (v : Value) :
    valOkIn (renFunc ρ f) n t v = valOkIn f n t v := by
  induction n generalizing t v with
  | zero => rfl
  | succ n ih =>
    simp only [renFunc] at ih
    simp only [valOkIn, renFunc]
    split <;> (try rw [ih]) <;> rfl

theorem argsOk_renFunc (ts : List TyId) (args : List Value) :
    argsOk (renFunc ρ f) ts args = argsOk f ts args := by
  induction ts generalizing args with
  | nil => cases args <;> rfl
  | cons t ts ih => cases args <;> simp only [argsOk, valOkIn_renFunc, ih]

end RenFunc

/-- The context of the renamed run. -/
def renCtx (ρ : InstId → InstId) (c : Ctx) : Ctx := { c with func := renFunc ρ c.func }

theorem iteration_ren (ρ : InstId → InstId) (c : Ctx) {α : Type} (body : SM α) :
    iteration (renCtx ρ c) body = iteration c body := rfl

/-! ## Operands of the renamed run -/

theorem rok_of_run {α : Type} {P : α → Prop} {x : Result α} {a : α} (hx : x.run = some (.ok a))
    (h : P a) : ROk P x := fun b hb => by rw [hx] at hb; cases hb; exact h

theorem map_renV_of_rok {ρ : InstId → InstId} {x : Result Value} (h : ROk (cellFree · = true) x) :
    renV ρ <$> x = x := by
  apply ExceptT.ext
  rw [ExceptT.run_map]
  cases hx : x.run with
  | none => rfl
  | some e =>
    cases e with
    | error _ => rfl
    | ok a =>
      show some (Except.ok (renV ρ a)) = some (Except.ok a)
      rw [renV_of_cellFree ρ (h a hx)]

/-- `renVals` renames the cell names of every operand's value. -/
theorem operand_renVals (ρ : InstId → InstId) (f : Func) (env : Env) (v : Val) :
    operand f (renVals ρ env) v = renV ρ <$> operand f env v := by
  cases v
  case inst j =>
    simp only [operand, renVals]
    cases env j with
    | none => rfl
    | some p => rfl
  all_goals
    symm
    exact map_renV_of_rok (rok_operand_const f env _ (by intro _ h; cases h))

/-- An operand's value is a register local's own cell or has no cell names. -/
theorem operand_inv {f : Func} {env : Env} (hinv : InvEnv f env) (v : Val) {w : Value}
    (hw : (operand f env v).run = some (.ok w)) : cellFree w = true ∨ ∃ k, w = .cell k := by
  cases v
  case inst j =>
    simp only [operand] at hw
    cases hj : env j with
    | none => rw [hj] at hw; cases hw
    | some p =>
      obtain ⟨t, u⟩ := p
      rw [hj] at hw
      have e : w = u := rok_pure (P := fun x => x = u) rfl w hw
      subst e
      rcases hinv j t w hj with h | ⟨_, rfl⟩
      · exact .inl h
      · exact .inr ⟨j, rfl⟩
  all_goals exact .inl (rok_operand_const f env _ (by intro _ h; cases h) w hw)

theorem agree_of_clear {ρ : InstId → InstId} (hρ : Inj ρ) {f : Func} {env : Env} (hinv : InvEnv f env)
    (v : Val) (hc : ∀ a, regAlloc f a = true → clearOf a v = true) : Agree ρ f (renEnv ρ env) env v :=
  ⟨by rw [operand_ren hρ, (operand_clear ρ hinv v hc).1], operandTy_ren hρ env v⟩

theorem cellVal_ren {ρ : InstId → InstId} (hρ : Inj ρ) {f : Func} {env : Env} (hinv : InvEnv f env)
    (v : Val) (hc : ∀ a, regAlloc f a = true → clearOf a v = true) :
    cellVal f (renEnv ρ env) (renVal ρ v) = cellVal f env v := by
  have h := (agree_of_clear hρ hinv v hc).1
  cases v
  case undef t => rfl
  all_goals exact congrArg (some <$> ·) h

theorem renEnv_set_cf {ρ : InstId → InstId} (hρ : Inj ρ) {env : Env} {j : InstId} {t : TyId} {v : Value}
    (hv : cellFree v = true) : (renEnv ρ env).set (ρ j) t v = renEnv ρ (env.set j t v) := by
  rw [renEnv_set hρ, renV_of_cellFree ρ hv]

theorem mapM_map_congr {α β γ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (g : α → β)
    (F : β → m γ) (G : α → m γ) : ∀ l : List α, (∀ a ∈ l, F (g a) = G a) → (l.map g).mapM F = l.mapM G
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.map_cons, List.mapM_cons, h a (by simp),
      mapM_map_congr g F G l fun b hb => h b (by simp [hb])]

/-- A renamed case compares the same values when its items and ranges are clear. -/
theorem caseHit_ren {ρ : InstId → InstId} (hρ : Inj ρ) {f : Func} {env : Env} (hinv : InvEnv f env)
    (s : Bool) {w : Nat} (x : BitVec w) (sc : SwitchCase) (b : Array Inst)
    (hc : ∀ a, regAlloc f a = true → (sc.items.toList.all (clearOf a ·) &&
      sc.ranges.toList.all fun (l, h) => clearOf a l && clearOf a h) = true) :
    caseHit f (renEnv ρ env) s x
        { items := sc.items.map (renVal ρ), ranges := sc.ranges.map fun (l, h) => (renVal ρ l, renVal ρ h),
          body := b } =
      caseHit f env s x sc := by
  have hop : ∀ v, (∀ a, regAlloc f a = true → clearOf a v = true) →
      operand f (renEnv ρ env) (renVal ρ v) = operand f env v :=
    fun v hv => (agree_of_clear hρ hinv v hv).1
  simp only [Bool.and_eq_true, List.all_eq_true] at hc
  simp only [caseHit, Array.toList_map]
  rw [mapM_map_congr _ _ (fun it => do pure (x == (← (← operand f env it).asInt w))) _
      fun it hit => by simp only [hop it fun a ha => (hc a ha).1 it hit],
    mapM_map_congr _ _ (fun (lo, hi) => do
      let l ← (← operand f env lo).asInt w
      let h ← (← operand f env hi).asInt w
      pure (Zig.le s l x && Zig.le s x h)) _
      fun ⟨lo, hi⟩ hr => by
        simp only [hop lo fun a ha => by simpa using ((hc a ha).2 _ hr).1,
          hop hi fun a ha => by simpa using ((hc a ha).2 _ hr).2]]

/-! ## The simulation -/

/-- The renamed computation `x` runs as `y`, with every cell name of the frame and the result
(`g`) renamed. -/
def Sim {α β : Type} (ρ : InstId → InstId) (g : β → α) (x : SM α) (y : SM β) : Prop :=
  ∀ s, x.run (renFrame ρ s) = mapRes g (renFrame ρ) <$> y.run s

/-- Two continuations of `x` need to agree only on the results `x` has. -/
theorem memBind_congr {α β : Type} {x : MemM α} {Q : α → Prop}
    (hx : ∀ m r, (x.run m).run = some (.ok r) → Q r.1) {k₁ k₂ : α → MemM β}
    (h : ∀ a, Q a → k₁ a = k₂ a) : x >>= k₁ = x >>= k₂ := by
  apply StateT.ext; intro m
  rw [StateT.run_bind, StateT.run_bind]
  exact bind_congr_ok _ (fun r => Q r.1) (hx m) fun r hr => by rw [h r.1 hr]

section SimLemmas
variable {ρ : InstId → InstId}

theorem sim_bind {α β α' β' : Type} {g : β → α} {g' : β' → α'} {x : SM α} {y : SM β}
    {k₁ : α → SM α'} {k₂ : β → SM β'} {Q : β → Prop}
    (hxy : Sim ρ g x y) (hy : Ok Q y) (hk : ∀ b, Q b → Sim ρ g' (k₁ (g b)) (k₂ b)) :
    Sim ρ g' (x >>= k₁) (y >>= k₂) := by
  intro s
  rw [StateT.run_bind, StateT.run_bind, hxy s, bind_map_left, map_bind]
  exact memBind_congr (Q := fun p => Q p.1) (fun m r hr => hy s m r hr) fun p hp => hk p.1 hp p.2

theorem ok_true {σ α : Type} (x : Zig.MM σ α) : Ok (fun _ => True) x := fun _ _ _ _ => trivial

theorem sim_pure {α β : Type} {g : β → α} {a : α} {b : β} (h : a = g b) : Sim ρ g (pure a) (pure b) := by
  intro s; subst h; simp only [StateT.run_pure, map_pure]

theorem sim_liftR {α β : Type} (g : β → α) (x : Result β) : Sim ρ g (liftR (g <$> x)) (liftR x) := by
  intro s
  apply StateT.ext; intro m
  simp only [liftR, StateT.run_lift, StateT.run_bind, StateT.run_pure, map_bind,
    bind_map_left, map_pure, bind_assoc, pure_bind, mapRes]

theorem sim_liftR_eq {α : Type} {x₁ x₂ : Result α} (h : x₁ = x₂) : Sim ρ id (liftR x₁) (liftR x₂) := by
  subst h; simpa only [id_map] using sim_liftR (ρ := ρ) id x₁

theorem sim_liftMem_eq {α : Type} {x₁ x₂ : MemM α} (h : x₁ = x₂) : Sim ρ id (liftMem x₁) (liftMem x₂) := by
  subst h; intro s
  simp only [liftMem, StateT.run_lift, map_bind, map_pure, mapRes, id]

theorem sim_stuck {α β : Type} {g : β → α} : Sim ρ g (liftR (stuck : Result α)) (liftR stuck) :=
  sim_liftR (x := stuck) g

theorem sim_throw {α β : Type} {g : β → α} {e : Zig.Error} :
    Sim ρ g (liftR (throw e : Result α)) (liftR (throw e)) :=
  sim_liftR (x := throw e) g

theorem sim_ite {α β : Type} {g : β → α} {c : Prop} [Decidable c] {x₁ x₂ : SM α} {y₁ y₂ : SM β}
    (h₁ : Sim ρ g x₁ y₁) (h₂ : Sim ρ g x₂ y₂) : Sim ρ g (if c then x₁ else x₂) (if c then y₁ else y₂) := by
  by_cases hc : c
  · simp only [if_pos hc]; exact h₁
  · simp only [if_neg hc]; exact h₂

theorem sim_iteration {α β : Type} {g : β → α} (c : Ctx) {x : SM α} {y : SM β} (h : Sim ρ g x y) :
    Sim ρ g (iteration c x) (iteration c y) := by
  by_cases ht : c.prog.ticked c.func.name = true
  · simp only [iteration, ht, ↓reduceIte]
    exact sim_bind (sim_liftMem_eq rfl) (ok_true _) fun _ _ => h
  · simp only [iteration, ht, Bool.false_eq_true, ↓reduceIte]
    exact h

theorem sim_modify_setCell (hρ : Inj ρ) (k : InstId) (v : Option Value) :
    Sim ρ id (modify fun x => x.setCell (ρ k) v) (modify fun x => x.setCell k v) := by
  intro s; simp only [StateT.run_modify, map_pure, mapRes, id, renFrame_setCell hρ]

theorem sim_modify_blocks (p : Zig.Ptr) :
    Sim ρ id (modify fun fr : Frame => { blocks := p :: fr.blocks, cells := fr.cells })
      (modify fun fr : Frame => { blocks := p :: fr.blocks, cells := fr.cells }) := by
  intro s; simp only [StateT.run_modify, map_pure, mapRes, id]; rfl

theorem sim_cellRead (hρ : Inj ρ) (t : Ty) (k : InstId) :
    Sim ρ id (get >>= fun fr : Frame => liftR (cellRead t (fr.cells (ρ k))))
      (get >>= fun fr : Frame => liftR (cellRead t (fr.cells k))) := by
  intro s
  simp only [StateT.run_bind, StateT.run_get, pure_bind, renFrame_cells hρ]
  exact sim_liftR_eq rfl s

theorem sim_env {cG c : Ctx} {l l' : List Inst} {E env : Env} (h : E = renEnv ρ env)
    (hs : Sim ρ (renExit ρ) (execBody cG l (renEnv ρ env)) (execBody c l' env)) :
    Sim ρ (renExit ρ) (execBody cG l E) (execBody c l' env) := by
  subst h; exact hs

theorem again_ren (hρ : Inj ρ) (id : InstId) : ∀ e, Exit.again (ρ id) (renExit ρ e) = Exit.again id e
  | .rep t => by
    simp only [renExit, Exit.again]
    by_cases h : t = id
    · subst h; simp
    · have : ρ t ≠ ρ id := fun e => h (hρ _ _ e)
      rw [beq_false_of_ne this, beq_false_of_ne h]
  | .br .. | .ret _ => rfl

/-- `execInst`'s last arm, renamed: the memory step of a clear instruction, then the rest. -/
theorem sim_default {cG c : Ctx} {f' f : Func} {env : Env} {id : InstId} {ty : TyId} {i' i : Inst}
    {L rest : List Inst} (hρ : Inj ρ) (hev : evalMem f' (renEnv ρ env) i' = evalMem f env i)
    (hok : MOk (cellFree · = true) (evalMem f env i))
    (ih : ∀ v, cellFree v = true →
      Sim ρ (renExit ρ) (execBody cG L (renEnv ρ (env.set id ty v))) (execBody c rest (env.set id ty v))) :
    Sim ρ (renExit ρ) (liftMem (evalMem f' (renEnv ρ env) i') >>= fun v => execBody cG L ((renEnv ρ env).set (ρ id) ty v))
      (liftMem (evalMem f env i) >>= fun v => execBody c rest (env.set id ty v)) :=
  sim_bind (sim_liftMem_eq hev) (ok_liftMem hok) fun v hv => sim_env (renEnv_set_cf hρ hv) (ih v hv)

end SimLemmas

/-- The items and ranges of every case are clear of `a`. -/
abbrev casesClear (a : InstId) (cs : List SwitchCase) : Bool :=
  cs.all fun sc => sc.items.toList.all (clearOf a ·) && sc.ranges.toList.all fun (l, h) => clearOf a l && clearOf a h

section Sim
variable {ρ : InstId → InstId} (hρ : Inj ρ) {c : Ctx} (hcf : Oracle.CellFree c.call)
  (hargs : c.args.all cellFree = true) (hview : ∀ k, c.view k = none)
include hρ hcf hargs hview

/-- The renamed body runs as the original, with every cell name renamed. -/
theorem execBody_sim : ∀ l env, InvEnv c.func env → RegOk c.func l →
    Sim ρ (renExit ρ) (execBody (renCtx ρ c) (renBody ρ l) (renEnv ρ env)) (execBody c l env) := by
  have flow := execBody_flow hcf hargs hview
  apply execBody.induct c
    (motive2 := fun i rest env => InvEnv c.func env → RegOk c.func (i :: rest) →
      Sim ρ (renExit ρ) (execInst (renCtx ρ c) (renInst ρ i) (renBody ρ rest) (renEnv ρ env))
        (execInst c i rest env))
    (motive3 := fun s _ x cs el env => InvEnv c.func env →
      (∀ a, regAlloc c.func a = true →
        regCases a cs = true ∧ regBody a el.toList = true ∧ casesClear a cs = true) →
      Sim ρ (renExit ρ) (execSwitch (renCtx ρ c) s x (renCases ρ cs) (renBody ρ el.toList).toArray
        (renEnv ρ env)) (execSwitch c s x cs el env))
    (motive4 := fun id body env => InvEnv c.func env → RegOk c.func body.toList →
      Sim ρ (renExit ρ) (execLoop (renCtx ρ c) (ρ id) (renBody ρ body.toList).toArray (renEnv ρ env))
        (execLoop c id body env))
  case case1 => intro env _ _; simp only [renBody, execBody]; exact sim_stuck
  case case2 => intro i rest env ih hinv hreg; simp only [renBody, execBody]; exact ih hinv hreg
  case case27 =>
    intro s w x el env ih hinv hreg
    simp only [renCases, execSwitch]
    exact ih hinv fun a ha => (hreg a ha).2.1
  case case28 =>
    intro s w x sc more el env ihb ihm hinv hreg
    have hc : ∀ a, regAlloc c.func a = true → (sc.items.toList.all (clearOf a ·) &&
        sc.ranges.toList.all fun (l, h) => clearOf a l && clearOf a h) = true := fun a ha => by
      have := (hreg a ha).2.2; simp only [casesClear, List.all_cons, Bool.and_eq_true] at this
      simp only [Bool.and_eq_true]; exact this.1
    simp only [renCases, execSwitch, renCtx, caseHit_renFunc]
    refine sim_bind (sim_liftR_eq (caseHit_ren hρ hinv s x sc _ hc)) (ok_true _) fun b _ => sim_ite ?_ ?_
    · exact ihb hinv fun a ha => by
        have := (hreg a ha).1; simp only [regCases, Bool.and_eq_true] at this; exact this.1
    · exact ihm hinv fun a ha => by
        have h := hreg a ha
        simp only [regCases, casesClear, List.all_cons, Bool.and_eq_true] at h
        exact ⟨h.1.2, h.2.1, h.2.2.2⟩
  case case29 =>
    intro id body env ih hinv hreg
    intro s
    simp only [execLoop, iteration_ren]
    exact loop_comm _ _ _ _ (renExit ρ) (renFrame ρ) (sim_iteration c (ih hinv hreg)) (again_ren hρ id) s
  case case3 =>
    intro i rest env index hop v hv ih hinv hreg
    have hc : cellFree v = true := List.all_eq_true.mp hargs v (List.mem_of_getElem? hv)
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [renInst, renFlat, execInst, renCtx, hv]
    exact sim_env (renEnv_set_cf hρ hc) (ih (hinv.set _ _ hc) (RegOk.cons hreg).2)
  case case4 =>
    intro i rest env index hop hv _ _
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [renInst, renFlat, execInst, renCtx, hv]; exact sim_stuck
  case case5 =>
    intro i rest env body hop ihb ihr hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨h1, h2⟩ := RegOk.cons hreg
    simp only [regInst, regUse, Bool.true_and] at h1
    simp only [renInst, execInst]
    refine sim_bind (ihb hinv h1) (flow _ _ hinv h1) fun e he => ?_
    cases e with
    | br t v =>
      by_cases ht : t = id
      · subst ht
        simp only [renExit, ↓reduceIte]
        exact sim_env (renEnv_set hρ env t ty v).symm (ihr _ _ rfl (hinv.set _ _ he) h2)
      · have : ρ t ≠ ρ id := fun e => ht (hρ _ _ e)
        simp only [renExit, ht, this, ↓reduceIte]
        exact sim_pure rfl
    | rep t => exact sim_pure rfl
    | ret v => exact sim_pure rfl
  case case6 =>
    intro i rest env body hop ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    obtain ⟨h1, _⟩ := RegOk.cons hreg
    simp only [regInst, regUse, Bool.true_and] at h1
    simp only [renInst, execInst]
    exact ih hinv h1
  case case7 =>
    intro i rest env t v hop hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have hc : ∀ a, regAlloc c.func a = true → clearOf a v = true :=
      fun a ha => regUse_of_regInst ((RegOk.cons hreg).1 a ha)
    simp only [renInst, renFlat, execInst, renCtx, operand_renFunc]
    exact sim_bind (sim_liftR_eq (agree_of_clear hρ hinv v hc).1) (ok_lift (operand_clear ρ hinv v hc).2)
      fun w hw => sim_pure (by simp only [renExit, id_eq, renV_of_cellFree ρ hw])
  case case8 =>
    intro i rest env t hop _ _
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [renInst, renFlat, execInst]; exact sim_pure rfl
  case case9 =>
    intro i rest env v hop hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have hc : ∀ a, regAlloc c.func a = true → clearOf a v = true :=
      fun a ha => regUse_of_regInst ((RegOk.cons hreg).1 a ha)
    simp only [renInst, renFlat, execInst, renCtx, operand_renFunc]
    exact sim_bind (sim_liftR_eq (agree_of_clear hρ hinv v hc).1) (ok_lift (operand_clear ρ hinv v hc).2)
      fun w hw => sim_pure (by simp only [renExit, id_eq, renV_of_cellFree ρ hw])
  case case10 =>
    intro i rest env hop _ _
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [renInst, renFlat, execInst]; exact sim_throw
  case case11 =>
    intro i rest env hop _ _
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [renInst, renFlat, execInst]; exact sim_throw
  case case12 =>
    intro i rest env cv th el hop iht ihe hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have hc : ∀ a, regAlloc c.func a = true → clearOf a cv = true :=
      fun a ha => regUse_of_regInst ((RegOk.cons hreg).1 a ha)
    obtain ⟨h1, _⟩ := RegOk.cons hreg
    simp only [regInst, Bool.and_eq_true] at h1
    simp only [renInst, execInst, renCtx, operand_renFunc]
    exact sim_bind (sim_liftR_eq (agree_of_clear hρ hinv cv hc).1) (ok_true _) fun w _ =>
      sim_bind (sim_liftR_eq rfl) (ok_true _) fun b _ =>
        sim_ite (iht hinv fun a ha => (h1 a ha).2.1) (ihe hinv fun a ha => (h1 a ha).2.2)
  case case13 =>
    intro i rest env v cs el hop ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have hu : ∀ a, regAlloc c.func a = true → clearOf a v = true ∧ casesClear a cs.toList = true :=
      fun a ha => by
        have := regUse_of_regInst ((RegOk.cons hreg).1 a ha)
        simp only [regUse, Bool.and_eq_true] at this; exact this
    obtain ⟨h1, _⟩ := RegOk.cons hreg
    simp only [regInst, Bool.and_eq_true] at h1
    simp only [renInst, execInst, renCtx, operand_renFunc]
    refine sim_bind (sim_liftR_eq (agree_of_clear hρ hinv v fun a ha => (hu a ha).1).1) (ok_true _)
      fun w _ => ?_
    cases w
    case int s n x => exact ih s n x hinv fun a ha => ⟨(h1 a ha).2.1, (h1 a ha).2.2, (hu a ha).2⟩
    all_goals exact sim_stuck
  case case14 =>
    intro i rest env hop hr ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only at hr
    have hr' : regAlloc (renFunc ρ c.func) (ρ id) = true := by rw [regAlloc_ren hρ]; exact hr
    simp only [renInst, renFlat, execInst, renCtx, hr, hr', ↓reduceIte]
    exact sim_bind (sim_modify_setCell hρ id none) (ok_true _) fun _ _ =>
      sim_env (by simp only [renEnv_set hρ, renV]) (ih (hinv.setReg hr _) (RegOk.cons hreg).2)
  case case15 =>
    intro i rest env hop hr size snd align ha hl ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only at hr ha hl
    have hr' : ¬regAlloc (renFunc ρ c.func) (ρ id) = true := by rw [regAlloc_ren hρ]; exact hr
    simp only [renInst, renFlat, execInst, renCtx, hr, hr', Bool.false_eq_true, ↓reduceIte,
      pointee_renFunc, layoutOf_renFunc, ptrAlignOf_renFunc, ha, hl]
    exact sim_bind (sim_liftMem_eq rfl) (ok_true _) fun p _ =>
      sim_bind (sim_modify_blocks p) (ok_true _) fun _ _ =>
        sim_env (renEnv_set_cf hρ (v := .ptr p) rfl) (ih p (hinv.set _ _ rfl) (RegOk.cons hreg).2)
  case case16 =>
    intro i rest env hop hr hne _ _
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only at hr hne
    have hr' : ¬regAlloc (renFunc ρ c.func) (ρ id) = true := by rw [regAlloc_ren hρ]; exact hr
    simp only [renInst, renFlat, execInst, renCtx, hr, hr', Bool.false_eq_true, ↓reduceIte,
      pointee_renFunc, layoutOf_renFunc, ptrAlignOf_renFunc]
    rcases h1 : (pointee? c.func ty).bind (layoutOf c.func) with _ | ⟨size, snd⟩ <;>
      rcases h2 : ptrAlignOf c.func ty with _ | align <;> (try simp only [h1, h2]) <;>
      first | exact sim_stuck | exact absurd h2 fun h => hne _ _ _ h1 h
  case case17 =>
    intro i rest env p hop ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [renInst, renFlat, execInst, renCtx, operand_renFunc, evalMem_renFunc, tyOf_renFunc]
    rw [operand_ren hρ, operand_renVals]
    refine sim_bind (g := _root_.id) (Q := (cellFree · = true)) ?_ ?_
      fun v hv => sim_env (renEnv_set_cf hρ hv) (ih v (hinv.set _ _ hv) (RegOk.cons hreg).2)
    · refine sim_bind (sim_liftR (renV ρ) _)
        (Q := fun w => (operand c.func env p).run = some (.ok w) ∧ (cellFree w = true ∨ ∃ k, w = .cell k))
        (ok_lift fun w hw => ⟨hw, operand_inv hinv p hw⟩) fun w ⟨hX, hw⟩ => ?_
      rcases hw with hw | ⟨k, rfl⟩
      · have hag : Agree ρ c.func (renEnv ρ env) env p :=
          ⟨by rw [operand_ren hρ, operand_renVals, map_renV_of_rok (rok_of_run hX hw)],
            operandTy_ren hρ env p⟩
        rw [renV_of_cellFree ρ hw]
        split
        · simp [cellFree] at hw
        · exact sim_liftMem_eq (evalMem_congr ρ c.func _ _ (ρ id) id ty (.load p)
            fun u hu => by simp only [topVals, List.mem_singleton] at hu; subst hu; exact hag)
      · exact sim_cellRead hρ _ k
    · exact ok_bind fun w => by
        split
        · exact ok_bind fun _ => ok_lift (rok_cellRead _ _)
        · exact ok_liftMem (evalMem_cf _ _ _ rok_stuck)
  case case18 =>
    intro i rest env p v hop ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have hcv : ∀ a, regAlloc c.func a = true → clearOf a v = true :=
      fun a ha => regUse_of_regInst ((RegOk.cons hreg).1 a ha)
    simp only [renInst, renFlat, execInst, renCtx, operand_renFunc, evalMem_renFunc, cellVal_renFunc]
    rw [operand_ren hρ, operand_renVals]
    refine sim_bind (g := _root_.id) (Q := fun _ => True) ?_ (ok_true _)
      fun _ _ => sim_env (renEnv_set_cf hρ (v := .void) rfl) (ih (hinv.set _ _ rfl) (RegOk.cons hreg).2)
    refine sim_bind (sim_liftR (renV ρ) _)
      (Q := fun w => (operand c.func env p).run = some (.ok w) ∧ (cellFree w = true ∨ ∃ k, w = .cell k))
      (ok_lift fun w hw => ⟨hw, operand_inv hinv p hw⟩) fun w ⟨hX, hw⟩ => ?_
    rcases hw with hw | ⟨k, rfl⟩
    · have hag : Agree ρ c.func (renEnv ρ env) env p :=
        ⟨by rw [operand_ren hρ, operand_renVals, map_renV_of_rok (rok_of_run hX hw)],
          operandTy_ren hρ env p⟩
      rw [renV_of_cellFree ρ hw]
      split
      · simp [cellFree] at hw
      · refine sim_bind (sim_liftMem_eq (evalMem_congr ρ c.func _ _ (ρ id) id ty (.store p v)
          fun u hu => ?_)) (ok_true _) fun _ _ => sim_pure rfl
        simp only [topVals, List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact hag
        · exact agree_of_clear hρ hinv _ hcv
    · simp only [renV]
      exact sim_bind (sim_liftR_eq (cellVal_ren hρ hinv v hcv)) (ok_true _)
        fun nv _ => sim_modify_setCell hρ k nv
  case case19 =>
    intro i rest env name nr sp args hop e he _ _
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [renInst, renFlat, renVal, execInst, he]; exact sim_throw
  case case20 =>
    intro i rest env name nr sp args hop hn ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have ho := operands_clear ρ hinv (op := .call (.func name nr sp) args)
      (fun a ha => regUse_of_regInst ((RegOk.cons hreg).1 a ha)) (by simp) (by simp)
    have hvs : (args.map (renVal ρ)).toList.mapM (operand (renFunc ρ c.func) (renEnv ρ env)) =
        args.toList.mapM (operand c.func env) := by
      rw [Array.toList_map]
      exact mapM_map_congr _ _ _ _ fun a ha => by
        rw [operand_renFunc, operand_ren hρ, (ho a (List.mem_cons_of_mem _ ha)).1]
    simp only [renInst, renFlat, renVal, execInst, renCtx, hn]
    exact sim_bind (sim_liftR_eq hvs)
      (ok_lift (rok_mapM args.toList fun v hv => (ho v (List.mem_cons_of_mem _ hv)).2)) fun vs hvs =>
      sim_bind (sim_liftMem_eq rfl) (ok_liftMem (hcf name vs hvs)) fun v hv =>
        sim_env (renEnv_set_cf hρ hv) (ih v (hinv.set _ _ hv) (RegOk.cons hreg).2)
  case case21 =>
    intro i rest env n hop ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [renInst, renFlat, execInst]; exact ih hinv (RegOk.cons hreg).2
  case case22 =>
    intro i rest env n v hop ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    simp only [renInst, renFlat, execInst]; exact ih hinv (RegOk.cons hreg).2
  case case23 =>
    intro i rest env v eb hop ihr ihe hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have hc : ∀ a, regAlloc c.func a = true → clearOf a v = true :=
      fun a ha => regUse_of_regInst ((RegOk.cons hreg).1 a ha)
    obtain ⟨h1, h2⟩ := RegOk.cons hreg
    simp only [regInst, Bool.and_eq_true] at h1
    have he : errUnionOperand c.func (renEnv ρ env) (renVal ρ v) = errUnionOperand c.func env v := by
      simp only [errUnionOperand, operandTy_ren hρ, (agree_of_clear hρ hinv v hc).1]
    simp only [renInst, execInst, renCtx, errUnionOperand_renFunc]
    refine sim_bind (sim_liftR_eq he) (Q := (cellFree · = true)) (ok_lift ?_) fun w hw => ?_
    · unfold errUnionOperand
      split
      · exact (operand_clear ρ hinv v hc).2
      · exact rok_stuck
    · cases w
      case errOk x =>
        have hx : cellFree x = true := hw
        exact sim_env (renEnv_set_cf hρ hx) (ihr x (hinv.set _ _ hx) h2)
      case errErr n => exact ihe hinv fun a ha => (h1 a ha).2
      all_goals exact sim_stuck
  case case24 =>
    intro i rest env k idx hop items hv _ _ _
    simp [hview] at hv
  case case25 =>
    intro i rest env k idx hop hv ih hinv hreg
    obtain ⟨id, ty, op⟩ := i; simp only at hop; subst hop
    have ho := operands_clear ρ hinv (op := .sliceElemVal (.inst k) idx)
      (fun a ha => regUse_of_regInst ((RegOk.cons hreg).1 a ha)) (by simp) (by simp)
    simp only [renInst, renFlat, renVal, execInst, renCtx, hview, evalMem_renFunc]
    exact sim_default hρ
      (evalMem_congr ρ c.func _ _ (ρ id) id ty (.sliceElemVal (.inst k) idx) fun u hu =>
        agree_of_clear hρ hinv u fun a ha =>
          topVals_clear (regUse_of_regInst ((RegOk.cons hreg).1 a ha)) (by simp) (by simp) u hu)
      (evalMem_cf _ _ _ (evalPure_cf _ _ _ fun v hv => (ho v hv).2))
      fun v hv => ih v (hinv.set _ _ hv) (RegOk.cons hreg).2
  case case26 =>
    intro i rest env h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 ih hinv hreg
    obtain ⟨id, ty, op⟩ := i
    have hc : ∀ u ∈ topVals op, ∀ a, regAlloc c.func a = true → clearOf a u = true :=
      fun u hu a ha => topVals_clear (regUse_of_regInst ((RegOk.cons hreg).1 a ha))
        (fun p e => h12 p e) (fun p v e => h13 p v e) u hu
    have hok : MOk (cellFree · = true) (evalMem c.func env ⟨id, ty, op⟩) :=
      evalMem_cf _ _ _ (evalPure_cf _ _ _ fun u hu => (operand_clear ρ hinv u (hc u hu)).2)
    have ih' : ∀ v, cellFree v = true → Sim ρ (renExit ρ)
        (execBody (renCtx ρ c) (renBody ρ rest) (renEnv ρ (env.set id ty v)))
        (execBody c rest (env.set id ty v)) :=
      fun v hv => ih v (hinv.set _ _ hv) (RegOk.cons hreg).2
    have hev : evalMem c.func (renEnv ρ env) ⟨ρ id, ty, renFlat ρ op⟩ = evalMem c.func env ⟨id, ty, op⟩ :=
      evalMem_congr ρ c.func _ _ (ρ id) id ty op fun u hu => agree_of_clear hρ hinv u (hc u hu)
    clear ih hreg hinv
    cases op
    case call cv args =>
      cases cv <;> first
        | exact (h14 _ _ _ _ rfl).elim
        | (simp only [renInst, renFlat, renVal, execInst, renCtx, evalMem_renFunc]
           exact sim_default hρ hev hok ih')
    case sliceElemVal sv idx =>
      cases sv <;> first
        | exact (h18 _ _ rfl).elim
        | (simp only [renInst, renFlat, renVal, execInst, renCtx, evalMem_renFunc]
           exact sim_default hρ hev hok ih')
    case loopSwitchBr v cs el =>
      simp only [renInst, execInst, renCtx, evalMem_renFunc]; exact sim_default hρ rfl hok ih'
    case tryPtr v b =>
      simp only [renInst, execInst, renCtx, evalMem_renFunc]; exact sim_default hρ rfl hok ih'
    all_goals first
      | exact (h1 _ rfl).elim | exact (h2 _ rfl).elim | exact (h3 _ rfl).elim
      | exact (h4 _ _ rfl).elim | exact (h5 _ rfl).elim | exact (h6 _ rfl).elim | exact (h7 rfl).elim
      | exact (h8 rfl).elim | exact (h9 _ _ _ rfl).elim | exact (h10 _ _ _ rfl).elim
      | exact (h11 rfl).elim | exact (h12 _ rfl).elim | exact (h13 _ _ rfl).elim
      | exact (h15 _ rfl).elim | exact (h16 _ _ rfl).elim | exact (h17 _ _ rfl).elim
      | (simp only [renInst, renFlat, execInst, renCtx, evalMem_renFunc]
         exact sim_default hρ hev hok ih')

end Sim

/-! ## Functions and programs -/

theorem mok_bind' {α β : Type} {P : β → Prop} {Q : α → Prop} {x : MemM α} {k : α → MemM β}
    (hx : ∀ m r, (x.run m).run = some (.ok r) → Q r.1) (h : ∀ a, Q a → MOk P (k a)) :
    MOk P (x >>= k) := by
  intro m r hr
  rw [StateT.run_bind] at hr
  obtain ⟨p, hp, hk⟩ := Result.bind_ok hr
  exact h p.1 (hx m p hp) _ _ hk

/-- A function's value names no register cell, under every oracle that keeps the contract. -/
theorem execFunc_cellFree (prog : Prog) {o : Oracle} (ho : Oracle.CellFree o) (f : Func)
    (args : List Value) : MOk (cellFree · = true) (execFunc prog o f args) := by
  by_cases h : argsOk f f.params.toList args = true
  · have hflow := execBody_flow (c := ⟨prog, f, args, o, fun _ => none⟩) ho
      (cellFree_of_argsOk f _ _ h) (fun _ => rfl) f.body.toList (fun _ => none)
      (fun _ _ _ h => by cases h) (fun _ ha => ha) {}
    have hk : MOk (cellFree · = true) (do
        let (e, frame) ← (execBody ⟨prog, f, args, o, fun _ => none⟩ f.body.toList (fun _ => none)).run {}
        frame.blocks.forM Zig.free
        match e with
        | .ret v => pure v
        | _ => StateT.lift stuck : MemM Value) :=
      mok_bind' (Q := fun p => exitFree p.1) (fun m r hr => hflow m r hr) fun ⟨e, _⟩ he =>
        mok_bind fun _ => by
          cases e
          · exact mok_lift rok_stuck
          · exact mok_lift rok_stuck
          · exact mok_pure he
    by_cases ht : prog.entryTicked f.name = true
    · simp only [execFunc, h, ht, ↓reduceIte]
      exact mok_bind fun _ => hk
    · simp only [execFunc, h, ht, Bool.false_eq_true, ↓reduceIte]
      exact hk
  · simp only [execFunc, h, Bool.false_eq_true, ↓reduceIte]
    exact mok_lift rok_stuck

/-- **Renaming instruction IDs preserves a function's execution** (V02, Canon `renumber`): for
every function, every injective renaming, every argument list and every oracle that keeps the
contract, the renamed function has the same execution, memory included. -/
theorem execFunc_rename {ρ : InstId → InstId} (hρ : Inj ρ) (prog : Prog) {o : Oracle}
    (ho : Oracle.CellFree o) (f : Func) (args : List Value) :
    execFunc prog o (renFunc ρ f) args = execFunc prog o f args := by
  simp only [execFunc, argsOk_renFunc, show (renFunc ρ f).params = f.params from rfl,
    show (renFunc ρ f).name = f.name from rfl]
  by_cases h : argsOk f f.params.toList args = true
  · simp only [h, ↓reduceIte]
    have hargs := cellFree_of_argsOk f _ _ h
    have hs := execBody_sim hρ (c := ⟨prog, f, args, o, fun _ => none⟩) ho hargs (fun _ => rfl)
      f.body.toList (fun _ => none) (fun _ _ _ h => by cases h) (fun _ ha => ha) {}
    have hflow := execBody_flow (c := ⟨prog, f, args, o, fun _ => none⟩) ho hargs (fun _ => rfl)
      f.body.toList (fun _ => none) (fun _ _ _ h => by cases h) (fun _ ha => ha) {}
    rw [renEnv_empty, renFrame_empty] at hs
    have key : ∀ K : Exit × Frame → MemM Value,
        (∀ e fr, exitFree e → K (renExit ρ e, renFrame ρ fr) = K (e, fr)) →
        (mapRes (renExit ρ) (renFrame ρ) <$>
            (execBody ⟨prog, f, args, o, fun _ => none⟩ f.body.toList (fun _ => none)).run {}) >>= K =
          (execBody ⟨prog, f, args, o, fun _ => none⟩ f.body.toList (fun _ => none)).run {} >>= K := by
      intro K hK
      rw [bind_map_left]
      exact memBind_congr (Q := fun p => exitFree p.1) (fun m r hr => hflow m r hr)
        fun p hp => hK p.1 p.2 hp
    change (do
      if prog.entryTicked f.name then Zig.tick
      let (e, frame) ← (execBody (renCtx ρ ⟨prog, f, args, o, fun _ => none⟩)
        (renBody ρ f.body.toList) (fun _ => none)).run {}
      frame.blocks.forM Zig.free
      match e with | .ret v => pure v | _ => StateT.lift stuck) = _
    rw [hs, key]
    · rfl
    · intro e fr he
      cases e with
      | ret v =>
        have hv : cellFree v = true := he
        simp only [renExit, renV_of_cellFree ρ hv] <;> rfl
      | br t v => rfl
      | rep t => rfl
  · simp only [h, Bool.false_eq_true, ↓reduceIte]

section Fixpoint
open Lean.Order

/-- The program's own semantics keeps the oracle contract: `run p` never returns a register
cell's name. -/
theorem run_cellFree (p : Prog) : Oracle.CellFree (run p) := by
  suffices h : ∀ name vs, vs.all cellFree = true → ∀ m r,
      ((run p name vs).run m).run = some (.ok r) → cellFree r.1 = true from h
  apply run.fixpoint_induct p (motive := fun o => ∀ name vs, vs.all cellFree = true → ∀ m r,
    ((o name vs).run m).run = some (.ok r) → cellFree r.1 = true)
  · apply admissible_pi; intro name
    apply admissible_pi; intro vs
    apply admissible_pi; intro _
    apply admissible_pi; intro m
    apply admissible_apply (fun _ (o : List Value → MemM Value) =>
      ∀ r, ((o vs).run m).run = some (.ok r) → cellFree r.1 = true) name
    apply admissible_apply (fun _ (x : MemM Value) =>
      ∀ r, (x m).run = some (.ok r) → cellFree r.1 = true) vs
    apply admissible_apply (fun _ (v : Zig.Result (Value × Zig.Mem)) =>
      ∀ r, v.run = some (.ok r) → cellFree r.1 = true) m
    apply admissible_flatOrder
    intro r hr; cases hr
  · intro o ho name vs _
    show MOk (cellFree · = true)
      (match p.lookup name with | some f => execFunc p o f vs | none => StateT.lift stuck)
    split
    · exact execFunc_cellFree p ho _ vs
    · exact mok_lift rok_stuck

/-- `runOn p names` keeps the oracle contract too. -/
theorem runOn_cellFree (p : Prog) (names : List String) : Oracle.CellFree (runOn p names) := by
  suffices h : ∀ name vs, vs.all cellFree = true → ∀ m r,
      ((runOn p names name vs).run m).run = some (.ok r) → cellFree r.1 = true from h
  apply runOn.fixpoint_induct p names (motive := fun o => ∀ name vs, vs.all cellFree = true → ∀ m r,
    ((o name vs).run m).run = some (.ok r) → cellFree r.1 = true)
  · apply admissible_pi; intro name
    apply admissible_pi; intro vs
    apply admissible_pi; intro _
    apply admissible_pi; intro m
    apply admissible_apply (fun _ (o : List Value → MemM Value) =>
      ∀ r, ((o vs).run m).run = some (.ok r) → cellFree r.1 = true) name
    apply admissible_apply (fun _ (x : MemM Value) =>
      ∀ r, (x m).run = some (.ok r) → cellFree r.1 = true) vs
    apply admissible_apply (fun _ (v : Zig.Result (Value × Zig.Mem)) =>
      ∀ r, v.run = some (.ok r) → cellFree r.1 = true) m
    apply admissible_flatOrder
    intro r hr; cases hr
  · intro o ho name vs _
    show MOk (cellFree · = true) (if names.contains name then
      match p.lookup name with | some f => execFunc p o f vs | none => StateT.lift stuck
      else StateT.lift stuck)
    split
    · split
      · exact execFunc_cellFree p ho _ vs
      · exact mok_lift rok_stuck
    · exact mok_lift rok_stuck

end Fixpoint

/-- `execFunc_rename` under the program's own semantics. -/
theorem execFunc_rename_run {ρ : InstId → InstId} (hρ : Inj ρ) (p : Prog) (f : Func) (args : List Value) :
    execFunc p (run p) (renFunc ρ f) args = execFunc p (run p) f args :=
  execFunc_rename hρ p (run_cellFree p) f args

/-! ## The renaming of actual snapshots -/

/-- The renaming that maps each source of `pairs` to its (first) target and every other ID above
all targets. A certificate builds it from the instruction IDs before and after `renumber`. -/
def zipRen (pairs : List (InstId × InstId)) (x : InstId) : InstId :=
  match pairs.lookup x with
  | some t => t
  | none => pairs.foldr (fun p m => max p.2 m) 0 + 1 + x

theorem lookup_mem : ∀ (pairs : List (InstId × InstId)) (x t : InstId),
    pairs.lookup x = some t → (x, t) ∈ pairs
  | [], _, _, h => by simp [List.lookup] at h
  | (a, b) :: ps, x, t, h => by
    by_cases hx : x = a
    · subst hx; simp [List.lookup] at h; subst h; simp
    · have : (x == a) = false := beq_false_of_ne hx
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (lookup_mem ps x t h)

theorem le_foldr_max : ∀ (pairs : List (InstId × InstId)) (x t : InstId), (x, t) ∈ pairs →
    t ≤ pairs.foldr (fun p m => max p.2 m) 0
  | [], _, _, h => by cases h
  | p :: ps, x, t, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with e | h
    · subst e; exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_foldr_max ps x t h) (Nat.le_max_right _ _)

theorem eq_of_mem_nodup : ∀ (pairs : List (InstId × InstId)), (pairs.map (·.2)).Nodup →
    ∀ x y t : InstId, (x, t) ∈ pairs → (y, t) ∈ pairs → x = y
  | [], _, _, _, _, h, _ => by cases h
  | p :: ps, hn, x, y, t, hx, hy => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hx with ex | hx' <;> rcases List.mem_cons.mp hy with ey | hy'
    · exact (Prod.mk.inj (ex.trans ey.symm)).1
    · exfalso; apply hn.1; subst ex; exact List.mem_map.mpr ⟨_, hy', rfl⟩
    · exfalso; apply hn.1; subst ey; exact List.mem_map.mpr ⟨_, hx', rfl⟩
    · exact eq_of_mem_nodup ps hn.2 x y t hx' hy'

/-- `zipRen` is injective when no two pairs share a target. -/
theorem zipRen_inj (pairs : List (InstId × InstId)) (h : (pairs.map (·.2)).Nodup) :
    Inj (zipRen pairs) := by
  intro x y hxy
  have bound : ∀ z t, pairs.lookup z = some t → t < pairs.foldr (fun p m => max p.2 m) 0 + 1 :=
    fun z t hz => Nat.lt_succ_of_le (le_foldr_max pairs z t (lookup_mem pairs z t hz))
  unfold zipRen at hxy
  cases hx : pairs.lookup x <;> cases hy : pairs.lookup y <;> simp only [hx, hy] at hxy
  -- `omega` needs `Nat`, not the abbreviation `InstId`.
  · dsimp only [InstId] at *; omega
  · have := bound y _ hy; dsimp only [InstId] at *; omega
  · have := bound x _ hx; dsimp only [InstId] at *; omega
  · subst hxy; exact eq_of_mem_nodup pairs h x y _ (lookup_mem pairs x _ hx) (lookup_mem pairs y _ hy)

/-- `execFunc_rename` under a certified subprogram's semantics. -/
theorem execFunc_rename_runOn {ρ : InstId → InstId} (hρ : Inj ρ) (p : Prog) (names : List String)
    (f : Func) (args : List Value) :
    execFunc p (runOn p names) (renFunc ρ f) args = execFunc p (runOn p names) f args :=
  execFunc_rename hρ p (runOn_cellFree p names) f args

end Air2Lean.Renumber
