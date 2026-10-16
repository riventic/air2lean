import Air2Lean.Sem

/-!
# Debug-definition IDs preserve the AIR interpreter

The erasure changes only `.line`/`.dbg` definition IDs, recursively. Live definitions,
operands, branch targets, register-local cells and oracle values keep their names.
The preservation equality is unconditional over `Sem.Oracle`, arguments and full memory;
it is relative to the existing fragment interpreter, not a native-language theorem.
-/

namespace Air2Lean.DebugIds

open Air2Lean.Sem

mutual

/-- Rename only debug definition IDs; every operand and live definition keeps its name. -/
def mapDebugBody (rename : InstId → InstId) : List Inst → List Inst
  | [] => []
  | i :: rest => mapDebugInst rename i :: mapDebugBody rename rest
termination_by l => (sizeOf l, 0)

def mapDebugInst (rename : InstId → InstId) (i : Inst) : Inst :=
  let id := match i.op with
    | .line _ | .dbg .. => rename i.id
    | _ => i.id
  let op := match _h : i.op with
    | .block b => .block (mapDebugBody rename b.toList).toArray
    | .loop b => .loop (mapDebugBody rename b.toList).toArray
    | .condBr v t e => .condBr v (mapDebugBody rename t.toList).toArray (mapDebugBody rename e.toList).toArray
    | .switchBr v cs e =>
      .switchBr v (mapDebugCases rename cs.toList).toArray (mapDebugBody rename e.toList).toArray
    | .loopSwitchBr v cs e =>
      .loopSwitchBr v (mapDebugCases rename cs.toList).toArray (mapDebugBody rename e.toList).toArray
    | .«try» v b => .«try» v (mapDebugBody rename b.toList).toArray
    | .tryPtr v b => .tryPtr v (mapDebugBody rename b.toList).toArray
    | op => op
  { i with id, op }
termination_by (sizeOf i, 1)
decreasing_by
  all_goals
    obtain ⟨id, ty, op⟩ := i
    simp only at _h
    subst _h
    simp_wf
    try simp only [sizeOf_toList]
    omega

def mapDebugCases (rename : InstId → InstId) : List SwitchCase → List SwitchCase
  | [] => []
  | sc :: more =>
    { sc with body := (mapDebugBody rename sc.body.toList).toArray } :: mapDebugCases rename more
termination_by cs => (sizeOf cs, 0)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [sizeOf_toList]
  all_goals (try have := sizeOf_case_body sc); omega

end

abbrev eraseBody : List Inst → List Inst := mapDebugBody (fun _ => 0)
abbrev eraseInst : Inst → Inst := mapDebugInst (fun _ => 0)
abbrev eraseCases : List SwitchCase → List SwitchCase := mapDebugCases (fun _ => 0)

mutual

theorem mapDebugBody_comp (first second : InstId → InstId) (body : List Inst) :
    mapDebugBody first (mapDebugBody second body) =
      mapDebugBody (fun id => first (second id)) body := by
  cases body with
  | nil => rw [mapDebugBody, mapDebugBody, mapDebugBody]
  | cons i rest =>
    rw [mapDebugBody, mapDebugBody, mapDebugBody,
      mapDebugInst_comp first second i, mapDebugBody_comp first second rest]
termination_by (sizeOf body, 0)
decreasing_by all_goals simp_wf; omega

theorem mapDebugInst_comp (first second : InstId → InstId) (i : Inst) :
    mapDebugInst first (mapDebugInst second i) =
      mapDebugInst (fun id => first (second id)) i := by
  obtain ⟨id, ty, op⟩ := i
  cases op <;>
    (conv => lhs; arg 2; rw [mapDebugInst]) <;>
    rw [mapDebugInst, mapDebugInst] <;>
    dsimp only
  all_goals try rfl
  case block b => rw [mapDebugBody_comp first second b.toList]
  case loop b => rw [mapDebugBody_comp first second b.toList]
  case condBr v t e =>
    rw [mapDebugBody_comp first second t.toList, mapDebugBody_comp first second e.toList]
  case switchBr v cs e =>
    rw [mapDebugCases_comp first second cs.toList, mapDebugBody_comp first second e.toList]
  case loopSwitchBr v cs e =>
    rw [mapDebugCases_comp first second cs.toList, mapDebugBody_comp first second e.toList]
  case «try» v b => rw [mapDebugBody_comp first second b.toList]
  case tryPtr v b => rw [mapDebugBody_comp first second b.toList]
termination_by (sizeOf i, 1)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [sizeOf_toList]
  all_goals omega

theorem mapDebugCases_comp (first second : InstId → InstId) (cs : List SwitchCase) :
    mapDebugCases first (mapDebugCases second cs) =
      mapDebugCases (fun id => first (second id)) cs := by
  cases cs with
  | nil => rw [mapDebugCases, mapDebugCases, mapDebugCases]
  | cons sc more =>
    obtain ⟨items, ranges, body⟩ := sc
    rw [mapDebugCases, mapDebugCases, mapDebugCases, List.toList_toArray,
      mapDebugBody_comp first second body.toList, mapDebugCases_comp first second more]
termination_by (sizeOf cs, 0)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [sizeOf_toList]
  all_goals (try have := sizeOf_case_body sc); omega

end

def mapDebugArray (rename : InstId → InstId) (body : Array Inst) : Array Inst :=
  (mapDebugBody rename body.toList).toArray

/-- This applies to every body and every debug-ID map; no concrete body is reduced. -/
theorem erase_mapDebugArray (rename : InstId → InstId) (body : Array Inst) :
    eraseBody body.toList = eraseBody (mapDebugArray rename body).toList := by
  simp only [eraseBody, mapDebugArray, List.toList_toArray, mapDebugBody_comp]

def eraseFunc (f : Func) : Func := { f with body := (eraseBody f.body.toList).toArray }

def eraseCtx (c : Ctx) : Ctx := { c with func := eraseFunc c.func }

theorem eraseCases_all (cs : List SwitchCase)
    (p : Array Val → Array (Val × Val) → Bool) :
    (eraseCases cs).all (fun sc => p sc.items sc.ranges) =
      cs.all (fun sc => p sc.items sc.ranges) := by
  induction cs with
  | nil => simp only [eraseCases, mapDebugCases, List.all_nil]
  | cons sc more ih => simp only [eraseCases, mapDebugCases, List.all_cons, ih]

mutual

theorem regBody_erase (a : InstId) (l : List Inst) :
    regBody a (eraseBody l) = regBody a l := by
  cases l with
  | nil => simp only [eraseBody, mapDebugBody, regBody]
  | cons i rest =>
    rw [eraseBody, mapDebugBody, regBody, regBody, regInst_erase a i, regBody_erase a rest]
termination_by (sizeOf l, 0)
decreasing_by all_goals simp_wf; omega

theorem regInst_erase (a : InstId) (i : Inst) :
    regInst a (eraseInst i) = regInst a i := by
  obtain ⟨id, ty, op⟩ := i
  cases op <;> simp [eraseInst, mapDebugInst, regInst, regUse]
  case block b => exact regBody_erase a b.toList
  case loop b => exact regBody_erase a b.toList
  case condBr v t e => rw [regBody_erase a t.toList, regBody_erase a e.toList]
  case switchBr v cs e =>
    rw [regCases_erase a cs.toList, regBody_erase a e.toList,
      eraseCases_all cs.toList (fun items ranges =>
        items.all (clearOf a ·) && ranges.all (fun x => clearOf a x.1 && clearOf a x.2)),
      Array.all_toList]
  case «try» v b => rw [regBody_erase a b.toList]
termination_by (sizeOf i, 1)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [sizeOf_toList]
  all_goals omega

theorem regCases_erase (a : InstId) (cs : List SwitchCase) :
    regCases a (eraseCases cs) = regCases a cs := by
  cases cs with
  | nil => simp only [eraseCases, mapDebugCases, regCases]
  | cons sc more =>
    rw [eraseCases, mapDebugCases, regCases, regCases, List.toList_toArray,
      regBody_erase a sc.body.toList, regCases_erase a more]
termination_by (sizeOf cs, 0)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [sizeOf_toList]
  all_goals (try have := sizeOf_case_body sc); omega

end

theorem regAlloc_erase (f : Func) (a : InstId) :
    regAlloc (eraseFunc f) a = regAlloc f a := by
  simp only [regAlloc, eraseFunc, List.toList_toArray, regBody_erase]

theorem valOkIn_erase (f : Func) (n : Nat) (t : TyId) (v : Value) :
    valOkIn (eraseFunc f) n t v = valOkIn f n t v := by
  induction n generalizing t v with
  | zero => rfl
  | succ n ih =>
    simp only [eraseFunc] at ih
    simp only [valOkIn, eraseFunc]
    split <;> (try rw [ih]) <;> rfl

theorem argsOk_erase (f : Func) (ts : List TyId) (args : List Value) :
    argsOk (eraseFunc f) ts args = argsOk f ts args := by
  induction ts generalizing args with
  | nil => cases args <;> rfl
  | cons t ts ih =>
    cases args <;> simp only [argsOk, valOkIn_erase, ih]

theorem operand_erase (f : Func) (env : Env) (v : Val) :
    operand (eraseFunc f) env v = operand f env v := by rfl

theorem cellVal_erase (f : Func) (env : Env) (v : Val) :
    cellVal (eraseFunc f) env v = cellVal f env v := by rfl

theorem errUnionOperand_erase (f : Func) (env : Env) (v : Val) :
    errUnionOperand (eraseFunc f) env v = errUnionOperand f env v := by rfl

theorem sliceOperand_erase (f : Func) (env : Env) (v : Val) :
    sliceOperand (eraseFunc f) env v = sliceOperand f env v := by rfl

theorem indexOperand_erase (f : Func) (env : Env) (v : Val) :
    indexOperand (eraseFunc f) env v = indexOperand f env v := by rfl

theorem itemLayout_erase (f : Func) (t : TyId) (a : Nat) :
    itemLayout (eraseFunc f) t a = itemLayout f t a := by rfl

theorem tyOf_erase (f : Func) (t : TyId) : tyOf (eraseFunc f) t = tyOf f t := by rfl

theorem pointee_erase (f : Func) (t : TyId) : pointee? (eraseFunc f) t = pointee? f t := by rfl

theorem layoutOf_erase (f : Func) : layoutOf (eraseFunc f) = layoutOf f := by rfl

theorem ptrAlignOf_erase (f : Func) (t : TyId) :
    ptrAlignOf (eraseFunc f) t = ptrAlignOf f t := by rfl

theorem evalMem_func_erase (f : Func) (env : Env) (i : Inst) :
    evalMem (eraseFunc f) env i = evalMem f env i := by
  obtain ⟨id, ty, op⟩ := i
  cases op <;> rfl

theorem execBody_erase (c : Ctx) : ∀ l env,
    execBody (eraseCtx c) (eraseBody l) env = execBody c l env := by
  apply execBody.induct c
    (motive2 := fun i rest env =>
      execInst (eraseCtx c) (eraseInst i) (eraseBody rest) env = execInst c i rest env)
    (motive3 := fun s w x cs el env =>
      execSwitch (eraseCtx c) s x (eraseCases cs) (eraseBody el.toList).toArray env =
        execSwitch c s x cs el env)
    (motive4 := fun id body env =>
      execLoop (eraseCtx c) id (eraseBody body.toList).toArray env = execLoop c id body env)
  case case1 => intros; simp only [eraseBody, mapDebugBody, execBody]
  case case2 =>
    intro i rest env ih
    simp only [eraseBody, mapDebugBody, execBody]
    exact ih
  case case27 =>
    intro s w x el env ih
    simpa only [eraseCases, mapDebugCases, execSwitch, List.toList_toArray] using ih
  case case28 =>
    intro s w x sc more el env ihb ihm
    simp only [eraseCases, mapDebugCases, execSwitch, ihb, ihm]
    rfl
  case case29 =>
    intro id body env ih
    simp only [execLoop, ih]
  all_goals
    intro i
    obtain ⟨id, ty, op⟩ := i
    intro rest env
    intros
    simp only at *
    subst_vars
    simp_all only [eraseInst, mapDebugInst, eraseCtx, execInst,
      regAlloc_erase, operand_erase, cellVal_erase, errUnionOperand_erase,
      sliceOperand_erase, indexOperand_erase, itemLayout_erase, tyOf_erase,
      pointee_erase, layoutOf_erase, ptrAlignOf_erase, evalMem_func_erase,
      ite_true, ite_false, Bool.false_eq_true]
    try rfl
  case case26 =>
    cases op <;> simp_all <;> try rfl

theorem execFunc_erase (call : Oracle) (f : Func) (args : List Value) :
    execFunc call (eraseFunc f) args = execFunc call f args := by
  simp only [execFunc, argsOk_erase, show (eraseFunc f).params = f.params from rfl]
  by_cases h : argsOk f f.params.toList args = true
  · simp only [h, ite_true]
    have hb := execBody_erase ⟨f, args, call, fun _ => none⟩ f.body.toList (fun _ => none)
    change (do
      let (e, frame) ← (execBody (eraseCtx ⟨f, args, call, fun _ => none⟩)
        (eraseBody f.body.toList) (fun _ => none)).run {}
      frame.blocks.forM Zig.free
      match e with | .ret v => pure v | _ => StateT.lift stuck) = _
    rw [hb]
    congr 1
  · simp only [h, Bool.false_eq_true, ite_false]

theorem execFunc_of_erase_eq (call : Oracle) (f g : Func) (args : List Value)
    (h : eraseFunc f = eraseFunc g) : execFunc call f args = execFunc call g args := by
  calc
    execFunc call f args = execFunc call (eraseFunc f) args := (execFunc_erase call f args).symm
    _ = execFunc call (eraseFunc g) args := congrArg (fun k => execFunc call k args) h
    _ = execFunc call g args := execFunc_erase call g args

/-- Keep shared metadata opaque while checking the actual bodies. The conclusion is the
same full execution equality; the certificate discharges the body-erasure equality. -/
theorem execFunc_of_body_erase_eq (call : Oracle) (metadata : Func)
    (before after : Array Inst) (args : List Value)
    (h : eraseBody before.toList = eraseBody after.toList) :
    execFunc call { metadata with body := before } args =
      execFunc call { metadata with body := after } args := by
  apply execFunc_of_erase_eq
  exact congrArg (fun body => { metadata with body := body.toArray }) h

end Air2Lean.DebugIds
