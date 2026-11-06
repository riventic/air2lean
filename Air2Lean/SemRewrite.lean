import Air2Lean.Sem

/-!
# Function-body rewrites and the whole program

Canon's rewrites with a preservation theorem (`CanonSem`'s debug-ID erasure, `Renumber`'s
renaming) change only a function's body. This module states once what they share:

* everything `Sem` reads besides the body is the same for `f.withBody b` as for `f`
  (operands, types, layouts, argument checks);
* a body runs the same in two programs with the same step-tick policy for its function
  (`execBody_prog`, `execFunc_prog`): `Sem` reads its program only through the policy;
* the program analyses that fix the policy (`memoryFunctions`, `concFunctions`,
  `callGroups`) read each function only through its name, its globals and types, and its
  local memory, sync and callee facts (`tickPolicy_map`);
* a whole-program lift (`run_map`, `runOn_map`): rewriting every function of a program by a
  rewrite that preserves each function's execution and the program's policies preserves the
  program's semantics.

These are compiler-correctness equalities about `Sem`, not program judgments or premises.
-/

namespace Air2Lean.Sem

open Zig

/-! ## A function with another body -/

/-- `f` with the body `b`, everything else unchanged. -/
def _root_.Air2Lean.Func.withBody (f : Func) (b : Array Inst) : Func := { f with body := b }

section WithBody
variable (f : Func) (b : Array Inst)

theorem operand_withBody (env : Env) (v : Val) : operand (f.withBody b) env v = operand f env v := rfl

theorem cellVal_withBody (env : Env) (v : Val) : cellVal (f.withBody b) env v = cellVal f env v := rfl

theorem errUnionOperand_withBody (env : Env) (v : Val) :
    errUnionOperand (f.withBody b) env v = errUnionOperand f env v := rfl

theorem sliceOperand_withBody (env : Env) (v : Val) :
    sliceOperand (f.withBody b) env v = sliceOperand f env v := rfl

theorem indexOperand_withBody (env : Env) (v : Val) :
    indexOperand (f.withBody b) env v = indexOperand f env v := rfl

theorem itemLayout_withBody (t : TyId) (a : Nat) : itemLayout (f.withBody b) t a = itemLayout f t a := rfl

theorem tyOf_withBody (t : TyId) : tyOf (f.withBody b) t = tyOf f t := rfl

theorem pointee_withBody (t : TyId) : pointee? (f.withBody b) t = pointee? f t := rfl

theorem layoutOf_withBody : layoutOf (f.withBody b) = layoutOf f := rfl

theorem ptrAlignOf_withBody (t : TyId) : ptrAlignOf (f.withBody b) t = ptrAlignOf f t := rfl

theorem caseHit_withBody (env : Env) (s : Bool) {w : Nat} (x : BitVec w) (sc : SwitchCase) :
    caseHit (f.withBody b) env s x sc = caseHit f env s x sc := rfl

theorem evalMem_withBody (env : Env) (i : Inst) : evalMem (f.withBody b) env i = evalMem f env i := by
  obtain ⟨id, ty, op⟩ := i
  cases op <;> rfl

theorem valOkIn_withBody (n : Nat) (t : TyId) (v : Value) :
    valOkIn (f.withBody b) n t v = valOkIn f n t v := by
  induction n generalizing t v with
  | zero => rfl
  | succ n ih =>
    simp only [Func.withBody] at ih
    simp only [valOkIn, Func.withBody]
    split <;> (try rw [ih]) <;> rfl

theorem argsOk_withBody (ts : List TyId) (args : List Value) :
    argsOk (f.withBody b) ts args = argsOk f ts args := by
  induction ts generalizing args with
  | nil => cases args <;> rfl
  | cons t ts ih => cases args <;> simp only [argsOk, valOkIn_withBody, ih]

theorem iteration_withBody (c : Ctx) {α : Type} (body : SM α) :
    iteration { c with func := c.func.withBody b } body = iteration c body := rfl

end WithBody

/-! ## The program enters a body only through its tick policy -/

theorem iteration_prog (c : Ctx) (q : Prog) (h : q.ticked c.func.name = c.prog.ticked c.func.name)
    {α : Type} (body : SM α) : iteration { c with prog := q } body = iteration c body := by
  simp only [iteration, h]

/-- A body runs the same in every program with the same loop-tick policy for its function. -/
theorem execBody_prog (c : Ctx) (q : Prog) (h : q.ticked c.func.name = c.prog.ticked c.func.name) :
    ∀ l env, execBody { c with prog := q } l env = execBody c l env := by
  apply execBody.induct c
    (motive2 := fun i rest env => execInst { c with prog := q } i rest env = execInst c i rest env)
    (motive3 := fun s w x cs el env =>
      execSwitch { c with prog := q } s x cs el env = execSwitch c s x cs el env)
    (motive4 := fun id body env => execLoop { c with prog := q } id body env = execLoop c id body env)
  case case1 => intros; simp only [execBody]
  case case2 =>
    intro i rest env ih
    simp only [execBody]
    exact ih
  case case27 =>
    intro s w x el env ih
    simpa only [execSwitch] using ih
  case case28 =>
    intro s w x sc more el env ihb ihm
    simp only [execSwitch, ihb, ihm]
  case case29 =>
    intro id body env ih
    simp only [execLoop, iteration_prog c q h, ih]
  all_goals
    intro i
    obtain ⟨id, ty, op⟩ := i
    intro rest env
    intros
    simp only at *
    subst_vars
    simp_all only [execInst, ite_true, ite_false, Bool.false_eq_true]
    try rfl

/-- A function runs the same in every program with the same tick policy for it. -/
theorem execFunc_prog (p q : Prog) (o : Oracle) (f : Func) (args : List Value)
    (h : q.tickPolicy f.name = p.tickPolicy f.name) : execFunc q o f args = execFunc p o f args := by
  have hl : q.ticked f.name = p.ticked f.name := congrArg TickPolicy.loop h
  have he : q.entryTicked f.name = p.entryTicked f.name := congrArg TickPolicy.entry h
  have hb := execBody_prog ⟨p, f, args, o, fun _ => none⟩ q hl f.body.toList (fun _ => none)
  simp only [execFunc, he]
  simp only at hb
  rw [hb]

/-! ## The program analyses read each function through its local facts -/

section Analyses
variable (g : Func → Func) (funcs : Array Func)

theorem fnRefs_map (hglobals : ∀ f, (g f).globals = f.globals) (htypes : ∀ f, (g f).types = f.types) :
    fnRefs (funcs.map g) = fnRefs funcs := by
  simp only [fnRefs, Array.foldl_map, hglobals, htypes]

variable (hname : ∀ f, (g f).name = f.name)
  (hrefs : fnRefs (funcs.map g) = fnRefs funcs)
  (hcallees : ∀ f refs, (g f).callees refs = f.callees refs)
include hname hrefs hcallees

theorem memoryFunctions_map (hmem : ∀ f, (g f).usesMemoryLocally = f.usesMemoryLocally)
    (ext : Array String) : memoryFunctions (funcs.map g) ext = memoryFunctions funcs ext := by
  simp only [memoryFunctions, hrefs, Array.filterMap_map, Function.comp_def]
  simp only [hname, hmem, hcallees, Array.size_map]

theorem concFunctions_map (hsync : ∀ f, (g f).syncLocally = f.syncLocally) :
    concFunctions (funcs.map g) = concFunctions funcs := by
  simp only [concFunctions, hrefs, Array.filterMap_map, Function.comp_def]
  simp only [hname, hsync, hcallees, Array.size_map]

omit hcallees in
theorem callGroups_map (hcalleesOf : ∀ names refs f, calleesOf names refs (g f) = calleesOf names refs f) :
    callGroups (funcs.map g) =
      (callGroups funcs).map fun (members, recursive) => (members.map g, recursive) := by
  have hnames : (funcs.map g).map (·.name) = funcs.map (·.name) := by
    simp only [Array.map_map, Function.comp_def, hname]
  simp only [callGroups, hnames, hrefs, Graph.callGroupsBy_map, hname, hcalleesOf]

end Analyses

theorem recursiveIn_map (g : Func → Func) (hname : ∀ f, (g f).name = f.name)
    (groups : Array (Array Func × Bool)) (name : String) :
    recursiveIn (groups.map fun (members, recursive) => (members.map g, recursive)) name =
      recursiveIn groups name := by
  simp only [recursiveIn, Array.any_map, Function.comp_def, hname]

/-- **The tick policies of a rewritten program** are the original ones when the rewrite keeps
every function's name, globals, types and local memory, sync and callee facts. -/
theorem tickPolicy_map (p q : Prog) (g : Func → Func) (hq : q.funcs = p.funcs.map g)
    (hm : q.models = p.models) (hname : ∀ f, (g f).name = f.name)
    (hglobals : ∀ f, (g f).globals = f.globals) (htypes : ∀ f, (g f).types = f.types)
    (hmem : ∀ f, (g f).usesMemoryLocally = f.usesMemoryLocally)
    (hsync : ∀ f, (g f).syncLocally = f.syncLocally)
    (hcallees : ∀ f refs, (g f).callees refs = f.callees refs)
    (hcalleesOf : ∀ names refs f, calleesOf names refs (g f) = calleesOf names refs f)
    (name : String) : q.tickPolicy name = p.tickPolicy name := by
  have hrefs := fnRefs_map g p.funcs hglobals htypes
  simp only [Program.tickPolicy, Program.ticked, Program.entryTicked, Program.recursive,
    Program.usesMemory, Program.concurrent, Program.memFuncs, Program.concFuncs, Program.groups,
    hq, hm, memoryFunctions_map g p.funcs hname hrefs hcallees hmem,
    concFunctions_map g p.funcs hname hrefs hcallees hsync,
    callGroups_map g p.funcs hname hrefs hcalleesOf, recursiveIn_map g hname]

/-! ## The whole-program lift -/

theorem lookup_map (p q : Prog) (g : Func → Func) (hq : q.funcs = p.funcs.map g)
    (hname : ∀ f, (g f).name = f.name) (name : String) :
    q.lookup name = (p.lookup name).map g := by
  simp only [Program.lookup, hq, Array.find?_map, Function.comp_def, hname]

open Lean.Order in
/-- **A whole-program rewrite preserves the program's semantics** when it keeps the names and
tick policies and preserves each function's execution under both programs' own oracles. -/
theorem run_map (p q : Prog) (g : Func → Func) (hq : q.funcs = p.funcs.map g)
    (hname : ∀ f, (g f).name = f.name) (hpol : ∀ name, q.tickPolicy name = p.tickPolicy name)
    (hexec : ∀ o, (o = run p ∨ o = run q) → ∀ f args, execFunc q o (g f) args = execFunc q o f args) :
    run q = run p := by
  apply PartialOrder.rel_antisymm
  · apply run_le_of_fixpoint q (run p)
    intro name f' args hf' _
    rw [lookup_map p q g hq hname] at hf'
    obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hf'
    rw [hexec _ (.inl rfl), execFunc_prog p q _ f args (hpol _), run_of_lookup hf]
  · apply run_le_of_fixpoint p (run q)
    intro name f args hf _
    have hgf : q.lookup name = some (g f) := by rw [lookup_map p q g hq hname, hf]; rfl
    rw [run_of_lookup hgf, hexec _ (.inr rfl), execFunc_prog p q _ f args (hpol _)]

open Lean.Order in
/-- `run_map` for a certified subprogram's semantics. -/
theorem runOn_map (p q : Prog) (names : List String) (g : Func → Func) (hq : q.funcs = p.funcs.map g)
    (hname : ∀ f, (g f).name = f.name) (hpol : ∀ name, q.tickPolicy name = p.tickPolicy name)
    (hexec : ∀ o, (o = runOn p names ∨ o = runOn q names) → ∀ f args,
      execFunc q o (g f) args = execFunc q o f args) :
    runOn q names = runOn p names := by
  apply PartialOrder.rel_antisymm
  · apply runOn_le_of_fixpoint q names (runOn p names)
    intro name f' args hn hf' _
    rw [lookup_map p q g hq hname] at hf'
    obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hf'
    rw [hexec _ (.inl rfl), execFunc_prog p q _ f args (hpol _), runOn_of_lookup hn hf]
  · apply runOn_le_of_fixpoint p names (runOn q names)
    intro name f args hn hf _
    have hgf : q.lookup name = some (g f) := by rw [lookup_map p q g hq hname, hf]; rfl
    rw [runOn_of_lookup hn hgf, hexec _ (.inr rfl), execFunc_prog p q _ f args (hpol _)]

end Air2Lean.Sem
