import ZigLean.Sep.Array
import ZigLean.Sep.Total
import Lean

/-!
# Proof-producing separation steps for generated code

Symbolic execution of generated `MemM`/`MM` bodies against `Triple` and `TotalTriple`
goals. Every tactic below elaborates to applications of the lemmas of this file, which are
ordinary theorems over the existing rules (`bind`, `frame`, `conseq`, `lift`, `ex`, `load`,
`store`, `arr_store`), so the kernel checks each generated step.

* `sep_unfold [e, …]` rewrites the command of the goal: unfolds the named definitions, pushes
  `StateT.run` through binds, `get`, `modify` and `StateT.lift`, and flattens binds. Facts in
  the list (for example `hc : s.cur = some p` or an overflow fact) decide branches.
* `sep_step [e, …]` executes the first command of a `c >>= f` (or a lone `c`). For a load or
  store it finds the points-to in the precondition (`pts p a ?v`, or `arr q ?xs` when the
  address is `q.elem size i`), frames the rest, applies the load/store lemma and continues with
  `f v` (`sep_unfold [e, …]` is run on the continuation). Array bounds are tried with
  `assumption`/`omega`; an unproved bound remains a goal after the continuation.
* `sep_step [e, …] using rule` does the same with a caller-supplied triple for the command
  (a function contract or a representation lemma); the rule's pure facts and existentials
  are introduced with `sep_intro`. `sep_steps [e, …] using r₁, …` repeats the step while a
  built-in rule or one of the `rᵢ` applies.
* `sep_intro x hx …` moves pure facts `⌜φ⌝` and existentials `Assn.ex` out of the
  precondition into the context; an unnamed equation `x = e` with a local `x` is substituted.
* `sep_ret w …` closes `Triple P (pure v) Q`: existentials of `Q v` take the witnesses, pure
  atoms become goals (`rfl`/`assumption` are tried), and the spatial rest must equal `P` up to
  associativity, commutativity and `emp`. Otherwise it leaves `∀ h, P h → Q v h`.
  `sep_close hp w …` is the same entailment step for a goal `Q h` with `hp : P h`.
* `sep_split p k` splits `arr p xs` in the precondition at `k` (`arr_split`).

Frame inference matches atoms by definitional equality, as `sep_frame` does. The tactics do
not choose invariants, measures, ranges or existential witnesses; that remains the caller's
proof.
-/

namespace Zig

open Assn

/-! ## The step lemmas (partial correctness) -/

namespace Triple

variable {α β : Type} {P P' R : Assn} {Q : β → Assn}

theorem pre {c : MemM β} (hp : ∀ h, P h → P' h) (t : Triple P' c Q) : Triple P c Q :=
  conseq t hp fun _ _ hq => hq

theorem of_bind_pure {c : MemM β} (t : Triple P (c >>= pure) Q) : Triple P c Q := by
  simpa only [bind_pure] using t

theorem ret_of {v : β} (h : ∀ h, P h → Q v h) : Triple P (pure v) Q :=
  conseq (ret (Q := Q) v) h fun _ _ hq => hq

/-- A command proved by `rule`, framed by `R`; the continuation gets the rule's result. -/
theorem spec_bind {P₀ : Assn} {Q₀ : α → Assn} {c : MemM α} {f : α → MemM β}
    (rule : Triple P₀ c Q₀) (k : ∀ r, Triple (Q₀ r ∗ R) (f r) Q) :
    Triple (P₀ ∗ R) (c >>= f) Q :=
  bind (frame rule) k

/-- A command whose rule fixes its result `v`: the continuation runs on `f v`. -/
theorem spec_bind_eq {P₀ P₁ : Assn} {c : MemM α} {v : α} {f : α → MemM β}
    (rule : Triple P₀ c (fun r => ⌜r = v⌝ ∗ P₁)) (k : Triple (P₁ ∗ R) (f v) Q) :
    Triple (P₀ ∗ R) (c >>= f) Q :=
  spec_bind rule fun _ => conseq (lift (P := P₁ ∗ R) fun hr => hr ▸ k)
    (fun _ hp => sep_assoc hp) fun _ _ hq => hq

theorem ex_sep {γ : Type} {F : γ → Assn} {c : MemM β}
    (t : ∀ x, Triple (F x ∗ R) c Q) : Triple (Assn.ex F ∗ R) c Q :=
  pre (P' := Assn.ex fun x => F x ∗ R)
    (fun _ ⟨h₁, h₂, d, e, ⟨x, hx⟩, hr⟩ => ⟨x, h₁, h₂, d, e, hx, hr⟩) (ex t)

end Triple

section Rules

variable {T β : Type} [Enc T] {p : Ptr} {a : Nat} {R : Assn} {Q : β → Assn}

theorem Triple.arr_load {xs : List T} {i : BitVec 64} (hn : 0 < Enc.size T)
    (ha : a ∣ Enc.align T) (hs : Enc.align T ∣ Enc.size T) (hi : i.toNat < xs.length) :
    Triple (arr p xs) (Zig.load T a (p.elem (Enc.size T) i)) (fun r => ⌜r = xs[i.toNat]⌝ ∗ arr p xs) :=
  Triple.of_run fun _ hP _ hd hm hp hs' => by
    obtain ⟨m', hr, hm', hs''⟩ := arr_load_run hp hm hn ha hs hi hs'
    exact ⟨_, m', hP, hr, hd, hm', sep_lift.mpr ⟨rfl, hp⟩, hs''⟩

theorem Triple.load_bind {v : T} {f : T → MemM β} (hn : 0 < Enc.size T)
    (k : Triple (pts p a v ∗ R) (f v) Q) : Triple (pts p a v ∗ R) (Zig.load T a p >>= f) Q :=
  Triple.spec_bind_eq (Triple.load hn) k

theorem Triple.store_bind [LawfulEnc T] {v w : T} {f : Unit → MemM β} (hn : 0 < Enc.size T)
    (k : Triple (pts p a w ∗ R) (f ()) Q) : Triple (pts p a v ∗ R) (Zig.store a p w >>= f) Q :=
  Triple.spec_bind (Triple.store hn w) fun () => k

theorem Triple.arr_load_bind {xs : List T} {i : BitVec 64} {f : T → MemM β}
    (hn : 0 < Enc.size T) (ha : a ∣ Enc.align T) (hs : Enc.align T ∣ Enc.size T)
    (hi : i.toNat < xs.length) (k : Triple (arr p xs ∗ R) (f xs[i.toNat]) Q) :
    Triple (arr p xs ∗ R) (Zig.load T a (p.elem (Enc.size T) i) >>= f) Q :=
  Triple.spec_bind_eq (Triple.arr_load hn ha hs hi) k

theorem Triple.arr_store_bind [LawfulEnc T] {xs : List T} {i : BitVec 64} {w : T}
    {f : Unit → MemM β} (hn : 0 < Enc.size T) (ha : a ∣ Enc.align T)
    (hs : Enc.align T ∣ Enc.size T) (hi : i.toNat < xs.length)
    (k : Triple (arr p (xs.set i.toNat w) ∗ R) (f ()) Q) :
    Triple (arr p xs ∗ R) (Zig.store a (p.elem (Enc.size T) i) w >>= f) Q :=
  Triple.spec_bind (TotalTriple.arr_store hn ha hs hi w).toPartial fun () => k

theorem Triple.arr_ptrProject_bind {xs : List T} {i : BitVec 64} {f : Ptr → MemM β}
    (hi : i.toNat ≤ xs.length) (k : Triple (arr p xs ∗ R) (f (p.elem (Enc.size T) i)) Q) :
    Triple (arr p xs ∗ R) (ptrProject p (·.elem (Enc.size T) i) >>= f) Q :=
  Triple.spec_bind_eq (Triple.arr_ptrProject hi) k

theorem Triple.arr_split_pre {xs : List T} {k : Nat} {c : MemM β} (hs : Enc.align T ∣ Enc.size T)
    (hk : k ≤ xs.length)
    (t : Triple ((arr p (xs.take k) ∗ arr (p.add (Enc.size T * k)) (xs.drop k)) ∗ R) c Q) : Triple (arr p xs ∗ R) c Q :=
  Triple.pre (fun _ => sep_mono (fun _ ha => arr_split ha hk hs) fun _ hr => hr) t

end Rules

/-! ## The step lemmas (total correctness) -/

namespace TotalTriple

variable {α β : Type} {P P' R : Assn} {Q : β → Assn}

theorem pre {c : MemM β} (hp : ∀ h, P h → P' h) (t : TotalTriple P' c Q) : TotalTriple P c Q :=
  conseq t hp fun _ _ hq => hq

theorem of_bind_pure {c : MemM β} (t : TotalTriple P (c >>= pure) Q) : TotalTriple P c Q := by
  simpa only [bind_pure] using t

theorem ret_of {v : β} (h : ∀ h, P h → Q v h) : TotalTriple P (pure v) Q :=
  conseq (ret (Q := Q) v) h fun _ _ hq => hq

theorem spec_bind {P₀ : Assn} {Q₀ : α → Assn} {c : MemM α} {f : α → MemM β}
    (rule : TotalTriple P₀ c Q₀) (k : ∀ r, TotalTriple (Q₀ r ∗ R) (f r) Q) :
    TotalTriple (P₀ ∗ R) (c >>= f) Q :=
  bind (frame rule) k

theorem spec_bind_eq {P₀ P₁ : Assn} {c : MemM α} {v : α} {f : α → MemM β}
    (rule : TotalTriple P₀ c (fun r => ⌜r = v⌝ ∗ P₁)) (k : TotalTriple (P₁ ∗ R) (f v) Q) :
    TotalTriple (P₀ ∗ R) (c >>= f) Q :=
  spec_bind rule fun _ => conseq (lift (P := P₁ ∗ R) fun hr => hr ▸ k)
    (fun _ hp => sep_assoc hp) fun _ _ hq => hq

theorem ex_sep {γ : Type} {F : γ → Assn} {c : MemM β}
    (t : ∀ x, TotalTriple (F x ∗ R) c Q) : TotalTriple (Assn.ex F ∗ R) c Q :=
  pre (P' := Assn.ex fun x => F x ∗ R)
    (fun _ ⟨h₁, h₂, d, e, ⟨x, hx⟩, hr⟩ => ⟨x, h₁, h₂, d, e, hx, hr⟩) (ex t)

section Rules

variable {T : Type} [Enc T] {p : Ptr} {a : Nat}

theorem arr_load {xs : List T} {i : BitVec 64} (hn : 0 < Enc.size T)
    (ha : a ∣ Enc.align T) (hs : Enc.align T ∣ Enc.size T) (hi : i.toNat < xs.length) :
    TotalTriple (arr p xs) (Zig.load T a (p.elem (Enc.size T) i))
      (fun r => ⌜r = xs[i.toNat]⌝ ∗ arr p xs) := by
  intro m hP hF hd hm hp hs'
  obtain ⟨m', hr, hm', hs''⟩ := arr_load_run hp hm hn ha hs hi hs'
  exact ⟨_, m', hP, hr, hd, hm', sep_lift.mpr ⟨rfl, hp⟩, hs''⟩

/-- `&xs[i]` of an owned array, `i ≤ len`: checked pointer formation (`ptrProject`, MM-3). -/
theorem arr_ptrProject {xs : List T} {i : BitVec 64} (hi : i.toNat ≤ xs.length) :
    TotalTriple (arr p xs) (ptrProject p (·.elem (Enc.size T) i))
      (fun q => ⌜q = p.elem (Enc.size T) i⌝ ∗ arr p xs) := by
  intro m hP hF hd hm hp hs'
  exact ⟨_, m, hP, arr_ptrProject_run hp hm hi, hd, hm, sep_lift.mpr ⟨rfl, hp⟩, hs'⟩

theorem load_bind {v : T} {f : T → MemM β} (hn : 0 < Enc.size T)
    (k : TotalTriple (pts p a v ∗ R) (f v) Q) :
    TotalTriple (pts p a v ∗ R) (Zig.load T a p >>= f) Q :=
  spec_bind_eq (TotalTriple.load hn) k

theorem store_bind [LawfulEnc T] {v w : T} {f : Unit → MemM β} (hn : 0 < Enc.size T)
    (k : TotalTriple (pts p a w ∗ R) (f ()) Q) :
    TotalTriple (pts p a v ∗ R) (Zig.store a p w >>= f) Q :=
  spec_bind (TotalTriple.store hn w) fun () => k

theorem arr_load_bind {xs : List T} {i : BitVec 64} {f : T → MemM β}
    (hn : 0 < Enc.size T) (ha : a ∣ Enc.align T) (hs : Enc.align T ∣ Enc.size T)
    (hi : i.toNat < xs.length) (k : TotalTriple (arr p xs ∗ R) (f xs[i.toNat]) Q) :
    TotalTriple (arr p xs ∗ R) (Zig.load T a (p.elem (Enc.size T) i) >>= f) Q :=
  spec_bind_eq (arr_load hn ha hs hi) k

theorem arr_store_bind [LawfulEnc T] {xs : List T} {i : BitVec 64} {w : T}
    {f : Unit → MemM β} (hn : 0 < Enc.size T) (ha : a ∣ Enc.align T)
    (hs : Enc.align T ∣ Enc.size T) (hi : i.toNat < xs.length)
    (k : TotalTriple (arr p (xs.set i.toNat w) ∗ R) (f ()) Q) :
    TotalTriple (arr p xs ∗ R) (Zig.store a (p.elem (Enc.size T) i) w >>= f) Q :=
  spec_bind (arr_store hn ha hs hi w) fun () => k

theorem arr_ptrProject_bind {xs : List T} {i : BitVec 64} {f : Ptr → MemM β}
    (hi : i.toNat ≤ xs.length) (k : TotalTriple (arr p xs ∗ R) (f (p.elem (Enc.size T) i)) Q) :
    TotalTriple (arr p xs ∗ R) (ptrProject p (·.elem (Enc.size T) i) >>= f) Q :=
  spec_bind_eq (arr_ptrProject hi) k

theorem arr_split_pre {xs : List T} {k : Nat} {c : MemM β} (hs : Enc.align T ∣ Enc.size T)
    (hk : k ≤ xs.length)
    (t : TotalTriple ((arr p (xs.take k) ∗ arr (p.add (Enc.size T * k)) (xs.drop k)) ∗ R) c Q) : TotalTriple (arr p xs ∗ R) c Q :=
  pre (fun _ => sep_mono (fun _ ha => arr_split ha hk hs) fun _ hr => hr) t

end Rules

/-- A loop body proved as a total triple gives the run-level step that `loop_sep_ghost`,
`loop_sep_spec` and `TotalTriple.loop_ghost` take. -/
theorem step_run {σ ε : Type} {body : MM σ ε} {s : σ} {post : ε → σ → Heap → Prop}
    {m : Mem} {h hF : Heap}
    (t : TotalTriple P (body.run s) (fun r => post r.1 r.2)) (hd : Heap.Disjoint h hF)
    (hm : m.heap = h ∪ hF) (hp : P h) (hst : m.Seq) :
    ∃ e s' m' h', (body.run s).run m = pure ((e, s'), m') ∧ Heap.Disjoint h' hF ∧
      m'.heap = h' ∪ hF ∧ m'.Seq ∧ post e s' h' := by
  obtain ⟨⟨e, s'⟩, m', h', hr, hd', hm', hq, hst'⟩ := t m h hF hd hm hp hst
  exact ⟨e, s', m', h', hr, hd', hm', hst', hq⟩

end TotalTriple

theorem assn_cast {P Q : Assn} {h : Heap} (e : P = Q) (hp : P h) : Q h := e ▸ hp

theorem ex_sep_intro {γ : Type} {F : γ → Assn} {R : Assn} {h : Heap} (x : γ)
    (hx : (F x ∗ R) h) : (Assn.ex F ∗ R) h :=
  sep_mono (fun _ hf => ⟨x, hf⟩) (fun _ hr => hr) hx

/-- `StateT.lift` of a pure result (an arithmetic step whose overflow check passed). -/
theorem StateT.lift_pure_eq {σ α : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (a : α) : (StateT.lift (pure a) : StateT σ m α) = pure a := by
  funext s; simp [StateT.lift, pure, StateT.pure]

end Zig

/-! ## Tactics -/

open Lean.Parser.Tactic in
/-- Normalize the command of a `Triple`/`TotalTriple` goal: unfold the given definitions,
push `StateT.run` inward, flatten binds and decide branches with the given facts. -/
syntax (name := sepUnfold) "sep_unfold" (" [" (simpStar <|> simpErase <|> simpLemma),* "]")? : tactic

macro_rules
  | `(tactic| sep_unfold $[[$args,*]]?) => do
    let args := args.map (·.getElems) |>.getD #[]
    `(tactic| conv => arg 2; simp only [StateT.run'_eq, StateT.run_bind, StateT.run_get,
        StateT.run_set, StateT.run_pure, StateT.run_modify, StateT.run_monadLift,
        StateT.run_lift, monadLift, MonadLift.monadLift, Zig.callM, Zig.optPayload,
        Zig.StateT.lift_pure_eq, map_bind, map_pure, pure_bind, bind_assoc, Option.isSome_some,
        Option.isSome_none, ↓reduceIte, Bool.false_eq_true, Zig.lt, Zig.le, Zig.gt, Zig.ge,
        BitVec.ult, BitVec.ule, BitVec.reduceToNat, decide_eq_true_eq, $args,*])

namespace Zig.SepStep

open Lean Meta Elab Tactic

/-- The separating atoms of an assertion: `∗` is flattened and `emp` dropped. -/
partial def atoms (e : Expr) : Array Expr :=
  go [e] #[]
where
  go : List Expr → Array Expr → Array Expr
    | [], acc => acc
    | e :: rest, acc =>
      let e := e.consumeMData.headBeta
      if e.isAppOfArity ``Zig.Assn.sep 2 then go (e.appFn!.appArg! :: e.appArg! :: rest) acc
      else if e.isConstOf ``Zig.Assn.emp then go rest acc
      else go rest (acc.push e)

def sepOf (xs : Array Expr) : Expr :=
  if xs.isEmpty then mkConst ``Zig.Assn.emp
  else xs.pop.foldr (fun p q => mkApp2 (mkConst ``Zig.Assn.sep) p q) xs.back!

/-- The main goal as `(kind, P, c, Q)` for a `Triple` or `TotalTriple`. -/
def goalTriple : TacticM (Name × Expr × Expr × Expr) := do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  for kind in [``Zig.Triple, ``Zig.TotalTriple] do
    if t.isAppOfArity kind 4 then
      let args := t.getAppArgs
      return (kind, args[1]!, args[2]!.consumeMData, args[3]!)
  throwError "sep: expected a Zig.Triple or Zig.TotalTriple goal{indentExpr t}"

def lemmaId (kind : Name) (l : String) : Ident := mkIdent (kind ++ Name.mkSimple l)

/-- Reorder the precondition to `head ∗ R`, proved by AC normalization. `headExpr` is the
assertion whose atoms are `head` (default: their right-nested `∗`), kept as the rule states it. -/
def focus (kind : Name) (P : Expr) (head : Array Expr) (headExpr : Option Expr := none) :
    TacticM Unit := do
  let all := atoms P
  let mut used := Array.replicate all.size false
  for a in head do
    let mut found := false
    for i in [0:all.size] do
      unless used[i]! do
        if ← isDefEq a all[i]! then
          used := used.set! i true; found := true; break
    unless found do throwError "sep: the precondition has no atom{indentExpr a}"
  let mut rest := #[]
  for i in [0:all.size] do
    unless used[i]! do rest := rest.push all[i]!
  let target := mkApp2 (mkConst ``Zig.Assn.sep) (headExpr.getD (sepOf head)) (sepOf rest)
  let target ← Term.exprToSyntax (← instantiateMVars target)
  evalTactic (← `(tactic| refine $(lemmaId kind "pre") (P' := $target)
    (fun _ hp => by first | exact hp | (sep_normalize at hp ⊢; exact hp)) ?_))

/-- Whether an atom of `P` with head constant `head` unifies with `pat`. -/
def findAtom (P pat : Expr) (head : Name) : MetaM Bool := do
  for a in atoms P do
    if a.getAppFn.isConstOf head then
      if ← isDefEq a pat then return true
  return false

/-- Prove a bound side goal if possible; otherwise keep it. -/
def tryBound (g : MVarId) : TacticM (List MVarId) := do
  let tac ← `(tactic| first
    | assumption
    | omega
    | (simp only [List.length_set, List.length_take, List.length_drop, List.length_cons,
         List.length_nil, BitVec.reduceToNat] at *
       omega))
  match ← observing? (evalTacticAt tac g) with
  | some [] => return []
  | _ => return [g]

/-- Move pure facts and existentials out of the precondition, using `names` in order. An
unnamed equation with a local variable on one side is substituted. -/
partial def intro (names : List Name) : TacticM Unit := withMainContext do
  let (kind, P, _, _) ← goalTriple
  let some a := (atoms P).find? fun a =>
      a.isAppOfArity ``Zig.Assn.lift 1 || a.isAppOfArity ``Zig.Assn.ex 2 | return
  focus kind P #[a]
  let (name?, names) := match names with
    | n :: ns => (some n, ns)
    | [] => (none, [])
  if a.isAppOfArity ``Zig.Assn.lift 1 then
    evalTactic (← `(tactic| refine $(lemmaId kind "lift") ?_))
    match name? with
    | some n => evalTactic (← `(tactic| intro $(mkIdent n):ident))
    | none =>
      let g ← getMainGoal
      let (fv, g) ← g.intro1
      setGoals [g]
      withMainContext do
        let ty ← instantiateMVars (← fv.getType)
        if let some (_, l, r) := ty.eq? then
          for side in [l, r] do
            if side.isFVar then
              if let some g' ← observing? (substCore (← getMainGoal) fv (symm := side == r)) then
                setGoals [g'.2]
                break
  else
    let n := name?.getD ((match a.appArg! with | .lam n .. => n | _ => `x))
    evalTactic (← `(tactic| refine $(lemmaId kind "ex_sep") ?_))
    evalTactic (← `(tactic| intro $(mkIdent n):ident))
  intro names

/-- Normalize the continuation's command with `sep_unfold` and the caller's facts. -/
def cont (facts : Array Syntax) : TacticM Unit := do
  evalTactic (← `(tactic| try dsimp only))
  let facts : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := facts.map (⟨·⟩)
  discard <| observing? (evalTactic (← `(tactic| sep_unfold [$facts,*])))

/-- `&xs[i]` of an owned array `arr p xs` (`arr_ptrProject_bind`, MM-3): the side goals. -/
def ptrProjectStep (kind : Name) (P cmd : Expr) : TacticM (List MVarId) := do
  let base := cmd.getAppArgs[0]!.consumeMData
  let T ← mkFreshExprMVar (mkSort Level.one)
  let inst ← mkFreshExprMVar none
  let xs ← mkFreshExprMVar (mkApp (mkConst ``List [Level.zero]) T)
  let arr := mkAppN (mkConst ``Zig.arr) #[T, inst, base, xs]
  unless ← findAtom P arr ``Zig.arr do
    throwError "sep_step: the precondition has no `arr` for{indentExpr base}"
  focus kind P #[← instantiateMVars arr]
  match ← evalTacticAt (← `(tactic| refine $(lemmaId kind "arr_ptrProject_bind") ?_ ?_)) (← getMainGoal) with
  | [hi, k] => setGoals [k]; tryBound hi
  | _ => throwError "sep_step: unexpected goals after the pointer rule"

/-- One symbolic-execution step on the main goal. -/
def step (rule? : Option Term) (facts : Array Syntax) : TacticM Unit := withMainContext do
  let (kind, _, c, _) ← goalTriple
  unless c.isAppOfArity ``Bind.bind 6 do
    evalTactic (← `(tactic| refine $(lemmaId kind "of_bind_pure") ?_))
  withMainContext do
  let (kind, P, c, _) ← goalTriple
  let cmd := c.getAppArgs[4]!.consumeMData
  let side ← match rule? with
    | some rule => do
      let proof ← Term.elabTerm rule none
      Term.synthesizeSyntheticMVarsNoPostponing
      let ty ← instantiateMVars (← inferType proof)
      unless ty.isAppOfArity kind 4 do
        throwError "sep_step: the rule must prove a {kind} goal{indentExpr ty}"
      unless ← isDefEq ty.getAppArgs[2]! cmd do
        throwError "sep_step: the rule is about a different command{indentExpr ty.getAppArgs[2]!}"
      let pre ← instantiateMVars ty.getAppArgs[1]!
      focus kind P (atoms pre) pre
      let rule ← Term.exprToSyntax (← instantiateMVars proof)
      if (← observing? (evalTactic (← `(tactic|
          refine $(lemmaId kind "spec_bind_eq") $rule ?_)))).isNone then
        evalTactic (← `(tactic| refine $(lemmaId kind "spec_bind") $rule ?_))
        evalTactic (← `(tactic| intro r))
        evalTactic (← `(tactic| try clear r))
        evalTactic (← `(tactic| try dsimp only))
        intro []
      pure []
    | none => if cmd.isAppOfArity ``Zig.ptrProject 2 then ptrProjectStep kind P cmd else do
      let isLoad := cmd.isAppOfArity ``Zig.load 4
      let isStore := cmd.isAppOfArity ``Zig.store 5
      unless isLoad || isStore do
        throwError "sep_step: no built-in rule for{indentExpr cmd}\nuse `sep_step using rule`"
      let args := cmd.getAppArgs
      let (T, inst, a, ptr) := (args[0]!, args[1]!, args[2]!, args[3]!.consumeMData)
      let v ← mkFreshExprMVar T
      let pts := mkAppN (mkConst ``Zig.pts) #[T, inst, ptr, a, v]
      if ← findAtom P pts ``Zig.pts then
        focus kind P #[← instantiateMVars pts]
        let l := if isLoad then "load_bind" else "store_bind"
        evalTactic (← `(tactic| refine $(lemmaId kind l) (by decide) ?_))
        pure []
      else
        unless ptr.isAppOfArity ``Zig.Ptr.elem 3 do
          throwError "sep_step: the precondition has no `pts` for{indentExpr ptr}"
        let xs ← mkFreshExprMVar (← mkAppM ``List #[T])
        let arr := mkAppN (mkConst ``Zig.arr) #[T, inst, ptr.getAppArgs[0]!, xs]
        unless ← findAtom P arr ``Zig.arr do
          throwError "sep_step: the precondition has no `pts` or `arr` for{indentExpr ptr}"
        focus kind P #[← instantiateMVars arr]
        let l := if isLoad then "arr_load_bind" else "arr_store_bind"
        let goals ← evalTacticAt (← `(tactic|
          refine $(lemmaId kind l) (by decide) (by decide) (by decide) ?_ ?_)) (← getMainGoal)
        match goals with
        | [hi, k] => setGoals [k]; tryBound hi
        | _ => throwError "sep_step: unexpected goals after the array rule"
  let main :: rest ← getGoals | return
  setGoals [main]
  cont facts
  setGoals ((← getGoals) ++ side ++ rest)

/-- Prove the entailment goal `Q h` from `hp : P h`. Existentials of `Q` take the witnesses
`ws` in order; pure atoms of `Q` become goals (closed by `rfl`/`assumption` when possible);
the spatial rest must equal `P` up to AC and `emp`. Fails otherwise. -/
def close (hp : Ident) (ws : List Term) : TacticM Unit := do
  evalTactic (← `(tactic| try dsimp only at $hp:ident ⊢))
  let mut pure := #[]
  let mut ws := ws
  repeat
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let .app q _ := t.consumeMData | break
    let all := atoms q
    let some a := all.find? fun a =>
        a.isAppOfArity ``Zig.Assn.lift 1 || (a.isAppOfArity ``Zig.Assn.ex 2 && !ws.isEmpty)
      | break
    let some i := all.idxOf? a | break
    let target ← Term.exprToSyntax
      (mkApp2 (mkConst ``Zig.Assn.sep) a (sepOf (all.eraseIdx! i)))
    let [k] ← evalTacticAt (← `(tactic|
        refine Zig.assn_cast (P := $target) (by first | rfl | sep_normalize) ?_)) g
      | throwError "sep: unexpected goals"
    if a.isAppOfArity ``Zig.Assn.ex 2 then
      let w :: rest := ws | break
      ws := rest
      let [k'] ← evalTacticAt (← `(tactic| refine Zig.ex_sep_intro $w ?_)) k
        | throwError "sep: unexpected goals"
      setGoals [k']
      evalTactic (← `(tactic| try dsimp only))
    else
      let [hφ, k'] ← evalTacticAt (← `(tactic| refine Zig.sep_lift.mpr ⟨?_, ?_⟩)) k
        | throwError "sep: unexpected goals"
      if (← observing? (evalTacticAt (← `(tactic| first | rfl | assumption | trivial)) hφ)).isNone then
        pure := pure.push hφ
      setGoals [k']
  evalTactic (← `(tactic| first | exact $hp | (sep_normalize at $hp:ident ⊢; exact $hp)))
  setGoals ((← getGoals) ++ pure.toList)

end Zig.SepStep

open Lean.Parser.Tactic in
/-- One proof-producing step of symbolic execution (module doc). -/
syntax (name := sepStep) "sep_step"
  (" [" (simpStar <|> simpErase <|> simpLemma),* "]")? (" using " term)? : tactic

open Lean.Parser.Tactic in
/-- `sep_step` repeated while a built-in load/store rule or one of the given rules applies. -/
syntax (name := sepSteps) "sep_steps"
  (" [" (simpStar <|> simpErase <|> simpLemma),* "]")? (" using " term,+)? : tactic

/-- Move `⌜φ⌝` facts and `Assn.ex` witnesses of the precondition into the context. -/
syntax (name := sepIntro) "sep_intro" (ppSpace colGt ident)* : tactic

/-- Close `Triple P (pure v) Q` (`sep_close` with the given witnesses), or reduce it to
`∀ h, P h → Q v h`. -/
syntax (name := sepRet) "sep_ret" (ppSpace colGt term:max)* : tactic

/-- Prove `Q h` from `hp : P h`: witnesses for the existentials of `Q`, pure atoms as goals,
spatial atoms by AC normalization. -/
syntax (name := sepClose) "sep_close " ident (ppSpace colGt term:max)* : tactic

/-- Split `arr p xs` in the precondition at `k` into its prefix and suffix. -/
syntax (name := sepSplit) "sep_split " term:max ppSpace term:max : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| sep_step $[[$facts,*]]? $[using $rule]?) =>
    Zig.SepStep.step rule (facts.map (·.getElems.map (·.raw)) |>.getD #[])
  | `(tactic| sep_steps $[[$facts,*]]? $[using $rules,*]?) => do
    let facts := facts.map (·.getElems.map (·.raw)) |>.getD #[]
    let rules := (rules.map (·.getElems) |>.getD #[]).toList.map some
    repeat
      if (← getGoals).isEmpty then break
      let mut progress := false
      for rule in none :: rules do
        if (← observing? (Zig.SepStep.step rule facts)).isSome then
          progress := true
          break
      unless progress do break
  | `(tactic| sep_intro $names*) => Zig.SepStep.intro (names.map (·.getId)).toList
  | `(tactic| sep_ret $ws*) => withMainContext do
    let (kind, _, _, _) ← Zig.SepStep.goalTriple
    evalTactic (← `(tactic| refine $(Zig.SepStep.lemmaId kind "ret_of") ?_))
    let g ← getMainGoal
    let ws := ws.toList
    let entail : TacticM Unit := do
      let hp := mkIdent `hp
      evalTactic (← `(tactic| intro _ $hp:ident))
      Zig.SepStep.close hp ws
    if (← observing? entail).isNone then
      setGoals [g]
      evalTactic (← `(tactic| try dsimp only))
  | `(tactic| sep_close $hp $ws*) => withMainContext do
    Zig.SepStep.close hp ws.toList
  | `(tactic| sep_split $p $k) => withMainContext do
    let (kind, P, _, _) ← Zig.SepStep.goalTriple
    let p ← Term.elabTerm p (mkConst ``Zig.Ptr)
    let some a ← (Zig.SepStep.atoms P).findM? fun a =>
        return a.isAppOfArity ``Zig.arr 4 && (← isDefEq a.getAppArgs[2]! p)
      | throwError "sep_split: the precondition has no `arr` at{indentExpr p}"
    Zig.SepStep.focus kind P #[a]
    let goals ← evalTacticAt (← `(tactic|
      refine $(Zig.SepStep.lemmaId kind "arr_split_pre") (k := $k) (by decide) ?_ ?_))
      (← getMainGoal)
    match goals with
    | [hk, t] => setGoals (t :: (← Zig.SepStep.tryBound hk))
    | gs => setGoals gs
