import Lean

/-!
# Registries of the full-state symbolic executor (`fsym`, `docs/proof-automation.md`)

* `@[fsym]` marks a **step rule**: a theorem whose conclusion is a triple about one command `c`:
  total (`FTotalTriple P c Q`, every backend) or partial (`FTriple P c Q`: `FLogic.partial` and the
  concurrent `CTriple` backend, where it executes `ConcM.liftMem c`), or a thread's
  (`FTTotalTriple`, `FTTriple`: the thread backend, where the sequential ones apply too, with
  the locality of their command), or a `WP` of a thread's run in a protocol (`P.WP t c Q G m n`:
  only in a `WP` walk, keyed by the head of `c` through `StateT.run`). `fsym` tries the
  rules whose command unifies with the command it executes; the rule's hypotheses become side
  goals (blocks, providers, arithmetic), solved by `fsym`'s solvers.
* `@[fsym_atom]` marks an assertion constant that `fsym` must not unfold in a precondition
  (library atoms such as `Junk`; a user may mark an opaque representation predicate).
* `@[fsym_provider]` marks a **provider lemma** `AddrOf b A X`/`Reaches b k X` of an atom `X`
  (the address or the extent of the block of memory that `X` owns), or of another provider
  kind (a constant `K` with `K.of_within`: `Live`, `Active`, `ReadsAt`, `ThreadLocal`,
  `OwnsPtr`, …): side goals of rules.
* `@[fsym_facts]` marks a **facts lemma** `AtomFacts X φ` or `MemFacts X φ`: the pure facts `φ`
  that an assertion `X` implies (the block, offset and alignment of an owned pointer), or that
  it implies in a memory that holds it (`X` an atom or a pair `X₁ ⋆ X₂`). `fsym` adds the facts of the
  precondition's atoms when it needs more facts (a rule's side goal, an `if`, a panic).
* `@[fsym_plan]` marks a **range law** `X … lo m … ⋆ X … m hi … = X … lo hi …` (byte-range
  claims, `bclaim_split`): when `fsym` closes an update `EUpd P Q`, after regions and shares, it
  carves each range atom of `Q` out of a state atom of the same head that covers it, joining
  adjacent state atoms first when none does. The laws are data (a declared table checked when
  the attribute is added), not code `fsym` evaluates. A head with a law is an atom (never unfolded).
* `@[fsym_drop]` marks a **drop lemma** `EUpd (X ⋆ R) R`: an atom `X` of the state that the
  postcondition does not use is forgotten (knowledge, claims).
* `@[fsym_view]` marks a **view lemma** `EUpd X Y`: the atom `X` seen as `Y` (an atomic word
  as a region of plain bytes; bytes with their facts as a typed view). When the planner does
  not find an atom of the head that `Y` provides (a rule's precondition, a return's
  postcondition), `fsym` applies the view to the state atoms of that block and walks on.
* `@[fsym_inv]` marks a **loop's invariant** `B.inv`, its measure `B.meas` and its exit post
  `B.post`, definitions next to the loop body `B` (P09-E4): at `(Zig.loop (B …) again).run s`
  with no rule, `fsym` applies its backend's loop rule with them and walks the body's step. A
  body registers a second invariant for the credit mode (`B.credits.inv … s n` with its exact
  count `n`, and `B.credits.post`; `LoopMode`): `fsym` takes it when the state at the loop holds
  credits and no plain mode, with the backend's counted loop rule (`loop_exact`).
* `fsym_norm` is the simp set that normalizes generated programs (pushes `StateT.run` through the
  generated `MM` layer, flattens binds, folds trivial results).
* `fsym_arith` is the simp set that prepares arithmetic side goals for `omega` (`Ptr` offsets,
  `BitVec` values, casts).
-/

namespace Zig.Full.Auto

open Lean

/-- The step rules (`@[fsym]`), in declaration order. -/
initialize fsymRuleExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s n => s.push n
    initial := #[]
  }

initialize registerBuiltinAttribute {
  name := `fsym
  descr := "a step rule of the full-state symbolic executor `fsym`"
  add := fun decl _ kind => fsymRuleExt.add decl kind
}

/-- Assertion constants that `fsym` keeps opaque in preconditions (also imported ones: the
library's `Junk` is tagged where `fsym`'s rules are). -/
initialize fsymAtomExt : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s n => s.insert n
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `fsym_atom
  descr := "an assertion that `fsym` keeps opaque"
  add := fun decl _ kind => fsymAtomExt.add decl kind
}

/-- The facts lemmas (`@[fsym_facts]`), in declaration order. -/
initialize fsymFactsExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s n => s.push n
    initial := #[]
  }

initialize registerBuiltinAttribute {
  name := `fsym_facts
  descr := "a facts lemma `AtomFacts X φ` of the full-state symbolic executor `fsym`"
  add := fun decl _ kind => fsymFactsExt.add decl kind
}

/-- The run lemmas (`@[fsym_run]`): a premise is a step's run, `(x.run m).run = some (.ok (a, m'))`,
the conclusion facts of its value and of the memories (`m'.atomics = m.atomics`); in declaration
order. -/
initialize fsymRunExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s n => s.push n
    initial := #[]
  }

initialize registerBuiltinAttribute {
  name := `fsym_run
  descr := "a run lemma of the full-state symbolic executor `fsym`: facts of a step's run"
  add := fun decl _ kind => fsymRunExt.add decl kind
}

/-- The provider lemmas (`@[fsym_provider]`: `AddrOf b A X`, `Reaches b k X` of an atom `X`), in
declaration order. -/
initialize fsymProviderExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s n => s.push n
    initial := #[]
  }

initialize registerBuiltinAttribute {
  name := `fsym_provider
  descr := "a provider lemma `AddrOf b A X` or `Reaches b k X` of the full-state symbolic executor `fsym`"
  add := fun decl _ kind => fsymProviderExt.add decl kind
}

/-- A **range law** (`@[fsym_plan]`): the theorem `decl` states
`X … lo m … ⋆ X … m hi … = X … lo hi …` for the assertion constant `head`, whose range bounds are
its arguments `lo` and `hi` (positions); its other hypotheses are side goals (bounds). -/
structure RangeLaw where
  decl : Name
  head : Name
  lo : Nat
  hi : Nat
  deriving Inhabited

open Meta in
/-- The range law of `decl`, or an error that says why its statement is not one. -/
def RangeLaw.ofDecl (decl : Name) : MetaM RangeLaw := do
  let info ← getConstInfo decl
  forallTelescopeReducing info.type fun _ concl => do
    let fail {α} (why : MessageData) : MetaM α :=
      throwError "@[fsym_plan] {decl}: {why}; expected a range law `X … lo m … ⋆ X … m hi … = X … lo hi …`"
    let some (_, lhs, c) := concl.eq? | fail "the conclusion is not an equation"
    unless lhs.isAppOfArity `Zig.Full.FAssn.sep 2 do fail "the left side is not a separating conjunction"
    let a := lhs.appFn!.appArg!
    let b := lhs.appArg!
    let some head := c.getAppFn.constName? | fail "the right side is not a constant application"
    let n := c.getAppNumArgs
    unless a.isAppOfArity head n && b.isAppOfArity head n do
      fail "the left side's atoms are not applications of the right side's constant"
    let (as, bs, cs) := (a.getAppArgs, b.getAppArgs, c.getAppArgs)
    let diff (xs : Array Expr) := (List.range n).filter fun i => xs[i]! != cs[i]!
    let ([hi], [lo]) := (diff as, diff bs) | fail "the atoms differ from the right side in more than one bound"
    unless lo != hi && as[hi]! == bs[lo]! && as[hi]!.isFVar && cs[lo]!.isFVar && cs[hi]!.isFVar do
      fail "the bounds are not variables `lo m hi` split at `m`"
    return { decl, head, lo, hi }

/-- The range laws (`@[fsym_plan]`), in declaration order: the planner's declared table. -/
initialize fsymPlanExt : SimpleScopedEnvExtension RangeLaw (Array RangeLaw) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s n => s.push n
    initial := #[]
  }

initialize registerBuiltinAttribute {
  name := `fsym_plan
  descr := "a range law `X lo m ⋆ X m hi = X lo hi` that the full-state symbolic executor `fsym` plans by"
  add := fun decl _ kind => do
    let law ← (RangeLaw.ofDecl decl).run' {} {}
    if let some l := (fsymPlanExt.getState (← getEnv)).find? (·.head == law.head) then
      throwError "@[fsym_plan] {decl}: `{law.head}` already has the range law {l.decl}"
    fsymPlanExt.add law kind
}

/-- The drop lemmas (`@[fsym_drop]`: `EUpd (X ⋆ R) R`), in declaration order. -/
initialize fsymDropExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s n => s.push n
    initial := #[]
  }

initialize registerBuiltinAttribute {
  name := `fsym_drop
  descr := "a drop lemma `EUpd (X ⋆ R) R` of the full-state symbolic executor `fsym`"
  add := fun decl _ kind => fsymDropExt.add decl kind
}

/-- The view lemmas (`@[fsym_view]`: `EUpd X Y` of one atom `X`), in declaration order. -/
initialize fsymViewExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s n => s.push n
    initial := #[]
  }

initialize registerBuiltinAttribute {
  name := `fsym_view
  descr := "a view lemma `EUpd X Y` (one atom `X` seen as `Y`) of the full-state symbolic executor `fsym`"
  add := fun decl _ kind => do
    let ty := (← getConstInfo decl).type
    let ok : Bool ← Meta.MetaM.run' (Meta.forallTelescope ty fun _ concl => do
      unless concl.isAppOfArity `Zig.Full.EUpd 2 do return false
      let X := concl.appFn!.appArg!
      return !(X.isAppOfArity `Zig.Full.FAssn.sep 2 || X.isConstOf `Zig.Full.FAssn.emp))
    unless ok do
      throwError "@[fsym_view] {decl}: expected a view lemma `EUpd X Y` of one atom `X`"
    fsymViewExt.add decl kind
}

/-- The parts of a loop body `B` that `@[fsym_inv]` registers: `B.inv`, `B.meas` and `B.post`. -/
def loopInvParts : List String := ["inv", "meas", "post"]

/-- **The mode of a registered loop invariant** (P09, maintainer 2026-11-24): a loop body registers
one invariant per mode, and `fsym` takes the one of the walk's mode.
* `plain`: `B.inv`, `B.meas`, `B.post`, for a walk that bounds no steps (the backend's loop rule
  with a measure, or the partial one).
* `credits`: `B.credits.inv` and `B.credits.post`, for a walk that pays its steps with credits
  (the state at the loop holds `credits` and no plain mode). The invariant's last parameter is
  the exact count: the body runs left before the last one (`B.credits.inv … s n`). The rule is
  the backend's counted loop rule (`loop_exact`), which adds the credits and the receipts, so the
  invariant names neither. -/
inductive LoopMode where
  | plain
  | credits
  deriving BEq, Hashable, Inhabited, Repr

/-- The name of the part `part` (`inv`, `meas`, `post`) of the loop body `body` in a mode. -/
def LoopMode.name (mode : LoopMode) (body : Name) (part : String) : Name :=
  match mode with
  | .plain => body.str part
  | .credits => (body.str "credits").str part

/-- A registered name read as `(B, mode, part)`: `B.credits.part` is the credit mode's part of `B`
unless `B.credits` is itself a declaration (a loop body of that name: its plain-mode part). -/
def loopInvKey? (env : Environment) : Name → Option (Name × LoopMode × String)
  | .str (.str b "credits") part =>
    if env.contains (b.str "credits") then some (b.str "credits", .plain, part)
    else some (b, .credits, part)
  | .str b part => some (b, .plain, part)
  | _ => none

/-- The parameter of `B.inv` (and `B.meas`, `B.post`) that is the locals at the loop's entry. -/
def loopEntryParam : Name := `s0

open Meta in
/-- The parameters `xs` of `B.inv` end in a ghost measure (`B.inv … s n`): a last parameter of
type `Nat` after the locals, of a type `σ` other than `Nat` (`none`: locals that depend on the
body's parameters). Locals of type `Nat` have no ghost measure: their invariant's last parameter
is the locals. Only the signature's shape decides, so the registration (`checkLoopInv`, which then
checks the locals' parameter) and the loop's use (`registeredLoop?`, with the instantiated `σ`)
read an invariant alike. -/
def isGhostInv (xs : Array Expr) (σ? : Option Expr) : MetaM Bool := do
  unless xs.size ≥ 2 do return false
  unless ← isDefEq (← inferType xs.back!) (mkConst ``Nat) do return false
  let some σ := σ? | return true
  return !(← isDefEq σ (mkConst ``Nat))

open Meta in
/-- Check that `decl` is `B.inv`, `B.meas` or `B.post` of a loop body `B` (a definition of a
`StateT σ m ε` program, `Zig.MM σ ε` or `CM Tgt σ ε`), or say why not: a definition without
universe parameters whose parameters are explicit and named apart (`fsym` matches them by name with
`B.inv`'s), whose last parameter is the loop's locals (`s : σ`; `r : ε × σ` for the post; for
the invariant, the locals may be followed by a ghost measure `n : Nat`), whose
parameter of the locals at the loop's entry is named `s0` and whose value is an `FAssn` (a `Nat`
for the measure). In the credit mode (`B.credits.inv`, `B.credits.post`) the invariant ends in
the exact count `n : Nat` and there is no measure. -/
def checkLoopInv (decl : Name) : MetaM Unit := do
  let fail {α} (why : MessageData) : MetaM α :=
    throwError "@[fsym_inv] {decl}: {why}; expected the definition `B.inv`, `B.meas` or `B.post` of \
      a loop body `B`"
  let some (body, mode, last) := loopInvKey? (← getEnv) decl
    | fail "not a name `B.inv`, `B.meas` or `B.post`"
  unless last ∈ loopInvParts do fail "its name does not end in `inv`, `meas` or `post`"
  let credits := mode == .credits
  if credits && last == "meas" then
    fail m!"the credit mode has no measure (`{body}.credits.inv … s n` ends in its exact count `n`)"
  let some (.defnInfo b) := (← getEnv).find? body
    | fail m!"`{body}` is not a definition (declared before its invariant)"
  let some (.defnInfo d) := (← getEnv).find? decl | fail "not a definition"
  unless d.levelParams.isEmpty do fail "a definition with universe parameters"
  -- the locals `σ` and the exit `ε` of the body's program
  -- (`none` when they depend on the body's parameters: `fsym` checks the types where it applies
  -- the loop rule)
  let types? ← forallTelescope b.type fun ys ty => do
    let ty ← whnfR ty
    unless ty.isAppOfArity ``StateT 3 do fail m!"`{body}` is not a program over locals"
    let (σ, ε) := (ty.getArg! 0, ty.getArg! 2)
    let dep (e : Expr) := e.hasAnyFVar fun v => ys.any (·.fvarId! == v)
    return if dep σ || dep ε then none else some (σ, ε)
  forallTelescope d.type fun xs res => do
    -- a ghost measure (`B.inv … s n`: a last parameter `n : Nat` after the locals; the loop rule
    -- is `loop_ghost_ex`, so there is no `B.meas`)
    let ghost ← if last == "inv" then isGhostInv xs (types?.map (·.1)) else pure false
    if credits && last == "inv" && !ghost then
      fail m!"a credit-mode invariant ends in its exact count (`{body}.credits.inv … s n`, with \
        `n : Nat` the body runs left before the last one, after the locals)"
    let xs := if ghost then xs.pop else xs
    let some s := xs.back? | fail "no parameter for the loop's locals"
    if let some (σ, ε) := types? then
      let loc ← if last == "post" then mkAppM ``Prod #[ε, σ] else pure σ
      unless ← isDefEq (← inferType s) loc do fail m!"its last parameter is not of type {loc}"
    let env ← getEnv
    let locStruct := types?.any fun (σ, _) => σ.getAppFn.constName?.any (isStructure env)
    let mut seen : NameSet := {}
    for h : i in [0:xs.size] do
      let l ← xs[i].fvarId!.getDecl
      unless l.binderInfo.isExplicit do fail m!"the parameter {l.userName} is not explicit"
      if l.userName.hasMacroScopes || seen.contains l.userName then
        fail m!"the parameter {l.userName} has no name of its own"
      seen := seen.insert l.userName
      -- the locals at the entry: the parameter `s0` (`fsym` binds it by name), and no other of a
      -- locals structure's type
      if let some (σ, _) := types? then
        if i + 1 < xs.size then
          let isLoc ← isDefEq l.type σ
          if l.userName == loopEntryParam && !isLoc then
            fail m!"its parameter {loopEntryParam} is not of type {σ}"
          if l.userName != loopEntryParam && isLoc && locStruct then
            fail m!"its parameter {l.userName} of the locals' type is not named {loopEntryParam} \
              (the locals at the loop's entry)"
    let want := if last == "meas" then mkConst ``Nat else mkConst `Zig.Full.FAssn
    unless ← isDefEq res want do fail m!"its value is not of type {want}"

/-- The loops' invariants (`@[fsym_inv]`): at a loop with no rule, `fsym` applies its backend's
loop rule with them (`walkCore`). -/
initialize fsymInvExt :
    SimpleScopedEnvExtension ((Name × LoopMode × String) × Name)
      (PersistentHashMap (Name × LoopMode × String) Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s (key, decl) => s.insert key decl
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `fsym_inv
  descr := "a loop's invariant `B.inv`, measure `B.meas` or exit post `B.post` (loop body `B`) for \
    the full-state symbolic executor `fsym`"
  add := fun decl _ kind => do
    (checkLoopInv decl).run' {} {}
    -- (keyed as `checkLoopInv` read the name, once: a later declaration does not re-read it)
    let some key := loopInvKey? (← getEnv) decl
      | throwError "@[fsym_inv] {decl}: not a name `B.inv`, `B.meas` or `B.post`"
    fsymInvExt.add (key, decl) kind
}

/-- The registered invariant, measure and exit post of the loop body `body` in the mode `mode`
(`@[fsym_inv]`: the registry is keyed by the body, the mode and the part, as `loopInvKey?` read
the name at its registration). -/
def loopInvOf (env : Environment) (body : Name) (mode : LoopMode := .plain) :
    Option Name × Option Name × Option Name :=
  let s := fsymInvExt.getState env
  let get (part : String) := s.find? (body, mode, part)
  (get "inv", get "meas", get "post")

/-- `c` is an `@[fsym_atom]` or the head of a range law (planned by its law, never unfolded). -/
def isFsymAtom (env : Environment) (c : Name) : Bool :=
  (fsymAtomExt.getState env).contains c || (fsymPlanExt.getState env).any (·.head == c)

/-- A constant of the library or of Lean (not generated code, not the user's). The simprocs ask
this for every application, so it indexes `env.header.modules` directly: `moduleNames` would
build the array of all imported module names on each call. -/
def isLibraryConst (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some idx => [`ZigLean, `Init, `Std, `Lean].contains env.header.modules[idx.toNat]!.module.getRoot
  | none => false

/-- The user definitions the simprocs evaluated (`evalUserCtor`, `reduceUserProj`), by `fsym` run
(the option `fsym.run`) and term; `withRunCaches` drops a run's entries. -/
initialize fsymEvalCache : IO.Ref (Std.HashMap (Nat × Expr) Expr) ← IO.mkRef {}

open Meta in
/-- `whnf` at default transparency, cached for the current `fsym` run (a term without
metavariables: its value does not change within the run). -/
def whnfDCached (e : Expr) : MetaM Expr := do
  let id := (← getOptions).get `fsym.run (0 : Nat)
  if id == 0 || e.hasMVar then return ← withTransparency .default (whnf e)
  if let some v := (← fsymEvalCache.get).get? (id, e) then return v
  let v ← withTransparency .default (whnf e)
  fsymEvalCache.modify (·.insert (id, e) v)
  return v

open Meta in
/-- The imports' environment, for the kernel's work on a term `e` without locals that uses only
imported constants (a reduction `Kernel.whnf`, a check): there the kernel does what it does in the
current environment. The kernel reads an environment only once it is checked
(`Environment.toKernelEnv` waits for `checked`), and the current one is checked only when every
earlier theorem of the file is (`Elab.async`): the kernel's work in a proof would wait for all of
them, and the file's theorems would run one after the other (the pattern of
`Lean.Meta.evalExprCore`). `none`: the current environment. -/
def importEnvFor? (e : Expr) : MetaM (Option Environment) := do
  let env ← getEnv
  if e.hasFVar || (e.find? fun c => c.isConst && !env.isImportedConst c.constName!).isSome then
    return none
  return env.importEnv?

/-- The kernel accepts `pf` as a proof of `t` in `env` (a theorem checked and dropped), within the
options' heartbeat and recursion limits, as `addDecl` checks a declaration. -/
def kernelChecks (env : Environment) (t pf : Expr) : CoreM Bool := do
  let opts ← getOptions
  let decl : Declaration := .thmDecl { name := `_fsym_kernel_check, type := t, value := pf,
                         levelParams := (collectLevelParams {} (mkApp t pf)).params.toList }
  return env.toKernelEnv.addDeclCore (Core.getMaxHeartbeats opts).toUSize
    (maxRecDepth.get opts).toUSize decl (← read).cancelTk? matches .ok _

end Zig.Full.Auto

register_simp_attr fsym_norm
register_simp_attr fsym_arith
