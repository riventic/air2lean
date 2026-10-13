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

/-- `c` is an `@[fsym_atom]` or the head of a range law (planned by its law, never unfolded). -/
def isFsymAtom (env : Environment) (c : Name) : Bool :=
  (fsymAtomExt.getState env).contains c || (fsymPlanExt.getState env).any (·.head == c)

end Zig.Full.Auto

register_simp_attr fsym_norm
register_simp_attr fsym_arith
