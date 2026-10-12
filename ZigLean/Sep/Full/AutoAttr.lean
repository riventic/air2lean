import Lean

/-!
# Registries of the full-state symbolic executor (`fsym`, `docs/proof-automation.md`)

* `@[fsym]` marks a **step rule**: a theorem whose conclusion is a triple about one command `c`:
  total (`FTotalTriple P c Q`, every backend) or partial (`FTriple P c Q`: `FLogic.partial` and the
  concurrent `CTriple` backend, where it executes `ConcM.liftMem c`). `fsym` tries the
  rules whose command unifies with the command it executes; the rule's hypotheses become side
  goals (blocks, providers, arithmetic), solved by `fsym`'s solvers.
* `@[fsym_atom]` marks an assertion constant that `fsym` must not unfold in a precondition
  (library atoms such as `Junk`; a user may mark an opaque representation predicate).
* `@[fsym_facts]` marks a **facts lemma** `AtomFacts X φ`: the pure facts `φ` that an assertion
  `X` implies (the block, offset and alignment of an owned pointer). `fsym` adds the facts of the
  precondition's atoms when it needs more facts (a rule's side goal, an `if`, a panic).
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

/-- `c` is an `@[fsym_atom]`. -/
def isFsymAtom (env : Environment) (c : Name) : Bool := (fsymAtomExt.getState env).contains c

end Zig.Full.Auto

register_simp_attr fsym_norm
register_simp_attr fsym_arith
