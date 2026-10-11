import Lean

/-!
# Registries of the full-state symbolic executor (`fsym`, `docs/proof-automation.md`)

* `@[fsym]` marks a **step rule**: a theorem whose conclusion is a triple
  (`FTotalTriple P c Q`, `FTriple P c Q`, `CTriple P x Q`) about one command `c`. `fsym` tries the
  rules whose command unifies with the command it executes; the rule's hypotheses become side
  goals (blocks, providers, arithmetic), solved by `fsym`'s solvers.
* `@[fsym_atom]` marks an assertion constant that `fsym` must not unfold in a precondition
  (library atoms such as `junk`; a user may mark an opaque representation predicate).
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

/-- Assertion constants that `fsym` keeps opaque in preconditions. -/
initialize fsymAtomAttr : TagAttribute ←
  registerTagAttribute `fsym_atom "an assertion that `fsym` keeps opaque"

end Zig.Full.Auto

register_simp_attr fsym_norm
register_simp_attr fsym_arith
