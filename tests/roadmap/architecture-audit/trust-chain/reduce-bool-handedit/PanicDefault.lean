import ZigLean.Mem.Basic

/-! Counterexample support (docs/architecture-audit/trust-chain.md, finding 5). `Emit.lean`
writes `(panic! "air2lean: ...")` in arms it assumes unreachable. In the kernel `panic!` is
`default`, and `default` of the generated function monads is a *successful* return of the
default value with the state unchanged, not a failure or divergence. So an accepted input that
reaches such an arm gets a defined, provable result. -/

example (s : Unit) :
    ((panic! "air2lean: arithmetic @reduce of a bool vector" : Zig.M Unit Bool).run s).run =
      some (.ok (false, s)) := by
  rfl

example (s : Unit) (m : Zig.Mem) :
    ((((panic! "air2lean: arithmetic @reduce of a bool vector" : Zig.MM Unit Bool).run s).run m).run) =
      some (.ok ((false, s), m)) := by
  rfl
