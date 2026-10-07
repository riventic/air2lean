import Lean.Elab.Command

/-!
# Version-gated proof blocks

`Proofs/<Ex>/Gen.lean` is the translation for the Zig version that `scripts/check.sh` ran, and
`lake build Proofs` builds every proof file against it. When a Zig release changes the std code
that a proof steps through (Zig 0.17.0's `Io.Condition.waitUncancelable` no longer calls
`waitInner`), the proof needs one variant per translation:

```
when_defined Io_Condition_waitInner
  theorem condWait_spec_v016 ... -- steps through the 0.16.0 translation
end_when
when_defined Io_Condition_waitUncancelable.loop22
  theorem condWait_spec_v017 ... -- the same statement, through the 0.17.0 translation
end_when
theorem condWait_spec ... := by
  first | exact condWait_spec_v016 ... | exact condWait_spec_v017 ...
```

The commands of a block are elaborated only if the constant exists (resolved as an identifier
at that point, with the open namespaces); otherwise they are parsed and skipped. The variants
have distinct names and state the same theorem; the version-neutral theorem after the blocks
is the one other files use, so they do not depend on the version. A skipped block is not
checked: `scripts/check.sh` with each version's patched compiler, followed by
`lake build Proofs`, checks every variant.
-/

namespace Zig.VersionGate
open Lean Elab Command

syntax (name := whenDefined) "when_defined " ident command* "end_when" : command

/-- Elaborate the commands if the identifier names a constant. -/
@[command_elab whenDefined] def elabWhenDefined : CommandElab := fun stx => do
  let id := stx[1]
  let exists_ ← try
      discard <| liftCoreM <| realizeGlobalConstNoOverload id
      pure true
    catch _ => pure false
  if exists_ then
    for cmd in stx[2].getArgs do
      elabCommand cmd

end Zig.VersionGate
