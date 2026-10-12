import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.AutoPrim
import ZigLean.Sep.Full.AutoClaims
import ZigLean.Sep.Full.Const
import ZigLean.Sep.Full.Arr
import ZigLean.Sep.Full.Typed
import ZigLean.Sep.Full.Try
import ZigLean.Sep.Full.Region
import ZigLean.Sep.Full.Wrappers
import ZigLean.Sep.Full.Block
import ZigLean.Sep.Full.Malloc
import ZigLean.Sep.Full.Mmap
import ZigLean.Sep.Full.Loop
import ZigLean.Sep.Full.Init
import ZigLean.Sep.Full.Witness
import ZigLean.VC.Rules

/-!
# The proof framework in one import (`docs/proof-framework.md`)

A proof of generated code in the full-state logic imports this module and nothing else from the
library: `fsym` (`Auto`) with every `@[fsym]`, `@[fsym_facts]`, `@[fsym_plan]`, `@[fsym_drop]` and
provider rule of the library (primitive commands, byte-range claims, `const` globals, arrays,
typed values and fields, error unions and optionals through pointers, regions, the
`std.mem.Allocator` wrappers, blocks, the page-mapping primitives, the primitive `Result`
contracts of `VC/Rules`), the loop and recursion rules (`Loop`), the start memory (`Init`) and the
full-state witnesses of claims (`Witness`).

A module of the library that declares a rule is imported here (directly or through another);
`tests/roadmap/one-logic/check.sh` fails otherwise, so a proof never misses a rule because of
its imports. Tooling built on `fsym` (`vc_gen` in `VC/Extract`, `unroll_solo` in `Full/Unroll`)
is not part of the umbrella.
-/
