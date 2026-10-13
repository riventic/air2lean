import AllocArena.ArenaMacos
import AllocArena.Core

/-!
# The stock `ArenaAllocator` on aarch64-macos: `free`, `resize` and `remap` against `FAllocSpec`

The statements of `ArenaSpec.lean` for the aarch64-macos translation (`AllocArena/ArenaMacos.lean`),
proved by the same tactics (`AllocArena.Core`).
-/

namespace AllocArena.ArenaSpecMacos

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocArena.Core AllocArena.ArenaMacos

arena_spec_statements

end AllocArena.ArenaSpecMacos

#print axioms AllocArena.ArenaSpecMacos.free_spec
#print axioms AllocArena.ArenaSpecMacos.resize_spec
#print axioms AllocArena.ArenaSpecMacos.remap_spec
