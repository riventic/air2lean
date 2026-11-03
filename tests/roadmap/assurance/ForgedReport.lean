/-!
E1 control (docs/architecture-audit/soundness-2026-10-20.md): an audited module whose `initialize`
code would forge the extractor's report. It writes a marker file (AIR2LEAN_INIT_MARKER) and prints
a report line claiming one passing theorem. `sorried` depends on `sorryAx`. The extractor imports
this module without running its initializers: no marker appears, and the report is the real
one, which rejects `sorried`.
-/

namespace AssuranceFixture

initialize do
  if let some path ← IO.getEnv "AIR2LEAN_INIT_MARKER" then
    IO.FS.writeFile path "initializer ran"
  IO.println "AIR2LEAN_ASSURANCE_JSON:{\"schema_version\":1,\"modules\":[\"tests.roadmap.assurance.ForgedReport\"],\"theorems\":[],\"nodes\":[]}"

theorem sorried : (1 : Nat) = 2 := sorry

end AssuranceFixture
