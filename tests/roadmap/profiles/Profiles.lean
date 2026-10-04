import Air2Lean.Main

/-! Run only after the root serialized build. No compiler is launched by this driver. -/
open Air2Lean Lean

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

#eval do
  let current ← IO.FS.readFile "tests/roadmap/profiles/current.json"
  let legacy ← IO.FS.readFile "tests/roadmap/profiles/legacy.json"
  let p ← match Raw.parseFile current with
    | .ok f => pure f.profile
    | .error e => throw (IO.userError e)
  let l ← match Raw.parseFile legacy with
    | .ok f => pure f.profile
    | .error e => throw (IO.userError e)
  require (p.name == BuildProfile.currentName) "wrong current profile name"
  require (l.name == BuildProfile.legacyName) "wrong legacy profile name"
  require l.errorTracing.isNone "legacy error tracing claimed verified"
  require (BuildProfile.checkProgram #[p, p] |>.toOption.isSome) "identical profiles rejected"
  require (BuildProfile.checkProgram #[p, l] |>.toOption.isNone) "mixed profiles accepted"
  require (BuildProfile.checkProgram #[p] (some BuildProfile.legacyName) |>.toOption.isNone)
    "profile selection mismatch accepted"
  require (BuildProfile.checkProgram #[] |>.toOption.isNone) "empty profiles accepted"
  let good := ["air", "-o", "out.lean", "--namespace", "Tests"]
  require (parseArgs (good ++ ["--profile", BuildProfile.currentName]) |>.toOption.isSome)
    "valid --profile rejected"
  require (parseArgs (good ++ ["--profile", "unqualified"]) |>.toOption.isNone)
    "invalid --profile accepted"
  IO.println "profile parser and selection checks passed"
