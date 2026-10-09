import Air2Lean
import Air2Lean.Check

open Air2Lean

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-- The checked-in public C01 export supplies an actual normalized config shape.
Only this modeled call's config is changed; no compiler or source is substituted. -/
private def configVariant (f : Func) (value : Int) (allocator : Bool := false)
    (runtime : Bool := false) : Func :=
  { f with body := f.body.map fun i =>
    match i.op with
    | .call (.func name nr target) args =>
      if threadFn? name == some .spawn then
        match (args[0]? : Option Val) with
        | some (.agg ty fields) =>
          let fields := match fields[0]!, fields[1]! with
            | .int stackTy _, .optNull allocatorTy =>
              #[Val.int stackTy value, if allocator then Val.undef allocatorTy else Val.optNull allocatorTy]
            | _, _ => fields
          let config := if runtime then Val.inst 0 else Val.agg ty fields
          { i with op := .call (.func name nr target) (args.set! 0 config) }
        | _ => i
      else i
    | _ => i }

def main : IO Unit := do
  let text ← IO.FS.readFile "tests/roadmap/thread-tuples/air/0.16.0/thread_tuples.empty.json"
  let f ← match (do let f ← normalize (← Raw.parseFile text); check f; pure f : Except String Func) with
    | .ok f => pure f
    | .error e => throw (IO.userError e)
  require (f.allInsts.any fun i => match i.op with
    | .call (.func name ..) _ => threadFn? name == some .spawn
    | _ => false) "boundary fixture has no spawn call"
  for version in #["0.14.1", "0.15.2", "0.16.0", "0.17.0"] do
    let f := { f with zigVersion := version }
    for stack in #[(1048576 : Int), 16777216] do
      require ((checkFallibleSpawnCalls #[configVariant f stack]).toOption.isSome)
        s!"audited stack request rejected: {version}, {stack}"
    for stack in #[(0 : Int), -1, 16384, 1048577, 33554432, 18446744073709551615] do
      require ((checkFallibleSpawnCalls #[configVariant f stack]).toOption.isNone)
        s!"unsupported stack request accepted: {version}, {stack}"
    require ((checkFallibleSpawnCalls #[configVariant f 1048576 true]).toOption.isNone)
      "custom allocator accepted"
    require ((checkFallibleSpawnCalls #[configVariant f 1048576 false true]).toOption.isNone)
      "runtime config accepted"
  -- 0.17.0's `Thread.spawn`/`SpawnConfig` are unchanged and audited (docs/std-models.md).
  require ((checkFallibleSpawnCalls #[{ f with zigVersion := "0.18.0" }]).toOption.isNone)
    "unaudited version accepted"
  IO.println "audited spawn resource boundary passed"
