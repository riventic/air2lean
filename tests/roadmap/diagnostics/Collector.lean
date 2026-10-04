import Air2Lean.Diagnose

/-! Evaluation regressions for the actual collector, run only by the root guard.
These tests inspect diagnostic behavior; they establish no program proof status. -/
open Air2Lean Air2Lean.Diagnostics

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def mkFunc (name : String) (body : Array Inst := #[]) : Func := {
  zigVersion := "0.16.0", name, params := #[3], ret := 1,
  types := #[.int false 32, .void, .noreturn, .ptr "one" false 0],
  layouts := Array.replicate 4 {}, globals := #[], body }

private def collectorChecks : IO Unit := do
  let bad := mkFunc "branches" #[
    { id := 0, ty := 3, op := .arg 0 },
    { id := 1, ty := 1, op := .line 42 },
    { id := 2, ty := 2, op := .condBr (.bool true)
      #[{ id := 3, ty := 0, op := .atomicLoad (.inst 0) .unordered }]
      #[{ id := 4, ty := 1, op := .asm "" false #["memory"] #[] #[] }] },
    { id := 5, ty := 2, op := .ret .void }]
  require (diagnosticStructure bad).toOption.isSome "fixture must satisfy structural prerequisites"
  let log := collectFunctionChecks "branches.json" bad {}
  let instructions := log.items.filter (·.code == .instructionFailure)
  require (instructions.map (·.anchor.instruction) == #[some 3, some 4]) "both branches must report their blocker"
  require (instructions.all (fun d => d.anchor.idSpace == .canonical && d.anchor.nearestDbgLine == some 42))
    "canonical identity and approximate line hint"
  require (log.failed && !log.complete && !log.truncated) "first-error validator units must disclose incomplete detail"
  let capped := collectFunctionChecks "branches.json" bad { limit := 1 }
  require (capped.items.size == 1 && capped.truncated && !capped.complete && capped.observed > 1)
    "diagnostic count cap must preserve rejection and incompleteness"
  let malformed := inspect "bad.json" "{" {}
  require (malformed.2.items[0]?.map (·.code) == some .jsonSyntax) "strict malformed JSON boundary"
  require (malformed.2.items.any (·.code == .prerequisiteSkipped)) "failed parse must report skipped prerequisites"
  let marked := inspect "marked.json"
    "{\"schema\":11,\"zig_version\":\"0.16.0\",\"name\":\"marked\",\"types\":[{\"k\":\"void\"}],\"params\":[],\"ret\":0,\"body\":[{\"id\":42,\"tag\":\"unknown_a\",\"ty\":0,\"unsupported\":true},{\"id\":43,\"tag\":\"unknown_b\",\"ty\":0,\"unsupported\":true}]}" {}
  let markers := marked.2.items.filter (·.code == .exporterUnsupported)
  require (markers.map (·.anchor.instruction) == #[some 42, some 43]) "independent explicit exporter markers"
  require (markers.all (fun d => d.category == .unsupportedSemantics && d.anchor.idSpace == .exported))
    "exported IDs must not be labeled canonical"
  let graph : Array Edge := #[
    { caller := "root", callee := "a", instruction := 0, file := "r" },
    { caller := "a", callee := "root", instruction := 0, file := "a" },
    { caller := "a", callee := "blocked", instruction := 1, file := "a" },
    { caller := "root", callee := "blocked", instruction := 1, file := "r" }]
  require (shortestChain graph "root" "blocked" == some #["root", "blocked"]) "BFS must choose shortest deterministic path"
  require (shortestChain graph "root" "absent" == none) "cycles must terminate"
  require (shortestChain graph "root" "blocked" 1 == none) "queue bounds must not invent a chain"
  let call := mkFunc "calls" #[
    { id := 0, ty := 3, op := .arg 0 },
    { id := 1, ty := 1, op := .call (.func "target" false) #[] },
    { id := 2, ty := 1, op := .call (.func "target" false) #[] },
    { id := 3, ty := 2, op := .ret .void }]
  let target := mkFunc "target" #[{ id := 0, ty := 3, op := .arg 0 }, { id := 1, ty := 2, op := .ret .void }]
  let calls := collectCallChecks "calls.json" call #[call, target] {}
  require ((calls.items.filter (·.code == .signatureFailure)).size == 2) "every independent call signature must be checked"
  for flags in [["--diagnostics-json"], ["--diagnostics-json", "x", "-o", "out"],
      ["--diagnostics-json", "x", "--namespace", "N"],
      ["--diagnostics-json", "x", "--diagnostic-limit", "0"]] do
    require (parseCheckArgs flags).toOption.isNone "invalid/mutually incompatible flags"
  let payload := ({ payloadBytes := 1024 * 1024 } : Log).add {
    code := .inputRead, phase := .input, category := .ioFailure, message := "test" }
  require (payload.failed && payload.truncated && !payload.complete && payload.items.isEmpty)
    "payload cap must preserve a failed verdict"
  IO.println "diagnostic collector regressions passed"

#eval collectorChecks
