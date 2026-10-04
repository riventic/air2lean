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
  let malformedType := { (mkFunc "prerequisite") with types := (mkFunc "").types.push (.other "unsupported"),
    layouts := Array.replicate 5 {}, body := #[
      { id := 0, ty := 3, op := .arg 0 },
      { id := 1, ty := 4, op := .elemPtr (.inst 0) (.int 0 0) },
      { id := 2, ty := 4, op := .block #[{ id := 3, ty := 1, op := .asm "" false #["memory"] #[] #[] }] },
      { id := 4, ty := 2, op := .ret .void }] }
  let prerequisite := collectFunctionChecksDetailed "prerequisite.json" malformedType {}
  require prerequisite.structureValid "unsupported result types must not invalidate the structural fixture"
  require (prerequisite.index.insts.map (·.id) == malformedType.allInsts.map (·.id)) "returned index must describe the actual complete function"
  require (prerequisite.log.items.any (fun d => d.code == .prerequisiteSkipped && d.anchor.instruction == some 1 &&
    d.prerequisites == #["instruction_result_type"])) "unsafe dependent operation must be skipped explicitly"
  require ((prerequisite.log.items.filter (·.code == .instructionFailure)).map (·.anchor.instruction) == #[some 3])
    "failed types must suppress dependent operations but preserve nested siblings"
  let huge := String.ofList (List.replicate (100 * 1024) 'x')
  let original : Diagnostic := { code := .typeFailure, phase := .check, category := .validationFailure, message := huge }
  require (original.render == huge) "compatibility rendering outside a bounded log must remain unchanged"
  let captured : Except Diagnostic Unit := capture original (.error huge)
  require (match captured with | .error d => d.render == huge | .ok _ => false)
    "typed compatibility capture must preserve full validator text outside the log"
  let retained := ({} : Log).add original
  require (retained.items.all (fun d => d.message.length ≤ 2048 && d.messageTruncated)) "truncate before retaining diagnostic messages"
  require (retained.items[0]?.map (fun d => (d.toJson.getObjValAs? Bool "message_truncated").toOption) == some (some true))
    "JSON must preserve the original truncation flag after retaining a short message"
  require (retained.payloadBytes == retained.items[0]!.toJson.compress.utf8ByteSize && retained.failed)
    "payload accounting must use retained serialized diagnostics"
  let longType := { malformedType with types := malformedType.types.set! 4 (.other huge) }
  let longErrors := collectFunctionChecks "large.json" longType {}
  require (longErrors.items.any (·.messageTruncated) && longErrors.items.all (fun d => d.message.length ≤ 2048))
    "multiple large validator errors must not remain in the bounded log"
  let pointer := { (mkFunc "pointer") with params := #[], globals := #[
      { name := some "g", ty := 0, isConst := true, threadlocal := false, isExtern := false, init := some (.int 0 0) }],
    layouts := #[{ size := some 4, align := some 4 }, {}, {}, { size := some 8, align := some 8, ptrAlign := some 8 }],
    body := #[{ id := 0, ty := 3, op := .bitcast (.ptrConst 3 0 0) }, { id := 1, ty := 2, op := .ret .void }] }
  let pointerErrors := collectFunctionChecks "pointer.json" pointer {}
  require ((check pointer).toOption.isNone && pointerErrors.items.any (fun d => d.code == .constantFailure && d.anchor.instruction == some 0))
    "shared pointer/global alignment policy must reject both interfaces"
  require (match check pointer with
    | .error message => message == "pointer: a pointer with `align(8)` to a global of alignment 4 is outside the subset"
    | .ok _ => false) "ordinary pointer alignment message must remain byte-identical"
  require (pointerErrors.items.any (fun d => d.code == .constantFailure &&
    d.message == "pointer: a pointer with align(8) to a global of alignment 4 is outside the subset"))
    "diagnostic pointer alignment display context must be preserved"
  let refs := { target with types := target.types.push (.other "fn () void"), layouts := Array.replicate 5 {},
    globals := #[{ name := some "b", ty := 4, isConst := true, threadlocal := false, isExtern := false, init := some (.func "b" false) },
      { name := some "a", ty := 4, isConst := true, threadlocal := false, isExtern := false, init := some (.func "a" false) }] }
  let snapshot := CallChecksSnapshot.build #[refs, target, { target with name := "other" }]
  require (snapshot.references == #[ ("fn () void", "b"), ("fn () void", "a") ]) "reference order must be preserved"
  require ((snapshot.unique "target").isNone && (snapshot.unique "other").isSome) "safe-subset duplicates must stay ambiguous"
  require ((collectCallChecksIndexed "calls.json" call call.operandTypes (CallChecksSnapshot.build #[call, target]) {}).items.size == calls.items.size)
    "shared program snapshot and compatibility wrapper must agree"
  let worker : Func := { zigVersion := "0.16.0", name := "worker", types := #[.int false 32, .void, .noreturn],
    layouts := Array.replicate 3 {}, params := #[0], ret := 1, globals := #[],
    body := #[{ id := 0, ty := 0, op := .arg 0 }, { id := 1, ty := 2, op := .ret .void }] }
  let spawn : Func := { zigVersion := "0.16.0", name := "spawn", types := #[.int false 32, .tuple #[0],
    .struct "Thread.SpawnConfig" "auto" #[], .errorSet none, .thread, .errorUnion 3 4, .noreturn],
    layouts := Array.replicate 7 {}, params := #[], ret := 5, globals := #[], body := #[
      { id := 0, ty := 5, op := .call (.func "Thread.spawn__anon_1" false (some "worker")) #[.undef 2, .agg 1 #[.int 0 7]] },
      { id := 1, ty := 6, op := .ret (.inst 0) }] }
  require (checkProgram #[spawn, worker]).toOption.isSome "shared spawn signature must preserve ordinary acceptance"
  require (collectCallChecks "spawn.json" spawn #[spawn, worker] {}).items.isEmpty "uncached spawn diagnostics must preserve acceptance"
  let wrongWorker := { worker with types := #[.bool, .void, .noreturn] }
  require (checkProgram #[spawn, wrongWorker]).toOption.isNone "cached spawn comparator must reject worker type mismatch"
  require ((collectCallChecks "spawn.json" spawn #[spawn, wrongWorker] {}).items.any (·.code == .signatureFailure))
    "uncached shared spawn comparator must reject the same worker type mismatch"
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
