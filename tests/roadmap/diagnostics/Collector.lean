import Air2Lean.Diagnose

/-! Evaluation regressions for the actual collector, run only by the root guard.
These tests inspect diagnostic behavior; they establish no program proof status. -/
open Air2Lean Air2Lean.Diagnostics

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def mkFunc (name : String) (body : Array Inst := #[]) : Func := {
  zigVersion := "0.16.0"
  name
  params := #[3]
  ret := 1
  types := #[.int false 32, .void, .noreturn, .ptr "one" false 0]
  layouts := Array.replicate 4 {}
  globals := #[]
  body }

private def collectorChecks : IO Unit := do
  let bad := mkFunc "branches" #[
    { id := 0, ty := 3, op := .arg 0 },
    { id := 1, ty := 1, op := .line 42 },
    {
      id := 2
      ty := 2
      op := .condBr (.bool true)
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
  require malformed.1.decodedProfile.isNone "JSON failure cannot fabricate decoded profile eligibility"
  let undecoded := inspect "undecoded.json" "{\"name\":\"declared\"}" {}
  require (undecoded.1.function == some "declared" && undecoded.1.decodedProfile.isNone)
    "declared identity alone cannot make a failed decode eligible for profile comparison"
  let oversized := inspect "oversized.json" ("{\"name\":\"" ++ String.ofList (List.replicate 1025 'x') ++ "\"}") {}
  require (oversized.1.function.isNone && oversized.1.decodedProfile.isNone) "oversized identities must remain ineligible"
  let marked := inspect "marked.json"
    "{\"schema\":11,\"zig_version\":\"0.16.0\",\"name\":\"marked\",\"types\":[{\"k\":\"void\"}],\"params\":[],\"ret\":0,\"body\":[{\"id\":42,\"tag\":\"unknown_a\",\"ty\":0,\"unsupported\":true},{\"id\":43,\"tag\":\"unknown_b\",\"ty\":0,\"unsupported\":true}]}" {}
  let markers := marked.2.items.filter (·.code == .exporterUnsupported)
  require (markers.map (·.anchor.instruction) == #[some 42, some 43]) "independent explicit exporter markers"
  require (markers.all (fun d => d.category == .unsupportedSemantics && d.anchor.idSpace == .exported))
    "exported IDs must not be labeled canonical"
  require (marked.1.decodedProfile.isSome && marked.1.normalized.isNone) "decoded exporter markers retain real profile eligibility"
  let untranslated := inspect "untranslated.json"
    "{\"schema\":11,\"zig_version\":\"0.16.0\",\"name\":\"untranslated\",\"types\":[{\"k\":\"void\"}],\"params\":[],\"ret\":0,\"body\":[{\"id\":0,\"tag\":\"unknown_plain\",\"ty\":0}]}" {}
  require (untranslated.1.decodedProfile.isSome && untranslated.1.normalized.isNone)
    "normalization failure retains the successfully decoded profile"
  let uncanonical := inspect "uncanonical.json"
    "{\"schema\":11,\"zig_version\":\"0.16.0\",\"name\":\"uncanonical\",\"types\":[{\"k\":\"void\"}],\"params\":[],\"ret\":0,\"body\":[{\"id\":0,\"tag\":\"unknown_plain\",\"ty\":0},{\"id\":0,\"tag\":\"unknown_plain\",\"ty\":0}]}" {}
  require (uncanonical.1.decodedProfile.isSome && uncanonical.2.items.any (·.code == .canonicalFailure))
    "canonicalization failure retains real decoded profile eligibility"
  let graph : Array Edge := #[
    { caller := "root", callee := "a", instruction := 0, file := "r" },
    { caller := "a", callee := "root", instruction := 0, file := "a" },
    { caller := "a", callee := "blocked", instruction := 1, file := "a" },
    { caller := "root", callee := "blocked", instruction := 1, file := "r" }]
  require (shortestChain graph "root" "blocked" == some #["root", "blocked"]) "BFS must choose shortest deterministic path"
  require (shortestChain graph "root" "absent" == none) "cycles must terminate"
  require (shortestChain graph "root" "blocked" 1 == none) "queue bounds must not invent a chain"
  let ties : Array Edge := #[
    { caller := "root", callee := "first", instruction := 0, file := "r" },
    { caller := "root", callee := "second", instruction := 1, file := "r" },
    { caller := "first", callee := "blocked", instruction := 0, file := "f" },
    { caller := "second", callee := "blocked", instruction := 0, file := "s" }]
  require (shortestChain ties "root" "blocked" == some #["root", "first", "blocked"])
    "reversed adjacency buckets must preserve first-edge BFS ties"
  let duplicatedTies := #[ties[0]'(by simp [ties]), ties[0]'(by simp [ties]), ties[1]'(by simp [ties]), ties[0]'(by simp [ties]), ties[2]'(by simp [ties]), ties[2]'(by simp [ties]), ties[3]'(by simp [ties])]
  for cap in [0, 1, 2, 3, 4, 257] do
    for goal in ["root", "first", "second", "blocked", "absent"] do
      require (shortestChain duplicatedTies "root" goal cap == shortestChain ties "root" goal cap)
        "repeated adjacency neighbors must preserve shortest paths, terminal goals, first-edge ties and node caps"
  require (shortestChain duplicatedTies "root" "blocked" 4 == some #["root", "first", "blocked"])
    "deduplicated adjacency must keep first-seen tie order"
  require (shortestChain duplicatedTies "root" "blocked" 3 == none &&
    shortestChain duplicatedTies "root" "first" 2 == some #["root", "first"] &&
    shortestChain duplicatedTies "root" "second" 3 == some #["root", "second"])
    "deduplicated adjacency must retain exact queue-cap boundaries and explicit terminal goals"
  let duplicatedCycle := graph ++ graph ++ graph
  require (shortestChain duplicatedCycle "root" "blocked" == some #["root", "blocked"] &&
    shortestChain duplicatedCycle "root" "absent" == none)
    "deduplicated adjacency must preserve cycles and direct shortest paths"
  let repeatedMissing := { (mkFunc "repeated") with
    params := #[]
    body := #[{ id := 0, ty := 1, op := .call (.func "missing" false) #[] },
      { id := 1, ty := 1, op := .call (.func "missing" false) #[] },
      { id := 2, ty := 2, op := .ret .void }] }
  let repeatedUnits : Array FileResult := #[{
    file := "repeated.json"
    function := some repeatedMissing.name
    normalized := some repeatedMissing
    structureValid := true
    localPassed := true }]
  require ((edges repeatedUnits).map (·.instruction) == #[0, 1])
    "BFS-only deduplication must retain every instruction edge"
  let repeatedBlockers := (collectProgram repeatedUnits {}).items.filter (·.code == .calleeMissing)
  require (repeatedBlockers.map (·.anchor.instruction) == #[some 0, some 1] &&
    repeatedBlockers.all (fun d => d.dependencyChain == #["repeated", "missing"]))
    "deduplicated adjacency must preserve per-instruction blocker diagnostics and dependency chains"
  let readChunks (bytes : ByteArray) : IO ((USize → IO ByteArray) × IO.Ref (Array Nat)) := do
    let remaining ← IO.mkRef bytes
    let requests ← IO.mkRef (#[] : Array Nat)
    let read (n : USize) : IO ByteArray := do
      requests.modify (·.push n.toNat)
      let bytes ← remaining.get
      let count := min 2 n.toNat
      remaining.set (bytes.extract count bytes.size)
      return bytes.extract 0 count
    return (read, requests)
  let charged ← IO.mkRef (0 : Nat)
  let (shortRead, shortRequests) ← readChunks "abcd".toUTF8
  let shortContents ← readCharged shortRead charged 4
  require (shortContents == "abcd" && (← charged.get) == 4 && (← shortRequests.get) == #[5, 3, 1])
    "short reads must charge actual chunks through EOF at the exact aggregate boundary"
  let invalidCharged ← IO.mkRef (0 : Nat)
  let (invalidRead, _) ← readChunks (ByteArray.mk #[255])
  let invalidRejected ← try
    let _ ← readCharged invalidRead invalidCharged 4
    pure false
  catch error => pure (decide ((error.toString.splitOn "non UTF-8 AIR input").length > 1))
  require (invalidRejected && (← invalidCharged.get) == 1)
    "invalid UTF-8 must remain rejected while its consumed bytes reduce the aggregate budget"
  let (afterInvalidRead, afterInvalidRequests) ← readChunks "abc".toUTF8
  let afterInvalidContents ← readCharged afterInvalidRead invalidCharged 4
  require (afterInvalidContents == "abc" && (← invalidCharged.get) == 4 &&
    (← afterInvalidRequests.get) == #[4, 2, 1])
    "invalid UTF-8 charges must reduce the next sibling's actual read allowance"
  let partialCharged ← IO.mkRef (0 : Nat)
  let partialRequests ← IO.mkRef (#[] : Array Nat)
  let partialRead (n : USize) : IO ByteArray := do
    let requests ← partialRequests.get
    partialRequests.modify (·.push n.toNat)
    if requests.isEmpty then return "ab".toUTF8
    throw (IO.userError "injected partial read failure")
  let partialRejected ← try
    let _ ← readCharged partialRead partialCharged 4
    pure false
  catch error => pure (decide ((error.toString.splitOn "injected partial read failure").length > 1))
  require (partialRejected && (← partialCharged.get) == 2 && (← partialRequests.get) == #[5, 3])
    "partial I/O failure must not discard previously returned-byte charges or become valid contents"
  let (remainingRead, remainingRequests) ← readChunks "cd".toUTF8
  let remainingContents ← readCharged remainingRead partialCharged 4
  require (remainingContents == "cd" && (← partialCharged.get) == 4 && (← remainingRequests.get) == #[3, 1])
    "a later sibling must receive only the remaining aggregate budget"
  let (growthRead, growthRequests) ← readChunks "ef".toUTF8
  let growthRejected ← try
    let _ ← readCharged growthRead partialCharged 4
    pure false
  catch _ => pure true
  require (growthRejected && (← partialCharged.get) == 5 && (← growthRequests.get) == #[1])
    "growth at an exhausted budget must charge exactly the one global detection byte"
  let (afterGrowthRead, afterGrowthRequests) ← readChunks "g".toUTF8
  let exhaustedRejected ← try
    let _ ← readCharged afterGrowthRead partialCharged 4
    pure false
  catch _ => pure true
  require (exhaustedRejected && (← partialCharged.get) == 5 && (← afterGrowthRequests.get).isEmpty)
    "later files must not receive a new detection-byte allowance after aggregate exhaustion"
  let remainingGrowthCharged ← IO.mkRef (1 : Nat)
  let (remainingGrowthRead, remainingGrowthRequests) ← readChunks "abcd".toUTF8
  let remainingGrowthRejected ← try
    let _ ← readCharged remainingGrowthRead remainingGrowthCharged 4
    pure false
  catch _ => pure true
  require (remainingGrowthRejected && (← remainingGrowthCharged.get) == 5 &&
    (← remainingGrowthRequests.get) == #[4, 2])
    "growth must honor the remaining budget and stop at global budget plus one"
  let unicodeCharged ← IO.mkRef (0 : Nat)
  let (unicodeRead, _) ← readChunks "€".toUTF8
  let unicodeContents ← readCharged unicodeRead unicodeCharged 3
  require (unicodeContents == "€" && (← unicodeCharged.get) == 3)
    "UTF-8 decoding must happen after all short chunks are charged and assembled"
  let call := mkFunc "calls" #[
    { id := 0, ty := 3, op := .arg 0 },
    { id := 1, ty := 1, op := .call (.func "target" false) #[] },
    { id := 2, ty := 1, op := .call (.func "target" false) #[] },
    { id := 3, ty := 2, op := .ret .void }]
  let target := mkFunc "target" #[{ id := 0, ty := 3, op := .arg 0 }, { id := 1, ty := 2, op := .ret .void }]
  let noBlockers := collectProgram #[
    { file := "target.json", function := some target.name, normalized := some target, structureValid := true, localPassed := true }] {}
  require (!noBlockers.failed && noBlockers.complete) "no-blocker program remains accepted without dependency expansion"
  let sharedFailure := collectProgram #[
    { file := "a.json", function := some target.name, normalized := some target, structureValid := true, localPassed := true },
    { file := "b.json", function := some target.name, normalized := some target, structureValid := true, localPassed := true }] {}
  require (sharedFailure.items.any (·.code == .programFailure)) "no dependency blockers must not suppress the authoritative program validator"
  let calls := collectCallChecks "calls.json" call #[call, target] {}
  require ((calls.items.filter (·.code == .signatureFailure)).size == 2) "every independent call signature must be checked"
  let beforeDependency : Log := {
    limit := 1
    items := #[{ code := .inputLimit, phase := .input, category := .resourceLimit, message := "cap" }]
    observed := 1
    failed := true
    complete := false
    truncated := true }
  let afterDependency := collectProgram #[
    { file := "calls.json", function := some call.name, normalized := some call, structureValid := true, localPassed := true },
    { file := "target.json", function := some target.name, normalized := some target, structureValid := true, localPassed := true }] beforeDependency
  -- Both call signature findings are observed (and dropped); the collected whole-program
  -- validator does not count the same two call sites again.
  require (afterDependency.observed == 3 && afterDependency.failed && afterDependency.truncated && !afterDependency.complete)
    "pre-truncated dependency phase must preserve both call additions without duplicate program additions"
  require (afterDependency.items.map (·.code) == #[.inputLimit]) "pre-truncated report cannot add dependency items"
  let malformedType := { (mkFunc "prerequisite") with
    types := (mkFunc "").types.push (.other "unsupported")
    layouts := Array.replicate 5 {}
    body := #[
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
  let nested : Func := {
    (mkFunc "nested") with
    types := #[.int false 32, .void, .noreturn, .ptr "one" false 4,
      .errorUnion 5 0, .errorSet none, .other "unsupported", .ptr "one" false 0]
    layouts := #[{ size := some 4, align := some 4 }, {}, {},
      { size := some 8, align := some 8, ptrAlign := some 4 },
      { size := some 8, align := some 4 }, { size := some 2, align := some 2 }, {},
      { size := some 8, align := some 8, ptrAlign := some 4 }]
    body := #[{ id := 0, ty := 3, op := .arg 0 }, {
      id := 1
      ty := 2
      op := .loopSwitchBr (.int 0 0) #[{
        items := #[.int 0 0]
        ranges := #[]
        body := #[{
          id := 2
          ty := 7
          op := .tryPtr (.inst 0) #[
            { id := 3, ty := 6, op := .asm "" false #[] #[] #[] },
            { id := 4, ty := 1, op := .asm "" false #["memory"] #[] #[] },
            { id := 5, ty := 2, op := .ret .void }] },
          { id := 6, ty := 2, op := .ret .void }] }, {
        items := #[.int 0 1]
        ranges := #[]
        body := #[{ id := 7, ty := 1, op := .asm "" false #["memory"] #[] #[] },
          { id := 8, ty := 2, op := .ret .void }] }]
        #[{ id := 9, ty := 1, op := .asm "" false #["memory"] #[] #[] },
          { id := 10, ty := 2, op := .ret .void }] }] }
  let nestedChecks := collectFunctionChecksDetailed "nested.json" nested {}
  require nestedChecks.structureValid "loop-switch/try-pointer fixture must satisfy structural prerequisites"
  require ((nestedChecks.log.items.filter (·.code == .typeFailure)).map (·.anchor.instruction) == #[some 3])
    "try-pointer error-body type failures must retain their canonical anchor"
  require ((nestedChecks.log.items.filter (·.code == .instructionFailure)).map (·.anchor.instruction) ==
    #[some 4, some 7, some 9]) "try-pointer siblings, later loop cases and the else body remain independently inspectable"
  require (nestedChecks.log.items.any (fun d => d.code == .prerequisiteSkipped && d.anchor.instruction == some 3))
    "failed nested result types must skip only their dependent operation"
  let cleanNested := { nested with body := #[{ id := 0, ty := 3, op := .arg 0 }, {
    id := 1
    ty := 2
    op := .loopSwitchBr (.int 0 0) #[{
      items := #[.int 0 0]
      ranges := #[]
      body := #[{ id := 2, ty := 7, op := (.tryPtr (.inst 0)
          #[{ id := 3, ty := 2, op := .ret .void }]) },
        { id := 6, ty := 2, op := .ret .void }] }]
      #[{ id := 9, ty := 2, op := .ret .void }] }] }
  require (check cleanNested).toOption.isSome "current loop-switch/try-pointer policy must accept the clean fixture"
  require ((collectFunctionChecks "clean-nested.json" cleanNested {}).items.isEmpty)
    "nested collector traversal must preserve ordinary acceptance"
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
  let some retainedDiagnostic := retained.items[0]?
    | throw (IO.userError "bounded log unexpectedly dropped its single retained diagnostic")
  require (retained.payloadBytes == retainedDiagnostic.toJson.compress.utf8ByteSize && retained.failed)
    "payload accounting must use retained serialized diagnostics"
  let longType := { malformedType with types := malformedType.types.set! 4 (.other huge) }
  let longErrors := collectFunctionChecks "large.json" longType {}
  require (longErrors.items.any (·.messageTruncated) && longErrors.items.all (fun d => d.message.length ≤ 2048))
    "multiple large validator errors must not remain in the bounded log"
  let pointer := { (mkFunc "pointer") with
    params := #[]
    globals := #[
      { name := some "g", ty := 0, isConst := true, threadlocal := false, isExtern := false, init := some (.int 0 0) }]
    layouts := #[{ size := some 4, align := some 4 }, {}, {}, { size := some 8, align := some 8, ptrAlign := some 8 }]
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
  let refs := { target with
    types := target.types.push (.other "fn () void")
    layouts := Array.replicate 5 {}
    globals := #[{ name := some "b", ty := 4, isConst := true, threadlocal := false, isExtern := false, init := some (.func "b" false) },
      { name := some "a", ty := 4, isConst := true, threadlocal := false, isExtern := false, init := some (.func "a" false) }] }
  let snapshot := CallChecksSnapshot.build #[refs, target, { target with name := "other" }]
  require (snapshot.references == #[ ("fn () void", "b"), ("fn () void", "a") ]) "reference order must be preserved"
  require ((snapshot.unique "target").isNone && (snapshot.unique "other").isSome) "safe-subset duplicates must stay ambiguous"
  require ((collectCallChecksIndexed "calls.json" call call.operandTypes (CallChecksSnapshot.build #[call, target]) {}).items.size == calls.items.size)
    "shared program snapshot and compatibility wrapper must agree"
  let reference (name : String) (ty : TyId) : Global := {
    name := some name
    ty
    isConst := true
    threadlocal := false
    isExtern := false
    init := some (.func name false) }
  let indirect := { (mkFunc "indirect") with
    types := #[.int false 32, .void, .noreturn, .ptr "one" false 4,
      .other "fn () void", .other "fn (u32) void"]
    layouts := Array.replicate 6 {}
    globals := #[reference "later" 4, reference "unrelated" 5, reference "ambiguous" 4,
      reference "first" 4, reference "missing" 4, reference "later" 4]
    body := #[{ id := 0, ty := 3, op := .arg 0 },
      { id := 1, ty := 1, op := .call (.inst 0) #[] },
      { id := 2, ty := 1, op := .call (.inst 0) #[] },
      { id := 3, ty := 2, op := .ret .void }] }
  require (diagnosticStructure indirect).toOption.isSome "indirect bucket fixture must be structurally valid"
  let indirectSnapshot := CallChecksSnapshot.build #[indirect,
    { target with name := "later" }, { target with name := "ambiguous" },
    { target with name := "unrelated" }, { target with name := "first" },
    { target with name := "ambiguous" }]
  require (indirectSnapshot.references == #[("fn () void", "later"), ("fn (u32) void", "unrelated"),
    ("fn () void", "ambiguous"), ("fn () void", "first"), ("fn () void", "missing")])
    "reference buckets must retain first-occurrence pair deduplication and interleaved order"
  let some buckets := indirectSnapshot.referenceBuckets
    | throw (IO.userError "builder did not prepare reference buckets")
  require (buckets.getD "fn () void" #[] == #["later", "ambiguous", "first", "missing"] &&
    buckets.getD "fn (u32) void" #[] == #["unrelated"])
    "matching and unrelated reference buckets must keep their own traversal order"
  let bare : CallChecksSnapshot := { references := indirectSnapshot.references, targets := indirectSnapshot.targets }
  require bare.referenceBuckets.isNone "bare compatibility snapshots must retain an absent-cache default"
  let indirectIndex := indirect.operandTypes
  let collectIndirect (context : CallChecksSnapshot) (log : Log := {}) :=
    collectCallChecksIndexed "indirect.json" indirect indirectIndex context log
  let signatureRows (log : Log) := log.items.map fun d => (d.anchor.instruction, d.message)
  let expected : Array (Option Nat × String) := #[
    (some 1, "indirect: inst 1: callee 'later' has 0 arguments, expected 1"),
    (some 1, "indirect: inst 1: callee 'first' has 0 arguments, expected 1"),
    (some 2, "indirect: inst 2: callee 'later' has 0 arguments, expected 1"),
    (some 2, "indirect: inst 2: callee 'first' has 0 arguments, expected 1")]
  let indexedIndirect := collectIndirect indirectSnapshot
  let bareIndirect := collectIndirect bare
  require (signatureRows indexedIndirect == expected && signatureRows bareIndirect == expected)
    "repeated indirect calls must preserve ordered failures and skip unrelated, ambiguous and missing targets"
  require (indexedIndirect.items.all (fun d => d.code == .signatureFailure && d.anchor.idSpace == .canonical) &&
    indexedIndirect.observed == 4 && indexedIndirect.payloadBytes == bareIndirect.payloadBytes)
    "cached and bare indirect snapshots must retain identical canonical diagnostics and payload accounting"
  for context in [indirectSnapshot, bare] do
    let cappedIndirect := collectIndirect context { limit := 3 }
    require (signatureRows cappedIndirect == expected.extract 0 3 && cappedIndirect.observed == 4 &&
      cappedIndirect.failed && cappedIndirect.truncated && !cappedIndirect.complete)
      "reference buckets must preserve ordered capped items and continued observation counts"
  let notFunctionPointer := { indirect with types := indirect.types.set! 3 (.ptr "one" false 0) }
  let unknownCallee := collectCallChecksIndexed "indirect.json" notFunctionPointer
    notFunctionPointer.operandTypes indirectSnapshot {}
  require (signatureRows unknownCallee == #[(some 1, "indirect callee is not a function pointer"),
    (some 2, "indirect callee is not a function pointer")])
    "bucket lookup must not change unknown indirect-callee diagnostics or their call anchors"
  let worker : Func := {
    zigVersion := "0.16.0"
    name := "worker"
    types := #[.int false 32, .void, .noreturn]
    layouts := Array.replicate 3 {}
    params := #[0]
    ret := 1
    globals := #[]
    body := #[{ id := 0, ty := 0, op := .arg 0 }, { id := 1, ty := 2, op := .ret .void }] }
  let spawn : Func := {
    zigVersion := "0.16.0"
    name := "spawn"
    types := #[.int false 32, .tuple #[0],
      .struct "Thread.SpawnConfig" "auto" #[], .errorSet none, .thread, .errorUnion 3 4, .noreturn]
    layouts := Array.replicate 7 {}
    params := #[]
    ret := 5
    globals := #[]
    body := #[
      { id := 0, ty := 5, op := .call (.func "Thread.spawn__anon_1" false (some "worker")) #[.undef 2, .agg 1 #[.int 0 7]] },
      { id := 1, ty := 6, op := .ret (.inst 0) }] }
  require (checkProgram #[spawn, worker]).toOption.isSome "shared spawn signature must preserve ordinary acceptance"
  require (collectCallChecks "spawn.json" spawn #[spawn, worker] {}).items.isEmpty "uncached spawn diagnostics must preserve acceptance"
  let wrongWorker := { worker with types := #[.bool, .void, .noreturn] }
  require (checkProgram #[spawn, wrongWorker]).toOption.isNone "cached spawn comparator must reject worker type mismatch"
  require ((collectCallChecks "spawn.json" spawn #[spawn, wrongWorker] {}).items.any (·.code == .signatureFailure))
    "uncached shared spawn comparator must reject the same worker type mismatch"
  let workerBoundary (source target : Func) (expected : Option String := none) : IO Unit := do
    let ordinary := checkProgram #[source, target]
    let diagnostics := collectCallChecks "worker-boundary.json" source #[source, target] {}
    match expected with
    | none =>
      require ordinary.toOption.isSome "ordinary worker coercion boundary rejected"
      require diagnostics.items.isEmpty "collector rejected an ordinary worker coercion"
    | some message =>
      require (match ordinary with | .error error => error == message | .ok _ => false)
        "ordinary worker rejection must reach the intended tuple/result policy"
      require (diagnostics.items.any (fun d => d.code == .signatureFailure && d.message == message &&
        d.anchor.idSpace == .canonical && d.anchor.instruction == some 0))
        "collector must share the exact worker rejection and canonical call anchor"
  let pointerSpawn := { spawn with
    types := (spawn.types.set! 0 (.ptr "one" false 7)).push (.int false 32)
    layouts := (spawn.layouts.set! 0 { size := some 8, align := some 8, ptrAlign := some 4 }).push
      { size := some 4, align := some 4 }
    body := #[{ id := 0, ty := 5, op := (.call (.func "Thread.spawn__anon_1" false (some "worker"))
      #[.undef 2, .agg 1 #[.undef 0]]) }, { id := 1, ty := 6, op := .ret (.inst 0) }] }
  let pointerWorker := { worker with
    types := worker.types.push (.ptr "one" true 0)
    layouts := (worker.layouts.set! 0 { size := some 4, align := some 4 }).push
      { size := some 8, align := some 8, ptrAlign := some 1 }
    params := #[3]
    body := #[{ id := 0, ty := 3, op := .arg 0 }, { id := 1, ty := 2, op := .ret .void }] }
  workerBoundary pointerSpawn pointerWorker
  workerBoundary { pointerSpawn with
      types := pointerSpawn.types.set! 0 (.ptr "slice" false 7)
      layouts := pointerSpawn.layouts.set! 0 { size := some 16, align := some 8, ptrAlign := some 4 } }
    { pointerWorker with
      types := pointerWorker.types.set! 3 (.ptr "slice" true 0)
      layouts := pointerWorker.layouts.set! 3 { size := some 16, align := some 8, ptrAlign := some 1 } }
  let mismatch := "spawn: Thread.spawn argument 0 does not match worker 'worker' parameter 0; capture the exact runtime parameter type with an explicit cast"
  workerBoundary { pointerSpawn with types := pointerSpawn.types.set! 0 (.ptr "one" true 7) }
    { pointerWorker with types := pointerWorker.types.set! 3 (.ptr "one" false 0) } (some mismatch)
  workerBoundary pointerSpawn
    { pointerWorker with layouts := pointerWorker.layouts.set! 3 { size := some 8, align := some 8, ptrAlign := some 8 } }
    (some mismatch)
  workerBoundary spawn { worker with params := #[], body := #[{ id := 1, ty := 2, op := .ret .void }] }
    (some "spawn: Thread.spawn's args tuple has 1 fields, but worker 'worker' has 0 runtime parameters")
  let resultMessage := "worker 'worker' has an unsupported result; supported workers return void or noreturn, and Thread.spawn also accepts u8; error-return handling is outside the model"
  workerBoundary spawn { worker with ret := 0, body := #[{ id := 0, ty := 0, op := .arg 0 },
    { id := 1, ty := 2, op := .ret (.inst 0) }] } (some ("spawn: Thread.spawn " ++ resultMessage))
  let group := { spawn with
    name := "group"
    ret := 5
    types := (spawn.types.set! 5 .void) ++ #[.struct "Io.Group" "auto" #[], .ptr "one" false 7, .io]
    layouts := spawn.layouts ++ #[{}, { size := some 8, align := some 8, ptrAlign := some 1 }, {}]
    body := #[{ id := 0, ty := 5, op := (.call (.func "Io.Group.async" false (some "worker"))
      #[.undef 8, .undef 9, .agg 1 #[.int 0 7]]) }, { id := 1, ty := 6, op := .ret (.inst 0) }] }
  workerBoundary group worker
  let groupByteWorker := { worker with
    types := worker.types.push (.int false 8)
    layouts := worker.layouts.push {}
    ret := 3
    body := #[{ id := 0, ty := 0, op := .arg 0 }, { id := 1, ty := 2, op := .ret (.int 3 7) }] }
  workerBoundary group groupByteWorker (some ("group: Io.Group.async " ++ resultMessage))
  let concurrent := { group with
    types := group.types.push (.errorUnion 3 5)
    layouts := group.layouts.push {}
    ret := 10
    body := #[{ id := 0, ty := 10, op := (.call (.func "Io.Group.concurrent" false (some "worker"))
      #[.undef 8, .undef 9, .agg 1 #[.int 0 7]]) }, { id := 1, ty := 6, op := .ret (.inst 0) }] }
  workerBoundary concurrent worker
  workerBoundary concurrent groupByteWorker (some ("group: Io.Group.async " ++ resultMessage))
  -- Program-level policy uses the exact translation boundary, after the ordinary
  -- worker/model checks. These synthetic units exercise collector composition;
  -- raw AIR parser/normalizer parity is covered by the CLI fixture separately.
  let policyUnit (f : Func) : FileResult := {
    file := f.name ++ ".json"
    function := some f.name
    normalized := some f
    structureValid := true
    localPassed := true }
  let audited := { spawn with
    types := (spawn.types.set! 2 (.struct "Thread.SpawnConfig" "auto"
      #[("stack_size", 7), ("allocator", 9)])) ++
      #[.int false 64, .struct "mem.Allocator" "auto" #[], .optional 8]
    layouts := (spawn.layouts.set! 2 { size := some 32, align := some 8 }) ++
      #[{ size := some 8, align := some 8 }, { size := some 16, align := some 8 },
        { size := some 24, align := some 8 }]
    body := #[{ id := 0, ty := 5, op := (.call (.func "Thread.spawn__anon_1" false (some "worker"))
      #[.agg 2 #[.int 7 16777216, .optNull 9], .agg 1 #[.int 0 7]]) },
      { id := 1, ty := 6, op := .ret (.inst 0) }] }
  let auditedUnits := #[policyUnit audited, policyUnit worker]
  require (checkProgram #[audited, worker]).toOption.isSome "audited spawn must pass the ordinary program prerequisite"
  require (checkFallibleSpawnCalls #[audited, worker]).toOption.isSome "audited null allocator boundary rejected"
  require (collectProgram auditedUnits {} .fallible).items.isEmpty "eligible fallible program rejected"
  require ((report auditedUnits (collectProgram auditedUnits {})).compress ==
    (report auditedUnits (collectProgram auditedUnits {} .available)).compress)
    "omitted and explicit available policies must preserve producer bytes"
  let policyBoundary (source : Func) (marker : String) : IO Unit := do
    require (checkProgram #[source, worker]).toOption.isSome "negative policy fixture failed ordinary prerequisite"
    let expected := checkFallibleSpawnCalls #[source, worker]
    let collected := collectProgram #[policyUnit source, policyUnit worker] {} .fallible
    match expected with
    | .ok _ => throw (IO.userError "negative policy fixture accepted")
    | .error message =>
      require ((message.splitOn marker).length > 1) "negative fixture reached the wrong policy rejection"
      require (collected.failed && !collected.complete && collected.items.size == 1 &&
        collected.items.all (fun d => d.code == .modelFailure && d.phase == .program &&
          d.category == .unsupportedSemantics && d.message == message &&
          d.prerequisites == #["validated_selected_program"] && d.firstErrorInUnit))
        "collector must retain exact shared policy rejection and typed prerequisite"
  policyBoundary spawn "constant SpawnConfig"
  policyBoundary { audited with body := #[
    { id := 0, ty := 5, op := (.call (.func "Thread.spawn__anon_1" false (some "worker"))
      #[.agg 2 #[.int 7 0, .optNull 9], .agg 1 #[.int 0 7]]) },
    { id := 1, ty := 6, op := .ret (.inst 0) }] } "audited 1 MiB or default 16 MiB"
  policyBoundary { audited with body := #[
    { id := 0, ty := 5, op := (.call (.func "Thread.spawn__anon_1" false (some "worker"))
      #[.agg 2 #[.int 7 16777216, .undef 9], .agg 1 #[.int 0 7]]) },
    { id := 1, ty := 6, op := .ret (.inst 0) }] } "custom allocators"
  policyBoundary { group with zigVersion := "0.15.2" } "requires Zig 0.16.0"
  let blockedPolicy := collectProgram #[policyUnit audited, policyUnit wrongWorker] {} .fallible
  require (blockedPolicy.failed && !blockedPolicy.complete &&
    blockedPolicy.items.any (fun d => d.code == .prerequisiteSkipped &&
      d.prerequisites == #["validated_selected_program"]) &&
    !blockedPolicy.items.any (·.code == .modelFailure))
    "policy must not run when the selected program prerequisite fails"
  let excluded := collectProgram #[{ (policyUnit spawn) with structureValid := false }] {} .fallible
  require excluded.items.isEmpty "structurally invalid functions must not reach the policy checker"
  let cappedPolicy := collectProgram #[policyUnit spawn, policyUnit worker] { limit := 0 } .fallible
  require (cappedPolicy.failed && cappedPolicy.truncated && !cappedPolicy.complete &&
    cappedPolicy.observed == 1 && cappedPolicy.items.isEmpty) "policy rejection must survive diagnostic caps"
  for policy in ["available", "fallible"] do
    let flags := ["--diagnostics-json", "x", "--spawn-policy", policy, "--diagnostic-limit", "17"]
    match parseCheckArgs flags, parseSpawnPolicy policy with
    | .ok parsed, .ok expected =>
      require (parsed.spawnPolicy == expected && parsed.limit == 17) "valid policy parsing/propagation"
    | _, _ => throw (IO.userError "valid spawn policy rejected")
  require ((parseCheckArgs ["--diagnostics-json", "x"]).toOption.map (·.spawnPolicy) == some .available)
    "omitted policy must default to available"
  for (flags, expected) in [
      (["--spawn-policy"], "missing value for --spawn-policy"),
      (["--spawn-policy", "unknown"], "invalid --spawn-policy (expected available or fallible)"),
      (["--spawn-policy", "available", "--spawn-policy", "fallible"], "duplicate --spawn-policy"),
      (["--spawn-policy", "fallible", "--profile", BuildProfile.legacyName,
        "--spawn-policy", "fallible"], "duplicate --spawn-policy")] do
    require (match parseCheckArgs (["--diagnostics-json", "x"] ++ flags) with
      | .error message => message == expected
      | .ok _ => false) "policy CLI boundary must reject with the intended diagnostic"
  for flags in [["--diagnostics-json"], ["--diagnostics-json", "x", "-o", "out"],
      ["--diagnostics-json", "x", "--namespace", "N"],
      ["--diagnostics-json", "x", "--diagnostic-limit", "0"]] do
    require (parseCheckArgs flags).toOption.isNone "invalid/mutually incompatible flags"
  let payload := ({ payloadBytes := 1024 * 1024 } : Log).add {
    code := .inputRead
    phase := .input
    category := .ioFailure
    message := "test" }
  require (payload.failed && payload.truncated && !payload.complete && payload.items.isEmpty)
    "payload cap must preserve a failed verdict"
  IO.println "diagnostic collector regressions passed"

#eval collectorChecks
