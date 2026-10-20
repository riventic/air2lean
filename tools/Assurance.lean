import Lean
import tools.AllocatorAdmission
import ZigLean.Witness
-- Every registered claim head of assurance/claim-heads.json is imported here, so an audited
-- module that defines a declaration with the same name fails with a name clash instead of
-- spoofing it. Its reserved (retired) head names are not imported: scripts/claims.py rejects
-- every theorem concluding in one, whatever declaration it is.
import ZigLean.Sep.Full.Triple
import ZigLean.Sep.Full.Logic
import ZigLean.Sep.Full.Conc
import ZigLean.Sep.Full.Thread
import ZigLean.Sep.Full.AllocSpec
import tools.OutcomeContracts

/-!
Environment-based assurance data extraction. The generated driver imports every selected
module and invokes `#assurance_audit`. Policy is deliberately applied outside this command:
the raw declaration graph and Lean's own transitive axiom inventory remain inspectable.
-/

open Lean Elab Command Meta

register_option air2lean.assurance.allDeclarations : Bool := {
  defValue := false
  descr := "seed the assurance graph with every checked declaration in selected modules"
}

namespace Air2Lean.Assurance

private def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => env.allImportedModuleNames[i.toNat]!.toString
  | none => ""

private def kind (c : ConstantInfo) : String :=
  match c with
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .defnInfo _ => "definition"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def namesJson (ns : Array Name) : Json :=
  toJson (ns.map Name.toString)

private def externEntryJson : ExternEntry → Json
  | .standard backend target => Json.mkObj [
      ("kind", toJson "standard"), ("backend", toJson backend.toString), ("target", toJson target)]
  | .inline backend pattern => Json.mkObj [
      ("kind", toJson "inline"), ("backend", toJson backend.toString), ("target", toJson pattern)]
  | .adhoc backend => Json.mkObj [
      ("kind", toJson "adhoc"), ("backend", toJson backend.toString), ("target", Json.null)]
  | .opaque => Json.mkObj [
      ("kind", toJson "opaque"), ("backend", toJson "all"), ("target", Json.null)]

private def externJson (env : Environment) (n : Name) : Json :=
  Json.arr <| ((getExternAttrData? env n).map fun data =>
    data.entries.toArray.map externEntryJson).getD #[]

/-- Include inductive/recursor relations as well as constants in types and bodies. -/
private def dependencies (c : ConstantInfo) : Array Name := Id.run do
  let mut ns := c.getUsedConstantsAsSet
  if let .recInfo v := c then
    for rule in v.rules do
      ns := ns ++ rule.rhs.getUsedConstantsAsSet
  if let .ctorInfo v := c then
    ns := ns.insert v.induct
  return ns.toArray.qsort Name.lt

/-- Build one shared graph, retaining edges through imported theorem and opaque bodies. -/
private partial def graph (env : Environment) (pending : List Name)
    (seen : NameSet := {}) (nodes : Array Json := #[]) : Array Json :=
  match pending with
  | [] => nodes
  | n :: rest =>
    if seen.contains n then graph env rest seen nodes else
    let seen := seen.insert n
    match env.checked.get.find? n with
    | none => graph env rest seen (nodes.push <| Json.mkObj [
        ("name", toJson n.toString), ("module", toJson (moduleOf env n)),
        ("kind", toJson "unresolved"), ("dependencies", toJson (#[] : Array String))])
    | some c =>
      let ds := dependencies c
      -- How the compiler, not the kernel, gives an opaque its meaning: `partial def` (an unsafe
      -- `_unsafe_rec` twin) or `initialize` (an `[init]` function). Such an opaque is code, not a
      -- logical constant (`scripts/assumptions.py`, `is_meta_code`).
      let isOpaque := kind c == "opaque"
      let backing :=
        if isOpaque && env.contains (Compiler.mkUnsafeRecName n) then toJson "partial"
        else if isOpaque && (getInitFnNameFor? env n).isSome then toJson "init"
        else Json.null
      let node := Json.mkObj [
        ("name", toJson n.toString), ("module", toJson (moduleOf env n)),
        ("user_name", toJson ((privateToUserName? n).getD n).toString),
        ("kind", toJson (kind c)), ("unsafe", toJson c.isUnsafe),
        ("partial", toJson c.isPartial), ("dependencies", namesJson ds),
        ("backing", backing),
        ("implemented_by", toJson ((Compiler.getImplementedBy? env n).map Name.toString)),
        ("extern", externJson env n)]
      graph env (ds.toList ++ rest) seen (nodes.push node)

/-- Binders and hypotheses are premises; the conclusion is what remains. No definition is
unfolded, so a wrapper definition keeps its own head constant. -/
private partial def stripBinders : Expr → Expr
  | .forallE _ _ b _ => stripBinders b
  | .mdata _ b => stripBinders b
  | e => e

private def headJson (e : Expr) : Json :=
  match e.consumeMData.getAppFn.consumeMData with
  | .const n _ => toJson n.toString
  | _ => Json.null

/-- Value shape on an equation's right-hand side. `Option.some` is peeled to its value;
`Pure.pure` to its monad and value, since `pure` in `Option` can wrap an error. -/
private partial def valueShape (depth : Nat) (e : Expr) : Json :=
  let e := e.consumeMData
  let head := ("head", headJson e)
  if depth == 0 then Json.mkObj [head]
  else if e.isAppOfArity ``Option.some 2 then
    Json.mkObj [head, ("args", Json.arr #[valueShape (depth - 1) e.appArg!])]
  else if e.isAppOfArity ``Pure.pure 4 then
    Json.mkObj [head, ("args", Json.arr #[Json.mkObj [("head", headJson (e.getArg! 0))],
      valueShape (depth - 1) e.appArg!])]
  else Json.mkObj [head]

/-- Raw conclusion shape for claim classification; policy is applied in `scripts/claims.py`.
Only an equation's right-hand side is expanded: the left side is the computation it states. -/
private def conclusionShape (depth : Nat) (e : Expr) : Json :=
  let e := (stripBinders e).consumeMData
  let head := ("head", headJson e)
  if depth == 0 then Json.mkObj [head]
  else if e.isAppOfArity ``Eq 3 then
    Json.mkObj [head, ("args", Json.arr #[valueShape (depth - 1) e.appArg!])]
  else Json.mkObj [head]

/-- Statement-only constants, read from the kernel type without the proof term or any
unfolding: a proof that merely mentions a definition does not make the theorem about it.
`conclusion_dependencies` drops binders and hypotheses as well. -/
private def statementDependencies (type : Expr) : List (String × Json) :=
  let names (e : Expr) := namesJson (e.getUsedConstants.qsort Name.lt)
  [("statement_dependencies", names type), ("conclusion_dependencies", names (stripBinders type))]

/-! ## Statement structure (claim binding, `scripts/claims.py`)

Everything below reads the kernel type only. Binders are the theorem's own telescope; the
conclusion head is identified by its declaration (module and expression hashes), and each of
its arguments is described as a computation: wrappers that run a computation on a state are
peeled, and the remaining application's arguments are bound variables of the telescope,
closed terms or open terms. -/

private def binderJson : BinderInfo → Json
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "inst_implicit"

/-- Computational constants of a hypothesis: definitions and opaques that are not projections,
instances, matchers or structural auxiliaries. -/
private def definitionsIn (env : Environment) (e : Expr) : Array Name :=
  (e.getUsedConstants.filter fun n =>
    match env.checked.get.find? n with
    | some (.defnInfo _) | some (.opaqueInfo _) =>
      !(env.isProjectionFn n || Meta.isInstanceCore env n || Meta.isMatcherCore env n ||
        isAuxRecursor env n || isNoConfusion env n)
    | _ => false).qsort Name.lt

/-- Telescope indices of the free variables occurring in `e`. -/
private def bvarUses (xs : Array Expr) (e : Expr) : Array Nat := Id.run do
  let mut out := #[]
  for i in [:xs.size] do
    if e.containsFVar xs[i]!.fvarId! then out := out.push i
  return out

private def atomJson (xs : Array Expr) (e : Expr) : Json :=
  let e := e.consumeMData
  match xs.idxOf? e with
  | some i => Json.mkObj [("bvar", toJson i)]
  | none =>
    let head := headJson e
    if e.hasFVar then Json.mkObj [("open", head), ("bvars", toJson (bvarUses xs e))]
    else Json.mkObj [("closed", head)]

/-- The leading binder kinds of a constant's type (its own parameters). -/
private def paramBinders (env : Environment) (n : Name) : Array Json := Id.run do
  let some c := env.checked.get.find? n | return #[]
  return (computationParameters c.type).map binderJson

/-- A conclusion argument as a computation: peeled runners, the applied constant, its
parameter kinds, its arguments and the runners' extra arguments, as atoms; `atom` describes the
argument itself. -/
private def subjectJson (env : Environment) (xs : Array Expr) (e : Expr)
    (checked : Except String ComputationView) : Json := Id.run do
  let result := match checked with
    | .error reason => Json.mkObj [("fn", Json.null), ("runner_error", toJson reason)]
    | .ok view => Id.run do
      let fn := match view.source.getAppFn.consumeMData with
        | .const n _ => some n
        | _ => none
      return Json.mkObj [("peeled", toJson (view.peeled.map Name.toString)),
        ("fn", toJson (fn.map Name.toString)), ("fn_module", toJson (fn.map (moduleOf env))),
        ("params", Json.arr ((fn.map (paramBinders env)).getD #[])),
        ("args", Json.arr (view.source.getAppArgs.map (atomJson xs))),
        ("extra", Json.arr (view.extra.map (atomJson xs)))]
  return result.setObjVal! "atom" (atomJson xs e)

private def hashHex (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  "".pushn '0' (16 - s.length) ++ s

/-- A deterministic serialization of a closed kernel expression (binder names and metadata
dropped; constants, universe levels, binder kinds and literals kept). -/
private partial def serialize : Expr → String
  | .bvar i => s!"#{i}"
  | .fvar _ => "?f"
  | .mvar _ => "?m"
  | .sort l => s!"(S {l})"
  | .const n ls => s!"(C {n} {ls})"
  | .app f a => s!"(A {serialize f} {serialize a})"
  | .lam _ t b bi => s!"(L {binderJson bi} {serialize t} {serialize b})"
  | .forallE _ t b bi => s!"(F {binderJson bi} {serialize t} {serialize b})"
  | .letE _ t v b _ => s!"(Z {serialize t} {serialize v} {serialize b})"
  | .lit (.natVal n) => s!"(N {n})"
  | .lit (.strVal v) => s!"(T {v.quote})"
  | .mdata _ e => serialize e
  | .proj n i e => s!"(P {n} {i} {serialize e})"

/-- 64-bit FNV-1a over the UTF-8 bytes, independent of Lean's `String.hash`. -/
private def fnv1a (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 0x100000001b3) 0xcbf29ce484222325

/-- The 128-bit digest of a text: Lean's `String.hash` and FNV-1a, as 32 hex digits. -/
private def digestText (text : String) : String :=
  hashHex text.hash ++ hashHex (fnv1a text)

/-- The digest of a closed kernel expression: the digest of its node in `serialize`'s grammar
with every immediate subterm written as that subterm's digest (a Merkle hash over the term, so
it is a function of the term alone, not of how its subterms are shared). Structurally equal
subterms are digested once: the cost follows the term's distinct subterms, not its unshared
tree. Proof terms are built with sharing and can unfold to billions of nodes
(`AllocFba.FBA.fthread_alloc`: 5.4·10⁹ tree nodes, 2.2·10⁵ distinct ones), which a serialized
text would have to hold in memory at once. -/
private partial def exprDigest (e : Expr) : StateM (ExprStructMap String) String := do
  if let some digest := (← get).get? e then
    return digest
  let digest ← match e with
    | .app f a => do pure (digestText s!"(A {← exprDigest f} {← exprDigest a})")
    | .lam _ t b bi => do pure (digestText s!"(L {binderJson bi} {← exprDigest t} {← exprDigest b})")
    | .forallE _ t b bi => do pure (digestText s!"(F {binderJson bi} {← exprDigest t} {← exprDigest b})")
    | .letE _ t v b _ => do
      pure (digestText s!"(Z {← exprDigest t} {← exprDigest v} {← exprDigest b})")
    | .mdata _ b => exprDigest b
    | .proj n i b => do pure (digestText s!"(P {n} {i} {← exprDigest b})")
    | leaf => pure (digestText (serialize leaf))
  modify (·.insert e digest)
  return digest

/-- 128-bit fingerprint of a declaration's kernel type and value (`exprDigest`). -/
private def fingerprint (c : ConstantInfo) : String := Id.run do
  let (type, seen) := (exprDigest c.type).run {}
  let value := ((c.value? (allowOpaque := true)).map fun v => ((exprDigest v).run seen).1).getD "-"
  return digestText s!"{type}|{value}"

/-! Factual partial-fixpoint metadata for the existing AIR certificate producer. The reader
uses Lean's own lazy induction theorem and its actual telescope; it does not repeat SCC,
fixed-parameter or recursion analysis. It is independent of the assurance audit below. -/

private def fixpointBinder (xs : Array Expr) (x : Expr) : MetaM Json := do
  let some index := xs.idxOf? x | throwError "fixpoint binder is outside its telescope"
  let decl ← x.fvarId!.getDecl
  return Json.mkObj [("index", toJson index), ("name", toJson decl.userName.toString),
    ("binder", binderJson decl.binderInfo)]

private def realizeFixpointInduction (member : Name) (isMutual : Bool) : MetaM ConstantInfo := do
  let some info := Lean.Elab.PartialFixpoint.eqnInfoExt.find? (← getEnv) member
    | throwError "missing compiler partial-fixpoint metadata: {member}"
  unless !info.declNames.isEmpty && info.declNames.contains member &&
      info.fixpointType.size == info.declNames.size &&
      info.fixpointType.all (fun kind => kind matches .partialFixpoint) do
    throwError "invalid compiler partial-fixpoint membership or kind: {member}"
  if isMutual then
    unless info.declNames.size > 1 && info.declNames[0]? == some member do
      throwError "mutual fixpoint induction requires the actual group leader: {member}"
  -- These are the names registered by Lean's standard partial-fixpoint reserved-name
  -- action. The public resolver below must realize its actual checked theorem.
  let suffix : Name := if isMutual then `mutual_fixpoint_induct else `fixpoint_induct
  let expected := member ++ suffix
  let actual ← realizeGlobalConstNoOverloadCore expected
  unless actual == expected do throwError "fixpoint theorem resolved to another declaration: {actual}"
  let ci ← getConstInfo actual
  unless ci.isTheorem do throwError "fixpoint induction is not a checked theorem: {actual}"
  if ci.type.hasFVar || ci.type.hasMVar || ci.type.hasLooseBVars then
    throwError "fixpoint induction has an open kernel type: {actual}"
  return ci

/-- The original declaration application retained in a compiler induction conclusion. Do not
unfold it: its declaration identity and actual arguments bind the compiler's fixed positions. -/
private def fixpointApplication (e : Expr) : MetaM (Name × Array Expr) :=
  lambdaTelescope e fun _ body => do
    let body := body.consumeMData
    let .const name _ := body.getAppFn | throwError "fixpoint conclusion has no declaration head"
    return (name, body.getAppArgs)

private def fixpointConclusion (xs : Array Expr) (body : Expr) : MetaM (Expr × Name × Array Expr) := do
  let body := body.consumeMData
  let motive := body.getAppFn
  unless motive.isFVar && (xs.idxOf? motive).isSome && body.getAppArgs.size == 1 do
    throwError "fixpoint conclusion is not a telescope motive applied to one declaration"
  let (member, args) ← fixpointApplication body.appArg!
  return (motive, member, args)

/-- Member labels come from the actual packed theorem, using the compiler's existing product
projections. The single-member case has no product. Names below are read, never synthesized. -/
private def fixpointMotiveLabels (info : Lean.Elab.PartialFixpoint.EqnInfo)
    (ci : ConstantInfo) : MetaM (Array (Name × Name)) :=
  forallTelescope ci.type fun xs body =>
    withLocalDeclD `conclusion body fun proof => do
      let parts := Lean.Meta.PProdN.projs info.declNames.size body proof
      let mut labels := #[]
      for part in parts do
        let (motive, member, _) ← fixpointConclusion xs (← inferType part)
        unless info.declNames.contains member do
          throwError "fixpoint induction mentions an unexpected member: {member}"
        let name := (← motive.fvarId!.getDecl).userName
        if labels.any (fun (oldName, oldMember) => oldName == name || oldMember == member) then
          throwError "fixpoint induction has duplicate motive or member labels"
        labels := labels.push (name, member)
      unless labels.size == info.declNames.size do throwError "incomplete fixpoint motive labels"
      return labels

private def fixpointInductionJson (info : Lean.Elab.PartialFixpoint.EqnInfo)
    (labels : Array (Name × Name)) (target : Name) : MetaM Json := do
  let ci ← realizeFixpointInduction target false
  forallTelescope ci.type fun xs body => do
    let (targetMotive, actualTarget, targetArgs) ← fixpointConclusion xs body
    unless actualTarget == target do throwError "fixpoint theorem concludes in another member"
    let some targetIndex := info.declNames.idxOf? target | throwError "unknown fixpoint target"
    let some perm := info.fixedParamPerms.perms[targetIndex]? | throwError "missing fixed permutation"
    let mut fixed := #[]
    let mut fixedIndices := #[]
    for groupIndex in [:info.fixedParamPerms.numFixed] do
      let positions := (Array.range perm.size).filter (fun i => perm[i]! == some groupIndex)
      unless positions.size == 1 do throwError "invalid fixed-parameter permutation"
      let some arg := targetArgs[positions[0]!]?
        | throwError "fixed parameter absent from actual induction conclusion"
      let entry ← fixpointBinder xs arg
      fixed := fixed.push (entry.setObjVal! "group_index" (toJson groupIndex))
      fixedIndices := fixedIndices.push (xs.idxOf arg)
    let mut motives : Array (Name × Expr) := #[]
    for (name, member) in labels do
      let candidates ← xs.filterM fun x => return (← x.fvarId!.getDecl).userName == name
      unless candidates.size == 1 do throwError "fixpoint motive binder is missing or ambiguous: {name}"
      motives := motives.push (member, candidates[0]!)
    unless motives.any (fun (member, motive) => member == target && motive == targetMotive) do
      throwError "fixpoint target motive disagrees with the compiler's packed theorem"
    let mut members := #[]
    let mut roleIndices := fixedIndices
    for member in info.declNames do
      let some (_, motive) := motives.find? (·.1 == member) | throwError "missing member motive"
      let mut adms : Array Expr := #[]
      let mut steps : Array (Expr × Json) := #[]
      for x in xs do
        let decl ← x.fvarId!.getDecl
        let type := decl.type.consumeMData
        if type.isAppOf ``Lean.Order.admissible && type.getAppArgs.back? == some motive then
          adms := adms.push x
        else
          let step? ← forallTelescope type fun inner result => do
            let result := result.consumeMData
            unless result.getAppFn == motive && result.getAppArgs.size == 1 do return none
            let mut approxs : Array (Name × Expr) := #[]
            let mut ihs : Array Json := #[]
            for ih in inner do
              let ihType := (← ih.fvarId!.getDecl).type.consumeMData
              let some (callee, _) := motives.find? (·.2 == ihType.getAppFn) | continue
              unless ihType.getAppArgs.size == 1 do throwError "invalid induction hypothesis application"
              let approx := ihType.appArg!.consumeMData
              unless approx.isFVar && (inner.idxOf? approx).isSome do
                throwError "induction hypothesis does not refer to a step approximation"
              if approxs.any (fun (oldMember, oldApprox) => oldMember == callee || oldApprox == approx) then
                throwError "duplicate retained fixpoint approximation"
              approxs := approxs.push (callee, approx)
              let entry ← fixpointBinder inner ih
              ihs := ihs.push <| (entry.setObjVal! "member" (toJson callee.toString)).setObjVal!
                "approx_index" (toJson (inner.idxOf approx))
            let mut approxJson := #[]
            for approx in inner do
              if let some (callee, _) := approxs.find? (·.2 == approx) then
                let entry ← fixpointBinder inner approx
                approxJson := approxJson.push (entry.setObjVal! "member" (toJson callee.toString))
            unless approxJson.size + ihs.size == inner.size do
              throwError "unclassified binder in actual fixpoint step telescope"
            let entry ← fixpointBinder xs x
            return some <| (entry.setObjVal! "approxs" (Json.arr approxJson)).setObjVal! "ihs" (Json.arr ihs)
          if let some entry := step? then steps := steps.push (x, entry)
      unless adms.size == 1 && steps.size == 1 do
        throwError "missing or ambiguous admissibility/step binder for {member}"
      let motiveJson ← fixpointBinder xs motive
      let admJson ← fixpointBinder xs adms[0]!
      let (step, stepJson) := steps[0]!
      for role in #[motive, adms[0]!, step] do roleIndices := roleIndices.push (xs.idxOf role)
      members := members.push <| Json.mkObj [("name", toJson member.toString),
        ("motive", motiveJson), ("adm", admJson), ("step", stepJson)]
    unless roleIndices.size == xs.size && roleIndices.toList.eraseDups.length == xs.size do
      throwError "unclassified or duplicate outer fixpoint induction binder"
    return Json.mkObj [("name", toJson ci.name.toString), ("target", toJson target.toString),
      ("fixed", Json.arr fixed), ("members", Json.arr members),
      ("type", toJson (serialize ci.type)), ("fingerprint", toJson (fingerprint ci))]

/-- Read compiler facts for selected, already-imported generated modules. A private preparation
driver calls this ordinary helper through Lean's existing `run_meta`; it adds no proof API and
does not change the assurance audit's selected roots, graph, claims or output. -/
def partialFixpointData (modules : Array String) : MetaM Json := withoutExporting do
  let env ← getEnv
  let leaders := env.checked.get.constants.fold (init := ({} : NameSet)) fun found name _ =>
    if !(modules.contains (moduleOf env name)) then found else
    match Lean.Elab.PartialFixpoint.eqnInfoExt.find? env name with
    | some info => if info.fixpointType.all (fun kind => kind matches .partialFixpoint) then
        found.insert info.declNames[0]! else found
    | none => found
  let mut groups := #[]
  for leader in leaders.toArray.qsort Name.lt do
    let some info := Lean.Elab.PartialFixpoint.eqnInfoExt.find? (← getEnv) leader
      | throwError "partial-fixpoint metadata disappeared: {leader}"
    unless !info.declNames.isEmpty && info.fixedParamPerms.perms.size == info.declNames.size do
      throwError "invalid compiler fixpoint membership/permutations"
    let canonical ← realizeFixpointInduction leader (info.declNames.size > 1)
    let labels ← fixpointMotiveLabels info canonical
    let mut members := #[]
    for member in info.declNames, perm in info.fixedParamPerms.perms do
      let ci ← getConstInfo member
      let params ← forallBoundedTelescope ci.type (some perm.size) fun xs _ => do
        unless xs.size == perm.size do throwError "compiler fixed permutation exceeds declaration arity"
        xs.mapM fun x => do
          let decl ← x.fvarId!.getDecl
          return Json.mkObj [("name", toJson decl.userName.toString),
            ("binder", binderJson decl.binderInfo)]
      members := members.push <| Json.mkObj [("name", toJson member.toString),
        ("params", Json.arr params), ("fixed", toJson perm)]
    let inductions ← info.declNames.mapM (fixpointInductionJson info labels)
    groups := groups.push <| Json.mkObj [("members", Json.arr members),
      ("num_fixed", toJson info.fixedParamPerms.numFixed), ("inductions", Json.arr inductions)]
  return Json.mkObj [("fixpoint_groups", Json.arr groups)]

/-- Original kernel facts for the framework ratchet. These are candidate evidence, never an
ordinary-data exemption. In particular, a non-Prop result does not prove a record harmless. -/
private def frameworkEvidence (env : Environment) (n : Name) (c : ConstantInfo) : MetaM Json := do
  -- A proof's type is already a proposition. Reducing that proposition could run the program
  -- it mentions; only a definition whose TYPE returns the sort Prop needs the telescope test.
  if c.type.hasMVar || c.type.hasFVar || c.type.hasLooseBVars then
    throwError "framework evidence requires a closed kernel signature: {n}"
  let proof ← if c.isTheorem then pure true else do
    -- Ask the kernel for the original signature's SORT, without examining a proof value/body.
    -- Meta's isProp/inferType use default transparency internally; the existing kernel
    -- APIs handle irreducible sort aliases through forall/let/metadata uniformly.
    let sort ← match Kernel.check env {} c.type with
      | .ok sort => pure sort
      | .error ex => throwError "framework signature check failed for {n}: {ex.toMessageData (← getOptions)}"
    match Kernel.isDefEq env {} sort (mkSort .zero) with
    | .ok proof => pure proof
    | .error ex => throwError "framework signature sort check failed for {n}: {ex.toMessageData (← getOptions)}"
  let (propValued, binders) ←
    if proof then
      pure ((some false : Option Bool), (#[] : Array Json))
    else
      withTransparency .all <| forallTelescopeReducing c.type (whnfType := true) fun xs result => do
        let mut binders := #[]
        for x in xs do
          let decl ← x.fvarId!.getDecl
          binders := binders.push <| Json.mkObj [
            ("binder", binderJson decl.binderInfo),
            ("type_constants", namesJson (decl.type.getUsedConstants.qsort Name.lt))]
        let propValued : Option Bool := match result.consumeMData with
          | .sort .zero => some true
          | .sort (.succ _) => some false
          | _ => none
        return (propValued, binders)
  let body := c.value? (allowOpaque := true)
  let valueConstants := (body.map fun e => e.getUsedConstants.qsort Name.lt).getD #[]
  return Json.mkObj [
    ("name", toJson n.toString), ("module", toJson (moduleOf env n)),
    ("user_name", toJson ((privateToUserName? n).getD n).toString),
    ("kind", toJson (kind c)), ("is_proof", toJson proof), ("prop_valued", toJson propValued),
    ("binders", Json.arr binders),
    ("original_type_constants", namesJson (c.type.getUsedConstants.qsort Name.lt)),
    ("original_body_constants", namesJson valueConstants),
    ("body_available", toJson body.isSome),
    ("kernel_fingerprint", toJson (fingerprint c)),
    ("projection", toJson (env.isProjectionFn n)),
    ("matcher", toJson (Meta.isMatcherCore env n)),
    ("auxiliary_recursor", toJson (isAuxRecursor env n || isNoConfusion env n))]

/-- The declaration behind a conclusion head: its module and a fingerprint of its kernel type
and value, so that a same-named declaration elsewhere is distinguishable. -/
private def headIdentity (env : Environment) (e : Expr) : Json :=
  match e.getAppFn.consumeMData with
  | .const n _ =>
    match env.checked.get.find? n with
    | some c => Json.mkObj [("name", toJson n.toString), ("module", toJson (moduleOf env n)),
        ("kind", toJson (kind c)), ("fingerprint", toJson (fingerprint c))]
    | none => Json.mkObj [("name", toJson n.toString), ("module", toJson ""),
        ("kind", toJson "unresolved"), ("fingerprint", Json.null)]
  | _ => Json.null

/-- A companion witness theorem: verified when its kernel type is exactly the statement
recomputed from the claim's type. -/
private def witnessJson (env : Environment) (thm : Name) (suffix : Name)
    (expected : Option Expr) : Json :=
  let companion := thm ++ suffix
  match expected, env.checked.get.find? companion with
  | none, _ => Json.mkObj [("status", toJson "not_required"), ("theorem", Json.null)]
  | some _, none => Json.mkObj [("status", toJson "absent"), ("theorem", Json.null)]
  | some ty, some c =>
    let ok := c.isTheorem && c.type == ty
    Json.mkObj [("status", toJson (if ok then "verified" else "mismatch")),
      ("theorem", toJson companion.toString)]

/-- A concrete allocator implementation, rather than a rule parameterized by an unknown
invariant. The contract's final argument is its invariant in both existing contract heads. -/
private def allocatorInvariant? (type : Expr) : Option Expr :=
  let body := stripBinders type
  if body.isAppOf `Zig.Full.FAllocSpec || body.isAppOf `Zig.Full.CAllocSpec then
    let inv := body.appArg!
    if inv.getAppFn.isBVar then none else some inv
  else none

/-- A generic contract-producing function specialized to a concrete invariant needs a named
implementation theorem and its companions too. This includes anonymous constructor proofs. -/
private partial def specializedAllocator (type : Expr) (args : Array Expr) (binders : Nat := 0) : Bool :=
  match type.consumeMData with
  | .forallE _ _ body _ => specializedAllocator body args (binders + 1)
  | body =>
    if body.isAppOf `Zig.Full.FAllocSpec || body.isAppOf `Zig.Full.CAllocSpec then
      match body.appArg!.getAppFn with
      | .bvar i =>
        if i < binders then
          match args[binders - i - 1]? with
          | some inv => !inv.getAppFn.isBVar && !inv.getAppFn.isFVar
          | none => false
        else false
      | _ => false
    else false

/-- Proposition aliases cannot hide a concrete contract premise. Unfold only definitions whose
codomain is Prop; recursive aliases are visited once, and ordinary program bodies stay opaque. -/
private partial def concreteAllocatorApplication (env : Environment) (expr : Expr)
    (seen : NameSet := {}) : Bool := Id.run do
  let expr := expr.consumeMData.headBeta
  if expr.isAppOfArity `Zig.Full.FAllocSpec 4 || expr.isAppOfArity `Zig.Full.CAllocSpec 4 then
    return !expr.appArg!.getAppFn.isBVar && !expr.appArg!.getAppFn.isFVar
  let .const name levels := expr.getAppFn | return false
  if seen.contains name then return false
  let some (.defnInfo d) := env.checked.get.find? name | return false
  unless stripBinders d.type == .sort .zero do return false
  -- A partial predicate application is a function, not a proposition alias. Expanding its
  -- remaining lambda domains would invent a concrete premise that the full call may ignore.
  unless expr.getAppNumArgs == d.type.getNumHeadForalls do return false
  let expanded := (d.value.instantiateLevelParams d.levelParams levels).beta expr.getAppArgs
  return (expanded.find? fun e => concreteAllocatorApplication env e (seen.insert name)).isSome

private def unnamedAllocator (env : Environment) (c : ConstantInfo) (ds : Array Name) : Bool := Id.run do
  if (allocatorInvariant? c.type).isSome then return false
  if (c.type.find? fun expr => concreteAllocatorApplication env expr).isSome then return true
  let mut producers : NameSet := {}
  for name in ds do
    if let some called := env.checked.get.find? name then
      let body := stripBinders called.type
      if (body.isAppOf `Zig.Full.FAllocSpec || body.isAppOf `Zig.Full.CAllocSpec) &&
          body.appArg!.getAppFn.isBVar then producers := producers.insert name
  if producers.isEmpty then return false
  return ((c.value? (allowOpaque := true)).bind fun value => value.find? fun expr =>
    let expr := expr.consumeMData.headBeta
    match expr.getAppFn with
    | .const name _ =>
      if producers.contains name then
        match env.checked.get.find? name with
        | some called => specializedAllocator called.type expr.getAppArgs
        | none => false
      else false
    | _ => false).isSome

/-- All concrete allocator contracts used by the statement or proof, including imported ones.
Generic interface rules whose invariant is a parameter introduce no implementation assumption. -/
private partial def allocatorGraph (env : Environment) (pending : List Name)
    (deps : Std.HashMap Name (Array Name) := {}) (out : Array Name := #[]) :
    Std.HashMap Name (Array Name) × Array Name :=
  match pending with
  | [] => (deps, out.qsort Name.lt)
  | n :: rest =>
    if deps.contains n then allocatorGraph env rest deps out else
    match env.checked.get.find? n with
    | none => allocatorGraph env rest (deps.insert n #[]) out
    | some c =>
      let ds := dependencies c
      let concrete := (allocatorInvariant? c.type).isSome
      let out := if concrete || unnamedAllocator env c ds then out.push n else out
      let companions := if concrete then #[n ++ `creationParameters, n ++ `creation,
        n ++ `creation ++ Zig.Witness.nonvacuousSuffix] else #[]
      let witnesses := if c.isTheorem then
        #[n ++ Zig.Witness.nonvacuousSuffix, n ++ Zig.Witness.livenessSuffix,
          n ++ Zig.Witness.reachableSuffix].filter (fun name => (env.checked.get.find? name).isSome) else #[]
      let next := ds ++ companions ++ witnesses
      allocatorGraph env (next.toList ++ rest) (deps.insert n next) out

/-- Per-root reachability reuses the shared graph and already checked companion records. No
proof body, declaration classification or kernel post comparison is repeated for each client. -/
private partial def allocatorReachable (deps : Std.HashMap Name (Array Name))
    (records : Std.HashMap Name (Json × List Nat)) (pending : List Name) (seen : NameSet := {})
    (out : Array Name := #[]) : Array Json :=
  match pending with
  | [] => (out.qsort Name.lt).map fun n => ((records.get? n).map Prod.fst).getD Json.null
  | n :: rest =>
    if seen.contains n then allocatorReachable deps records rest seen out else
    let out := if records.contains n then out.push n else out
    allocatorReachable deps records (((deps.get? n).getD #[]).toList ++ rest) (seen.insert n) out

/-- Read plain specification data by kernel reduction, never by an external evaluator. -/
private partial def creationIndices? (expr : Expr) : MetaM (Option (List Nat)) := do
  let expr ← whnf expr
  if expr.isAppOfArity ``List.nil 1 then return some []
  unless expr.isAppOfArity ``List.cons 3 do return none
  let args := expr.getAppArgs
  let some n ← evalNat args[1]! | return none
  let some rest ← creationIndices? args[2]! | return none
  return some (n :: rest)

private def creationParameters? (env : Environment) (contract : Name) :
    MetaM (Option (List Nat × List Nat)) := do
  let name := contract ++ `creationParameters
  let some c := env.checked.get.find? name | return none
  unless c.type.isConstOf ``Zig.Full.FAllocCreationParameters && kind c == "definition" do return none
  let value ← whnf (mkConst name)
  unless value.isAppOfArity ``Zig.Full.FAllocCreationParameters.mk 2 do return none
  let args := value.getAppArgs
  let some visible ← creationIndices? args[0]! | return none
  let some fresh ← creationIndices? args[1]! | return none
  return some (visible, fresh)

/-- Compare the exact invariant family with visible instance parameters kept fixed. Only the
explicit fresh ghost parameters are existential; unused inhabited binders can be erased. -/
private def allocatorCreationPost (type : Expr) (visible fresh : List Nat) (ys : Array Expr) :
    MetaM (Option Expr) :=
  forallTelescope type fun xs body => do
    unless ys.size == visible.length &&
        (visible ++ fresh).mergeSort (· ≤ ·) == List.range xs.size do return none
    -- Roles are specification, but cannot relabel a parameter already captured by the
    -- executable contract (logic, vtable, context) or its client-visible request bound.
    let captured := body.getAppArgs.pop
    let fits ← whnf (← mkAppM ``Zig.Full.FAllocInv.fits #[body.appArg!])
    for index in fresh do
      let id := xs[index]!.fvarId!
      if captured.any (·.containsFVar id) || fits.containsFVar id then return none
    let mut sources := #[]
    let mut replacements := #[]
    for (index, y) in visible.zip ys.toList do
      let x := xs[index]!
      unless ← isDefEq ((← inferType x).replaceFVars sources replacements) (← inferType y) do return none
      sources := sources.push x
      replacements := replacements.push y
    let post ← mkAppM `Zig.Full.FAllocInv.creationPost #[body.appArg!]
    withLocalDeclD `r (mkConst `Zig.Full.Res) fun r => do
      let mut acc := mkApp post r
      for index in fresh.reverse do
        let x := xs[index]!
        let ty ← inferType x
        let needed ← if acc.containsFVar x.fvarId! || (← isProp ty) then pure true
          else if ty.isSort then pure false
          else do
            let u ← getLevel ty
            pure (← synthInstance? (mkApp (mkConst ``Nonempty [u]) ty)).isNone
        if needed then
          acc ← mkAppM ``Exists #[← mkLambdaFVars #[x] acc]
      let target := (← mkLambdaFVars #[r] acc).replaceFVars sources replacements
      if xs.any fun x => target.containsFVar x.fvarId! then return none
      return some target

/-- Creation is an actual existing total triple into the exact invariant family and a positive
fee. Its admissibility companion is recomputed from that triple, just like other witnesses. -/
private def allocatorCreationJson (env : Environment) (contract : Name) : MetaM (Json × List Nat) := do
  let creation := contract ++ `creation
  let base := [("contract", toJson contract.toString), ("theorem", toJson creation.toString)]
  let some contractInfo := env.checked.get.find? contract |
    return (Json.mkObj (base ++ [("status", toJson "absent"), ("admissibility", Json.null)]), [])
  if (allocatorInvariant? contractInfo.type).isNone then
    return (Json.mkObj (base ++ [("status", toJson "unnamed"), ("admissibility", Json.null)]), [])
  let some c := env.checked.get.find? creation |
    return (Json.mkObj (base ++ [("status", toJson "absent"), ("admissibility", Json.null)]), [])
  let parameters ← creationParameters? env contract
  let (matchesPost, admissionBound, positions) ← forallTelescope c.type fun ys body => do
    unless c.isTheorem && body.isAppOfArity `Zig.Full.FTotalTriple 4 do return (false, false, [])
    let some (visible, fresh) := parameters | return (false, false, [])
    let some target ← allocatorCreationPost contractInfo.type visible fresh ys | return (false, false, [])
    let args := body.getAppArgs
    let pre ← whnf args[1]!
    -- An existential FAdmit witness covers every visible value only when the precondition
    -- does not depend on that value. Parameter-dependent raw input needs the checked applied
    -- admission/domain protocol of engine ledger #allocator-creation-admissibility.
    -- An existential fresh post also does not bind a client's actual fresh arguments. Until
    -- their created-result relation is extracted, even a constant raw pre stays unbound.
    let admissionBound := fresh.isEmpty && !ys.any fun y => pre.containsFVar y.fvarId!
    -- Diagnostics use zero-based CONTRACT positions, even when creation reorders binders.
    -- These indices never decide admission; unsupported/fresh cases retain their own cause.
    let positions := (visible.zip ys.toList).filterMap fun (index, y) =>
      if pre.containsFVar y.fvarId! then some index else none
    withLocalDeclD `v args[0]! fun v => do
      let matchesPost ← isDefEq (mkApp args[3]! v) target
      return (matchesPost, admissionBound,
        if matchesPost && fresh.isEmpty then positions.mergeSort (· ≤ ·) else [])
  let expected ← Zig.Witness.nonvacuityType c.type
  let status := if !matchesPost then "mismatch" else if admissionBound then "verified" else "unbound_admissibility"
  return (Json.mkObj (base ++ [("status", toJson status),
    ("post_status", toJson (if matchesPost then "verified" else "mismatch")),
    ("admission_binding", toJson (if admissionBound then "constant_precondition" else "unbound")),
    ("parameters", toJson (contract ++ `creationParameters).toString),
    ("admissibility", witnessJson env creation Zig.Witness.nonvacuousSuffix (some expected))]), positions)

/-- Names select which proof bodies need inspection; argument binding is done separately on
their actual applications. The reverse closure is shared by all selected theorem roots. -/
private def allocatorRelevant (deps : Std.HashMap Name (Array Name))
    (contracts : Array Name) : NameSet := Id.run do
  let mut reverse : Std.HashMap Name (Array Name) := {}
  for (name, ds) in deps do
    for d in ds do reverse := reverse.insert d (((reverse.get? d).getD #[]).push name)
  let mut pending := (contracts ++ #[`Zig.Full.FAllocSpec, `Zig.Full.CAllocSpec,
    `Zig.Full.FAllocSpec.mk, `Zig.Full.CAllocSpec.mk]).toList
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      seen := seen.insert name
      pending := ((reverse.get? name).getD #[]).toList ++ pending
  return seen

/-- The existing non-vacuity predicate after applying the creator to these exact visible
arguments. No metavariable is used as an argument; only universe constraints may be solved by
checking the creator's dependent parameter types against the checked actual arguments. -/
private def appliedAllocatorAdmission (env : Environment) (expr : Expr) : MetaM (Option Expr) := do
  let .const contract levels := expr.getAppFn | return none
  let some ci := env.checked.get.find? contract | return none
  let args := expr.getAppArgs
  if args.any (·.hasMVar) then return none
  let arity ← forallTelescope (ci.type.instantiateLevelParams ci.levelParams levels) fun xs _ =>
    pure xs.size
  unless args.size == arity do return none
  let some (visible, fresh) ← creationParameters? env contract | return none
  unless (visible ++ fresh).mergeSort (· ≤ ·) == List.range arity do return none
  -- Raw admission alone cannot identify the existential fresh values produced by creation.
  unless fresh.isEmpty do return none
  let creation := contract ++ `creation
  let some info := env.checked.get.find? creation | return none
  unless info.isTheorem do return none
  let creator ← mkConstWithFreshMVarLevels creation
  let mut ty ← inferType creator
  for i in visible do
    let .forallE _ domain body _ ← whnf ty | return none
    let actual := args[i]!
    unless ← isDefEq domain (← inferType actual) do return none
    ty := body.instantiate1 actual
  let appliedType ← instantiateMVars ty
  if appliedType.hasMVar || appliedType.isForall then return none
  unless appliedType.isAppOfArity `Zig.Full.FTotalTriple 4 do return none
  let expected ← instantiateMVars (← Zig.Witness.nonvacuityType appliedType)
  if expected.hasMVar then return none
  return some expected

/-- Extract once per checked root; these closed uses do not depend on creation-record status. -/
private def allocatorUses (env : Environment) (root : Name)
    (contracts relevant : NameSet) :=
  Air2Lean.AllocatorAdmission.collectUses env root contracts relevant
    (appliedAllocatorAdmission env) (fun ty => do
      unless ty.getUsedConstants.any relevant.contains do return false
      let ty ← zetaReduce ty (beta := false)
      return (ty.find? fun expr => concreteAllocatorApplication env expr).isSome)

private def allocatorApplicationError (record : Json) (message : String) : Json := Id.run do
  let status := (record.getObjValAs? String "status").toOption.getD ""
  let record := record.setObjVal! "application_error" (toJson message)
  return if status == "verified" || status == "unbound_admissibility" then
    record.setObjVal! "status" (toJson "unbound_application") else record

/-- Apply closed uses to the current records. Exact evidence in the original client context
binds a parameter-dependent creator; an existential witness for another member never does. -/
private def allocatorApplications (root : Name) (records : Array Json)
    (found : Except String (Array Air2Lean.AllocatorAdmission.AppliedUse)) : Array Json := Id.run do
  match found with
  | .error message =>
    if records.isEmpty then
      return #[Json.mkObj [("contract", toJson root.toString), ("theorem", Json.null),
        ("status", toJson "unnamed"), ("admissibility", Json.null),
        ("application_error", toJson message)]]
    return records.map (allocatorApplicationError · message)
  | .ok uses =>
    records.mapM fun record => do
      let name := (record.getObjValAs? String "contract").toOption.getD ""
      let actual := (uses.filter fun use => use.contract.toString == name).map fun use =>
        (serialize use.application, use)
      let actual := actual.qsort fun a b => a.1 < b.1
      let applications := actual.map fun (application, use) => Json.mkObj [
        ("application", toJson application),
        ("admission", toJson (serialize use.obligation)),
        ("evidence", toJson (use.evidence.map serialize)),
        ("root_bound", toJson use.rootBound)]
      let record := record.setObjVal! "applications" (Json.arr applications)
      let status := (record.getObjValAs? String "status").toOption.getD ""
      if status != "unbound_admissibility" then return record
      if !actual.isEmpty && actual.all (fun (_, use) => use.evidence.isSome && use.rootBound) then
        return (record.setObjVal! "status" (toJson "verified")).setObjVal! "admission_binding"
          (toJson "checked_client_context")
      return record

private def statementJson (n : Name) (type : Expr) (allocatorCreation : Array Json) : MetaM Json := do
  let env ← getEnv
  -- One premise telescope serves every witness statement (`Zig.Witness.statements`): unfolding
  -- the conclusion head can evaluate a whole computation, which is not repeated per statement.
  let st ← Zig.Witness.statements type
  let nonvacuityJson :=
    if st.trivial then Json.mkObj [("status", toJson "trivial"), ("theorem", Json.null)]
    else witnessJson env n Zig.Witness.nonvacuousSuffix (some st.nonvacuity)
  let reachabilityJson :=
    if st.triviallyReachable then Json.mkObj [("status", toJson "trivial"), ("theorem", Json.null)]
    else witnessJson env n Zig.Witness.reachableSuffix st.reachability
  forallTelescope type fun xs body => do
    let mut binders := #[]
    for i in [:xs.size] do
      let decl ← xs[i]!.fvarId!.getDecl
      binders := binders.push <| Json.mkObj [
        ("name", toJson decl.userName.toString), ("binder", binderJson decl.binderInfo),
        ("prop", toJson (← isProp decl.type)), ("defs", namesJson (definitionsIn env decl.type)),
        ("uses", toJson (bvarUses (xs.extract 0 i) decl.type))]
    let body := body.consumeMData
    -- A natural-number argument (a bound of a bounded head) also records its value when it is
    -- closed (`evalNat`) and its printed form, so a manifest can check the bound it states.
    let computation ← statementComputation body
    let computationIndex := computationArgument? body
    let computations ← body.getAppArgs.mapIdxM fun i a =>
      if computationIndex == some i then pure computation else peelComputation a
    let args ← (body.getAppArgs.zip computations).mapM fun (a, checked) => do
      let j := subjectJson env xs a checked
      let isNat ← try pure ((← whnfR (← inferType a)).isConstOf ``Nat) catch _ => pure false
      unless isNat do return j
      let value ← if a.hasFVar || a.hasMVar then pure none else evalNat a
      let pp ← match value with
        | some v => pure (toString v)
        | none => return j.setObjVal! "nat" (Json.mkObj [("value", Json.null),
            ("pp", toJson (toString (← ppExpr a)))])
      return j.setObjVal! "nat" (Json.mkObj [("value", toJson value), ("pp", toJson pp)])
    return Json.mkObj [
      ("binders", Json.arr binders), ("head", headIdentity env body),
      ("args", Json.arr args),
      ("allocator_creation", Json.arr allocatorCreation),
      ("outcomes", ← outcomeJson body (some computation)),
      ("witnesses", Json.mkObj [("nonvacuity", nonvacuityJson),
        ("liveness", witnessJson env n Zig.Witness.livenessSuffix st.liveness),
        ("reachability", reachabilityJson)])]

syntax (name := assuranceAudit) "#assurance_audit" "[" str,* "]" : command

elab_rules : command
  | `(#assurance_audit [$modules:str,*]) => do
    let selected := modules.getElems.map (·.getString)
    if selected.isEmpty then throwError "assurance audit requires modules"
    -- The checked environment excludes erroneous elaborator placeholders. Private olean
    -- data is loaded by ordinary (non-`module`) imports, so proof bodies are available.
    let env := (← getEnv).setExporting false
    if env.header.modules.size != env.header.moduleData.size then
      throwError "assurance import metadata is incomplete"
    let moduleImports := (env.header.modules.zip env.header.moduleData).map fun (entry, data) =>
      (entry.module.toString, if entry.hasData then namesJson (data.imports.map (·.module)) else Json.null)
    let selectedSet := Std.HashSet.ofArray selected
    let seedAll := air2lean.assurance.allDeclarations.get (← getOptions)
    let (roots, declarations, selectedDeclarations) := env.checked.get.constants.fold
      (init := ((#[] : Array Name), (#[] : Array Name), (#[] : Array Name)))
      fun (roots, declarations, selectedDeclarations) n c =>
        if !selectedSet.contains (moduleOf env n) then (roots, declarations, selectedDeclarations) else
        let roots := if c.isTheorem then roots.push n else roots
        let declarations := if c.isAxiom || (kind c == "opaque") ||
            (Compiler.getImplementedBy? env n).isSome ||
            (getExternAttrData? env n).isSome then declarations.push n else declarations
        (roots, declarations, if seedAll then selectedDeclarations.push n else selectedDeclarations)
    -- Imported implementation companions must themselves be audited, not merely named by a
    -- selected client. Their statements and complete proof closures receive the same policy.
    let (allocatorDeps, contracts) := allocatorGraph env roots.toList
    let mut creationRecords : Std.HashMap Name (Json × List Nat) := {}
    for contract in contracts do
      let record ← liftTermElabM <| withoutExporting <| allocatorCreationJson env contract
      creationRecords := creationRecords.insert contract record
    let namedContracts := contracts.filter fun name =>
      ((env.checked.get.find? name).bind fun ci => allocatorInvariant? ci.type).isSome
    let contractSet := namedContracts.foldl (init := ({} : NameSet)) fun set name => set.insert name
    let relevant := allocatorRelevant allocatorDeps namedContracts
    let mut applicationUses : Std.HashMap Name
        (Except String (Array Air2Lean.AllocatorAdmission.AppliedUse)) := {}
    -- A client records named calls without expanding their implementation bodies. Audit
    -- those bodies once here, and propagate any failure into every client's cached record.
    for contract in namedContracts do
      let records := allocatorReachable allocatorDeps creationRecords [contract]
      let found ← liftTermElabM <| withoutExporting <|
        allocatorUses env contract contractSet relevant
      applicationUses := applicationUses.insert contract found
      let inspected := allocatorApplications contract records found
      let some checked := inspected.find? fun record =>
          (record.getObjValAs? String "contract").toOption == some contract.toString |
        throwError "allocator admission lost its checked own creation record"
      let mut checked := checked
      unless (checked.getObjValAs? String "application_error").isOk do
        if let some foreign := inspected.find? fun record =>
            (record.getObjValAs? String "contract").toOption != some contract.toString &&
            (record.getObjValAs? String "status").toOption != some "verified" then
          let name := (foreign.getObjValAs? String "contract").toOption.getD ""
          let creation := (foreign.getObjValAs? String "theorem").toOption.getD s!"{name}.creation"
          let mut message := s!"allocator admission named body has an unbound foreign creation: {creation}"
          if let some cause := (foreign.getObjValAs? String "application_error").toOption then
            message := s!"{message}; {cause}"
          else
            let positions := ((namedContracts.find? (·.toString == name)).bind fun name =>
              (creationRecords.get? name).map Prod.snd).getD []
            if !positions.isEmpty then
              message := s!"{message}; zero-based contract argument positions {reprStr positions}"
            else
              let cause := (foreign.getObjValAs? String "status").toOption.getD "unknown status"
              message := s!"{message}; {cause}"
          checked := allocatorApplicationError checked message
      if let .ok _ := checked.getObjValAs? String "application_error" then
        creationRecords := creationRecords.insert contract (checked, (creationRecords[contract]!).2)
    let mut rootSet : NameSet := {}
    for n in roots do rootSet := rootSet.insert n
    for contract in contracts do
      for name in #[contract, contract ++ `creation, contract ++ `creation ++ Zig.Witness.nonvacuousSuffix] do
        if let some c := env.checked.get.find? name then
          if c.isTheorem then rootSet := rootSet.insert name
    let roots := rootSet.toArray.qsort Name.lt
    let declarations := declarations.qsort Name.lt
    let selectedDeclarations := selectedDeclarations.qsort Name.lt
    let mut framework : Array Json := #[]
    if seedAll then
      for n in selectedDeclarations do
        let some c := env.checked.get.find? n | throwError "selected declaration disappeared: {n}"
        let evidence ← liftTermElabM <| withoutExporting <| frameworkEvidence env n c
        framework := framework.push evidence
    let mut theorems : Array Json := #[]
    for n in roots do
      let axs ← collectAxioms n
      let (conclusion, statement, shape) ← match env.checked.get.find? n with
        | some c => do
          let creation := allocatorReachable allocatorDeps creationRecords [n]
          let shape ← liftTermElabM <| withoutExporting do
            let creation ← if creation.isEmpty && !relevant.contains n then pure creation else do
              let found ← match applicationUses.get? n with
                | some found => pure found
                | none => allocatorUses env n contractSet relevant
              pure (allocatorApplications n creation found)
            statementJson n c.type creation
          pure (conclusionShape 8 c.type, statementDependencies c.type, shape)
        | none => pure (Json.null, [], Json.null)
      theorems := theorems.push <| Json.mkObj <| [
        ("name", toJson n.toString), ("module", toJson (moduleOf env n)),
        ("axioms", namesJson axs), ("conclusion", conclusion)] ++ statement ++
        [("statement", shape)]
    let result := Json.mkObj <| [
      ("schema_version", toJson (1 : Nat)), ("modules", toJson selected),
      ("module_imports", Json.mkObj moduleImports.toList),
      ("theorems", Json.arr theorems), ("project_declarations", namesJson declarations),
      ("nodes", Json.arr (graph env (if seedAll then selectedDeclarations.toList ++ roots.toList ++ declarations.toList
        else roots.toList ++ declarations.toList)))] ++
      if seedAll then [("selected_declaration_roots", namesJson selectedDeclarations),
        ("selected_declaration_evidence", Json.arr framework)] else []
    liftIO <| IO.println ("AIR2LEAN_ASSURANCE_JSON:" ++ result.compress)

end Air2Lean.Assurance
