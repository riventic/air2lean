import Air2Lean.CanonCertificate
import Air2Lean.Air.Normalize
import Air2Lean.Check
import Init.Data.Array.Bootstrap

/-!
Audit regression: full live-ID renumbering cannot preserve `Sem.execFunc` for the same
arbitrary oracle. This is a counterexample to that proposed compiler-correctness equality,
not a native Zig or whole-program execution counterexample. The checked identity callee
does not manufacture a caller cell; the unrestricted per-function oracle does.
-/

namespace CanonRenumberOracle

open Air2Lean Air2Lean.Sem

def caller (base : Nat) (identities : Array Identity.Record := #[]) : Func :=
  { dialect := .ofVersion .v0_17_0, name := "canon.caller", params := #[1], ret := 0,
    types := #[.bool, .ptr "one" false 0, .void, .noreturn],
    layouts := #[{ size := some 1, align := some 1 },
      { size := some 8, align := some 8, ptrAlign := some 1 },
      { size := some 0, align := some 1 }, {}],
    globals := #[], identities,
    body := #[
      ⟨base, 1, .arg 0⟩,
      ⟨base + 1, 1, .alloc⟩,
      ⟨base + 2, 2, .store (.inst (base + 1)) (.bool false)⟩,
      ⟨base + 3, 2, .store (.inst (base + 1)) (.bool true)⟩,
      ⟨base + 4, 1, .call (.func "canon.identity" false none) #[.inst base]⟩,
      ⟨base + 5, 0, .load (.inst (base + 4))⟩,
      ⟨base + 6, 3, .ret (.inst (base + 5))⟩] }

def identity : Func :=
  { (caller 0) with
    name := "canon.identity"
    ret := 1
    body := #[⟨0, 1, .arg 0⟩, ⟨1, 3, .ret (.inst 0)⟩] }

/-- Both executions retain the complete original source program as their classification
context. Changing a live ID is the proposed transformation under test, not a second
choice of execution policy. -/
def program (records : Array Identity.Record) : Program :=
  { funcs := #[caller 10 records, identity] }

private theorem caller_allInsts (base : Nat) (records : Array Identity.Record) :
    (caller base records).allInsts = (caller base records).body := by
  rw [Func.allInsts, ← Array.foldl_toList]
  simp only [caller, List.foldl_cons, List.foldl_nil, flattenInst]
  simp only [flattenOp, Op.call_control_bodies, Op.effects, Op.effectsIn,
    Effects.pure, Effects.placeAccess, Effects.flow, Control.bodies,
    Array.attach_empty, Array.foldl_empty] <;> rfl

private theorem identity_allInsts : identity.allInsts = identity.body := by
  rw [Func.allInsts, ← Array.foldl_toList]
  simp only [identity, List.foldl_cons, List.foldl_nil, flattenInst]
  simp only [flattenOp, Op.call_control_bodies, Op.effects, Op.effectsIn,
    Effects.pure, Effects.placeAccess, Effects.flow, Control.bodies,
    Array.attach_empty, Array.foldl_empty] <;> rfl

private theorem caller_edges (base : Nat) (records : Array Identity.Record) :
    calleesOf #["canon.caller", "canon.identity"] #[] (caller base records) =
      #["canon.identity"] := by
  simp only [calleesOf, Func.indirectCallees, caller_allInsts]
  apply Array.ext'
  simp only [dedupNames, Graph.dedupKeys, ← Array.foldl_toList,
    Array.toList_append, Array.toList_flatMap, Array.toList_filter,
    Option.toArray_none, Option.toArray_some,
    caller, Func.calleeValFnTy?, Array.toList_push, Array.toList_empty,
    List.append_nil, List.nil_append, List.filterMap_cons, List.filterMap_nil,
    List.flatMap_cons, List.flatMap_nil, List.filter_cons, List.filter_nil,
    List.foldl_cons, List.foldl_nil]
  simp only [← Array.contains_toList, List.contains_cons, List.contains_nil,
    beq_self_eq_true, Bool.or_true, Bool.or_false, List.foldl_cons, List.foldl_nil,
    Array.toList_push, Array.toList_empty, List.nil_append,
    Bool.false_eq_true, ite_false, ite_true] <;> rfl

private theorem identity_edges :
    calleesOf #["canon.caller", "canon.identity"] #[] identity = #[] := by
  simp only [calleesOf, Func.indirectCallees, identity_allInsts] <;> rfl

/-- The actual source graph, retaining arbitrary identity records in its original nodes. -/
private theorem program_rows (records : Array Identity.Record) :
    (program records).funcs.map (fun f =>
      (f.name, calleesOf ((program records).funcs.map (·.name))
        (fnRefs (program records).funcs) f)) =
      #[("canon.caller", #["canon.identity"]), ("canon.identity", #[])] := by
  have hnames : (program records).funcs.map (·.name) =
      #["canon.caller", "canon.identity"] := by
    apply Array.ext'
    simp only [Array.toList_map, program, caller, identity, List.map_cons, List.map_nil]
  have hrefs : fnRefs (program records).funcs = #[] := by rfl
  rw [hnames, hrefs]
  apply Array.ext'
  simp only [Array.toList_map, program, List.map_cons, List.map_nil,
    caller_edges, identity_edges]
  rfl

private theorem recursive_false_of_rows (records : Array Identity.Record)
    (hrows : (program records).funcs.map (fun f =>
      (f.name, calleesOf ((program records).funcs.map (·.name))
        (fnRefs (program records).funcs) f)) =
      #[("canon.caller", #["canon.identity"]), ("canon.identity", #[])]) :
    (program records).recursive "canon.caller" = false := by
  let nodes := (program records).funcs
  let project (f : Func) :=
    (f.name, calleesOf (nodes.map (·.name)) (fnRefs nodes) f)
  let observe (groups : Array (Array (String × Array String) × Bool)) :=
    groups.any fun (members, recursive) =>
      recursive && members.any (fun member => member.1 == "canon.caller")
  have hmapped := congrArg observe
    (Graph.callGroupsBy_map nodes project Prod.fst Prod.snd)
  have hrecursive : (program records).recursive "canon.caller" =
      observe (Graph.callGroupsBy (nodes.map project) Prod.fst Prod.snd) := by
    simpa only [observe, nodes, project, Program.recursive, recursiveIn, Program.groups, callGroups,
      Array.any_map, Function.comp_def] using hmapped.symm
  rw [hrecursive]
  change observe (Graph.callGroupsBy ((program records).funcs.map (fun f =>
    (f.name, calleesOf ((program records).funcs.map (·.name))
      (fnRefs (program records).funcs) f))) Prod.fst Prod.snd) = false
  rw [hrows]
  decide +kernel

theorem entry_unticked (records : Array Identity.Record) :
    (program records).entryTicked "canon.caller" = false := by
  have hrecursive := recursive_false_of_rows records (program_rows records)
  simp only [Program.entryTicked, hrecursive, Bool.false_and]

def oracle : Oracle := fun _ _ => pure (.cell 11)

theorem identity_not_panic : panicOf? "canon.identity" = none := by rfl

theorem before_run (records : Array Identity.Record) (m : Zig.Mem) (p : Zig.Ptr) :
    ((execFunc (program records) oracle (caller 10 records) [.ptr p]).run m).run =
      some (.ok (.bool true, m)) := by
  simp only [caller, oracle, air_sem, entry_unticked, Nat.reduceAdd, identity_not_panic] <;> rfl

theorem after_run (records : Array Identity.Record) (m : Zig.Mem) (p : Zig.Ptr) :
    ((execFunc (program records) oracle (caller 0 records) [.ptr p]).run m).run =
      some (.error .unspecified) := by
  simp only [caller, oracle, air_sem, entry_unticked, Nat.reduceAdd, identity_not_panic] <;> rfl

theorem same_oracle_not_preserved (records : Array Identity.Record) (m : Zig.Mem) (p : Zig.Ptr) :
    (execFunc (program records) oracle (caller 10 records) [.ptr p]).run m ≠
      (execFunc (program records) oracle (caller 0 records) [.ptr p]).run m := by
  intro h
  have h' := congrArg (fun r => r.run) h
  rw [before_run, after_run] at h'
  cases h'

def source : String := r#"{
  "schema": 11, "zig_version": "0.17.0", "name": "canon.caller", "params": [1], "ret": 0,
  "types": [
    {"k": "bool", "abi_size": 1, "abi_align": 1},
    {"k": "ptr", "size": "one", "const": false, "child": 0,
     "abi_size": 8, "abi_align": 8, "ptr_align": 1},
    {"k": "void", "abi_size": 0, "abi_align": 1}, {"k": "noreturn"}],
  "body": [
    {"id": 10, "tag": "arg", "ty": 1, "param": 0},
    {"id": 11, "tag": "alloc", "ty": 1},
    {"id": 12, "tag": "store", "ty": 2, "args": [{"inst": 11}, {"ty": 0, "val": "false"}]},
    {"id": 13, "tag": "store", "ty": 2, "args": [{"inst": 11}, {"ty": 0, "val": "true"}]},
    {"id": 14, "tag": "call", "ty": 1, "callee": {"func": "canon.identity"}, "args": [{"inst": 10}]},
    {"id": 15, "tag": "load", "ty": 0, "args": [{"inst": 14}]},
    {"id": 16, "tag": "ret", "ty": 3, "args": [{"inst": 15}]}]
}"#

-- Native acceptance/binding checks are separate from the kernel-checked non-equality.
-- Two stores keep the preceding copy-forwarding pass from deleting the local.
#eval IO.ofExcept do
  let raw ← Raw.parseFile source
  Raw.validateRefs raw
  let before ← normalizeCanonical raw
  let after ← normalizeCanonical (Raw.renumber raw)
  unless CanonCertificate.sameFunction before (caller 10 raw.identities) do
    throw "decoding did not produce the counterexample source"
  unless CanonCertificate.sameFunction after (caller 0 raw.identities) do
    throw "renumbering did not produce the counterexample target"
  unless CanonCertificate.sameFunction (← normalize raw) (caller 0 raw.identities) do
    throw "another canonicalization pass changed the counterexample"
  checkProgram #[before, identity]
  checkProgram #[after, identity]

end CanonRenumberOracle
