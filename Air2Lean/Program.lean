import Air2Lean.ModelRegistry
import Init.Data.Array.Find
import Init.Data.Array.Lemmas

/-!
# Original source programs

The emitter, reference semantics and certificates share this finite original program. Its
memory effects, concurrency effects and recursive call groups are derived from the complete
source functions and validated external-model bindings, before helper extraction or certificate
fragmentation. There is no second lookup or independently selectable instrumentation policy.
-/

namespace Air2Lean

namespace Graph

/-- Keep the first occurrence of each graph key, retaining successor order. -/
def dedupKeys {κ : Type} [BEq κ] (a : Array κ) : Array κ :=
  a.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

/-- Prepare one finite adjacency table from the producer's nodes and references. References to
external declarations are excluded from this graph; they cannot form a component with its nodes. -/
private def successorsBy {α κ : Type} [BEq κ] (nodes : Array α) (key : α → κ)
    (successors : α → Array κ) : κ → Array κ :=
  let keys := nodes.map key
  let edges := nodes.map fun node =>
    (key node, dedupKeys ((successors node).filter keys.contains))
  fun k => ((edges.find? (·.1 == k)).map (·.2)).getD #[]

/-- The single bounded DFS used by both source-function and emitted-declaration graphs. -/
private def topoVisitCore {α κ : Type} [BEq κ] (nodes : Array α) (key : α → κ)
    (next : κ → Array κ) (vo : Array κ × Array α) (name : κ) : Array κ × Array α :=
  let rec visit : Nat → (Array κ × Array α) → κ → Array κ × Array α
    | 0, state, _ => state
    | depth + 1, (visited, order), name =>
      if visited.contains name then (visited, order)
      else
        let visited := visited.push name
        match nodes.find? (fun node => key node == name) with
        | none => (visited, order)
        | some node =>
          let (visited, order) := (next name).foldl (visit depth) (visited, order)
          (visited, order.push node)
  -- A descent expands a new node key. The extra step processes the final already-visited
  -- or absent key after at most `nodes.size` expansions.
  visit (nodes.size + 1) vo name

private def topoOrderCore {α κ : Type} [BEq κ] (nodes : Array α) (key : α → κ)
    (next : κ → Array κ) : Array α :=
  ((nodes.map key).foldl (topoVisitCore nodes key next) (#[], #[])).2

private def reachableCore {κ : Type} [BEq κ] (keys : Array κ) (nextOf : κ → Array κ)
    (name : κ) : Array κ := Id.run do
  let mut seen := #[]
  let mut todo := [name]
  -- Each successor is in `keys` and is added to `seen` before another node is processed.
  -- It is enqueued once; only the initial key can occur once more through a cycle.
  for _ in [:keys.size + 1] do
    let n :: rest := todo | return seen
    let next := (nextOf n).toList.filter (!seen.contains ·)
    seen := seen ++ next.toArray
    todo := rest ++ next
  return seen

def topoOrderBy {α κ : Type} [BEq κ] (nodes : Array α) (key : α → κ)
    (successors : α → Array κ) : Array α :=
  topoOrderCore nodes key (successorsBy nodes key successors)

/-- The internal node keys reachable by one or more edges, in discovery order. -/
def reachableBy {α κ : Type} [BEq κ] (nodes : Array α) (key : α → κ)
    (successors : α → Array κ) (name : κ) : Array κ :=
  reachableCore (nodes.map key) (successorsBy nodes key successors) name

/-- Ordered strongly connected components, with the original DFS ordering. A component is
emitted at its last member in DFS post-order; members retain that post-order. The Boolean is
true exactly for a multi-node component or a positive self-path. One derived adjacency table
is shared by reachability and ordering. -/
def callGroupsBy {α κ : Type} [BEq κ] (nodes : Array α) (key : α → κ)
    (successors : α → Array κ) : Array (Array α × Bool) :=
  let keys := nodes.map key
  let next := successorsBy nodes key successors
  let reach := keys.map fun n => (n, reachableCore keys next n)
  let reaches (a b : κ) : Bool :=
    ((reach.find? (·.1 == a)).map (·.2.contains b)).getD false
  let order := topoOrderCore nodes key next
  -- A group is complete at its last member in DFS post-order (the member where the DFS entered
  -- the group), and everything that the group calls is finished before that point.
  let (_, groups) := order.foldl (init := ((#[] : Array κ), (#[] : Array (Array α × Bool))))
    fun (done, groups) node =>
      let name := key node
      let done := done.push name
      let members := order.filter fun other =>
        key other == name || (reaches name (key other) && reaches (key other) name)
      if members.all (fun member => done.contains (key member)) &&
          !groups.any (fun group => group.1.any (fun member => key member == name)) then
        (done, groups.push (members, members.size > 1 || reaches name name))
      else (done, groups)
  groups

/-- The adjacency table depends only on the projected node fields. -/
private theorem successorsBy_map {A B K : Type} [BEq K]
    (nodes : Array A) (project : A → B) (key : B → K) (next : B → Array K) :
    successorsBy (nodes.map project) key next =
      successorsBy nodes (fun x => key (project x)) (fun x => next (project x)) := by
  simp only [successorsBy, Array.map_map, Function.comp_def]

/-- Naturality of the existing bounded walk, with its fuel left unchanged. -/
private theorem topoVisitCore_visit_map {A B K : Type} [BEq K]
    (nodes : Array A) (project : A → B) (key : B → K) (next : K → Array K)
    (fuel : Nat) (visited : Array K) (order : Array A) (name : K) :
    topoVisitCore.visit (nodes.map project) key next fuel
        (visited, order.map project) name =
      let r := topoVisitCore.visit nodes (fun x => key (project x)) next fuel
        (visited, order) name
      (r.1, r.2.map project) := by
  induction fuel generalizing visited order name with
  | zero => rfl
  | succ fuel ih =>
    by_cases hseen : visited.contains name
    · simp only [topoVisitCore.visit, hseen, if_pos]
    · simp only [topoVisitCore.visit, hseen, Bool.false_eq_true, ite_false,
        Array.find?_map, Function.comp_def]
      cases hfind : nodes.find? (fun x => key (project x) == name) with
      | none => simp only [hfind, Option.map_none]
      | some node =>
        simp only [hfind, Option.map_some]
        let liftState : Array K × Array A → Array K × Array B :=
          fun state => (state.1, state.2.map project)
        have hfold :
            (next name).foldl (topoVisitCore.visit (nodes.map project) key next fuel)
                (visited.push name, order.map project) =
              liftState ((next name).foldl
                (topoVisitCore.visit nodes (fun x => key (project x)) next fuel)
                (visited.push name, order)) := by
          exact Array.foldl_hom liftState
            (xs := next name) (init := (visited.push name, order))
            (g₁ := topoVisitCore.visit nodes (fun x => key (project x)) next fuel)
            (g₂ := topoVisitCore.visit (nodes.map project) key next fuel)
            (fun state target => by
              rcases state with ⟨seen, ordered⟩
              exact ih seen ordered target)
        rw [hfold]
        simp only [liftState, Array.map_push]

private theorem topoVisitCore_map {A B K : Type} [BEq K]
    (nodes : Array A) (project : A → B) (key : B → K) (next : K → Array K)
    (visited : Array K) (order : Array A) (name : K) :
    topoVisitCore (nodes.map project) key next (visited, order.map project) name =
      let r := topoVisitCore nodes (fun x => key (project x)) next (visited, order) name
      (r.1, r.2.map project) := by
  simpa only [topoVisitCore, Array.size_map] using
    topoVisitCore_visit_map nodes project key next (nodes.size + 1) visited order name

private theorem topoOrderCore_map {A B K : Type} [BEq K]
    (nodes : Array A) (project : A → B) (key : B → K) (next : K → Array K) :
    topoOrderCore (nodes.map project) key next =
      (topoOrderCore nodes (fun x => key (project x)) next).map project := by
  let liftState : Array K × Array A → Array K × Array B :=
    fun state => (state.1, state.2.map project)
  have hfold := Array.foldl_hom liftState
    (xs := nodes.map (fun x => key (project x)))
    (init := (#[], #[]))
    (g₁ := topoVisitCore nodes (fun x => key (project x)) next)
    (g₂ := topoVisitCore (nodes.map project) key next)
    (fun state target => by
      rcases state with ⟨seen, ordered⟩
      exact topoVisitCore_map nodes project key next seen ordered target)
  simpa only [topoOrderCore, Array.map_map, Function.comp_def, liftState, Array.map_empty]
    using congrArg Prod.snd hfold

/-- Mapping node payloads preserves the existing ordered components. Keys, successors,
fuel, ordering and the recursive flag all come from the same graph computation. -/
theorem callGroupsBy_map {A B K : Type} [BEq K]
    (nodes : Array A) (project : A → B) (key : B → K) (next : B → Array K) :
    callGroupsBy (nodes.map project) key next =
      (callGroupsBy nodes (fun x => key (project x)) (fun x => next (project x))).map
        (fun (members, recursive) => (members.map project, recursive)) := by
  simp only [callGroupsBy, successorsBy_map, Array.map_map, Function.comp_def,
    topoOrderCore_map]
  rw [Array.foldl_map]
  let liftGroups :
      Array K × Array (Array A × Bool) → Array K × Array (Array B × Bool) :=
    fun state =>
      (state.1, state.2.map (fun (members, recursive) => (members.map project, recursive)))
  let keys := nodes.map (fun node => key (project node))
  let nextOf := successorsBy nodes (fun node => key (project node)) (fun node => next (project node))
  let reach := nodes.map fun node =>
    (key (project node), reachableCore keys nextOf (key (project node)))
  let reaches (a b : K) : Bool :=
    ((reach.find? (·.1 == a)).map (·.2.contains b)).getD false
  let order := topoOrderCore nodes (fun node => key (project node)) nextOf
  let stepA : Array K × Array (Array A × Bool) → A →
      Array K × Array (Array A × Bool) := fun (done, groups) node =>
    let name := key (project node)
    let done := done.push name
    let members := order.filter fun other =>
      key (project other) == name ||
        (reaches name (key (project other)) && reaches (key (project other)) name)
    if members.all (fun member => done.contains (key (project member))) &&
        !groups.any (fun group => group.1.any (fun member => key (project member) == name)) then
      (done, groups.push (members, members.size > 1 || reaches name name))
    else (done, groups)
  let stepB : Array K × Array (Array B × Bool) → A →
      Array K × Array (Array B × Bool) := fun (done, groups) node =>
    let name := key (project node)
    let done := done.push name
    let members := (order.map project).filter fun other =>
      key other == name || (reaches name (key other) && reaches (key other) name)
    if members.all (fun member => done.contains (key member)) &&
        !groups.any (fun group => group.1.any (fun member => key member == name)) then
      (done, groups.push (members, members.size > 1 || reaches name name))
    else (done, groups)
  change (order.foldl stepB (#[], #[])).2 =
    ((order.foldl stepA (#[], #[])).2.map
      (fun (members, recursive) => (members.map project, recursive)))
  have hfold := Array.foldl_hom liftGroups
    (xs := order) (init := (#[], #[])) (g₁ := stepA) (g₂ := stepB)
    (fun state node => by
      rcases state with ⟨done, groups⟩
      simp only [stepA, stepB, liftGroups, Array.filter_map, Array.any_map, Array.all_map,
        Array.map_map, Function.comp_def, Array.map_push]
      simp only [Array.size_map]
      split <;> simp_all only [Array.map_push, Bool.false_eq_true, ite_false, ite_true])
  simpa only [liftGroups, Array.map_empty] using congrArg Prod.snd hfold

end Graph

def dedupNames (a : Array String) : Array String := Graph.dedupKeys a

def calleesOf (allNames : Array String) (refs : Array (String × String)) (f : Func) :
    Array String :=
  -- A call with a comptime function argument (`comptime_fn`: a spawned worker, an `Io.async`
  -- task, or any generic instance's function argument) has two edges: the callee itself, when it
  -- is a source function (a generic instance calling itself is recursive), and the function
  -- argument, which runs under the call (the std spawn wrappers are not source functions).
  let direct := f.allInsts.flatMap fun i => match i.op with
    | .call (.func nm _ spawnFn) _ => (#[nm] ++ spawnFn.toArray).filter allNames.contains
    | _ => #[]
  dedupNames (direct ++ (f.indirectCallees refs).filter allNames.contains)

/-- DFS post-order over the original call graph. The explicit-name API retains absent keys in
its visited set, as before; complete-program callers use `Graph.topoOrderBy` below. -/
def topoVisit (funcs : Array Func) (allNames : Array String) (refs : Array (String × String))
    (vo : Array String × Array Func) (name : String) : Array String × Array Func :=
  Graph.topoVisitCore funcs (·.name) (fun n =>
    ((funcs.find? (·.name == n)).map (calleesOf allNames refs)).getD #[]) vo name

def topoOrder (funcs : Array Func) : Array Func :=
  Graph.topoOrderBy funcs (·.name) (calleesOf (funcs.map (·.name)) (fnRefs funcs))

/-- Every original function name reachable from `name` by one or more calls. -/
def reachable (funcs : Array Func) (allNames : Array String) (refs : Array (String × String))
    (name : String) : Array String :=
  Graph.reachableCore allNames (fun n =>
    ((funcs.find? (·.name == n)).map (calleesOf allNames refs)).getD #[]) name

/-- The original source-function components; effect and cost policy never use the emitted
declaration graph. -/
def callGroups (funcs : Array Func) : Array (Array Func × Bool) :=
  Graph.callGroupsBy funcs (·.name) (calleesOf (funcs.map (·.name)) (fnRefs funcs))

/-- A complete normalized source program and its validated project-model bindings. The CLI
constructs this after checking the whole program; reified semantics retain every original body,
including functions outside an individual certificate's supported fragment. -/
structure Program where
  funcs : Array Func
  models : Array ModelBinding := #[]

/-- Lookup never invents a body for an absent source function. -/
def Program.lookup (p : Program) (name : String) : Option Func :=
  p.funcs.find? (·.name == name)

def Program.memFuncs (p : Program) : Array String :=
  memoryFunctions p.funcs (p.models.map (·.symbol))

def Program.concFuncs (p : Program) : Array String :=
  concFunctions p.funcs

def Program.groups (p : Program) : Array (Array Func × Bool) :=
  callGroups p.funcs

/-- `name` is a member of a recursive group of `groups`. -/
def recursiveIn (groups : Array (Array Func × Bool)) (name : String) : Bool :=
  groups.any fun (members, recursive) => recursive && members.any (·.name == name)

def Program.recursive (p : Program) (name : String) : Bool :=
  recursiveIn p.groups name

def Program.usesMemory (p : Program) (name : String) : Bool :=
  p.memFuncs.contains name

def Program.concurrent (p : Program) (name : String) : Bool :=
  p.concFuncs.contains name

/-- Every memory/concurrent loop iteration pays one tick, including its final exit. -/
def Program.ticked (p : Program) (name : String) : Bool :=
  p.usesMemory name || p.concurrent name

/-- A recursive original memory/concurrent function also pays one entry tick. Extracted loop
helpers use the original function's classification and do not introduce another entry. -/
def Program.entryTicked (p : Program) (name : String) : Bool :=
  p.recursive name && p.ticked name

/-- A function's step-tick policy: one tick per loop-body run (`loop`) and one per entry
(`entry`). The emitter reads it from the same `Program` as the semantics (`tickPolicy`). -/
structure TickPolicy where
  loop : Bool := false
  entry : Bool := false
  deriving Inhabited, DecidableEq, Repr

/-- The policy of a function from its classification: the formula of `Program.ticked` and
`Program.entryTicked` (`Program.tickPolicy_eq`), also used by standalone emission. -/
def TickPolicy.of (recursive mem conc : Bool) : TickPolicy :=
  { loop := mem || conc, entry := recursive && (mem || conc) }

def Program.tickPolicy (p : Program) (name : String) : TickPolicy :=
  { loop := p.ticked name, entry := p.entryTicked name }

theorem Program.tickPolicy_eq (p : Program) (name : String) :
    p.tickPolicy name = TickPolicy.of (p.recursive name) (p.usesMemory name) (p.concurrent name) :=
  rfl

/-- The policy of every function, the call groups and classifications computed once (`let`):
the table the emitter reads and an AIR certificate states in one kernel evaluation. -/
def Program.tickPolicies (p : Program) : Array (String × TickPolicy) :=
  let groups := p.groups
  let mem := p.memFuncs
  let conc := p.concFuncs
  p.funcs.map fun f =>
    (f.name, TickPolicy.of (recursiveIn groups f.name) (mem.contains f.name) (conc.contains f.name))

/-- Every entry of the table is the policy of its name (`Program.tickPolicy`), whatever the
table was computed to be (`h`, by one kernel evaluation in a certificate). -/
theorem Program.tickPolicy_of_tickPolicies {p : Program} {xs : Array (String × TickPolicy)}
    (h : p.tickPolicies = xs) (i : Nat) (hi : i < xs.size) :
    p.tickPolicy xs[i].1 = xs[i].2 := by
  subst h
  simp only [tickPolicies, Array.getElem_map]
  rfl

end Air2Lean
