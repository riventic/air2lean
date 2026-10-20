import Air2Lean.ModelRegistry

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

/-- DFS post-order, preserving node order and first-occurrence successor order. -/
def topoVisitBy {α κ : Type} [BEq κ] (nodes : Array α) (key : α → κ)
    (successors : α → Array κ) (vo : Array κ × Array α) (name : κ) : Array κ × Array α :=
  topoVisitCore nodes key (successorsBy nodes key successors) vo name

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

end Graph

def dedupNames (a : Array String) : Array String := Graph.dedupKeys a

def calleesOf (allNames : Array String) (refs : Array (String × String)) (f : Func) :
    Array String :=
  let direct := f.allInsts.filterMap fun i => match i.op with
    -- The original source edge is the spawned worker, not the absent std wrapper.
    | .call (.func nm _ (some spawnFn)) _ =>
      if allNames.contains spawnFn then some spawnFn
      else if allNames.contains nm then some nm else none
    | .call (.func nm ..) _ => if allNames.contains nm then some nm else none
    | _ => none
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

def Program.recursive (p : Program) (name : String) : Bool :=
  p.groups.any fun (members, recursive) => recursive && members.any (·.name == name)

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

end Air2Lean
