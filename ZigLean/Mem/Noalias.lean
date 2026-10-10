import ZigLean.Mem.Basic

/-!
# `noalias` parameters

Zig lowers a `noalias` parameter (a pointer or slice, `fn f(noalias p: *T)`) to LLVM's
`noalias` argument attribute. During a call, memory that is accessed through a pointer based
on the parameter must not also be accessed through a pointer not based on it, if one of the
two accesses writes. Anything else is illegal behaviour (`docs/illegal-behavior.md`).

The translator finds, for every instruction of such a function, the parameter that the
pointer of each of its accesses is based on (its *root*, `Air2Lean/Noalias.lean`); it rejects
the function when that is not one parameter or none. The generated function opens a scope
(`naEnter`), and right after each instruction that can touch memory it marks that
instruction's roots (`naMark`: the root of its reads and of its writes). The mark logs the
instruction's accesses from the footprint (`Mem.footprint`), including the accesses of the
functions it calls, which the mark of the call gives the root `none`, and throws `.illegal` at
once for an access that overlaps a logged access with another root, one of them a write.
Every function that such a function may call marks its own accesses too (root `none`), so a
later failure cannot take the place of a violation. `naExit` closes the scope before the call
returns.
-/

namespace Zig

/-- `e` and `l` are a `noalias` violation: their bytes overlap, one of them writes, and exactly
one of them is based on some `noalias` parameter (different roots). -/
def NaEntry.conflicts (e l : NaEntry) : Bool :=
  e.root != l.root && (e.write || l.write) && e.block == l.block && e.len != 0 && l.len != 0 &&
    e.off < l.off + l.len && l.off < e.off + e.len

/-- The index in `Mem.noalias` of the current thread's innermost scope. -/
def Mem.naTop? (m : Mem) : Option Nat :=
  (List.range m.noalias.size).reverse.find? fun k => m.noalias[k]!.tid == m.current

/-- Move the footprint entries after `sc.seen` into the log: reads with the root `readRoot`,
writes with `writeRoot`. An entry that conflicts with a logged access throws `.illegal`. -/
def NaScope.flush (sc : NaScope) (fp : Array FootprintEntry) (readRoot writeRoot : Option Nat) :
    Except Error NaScope := do
  let mut log := sc.log
  for f in fp.extract sc.seen fp.size do
    let write := f.kind.isWrite
    let e : NaEntry :=
      { block := f.block, off := f.off, len := f.len, write,
        root := if write then writeRoot else readRoot }
    if log.any e.conflicts then throw .illegal
    log := log.push e
  pure { sc with seen := fp.size, log }

/-- After an instruction: its accesses (the footprint entries since the last mark) are checked
against the log of every scope of the current thread and logged (`NaScope.flush`). In the
innermost scope they are reads based on `readRoot` and writes based on `writeRoot`. In an outer
scope they are based on none of its parameters: the call that leads to the inner one passes it
no pointer based on them. Does nothing outside a scope. -/
def naMark (readRoot writeRoot : Option Nat) : MemM Unit := do
  let m ← get
  match m.naTop? with
  | none => pure ()
  | some top =>
    let mut scopes := m.noalias
    for k in [0:scopes.size] do
      if scopes[k]!.tid != m.current then continue
      let (r, w) := if k == top then (readRoot, writeRoot) else (none, none)
      match scopes[k]!.flush m.footprint r w with
      | .error e => throw e
      | .ok sc => scopes := scopes.set! k sc
    set { m with noalias := scopes }

/-- Open the scope of a call of a function with `noalias` parameters. -/
def naEnter : MemM Unit :=
  modify fun m => { m with noalias := m.noalias.push { tid := m.current, seen := m.footprint.size } }

/-- Close the scope before the call returns. Every access of the call has been checked by the
mark after its instruction. -/
def naExit : MemM Unit :=
  modify fun m => match m.naTop? with
    | none => m
    | some k => { m with noalias := m.noalias.eraseIdxIfInBounds k }

end Zig
