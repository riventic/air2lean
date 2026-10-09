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
(`naEnter`), marks each instruction with its roots (`naMark`: the root of its reads and of its
writes) and closes the scope before it returns (`naExit`). The scope logs every access of the
call from the footprint (`Mem.footprint`), including the accesses of the functions it calls,
which the mark of the call gives the root `none`. A logged access that overlaps an access with
another root, one of them a write, throws `.illegal`.
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

/-- Move the footprint entries after `sc.seen` into the log, with the roots `sc.cur`. An entry
that conflicts with a logged access throws `.illegal`. -/
def NaScope.flush (sc : NaScope) (fp : Array FootprintEntry) : Except Error NaScope := do
  let mut log := sc.log
  for f in fp.extract sc.seen fp.size do
    let write := f.kind.isWrite
    let e : NaEntry :=
      { block := f.block, off := f.off, len := f.len, write,
        root := if write then sc.cur.2 else sc.cur.1 }
    if log.any e.conflicts then throw .illegal
    log := log.push e
  pure { sc with seen := fp.size, log }

/-- The next instruction's accesses: reads based on `readRoot`, writes on `writeRoot`. The
accesses since the last mark are logged first (`NaScope.flush`). Does nothing outside a scope. -/
def naMark (readRoot writeRoot : Option Nat) : MemM Unit := do
  let m ← get
  match m.naTop? with
  | none => pure ()
  | some k =>
    match m.noalias[k]!.flush m.footprint with
    | .error e => throw e
    | .ok sc => set { m with noalias := m.noalias.set! k { sc with cur := (readRoot, writeRoot) } }

/-- Open the scope of a call of a function with `noalias` parameters. -/
def naEnter : MemM Unit :=
  modify fun m => { m with noalias := m.noalias.push { tid := m.current, seen := m.footprint.size } }

/-- Close the scope before the call returns: its last accesses are logged first. -/
def naExit : MemM Unit := do
  naMark none none
  let m ← get
  match m.naTop? with
  | none => pure ()
  | some k => set { m with noalias := m.noalias.eraseIdxIfInBounds k }

end Zig
