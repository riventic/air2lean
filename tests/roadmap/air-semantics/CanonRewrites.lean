import Air2Lean.Air.Canon

/-!
The side conditions of the Canon rewrites that have no preservation theorem (V02; the killing
check of the `canon` mutants of `mutations.py`, Q02).

Each certificate names these rewrites as trusted (`trusted-Canon`, docs/air-semantics.md): the
theorems are over the canonical AIR. Until a rewrite has its theorem, this file holds for each one
a hand-built raw function on which the rewrite's own condition decides the outcome:

* a rewrite that drops, forwards or moves an instruction must leave unchanged a function that
  differs from its pattern in exactly the condition that makes the rewrite meaning-preserving
  (a read before the copy's store, a write between a load and its item read, a signed `0 <= x`,
  a read placeholder or lane pointer, a load that is no pointer formation);
* a rewrite that only renames or renumbers must give the one right result (an integer `bit_and`
  stays, an `arg` takes its runtime slot, a call receives the error return trace).

These are negative tests of the rewrites, not preservation proofs: the rewrites stay trusted.
`lean --run` prints one `check ok <name>` or `check FAILED <name>` line per check and fails when
any check failed.
-/

namespace CanonRewrites

open Air2Lean Air2Lean.Raw

def tU8 : TyId := 0
def tI32 : TyId := 1
def tBool : TyId := 2
def tVoid : TyId := 3
def tNoret : TyId := 4
def tPU8 : TyId := 5
def tPConst : TyId := 6
def tCPtr : TyId := 7
def tU64 : TyId := 8
def tArr : TyId := 9
def tPArr : TyId := 10
def tLane : TyId := 11
def tTrace : TyId := 12

def types : Array Ty := #[
  .int false 8, .int true 32, .bool, .void, .noreturn, .ptr "one" false tU8, .ptr "one" true tU8,
  .ptr "c" false tU8, .int false 64, .array 4 tU8 false, .ptr "one" false tArr,
  .ptr "one" false tU8, .optional tPU8]

def ptrLayout : Layout := { size := some 8, align := some 8, ptrAlign := some 1 }

def layouts : Array Layout := #[
  { size := some 1, align := some 1 }, { size := some 4, align := some 4 },
  { size := some 1, align := some 1 }, { size := some 0, align := some 1 }, {}, ptrLayout, ptrLayout,
  ptrLayout, { size := some 8, align := some 8 }, { size := some 4, align := some 1 }, ptrLayout,
  { ptrLayout with runtimeLane := true }, { size := some 8, align := some 8 }]

def inst (id : InstId) (tag : String) (ty : TyId) (args : Array Val := #[]) : RawInst :=
  { id, tag, ty := some ty, args, body := #[], thenBody := #[], elseBody := #[], cases := #[],
    target := none, param := none, callee := none, index := none, name := none, line := none,
    order := none, rmwOp := none, successOrder := none, failureOrder := none, op := none,
    mask := #[], asm := none, unsupported := false }

def arg (id : InstId) (ty : TyId) (param : Nat) : RawInst := { inst id "arg" ty with param := some param }

def ret (id : InstId) (v : Val) : RawInst := inst id "ret" tNoret #[v]

def fn (version : ZigVersion) (params : Array TyId) (body : Array RawInst) : RawFunc :=
  { schema := 12, version? := some version,
    profile := { name := "abi64-le-v1", schema := 12, zigVersion := version.toString },
    name := "canon.f", params, ret := tU8, body, types, layouts, globals := #[] }

/-- Sema's safety check of the condition `c`: `block { cond_br c { br } else { unreach } }`, the
block `id` and the three instructions after it. -/
def check (id : InstId) (c : InstId) : RawInst :=
  { inst id "block" tVoid with
    body := #[{ inst (id + 1) "cond_br" tNoret #[.inst c] with
      thenBody := #[{ inst (id + 2) "br" tNoret #[.void] with target := some id }],
      elseBody := #[inst (id + 3) "unreach" tNoret] }] }

def tagOf (f : RawFunc) (id : InstId) : Option String := ((flatten f.body).find? (·.id == id)).map (·.tag)

/-- `a & b` at the type `t`, as Zig 0.17.1 writes it. -/
def bitAnd (t : TyId) : RawFunc :=
  fn .v0_17_1 #[t, t] #[arg 0 t 0, arg 1 t 1, inst 2 "bit_and" t #[.inst 0, .inst 1], ret 3 (.inst 2)]

/-- A runtime parameter after a `void` one and five `comptime` ones: source index 5, slot 1. -/
def ranked : RawFunc := fn .v0_16_0 #[tVoid, tU8] #[arg 0 tU8 5, ret 1 (.inst 0)]

/-- A function with the hidden trace parameter that calls one that takes it too. -/
def traced : RawFunc :=
  let call : RawInst :=
    { inst 0 "call" tU8 with callee := some (.func "canon.g" false), errTrace := some (some tTrace) }
  { fn .v0_16_0 #[] #[call, ret 1 (.inst 0)] with errTrace := some (some tTrace) }

/-- A placeholder (`bitcast` of 0 to `*u8`) that a `load` reads. -/
def readPlaceholder : RawFunc :=
  fn .v0_16_0 #[] #[inst 0 "bitcast" tPU8 #[.int tU64 0], inst 1 "load" tU8 #[.inst 0], ret 2 (.inst 1)]

/-- A runtime lane pointer that a `load` reads. -/
def readLanePtr : RawFunc :=
  fn .v0_15_2 #[tPArr] #[arg 0 tPArr 0, inst 1 "ptr_elem_ptr" tLane #[.inst 0, .int tU64 1],
    inst 2 "load" tU8 #[.inst 1], ret 3 (.inst 2)]

/-- A local read through a const pointer before its one store: the read is of undefined bytes. -/
def readBeforeStore : RawFunc :=
  fn .v0_16_0 #[tU8] #[arg 0 tU8 0, inst 1 "alloc" tPU8, inst 2 "bitcast" tPConst #[.inst 1],
    inst 3 "load" tU8 #[.inst 2], inst 4 "store" tVoid #[.inst 1, .inst 0], ret 5 (.inst 3)]

/-- An array loaded whole, a write to it, then an item of the loaded value: the old item. -/
def writeBetween : RawFunc :=
  fn .v0_15_2 #[tPArr] #[arg 0 tPArr 0, inst 1 "load" tArr #[.inst 0],
    inst 2 "store" tVoid #[.inst 0, .undef tArr], inst 3 "array_elem_val" tU8 #[.inst 1, .int tU64 2],
    ret 4 (.inst 3)]

/-- The check `0 <= x` of a signed `x`: false for a negative one. -/
def signedCheck : RawFunc :=
  fn .v0_15_2 #[tI32] #[arg 0 tI32 0, inst 1 "cmp_lte" tBool #[.int tI32 0, .inst 0], check 2 1,
    ret 6 (.int tU8 0)]

/-- A load through a C pointer, a store through it, a safety check, then the loaded value: the
load is no pointer formation and reads the old byte. -/
def loadBeforeCheck : RawFunc :=
  fn .v0_16_0 #[tCPtr, tBool] #[arg 0 tCPtr 0, arg 1 tBool 1, inst 2 "load" tU8 #[.inst 0],
    inst 3 "store" tVoid #[.inst 0, .int tU8 9], check 4 1, ret 8 (.inst 2)]

def unchanged (name : String) (rewrite : RawFunc → RawFunc) (f : RawFunc) : String × Bool :=
  (name, rewrite f == f)

def checks : List (String × Bool) := [
  ("versionTags.int.bit_and", (versionTags (bitAnd tU8)).toOption.bind (tagOf · 2) == some "bit_and"),
  ("versionTags.bool.bit_and", (versionTags (bitAnd tBool)).toOption.bind (tagOf · 2) == some "bool_and"),
  ("argRanks.slot", ((argRanks ranked).toOption.map fun f => f.body.map (·.param)) == some #[some 1, none]),
  -- The trace parameter is the new last one (instruction 2), and the call passes it.
  ("errTraces.call", ((errTraces traced).toOption.map fun f =>
      (f.params, f.body.map fun i => (i.id, i.tag, i.param, i.args))) ==
    some (#[tTrace], #[(2, "arg", some 0, #[]), (0, "call", none, #[.inst 2]), (1, "ret", none, #[.inst 0])])),
  unchanged "dropDeadAllocPlaceholders.read" dropDeadAllocPlaceholders readPlaceholder,
  unchanged "dropDeadRuntimeLanePtrs.read" dropDeadRuntimeLanePtrs readLanePtr,
  unchanged "forwardReadOnlyCopies.read.before.store" forwardReadOnlyCopies readBeforeStore,
  unchanged "itemReads.write.between" itemReads writeBetween,
  unchanged "dropTrueChecks.signed" dropTrueChecks signedCheck,
  unchanged "sinkPastChecks.load" sinkPastChecks loadBeforeCheck]

end CanonRewrites

def main : IO Unit := do
  let mut failed := 0
  for (name, ok) in CanonRewrites.checks do
    if ok then IO.println s!"check ok {name}"
    else
      failed := failed + 1
      IO.println s!"check FAILED {name}"
  IO.println s!"checks: {CanonRewrites.checks.length}, failed: {failed}"
  if failed != 0 then throw (IO.userError s!"{failed} Canon rewrite checks failed")
