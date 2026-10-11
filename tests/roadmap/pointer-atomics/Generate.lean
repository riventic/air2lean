import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

/-! C09 offline AIR/checker/emitter regressions for pointer atomics. Generates one standalone
Lean file whose `native_decide` examples run the emitted pointer ops (`Zig.atomicLoadPtrC`, …)
and checks the rejections of other atomic formats. No compiler is invoked. -/
open Lean Air2Lean
private def obj := Json.mkObj
private def num (n : Nat) : Json := toJson n
private def ref (n : Nat) := obj [("inst", num n)]
private def intTy (bits : Nat) := obj [("k", .str "int"), ("signed", .bool false),
  ("bits", num bits), ("abi_size", num (Zig.intSize bits)), ("abi_align", num (Zig.intAlign bits))]
private def ptrTy (size : String) (child align : Nat) (allowzero : Bool := false) :=
  obj [("k", .str "ptr"), ("size", .str size), ("child", num child), ("const", .bool false),
    ("allowzero", .bool allowzero), ("ptr_align", num align), ("abi_size", num (if size == "slice" then 16 else 8)),
    ("abi_align", num 8)]
private def optTy (child : Nat) := obj [("k", .str "optional"), ("child", num child),
  ("abi_size", num 8), ("abi_align", num 8)]
private def inst (id : Nat) (tag : String) (ty : Nat) (args : Array Json := #[])
    (extra : List (String × Json) := []) :=
  obj ([("id", num id), ("tag", .str tag), ("ty", num ty), ("args", .arr args)] ++ extra)
private def file (name : String) (types : Array Json) (params : Array Nat) (ret : Nat)
    (body : Array Json) := obj [("schema", num 11), ("zig_version", .str "0.16.0"),
  ("name", .str name), ("types", .arr types), ("params", toJson params),
  ("ret", num ret), ("body", .arr body)]
private def arg (id ty : Nat) := inst id "arg" ty #[] [("param", num id)]
private def process (j : Json) : Except String Func := do
  let f ← normalize (← Raw.parseFunc j)
  check f
  pure f
private def reject (j : Json) (diagnostic : String) : IO Unit := do
  match process j with
  | .ok _ => throw (IO.userError s!"accepted rejection fixture: {diagnostic}")
  | .error e => unless (e.splitOn diagnostic).length > 1 do
      throw (IO.userError s!"wrong rejection: expected {diagnostic}, got {e}")

/-- 0 `u32`, 1 `*u32`, 2 `?*u32`, 3 `**u32`, 4 `*?*u32`, 5 `void`, 6 `??*u32`, 7 `bool`,
8 `noreturn`, 9 `f32`, 10 `*f32`, 11 `[]u32`, 12 `*[]u32`, 13 `[*c]u32`, 14 `*[*c]u32`,
15 `*allowzero u32`, 16 `**allowzero u32`. -/
private def types : Array Json :=
  #[intTy 32, ptrTy "one" 0 4, optTy 1, ptrTy "one" 1 8, ptrTy "one" 2 8, obj [("k", .str "void")],
    obj [("k", .str "optional"), ("child", num 2), ("abi_size", num 16), ("abi_align", num 8)],
    obj [("k", .str "bool")], obj [("k", .str "noreturn")],
    obj [("k", .str "float"), ("bits", num 32), ("abi_size", num 4), ("abi_align", num 4)],
    ptrTy "one" 9 4, ptrTy "slice" 0 4, ptrTy "one" 11 8, ptrTy "c" 0 4, ptrTy "one" 13 8,
    ptrTy "one" 0 4 true, ptrTy "one" 15 8]

private def order (o : String) := ("order", Json.str o)

private def fixtures : Array Json := #[
  file "ptrs.loadPtr" types #[3] 1
    #[arg 0 3, inst 1 "atomic_load" 1 #[ref 0] [order "acquire"], inst 2 "ret" 8 #[ref 1]],
  file "ptrs.storePtr" types #[3, 1] 5
    #[arg 0 3, arg 1 1, inst 2 "atomic_store_release" 5 #[ref 0, ref 1],
      inst 3 "ret" 8 #[obj [("ty", num 5), ("val", .str "{}")]]],
  file "ptrs.xchgPtr" types #[3, 1] 1
    #[arg 0 3, arg 1 1, inst 2 "atomic_rmw" 1 #[ref 0, ref 1] [("op", .str "Xchg"), order "acq_rel"],
      inst 3 "ret" 8 #[ref 2]],
  file "ptrs.casPtr" types #[3, 1, 1] 2
    #[arg 0 3, arg 1 1, arg 2 1,
      inst 3 "cmpxchg_strong" 2 #[ref 0, ref 1, ref 2]
        [("success_order", .str "seq_cst"), ("failure_order", .str "monotonic")],
      inst 4 "ret" 8 #[ref 3]],
  file "ptrs.loadOpt" types #[4] 2
    #[arg 0 4, inst 1 "atomic_load" 2 #[ref 0] [order "acquire"], inst 2 "ret" 8 #[ref 1]],
  file "ptrs.casWeakOpt" types #[4, 2, 2] 6
    #[arg 0 4, arg 1 2, arg 2 2,
      inst 3 "cmpxchg_weak" 6 #[ref 0, ref 1, ref 2]
        [("success_order", .str "release"), ("failure_order", .str "monotonic")],
      inst 4 "ret" 8 #[ref 3]]]

/-- Runs of the emitted ops on one thread, decided by the kernel. Block 0 is the slot, blocks 1
and 2 are nodes; node 1's address plus 8 is node 2's address (4108 + 8 = 4116). -/
private def tests : String := "
open Zig in
private def run1 {α : Type} (x : ConcM PtrAtomics.Tgt α) : Result (α × Mem) :=
  Sched.run ⟨.any, .available⟩ PtrAtomics.dispatch 100 (fun _ => 0) x {}

open Zig in
/-- The slot holds node 2; `f` gets the slot and the two nodes. -/
private def withSlot {α : Type} (f : Ptr → Ptr → Ptr → ConcM PtrAtomics.Tgt α) :
    ConcM PtrAtomics.Tgt α := do
  let s ← (alloc .stack 8 8 : MemM Ptr)
  let a ← (alloc .heap 4 4 : MemM Ptr)
  let b ← (alloc .heap 4 4 : MemM Ptr)
  (store 8 s b : MemM Unit)
  (store 4 b (7 : BitVec 32) : MemM Unit)
  f s a b

private def ok? {α : Type} (r : Zig.Result (α × Zig.Mem)) : Option α :=
  match r.run with | some (.ok (v, _)) => some v | _ => none
private def err? {α : Type} (r : Zig.Result (α × Zig.Mem)) : Option Zig.Error :=
  match r.run with | some (.error e) => some e | _ => none

-- A load returns the pointer with its block; a read through it reaches node 2.
example : ok? (run1 (withSlot fun s _ _ => PtrAtomics.loadPtr s)) = some ⟨some 2, 0⟩ := by
  native_decide
example : ok? (run1 (withSlot fun s _ _ => do
    let p ← PtrAtomics.loadPtr s
    (Zig.load (BitVec 32) 4 p : Zig.MemM _))) = some 7 := by native_decide
-- A store, then a load: node 1.
example : ok? (run1 (withSlot fun s a _ => do
    PtrAtomics.storePtr s a
    PtrAtomics.loadPtr s)) = some ⟨some 1, 0⟩ := by native_decide
-- `xchg` returns the old pointer.
example : ok? (run1 (withSlot fun s a _ => PtrAtomics.xchgPtr s a)) = some ⟨some 2, 0⟩ := by
  native_decide
-- CAS with the same identity succeeds; with another block it fails and returns the pointer read.
example : ok? (run1 (withSlot fun s a b => PtrAtomics.casPtr s b a)) = some none := by
  native_decide
example : ok? (run1 (withSlot fun s a _ => PtrAtomics.casPtr s a a)) = some (some ⟨some 2, 0⟩) := by
  native_decide
-- Node 1 plus 8 has node 2's address, but another block: no success, `.unspecified`.
example : err? (run1 (withSlot fun s a _ => PtrAtomics.casPtr s (a.add 8) a)) =
    some .unspecified := by native_decide
-- A raw address equal to node 2's has no block: `.unspecified`, not success.
example : err? (run1 (withSlot fun s a _ => PtrAtomics.casPtr s ⟨none, 4116⟩ a)) =
    some .unspecified := by native_decide
-- `?*u32`: a `null` slot loads `null`; a weak CAS from `null` may succeed or fail spuriously.
open Zig in
private def withNull {α : Type} (f : Ptr → Ptr → ConcM PtrAtomics.Tgt α) : ConcM PtrAtomics.Tgt α := do
  let s ← (alloc .stack 8 8 : MemM Ptr)
  let a ← (alloc .heap 4 4 : MemM Ptr)
  (store 8 s (none : Option Ptr) : MemM Unit)
  f s a
example : ok? (run1 (withNull fun s _ => PtrAtomics.loadOpt s)) = some none := by native_decide
example : ok? (run1 (withNull fun s a => do
    let r ← PtrAtomics.casWeakOpt s none (some a)
    let v ← PtrAtomics.loadOpt s
    pure (r, v))) = some (none, some ⟨some 1, 0⟩) := by native_decide
example : ok? (Zig.Sched.run ⟨.any, .available⟩ PtrAtomics.dispatch 100 (fun _ => 1)
    (withNull fun s a => PtrAtomics.casWeakOpt s none (some a)) {}) = some (some none) := by
  native_decide
"

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: Generate.lean OUTPUT_DIR")
  let dir := System.FilePath.mk directory
  IO.FS.createDirAll dir
  let fs ← fixtures.mapM fun j => match process j with
    | .ok f => pure f
    | .error e => throw (IO.userError e)
  IO.FS.writeFile (dir / "PtrAtomics.lean") (emit fs "PtrAtomics" "ptrs." ++ tests)
  -- Other atomic formats stay rejected, each with its reason.
  reject (file "ptrs.floatLoad" types #[10] 9
    #[arg 0 10, inst 1 "atomic_load" 9 #[ref 0] [order "acquire"], inst 2 "ret" 8 #[ref 1]])
    "a float atomic is outside the subset"
  reject (file "ptrs.addPtr" types #[3, 1] 1
    #[arg 0 3, arg 1 1, inst 2 "atomic_rmw" 1 #[ref 0, ref 1] [("op", .str "Add"), order "seq_cst"],
      inst 3 "ret" 8 #[ref 2]])
    "other than `.Xchg`"
  reject (file "ptrs.sliceLoad" types #[12] 11
    #[arg 0 12, inst 1 "atomic_load" 11 #[ref 0] [order "acquire"], inst 2 "ret" 8 #[ref 1]])
    "single/many pointer"
  reject (file "ptrs.cPtrLoad" types #[14] 13
    #[arg 0 14, inst 1 "atomic_load" 13 #[ref 0] [order "acquire"], inst 2 "ret" 8 #[ref 1]])
    "null-byte encoding"
  reject (file "ptrs.allowzeroLoad" types #[16] 15
    #[arg 0 16, inst 1 "atomic_load" 15 #[ref 0] [order "acquire"], inst 2 "ret" 8 #[ref 1]])
    "null-byte encoding"
  IO.println "pointer atomics: 6 accepted ops emitted; 5 rejections checked"
