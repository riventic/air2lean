import Proofs.Lists.Sep

/-!
# Memory safety, end to end: build a list, then free it

From the repository root:

    lake build Proofs.Lists.Sep
    lake env lean tutorials/memory-safety/Main.lean

A Lean client composes three functions translated from `examples/lists/lists.zig`
(`Proofs/Lists/Gen.lean`): `push` once per item, `reverse`, then `freeAll`. If a `push` fails
with `error.OutOfMemory`, the client frees the part of the list it has built, as a Zig
`errdefer freeAll(a, head)` would. The client is the Lean form of

    fn buildThenFree(a: Allocator, xs: []const u32) !void {
        var head: ?*Node = null;
        for (xs) |x| head = push(a, head, x) catch |e| { freeAll(a, head); return e; };
        head = reverse(head);
        freeAll(a, head);
    }

For every input, every allocation policy and every failure trace (`Mem.failAt`,
`Mem.allocPolicy`), and every heap the caller already owns, the theorems below prove:

* no use after free, double free or invalid free: the run returns (`run = pure _`), so it
  throws no `.illegal`. A dead or inner-pointer access or free would throw it
  (`buildThenFree_no_illegal`);
* no leak, also on the out-of-memory path: the live heap after the run is exactly the live
  heap before it (`buildThenFree_no_leak`);
* on success, the list holds the pushed items in order (`build_total`).

`tutorials/memory-safety/Negative.lean` shows that each property can fail: a double free and
a read after free throw `.illegal`, and a client that skips the free leaks. README.md lists
the premises and limits.
-/

namespace MemorySafety

open Zig Assn Lists

/-! ## The client -/

/-- Push the items of `xs` on `hd` with the generated `push`. If one fails, free the list built
so far with the generated `freeAll` and return the error. -/
def pushAll (a : Allocator) : Option Ptr → List (BitVec 32) → MemM (Except ErrName (Option Ptr))
  | hd, [] => pure (.ok hd)
  | hd, v :: vs => do
    match ← push a hd v with
    | .error e => do freeAll a hd; pure (.error e)
    | .ok p => pushAll a (some p) vs

/-- Build the list of `xs`: push every item, then the generated `reverse`. -/
def build (a : Allocator) (xs : List (BitVec 32)) : MemM (Except ErrName (Option Ptr)) := do
  match ← pushAll a none xs with
  | .error e => pure (.error e)
  | .ok hd => pure (.ok (← reverse hd))

/-- Build the list of `xs`, then free it with the generated `freeAll`. -/
def buildThenFree (a : Allocator) (xs : List (BitVec 32)) : MemM (Except ErrName Unit) := do
  match ← build a xs with
  | .error e => pure (.error e)
  | .ok hd => do freeAll a hd; pure (.ok ())

/-! ## Specifications -/

/-- What a build returns: the list of `xs`, or `error.OutOfMemory` and no bytes. -/
def built (xs : List (BitVec 32)) : Except ErrName (Option Ptr) → Assn
  | .ok hd => list hd xs
  | .error e => ⌜e = "OutOfMemory"⌝

theorem emp_sep {R : Assn} {h : Heap} (hr : R h) : (emp ∗ R) h := sep_comm (sep_emp.mpr hr)

/-- `pushAll` on a list of `ys` returns the list of `xs` reversed in front of `ys`, or
`error.OutOfMemory` with every node freed, including the ones of `ys`. -/
theorem pushAll_total (a : Allocator) (xs ys : List (BitVec 32)) (hd : Option Ptr) :
    TotalTriple (list hd ys) (pushAll a hd xs) (built (xs.reverse ++ ys)) := by
  induction xs generalizing hd ys with
  | nil => exact TotalTriple.ret (Q := built ys) (.ok hd)
  | cons v vs ih =>
    rw [pushAll]
    refine TotalTriple.bind
      (TotalTriple.conseq ((push_total a hd v).frame (R := list hd ys)) (fun _ => emp_sep)
        (fun _ _ h => h)) (fun r => ?_)
    cases r with
    | error e =>
      apply TotalTriple.lift
      intro he
      refine TotalTriple.bind (freeAll_total a hd ys) (fun _ => ?_)
      exact TotalTriple.conseq (TotalTriple.ret (Q := built _) (.error e)) (fun _ hh => ⟨he, hh⟩)
        (fun _ _ h => h)
    | ok p =>
      refine TotalTriple.conseq (ih (v :: ys) (some p)) (fun _ hh => ⟨p, hd, rfl, hh⟩) ?_
      intro r h hh
      simpa using hh

/-- (c) `build` returns the list of the items of `xs`, in order, or `error.OutOfMemory` and no
bytes: on that path every node it allocated is freed. -/
theorem build_total (a : Allocator) (xs : List (BitVec 32)) :
    TotalTriple emp (build a xs) (built xs) := by
  refine TotalTriple.bind
    (TotalTriple.conseq (pushAll_total a xs [] none) (fun _ hh => ⟨rfl, hh⟩) (fun _ _ h => h))
    (fun r => ?_)
  cases r with
  | error e => exact TotalTriple.ret (Q := built xs) (.error e)
  | ok hd =>
    refine TotalTriple.bind (reverse_total hd _) (fun r => ?_)
    refine TotalTriple.conseq (TotalTriple.ret (Q := built xs) (.ok r)) ?_ (fun _ _ h => h)
    intro h hh
    simpa [built] using hh

/-- How `buildThenFree` can end: `ok`, or `error.OutOfMemory`. -/
def Ended (r : Except ErrName Unit) : Prop := r = .ok () ∨ r = .error "OutOfMemory"

/-- `buildThenFree` returns `ok` or `error.OutOfMemory`, and owns no bytes after it. -/
theorem buildThenFree_total (a : Allocator) (xs : List (BitVec 32)) :
    TotalTriple emp (buildThenFree a xs) (fun r => ⌜Ended r⌝) := by
  refine TotalTriple.bind (build_total a xs) (fun r => ?_)
  cases r with
  | error e =>
    refine TotalTriple.conseq (TotalTriple.ret (Q := fun r => ⌜Ended r⌝) (.error e)) ?_
      (fun _ _ h => h)
    rintro h ⟨rfl, hh⟩
    exact ⟨Or.inr rfl, hh⟩
  | ok hd =>
    refine TotalTriple.bind (freeAll_total a hd xs) (fun _ => ?_)
    exact TotalTriple.conseq (TotalTriple.ret (Q := fun r => ⌜Ended r⌝) (.ok ()))
      (fun _ hh => ⟨Or.inl rfl, hh⟩) (fun _ _ h => h)

/-! ## The three properties, on the whole memory -/

/-- From every single-threaded memory (any allocation policy, any failure trace, any heap
already in use), `buildThenFree` returns `ok` or `error.OutOfMemory`, and the live heap after
it is exactly the live heap before it. -/
theorem buildThenFree_memory_safe (a : Allocator) (xs : List (BitVec 32)) (m : Mem)
    (hs : m.Seq) :
    ∃ r m', (buildThenFree a xs).run m = pure (r, m') ∧ Ended r ∧ m'.heap = m.heap := by
  obtain ⟨r, m', hQ, hr, -, hm', ⟨hpost, rfl⟩, -⟩ :=
    buildThenFree_total a xs m Heap.empty m.heap (Heap.disjoint_empty _).symm (by simp) rfl hs
  exact ⟨r, m', hr, hpost, by simpa using hm'⟩

/-- (a) No use after free, no double free, no invalid free: the run never throws `.illegal`
(nor any other `Zig.Error`). -/
theorem buildThenFree_no_illegal (a : Allocator) (xs : List (BitVec 32)) (m : Mem)
    (hs : m.Seq) (e : Error) : (buildThenFree a xs).run m ≠ throw e := by
  obtain ⟨r, m', hr, -, -⟩ := buildThenFree_memory_safe a xs m hs
  rw [hr]
  intro h
  cases h

/-- (b) No leak: every block that `buildThenFree` allocates is freed, on success and on every
out-of-memory path, and no block that it did not allocate is touched. -/
theorem buildThenFree_no_leak (a : Allocator) (xs : List (BitVec 32)) (m : Mem) (hs : m.Seq)
    (r : Except ErrName Unit) (m' : Mem) (hr : (buildThenFree a xs).run m = pure (r, m')) :
    m'.heap = m.heap := by
  obtain ⟨r', m'', hr', -, hh⟩ := buildThenFree_memory_safe a xs m hs
  rw [hr] at hr'
  cases hr'
  exact hh

/-- The allocation policy and the failure trace are arbitrary: the same holds after setting
them to any values. -/
theorem buildThenFree_every_policy (a : Allocator) (xs : List (BitVec 32)) (m : Mem)
    (hs : m.Seq) (k : Option Nat) (pol : AllocPolicy) :
    ∃ r m', (buildThenFree a xs).run { m with failAt := k, allocPolicy := pol } = pure (r, m') ∧
      Ended r ∧ m'.heap = m.heap :=
  buildThenFree_memory_safe a xs { m with failAt := k, allocPolicy := pol } ⟨hs.single, hs.addr⟩

end MemorySafety
