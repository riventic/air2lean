import Proofs.Lists.Alloc

/-!
# Memory safety, end to end: build a list, then free it, with any allocator

From the repository root:

    lake build Proofs.Lists.Alloc
    lake env lean tutorials/memory-safety/Main.lean

A Lean client composes three functions translated from `examples/lists/lists.zig`
(`Proofs/Lists/Open.lean`): `push` once per item, `reverse`, then `freeAll`. If a `push` fails
with `error.OutOfMemory`, the client frees the part of the list it has built, as a Zig
`errdefer freeAll(a, head)` would. The client is the Lean form of

    fn buildThenFree(a: Allocator, xs: []const u32) !void {
        var head: ?*Node = null;
        for (xs) |x| head = push(a, head, x) catch |e| { freeAll(a, head); return e; };
        head = reverse(head);
        freeAll(a, head);
    }

The allocator `a` is a parameter: every call through it reaches the environment (`Ext`,
premise EXT-05), and the theorems assume only the `std.mem.Allocator` contract `CAllocSpec` of
that allocator (`Proofs/Lists/Alloc.lean`, `docs/interfaces.md`). They hold for every allocator
that meets it, so for every allocation-failure pattern it allows: the contract lets every
allocation return `null`. An allocation takes a fee `I.fee φ` of the allocator (nothing for most
allocators, a fraction of an arena's epoch token; `docs/sep-full-state.md` §The fee of a grant),
so the client starts with one fee per item (`fees I φ xs.length`); every free gives a fee back.
For every such allocator, every memory and every frame (whatever the rest of the program owns),
the theorems below prove:

* no use after free, double free or invalid free: a run throws no error except running out of
  stack (`.stackOverflow`); in particular no `.illegal`, which a dead or inner-pointer access or
  free would throw (`buildThenFree_no_illegal`);
* no leak, also on the out-of-memory path: after the run the caller owns exactly what it owned
  before, the allocator's state, the fees and the vtable, and the frame is untouched: every node
  the client allocated was given back to the allocator (`buildThenFree_no_leak`);
* on success, the list holds the pushed items in order (`build_spec`).

These are partial-correctness statements (`CTriple`): the allocator contract is one, so a
client of an arbitrary allocator cannot conclude that the allocator returns.
README.md lists the premises and limits.
-/

namespace MemorySafety

open Zig Zig.Full Zig.Full.FAssn Lists.Open Lists.Alloc

variable [Ext]

/-! ## The client -/

/-- Push the items of `xs` on `hd` with the generated `push`. If one fails, free the list built
so far with the generated `freeAll` and return the error. -/
def pushAll (a : mem_Allocator) : Option Ptr → List (BitVec 32) →
    ConcM Tgt (Except ErrName (Option Ptr))
  | hd, [] => pure (.ok hd)
  | hd, v :: vs => do
    match ← push a hd v with
    | .error e => do freeAll a hd; pure (.error e)
    | .ok p => pushAll a (some p) vs

/-- Build the list of `xs`: push every item, then the generated `reverse`. -/
def build (a : mem_Allocator) (xs : List (BitVec 32)) : ConcM Tgt (Except ErrName (Option Ptr)) := do
  match ← pushAll a none xs with
  | .error e => pure (.error e)
  | .ok hd => pure (.ok (← ConcM.liftMem (reverse hd)))

/-- Build the list of `xs`, then free it with the generated `freeAll`. -/
def buildThenFree (a : mem_Allocator) (xs : List (BitVec 32)) : ConcM Tgt (Except ErrName Unit) := do
  match ← build a xs with
  | .error e => pure (.error e)
  | .ok hd => do freeAll a hd; pure (.ok ())

/-! ## Specifications -/

/-- What a build returns: the list of `xs`, or `error.OutOfMemory` and the fee of every item
back. -/
def built (I : FAllocInv) (φ : Frac) (xs : List (BitVec 32)) : Except ErrName (Option Ptr) → FAssn
  | .ok hd => list I φ hd xs
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ fees I φ xs.length

variable (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac)
  (hfit : I.fits (16 : BitVec 64).toNat 3) (h : CAllocSpec (CVTable.env (env e) fns) ctx I)

include hfit h

/-- `pushAll` on a list of `ys`, with a fee for each item of `xs`, returns the list of `xs`
reversed in front of `ys`, or `error.OutOfMemory` with every node given back, including the ones
of `ys`, and every fee back. -/
theorem pushAll_spec (xs ys : List (BitVec 32)) (hd : Option Ptr) :
    CTriple (I.own ⋆ (fees I φ xs.length ⋆ (list I φ hd ys ⋆ vtR vtp fns.toList)))
      (pushAll ⟨ctx, vtp⟩ hd xs)
      (fun r => I.own ⋆ (built I φ (xs.reverse ++ ys) r ⋆ vtR vtp fns.toList)) := by
  induction xs generalizing hd ys with
  | nil => exact CTriple.ret' _ fun _ hr => sep_mono_right (fun _ hr => Full.sep_emp.mp (sep_comm hr)) hr
  | cons v vs ih =>
    rw [pushAll]
    refine CTriple.bind (((push_spec ctx vtp fns I e φ hd v hfit h).frame
      (R := fees I φ vs.length ⋆ list I φ hd ys)).pre
      fun _ hr => ac_cast hr (by simp only [List.length_cons, fees_succ]; ac_rfl)) fun r => ?_
    cases r with
    | error e' =>
      -- `error.OutOfMemory`: the list built so far goes back to the allocator
      dsimp only [pushed]
      refine CTriple.pre (P := ⟪e' = "OutOfMemory"⟫ ⋆ (I.own ⋆ (list I φ hd ys ⋆
          (vtR vtp fns.toList ⋆ (I.fee φ ⋆ fees I φ vs.length)))))
        (CTriple.lift fun he => ?_) fun _ hr => ac_cast hr (by ac_rfl)
      refine CTriple.bind ((freeAll_spec ctx vtp fns I e φ hd ys h).frame
        (R := I.fee φ ⋆ fees I φ vs.length) |>.pre fun _ hr => ac_cast hr (by ac_rfl))
        fun _ => CTriple.ret' _ fun _ hr => ?_
      dsimp only [built]
      have e : ((v :: vs).reverse ++ ys).length = (vs.length + 1) + ys.length := by simp; omega
      rw [e, fees_add, fees_succ]
      exact ac_cast (Full.sep_lift.mpr ⟨he, hr⟩ :
        (⟪e' = "OutOfMemory"⟫ ⋆ _) _) (by ac_rfl)
    | ok p =>
      -- the new node is the head of the list of `v :: ys`
      dsimp only [pushed]
      rw [List.reverse_cons, List.append_assoc, List.singleton_append]
      refine (ih (v :: ys) (some p)).pre fun _ hr => ?_
      have hr' : (I.own ⋆ (fees I φ vs.length ⋆ ((node I φ p v hd ⋆ list I φ hd ys) ⋆
          vtR vtp fns.toList))) _ :=
        ac_cast hr (by ac_rfl)
      exact sep_mono_right (fun _ h' => sep_mono_right (fun _ h' => sep_mono_left (fun _ h'' =>
        ⟨p, hd, Full.sep_lift.mpr ⟨rfl, h''⟩⟩) h') h') hr'

/-- `build`, with a fee for each item of `xs`, returns the list of the items of `xs`, in order,
or `error.OutOfMemory` and the fees: on that path every node it allocated is given back. -/
theorem build_spec (xs : List (BitVec 32)) :
    CTriple (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList)) (build ⟨ctx, vtp⟩ xs)
      (fun r => I.own ⋆ (built I φ xs r ⋆ vtR vtp fns.toList)) := by
  refine CTriple.bind ((pushAll_spec ctx vtp fns I e φ hfit h xs [] none).pre fun _ hr =>
    sep_mono_right (fun _ h' => sep_mono_right (fun _ h' => ac_cast (Full.sep_lift.mpr ⟨rfl, h'⟩ :
      (⟪(none : Option Ptr) = none⟫ ⋆ vtR vtp fns.toList) _) rfl) h') hr) fun r => ?_
  cases r with
  | error e' =>
    exact CTriple.ret' _ fun _ hr => by
      simpa only [built, List.append_nil, List.length_reverse] using hr
  | ok hd =>
    refine CTriple.bind (CTriple.liftMem (((Lists.Linked.reverse_spec (X := nodeRest I φ) hd
      (xs.reverse ++ [])).frame (R := I.own ⋆ vtR vtp fns.toList)).pre fun _ hr => ?_))
      fun r => CTriple.ret' _ fun _ hr => ?_
    · exact ac_cast hr (by dsimp only [built]; ac_rfl)
    · simp only [List.append_nil, List.reverse_reverse] at hr
      exact ac_cast hr (by dsimp only [built]; ac_rfl)

/-- How `buildThenFree` can end: `ok`, or `error.OutOfMemory`. -/
def Ended (r : Except ErrName Unit) : Prop := r = .ok () ∨ r = .error "OutOfMemory"

/-- `buildThenFree` returns `ok` or `error.OutOfMemory`, and the caller owns what it owned
before: the allocator's state, the fees and the vtable. -/
theorem buildThenFree_spec (xs : List (BitVec 32)) :
    CTriple (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList)) (buildThenFree ⟨ctx, vtp⟩ xs)
      (fun r => ⟪Ended r⟫ ⋆ (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList))) := by
  refine CTriple.bind (build_spec ctx vtp fns I e φ hfit h xs) fun r => ?_
  cases r with
  | error e' =>
    refine CTriple.pre (P := ⟪e' = "OutOfMemory"⟫ ⋆ (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList)))
      (CTriple.lift fun he => CTriple.ret' _ fun _ hr => Full.sep_lift.mpr ⟨Or.inr (by rw [he]), hr⟩)
      fun _ hr => ac_cast hr (by dsimp only [built]; ac_rfl)
  | ok hd =>
    exact CTriple.bind (freeAll_spec ctx vtp fns I e φ hd xs h) fun _ =>
      CTriple.ret' _ fun _ hr => Full.sep_lift.mpr ⟨Or.inl rfl, hr⟩

/-! ## The properties, on the whole memory -/

/-- From every memory that holds the allocator's state, the fees and the vtable, with any frame
`rF` (whatever else the program owns), and at every depth `n` of the run, `buildThenFree` throws
no error but `.stackOverflow`, and if it returns, it returns `ok` or `error.OutOfMemory` in a
memory that holds the same resources with the same frame. -/
theorem buildThenFree_memory_safe (xs : List (BitVec 32)) (n : Nat) (m : Mem) (r rF : Res)
    (hh : Holds m r rF) (hr : (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList)) r) (hs : m.FSeq) :
    match ((Sched.soloRun n (buildThenFree ⟨ctx, vtp⟩ xs)).run m).run with
    | none => True
    | some (.error err) => err = .stackOverflow
    | some (.ok (v, m')) => Ended v ∧ ∃ r', Holds m' r' rF ∧
        (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList)) r' ∧ m'.FSeq := by
  have t := buildThenFree_spec ctx vtp fns I e φ hfit h xs n m r rF hh hr hs
  revert t
  rcases ((Sched.soloRun n (buildThenFree ⟨ctx, vtp⟩ xs)).run m).run with _ | err | ⟨v, m'⟩ <;>
    intro t
  · trivial
  · exact t
  · obtain ⟨r', hh', hq, hs'⟩ := t
    obtain ⟨he, hq⟩ := Full.sep_lift.mp hq
    exact ⟨he, r', hh', hq, hs'⟩

/-- **No use after free, no double free, no invalid free**: the run never throws `.illegal`. -/
theorem buildThenFree_no_illegal (xs : List (BitVec 32)) (n : Nat) (m : Mem) (r rF : Res)
    (hh : Holds m r rF) (hr : (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList)) r) (hs : m.FSeq) :
    ((Sched.soloRun n (buildThenFree ⟨ctx, vtp⟩ xs)).run m).run ≠ some (.error .illegal) := by
  intro he
  have t := buildThenFree_memory_safe ctx vtp fns I e φ hfit h xs n m r rF hh hr hs
  rw [he] at t
  cases t

/-- **No leak**: every node that `buildThenFree` allocates is given back to the allocator, on
success and on every out-of-memory path, and no resource of the frame is touched: after the
run the caller holds exactly the allocator's state, the fees and the vtable again. -/
theorem buildThenFree_no_leak (xs : List (BitVec 32)) (n : Nat) (m : Mem) (r rF : Res)
    (hh : Holds m r rF) (hr : (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList)) r) (hs : m.FSeq)
    (v : Except ErrName Unit) (m' : Mem)
    (hrun : ((Sched.soloRun n (buildThenFree ⟨ctx, vtp⟩ xs)).run m).run = some (.ok (v, m'))) :
    ∃ r', Holds m' r' rF ∧ (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList)) r' := by
  have t := buildThenFree_memory_safe ctx vtp fns I e φ hfit h xs n m r rF hh hr hs
  rw [hrun] at t
  obtain ⟨-, r', hh', hq, -⟩ := t
  exact ⟨r', hh', hq⟩

end MemorySafety
