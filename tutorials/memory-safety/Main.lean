import Proofs.Lists.Client

/-!
# Memory safety, end to end: build a list, then free it, with any allocator

From the repository root:

    lake build Proofs.Lists.Client
    lake env lean tutorials/memory-safety/Main.lean

A Lean client composes three functions translated from `examples/lists/lists.zig`
(`Proofs/Lists/Open.lean`): `push` once per item, `reverse`, then `freeAll`. If a `push` fails
with `error.OutOfMemory`, the client frees the part of the list it has built, as a Zig
`errdefer freeAll(a, head)` would. The client, `buildThenFree` in `Proofs/Lists/Client.lean`, is
the Lean form of

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

`Proofs/Lists/Client.lean` proves the client's specifications: `pushAll_spec`, `build_spec` (on
success, the list holds the pushed items in order) and `buildThenFree_spec` (the run returns `ok`
or `error.OutOfMemory` and owns what it owned before). This file reads them on the whole memory:
for every such allocator, every memory and every frame (whatever the rest of the program owns),

* no use after free, double free or invalid free: a run throws no error except running out of
  stack (`.stackOverflow`); in particular no `.illegal`, which a dead or inner-pointer access or
  free would throw (`buildThenFree_no_illegal`, the library's `NoIllegal` property);
* no leak, also on the out-of-memory path: after the run the caller owns exactly what it owned
  before, the allocator's state, the fees and the vtable, and the frame is untouched: every node
  the client allocated was given back to the allocator (`buildThenFree_no_leak`, the library's
  `NoLeak` property).

These are partial-correctness statements (`CTriple`): the allocator contract is one, so a
client of an arbitrary allocator cannot conclude that the allocator returns.
README.md lists the premises and limits.
-/

namespace MemorySafety

open Zig Zig.Full Zig.Full.FAssn Lists.Open Lists.Alloc Lists.Client

variable [Ext] (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac)
  (hfit : I.fits (16 : BitVec 64).toNat 3) (h : CAllocSpec (CVTable.env (env e) fns) ctx I)

include hfit h

/-! ## The properties, on the whole memory -/

/-- From every memory that holds the allocator's state, the fees and the vtable, with any frame
`rF` (whatever else the program owns), and at every depth `n` of the run, `buildThenFree` throws
no error but `.stackOverflow`, and if it returns, it returns `ok` or `error.OutOfMemory` in a
memory that holds the same resources with the same frame. -/
theorem buildThenFree_memory_safe (xs : List (BitVec 32)) (n : Nat) (m : Mem) (r rF : Res)
    (hh : Holds m r rF) (hr : (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList) ⋆ plain) r)
    (hs : m.FSeq) :
    match ((Sched.soloRun n (buildThenFree ⟨ctx, vtp⟩ xs)).run m).run with
    | none => True
    | some (.error err) => err = .stackOverflow
    | some (.ok (v, m')) => Ended v ∧ ∃ r', Holds m' r' rF ∧
        (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList) ⋆ plain) r' ∧ m'.FSeq := by
  have t := (buildThenFree_spec ctx vtp fns I e φ hfit h xs).toSolo n m r rF hh hr hs
  revert t
  rcases ((Sched.soloRun n (buildThenFree ⟨ctx, vtp⟩ xs)).run m).run with _ | err | ⟨v, m'⟩ <;>
    intro t
  · trivial
  · exact t
  · obtain ⟨r', hh', hq, hs'⟩ := t
    obtain ⟨he, hq⟩ := Full.sep_lift.mp hq
    exact ⟨he, r', hh', hq, hs'⟩

/-- **No use after free, no double free, no invalid free**: the run never throws `.illegal`
(`buildThenFree_noIllegal`). -/
theorem buildThenFree_no_illegal (xs : List (BitVec 32)) (n : Nat) (m : Mem) (r rF : Res)
    (hh : Holds m r rF) (hr : (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList) ⋆ plain) r)
    (hs : m.FSeq) :
    ((Sched.soloRun n (buildThenFree ⟨ctx, vtp⟩ xs)).run m).run ≠ some (.error .illegal) :=
  buildThenFree_noIllegal xs _ ctx vtp fns I e φ hfit h n m r rF hh hr hs

/-- **No leak**: every node that `buildThenFree` allocates is given back to the allocator, on
success and on every out-of-memory path, and no resource of the frame is touched: after the
run the caller holds exactly the allocator's state, the fees and the vtable again
(`buildThenFree_noLeak`). -/
theorem buildThenFree_no_leak (xs : List (BitVec 32)) (n : Nat) (m : Mem) (r rF : Res)
    (hh : Holds m r rF) (hr : (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList) ⋆ plain) r)
    (hs : m.FSeq)
    (v : Except ErrName Unit) (m' : Mem)
    (hrun : ((Sched.soloRun n (buildThenFree ⟨ctx, vtp⟩ xs)).run m).run = some (.ok (v, m'))) :
    ∃ r', Holds m' r' rF ∧ (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList) ⋆ plain) r' :=
  buildThenFree_noLeak xs _ ctx vtp fns I e φ hfit h n m r rF hh hr hs v m' hrun

end MemorySafety
