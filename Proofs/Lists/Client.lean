import Proofs.Lists.Alloc
import ZigLean.Sep.Full.Witness

/-!
# A client of the generated list functions, for every allocator

A Lean client composes three functions translated from `examples/lists/lists.zig`
(`Proofs/Lists/Open.lean`): `push` once per item, `reverse`, then `freeAll`. If a `push` fails
with `error.OutOfMemory`, the client frees the part of the list it has built, as a Zig
`errdefer freeAll(a, head)` would. `buildThenFree` is the Lean form of

    fn buildThenFree(a: Allocator, xs: []const u32) !void {
        var head: ?*Node = null;
        for (xs) |x| head = push(a, head, x) catch |e| { freeAll(a, head); return e; };
        head = reverse(head);
        freeAll(a, head);
    }

The allocator `a` is a parameter: every call through it reaches the environment (`Ext`,
premise EXT-05), and the theorems assume only the `std.mem.Allocator` contract `CAllocSpec` of
that allocator (`Proofs/Lists/Alloc.lean`, `docs/interfaces.md`). The client starts with one fee
per item (`fees I φ xs.length`); every free gives a fee back.

`NoIllegal k c` and `NoLeak k c` are the memory-safety properties of a client `c` of one
allocator that starts with `k` fees (`pre`), for every environment, every allocator that meets the
contract, every memory that holds `pre` with any frame and every depth of the run: the run never
throws `.illegal` (no use after free, double free or invalid free), and a run that returns ends
holding `pre` again with the same frame (no leak). `NoIllegal.of_spec` and `NoLeak.of_spec` derive
them from a `CTriple` of the client; `buildThenFree_noIllegal` and `buildThenFree_noLeak` are the
instances for `buildThenFree`. `tutorials/memory-safety/Main.lean` walks through them, and
`tests/roadmap/alloc-translated/ListsPage.lean` refutes them for wrong clients.
-/

namespace Lists.Client

open Zig Zig.Full Zig.Full.FAssn Lists.Open Lists.Alloc

/-! ## The properties -/

/-- What a client of the allocator at `⟨ctx, vtp⟩` starts and ends with: the allocator's state,
`k` fees and the vtable, in the plain mode. -/
abbrev pre (I : FAllocInv) (φ : Frac) (vtp : Ptr) (fns : VTableFns) (k : Nat) : FAssn :=
  I.own ⋆ (fees I φ k ⋆ vtR vtp fns.toList) ⋆ plain

/-- **No use after free, no double free, no invalid free**: for every environment, every
allocator that meets the contract, every memory that holds `pre … k` with any frame, and every
depth, the run of `c` never throws `.illegal`. -/
def NoIllegal (k : Nat) {α : Type} (c : ∀ [Ext], mem_Allocator → ConcM Tgt α) : Prop :=
  ∀ (_ : Ext) (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac),
    I.fits (16 : BitVec 64).toNat 3 → CAllocSpec (CVTable.env (env e) fns) ctx I →
    ∀ (n : Nat) (m : Mem) (r rF : Res), Holds m r rF → pre I φ vtp fns k r → m.FSeq →
      ((Sched.soloRun n (c ⟨ctx, vtp⟩)).run m).run ≠ some (.error .illegal)

/-- **No leak**: under the premises of `NoIllegal`, a run that returns ends holding `pre … k`
again, with the same frame. -/
def NoLeak (k : Nat) {α : Type} (c : ∀ [Ext], mem_Allocator → ConcM Tgt α) : Prop :=
  ∀ (_ : Ext) (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac),
    I.fits (16 : BitVec 64).toNat 3 → CAllocSpec (CVTable.env (env e) fns) ctx I →
    ∀ (n : Nat) (m : Mem) (r rF : Res), Holds m r rF → pre I φ vtp fns k r → m.FSeq →
      ∀ (v : α) (m' : Mem), ((Sched.soloRun n (c ⟨ctx, vtp⟩)).run m).run = some (.ok (v, m')) →
        ∃ r', Holds m' r' rF ∧ pre I φ vtp fns k r'

/-- A client with a `CTriple` from `pre … k`, for every allocator that meets the contract, never
throws `.illegal` (`FTriple.not_illegal`, for every triple). -/
theorem NoIllegal.of_spec {k : Nat} {α : Type} {c : ∀ [Ext], mem_Allocator → ConcM Tgt α}
    (hc : ∀ [Ext] (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac),
      I.fits (16 : BitVec 64).toNat 3 → CAllocSpec (CVTable.env (env e) fns) ctx I →
      ∃ Q, CTriple (pre I φ vtp fns k) (c ⟨ctx, vtp⟩) Q) :
    NoIllegal k c := fun _ ctx vtp fns I e φ hfit h n _ _ _ hh hr hs =>
  have ⟨_, t⟩ := hc ctx vtp fns I e φ hfit h
  (t.toSolo n).not_illegal hh hr hs

/-- A client with a `CTriple` from `pre … k` to `pre … k`, for every allocator that meets the
contract, leaks nothing (`FTriple.holds_of_ok`, for every triple). -/
theorem NoLeak.of_spec {k : Nat} {α : Type} {c : ∀ [Ext], mem_Allocator → ConcM Tgt α}
    (hc : ∀ [Ext] (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac),
      I.fits (16 : BitVec 64).toNat 3 → CAllocSpec (CVTable.env (env e) fns) ctx I →
      CTriple (pre I φ vtp fns k) (c ⟨ctx, vtp⟩) (fun _ => pre I φ vtp fns k)) :
    NoLeak k c := fun _ ctx vtp fns I e φ hfit h n _ _ _ hh hr hs _ _ hrun =>
  have ⟨r', hh', hq, _⟩ := ((hc ctx vtp fns I e φ hfit h).toSolo n).holds_of_ok hh hr hs hrun
  ⟨r', hh', hq⟩

section Client
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
    CTriple (I.own ⋆ (fees I φ xs.length ⋆ (list I φ hd ys ⋆ vtR vtp fns.toList)) ⋆ plain)
      (pushAll ⟨ctx, vtp⟩ hd xs)
      (fun r => I.own ⋆ (built I φ (xs.reverse ++ ys) r ⋆ vtR vtp fns.toList) ⋆ plain) := by
  induction xs generalizing hd ys with
  | nil => exact CTriple.ret' _ fun _ hr => sep_mono_right (fun _ hr =>
      sep_mono_left (fun _ hr => Full.sep_emp.mp (sep_comm hr)) hr) hr
  | cons v vs ih =>
    rw [pushAll]
    refine CTriple.bind (((push_spec ctx vtp fns I e φ hd v hfit h).frame
      (R := fees I φ vs.length ⋆ list I φ hd ys)).pre
      fun _ hr => ac_cast hr (by simp only [List.length_cons, fees_succ]; ac_rfl)) fun r => ?_
    cases r with
    | error e' =>
      -- `error.OutOfMemory`: the list built so far goes back to the allocator
      dsimp only [pushed]
      refine CTriple.pre (P := ⟪e' = "OutOfMemory"⟫ ⋆ ((I.own ⋆ (list I φ hd ys ⋆
          (vtR vtp fns.toList ⋆ (I.fee φ ⋆ fees I φ vs.length)))) ⋆ plain))
        (CTriple.lift fun he => ?_) fun _ hr => ac_cast hr (by ac_rfl)
      refine CTriple.bind ((freeAll_spec ctx vtp fns I e φ hd ys h).frame
        (R := (I.fee φ ⋆ fees I φ vs.length) ⋆ plain) |>.pre fun _ hr => ac_cast hr (by ac_rfl))
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
          vtR vtp fns.toList)) ⋆ plain) _ :=
        ac_cast hr (by ac_rfl)
      exact sep_mono_right (fun _ h' => sep_mono_left (fun _ h' => sep_mono_right (fun _ h' =>
        sep_mono_left (fun _ h'' => ⟨p, hd, Full.sep_lift.mpr ⟨rfl, h''⟩⟩) h') h') h') hr'

/-- `build`, with a fee for each item of `xs`, returns the list of the items of `xs`, in order,
or `error.OutOfMemory` and the fees: on that path every node it allocated is given back. -/
theorem build_spec (xs : List (BitVec 32)) :
    CTriple (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList) ⋆ plain) (build ⟨ctx, vtp⟩ xs)
      (fun r => I.own ⋆ (built I φ xs r ⋆ vtR vtp fns.toList) ⋆ plain) := by
  refine CTriple.bind ((pushAll_spec ctx vtp fns I e φ hfit h xs [] none).pre fun _ hr =>
    sep_mono_right (fun _ h' => sep_mono_left (fun _ h' => sep_mono_right (fun _ h' =>
      ac_cast (Full.sep_lift.mpr ⟨rfl, h'⟩ :
        (⟪(none : Option Ptr) = none⟫ ⋆ vtR vtp fns.toList) _) rfl) h') h') hr) fun r => ?_
  cases r with
  | error e' =>
    exact CTriple.ret' _ fun _ hr => by
      simpa only [built, List.append_nil, List.length_reverse] using hr
  | ok hd =>
    refine CTriple.bind (CTriple.liftMem (((Lists.Linked.reverse_thread (X := nodeRest I φ) hd
      (xs.reverse ++ [])).toPartial.frame (R := (I.own ⋆ vtR vtp fns.toList) ⋆ plain)).pre
        fun _ hr => ?_))
      fun r => CTriple.ret' _ fun _ hr => ?_
    · exact ac_cast hr (by dsimp only [built]; ac_rfl)
    · simp only [List.append_nil, List.reverse_reverse] at hr
      exact ac_cast hr (by dsimp only [built]; ac_rfl)

/-- How `buildThenFree` can end: `ok`, or `error.OutOfMemory`. -/
def Ended (r : Except ErrName Unit) : Prop := r = .ok () ∨ r = .error "OutOfMemory"

/-- `buildThenFree` returns `ok` or `error.OutOfMemory`, and the caller owns what it owned
before: the allocator's state, the fees and the vtable. -/
theorem buildThenFree_spec (xs : List (BitVec 32)) :
    CTriple (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList) ⋆ plain) (buildThenFree ⟨ctx, vtp⟩ xs)
      (fun r => ⟪Ended r⟫ ⋆ (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList) ⋆ plain)) := by
  refine CTriple.bind (build_spec ctx vtp fns I e φ hfit h xs) fun r => ?_
  cases r with
  | error e' =>
    refine CTriple.pre
      (P := ⟪e' = "OutOfMemory"⟫ ⋆ (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList) ⋆ plain))
      (CTriple.lift fun he => CTriple.ret' _ fun _ hr => Full.sep_lift.mpr ⟨Or.inr (by rw [he]), hr⟩)
      fun _ hr => ac_cast hr (by dsimp only [built]; ac_rfl)
  | ok hd =>
    exact CTriple.bind ((freeAll_spec ctx vtp fns I e φ hd xs h).frame (R := plain) |>.pre
      fun _ hr => ac_cast hr (by dsimp only [built]; ac_rfl)) fun _ =>
      CTriple.ret' _ fun _ hr => Full.sep_lift.mpr ⟨Or.inl rfl, ac_cast hr (by ac_rfl)⟩

end Client

/-! ## The properties of the client -/

/-- **`buildThenFree` never throws `.illegal`**, for every allocator that meets the contract. -/
theorem buildThenFree_noIllegal (xs : List (BitVec 32)) :
    NoIllegal xs.length (buildThenFree · xs) :=
  NoIllegal.of_spec fun ctx vtp fns I e φ hfit h => ⟨_, buildThenFree_spec ctx vtp fns I e φ hfit h xs⟩

/-- **`buildThenFree` leaks nothing**, on success and on every out-of-memory path. -/
theorem buildThenFree_noLeak (xs : List (BitVec 32)) :
    NoLeak xs.length (buildThenFree · xs) :=
  NoLeak.of_spec fun ctx vtp fns I e φ hfit h =>
    (buildThenFree_spec ctx vtp fns I e φ hfit h xs).post fun _ _ hr => (Full.sep_lift.mp hr).2

end Lists.Client
