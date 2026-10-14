import ZigLean.Sep.Full.Conc
import ZigLean.Sep.Full.Const
import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.AllocSpec.Ops
import ZigLean.Sep.AllocSpec.Dispatch

/-!
# Indirect calls through a read-only vtable, read in one thread

The translator emits an indirect call (`Air2Lean/Emit.lean`, M20/L11) as a test of the loaded
function pointer against every address-taken function of the callee's type, in a fixed order, and
a last arm for any other pointer: `.illegal` for a closed function type, the environment's call
`Zig.callC (Zig.extCall (Ext.call<i> f …))` for one that the model registry declares open
(`docs/interfaces.md`):

    if f == ⟨some b₁, 0⟩ then call₁ else if f == ⟨some b₂, 0⟩ then call₂ else … else d

`callIndirect f arms d` is that chain over the list `arms` of (function pointer, call) pairs.
`simp only [callIndirect_fold_one, callIndirect_fold_ext, callIndirect_fold_cons]` folds a
generated chain into it (the lemmas are `rfl`; not `@[simp]`, so they neither fire in unrelated
goals nor loop against `callIndirect`'s equations; `fsym` folds with them in concurrent bodies),
and `CTriple.callIndirect` reads it: if the arm that `f` selects (`arms.lookup f`) meets a
triple, so does the call. A `Table` is the program's candidates for one function type, as
functions of the call's arguments, and an `EnvFn` the environment's implementation of that type
at each pointer (the generated `Ext.call<i>`). `Table.callOr t e` is the call through the
table with the environment `e`; `Table.call t` the closed one.

**One mechanism for every interface.** A contract is any property `C` of the function that a
call through a pointer runs (`A → ConcM Tgt α`). The call through `f` runs the arm that `f`
selects (`Table.callOr_of_sel`: whatever the environment, `callOr_env_indep`) or, for a pointer
that no arm serves, the environment (`Table.callOr_of_fresh`). So `C` of the code that runs
follows from `C` of the program's implementation (proved about its translated code) or from `C`
of the environment's (premise EXT-05), never from the environment's contract at a pointer of
the program (`tests/roadmap/interfaces`, the counterexample to that alternative).

The function pointer comes from a vtable, a `const` global: `vtR vtp fns` is the **persistent
knowledge** (`ZigLean/Sep/Full/Const.lean`) that its entries are `fns` (at `vtp`, `vtp + 8`, …). It
owns nothing, so any number of owners hold it at once (`vtR_dup`): two allocator handles with the
same vtable, an allocator and its client. `vtR_load` and `vtR_project` read entry `i` and keep it.
`vtOwn vtp fns` owns the entries' bytes instead (`ptsR`, any block kind: a vtable built at run
time), with the same rules (`vtOwn_load`, `vtOwn_project`); for a `const` global, `vtR_intro`
turns it into `vtR`. Both are `Dispatch.vtR` of the legacy logic
(`ZigLean/Sep/AllocSpec/Dispatch.lean`) for any interface: the list has one entry per function of
the interface.

For `std.mem.Allocator` (`CVTable`, `CAllocSpec`, `CVTable.dispatch`): an allocator whose entries
are concurrent functions meets `FAllocSpec` in the one-thread reading at every depth
(`CAllocSpec`); the allocator that a call site reaches through a vtable holding `fns` is the
dispatch of the program's tables and environment at `fns` (`CVTable.dispatch`). If each entry of
`fns` selects the corresponding function of an implementation `impl`, the dispatch is `impl`
(`CVTable.dispatch_of_selects`), so it meets `impl`'s specification (`CAllocSpec.dispatch`); if no
entry is a function of the program (`AllocTables.Fresh`), it is the environment's allocator at
`fns` (`CVTable.dispatch_of_fresh`, `CAllocSpec.dispatch_env`). These are the `Table` rules for
the four entries; other interfaces (`std.Random`, `Io`, …) use `callIndirect`, `Table`, `EnvFn`
and `vtR` the same way.

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig
namespace Full

open FAssn

variable {Tgt α A : Type}

/-- The arms of a generated indirect call on the function pointer `f`, and the last arm `d` for
any other pointer (module doc). -/
def callIndirect {m : Type → Type} (f : Ptr) : List (Ptr × m α) → m α → m α
  | [], d => d
  | (c, x) :: arms, d => if f == c then x else callIndirect f arms d

section Fold

variable {m : Type → Type} {f c : Ptr} {x : m α}

/-- The innermost arm of a generated chain of a closed function type. -/
theorem callIndirect_fold_one [MonadExceptOf Error m] :
    (if f == c then x else (throw .illegal : m α)) = callIndirect f [(c, x)] (throw .illegal) :=
  rfl

/-- The innermost arm of a generated chain of an open function type: the environment's call
after it. -/
theorem callIndirect_fold_ext {σ : Type} {x : CM Tgt σ α} {d : ConcM Tgt α} :
    (if f == c then x else (callC (extCall d) : CM Tgt σ α)) =
      callIndirect f [(c, x)] (callC (extCall d)) := rfl

/-- One more arm of a generated chain. -/
theorem callIndirect_fold_cons {arms : List (Ptr × m α)} {d : m α} :
    (if f == c then x else callIndirect f arms d) = callIndirect f ((c, x) :: arms) d := rfl

end Fold

section Arms

variable {m : Type → Type} {f : Ptr} {arms : List (Ptr × m α)} {d : m α}

/-- The arm that `f` selects. -/
theorem callIndirect_of_lookup {x : m α} (h : arms.lookup f = some x) :
    callIndirect f arms d = x := by
  induction arms with
  | nil => cases h
  | cons a arms ih =>
    obtain ⟨c, y⟩ := a
    by_cases hc : f = c
    · subst hc
      simp only [List.lookup_cons_self, Option.some.injEq] at h
      simp [callIndirect, h]
    · have hc' : (f == c) = false := beq_false_of_ne hc
      simp only [List.lookup, hc'] at h
      simp only [callIndirect, hc', Bool.false_eq_true, ↓reduceIte]
      exact ih h

/-- A pointer that no arm serves takes the last arm. -/
theorem callIndirect_of_lookup_none (h : arms.lookup f = none) : callIndirect f arms d = d := by
  induction arms with
  | nil => rfl
  | cons a arms ih =>
    obtain ⟨c, y⟩ := a
    have hc' : (f == c) = false := by
      by_cases hc : f = c
      · subst hc; simp at h
      · exact beq_false_of_ne hc
    simp only [List.lookup, hc'] at h
    simp only [callIndirect, hc', Bool.false_eq_true, ↓reduceIte]
    exact ih h

end Arms

/-- The chain under the locals of a generated function (`CM`). -/
theorem callIndirect_run {σ : Type} {f : Ptr} (arms : List (Ptr × CM Tgt σ α)) (d : CM Tgt σ α)
    (s : σ) :
    (callIndirect f arms d).run s =
      callIndirect f (arms.map fun a => (a.1, a.2.run s)) (d.run s) := by
  induction arms with
  | nil => rfl
  | cons a arms ih =>
    simp only [callIndirect, List.map_cons]
    split
    · rfl
    · exact ih

/-- A continuation after the call is a continuation of every arm. -/
theorem callIndirect_bind {β : Type} {f : Ptr} (arms : List (Ptr × ConcM Tgt α)) (d : ConcM Tgt α)
    (k : α → ConcM Tgt β) :
    callIndirect f arms d >>= k = callIndirect f (arms.map fun a => (a.1, a.2 >>= k)) (d >>= k) := by
  induction arms with
  | nil => rfl
  | cons a arms ih =>
    simp only [callIndirect, List.map_cons]
    split
    · rfl
    · exact ih

/-- **An indirect call** meets the triple of the arm that its function pointer selects. -/
theorem CTriple.callIndirect {P : FAssn} {Q : α → FAssn} {f : Ptr}
    {arms : List (Ptr × ConcM Tgt α)} {d x : ConcM Tgt α} (h : arms.lookup f = some x)
    (hx : CTriple P x Q) : CTriple P (Full.callIndirect f arms d) Q := by
  rw [callIndirect_of_lookup h]; exact hx

/-- The program's candidates for an indirect call of one function type, as functions of the
call's arguments `A` (module doc). -/
abbrev Table (Tgt A α : Type) := List (Ptr × (A → ConcM Tgt α))

/-- The environment's implementation of one function type at each function pointer (the
generated `Ext.call<i>`, premise EXT-05; module doc). -/
abbrev EnvFn (Tgt A α : Type) := Ptr → A → ConcM Tgt α

/-- The environment of a closed program: no function besides the program's (`Ext.closed`). -/
def EnvFn.closed : EnvFn Tgt A α := fun _ _ => throw .illegal

/-- **The indirect call through `f` with arguments `a`**, the environment `e` serving every
pointer that no arm of `t` does: the generated call of an open function type. -/
def Table.callOr (t : Table Tgt A α) (e : EnvFn Tgt A α) (f : Ptr) (a : A) : ConcM Tgt α :=
  callIndirect f (t.map fun g => (g.1, g.2 a)) (extCall (e f a))

/-- The indirect call of a closed function type: `.illegal` for a pointer that no arm serves. -/
def Table.call (t : Table Tgt A α) (f : Ptr) (a : A) : ConcM Tgt α :=
  callIndirect f (t.map fun g => (g.1, g.2 a)) (throw .illegal)

/-- The closed call is the call with the closed environment. -/
theorem Table.call_eq_callOr (t : Table Tgt A α) (f : Ptr) (a : A) :
    t.call f a = t.callOr EnvFn.closed f a := rfl

/-- `f` selects `g` in `t`. -/
def Table.Sel (t : Table Tgt A α) (f : Ptr) (g : A → ConcM Tgt α) : Prop := t.lookup f = some g

/-- No arm of `t` serves `f`: a call through `f` reaches the environment. -/
def Table.Fresh (t : Table Tgt A α) (f : Ptr) : Prop := t.lookup f = none

theorem Table.fresh_nil (f : Ptr) : Table.Fresh ([] : Table Tgt A α) f := rfl

theorem Table.lookup_map {t : Table Tgt A α} {f : Ptr} (a : A) :
    (t.map fun g => (g.1, g.2 a)).lookup f = (t.lookup f).map (· a) := by
  induction t with
  | nil => rfl
  | cons c t ih =>
    obtain ⟨c, g⟩ := c
    by_cases hc : f = c
    · subst hc; simp
    · have hc' : (f == c) = false := beq_false_of_ne hc
      simp only [List.map_cons, List.lookup, hc']
      exact ih

section Table

variable {t : Table Tgt A α} {f : Ptr}

/-- **A pointer of the program runs its arm**, whatever the environment. -/
theorem Table.callOr_of_sel {g : A → ConcM Tgt α} (h : t.Sel f g) (e : EnvFn Tgt A α) (a : A) :
    t.callOr e f a = g a :=
  callIndirect_of_lookup (by rw [Table.lookup_map, show t.lookup f = some g from h]; rfl)

theorem Table.call_of_sel {g : A → ConcM Tgt α} (h : t.Sel f g) (a : A) : t.call f a = g a :=
  Table.callOr_of_sel h EnvFn.closed a

/-- **A pointer that no arm serves runs the environment.** -/
theorem Table.callOr_of_fresh (h : t.Fresh f) (e : EnvFn Tgt A α) (a : A) :
    t.callOr e f a = extCall (e f a) :=
  callIndirect_of_lookup_none (by rw [Table.lookup_map, show t.lookup f = none from h]; rfl)

/-- **The environment does not reach a pointer of the program.** -/
theorem Table.callOr_env_indep {g : A → ConcM Tgt α} (h : t.Sel f g) (e e' : EnvFn Tgt A α) :
    t.callOr e f = t.callOr e' f :=
  funext fun a => (Table.callOr_of_sel h e a).trans (Table.callOr_of_sel h e' a).symm

/-- **A contract of the code that runs, from the program's implementation** (proved about its
translated code). `C` is any property of the function the pointer runs. -/
theorem Table.contract_of_sel {C : (A → ConcM Tgt α) → Prop} {g : A → ConcM Tgt α}
    (h : t.Sel f g) (e : EnvFn Tgt A α) (hg : C g) : C (t.callOr e f) := by
  have : t.callOr e f = g := funext (Table.callOr_of_sel h e)
  rwa [this]

/-- **A contract of the code that runs, from the environment's** (premise EXT-05), for a
pointer that no arm serves. -/
theorem Table.contract_of_fresh {C : (A → ConcM Tgt α) → Prop} (h : t.Fresh f)
    (e : EnvFn Tgt A α) (he : C fun a => extCall (e f a)) : C (t.callOr e f) := by
  have : t.callOr e f = fun a => extCall (e f a) := funext (Table.callOr_of_fresh h e)
  rwa [this]

end Table

/-- **The contract of an interface function** `g` (a callback, a vtable entry): every call
`g a` meets the precondition `P a` and the postcondition `Q a`. Each interface states its own
`P`/`Q` (plain assertions); logical variables are quantified outside (`∀ x, FnSpec (P x) (Q x)
g`). A client assumes it of the function the call runs (`Table.contract_of_sel`/`_of_fresh`). -/
def FnSpec (P : A → FAssn) (Q : A → α → FAssn) (g : A → ConcM Tgt α) : Prop :=
  ∀ a, CTriple (P a) (g a) (Q a)

/-- The call step of a contract. -/
theorem FnSpec.call {P : A → FAssn} {Q : A → α → FAssn} {g : A → ConcM Tgt α}
    (h : FnSpec P Q g) (a : A) : CTriple (P a) (g a) (Q a) :=
  h a

/-- **A call through a table, then a continuation**: the form of a generated call site after
`conc_norm` (the continuation is pushed into every arm). -/
theorem CTriple.tableCall {β : Type} {P : FAssn} {Q : α → FAssn} {S : β → FAssn}
    {t : Table Tgt A α} {f : Ptr} {a : A} {g : α → ConcM Tgt β} (h : CTriple P (t.call f a) Q)
    (hg : ∀ v, CTriple (Q v) (g v) S) :
    CTriple P (Full.callIndirect f (t.map fun x => (x.1, x.2 a >>= g)) (throw .illegal)) S := by
  have e : Full.callIndirect f (t.map fun x => (x.1, x.2 a >>= g)) (throw .illegal) =
      t.call f a >>= g := by
    rw [Table.call, callIndirect_bind, List.map_map]; rfl
  rw [e]; exact CTriple.bind h hg

/-- **A call through a table with an environment, then a continuation** (`CTriple.tableCall`
for an open function type). -/
theorem CTriple.tableCallOr {β : Type} {P : FAssn} {Q : α → FAssn} {S : β → FAssn}
    {t : Table Tgt A α} {e : EnvFn Tgt A α} {f : Ptr} {a : A} {g : α → ConcM Tgt β}
    (h : CTriple P (t.callOr e f a) Q) (hg : ∀ v, CTriple (Q v) (g v) S) :
    CTriple P (Full.callIndirect f (t.map fun x => (x.1, x.2 a >>= g)) (extCall (e f a) >>= g))
      S := by
  have e : Full.callIndirect f (t.map fun x => (x.1, x.2 a >>= g)) (extCall (e f a) >>= g) =
      t.callOr e f a >>= g := by
    rw [Table.callOr, callIndirect_bind, List.map_map]; rfl
  rw [e]; exact CTriple.bind h hg

/-! ## An owned vtable -/

open Assn in
/-- The vtable at `vtp` holds the function pointers `fns`, as owned bytes read only (`ptsR`, any
block kind). -/
def vtOwn (vtp : Ptr) : List Ptr → Assn
  | [] => Assn.emp
  | f :: fns => ptsR vtp 8 f ∗ vtOwn (vtp.add 8) fns

open Assn in
/-- Entry `i` of the vtable, and the rest. -/
theorem vtOwn_split {vtp : Ptr} {fns : List Ptr} {i : Nat} (hi : i < fns.length) {h : Heap}
    (hv : vtOwn vtp fns h) :
    ∃ R : Assn, (ptsR (vtp.add (8 * i)) 8 fns[i] ∗ R) h ∧
      ∀ h', (ptsR (vtp.add (8 * i)) 8 fns[i] ∗ R) h' → vtOwn vtp fns h' := by
  induction fns generalizing vtp i h with
  | nil => cases hi
  | cons f fns ih =>
    cases i with
    | zero =>
      refine ⟨vtOwn (vtp.add 8) fns, ?_, fun h' x => ?_⟩
      · simpa [vtOwn, Ptr.add] using hv
      · simpa [vtOwn, Ptr.add] using x
    | succ i =>
      obtain ⟨h₁, h₂, hd, rfl, h1, h2⟩ := hv
      obtain ⟨R, hR, back⟩ := ih (vtp := vtp.add 8) (i := i) (by simp at hi; omega) h2
      have e : (vtp.add 8).add (8 * i) = vtp.add (8 * (i + 1)) := by
        simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega
      rw [e] at hR back
      refine ⟨ptsR vtp 8 f ∗ R, ?_, fun h' x => ?_⟩
      · simp only [List.getElem_cons_succ]
        rw [Zig.sep_left_comm_eq]; exact ⟨h₁, h₂, hd, rfl, h1, hR⟩
      · simp only [List.getElem_cons_succ] at x
        rw [Zig.sep_left_comm_eq] at x
        obtain ⟨h₁', h₂', hd', rfl, h1', h2'⟩ := x
        exact ⟨h₁', h₂', hd', rfl, h1', back _ h2'⟩

/-- **Load** of a read-only typed value (`ptsR`, a block of any kind): the owned bytes' rule
`load_bytesAt` at byte 0. -/
theorem FTotalTriple.ptsR_load {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    FTotalTriple (up (ptsR p a v)) (Zig.load T a p) (fun x => ⟪x = v⟫ ⋆ up (ptsR p a v)) := by
  refine FTotalTriple.of_cases fun r hp => ?_
  obtain ⟨⟨A, S, K, bs, ha, hs, hv, hb⟩, hk, hg⟩ := hp
  have t := FTotalTriple.load_bytesAt (q := p) (k := 0) (al := a) (A := A) (S := S) (K := K)
    (bs := bs) hn (by omega) (by simpa using ha)
    (by rw [Nat.zero_add, ← hs, Array.extract_size]; exact hv)
  simp only [Int.natCast_zero, Ptr.add_zero] at t
  refine ⟨_, _, t, ⟨hb, hk, hg⟩, fun x r' h => ?_⟩
  obtain ⟨hx, hb', hk', hg'⟩ := sep_lift.mp h
  exact sep_lift.mpr ⟨hx, ⟨A, S, K, bs, ha, hs, hv, hb'⟩, hk', hg'⟩

/-- Load entry `i` of the vtable: the function pointer `fns[i]`; the vtable stays. -/
theorem vtOwn_load {vtp : Ptr} {fns : List Ptr} {i : Nat} (hi : i < fns.length) :
    FTriple (up (vtOwn vtp fns)) (load Ptr 8 (vtp.add (8 * i)))
      (fun f => ⟪f = fns[i]⟫ ⋆ up (vtOwn vtp fns)) := by
  intro m r rF hh hp hs
  obtain ⟨R, hR, back⟩ := vtOwn_split hi hp.1
  refine (((FTotalTriple.ptsR_load (p := vtp.add (8 * i)) (a := 8) (v := fns[i])
    (by decide)).toPartial.frame (R := up R)).post fun f r' hq => ?_) m r rF hh
      (up_sep ⟨hR, hp.2⟩) hs
  obtain ⟨hv, hq⟩ := sep_lift.mp (sep_assoc hq)
  obtain ⟨hq, hk, hg⟩ := sep_up hq
  exact sep_lift.mpr ⟨hv, back _ hq, hk, hg⟩

open Assn in
/-- The pointer to entry `i` of a vtable that the precondition holds: formed (MM-3), no effect. -/
theorem vtOwn_project {vtp : Ptr} {fns : List Ptr} {i : Nat} (hi : i < fns.length)
    (hv : 0 ≤ vtp.off) :
    FTriple (up (vtOwn vtp fns)) (ptrProject vtp (·.add (8 * i)))
      (fun q => ⟪q = vtp.add (8 * i)⟫ ⋆ up (vtOwn vtp fns)) := by
  refine FTriple.of_run fun m r rF hh hp hs => ?_
  obtain ⟨R, hR, -⟩ := vtOwn_split hi hp.1
  obtain ⟨h₁, h₂, -, he, ⟨A, S, K, bs, -, hsz, -, b, hqb, h0, hl⟩, -⟩ := hR
  have hs8 : bs.size = 8 := hsz
  -- the entry's last byte is owned: the block reaches past the entry (ownership, `Holds.block`)
  have hc := hl (b, (vtp.add (8 * i)).off.toNat + 7)
  rw [if_pos ⟨rfl, by omega, by omega⟩] at hc
  have hc' : r.heap.erase (b, (vtp.add (8 * i)).off.toNat + 7) = some
      ⟨bs[(vtp.add (8 * i)).off.toNat + 7 - (vtp.add (8 * i)).off.toNat]!, A, S, K⟩ := by
    rw [he]; simp [hc]
  simp only [FHeap.erase, Option.map_eq_some_iff] at hc'
  obtain ⟨fc, hfc, -⟩ := hc'
  obtain ⟨blk, hblk, -, hx, -⟩ := hh.block hfc
  have hvb : vtp.block = some b := by simpa [Ptr.add] using hqb
  have hoff : (vtp.add (8 * i)).off = vtp.off + 8 * i := by simp [Ptr.add]
  exact ⟨_, m, r, ptrProject_add_run (inBounds_of hvb hblk hv (by omega))
    (inBounds_of hqb hblk h0 (by omega)), hh, sep_lift.mpr ⟨rfl, hp⟩, hs⟩

/-! ## The read-only vtable (persistent) -/

/-- **The vtable at `vtp` holds the function pointers `fns`**: persistent knowledge of a `const`
global (module doc). -/
def vtR (vtp : Ptr) : List Ptr → FAssn
  | [] => FAssn.emp
  | f :: fns => cpts vtp 8 f ⋆ vtR (vtp.add 8) fns

theorem Persistent.vtR {vtp : Ptr} : ∀ {fns : List Ptr}, Persistent (Zig.Full.vtR vtp fns)
  | [] => Persistent.emp
  | _ :: _ => Persistent.cpts.sep Persistent.vtR

/-- **The vtable is duplicable**: any number of owners hold it. -/
theorem vtR_dup {vtp : Ptr} {fns : List Ptr} {r : Res} (h : vtR vtp fns r) :
    (vtR vtp fns ⋆ vtR vtp fns) r :=
  Persistent.vtR.dup h

/-- The vtable can be forgotten. -/
theorem vtR_drop {vtp : Ptr} {fns : List Ptr} {R : FAssn} : EUpd (vtR vtp fns ⋆ R) R :=
  Persistent.vtR.drop

/-- Entry `i` of the vtable: `const` bytes that decode to `fns[i]`. -/
theorem vtR_entry {vtp : Ptr} {fns : List Ptr} {i : Nat} (hi : i < fns.length) :
    ConstAt (vtp.add (8 * i)) (fun A bs => (A + (vtp.add (8 * i)).off.toNat) % 8 = 0 ∧
      bs.size = Enc.size Ptr ∧ Enc.decode bs = pure fns[i]) (vtR vtp fns) := by
  induction fns generalizing vtp i with
  | nil => cases hi
  | cons f fns ih =>
    cases i with
    | zero =>
      show ConstAt _ _ (cpts vtp 8 f ⋆ vtR (vtp.add 8) fns)
      simpa using (ConstAt.cpts (p := vtp) (a := 8) (v := f) (by decide)).sepL
    | succ i =>
      show ConstAt _ _ (cpts vtp 8 f ⋆ vtR (vtp.add 8) fns)
      have e : (vtp.add 8).add (8 * i) = vtp.add (8 * (i + 1)) := by
        simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega
      have := (ih (vtp := vtp.add 8) (i := i) (by simp at hi; omega)).sepR (R := cpts vtp 8 f)
      rw [e] at this
      simpa using this

/-- Load entry `i` of the vtable: the function pointer `fns[i]`; the vtable stays. A thread rule
(`FTTotalTriple.load_const`: a read of `const` bytes); the sequential rule is its
`toFTotalTriple`. -/
theorem vtR_load {vtp : Ptr} {fns : List Ptr} {i : Nat} (hi : i < fns.length) :
    FTTotalTriple (vtR vtp fns) (load Ptr 8 (vtp.add (8 * i)))
      (fun f => ⟪f = fns[i]⟫ ⋆ vtR vtp fns) :=
  FTTotalTriple.load_const (vtR_entry hi) fun _ _ h => h

/-- The pointer to entry `i` of the vtable: formed (MM-3), no effect. -/
theorem vtR_project {vtp : Ptr} {fns : List Ptr} {i : Nat} (hi : i < fns.length)
    (hv : 0 ≤ vtp.off) :
    FTotalTriple (vtR vtp fns) (ptrProject vtp (·.add (8 * i)))
      (fun q => ⟪q = vtp.add (8 * i)⟫ ⋆ vtR vtp fns) :=
  FTotalTriple.of_read fun m r rF hh hp _ => by
    obtain ⟨b, blk, bs, hqb, hblk, -, -, h0, hpos, -, hx⟩ := vtR_entry (vtp := vtp) hi m r rF hh hp
    obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp (hx (bs.size - 1) (by omega))
    have hvb : vtp.block = some b := by simpa [Ptr.add] using hqb
    have hoff : (vtp.add (8 * i)).off = vtp.off + 8 * i := by simp [Ptr.add]
    exact ptrProject_add_run (inBounds_of hvb hblk hv (by omega))
      (inBounds_of hqb hblk h0 (by omega))

/-- The vtable from known `const` bytes `bs` at `vtp` that hold the entries `fns`: its facts are
facts of `bs`. -/
theorem vtR_know {b : BlockId} {A : Nat} : ∀ {fns : List Ptr} {vtp : Ptr} {bs : Array Byte},
    vtp.block = some b → 0 ≤ vtp.off → (A + vtp.off.toNat) % 8 = 0 → bs.size = 8 * fns.length →
    (∀ i (hi : i < fns.length), Enc.decode (bs.extract (8 * i) (8 * i + 8)) = pure fns[i]) →
    ∃ k, Know.Sub k (cknow b A vtp.off.toNat bs) ∧ vtR vtp fns ⟨FHeap.empty, k, Ghost.unit⟩
  | [], _, _, _, _, _, _, _ => ⟨Know.none, Know.sub_none _, rfl, rfl, rfl⟩
  | f :: fns, vtp, bs, hpb, h0, hal, hs, hd => by
    simp only [List.length_cons] at hs
    have hoff : (vtp.add 8).off.toNat = vtp.off.toNat + 8 := by simp [Ptr.add]; omega
    have hpb' : (vtp.add 8).block = some b := by simpa [Ptr.add] using hpb
    have h0' : 0 ≤ (vtp.add 8).off := by simp [Ptr.add]; omega
    have hal' : (A + (vtp.add 8).off.toNat) % 8 = 0 := by rw [hoff]; omega
    have hs' : (bs.extract 8 bs.size).size = 8 * fns.length := by simp; omega
    have hd' : ∀ i (hi : i < fns.length),
        Enc.decode ((bs.extract 8 bs.size).extract (8 * i) (8 * i + 8)) = pure fns[i] := by
      intro i hi
      have := hd (i + 1) (by simp only [List.length_cons]; omega)
      simp only [List.getElem_cons_succ] at this
      rw [← this, Array.extract_extract, show 8 + 8 * i = 8 * (i + 1) by omega,
        show (Min.min (8 + (8 * i + 8)) bs.size : Nat) = 8 * (i + 1) + 8 by omega]
    obtain ⟨k, hk, hv⟩ := vtR_know hpb' h0' hal' hs' hd'
    let k₀ := cknow b A vtp.off.toNat (bs.extract 0 8)
    have hv0 : cpts vtp 8 f ⟨FHeap.empty, k₀, Ghost.unit⟩ := by
      refine ⟨A, bs.extract 0 8, hal, ?_, ?_, rfl, rfl, b, hpb, h0, rfl⟩
      · simp only [Array.size_extract]; rw [show Enc.size Ptr = 8 from rfl]; omega
      · have := hd 0 (by simp)
        simpa only [List.getElem_cons_zero, Nat.mul_zero, Nat.zero_add] using this
    refine ⟨k₀.union k, Know.Sub.union ?_ ?_, ?_⟩
    · rintro f (rfl | ⟨i, hi, rfl⟩)
      · exact .inl rfl
      · simp only [Array.size_extract] at hi
        exact .inr ⟨i, by omega, by simp [Array.getElem_extract]⟩
    · intro f hf
      rcases hk f hf with rfl | ⟨i, hi, rfl⟩
      · exact .inl rfl
      · simp only [Array.size_extract] at hi
        refine .inr ⟨8 + i, by omega, ?_⟩
        rw [hoff]; simp [Array.getElem_extract, Nat.add_assoc]
    · show (cpts vtp 8 f ⋆ vtR (vtp.add 8) fns) _
      exact ⟨⟨FHeap.empty, k₀, Ghost.unit⟩, ⟨FHeap.empty, k, Ghost.unit⟩, fun _ => .inl rfl,
        by simp [Ghost.add_unit], hv0, hv⟩

/-- **Known `const` bytes that hold the entries `fns` are the vtable** (the bytes stay known). -/
theorem vtR_of_cbytesAt {vtp : Ptr} {A : Nat} {fns : List Ptr} {bs : Array Byte} {r : Res}
    (hal : (A + vtp.off.toNat) % 8 = 0) (hs : bs.size = 8 * fns.length)
    (hd : ∀ i (hi : i < fns.length), Enc.decode (bs.extract (8 * i) (8 * i + 8)) = pure fns[i])
    (h : cbytesAt vtp A bs r) : (vtR vtp fns ⋆ cbytesAt vtp A bs) r := by
  obtain ⟨-, -, b, hpb, h0, hk⟩ := id h
  obtain ⟨k, hsub, hv⟩ := vtR_know hpb h0 hal hs hd
  exact Persistent.absorb hv (by rw [hk]; exact hsub) h

/-- **The owner of a `const` global vtable's bytes gives out the persistent vtable** and keeps
the bytes (e.g. at program start: the global's initial bytes). -/
theorem vtR_intro {vtp : Ptr} {A S : Nat} {bs : Array Byte} {fns : List Ptr}
    (hal : (A + vtp.off.toNat) % 8 = 0) (hs : bs.size = 8 * fns.length) (hpos : 0 < fns.length)
    (hd : ∀ i (hi : i < fns.length), Enc.decode (bs.extract (8 * i) (8 * i + 8)) = pure fns[i]) :
    EUpd (up (bytesAt vtp A S .constGlobal bs))
      (up (bytesAt vtp A S .constGlobal bs) ⋆ vtR vtp fns) :=
  ((cbytesAt_intro (by omega)).trans (EUpd.of_imp fun _ h => by
    have := sep_mono_right (fun _ hc => sep_comm (vtR_of_cbytesAt hal hs hd hc)) h
    rwa [sep_left_comm_eq] at this)).trans Persistent.cbytesAt.drop

/-! ## `std.mem.Allocator` -/

/-- An allocator's four entries as concurrent functions (a translated implementation of
`std.mem.Allocator.VTable`; the alignment as its log2). -/
structure CVTable (Tgt : Type) where
  alloc : Ptr → BitVec 64 → Nat → BitVec 64 → ConcM Tgt (Option Ptr)
  resize : Ptr → Slice → Nat → BitVec 64 → BitVec 64 → ConcM Tgt Bool
  remap : Ptr → Slice → Nat → BitVec 64 → BitVec 64 → ConcM Tgt (Option Ptr)
  free : Ptr → Slice → Nat → BitVec 64 → ConcM Tgt Unit

/-- The entries read in one thread at depth `fuel` (`Sched.soloRun`). -/
def CVTable.solo (vt : CVTable Tgt) (fuel : Nat) : RawVTable where
  alloc c n k ra := Sched.soloRun fuel (vt.alloc c n k ra)
  resize c s k n ra := Sched.soloRun fuel (vt.resize c s k n ra)
  remap c s k n ra := Sched.soloRun fuel (vt.remap c s k n ra)
  free c s k ra := Sched.soloRun fuel (vt.free c s k ra)

/-- **The allocator contract for concurrent entries** (audit `structure-2026-10-13.md` #2): the
four entries' `CTriple`s, the concurrent form of `FAllocSpec` (the same pre- and postconditions).
A thread calls an entry inside a protocol (`WP.call_fowned`); a sequential caller reads it in its
own thread (`CAllocSpec.solo`, `CTriple.toSolo`). -/
structure CAllocSpec (vt : CVTable Tgt) (ctx : Ptr) (I : FAllocInv) : Prop where
  alloc : ∀ len k ra φ, 0 < len.toNat → k < 64 → I.fits len.toNat k →
    CTriple (I.own ⋆ I.fee φ) (vt.alloc ctx len k ra) (I.allocPost len.toNat k φ)
  /-- The refined `resize` (`FAllocSpec.resize`). -/
  resize : ∀ s k n ra A S K q q' φ tl, k < 64 → 0 < n.toNat → I.fits n.toNat k →
    0 < s.len.toNat → q'.val ≤ q.val → (n.toNat < s.len.toNat → q' = q) →
    CTriple (I.own ⋆ (I.held s.ptr s.len.toNat k A S K q q' φ ⋆
        I.relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (vt.resize ctx s k n ra) (I.rresizePost s.ptr k s.len.toNat n.toNat A S K q q' φ tl)
  remap : ∀ s k n ra φ bs, k < 64 → 0 < n.toNat → I.fits n.toNat k → s.len.toNat = bs.size →
    0 < bs.size → CTriple (I.own ⋆ I.granted s.ptr k φ bs) (vt.remap ctx s k n ra)
      (I.remapPost s.ptr k φ bs n.toNat)
  free : ∀ s k ra φ bs, k < 64 → s.len.toNat = bs.size → 0 < bs.size →
    CTriple (I.own ⋆ I.granted s.ptr k φ bs) (vt.free ctx s k ra) (fun _ => I.own ⋆ I.fee φ)

/-- `CAllocSpec` from `CTriple`s of the four entries. -/
theorem CAllocSpec.of_ctriples {vt : CVTable Tgt} {ctx : Ptr} {I : FAllocInv}
    (ha : ∀ len k ra φ, 0 < len.toNat → k < 64 → I.fits len.toNat k →
      CTriple (I.own ⋆ I.fee φ) (vt.alloc ctx len k ra) (I.allocPost len.toNat k φ))
    (hr : ∀ s k n ra A S K q q' φ tl, k < 64 → 0 < n.toNat → I.fits n.toNat k → 0 < s.len.toNat →
      q'.val ≤ q.val → (n.toNat < s.len.toNat → q' = q) →
      CTriple (I.own ⋆ (I.held s.ptr s.len.toNat k A S K q q' φ ⋆
          I.relBytes s.ptr A S K n.toNat s.len.toNat tl))
        (vt.resize ctx s k n ra) (I.rresizePost s.ptr k s.len.toNat n.toNat A S K q q' φ tl))
    (hm : ∀ s k n ra φ bs, k < 64 → 0 < n.toNat → I.fits n.toNat k → s.len.toNat = bs.size →
      0 < bs.size → CTriple (I.own ⋆ I.granted s.ptr k φ bs) (vt.remap ctx s k n ra)
        (I.remapPost s.ptr k φ bs n.toNat))
    (hf : ∀ s k ra φ bs, k < 64 → s.len.toNat = bs.size → 0 < bs.size →
      CTriple (I.own ⋆ I.granted s.ptr k φ bs) (vt.free ctx s k ra) (fun _ => I.own ⋆ I.fee φ)) :
    CAllocSpec vt ctx I := ⟨ha, hr, hm, hf⟩

section CAllocSpec

variable {vt : CVTable Tgt} {ctx : Ptr} {I : FAllocInv} (h : CAllocSpec vt ctx I)
include h

/-- The whole-region `resize` (`FAllocInv.resize_granted_gen`). -/
theorem CAllocSpec.resize_granted (s : Slice) (k : Nat) (n ra : BitVec 64) (φ : Frac)
    (bs : Array Byte) (h1 : k < 64) (h2 : 0 < n.toNat) (h3 : I.fits n.toNat k)
    (h4 : s.len.toNat = bs.size) (h5 : 0 < bs.size) :
    CTriple (I.own ⋆ I.granted s.ptr k φ bs) (vt.resize ctx s k n ra)
      (I.resizePost s.ptr k φ bs n.toNat) :=
  I.resize_granted_gen (T := CTriple) (fun h hp => CTriple.pre h hp) (fun h => CTriple.frame h)
    (fun h => CTriple.ex h) (fun h hu => CTriple.eupd_post h hu)
    (fun A S K q q' tl h6 h7 => h.resize s k n ra A S K q q' φ tl h1 h2 h3 (by omega) h6 h7) h4

/-- **The old statement**: the entries read in one thread at every depth satisfy `FAllocSpec`
(partial correctness). -/
theorem CAllocSpec.solo (fuel : Nat) : FAllocSpec FLogic.partial (vt.solo fuel) ctx I where
  alloc len k ra φ h1 h2 h3 := (h.alloc len k ra φ h1 h2 h3).toSolo fuel
  resize s k n ra A S K q q' φ tl h1 h2 h3 h4 h5 h6 :=
    (h.resize s k n ra A S K q q' φ tl h1 h2 h3 h4 h5 h6).toSolo fuel
  remap s k n ra φ bs h1 h2 h3 h4 h5 := (h.remap s k n ra φ bs h1 h2 h3 h4 h5).toSolo fuel
  free s k ra φ bs h1 h2 h3 := (h.free s k ra φ bs h1 h2 h3).toSolo fuel

end CAllocSpec

/-- The environment's implementations of the four entries' function types of
`std.mem.Allocator.VTable` (the generated `Ext`, premise EXT-05). -/
structure AllocEnv (Tgt : Type) where
  alloc : EnvFn Tgt (Ptr × BitVec 64 × Nat × BitVec 64) (Option Ptr)
  resize : EnvFn Tgt (Ptr × Slice × Nat × BitVec 64 × BitVec 64) Bool
  remap : EnvFn Tgt (Ptr × Slice × Nat × BitVec 64 × BitVec 64) (Option Ptr)
  free : EnvFn Tgt (Ptr × Slice × Nat × BitVec 64) Unit

/-- A closed program's environment: no allocator besides the program's. -/
def AllocEnv.closed : AllocEnv Tgt := ⟨EnvFn.closed, EnvFn.closed, EnvFn.closed, EnvFn.closed⟩

/-- The program's candidates for the four entries of `std.mem.Allocator.VTable`: one `Table` per
function type, and the environment for any other pointer (closed by default). -/
structure AllocTables (Tgt : Type) where
  alloc : Table Tgt (Ptr × BitVec 64 × Nat × BitVec 64) (Option Ptr)
  resize : Table Tgt (Ptr × Slice × Nat × BitVec 64 × BitVec 64) Bool
  remap : Table Tgt (Ptr × Slice × Nat × BitVec 64 × BitVec 64) (Option Ptr)
  free : Table Tgt (Ptr × Slice × Nat × BitVec 64) Unit
  env : AllocEnv Tgt := AllocEnv.closed

/-- The allocator that a call site reaches through a vtable holding `fns`: each entry is the
indirect call through the entry's function pointer, the environment serving any pointer that no
function of the program does. -/
def CVTable.dispatch (t : AllocTables Tgt) (fns : VTableFns) : CVTable Tgt where
  alloc c n k ra := t.alloc.callOr t.env.alloc fns.alloc (c, n, k, ra)
  resize c s k n ra := t.resize.callOr t.env.resize fns.resize (c, s, k, n, ra)
  remap c s k n ra := t.remap.callOr t.env.remap fns.remap (c, s, k, n, ra)
  free c s k ra := t.free.callOr t.env.free fns.free (c, s, k, ra)

/-- The environment's allocator at the vtable `fns`: each entry is the environment's call
through the entry's function pointer. -/
def CVTable.env (e : AllocEnv Tgt) (fns : VTableFns) : CVTable Tgt where
  alloc c n k ra := extCall (e.alloc fns.alloc (c, n, k, ra))
  resize c s k n ra := extCall (e.resize fns.resize (c, s, k, n, ra))
  remap c s k n ra := extCall (e.remap fns.remap (c, s, k, n, ra))
  free c s k ra := extCall (e.free fns.free (c, s, k, ra))

/-- The vtable `fns` selects the entries of `impl` in the program's tables. -/
structure Selects (t : AllocTables Tgt) (fns : VTableFns) (impl : CVTable Tgt) : Prop where
  alloc : t.alloc.Sel fns.alloc fun a => impl.alloc a.1 a.2.1 a.2.2.1 a.2.2.2
  resize : t.resize.Sel fns.resize fun a => impl.resize a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2
  remap : t.remap.Sel fns.remap fun a => impl.remap a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2
  free : t.free.Sel fns.free fun a => impl.free a.1 a.2.1 a.2.2.1 a.2.2.2

/-- No entry of the vtable `fns` is a function of the program: every call through it reaches the
environment. -/
structure AllocTables.Fresh (t : AllocTables Tgt) (fns : VTableFns) : Prop where
  alloc : t.alloc.Fresh fns.alloc
  resize : t.resize.Fresh fns.resize
  remap : t.remap.Fresh fns.remap
  free : t.free.Fresh fns.free

/-- A program without allocator functions: every vtable is fresh. -/
theorem AllocTables.fresh_nil (e : AllocEnv Tgt) (fns : VTableFns) :
    AllocTables.Fresh { alloc := [], resize := [], remap := [], free := [], env := e } fns :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The dispatch through a vtable of the program is the implementation it selects**, whatever
the environment. -/
theorem CVTable.dispatch_of_selects {t : AllocTables Tgt} {fns : VTableFns} {impl : CVTable Tgt}
    (hs : Selects t fns impl) : CVTable.dispatch t fns = impl := by
  obtain ⟨a, r, m, f⟩ := impl
  simp only [CVTable.dispatch, Table.callOr_of_sel hs.alloc, Table.callOr_of_sel hs.resize,
    Table.callOr_of_sel hs.remap, Table.callOr_of_sel hs.free]

/-- **The dispatch through a fresh vtable is the environment's allocator.** -/
theorem CVTable.dispatch_of_fresh {t : AllocTables Tgt} {fns : VTableFns} (hf : t.Fresh fns) :
    CVTable.dispatch t fns = CVTable.env t.env fns := by
  simp only [CVTable.dispatch, CVTable.env, Table.callOr_of_fresh hf.alloc,
    Table.callOr_of_fresh hf.resize, Table.callOr_of_fresh hf.remap, Table.callOr_of_fresh hf.free]

/-- **The dispatch through a vtable meets the specification of the implementation it selects.** -/
theorem CAllocSpec.dispatch {t : AllocTables Tgt} {fns : VTableFns} {impl : CVTable Tgt}
    {ctx : Ptr} {I : FAllocInv} (hs : Selects t fns impl) (h : CAllocSpec impl ctx I) :
    CAllocSpec (CVTable.dispatch t fns) ctx I := by
  rwa [CVTable.dispatch_of_selects hs]

/-- **The dispatch through a fresh vtable meets the environment's contract** (premise EXT-05: the
environment's allocator at `fns` meets `CAllocSpec`). -/
theorem CAllocSpec.dispatch_env {t : AllocTables Tgt} {fns : VTableFns} {ctx : Ptr}
    {I : FAllocInv} (hf : t.Fresh fns) (h : CAllocSpec (CVTable.env t.env fns) ctx I) :
    CAllocSpec (CVTable.dispatch t fns) ctx I := by
  rwa [CVTable.dispatch_of_fresh hf]

/-- **The dispatch through a vtable of the program does not depend on the environment**: no
assumption about the environment says anything about it (`tests/roadmap/interfaces`). -/
theorem CVTable.dispatch_closure_env {t : AllocTables Tgt} {fns : VTableFns} {impl : CVTable Tgt}
    (hs : Selects t fns impl) (e : AllocEnv Tgt) :
    CVTable.dispatch { t with env := e } fns = CVTable.dispatch t fns := by
  rw [CVTable.dispatch_of_selects hs,
    CVTable.dispatch_of_selects (t := { t with env := e }) ⟨hs.alloc, hs.resize, hs.remap, hs.free⟩]

/-- The four entries of a `std.mem.Allocator.VTable` in field order, for `vtR`/`vtOwn`. -/
def _root_.Zig.VTableFns.toList (fns : VTableFns) : List Ptr := [fns.alloc, fns.resize, fns.remap, fns.free]

/-! ## `std.Random`

The second instance of the mechanism: `std.Random` is a context pointer and `fillFn :
*const fn (*anyopaque, []u8) void`. Its calls go through a `Table` of the program's fill
functions with the environment `EnvFn Tgt (Ptr × Slice) Unit` (the generated `Ext.call<i>` of the
`fillFn` type); a client assumes the contract `∀ A S K bs, FnSpec (randomFillPre ctx R A S K bs)
(randomFillPost R A S K) fill` of the function `fill` that the call runs (`Table.contract_of_sel`
for a generator of the program, `Table.contract_of_fresh` for the environment's, premise
EXT-05). -/

/-- The precondition of `std.Random`'s `fillFn` with the context `ctx` and the generator's own
resources `R` (its state), at the call's arguments `a`: the bytes `bs` of the slice `a.2`, of
any block but a constant global's (which no fill can write). `A S K bs` are logical variables. -/
def randomFillPre (ctx : Ptr) (R : FAssn) (A S : Nat) (K : BlockKind) (bs : Array Byte)
    (a : Ptr × Slice) : FAssn :=
  ⟪a.1 = ctx ∧ K ≠ .constGlobal ∧ bs.size = a.2.len.toNat⟫ ⋆ (R ⋆ up (bytesAt a.2.ptr A S K bs))

/-- The postcondition of `fillFn`: it keeps `R` and fills the slice with integer bytes, touching
nothing else. -/
def randomFillPost (R : FAssn) (A S : Nat) (K : BlockKind) (a : Ptr × Slice) (_ : Unit) : FAssn :=
  R ⋆ FAssn.ex fun vs : Array (BitVec 8) =>
    ⟪vs.size = a.2.len.toNat⟫ ⋆ up (bytesAt a.2.ptr A S K (vs.map Byte.int))

/-- The fill step of `std.Random`'s contract (an `fsym` rule: `fsym [FnSpec.randomFill h]`). -/
theorem FnSpec.randomFill {fill : Ptr × Slice → ConcM Tgt Unit} {ctx : Ptr} {R : FAssn}
    (h : ∀ A S K bs, FnSpec (randomFillPre ctx R A S K bs) (randomFillPost R A S K) fill)
    (s : Slice) (A S : Nat) (K : BlockKind) (bs : Array Byte)
    (hK : K ≠ .constGlobal) (hn : bs.size = s.len.toNat) :
    CTriple (R ⋆ up (bytesAt s.ptr A S K bs)) (fill (ctx, s))
      (fun _ => R ⋆ FAssn.ex fun vs : Array (BitVec 8) =>
        ⟪vs.size = s.len.toNat⟫ ⋆ up (bytesAt s.ptr A S K (vs.map Byte.int))) :=
  ((h A S K bs).call (ctx, s)).pre fun _ hr => sep_lift.2 ⟨⟨rfl, hK, hn⟩, hr⟩

end Full
end Zig
