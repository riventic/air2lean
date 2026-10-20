import ZigLean.Sep.Full.AutoWP
import ZigLean.Sep.Full.ThreadCall
import ZigLean.Sep.Full.Local
import ZigLean.Sep.Full.ThreadFacts

/-!
# `fsym` on a thread's run in a protocol (`Proto.WP`, the `WP` backend)

A run of thread `t` of any protocol `P`, from a context where `t` owns its part (`FOwned`):
`MemM` segments walked by the thread backend with their posts inferred (each segment's
precondition is the context's assertion about the part, the next one's is the previous post),
the final post from the segments' facts. A call of a concurrent function known only by its
contract (`CTriple`) is the caller's rule `WP.call_fowned` (`Full/ThreadCall.lean`). `main`'s
start: its own stack block, the protocol's start at its spawn (backwards or forwards) and the
spawn's facts from the fork's run.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

namespace SepAuto.WP

attribute [local irreducible] Proto.WP

/-- **Two segments**: a store, then a load of the word the thread owns; the load reads the
store's value (the first segment's inferred post is the second's precondition). -/
theorem two_segments {Tgt γ : Type} (P : Proto Tgt γ) (hpart : P.Partial) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res) (q : Ptr)
    (v : BitVec 32) (ho : FOwned own rO m) (hc : m.current = t) (htl : t < m.threads.size)
    (hp : up (pts q 4 v) (own t)) :
    P.WP t (ConcM.liftMem (store (α := BitVec 32) 4 q 7) >>= fun _ =>
        ConcM.liftMem (load (BitVec 32) 4 q))
      (fun w _ _ _ => w = 7) G m n := by
  fsym

/-- **Steps of a concurrent body** (`callMC`, `callRC`: one rule form, `ConcM.liftMem`): a field
pointer whose run the caller's lemma gives (`WP.liftMem_pure`), then a pure step
(`WP.liftMem_liftR`). -/
theorem body_steps {Tgt γ : Type} (P : Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (p : Ptr)
    (hproj : (ptrProject p (·.add 8)).run m = pure (p.add 8, m)) :
    P.WP t (((do
        let q ← callMC (ptrProject p (·.add 8))
        let k ← callRC (Zig.add false (1 : BitVec 32) 2)
        pure (q, k)) : CM Tgt Unit (Ptr × BitVec 32)).run ())
      (fun r _ m' _ => r.1.1 = p.add 8 ∧ m' = m) G m n := by
  fsym [WP.liftMem_pure hproj rfl]

/-- **Checked arithmetic on a symbolic word** (`WP.liftMem_add`, `WP.liftMem_sub`): the bound
from the context, the value as a fact (no overflow branch, also in strict mode). -/
theorem checked_steps {Tgt γ : Type} (P : Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (a : BitVec 32) (ha : a.toNat < 10) :
    P.WP t (ConcM.liftMem (StateT.lift (Zig.add false a 1)) >>= fun b =>
        ConcM.liftMem (StateT.lift (Zig.sub false b 1)))
      (fun r _ _ _ => r.toNat = a.toNat) G m n := by
  fsym

/-- **Branches of a run** (`if` between segments): each branch's segments, the post a disjunction
proved by one of its sides. -/
theorem branch_runs {Tgt γ : Type} (P : Proto Tgt γ) (hpart : P.Partial) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res) (q : Ptr)
    (v : BitVec 32) (b : Bool) (ho : FOwned own rO m) (hc : m.current = t)
    (htl : t < m.threads.size) (hp : up (pts q 4 v) (own t)) :
    P.WP t (ConcM.liftMem (if b then store (α := BitVec 32) 4 q 7 else pure ()) >>= fun _ =>
        ConcM.liftMem (load (BitVec 32) 4 q))
      (fun w _ _ _ => w = 7 ∨ w = v) G m n := by
  fsym

/-- A function of the thread whose branches end in different states. -/
def setIfZero (q : Ptr) : MemM Unit := do
  let w ← load (BitVec 32) 4 q
  if w = 0 then store (α := BitVec 32) 4 q 7 else pure ()

/-- **A segment whose branches end in different states** (`joinPosts`): its post is the join of
the branches' (`∃ b, if b then … else …`); the next segment starts from each. -/
theorem branch_states {Tgt γ : Type} (P : Proto Tgt γ) (hpart : P.Partial) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res) (q : Ptr)
    (v : BitVec 32) (ho : FOwned own rO m) (hc : m.current = t) (htl : t < m.threads.size)
    (hp : up (pts q 4 v) (own t)) :
    P.WP t (ConcM.liftMem (setIfZero q) >>= fun _ => ConcM.liftMem (load (BitVec 32) 4 q))
      (fun w _ _ _ => w = 7 ∨ w ≠ 0) G m n := by
  fsym

/-- **A call of a concurrent function by its contract** (`WP.call_fowned`): a function `f` known
only by a `CTriple` on the thread's part, called by thread `t` of every protocol whose invariant
keeps the parts (`hinv`) and is local to them (`hloc`) and that counts no turns. The contract is
the caller's rule; the call's precondition is the context's assertion about the part. -/
theorem call_contract {Tgt γ : Type} (P : Proto Tgt γ) (t : ThreadId)
    (res : γ → Res) (set : γ → Res → γ) (hres : ∀ g r, res (set g r) = r) (hcost : P.cost = none)
    (hinv : ∀ G m, P.inv G m → t < m.threads.size ∧ ∃ rO, FOwned (fun u => res (G u)) rO m)
    (hloc : ∀ G m m' rO rR r', P.inv G m →
      sepN m.threads.size (partsBut (fun u => res (G u)) t) rR →
      FOwned (upd (fun u => res (G u)) t r') rO m' →
      FStepIn (FHeap.erase (rR.heap ∪ rO.heap)) { m with current := t } m' →
      P.inv (upd G t (set (G t) r')) m')
    (q : Ptr) (f : ConcM Tgt Unit)
    (hf : CTriple (up (pts q 4 (0 : BitVec 32))) f (fun _ => up (pts q 4 (1 : BitVec 32))))
    (G : ThreadId → γ) (m : Mem) (n : Nat) (hi : P.inv G m) (hc : m.current = t)
    (hp : up (pts q 4 (0 : BitVec 32)) (res (G t))) :
    P.WP t f (fun _ _ m' _ => m'.current = t) G m n := by
  fsym [WP.call_fowned (Q := fun _ _ m' _ => m'.current = t) hf hcost hres hinv hloc
    (fun _ _ _ _ _ _ _ _ _ _ _ hs _ => hs.current)]

/-- **A thread's own stack block and its fields** (`main` before its spawn): the allocation in the
plain mode (`FTriple.allocStackDrop`), then field pointers (`ptrProject`, the block's size from
its extent: `Reaches.bauth`) and stores at byte offsets of the block's bytes (`storeBytesAt`, the
offsets as generated code writes them; the closed sizes of the bytes written evaluated). Each
command is a segment of the thread's part (`WP.liftMem_fowned`), the next one's precondition the
previous one's inferred post. -/
theorem block_fields {Tgt γ : Type} (P : Proto Tgt γ) (hpart : P.Partial) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res)
    (ho : FOwned own rO m) (hc : m.current = t) (htl : t < m.threads.size) (hp : plain (own t)) :
    P.WP t (ConcM.liftMem (allocStack 16 8) >>= fun p =>
        ConcM.liftMem (store 8 p (⟨⟩ : Io)) >>= fun _ =>
        ConcM.liftMem (ptrProject p (·.add 8)) >>= fun q =>
        ConcM.liftMem (store (α := BitVec 32) 4 q 5) >>= fun _ =>
        ConcM.liftMem (ptrProject p (·.add 12)) >>= fun q' =>
        ConcM.liftMem (store (α := BitVec 32) 4 q' 6))
      (fun _ _ m' _ => m'.current = t) G m n := by
  fsym [FTriple.allocStackDrop]

/-- **The facts of the steps' runs** (`@[fsym_run]`, `wpRunFacts`): the new block's pointer and
count, and the protocol fields the allocation, a field pointer and the stores keep. The initial
fields are arbitrary, so this also covers nonempty queues and groups. -/
theorem run_facts {Tgt γ : Type} (P : Proto Tgt γ) (hpart : P.Partial) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res)
    (ho : FOwned own rO m) (hc : m.current = t) (htl : t < m.threads.size) (hp : plain (own t)) :
    P.WP t (ConcM.liftMem (allocStack 16 8) >>= fun p =>
        ConcM.liftMem (store 8 p (⟨⟩ : Io)) >>= fun _ =>
        ConcM.liftMem (ptrProject p (·.add 8)) >>= fun q =>
        ConcM.liftMem (store (α := BitVec 32) 4 q 5) >>= fun _ => pure p)
      (fun p _ m' _ => p = ⟨some m.blocks.size, 0⟩ ∧ m'.atomics = m.atomics ∧
        m'.waiters = m.waiters ∧ m'.current = m.current ∧ m'.threads = m.threads ∧
        m'.woken = m.woken ∧ m'.groups = m.groups ∧ m'.clocks.size = m.clocks.size ∧
        m'.blocks.size = m.blocks.size + 1) G m n := by
  fsym [FTriple.allocStackDrop]

/-- Two allocations separated by stores: the next pointer uses the first allocation's count,
which the stores keep. The field pointers use the owned block's authority, without a separate
memory-description rule. Only the final allocation consumes the plain mode. -/
theorem two_blocks {Tgt γ : Type} (P : Proto Tgt γ) (hpart : P.Partial) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res)
    (ho : FOwned own rO m) (hc : m.current = t) (htl : t < m.threads.size) (hp : plain (own t)) :
    P.WP t (ConcM.liftMem (allocStack 24 8) >>= fun p =>
        ConcM.liftMem (store (α := BitVec 64) 8 p 1) >>= fun _ =>
        ConcM.liftMem (ptrProject p (·.add 16)) >>= fun p16 =>
        ConcM.liftMem (store (α := BitVec 32) 4 p16 2) >>= fun _ =>
        ConcM.liftMem (ptrProject p (·.add 20)) >>= fun p20 =>
        ConcM.liftMem (store (α := BitVec 32) 4 p20 3) >>= fun _ =>
        ConcM.liftMem (allocStack 16 8) >>= fun q =>
        ConcM.liftMem (store (α := BitVec 32) 4 q 4) >>= fun _ => pure (p, q))
      (fun r _ m' _ => r.1 = ⟨some m.blocks.size, 0⟩ ∧
        r.2 = ⟨some (m.blocks.size + 1), 0⟩ ∧ m'.blocks.size = m.blocks.size + 2 ∧
        m'.atomics = m.atomics ∧ m'.waiters = m.waiters ∧ m'.current = m.current ∧
        m'.threads = m.threads ∧ m'.woken = m.woken ∧ m'.groups = m.groups ∧
        m'.clocks.size = m.clocks.size) G m n := by
  fsym [FTriple.allocStackDrop 16 8]

/-- A loop body that returns the two pointers it was given. -/
def pointerBody {Tgt : Type} (p q : Ptr) : CM Tgt Unit (Ptr × Ptr) := pure (p, q)

/-- The loop rule infers its body from the current command. The walk proves the body's step
from the allocation-count facts and the groups preserved by the initial memory steps. -/
theorem two_blocks_loop {Tgt γ : Type} (P : Proto Tgt γ) (hpart : P.Partial) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res)
    (ho : FOwned own rO m) (hc : m.current = t) (htl : t < m.threads.size) (hp : plain (own t)) :
    P.WP t (ConcM.liftMem (allocStack 24 8) >>= fun p =>
        ConcM.liftMem (store (α := BitVec 64) 8 p 1) >>= fun _ =>
        ConcM.liftMem (allocStack 16 8) >>= fun q =>
        (loop (pointerBody p q) (fun _ => false)).run ())
      (fun r _ m' _ => r.1 = (⟨some m.blocks.size, 0⟩, ⟨some (m.blocks.size + 1), 0⟩) ∧
        m'.groups = m.groups) G m n := by
  fsym [FTriple.allocStackDrop 16 8,
    WP.loop (P := P) (t := t) (σ := Unit) (ε := Ptr × Ptr) _
      (fun _ => false) (fun _ _ m' _ => m'.groups = m.groups) (fun _ => 0)
      (fun r _ m' _ => r.1 = (⟨some m.blocks.size, 0⟩, ⟨some (m.blocks.size + 1), 0⟩) ∧
        m'.groups = m.groups)]

/-- **A thread's bound by the arithmetic** (`numAliases`): `t < m.threads.size` of a
`t : ThreadId` (the segment rule's side goal) from a fact about `t + 1`; `omega` reads an order
only at `Nat` itself. -/
theorem thread_bound {Tgt γ : Type} (P : Proto Tgt γ) (hpart : P.Partial) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res) (q : Ptr)
    (v : BitVec 32) (ho : FOwned own rO m) (hc : m.current = t)
    (ht : t + 1 < m.threads.size) (hp : up (pts q 4 v) (own t)) :
    P.WP t (ConcM.liftMem (store (α := BitVec 32) 4 q 7)) (fun _ _ _ _ => True) G m n := by
  fsym

/-- A spawned thread's ghost value. -/
def gKid : Nat × Bool := (1, false)

/-- **A hypothesis of the same predicate up to unfolding** (`wpAssumptionArgs`): the post's
ghost value `gKid` and the hypothesis's `(1, false)` (a value a protocol's `init` fixed), each
argument compared on its own, the predicate not unfolded. -/
theorem same_pred {Tgt : Type} (P : Proto Tgt (Nat × Bool)) (t : ThreadId)
    (G : ThreadId → Nat × Bool) (m : Mem) (n : Nat) (hi : P.inv (upd G 1 (1, false)) m) :
    P.WP t (pure ()) (fun _ G' m' _ => P.inv (upd G' 1 gKid) m') G m n := by
  fsym

/-- **A Boolean fact selects a case** (`fieldEqs`): the flag `f (G 1)` of the post's `if` (a
ghost value's flag) is `false` by a hypothesis. -/
theorem bool_case {Tgt γ : Type} (P : Proto Tgt γ) (t : ThreadId) (G : ThreadId → γ) (m : Mem)
    (n : Nat) (f : γ → Bool) (R S : Prop) (hb : f (G 1) = false) (hR : R) :
    P.WP t (pure ()) (fun _ G' _ _ => if f (G' 1) = true then S else R) G m n := by
  fsym

/-- An even number. -/
def Even2 (v : Nat) : Prop := v % 2 = 0

/-- **A conjunction's first part with an unknown that its second part fixes** (`wpGoal`): the
first part again once the second one took the hypothesis's value. -/
theorem and_retry {Tgt γ : Type} (P : Proto Tgt γ) (t : ThreadId) (G : ThreadId → γ) (m : Mem)
    (n : Nat) (R : Nat → Prop) (hR : R 2) :
    P.WP t (pure ()) (fun _ _ _ _ => ∃ v, Even2 v ∧ R v) G m n := by
  fsym

/-! ### A protocol's start at `main`'s spawn

A program's start as generated code and a client's protocol name it: the start memory `mem0`,
the threads' ghost values `G0`, `main`'s ghost value before the spawn `gPre` and a spawned
thread's `gKid` (above). The protocol's invariant needs `main`'s ghost value, which the walk does
not know: the protocol's start gives it, backwards (a client's `inv_start`) or forwards
(`inv_of_box`). -/

/-- The start memory of a program with no globals. -/
def mem0 (σ : Placement) : Mem := Mem.ofGlobals σ []

/-- The threads' start ghost values. -/
def G0 : ThreadId → Nat × Bool := fun _ => (0, false)

/-- `main`'s ghost value before its spawn. -/
def gPre : Nat × Bool := (1, true)

/-- `main` alone with a ghost value of a positive count; a spawned thread starts at `gKid` (the
`init` a field of a structure value). -/
def startProto : Proto Unit (Nat × Bool) :=
  { inv := fun G m => m.threads.size = 1 ∧ 0 < (G 0).1, init := fun _ g => g = gKid,
    fin := fun _ => True }

/-- The protocol's start from what `main` owns (a client's `inv_start`: the thread's part, its
block's bytes and extent, the start facts). -/
theorem start_inv {m : Mem} {r : Res} {A : Nat} {bs : Array Byte}
    (_ho : FOwned (upd (fun _ => rnil) 0 r) rnil m)
    (_hF : (up (bytesAt ⟨some 0, 0⟩ A 8 .stack bs) ⋆ bext 0 8 .stack) r) (_hs : bs.size = 8)
    (_hb : bs.extract 0 4 = Enc.encode (5 : BitVec 32))
    (hth : m.threads = #[{ spawner := 0, joined := true }]) (_hat : m.atomics = #[])
    (_hq : m.waiters = #[]) :
    startProto.inv (upd G0 0 gPre) m := by
  show m.threads.size = 1 ∧ 0 < (upd G0 0 gPre 0).1
  rw [upd_self, hth]
  exact ⟨rfl, by decide⟩

/-- `start_inv` with `main`'s ghost value a witness (a client's `inv_of_box`: the part `main`
keeps). -/
theorem start_ex {m : Mem} {r : Res} {A : Nat} {bs : Array Byte}
    (_ho : FOwned (upd (fun _ => rnil) 0 r) rnil m)
    (_hF : (up (bytesAt ⟨some 0, 0⟩ A 8 .stack bs) ⋆ bext 0 8 .stack) r) (_hs : bs.size = 8)
    (hth : m.threads = #[{ spawner := 0, joined := true }]) (_hat : m.atomics = #[]) :
    ∃ k : Nat, 0 < k ∧ startProto.inv (upd G0 0 (k, true)) m := by
  refine ⟨1, Nat.one_pos, ?_⟩
  show m.threads.size = 1 ∧ 0 < (upd G0 0 (1, true) 0).1
  rw [upd_self, hth]
  exact ⟨rfl, Nat.one_pos⟩

/-- The protocol's spawn (a client's `inv_spawn`): the child and the threads after the fork,
from the fork's run. -/
theorem spawn_threads {G : ThreadId → Nat × Bool} {m m' : Mem} {c : ThreadId}
    (hi : startProto.inv G m)
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (c, m'))) :
    c = 1 ∧ m'.current = 0 ∧ m'.threads.size = 2 := by
  rw [fork_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  have h1 : m.threads.size = 1 := hi.1
  exact ⟨h1, rfl, by simp [h1]⟩

/-- **The protocol's start backwards** at `main`'s spawn, from the start facts
(`FOwned.start0_facts`), after the thread's own stack block and its store: `start_inv` proves the
spawn's invariant; its premise about the thread's part has unknowns (`assnByHyp`), and the facts
of the steps' runs give the block's pointer, no atomic location and no waiter (`@[fsym_run]`).
The child's ghost value is the protocol's `init`'s (a field of a structure value: its equation
fixes the unknown); the spawn's facts are the caller's run lemma's (`spawn_threads`). -/
theorem main_start (σ : Placement) (n : Nat) :
    startProto.WP 0 (ConcM.liftMem (allocStack 8 4) >>= fun p =>
        ConcM.liftMem (store (α := BitVec 32) 4 p 5) >>= fun _ =>
        (spawnC () : CM Unit Unit (Except ErrName ThreadId)).run ())
      (fun r _ m' _ => r.1 = .ok 1 ∧ m'.current = 0 ∧ m'.threads.size = 2) G0
      { mem0 σ with current := 0 } n := by
  have := FOwned.start0_facts (σ := σ) (m := mem0 σ) rfl
  fsym [FTriple.allocStackDrop, start_inv, spawn_threads]

/-- **The protocol's start forwards** (`wpForwardEx`): `start_ex`, whose conclusion is an `∃`,
on the thread's part after its store, before the spawn; its witness (`main`'s ghost value) is a
local that the spawn's ghost value takes. -/
theorem main_start_ex (σ : Placement) (n : Nat) :
    startProto.WP 0 (ConcM.liftMem (allocStack 8 4) >>= fun p =>
        ConcM.liftMem (store (α := BitVec 32) 4 p 5) >>= fun _ =>
        (spawnC () : CM Unit Unit (Except ErrName ThreadId)).run ())
      (fun r _ m' _ => r.1 = .ok 1 ∧ m'.current = 0 ∧ m'.threads.size = 2) G0
      { mem0 σ with current := 0 } n := by
  have := FOwned.start0_facts (σ := σ) (m := mem0 σ) rfl
  fsym [FTriple.allocStackDrop, start_ex, spawn_threads]

end SepAuto.WP

namespace SepAuto.WP

open Lean Meta Elab Tactic Zig.Full.Auto

/-- An unrelated polymorphic definition unfolds by name without instantiating its class. -/
theorem global_definition_hint :
    FTotalTriple emp (pure (7 : Nat) : MemM Nat) (fun _ => emp) := by
  fsym [Functor.discard]

/-- A definition hint supplies no proof of an opaque postcondition. -/
theorem global_definition_missing_fact (R : Prop) : True := by
  fail_if_success
    have : FTotalTriple emp (pure (7 : Nat) : MemM Nat) (fun _ => ⟪R⟫) := by
      fsym [Functor.discard]
  trivial

/-- A wrapper keeps an unknown inner head as a wildcard; concrete mismatches still prune
before unfolding, including when the inner commands or assertions contain metavariables. -/
def wrapper_keys : MetaM Unit := do
  let a ← mkFreshExprMVar (mkApp (mkConst ``BitVec) (mkNatLit 32))
  let add ← mkAppM ``Zig.add #[mkConst ``Bool.false, a, a, mkConst ``Bool.true]
  let actual ← mkAppOptM ``StateT.lift #[some (mkConst ``Mem), none, none, none, some add]
  let x ← mkFreshExprMVar (← inferType add)
  let pattern ← mkAppOptM ``StateT.lift #[some (mkConst ``Mem), none, none, none, some x]
  unless headKey pattern == .anonymous && headKey actual == `lift ++ ``Zig.add do
    throwError "wrapper_keys: StateT.lift lost its wildcard or concrete head"
  unless ← unifyKeyed pattern actual do
    throwError "wrapper_keys: StateT.lift wildcard did not unify"
  unless ← x.mvarId!.isAssigned do
    throwError "wrapper_keys: StateT.lift left its inner command unassigned"
  unless ← isDefEq x add do
    throwError "wrapper_keys: StateT.lift did not determine the inner command"
  let sub ← mkAppM ``Zig.sub #[mkConst ``Bool.false, a, a, mkConst ``Bool.true]
  let other ← mkAppOptM ``StateT.lift #[some (mkConst ``Mem), none, none, none, some sub]
  if ← unifyKeyed actual other then
    throwError "wrapper_keys: StateT.lift unfolded different concrete heads"
  let emp := mkConst ``Zig.Assn.emp
  let actual ← mkAppM ``FAssn.up #[emp]
  let x ← mkFreshExprMVar (← inferType emp)
  let pattern ← mkAppM ``FAssn.up #[x]
  unless headKey pattern == .anonymous && headKey actual == `lift ++ ``Zig.Assn.emp do
    throwError "wrapper_keys: up lost its wildcard or concrete head"
  unless ← unifyAtom pattern actual do
    throwError "wrapper_keys: up wildcard did not unify"
  unless ← x.mvarId!.isAssigned do
    throwError "wrapper_keys: up left its inner assertion unassigned"
  unless ← isDefEq x emp do
    throwError "wrapper_keys: up did not determine the inner assertion"
  let prop ← mkFreshExprMVar (mkSort .zero)
  let lifted ← mkAppM ``Zig.Assn.lift #[prop]
  let other ← mkAppM ``FAssn.up #[lifted]
  if ← unifyKeyed actual other then
    throwError "wrapper_keys: up unfolded different concrete heads"

run_meta wrapper_keys

/-- Generic memory/result rules remain behind specific caller and registered commands. -/
theorem generic_rule_priority : True := by
  run_tac withRunCaches do
    let memory ← mkConstWithFreshMVarLevels ``WP.liftMem_fownedT
    let result ← mkConstWithFreshMVarLevels ``WP.liftMem_liftR
    let add ← mkConstWithFreshMVarLevels ``WP.liftMem_add
    let sub ← mkConstWithFreshMVarLevels ``WP.liftMem_sub
    unless (← wpGenericRule memory) && (← wpGenericRule result) do
      throwError "generic_rule_priority: a wildcard rule was classified as concrete"
    if (← wpGenericRule add) || (← wpGenericRule sub) then
      throwError "generic_rule_priority: a concrete rule was classified as generic"
    let (_, _, concl) ← forallMetaTelescope (← inferType add)
    let some args := wpArgs? concl | throwError "generic_rule_priority: not a WP rule"
    let ordered ← rules #[result, add] args[5]! (wp := true)
    unless ordered[0]? == some add && ordered.back? == some result do
      throwError "generic_rule_priority: a supplied wildcard preceded a concrete rule"
  trivial

/-- A pure forward fact can substitute its result, renaming the dependent premise. -/
theorem forward_to_one {r : BitVec 32} (hr : r.toNat = 1) : r = 1 :=
  BitVec.eq_of_toNat_eq hr

/-- Re-read the current premise after forwarding; its old free variable was replaced. -/
theorem forward_substitution {Tgt γ : Type} (P : Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) :
    P.WP t (pure ()) (fun _ _ _ _ => ∀ r : BitVec 32, r.toNat = 1 → r = 1) G m n := by
  fsym [forward_to_one]

/-- Normalize an incoming fact with an earlier opaque Boolean equation before splitting. -/
theorem incoming_boolean_fact {Tgt γ : Type} (P : Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (flag : Nat → Bool) (k : Nat)
    (hf : flag k = false) (R : Prop) :
    P.WP t (pure ()) (fun _ _ _ _ => (flag k = true ∨ R) → R) G m n := by
  fsym

/-- A newly introduced equation stays available instead of simplifying itself to True. -/
theorem incoming_boolean_equation {Tgt γ : Type} (P : Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (flag : Nat → Bool) (k : Nat) :
    P.WP t (pure ()) (fun _ _ _ _ => flag k = true → flag k = true) G m n := by
  fsym

/-- Without the earlier equation the opaque Boolean branch must not be discarded. -/
theorem incoming_boolean_missing {Tgt γ : Type} (P : Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (flag : Nat → Bool) (k : Nat) (R : Prop) : True := by
  fail_if_success
    have : P.WP t (pure ()) (fun _ _ _ _ => (flag k = true ∨ R) → R) G m n := by
      fsym
  trivial

/-- A bare projection equation in the context is not a projection applied to an object. -/
theorem incoming_projection_function {Tgt γ : Type} (P : Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (hp : Mem.current = Mem.current) :
    P.WP t (pure ()) (fun _ _ _ _ => True → True) G m n := by
  fsym

/-- A global forward lemma may retain the unnormalized form of its first premise. -/
theorem incoming_raw_or_bound (flag : Nat → Bool) (k j : Nat)
    (h : flag k = true ∨ Nonempty (Fin (1 - j))) (hf : flag k = false) : j - 1 = 0 := by
  cases h with
  | inl ht =>
    rw [hf] at ht
    cases ht
  | inr hn =>
    cases hn with
    | intro i =>
      have hi := i.isLt
      omega

/-- Forwarding sees the raw premise before context normalization, fixing its remaining index. -/
theorem incoming_forward_compatibility {Tgt γ : Type} (P : Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (flag : Nat → Bool) (k j : Nat)
    (hf : flag k = false) :
    P.WP t (pure ())
      (fun _ _ _ _ => (flag k = true ∨ Nonempty (Fin (1 - j))) → j - 1 = 0) G m n := by
  fsym [incoming_raw_or_bound flag k]

/-- Inspect the simplifier result and require that the existing normalization API closes
the goal when a closed bit-vector comparison makes an incoming fact impossible. -/
theorem incoming_false_result (R : Prop) (flag : Bool)
    (h : (1 : BitVec 32) = 0 ∨ false = true ∧ flag = true) : R := by
  run_tac withRunCaches do
    let g ← getMainGoal
    let h := (← getLocalDeclFromUserName `h).fvarId
    let ty ← instantiateMVars (← h.getType)
    let (r, _) ← simp ty (← wpHypCtx #[]) (simprocs := #[← Simp.getSimprocs])
    unless r.expr.isFalse do
      throwError "incoming_false_result: the incoming fact did not simplify to False"
    if (← wpNorm g h #[]).isSome then
      throwError "incoming_false_result: False was retained as an open hypothesis"
    unless ← g.isAssigned do
      throwError "incoming_false_result: the goal was not closed"
    replaceMainGoal []

/-- An already-False premise follows the same closed-goal result, including the no-rewrite path. -/
theorem incoming_false_unchanged (R : Prop) (h : False) : R := by
  run_tac withRunCaches do
    let g ← getMainGoal
    let h := (← getLocalDeclFromUserName `h).fvarId
    if (← wpNorm g h #[]).isSome then
      throwError "incoming_false_unchanged: False was retained as an open hypothesis"
    unless ← g.isAssigned do
      throwError "incoming_false_unchanged: the goal was not closed"
    replaceMainGoal []

/-- An opaque Boolean premise cannot close an unrelated opaque proposition; it also cannot
rewrite itself to True through the context-equation set. -/
theorem incoming_unknown_stays (R : Prop) (flag : Bool) (h : flag = true) : True := by
  run_tac withRunCaches do
    let g ← mkFreshExprSyntheticOpaqueMVar (← getLocalDeclFromUserName `R).toExpr
    let h := (← getLocalDeclFromUserName `h).fvarId
    let some (h', g') ← wpNorm g.mvarId! h #[] (fields := true)
      | throwError "incoming_unknown_stays: an unknown Boolean closed the goal"
    if ← g'.isAssigned then
      throwError "incoming_unknown_stays: an unknown Boolean assigned the goal"
    unless (← instantiateMVars (← h'.getType)) == (← h.getType) do
      throwError "incoming_unknown_stays: the premise erased its own equation"
  trivial

/-- A closed nonzero unsigned divisor needs no caller-provided nonzero fact. This is the
same pure-result rule as the symbolic all-width control and the actual translated client. -/
theorem division_unsigned_literal {Tgt γ : Type} (P : Proto Tgt γ) (hpart : P.Partial)
    (t : ThreadId) (G : ThreadId → γ) (m : Mem) (n : Nat) (a : BitVec 32) :
    P.WP t (ConcM.liftMem (StateT.lift (Zig.divTrunc false a 1)))
      (fun r _ _ _ => r = a.udiv 1) G m n := by
  fsym

/-- The generic pure-result rule learns the quotient from a symbolic unsigned run. -/
theorem division_unsigned {Tgt γ : Type} (P : Proto Tgt γ) (hpart : P.Partial)
    (t : ThreadId) (G : ThreadId → γ) (m : Mem) (n : Nat)
    {w : Nat} (a b : BitVec w) (hb : b ≠ 0) :
    P.WP t (ConcM.liftMem (StateT.lift (Zig.divTrunc false a b)))
      (fun r _ _ _ => r = a.udiv b) G m n := by
  fsym

/-- Signed division uses the existing overflow predicate, with no width restriction. -/
theorem division_signed {Tgt γ : Type} (P : Proto Tgt γ) (hpart : P.Partial)
    (t : ThreadId) (G : ThreadId → γ) (m : Mem) (n : Nat)
    {w : Nat} (a b : BitVec w) (hb : b ≠ 0) (ho : a.sdivOverflow b = false) :
    P.WP t (ConcM.liftMem (StateT.lift (Zig.divTrunc true a b)))
      (fun r _ _ _ => r = a.sdiv b) G m n := by
  fsym

/-- The negative controls retain actual illegal outcomes, independently of automation. -/
theorem division_error_outcomes :
    (Zig.divTrunc false (7 : BitVec 32) 0).run = some (.error .illegal) ∧
    (Zig.divTrunc false (0 : BitVec 0) 1).run = some (.error .illegal) ∧
    (Zig.divTrunc true (128 : BitVec 8) 255).run = some (.error .illegal) := by
  decide +kernel

theorem division_unsafe_rejected (G : ThreadId → Nat × Bool) (m : Mem) (n : Nat) : True := by
  fail_if_success
    have : ({ startProto with strict := true }).WP 0
        (ConcM.liftMem (StateT.lift (Zig.divTrunc false (7 : BitVec 32) 0)))
        (fun _ _ _ _ => True) G m n := by fsym
  fail_if_success
    have : ({ startProto with strict := true }).WP 0
        (ConcM.liftMem (StateT.lift (Zig.divTrunc false (0 : BitVec 0) 1)))
        (fun _ _ _ _ => True) G m n := by fsym
  fail_if_success
    have : ({ startProto with strict := true }).WP 0
        (ConcM.liftMem (StateT.lift (Zig.divTrunc true (128 : BitVec 8) 255)))
        (fun _ _ _ _ => True) G m n := by fsym
  trivial

end SepAuto.WP

namespace SepAuto.WP

attribute [local irreducible] Proto.WP

variable {Tgt γ α : Type} {P : Proto Tgt γ} {t : ThreadId}
  {G : ThreadId → γ} {m : Mem} {n : Nat}

/-- A current local function supplies a quantified post, after its opaque antecedent. -/
theorem local_pi_imp (R B C : Prop) (A : α → Prop)
    (_wrongHead : ∀ u, A u → C) (h : R → ∀ u, A u → B) (hr : R) :
    P.WP t (pure ()) (fun _ _ _ _ => ∀ u, A u → B) G m n := by
  fsym

theorem local_pi_true (B : Prop) (A : α → Prop) (h : True → ∀ u, A u → B) :
    P.WP t (pure ()) (fun _ _ _ _ => ∀ u, A u → B) G m n := by
  fsym

theorem local_pi (B : Prop) (A : α → Prop) (h : ∀ u, A u → B) :
    P.WP t (pure ()) (fun _ _ _ _ => ∀ u, A u → B) G m n := by
  fsym

-- The direct post must not introduce the missing opaque argument itself.
include P t G m n in
theorem local_pi_missing_arg (R B : Prop) (A : α → Prop) (u : α)
    (h : R → ∀ u, A u → B) (hr : R) : True := by
  fail_if_success
    have : P.WP t (pure ()) (fun _ _ _ _ => B) G m n := by fsym
  trivial

include P t G m n in
theorem local_pi_missing_antecedent (R B : Prop) (A : α → Prop) (u : α)
    (h : R → ∀ u, A u → B) (ha : A u) : True := by
  fail_if_success
    have : P.WP t (pure ()) (fun _ _ _ _ => B) G m n := by fsym
  trivial

include P t G m n in
theorem local_self_cycle (B : Prop) (self : B → B) : True := by
  fail_if_success
    have : P.WP t (pure ()) (fun _ _ _ _ => B) G m n := by fsym
  trivial

include P t G m n in
theorem local_mutual_cycle (A B : Prop) (ab : A → B) (ba : B → A) : True := by
  fail_if_success
    have : P.WP t (pure ()) (fun _ _ _ _ => B) G m n := by fsym
  trivial

/-- Failed cyclic candidates leave a later usable function available. -/
theorem local_cycle_then_function (A R B : Prop) (self : B → B)
    (ab : A → B) (ba : B → A) (later : R → B) (hr : R) :
    P.WP t (pure ()) (fun _ _ _ _ => B) G m n := by
  fsym

/-- Equal predicate heads do not authorize unequal conclusion arguments. -/
theorem local_indexed_args (R : Prop) (D : Nat → Prop) (i j : Nat) (hne : i ≠ j)
    (wrong : R → D j) (right : R → D i) (hr : R) :
    P.WP t (pure ()) (fun _ _ _ _ => D i) G m n := by
  fsym

/-- This is logically provable, independently of the deliberately bounded search below. -/
theorem no_cases_kernel (A C R B : Prop) (h : ((A ∨ C) → R) → B)
    (ha : A → R) (hc : C → R) : B :=
  h (fun ac => ac.elim ha hc)

-- Do not supply no_cases_kernel to fsym: a local attempt may not split its new premise.
include P t G m n in
theorem local_no_cases (A C R B : Prop) (h : ((A ∨ C) → R) → B)
    (ha : A → R) (hc : C → R) : True := by
  fail_if_success
    have : P.WP t (pure ()) (fun _ _ _ _ => B) G m n := by fsym
  trivial

/-- The arithmetic version is also provable, but needs the newly introduced case fact. -/
theorem no_arithmetic_cases_kernel (B : Prop) (x y z M c : Nat)
    (h : ((x = y ∨ x = z) → x % M = c) → B) (hzy : z = y) (hmod : y % M = c) : B :=
  h (fun hx => (congrArg (fun v => v % M) (hx.elim id (fun hxz => hxz.trans hzy))).trans hmod)

-- Keep the disjunction inside the attempted function premise, outside the ordinary splitter.
include P t G m n in
theorem local_no_arithmetic_cases (B : Prop) (x y z M c : Nat)
    (h : ((x = y ∨ x = z) → x % M = c) → B) (hzy : z = y) (hmod : y % M = c) : True := by
  fail_if_success
    have : P.WP t (pure ()) (fun _ _ _ _ => B) G m n := by fsym
  trivial

/-- A failed witness choice must not retain normalization of a hypothesis at that choice. -/
theorem local_witness_retry (B Missing : Prop) (D : Nat → Prop) (x : Nat)
    (outer : (∃ i : Nat, (if i = 0 then x = 0 else x = 1) → D i) → B)
    (bad : x + 1 = 1 → Missing → D 0) (good : x + 1 = 2 → D 1) :
    P.WP t (pure ()) (fun _ _ _ _ => B) G m n := by
  fsym

/-- The usable second witness in the rollback control has a direct kernel derivation. -/
theorem witness_retry_kernel (B Missing : Prop) (D : Nat → Prop) (x : Nat)
    (outer : (∃ i : Nat, (if i = 0 then x = 0 else x = 1) → D i) → B)
    (_bad : x + 1 = 1 → Missing → D 0) (good : x + 1 = 2 → D 1) : B := by
  apply outer
  refine ⟨1, ?_⟩
  intro hx
  have hx : x = 1 := by simpa using hx
  exact good (by omega)

end SepAuto.WP
