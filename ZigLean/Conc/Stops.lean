import ZigLean.Conc.Logic
import ZigLean.Conc.Progress
import ZigLean.Mem.Halts

/-!
# Turn budgets of a thread

A thread's run is a tree (`CoN`, `ZigLean/Conc/Basic.lean`); the scheduler gives it one turn
at each sync op. `Turns R kb Q B tree`: every path of `tree` ends with a result (never "no
result") after sync ops whose turn costs (`opCost`) sum to at most `B`, and each value at the end
satisfies `Q` with the budget and depth that are left. At a stop the thread goes on from any
memory that satisfies the rely `R` (`R` holds of every memory that a scheduler turn can resume
the thread in; `ZigLean/Conc/Returns.lean` derives it from a strict protocol's invariant).

- **Costs.** A `yield`, `choose`, `pick`, `asyncChoice`, `join` or `wake` is one turn. A
  `spawn tgt` costs one turn plus the turns of the new thread: its first turn and its budget
  `kb tgt`, so the sum over all threads never grows. `kb tgt = none`: the proof does not
  allow a spawn of `tgt`. A futex `wait`, a deferred task (`spawnGated`, `gate`) have no cost:
  a thread that reaches one has no budget (fail closed). A sleeping wait is resumed only by
  another thread, so its turns are not a property of the waiting thread alone.
- **`Stops R kb x Q m B`**: from the memory `m`, every depth `n ≥ B` of `x` keeps budget `B`,
  and every result leaves a budget `B' ≤` the depth that is left with `Q`. The rules
  (`Stops.bind`, `Stops.liftMem`, `Stops.sync`, the `CM` lifts, `Stops.loop`) follow the
  program; `stops` walks generated code with them. A module supplies the budget, the loop
  invariants and their measures.
-/

namespace Zig
namespace Conc

variable {Tgt : Type}

/-- The turns of a sync op (see the module doc). `none`: no turn budget for this op. -/
def opCost (kb : Tgt → Option Nat) : SyncOp Tgt → Option Nat
  | .spawn tgt => (kb tgt).map (· + 2)
  | .yield | .choose _ | .pick _ | .asyncChoice | .join _ | .wake .. => some 1
  | .wait .. | .gate | .spawnGated _ => none

theorem opCost_pos {kb : Tgt → Option Nat} {op : SyncOp Tgt} {c : Nat} (h : opCost kb op = some c) :
    1 ≤ c := by
  cases op <;> simp [opCost] at h <;> omega

/-- A tree whose paths end with a result within `B` turns (see the module doc). -/
def Turns (R : Mem → Prop) (kb : Tgt → Option Nat) {β : Type} (Q : β → Mem → Nat → Nat → Prop) :
    Nat → {n : Nat} → CoN Tgt (β × Mem) n → Prop
  | _, _, .leaf none => False
  | _, _, .leaf (some (.error _)) => True
  | B, n, .leaf (some (.ok (b, m))) => Q b m B n
  | B, _, .sync op _ k => ∃ c, opCost kb op = some c ∧ c ≤ B ∧
      ∀ r m', R m' → Turns R kb Q (B - c) (k r m')

namespace Turns

variable {R R' : Mem → Prop} {kb : Tgt → Option Nat} {β γ : Type}

theorem mono {Q Q' : β → Mem → Nat → Nat → Prop} (hR : ∀ m, R' m → R m)
    (hq : ∀ b m B d, Q b m B d → Q' b m B d) {B n : Nat} (x : CoN Tgt (β × Mem) n) :
    Turns R kb Q B x → Turns R' kb Q' B x := by
  induction x generalizing B with
  | leaf r =>
    rcases r with _ | _ | ⟨b, m⟩ <;> simp only [Turns] <;> try exact id
    exact hq _ _ _ _
  | sync op m k ih =>
    simp only [Turns]
    exact fun ⟨c, hc, hle, h⟩ => ⟨c, hc, hle, fun r m' hr => ih r m' (h r m' (hR m' hr))⟩

/-- Sequencing: the rest `f` of a result runs with the budget and the depth that are left. -/
theorem bind {Q₁ : β → Mem → Nat → Nat → Prop} {Q₂ : γ → Mem → Nat → Nat → Prop}
    {f : β → (k : Nat) → Mem → CoN Tgt (γ × Mem) k}
    (hf : ∀ b m B d, Q₁ b m B d → Turns R kb Q₂ B (f b d m)) {B n : Nat}
    (x : CoN Tgt (β × Mem) n) :
    Turns R kb Q₁ B x → Turns R kb Q₂ B (x.bind fun (b, m) k => f b k m) := by
  induction x generalizing B with
  | leaf r =>
    rcases r with _ | _ | ⟨b, m⟩ <;> simp only [Turns, CoN.bind] <;> try exact id
    exact hf _ _ _ _
  | sync op m k ih =>
    simp only [Turns, CoN.bind]
    exact fun ⟨c, hc, hle, h⟩ => ⟨c, hc, hle, fun r m' hr => ih r m' (h r m' hr)⟩

end Turns

/-- From the memory `m`, every depth `n ≥ B` of `x` ends within budget `B`; a result leaves a
budget `B'` no larger than the depth that is left, with `Q` (see the module doc). -/
def Stops (R : Mem → Prop) (kb : Tgt → Option Nat) {α : Type} (x : ConcM Tgt α)
    (Q : α → Mem → Nat → Prop) (m : Mem) (B : Nat) : Prop :=
  ∀ n, B ≤ n → Turns R kb (fun a m' B' d => B' ≤ d ∧ Q a m' B') B (x n m)

namespace Stops

variable {R : Mem → Prop} {kb : Tgt → Option Nat} {α β σ : Type} {m : Mem} {B : Nat}
  {Q : α → Mem → Nat → Prop}

theorem mono {Q' : α → Mem → Nat → Prop} {x : ConcM Tgt α} (h : Stops R kb x Q m B)
    (hq : ∀ a m B, Q a m B → Q' a m B) : Stops R kb x Q' m B := fun n hn =>
  Turns.mono (fun _ h => h) (fun _ _ _ _ ⟨h1, h2⟩ => ⟨h1, hq _ _ _ h2⟩) _ (h n hn)

theorem pure' {a : α} (h : Q a m B) : Stops R kb (pure a : ConcM Tgt α) Q m B := fun n hn => by
  show Turns R kb _ B (n := n) (.leaf (some (.ok (a, m))))
  simp only [Turns]; exact ⟨hn, h⟩

theorem bind {x : ConcM Tgt α} {f : α → ConcM Tgt β} {Q : β → Mem → Nat → Prop}
    (h : Stops R kb x (fun a m' B' => Stops R kb (f a) Q m' B') m B) :
    Stops R kb (x >>= f) Q m B := fun n hn =>
  Turns.bind (f := fun a k m => f a k m) (fun _ _ _ d ⟨hd, hs⟩ => hs d hd) _ (h n hn)

theorem map {x : ConcM Tgt α} {g : α → β} {Q : β → Mem → Nat → Prop}
    (h : Stops R kb x (fun a m' B' => Q (g a) m' B') m B) : Stops R kb (g <$> x) Q m B := by
  rw [map_eq_pure_bind]
  exact bind (h.mono fun _ _ _ hq => pure' hq)

theorem discard' {x : ConcM Tgt α} {Q : PUnit → Mem → Nat → Prop}
    (h : Stops R kb x (fun _ m' B' => Q () m' B') m B) : Stops R kb (discard x) Q m B :=
  map h

theorem throw' (e : Error) : Stops R kb (throw e : ConcM Tgt α) Q m B := fun n _ => by
  show Turns R kb _ B (n := n) (.leaf (some (.error e)))
  simp only [Turns]

/-- A step in `MemM`: no stop. It must have a result (`MemM.Halts`). -/
theorem liftMem {x : MemM α} (hx : x.Halts)
    (h : ∀ a m', (x.run m).run = some (.ok (a, m')) → Q a m' B) :
    Stops R kb (ConcM.liftMem x : ConcM Tgt α) Q m B := by
  intro n hn
  show Turns R kb _ B (.leaf (x.run m))
  have hh := hx m
  unfold Result.Halts at hh
  match hr : (x.run m).run, hh with
  | some (.error e), _ =>
    rw [show x.run m = ExceptT.mk (some (.error e)) from hr]; simp only [ExceptT.mk, Turns]
  | some (.ok (a, m')), _ =>
    rw [show x.run m = ExceptT.mk (some (.ok (a, m'))) from hr]
    simp only [ExceptT.mk, Turns]
    exact ⟨hn, h a m' hr⟩

theorem monadLift' {x : MemM α} (hx : x.Halts)
    (h : ∀ a m', (x.run m).run = some (.ok (a, m')) → Q a m' B) :
    Stops R kb (monadLift x : ConcM Tgt α) Q m B := liftMem hx h

/-- A sync op with a cost `c` within the budget: the thread goes on from every memory of the
rely, with `c` turns less. -/
theorem sync {op : SyncOp Tgt} {Q : op.Resp → Mem → Nat → Prop} {c : Nat}
    (hc : opCost kb op = some c) (hle : c ≤ B) (h : ∀ r m', R m' → Q r m' (B - c)) :
    Stops R kb (ConcM.sync op) Q m B := by
  intro n hn
  have h1 := opCost_pos hc
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  show Turns R kb _ B (.sync op m fun r m' => .leaf (some (.ok (r, m'))))
  simp only [Turns]
  exact ⟨c, hc, hle, fun r m' hr => ⟨by omega, h r m' hr⟩⟩

/-- A spin hint: one turn. -/
theorem spinLoopHint' {Q : Unit → Mem → Nat → Prop} (hle : 1 ≤ B)
    (h : ∀ m', R m' → Q () m' (B - 1)) : Stops R kb (Zig.spinLoopHint : ConcM Tgt Unit) Q m B :=
  sync rfl hle fun _ m' hr => h m' hr

/-! ### The body monad of a concurrent function (`CM`) -/

theorem liftM' {x : MemM α} {s : σ} {Q : α × σ → Mem → Nat → Prop} (hx : x.Halts)
    (h : ∀ a m', (x.run m).run = some (.ok (a, m')) → Q (a, s) m' B) :
    Stops R kb ((liftM x : CM Tgt σ α).run s) Q m B := by
  show Stops R kb (ConcM.liftMem x >>= fun a => pure (a, s)) Q m B
  exact bind (liftMem hx fun a m' hr => pure' (h a m' hr))

theorem callMC' {x : MemM α} {s : σ} {Q : α × σ → Mem → Nat → Prop} (hx : x.Halts)
    (h : ∀ a m', (x.run m).run = some (.ok (a, m')) → Q (a, s) m' B) :
    Stops R kb ((callMC x : CM Tgt σ α).run s) Q m B := liftM' hx h

theorem callRC' {x : Result α} {s : σ} {Q : α × σ → Mem → Nat → Prop} (hx : x.Halts)
    (h : ∀ a, x.run = some (.ok a) → Q (a, s) m B) :
    Stops R kb ((callRC x : CM Tgt σ α).run s) Q m B := by
  show Stops R kb (ConcM.liftMem (StateT.lift x) >>= fun a => pure (a, s)) Q m B
  refine bind (liftMem (MemM.Halts.lift' hx) fun a m' hr => pure' ?_)
  obtain ⟨ha, rfl⟩ := Proto.MemM.lift_ok hr
  exact h a ha

/-- A sync op of the body. -/
theorem liftSync {op : SyncOp Tgt} {s : σ} {Q : op.Resp × σ → Mem → Nat → Prop} {c : Nat}
    (hc : opCost kb op = some c) (hle : c ≤ B) (h : ∀ r m', R m' → Q (r, s) m' (B - c)) :
    Stops R kb ((StateT.lift (ConcM.sync op) : CM Tgt σ op.Resp).run s) Q m B := by
  show Stops R kb (ConcM.sync op >>= fun a => pure (a, s)) Q m B
  exact bind (sync hc hle fun r m' hr => pure' (h r m' hr))

theorem pickC' {count : Mem → Nat} {s : σ} {Q : Nat × σ → Mem → Nat → Prop} (hle : 1 ≤ B)
    (h : ∀ c m', R m' → Q (c, s) m' (B - 1)) :
    Stops R kb ((pickC count : CM Tgt σ Nat).run s) Q m B := liftSync rfl hle h

/-- `Thread.spawn` of a target with a budget `k`: `k + 2` turns. -/
theorem spawnC' {tgt : Tgt} {k : Nat} {s : σ} {Q : Except ErrName ThreadId × σ → Mem → Nat → Prop}
    (hk : kb tgt = some k) (hle : k + 2 ≤ B) (h : ∀ r m', R m' → Q (r, s) m' (B - (k + 2))) :
    Stops R kb ((spawnC tgt : CM Tgt σ (Except ErrName ThreadId)).run s) Q m B :=
  liftSync (by simp [opCost, hk]) hle h

theorem joinC' {tid : ThreadId} {s : σ} {Q : Unit × σ → Mem → Nat → Prop} (hle : 1 ≤ B)
    (h : ∀ m', R m' → Q ((), s) m' (B - 1)) :
    Stops R kb ((joinC tid : CM Tgt σ Unit).run s) Q m B := by
  show Stops R kb (((fun _ => ()) <$> ConcM.sync (Tgt := Tgt) (.join tid)) >>= fun a =>
    pure (a, s)) Q m B
  exact bind (map (sync rfl hle fun _ m' hr => pure' (h m' hr)))

/-- An atomic op of the body (`atomicLoadC`, `atomicRmwC`, …): the oracle's pick (one turn),
then the op in `MemM`. -/
theorem pickMem {count : Mem → Nat} {x : Nat → MemM α} {s : σ} {Q : α × σ → Mem → Nat → Prop}
    (hle : 1 ≤ B) (hx : ∀ c, (x c).Halts)
    (h : ∀ c m', R m' → ∀ a m'', ((x c).run m').run = some (.ok (a, m'')) → Q (a, s) m'' (B - 1)) :
    Stops R kb ((do let c ← pickC count; callMC (x c) : CM Tgt σ α).run s) Q m B := by
  show Stops R kb ((pickC count : CM Tgt σ Nat).run s >>= fun p => (callMC (x p.1) : CM Tgt σ α).run p.2)
    Q m B
  exact bind (pickC' hle fun c m' hr => callMC' (hx c) fun a m'' he => h c m' hr a m'' he)

/-! ### Loops -/

/-- A loop (`Zig.loop`) whose repeats make the measure `meas` smaller, with the invariant `inv`
on the locals, the memory and the budget. -/
theorem loop {ε : Type} (body : CM Tgt σ ε) (again : ε → Bool) (inv : σ → Mem → Nat → Prop)
    (meas : σ → Nat) (post : ε × σ → Mem → Nat → Prop)
    (step : ∀ s m B, inv s m B → Stops R kb (body.run s) (fun r m' B' =>
      if again r.1 then inv r.2 m' B' ∧ meas r.2 < meas s else post r m' B') m B) :
    ∀ s m B, inv s m B → Stops R kb ((Zig.loop body again).run s) post m B := by
  intro s
  induction hk : meas s using Nat.strongRecOn generalizing s with
  | _ k ih =>
  intro m B hi
  rw [Zig.loop.eq_1, StateT.run_bind]
  refine bind ((step s m B hi).mono ?_)
  rintro ⟨e, s'⟩ m' B' hq
  cases ha : again e
  · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hq ⊢
    exact pure' hq
  · simp only [ha, ↓reduceIte] at hq ⊢
    exact ih (meas s') (hk ▸ hq.2) s' rfl m' B' hq.1

end Stops

end Conc
end Zig
