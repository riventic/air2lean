import ZigLean.Conc.Detach

/-!
# A transferred join handle over all schedules (C07)

`main` spawns `A`, spawns `B` with `A`'s handle as its argument and transfers the handle to `B`
(`transferHandleC`); `B` joins `A`, and `main` joins `B`. For every schedule and every fuel:

- no run gives an error (`transfer_safe`): no invalid join, no deadlock;
- a run that ends returns `1`, and `A` was joined by its one authorized owner `B`: its record
  names `B` as the owner and is consumed, and every handle `main` owns is consumed
  (`transfer_result`).

The join order is not the thread order (`B` is later than `A` but joins it), so the protocol
picks the rank `0 < B < A` (`Proto.rank`). The negative side, `main` and `B` both joining `A`, is
rejected with `.illegal` (`join_after_transfer` in `ZigLean/Conc/Detach.lean`; the run-level
witnesses are in `tests/roadmap/detached-threads/Runtime.lean`).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Detach

namespace Detach.Transfer

/-- The spawn targets: `A`, and `B` with the handle it joins. -/
inductive Tgt where
  | a
  | b (h : ThreadId)

/-- The workers: `A` does nothing; `B` joins the handle it received. -/
def body : Tgt → CM Tgt Unit Unit
  | .a => pure ()
  | .b h => joinC h

def dispatch (tgt : Tgt) : ConcM Tgt Unit := Prod.fst <$> (body tgt).run ()

/-- `main`: spawn `A`; spawn `B` with `A`'s handle, and hand the handle to `B`; join `B`. -/
def main : CM Tgt Unit (BitVec 8) := do
  match ← spawnC Tgt.a with
  | .error _ => pure 0
  | .ok a =>
    match ← spawnC (Tgt.b a) with
    | .error _ => pure 0
    | .ok b =>
      transferHandleC a b
      joinC b
      pure 1

def mainRun : ConcM Tgt (BitVec 8) := Prod.fst <$> main.run ()

/-! ## Protocol -/

/-- Ghost values: `main` at its three stops, `A` (done) and `B` (it joined `A`). -/
inductive Gh where
  | none | m0 | m1 | m2
  | a (done : Bool)
  | b (done : Bool)
  deriving DecidableEq

/-- A thread record. -/
abbrev R (s : ThreadId) (j : Bool) : ThreadRec := { spawner := s, joined := j }

/-- The threads at each stop of `main`. At its join of `B` (`m2`), `B` owns `A`'s handle; it is
consumed exactly when `B` has joined `A`, which is after `A` ended. -/
def InvT (G : ThreadId → Gh) (ts : Array ThreadRec) : Prop :=
  ts[0]? = some (R 0 true) ∧
  ((G 0 = .m0 ∧ ts.size = 1 ∧ ∀ u, 1 ≤ u → G u = .none) ∨
   (G 0 = .m1 ∧ ts.size = 2 ∧ ts[1]? = some (R 0 false) ∧ (∃ d, G 1 = .a d) ∧
     ∀ u, 2 ≤ u → G u = .none) ∨
   (G 0 = .m2 ∧ ts.size = 3 ∧ ts[2]? = some (R 0 false) ∧
     (∃ jb d, G 2 = .b jb ∧ G 1 = .a d ∧ ts[1]? = some (R 2 jb) ∧ (jb = true → d = true)) ∧
     ∀ u, 3 ≤ u → G u = .none))

/-- The invariant is on the thread table only. -/
def Inv (G : ThreadId → Gh) (m : Mem) : Prop := InvT G m.threads

/-- `B` joins `A` although `A` is the earlier thread: `main` < `B` < `A`. -/
def rank (u : ThreadId) : Nat := if u = 1 then 2 else if u = 2 then 1 else u

def proto : Proto Tgt Gh where
  inv := Inv
  init tgt g := match tgt with
    | .a => g = .a false
    | .b h => g = .b false ∧ h = 1
  fin g := g = .a true ∨ g = .b true
  strict := true
  rank := rank

/-- `main`'s post: the result, and `A`'s handle owned by `B` and consumed. -/
def QM (v : BitVec 8) (_ : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  v = 1 ∧ joinedAll 0 m ∧ m.threads[1]? = some (R 2 true) ∧ m.threads[2]? = some (R 0 true)

/-! ## Facts of the invariant -/

theorem joinedAll_of {t : ThreadId} {m : Mem} {ts : Array ThreadRec} (hth : m.threads = ts)
    (hs : ts.size ≤ 3) (h : ∀ i r, i < 3 → ts[i]? = some r → r.spawner = t → r.joined = true) :
    joinedAll t m := by
  intro r hr hsp
  rw [hth] at hr
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hr
  exact h i _ (by omega) (Array.getElem?_eq_getElem hi) hsp

theorem set_get {ts : Array ThreadRec} {i j : Nat} {r : ThreadRec} (hi : i < ts.size) :
    (ts.setIfInBounds i r)[j]? = if i = j then some r else ts[j]? := by
  rw [Array.getElem?_setIfInBounds]; simp [hi]

/-- Only thread 1 is `A`. -/
theorem a_one {G : ThreadId → Gh} {ts : Array ThreadRec} {u : ThreadId} {d : Bool}
    (hi : InvT G ts) (hu : G u = .a d) : u = 1 := by
  obtain ⟨-, ⟨h0, -, hn⟩ | ⟨h0, -, -, -, hn⟩ | ⟨h0, -, -, ⟨jb, d', h2, -⟩, hn⟩⟩ := hi
  · by_cases hu0 : u = 0
    · subst hu0; rw [h0] at hu; cases hu
    · rw [hn u (by unfold ThreadId at *; omega)] at hu; cases hu
  · by_cases hu0 : u = 0
    · subst hu0; rw [h0] at hu; cases hu
    · by_cases hu1 : u = 1
      · exact hu1
      · rw [hn u (by unfold ThreadId at *; omega)] at hu; cases hu
  · by_cases hu0 : u = 0
    · subst hu0; rw [h0] at hu; cases hu
    · by_cases hu1 : u = 1
      · exact hu1
      · by_cases hu2 : u = 2
        · subst hu2; rw [h2] at hu; cases hu
        · rw [hn u (by unfold ThreadId at *; omega)] at hu; cases hu

/-- Only thread 2 is `B`. -/
theorem b_two {G : ThreadId → Gh} {ts : Array ThreadRec} {u : ThreadId} {d : Bool}
    (hi : InvT G ts) (hu : G u = .b d) : u = 2 := by
  obtain ⟨-, ⟨h0, -, hn⟩ | ⟨h0, -, -, ⟨d', h1⟩, hn⟩ | ⟨h0, -, -, ⟨jb, d', h2, h1, -⟩, hn⟩⟩ := hi
  · by_cases hu0 : u = 0
    · subst hu0; rw [h0] at hu; cases hu
    · rw [hn u (by unfold ThreadId at *; omega)] at hu; cases hu
  · by_cases hu0 : u = 0
    · subst hu0; rw [h0] at hu; cases hu
    · by_cases hu1 : u = 1
      · subst hu1; rw [h1] at hu; cases hu
      · rw [hn u (by unfold ThreadId at *; omega)] at hu; cases hu
  · by_cases hu0 : u = 0
    · subst hu0; rw [h0] at hu; cases hu
    · by_cases hu1 : u = 1
      · subst hu1; rw [h1] at hu; cases hu
      · by_cases hu2 : u = 2
        · exact hu2
        · rw [hn u (by unfold ThreadId at *; omega)] at hu; cases hu

/-- No thread record names `A` as an owner. -/
theorem joinedAll_a {G : ThreadId → Gh} {m : Mem} (hi : InvT G m.threads) : joinedAll 1 m := by
  obtain ⟨h0, ⟨-, hs, -⟩ | ⟨-, hs, h1, -⟩ | ⟨-, hs, h2, ⟨jb, d, -, -, h1, -⟩, -⟩⟩ := hi
  · refine joinedAll_of rfl (by omega) fun i r hi hr hsp => ?_
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · cases rec_eq h0 hr; cases hsp
    · rw [Array.getElem?_eq_none (by omega)] at hr; cases hr
    · rw [Array.getElem?_eq_none (by omega)] at hr; cases hr
  · refine joinedAll_of rfl (by omega) fun i r hi hr hsp => ?_
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · cases rec_eq h0 hr; cases hsp
    · cases rec_eq h1 hr; cases hsp
    · rw [Array.getElem?_eq_none (by omega)] at hr; cases hr
  · refine joinedAll_of rfl (by omega) fun i r hi hr hsp => ?_
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · cases rec_eq h0 hr; cases hsp
    · cases rec_eq h1 hr; cases hsp
    · cases rec_eq h2 hr; cases hsp

/-! ## The workers -/

theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (n : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } n := by
  have hiT : InvT G m.threads := hi
  cases tgt with
  | a =>
    subst hg
    have := a_one hiT hgu
    subst this
    refine WP.map (WP.pure' ⟨.a true, ?_, .inl rfl, fun _ => joinedAll_a hiT⟩)
    -- `A` ends: its ghost value is `done`.
    show InvT _ m.threads
    obtain ⟨h0, ⟨-, -, hn⟩ | ⟨g0, hs, h1, -, hn⟩ | ⟨g0, hs, h2, ⟨jb, d, gb, ga, h1, hjd⟩, hn⟩⟩ :=
      hiT
    · rw [hn 1 (by decide)] at hgu; cases hgu
    · exact ⟨h0, .inr (.inl ⟨by rw [upd_ne _ _ (by decide)]; exact g0, hs, h1,
        ⟨true, upd_self _ _ _⟩, fun u hu => by
          rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact hn u hu⟩)⟩
    · exact ⟨h0, .inr (.inr ⟨by rw [upd_ne _ _ (by decide)]; exact g0, hs, h2,
        ⟨jb, true, by rw [upd_ne _ _ (by decide)]; exact gb, upd_self _ _ _, h1, fun _ => rfl⟩,
        fun u hu => by rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact hn u hu⟩)⟩
  | b h =>
    obtain ⟨rfl, rfl⟩ := hg
    have := b_two hiT hgu
    subst this
    refine WP.map (WP.joinC fun k _ => ⟨.b false, by rw [← hgu, upd_same]; exact hi,
      fun G₁ m₁ hg₁ hi₁ => ?_⟩)
    have hiT₁ : InvT G₁ m₁.threads := hi₁
    obtain ⟨h0, ⟨-, -, hn⟩ | ⟨-, -, -, -, hn⟩ | ⟨g0, hs, h2, ⟨jb, d, gb, ga, h1, -⟩, hn⟩⟩ := hiT₁
    · rw [hn 2 (by decide)] at hg₁; cases hg₁
    · rw [hn 2 (by decide)] at hg₁; cases hg₁
    rw [hg₁] at gb; cases gb
    refine ⟨fun _ => ⟨by decide, by rw [hs]; decide, trivial, by
      simp [Thread.joinValid, h1]⟩, fun hfin => ⟨fun _ => join_run h1 rfl rfl, fun m' hj => ?_⟩⟩
    -- `B` joined `A`, which ended.
    have hda : d = true := by
      rcases hfin with hf | hf <;> rw [ga] at hf <;> cases hf; rfl
    subst hda
    obtain ⟨-, hth⟩ := join_threads h1 hj
    have hth' : m'.threads = m₁.threads.setIfInBounds 1 (R 2 true) := hth
    have hlt : 1 < m₁.threads.size := by rw [hs]; decide
    refine ⟨.b true, ?_, .inr rfl, fun _ => ?_⟩
    · show InvT _ m'.threads
      rw [hth']
      refine ⟨by rw [set_get hlt]; exact h0, .inr (.inr ⟨?_, by simp [hs], ?_,
        ⟨true, true, upd_self _ _ _, by rw [upd_ne _ _ (by decide)]; exact ga,
          by rw [set_get hlt]; rfl, fun _ => rfl⟩, ?_⟩)⟩
      · rw [upd_ne _ _ (by decide)]; exact g0
      · rw [set_get hlt]; exact h2
      · intro u hu; rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact hn u hu
    · refine joinedAll_of hth' (by simp [hs]) fun i r hi hr hsp => ?_
      rw [set_get hlt] at hr
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · cases rec_eq h0 hr; cases hsp
      · cases hr; rfl
      · cases rec_eq h2 hr; cases hsp

/-! ## `main` -/

/-- The start: `main` alone, at its first stop. -/
def G0 : ThreadId → Gh := fun u => if u = 0 then .m0 else .none

theorem main_spec (n : Nat) : proto.WP 0 mainRun QM G0 ({} : Mem) n := by
  unfold mainRun main
  refine WP.map ?_
  simp only [StateT.run_bind]
  -- Spawn `A`.
  refine WP.bind (WP.spawnC fun k _ => ⟨.m0, ?_, fun G₁ m₁ hg₁ hi₁ =>
    ⟨.a false, rfl, fun child m₂ hf => ?_⟩⟩)
  · refine ⟨rfl, .inl ⟨by simp [upd], rfl, fun u hu => ?_⟩⟩
    simp [upd, G0, show u ≠ 0 by unfold ThreadId at *; omega]
  have hiT₁ : InvT G₁ m₁.threads := hi₁
  obtain ⟨h0₁, ⟨-, hs₁, hn₁⟩ | ⟨g0, -⟩ | ⟨g0, -⟩⟩ := hiT₁
  rotate_left
  · rw [hg₁] at g0; cases g0
  · rw [hg₁] at g0; cases g0
  obtain ⟨hc, hth₂, -⟩ := fork_eq hf
  rw [hs₁] at hc
  subst hc
  dsimp only
  simp only [StateT.run_bind]
  -- Spawn `B` with `A`'s handle.
  refine WP.bind (WP.spawnC fun k _ => ⟨.m1, ?_, fun G₂ m₃ hg₂ hi₃ =>
    ⟨.b false, ⟨rfl, rfl⟩, fun child m₄ hf => ?_⟩⟩)
  · show InvT _ m₂.threads
    rw [hth₂]
    refine ⟨by rw [Array.getElem?_push, ite_eq_right (by omega)]; exact h0₁, .inr (.inl ⟨upd_self _ _ _,
      by simp [hs₁], by rw [Array.getElem?_push, ite_eq_left hs₁.symm], ⟨false, ?_⟩, fun u hu => ?_⟩)⟩
    · rw [upd_ne _ _ (by decide), upd_self]
    · rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega)]
      exact hn₁ u (by unfold ThreadId at *; omega)
  have hiT₃ : InvT G₂ m₃.threads := hi₃
  obtain ⟨h0₃, ⟨g0, -⟩ | ⟨-, hs₃, h1₃, ⟨d, ga₃⟩, hn₃⟩ | ⟨g0, -⟩⟩ := hiT₃
  · rw [hg₂] at g0; cases g0
  rotate_left
  · rw [hg₂] at g0; cases g0
  obtain ⟨hc, hth₄, hcur₄⟩ := fork_eq hf
  rw [hs₃] at hc
  subst hc
  dsimp only
  simp only [StateT.run_bind]
  -- Hand `A`'s handle to `B`.
  have h1₄ : m₄.threads[1]? = some (R 0 false) := by
    rw [hth₄, Array.getElem?_push, ite_eq_right (by omega)]; exact h1₃
  refine WP.bind (WP.transferHandleC h1₄ hcur₄.symm rfl (by decide) (by simp [hth₄, hs₃]) ?_)
  -- Join `B`.
  refine WP.bind (WP.joinC fun k _ => ⟨.m2, ?_, fun G₃ m₅ hg₃ hi₅ => ?_⟩)
  · show InvT _ (m₄.threads.set! 1 _)
    have hlt : 1 < m₄.threads.size := by simp [hth₄, hs₃]
    rw [Array.set!_eq_setIfInBounds]
    refine ⟨by
        rw [set_get hlt, ite_eq_right (by decide : ¬ (1 = 0)), hth₄, Array.getElem?_push,
          ite_eq_right (by omega : ¬ (0 = m₃.threads.size))]; exact h0₃,
      .inr (.inr ⟨upd_self _ _ _, by simp [hth₄, hs₃], ?_,
      ⟨false, d, by rw [upd_ne _ _ (by decide), upd_self], ?_, by rw [set_get hlt]; rfl,
        fun h => by cases h⟩, fun u hu => ?_⟩)⟩
    · rw [set_get hlt, ite_eq_right (by decide : ¬ (1 = 2)), hth₄, Array.getElem?_push, ite_eq_left hs₃.symm]
    · rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact ga₃
    · rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega)]
      exact hn₃ u (by unfold ThreadId at *; omega)
  have hiT₅ : InvT G₃ m₅.threads := hi₅
  obtain ⟨h0₅, ⟨g0, -⟩ | ⟨g0, -⟩ | ⟨-, hs₅, h2₅, ⟨jb, d', gb, -, h1₅, -⟩, -⟩⟩ := hiT₅
  · rw [hg₃] at g0; cases g0
  · rw [hg₃] at g0; cases g0
  refine ⟨fun _ => ⟨by decide, by rw [hs₅]; decide, trivial, by
    simp [Thread.joinValid, h2₅]⟩, fun hfin => ⟨fun _ => join_run h2₅ rfl rfl, fun m₆ hj => ?_⟩⟩
  -- `B` ended, so it joined `A`.
  have hjb : jb = true := by
    rcases hfin with hf | hf <;> rw [gb] at hf <;> cases hf; rfl
  subst hjb
  obtain ⟨-, hth⟩ := join_threads h2₅ hj
  have hth₆ : m₆.threads = m₅.threads.setIfInBounds 2 (R 0 true) := hth
  have hlt : 2 < m₅.threads.size := by rw [hs₅]; decide
  refine WP.pure' ⟨rfl, ?_, by rw [hth₆, set_get hlt]; exact h1₅, by rw [hth₆, set_get hlt]; rfl⟩
  refine joinedAll_of hth₆ (by simp [hs₅]) fun i r hi hr hsp => ?_
  rw [set_get hlt] at hr
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · cases rec_eq h0₅ hr; rfl
  · cases rec_eq h1₅ hr; cases hsp
  · cases hr; rfl

/-! ## Over all schedules -/

/-- **No error.** Under every schedule and fuel, no run gives an error. -/
theorem transfer_safe (fuel : Nat) (o : Nat → Nat) (e : Error) :
    (Sched.run dispatch fuel o mainRun {}).run ≠ some (.error e) :=
  run_safe (P := proto) dispatch G0 rfl
    (fun tgt g hg u G m n hu hgu hi => dispatch_spec tgt g hg u G m n hu hgu hi)
    (fun _ _ _ _ h => h.2.1) rfl (fun n => main_spec n)

/-- **One authorized owner.** A run that ends returns `1`; `A`'s handle is owned by `B` and was
consumed (joined by `B`, the only thread that could), and `main` owes no join. -/
theorem transfer_result {fuel : Nat} {o : Nat → Nat} {v : BitVec 8} {m : Mem}
    (h : (Sched.run dispatch fuel o mainRun {}).run = some (.ok (v, m))) :
    v = 1 ∧ joinedAll 0 m ∧ m.threads[1]? = some { spawner := 2, joined := true } := by
  obtain ⟨G, d, hv, hj, h1, -⟩ := run_sound (P := proto) dispatch G0
    (fun tgt g hg u G m n hu hgu hi => dispatch_spec tgt g hg u G m n hu hgu hi)
    (fun _ _ _ _ _ h => h.2.1) rfl (fun n => main_spec n) h
  exact ⟨hv, hj, h1⟩

end Detach.Transfer
