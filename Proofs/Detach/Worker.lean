import ZigLean.Conc.Detach
import ZigLean.Conc.Progress

/-!
# A detached worker that owns its heap buffer, over all schedules (C07)

`main` allocates a 4-byte heap buffer, spawns a worker with the buffer as its argument, detaches
the worker and returns without joining it. The worker writes the buffer and frees it itself. The
buffer is a C01 `owned` transfer (`ZigLean/Conc/Transfer.lean`): `main` hands all its cells to the
worker at the spawn (`Owned.fork`), so the worker's accesses do not race with anyone, and the
worker alone can free it. For every schedule and every fuel:

- no run gives an error (`worker_safe`): no data race, no use after free, no invalid handle, no
  missing join (`checkJoinedByChild 0` passes with the worker detached and possibly running);
- a run that ends returns `7`, and the worker's handle is consumed by the detach
  (`worker_result`).

`main` stops once after the detach (a `yield`), so the worker may run before or after `main`
ends; `main`'s end ends the run, as the process exit does. The negative side (a detached worker
that captured a pointer into a frame that has exited) is `.illegal`: `frame_exit_kills` in
`ZigLean/Conc/Detach.lean`, run-level witnesses in `tests/roadmap/detached-threads/Runtime.lean`.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Detach Assn

namespace Detach.Worker

/-- The spawn target: the worker with its buffer. -/
inductive Tgt where
  | worker (p : Ptr)

/-- The worker writes its buffer and frees it (the allocator's raw free). -/
def work (p : Ptr) : MemM Unit := do
  store 4 p (42 : BitVec 32)
  free p

def dispatch : Tgt → ConcM Tgt Unit
  | .worker p => ConcM.liftMem (work p)

/-- `main`: allocate and initialize the buffer, spawn the worker with it, detach the worker. -/
def main : CM Tgt Unit (BitVec 32) := do
  let p ← _root_.liftM (alloc .heap 4 4)
  _root_.liftM (store 4 p (0 : BitVec 32))
  match ← spawnC (Tgt.worker p) with
  | .error _ => pure 0
  | .ok w =>
    detachC w
    spinLoopHintC
    pure 7

def mainRun : ConcM Tgt (BitVec 32) := Prod.fst <$> main.run ()

/-! ## The worker's buffer -/

/-- The worker's part: the 4-byte heap buffer at `p`. -/
def Buf (p : Ptr) : Assn := fun h =>
  ∃ A bs, p.off = 0 ∧ A % 4 = 0 ∧ bs.size = 4 ∧ bytesAt p A 4 .heap bs h

theorem enc_u32 (v : BitVec 32) : (Enc.encode v).size = 4 := LawfulEnc.size_encode v

theorem work_spec {p : Ptr} {A : Nat} {bs : Array Byte} (h0 : p.off = 0) (hA : A % 4 = 0)
    (hs : bs.size = 4) : TTriple (bytesAt p A 4 .heap bs) (work p) (fun _ => emp) := by
  unfold work
  refine TTriple.bind (TTriple.storeAt (k := 0) (a := 4) (42 : BitVec 32) (by simp [Ptr.add])
    (by decide) (by rw [hs]; decide) (by simp [h0, hA]) (by decide)) fun _ => ?_
  refine TTriple.free ?_ h0 (by decide)
  rw [writeBytes_size _ _ _ (by rw [hs, enc_u32]; decide), hs]

/-! ## Protocol -/

/-- Ghost values: `main` before the spawn (it owns `h`) and after it (it owns nothing); the
worker with its part `h`, its buffer `p` and whether it is done. -/
inductive Gh where
  | none
  | pre (h : Heap)
  | post
  | wk (h : Heap) (p : Ptr) (done : Bool)

/-- The part of a thread. -/
def Gh.heap : Gh → Heap
  | .pre h | .wk h _ _ => h
  | .none | .post => Heap.empty

abbrev R (s : ThreadId) (j : Bool) : ThreadRec := { spawner := s, joined := j }

/-- The thread table: before the spawn, `main` alone; after it, the worker, detached. -/
def Shape (G : ThreadId → Gh) (ts : Array ThreadRec) : Prop :=
  ts[0]? = some (R 0 true) ∧
  ((∃ h, G 0 = .pre h ∧ ts.size = 1 ∧ ∀ u, 1 ≤ u → G u = .none) ∨
   (G 0 = .post ∧ ts.size = 2 ∧ ts[1]? = some (R 0 true) ∧ (∃ h p d, G 1 = .wk h p d) ∧
     ∀ u, 2 ≤ u → G u = .none))

/-- The invariant: the parts (`Owned`), the worker's buffer while it runs, and the threads. -/
structure Inv (G : ThreadId → Gh) (m : Mem) : Prop where
  own : Owned (fun u => (G u).heap) m
  kid : ∀ u h p d, G u = .wk h p d → (d = false → Buf p h) ∧ (d = true → h = Heap.empty)
  shape : Shape G m.threads

def proto : Proto Tgt Gh where
  inv := Inv
  init tgt g := match tgt with
    | .worker p => ∃ h, g = .wk h p false
  fin g := ∃ p, g = .wk Heap.empty p true
  strict := true

/-- `main`'s post: the result, and the worker's handle consumed by the detach. -/
def QM (v : BitVec 32) (_ : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  v = 7 ∧ joinedAll 0 m ∧ m.threads[1]? = some (R 0 true)

/-! ## Facts of the invariant -/

/-- Every thread record is consumed: `main`'s own, and the detached worker's. -/
theorem joinedAll_of {G : ThreadId → Gh} {m : Mem} (hs : Shape G m.threads) {t : ThreadId} :
    joinedAll t m := by
  intro r hr _
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hr
  have hget := Array.getElem?_eq_getElem hi
  obtain ⟨h0, ⟨_, -, hsz, -⟩ | ⟨-, hsz, h1, -⟩⟩ := hs
  · have : i = 0 := by omega
    subst this; rw [rec_eq h0 hget]
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [rec_eq h0 hget]
    · rw [rec_eq h1 hget]

/-! ## The worker -/

theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (n : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } n := by
  have hi : Inv G m := hi
  cases tgt with
  | worker p =>
    obtain ⟨h, rfl⟩ := hg
    -- The worker is thread 1, after the spawn.
    obtain ⟨h0, ⟨h', g0, -, hn⟩ | ⟨g0, hsz, h1, -, hn⟩⟩ := hi.shape
    · rw [hn u (by unfold ThreadId at *; omega)] at hgu; cases hgu
    have hu1 : u = 1 := by
      by_cases h2 : 2 ≤ u
      · rw [hn u h2] at hgu; cases hgu
      · unfold ThreadId at *; omega
    subst hu1
    obtain ⟨A, bs, hp0, hA, hbs, hb⟩ := (hi.kid 1 h p false hgu).1 rfl
    refine WP.liftMem_owned (own := fun u => (G u).heap) (work_spec hp0 hA hbs)
      (hi.own.current 1) rfl (by rw [hsz]; decide) (by simp only [hgu, Gh.heap]; exact hb)
      fun _ m' hQ _ ho' hq hs _ _ => ?_
    have hQ0 : hQ = Heap.empty := hq
    subst hQ0
    have hown : (fun w => (upd G 1 (.wk Heap.empty p true) w).heap) =
        upd (fun u => (G u).heap) 1 Heap.empty := by
      funext w; by_cases hw : w = 1
      · subst hw; simp [Gh.heap]
      · simp [upd, hw]
    have hth : m'.threads = m.threads := hs.threads
    refine ⟨.wk Heap.empty p true, ⟨by rw [hown]; exact ho', fun w h₁ p₁ d₁ hw => ?_, ?_⟩,
      ⟨p, rfl⟩, fun _ => ?_⟩
    · by_cases hw1 : w = 1
      · subst hw1; rw [upd_self] at hw; cases hw; exact ⟨fun h => (by cases h), fun _ => rfl⟩
      · rw [upd_ne _ _ hw1] at hw; exact hi.kid w h₁ p₁ d₁ hw
    · show Shape _ m'.threads
      rw [hth]
      exact ⟨h0, .inr ⟨by rw [upd_ne _ _ (by decide)]; exact g0, hsz, h1,
        ⟨_, _, _, upd_self _ _ _⟩,
        fun w hw => by rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact hn w hw⟩⟩
    · have hs' : Shape G m'.threads := by rw [hth]; exact ⟨h0, .inr ⟨g0, hsz, h1, ⟨_, _, _, hgu⟩, hn⟩⟩
      exact joinedAll_of hs'

/-! ## `main` -/

/-- The start: `main` alone, owning nothing. -/
def G0 : ThreadId → Gh := fun u => if u = 0 then .pre Heap.empty else .none

theorem main_spec (n : Nat) : proto.WP 0 mainRun QM G0 ({} : Mem) n := by
  unfold mainRun main
  refine WP.map ?_
  simp only [StateT.run_bind]
  have ho₀ : Owned (upd (fun _ => Heap.empty) 0 Heap.empty) ({} : Mem) := by
    rw [show upd (fun _ => Heap.empty) 0 Heap.empty = (fun _ => Heap.empty) from upd_same _ _]
    exact Owned.start rfl rfl
  -- Allocate and initialize the buffer.
  refine WP.bind (WP.liftM_upd (TTriple.alloc .heap 4 4 (by decide)) ho₀ rfl (by decide) rfl
    fun p m₁ h₁ ho₁ hq₁ hc₁ ht₁ => ?_)
  obtain ⟨A, hA⟩ := hq₁
  obtain ⟨⟨hp0, hAl⟩, hb₁⟩ := sep_lift.mp hA
  refine WP.bind (WP.liftM_upd (TTriple.storeAt (k := 0) (a := 4) (0 : BitVec 32)
    (by simp [Ptr.add]) (by decide) (by simp; decide) (by simp [hp0, hAl]) (by decide)) ho₁ hc₁
    (by rw [ht₁]; decide) hb₁ fun _ m₂ h₂ ho₂ hb₂ hc₂ ht₂ => ?_)
  have hbs : (writeBytes (Array.replicate 4 Byte.undef) 0 (Enc.encode (0 : BitVec 32))).size = 4 := by
    rw [writeBytes_size _ _ _ (by rw [enc_u32]; simp)]; simp
  dsimp only
  -- Spawn the worker: it gets the whole buffer.
  refine WP.bind (WP.spawnC fun k _ => ⟨.pre h₂, ?_, fun G₁ m₃ hg₁ hi₃ =>
    ⟨.wk h₂ p false, ⟨h₂, rfl⟩, fun child m₄ hf => ?_⟩⟩)
  · have hown : (fun u => (upd G0 0 (.pre h₂) u).heap) = upd (fun _ => Heap.empty) 0 h₂ := by
      funext u; by_cases hu : u = 0
      · subst hu; simp [Gh.heap]
      · simp [upd, G0, hu, Gh.heap]
    refine ⟨by rw [hown]; exact ho₂, fun u h p' d hu => ?_, ?_⟩
    · by_cases hu0 : u = 0
      · subst hu0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ hu0] at hu; simp [G0, hu0] at hu
    · show Shape _ m₂.threads
      rw [ht₂, ht₁]
      refine ⟨rfl, .inl ⟨h₂, upd_self _ _ _, rfl, fun u hu => ?_⟩⟩
      simp [upd, G0, show u ≠ 0 by unfold ThreadId at *; omega]
  have hi₃ : Inv G₁ m₃ := hi₃
  obtain ⟨h0₃, ⟨h', g0, hs₃, hn₃⟩ | ⟨g0, -⟩⟩ := hi₃.shape
  rotate_left
  · rw [hg₁] at g0; cases g0
  rw [hg₁] at g0; cases g0
  obtain ⟨hc, hth₄, hcur₄⟩ := fork_eq hf
  rw [hs₃] at hc
  subst hc
  have hown₃ : (fun u => (G₁ u).heap) 0 = Heap.empty ∪ h₂ := by
    simp [hg₁, Gh.heap]
  have ho₄ := Owned.fork (hi₃.own.current 0) (by rw [hs₃]; decide) hown₃
    (Heap.disjoint_empty _).symm hf
  dsimp only
  simp only [StateT.run_bind]
  -- Detach the worker.
  have h1₄ : m₄.threads[1]? = some (R 0 false) := by
    rw [hth₄, Array.getElem?_push, ite_eq_left hs₃.symm]
  refine WP.bind (WP.detachC h1₄ hcur₄.symm rfl ?_)
  -- The stop after the detach: the worker may run now, or after `main` ends.
  refine WP.bind (WP.callC (WP.spinLoopHint fun k _ => ⟨.post, ?_, fun G₂ m₅ hg₂ hi₅ => ?_⟩))
  · have hown : (fun u => (upd (upd G₁ 1 (.wk h₂ p false)) 0 .post u).heap) =
        upd (upd (fun u => (G₁ u).heap) 0 Heap.empty) 1 h₂ := by
      funext u
      by_cases hu0 : u = 0
      · subst hu0; simp [upd, Gh.heap]
      · by_cases hu1 : u = 1
        · subst hu1; simp [upd, Gh.heap]
        · simp [upd, hu0, hu1]
    refine ⟨by rw [hown]; exact Owned.setThread ho₄ _, fun u h p' d hu => ?_, ?_⟩
    · by_cases hu0 : u = 0
      · subst hu0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ hu0] at hu
        by_cases hu1 : u = 1
        · subst hu1; rw [upd_self] at hu; cases hu
          exact ⟨fun _ => ⟨A, _, hp0, hAl, hbs, hb₂⟩, fun h => (by cases h)⟩
        · rw [upd_ne _ _ hu1, hn₃ u (by unfold ThreadId at *; omega)] at hu; cases hu
    · show Shape _ (m₄.threads.set! 1 _)
      have hlt : 1 < m₄.threads.size := by simp [hth₄, hs₃]
      rw [Array.set!_eq_setIfInBounds]
      refine ⟨?_, .inr ⟨upd_self _ _ _, by simp [hth₄, hs₃], ?_, ⟨h₂, p, false, ?_⟩, fun u hu => ?_⟩⟩
      · rw [Array.getElem?_setIfInBounds_ne (by decide), hth₄, Array.getElem?_push,
          ite_eq_right (by omega)]
        exact h0₃
      · simp [Array.getElem?_setIfInBounds_self_of_lt hlt]
      · rw [upd_ne _ _ (by decide), upd_self]
      · rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega)]
        exact hn₃ u (by unfold ThreadId at *; omega)
  -- `main` ends: it owes no join; the detached worker may still run.
  have hi₅ : Inv G₂ m₅ := hi₅
  obtain ⟨h0₅, ⟨h'', g0, -⟩ | ⟨-, hs₅, h1₅, -, -⟩⟩ := hi₅.shape
  · rw [hg₂] at g0; cases g0
  exact WP.pure' ⟨rfl, joinedAll_of hi₅.shape, h1₅⟩

/-! ## Over all schedules -/

/-- **No error.** Under every schedule and fuel, no run gives an error: the detached worker's
accesses and its free do not race, and `main` may end without joining it. -/
theorem worker_safe (fuel : Nat) (o : Nat → Nat) (e : Error) :
    (Sched.run dispatch fuel o mainRun {}).run ≠ some (.error e) :=
  run_safe (P := proto) dispatch G0 rfl
    (fun tgt g hg u G m n hu hgu hi => dispatch_spec tgt g hg u G m n hu hgu hi)
    (fun _ _ _ _ h => h.2.1) rfl (fun n => main_spec n)

/-- A run that ends returns `7`; the worker's handle was consumed by the detach. -/
theorem worker_result {fuel : Nat} {o : Nat → Nat} {v : BitVec 32} {m : Mem}
    (h : (Sched.run dispatch fuel o mainRun {}).run = some (.ok (v, m))) :
    v = 7 ∧ joinedAll 0 m ∧ m.threads[1]? = some { spawner := 0, joined := true } := by
  obtain ⟨G, d, hv, hj, h1⟩ := run_sound (P := proto) dispatch G0
    (fun tgt g hg u G m n hu hgu hi => dispatch_spec tgt g hg u G m n hu hgu hi)
    (fun _ _ _ _ _ h => h.2.1) rfl (fun n => main_spec n) h
  exact ⟨hv, hj, h1⟩

end Detach.Worker
