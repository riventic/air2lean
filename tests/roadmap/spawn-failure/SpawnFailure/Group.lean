import SpawnFailure.Gen
import ZigLean.Sep.Full.ThreadSpawn
import ZigLean.Sep.Full.ThreadBridge
import ZigLean.Sep.Full.ThreadFacts
import ZigLean.Sep.Full.Init

/-!
# `groupAsync`: the same result for assignment and caller fallback

`groupAsync(io, v)` (`spawn_failure.zig`, fresh Zig 0.16.0 AIR translated with
`--spawn-policy fallible`) zeroes `out`, calls `group.async(io, writeWorker, .{ &out, v })`,
awaits the group and returns `out`. Under the fallible policy `Group.async` either assigns a
child (thread 1, recorded in the group) or runs `writeWorker(&out, v)` in the caller before
returning. The caller's budget `Mem.spawnLimit` can force the fallback.

`afterAsync_spec` proves that both outcomes of the choice establish one post (`AfterAsync`):
`main` then either owns `out = v` (fallback) or has handed `out` to the recorded child
(assignment). From there `await_spec` proves the declared result contract `QM`: the result is
`.ok v` and every thread is joined. `groupAsync_spec` and `groupAsync_safe` lift this to every
schedule, every failure oracle, every initial budget and every placement: the contract is
quantified over the failure policy rather than proved for one selected outcome.

The proof is in the full-state concurrent separation logic (`docs/sep-threads.md`): each thread
owns whole stack blocks (their bytes and full extents), the threads' parts are `FOwned`, `out`
moves to the child at the spawn (`FOwned.fork`) and back at the join (`FOwned.join`); the group
table's steps keep the parts (`FOwned.keep`).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn SpawnFailure

namespace SpawnFailure.Group

-- Unification must not unfold `WP` into the program (as in `Proofs/Threads/Disjoint.lean`).
attribute [local irreducible] Proto.WP

theorem writeWorker_eq (x : Ptr) (v : BitVec 32) :
    writeWorker x v = Zig.store (α := BitVec 32) 4 x v := by
  unfold writeWorker
  simp [StateT.run'_eq, StateT.run_monadLift]

/-- A `u32` stack block `b` at `x` (address `A`) that holds `w`, with its full extent. -/
abbrev flagA (x : Ptr) (A : Nat) (b : BlockId) (w : BitVec 32) : FAssn :=
  up (bytesAt x A 4 .stack (Enc.encode w)) ⋆ bext b 4 .stack

theorem wr (v w : BitVec 32) : writeBytes (Enc.encode v) 0 (Enc.encode w) = Enc.encode w :=
  writeBytes_all (by rw [LawfulEnc.size_encode_u32, LawfulEnc.size_encode_u32])

/-- `writeWorker(x, v)` writes `v` to the `u32` block that it owns. -/
theorem writeWorker_spec {x : Ptr} {A : Nat} {b : BlockId} {w : BitVec 32} (v : BitVec 32)
    (hxb : x.block = some b) (hx0 : x.off = 0) (hA : A % 4 = 0) :
    FTTriple (flagA x A b w) (writeWorker x v) (fun _ => flagA x A b v) := by
  rw [writeWorker_eq]
  refine (FTTriple.storeAt (k := 0) (a := 4) v hxb (by simp [Ptr.add]) (by decide)
    (by rw [LawfulEnc.size_encode_u32]; decide) (by simp [hx0, hA]) (by decide)).post
    fun _ _ h => ?_
  rwa [wr] at h

/-- The pure fact of a framed load's post. -/
theorem lift_l {φ : Prop} {P Q : FAssn} {r : Res} (h : ((⟪φ⟫ ⋆ P) ⋆ Q) r) : φ ∧ (P ⋆ Q) r :=
  sep_lift.mp (sep_assoc h)

/-- The start memory, with any budget, holds the parts: no thread owns anything. -/
theorem start (σ : Placement) (lim : Option Nat) :
    ∃ rO, FOwned (fun _ => rnil) rO { ({ mem0 σ with spawnLimit := lim } : Mem) with current := 0 } := by
  have hs := Mem.init_fseq σ [] (by decide)
  exact ⟨_, FOwned.start (m := { ({ mem0 σ with spawnLimit := lim } : Mem) with current := 0 })
    rfl rfl hs.2.1 hs.2.2⟩

/-- The zero `Io.Group`. -/
def group0 : Io_Group := { token := { raw := none }, state := 0 }

theorem enc_group : (Enc.encode group0).size = 16 := by decide +kernel

/-- The two blocks of `groupAsync`: `out` and the `Io.Group`, with their block ids and
addresses. -/
structure Blks where
  x : Ptr
  g : Ptr
  kx : BlockId
  kg : BlockId
  ax : Nat
  ag : Nat

def Blks.Ok (B : Blks) : Prop :=
  B.x.block = some B.kx ∧ B.g.block = some B.kg ∧ B.x.off = 0 ∧ B.g.off = 0 ∧ B.ax % 4 = 0

/-- The `Io.Group`'s block. -/
def grpA (B : Blks) : FAssn := FAssn.ex fun bs : Array Byte =>
  ⟪bs.size = 16⟫ ⋆ (up (bytesAt B.g B.ag 16 .stack bs) ⋆ bext B.kg 16 .stack)

/-! ## Protocol -/

/-- Where `main` is: no task was assigned (`solo`, `out = w`), the task is thread 1 in the
group (`async`), `Group.await` took thread 1 from the group (`taken`), or joined it (`joined`). -/
inductive Ph where
  | solo | async | taken | joined
  deriving DecidableEq

inductive Gh where
  | none
  /-- `main` at `ph`: it owns `r`; `w` is `out` in `solo`. -/
  | main (ph : Ph) (w : BitVec 32) (r : Res) (B : Blks)
  /-- A child: it owns `r`, the `u32` at `x` (address `ax`); `done`: it wrote `v`. -/
  | kid (r : Res) (x : Ptr) (ax : Nat) (v : BitVec 32) (done : Bool)

/-- The resource that a thread owns. -/
def Gh.res : Gh → Res
  | .main _ _ r _ | .kid r _ _ _ _ => r
  | .none => rnil

/-- A child's part: its `u32` block, with `v` when it is done. -/
def KidA (x : Ptr) (ax : Nat) (v : BitVec 32) (done : Bool) : FAssn :=
  FAssn.ex fun b : BlockId => ⟪x.block = some b ∧ x.off = 0 ∧ ax % 4 = 0⟫ ⋆
    flagA x ax b (if done then v else 0)

variable (v : BitVec 32)

/-- `main`'s part at each phase. -/
def MainA (B : Blks) (w : BitVec 32) : Ph → FAssn
  | .solo => flagA B.x B.ax B.kx w ⋆ grpA B
  | .async | .taken => grpA B
  | .joined => flagA B.x B.ax B.kx v ⋆ grpA B

/-- The thread record of child `u` (an assigned or a deferred task, `gated`). -/
def KidRec (m : Mem) (u : ThreadId) (joined : Bool) : Prop :=
  ∃ gt, m.threads[u]? = some { spawner := 0, joined, gated := gt }

/-- The threads and the group at each phase of `main`. -/
def Shape (B : Blks) (G : ThreadId → Gh) (m : Mem) : Ph → Prop
  | .solo => m.threads.size = 1 ∧ m.groups = #[] ∧ ∀ u, 1 ≤ u → G u = .none
  | .async => m.threads.size = 2 ∧ KidRec m 1 false ∧ m.groups = #[(B.g, 1)] ∧
      (∃ r d, G 1 = .kid r B.x B.ax v d) ∧ ∀ u, 2 ≤ u → G u = .none
  | .taken => m.threads.size = 2 ∧ KidRec m 1 false ∧ m.groups = #[] ∧
      (∃ r d, G 1 = .kid r B.x B.ax v d) ∧ ∀ u, 2 ≤ u → G u = .none
  | .joined => m.threads.size = 2 ∧ KidRec m 1 true ∧ m.groups = #[] ∧
      (∃ r, G 1 = .kid r B.x B.ax v true) ∧ ∀ u, 2 ≤ u → G u = .none

/-- The parts of the threads: a joined thread owns nothing. -/
def ownOf (G : ThreadId → Gh) (m : Mem) (u : ThreadId) : Res :=
  if joinedB m u then rnil else (G u).res

structure Inv (G : ThreadId → Gh) (m : Mem) : Prop where
  own : ∃ rO, FOwned (ownOf G m) rO m
  kids : ∀ u r x ax w d, G u = .kid r x ax w d → KidA x ax w d r
  main : ∃ ph w r B, G 0 = .main ph w r B ∧ B.Ok ∧ MainA v B w ph r ∧ Shape v B G m ph
  t0 : m.threads[0]? = some { spawner := 0, joined := true }

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv := Inv v
  init tgt g := match tgt with
    | .writeWorker (x, w) => ∃ r ax, g = .kid r x ax w false
  fin g := ∃ r x ax w, g = .kid r x ax w true
  strict := true
  joins g := (∃ w r B, g = .main .taken w r B) ∨ ∃ r x ax w, g = .kid r x ax w false

/-- The declared result contract of `groupAsync`. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun r _ m _ => r = .ok v ∧ joinedAll 0 m

variable {v}

/-! ## Invariant bookkeeping -/

theorem inv_current {G : ThreadId → Gh} {m : Mem} (hi : Inv v G m) (t : ThreadId) :
    Inv v G { m with current := t } :=
  ⟨let ⟨rO, ho⟩ := hi.own; ⟨rO, ho.current t⟩, hi.kids, hi.main, hi.t0⟩

/-- A child that is not done was not joined: it is thread 1 in phase `async`. -/
theorem kid_live {G : ThreadId → Gh} {m : Mem} {u : ThreadId} {r x ax w}
    (hi : Inv v G m) (hu : 0 < u) (hg : G u = .kid r x ax w false) :
    joinedB m u = false ∧ u < m.threads.size ∧ u = 1 := by
  obtain ⟨ph, w', hm, B, h0, -, -, hs⟩ := hi.main
  have hne : G u ≠ .none := fun he => by rw [hg] at he; cases he
  cases ph with
  | solo => exact absurd (hs.2.2 u hu) hne
  | async | taken =>
    obtain ⟨hsz, r1, -, -, hn⟩ := hs
    have : u = 1 := by
      by_cases h2 : 2 ≤ u
      · exact absurd (hn u h2) hne
      · unfold ThreadId at *; omega
    subst this
    refine ⟨?_, by rw [hsz]; decide, rfl⟩
    obtain ⟨gt, r1⟩ := r1
    unfold joinedB; rw [r1]; rfl
  | joined =>
    obtain ⟨hsz, r1, -, ⟨h', hk⟩, hn⟩ := hs
    by_cases h1 : u = 1
    · subst h1; rw [hg] at hk; cases hk
    · exact absurd (hn u (by unfold ThreadId at *; omega)) hne

theorem ownOf_upd {G : ThreadId → Gh} {m m' : Mem} {u : ThreadId} {g : Gh}
    (ht : m'.threads = m.threads) (hj : joinedB m u = false) :
    ownOf (upd G u g) m' = upd (ownOf G m) u g.res := by
  funext w
  unfold ownOf joinedB at *
  rw [ht]
  by_cases hw : w = u
  · subst hw; simp only [upd_self]; rw [hj]; rfl
  · rw [upd_ne _ _ hw, upd_ne _ _ hw]

/-- Every thread record has the spawner `main`. -/
theorem spawner0 {G : ThreadId → Gh} {m : Mem} (hi : Inv v G m) :
    ∀ r ∈ m.threads, r.spawner = 0 := by
  obtain ⟨ph, w, hm, B, -, -, -, hs⟩ := hi.main
  refine spawners_of_getElem fun i hi' => ?_
  have hk : ∀ (j : Nat) (jn : Bool) (gt : Bool),
      m.threads[j]? = some { spawner := 0, joined := jn, gated := gt } →
      ∀ (hj : j < m.threads.size), m.threads[j].spawner = 0 := by
    intro j jn gt he hj
    rw [Array.getElem?_eq_getElem hj] at he
    simp only [Option.some.injEq] at he
    rw [he]
  cases ph with
  | solo =>
    have : i = 0 := by have := hs.1; omega
    subst this; exact hk 0 true false hi.t0 _
  | async | taken =>
    obtain ⟨hsz, ⟨gt, r1⟩, -⟩ := hs
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact hk 0 true false hi.t0 _
    · exact hk 1 false gt r1 _
  | joined =>
    obtain ⟨hsz, ⟨gt, r1⟩, -⟩ := hs
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact hk 0 true false hi.t0 _
    · exact hk 1 true gt r1 _

/-! ## The child -/

theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : (proto v).init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : Inv v G m) :
    (proto v).WP u (dispatch tgt) ((proto v).QKid u) G { m with current := u } d := by
  cases tgt with
  | writeWorker a =>
    obtain ⟨x, w⟩ := a
    obtain ⟨r, ax, rfl⟩ := hg
    obtain ⟨hj, hut, rfl⟩ := kid_live hi hu hgu
    obtain ⟨bx, hka⟩ := hi.kids 1 _ _ _ _ _ hgu
    obtain ⟨⟨hxb, hx0, hax⟩, hfl⟩ := sep_lift.mp hka
    obtain ⟨rO, ho⟩ := hi.own
    have hown : ownOf G m 1 = r := by unfold ownOf; rw [hj, hgu]; rfl
    show (proto v).WP 1 ((fun _ => ()) <$> ConcM.liftMem (writeWorker x w)) _ G _ d
    refine WP.map (WP.liftMem_fownedS (writeWorker_spec w hxb hx0 hax) (ho.current 1) rfl hut
      (by rw [hown]; exact hfl) fun _ m' rQ _ _ ho' hq hs => ?_)
    refine ⟨.kid rQ x ax w true, ?_, ⟨_, _, _, _, rfl⟩, fun _ => ?_⟩
    · refine ⟨⟨rO, ?_⟩, fun u' h' x' ax' w' d' hw => ?_, ?_, ?_⟩
      · rw [ownOf_upd hs.threads hj]; exact ho'
      · by_cases hwu : u' = 1
        · subst hwu; rw [upd_self] at hw; cases hw
          exact ⟨bx, sep_lift.mpr ⟨⟨hxb, hx0, hax⟩, hq⟩⟩
        · rw [upd_ne _ _ hwu] at hw; exact hi.kids u' _ _ _ _ _ hw
      · obtain ⟨ph, w₀, hm, B, h0, hB, hma, hsh⟩ := hi.main
        refine ⟨ph, w₀, hm, B, by rw [upd_ne _ _ (by decide)]; exact h0, hB, hma, ?_⟩
        have hnone : ∀ k, 1 < k → (∀ j, k ≤ j → G j = .none) →
            ∀ j, k ≤ j → upd G 1 (.kid rQ x ax w true) j = .none := by
          intro k hk hn j hj
          rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact hn j hj
        have hrec : ∀ jn, KidRec m 1 jn → KidRec m' 1 jn := by
          intro jn hr; unfold KidRec at hr ⊢; rw [hs.threads]; exact hr
        cases ph with
        | solo => exact absurd (hsh.2.2 1 (by decide)) (by rw [hgu]; exact fun h => by cases h)
        | async =>
          obtain ⟨hsz, r1, hgr, ⟨h', d', hk⟩, hn⟩ := hsh
          rw [hgu] at hk; cases hk
          exact ⟨by rw [hs.threads]; exact hsz, hrec _ r1, by rw [hs.groups]; exact hgr,
            ⟨rQ, true, by rw [upd_self]⟩, hnone 2 (by decide) hn⟩
        | taken =>
          obtain ⟨hsz, r1, hgr, ⟨h', d', hk⟩, hn⟩ := hsh
          rw [hgu] at hk; cases hk
          exact ⟨by rw [hs.threads]; exact hsz, hrec _ r1, by rw [hs.groups]; exact hgr,
            ⟨rQ, true, by rw [upd_self]⟩, hnone 2 (by decide) hn⟩
        | joined =>
          obtain ⟨-, -, -, ⟨h', hk⟩, -⟩ := hsh
          rw [hgu] at hk; cases hk
      · rw [hs.threads]; exact hi.t0
    · exact joinedAll_of_main (fun r hr => spawner0 hi r (by rwa [hs.threads] at hr)) (by decide)

/-! ## `main`: the two outcomes of `Group.async` -/

/-- The caller fallback that the emitter renders for `writeWorker` (`Group.async`). -/
abbrev fallback : Ptr × BitVec 32 → ConcM Tgt Unit := fun a =>
  (do let (capture0, capture1) := a; discard (Zig.ConcM.liftMem (writeWorker capture0 capture1)) : Zig.ConcM Tgt Unit)

/-- The common post of both outcomes of `Group.async` (`main` resumed, every stop's invariant):
fallback leaves `main` in `solo` with `out = v`; assignment leaves the child in the group. -/
def AfterAsync (B : Blks) (G : ThreadId → Gh) (m : Mem) : Prop :=
  m.current = 0 ∧ ∃ ph w r, (ph = .solo ∧ w = v ∨ ph = .async) ∧
    Inv v (upd G 0 (.main ph w r B)) m

/-- An assigned or a deferred task (`gt`): thread 1, recorded in the group, gets `out`. -/
theorem assign_after {B : Blks} (hB : B.Ok) {hX hGr : Res} (hdX : FHeap.Disjoint hX.heap hGr.heap)
    (hx : flagA B.x B.ax B.kx 0 hX) (hg : grpA B hGr) {G₁ : ThreadId → Gh} {m₁ m' : Mem}
    {child : ThreadId} {gt : Bool} (hi₁ : Inv v G₁ m₁)
    (hg₁ : G₁ 0 = .main .solo 0 (rsum hX hGr) B)
    (hf : ((Thread.forkWith gt).run { m₁ with current := 0 }).run = some (.ok (child, m'))) :
    AfterAsync (v := v) B (upd G₁ child (.kid hX B.x B.ax v false))
      { m' with groups := m'.groups.push (B.g, child) } := by
  obtain ⟨hxb, hgb, hx0, hg0, hax⟩ := hB
  obtain ⟨ph, w, hm, B', h0, -, -, hsh⟩ := hi₁.main
  rw [hg₁] at h0; cases h0
  obtain ⟨hsz₁, hgr₁, hn₁⟩ := hsh
  obtain ⟨rfl, hth'⟩ := fork_threads hf
  obtain ⟨rO, ho₁⟩ := hi₁.own
  have hown₁ : ownOf G₁ m₁ 0 = rsum hGr hX := by
    simp only [ownOf, joinedB, hi₁.t0, hg₁, Gh.res]; exact rsum_comm hdX
  have ho' := FOwned.fork (ho₁.current 0) (by rw [hsz₁]; decide) hown₁ hdX.symm hf
  rw [hsz₁] at ho' ⊢
  have hjb' : joinedB m' = joinedB m₁ := joinedB_fork hf
  have hjb1 : joinedB m₁ 1 = false := by
    simp [joinedB, Array.getElem?_eq_none (show m₁.threads.size ≤ 1 by omega)]
  have hfe := hf
  rw [Proto.forkWith_run] at hfe
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hfe
  obtain ⟨-, hm'⟩ := hfe
  have hcur' : m'.current = 0 := by rw [← hm']
  have hgr' : m'.groups = m₁.groups := by rw [← hm']
  refine ⟨hcur', .async, 0, hGr, .inr rfl, ?_⟩
  refine ⟨⟨rO, ?_⟩, fun u h x ax w d hu => ?_, ⟨.async, 0, hGr, B, upd_self _ _ _,
    ⟨hxb, hgb, hx0, hg0, hax⟩, hg, ?_⟩, ?_⟩
  · have e : ownOf (upd (upd G₁ 1 (.kid hX B.x B.ax v false)) 0 (.main .async 0 hGr B))
        { m' with groups := m'.groups.push (B.g, 1) } =
        upd (upd (ownOf G₁ m₁) 0 hGr) 1 hX := by
      funext u
      unfold ownOf
      rw [show joinedB { m' with groups := m'.groups.push (B.g, 1) } = joinedB m' from rfl,
        hjb']
      by_cases h0 : u = 0
      · subst h0; simp [joinedB, upd, Gh.res]
      · by_cases h1 : u = 1
        · subst h1; simp [hjb1, upd, Gh.res]
        · simp [upd, h0, h1]
    rw [e]; exact ho'.keep rfl rfl rfl rfl rfl
  · by_cases h0 : u = 0
    · subst h0; rw [upd_self] at hu; cases hu
    · rw [upd_ne _ _ h0] at hu
      by_cases h1 : u = 1
      · subst h1; rw [upd_self] at hu; cases hu
        exact ⟨B.kx, sep_lift.mpr ⟨⟨hxb, hx0, hax⟩, hx⟩⟩
      · rw [upd_ne _ _ h1, hn₁ u (by unfold ThreadId at *; omega)] at hu; cases hu
  · refine ⟨by show m'.threads.size = 2; rw [hth']; simp [hsz₁], ?_, ?_,
      ⟨hX, false, by simp [upd]⟩, fun u hu => ?_⟩
    · refine ⟨gt, ?_⟩; show m'.threads[1]? = _
      rw [hth', Array.getElem?_push, if_pos hsz₁.symm]
    · show m'.groups.push (B.g, 1) = _
      rw [hgr', hgr₁]; rfl
    · rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega),
        hn₁ u (by unfold ThreadId at *; omega)]
  · show m'.threads[0]? = _
    rw [hth', Array.getElem?_push, if_neg (by omega)]; exact hi₁.t0

/-- **Both outcomes of `Group.async` establish `AfterAsync`.** Outcome 0 assigns thread 1 and
records it in the group; it gives `out` to the child. Outcome 1 runs `writeWorker(&out, v)` in
`main`, which keeps `out`. -/
theorem afterAsync_spec {σ : Type} {s : σ} (io : Io) (B : Blks) (hB : B.Ok) (c : Nat)
    (hc : c < groupAsyncOutcomes)
    (hX hGr : Res) (hdX : FHeap.Disjoint hX.heap hGr.heap) (hx : flagA B.x B.ax B.kx 0 hX)
    (hg : grpA B hGr) {G : ThreadId → Gh} {m : Mem} {n : Nat} (hcur : m.current = 0)
    (hi : Inv v (upd G 0 (.main .solo 0 (rsum hX hGr) B)) m) :
    (proto v).WP 0 ((groupAsyncOutcomeC c B.g io (Tgt.writeWorker (B.x, v))
      (fallback (B.x, v)) : CM Tgt σ Unit).run s)
      (fun r G' m' _ => r.2 = s ∧ AfterAsync (v := v) B G' m') G m n := by
  have hB' := hB
  obtain ⟨hxb, hgb, hx0, hg0, hax⟩ := hB
  obtain ⟨ph, w, hm, B', h0, -, -, hsh⟩ := hi.main
  rw [upd_self] at h0; cases h0
  obtain ⟨hsz, hgr, hn⟩ := hsh
  unfold groupAsyncOutcomes at hc
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
  · -- Assignment: thread 1 gets `out`.
    simp only [groupAsyncOutcomeC]
    refine WP.groupAsyncC (io := io) fun k _ => ⟨.main .solo 0 (rsum hX hGr) B, hi,
      fun G₁ m₁ hg₁ hi₁ => ⟨.kid hX B.x B.ax v false, ⟨_, _, rfl⟩, fun child m' hf => ?_⟩⟩
    exact ⟨rfl, assign_after hB' hdX hx hg hi₁ hg₁ hf⟩
  · -- Fallback: `main` runs the task with `out`, which it keeps.
    simp only [groupAsyncOutcomeC, if_neg (show (1 : Nat) ≠ 0 by decide)]
    refine WP.callC ?_
    show (proto v).WP 0 ((fun _ => ()) <$> ConcM.liftMem (writeWorker B.x v)) _ G m n
    obtain ⟨rO, ho⟩ := hi.own
    have hown : ownOf (upd G 0 (.main .solo 0 (rsum hX hGr) B)) m 0 = rsum hX hGr := by
      simp [ownOf, joinedB, hi.t0, Gh.res]
    refine WP.map (WP.liftMem_fownedS ((writeWorker_spec v hxb hx0 hax).frame (R := grpA B))
      ho hcur (by rw [hsz]; decide) (by rw [hown]; exact ⟨hX, hGr, hdX, rfl, hx, hg⟩)
      fun _ m' rQ _ _ ho' hq hs => ?_)
    refine ⟨rfl, hs.current.trans hcur, .solo, v, rQ, .inl ⟨rfl, rfl⟩, ?_⟩
    have hj0 : joinedB m 0 = false := by simp [joinedB, hi.t0]
    refine ⟨⟨rO, ?_⟩, fun u h x ax w d hu => ?_, ⟨.solo, v, rQ, B, upd_self _ _ _,
      ⟨hxb, hgb, hx0, hg0, hax⟩, hq, ?_⟩, ?_⟩
    · have e := ownOf_upd (G := upd G 0 (.main .solo 0 (rsum hX hGr) B)) (g := .main .solo v rQ B)
        hs.threads hj0
      rw [upd_upd] at e
      rw [e]; exact ho'
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu
        have := hn u (by unfold ThreadId at *; omega)
        rw [upd_ne _ _ h0, hu] at this; cases this
    · refine ⟨by rw [hs.threads]; exact hsz, by rw [hs.groups]; exact hgr, fun u hu => ?_⟩
      have hu0 : u ≠ 0 := by unfold ThreadId at *; omega
      have := hn u hu
      rw [upd_ne _ _ hu0] at this ⊢; exact this
    · rw [hs.threads]; exact hi.t0
  · -- Deferred: thread 1 is recorded in the group and starts only at `Group.await`.
    simp only [groupAsyncOutcomeC, if_neg (show (2 : Nat) ≠ 0 by decide),
      if_neg (show (2 : Nat) ≠ 1 by decide)]
    refine WP.groupDeferC (io := io) fun k _ => ⟨.main .solo 0 (rsum hX hGr) B, hi,
      fun G₁ m₁ hg₁ hi₁ => ⟨.kid hX B.x B.ax v false, ⟨_, _, rfl⟩, fun _ => .inr ⟨_, _, _, _, rfl⟩,
        fun child m' hf => ?_⟩⟩
    exact ⟨rfl, assign_after hB' hdX hx hg hi₁ hg₁ hf⟩

/-! ## `main`: `Group.await` -/

/-- After `Group.await`: `main` owns `out = v` and the group, and no task is outstanding. -/
def Final (B : Blks) (G : ThreadId → Gh) (m : Mem) : Prop :=
  m.current = 0 ∧ ∃ ph r, (ph = .solo ∨ ph = .joined) ∧ Inv v (upd G 0 (.main ph v r B)) m

/-- The invariant does not depend on `current`, and the parts not on the group table. -/
theorem inv_groups {G : ThreadId → Gh} {m : Mem} {gs : Array (Ptr × ThreadId)}
    (hi : Inv v G m)
    (hm : ∃ ph w r B, G 0 = .main ph w r B ∧ B.Ok ∧ MainA v B w ph r ∧
      Shape v B G { m with groups := gs } ph) :
    Inv v G { m with groups := gs } :=
  ⟨let ⟨rO, ho⟩ := hi.own; ⟨rO, ho.keep rfl rfl rfl rfl rfl⟩, hi.kids, hm, hi.t0⟩

theorem take_run {m : Mem} {g : Ptr} {gs : Array (Ptr × ThreadId)} (hg : m.groups = gs) :
    ((Thread.groupTake g).run m).run = some (.ok ((gs.filter (·.1 == g)).map (·.2),
      { m with groups := gs.filter (·.1 != g) })) := by
  unfold Thread.groupTake
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hg]
  rfl

/-- **`Group.await` from either outcome.** After fallback the group is empty and nothing is
joined; after assignment `main` joins thread 1 and takes `out` back from it, with `v`. -/
theorem await_spec {σ : Type} {s : σ} (io : Io) (B : Blks) {G : ThreadId → Gh} {m : Mem}
    {n : Nat} (h : AfterAsync (v := v) B G m) :
    (proto v).WP 0 ((groupAwaitC B.g io : CM Tgt σ _).run s)
      (fun r G' m' _ => r = (.ok (), s) ∧ Final (v := v) B G' m') G m n := by
  obtain ⟨hc, ph, w, h, hph, hi⟩ := h
  obtain ⟨ph', w', h', B', h0, hB, hma, hsh⟩ := hi.main
  rw [upd_self] at h0; cases h0
  unfold groupAwaitC
  simp only [StateT.run_bind]
  rcases hph with ⟨rfl, hw⟩ | rfl
  · -- Fallback: the group is empty.
    subst w
    obtain ⟨hsz, hgr, hn⟩ := hsh
    have hrun := take_run (g := B.g) hgr
    refine WP.bind (WP.callMC (fun e he => by rw [hrun] at he; cases he) fun tids m₁ hr => ?_)
    rw [hrun] at hr
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨rfl, ?_⟩
    -- `main` is not an `Io` task: no cancelation point (C05).
    refine WP.bind (WP.callMC (fun e he => by rw [isTask_run] at he; cases he) fun b m₈ hr => ?_)
    rw [isTask_run] at hr
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨hb, rfl⟩ := hr
    obtain rfl : b = false := by rw [← hb]; simp [hc]
    refine ⟨rfl, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [Array.filter_empty, Array.map_empty, StateT.run_bind]
    rw [← Array.forIn_toList]
    simp only [List.forIn_nil, StateT.run_pure, pure_bind]
    refine WP.pure' ⟨rfl, hc, .solo, h, .inl rfl, inv_groups hi ⟨.solo, v, h, B, upd_self _ _ _,
      hB, hma, hsz, rfl, hn⟩⟩
  · -- Assignment: take thread 1 from the group and join it.
    obtain ⟨hsz, r1, hgr, hk1, hn⟩ := hsh
    have hrun := take_run (g := B.g) hgr
    refine WP.bind (WP.callMC (fun e he => by rw [hrun] at he; cases he) fun tids m₁ hr => ?_)
    rw [hrun] at hr
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨rfl, ?_⟩
    -- `main` is not an `Io` task: no cancelation point (C05).
    refine WP.bind (WP.callMC (fun e he => by rw [isTask_run] at he; cases he) fun b m₈ hr => ?_)
    rw [isTask_run] at hr
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨hb, rfl⟩ := hr
    obtain rfl : b = false := by rw [← hb]; simp [hc]
    refine ⟨rfl, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hft : (#[(B.g, (1 : ThreadId))].filter (·.1 == B.g)).map (·.2) = #[1] := by simp
    have hfn : #[(B.g, (1 : ThreadId))].filter (·.1 != B.g) = #[] := by simp
    rw [hft, hfn]
    have hiT : Inv v (upd G 0 (.main .taken w h B)) { m with groups := #[] } := by
      have hi' := hi
      obtain ⟨⟨rO, own⟩, kids, -, t0⟩ := hi'
      refine ⟨⟨rO, ?_⟩, fun u h₀ x ax w₀ d hu => ?_, ⟨.taken, w, h, B, upd_self _ _ _, hB, hma,
        hsz, r1, rfl, ?_, ?_⟩, t0⟩
      · have e : ownOf (upd G 0 (.main .taken w h B)) { m with groups := #[] } =
            ownOf (upd G 0 (.main .async w h B)) m := by
          funext u; unfold ownOf
          by_cases h0 : u = 0
          · subst h0; simp [joinedB, upd, Gh.res]
          · simp only [show joinedB { m with groups := #[] } = joinedB m from rfl, upd, h0,
              ↓reduceIte]
        rw [e]; exact own.keep rfl rfl rfl rfl rfl
      · by_cases h0 : u = 0
        · subst h0; rw [upd_self] at hu; cases hu
        · rw [upd_ne _ _ h0] at hu
          exact kids u h₀ x ax w₀ d (by rw [upd_ne _ _ h0]; exact hu)
      · obtain ⟨hk, d, e⟩ := hk1
        exact ⟨hk, d, by rw [upd_ne _ _ (by decide)] at e ⊢; exact e⟩
      · intro u hu
        have := hn u hu
        rw [upd_ne _ _ (by unfold ThreadId at *; omega)] at this ⊢; exact this
    rw [← Array.forIn_toList]
    simp only [List.forIn_cons, List.forIn_nil, StateT.run_bind, bind_assoc]
    refine WP.bind (WP.joinC fun k _ => ⟨.main .taken w h B, hiT, fun G₁ m₁ hg₁ hi₁ => ?_⟩)
    obtain ⟨ph, w₁, hm, B', h0, -, hma₁, hsh⟩ := hi₁.main
    rw [hg₁] at h0; cases h0
    obtain ⟨hsz₁, ⟨gt₁, r1₁⟩, hgr₁, ⟨hk, dk, hk1₁⟩, hn₁⟩ := hsh
    refine ⟨fun _ => ⟨by exact Nat.zero_lt_succ _, by rw [hsz₁]; decide, .inl ⟨_, _, _, rfl⟩, by
      have hr := r1₁
      simp [Thread.joinValid, Mem.isGated, hr, hgr₁]⟩,
      fun hfin => ⟨fun _ => join_run r1₁ rfl rfl (.inr (by simp [hgr₁])), fun m₂ hj => ?_⟩⟩
    obtain ⟨hk', x', ax', w', hf1⟩ := hfin
    rw [hf1] at hk1₁; cases hk1₁
    obtain ⟨bo, hka1⟩ := hi₁.kids 1 _ _ _ _ _ hf1
    obtain ⟨⟨hbo, -, -⟩, hka1⟩ := sep_lift.mp hka1
    rw [hB.1] at hbo; cases hbo
    simp only [↓reduceIte] at hka1
    obtain ⟨hc₂, hth₂⟩ := join_threads r1₁ hj
    obtain ⟨rO₁, ho₁⟩ := hi₁.own
    have ho₂ := FOwned.join (ho₁.current 0) (by rw [hsz₁]; decide) (by decide) hj
    have e0 : ownOf G₁ m₁ 0 = h := by simp [ownOf, joinedB, hg₁, hi₁.t0, Gh.res]
    have e1 : ownOf G₁ m₁ 1 = hk := by
      have r : m₁.threads[1]? = some { spawner := 0, joined := false, gated := gt₁ } := r1₁
      simp [ownOf, joinedB, r, hf1, Gh.res]
    have hd01 : FHeap.Disjoint h.heap hk.heap := by
      have := ho₁.disj (u := 0) (v := 1) (by rw [hsz₁]; decide) (by rw [hsz₁]; decide) (by decide)
      rwa [e0, e1] at this
    rw [e0, e1] at ho₂
    have hjb₂ : ∀ u, joinedB m₂ u = if u = 1 then true else joinedB m₁ u := by
      intro u
      unfold joinedB
      rw [hth₂]
      by_cases h1 : u = 1
      · subst h1
        rw [Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz₁]; decide)]; rfl
      · rw [Array.getElem?_setIfInBounds_ne (Ne.symm h1)]; simp [h1]
    have hgr₂ : m₂.groups = m₁.groups := by
      obtain ⟨rec, -, -, hm₂⟩ := Proto.join_eq hj
      rw [hm₂]
    refine WP.pure' ⟨rfl, hc₂, .joined, rsum h hk, .inr rfl, ⟨rO₁, ?_⟩,
      fun u h₀ x ax w₀ d hu => ?_, ⟨.joined, v, rsum h hk, B, upd_self _ _ _, hB, ?_, ?_⟩, ?_⟩
    · have e : ownOf (upd G₁ 0 (.main .joined v (rsum h hk) B)) m₂ =
          upd (upd (ownOf G₁ m₁) 1 rnil) 0 (rsum h hk) := by
        funext u
        unfold ownOf
        rw [hjb₂]
        by_cases h0 : u = 0
        · subst h0; simp [joinedB, hi₁.t0, upd, Gh.res]
        · by_cases h1 : u = 1
          · subst h1; simp [upd]
          · simp [upd, h0, h1]
      rw [e]; exact ho₂
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu; exact hi₁.kids u _ _ _ _ _ hu
    · exact ⟨hk, h, hd01.symm, rsum_comm hd01, hka1, hma₁⟩
    · refine ⟨by rw [hth₂, Array.size_setIfInBounds, hsz₁], ?_, by rw [hgr₂, hgr₁],
        ⟨hk, by rw [upd_ne _ _ (by decide)]; exact hf1⟩, fun u hu => ?_⟩
      · refine ⟨gt₁, ?_⟩; rw [hth₂, Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz₁]; decide)]
      · rw [upd_ne _ _ (by unfold ThreadId at *; omega), hn₁ u hu]
    · rw [hth₂, Array.getElem?_setIfInBounds_ne (by decide)]; exact hi₁.t0

/-- After `Group.await`, every thread that `main` spawned is joined. -/
theorem final_joined {G : ThreadId → Gh} {m : Mem} {ph : Ph} {w : BitVec 32} {r : Res}
    {B : Blks} (hph : ph = .solo ∨ ph = .joined) (hi : Inv v (upd G 0 (.main ph w r B)) m) :
    joinedAll 0 m := by
  obtain ⟨ph', w', h', B', h0, -, -, hsh⟩ := hi.main
  rw [upd_self] at h0; cases h0
  intro r hr _
  obtain ⟨i, hil, rfl⟩ := Array.mem_iff_getElem.mp hr
  have hget : m.threads[i]? = some m.threads[i] := Array.getElem?_eq_getElem hil
  rcases hph with rfl | rfl
  · have : i = 0 := by have := hsh.1; omega
    subst this; rw [Option.some.inj (hget.symm.trans hi.t0)]
  · obtain ⟨hsz, ⟨gt, r1⟩, -⟩ := hsh
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [Option.some.inj (hget.symm.trans hi.t0)]
    · rw [Option.some.inj (hget.symm.trans r1)]

/-! ## `main` -/

set_option maxHeartbeats 2000000 in
/-- **`groupAsync` meets its contract from any initial budget**, for every resource outcome. -/
theorem main_spec (σ : Placement) (io : Io) (lim : Option Nat) (d : Nat) :
    (proto v).WP 0 (groupAsync io v) (QM v) (fun _ => .none)
      { ({ mem0 σ with spawnLimit := lim } : Mem) with current := 0 } d := by
  unfold groupAsync
  obtain ⟨rO, ho₀⟩ := start σ lim
  -- `out` and the `Io.Group`.
  refine WP.bind (WP.liftMem_fownedS (FTTriple.alloc' .stack 4 4 (by decide) (by decide)) ho₀ rfl
    (by simp [mem0, Mem.ofGlobals]) ⟨rfl, rfl, rfl⟩ fun s2 m₁ r₁ _ _ ho₁ hq₁ hs₁ => ?_)
  obtain ⟨Ax, kx, hA⟩ := hq₁
  obtain ⟨⟨hxb, hx0, hAx⟩, hx⟩ := sep_lift.mp hA
  refine WP.bind (WP.liftMem_fownedS (((FTTriple.alloc' .stack 16 8 (by decide) (by decide)).frameL).pre
    fun _ h => sep_emp.mpr h) ho₁ hs₁.current (by rw [hs₁.threads]; simp [mem0, Mem.ofGlobals]) hx
    fun s4 m₂ r₂ _ _ ho₂ hq₂ hs₂ => ?_)
  obtain ⟨Ag, kg, ⟨hgb, hg0, hAg⟩, F₂⟩ := FAssn.sep_ex_ex_lift hq₂
  rw [upd_upd] at ho₂
  have htt₂ : m₂.threads = #[{ spawner := 0, joined := true }] := by
    rw [hs₂.threads, hs₁.threads]; rfl
  have hc₂ : m₂.current = 0 := hs₂.current.trans hs₁.current
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  -- `out = 0`, `group = .init`.
  refine WP.bind (WP.callMC_fownedS ((FTTriple.storeAt (k := 0) (a := 4) (0 : BitVec 32) hxb
    (by simp [Ptr.add]) (by decide) (by simp; decide) (by simp [hx0, hAx]) (by decide)).frame) ho₂ hc₂
    (by rw [htt₂]; decide) F₂ fun _ m₃ r₃ _ _ ho₃ F₃ hs₃ => ?_)
  rw [upd_upd] at ho₃
  refine WP.bind (WP.callMC_fownedS ((FTTriple.storeAt' (k := 0) (a := 8) group0 enc_group hgb
    (by simp [Ptr.add]) (by decide) (by simp; decide) (by simp [hg0, hAg]) (by decide)).frameL)
    ho₃ (hs₃.current.trans hc₂) (by rw [hs₃.threads, htt₂]; decide) F₃
    fun _ m₄ r₄ _ _ ho₄ F₄ hs₄ => ?_)
  rw [upd_upd] at ho₄
  have htt₄ : m₄.threads = #[{ spawner := 0, joined := true }] := by
    rw [hs₄.threads, hs₃.threads, htt₂]
  have hgr₄ : m₄.groups = #[] := by rw [hs₄.groups, hs₃.groups, hs₂.groups, hs₁.groups]; rfl
  have hc₄ : m₄.current = 0 := hs₄.current.trans (hs₃.current.trans hc₂)
  rw [writeBytes_all (by simp [LawfulEnc.size_encode_u32]), writeBytes_all (by simp [enc_group])] at F₄
  obtain ⟨hX, hGr, hdX, rfl, hxF, hgF⟩ := F₄
  let B : Blks := ⟨s2, s4, kx, kg, Ax, Ag⟩
  have hB : B.Ok := ⟨hxb, hgb, hx0, hg0, hAx⟩
  have hgA : grpA B hGr := ⟨_, sep_lift.mpr ⟨enc_group, hgF⟩⟩
  have hi₀ : Inv v (upd (fun _ => .none) 0 (.main .solo 0 (rsum hX hGr) B)) m₄ := by
    refine ⟨⟨rO, ?_⟩, fun u h x ax w dn hu => ?_, ⟨.solo, 0, rsum hX hGr, B, upd_self _ _ _, hB,
      ⟨hX, hGr, hdX, rfl, hxF, hgA⟩, by rw [htt₄]; rfl, hgr₄, fun u hu => ?_⟩,
      by rw [htt₄]; rfl⟩
    · have e : ownOf (upd (fun _ => .none) 0 (.main .solo 0 (rsum hX hGr) B)) m₄ =
          upd (fun _ => rnil) 0 (rsum hX hGr) := by
        funext u
        by_cases hu : u = 0
        · subst hu; simp [ownOf, joinedB, htt₄, upd, Gh.res]
        · simp only [ownOf, upd, hu, ↓reduceIte, Gh.res]; split <;> rfl
      rw [e]; exact ho₄
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu; cases hu
    · rw [upd_ne _ _ (by unfold ThreadId at *; omega)]
  -- `Group.async`: every resource outcome, then `Group.await`.
  refine WP.bind (WP.groupAsyncWithPolicyC fun k _ => ⟨.main .solo 0 (rsum hX hGr) B, hi₀,
    fun G₁ m₅ hg₁ hi₅ c hc => WP.mono ?_ (afterAsync_spec (v := v) io B hB c hc hX hGr hdX hxF
      hgA rfl (by rw [← hg₁, upd_same]; exact inv_current hi₅ 0))⟩)
  rintro ⟨⟨⟩, s'⟩ G₂ m₆ d₂ ⟨hs', hA₆⟩
  simp only at hs'
  subst hs'
  refine WP.bind (WP.mono ?_ (await_spec io B hA₆))
  rintro r G₃ m₇ d₃ ⟨rfl, hc₇, ph, h, hph, hi₇⟩
  simp only [StateT.run_bind]
  -- `out` holds `v` under both outcomes.
  obtain ⟨ph', w', h', B', h0, -, hma, -⟩ := hi₇.main
  rw [upd_self] at h0; cases h0
  have hM : (flagA B.x B.ax B.kx v ⋆ grpA B) h := by rcases hph with rfl | rfl <;> exact hma
  obtain ⟨hX₇, hG₇, hd₇, rfl, hx₇, bs, hg₇⟩ := hM
  obtain ⟨hbs, hg₇⟩ := sep_lift.mp hg₇
  have hja := final_joined hph hi₇
  obtain ⟨rO₇, ho₇⟩ := hi₇.own
  have hown : ownOf (upd G₃ 0 (.main ph v (rsum hX₇ hG₇) B)) m₇ 0 = rsum hX₇ hG₇ := by
    simp [ownOf, joinedB, hi₇.t0, Gh.res]
  have htl : 0 < m₇.threads.size := (Array.getElem?_eq_some_iff.mp hi₇.t0).1
  refine WP.bind (WP.liftM_fowned ((FTTriple.loadAt (A := Ax) (k := 0) (a := 4) (v := v) hxb
    (by simp [Ptr.add]) (by decide) (by rw [LawfulEnc.size_encode_u32]; decide)
    (by simp [hx0, hAx]) (LawfulEnc.decode_extract v)).frame
      (R := up (bytesAt s4 Ag 16 .stack bs) ⋆ bext kg 16 .stack))
    ho₇ hc₇ htl (by rw [hown]; exact ⟨hX₇, hG₇, hd₇, rfl, hx₇, hg₇⟩)
    fun r₁ m₈ r₈ _ ho₈ hq₈ hc₈ ht₈ => ?_)
  obtain ⟨hr₁, hF₈⟩ := lift_l hq₈
  subst r₁
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  -- The frees, in reverse order of allocation (MM-18): the group, then `out`.
  refine WP.bind (WP.liftMem_fowned (FTTriple.free_front (K := .stack) hgb hbs hg0 (by decide)) ho₈ hc₈
    (by rw [ht₈]; exact htl) (by rw [upd_self]; exact sep_comm hF₈)
    fun _ m₉ r₉ _ ho₉ hq₉ hc₉ ht₉ => ?_)
  rw [upd_upd] at ho₉
  refine WP.bind (WP.liftMem_fowned (FTTriple.free' (K := .stack) hxb (LawfulEnc.size_encode_u32 v) hx0
    (by decide)) ho₉ hc₉ (by rw [ht₉, ht₈]; exact htl) (by rw [upd_self]; exact hq₉)
    fun _ m₁₀ _ _ _ _ _ ht₁₀ => ?_)
  refine WP.pure' ⟨rfl, fun r hr hsp => hja r ?_ hsp⟩
  rwa [ht₁₀, ht₉, ht₈] at hr

/-! ## The results -/

/-- **`groupAsync io v` returns `.ok v` under every schedule, every resource outcome, every
initial budget and every placement**, and joins every thread it spawned. Assigned and fallback
executions both reach this declared contract (`afterAsync_spec`). -/
theorem groupAsync_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {lim : Option Nat} {fuel : Nat} {o : Nat → Nat}
    {r : Except ErrName (BitVec 32)} {m : Mem} (io : Io)
    (h : (Sched.run env dispatch fuel o (groupAsync io v) { mem0 σ with spawnLimit := lim }).run =
      some (.ok (r, m))) :
    r = .ok v ∧ joinedAll 0 m := by
  obtain ⟨_, _, hq⟩ := (proto v).run_sound env (Proto.of_available henv) dispatch (fun _ => .none) dispatch_spec
    (fun _ _ _ _ _ hq => hq.2) rfl (main_spec σ io lim) h
  exact hq

/-- **No run of `groupAsync io v` gives an error**, for every schedule, resource outcome and
budget: no race on `out` between the child and `main`, no invalid join, no use after free. -/
theorem groupAsync_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {lim : Option Nat} {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    e ≠ .stackOverflow → (Sched.run env dispatch fuel o (groupAsync io v) { mem0 σ with spawnLimit := lim }).run ≠
      some (.error e) :=
  (proto v).run_safe env (Proto.of_available henv) dispatch (fun _ => .none) rfl dispatch_spec (fun _ _ _ _ hq => hq.2) rfl
    (main_spec σ io lim)

end SpawnFailure.Group
