import SpawnFailure.Gen
import ZigLean.Conc.Csl
import ZigLean.Conc.SpawnLemmas

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
schedule, every failure oracle, and every initial budget: the contract is quantified over the
failure policy rather than proved for one selected outcome.
-/

open Zig Zig.Conc Zig.Conc.Proto SpawnFailure Assn

namespace SpawnFailure.Group

theorem writeWorker_eq (x : Ptr) (v : BitVec 32) :
    writeWorker x v = Zig.store (α := BitVec 32) 4 x v := by
  unfold writeWorker
  simp [StateT.run'_eq, StateT.run_monadLift]

theorem enc_u32 (v : BitVec 32) : (Enc.encode v).size = 4 := LawfulEnc.size_encode v

/-- A `u32` at `x` (address `A`) that holds `w`. -/
def flagA (x : Ptr) (A : Nat) (w : BitVec 32) : Assn := bytesAt x A 4 .stack (Enc.encode w)

/-- `writeWorker(x, v)` writes `v` to the `u32` that it owns. -/
theorem writeWorker_spec {x : Ptr} {A : Nat} {bs : Array Byte} (v : BitVec 32)
    (hx0 : x.off = 0) (hA : A % 4 = 0) (hs : bs.size = 4) :
    TTriple (bytesAt x A 4 .stack bs) (writeWorker x v) (fun _ => flagA x A v) := by
  rw [writeWorker_eq]
  refine (TTriple.storeAt (k := 0) (a := 4) v (by simp [Ptr.add]) (by decide)
    (by rw [hs]; decide) (by simp [hx0, hA]) (by decide)).conseq (fun _ h => h) fun _ _ h => ?_
  unfold flagA
  rwa [writeBytes_all (by rw [hs, enc_u32])] at h

/-- The zero `Io.Group`. -/
def group0 : Io_Group := { token := { raw := none }, state := 0 }

theorem enc_group : (Enc.encode group0).size = 16 := by decide +kernel

/-- The two blocks of `groupAsync`: `out` and the `Io.Group`, with their addresses. -/
structure Blks where
  x : Ptr
  g : Ptr
  ax : Nat
  ag : Nat

def Blks.Ok (B : Blks) : Prop := B.x.off = 0 ∧ B.g.off = 0 ∧ B.ax % 4 = 0

/-- The `Io.Group`'s bytes. -/
def grpA (B : Blks) : Assn := fun h => ∃ bs : Array Byte, bs.size = 16 ∧ bytesAt B.g B.ag 16 .stack bs h

/-! ## Protocol -/

/-- Where `main` is: no task was assigned (`solo`, `out = w`), the task is thread 1 in the
group (`async`), `Group.await` took thread 1 from the group (`taken`), or joined it (`joined`). -/
inductive Ph where
  | solo | async | taken | joined
  deriving DecidableEq

inductive Gh where
  | none
  /-- `main` at `ph`: it owns `h`; `w` is `out` in `solo`. -/
  | main (ph : Ph) (w : BitVec 32) (h : Heap) (B : Blks)
  /-- A child: it owns `h`, the `u32` at `x` (address `ax`); `done`: it wrote `v`. -/
  | kid (h : Heap) (x : Ptr) (ax : Nat) (v : BitVec 32) (done : Bool)

def Gh.heap : Gh → Heap
  | .main _ _ h _ | .kid h _ _ _ _ => h
  | .none => Heap.empty

/-- A child's heap: its `u32`, with `v` when it is done. -/
def KidA (x : Ptr) (ax : Nat) (v : BitVec 32) (done : Bool) : Assn :=
  ⌜x.off = 0 ∧ ax % 4 = 0⌝ ∗ flagA x ax (if done then v else 0)

variable (v : BitVec 32)

/-- `main`'s heap at each phase. -/
def MainA (B : Blks) (w : BitVec 32) : Ph → Assn
  | .solo => flagA B.x B.ax w ∗ grpA B
  | .async | .taken => grpA B
  | .joined => flagA B.x B.ax v ∗ grpA B

/-- The thread record of child `u` (an assigned or a deferred task, `gated`). -/
def KidRec (m : Mem) (u : ThreadId) (joined : Bool) : Prop :=
  ∃ gt, m.threads[u]? = some { spawner := 0, joined, gated := gt }

/-- The threads and the group at each phase of `main`. -/
def Shape (B : Blks) (G : ThreadId → Gh) (m : Mem) : Ph → Prop
  | .solo => m.threads.size = 1 ∧ m.groups = #[] ∧ ∀ u, 1 ≤ u → G u = .none
  | .async => m.threads.size = 2 ∧ KidRec m 1 false ∧ m.groups = #[(B.g, 1)] ∧
      (∃ h d, G 1 = .kid h B.x B.ax v d) ∧ ∀ u, 2 ≤ u → G u = .none
  | .taken => m.threads.size = 2 ∧ KidRec m 1 false ∧ m.groups = #[] ∧
      (∃ h d, G 1 = .kid h B.x B.ax v d) ∧ ∀ u, 2 ≤ u → G u = .none
  | .joined => m.threads.size = 2 ∧ KidRec m 1 true ∧ m.groups = #[] ∧
      (∃ h, G 1 = .kid h B.x B.ax v true) ∧ ∀ u, 2 ≤ u → G u = .none

/-- A joined thread owns nothing. -/
def ownOf (G : ThreadId → Gh) (m : Mem) (u : ThreadId) : Heap :=
  if joinedB m u then Heap.empty else (G u).heap

structure Inv (G : ThreadId → Gh) (m : Mem) : Prop where
  own : Owned (ownOf G m) m
  kids : ∀ u h x ax w d, G u = .kid h x ax w d → KidA x ax w d h
  main : ∃ ph w h B, G 0 = .main ph w h B ∧ B.Ok ∧ MainA v B w ph h ∧ Shape v B G m ph
  t0 : m.threads[0]? = some { spawner := 0, joined := true }

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv := Inv v
  init tgt g := match tgt with
    | .writeWorker (x, w) => ∃ h ax, g = .kid h x ax w false
  fin g := ∃ h x ax w, g = .kid h x ax w true
  strict := true
  joins g := (∃ w h B, g = .main .taken w h B) ∨ ∃ h x ax w, g = .kid h x ax w false

/-- The declared result contract of `groupAsync`. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun r _ m _ => r = .ok v ∧ joinedAll 0 m

variable {v}

/-! ## Invariant bookkeeping -/

theorem inv_current {G : ThreadId → Gh} {m : Mem} (hi : Inv v G m) (t : ThreadId) :
    Inv v G { m with current := t } :=
  ⟨hi.own.current t, hi.kids, hi.main, hi.t0⟩

/-- A child that is not done was not joined: it is thread 1 in phase `async`. -/
theorem kid_live {G : ThreadId → Gh} {m : Mem} {u : ThreadId} {h x ax w}
    (hi : Inv v G m) (hu : 0 < u) (hg : G u = .kid h x ax w false) :
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
    ownOf (upd G u g) m' = upd (ownOf G m) u g.heap := by
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
  intro r hr
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
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
    obtain ⟨h, ax, rfl⟩ := hg
    obtain ⟨hj, hut, rfl⟩ := kid_live hi hu hgu
    have hka := hi.kids 1 _ _ _ _ _ hgu
    obtain ⟨⟨hx0, hax⟩, hfl⟩ := sep_lift.mp hka
    have hown : ownOf G m 1 = h := by unfold ownOf; rw [hj, hgu]; rfl
    show (proto v).WP 1 ((fun _ => ()) <$> ConcM.liftMem (writeWorker x w)) _ G _ d
    refine WP.map (WP.liftMem_owned (own := ownOf G m)
      (writeWorker_spec (bs := Enc.encode (0 : BitVec 32)) w hx0 hax (enc_u32 0))
      (hi.own.current 1) rfl hut (by rw [hown]; simpa [flagA] using hfl)
      fun _ m' hQ _ ho' hq hs _ _ => ?_)
    refine ⟨.kid hQ x ax w true, ?_, ⟨_, _, _, _, rfl⟩, fun _ => ?_⟩
    · refine ⟨?_, fun u' h' x' ax' w' d' hw => ?_, ?_, ?_⟩
      · rw [ownOf_upd hs.threads hj]; exact ho'
      · by_cases hwu : u' = 1
        · subst hwu; rw [upd_self] at hw; cases hw
          exact sep_lift.mpr ⟨⟨hx0, hax⟩, by simpa using hq⟩
        · rw [upd_ne _ _ hwu] at hw; exact hi.kids u' _ _ _ _ _ hw
      · obtain ⟨ph, w₀, hm, B, h0, hB, hma, hsh⟩ := hi.main
        refine ⟨ph, w₀, hm, B, by rw [upd_ne _ _ (by decide)]; exact h0, hB, hma, ?_⟩
        have hnone : ∀ k, 1 < k → (∀ j, k ≤ j → G j = .none) →
            ∀ j, k ≤ j → upd G 1 (.kid hQ x ax w true) j = .none := by
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
            ⟨hQ, true, by rw [upd_self]⟩, hnone 2 (by decide) hn⟩
        | taken =>
          obtain ⟨hsz, r1, hgr, ⟨h', d', hk⟩, hn⟩ := hsh
          rw [hgu] at hk; cases hk
          exact ⟨by rw [hs.threads]; exact hsz, hrec _ r1, by rw [hs.groups]; exact hgr,
            ⟨hQ, true, by rw [upd_self]⟩, hnone 2 (by decide) hn⟩
        | joined =>
          obtain ⟨-, -, -, ⟨h', hk⟩, -⟩ := hsh
          rw [hgu] at hk; cases hk
      · rw [hs.threads]; exact hi.t0
    · intro r hr hsp
      rw [hs.threads] at hr
      rw [spawner0 hi r hr] at hsp
      cases hsp

/-! ## `main`: the two outcomes of `Group.async` -/

/-- The caller fallback that the emitter renders for `writeWorker` (`Group.async`). -/
abbrev fallback : Ptr × BitVec 32 → ConcM Tgt Unit := fun a =>
  (do let (capture0, capture1) := a; discard (Zig.ConcM.liftMem (writeWorker capture0 capture1)) : Zig.ConcM Tgt Unit)

/-- The common post of both outcomes of `Group.async` (`main` resumed, every stop's invariant):
fallback leaves `main` in `solo` with `out = v`; assignment leaves the child in the group. -/
def AfterAsync (B : Blks) (G : ThreadId → Gh) (m : Mem) : Prop :=
  m.current = 0 ∧ ∃ ph w h, (ph = .solo ∧ w = v ∨ ph = .async) ∧
    Inv v (upd G 0 (.main ph w h B)) m

/-- An assigned or a deferred task (`gt`): thread 1, recorded in the group, gets `out`. -/
theorem assign_after {B : Blks} (hB : B.Ok) {hX hGr : Heap} (hdX : Heap.Disjoint hX hGr)
    (hx : flagA B.x B.ax 0 hX) (hg : grpA B hGr) {G₁ : ThreadId → Gh} {m₁ m' : Mem}
    {child : ThreadId} {gt : Bool} (hi₁ : Inv v G₁ m₁)
    (hg₁ : G₁ 0 = .main .solo 0 (hX ∪ hGr) B)
    (hf : ((Thread.forkWith gt).run { m₁ with current := 0 }).run = some (.ok (child, m'))) :
    AfterAsync (v := v) B (upd G₁ child (.kid hX B.x B.ax v false))
      { m' with groups := m'.groups.push (B.g, child) } := by
  obtain ⟨hx0, hg0, hax⟩ := hB
  obtain ⟨ph, w, hm, B', h0, -, -, hsh⟩ := hi₁.main
  rw [hg₁] at h0; cases h0
  obtain ⟨hsz₁, hgr₁, hn₁⟩ := hsh
  obtain ⟨rfl, hth'⟩ := fork_threads hf
  have hown₁ : ownOf G₁ m₁ 0 = hGr ∪ hX := by
    simp [ownOf, joinedB, hg₁, Gh.heap, Heap.union_comm hdX]
  have ho' := Owned.fork (hi₁.own.current 0) (by rw [hsz₁]; decide) hown₁ hdX.symm hf
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
  refine ⟨?_, fun u h x ax w d hu => ?_, ⟨.async, 0, hGr, B, upd_self _ _ _, ⟨hx0, hg0, hax⟩,
    hg, ?_⟩, ?_⟩
  · have e : ownOf (upd (upd G₁ 1 (.kid hX B.x B.ax v false)) 0 (.main .async 0 hGr B))
        { m' with groups := m'.groups.push (B.g, 1) } =
        upd (upd (ownOf G₁ m₁) 0 hGr) 1 hX := by
      funext u
      unfold ownOf
      rw [show joinedB { m' with groups := m'.groups.push (B.g, 1) } = joinedB m' from rfl,
        hjb']
      by_cases h0 : u = 0
      · subst h0; simp [joinedB, upd, Gh.heap]
      · by_cases h1 : u = 1
        · subst h1; simp [hjb1, upd, Gh.heap]
        · simp [upd, h0, h1]
    rw [e]; exact ⟨ho'.sub, ho'.disj, ho'.owns, ho'.outside, ho'.csize⟩
  · by_cases h0 : u = 0
    · subst h0; rw [upd_self] at hu; cases hu
    · rw [upd_ne _ _ h0] at hu
      by_cases h1 : u = 1
      · subst h1; rw [upd_self] at hu; cases hu
        exact sep_lift.mpr ⟨⟨hx0, hax⟩, hx⟩
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
    (hX hGr : Heap) (hdX : Heap.Disjoint hX hGr) (hx : flagA B.x B.ax 0 hX) (hg : grpA B hGr)
    {G : ThreadId → Gh} {m : Mem} {n : Nat} (hcur : m.current = 0)
    (hi : Inv v (upd G 0 (.main .solo 0 (hX ∪ hGr) B)) m) :
    (proto v).WP 0 ((groupAsyncOutcomeC c B.g io (Tgt.writeWorker (B.x, v))
      (fallback (B.x, v)) : CM Tgt σ Unit).run s)
      (fun r G' m' _ => r.2 = s ∧ AfterAsync (v := v) B G' m') G m n := by
  have hB' := hB
  obtain ⟨hx0, hg0, hax⟩ := hB
  obtain ⟨ph, w, hm, B', h0, -, -, hsh⟩ := hi.main
  rw [upd_self] at h0; cases h0
  obtain ⟨hsz, hgr, hn⟩ := hsh
  unfold groupAsyncOutcomes at hc
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
  · -- Assignment: thread 1 gets `out`.
    simp only [groupAsyncOutcomeC, if_pos rfl]
    refine WP.groupAsyncC (io := io) fun k _ => ⟨.main .solo 0 (hX ∪ hGr) B, hi, fun G₁ m₁ hg₁ hi₁ =>
      ⟨.kid hX B.x B.ax v false, ⟨_, _, rfl⟩, fun child m' hf => ?_⟩⟩
    exact ⟨rfl, assign_after hB' hdX hx hg hi₁ hg₁ hf⟩
  · -- Fallback: `main` runs the task with `out`, which it keeps.
    simp only [groupAsyncOutcomeC, if_neg (show (1 : Nat) ≠ 0 by decide), if_pos rfl]
    refine WP.callC ?_
    show (proto v).WP 0 ((fun _ => ()) <$> ConcM.liftMem (writeWorker B.x v)) _ G m n
    have hown : ownOf (upd G 0 (.main .solo 0 (hX ∪ hGr) B)) m 0 = hX ∪ hGr := by
      simp [ownOf, joinedB, Gh.heap]
    have hP : (bytesAt B.x B.ax 4 .stack (Enc.encode (0 : BitVec 32)) ∗ grpA B)
        (ownOf (upd G 0 (.main .solo 0 (hX ∪ hGr) B)) m 0) := by
      rw [hown]; exact ⟨hX, hGr, hdX, rfl, hx, hg⟩
    refine WP.map (WP.liftMem_owned
      ((writeWorker_spec (bs := Enc.encode (0 : BitVec 32)) v hx0 hax (enc_u32 0)).frame)
      hi.own hcur (by rw [hsz]; decide) hP fun _ m' hQ _ ho' hq hs _ _ => ?_)
    refine ⟨rfl, hs.current.trans hcur, .solo, v, hQ, .inl ⟨rfl, rfl⟩, ?_⟩
    have hj0 : joinedB m 0 = false := by simp [joinedB]
    refine ⟨?_, fun u h x ax w d hu => ?_, ⟨.solo, v, hQ, B, upd_self _ _ _, ⟨hx0, hg0, hax⟩, hq,
      ?_⟩, ?_⟩
    · have e := ownOf_upd (G := upd G 0 (.main .solo 0 (hX ∪ hGr) B)) (g := .main .solo v hQ B)
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
    refine WP.groupDeferC (io := io) fun k _ => ⟨.main .solo 0 (hX ∪ hGr) B, hi, fun G₁ m₁ hg₁ hi₁ =>
      ⟨.kid hX B.x B.ax v false, ⟨_, _, rfl⟩, fun _ => .inr ⟨_, _, _, _, rfl⟩,
        fun child m' hf => ?_⟩⟩
    exact ⟨rfl, assign_after hB' hdX hx hg hi₁ hg₁ hf⟩

/-! ## `main`: `Group.await` -/

/-- After `Group.await`: `main` owns `out = v` and the group, and no task is outstanding. -/
def Final (B : Blks) (G : ThreadId → Gh) (m : Mem) : Prop :=
  m.current = 0 ∧ ∃ ph h, (ph = .solo ∨ ph = .joined) ∧ Inv v (upd G 0 (.main ph v h B)) m

/-- The invariant does not depend on `current`, and `Owned` not on the group table. -/
theorem inv_groups {G : ThreadId → Gh} {m : Mem} {gs : Array (Ptr × ThreadId)}
    (hi : Inv v G m)
    (hm : ∃ ph w h B, G 0 = .main ph w h B ∧ B.Ok ∧ MainA v B w ph h ∧
      Shape v B G { m with groups := gs } ph) :
    Inv v G { m with groups := gs } :=
  ⟨⟨hi.own.sub, hi.own.disj, hi.own.owns, hi.own.outside, hi.own.csize⟩, hi.kids, hm, hi.t0⟩

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
    simp only [Array.toList, List.forIn_nil, StateT.run_pure, pure_bind]
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
      obtain ⟨own, kids, -, t0⟩ := hi'
      refine ⟨?_, fun u h₀ x ax w₀ d hu => ?_, ⟨.taken, w, h, B, upd_self _ _ _, hB, hma, hsz, r1,
        rfl, ?_, ?_⟩, t0⟩
      · have e : ownOf (upd G 0 (.main .taken w h B)) { m with groups := #[] } =
            ownOf (upd G 0 (.main .async w h B)) m := by
          funext u; unfold ownOf
          by_cases h0 : u = 0
          · subst h0; simp [joinedB, upd, Gh.heap]
          · simp only [show joinedB { m with groups := #[] } = joinedB m from rfl, upd, h0,
              ↓reduceIte]
        rw [e]; exact ⟨own.sub, own.disj, own.owns, own.outside, own.csize⟩
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
    simp only [Array.toList, List.forIn_cons, List.forIn_nil, StateT.run_bind, bind_assoc]
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
    obtain ⟨-, hka1⟩ := sep_lift.mp (hi₁.kids 1 _ _ _ _ _ hf1)
    simp only [↓reduceIte] at hka1
    obtain ⟨hc₂, hth₂⟩ := join_threads r1₁ hj
    have ho₂ := Owned.join (hi₁.own.current 0) (by rw [hsz₁]; decide) (by decide) hj
    have e0 : ownOf G₁ m₁ 0 = h := by simp [ownOf, joinedB, hg₁, Gh.heap]
    have e1 : ownOf G₁ m₁ 1 = hk := by
      have r : m₁.threads[1]? = some { spawner := 0, joined := false, gated := gt₁ } := r1₁
      simp [ownOf, joinedB, r, hf1, Gh.heap]
    have hd01 : Heap.Disjoint h hk := by
      have := hi₁.own.disj 0 1 (by decide); rwa [e0, e1] at this
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
    refine WP.pure' ⟨rfl, hc₂, .joined, h ∪ hk, .inr rfl, ?_, fun u h₀ x ax w₀ d hu => ?_,
      ⟨.joined, v, h ∪ hk, B, upd_self _ _ _, hB, ?_, ?_⟩, ?_⟩
    · have e : ownOf (upd G₁ 0 (.main .joined v (h ∪ hk) B)) m₂ =
          upd (upd (ownOf G₁ m₁) 0 (h ∪ hk)) 1 Heap.empty := by
        funext u
        unfold ownOf
        rw [hjb₂]
        by_cases h0 : u = 0
        · subst h0; simp [joinedB, upd, Gh.heap]
        · by_cases h1 : u = 1
          · subst h1; simp [upd]
          · simp [upd, h0, h1]
      rw [e]; exact ho₂
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu; exact hi₁.kids u _ _ _ _ _ hu
    · exact ⟨hk, h, hd01.symm, Heap.union_comm hd01, hka1, hma₁⟩
    · refine ⟨by rw [hth₂, Array.size_setIfInBounds, hsz₁], ?_, by rw [hgr₂, hgr₁],
        ⟨hk, by rw [upd_ne _ _ (by decide)]; exact hf1⟩, fun u hu => ?_⟩
      · refine ⟨gt₁, ?_⟩; rw [hth₂, Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz₁]; decide)]
      · rw [upd_ne _ _ (by unfold ThreadId at *; omega), hn₁ u hu]
    · rw [hth₂, Array.getElem?_setIfInBounds_ne (by decide)]; exact hi₁.t0

/-- After `Group.await`, every thread that `main` spawned is joined. -/
theorem final_joined {G : ThreadId → Gh} {m : Mem} {ph : Ph} {w : BitVec 32} {h : Heap}
    {B : Blks} (hph : ph = .solo ∨ ph = .joined) (hi : Inv v (upd G 0 (.main ph w h B)) m) :
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

section Steps
variable {γ σ α : Type} {P : Proto Tgt γ} {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat}
  {own : ThreadId → Heap}

/-- `WP.liftMem_upd`, which also keeps the group table. -/
theorem liftMem_upd' {x : MemM α} {Pa : Assn} {Qa : α → Assn} {h : Heap}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop} (ht : TTriple Pa x Qa) (ho : Owned (upd own t h) m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa h)
    (k : ∀ a m' h', Owned (upd own t h') m' → Qa a h' → m'.current = t →
      m'.threads = m.threads → m'.groups = m.groups → Q a G m' n) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n :=
  WP.liftMem_owned ht ho hc htl (by rw [upd_self]; exact hp) fun a m' h' _ ho' hq hs _ _ =>
    k a m' h' (by rw [upd_upd] at ho'; exact ho') hq (hs.current.trans hc) hs.threads hs.groups

theorem liftM_upd' {x : MemM α} {s : σ} {Pa : Assn} {Qa : α → Assn} {h : Heap}
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop} (ht : TTriple Pa x Qa)
    (ho : Owned (upd own t h) m) (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa h)
    (k : ∀ a m' h', Owned (upd own t h') m' → Qa a h' → m'.current = t →
      m'.threads = m.threads → m'.groups = m.groups → Q (a, s) G m' n) :
    P.WP t ((_root_.liftM x : CM Tgt σ α).run s) Q G m n := by
  show P.WP t (ConcM.liftMem x >>= fun a => pure (a, s)) Q G m n
  exact WP.bind (liftMem_upd' ht ho hc htl hp fun a m' h' ho' hq hc' ht' hg' =>
    WP.pure' (k a m' h' ho' hq hc' ht' hg'))

end Steps

theorem decode_u32 (w : BitVec 32) :
    Enc.decode ((Enc.encode w).extract 0 (0 + Enc.size (BitVec 32))) =
      (pure w : Result (BitVec 32)) := by
  rw [show 0 + Enc.size (BitVec 32) = (Enc.encode w).size from (enc_u32 w).symm,
    Array.extract_size]
  exact LawfulEnc.decode_encode w

/-- `free` of the first block. -/
theorem free_front {R : Assn} {p : Ptr} {A S : Nat} {bs : Array Byte} (hS : bs.size = S)
    (h0 : p.off = 0) (hpos : 0 < S) :
    TTriple (bytesAt p A S .stack bs ∗ R) (Zig.free p) (fun _ => R) :=
  (TTriple.free hS h0 hpos).frame.conseq (fun _ h => h) fun _ _ h => sep_emp.mp (sep_comm h)

set_option maxHeartbeats 1000000 in
/-- **`groupAsync` meets its contract from any initial budget**, for every resource outcome. -/
theorem main_spec (σ : Placement) (io : Io) (lim : Option Nat) (d : Nat) :
    (proto v).WP 0 (groupAsync io v) (QM v) (fun _ => .none)
      { ({ mem0 σ with spawnLimit := lim } : Mem) with current := 0 } d := by
  unfold groupAsync
  have ho₀ : Owned (upd (fun _ => Heap.empty) 0 Heap.empty)
      { ({ mem0 σ with spawnLimit := lim } : Mem) with current := 0 } := by
    rw [show upd (fun _ => Heap.empty) 0 Heap.empty = (fun _ => Heap.empty) from upd_same _ _]
    exact Owned.start rfl rfl
  -- `out` and the `Io.Group`.
  refine WP.bind (liftMem_upd' (TTriple.alloc .stack 4 4 (by decide)) ho₀ rfl
    (by show 0 < (mem0 σ).threads.size; simp [mem0, Mem.ofGlobals]) rfl fun s2 m₁ h₁ ho₁ hq₁ hc₁ ht₁ hg₁ => ?_)
  obtain ⟨Ax, hA⟩ := hq₁
  obtain ⟨⟨hx0, hAx⟩, hx⟩ := sep_lift.mp hA
  refine WP.bind (liftMem_upd' (alloc_next 16 8 (by decide)) ho₁ hc₁
    (by rw [ht₁]; show 0 < (mem0 σ).threads.size; simp [mem0, Mem.ofGlobals]) hx
    fun s4 m₂ h₂ ho₂ hq₂ hc₂ ht₂ hg₂ => ?_)
  obtain ⟨Ag, ⟨hg0, hAg⟩, F₂⟩ := sep_ex_lift hq₂
  have htt₂ : m₂.threads = #[{ spawner := 0, joined := true }] := by rw [ht₂, ht₁]; rfl
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  -- `out = 0`, `group = .init`.
  refine WP.bind (liftM_upd' ((TTriple.storeAt (k := 0) (a := 4) (0 : BitVec 32)
    (by simp [Ptr.add]) (by decide) (by simp; decide) (by simp [hx0, hAx]) (by decide)).frame) ho₂ hc₂
    (by rw [htt₂]; decide) F₂ fun _ m₃ h₃ ho₃ F₃ hc₃ ht₃ hg₃ => ?_)
  refine WP.bind (liftM_upd' ((TTriple.storeAt' (k := 0) (a := 8) group0 enc_group
    (by simp [Ptr.add]) (by decide) (by simp; decide) (by simp [hg0, hAg]) (by decide)).frameL)
    ho₃ hc₃ (by rw [ht₃, htt₂]; decide) F₃ fun _ m₄ h₄ ho₄ F₄ hc₄ ht₄ hg₄ => ?_)
  have htt₄ : m₄.threads = #[{ spawner := 0, joined := true }] := by rw [ht₄, ht₃, htt₂]
  have hgr₄ : m₄.groups = #[] := by rw [hg₄, hg₃, hg₂, hg₁]; rfl
  rw [writeBytes_all (by simp [enc_u32]), writeBytes_all (by simp [enc_group])] at F₄
  obtain ⟨hX, hGr, hdX, rfl, hxF, hgF⟩ := F₄
  let B : Blks := ⟨s2, s4, Ax, Ag⟩
  have hB : B.Ok := ⟨hx0, hg0, hAx⟩
  have hi₀ : Inv v (upd (fun _ => .none) 0 (.main .solo 0 (hX ∪ hGr) B)) m₄ := by
    refine ⟨?_, fun u h x ax w dn hu => ?_, ⟨.solo, 0, hX ∪ hGr, B, upd_self _ _ _, hB,
      ⟨hX, hGr, hdX, rfl, hxF, _, enc_group, hgF⟩, by rw [htt₄]; rfl, hgr₄, fun u hu => ?_⟩,
      by rw [htt₄]; rfl⟩
    · have e : ownOf (upd (fun _ => .none) 0 (.main .solo 0 (hX ∪ hGr) B)) m₄ =
          upd (fun _ => Heap.empty) 0 (hX ∪ hGr) := by
        funext u
        by_cases hu : u = 0
        · subst hu; simp [ownOf, joinedB, upd, Gh.heap]
        · simp only [ownOf, upd, hu, ↓reduceIte, Gh.heap]; split <;> rfl
      rw [e]; exact ho₄
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu; cases hu
    · rw [upd_ne _ _ (by unfold ThreadId at *; omega)]
  -- `Group.async`: every resource outcome, then `Group.await`.
  refine WP.bind (WP.groupAsyncWithPolicyC fun k _ => ⟨.main .solo 0 (hX ∪ hGr) B, hi₀,
    fun G₁ m₅ hg₁ hi₅ c hc => WP.mono ?_ (afterAsync_spec (v := v) io B hB c hc hX hGr hdX hxF
      ⟨_, enc_group, hgF⟩ rfl (by rw [← hg₁, upd_same]; exact inv_current hi₅ 0))⟩)
  rintro ⟨⟨⟩, s'⟩ G₂ m₆ d₂ ⟨hs', hA₆⟩
  simp only at hs'
  subst hs'
  refine WP.bind (WP.mono ?_ (await_spec io B hA₆))
  rintro r G₃ m₇ d₃ ⟨rfl, hc₇, ph, h, hph, hi₇⟩
  simp only [StateT.run_bind]
  -- `out` holds `v` under both outcomes.
  obtain ⟨ph', w', h', B', h0, -, hma, -⟩ := hi₇.main
  rw [upd_self] at h0; cases h0
  have hM : (flagA B.x B.ax v ∗ grpA B) h := by rcases hph with rfl | rfl <;> exact hma
  obtain ⟨hX₇, hG₇, hd₇, rfl, hx₇, bs, hbs, hg₇⟩ := hM
  have hja := final_joined hph hi₇
  have hown : ownOf (upd G₃ 0 (.main ph v (hX₇ ∪ hG₇) B)) m₇ 0 = hX₇ ∪ hG₇ := by
    simp [ownOf, joinedB, Gh.heap]
  have htl : 0 < m₇.threads.size := by
    have := hi₇.t0; exact (Array.getElem?_eq_some_iff.mp this).1
  refine WP.bind (WP.liftM_owned ((TTriple.loadAt (p := s2) (A := Ax) (S := 4) (K := .stack)
    (k := 0) (a := 4) (v := v) (by simp [Ptr.add])
    (by decide) (by rw [enc_u32]; decide) (by simp [hx0, hAx]) (decode_u32 v)).frame_eq)
    hi₇.own hc₇ htl (by rw [hown]; exact ⟨hX₇, hG₇, hd₇, rfl, hx₇, hg₇⟩)
    fun r₁ m₈ h₈ _ ho₈ hq₈ hs₈ _ _ => ?_)
  have hF₈ := (sep_lift.mp hq₈).2
  have hr₁ := (sep_lift.mp hq₈).1
  subst r₁
  simp only [StateT.run_pure, pure_bind]
  refine WP.pure' ?_
  -- The frees.
  refine WP.bind (WP.liftMem_upd (free_front (R := bytesAt B.g B.ag 16 .stack bs) (enc_u32 v) hx0
    (by decide)) ho₈ (hs₈.current.trans hc₇) (by rw [hs₈.threads]; exact htl) hF₈
    fun _ m₉ h₉ ho₉ hq₉ hc₉ ht₉ => ?_)
  refine WP.bind (WP.liftMem_upd (TTriple.free hbs hg0 (by decide)) ho₉ hc₉
    (by rw [ht₉, hs₈.threads]; exact htl) hq₉ fun _ m₁₀ _ _ _ _ ht₁₀ => ?_)
  refine WP.pure' ⟨rfl, fun r hr hsp => hja r ?_ hsp⟩
  rwa [ht₁₀, ht₉, hs₈.threads] at hr

/-! ## The results -/

/-- **`groupAsync io v` returns `.ok v` under every schedule, every resource outcome and every
initial budget**, and joins every thread it spawned. Assigned and fallback executions both
reach this declared contract (`afterAsync_spec`). -/
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
    (Sched.run env dispatch fuel o (groupAsync io v) { mem0 σ with spawnLimit := lim }).run ≠
      some (.error e) :=
  (proto v).run_safe env (Proto.of_available henv) dispatch (fun _ => .none) rfl dispatch_spec (fun _ _ _ _ hq => hq.2) rfl
    (main_spec σ io lim)

end SpawnFailure.Group
