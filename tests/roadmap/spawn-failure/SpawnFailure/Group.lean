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
group (`async`), or thread 1 was joined (`joined`). -/
inductive Ph where
  | solo | async | joined
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
  | .async => grpA B
  | .joined => flagA B.x B.ax v ∗ grpA B

/-- The thread record of child `u`. -/
def KidRec (m : Mem) (u : ThreadId) (joined : Bool) : Prop :=
  m.threads[u]? = some { spawner := 0, joined }

/-- The threads and the group at each phase of `main`. -/
def Shape (B : Blks) (G : ThreadId → Gh) (m : Mem) : Ph → Prop
  | .solo => m.threads.size = 1 ∧ m.groups = #[] ∧ ∀ u, 1 ≤ u → G u = .none
  | .async => m.threads.size = 2 ∧ KidRec m 1 false ∧ m.groups = #[(B.g, 1)] ∧
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
  joins g := ∃ w h B, g = .main .async w h B

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
  | async =>
    obtain ⟨hsz, r1, -, -, hn⟩ := hs
    have : u = 1 := by
      by_cases h2 : 2 ≤ u
      · exact absurd (hn u h2) hne
      · unfold ThreadId at *; omega
    subst this
    refine ⟨?_, by rw [hsz]; decide, rfl⟩
    unfold joinedB; unfold KidRec at r1; rw [r1]; rfl
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
  have hk : ∀ (j : Nat) (jn : Bool), m.threads[j]? = some { spawner := 0, joined := jn } →
      ∀ (hj : j < m.threads.size), m.threads[j].spawner = 0 := by
    intro j jn he hj
    rw [Array.getElem?_eq_getElem hj] at he
    simp only [Option.some.injEq] at he
    rw [he]
  cases ph with
  | solo =>
    have : i = 0 := by have := hs.1; omega
    subst this; exact hk 0 true hi.t0 _
  | async =>
    obtain ⟨hsz, r1, -⟩ := hs
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact hk 0 true hi.t0 _
    · exact hk 1 false r1 _
  | joined =>
    obtain ⟨hsz, r1, -⟩ := hs
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact hk 0 true hi.t0 _
    · exact hk 1 true r1 _

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
          intro jn hr; unfold KidRec; rw [hs.threads]; exact hr
        cases ph with
        | solo => exact absurd (hsh.2.2 1 (by decide)) (by rw [hgu]; exact fun h => by cases h)
        | async =>
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

/-- **Both outcomes of `Group.async` establish `AfterAsync`.** Outcome 0 assigns thread 1 and
records it in the group; it gives `out` to the child. Outcome 1 runs `writeWorker(&out, v)` in
`main`, which keeps `out`. -/
theorem afterAsync_spec {σ : Type} {s : σ} (io : Io) (B : Blks) (hB : B.Ok) (c : Nat) (hc : c < 2)
    (hX hGr : Heap) (hdX : Heap.Disjoint hX hGr) (hx : flagA B.x B.ax 0 hX) (hg : grpA B hGr)
    {G : ThreadId → Gh} {m : Mem} {n : Nat} (hcur : m.current = 0)
    (hi : Inv v (upd G 0 (.main .solo 0 (hX ∪ hGr) B)) m) :
    (proto v).WP 0 ((groupAsyncOutcomeC c B.g io (Tgt.writeWorker (B.x, v))
      (fallback (B.x, v)) : CM Tgt σ Unit).run s)
      (fun r G' m' _ => r.2 = s ∧ AfterAsync (v := v) B G' m') G m n := by
  obtain ⟨hx0, hg0, hax⟩ := hB
  obtain ⟨ph, w, hm, B', h0, -, -, hsh⟩ := hi.main
  rw [upd_self] at h0; cases h0
  obtain ⟨hsz, hgr, hn⟩ := hsh
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · -- Assignment: thread 1 gets `out`.
    simp only [groupAsyncOutcomeC, if_pos rfl]
    refine WP.groupAsyncC (io := io) fun k _ => ⟨.main .solo 0 (hX ∪ hGr) B, hi, fun G₁ m₁ hg₁ hi₁ =>
      ⟨.kid hX B.x B.ax v false, ⟨_, _, rfl⟩, fun child m' hf => ?_⟩⟩
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
    rw [Proto.fork_run] at hfe
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hfe
    obtain ⟨-, hm'⟩ := hfe
    have hcur' : m'.current = 0 := by rw [← hm']
    have hgr' : m'.groups = m₁.groups := by rw [← hm']
    refine ⟨rfl, hcur', .async, 0, hGr, .inr rfl, ?_⟩
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
      · unfold KidRec; show m'.threads[1]? = _
        rw [hth', Array.getElem?_push, if_pos hsz₁.symm]
      · show m'.groups.push (B.g, 1) = _
        rw [hgr', hgr₁]; rfl
      · rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega),
          hn₁ u (by unfold ThreadId at *; omega)]
    · show m'.threads[0]? = _
      rw [hth', Array.getElem?_push, if_neg (by omega)]; exact hi₁.t0
  · -- Fallback: `main` runs the task with `out`, which it keeps.
    simp only [groupAsyncOutcomeC, if_neg (show (1 : Nat) ≠ 0 by decide)]
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

end SpawnFailure.Group
