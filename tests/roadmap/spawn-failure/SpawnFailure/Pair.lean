import SpawnFailure.Group
import ZigLean.Conc.Transfer

/-!
# `threadPair`: failed assignments leave ownership with the caller

`threadPair(v)` (`spawn_failure.zig`, fresh Zig 0.16.0 AIR translated with
`--spawn-policy fallible`) zeroes `left` and `right`, spawns `writeWorker(&left, v)`, then
`writeWorker(&right, v +% 1)`, joins both and returns `left +% right`. A failed first spawn
returns its error; a failed second spawn joins the first child (`errdefer`) and returns its error.

Each spawn hands its child exactly the C01 grant of the generated `Tgt.captures`
(`[.ptr out, .value]`, `Capture.grant`). At a failed assignment `WP.spawnFailureRetains` keeps
the caller's split and grant unchanged: `main` still owns the refused capture and frees it
itself, which strict mode only permits for a region that no running child holds.

`threadPair_spec` and `threadPair_safe` hold for every schedule, every resource outcome and every
initial budget: the result is the sum or one of the declared spawn errors, and every child is
joined.
-/

open Zig Zig.Conc Zig.Conc.Proto SpawnFailure Assn
open SpawnFailure.Group (flagA KidA enc_u32 writeWorker_spec decode_u32 free_front)

namespace SpawnFailure.Pair

/-- How a spawn of `writeWorker(x, w)` hands over its captured pointer: the `u32` at `x`. -/
def transfer (x : Ptr) (ax : Nat) (w : BitVec 32) : Ptr → Transfer :=
  fun _ => .owned (KidA x ax w false)

theorem captures (x : Ptr) (w : BitVec 32) :
    Tgt.captures (.writeWorker (x, w)) = [.ptr x, .value] := rfl

/-- A child's starting heap is exactly the grant of its captured fields. -/
theorem grant_iff {x : Ptr} {ax : Nat} {w : BitVec 32} {h : Heap} :
    Capture.grant (transfer x ax w) (Tgt.captures (.writeWorker (x, w))) h ↔ KidA x ax w false h := by
  rw [captures]
  constructor
  · rintro ⟨⟨h₁, h₂, hd, rfl, h1, h2⟩, -⟩
    have h2' : Capture.cellsOf (transfer x ax w) [] h₂ := by
      obtain ⟨h₃, h₄, -, rfl, h3, h4⟩ := h2
      have e3 : h₃ = Heap.empty := h3
      have e4 : h₄ = Heap.empty := h4
      subst e3; subst e4; simp; rfl
    have e2 : h₂ = Heap.empty := h2'
    subst e2
    simpa [Capture.cells, transfer, Transfer.cells] using h1
  · intro hk
    refine ⟨?_, fun c hc => ?_⟩
    · have := Capture.cellsOf_cons (mode := transfer x ax w) (c := .ptr x) (cs := [.value])
        (Heap.disjoint_empty h).symm.symm hk (Capture.cellsOf_value Capture.cellsOf_nil)
      simpa using this
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> trivial

/-- The two blocks of `threadPair`, with their addresses. -/
structure Blks where
  l : Ptr
  r : Ptr
  al : Nat
  ar : Nat

def Blks.Ok (B : Blks) : Prop := B.l.off = 0 ∧ B.r.off = 0 ∧ B.al % 4 = 0 ∧ B.ar % 4 = 0

/-- Where `main` is: before the first spawn (`pre`), after one (`one`) or two (`two`) spawns,
after the join of child 1 (`j1`) or both (`both`), or after the errdefer join that follows a
failed second spawn (`back`). -/
inductive Ph where
  | pre | one | two | j1 | both | back
  deriving DecidableEq

inductive Gh where
  | none
  | main (ph : Ph) (h : Heap) (B : Blks)
  /-- A child: it owns `h`, the `u32` at `x` (address `ax`); `done`: it wrote `w`. -/
  | kid (h : Heap) (x : Ptr) (ax : Nat) (w : BitVec 32) (done : Bool)

def Gh.heap : Gh → Heap
  | .main _ h _ | .kid h _ _ _ _ => h
  | .none => Heap.empty

variable (v : BitVec 32)

/-- `main`'s heap at each phase. -/
def MainA (B : Blks) : Ph → Assn
  | .pre => flagA B.l B.al 0 ∗ flagA B.r B.ar 0
  | .one => flagA B.r B.ar 0
  | .two => emp
  | .j1 => flagA B.l B.al v
  | .both => flagA B.l B.al v ∗ flagA B.r B.ar (addWrap v 1)
  | .back => flagA B.l B.al v ∗ flagA B.r B.ar 0

/-- Thread `u` is child 1 (`left`, `v`) or child 2 (`right`, `v +% 1`). -/
def IsKid (B : Blks) (G : ThreadId → Gh) (u : ThreadId) (done : Option Bool) : Prop :=
  ∃ h d, (done = none ∨ done = some d) ∧
    G u = if u = 1 then .kid h B.l B.al v d else .kid h B.r B.ar (addWrap v 1) d

def KidRec (m : Mem) (u : ThreadId) (joined : Bool) : Prop :=
  m.threads[u]? = some { spawner := 0, joined }

def Shape (B : Blks) (G : ThreadId → Gh) (m : Mem) : Ph → Prop
  | .pre => m.threads.size = 1 ∧ ∀ u, 1 ≤ u → G u = .none
  | .one => m.threads.size = 2 ∧ KidRec m 1 false ∧ IsKid v B G 1 none ∧ ∀ u, 2 ≤ u → G u = .none
  | .two => m.threads.size = 3 ∧ KidRec m 1 false ∧ KidRec m 2 false ∧ IsKid v B G 1 none ∧
      IsKid v B G 2 none ∧ ∀ u, 3 ≤ u → G u = .none
  | .j1 => m.threads.size = 3 ∧ KidRec m 1 true ∧ KidRec m 2 false ∧ IsKid v B G 1 (some true) ∧
      IsKid v B G 2 none ∧ ∀ u, 3 ≤ u → G u = .none
  | .both => m.threads.size = 3 ∧ KidRec m 1 true ∧ KidRec m 2 true ∧
      IsKid v B G 1 (some true) ∧ IsKid v B G 2 (some true) ∧ ∀ u, 3 ≤ u → G u = .none
  | .back => m.threads.size = 2 ∧ KidRec m 1 true ∧ IsKid v B G 1 (some true) ∧
      ∀ u, 2 ≤ u → G u = .none

def ownOf (G : ThreadId → Gh) (m : Mem) (u : ThreadId) : Heap :=
  if joinedB m u then Heap.empty else (G u).heap

structure Inv (G : ThreadId → Gh) (m : Mem) : Prop where
  own : Owned (ownOf G m) m
  kids : ∀ u h x ax w d, G u = .kid h x ax w d → KidA x ax w d h
  main : ∃ ph h B, G 0 = .main ph h B ∧ B.Ok ∧ MainA v B ph h ∧ Shape v B G m ph
  t0 : m.threads[0]? = some { spawner := 0, joined := true }

/-- The protocol, in strict mode. A child starts with exactly the grant of its captures. -/
def proto : Proto Tgt Gh where
  inv := Inv v
  init tgt g := match tgt with
    | .writeWorker (x, w) => ∃ h ax, g = .kid h x ax w false ∧
        Capture.grant (transfer x ax w) (Tgt.captures (.writeWorker (x, w))) h
  fin g := ∃ h x ax w, g = .kid h x ax w true
  strict := true
  joins g := ∃ h B, g = .main .one h B ∨ g = .main .two h B ∨ g = .main .j1 h B

/-- The declared result contract: the sum, or a declared spawn error; every child joined. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun r _ m _ => (r = .ok (addWrap v (addWrap v 1)) ∨ ∃ e ∈ spawnErrors, r = .error e) ∧
    joinedAll 0 m

variable {v}

/-! ## The children -/

theorem kid_live {G : ThreadId → Gh} {m : Mem} {u : ThreadId} {h x ax w}
    (hi : Inv v G m) (hu : 0 < u) (hg : G u = .kid h x ax w false) :
    joinedB m u = false ∧ u < m.threads.size ∧ (u = 1 ∨ u = 2) := by
  obtain ⟨ph, hm, B, h0, -, -, hs⟩ := hi.main
  have hne : G u ≠ .none := fun he => by rw [hg] at he; cases he
  have jb : ∀ jn, KidRec m u jn → jn = false → joinedB m u = false := by
    intro jn hr hj; unfold joinedB; rw [hr]; simp [hj]
  have hdone : ∀ (k : ThreadId), IsKid v B G k (some true) → u ≠ k := by
    rintro k ⟨h', d, hd, hk⟩ rfl
    rw [hg] at hk
    rcases hd with hd | hd
    · cases hd
    · cases hd; split at hk <;> cases hk
  cases ph with
  | pre => exact absurd (hs.2 u hu) hne
  | one =>
    obtain ⟨hsz, r1, -, hn⟩ := hs
    have : u = 1 := by
      by_cases h2 : 2 ≤ u
      · exact absurd (hn u h2) hne
      · unfold ThreadId at *; omega
    subst this
    exact ⟨jb _ r1 rfl, by rw [hsz]; decide, .inl rfl⟩
  | two =>
    obtain ⟨hsz, r1, r2, -, -, hn⟩ := hs
    by_cases h1 : u = 1
    · subst h1; exact ⟨jb _ r1 rfl, by rw [hsz]; decide, .inl rfl⟩
    · by_cases h2 : u = 2
      · subst h2; exact ⟨jb _ r2 rfl, by rw [hsz]; decide, .inr rfl⟩
      · exact absurd (hn u (by unfold ThreadId at *; omega)) hne
  | j1 =>
    obtain ⟨hsz, -, r2, k1, -, hn⟩ := hs
    have h1 := hdone 1 k1
    by_cases h2 : u = 2
    · subst h2; exact ⟨jb _ r2 rfl, by rw [hsz]; decide, .inr rfl⟩
    · exact absurd (hn u (by unfold ThreadId at *; omega)) hne
  | both =>
    obtain ⟨-, -, -, k1, k2, hn⟩ := hs
    have h1 := hdone 1 k1
    have h2 := hdone 2 k2
    exact absurd (hn u (by unfold ThreadId at *; omega)) hne
  | back =>
    obtain ⟨-, -, k1, hn⟩ := hs
    have h1 := hdone 1 k1
    exact absurd (hn u (by unfold ThreadId at *; omega)) hne

theorem ownOf_upd {G : ThreadId → Gh} {m m' : Mem} {u : ThreadId} {g : Gh}
    (ht : m'.threads = m.threads) (hj : joinedB m u = false) :
    ownOf (upd G u g) m' = upd (ownOf G m) u g.heap := by
  funext w
  unfold ownOf joinedB at *
  rw [ht]
  by_cases hw : w = u
  · subst hw; simp only [upd_self]; rw [hj]; rfl
  · rw [upd_ne _ _ hw, upd_ne _ _ hw]

theorem spawner0 {G : ThreadId → Gh} {m : Mem} (hi : Inv v G m) :
    ∀ r ∈ m.threads, r.spawner = 0 := by
  obtain ⟨ph, hm, B, -, -, -, hs⟩ := hi.main
  have ht0 := hi.t0
  intro r hr
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  have hk : ∀ (j : Nat) (jn : Bool), m.threads[j]? = some { spawner := 0, joined := jn } →
      ∀ (hj : j < m.threads.size), m.threads[j].spawner = 0 := by
    intro j jn he hj
    rw [Array.getElem?_eq_getElem hj] at he
    simp only [Option.some.injEq] at he
    rw [he]
  cases ph with
  | pre =>
    have : i = 0 := by have := hs.1; omega
    subst this; exact hk 0 true ht0 _
  | one | back =>
    obtain ⟨hsz, r1, -⟩ := hs
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact hk 0 true ht0 _
    · exact hk 1 _ r1 _
  | two | j1 | both =>
    obtain ⟨hsz, r1, r2, -⟩ := hs
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hk 0 true ht0 _
    · exact hk 1 _ r1 _
    · exact hk 2 _ r2 _

theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : (proto v).init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : Inv v G m) :
    (proto v).WP u (dispatch tgt) ((proto v).QKid u) G { m with current := u } d := by
  cases tgt with
  | writeWorker a =>
    obtain ⟨x, w⟩ := a
    obtain ⟨h, ax, rfl, -⟩ := hg
    obtain ⟨hj, hut, h12⟩ := kid_live hi hu hgu
    have hka := hi.kids u _ _ _ _ _ hgu
    obtain ⟨⟨hx0, hax⟩, hfl⟩ := sep_lift.mp hka
    have hown : ownOf G m u = h := by unfold ownOf; rw [hj, hgu]; rfl
    show (proto v).WP u ((fun _ => ()) <$> ConcM.liftMem (writeWorker x w)) _ G _ d
    refine WP.map (WP.liftMem_owned (own := ownOf G m)
      (writeWorker_spec (bs := Enc.encode (0 : BitVec 32)) w hx0 hax (enc_u32 0))
      (hi.own.current u) rfl hut (by rw [hown]; simpa [flagA] using hfl)
      fun _ m' hQ _ ho' hq hs _ _ => ?_)
    refine ⟨.kid hQ x ax w true, ?_, ⟨_, _, _, _, rfl⟩, fun _ => ?_⟩
    · refine ⟨?_, fun u' h' x' ax' w' d' hw => ?_, ?_, ?_⟩
      · rw [ownOf_upd hs.threads hj]; exact ho'
      · by_cases hwu : u' = u
        · subst hwu; rw [upd_self] at hw; cases hw
          exact sep_lift.mpr ⟨⟨hx0, hax⟩, by simpa using hq⟩
        · rw [upd_ne _ _ hwu] at hw; exact hi.kids u' _ _ _ _ _ hw
      · obtain ⟨ph, hm, B, h0, hB, hma, hsh⟩ := hi.main
        refine ⟨ph, hm, B, by rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact h0, hB, hma,
          ?_⟩
        have hkid : ∀ k dn, IsKid v B G k dn → k ≠ u ∨ dn = none →
            IsKid v B (upd G u (.kid hQ x ax w true)) k dn := by
          intro k dn ⟨h', d', hd', hk⟩ hw
          by_cases hku : k = u
          · subst hku
            rcases hw with hw | rfl
            · exact absurd rfl hw
            · refine ⟨hQ, true, .inl rfl, ?_⟩
              rw [upd_self]
              rw [hgu] at hk
              by_cases h1 : k = 1
              · simp only [h1, ↓reduceIte] at hk ⊢; cases hk; rfl
              · simp only [h1, ↓reduceIte] at hk ⊢; cases hk; rfl
          · exact ⟨h', d', hd', by rw [upd_ne _ _ hku]; exact hk⟩
        have hnone : ∀ k, (∀ j, k ≤ j → G j = .none) →
            ∀ j, k ≤ j → upd G u (.kid hQ x ax w true) j = .none := by
          intro k hk j hkj
          by_cases hju : j = u
          · subst hju; have := hk j hkj; rw [hgu] at this; cases this
          · rw [upd_ne _ _ hju]; exact hk j hkj
        have hrec : ∀ k jn, KidRec m k jn → KidRec m' k jn := by
          intro k jn hr; unfold KidRec; rw [hs.threads]; exact hr
        have hdone : ∀ k, IsKid v B G k (some true) → k ≠ u := by
          rintro k ⟨h', d', hd', hk⟩ rfl
          rw [hgu] at hk
          rcases hd' with hd' | hd'
          · cases hd'
          · cases hd'; split at hk <;> cases hk
        cases ph with
        | pre => exact ⟨by rw [hs.threads]; exact hsh.1, hnone 1 hsh.2⟩
        | one =>
          obtain ⟨hsz, r1, k1, hn⟩ := hsh
          exact ⟨by rw [hs.threads]; exact hsz, hrec _ _ r1, hkid 1 _ k1 (.inr rfl), hnone 2 hn⟩
        | two =>
          obtain ⟨hsz, r1, r2, k1, k2, hn⟩ := hsh
          exact ⟨by rw [hs.threads]; exact hsz, hrec _ _ r1, hrec _ _ r2, hkid 1 _ k1 (.inr rfl),
            hkid 2 _ k2 (.inr rfl), hnone 3 hn⟩
        | j1 =>
          obtain ⟨hsz, r1, r2, k1, k2, hn⟩ := hsh
          exact ⟨by rw [hs.threads]; exact hsz, hrec _ _ r1, hrec _ _ r2,
            hkid 1 _ k1 (.inl (hdone 1 k1)), hkid 2 _ k2 (.inr rfl), hnone 3 hn⟩
        | both =>
          obtain ⟨hsz, r1, r2, k1, k2, hn⟩ := hsh
          exact ⟨by rw [hs.threads]; exact hsz, hrec _ _ r1, hrec _ _ r2,
            hkid 1 _ k1 (.inl (hdone 1 k1)), hkid 2 _ k2 (.inl (hdone 2 k2)), hnone 3 hn⟩
        | back =>
          obtain ⟨hsz, r1, k1, hn⟩ := hsh
          exact ⟨by rw [hs.threads]; exact hsz, hrec _ _ r1, hkid 1 _ k1 (.inl (hdone 1 k1)),
            hnone 2 hn⟩
      · rw [hs.threads]; exact hi.t0
    · intro r hr hsp
      rw [hs.threads] at hr
      rw [spawner0 hi r hr] at hsp
      unfold ThreadId at *; omega

/-! ## `main` -/

theorem ownOf_main (m : Mem) (g : Gh) :
    ownOf (upd (fun _ => .none) 0 g) m = upd (fun _ => Heap.empty) 0 g.heap := by
  funext u
  by_cases hu : u = 0
  · subst hu; simp [ownOf, joinedB, upd]
  · simp only [ownOf, upd, hu, ↓reduceIte, Gh.heap]; split <;> rfl

theorem kid_grant {x : Ptr} {ax : Nat} {h : Heap} (hx0 : x.off = 0) (hax : ax % 4 = 0)
    (hf : flagA x ax 0 h) (w : BitVec 32) :
    Capture.grant (transfer x ax w) (Tgt.captures (.writeWorker (x, w))) h :=
  grant_iff.mpr (sep_lift.mpr ⟨⟨hx0, hax⟩, by simpa using hf⟩)

theorem spawnErrorAt_mem {c : Nat} (hc : c < spawnErrors.size + 1) (h0 : c ≠ 0) :
    spawnErrorAt (c - 1) ∈ spawnErrors := by
  have hlt : c - 1 < spawnErrors.size := by omega
  simpa [spawnErrorAt, Array.getElem?_eq_getElem hlt] using Array.getElem_mem hlt

/-- Every thread record is `main`'s or a joined child's. -/
theorem joined_of {m : Mem} (h0 : m.threads[0]? = some { spawner := 0, joined := true })
    (hk : ∀ i, 0 < i → i < m.threads.size → m.threads[i]? = some { spawner := 0, joined := true }) :
    joinedAll 0 m := by
  intro r hr _
  obtain ⟨i, hil, rfl⟩ := Array.mem_iff_getElem.mp hr
  have hget : m.threads[i]? = some m.threads[i] := Array.getElem?_eq_getElem hil
  by_cases hi0 : i = 0
  · subst hi0; rw [Option.some.inj (hget.symm.trans h0)]
  · rw [Option.some.inj (hget.symm.trans (hk i (Nat.pos_of_ne_zero hi0) hil))]

set_option maxHeartbeats 4000000 in
/-- **`threadPair` meets its contract from any initial budget**, for every resource outcome of
both spawns. -/
theorem main_spec (lim : Option Nat) (d : Nat) :
    (proto v).WP 0 (threadPair v) (QM v) (fun _ => .none)
      { ({ mem0 with spawnLimit := lim } : Mem) with current := 0 } d := by
  unfold threadPair
  have ho₀ : Owned (upd (fun _ => Heap.empty) 0 Heap.empty)
      { ({ mem0 with spawnLimit := lim } : Mem) with current := 0 } := by
    rw [show upd (fun _ => Heap.empty) 0 Heap.empty = (fun _ => Heap.empty) from upd_same _ _]
    exact Owned.start rfl rfl
  -- `left` and `right`.
  refine WP.bind (WP.liftMem_upd (TTriple.alloc .stack 4 4 (by decide)) ho₀ rfl
    (by show 0 < mem0.threads.size; decide) rfl fun s1 m₁ h₁ ho₁ hq₁ hc₁ ht₁ => ?_)
  obtain ⟨Al, hA⟩ := hq₁
  obtain ⟨⟨hl0, hAl⟩, hl⟩ := sep_lift.mp hA
  refine WP.bind (WP.liftMem_upd (alloc_next 4 4 (by decide)) ho₁ hc₁
    (by rw [ht₁]; show 0 < mem0.threads.size; decide) hl fun s3 m₂ h₂ ho₂ hq₂ hc₂ ht₂ => ?_)
  obtain ⟨Ar, ⟨hr0, hAr⟩, F₂⟩ := sep_ex_lift hq₂
  have htt₂ : m₂.threads = #[{ spawner := 0, joined := true }] := by rw [ht₂, ht₁]; rfl
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  -- `left = 0`, `right = 0`.
  refine WP.bind (WP.liftM_upd ((TTriple.storeAt (k := 0) (a := 4) (0 : BitVec 32)
    (by simp [Ptr.add]) (by decide) (by simp; decide) (by simp [hl0, hAl]) (by decide)).frame) ho₂ hc₂
    (by rw [htt₂]; decide) F₂ fun _ m₃ h₃ ho₃ F₃ hc₃ ht₃ => ?_)
  refine WP.bind (WP.liftM_upd ((TTriple.storeAt (k := 0) (a := 4) (0 : BitVec 32)
    (by simp [Ptr.add]) (by decide) (by simp; decide) (by simp [hr0, hAr]) (by decide)).frameL) ho₃ hc₃
    (by rw [ht₃, htt₂]; decide) F₃ fun _ m₄ h₄ ho₄ F₄ hc₄ ht₄ => ?_)
  have htt₄ : m₄.threads = #[{ spawner := 0, joined := true }] := by rw [ht₄, ht₃, htt₂]
  rw [writeBytes_all (by simp [enc_u32])] at F₄
  obtain ⟨hL, hR, hdLR, rfl, hLa, hRa⟩ := F₄
  let B : Blks := ⟨s1, s3, Al, Ar⟩
  have hB : B.Ok := ⟨hl0, hr0, hAl, hAr⟩
  have hi₀ : Inv v (upd (fun _ => .none) 0 (.main .pre (hL ∪ hR) B)) m₄ := by
    refine ⟨by rw [ownOf_main]; exact ho₄, fun u _ _ _ _ _ hu => ?_,
      ⟨.pre, _, B, upd_self _ _ _, hB, ⟨hL, hR, hdLR, rfl, hLa, hRa⟩, by rw [htt₄]; rfl,
        fun u hu => ?_⟩, by rw [htt₄]; rfl⟩
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu; cases hu
    · rw [upd_ne _ _ (by unfold ThreadId at *; omega)]
  -- The first spawn: every resource outcome.
  simp only [StateT.run_bind]
  refine WP.bind (WP.spawnFallibleC fun k _ => ⟨.main .pre (hL ∪ hR) B, hi₀,
    fun G₁ m₅ hg₁ hi₅ c hc _ => ?_⟩)
  have hi₅' : Inv v G₁ { m₅ with current := 0 } :=
    ⟨hi₅.own.current 0, hi₅.kids, hi₅.main, hi₅.t0⟩
  obtain ⟨ph, hm, B', h0, -, -, hsh⟩ := hi₅.main
  rw [hg₁] at h0; cases h0
  obtain ⟨hsz₅, hn₅⟩ := hsh
  have hown₅ : ownOf G₁ m₅ 0 = hR ∪ hL := by
    simp [ownOf, joinedB, hg₁, Gh.heap, Heap.union_comm hdLR]
  by_cases hc0 : c = 0
  rotate_left
  · -- The first spawn fails: `main` keeps both captures and frees them.
    refine WP.mono ?_ (WP.spawnFailureRetains (target := Tgt.writeWorker (s1, v)) hc0
      (hi₅.own.current 0) hown₅ (kid_grant hl0 hAl hLa v))
    rintro r G' m' d' ⟨hr, hG', hm', -, -, -⟩
    subst r; subst G'; subst m'
    simp only [StateT.run_bind]
    refine WP.bind (WP.callRC_ok rfl ?_)
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    refine WP.bind (WP.liftMem_owned (free_front (R := flagA s3 Ar 0) (enc_u32 0) hl0 (by decide))
      hi₅'.own rfl (by rw [hsz₅]; decide)
      (by rw [show ownOf G₁ { m₅ with current := 0 } 0 = hR ∪ hL from hown₅]
          exact ⟨hL, hR, hdLR, Heap.union_comm hdLR.symm, hLa, hRa⟩)
      fun _ m₆ h₆ _ ho₆ hq₆ hs₆ _ _ => ?_)
    refine WP.bind (WP.liftMem_upd (TTriple.free (enc_u32 0) hr0 (by decide)) ho₆
      (hs₆.current) (by rw [hs₆.threads]; show 0 < m₅.threads.size; rw [hsz₅]; decide) hq₆
      fun _ m₇ _ _ _ _ ht₇ => ?_)
    refine WP.pure' ⟨.inr ⟨_, spawnErrorAt_mem hc hc0, rfl⟩, joined_of ?_ fun i h0 hlt => ?_⟩
    · rw [ht₇, hs₆.threads]; exact hi₅.t0
    · exfalso; rw [ht₇, hs₆.threads] at hlt; change i < m₅.threads.size at hlt; omega
  -- The first spawn succeeds: child 1 gets `left`.
  subst hc0
  simp only [spawnOutcomeC, ↓reduceIte]
  refine WP.spawnC fun k' _ => ⟨.main .pre (hL ∪ hR) B, by rw [← hg₁, upd_same]; exact hi₅',
    fun G₂ m₆ hg₂ hi₆ => ⟨.kid hL s1 Al v false, ⟨_, _, rfl, kid_grant hl0 hAl hLa v⟩,
      fun child m₇ hf => ?_⟩⟩
  obtain ⟨ph, hm, B', h0, -, -, hsh⟩ := hi₆.main
  rw [hg₂] at h0; cases h0
  obtain ⟨hsz₆, hn₆⟩ := hsh
  obtain ⟨rfl, hth₇⟩ := fork_threads hf
  have hown₆ : ownOf G₂ m₆ 0 = hR ∪ hL := by
    simp [ownOf, joinedB, hg₂, Gh.heap, Heap.union_comm hdLR]
  have ho₇ := Owned.fork (hi₆.own.current 0) (by rw [hsz₆]; decide) hown₆ hdLR.symm hf
  rw [hsz₆] at ho₇ ⊢
  dsimp only
  have hjb₇ : joinedB m₇ = joinedB m₆ := joinedB_fork hf
  have hjb1 : joinedB m₆ 1 = false := by
    simp [joinedB, Array.getElem?_eq_none (show m₆.threads.size ≤ 1 by omega)]
  have hi₇ : Inv v (upd (upd G₂ 1 (.kid hL s1 Al v false)) 0 (.main .one hR B)) m₇ := by
    refine ⟨?_, fun u h x ax w dn hu => ?_, ⟨.one, hR, B, upd_self _ _ _, hB, hRa, ?_⟩, ?_⟩
    · have e : ownOf (upd (upd G₂ 1 (.kid hL s1 Al v false)) 0 (.main .one hR B)) m₇ =
          upd (upd (ownOf G₂ m₆) 0 hR) 1 hL := by
        funext u
        unfold ownOf
        rw [hjb₇]
        by_cases h0 : u = 0
        · subst h0; simp [joinedB, upd, Gh.heap]
        · by_cases h1 : u = 1
          · subst h1; simp [hjb1, upd, Gh.heap]
          · simp [upd, h0, h1]
      rw [e]; exact ho₇
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu
        by_cases h1 : u = 1
        · subst h1; rw [upd_self] at hu; cases hu
          exact sep_lift.mpr ⟨⟨hl0, hAl⟩, by simpa [flagA] using hLa⟩
        · rw [upd_ne _ _ h1, hn₆ u (by unfold ThreadId at *; omega)] at hu; cases hu
    · refine ⟨by rw [hth₇]; simp [hsz₆], ?_, ⟨hL, false, .inl rfl, by simp [upd, B]⟩,
        fun u hu => ?_⟩
      · unfold KidRec; rw [hth₇, Array.getElem?_push, if_pos hsz₆.symm]
      · rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega),
          hn₆ u (by unfold ThreadId at *; omega)]
    · rw [hth₇, Array.getElem?_push, if_neg (by omega)]; exact hi₆.t0
  -- The second spawn: every resource outcome.
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  refine WP.bind (WP.spawnFallibleC fun k _ => ⟨.main .one hR B, hi₇,
    fun G₃ m₈ hg₃ hi₈ c₂ hc₂ _ => ?_⟩)
  have hi₈' : Inv v G₃ { m₈ with current := 0 } :=
    ⟨hi₈.own.current 0, hi₈.kids, hi₈.main, hi₈.t0⟩
  obtain ⟨ph, hm, B', h0, -, -, hsh⟩ := hi₈.main
  rw [hg₃] at h0; cases h0
  obtain ⟨hsz₈, r1₈, k1₈, hn₈⟩ := hsh
  have hown₈ : ownOf G₃ m₈ 0 = Heap.empty ∪ hR := by
    simp [ownOf, joinedB, hg₃, Gh.heap]
  by_cases hc0 : c₂ = 0
  rotate_left
  · -- The second spawn fails: `main` keeps `right`, joins child 1 (errdefer) and frees both.
    refine WP.mono ?_ (WP.spawnFailureRetains (target := Tgt.writeWorker (s3, addWrap v 1)) hc0
      (hi₈.own.current 0) hown₈ (kid_grant hr0 hAr hRa (addWrap v 1)))
    rintro r G' m' d' ⟨hr, hG', hm', -, -, -⟩
    subst r; subst G'; subst m'
    simp only [StateT.run_bind]
    refine WP.bind (WP.callRC_ok rfl ?_)
    simp only [StateT.run_pure, pure_bind, StateT.run_bind]
    refine WP.bind (WP.joinC fun k₂ _ => ⟨Gh.main .one hR B, by rw [← hg₃, upd_same]; exact hi₈',
      fun G₄ m₉ hg₄ hi₉ => ?_⟩)
    obtain ⟨ph, hm, B', h0, -, -, hsh⟩ := hi₉.main
    rw [hg₄] at h0; cases h0
    obtain ⟨hsz₉, r1₉, k1₉, hn₉⟩ := hsh
    refine ⟨fun _ => ⟨by decide, by rw [hsz₉]; decide, ⟨_, B, .inl rfl⟩, by
      have hr := r1₉
      unfold KidRec at hr
      simp [Thread.joinValid, Mem.isGated, hr]⟩,
      fun hfin => ⟨fun _ => join_run r1₉ rfl rfl, fun m₁₀ hj => ?_⟩⟩
    obtain ⟨hk1, x', ax', w', hf1⟩ := hfin
    obtain ⟨h', d', -, hk1'⟩ := k1₉
    simp only [↓reduceIte] at hk1'
    rw [hf1] at hk1'; cases hk1'
    obtain ⟨-, hka1⟩ := sep_lift.mp (hi₉.kids 1 _ _ _ _ _ hf1)
    simp only [↓reduceIte] at hka1
    obtain ⟨hc₁₀, hth₁₀⟩ := join_threads r1₉ hj
    have ho₁₀ := Owned.join (hi₉.own.current 0) (by rw [hsz₉]; decide) (by decide) hj
    have e0 : ownOf G₄ m₉ 0 = hR := by simp [ownOf, joinedB, hg₄, Gh.heap]
    have e1 : ownOf G₄ m₉ 1 = hk1 := by
      have r : m₉.threads[1]? = some { spawner := 0, joined := false } := r1₉
      simp [ownOf, joinedB, r, hf1, Gh.heap]
    have hd : Heap.Disjoint hR hk1 := by
      have := hi₉.own.disj 0 1 (by decide); rwa [e0, e1] at this
    rw [e0, e1, upd_comm _ _ _ (show (0 : Nat) ≠ 1 by decide)] at ho₁₀
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    have hsz₁₀ : m₁₀.threads.size = 2 := by rw [hth₁₀, Array.size_setIfInBounds, hsz₉]
    refine WP.bind (WP.liftMem_upd (free_front (R := flagA s3 Ar 0) (enc_u32 v) hl0 (by decide))
      ho₁₀ hc₁₀ (by rw [hsz₁₀]; decide) ⟨hk1, hR, hd.symm, Heap.union_comm hd, hka1, hRa⟩
      fun _ m₁₁ h₁₁ ho₁₁ hq₁₁ hc₁₁ ht₁₁ => ?_)
    refine WP.bind (WP.liftMem_upd (TTriple.free (enc_u32 0) hr0 (by decide)) ho₁₁ hc₁₁
      (by rw [ht₁₁, hsz₁₀]; decide) hq₁₁ fun _ m₁₂ _ _ _ _ ht₁₂ => ?_)
    refine WP.pure' ⟨.inr ⟨_, spawnErrorAt_mem hc₂ hc0, rfl⟩, joined_of ?_ fun i hi0 hlt => ?_⟩
    · rw [ht₁₂, ht₁₁, hth₁₀, Array.getElem?_setIfInBounds_ne (by decide)]; exact hi₉.t0
    · rw [ht₁₂, ht₁₁, hsz₁₀] at hlt
      have : i = 1 := by omega
      subst this
      rw [ht₁₂, ht₁₁, hth₁₀, Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz₉]; decide)]
  -- The second spawn succeeds: child 2 gets `right`.
  subst hc0
  simp only [spawnOutcomeC, ↓reduceIte]
  refine WP.spawnC fun k' _ => ⟨Gh.main .one hR B, by rw [← hg₃, upd_same]; exact hi₈',
    fun G₄ m₉ hg₄ hi₉ => ⟨Gh.kid hR s3 Ar (addWrap v 1) false,
      ⟨_, _, rfl, kid_grant hr0 hAr hRa _⟩, fun child m₁₀ hf₂ => ?_⟩⟩
  obtain ⟨ph, hm, B', h0, -, -, hsh⟩ := hi₉.main
  rw [hg₄] at h0; cases h0
  obtain ⟨hsz₉, r1₉, k1₉, hn₉⟩ := hsh
  obtain ⟨rfl, hth₁₀⟩ := fork_threads hf₂
  have hown₉ : ownOf G₄ m₉ 0 = Heap.empty ∪ hR := by simp [ownOf, joinedB, hg₄, Gh.heap]
  have ho₁₀ := Owned.fork (hi₉.own.current 0) (by rw [hsz₉]; decide) hown₉
    (Heap.disjoint_empty _).symm hf₂
  rw [hsz₉] at ho₁₀ ⊢
  dsimp only
  have hjb₁₀ : joinedB m₁₀ = joinedB m₉ := joinedB_fork hf₂
  have hjb2 : joinedB m₉ 2 = false := by
    simp [joinedB, Array.getElem?_eq_none (show m₉.threads.size ≤ 2 by omega)]
  have hi₁₀ : Inv v (upd (upd G₄ 2 (.kid hR s3 Ar (addWrap v 1) false)) 0
      (.main .two Heap.empty B)) m₁₀ := by
    refine ⟨?_, fun u h x ax w dn hu => ?_, ⟨.two, Heap.empty, B, upd_self _ _ _, hB, rfl, ?_⟩,
      ?_⟩
    · have e : ownOf (upd (upd G₄ 2 (.kid hR s3 Ar (addWrap v 1) false)) 0
          (.main .two Heap.empty B)) m₁₀ = upd (upd (ownOf G₄ m₉) 0 Heap.empty) 2 hR := by
        funext u
        unfold ownOf
        rw [hjb₁₀]
        by_cases h0 : u = 0
        · subst h0; simp [joinedB, upd, Gh.heap]
        · by_cases h2 : u = 2
          · subst h2; simp [hjb2, upd, Gh.heap]
          · simp [upd, h0, h2]
      rw [e]; exact ho₁₀
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu
        by_cases h2 : u = 2
        · subst h2; rw [upd_self] at hu; cases hu
          exact sep_lift.mpr ⟨⟨hr0, hAr⟩, by simpa [flagA] using hRa⟩
        · rw [upd_ne _ _ h2] at hu; exact hi₉.kids u _ _ _ _ _ hu
    · refine ⟨by rw [hth₁₀]; simp [hsz₉], ?_, ?_, ?_, ⟨hR, false, .inl rfl, by simp [upd, B]⟩,
        fun u hu => ?_⟩
      · unfold KidRec; rw [hth₁₀, Array.getElem?_push, if_neg (by omega)]; exact r1₉
      · unfold KidRec; rw [hth₁₀, Array.getElem?_push, if_pos hsz₉.symm]
      · obtain ⟨h', d', hd', hk⟩ := k1₉
        exact ⟨h', d', hd', by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact hk⟩
      · rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega),
          hn₉ u (by unfold ThreadId at *; omega)]
    · rw [hth₁₀, Array.getElem?_push, if_neg (by omega)]; exact hi₉.t0
  -- The join of child 1: `main` gets `left` back, with `v`.
  simp only [StateT.run_bind]
  refine WP.bind (WP.joinC fun k _ => ⟨Gh.main .two Heap.empty B, hi₁₀, fun G₅ m₁₁ hg₅ hi₁₁ => ?_⟩)
  obtain ⟨ph, hm, B', h0, -, -, hsh⟩ := hi₁₁.main
  rw [hg₅] at h0; cases h0
  obtain ⟨hsz₁₁, r1₁₁, r2₁₁, k1₁₁, k2₁₁, hn₁₁⟩ := hsh
  refine ⟨fun _ => ⟨by decide, by rw [hsz₁₁]; decide, ⟨_, B, .inr (.inl rfl)⟩, by
    have hr := r1₁₁
    unfold KidRec at hr
    simp [Thread.joinValid, Mem.isGated, hr]⟩,
    fun hfin => ⟨fun _ => join_run r1₁₁ rfl rfl, fun m₁₂ hj => ?_⟩⟩
  obtain ⟨hk1, x', ax', w', hf1⟩ := hfin
  obtain ⟨h', d', -, hk1'⟩ := k1₁₁
  simp only [↓reduceIte] at hk1'
  rw [hf1] at hk1'; cases hk1'
  obtain ⟨-, hka1⟩ := sep_lift.mp (hi₁₁.kids 1 _ _ _ _ _ hf1)
  simp only [↓reduceIte] at hka1
  obtain ⟨hc₁₂, hth₁₂⟩ := join_threads r1₁₁ hj
  have ho₁₂ := Owned.join (hi₁₁.own.current 0) (by rw [hsz₁₁]; decide) (by decide) hj
  have e0 : ownOf G₅ m₁₁ 0 = Heap.empty := by simp [ownOf, joinedB, hg₅, Gh.heap]
  have e1 : ownOf G₅ m₁₁ 1 = hk1 := by
    have r : m₁₁.threads[1]? = some { spawner := 0, joined := false } := r1₁₁
    simp [ownOf, joinedB, r, hf1, Gh.heap]
  rw [e0, e1, Heap.empty_union] at ho₁₂
  have hjb₁₂ : ∀ u, joinedB m₁₂ u = if u = 1 then true else joinedB m₁₁ u := by
    intro u
    unfold joinedB
    rw [hth₁₂]
    by_cases h1 : u = 1
    · subst h1
      rw [Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz₁₁]; decide)]; rfl
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm h1)]; simp [h1]
  have hi₁₂ : Inv v (upd G₅ 0 (.main .j1 hk1 B)) m₁₂ := by
    refine ⟨?_, fun u h x ax w dn hu => ?_, ⟨.j1, hk1, B, upd_self _ _ _, hB, hka1, ?_⟩, ?_⟩
    · have e : ownOf (upd G₅ 0 (.main .j1 hk1 B)) m₁₂ =
          upd (upd (ownOf G₅ m₁₁) 0 hk1) 1 Heap.empty := by
        funext u
        unfold ownOf
        rw [hjb₁₂]
        by_cases h0 : u = 0
        · subst h0; simp [joinedB, upd, Gh.heap]
        · by_cases h1 : u = 1
          · subst h1; simp [upd]
          · simp [upd, h0, h1]
      rw [e]; exact ho₁₂
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu; exact hi₁₁.kids u _ _ _ _ _ hu
    · refine ⟨by rw [hth₁₂, Array.size_setIfInBounds, hsz₁₁], ?_, ?_,
        ⟨hk1, true, .inr rfl, by rw [upd_ne _ _ (by decide)]; exact hf1⟩, ?_, fun u hu => ?_⟩
      · unfold KidRec; rw [hth₁₂, Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz₁₁]; decide)]
      · unfold KidRec; rw [hth₁₂, Array.getElem?_setIfInBounds_ne (by decide)]; exact r2₁₁
      · obtain ⟨h'', d'', hd'', hk⟩ := k2₁₁
        exact ⟨h'', d'', hd'', by rw [upd_ne _ _ (by decide)]; exact hk⟩
      · rw [upd_ne _ _ (by unfold ThreadId at *; omega), hn₁₁ u hu]
    · rw [hth₁₂, Array.getElem?_setIfInBounds_ne (by decide)]; exact hi₁₁.t0
  -- The join of child 2: `main` owns both, with `v` and `v +% 1`.
  simp only [StateT.run_pure, pure_bind, StateT.run_bind]
  refine WP.bind (WP.joinC fun k _ => ⟨Gh.main .j1 hk1 B, hi₁₂, fun G₆ m₁₃ hg₆ hi₁₃ => ?_⟩)
  obtain ⟨ph, hm, B', h0, -, hma₁₃, hsh⟩ := hi₁₃.main
  rw [hg₆] at h0; cases h0
  obtain ⟨hsz₁₃, r1₁₃, r2₁₃, k1₁₃, k2₁₃, hn₁₃⟩ := hsh
  refine ⟨fun _ => ⟨by decide, by rw [hsz₁₃]; decide, ⟨_, B, .inr (.inr rfl)⟩, by
    have hr := r2₁₃
    unfold KidRec at hr
    simp [Thread.joinValid, Mem.isGated, hr]⟩,
    fun hfin => ⟨fun _ => join_run r2₁₃ rfl rfl, fun m₁₄ hj₂ => ?_⟩⟩
  obtain ⟨hk2, x'', ax'', w'', hf2⟩ := hfin
  obtain ⟨h'', d'', -, hk2'⟩ := k2₁₃
  simp only [show (2 : Nat) ≠ 1 by decide, ↓reduceIte] at hk2'
  rw [hf2] at hk2'; cases hk2'
  obtain ⟨-, hka2⟩ := sep_lift.mp (hi₁₃.kids 2 _ _ _ _ _ hf2)
  simp only [↓reduceIte] at hka2
  obtain ⟨hc₁₄, hth₁₄⟩ := join_threads r2₁₃ hj₂
  have ho₁₄ := Owned.join (hi₁₃.own.current 0) (by rw [hsz₁₃]; decide) (by decide) hj₂
  have e0 : ownOf G₆ m₁₃ 0 = hk1 := by simp [ownOf, joinedB, hg₆, Gh.heap]
  have e2 : ownOf G₆ m₁₃ 2 = hk2 := by
    have r : m₁₃.threads[2]? = some { spawner := 0, joined := false } := r2₁₃
    simp [ownOf, joinedB, r, hf2, Gh.heap]
  have hd12 : Heap.Disjoint hk1 hk2 := by
    have := hi₁₃.own.disj 0 2 (by decide); rwa [e0, e2] at this
  rw [e0, e2, upd_comm _ _ _ (show (0 : Nat) ≠ 2 by decide)] at ho₁₄
  have hA : (flagA s1 Al v ∗ flagA s3 Ar (addWrap v 1)) (hk1 ∪ hk2) :=
    ⟨hk1, hk2, hd12, rfl, hma₁₃, hka2⟩
  have hsz₁₄ : m₁₄.threads.size = 3 := by rw [hth₁₄, Array.size_setIfInBounds, hsz₁₃]
  have hja : joinedAll 0 m₁₄ := by
    refine joined_of ?_ fun i hi0 hlt => ?_
    · rw [hth₁₄, Array.getElem?_setIfInBounds_ne (by decide)]; exact hi₁₃.t0
    · rw [hsz₁₄] at hlt
      rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
      · rw [hth₁₄, Array.getElem?_setIfInBounds_ne (by decide)]; exact r1₁₃
      · rw [hth₁₄, Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz₁₃]; decide)]
  -- `left +% right`.
  simp only [StateT.run_pure, pure_bind, StateT.run_bind]
  refine WP.bind (WP.liftM_upd ((TTriple.loadAt (p := s1) (A := Al) (S := 4) (K := .stack)
    (k := 0) (a := 4) (v := v) (by simp [Ptr.add])
    (by decide) (by rw [enc_u32]; decide) (by simp [hl0, hAl]) (decode_u32 v)).frame_eq)
    ho₁₄ hc₁₄ (by rw [hsz₁₄]; decide) hA fun r₁ m₁₅ h₁₅ ho₁₅ hq₁₅ hc₁₅ ht₁₅ => ?_)
  obtain ⟨hr₁, hA₁₅⟩ := sep_lift.mp hq₁₅
  subst r₁
  refine WP.bind (WP.liftM_upd ((TTriple.loadAt (p := s3) (A := Ar) (S := 4) (K := .stack)
    (k := 0) (a := 4) (v := addWrap v 1)
    (by simp [Ptr.add]) (by decide) (by rw [enc_u32]; decide) (by simp [hr0, hAr])
    (decode_u32 _)).frameL_eq)
    ho₁₅ hc₁₅ (by rw [ht₁₅, hsz₁₄]; decide) hA₁₅ fun r₂ m₁₆ h₁₆ ho₁₆ hq₁₆ hc₁₆ ht₁₆ => ?_)
  obtain ⟨hr₂, hA₁₆⟩ := sep_lift.mp hq₁₆
  subst r₂
  simp only [StateT.run_pure, pure_bind]
  refine WP.pure' ?_
  -- The frees.
  refine WP.bind (WP.liftMem_upd (free_front (R := flagA s3 Ar (addWrap v 1)) (enc_u32 v) hl0
    (by decide)) ho₁₆ hc₁₆ (by rw [ht₁₆, ht₁₅, hsz₁₄]; decide) hA₁₆
    fun _ m₁₇ h₁₇ ho₁₇ hq₁₇ hc₁₇ ht₁₇ => ?_)
  refine WP.bind (WP.liftMem_upd (TTriple.free (enc_u32 _) hr0 (by decide)) ho₁₇ hc₁₇
    (by rw [ht₁₇, ht₁₆, ht₁₅, hsz₁₄]; decide) hq₁₇ fun _ m₁₈ _ _ _ _ ht₁₈ => ?_)
  refine WP.pure' ⟨.inl rfl, fun r hr hs => hja r ?_ hs⟩
  rwa [ht₁₈, ht₁₇, ht₁₆, ht₁₅] at hr

/-! ## The results -/

/-- **`threadPair v` meets its declared contract under every schedule, every resource outcome
and every initial budget**: it returns `v +% (v +% 1)` or a declared spawn error, and every
child is joined. -/
theorem threadPair_spec {lim : Option Nat} {fuel : Nat} {o : Nat → Nat}
    {r : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run dispatch fuel o (threadPair v) { mem0 with spawnLimit := lim }).run =
      some (.ok (r, m))) :
    (r = .ok (addWrap v (addWrap v 1)) ∨ ∃ e ∈ spawnErrors, r = .error e) ∧ joinedAll 0 m := by
  obtain ⟨_, _, hq⟩ := (proto v).run_sound dispatch (fun _ => .none) dispatch_spec
    (fun _ _ _ _ _ hq => hq.2) rfl (main_spec lim) h
  exact hq

/-- **No run of `threadPair v` gives an error**: a refused capture is freed by `main` with no
race, the errdefer join is valid, and no child outlives the stack it captured. -/
theorem threadPair_safe {lim : Option Nat} {fuel : Nat} {o : Nat → Nat} {e : Error} :
    (Sched.run dispatch fuel o (threadPair v) { mem0 with spawnLimit := lim }).run ≠
      some (.error e) :=
  (proto v).run_safe dispatch (fun _ => .none) rfl dispatch_spec (fun _ _ _ _ hq => hq.2) rfl
    (main_spec lim)

end SpawnFailure.Pair
