import Proofs.Threads.Gen
import ZigLean.Conc.Csl
import ZigLean.Simp

/-!
# `disjoint` over all schedules: concurrent separation logic

`disjoint a b` makes two flags `x`, `y` and two contexts `c1 = {&x, a}`, `c2 = {&y, b}`, spawns
`writeFlag(&c1)` and `writeFlag(&c2)`, joins both and returns `x +% y`. It is `race` with two
flags in place of one. The result is `a + b` (wrapping) under every schedule (`disjoint_spec`), and no
schedule gives an error (`disjoint_safe`): the two threads write disjoint bytes, so no race.

The proof is in concurrent separation logic (`ZigLean/Conc/Csl.lean`): each thread owns whole
blocks, and the blocks move at the spawns and the joins.

- **`writeFlag`** is a sequential thread triple over the two blocks that the thread owns
  (`writeFlag_spec`): its context and its flag.
- **Ghost values** (`Gh`). `main` has its phase, the heap it owns and the four blocks (`Blks`);
  a kid has the heap it owns, its context, its flag, its value and whether it is done.
- **Invariant** (`Inv`). The threads' heaps are the parts of `Owned` (a joined thread owns
  nothing); a kid's heap holds its context and its flag (the value when done); `main`'s heap is
  the one of its phase; the threads are those of the phase.
- **`main`**: before the first spawn it owns all four blocks; it gives `{c1, x}` to kid 1 and
  `{c2, y}` to kid 2 (`Owned.fork`); at each join it takes the kid's blocks back
  (`Owned.join`), with the flag written.
-/

open Zig Zig.Conc Zig.Conc.Proto Threads Assn

namespace Threads.Disjoint

/-! ## `writeFlag` -/

theorem writeFlag_eq (c : Ptr) : writeFlag c = (Zig.load Ptr 8 (c.add 0) >>= fun xp =>
    Zig.load (BitVec 32) 4 (c.add 8) >>= fun v => Zig.store (α := BitVec 32) 4 xp v) := by
  unfold writeFlag
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_monadLift]

/-- `writeFlag(c)` reads the flag `x` and the value `v` of its context `c` and writes `v` to the
flag. -/
theorem writeFlag_spec {c x : Ptr} {Ac Ax : Nat} {cb xb : Array Byte} {v : BitVec 32}
    (hc0 : c.off = 0) (hAc : Ac % 8 = 0) (hx0 : x.off = 0) (hAx : Ax % 4 = 0)
    (hcs : cb.size = 16) (hxs : xb.size = 4)
    (hcx : Enc.decode (cb.extract 0 8) = pure x) (hcv : Enc.decode (cb.extract 8 12) = pure v) :
    TTriple (bytesAt c Ac 16 .stack cb ∗ bytesAt x Ax 4 .stack xb) (writeFlag c)
      (fun _ => bytesAt c Ac 16 .stack cb ∗ bytesAt x Ax 4 .stack (Enc.encode v)) := by
  rw [writeFlag_eq]
  refine TTriple.bind_eq (v := x) (P' := bytesAt c Ac 16 .stack cb ∗ bytesAt x Ax 4 .stack xb) ?_
    (TTriple.bind_eq (v := v) (P' := bytesAt c Ac 16 .stack cb ∗ bytesAt x Ax 4 .stack xb) ?_ ?_)
  · exact (TTriple.loadAt (k := 0) (a := 8) rfl (by decide) (by rw [hcs]; decide)
      (by simp [hc0, hAc]) hcx).frame.conseq (fun _ h => h) fun _ _ h => sep_assoc h
  · exact (TTriple.loadAt (k := 8) (a := 4) rfl (by decide) (by rw [hcs]; decide)
      (by simp [hc0]; omega) hcv).frame.conseq (fun _ h => h) fun _ _ h => sep_assoc h
  · refine (TTriple.storeAt (k := 0) (a := 4) v (by simp [Ptr.add]) (by decide)
      (by rw [hxs]; decide) (by simp [hx0, hAx]) (by decide)).frameL.conseq (fun _ h => h)
      fun _ _ h => ?_
    rwa [writeBytes_all (by rw [hxs, LawfulEnc.size_encode]; rfl)] at h

/-! ## Blocks and heaps -/

/-- The bytes of a `RaceCtx` with the flag `f` and the value `v` (the padding is undefined). -/
def ctxBytes (f : Ptr) (v : BitVec 32) : Array Byte :=
  writeBytes (writeBytes (Array.replicate 16 .undef) 0 (Enc.encode f)) 8 (Enc.encode v)

theorem enc_ptr (f : Ptr) : (Enc.encode f).size = 8 := LawfulEnc.size_encode f

theorem enc_u32 (v : BitVec 32) : (Enc.encode v).size = 4 := LawfulEnc.size_encode v

theorem ctxBytes_one (f : Ptr) :
    (writeBytes (Array.replicate 16 .undef) 0 (Enc.encode f)).size = 16 := by
  rw [writeBytes_size _ _ _ (by simp [enc_ptr])]; simp

theorem ctxBytes_size (f : Ptr) (v : BitVec 32) : (ctxBytes f v).size = 16 := by
  unfold ctxBytes
  rw [writeBytes_size _ _ _ (by rw [ctxBytes_one, enc_u32]; decide), ctxBytes_one]

theorem ctxBytes_flag (f : Ptr) (v : BitVec 32) :
    Enc.decode ((ctxBytes f v).extract 0 8) = pure f := by
  unfold ctxBytes
  rw [show (8 : Nat) = 0 + 8 from rfl, extract_writeBytes_disjoint _ _ _ _ _
      (by rw [ctxBytes_one, enc_u32]; decide) (by rw [ctxBytes_one]; decide) (.inr (Nat.le_refl _)),
    extract_writeBytes_in _ _ _ _ _ (by simp [enc_ptr]) (Nat.le_refl _) (by simp [enc_ptr])]
  simp only [Nat.sub_zero, Nat.zero_add]
  rw [show (8 : Nat) = (Enc.encode f).size from (enc_ptr f).symm, Array.extract_size]
  exact LawfulEnc.decode_encode f

theorem ctxBytes_val (f : Ptr) (v : BitVec 32) :
    Enc.decode ((ctxBytes f v).extract 8 12) = pure v := by
  unfold ctxBytes
  rw [show (12 : Nat) = 8 + 4 from rfl, extract_writeBytes_in _ _ _ _ _
    (by rw [ctxBytes_one, enc_u32]; decide) (Nat.le_refl _) (by rw [enc_u32]; exact Nat.le_refl _)]
  simp only [Nat.sub_self, Nat.zero_add]
  rw [show (4 : Nat) = (Enc.encode v).size from (enc_u32 v).symm, Array.extract_size]
  exact LawfulEnc.decode_encode v

/-- A context at `c` (address `A`) with the flag `f` and the value `v`. -/
def ctxA (c : Ptr) (A : Nat) (f : Ptr) (v : BitVec 32) : Assn := bytesAt c A 16 .stack (ctxBytes f v)

/-- A flag at `x` (address `A`) that holds `w`. -/
def flagA (x : Ptr) (A : Nat) (w : BitVec 32) : Assn := bytesAt x A 4 .stack (Enc.encode w)

/-- The four blocks of `disjoint`, with their addresses. -/
structure Blks where
  x : Ptr
  y : Ptr
  c1 : Ptr
  c2 : Ptr
  ax : Nat
  ay : Nat
  a1 : Nat
  a2 : Nat

/-- Each block starts at offset 0, at an aligned address. -/
def Blks.Ok (B : Blks) : Prop :=
  B.x.off = 0 ∧ B.y.off = 0 ∧ B.c1.off = 0 ∧ B.c2.off = 0 ∧ B.ax % 4 = 0 ∧ B.ay % 4 = 0 ∧
    B.a1 % 8 = 0 ∧ B.a2 % 8 = 0

/-! ## Protocol -/

/-- Where `main` is: at its first spawn, at its second spawn, at the join of kid 1, at the join
of kid 2. -/
inductive Ph where
  | pre | one | j1 | j2
  deriving DecidableEq

/-- A thread's ghost value. -/
inductive Gh where
  | none
  /-- `main` at the phase `ph`: it owns `h`. -/
  | main (ph : Ph) (h : Heap) (B : Blks)
  /-- A kid: it owns `h`, its context `c` (address `ac`) holds its flag `x` (address `ax`) and
  its value `v`; `done`: it wrote `v`. -/
  | kid (h : Heap) (c : Ptr) (ac : Nat) (x : Ptr) (ax : Nat) (v : BitVec 32) (done : Bool)

/-- The heap that a thread owns. -/
def Gh.heap : Gh → Heap
  | .main _ h _ | .kid h _ _ _ _ _ _ => h
  | .none => Heap.empty

/-- A kid's heap: its context and its flag, with `v` when it is done. -/
def KidA (c : Ptr) (ac : Nat) (x : Ptr) (ax : Nat) (v : BitVec 32) (done : Bool) : Assn :=
  ⌜c.off = 0 ∧ ac % 8 = 0 ∧ x.off = 0 ∧ ax % 4 = 0⌝ ∗
    (ctxA c ac x v ∗ flagA x ax (if done then v else 0))

variable (a b : BitVec 32)

/-- `main`'s heap at each phase. -/
def MainA (B : Blks) : Ph → Assn
  | .pre => flagA B.x B.ax 0 ∗ flagA B.y B.ay 0 ∗ ctxA B.c1 B.a1 B.x a ∗ ctxA B.c2 B.a2 B.y b
  | .one => flagA B.y B.ay 0 ∗ ctxA B.c2 B.a2 B.y b
  | .j1 => emp
  | .j2 => ctxA B.c1 B.a1 B.x a ∗ flagA B.x B.ax a

/-- Thread `u` is kid 1 (`i = 1`) or kid 2 of the blocks `B`. -/
def IsKid (B : Blks) (G : ThreadId → Gh) (u : ThreadId) (done : Option Bool) : Prop :=
  ∃ h d, (done = none ∨ done = some d) ∧
    G u = if u = 1 then .kid h B.c1 B.a1 B.x B.ax a d else .kid h B.c2 B.a2 B.y B.ay b d

/-- The thread record of kid `u`. -/
def KidRec (m : Mem) (u : ThreadId) (joined : Bool) : Prop :=
  m.threads[u]? = some { spawner := 0, joined }

/-- The threads at each phase of `main`. -/
def Shape (B : Blks) (G : ThreadId → Gh) (m : Mem) : Ph → Prop
  | .pre => m.threads.size = 1 ∧ ∀ u, 1 ≤ u → G u = .none
  | .one => m.threads.size = 2 ∧ KidRec m 1 false ∧ IsKid a b B G 1 none ∧
      ∀ u, 2 ≤ u → G u = .none
  | .j1 => m.threads.size = 3 ∧ KidRec m 1 false ∧ KidRec m 2 false ∧ IsKid a b B G 1 none ∧
      IsKid a b B G 2 none ∧ ∀ u, 3 ≤ u → G u = .none
  | .j2 => m.threads.size = 3 ∧ KidRec m 1 true ∧ KidRec m 2 false ∧ IsKid a b B G 1 (some true) ∧
      IsKid a b B G 2 none ∧ ∀ u, 3 ≤ u → G u = .none

/-- The heaps of the threads: a joined thread owns nothing. -/
def ownOf (G : ThreadId → Gh) (m : Mem) (u : ThreadId) : Heap :=
  if joinedB m u then Heap.empty else (G u).heap

/-- The invariant (module doc). -/
structure Inv (G : ThreadId → Gh) (m : Mem) : Prop where
  own : Owned (ownOf G m) m
  kids : ∀ u h c ac x ax v d, G u = .kid h c ac x ax v d → KidA c ac x ax v d h
  main : ∃ ph h B, G 0 = .main ph h B ∧ B.Ok ∧ MainA a b B ph h ∧ Shape a b B G m ph
  t0 : m.threads[0]? = some { spawner := 0, joined := true }

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv := Inv a b
  init tgt g := match tgt with
    | .writeFlag c => ∃ h ac x ax v, g = .kid h c ac x ax v false
    | _ => False
  fin g := ∃ h c ac x ax v, g = .kid h c ac x ax v true
  strict := true
  joins g := ∃ h B, g = .main .j1 h B ∨ g = .main .j2 h B

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok (a + b) ∧ joinedAll 0 m

/-! ## The kids -/

variable {a b}

/-- A kid that is not done was not joined, and is a thread. -/
theorem kid_live {G : ThreadId → Gh} {m : Mem} {u : ThreadId} {h c ac x ax v}
    (hi : Inv a b G m) (hu : 0 < u) (hg : G u = .kid h c ac x ax v false) :
    joinedB m u = false ∧ u < m.threads.size ∧ (u = 1 ∨ u = 2) := by
  obtain ⟨ph, hm, B, h0, -, -, hs⟩ := hi.main
  have hne : ∀ k, k ≤ u → G u ≠ .none := fun _ _ he => by rw [hg] at he; cases he
  have jb : ∀ jn, KidRec m u jn → jn = false → joinedB m u = false := by
    intro jn hr hj; unfold joinedB; rw [hr]; simp [hj]
  cases ph with
  | pre => exact absurd (hs.2 u hu) (hne u (Nat.le_refl _))
  | one =>
    obtain ⟨hsz, r1, -, hn⟩ := hs
    have : u = 1 := by
      by_cases h2 : 2 ≤ u
      · exact absurd (hn u h2) (hne u (Nat.le_refl _))
      · unfold ThreadId at *; omega
    subst this
    exact ⟨jb _ r1 rfl, by rw [hsz]; decide, .inl rfl⟩
  | j1 =>
    obtain ⟨hsz, r1, r2, -, -, hn⟩ := hs
    by_cases h1 : u = 1
    · subst h1; exact ⟨jb _ r1 rfl, by rw [hsz]; decide, .inl rfl⟩
    · by_cases h2 : u = 2
      · subst h2; exact ⟨jb _ r2 rfl, by rw [hsz]; decide, .inr rfl⟩
      · exact absurd (hn u (by unfold ThreadId at *; omega)) (hne u (Nat.le_refl _))
  | j2 =>
    obtain ⟨hsz, r1, r2, ⟨h', d, hd, hk1⟩, -, hn⟩ := hs
    by_cases h1 : u = 1
    · subst h1
      simp only [↓reduceIte] at hk1
      rw [hg] at hk1; cases hk1
      simp at hd
    · by_cases h2 : u = 2
      · subst h2; exact ⟨jb _ r2 rfl, by rw [hsz]; decide, .inr rfl⟩
      · exact absurd (hn u (by unfold ThreadId at *; omega)) (hne u (Nat.le_refl _))

/-- A step of a thread that is not joined, with its new ghost value `g`: the parts. -/
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
theorem spawner0 {G : ThreadId → Gh} {m : Mem} (hi : Inv a b G m) :
    ∀ r ∈ m.threads, r.spawner = 0 := by
  obtain ⟨ph, hm, B, h0, -, -, hs⟩ := hi.main
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
  | one =>
    obtain ⟨hsz, r1, -⟩ := hs
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact hk 0 true ht0 _
    · exact hk 1 false r1 _
  | j1 =>
    obtain ⟨hsz, r1, r2, -⟩ := hs
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hk 0 true ht0 _
    · exact hk 1 false r1 _
    · exact hk 2 false r2 _
  | j2 =>
    obtain ⟨hsz, r1, r2, -⟩ := hs
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hk 0 true ht0 _
    · exact hk 1 true r1 _
    · exact hk 2 false r2 _

theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : (proto a b).init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : Inv a b G m) :
    (proto a b).WP u (dispatch tgt) ((proto a b).QKid u) G { m with current := u } d := by
  cases tgt with
  | writeFlag c =>
    obtain ⟨h, ac, x, ax, v, rfl⟩ := hg
    obtain ⟨hj, hut, h12⟩ := kid_live hi hu hgu
    have hka := hi.kids u _ _ _ _ _ _ _ hgu
    obtain ⟨⟨hc0, hac, hx0, hax⟩, hcx⟩ := sep_lift.mp hka
    have hown : ownOf G m u = h := by unfold ownOf; rw [hj, hgu]; rfl
    show (proto a b).WP u ((fun _ => ()) <$> ConcM.liftMem (writeFlag c)) _ G _ d
    refine WP.map (WP.liftMem_owned (own := ownOf G m)
      (writeFlag_spec (xb := Enc.encode (0 : BitVec 32)) hc0 hac hx0 hax (ctxBytes_size x v)
        (enc_u32 0)
        (ctxBytes_flag x v) (ctxBytes_val x v)) (hi.own.current u) rfl hut
      (by rw [hown]; simpa [ctxA, flagA] using hcx) fun _ m' hQ _ ho' hq hs _ _ => ?_)
    refine ⟨.kid hQ c ac x ax v true, ?_, ⟨_, _, _, _, _, _, rfl⟩, fun _ => ?_⟩
    · refine ⟨?_, fun w h' c' ac' x' ax' v' d' hw => ?_, ?_, ?_⟩
      · rw [ownOf_upd hs.threads hj]; exact ho'
      · by_cases hwu : w = u
        · subst hwu; rw [upd_self] at hw; cases hw
          exact sep_lift.mpr ⟨⟨hc0, hac, hx0, hax⟩, by simpa [ctxA, flagA] using hq⟩
        · rw [upd_ne _ _ hwu] at hw; exact hi.kids w _ _ _ _ _ _ _ hw
      · obtain ⟨ph, hm, B, h0, hB, hma, hsh⟩ := hi.main
        refine ⟨ph, hm, B, by rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact h0, hB, hma, ?_⟩
        have hkid : ∀ w dn, IsKid a b B G w dn → w ≠ u ∨ dn = none → IsKid a b B (upd G u (.kid hQ c ac x ax v true)) w dn := by
          intro w dn ⟨h', d', hd', hk⟩ hw
          by_cases hwu : w = u
          · subst hwu
            rcases hw with hw | rfl
            · exact absurd rfl hw
            · refine ⟨hQ, true, .inl rfl, ?_⟩
              rw [upd_self]
              rw [hgu] at hk
              by_cases h1 : w = 1
              · simp only [h1, ↓reduceIte] at hk ⊢; cases hk; rfl
              · simp only [h1, ↓reduceIte] at hk ⊢; cases hk; rfl
          · exact ⟨h', d', hd', by rw [upd_ne _ _ hwu]; exact hk⟩
        have hnone : ∀ k, (∀ w, k ≤ w → G w = .none) → ∀ w, k ≤ w → upd G u (.kid hQ c ac x ax v true) w = .none := by
          intro k hk w hw
          by_cases hwu : w = u
          · subst hwu; have := hk w hw; rw [hgu] at this; cases this
          · rw [upd_ne _ _ hwu]; exact hk w hw
        have hrec : ∀ w jn, KidRec m w jn → KidRec m' w jn := by
          intro w jn hr; unfold KidRec; rw [hs.threads]; exact hr
        cases ph with
        | pre => exact ⟨by rw [hs.threads]; exact hsh.1, hnone 1 hsh.2⟩
        | one =>
          obtain ⟨hsz, r1, k1, hn⟩ := hsh
          exact ⟨by rw [hs.threads]; exact hsz, hrec _ _ r1, hkid 1 _ k1 (.inr rfl), hnone 2 hn⟩
        | j1 =>
          obtain ⟨hsz, r1, r2, k1, k2, hn⟩ := hsh
          exact ⟨by rw [hs.threads]; exact hsz, hrec _ _ r1, hrec _ _ r2, hkid 1 _ k1 (.inr rfl),
            hkid 2 _ k2 (.inr rfl), hnone 3 hn⟩
        | j2 =>
          obtain ⟨hsz, r1, r2, k1, k2, hn⟩ := hsh
          have hu1 : u ≠ 1 := by
            intro h1; subst h1
            obtain ⟨h', d', hd', hk⟩ := k1
            rw [hgu] at hk; simp only [↓reduceIte] at hk; cases hk
            simp at hd'
          exact ⟨by rw [hs.threads]; exact hsz, hrec _ _ r1, hrec _ _ r2,
            hkid 1 _ k1 (.inl (Ne.symm hu1)), hkid 2 _ k2 (.inr rfl), hnone 3 hn⟩
      · rw [hs.threads]; exact hi.t0
    · intro r hr hsp
      rw [hs.threads] at hr
      rw [spawner0 hi r hr] at hsp
      unfold ThreadId at *; omega
  | _ => exact hg.elim

/-! ## `main` -/

/-- `main`'s ghost value and no kid: the parts. -/
theorem ownOf_main (m : Mem) (g : Gh) :
    ownOf (upd (fun _ => .none) 0 g) m = upd (fun _ => Heap.empty) 0 g.heap := by
  funext u
  by_cases hu : u = 0
  · subst hu; simp [ownOf, joinedB, upd]
  · simp only [ownOf, upd, hu, ↓reduceIte, Gh.heap]; split <;> rfl

theorem enc_zero : writeBytes (Array.replicate 4 .undef) 0 (Enc.encode (0 : BitVec 32)) =
    Enc.encode (0 : BitVec 32) :=
  writeBytes_all (by simp [enc_u32])

/-- `main`'s four blocks: it keeps `y`, `c2` and gives `c1`, `x` to kid 1. -/
theorem split_pre {X Y C1 C2 : Assn} {h : Heap} (hh : (X ∗ (Y ∗ (C1 ∗ C2))) h) :
    ((Y ∗ C2) ∗ (C1 ∗ X)) h := by
  have h1 := sep_left_comm hh
  refine sep_assoc' (sep_mono (fun _ h => h) (fun _ h => ?_) h1)
  exact sep_left_comm (sep_assoc (sep_comm h))

/-- `free` of the first block. -/
theorem free_front {R : Assn} {p : Ptr} {A S : Nat} {bs : Array Byte} (hS : bs.size = S)
    (h0 : p.off = 0) (hpos : 0 < S) :
    TTriple (bytesAt p A S .stack bs ∗ R) (Zig.free p) (fun _ => R) :=
  (TTriple.free hS h0 hpos).frame.conseq (fun _ h => h) fun _ _ h => sep_emp.mp (sep_comm h)

theorem decode_u32 (v : BitVec 32) : Enc.decode ((Enc.encode v).extract 0 (0 + Enc.size (BitVec 32))) =
    (pure v : Result (BitVec 32)) := by
  rw [show 0 + Enc.size (BitVec 32) = (Enc.encode v).size from (enc_u32 v).symm, Array.extract_size]
  exact LawfulEnc.decode_encode v

set_option maxHeartbeats 1000000 in
theorem main_spec (d : Nat) : (proto a b).WP 0 (disjoint a b) (QM a b) (fun _ => .none)
    { mem0 with current := 0 } d := by
  unfold disjoint
  have ho₀ : Owned (upd (fun _ => Heap.empty) 0 Heap.empty) { mem0 with current := 0 } := by
    rw [show upd (fun _ => Heap.empty) 0 Heap.empty = (fun _ => Heap.empty) from upd_same _ _]
    exact (Owned.start rfl rfl)
  -- The four blocks.
  refine WP.bind (WP.liftMem_upd (TTriple.alloc .stack 4 4 (by decide)) ho₀ rfl (by decide) rfl
    fun s2 m₁ h₁ ho₁ hq₁ hc₁ ht₁ => ?_)
  obtain ⟨Ax, hA⟩ := hq₁
  obtain ⟨⟨hx0, hAx⟩, hx⟩ := sep_lift.mp hA
  refine WP.bind (WP.liftMem_upd (alloc_next 4 4 (by decide)) ho₁ hc₁ (by rw [ht₁]; decide) hx
    fun s4 m₂ h₂ ho₂ hq₂ hc₂ ht₂ => ?_)
  obtain ⟨Ay, ⟨hy0, hAy⟩, hy⟩ := sep_ex_lift hq₂
  refine WP.bind (WP.liftMem_upd (alloc_next 16 8 (by decide)) ho₂ hc₂
    (by rw [ht₂, ht₁]; decide) hy fun s6 m₃ h₃ ho₃ hq₃ hc₃ ht₃ => ?_)
  obtain ⟨A1, ⟨h10, hA1⟩, hc1⟩ := sep_ex_lift hq₃
  refine WP.bind (WP.liftMem_upd (alloc_next 16 8 (by decide)) ho₃ hc₃
    (by rw [ht₃, ht₂, ht₁]; decide) hc1 fun s11 m₄ h₄ ho₄ hq₄ hc₄ ht₄ => ?_)
  obtain ⟨A2, ⟨h20, hA2⟩, hc2⟩ := sep_ex_lift hq₄
  have htt₄ : m₄.threads = mem0.threads := by rw [ht₄, ht₃, ht₂, ht₁]
  have F₄ := sep_assoc (sep_assoc hc2)
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  -- `x = 0`, `y = 0`, `c1 = {&x, a}`, `c2 = {&y, b}`.
  refine WP.bind (WP.liftM_upd ((TTriple.storeAt (k := 0) (a := 4) (0 : BitVec 32)
    (by simp [Ptr.add]) (by decide) (by simp; decide) (by simp [hx0, hAx]) (by decide)).frame) ho₄ hc₄
    (by rw [htt₄]; decide) F₄ fun _ m₅ h₅ ho₅ F₅ hc₅ ht₅ => ?_)
  refine WP.bind (WP.liftM_upd ((TTriple.storeAt (k := 0) (a := 4) (0 : BitVec 32)
    (by simp [Ptr.add]) (by decide) (by simp; decide) (by simp [hy0, hAy]) (by decide)).frame.frameL)
    ho₅ hc₅ (by rw [ht₅, htt₄]; decide) F₅ fun _ m₆ h₆ ho₆ F₆ hc₆ ht₆ => ?_)
  refine WP.bind (WP.liftM_upd ((TTriple.storeAt (k := 0) (a := 8) s2
    rfl (by decide) (by simp; decide) (by simp [h10, hA1]) (by decide)).frame.frameL.frameL)
    ho₆ hc₆ (by rw [ht₆, ht₅, htt₄]; decide) F₆ fun _ m₇ h₇ ho₇ F₇ hc₇ ht₇ => ?_)
  refine WP.bind (WP.liftM_upd ((TTriple.storeAt (k := 8) (a := 4) a
    rfl (by decide) (by rw [ctxBytes_one]; decide) (by simp [h10]; omega) (by decide)).frame.frameL.frameL)
    ho₇ hc₇ (by rw [ht₇, ht₆, ht₅, htt₄]; decide) F₇ fun _ m₈ h₈ ho₈ F₈ hc₈ ht₈ => ?_)
  refine WP.bind (WP.liftM_upd ((TTriple.storeAt (k := 0) (a := 8) s4
    rfl (by decide) (by simp; decide) (by simp [h20, hA2]) (by decide)).frameL.frameL.frameL)
    ho₈ hc₈ (by rw [ht₈, ht₇, ht₆, ht₅, htt₄]; decide) F₈ fun _ m₉ h₉ ho₉ F₉ hc₉ ht₉ => ?_)
  refine WP.bind (WP.liftM_upd ((TTriple.storeAt (k := 8) (a := 4) b
    rfl (by decide) (by rw [ctxBytes_one]; decide) (by simp [h20]; omega) (by decide)).frameL.frameL.frameL)
    ho₉ hc₉ (by rw [ht₉, ht₈, ht₇, ht₆, ht₅, htt₄]; decide) F₉
    fun _ m₁₀ h₁₀ ho₁₀ F₁₀ hc₁₀ ht₁₀ => ?_)
  have htt₁₀ : m₁₀.threads = mem0.threads := by rw [ht₁₀, ht₉, ht₈, ht₇, ht₆, ht₅, htt₄]
  rw [enc_zero] at F₁₀
  dsimp only at F₁₀ ⊢
  -- The first spawn: kid 1 gets `c1` and `x`.
  let B : Blks := ⟨s2, s4, s6, s11, Ax, Ay, A1, A2⟩
  have hB : B.Ok := ⟨hx0, hy0, h10, h20, hAx, hAy, hA1, hA2⟩
  have hM : MainA a b B .pre h₁₀ := F₁₀
  obtain ⟨hP, hK1, hdPK, rfl, hPa, hKa⟩ := split_pre hM
  refine WP.bind (WP.spawnC fun k _ => ⟨.main .pre (hP ∪ hK1) B, ?_, fun G₁ m₁₁ hg₁ hi₁₁ =>
    ⟨.kid hK1 s6 A1 s2 Ax a false, ⟨_, _, _, _, _, rfl⟩, fun child m₁₂ hf => ?_⟩⟩)
  · refine ⟨by rw [ownOf_main]; exact ho₁₀, fun u _ _ _ _ _ _ _ hu => ?_,
      ⟨.pre, _, B, upd_self _ _ _, hB, hM, by rw [htt₁₀]; rfl, fun u hu => ?_⟩, by rw [htt₁₀]; rfl⟩
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu; cases hu
    · rw [upd_ne _ _ (by unfold ThreadId at *; omega)]
  obtain ⟨ph, hm, B', h0, -, -, hsh⟩ := hi₁₁.main
  rw [hg₁] at h0; cases h0
  obtain ⟨hsz₁₁, hn₁₁⟩ := hsh
  obtain ⟨rfl, hth₁₂⟩ := fork_threads hf
  have hown₁₁ : ownOf G₁ m₁₁ 0 = hP ∪ hK1 := by simp [ownOf, joinedB, hg₁, Gh.heap]
  have ho₁₂ := Owned.fork (hi₁₁.own.current 0) (by rw [hsz₁₁]; decide) hown₁₁ hdPK hf
  rw [hsz₁₁] at ho₁₂ ⊢
  dsimp only
  have hjb₁₂ : joinedB m₁₂ = joinedB m₁₁ := joinedB_fork hf
  have hjb1 : joinedB m₁₁ 1 = false := by
    simp [joinedB, Array.getElem?_eq_none (show m₁₁.threads.size ≤ 1 by omega)]
  have hi₁₂ : Inv a b (upd (upd G₁ 1 (.kid hK1 s6 A1 s2 Ax a false)) 0 (.main .one hP B)) m₁₂ := by
    refine ⟨?_, fun u h c ac x ax v dn hu => ?_, ⟨.one, hP, B, upd_self _ _ _, hB, hPa, ?_⟩, ?_⟩
    · have e : ownOf (upd (upd G₁ 1 (.kid hK1 s6 A1 s2 Ax a false)) 0 (.main .one hP B)) m₁₂ =
          upd (upd (ownOf G₁ m₁₁) 0 hP) 1 hK1 := by
        funext u
        unfold ownOf
        rw [hjb₁₂]
        by_cases h0 : u = 0
        · subst h0; simp [joinedB, upd, Gh.heap]
        · by_cases h1 : u = 1
          · subst h1; simp [hjb1, upd, Gh.heap]
          · simp [upd, h0, h1]
      rw [e]; exact ho₁₂
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu
        by_cases h1 : u = 1
        · subst h1; rw [upd_self] at hu; cases hu
          exact sep_lift.mpr ⟨⟨h10, hA1, hx0, hAx⟩, by simpa [ctxA, flagA] using hKa⟩
        · rw [upd_ne _ _ h1, hn₁₁ u (by unfold ThreadId at *; omega)] at hu; cases hu
    · refine ⟨by rw [hth₁₂]; simp [hsz₁₁], ?_, ⟨hK1, false, .inl rfl, by simp [upd, B]⟩,
        fun u hu => ?_⟩
      · unfold KidRec; rw [hth₁₂, Array.getElem?_push, if_pos hsz₁₁.symm]
      · rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega),
          hn₁₁ u (by unfold ThreadId at *; omega)]
    · rw [hth₁₂, Array.getElem?_push, if_neg (by omega)]; exact hi₁₁.t0
  -- The second spawn: kid 2 gets `c2` and `y`; `main` owns nothing.
  simp only [StateT.run_bind]
  refine WP.bind (WP.spawnC fun k _ => ⟨Gh.main .one hP B, hi₁₂, fun G₂ m₁₃ hg₂ hi₁₃ =>
    ⟨Gh.kid hP s11 A2 s4 Ay b false, ⟨_, _, _, _, _, rfl⟩, fun child m₁₄ hf₂ => ?_⟩⟩)
  obtain ⟨ph, hm, B', h0, -, -, hsh⟩ := hi₁₃.main
  rw [hg₂] at h0; cases h0
  obtain ⟨hsz₁₃, r1₁₃, k1₁₃, hn₁₃⟩ := hsh
  obtain ⟨rfl, hth₁₄⟩ := fork_threads hf₂
  have hown₁₃ : ownOf G₂ m₁₃ 0 = Heap.empty ∪ hP := by simp [ownOf, joinedB, hg₂, Gh.heap]
  have ho₁₄ := Owned.fork (hi₁₃.own.current 0) (by rw [hsz₁₃]; decide) hown₁₃
    (Heap.disjoint_empty _).symm hf₂
  rw [hsz₁₃] at ho₁₄ ⊢
  dsimp only
  have hjb₁₄ : joinedB m₁₄ = joinedB m₁₃ := joinedB_fork hf₂
  have hjb2 : joinedB m₁₃ 2 = false := by
    simp [joinedB, Array.getElem?_eq_none (show m₁₃.threads.size ≤ 2 by omega)]
  have hi₁₄ : Inv a b (upd (upd G₂ 2 (.kid hP s11 A2 s4 Ay b false)) 0 (.main .j1 Heap.empty B))
      m₁₄ := by
    refine ⟨?_, fun u h c ac x ax v dn hu => ?_, ⟨.j1, Heap.empty, B, upd_self _ _ _, hB, rfl, ?_⟩,
      ?_⟩
    · have e : ownOf (upd (upd G₂ 2 (.kid hP s11 A2 s4 Ay b false)) 0 (.main .j1 Heap.empty B))
          m₁₄ = upd (upd (ownOf G₂ m₁₃) 0 Heap.empty) 2 hP := by
        funext u
        unfold ownOf
        rw [hjb₁₄]
        by_cases h0 : u = 0
        · subst h0; simp [joinedB, upd, Gh.heap]
        · by_cases h2 : u = 2
          · subst h2; simp [hjb2, upd, Gh.heap]
          · simp [upd, h0, h2]
      rw [e]; exact ho₁₄
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu
        by_cases h2 : u = 2
        · subst h2; rw [upd_self] at hu; cases hu
          exact sep_lift.mpr ⟨⟨h20, hA2, hy0, hAy⟩, by simpa [ctxA, flagA] using sep_comm hPa⟩
        · rw [upd_ne _ _ h2] at hu; exact hi₁₃.kids u _ _ _ _ _ _ _ hu
    · refine ⟨by rw [hth₁₄]; simp [hsz₁₃], ?_, ?_, ?_, ⟨hP, false, .inl rfl, by simp [upd, B]⟩,
        fun u hu => ?_⟩
      · unfold KidRec; rw [hth₁₄, Array.getElem?_push, if_neg (by omega)]; exact r1₁₃
      · unfold KidRec; rw [hth₁₄, Array.getElem?_push, if_pos hsz₁₃.symm]
      · obtain ⟨h', d', hd', hk⟩ := k1₁₃
        exact ⟨h', d', hd', by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact hk⟩
      · rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega),
          hn₁₃ u (by unfold ThreadId at *; omega)]
    · rw [hth₁₄, Array.getElem?_push, if_neg (by omega)]; exact hi₁₃.t0
  -- The join of kid 1: `main` gets `c1` and `x` back, with `x = a`.
  simp only [StateT.run_bind]
  refine WP.bind (WP.joinC fun k _ => ⟨Gh.main .j1 Heap.empty B, hi₁₄, fun G₃ m₁₅ hg₃ hi₁₅ => ?_⟩)
  obtain ⟨ph, hm, B', h0, -, -, hsh⟩ := hi₁₅.main
  rw [hg₃] at h0; cases h0
  obtain ⟨hsz₁₅, r1₁₅, r2₁₅, k1₁₅, k2₁₅, hn₁₅⟩ := hsh
  refine ⟨fun _ => ⟨by decide, by rw [hsz₁₅]; decide, ⟨_, B, .inl rfl⟩, by
    have hr := r1₁₅
    unfold KidRec at hr
    simp [Thread.joinValid, Mem.isGated, hr]⟩,
    fun hfin => ⟨fun _ => join_run r1₁₅ rfl rfl, fun m₁₆ hj => ?_⟩⟩
  obtain ⟨hk1, c', ac', x', ax', v', hf1⟩ := hfin
  obtain ⟨h', d', -, hk1'⟩ := k1₁₅
  simp only [↓reduceIte] at hk1'
  rw [hf1] at hk1'; cases hk1'
  obtain ⟨-, hka1⟩ := sep_lift.mp (hi₁₅.kids 1 _ _ _ _ _ _ _ hf1)
  simp only [↓reduceIte] at hka1
  obtain ⟨hc₁₆, hth₁₆⟩ := join_threads r1₁₅ hj
  have ho₁₆ := Owned.join (hi₁₅.own.current 0) (by rw [hsz₁₅]; decide) (by decide) hj
  have e0 : ownOf G₃ m₁₅ 0 = Heap.empty := by simp [ownOf, joinedB, hg₃, Gh.heap]
  have e1 : ownOf G₃ m₁₅ 1 = hk1 := by
    have r : m₁₅.threads[1]? = some { spawner := 0, joined := false } := r1₁₅
    simp [ownOf, joinedB, r, hf1, Gh.heap]
  rw [e0, e1, Heap.empty_union] at ho₁₆
  have hjb₁₆ : ∀ u, joinedB m₁₆ u = if u = 1 then true else joinedB m₁₅ u := by
    intro u
    unfold joinedB
    rw [hth₁₆]
    by_cases h1 : u = 1
    · subst h1
      rw [Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz₁₅]; decide)]; rfl
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm h1)]; simp [h1]
  have hi₁₆ : Inv a b (upd G₃ 0 (.main .j2 hk1 B)) m₁₆ := by
    refine ⟨?_, fun u h c ac x ax v dn hu => ?_, ⟨.j2, hk1, B, upd_self _ _ _, hB, hka1, ?_⟩, ?_⟩
    · have e : ownOf (upd G₃ 0 (.main .j2 hk1 B)) m₁₆ = upd (upd (ownOf G₃ m₁₅) 0 hk1) 1 Heap.empty := by
        funext u
        unfold ownOf
        rw [hjb₁₆]
        by_cases h0 : u = 0
        · subst h0; simp [joinedB, upd, Gh.heap]
        · by_cases h1 : u = 1
          · subst h1; simp [upd]
          · simp [upd, h0, h1]
      rw [e]; exact ho₁₆
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu; exact hi₁₅.kids u _ _ _ _ _ _ _ hu
    · refine ⟨by rw [hth₁₆, Array.size_setIfInBounds, hsz₁₅], ?_, ?_,
        ⟨hk1, true, .inr rfl, by rw [upd_ne _ _ (by decide)]; exact hf1⟩, ?_, fun u hu => ?_⟩
      · unfold KidRec; rw [hth₁₆, Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz₁₅]; decide)]
      · unfold KidRec; rw [hth₁₆, Array.getElem?_setIfInBounds_ne (by decide)]; exact r2₁₅
      · obtain ⟨h'', d'', hd'', hk⟩ := k2₁₅
        exact ⟨h'', d'', hd'', by rw [upd_ne _ _ (by decide)]; exact hk⟩
      · rw [upd_ne _ _ (by unfold ThreadId at *; omega), hn₁₅ u hu]
    · rw [hth₁₆, Array.getElem?_setIfInBounds_ne (by decide)]; exact hi₁₅.t0
  -- The join of kid 2: `main` owns all four blocks, with `x = a` and `y = b`.
  refine WP.bind (WP.joinC fun k _ => ⟨Gh.main .j2 hk1 B, hi₁₆, fun G₄ m₁₇ hg₄ hi₁₇ => ?_⟩)
  obtain ⟨ph, hm, B', h0, -, hma₁₇, hsh⟩ := hi₁₇.main
  rw [hg₄] at h0; cases h0
  obtain ⟨hsz₁₇, r1₁₇, r2₁₇, k1₁₇, k2₁₇, hn₁₇⟩ := hsh
  refine ⟨fun _ => ⟨by decide, by rw [hsz₁₇]; decide, ⟨_, B, .inr rfl⟩, by
    have hr := r2₁₇
    unfold KidRec at hr
    simp [Thread.joinValid, Mem.isGated, hr]⟩,
    fun hfin => ⟨fun _ => join_run r2₁₇ rfl rfl, fun m₁₈ hj₂ => ?_⟩⟩
  obtain ⟨hk2, c'', ac'', x'', ax'', v'', hf2⟩ := hfin
  obtain ⟨h'', d'', -, hk2'⟩ := k2₁₇
  simp only [show (2 : Nat) ≠ 1 by decide, ↓reduceIte] at hk2'
  rw [hf2] at hk2'; cases hk2'
  obtain ⟨-, hka2⟩ := sep_lift.mp (hi₁₇.kids 2 _ _ _ _ _ _ _ hf2)
  simp only [↓reduceIte] at hka2
  obtain ⟨hc₁₈, hth₁₈⟩ := join_threads r2₁₇ hj₂
  have ho₁₈ := Owned.join (hi₁₇.own.current 0) (by rw [hsz₁₇]; decide) (by decide) hj₂
  have e0 : ownOf G₄ m₁₇ 0 = hk1 := by simp [ownOf, joinedB, hg₄, Gh.heap]
  have e2 : ownOf G₄ m₁₇ 2 = hk2 := by
    have r : m₁₇.threads[2]? = some { spawner := 0, joined := false } := r2₁₇
    simp [ownOf, joinedB, r, hf2, Gh.heap]
  have hd12 : Heap.Disjoint hk1 hk2 := by
    have := hi₁₇.own.disj 0 2 (by decide); rwa [e0, e2] at this
  rw [e0, e2, upd_comm _ _ _ (show (0 : Nat) ≠ 2 by decide)] at ho₁₈
  have hA : ((ctxA s6 A1 s2 a ∗ flagA s2 Ax a) ∗ (ctxA s11 A2 s4 b ∗ flagA s4 Ay b)) (hk1 ∪ hk2) :=
    ⟨hk1, hk2, hd12, rfl, hma₁₇, hka2⟩
  have hja : joinedAll 0 m₁₈ := by
    intro r hr _
    rw [hth₁₈] at hr
    obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hr
    have hi' : i < 3 := by simpa [hsz₁₇] using hi
    have hget : (m₁₇.threads.setIfInBounds 2 { spawner := 0, joined := true })[i]? = some r := by
      rw [Array.getElem?_eq_getElem hi, he]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · rw [Array.getElem?_setIfInBounds_ne (by decide), hi₁₇.t0] at hget; cases hget; rfl
    · rw [Array.getElem?_setIfInBounds_ne (by decide), r1₁₇] at hget; cases hget; rfl
    · rw [Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz₁₇]; decide)] at hget; cases hget; rfl
  have htl : 0 < m₁₈.threads.size := by rw [hth₁₈, Array.size_setIfInBounds, hsz₁₇]; decide
  -- `x +% y`.
  refine WP.bind (WP.liftM_upd ((TTriple.loadAt (k := 0) (a := 4) (v := a) (by simp [Ptr.add])
    (by decide) (by rw [enc_u32]; decide) (by simp [hx0, hAx]) (decode_u32 a)).frameL_eq.frame_eq)
    ho₁₈ hc₁₈ htl hA fun r₁ m₁₉ h₁₉ ho₁₉ hq₁₉ hc₁₉ ht₁₉ => ?_)
  obtain ⟨hr₁, hA₁₉⟩ := sep_lift.mp hq₁₉
  refine WP.bind (WP.liftM_upd ((TTriple.loadAt (k := 0) (a := 4) (v := b) (by simp [Ptr.add])
    (by decide) (by rw [enc_u32]; decide) (by simp [hy0, hAy]) (decode_u32 b)).frameL_eq.frameL_eq)
    ho₁₉ hc₁₉ (by rw [ht₁₉]; exact htl) hA₁₉ fun r₂ m₂₀ h₂₀ ho₂₀ hq₂₀ hc₂₀ ht₂₀ => ?_)
  obtain ⟨hr₂, hA₂₀⟩ := sep_lift.mp hq₂₀
  refine WP.pure' ?_
  -- The frees.
  have htl₂₀ : 0 < m₂₀.threads.size := by rw [ht₂₀, ht₁₉]; exact htl
  refine WP.bind (WP.liftMem_upd ((free_front (R := ctxA s6 A1 s2 a ∗ (ctxA s11 A2 s4 b ∗
    flagA s4 Ay b)) (enc_u32 a) hx0 (by decide)).conseq (fun _ h => sep_left_comm (sep_assoc h))
    fun _ _ h => h) ho₂₀ hc₂₀ htl₂₀ hA₂₀ fun _ m₂₁ h₂₁ ho₂₁ hq₂₁ hc₂₁ ht₂₁ => ?_)
  refine WP.bind (WP.liftMem_upd ((free_front (R := ctxA s6 A1 s2 a ∗ ctxA s11 A2 s4 b)
    (enc_u32 b) hy0 (by decide)).conseq
    (fun _ h => sep_left_comm (sep_mono (fun _ h => h) (fun _ h => sep_comm h) h)) fun _ _ h => h)
    ho₂₁ hc₂₁ (by rw [ht₂₁]; exact htl₂₀) hq₂₁ fun _ m₂₂ h₂₂ ho₂₂ hq₂₂ hc₂₂ ht₂₂ => ?_)
  refine WP.bind (WP.liftMem_upd (free_front (R := ctxA s11 A2 s4 b) (ctxBytes_size s2 a) h10
    (by decide)) ho₂₂ hc₂₂ (by rw [ht₂₂, ht₂₁]; exact htl₂₀) hq₂₂
    fun _ m₂₃ h₂₃ ho₂₃ hq₂₃ hc₂₃ ht₂₃ => ?_)
  refine WP.bind (WP.liftMem_upd (TTriple.free (ctxBytes_size s4 b) h20 (by decide)) ho₂₃ hc₂₃
    (by rw [ht₂₃, ht₂₂, ht₂₁]; exact htl₂₀) hq₂₃ fun _ m₂₄ _ _ _ _ ht₂₄ => ?_)
  refine WP.pure' ⟨by simp [hr₁, hr₂, addWrap], fun r hr hs => hja r ?_ hs⟩
  rwa [ht₂₄, ht₂₃, ht₂₂, ht₂₁, ht₂₀, ht₁₉] at hr

/-! ## The results -/

/-- **`disjoint a b` gives `a + b` (wrapping) under every schedule** (every oracle `o`, every
`fuel`). -/
theorem disjoint_spec {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run dispatch fuel o (disjoint a b) mem0).run = some (.ok (v, m))) :
    v = .ok (a + b) := by
  obtain ⟨_, _, hv, -⟩ := (proto a b).run_sound dispatch (fun _ => .none) dispatch_spec
    (fun _ _ _ _ _ hq => hq.2) rfl main_spec h
  exact hv

/-- **No run of `disjoint a b` gives an error**, under any schedule: no data race (the two threads
write disjoint bytes), no other illegal behaviour. -/
theorem disjoint_safe {fuel : Nat} {o : Nat → Nat} {e : Error} :
    (Sched.run dispatch fuel o (disjoint a b) mem0).run ≠ some (.error e) :=
  (proto a b).run_safe dispatch (fun _ => .none) rfl dispatch_spec (fun _ _ _ _ hq => hq.2) rfl
    main_spec

end Threads.Disjoint
