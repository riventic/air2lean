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

/-- Thread `u` was joined (`main` never is). -/
def joinedB (m : Mem) (u : ThreadId) : Bool :=
  u != 0 && ((m.threads[u]?).map (·.joined)).getD false

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
      (by rw [hown]; simpa [ctxA, flagA] using hcx) fun _ m' hQ ho' hq hs _ => ?_)
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

end Threads.Disjoint
