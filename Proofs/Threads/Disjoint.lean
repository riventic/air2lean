import Proofs.Threads.Gen
import ZigLean.Simp
import ZigLean.Conc.Witness
import ZigLean.Sep.Full.ThreadOwned
import ZigLean.Sep.Full.Local
import ZigLean.Sep.Full.Init
import ZigLean.Sep.Full.Witness
import ZigLean.Sep.Full.Auto

/-!
# `disjoint` over all schedules: concurrent separation logic

`disjoint a b` makes two flags `x`, `y` and two contexts `c1 = {&x, a}`, `c2 = {&y, b}`, spawns
`writeFlag(&c1)` and `writeFlag(&c2)`, joins both and returns `x +% y`. It is `race` with two
flags in place of one. The result is `a + b` (wrapping) under every schedule (`disjoint_spec`), and no
schedule gives an error (`disjoint_safe`): the two threads write disjoint bytes, so no race.

The proof is in the full-state concurrent separation logic (`docs/sep-threads.md`): each thread
owns whole blocks (their bytes and full extents, `blk`), and the blocks move at the spawns and the
joins.

- **`writeFlag`** is a thread triple (`FTTriple`) over the two blocks that the thread owns
  (`writeFlag_spec`): its context and its flag.
- **Ghost values** (`Gh`). `main` has its phase, the resource it owns and the four blocks
  (`Blks`); a kid has the resource it owns, its context, its flag, its value and whether it is
  done.
- **Invariant** (`Inv`). The threads' resources are the parts of `FOwned` (a joined thread owns
  nothing); a kid's part holds its context and its flag (the value when done); `main`'s part is
  the one of its phase; the threads are those of the phase.
- **`main`**: before the first spawn it owns all four blocks; it gives `{c1, x}` to kid 1 and
  `{c2, y}` to kid 2 (`FOwned.fork`); at each join it takes the kid's blocks back
  (`FOwned.join`), with the flag written.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Threads

namespace Threads.Disjoint

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/RwLock.lean`).
attribute [local irreducible] Proto.WP

/-! ## Assertions -/

/-- A stack block of the thread: its bytes and its full extent. -/
abbrev blk (p : Ptr) (A S : Nat) (bs : Array Byte) (b : BlockId) : FAssn :=
  up (bytesAt p A S .stack bs) ⋆ bext b S .stack

theorem sep_lcomm {P Q R : FAssn} {r : Res} (h : (P ⋆ (Q ⋆ R)) r) : (Q ⋆ (P ⋆ R)) r :=
  sep_assoc (sep_mono_left (fun _ h => sep_comm h) (sep_assoc' h))

theorem sep_ex2_lift {R : FAssn} {φ : Nat → BlockId → Prop} {P : Nat → BlockId → FAssn} {r : Res}
    (h : (R ⋆ FAssn.ex fun A => FAssn.ex fun b => ⟪φ A b⟫ ⋆ P A b) r) :
    ∃ A b, φ A b ∧ (R ⋆ P A b) r := by
  obtain ⟨r₁, r₂, hd, e, hr, A, b, hp⟩ := h
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact ⟨A, b, hφ, r₁, r₂, hd, e, hr, hp⟩

/-! ## `writeFlag` -/

theorem writeFlag_eq (c : Ptr) : writeFlag c = (Zig.load Ptr 8 c >>= fun xp =>
    ptrProject c (·.add 8) >>= fun q => Zig.load (BitVec 32) 4 q >>= fun v =>
      Zig.store (α := BitVec 32) 4 xp v) := by
  unfold writeFlag
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_monadLift, callM, StateT.run_lift]

/-- `writeFlag(c)` reads the flag `x` and the value `v` of its context `c` and writes `v` to the
flag. -/
theorem writeFlag_spec {c x : Ptr} {bc bx : BlockId} {Ac Ax : Nat} {cb xb : Array Byte}
    {v : BitVec 32} (hcb : c.block = some bc) (hxb : x.block = some bx)
    (hc0 : c.off = 0) (hAc : Ac % 8 = 0) (hx0 : x.off = 0) (hAx : Ax % 4 = 0)
    (hcs : cb.size = 16) (hxs : xb.size = 4)
    (hcx : Enc.decode (cb.extract 0 8) = pure x) (hcv : Enc.decode (cb.extract 8 12) = pure v) :
    FTTriple (blk c Ac 16 cb bc ⋆ blk x Ax 4 xb bx) (writeFlag c)
      (fun _ => blk c Ac 16 cb bc ⋆ blk x Ax 4 (Enc.encode v) bx) := by
  rw [writeFlag_eq]
  have hlx : FTTriple (blk c Ac 16 cb bc) (Zig.load Ptr 8 c)
      (fun r => ⟪r = x⟫ ⋆ blk c Ac 16 cb bc) := by
    fsym [FTotalTriple.loadBlock (T := Ptr) (A := Ac) (S := 16) (K := .stack) (al := 8) hcb
      (by decide) (by rw [hcs]; decide) hcx (by simp [hc0, hAc])]
  have hlv : FTTriple (blk c Ac 16 cb bc) (Zig.load (BitVec 32) 4 (c.add 8))
      (fun r => ⟪r = v⟫ ⋆ blk c Ac 16 cb bc) := by
    fsym [FTotalTriple.load_bytesAt (q := c) (k := 8) (al := 4) (A := Ac) (S := 16) (K := .stack)
      (bs := cb) (T := BitVec 32) (by decide) (by rw [hcs]; decide) (by simp [hc0]; omega) hcv]
  refine FTTriple.bind (hlx.frame.post fun _ _ h => sep_assoc h)
    fun xp => FTTriple.lift fun hxp => ?_
  subst xp
  refine FTTriple.bind ((FTTriple.ptrProjectAt (k := 8) hcb (by rw [hcs]; decide)
    (by rw [hcs]; decide)).frame.post fun _ _ h => sep_assoc h) fun q => FTTriple.lift fun hq => ?_
  subst q
  refine FTTriple.bind (hlv.frame.post fun _ _ h => sep_assoc h)
    fun w => FTTriple.lift fun hw => ?_
  subst w
  refine (FTTriple.storeAt (k := 0) (a := 4) v hxb (by simp [Ptr.add]) (by decide)
    (by rw [hxs]; decide) (by simp [hx0, hAx]) (by decide)).frameL.post fun _ _ h => ?_
  rwa [writeBytes_all (by rw [hxs, LawfulEnc.size_encode]; rfl)] at h

/-! ## Blocks and resources -/

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

/-- A context at `c` (block `bc`, address `A`) with the flag `f` and the value `v`. -/
abbrev ctxF (c : Ptr) (bc : BlockId) (A : Nat) (f : Ptr) (v : BitVec 32) : FAssn :=
  blk c A 16 (ctxBytes f v) bc

/-- A flag at `x` (block `bx`, address `A`) that holds `w`. -/
abbrev flagF (x : Ptr) (bx : BlockId) (A : Nat) (w : BitVec 32) : FAssn :=
  blk x A 4 (Enc.encode w) bx

/-- The four blocks of `disjoint`, with their block ids and addresses. -/
structure Blks where
  x : Ptr
  y : Ptr
  c1 : Ptr
  c2 : Ptr
  kx : BlockId
  ky : BlockId
  k1 : BlockId
  k2 : BlockId
  ax : Nat
  ay : Nat
  a1 : Nat
  a2 : Nat

/-- Each block is its pointer's, starting at offset 0, at an aligned address. -/
def Blks.Ok (B : Blks) : Prop :=
  B.x.block = some B.kx ∧ B.y.block = some B.ky ∧ B.c1.block = some B.k1 ∧
    B.c2.block = some B.k2 ∧
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
  /-- `main` at the phase `ph`: it owns `r`. -/
  | main (ph : Ph) (r : Res) (B : Blks)
  /-- A kid: it owns `r`, its context `c` (address `ac`) holds its flag `x` (address `ax`) and
  its value `v`; `done`: it wrote `v`. -/
  | kid (r : Res) (c : Ptr) (ac : Nat) (x : Ptr) (ax : Nat) (v : BitVec 32) (done : Bool)

/-- The resource that a thread owns. -/
def Gh.res : Gh → Res
  | .main _ r _ | .kid r _ _ _ _ _ _ => r
  | .none => rnil

/-- A kid's part: its context and its flag, with `v` when it is done. -/
def KidA (c : Ptr) (ac : Nat) (x : Ptr) (ax : Nat) (v : BitVec 32) (done : Bool) : FAssn :=
  FAssn.ex fun bc : BlockId => FAssn.ex fun bx : BlockId =>
    ⟪c.block = some bc ∧ x.block = some bx ∧ c.off = 0 ∧ ac % 8 = 0 ∧ x.off = 0 ∧ ax % 4 = 0⟫ ⋆
      (ctxF c bc ac x v ⋆ flagF x bx ax (if done then v else 0))

variable (a b : BitVec 32)

/-- `main`'s part at each phase. -/
def MainA (B : Blks) : Ph → FAssn
  | .pre => flagF B.x B.kx B.ax 0 ⋆ (flagF B.y B.ky B.ay 0 ⋆
      (ctxF B.c1 B.k1 B.a1 B.x a ⋆ ctxF B.c2 B.k2 B.a2 B.y b))
  | .one => flagF B.y B.ky B.ay 0 ⋆ ctxF B.c2 B.k2 B.a2 B.y b
  | .j1 => emp
  | .j2 => ctxF B.c1 B.k1 B.a1 B.x a ⋆ flagF B.x B.kx B.ax a

/-- Thread `u` is kid 1 (`i = 1`) or kid 2 of the blocks `B`. -/
def IsKid (B : Blks) (G : ThreadId → Gh) (u : ThreadId) (done : Option Bool) : Prop :=
  ∃ r d, (done = none ∨ done = some d) ∧
    G u = if u = 1 then .kid r B.c1 B.a1 B.x B.ax a d else .kid r B.c2 B.a2 B.y B.ay b d

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

/-- The parts of the threads: a joined thread owns nothing. -/
def ownOf (G : ThreadId → Gh) (m : Mem) (u : ThreadId) : Res :=
  if joinedB m u then rnil else (G u).res

/-- The invariant (module doc). -/
structure Inv (G : ThreadId → Gh) (m : Mem) : Prop where
  own : ∃ rO, FOwned (ownOf G m) rO m
  kids : ∀ u r c ac x ax v d, G u = .kid r c ac x ax v d → KidA c ac x ax v d r
  main : ∃ ph r B, G 0 = .main ph r B ∧ B.Ok ∧ MainA a b B ph r ∧ Shape a b B G m ph
  t0 : m.threads[0]? = some { spawner := 0, joined := true }

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv := Inv a b
  init tgt g := match tgt with
    | .writeFlag c => ∃ r ac x ax v, g = .kid r c ac x ax v false
    | _ => False
  fin g := ∃ r c ac x ax v, g = .kid r c ac x ax v true
  strict := true
  joins g := ∃ r B, g = .main .j1 r B ∨ g = .main .j2 r B

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok (a + b) ∧ joinedAll 0 m

/-! ## The kids -/

variable {a b}

/-- A kid that is not done was not joined, and is a thread. -/
theorem kid_live {G : ThreadId → Gh} {m : Mem} {u : ThreadId} {r c ac x ax v}
    (hi : Inv a b G m) (hu : 0 < u) (hg : G u = .kid r c ac x ax v false) :
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
    ownOf (upd G u g) m' = upd (ownOf G m) u g.res := by
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
    obtain ⟨r, ac, x, ax, v, rfl⟩ := hg
    obtain ⟨hj, hut, h12⟩ := kid_live hi hu hgu
    obtain ⟨bc, bx, hka⟩ := hi.kids u _ _ _ _ _ _ _ hgu
    obtain ⟨⟨hcb, hxb, hc0, hac, hx0, hax⟩, hcx⟩ := sep_lift.mp hka
    have hown : ownOf G m u = r := by unfold ownOf; rw [hj, hgu]; rfl
    obtain ⟨rO, ho⟩ := hi.own
    show (proto a b).WP u ((fun _ => ()) <$> ConcM.liftMem (writeFlag c)) _ G _ d
    refine WP.map (WP.liftMem_fowned (own := ownOf G m)
      (writeFlag_spec (xb := Enc.encode (0 : BitVec 32)) hcb hxb hc0 hac hx0 hax
        (ctxBytes_size x v) (enc_u32 0) (ctxBytes_flag x v) (ctxBytes_val x v)) (ho.current u) rfl hut
      (by rw [hown]; exact hcx) fun _ m' r' _ ho' hq _ hth => ?_)
    refine ⟨.kid r' c ac x ax v true, ?_, ⟨_, _, _, _, _, _, rfl⟩, fun _ => ?_⟩
    · refine ⟨⟨rO, ?_⟩, fun w r₁ c' ac' x' ax' v' d' hw => ?_, ?_, ?_⟩
      · rw [ownOf_upd hth hj]; exact ho'
      · by_cases hwu : w = u
        · subst hwu; rw [upd_self] at hw; cases hw
          exact ⟨bc, bx, sep_lift.mpr ⟨⟨hcb, hxb, hc0, hac, hx0, hax⟩, hq⟩⟩
        · rw [upd_ne _ _ hwu] at hw; exact hi.kids w _ _ _ _ _ _ _ hw
      · obtain ⟨ph, hm, B, h0, hB, hma, hsh⟩ := hi.main
        refine ⟨ph, hm, B, by rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact h0, hB, hma, ?_⟩
        have hkid : ∀ w dn, IsKid a b B G w dn → w ≠ u ∨ dn = none →
            IsKid a b B (upd G u (.kid r' c ac x ax v true)) w dn := by
          intro w dn ⟨h', d', hd', hk⟩ hw
          by_cases hwu : w = u
          · subst hwu
            rcases hw with hw | rfl
            · exact absurd rfl hw
            · refine ⟨r', true, .inl rfl, ?_⟩
              rw [upd_self]
              rw [hgu] at hk
              by_cases h1 : w = 1
              · simp only [h1, ↓reduceIte] at hk ⊢; cases hk; rfl
              · simp only [h1, ↓reduceIte] at hk ⊢; cases hk; rfl
          · exact ⟨h', d', hd', by rw [upd_ne _ _ hwu]; exact hk⟩
        have hnone : ∀ k, (∀ w, k ≤ w → G w = .none) →
            ∀ w, k ≤ w → upd G u (.kid r' c ac x ax v true) w = .none := by
          intro k hk w hw
          by_cases hwu : w = u
          · subst hwu; have := hk w hw; rw [hgu] at this; cases this
          · rw [upd_ne _ _ hwu]; exact hk w hw
        have hrec : ∀ w jn, KidRec m w jn → KidRec m' w jn := by
          intro w jn hr; unfold KidRec; rw [hth]; exact hr
        cases ph with
        | pre => exact ⟨by rw [hth]; exact hsh.1, hnone 1 hsh.2⟩
        | one =>
          obtain ⟨hsz, r1, k1, hn⟩ := hsh
          exact ⟨by rw [hth]; exact hsz, hrec _ _ r1, hkid 1 _ k1 (.inr rfl), hnone 2 hn⟩
        | j1 =>
          obtain ⟨hsz, r1, r2, k1, k2, hn⟩ := hsh
          exact ⟨by rw [hth]; exact hsz, hrec _ _ r1, hrec _ _ r2, hkid 1 _ k1 (.inr rfl),
            hkid 2 _ k2 (.inr rfl), hnone 3 hn⟩
        | j2 =>
          obtain ⟨hsz, r1, r2, k1, k2, hn⟩ := hsh
          have hu1 : u ≠ 1 := by
            intro h1; subst h1
            obtain ⟨h', d', hd', hk⟩ := k1
            rw [hgu] at hk; simp only [↓reduceIte] at hk; cases hk
            simp at hd'
          exact ⟨by rw [hth]; exact hsz, hrec _ _ r1, hrec _ _ r2,
            hkid 1 _ k1 (.inl (Ne.symm hu1)), hkid 2 _ k2 (.inr rfl), hnone 3 hn⟩
      · rw [hth]; exact hi.t0
    · intro r hr hsp
      rw [hth] at hr
      rw [spawner0 hi r hr] at hsp
      unfold ThreadId at *; omega
  | _ => exact hg.elim

/-! ## `main` -/

/-- `main`'s ghost value and no kid: the parts. -/
theorem ownOf_main (m : Mem) (g : Gh) :
    ownOf (upd (fun _ => .none) 0 g) m = upd (fun _ => rnil) 0 g.res := by
  funext u
  by_cases hu : u = 0
  · subst hu; simp [ownOf, joinedB, upd]
  · simp only [ownOf, upd, hu, ↓reduceIte, Gh.res]; split <;> rfl

theorem enc_zero : writeBytes (Array.replicate 4 .undef) 0 (Enc.encode (0 : BitVec 32)) =
    Enc.encode (0 : BitVec 32) :=
  writeBytes_all (by simp [enc_u32])

/-- `main`'s four blocks: it keeps `y`, `c2` and gives `c1`, `x` to kid 1. -/
theorem split_pre {X Y C1 C2 : FAssn} {r : Res} (hh : (X ⋆ (Y ⋆ (C1 ⋆ C2))) r) :
    ((Y ⋆ C2) ⋆ (C1 ⋆ X)) r := by
  have h1 := sep_lcomm hh
  refine sep_assoc' (sep_mono (fun _ h => h) (fun _ h => ?_) h1)
  exact sep_lcomm (sep_assoc (sep_comm h))

theorem decode_u32 (v : BitVec 32) : Enc.decode ((Enc.encode v).extract 0 (0 + Enc.size (BitVec 32))) =
    (pure v : Result (BitVec 32)) := by
  rw [show 0 + Enc.size (BitVec 32) = (Enc.encode v).size from (enc_u32 v).symm, Array.extract_size]
  exact LawfulEnc.decode_encode v

/-- The load of a `u32` stack word. -/
theorem blk_load {p : Ptr} {A : Nat} {w : BitVec 32} {b : BlockId} (hpb : p.block = some b)
    (h0 : p.off = 0) (hA : A % 4 = 0) :
    FTTriple (blk p A 4 (Enc.encode w) b) (Zig.load (BitVec 32) 4 p)
      (fun r => ⟪r = w⟫ ⋆ blk p A 4 (Enc.encode w) b) := by
  fsym [FTotalTriple.loadBlock (T := BitVec 32) (A := A) (S := 4) (K := .stack) (al := 4) hpb
    (by decide) (by rw [enc_u32]; decide) (decode_u32 w) (by simp [h0, hA])]

/-- The start memory holds the parts: `main` holds the plain mode, no thread owns anything else. -/
theorem start (σ : Placement) :
    ∃ rO, FOwned plainOwn rO { mem0 σ with current := 0 } := by
  have hs := Mem.init_fseq σ [] (by decide)
  exact ⟨_, FOwned.start_plain (m := { mem0 σ with current := 0 }) rfl rfl hs.2.1 hs.2.2
    (Mem.MsgCov.of_atomics rfl) (by simp [mem0, Mem.ofGlobals])⟩

set_option maxHeartbeats 1000000 in
theorem main_spec (σ : Placement) (d : Nat) : (proto a b).WP 0 (disjoint a b) (QM a b) (fun _ => .none)
    { mem0 σ with current := 0 } d := by
  unfold disjoint
  obtain ⟨rO, ho₀⟩ := start σ
  -- The four blocks: stack blocks in the plain mode (`main` uses it up with the last one).
  refine WP.bind (WP.liftMem_fowned (FTTriple.allocStack 4 4 (by decide) (by decide)) ho₀ rfl
    (by simp [mem0, Mem.ofGlobals]) (by rw [plainOwn_zero]; exact plain_intro)
    fun s2 m₁ r₁ _ ho₁ hq₁ hc₁ ht₁ => ?_)
  obtain ⟨Ax, kx, hA⟩ := hq₁
  obtain ⟨⟨hxb, hx0, hAx⟩, hx⟩ := sep_lift.mp hA
  refine WP.bind (WP.liftMem_fowned ((FTTriple.allocStack 4 4 (by decide) (by decide)).frameL)
    ho₁ hc₁ (by rw [ht₁]; simp [mem0, Mem.ofGlobals]) hx
    fun s4 m₂ r₂ _ ho₂ hq₂ hc₂ ht₂ => ?_)
  obtain ⟨Ay, ky, ⟨hyb, hy0, hAy⟩, hy⟩ := sep_ex2_lift hq₂
  refine WP.bind (WP.liftMem_fowned (((FTTriple.allocStack 16 8 (by decide) (by decide)).frameL).pre
    fun _ h => sep_assoc' h) ho₂ hc₂ (by rw [ht₂, ht₁]; simp [mem0, Mem.ofGlobals]) hy
    fun s6 m₃ r₃ _ ho₃ hq₃ hc₃ ht₃ => ?_)
  obtain ⟨A1, k1, ⟨h1b, h10, hA1⟩, hc1⟩ := sep_ex2_lift hq₃
  refine WP.bind (WP.liftMem_fowned (((FTTriple.allocStackDrop 16 8 (by decide) (by decide)).frameL).pre
    fun _ h => sep_assoc' h) ho₃ hc₃ (by rw [ht₃, ht₂, ht₁]; simp [mem0, Mem.ofGlobals]) hc1
    fun s11 m₄ r₄ _ ho₄ hq₄ hc₄ ht₄ => ?_)
  obtain ⟨A2, k2, ⟨h2b, h20, hA2⟩, hc2⟩ := sep_ex2_lift hq₄
  have htt₄ : m₄.threads = #[{ spawner := 0, joined := true }] := by rw [ht₄, ht₃, ht₂, ht₁] <;> rfl
  have F₄ := sep_assoc (sep_assoc hc2)
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  -- `x = 0`, `y = 0`, `c1 = {&x, a}`, `c2 = {&y, b}`.
  refine WP.bind (WP.liftM_fowned ((FTTriple.storeAt (k := 0) (a := 4) (0 : BitVec 32) hxb
    (by simp [Ptr.add]) (by decide) (by simp; decide) (by simp [hx0, hAx]) (by decide)).frame) ho₄ hc₄
    (by rw [htt₄]; decide) F₄ fun _ m₅ r₅ _ ho₅ F₅ hc₅ ht₅ => ?_)
  refine WP.bind (WP.liftM_fowned ((FTTriple.storeAt (k := 0) (a := 4) (0 : BitVec 32) hyb
    (by simp [Ptr.add]) (by decide) (by simp; decide) (by simp [hy0, hAy]) (by decide)).frame.frameL)
    ho₅ hc₅ (by rw [ht₅, htt₄]; decide) F₅ fun _ m₆ r₆ _ ho₆ F₆ hc₆ ht₆ => ?_)
  refine WP.bind (WP.liftM_fowned ((FTTriple.storeAt (k := 0) (a := 8) s2 h1b
    (by simp) (by decide) (by simp; decide) (by simp [h10, hA1]) (by decide)).frame.frameL.frameL)
    ho₆ hc₆ (by rw [ht₆, ht₅, htt₄]; decide) F₆ fun _ m₇ r₇ _ ho₇ F₇ hc₇ ht₇ => ?_)
  refine WP.bind (WP.callMC_fowned ((FTTriple.ptrProjectAt (k := 8) h1b
    (by rw [ctxBytes_one]; decide) (by rw [ctxBytes_one]; decide)).frame.frameL.frameL.post
    fun _ _ h => sep_lcomm (sep_mono_right (fun _ h => sep_lcomm (sep_mono_right
      (fun _ h => sep_assoc h) h)) h))
    ho₇ hc₇ (by rw [ht₇, ht₆, ht₅, htt₄]; decide) F₇ fun q₁ m₇' r₇' _ ho₇' L₇ hc₇' ht₇' => ?_)
  obtain ⟨rfl, F₇'⟩ := sep_lift.mp L₇
  dsimp only
  refine WP.bind (WP.liftM_fowned ((FTTriple.storeAt (k := 8) (a := 4) (A := A1) (S := 16) (K := .stack)
    (bs := writeBytes (Array.replicate 16 .undef) 0 (Enc.encode s2)) a h1b rfl (by decide) (by rw [ctxBytes_one]; decide) (by simp [h10]; omega) (by decide)).frame.frameL.frameL)
    ho₇' hc₇' (by rw [ht₇', ht₇, ht₆, ht₅, htt₄]; decide) F₇' fun _ m₈ r₈ _ ho₈ F₈ hc₈ ht₈ => ?_)
  refine WP.bind (WP.liftM_fowned ((FTTriple.storeAt (k := 0) (a := 8) s4 h2b
    (by simp) (by decide) (by simp; decide) (by simp [h20, hA2]) (by decide)).frameL.frameL.frameL)
    ho₈ hc₈ (by rw [ht₈, ht₇', ht₇, ht₆, ht₅, htt₄]; decide) F₈ fun _ m₉ r₉ _ ho₉ F₉ hc₉ ht₉ => ?_)
  refine WP.bind (WP.callMC_fowned ((FTTriple.ptrProjectAt (k := 8) h2b
    (by rw [ctxBytes_one]; decide) (by rw [ctxBytes_one]; decide)).frameL.frameL.frameL.post
    fun _ _ h => sep_lcomm (sep_mono_right (fun _ h => sep_lcomm (sep_mono_right
      (fun _ h => sep_lcomm h) h)) h))
    ho₉ hc₉ (by rw [ht₉, ht₈, ht₇', ht₇, ht₆, ht₅, htt₄]; decide) F₉
    fun q₂ m₉' r₉' _ ho₉' L₉ hc₉' ht₉' => ?_)
  obtain ⟨rfl, F₉'⟩ := sep_lift.mp L₉
  dsimp only
  refine WP.bind (WP.liftM_fowned ((FTTriple.storeAt (k := 8) (a := 4) (A := A2) (S := 16) (K := .stack)
    (bs := writeBytes (Array.replicate 16 .undef) 0 (Enc.encode s4)) b h2b rfl (by decide) (by rw [ctxBytes_one]; decide) (by simp [h20]; omega) (by decide)).frameL.frameL.frameL)
    ho₉' hc₉' (by rw [ht₉', ht₉, ht₈, ht₇', ht₇, ht₆, ht₅, htt₄]; decide) F₉'
    fun _ m₁₀ r₁₀ _ ho₁₀ F₁₀ hc₁₀ ht₁₀ => ?_)
  have htt₁₀ : m₁₀.threads = #[{ spawner := 0, joined := true }] := by
    rw [ht₁₀, ht₉', ht₉, ht₈, ht₇', ht₇, ht₆, ht₅, htt₄]
  rw [enc_zero] at F₁₀
  dsimp only at F₁₀ ⊢
  -- The first spawn: kid 1 gets `c1` and `x`.
  let B : Blks := ⟨s2, s4, s6, s11, kx, ky, k1, k2, Ax, Ay, A1, A2⟩
  have hB : B.Ok := ⟨hxb, hyb, h1b, h2b, hx0, hy0, h10, h20, hAx, hAy, hA1, hA2⟩
  have hM : MainA a b B .pre r₁₀ := F₁₀
  obtain ⟨rP, rK1, hdPK, rfl, hPa, hKa⟩ := split_pre hM
  refine WP.bind (WP.spawnC fun k _ => ⟨.main .pre (rsum rP rK1) B, ?_, fun G₁ m₁₁ hg₁ hi₁₁ =>
    ⟨.kid rK1 s6 A1 s2 Ax a false, ⟨_, _, _, _, _, rfl⟩, fun child m₁₂ hf => ?_⟩⟩)
  · refine ⟨⟨rO, by rw [ownOf_main]; simp only [plainOwn, upd_upd] at ho₁₀; exact ho₁₀⟩,
      fun u _ _ _ _ _ _ _ hu => ?_,
      ⟨.pre, _, B, upd_self _ _ _, hB, hM, by rw [htt₁₀]; rfl, fun u hu => ?_⟩, by rw [htt₁₀]; rfl⟩
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu; cases hu
    · rw [upd_ne _ _ (by unfold ThreadId at *; omega)]
  obtain ⟨ph, hm, B', h0, -, -, hsh⟩ := hi₁₁.main
  rw [hg₁] at h0; cases h0
  obtain ⟨hsz₁₁, hn₁₁⟩ := hsh
  obtain ⟨rfl, hth₁₂⟩ := fork_threads hf
  obtain ⟨rO₁₁, ho₁₁⟩ := hi₁₁.own
  have hown₁₁ : ownOf G₁ m₁₁ 0 = ⟨rP.heap ∪ rK1.heap, rP.know.union rK1.know, rP.gh.add rK1.gh⟩ := by
    simp [ownOf, joinedB, hg₁, Gh.res]
  have ho₁₂ := FOwned.fork (ho₁₁.current 0) (by rw [hsz₁₁]; decide) hown₁₁ hdPK hf
  rw [hsz₁₁] at ho₁₂ ⊢
  dsimp only
  have hjb₁₂ : joinedB m₁₂ = joinedB m₁₁ := joinedB_fork hf
  have hjb1 : joinedB m₁₁ 1 = false := by
    simp [joinedB, Array.getElem?_eq_none (show m₁₁.threads.size ≤ 1 by omega)]
  have hi₁₂ : Inv a b (upd (upd G₁ 1 (.kid rK1 s6 A1 s2 Ax a false)) 0 (.main .one rP B)) m₁₂ := by
    refine ⟨⟨rO₁₁, ?_⟩, fun u h c ac x ax v dn hu => ?_, ⟨.one, rP, B, upd_self _ _ _, hB, hPa, ?_⟩, ?_⟩
    · have e : ownOf (upd (upd G₁ 1 (.kid rK1 s6 A1 s2 Ax a false)) 0 (.main .one rP B)) m₁₂ =
          upd (upd (ownOf G₁ m₁₁) 0 rP) 1 rK1 := by
        funext u
        unfold ownOf
        rw [hjb₁₂]
        by_cases h0 : u = 0
        · subst h0; simp [joinedB, upd, Gh.res]
        · by_cases h1 : u = 1
          · subst h1; simp [hjb1, upd, Gh.res]
          · simp [upd, h0, h1]
      rw [e]; exact ho₁₂
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu
        by_cases h1 : u = 1
        · subst h1; rw [upd_self] at hu; cases hu
          exact ⟨k1, kx, sep_lift.mpr ⟨⟨h1b, hxb, h10, hA1, hx0, hAx⟩, hKa⟩⟩
        · rw [upd_ne _ _ h1, hn₁₁ u (by unfold ThreadId at *; omega)] at hu; cases hu
    · refine ⟨by rw [hth₁₂]; simp [hsz₁₁], ?_, ⟨rK1, false, .inl rfl, by simp [upd, B]⟩,
        fun u hu => ?_⟩
      · unfold KidRec; rw [hth₁₂, Array.getElem?_push, if_pos hsz₁₁.symm]
      · rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega),
          hn₁₁ u (by unfold ThreadId at *; omega)]
    · rw [hth₁₂, Array.getElem?_push, if_neg (by omega)]; exact hi₁₁.t0
  -- The second spawn: kid 2 gets `c2` and `y`; `main` owns nothing.
  simp only [StateT.run_bind]
  refine WP.bind (WP.spawnC fun k _ => ⟨Gh.main .one rP B, hi₁₂, fun G₂ m₁₃ hg₂ hi₁₃ =>
    ⟨Gh.kid rP s11 A2 s4 Ay b false, ⟨_, _, _, _, _, rfl⟩, fun child m₁₄ hf₂ => ?_⟩⟩)
  obtain ⟨ph, hm, B', h0, -, -, hsh⟩ := hi₁₃.main
  rw [hg₂] at h0; cases h0
  obtain ⟨hsz₁₃, r1₁₃, k1₁₃, hn₁₃⟩ := hsh
  obtain ⟨rfl, hth₁₄⟩ := fork_threads hf₂
  obtain ⟨rO₁₃, ho₁₃⟩ := hi₁₃.own
  have hown₁₃ : ownOf G₂ m₁₃ 0 = ⟨rnil.heap ∪ rP.heap, rnil.know.union rP.know, rnil.gh.add rP.gh⟩ := by
    simp [ownOf, joinedB, hg₂, Gh.res, Know.none_union]
  have ho₁₄ := FOwned.fork (ho₁₃.current 0) (by rw [hsz₁₃]; decide) hown₁₃
    (FHeap.disjoint_empty _).symm hf₂
  rw [hsz₁₃] at ho₁₄ ⊢
  dsimp only
  have hjb₁₄ : joinedB m₁₄ = joinedB m₁₃ := joinedB_fork hf₂
  have hjb2 : joinedB m₁₃ 2 = false := by
    simp [joinedB, Array.getElem?_eq_none (show m₁₃.threads.size ≤ 2 by omega)]
  have hi₁₄ : Inv a b (upd (upd G₂ 2 (.kid rP s11 A2 s4 Ay b false)) 0 (.main .j1 rnil B))
      m₁₄ := by
    refine ⟨⟨rO₁₃, ?_⟩, fun u h c ac x ax v dn hu => ?_,
      ⟨.j1, rnil, B, upd_self _ _ _, hB, ⟨rfl, rfl, rfl⟩, ?_⟩, ?_⟩
    · have e : ownOf (upd (upd G₂ 2 (.kid rP s11 A2 s4 Ay b false)) 0 (.main .j1 rnil B))
          m₁₄ = upd (upd (ownOf G₂ m₁₃) 0 rnil) 2 rP := by
        funext u
        unfold ownOf
        rw [hjb₁₄]
        by_cases h0 : u = 0
        · subst h0; simp [joinedB, upd, Gh.res]
        · by_cases h2 : u = 2
          · subst h2; simp [hjb2, upd, Gh.res]
          · simp [upd, h0, h2]
      rw [e]; exact ho₁₄
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu
        by_cases h2 : u = 2
        · subst h2; rw [upd_self] at hu; cases hu
          exact ⟨k2, ky, sep_lift.mpr ⟨⟨h2b, hyb, h20, hA2, hy0, hAy⟩, sep_comm hPa⟩⟩
        · rw [upd_ne _ _ h2] at hu; exact hi₁₃.kids u _ _ _ _ _ _ _ hu
    · refine ⟨by rw [hth₁₄]; simp [hsz₁₃], ?_, ?_, ?_, ⟨rP, false, .inl rfl, by simp [upd, B]⟩,
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
  refine WP.bind (WP.joinC fun k _ => ⟨Gh.main .j1 rnil B, hi₁₄, fun G₃ m₁₅ hg₃ hi₁₅ => ?_⟩)
  obtain ⟨ph, hm, B', h0, -, -, hsh⟩ := hi₁₅.main
  rw [hg₃] at h0; cases h0
  obtain ⟨hsz₁₅, r1₁₅, r2₁₅, k1₁₅, k2₁₅, hn₁₅⟩ := hsh
  refine ⟨fun _ => ⟨by show 0 < 1; decide, by rw [hsz₁₅]; decide, ⟨_, B, .inl rfl⟩, by
    have hr := r1₁₅
    unfold KidRec at hr
    simp [Thread.joinValid, Mem.isGated, hr]⟩,
    fun hfin => ⟨fun _ => join_run r1₁₅ rfl rfl, fun m₁₆ hj => ?_⟩⟩
  obtain ⟨rk1, c', ac', x', ax', v', hf1⟩ := hfin
  obtain ⟨h', d', -, hk1'⟩ := k1₁₅
  simp only [↓reduceIte] at hk1'
  rw [hf1] at hk1'; cases hk1'
  obtain ⟨kc1, kx1, hka1⟩ := hi₁₅.kids 1 _ _ _ _ _ _ _ hf1
  obtain ⟨⟨hc1b, hx1b, -⟩, hka1⟩ := sep_lift.mp hka1
  rw [hB.2.2.1] at hc1b; cases hc1b
  rw [hB.1] at hx1b; cases hx1b
  simp only [↓reduceIte] at hka1
  obtain ⟨hc₁₆, hth₁₆⟩ := join_threads r1₁₅ hj
  obtain ⟨rO₁₅, ho₁₅⟩ := hi₁₅.own
  have ho₁₆ := FOwned.join (ho₁₅.current 0) (by rw [hsz₁₅]; decide) (by decide) hj
  have e0 : ownOf G₃ m₁₅ 0 = rnil := by simp [ownOf, joinedB, hg₃, Gh.res]
  have e1 : ownOf G₃ m₁₅ 1 = rk1 := by
    have r : m₁₅.threads[1]? = some { spawner := 0, joined := false } := r1₁₅
    simp [ownOf, joinedB, r, hf1, Gh.res]
  rw [e0, e1, rnil_rsum] at ho₁₆
  have hjb₁₆ : ∀ u, joinedB m₁₆ u = if u = 1 then true else joinedB m₁₅ u := by
    intro u
    unfold joinedB
    rw [hth₁₆]
    by_cases h1 : u = 1
    · subst h1
      rw [Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz₁₅]; decide)]; rfl
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm h1)]; simp [h1]
  have hi₁₆ : Inv a b (upd G₃ 0 (.main .j2 rk1 B)) m₁₆ := by
    refine ⟨⟨rO₁₅, ?_⟩, fun u h c ac x ax v dn hu => ?_, ⟨.j2, rk1, B, upd_self _ _ _, hB, hka1, ?_⟩, ?_⟩
    · have e : ownOf (upd G₃ 0 (.main .j2 rk1 B)) m₁₆ =
          upd (upd (ownOf G₃ m₁₅) 1 rnil) 0 rk1 := by
        funext u
        unfold ownOf
        rw [hjb₁₆]
        by_cases h0 : u = 0
        · subst h0; simp [joinedB, upd, Gh.res]
        · by_cases h1 : u = 1
          · subst h1; simp [upd]
          · simp [upd, h0, h1]
      rw [e]; exact ho₁₆
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu; exact hi₁₅.kids u _ _ _ _ _ _ _ hu
    · refine ⟨by rw [hth₁₆, Array.size_setIfInBounds, hsz₁₅], ?_, ?_,
        ⟨rk1, true, .inr rfl, by rw [upd_ne _ _ (by decide)]; exact hf1⟩, ?_, fun u hu => ?_⟩
      · unfold KidRec; rw [hth₁₆, Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz₁₅]; decide)]
      · unfold KidRec; rw [hth₁₆, Array.getElem?_setIfInBounds_ne (by decide)]; exact r2₁₅
      · obtain ⟨h'', d'', hd'', hk⟩ := k2₁₅
        exact ⟨h'', d'', hd'', by rw [upd_ne _ _ (by decide)]; exact hk⟩
      · rw [upd_ne _ _ (by unfold ThreadId at *; omega), hn₁₅ u hu]
    · rw [hth₁₆, Array.getElem?_setIfInBounds_ne (by decide)]; exact hi₁₅.t0
  -- The join of kid 2: `main` owns all four blocks, with `x = a` and `y = b`.
  refine WP.bind (WP.joinC fun k _ => ⟨Gh.main .j2 rk1 B, hi₁₆, fun G₄ m₁₇ hg₄ hi₁₇ => ?_⟩)
  obtain ⟨ph, hm, B', h0, -, hma₁₇, hsh⟩ := hi₁₇.main
  rw [hg₄] at h0; cases h0
  obtain ⟨hsz₁₇, r1₁₇, r2₁₇, k1₁₇, k2₁₇, hn₁₇⟩ := hsh
  refine ⟨fun _ => ⟨by show 0 < 2; decide, by rw [hsz₁₇]; decide, ⟨_, B, .inr rfl⟩, by
    have hr := r2₁₇
    unfold KidRec at hr
    simp [Thread.joinValid, Mem.isGated, hr]⟩,
    fun hfin => ⟨fun _ => join_run r2₁₇ rfl rfl, fun m₁₈ hj₂ => ?_⟩⟩
  obtain ⟨rk2, c'', ac'', x'', ax'', v'', hf2⟩ := hfin
  obtain ⟨h'', d'', -, hk2'⟩ := k2₁₇
  simp only [show (2 : Nat) ≠ 1 by decide, ↓reduceIte] at hk2'
  rw [hf2] at hk2'; cases hk2'
  obtain ⟨kc2, ky2, hka2⟩ := hi₁₇.kids 2 _ _ _ _ _ _ _ hf2
  obtain ⟨⟨hc2b, hy2b, -⟩, hka2⟩ := sep_lift.mp hka2
  rw [hB.2.2.2.1] at hc2b; cases hc2b
  rw [hB.2.1] at hy2b; cases hy2b
  simp only [↓reduceIte] at hka2
  obtain ⟨hc₁₈, hth₁₈⟩ := join_threads r2₁₇ hj₂
  obtain ⟨rO₁₇, ho₁₇⟩ := hi₁₇.own
  have ho₁₈ := FOwned.join (ho₁₇.current 0) (by rw [hsz₁₇]; decide) (by decide) hj₂
  have e0 : ownOf G₄ m₁₇ 0 = rk1 := by simp [ownOf, joinedB, hg₄, Gh.res]
  have e2 : ownOf G₄ m₁₇ 2 = rk2 := by
    have r : m₁₇.threads[2]? = some { spawner := 0, joined := false } := r2₁₇
    simp [ownOf, joinedB, r, hf2, Gh.res]
  have hd12 : FHeap.Disjoint rk1.heap rk2.heap := by
    have := ho₁₇.disj (u := 0) (v := 2) (by rw [hsz₁₇]; decide) (by rw [hsz₁₇]; decide) (by decide)
    rwa [e0, e2] at this
  rw [e0, e2] at ho₁₈
  have hA : ((ctxF s6 k1 A1 s2 a ⋆ flagF s2 kx Ax a) ⋆ (ctxF s11 k2 A2 s4 b ⋆ flagF s4 ky Ay b))
      (rsum rk1 rk2) :=
    ⟨rk1, rk2, hd12, rfl, hma₁₇, hka2⟩
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
  refine WP.bind (WP.liftM_fowned ((blk_load (w := a) hxb hx0 hAx).frameL.frame.post
    fun _ _ h => sep_assoc (sep_mono_left (fun _ h => sep_lcomm h) h))
    ho₁₈ hc₁₈ htl hA fun r₁ m₁₉ r₁₉ _ ho₁₉ hq₁₉ hc₁₉ ht₁₉ => ?_)
  obtain ⟨hr₁, hA₁₉⟩ := sep_lift.mp hq₁₉
  refine WP.bind (WP.liftM_fowned ((blk_load (w := b) hyb hy0 hAy).frameL.frameL.post
    fun _ _ h => sep_lcomm (sep_mono_right (fun _ h => sep_lcomm h) h))
    ho₁₉ hc₁₉ (by rw [ht₁₉]; exact htl) hA₁₉ fun r₂ m₂₀ r₂₀ _ ho₂₀ hq₂₀ hc₂₀ ht₂₀ => ?_)
  obtain ⟨hr₂, hA₂₀⟩ := sep_lift.mp hq₂₀
  refine WP.pure' ?_
  -- The frees.
  have htl₂₀ : 0 < m₂₀.threads.size := by rw [ht₂₀, ht₁₉]; exact htl
  -- In reverse order of allocation (MM-18): `c2`, `c1`, `y`, `x`.
  refine WP.bind (WP.liftMem_fowned ((FTTriple.free_front (K := .stack)
    (R := (ctxF s6 k1 A1 s2 a ⋆ flagF s2 kx Ax a) ⋆ flagF s4 ky Ay b) h2b (ctxBytes_size s4 b) h20
    (by decide)).pre fun _ h => sep_lcomm h)
    ho₂₀ hc₂₀ htl₂₀ hA₂₀ fun _ m₂₁ r₂₁ _ ho₂₁ hq₂₁ hc₂₁ ht₂₁ => ?_)
  refine WP.bind (WP.liftMem_fowned ((FTTriple.free_front (K := .stack)
    (R := flagF s2 kx Ax a ⋆ flagF s4 ky Ay b) h1b (ctxBytes_size s2 a) h10 (by decide)).pre fun _ h => sep_assoc h)
    ho₂₁ hc₂₁ (by rw [ht₂₁]; exact htl₂₀) hq₂₁ fun _ m₂₂ r₂₂ _ ho₂₂ hq₂₂ hc₂₂ ht₂₂ => ?_)
  refine WP.bind (WP.liftMem_fowned ((FTTriple.free_front (K := .stack) (R := flagF s2 kx Ax a) hyb (enc_u32 b) hy0
    (by decide)).pre fun _ h => sep_comm h) ho₂₂ hc₂₂ (by rw [ht₂₂, ht₂₁]; exact htl₂₀) hq₂₂
    fun _ m₂₃ r₂₃ _ ho₂₃ hq₂₃ hc₂₃ ht₂₃ => ?_)
  refine WP.bind (WP.liftMem_fowned (FTTriple.free' hxb (enc_u32 a) hx0 (by decide))
    ho₂₃ hc₂₃ (by rw [ht₂₃, ht₂₂, ht₂₁]; exact htl₂₀) hq₂₃ fun _ m₂₄ _ _ _ _ _ ht₂₄ => ?_)
  refine WP.pure' ⟨by simp [hr₁, hr₂, addWrap], fun r hr hs => hja r ?_ hs⟩
  rwa [ht₂₄, ht₂₃, ht₂₂, ht₂₁, ht₂₀, ht₁₉] at hr

/-! ## The results -/

/-- **`disjoint a b` gives `a + b` (wrapping) under every schedule** (every oracle `o`, every
`fuel`). -/
theorem disjoint_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run env dispatch fuel o (disjoint a b) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok (a + b) := by
  obtain ⟨_, _, hv, -⟩ := (proto a b).run_sound env (Proto.of_available henv) dispatch (fun _ => .none) dispatch_spec
    (fun _ _ _ _ _ hq => hq.2) rfl (main_spec σ) h
  exact hv

/-- One schedule completes: under the oracle that always picks option 0, `disjoint 1 2` returns
3 within fuel 1000. The kernel computes the run. -/
theorem disjoint_completes :
    ∃ σ, Witness.okVal (Sched.run ⟨.any, .available⟩ dispatch 1000 (fun _ => 0) (disjoint 1 2) (mem0 σ)) = some 3 :=
  ⟨.fresh, by decide +kernel⟩

/-- **No run of `disjoint a b` gives an error**, under any schedule: no data race (the two threads
write disjoint bytes), no other illegal behaviour. -/
theorem disjoint_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} :
    e ≠ .stackOverflow → (Sched.run env dispatch fuel o (disjoint a b) (mem0 σ)).run ≠ some (.error e) :=
  (proto a b).run_safe env (Proto.of_available henv) dispatch (fun _ => .none) rfl dispatch_spec (fun _ _ _ _ hq => hq.2) rfl
    (main_spec σ)

/-! ## Non-vacuity and liveness witnesses

The thread triples' admissible inputs (`Witness.FTTAdmit`, `FTTLive`) in concrete memories: all
bytes of the memory with the full extents of its blocks (`FTTAdmit.of_exts`). -/

section Witnesses

open Zig.Witness

/-- A block's bytes and its full extent, as a resource. -/
theorem blk_of {p : Ptr} {A S : Nat} {bs : Array Byte} {b : BlockId} {F : FHeap}
    (hb : bytesAt p A S .stack bs F.erase) :
    blk p A S bs b ⟨F, Know.none, Ghost.atExt b (ECell.auth1 S .stack Frac.one)⟩ :=
  ⟨⟨F, Know.none, Ghost.unit⟩, ⟨FHeap.empty, Know.none, Ghost.atExt b (ECell.auth1 S .stack Frac.one)⟩,
    FHeap.disjoint_empty _, by simp [Know.union_none], ⟨by simpa using hb, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- A context block `c` (block 0) whose `x` field points to block 1 and whose value is 0. -/
abbrev ctxW : Array Byte :=
  Enc.encode Witness.p1 ++ Enc.encode (0 : BitVec 32) ++ Array.replicate 4 .undef

abbrev flagW : Mem := Witness.mem2 ctxW (Array.replicate 4 .undef) .stack .stack

theorem flagW_pre : (bytesAt Witness.p0 4096 16 .stack ctxW ∗
    bytesAt Witness.p1 8192 4 .stack (Array.replicate 4 .undef)) flagW.heap :=
  Witness.mem2_bytesAt' (by decide +kernel) rfl

theorem flagW_fseq : flagW.FSeq := by
  refine ⟨⟨singleThread_empty rfl Nat.zero_lt_one⟩, by simp [shapes, ShapesWF, Witness.mem2],
    fun b b' _ _ hne hb hb' _ => ?_, fun b bl hb _ => ?_⟩
  · have h1 := (Array.getElem?_eq_some_iff.mp hb).1
    have h2 := (Array.getElem?_eq_some_iff.mp hb').1
    simp only [Witness.mem2, List.size_toArray, List.length_cons, List.length_nil] at h1 h2
    rcases (by unfold BlockId at *; omega : b = 0 ∨ b = 1) with rfl | rfl <;>
      rcases (by unfold BlockId at *; omega : b' = 0 ∨ b' = 1) with rfl | rfl <;>
      first | exact absurd rfl hne |
        (simp only [Witness.mem2] at hb hb'; cases hb; cases hb'; decide +kernel)
  · have h1 := (Array.getElem?_eq_some_iff.mp hb).1
    simp only [Witness.mem2, List.size_toArray, List.length_cons, List.length_nil] at h1
    rcases (by unfold BlockId at *; omega : b = 0 ∨ b = 1) with rfl | rfl <;>
      (simp only [Witness.mem2] at hb; cases hb; decide +kernel)

/-- The full extents of `flagW`'s two blocks. -/
abbrev E2 : BlockId → Option (Nat × BlockKind) :=
  fun x => if x = 0 then some (16, .stack) else if x = 1 then some (4, .stack) else none

theorem exts_E2 : Ghost.exts E2 = (Ghost.atExt 0 (ECell.auth1 16 .stack Frac.one)).add
    (Ghost.atExt 1 (ECell.auth1 4 .stack Frac.one)) := by
  rw [Ghost.exts_split (b := 0) (S := 16) (K := .stack) rfl,
    Ghost.exts_split (b := 1) (S := 4) (K := .stack) rfl]
  have e : (fun x : BlockId => if x = 1 then none else if x = 0 then none else E2 x) = fun _ => none := by
    funext x; by_cases h1 : x = 1 <;> by_cases h0 : x = 0 <;> simp [E2, h0, h1]
  simp only [e, Ghost.exts_none, Ghost.add_unit]

theorem flagW_exts : ExtTrue flagW (Ghost.exts E2) := exts_true fun b S K h => by
  by_cases h0 : b = 0
  · subst h0; simp only [E2, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨_, rfl, rfl, by decide +kernel, rfl, by decide⟩
  · by_cases h1 : b = 1
    · subst h1; simp only [E2, ↓reduceIte] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨_, rfl, rfl, by decide +kernel, rfl, by decide⟩
    · simp [E2, h0, h1] at h

theorem flagW_res : (blk Witness.p0 4096 16 ctxW 0 ⋆ blk Witness.p1 8192 4 (Array.replicate 4 .undef) 1)
    ⟨flagW.fheap, Know.none, Ghost.exts E2⟩ := by
  obtain ⟨h₁, h₂, hd, he, hb1, hb2⟩ := flagW_pre
  have hf : flagW.fheap = FHeap.ofHeap (shapes flagW) h₁ ∪ FHeap.ofHeap (shapes flagW) h₂ := by
    rw [← FHeap.ofHeap_union, ← he]; rfl
  refine ⟨_, _, FHeap.ofHeap_disjoint hd, ?_, blk_of (F := FHeap.ofHeap (shapes flagW) h₁)
    (by simpa using hb1), blk_of (F := FHeap.ofHeap (shapes flagW) h₂) (by simpa using hb2)⟩
  rw [hf, exts_E2, Know.union_none]

nonvacuity_witness writeFlag_spec :=
  ⟨Witness.p0, Witness.p1, 0, 1, 4096, 8192, ctxW, Array.replicate 4 .undef, 0, rfl, rfl, rfl,
    by decide, rfl, by decide, by decide +kernel, rfl, by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    FTTAdmit.of_exts (Know.sub_none _) flagW_exts flagW_res flagW_fseq rfl⟩
liveness_witness writeFlag_spec :=
  ⟨Witness.p0, Witness.p1, 0, 1, 4096, 8192, ctxW, Array.replicate 4 .undef, 0, rfl, rfl, rfl,
    by decide, rfl, by decide, by decide +kernel, rfl, by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    FTTLive.of_exts (Know.sub_none _) flagW_exts flagW_res flagW_fseq rfl
      (Witness.ok_of_okb (by decide +kernel))⟩

/-- The full extent of `mem1`'s block. -/
abbrev E1 : BlockId → Option (Nat × BlockKind) := fun x => if x = 0 then some (1, .stack) else none

theorem front_res : (blk Witness.p0 4096 1 #[.undef] 0 ⋆ emp)
    ⟨(Witness.mem1 #[.undef] .stack).fheap, Know.none, Ghost.exts E1⟩ := by
  have e : Ghost.exts E1 = Ghost.atExt 0 (ECell.auth1 1 .stack Frac.one) := by
    rw [Ghost.exts_split (b := 0) (S := 1) (K := .stack) rfl]
    have e : (fun x : BlockId => if x = 0 then none else E1 x) = fun _ => none := by
      funext x; by_cases h0 : x = 0 <;> simp [E1, h0]
    simp only [e, Ghost.exts_none, Ghost.add_unit]
  rw [e]
  exact sep_emp.mpr (blk_of (by simpa using Witness.mem1_bytesAt #[.undef] .stack))

theorem front_exts : ExtTrue (Witness.mem1 #[.undef] .stack) (Ghost.exts E1) :=
  exts_true fun b S K h => by
    by_cases h0 : b = 0
    · subst h0; simp only [E1, ↓reduceIte] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨_, rfl, rfl, rfl, rfl, by decide⟩
    · simp [E1, h0] at h

/-! The library rule this proof frees its blocks with (`Full/Block`), witnessed at `mem1`. -/

nonvacuity_witness FTTriple.free_front :=
  ⟨emp, Witness.p0, 4096, 1, .stack, #[.undef], 0, rfl, rfl, rfl, by decide, by decide,
    FTTAdmit.of_exts (Know.sub_none _) front_exts front_res (mem1_fseq _ _ (by decide)) rfl⟩
liveness_witness FTTriple.free_front :=
  ⟨emp, Witness.p0, 4096, 1, .stack, #[.undef], 0, rfl, rfl, rfl, by decide, by decide,
    FTTLive.of_exts (Know.sub_none _) front_exts front_res (mem1_fseq _ _ (by decide)) rfl
      (Witness.ok_of_okb (by decide +kernel))⟩

end Witnesses

/-! ## Strength (`docs/sep-threads.md`): the legacy proof's statements, verbatim -/

example (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run env dispatch fuel o (disjoint a b) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok (a + b) :=
  disjoint_spec env henv h

example (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} :
    e ≠ .stackOverflow → (Sched.run env dispatch fuel o (disjoint a b) (mem0 σ)).run ≠ some (.error e) :=
  disjoint_safe env henv

end Threads.Disjoint
