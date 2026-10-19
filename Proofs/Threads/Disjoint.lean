import Proofs.Threads.Gen
import ZigLean.Simp
import ZigLean.Mem.Witness
import ZigLean.Sep.Full.ThreadOwned
import ZigLean.Sep.Full.ThreadFacts
import ZigLean.Sep.Full.Local
import ZigLean.Sep.Full.Init
import ZigLean.Sep.Full.Witness
import ZigLean.Sep.Full.AutoAll

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
  have hwrite : writeBytes xb 0 (Enc.encode v) = Enc.encode v :=
    writeBytes_all (by rw [hxs, LawfulEnc.size_encode]; rfl)
  rw [writeFlag_eq]
  fsym [FTotalTriple.loadBlock (T := Ptr) (A := Ac) (S := 16) (K := .stack) (al := 8) hcb
      (by decide) (by rw [hcs]; decide) hcx (by simp [hc0, hAc]),
    FTotalTriple.load_bytesAt (q := c) (k := 8) (al := 4) (A := Ac) (S := 16) (K := .stack)
      (bs := cb) (T := BitVec 32) (by decide) (by rw [hcs]; decide) (by simp [hc0]; omega) hcv,
    FTTriple.ptrProjectAt, hwrite]

/-! ## Blocks and resources -/

/-- The bytes of a `RaceCtx` with the flag `f` and the value `v` (the padding is undefined). -/
def ctxBytes (f : Ptr) (v : BitVec 32) : Array Byte :=
  writeBytes (writeBytes (Array.replicate 16 .undef) 0 (Enc.encode f)) 8 (Enc.encode v)

theorem enc_ptr (f : Ptr) : (Enc.encode f).size = 8 := LawfulEnc.size_encode f

theorem enc_u32 (v : BitVec 32) : (Enc.encode v).size = 4 := LawfulEnc.size_encode v

theorem ctxBytes_one (f : Ptr) :
    (writeBytes (Array.replicate 16 .undef) 0 (Enc.encode f)).size = 16 := by
  rw [writeBytes_size _ _ _ (by simp [enc_ptr])]; simp

@[fsym_arith] theorem ctxBytes_size (f : Ptr) (v : BitVec 32) : (ctxBytes f v).size = 16 := by
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

/-- The worker's postcondition follows from its completed resource and the protocol's
invariant. The generated worker body is walked independently by `fsym`. -/
theorem inv_kid_done {G : ThreadId → Gh} {m m' : Mem} {u : ThreadId}
    {r r' rO : Res} {c x : Ptr} {ac ax : Nat} {v : BitVec 32} {bc bx : BlockId}
    (hi : Inv a b G m) (hu : 0 < u) (hgu : G u = .kid r c ac x ax v false)
    (hcb : c.block = some bc) (hxb : x.block = some bx) (hc0 : c.off = 0)
    (hac : ac % 8 = 0) (hx0 : x.off = 0) (hax : ax % 4 = 0)
    (ho' : FOwned (upd (ownOf G m) u r') rO m')
    (hq : (ctxF c bc ac x v ⋆ flagF x bx ax v) r')
    (hth : m'.threads = m.threads) :
    Inv a b (upd G u (.kid r' c ac x ax v true)) m' := by
  obtain ⟨hj, _, _⟩ := kid_live hi hu hgu
  refine ⟨⟨rO, ?_⟩, fun w r₁ c' ac' x' ax' v' d' hw => ?_, ?_, ?_⟩
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

theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : (proto a b).init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : Inv a b G m) :
    (proto a b).WP u (dispatch tgt) ((proto a b).QKid u) G { m with current := u } d := by
  cases tgt with
  | writeFlag c =>
    obtain ⟨r, ac, x, ax, v, rfl⟩ := hg
    obtain ⟨hj, hut, _⟩ := kid_live hi hu hgu
    obtain ⟨bc, bx, hka⟩ := hi.kids u _ _ _ _ _ _ _ hgu
    obtain ⟨⟨hcb, hxb, hc0, hac, hx0, hax⟩, hcx⟩ := sep_lift.mp hka
    have hown : ownOf G m u = r := by unfold ownOf; rw [hj, hgu]; rfl
    obtain ⟨rO, ho⟩ := hi.own
    have ho' := ho.current u
    have hp : (ctxF c bc ac x v ⋆ flagF x bx ax 0) (ownOf G m u) := by
      rw [hown]; exact hcx
    have hja := joinedAll_of_main (spawner0 hi) hu
    fsym [Functor.discard, map_const, Function.comp_apply,
      writeFlag_spec (xb := Enc.encode (0 : BitVec 32)) hcb hxb hc0 hac hx0 hax
        (ctxBytes_size x v) (enc_u32 0) (ctxBytes_flag x v) (ctxBytes_val x v),
      inv_kid_done, proto, Proto.QKid, joinedAll_of_threads]
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
    ∃ rO, FOwned plainOwn rO { mem0 σ with current := 0 } :=
  ⟨rnil, FOwned.start0_plain σ⟩

/-- The protocol starts from the four initialized blocks. The two child parts are witnesses
of the resource split; the program walk chooses neither a resource nor a ghost value. -/
theorem inv_start {m : Mem} {r : Res} {x y c1 c2 : Ptr} {kx ky k1 k2 : BlockId}
    {Ax Ay A1 A2 : Nat}
    (ho : FOwned (upd (fun _ => rnil) 0 r) rnil m)
    (hF : ((flagF x kx Ax 0 ⋆ (flagF y ky Ay 0 ⋆
      (ctxF c1 k1 A1 x a ⋆ ctxF c2 k2 A2 y b))) ⋆ plain) r)
    (hxb : x.block = some kx) (hyb : y.block = some ky)
    (h1b : c1.block = some k1) (h2b : c2.block = some k2)
    (hx0 : x.off = 0) (hy0 : y.off = 0) (h10 : c1.off = 0) (h20 : c2.off = 0)
    (hAx : Ax % 4 = 0) (hAy : Ay % 4 = 0) (hA1 : A1 % 8 = 0) (hA2 : A2 % 8 = 0)
    (hth : m.threads = #[{ spawner := 0, joined := true }]) :
    ∃ B rP rK, FHeap.Disjoint rP.heap rK.heap ∧ MainA a b B .one rP ∧
      KidA B.c1 B.a1 B.x B.ax a false rK ∧
      Inv a b (upd (fun _ => .none) 0 (.main .pre (rsum rP rK) B)) m := by
  let B : Blks := ⟨x, y, c1, c2, kx, ky, k1, k2, Ax, Ay, A1, A2⟩
  have hB : B.Ok := ⟨hxb, hyb, h1b, h2b, hx0, hy0, h10, h20, hAx, hAy, hA1, hA2⟩
  obtain ⟨rB, rMode, hdMode, rfl, hBlocks, _⟩ := hF
  have ho' := ho.give (t := 0) (by rw [hth]; decide) (by rw [upd_self]) hdMode
  rw [upd_upd] at ho'
  simp only [rsum, FHeap.union_empty, Know.union_none, Ghost.add_unit] at ho'
  obtain ⟨rP, rK, hd, rfl, hPa, hKa⟩ := split_pre hBlocks
  refine ⟨B, rP, rK, hd, hPa,
    ⟨k1, kx, sep_lift.mpr ⟨⟨h1b, hxb, h10, hA1, hx0, hAx⟩, hKa⟩⟩,
    ⟨⟨rMode, ?_⟩, ?_, ⟨.pre, _, B, upd_self _ _ _, hB, ?_, ?_⟩, ?_⟩⟩
  · rw [ownOf_main]; exact ho'
  · intro u _ _ _ _ _ _ _ hu
    by_cases h0 : u = 0
    · subst h0; rw [upd_self] at hu; cases hu
    · rw [upd_ne _ _ h0] at hu; cases hu
  · exact hBlocks
  · refine ⟨by rw [hth]; rfl, fun u hu => ?_⟩
    rw [upd_ne _ _ (by unfold ThreadId at *; omega)]
  · rw [hth]; rfl

/-- The invariant's first transfer: the child receives its context and flag; the parent
keeps the second pair. This is a fact of a fork's run, not a program proof rule. -/
theorem inv_spawn_pre {G : ThreadId → Gh} {m m' : Mem} {child : ThreadId}
    {B : Blks} {rP rK : Res} (hi : Inv a b G m)
    (hg : G 0 = .main .pre (rsum rP rK) B)
    (hd : FHeap.Disjoint rP.heap rK.heap) (hPa : MainA a b B .one rP)
    (hKa : KidA B.c1 B.a1 B.x B.ax a false rK)
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (child, m'))) :
    child = 1 ∧ m'.current = 0 ∧
      Inv a b (upd (upd G 1 (.kid rK B.c1 B.a1 B.x B.ax a false))
        0 (.main .one rP B)) m' := by
  obtain ⟨ph, r, B', h0, hB, _, hsh⟩ := hi.main
  rw [hg] at h0; cases h0
  obtain ⟨hsz, hn⟩ := hsh
  obtain ⟨rfl, hth⟩ := fork_threads hf
  obtain ⟨rO, ho⟩ := hi.own
  have hown : ownOf G m 0 = rsum rP rK := by simp [ownOf, joinedB, hg, Gh.res]
  have ho' := FOwned.fork (ho.current 0) (by rw [hsz]; decide) hown hd hf
  rw [hsz] at ho' ⊢
  have hc : m'.current = 0 := by rw [(Lock.fork_eq hf).2]
  refine ⟨rfl, hc, ?_⟩
  have hjb : joinedB m' = joinedB m := joinedB_fork hf
  have hjb1 : joinedB m 1 = false := by
    simp [joinedB, Array.getElem?_eq_none (show m.threads.size ≤ 1 by omega)]
  refine ⟨⟨rO, ?_⟩, ?_, ⟨.one, rP, B, upd_self _ _ _, hB, hPa, ?_⟩, ?_⟩
  · have e : ownOf (upd (upd G 1 (.kid rK B.c1 B.a1 B.x B.ax a false))
          0 (.main .one rP B)) m' = upd (upd (ownOf G m) 0 rP) 1 rK := by
      funext u
      unfold ownOf
      rw [hjb]
      by_cases h0 : u = 0
      · subst h0; simp [joinedB, upd, Gh.res]
      · by_cases h1 : u = 1
        · subst h1; simp [hjb1, upd, Gh.res]
        · simp [upd, h0, h1]
    rw [e]; exact ho'
  · intro u r c ac x ax v dn hu
    by_cases h0 : u = 0
    · subst h0; rw [upd_self] at hu; cases hu
    · rw [upd_ne _ _ h0] at hu
      by_cases h1 : u = 1
      · subst h1; rw [upd_self] at hu; cases hu; exact hKa
      · rw [upd_ne _ _ h1, hn u (by unfold ThreadId at *; omega)] at hu; cases hu
  · refine ⟨by rw [hth]; simp [hsz], ?_, ⟨rK, false, .inl rfl, by simp [upd]⟩,
      fun u hu => ?_⟩
    · unfold KidRec; rw [hth, Array.getElem?_push, if_pos hsz.symm]
    · rw [upd_ne _ _ (by unfold ThreadId at *; omega),
        upd_ne _ _ (by unfold ThreadId at *; omega), hn u (by unfold ThreadId at *; omega)]
  · rw [hth, Array.getElem?_push, if_neg (by omega)]; exact hi.t0

/-- The invariant's second transfer: the parent gives its remaining pair to child 2. -/
theorem inv_spawn_one {G : ThreadId → Gh} {m m' : Mem} {child : ThreadId}
    {B : Blks} {rP : Res} (hi : Inv a b G m) (hg : G 0 = .main .one rP B)
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (child, m'))) :
    child = 2 ∧ m'.current = 0 ∧
      Inv a b (upd (upd G 2 (.kid rP B.c2 B.a2 B.y B.ay b false))
        0 (.main .j1 rnil B)) m' := by
  obtain ⟨ph, r, B', h0, hB, hPa, hsh⟩ := hi.main
  rw [hg] at h0; cases h0
  obtain ⟨hsz, r1, k1, hn⟩ := hsh
  obtain ⟨rfl, hth⟩ := fork_threads hf
  obtain ⟨rO, ho⟩ := hi.own
  have hown : ownOf G m 0 = rsum rnil rP := by
    simp [ownOf, joinedB, hg, Gh.res, rnil_rsum]
  have ho' := FOwned.fork (ho.current 0) (by rw [hsz]; decide) hown
    (FHeap.disjoint_empty _).symm hf
  rw [hsz] at ho' ⊢
  have hc : m'.current = 0 := by rw [(Lock.fork_eq hf).2]
  refine ⟨rfl, hc, ?_⟩
  have hjb : joinedB m' = joinedB m := joinedB_fork hf
  have hjb2 : joinedB m 2 = false := by
    simp [joinedB, Array.getElem?_eq_none (show m.threads.size ≤ 2 by omega)]
  refine ⟨⟨rO, ?_⟩, ?_, ⟨.j1, rnil, B, upd_self _ _ _, hB, ⟨rfl, rfl, rfl⟩, ?_⟩, ?_⟩
  · have e : ownOf (upd (upd G 2 (.kid rP B.c2 B.a2 B.y B.ay b false))
          0 (.main .j1 rnil B)) m' = upd (upd (ownOf G m) 0 rnil) 2 rP := by
      funext u
      unfold ownOf
      rw [hjb]
      by_cases h0 : u = 0
      · subst h0; simp [joinedB, upd, Gh.res]
      · by_cases h2 : u = 2
        · subst h2; simp [hjb2, upd, Gh.res]
        · simp [upd, h0, h2]
    rw [e]; exact ho'
  · intro u r c ac x ax v dn hu
    by_cases h0 : u = 0
    · subst h0; rw [upd_self] at hu; cases hu
    · rw [upd_ne _ _ h0] at hu
      by_cases h2 : u = 2
      · subst h2; rw [upd_self] at hu; cases hu
        obtain ⟨_, hyb, _, h2b, _, hy0, _, h20, _, hAy, _, hA2⟩ := hB
        exact ⟨B.k2, B.ky,
          sep_lift.mpr ⟨⟨h2b, hyb, h20, hA2, hy0, hAy⟩, sep_comm hPa⟩⟩
      · rw [upd_ne _ _ h2] at hu; exact hi.kids u _ _ _ _ _ _ _ hu
  · refine ⟨by rw [hth]; simp [hsz], ?_, ?_, ?_, ⟨rP, false, .inl rfl, by simp [upd]⟩,
      fun u hu => ?_⟩
    · unfold KidRec; rw [hth, Array.getElem?_push, if_neg (by omega)]; exact r1
    · unfold KidRec; rw [hth, Array.getElem?_push, if_pos hsz.symm]
    · obtain ⟨r, d, hd, hk⟩ := k1
      exact ⟨r, d, hd, by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact hk⟩
    · rw [upd_ne _ _ (by unfold ThreadId at *; omega),
        upd_ne _ _ (by unfold ThreadId at *; omega), hn u (by unfold ThreadId at *; omega)]
  · rw [hth, Array.getElem?_push, if_neg (by omega)]; exact hi.t0

/-- Joining child 1 restores its completed pair to the parent. -/
theorem inv_join_j1 {G : ThreadId → Gh} {m m' : Mem} {B : Blks}
    (hi : Inv a b G m) (hg : G 0 = .main .j1 rnil B)
    (hfin : (proto a b).fin (G 1))
    (hj : ((Thread.join 1).run { m with current := 0 }).run = some (.ok ((), m'))) :
    ∃ r, m'.current = 0 ∧ Inv a b (upd G 0 (.main .j2 r B)) m' := by
  obtain ⟨ph, r, B', h0, hB, _, hsh⟩ := hi.main
  rw [hg] at h0; cases h0
  obtain ⟨hsz, r1, r2, k1, k2, hn⟩ := hsh
  obtain ⟨rk1, c, ac, x, ax, v, hf1⟩ := hfin
  obtain ⟨_, _, _, hk1⟩ := k1
  simp only [↓reduceIte] at hk1
  rw [hf1] at hk1; cases hk1
  obtain ⟨kc1, kx1, hka⟩ := hi.kids 1 _ _ _ _ _ _ _ hf1
  obtain ⟨⟨hc1b, hx1b, _⟩, hka⟩ := sep_lift.mp hka
  rw [hB.2.2.1] at hc1b; cases hc1b
  rw [hB.1] at hx1b; cases hx1b
  simp only [↓reduceIte] at hka
  obtain ⟨hc, hth⟩ := join_threads r1 hj
  obtain ⟨rO, ho⟩ := hi.own
  have ho' := FOwned.join (ho.current 0) (by rw [hsz]; decide) (by decide) hj
  have e0 : ownOf G m 0 = rnil := by simp [ownOf, joinedB, hg, Gh.res]
  have e1 : ownOf G m 1 = rk1 := by
    have hr : m.threads[1]? = some { spawner := 0, joined := false } := r1
    simp [ownOf, joinedB, hr, hf1, Gh.res]
  rw [e0, e1, rnil_rsum] at ho'
  have hjb : ∀ u, joinedB m' u = if u = 1 then true else joinedB m u := by
    intro u
    unfold joinedB
    rw [hth]
    by_cases h1 : u = 1
    · subst h1
      rw [Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz]; decide)]; rfl
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm h1)]; simp [h1]
  refine ⟨rk1, hc, ⟨⟨rO, ?_⟩, ?_, ⟨.j2, rk1, B, upd_self _ _ _, hB, hka, ?_⟩, ?_⟩⟩
  · have e : ownOf (upd G 0 (.main .j2 rk1 B)) m' =
        upd (upd (ownOf G m) 1 rnil) 0 rk1 := by
      funext u
      unfold ownOf
      rw [hjb]
      by_cases h0 : u = 0
      · subst h0; simp [joinedB, upd, Gh.res]
      · by_cases h1 : u = 1
        · subst h1; simp [upd]
        · simp [upd, h0, h1]
    rw [e]; exact ho'
  · intro u r c ac x ax v dn hu
    by_cases h0 : u = 0
    · subst h0; rw [upd_self] at hu; cases hu
    · rw [upd_ne _ _ h0] at hu; exact hi.kids u _ _ _ _ _ _ _ hu
  · refine ⟨by rw [hth, Array.size_setIfInBounds, hsz], ?_, ?_,
      ⟨rk1, true, .inr rfl, by rw [upd_ne _ _ (by decide)]; exact hf1⟩, ?_, fun u hu => ?_⟩
    · unfold KidRec; rw [hth, Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz]; decide)]
    · unfold KidRec; rw [hth, Array.getElem?_setIfInBounds_ne (by decide)]; exact r2
    · obtain ⟨r, d, hd, hk⟩ := k2
      exact ⟨r, d, hd, by rw [upd_ne _ _ (by decide)]; exact hk⟩
    · rw [upd_ne _ _ (by unfold ThreadId at *; omega), hn u hu]
  · rw [hth, Array.getElem?_setIfInBounds_ne (by decide)]; exact hi.t0

/-- Joining child 2 restores all four completed blocks; every handle is now consumed. -/
theorem inv_join_j2 {G : ThreadId → Gh} {m m' : Mem} {B : Blks} {r1 : Res}
    (hi : Inv a b G m) (hg : G 0 = .main .j2 r1 B)
    (hfin : (proto a b).fin (G 2))
    (hj : ((Thread.join 2).run { m with current := 0 }).run = some (.ok ((), m'))) :
    ∃ rO r,
      FOwned (upd (upd (ownOf G m) 2 rnil) 0 r) rO m' ∧
      ((ctxF B.c1 B.k1 B.a1 B.x a ⋆ flagF B.x B.kx B.ax a) ⋆
        (ctxF B.c2 B.k2 B.a2 B.y b ⋆ flagF B.y B.ky B.ay b)) r ∧
      B.Ok ∧ m'.current = 0 ∧ 0 < m'.threads.size ∧ joinedAll 0 m' := by
  obtain ⟨ph, r, B', h0, hB, hma, hsh⟩ := hi.main
  rw [hg] at h0; cases h0
  obtain ⟨hsz, hr1, hr2, _, k2, _⟩ := hsh
  obtain ⟨rk2, c, ac, x, ax, v, hf2⟩ := hfin
  obtain ⟨_, _, _, hk2⟩ := k2
  simp only [show (2 : Nat) ≠ 1 by decide, ↓reduceIte] at hk2
  rw [hf2] at hk2; cases hk2
  obtain ⟨kc2, ky2, hka⟩ := hi.kids 2 _ _ _ _ _ _ _ hf2
  obtain ⟨⟨hc2b, hy2b, _⟩, hka⟩ := sep_lift.mp hka
  rw [hB.2.2.2.1] at hc2b; cases hc2b
  rw [hB.2.1] at hy2b; cases hy2b
  simp only [↓reduceIte] at hka
  obtain ⟨hc, hth⟩ := join_threads hr2 hj
  obtain ⟨rO, ho⟩ := hi.own
  have ho' := FOwned.join (ho.current 0) (by rw [hsz]; decide) (by decide) hj
  have e0 : ownOf G m 0 = r1 := by simp [ownOf, joinedB, hg, Gh.res]
  have e2 : ownOf G m 2 = rk2 := by
    have hr : m.threads[2]? = some { spawner := 0, joined := false } := hr2
    simp [ownOf, joinedB, hr, hf2, Gh.res]
  have hd : FHeap.Disjoint r1.heap rk2.heap := by
    have := ho.disj (u := 0) (v := 2) (by rw [hsz]; decide) (by rw [hsz]; decide) (by decide)
    rwa [e0, e2] at this
  rw [e0, e2] at ho'
  refine ⟨rO, rsum r1 rk2, ho', ⟨r1, rk2, hd, rfl, hma, hka⟩, hB, hc,
    by rw [hth, Array.size_setIfInBounds, hsz]; decide, ?_⟩
  intro r hr _
  rw [hth] at hr
  obtain ⟨i, hil, he⟩ := Array.mem_iff_getElem.mp hr
  have hi' : i < 3 := by simpa [hsz] using hil
  have hget : (m.threads.setIfInBounds 2 { spawner := 0, joined := true })[i]? = some r := by
    rw [Array.getElem?_eq_getElem hil, he]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · rw [Array.getElem?_setIfInBounds_ne (by decide), hi.t0] at hget; cases hget; rfl
  · rw [Array.getElem?_setIfInBounds_ne (by decide), hr1] at hget; cases hget; rfl
  · rw [Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz]; decide)] at hget; cases hget; rfl

set_option maxHeartbeats 1000000 in
theorem main_spec (σ : Placement) (d : Nat) : (proto a b).WP 0 (disjoint a b) (QM a b) (fun _ => .none)
    { mem0 σ with current := 0 } d := by
  have := FOwned.start0_facts (σ := σ) (m := mem0 σ) rfl
  unfold disjoint
  fsym [inv_start, inv_spawn_pre, inv_spawn_one, inv_join_j1, inv_join_j2,
    blk_load, FTTriple.storeAt, FTTriple.ptrProjectAt, ctxBytes, enc_zero, proto, Shape,
    KidRec, Thread.joinValid, Mem.isGated, @join_run, joinedAll_of_threads]

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
