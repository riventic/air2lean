import ThreadLocals.Gen
import ZigLean.Simp
import ZigLean.Sep.Full.ThreadTls
import ZigLean.Sep.Full.ThreadFacts

/-!
# Three threads, three counters: `twoCounters` over all schedules

`twoCounters` (the retained translation of `thread_locals.twoCounters`) stores 0 in its locals
`a` and `b`, spawns `bumpTwice(&a)` and `bumpTwice(&b)`, increments its own `counter`, joins
both and returns `a * 10000 + b * 100 + counter`. Each worker increments *its own* `counter`
twice and stores the value it then reads in its output.

`twoCounters_spec`: under every placement, every schedule and every fuel, an `ok` result is
`90908`: each worker read 9 (7 + 2) and `main` read 8 (7 + 1). `twoCounters_safe`: no run gives
an error (no race, no panic, no deadlock). So the three instances of `counter` do not alias, each
starts at the initial value 7, and the concurrent increments do not race.

The proof is in the full-state concurrent separation logic (`docs/sep-threads.md`), as
`Proofs/Threads/Disjoint.lean`, with the thread-local blocks owned by their threads
(`ZigLean/Sep/Full/ThreadTls.lean`):

- `main` owns its instance (block 0 of `mem0`, `cnt`) from the start (`FOwned.one` with the
  start memory's globals, `initRes_holds`); its `tlsPtr` reads the record `mem0` registered
  (`WP.liftM_tlsPtr`).
- A kid owns its output block (handed over at the spawn, `FOwned.fork`) and, after its thread
  start, the new block `tlsEnter` made (`WP.liftMem_tlsEnter_fowned`). Its worker is a sequence of
  thread triples (`seg_spec`), with each `tlsPtr` resolved against its record
  (`WP.liftMem_tlsPtr_bind`); at its end it frees its instance (`WP.liftMem_tlsExit_fowned`) and
  keeps only its output.
- At each join `main` takes the kid's output back (`FOwned.join`).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

namespace ThreadLocals.Counters

-- Unification must not unfold `WP` into the program (as in `Proofs/Threads/Disjoint.lean`).
attribute [local irreducible] Proto.WP

/-! ## Blocks -/

/-- A `u32` block `b` at `p` (address `A`, kind `K`) that holds `v`, with its full extent. -/
abbrev u32At (p : Ptr) (A : Nat) (K : BlockKind) (b : BlockId) (v : BitVec 32) : FAssn :=
  up (bytesAt p A 4 K (Enc.encode v)) ⋆ bext b 4 K

/-- `main`'s instance of `counter`: block 0 of `mem0` at the address `Ac`, and its knowledge. -/
abbrev cnt (Ac : Nat) (v : BitVec 32) : FAssn := u32At ⟨some 0, 0⟩ Ac .global 0 v ⋆ known 0 Ac

theorem wr (v w : BitVec 32) : writeBytes (Enc.encode v) 0 (Enc.encode w) = Enc.encode w :=
  writeBytes_all (by rw [LawfulEnc.size_encode_u32, LawfulEnc.size_encode_u32])

theorem enc_zero : writeBytes (Array.replicate 4 .undef) 0 (Enc.encode (0 : BitVec 32)) =
    Enc.encode (0 : BitVec 32) :=
  writeBytes_all (by simp [LawfulEnc.size_encode_u32])

theorem sep_lcomm {P Q R : FAssn} {r : Res} (h : (P ⋆ (Q ⋆ R)) r) : (Q ⋆ (P ⋆ R)) r :=
  sep_left_comm_eq P Q R ▸ h

/-- The pure fact of a framed load's post. -/
theorem lift_l {φ : Prop} {P Q : FAssn} {r : Res} (h : ((⟪φ⟫ ⋆ P) ⋆ Q) r) : φ ∧ (P ⋆ Q) r :=
  sep_lift.mp (sep_assoc h)

/-- `main`'s two output blocks and its instance, with their block ids and addresses. -/
structure Blks where
  a : Ptr
  b : Ptr
  ka : BlockId
  kb : BlockId
  A1 : Nat
  A2 : Nat
  Ac : Nat

def Blks.Ok (B : Blks) : Prop :=
  B.a.block = some B.ka ∧ B.b.block = some B.kb ∧ B.a.off = 0 ∧ B.b.off = 0 ∧ B.A1 % 4 = 0 ∧
    B.A2 % 4 = 0 ∧ B.Ac % 4 = 0

/-! ## Protocol -/

/-- Where `main` is: at its first spawn, its second spawn, the join of kid 1, of kid 2. -/
inductive Ph where
  | pre | one | j1 | j2
  deriving DecidableEq

inductive Gh where
  | none
  | main (ph : Ph) (r : Res) (B : Blks)
  /-- A kid: it owns `r`, its output `out` (address `A`); `done`: it wrote 9. -/
  | kid (r : Res) (out : Ptr) (A : Nat) (done : Bool)

/-- The resource that a thread owns. -/
def Gh.res : Gh → Res
  | .main _ r _ | .kid r _ _ _ => r
  | .none => rnil

/-- A kid's part at a stop: its output, 0 before it ran and 9 after. -/
def KidA (out : Ptr) (A : Nat) (done : Bool) : FAssn :=
  FAssn.ex fun bo : BlockId => ⟪out.block = some bo ∧ out.off = 0 ∧ A % 4 = 0⟫ ⋆
    u32At out A .stack bo (if done then 9 else 0)

/-- `main`'s part at each phase. -/
def MainA (B : Blks) : Ph → FAssn
  | .pre => cnt B.Ac 7 ⋆ (u32At B.a B.A1 .stack B.ka 0 ⋆ u32At B.b B.A2 .stack B.kb 0)
  | .one => cnt B.Ac 7 ⋆ u32At B.b B.A2 .stack B.kb 0
  | .j1 => cnt B.Ac 8
  | .j2 => cnt B.Ac 8 ⋆ u32At B.a B.A1 .stack B.ka 9

def IsKid (B : Blks) (G : ThreadId → Gh) (u : ThreadId) (done : Option Bool) : Prop :=
  ∃ r d, (done = none ∨ done = some d) ∧
    G u = if u = 1 then .kid r B.a B.A1 d else .kid r B.b B.A2 d

/-- Kid `u`'s record: spawned by `main`, with whatever instances it registered. -/
def KidRec (m : Mem) (u : ThreadId) (joined : Bool) : Prop :=
  ∃ tls, m.threads[u]? = some { spawner := 0, joined, tls }

def Shape (B : Blks) (G : ThreadId → Gh) (m : Mem) : Ph → Prop
  | .pre => m.threads.size = 1 ∧ ∀ u, 1 ≤ u → G u = .none
  | .one => m.threads.size = 2 ∧ KidRec m 1 false ∧ IsKid B G 1 none ∧ ∀ u, 2 ≤ u → G u = .none
  | .j1 => m.threads.size = 3 ∧ KidRec m 1 false ∧ KidRec m 2 false ∧ IsKid B G 1 none ∧
      IsKid B G 2 none ∧ ∀ u, 3 ≤ u → G u = .none
  | .j2 => m.threads.size = 3 ∧ KidRec m 1 true ∧ KidRec m 2 false ∧ IsKid B G 1 (some true) ∧
      IsKid B G 2 none ∧ ∀ u, 3 ≤ u → G u = .none

/-- The parts of the threads: a joined thread owns nothing. -/
def ownOf (G : ThreadId → Gh) (m : Mem) (u : ThreadId) : Res :=
  if joinedB m u then rnil else (G u).res

/-- The main thread's record: its instance of `counter` is block 0. -/
def mainRec : ThreadRec := { spawner := 0, joined := true, tls := #[(0, 0)] }

structure Inv (G : ThreadId → Gh) (m : Mem) : Prop where
  own : ∃ rO, FOwned (ownOf G m) rO m
  kids : ∀ u r out A d, G u = .kid r out A d → KidA out A d r
  main : ∃ ph r B, G 0 = .main ph r B ∧ B.Ok ∧ MainA B ph r ∧ Shape B G m ph
  t0 : m.threads[0]? = some mainRec

def proto : Proto Tgt Gh where
  inv := Inv
  init tgt g := match tgt with
    | .bumpTwice out => ∃ r A, g = .kid r out A false
    | .leak _ => False
  fin g := ∃ r out A, g = .kid r out A true
  strict := true
  joins g := ∃ r B, g = .main .j1 r B ∨ g = .main .j2 r B

def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 90908 ∧ joinedAll 0 m

/-! ## Facts about the protocol -/

theorem kid_live {G : ThreadId → Gh} {m : Mem} {u : ThreadId} {r out A}
    (hi : Inv G m) (hu : 0 < u) (hg : G u = .kid r out A false) :
    joinedB m u = false ∧ u < m.threads.size ∧ (u = 1 ∨ u = 2) := by
  obtain ⟨ph, hm, B, h0, -, -, hs⟩ := hi.main
  have hne : G u ≠ .none := fun he => by rw [hg] at he; cases he
  have jb : ∀ jn, KidRec m u jn → jn = false → joinedB m u = false := by
    rintro jn ⟨tls, hr⟩ hj; unfold joinedB; rw [hr]; simp [hj]
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
  | j1 =>
    obtain ⟨hsz, r1, r2, -, -, hn⟩ := hs
    by_cases h1 : u = 1
    · subst h1; exact ⟨jb _ r1 rfl, by rw [hsz]; decide, .inl rfl⟩
    · by_cases h2 : u = 2
      · subst h2; exact ⟨jb _ r2 rfl, by rw [hsz]; decide, .inr rfl⟩
      · exact absurd (hn u (by unfold ThreadId at *; omega)) hne
  | j2 =>
    obtain ⟨hsz, r1, r2, ⟨h', d, hd, hk1⟩, -, hn⟩ := hs
    by_cases h1 : u = 1
    · subst h1
      simp only [↓reduceIte] at hk1
      rw [hg] at hk1; cases hk1
      simp at hd
    · by_cases h2 : u = 2
      · subst h2; exact ⟨jb _ r2 rfl, by rw [hsz]; decide, .inr rfl⟩
      · exact absurd (hn u (by unfold ThreadId at *; omega)) hne

theorem ownOf_upd {G : ThreadId → Gh} {m m' : Mem} {u : ThreadId} {g : Gh}
    (hj' : joinedB m' = joinedB m) (hj : joinedB m u = false) :
    ownOf (upd G u g) m' = upd (ownOf G m) u g.res := by
  funext w
  unfold ownOf
  rw [hj']
  by_cases hw : w = u
  · subst hw; simp only [upd_self]; rw [hj]; rfl
  · rw [upd_ne _ _ hw, upd_ne _ _ hw]

theorem spawner0 {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) :
    ∀ r ∈ m.threads, r.spawner = 0 := by
  obtain ⟨ph, hm, B, h0, -, -, hs⟩ := hi.main
  have ht0 := hi.t0
  intro r hr
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  have hk : ∀ (j : Nat) (rec : ThreadRec), m.threads[j]? = some rec → rec.spawner = 0 →
      ∀ (hj : j < m.threads.size), m.threads[j].spawner = 0 := by
    intro j rec he hs hj
    rw [Array.getElem?_eq_getElem hj] at he
    simp only [Option.some.injEq] at he
    rw [he, hs]
  have hkr : ∀ j jn, KidRec m j jn → ∀ (hj : j < m.threads.size), m.threads[j].spawner = 0 :=
    fun j jn ⟨tls, hr⟩ hj => hk j _ hr rfl hj
  cases ph with
  | pre =>
    have : i = 0 := by have := hs.1; omega
    subst this; exact hk 0 _ ht0 rfl _
  | one =>
    obtain ⟨hsz, r1, -⟩ := hs
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact hk 0 _ ht0 rfl _
    · exact hkr 1 _ r1 _
  | j1 =>
    obtain ⟨hsz, r1, r2, -⟩ := hs
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hk 0 _ ht0 rfl _
    · exact hkr 1 _ r1 _
    · exact hkr 2 _ r2 _
  | j2 =>
    obtain ⟨hsz, r1, r2, -⟩ := hs
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hk 0 _ ht0 rfl _
    · exact hkr 1 _ r1 _
    · exact hkr 2 _ r2 _

/-- A kid's thread start changes only its own record. -/
theorem setTls_get_ne {m : Mem} {u v : ThreadId} {ids : Array (BlockId × BlockId)} (h : v ≠ u) :
    (m.setTls u ids).threads[v]? = m.threads[v]? := by
  unfold Mem.setTls
  simp only [Array.getElem?_modify]
  rw [if_neg (Ne.symm h)]

theorem setTls_kidRec {m : Mem} {u v : ThreadId} {ids : Array (BlockId × BlockId)} {jn : Bool}
    (h : KidRec m v jn) : KidRec (m.setTls u ids) v jn := by
  obtain ⟨tls, hr⟩ := h
  by_cases hv : v = u
  · subst hv
    refine ⟨ids, ?_⟩
    unfold Mem.setTls
    simp [Array.getElem?_modify, hr]
  · exact ⟨tls, by rw [setTls_get_ne hv]; exact hr⟩

theorem joinedB_of_threads {m m' : Mem} (h : m'.threads = m.threads) : joinedB m' = joinedB m := by
  funext v; unfold joinedB; rw [h]

theorem mem_setTls_spawner {m : Mem} {u : ThreadId} {ids : Array (BlockId × BlockId)} {r : ThreadRec}
    (hr : r ∈ (m.setTls u ids).threads) : ∃ r' ∈ m.threads, r'.spawner = r.spawner := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hr
  have hi' : i < m.threads.size := by simpa [Mem.setTls] using hi
  refine ⟨m.threads[i], Array.getElem_mem hi', ?_⟩
  simp only [Mem.setTls, Array.getElem_modify]
  split <;> rfl

/-! ## The worker -/

/-- The initial bytes of `counter`. -/
def init7 : Array Byte := Enc.encode (7 : BitVec 32)

theorem tlsInit_eq : tlsInit = [(0, init7, 4)] := rfl

theorem tlsInit_ok : ∀ x ∈ tlsInit, 0 < x.2.2 ∧ 0 < x.2.1.size := by
  intro x hx
  rw [tlsInit_eq, List.mem_singleton] at hx
  subst hx
  exact ⟨by decide, by show 0 < (Enc.encode (7 : BitVec 32)).size; rw [LawfulEnc.size_encode_u32]; decide⟩

/-- `counter += 1` through the pointer `p`. -/
def seg (p : Ptr) : MemM Unit :=
  load (BitVec 32) 4 p >>= fun v => (monadLift (Zig.add false v 1) : MemM (BitVec 32)) >>= fun w =>
    store (α := BitVec 32) 4 p w

/-- The worker as one `MemM` chain: three `tlsPtr`s, two increments and the output. -/
theorem bumpTwice_eq (out : Ptr) : bumpTwice out =
    (tlsPtr 0 >>= fun p₁ => seg p₁ >>= fun _ => tlsPtr 0 >>= fun p₂ => seg p₂ >>= fun _ =>
      tlsPtr 0 >>= fun p₃ => load (BitVec 32) 4 p₃ >>= fun v₃ => store (α := BitVec 32) 4 out v₃) := by
  unfold bumpTwice seg
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_monadLift]

/-- One increment of a thread's instance (block `b`, address `A`). -/
theorem seg_spec {b : BlockId} {A : Nat} {v w : BitVec 32} (hA : A % 4 = 0)
    (hw : (Zig.add false v 1).run = some (.ok w)) :
    FTTriple (u32At ⟨some b, 0⟩ A .global b v) (seg ⟨some b, 0⟩)
      (fun _ => u32At ⟨some b, 0⟩ A .global b w) := by
  unfold seg
  refine (FTTriple.loadAt (k := 0) (a := 4) (v := v) rfl (by simp [Ptr.add]) (by decide)
    (by rw [LawfulEnc.size_encode_u32]; decide) (by simpa using hA) (LawfulEnc.decode_extract v)).bind fun x =>
      FTTriple.lift fun hx => ?_
  subst x
  refine (FTTriple.liftR_ok hw).bind fun y => FTTriple.lift fun hy => ?_
  subst y
  refine (FTTriple.storeAt (k := 0) (a := 4) w rfl (by simp [Ptr.add]) (by decide)
    (by rw [LawfulEnc.size_encode_u32]; decide) (by simpa using hA) (by decide)).post fun _ _ h => ?_
  rwa [wr] at h

/-- The output: the instance's value, stored in `out` (block `bo`, address `Ao`). -/
theorem out_spec {b bo : BlockId} {A Ao : Nat} {out : Ptr} {v : BitVec 32} (hA : A % 4 = 0)
    (hob : out.block = some bo) (ho : out.off = 0) (hAo : Ao % 4 = 0) :
    FTTriple (u32At out Ao .stack bo 0 ⋆ u32At ⟨some b, 0⟩ A .global b v)
      (load (BitVec 32) 4 ⟨some b, 0⟩ >>= fun x => store (α := BitVec 32) 4 out x)
      (fun _ => u32At out Ao .stack bo v ⋆ u32At ⟨some b, 0⟩ A .global b v) := by
  refine ((FTTriple.loadAt (k := 0) (a := 4) (v := v) rfl (by simp [Ptr.add]) (by decide)
    (by rw [LawfulEnc.size_encode_u32]; decide) (by simpa using hA) (LawfulEnc.decode_extract v)).frameL
    (R := u32At out Ao .stack bo 0)).bind fun x => ?_
  refine FTTriple.pre (P := ⟪x = v⟫ ⋆ (u32At out Ao .stack bo 0 ⋆ u32At ⟨some b, 0⟩ A .global b v))
    (FTTriple.lift fun hx => ?_) fun _ h => sep_lcomm h
  subst x
  refine (FTTriple.storeAt (k := 0) (a := 4) v hob (by simp [Ptr.add]) (by decide)
    (by rw [LawfulEnc.size_encode_u32]; decide) (by simp [ho, hAo]) (by decide)).frame.post fun _ _ h => ?_
  rwa [wr] at h

theorem add7 : (Zig.add false (7 : BitVec 32) 1).run = some (.ok 8) := by decide
theorem add8' : (Zig.add false (8 : BitVec 32) 1).run = some (.ok 9) := by decide

/-- A dying instance: the whole block, any bytes. -/
theorem dying_one {b : BlockId} {A : Nat} {v : BitVec 32} {R : FAssn} {r : Res}
    (h : (u32At ⟨some b, 0⟩ A .global b v ⋆ R) r) : (tlsDying [b] ⋆ R) r := by
  obtain ⟨r₁, r₂, hd, e, h1, h2⟩ := h
  refine ⟨r₁, r₂, hd, e, sep_emp.mpr ⟨A, Enc.encode v, sep_lift.mpr ⟨by rw [LawfulEnc.size_encode_u32]; decide, ?_⟩⟩, h2⟩
  show (up (bytesAt ⟨some b, 0⟩ A (Enc.encode v).size .global (Enc.encode v)) ⋆
    bext b (Enc.encode v).size .global) r₁
  rw [LawfulEnc.size_encode_u32]; exact h1

/-! ## The kids -/

theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : Inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | leak _ => exact hg.elim
  | bumpTwice out =>
    obtain ⟨r, A, rfl⟩ := hg
    obtain ⟨hj, hut, h12⟩ := kid_live hi hu hgu
    obtain ⟨bo, ⟨hob, ho0, hA⟩, hcell⟩ := sep_lift_ex hi u hgu
    obtain ⟨rO, ho⟩ := hi.own
    have hown : ownOf G m u = r := by unfold ownOf; rw [hj, hgu]; rfl
    have hp₀ : u32At out A .stack bo 0 (ownOf G m u) := by rw [hown]; exact hcell
    have hu0 : u ≠ 0 := Nat.pos_iff_ne_zero.mp hu
    show proto.WP u (ConcM.tlsThread tlsInit (discard (ConcM.liftMem (bumpTwice out)))) _ G _ d
    unfold ConcM.tlsThread
    -- The thread start: a new block with 7.
    refine WP.bind (WP.liftMem_tlsEnter_fowned (R := u32At out A .stack bo 0) tlsInit_ok
      (ho.current u) rfl hut hp₀ fun ids m₁ r₁ ho₁ hq₁ hc₁ ht₁ => ?_)
    rw [tlsInit_eq] at hq₁
    obtain ⟨r₁a, r₁b, hd₁, e₁, hout₁, hown₁⟩ := hq₁
    obtain ⟨b, hl, Ac', hinst⟩ := tlsOwn_one hown₁
    obtain ⟨hAc', hinst⟩ := sep_lift.mp hinst
    have hids : ids = #[(0, b)] := by
      cases ids; simp at hl; subst hl; rfl
    subst hids
    have hut₁ : u < m₁.threads.size := by rw [ht₁]; exact hut
    have hreg : (m₁.setTls u #[(0, b)]).tlsOf u = #[(0, b)] := by
      rw [Mem.tlsOf_setTls _ _ _ _ hut₁, if_pos rfl]
    have hk : (m₁.setTls u #[(0, b)]).tlsInstance u 0 = some b := by
      unfold Mem.tlsInstance; rw [hreg]; rfl
    have hc₂ : (m₁.setTls u #[(0, b)]).current = u := hc₁
    have hut₂ : u < (m₁.setTls u #[(0, b)]).threads.size := by simpa using hut₁
    have hinst' : u32At ⟨some b, 0⟩ Ac' .global b 7 r₁b := by
      have h := hinst
      simp only [gblk] at h
      rw [show init7.size = 4 from LawfulEnc.size_encode_u32 7] at h
      exact h
    have hp₂ : (u32At out A .stack bo 0 ⋆ u32At ⟨some b, 0⟩ Ac' .global b 7)
        (upd (ownOf G m) u r₁ u) := by
      rw [upd_self]; exact ⟨r₁a, r₁b, hd₁, e₁, hout₁, hinst'⟩
    -- The worker.
    refine WP.bind ?_
    show proto.WP u ((fun _ => ()) <$> ConcM.liftMem (bumpTwice out)) _ G _ d
    refine WP.map ?_
    rw [bumpTwice_eq]
    refine WP.liftMem_tlsPtr_bind (by rw [hc₂]; exact hk) ?_
    refine WP.liftMem_fowned_bind ((seg_spec (b := b) hAc' add7).frameL
      (R := u32At out A .stack bo 0)) ho₁ hc₂ hut₂ hp₂ fun _ m₃ r₃ ho₃ hq₃ hc₃ ht₃ => ?_
    rw [upd_upd] at ho₃
    refine WP.liftMem_tlsPtr_bind (by rw [hc₃, Mem.tlsInstance_of_threads ht₃]; exact hk) ?_
    refine WP.liftMem_fowned_bind ((seg_spec (b := b) hAc' add8').frameL
      (R := u32At out A .stack bo 0)) ho₃ hc₃ (by rw [ht₃]; exact hut₂) (by rw [upd_self]; exact hq₃)
      fun _ m₄ r₄ ho₄ hq₄ hc₄ ht₄ => ?_
    rw [upd_upd] at ho₄
    refine WP.liftMem_tlsPtr_bind
      (by rw [hc₄, Mem.tlsInstance_of_threads (ht₄.trans ht₃)]; exact hk) ?_
    refine WP.liftMem_fowned (out_spec (b := b) (v := 9) hAc' hob ho0 hA) ho₄ hc₄
      (by rw [ht₄, ht₃]; exact hut₂) (by rw [upd_self]; exact hq₄)
      fun _ m₅ r₅ _ ho₅ hq₅ hc₅ ht₅ => ?_
    rw [upd_upd] at ho₅
    have ht₅' : m₅.threads = (m₁.setTls u #[(0, b)]).threads := ht₅.trans (ht₄.trans ht₃)
    -- The thread end: its instance is freed.
    have hR₅ : (m₅.tlsOf u).toList.map (·.2) = [b] := by
      rw [Mem.tlsOf_of_threads ht₅', hreg]; rfl
    refine WP.liftMem_tlsExit_fowned (R := u32At out A .stack bo 9) ho₅ hc₅
      (by rw [ht₅']; exact hut₂) (by rw [upd_self, hR₅]; exact dying_one (sep_comm hq₅))
      fun m₆ r₆ ho₆ hq₆ hc₆ ht₆ => ?_
    rw [upd_upd] at ho₆
    have ht₆' : m₆.threads = (m₁.setTls u #[(0, b)]).threads := ht₆.trans ht₅'
    have hjb : joinedB m₆ = joinedB m := by
      rw [joinedB_of_threads ht₆', joinedB_setTls, joinedB_of_threads ht₁]; rfl
    have hkid : ∀ v jn, KidRec m v jn → KidRec m₆ v jn := by
      intro v jn hr
      have := setTls_kidRec (m := m₁) (u := u) (ids := #[(0, b)]) (v := v) (jn := jn)
        (by obtain ⟨tls, hr⟩ := hr; exact ⟨tls, by rw [ht₁]; exact hr⟩)
      obtain ⟨tls, hr'⟩ := this
      exact ⟨tls, by rw [ht₆']; exact hr'⟩
    refine ⟨.kid r₆ out A true, ⟨⟨rO, ?_⟩, fun w h' o' A'' d' hw => ?_, ?_, ?_⟩, ⟨_, _, _, rfl⟩,
      fun _ => ?_⟩
    · rw [ownOf_upd hjb hj]; exact ho₆
    · by_cases hwu : w = u
      · subst hwu; rw [upd_self] at hw; cases hw
        exact ⟨bo, sep_lift.mpr ⟨⟨hob, ho0, hA⟩, hq₆⟩⟩
      · rw [upd_ne _ _ hwu] at hw; exact hi.kids w _ _ _ _ hw
    · obtain ⟨ph, hm, B, h0, hB, hma, hsh⟩ := hi.main
      refine ⟨ph, hm, B, by rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact h0, hB, hma, ?_⟩
      have hsz : m₆.threads.size = m.threads.size := by rw [ht₆']; simp [ht₁]
      have hik : ∀ w dn, IsKid B G w dn → w ≠ u ∨ dn = none →
          IsKid B (upd G u (.kid r₆ out A true)) w dn := by
        intro w dn ⟨h', d', hd', hk'⟩ hw
        by_cases hwu : w = u
        · subst hwu
          rcases hw with hw | rfl
          · exact absurd rfl hw
          · refine ⟨r₆, true, .inl rfl, ?_⟩
            rw [upd_self]
            rw [hgu] at hk'
            by_cases h1 : w = 1
            · simp only [h1, ↓reduceIte] at hk' ⊢; cases hk'; rfl
            · simp only [h1, ↓reduceIte] at hk' ⊢; cases hk'; rfl
        · exact ⟨h', d', hd', by rw [upd_ne _ _ hwu]; exact hk'⟩
      have hnone : ∀ k, (∀ w, k ≤ w → G w = .none) → ∀ w, k ≤ w →
          upd G u (.kid r₆ out A true) w = .none := by
        intro k hk' w hw
        by_cases hwu : w = u
        · subst hwu; have := hk' w hw; rw [hgu] at this; cases this
        · rw [upd_ne _ _ hwu]; exact hk' w hw
      cases ph with
      | pre => exact ⟨by rw [hsz]; exact hsh.1, hnone 1 hsh.2⟩
      | one =>
        obtain ⟨hsz', r1, k1, hn⟩ := hsh
        exact ⟨by rw [hsz]; exact hsz', hkid _ _ r1, hik 1 _ k1 (.inr rfl), hnone 2 hn⟩
      | j1 =>
        obtain ⟨hsz', r1, r2, k1, k2, hn⟩ := hsh
        exact ⟨by rw [hsz]; exact hsz', hkid _ _ r1, hkid _ _ r2, hik 1 _ k1 (.inr rfl),
          hik 2 _ k2 (.inr rfl), hnone 3 hn⟩
      | j2 =>
        obtain ⟨hsz', r1, r2, k1, k2, hn⟩ := hsh
        have hu1 : u ≠ 1 := by
          intro h1; subst h1
          obtain ⟨h', d', hd', hk'⟩ := k1
          rw [hgu] at hk'; simp only [↓reduceIte] at hk'; cases hk'
          simp at hd'
        exact ⟨by rw [hsz]; exact hsz', hkid _ _ r1, hkid _ _ r2,
          hik 1 _ k1 (.inl (Ne.symm hu1)), hik 2 _ k2 (.inr rfl), hnone 3 hn⟩
    · rw [ht₆', setTls_get_ne (Ne.symm hu0), ht₁]; exact hi.t0
    · refine joinedAll_of_main (fun r hr => ?_) hu
      rw [ht₆'] at hr
      obtain ⟨r', hr', hsr⟩ := mem_setTls_spawner hr
      rw [ht₁] at hr'
      rw [← hsr]; exact spawner0 hi r' hr'
where
  /-- A kid's part, unpacked. -/
  sep_lift_ex {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) (u : ThreadId) {r out A}
      (hgu : G u = .kid r out A false) :
      ∃ bo, (out.block = some bo ∧ out.off = 0 ∧ A % 4 = 0) ∧ u32At out A .stack bo 0 r := by
    obtain ⟨bo, h⟩ := hi.kids u _ _ _ _ hgu
    obtain ⟨hf, h⟩ := sep_lift.mp h
    exact ⟨bo, hf, h⟩

/-! ## `main` -/

theorem add9 : (Zig.add false (90000 : BitVec 32) 900).run = some (.ok 90900) := by decide
theorem add8 : (Zig.add false (90900 : BitVec 32) 8).run = some (.ok 90908) := by decide
theorem mul9a : (Zig.mul false (9 : BitVec 32) 10000).run = some (.ok 90000) := by decide
theorem mul9b : (Zig.mul false (9 : BitVec 32) 100).run = some (.ok 900) := by decide

theorem ownOf_main (m : Mem) (g : Gh) :
    ownOf (upd (fun _ => .none) 0 g) m = upd (fun _ => rnil) 0 g.res := by
  funext u
  by_cases hu : u = 0
  · subst hu; simp [ownOf, joinedB, upd]
  · simp only [ownOf, upd, hu, ↓reduceIte, Gh.res]; split <;> rfl

/-- The globals of `mem0`. -/
abbrev gs0 : List (Array Byte × Nat × BlockKind) := [(Enc.encode ((7 : BitVec 32) : BitVec 32), 4, .global)]

theorem mem0_t0 (σ : Placement) : (mem0 σ).threads[0]? = some mainRec := by
  simp [mem0, Mem.mainTls, Mem.setTls, Mem.ofGlobals, Mem.addGlobal, mainRec]

theorem mem0_size (σ : Placement) : (mem0 σ).threads.size = 1 := rfl

/-- **`main` owns its instance of `counter` from the start**: the start memory's globals
(`initRes_holds`) are its part. -/
theorem start (σ : Placement) : ∃ rO Ac, Ac % 4 = 0 ∧ ∃ r, cnt Ac 7 r ∧
    FOwned (upd (fun _ => rnil) 0 r) rO { mem0 σ with current := 0 } := by
  obtain ⟨hh, hg⟩ := initRes_holds σ gs0 (by intro g hg; simp at hg; subst hg; rfl)
  have hs := Mem.init_fseq σ gs0 (by simp [Mem.GlobalsFit, gs0, LawfulEnc.size_encode_u32])
  have ho := FOwned.one (m := { mem0 σ with current := 0 })
    (Holds.congrMem (m := Mem.ofGlobals σ gs0) rfl rfl hh) rfl rfl rfl hs.2.1 hs.2.2
  have hg' : (gblock 0 (Enc.encode (7 : BitVec 32)) 4 .global ⋆ emp) (initRes σ gs0) := hg
  obtain ⟨Ac, hg⟩ := sep_emp.mp hg'
  obtain ⟨hAc, hg⟩ := sep_lift.mp hg
  rw [LawfulEnc.size_encode_u32, gext, if_pos (by decide : (0 : Nat) < 4)] at hg
  exact ⟨_, Ac, hAc (by decide), _, sep_assoc' (sep_mono_right (fun _ h => sep_comm h) hg), ho⟩

/-- `main`'s `tlsPtr` finds its instance, block 0. -/
theorem main_inst {m : Mem} (hc : m.current = 0) (h0 : m.threads[0]? = some mainRec) :
    m.tlsInstance m.current 0 = some 0 := by
  rw [hc]
  apply Mem.tlsInstance_head
  unfold Mem.tlsOf; rw [h0]; rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem main_spec (σ : Placement) (d : Nat) :
    proto.WP 0 twoCounters QM (fun _ => .none) { mem0 σ with current := 0 } d := by
  unfold twoCounters
  obtain ⟨rO, Ac, hAc, r₀, hC₀, ho₀⟩ := start σ
  -- `a`, `b`.
  refine WP.bind (WP.liftMem_fowned (((FTTriple.alloc .stack 4 4 (by decide) (by decide)).frameL
    (R := cnt Ac 7)).pre fun _ h => sep_emp.mpr h) ho₀ rfl (by rw [mem0_size]; decide)
    hC₀ fun s0 m₁ r₁ _ ho₁ hq₁ hc₁ ht₁ => ?_)
  obtain ⟨Aa, ka, ⟨hab, ha0, hAa⟩, hq₁⟩ := FAssn.sep_ex_ex_lift hq₁
  rw [upd_upd] at ho₁
  refine WP.bind (WP.liftMem_fowned (((FTTriple.alloc .stack 4 4 (by decide) (by decide)).frameL
    (R := cnt Ac 7 ⋆ (up (bytesAt s0 Aa 4 .stack (Array.replicate 4 .undef)) ⋆ bext ka 4 .stack))).pre
    fun _ h => sep_emp.mpr h) ho₁ hc₁ (by rw [ht₁, mem0_size]; decide) hq₁
    fun s2 m₂ r₂ _ ho₂ hq₂ hc₂ ht₂ => ?_)
  obtain ⟨Ab, kb, ⟨hbb, hb0, hAb⟩, hq₂⟩ := FAssn.sep_ex_ex_lift hq₂
  rw [upd_upd] at ho₂
  have htt₂ : m₂.threads = (mem0 σ).threads := by rw [ht₂, ht₁]
  have F₂ := sep_assoc hq₂
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  -- `a = 0`, `b = 0`.
  refine WP.bind (WP.liftM_fowned ((FTTriple.storeAt (k := 0) (a := 4) (0 : BitVec 32) hab
    (by simp [Ptr.add]) (by decide) (by simp; decide) (by simp [ha0, hAa]) (by decide)).frame.frameL)
    ho₂ hc₂ (by rw [htt₂, mem0_size]; decide) F₂ fun _ m₃ r₃ _ ho₃ F₃ hc₃ ht₃ => ?_)
  rw [upd_upd] at ho₃
  refine WP.bind (WP.liftM_fowned ((FTTriple.storeAt (k := 0) (a := 4) (0 : BitVec 32) hbb
    (by simp [Ptr.add]) (by decide) (by simp; decide) (by simp [hb0, hAb]) (by decide)).frameL.frameL)
    ho₃ hc₃ (by rw [ht₃, htt₂, mem0_size]; decide) F₃ fun _ m₄ r₄ _ ho₄ F₄ hc₄ ht₄ => ?_)
  rw [upd_upd] at ho₄
  have htt₄ : m₄.threads = (mem0 σ).threads := by rw [ht₄, ht₃, htt₂]
  rw [enc_zero] at F₄
  dsimp only at F₄ ⊢
  let B : Blks := ⟨s0, s2, ka, kb, Aa, Ab, Ac⟩
  have hB : B.Ok := ⟨hab, hbb, ha0, hb0, hAa, hAb, hAc⟩
  have hM : MainA B .pre r₄ := F₄
  -- The first spawn: kid 1 gets `a`.
  obtain ⟨rP, rK1, hdPK, rfl, hPa, hKa⟩ :=
    sep_assoc' (sep_mono_right (fun _ h => sep_comm h) hM)
  refine WP.bind (WP.spawnC fun k _ => ⟨.main .pre (rsum rP rK1) B, ?_, fun G₁ m₅ hg₁ hi₅ =>
    ⟨.kid rK1 s0 Aa false, ⟨_, _, rfl⟩, fun child m₆ hf => ?_⟩⟩)
  · refine ⟨⟨rO, by rw [ownOf_main]; exact ho₄⟩, fun u _ _ _ _ hu => ?_,
      ⟨.pre, _, B, upd_self _ _ _, hB, hM, by rw [htt₄]; exact mem0_size σ, fun u hu => ?_⟩,
      by rw [htt₄]; exact mem0_t0 σ⟩
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu; cases hu
    · rw [upd_ne _ _ (by unfold ThreadId at *; omega)]
  obtain ⟨ph, hm, B', h0, -, -, hsh⟩ := hi₅.main
  rw [hg₁] at h0; cases h0
  obtain ⟨hsz₅, hn₅⟩ := hsh
  obtain ⟨rfl, hth₆⟩ := fork_threads hf
  obtain ⟨rO₅, ho₅⟩ := hi₅.own
  have hown₅ : ownOf G₁ m₅ 0 = ⟨rP.heap ∪ rK1.heap, rP.know.union rK1.know, rP.gh.add rK1.gh⟩ := by
    simp [ownOf, joinedB, hg₁, Gh.res]
  have ho₆ := FOwned.fork (ho₅.current 0) (by rw [hsz₅]; decide) hown₅ hdPK hf
  rw [hsz₅] at ho₆ ⊢
  dsimp only
  have hjb₆ : joinedB m₆ = joinedB m₅ := joinedB_fork hf
  have hjb1 : joinedB m₅ 1 = false := by
    simp [joinedB, Array.getElem?_eq_none (show m₅.threads.size ≤ 1 by omega)]
  have hi₆ : Inv (upd (upd G₁ 1 (.kid rK1 s0 Aa false)) 0 (.main .one rP B)) m₆ := by
    refine ⟨⟨rO₅, ?_⟩, fun u h c ac dn hu => ?_, ⟨.one, rP, B, upd_self _ _ _, hB, hPa, ?_⟩, ?_⟩
    · have e : ownOf (upd (upd G₁ 1 (.kid rK1 s0 Aa false)) 0 (.main .one rP B)) m₆ =
          upd (upd (ownOf G₁ m₅) 0 rP) 1 rK1 := by
        funext u
        unfold ownOf
        rw [hjb₆]
        by_cases h0 : u = 0
        · subst h0; simp [joinedB, upd, Gh.res]
        · by_cases h1 : u = 1
          · subst h1; simp [hjb1, upd, Gh.res]
          · simp [upd, h0, h1]
      rw [e]; exact ho₆
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu
        by_cases h1 : u = 1
        · subst h1; rw [upd_self] at hu; cases hu
          exact ⟨ka, sep_lift.mpr ⟨⟨hab, ha0, hAa⟩, hKa⟩⟩
        · rw [upd_ne _ _ h1, hn₅ u (by unfold ThreadId at *; omega)] at hu; cases hu
    · refine ⟨by rw [hth₆]; simp [hsz₅], ⟨#[], ?_⟩, ⟨rK1, false, .inl rfl, by simp [upd, B]⟩,
        fun u hu => ?_⟩
      · rw [hth₆, Array.getElem?_push, if_pos hsz₅.symm]
      · rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega),
          hn₅ u (by unfold ThreadId at *; omega)]
    · rw [hth₆, Array.getElem?_push, if_neg (by omega)]; exact hi₅.t0
  -- The second spawn: kid 2 gets `b`; `main` keeps its instance.
  obtain ⟨rC, rK2, hdCK, rfl, hCa, hK2a⟩ := hPa
  simp only [StateT.run_bind]
  refine WP.bind (WP.spawnC fun k _ => ⟨Gh.main .one (rsum rC rK2) B, hi₆, fun G₂ m₇ hg₂ hi₇ =>
    ⟨Gh.kid rK2 s2 Ab false, ⟨_, _, rfl⟩, fun child m₈ hf₂ => ?_⟩⟩)
  obtain ⟨ph, hm, B', h0, -, -, hsh⟩ := hi₇.main
  rw [hg₂] at h0; cases h0
  obtain ⟨hsz₇, r1₇, k1₇, hn₇⟩ := hsh
  obtain ⟨rfl, hth₈⟩ := fork_threads hf₂
  obtain ⟨rO₇, ho₇⟩ := hi₇.own
  have hown₇ : ownOf G₂ m₇ 0 = ⟨rC.heap ∪ rK2.heap, rC.know.union rK2.know, rC.gh.add rK2.gh⟩ := by
    simp [ownOf, joinedB, hg₂, Gh.res]
  have ho₈ := FOwned.fork (ho₇.current 0) (by rw [hsz₇]; decide) hown₇ hdCK hf₂
  rw [hsz₇] at ho₈ ⊢
  rw [upd_comm _ _ _ (show (0 : Nat) ≠ 2 by decide)] at ho₈
  dsimp only
  have hjb₈ : joinedB m₈ = joinedB m₇ := joinedB_fork hf₂
  have hjb2 : joinedB m₇ 2 = false := by
    simp [joinedB, Array.getElem?_eq_none (show m₇.threads.size ≤ 2 by omega)]
  have hc₈ : m₈.current = 0 := by
    rw [Proto.fork_run] at hf₂
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf₂
    rw [← hf₂.2]
  have ht0₈ : m₈.threads[0]? = some mainRec := by
    rw [hth₈, Array.getElem?_push, if_neg (by omega)]; exact hi₇.t0
  have hsz₈ : 0 < m₈.threads.size := by rw [hth₈]; simp
  -- `counter += 1` on `main`'s own instance.
  simp only [StateT.run_bind]
  refine WP.bind (WP.liftM_tlsPtr (main_inst hc₈ ht0₈) ?_)
  refine WP.bind (WP.liftM_fowned ((FTTriple.loadAt (p := ⟨some 0, 0⟩) (k := 0) (a := 4)
    (v := (7 : BitVec 32)) rfl (by simp [Ptr.add]) (by decide) (by rw [LawfulEnc.size_encode_u32]; decide)
    (by simpa using hAc) (LawfulEnc.decode_extract 7)).frame (R := known 0 Ac))
    ho₈ hc₈ hsz₈ hCa fun r₁ m₉ r₉ _ ho₉ hq₉ hc₉ ht₉ => ?_)
  obtain ⟨rfl, hC₉⟩ := lift_l hq₉
  rw [upd_upd] at ho₉
  refine WP.bind (WP.callRC_ok (v := (8 : BitVec 32)) add7 ?_)
  refine WP.bind (WP.liftM_fowned ((FTTriple.storeAt (p := ⟨some 0, 0⟩) (k := 0) (a := 4)
    (8 : BitVec 32) rfl (by simp [Ptr.add]) (by decide) (by rw [LawfulEnc.size_encode_u32]; decide) (by simpa using hAc)
    (by decide)).frame (R := known 0 Ac))
    ho₉ hc₉ (by rw [ht₉]; exact hsz₈) hC₉ fun _ m₁₀ r₁₀ _ ho₁₀ hC₁₀ hc₁₀ ht₁₀ => ?_)
  rw [upd_upd] at ho₁₀
  rw [wr] at hC₁₀
  have hth₁₀ : m₁₀.threads = m₈.threads := by rw [ht₁₀, ht₉]
  have hjb₁₀ : joinedB m₁₀ = joinedB m₇ := by rw [joinedB_of_threads hth₁₀, hjb₈]
  have hi₁₀ : Inv (upd (upd G₂ 2 (.kid rK2 s2 Ab false)) 0 (.main .j1 r₁₀ B)) m₁₀ := by
    refine ⟨⟨rO₇, ?_⟩, fun u h c ac dn hu => ?_, ⟨.j1, r₁₀, B, upd_self _ _ _, hB, hC₁₀, ?_⟩, ?_⟩
    · have e : ownOf (upd (upd G₂ 2 (.kid rK2 s2 Ab false)) 0 (.main .j1 r₁₀ B)) m₁₀ =
          upd (upd (ownOf G₂ m₇) 2 rK2) 0 r₁₀ := by
        funext u
        unfold ownOf
        rw [hjb₁₀]
        by_cases h0 : u = 0
        · subst h0; simp [joinedB, upd, Gh.res]
        · by_cases h2 : u = 2
          · subst h2; simp [hjb2, upd, Gh.res]
          · simp [upd, h0, h2]
      rw [e]; exact ho₁₀
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu
        by_cases h2 : u = 2
        · subst h2; rw [upd_self] at hu; cases hu
          exact ⟨kb, sep_lift.mpr ⟨⟨hbb, hb0, hAb⟩, hK2a⟩⟩
        · rw [upd_ne _ _ h2] at hu; exact hi₇.kids u _ _ _ _ hu
    · refine ⟨by rw [hth₁₀, hth₈]; simp [hsz₇], ?_, ?_, ?_, ⟨rK2, false, .inl rfl, by simp [upd, B]⟩,
        fun u hu => ?_⟩
      · obtain ⟨tls, hr⟩ := r1₇
        exact ⟨tls, by rw [hth₁₀, hth₈, Array.getElem?_push, if_neg (by omega)]; exact hr⟩
      · exact ⟨#[], by rw [hth₁₀, hth₈, Array.getElem?_push, if_pos hsz₇.symm]⟩
      · obtain ⟨h', d', hd', hk⟩ := k1₇
        exact ⟨h', d', hd', by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact hk⟩
      · rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega),
          hn₇ u (by unfold ThreadId at *; omega)]
    · rw [hth₁₀]; exact ht0₈
  -- The join of kid 1: `main` gets `a` back, with 9.
  refine WP.bind (WP.joinC fun k _ => ⟨Gh.main .j1 r₁₀ B, hi₁₀, fun G₃ m₁₁ hg₃ hi₁₁ => ?_⟩)
  obtain ⟨ph, hm, B', h0, -, hma₁₁, hsh⟩ := hi₁₁.main
  rw [hg₃] at h0; cases h0
  obtain ⟨hsz₁₁, r1₁₁, r2₁₁, k1₁₁, k2₁₁, hn₁₁⟩ := hsh
  obtain ⟨tls1, hr1⟩ := r1₁₁
  refine ⟨fun _ => ⟨by decide, by rw [hsz₁₁]; decide, ⟨_, B, .inl rfl⟩, by
    simp [Thread.joinValid, Mem.isGated, hr1]⟩,
    fun hfin => ⟨fun _ => join_run hr1 rfl rfl, fun m₁₂ hj => ?_⟩⟩
  obtain ⟨rk1, c', ac', hf1⟩ := hfin
  obtain ⟨h', d', -, hk1'⟩ := k1₁₁
  simp only [↓reduceIte] at hk1'
  rw [hf1] at hk1'; cases hk1'
  obtain ⟨ka1, hka1⟩ := hi₁₁.kids 1 _ _ _ _ hf1
  obtain ⟨⟨hka1b, -⟩, hka1⟩ := sep_lift.mp hka1
  rw [hab] at hka1b; cases hka1b
  simp only [↓reduceIte] at hka1
  obtain ⟨hc₁₂, hth₁₂⟩ := join_threads hr1 hj
  obtain ⟨rO₁₁, ho₁₁⟩ := hi₁₁.own
  have ho₁₂ := FOwned.join (ho₁₁.current 0) (by rw [hsz₁₁]; decide) (by decide) hj
  have e0 : ownOf G₃ m₁₁ 0 = r₁₀ := by simp [ownOf, joinedB, hg₃, Gh.res]
  have e1 : ownOf G₃ m₁₁ 1 = rk1 := by simp [ownOf, joinedB, hr1, hf1, Gh.res]
  rw [e0, e1] at ho₁₂
  have hjb₁₂ : ∀ u, joinedB m₁₂ u = if u = 1 then true else joinedB m₁₁ u := by
    intro u
    unfold joinedB
    rw [hth₁₂]
    by_cases h1 : u = 1
    · subst h1
      rw [Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz₁₁]; decide)]; rfl
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm h1)]; simp [h1]
  have hdk : FHeap.Disjoint r₁₀.heap rk1.heap := by
    have := ho₁₁.disj (u := 0) (v := 1) (by rw [hsz₁₁]; decide) (by rw [hsz₁₁]; decide) (by decide)
    rwa [e0, e1] at this
  have hi₁₂ : Inv (upd G₃ 0 (.main .j2 (rsum r₁₀ rk1) B)) m₁₂ := by
    refine ⟨⟨rO₁₁, ?_⟩, fun u h c ac dn hu => ?_, ⟨.j2, rsum r₁₀ rk1, B, upd_self _ _ _, hB,
      ⟨r₁₀, rk1, hdk, rfl, hma₁₁, by simpa [B] using hka1⟩, ?_⟩, ?_⟩
    · have e : ownOf (upd G₃ 0 (.main .j2 (rsum r₁₀ rk1) B)) m₁₂ =
          upd (upd (ownOf G₃ m₁₁) 1 rnil) 0 (rsum r₁₀ rk1) := by
        funext u
        unfold ownOf
        rw [hjb₁₂]
        by_cases h0 : u = 0
        · subst h0; simp [joinedB, upd, Gh.res]
        · by_cases h1 : u = 1
          · subst h1; simp [upd]
          · simp [upd, h0, h1]
      rw [e]; exact ho₁₂
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu; exact hi₁₁.kids u _ _ _ _ hu
    · refine ⟨by rw [hth₁₂, Array.size_setIfInBounds, hsz₁₁], ⟨tls1, ?_⟩, ?_,
        ⟨rk1, true, .inr rfl, by rw [upd_ne _ _ (by decide)]; exact hf1⟩, ?_, fun u hu => ?_⟩
      · rw [hth₁₂, Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz₁₁]; decide)]
      · obtain ⟨tls2, hr2⟩ := r2₁₁
        exact ⟨tls2, by rw [hth₁₂, Array.getElem?_setIfInBounds_ne (by decide)]; exact hr2⟩
      · obtain ⟨h'', d'', hd'', hk⟩ := k2₁₁
        exact ⟨h'', d'', hd'', by rw [upd_ne _ _ (by decide)]; exact hk⟩
      · rw [upd_ne _ _ (by unfold ThreadId at *; omega), hn₁₁ u hu]
    · rw [hth₁₂, Array.getElem?_setIfInBounds_ne (by decide)]; exact hi₁₁.t0
  -- The join of kid 2: `main` gets `b` back, with 9.
  refine WP.bind (WP.joinC fun k _ => ⟨Gh.main .j2 (rsum r₁₀ rk1) B, hi₁₂, fun G₄ m₁₃ hg₄ hi₁₃ => ?_⟩)
  obtain ⟨ph, hm, B', h0, -, hma₁₃, hsh⟩ := hi₁₃.main
  rw [hg₄] at h0; cases h0
  obtain ⟨hsz₁₃, r1₁₃, r2₁₃, k1₁₃, k2₁₃, hn₁₃⟩ := hsh
  obtain ⟨tls2, hr2⟩ := r2₁₃
  refine ⟨fun _ => ⟨by decide, by rw [hsz₁₃]; decide, ⟨_, B, .inr rfl⟩, by
    simp [Thread.joinValid, Mem.isGated, hr2]⟩,
    fun hfin => ⟨fun _ => join_run hr2 rfl rfl, fun m₁₄ hj₂ => ?_⟩⟩
  obtain ⟨rk2, c'', ac'', hf2⟩ := hfin
  obtain ⟨h'', d'', -, hk2'⟩ := k2₁₃
  simp only [show (2 : Nat) ≠ 1 by decide, ↓reduceIte] at hk2'
  rw [hf2] at hk2'; cases hk2'
  obtain ⟨kb2, hka2⟩ := hi₁₃.kids 2 _ _ _ _ hf2
  obtain ⟨⟨hkb2, -⟩, hka2⟩ := sep_lift.mp hka2
  rw [hbb] at hkb2; cases hkb2
  simp only [↓reduceIte] at hka2
  obtain ⟨hc₁₄, hth₁₄⟩ := join_threads hr2 hj₂
  obtain ⟨rO₁₃, ho₁₃⟩ := hi₁₃.own
  have ho₁₄ := FOwned.join (ho₁₃.current 0) (by rw [hsz₁₃]; decide) (by decide) hj₂
  have e0 : ownOf G₄ m₁₃ 0 = rsum r₁₀ rk1 := by simp [ownOf, joinedB, hg₄, Gh.res]
  have e2 : ownOf G₄ m₁₃ 2 = rk2 := by simp [ownOf, joinedB, hr2, hf2, Gh.res]
  have hd12 : FHeap.Disjoint (rsum r₁₀ rk1).heap rk2.heap := by
    have := ho₁₃.disj (u := 0) (v := 2) (by rw [hsz₁₃]; decide) (by rw [hsz₁₃]; decide) (by decide)
    rwa [e0, e2] at this
  rw [e0, e2] at ho₁₄
  have hA : ((cnt Ac 8 ⋆ u32At s0 Aa .stack ka 9) ⋆ u32At s2 Ab .stack kb 9)
      (rsum (rsum r₁₀ rk1) rk2) :=
    ⟨_, rk2, hd12, rfl, hma₁₃, by simpa [B] using hka2⟩
  have hja : joinedAll 0 m₁₄ := by
    intro r hr _
    rw [hth₁₄] at hr
    obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hr
    have hi' : i < 3 := by simpa [hsz₁₃] using hi
    have hget : (m₁₃.threads.setIfInBounds 2
        { ({ spawner := 0, joined := false, tls := tls2 } : ThreadRec) with joined := true })[i]? =
        some r := by
      rw [Array.getElem?_eq_getElem hi, he]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · rw [Array.getElem?_setIfInBounds_ne (by decide), hi₁₃.t0] at hget; cases hget; rfl
    · obtain ⟨tls1', hr1'⟩ := r1₁₃
      rw [Array.getElem?_setIfInBounds_ne (by decide), hr1'] at hget; cases hget; rfl
    · rw [Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz₁₃]; decide)] at hget; cases hget; rfl
  have htl : 0 < m₁₄.threads.size := by rw [hth₁₄, Array.size_setIfInBounds, hsz₁₃]; decide
  have hth₁₄₀ : m₁₄.threads[0]? = some mainRec := by
    rw [hth₁₄, Array.getElem?_setIfInBounds_ne (by decide)]; exact hi₁₃.t0
  -- `a * 10000 + b * 100 + counter`.
  refine WP.bind (WP.liftM_fowned ((FTTriple.loadAt (p := s0) (A := Aa) (S := 4) (K := .stack)
    (k := 0) (a := 4) (v := (9 : BitVec 32)) hab (by simp [Ptr.add]) (by decide)
    (by rw [LawfulEnc.size_encode_u32]; decide) (by simp [ha0, hAa]) (LawfulEnc.decode_extract 9)).frameL.frame.post
    fun _ _ h => sep_assoc (sep_mono_left (fun _ h => sep_lcomm h) h))
    ho₁₄ hc₁₄ htl hA fun r₁ m₁₅ r₁₅ _ ho₁₅ hq₁₅ hc₁₅ ht₁₅ => ?_)
  obtain ⟨rfl, F₁₅⟩ := sep_lift.mp hq₁₅
  rw [upd_upd] at ho₁₅
  refine WP.bind (WP.callRC_ok (v := (90000 : BitVec 32)) mul9a ?_)
  refine WP.bind (WP.liftM_fowned ((FTTriple.loadAt (p := s2) (A := Ab) (S := 4) (K := .stack)
    (k := 0) (a := 4) (v := (9 : BitVec 32)) hbb (by simp [Ptr.add]) (by decide)
    (by rw [LawfulEnc.size_encode_u32]; decide) (by simp [hb0, hAb]) (LawfulEnc.decode_extract 9)).frameL.post
    fun _ _ h => sep_lcomm h)
    ho₁₅ hc₁₅ (by rw [ht₁₅]; exact htl) F₁₅ fun r₂ m₁₆ r₁₆ _ ho₁₆ hq₁₆ hc₁₆ ht₁₆ => ?_)
  obtain ⟨rfl, F₁₆⟩ := sep_lift.mp hq₁₆
  rw [upd_upd] at ho₁₆
  refine WP.bind (WP.callRC_ok (v := (900 : BitVec 32)) mul9b ?_)
  refine WP.bind (WP.callRC_ok (v := (90900 : BitVec 32)) add9 ?_)
  refine WP.bind (WP.liftM_tlsPtr (main_inst hc₁₆ (by rw [ht₁₆, ht₁₅]; exact hth₁₄₀)) ?_)
  refine WP.bind (WP.liftM_fowned ((FTTriple.loadAt (p := ⟨some 0, 0⟩) (A := Ac) (S := 4)
    (K := .global) (k := 0) (a := 4) (v := (8 : BitVec 32)) rfl (by simp [Ptr.add]) (by decide)
    (by rw [LawfulEnc.size_encode_u32]; decide) (by simpa using hAc) (LawfulEnc.decode_extract 8)).frame.frame.frame
    (R := u32At s2 Ab .stack kb 9))
    ho₁₆ hc₁₆ (by rw [ht₁₆, ht₁₅]; exact htl) F₁₆ fun r₃ m₁₇ r₁₇ _ ho₁₇ hq₁₇ hc₁₇ ht₁₇ => ?_)
  obtain ⟨rfl, F₁₇⟩ := lift_l (lift_l' hq₁₇)
  rw [upd_upd] at ho₁₇
  refine WP.bind (WP.callRC_ok (v := (90908 : BitVec 32)) add8 ?_)
  refine WP.pure' ?_
  -- The frees.
  have htl₁₇ : 0 < m₁₇.threads.size := by rw [ht₁₇, ht₁₆, ht₁₅]; exact htl
  -- In reverse order of allocation (MM-18): `b`, then `a`.
  refine WP.bind (WP.liftMem_fowned ((FTTriple.free_front (R := cnt Ac 8 ⋆ u32At s0 Aa .stack ka 9)
    (K := .stack) hbb (LawfulEnc.size_encode_u32 9) hb0 (by decide)).pre fun _ h => sep_comm h)
    ho₁₇ hc₁₇ htl₁₇ F₁₇ fun _ m₁₈ r₁₈ _ ho₁₈ hq₁₈ hc₁₈ ht₁₈ => ?_)
  rw [upd_upd] at ho₁₈
  refine WP.bind (WP.liftMem_fowned ((FTTriple.free_front (R := cnt Ac 8) (K := .stack) hab
    (LawfulEnc.size_encode_u32 9) ha0 (by decide)).pre
    fun _ h => sep_comm h) ho₁₈ hc₁₈ (by rw [ht₁₈]; exact htl₁₇) hq₁₈
    fun _ m₁₉ _ _ _ _ _ ht₁₉ => ?_)
  refine WP.pure' ⟨rfl, fun r hr hs => hja r ?_ hs⟩
  rwa [ht₁₉, ht₁₈, ht₁₇, ht₁₆, ht₁₅] at hr
where
  /-- The pure fact of a load framed twice more. -/
  lift_l' {φ : Prop} {P Q R S : FAssn} {r : Res} (h : ((((⟪φ⟫ ⋆ P) ⋆ Q) ⋆ R) ⋆ S) r) :
      ((⟪φ⟫ ⋆ ((P ⋆ Q) ⋆ R)) ⋆ S) r :=
    sep_mono_left (fun _ h => sep_assoc (sep_mono_left (fun _ h => sep_assoc h) h)) h

/-! ## The results -/

/-- **`twoCounters` returns 90908 under every placement and every schedule**: each worker read 9
from its own `counter` and `main` read 8 from its own. -/
theorem twoCounters_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat}
    {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run env dispatch fuel o twoCounters (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 90908 := by
  obtain ⟨_, _, hv, -⟩ := proto.run_sound env (Proto.of_available henv) dispatch (fun _ => .none)
    dispatch_spec (fun _ _ _ _ _ hq => hq.2) (mem0_size σ) (main_spec σ) h
  exact hv

/-- **No run of `twoCounters` gives an error**: the concurrent increments of the three
instances do not race. -/
theorem twoCounters_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat}
    {o : Nat → Nat} {e : Error} :
    e ≠ .stackOverflow → (Sched.run env dispatch fuel o twoCounters (mem0 σ)).run ≠ some (.error e) :=
  proto.run_safe env (Proto.of_available henv) dispatch (fun _ => .none) rfl dispatch_spec
    (fun _ _ _ _ hq => hq.2) (mem0_size σ) (main_spec σ)

end ThreadLocals.Counters
