import ThreadLocals.Gen
import ZigLean.Conc.TlsLemmas
import ZigLean.Simp

/-!
# Three threads, three counters: `twoCounters` over all schedules

`twoCounters` (the retained translation of `thread_locals.twoCounters`) stores 0 in its locals
`a` and `b`, spawns `bumpTwice(&a)` and `bumpTwice(&b)`, increments its own `counter`, joins
both and returns `a * 10000 + b * 100 + counter`. Each worker increments *its own* `counter`
twice and stores the value it then reads in its output.

`twoCounters_spec`: under every schedule and every fuel, an `ok` result is `90908`: each worker
read 9 (7 + 2) and `main` read 8 (7 + 1). `twoCounters_safe`: no run gives an error (no race,
no panic, no deadlock). So the three instances of `counter` do not alias, each starts at the
initial value 7, and the concurrent increments do not race.

The proof is in concurrent separation logic, as `Proofs/Threads/Disjoint.lean`, with the
thread-local blocks owned by their threads:

- `main` owns its instance (block 0 of `mem0`, `cnt`) from the start (`Owned.add`); its
  `tlsPtr` reads the record `mem0` registered (`WP.liftM_tlsPtr`).
- A kid owns its output cell (handed over at the spawn, `Owned.fork`) and, after its thread
  start, the new block `tlsEnter` made (`TTriple.tlsAllocs_one`, `Owned.setTls`). Its worker is
  one thread triple with the thread records fixed (`TTripleIn`, `TTripleIn.tlsPtr`); at its end
  it frees its instance (`TTripleIn.tlsExit_one`) and keeps only its output.
- At each join `main` takes the kid's output back (`Owned.join`).
-/

open Zig Zig.Conc Zig.Conc.Proto Assn

namespace ThreadLocals.Counters

/-! ## Blocks and heaps -/

/-- A `u32` at `p` (address `A`, kind `K`) that holds `v`. -/
def u32At (p : Ptr) (A : Nat) (K : BlockKind) (v : BitVec 32) : Assn :=
  bytesAt p A 4 K (Enc.encode v)

/-- `main`'s instance of `counter`: block 0 of `mem0`. -/
def cnt (v : BitVec 32) : Assn := u32At ⟨some 0, 0⟩ 4096 .global v

theorem enc_u32 (v : BitVec 32) : (Enc.encode v).size = 4 := LawfulEnc.size_encode v

theorem decode_u32 (v : BitVec 32) : Enc.decode ((Enc.encode v).extract 0 (0 + Enc.size (BitVec 32))) =
    (pure v : Result (BitVec 32)) := by
  rw [show 0 + Enc.size (BitVec 32) = (Enc.encode v).size from (enc_u32 v).symm, Array.extract_size]
  exact LawfulEnc.decode_encode v

/-- `main`'s two output blocks, with their addresses. -/
structure Blks where
  a : Ptr
  b : Ptr
  A1 : Nat
  A2 : Nat

def Blks.Ok (B : Blks) : Prop := B.a.off = 0 ∧ B.b.off = 0 ∧ B.A1 % 4 = 0 ∧ B.A2 % 4 = 0

/-! ## Protocol -/

/-- Where `main` is: at its first spawn, its second spawn, the join of kid 1, of kid 2. -/
inductive Ph where
  | pre | one | j1 | j2
  deriving DecidableEq

inductive Gh where
  | none
  | main (ph : Ph) (h : Heap) (B : Blks)
  /-- A kid: it owns `h`, its output `out` (address `A`); `done`: it wrote 9. -/
  | kid (h : Heap) (out : Ptr) (A : Nat) (done : Bool)

def Gh.heap : Gh → Heap
  | .main _ h _ | .kid h _ _ _ => h
  | .none => Heap.empty

/-- A kid's heap at a stop: its output, 0 before it ran and 9 after. -/
def KidA (out : Ptr) (A : Nat) (done : Bool) : Assn :=
  ⌜out.off = 0 ∧ A % 4 = 0⌝ ∗ u32At out A .stack (if done then 9 else 0)

def MainA (B : Blks) : Ph → Assn
  | .pre => cnt 7 ∗ (u32At B.a B.A1 .stack 0 ∗ u32At B.b B.A2 .stack 0)
  | .one => cnt 7 ∗ u32At B.b B.A2 .stack 0
  | .j1 => cnt 8
  | .j2 => cnt 8 ∗ u32At B.a B.A1 .stack 9

def IsKid (B : Blks) (G : ThreadId → Gh) (u : ThreadId) (done : Option Bool) : Prop :=
  ∃ h d, (done = none ∨ done = some d) ∧
    G u = if u = 1 then .kid h B.a B.A1 d else .kid h B.b B.A2 d

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

def ownOf (G : ThreadId → Gh) (m : Mem) (u : ThreadId) : Heap :=
  if joinedB m u then Heap.empty else (G u).heap

/-- The main thread's record: its instance of `counter` is block 0. -/
def mainRec : ThreadRec := { spawner := 0, joined := true, tls := #[(0, 0)] }

structure Inv (G : ThreadId → Gh) (m : Mem) : Prop where
  own : Owned (ownOf G m) m
  kids : ∀ u h out A d, G u = .kid h out A d → KidA out A d h
  main : ∃ ph h B, G 0 = .main ph h B ∧ B.Ok ∧ MainA B ph h ∧ Shape B G m ph
  t0 : m.threads[0]? = some mainRec

def proto : Proto Tgt Gh where
  inv := Inv
  init tgt g := match tgt with
    | .bumpTwice out => ∃ h A, g = .kid h out A false
    | .leak _ => False
  fin g := ∃ h out A, g = .kid h out A true
  strict := true
  joins g := ∃ h B, g = .main .j1 h B ∨ g = .main .j2 h B

def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 90908 ∧ joinedAll 0 m

/-! ## Facts about the protocol -/

theorem kid_live {G : ThreadId → Gh} {m : Mem} {u : ThreadId} {h out A}
    (hi : Inv G m) (hu : 0 < u) (hg : G u = .kid h out A false) :
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
    ownOf (upd G u g) m' = upd (ownOf G m) u g.heap := by
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

/-- The worker as one `MemM` chain. -/
theorem bumpTwice_eq (out : Ptr) : bumpTwice out =
    (tlsPtr 0 >>= fun p₁ => load (BitVec 32) 4 p₁ >>= fun v₁ =>
      (monadLift (Zig.add false v₁ 1) : MemM (BitVec 32)) >>= fun w₁ => store (α := BitVec 32) 4 p₁ w₁ >>= fun _ =>
    tlsPtr 0 >>= fun p₂ => load (BitVec 32) 4 p₂ >>= fun v₂ =>
      (monadLift (Zig.add false v₂ 1) : MemM (BitVec 32)) >>= fun w₂ => store (α := BitVec 32) 4 p₂ w₂ >>= fun _ =>
    tlsPtr 0 >>= fun p₃ => load (BitVec 32) 4 p₃ >>= fun v₃ =>
      store (α := BitVec 32) 4 out v₃) := by
  unfold bumpTwice
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_monadLift]

/-- The worker, run by thread `t` whose instance of `counter` is block `b`: it reads 7, writes
8 and 9 to its own instance and 9 to its output. -/
theorem bumpTwice_spec {t : ThreadId} {R : Array ThreadRec} {b : BlockId} {A Ao : Nat}
    {out : Ptr} (hk : recInstance R t 0 = some b) (hA : A % 4 = 0) (ho : out.off = 0)
    (hAo : Ao % 4 = 0) :
    TTripleIn t R (u32At ⟨some b, 0⟩ A .global 7 ∗ u32At out Ao .stack 0) (bumpTwice out)
      (fun _ => u32At ⟨some b, 0⟩ A .global 9 ∗ u32At out Ao .stack 9) := by
  rw [bumpTwice_eq]
  have ld (v : BitVec 32) := TTriple.loadAt (p := (⟨some b, 0⟩ : Ptr))
    (A := A) (S := 4) (K := .global) (q := ⟨some b, 0⟩) (k := 0) (a := 4) (v := v)
    (by simp [Ptr.add]) (by decide) (by rw [enc_u32]; decide) (by simpa using hA) (decode_u32 v)
  have st (v w : BitVec 32) := TTriple.storeAt (p := (⟨some b, 0⟩ : Ptr)) (A := A)
    (S := 4) (K := .global) (bs := Enc.encode v) (q := ⟨some b, 0⟩) (k := 0) (a := 4) w
    (by simp [Ptr.add]) (by decide) (by rw [enc_u32]; decide) (by simpa using hA) (by decide)
  have wr (v w : BitVec 32) : writeBytes (Enc.encode v) 0 (Enc.encode w) = Enc.encode w :=
    writeBytes_all (by rw [enc_u32, enc_u32])
  refine (TTripleIn.tlsPtr hk).bind_eq ?_
  refine (TTripleIn.of (ld 7).frame_eq).bind_eq ?_
  refine (TTripleIn.of (TTriple.liftR_ok (x := (8 : BitVec 32)) (by rfl))).bind_eq ?_
  refine (TTripleIn.of (st 7 8).frame).bind fun _ => ?_
  simp only [u32At] at *
  rw [wr]
  refine (TTripleIn.tlsPtr hk).bind_eq ?_
  refine (TTripleIn.of (ld 8).frame_eq).bind_eq ?_
  refine (TTripleIn.of (TTriple.liftR_ok (x := (9 : BitVec 32)) (by rfl))).bind_eq ?_
  refine (TTripleIn.of (st 8 9).frame).bind fun _ => ?_
  rw [wr]
  refine (TTripleIn.tlsPtr hk).bind_eq ?_
  refine (TTripleIn.of (ld 9).frame_eq).bind_eq ?_
  exact TTripleIn.of ((TTriple.storeAt (p := out) (A := Ao) (S := 4) (K := .stack)
    (bs := Enc.encode (0 : BitVec 32)) (q := out) (k := 0) (a := 4) (9 : BitVec 32)
    (by simp [Ptr.add]) (by decide) (by rw [enc_u32]; decide) (by simp [ho, hAo]) (by decide)).frameL.conseq
    (fun _ h => h) fun _ _ h => by rwa [wr] at h)

/-! ## The kids -/

theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : Inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | leak _ => exact hg.elim
  | bumpTwice out =>
    obtain ⟨h, A, rfl⟩ := hg
    obtain ⟨hj, hut, h12⟩ := kid_live hi hu hgu
    have hka := hi.kids u _ _ _ _ hgu
    obtain ⟨⟨ho0, hA⟩, hcell⟩ := sep_lift.mp hka
    simp only [Bool.false_eq_true, ↓reduceIte] at hcell
    have hown : ownOf G m u = h := by unfold ownOf; rw [hj, hgu]; rfl
    have hu0 : u ≠ 0 := Nat.pos_iff_ne_zero.mp hu
    show proto.WP u (ConcM.tlsThread tlsInit (discard (ConcM.liftMem (bumpTwice out)))) _ G _ d
    unfold ConcM.tlsThread tlsEnter
    rw [liftMem_bind, tlsInit_eq]
    have ho₀ : Owned (upd (ownOf G m) u h) { m with current := u } := by
      rw [show upd (ownOf G m) u h = ownOf G m by rw [← hown, upd_same]]
      exact hi.own.current u
    -- The thread start: a new block with 7.
    refine WP.bind (WP.bind (WP.liftMem_upd (h := h)
      ((TTriple.tlsAllocs_one (key := 0) (bs := init7) (a := 4) (by decide)
        (by rw [show init7.size = 4 from enc_u32 7]; decide)).frameL
        (R := u32At out A .stack 0) |>.conseq (fun _ hh => sep_emp.mpr hh) fun _ _ hh => hh)
      ho₀ rfl hut hcell fun ids m₁ h₁ ho₁ hq₁ hc₁ ht₁ => ?_))
    obtain ⟨h₁a, h₁b, hd₁, rfl, hc₁', b, A', hq⟩ := hq₁
    obtain ⟨⟨rfl, hA'⟩, htls⟩ := sep_lift.mp hq
    have hut₁ : u < m₁.threads.size := by rw [ht₁]; exact hut
    rw [show init7.size = 4 from enc_u32 7] at htls
    refine WP.liftMem_setTls ?_
    -- The thread start registered block `b` as `u`'s instance.
    have hc₁u : m₁.current = u := hc₁
    simp only [hc₁u]
    have hreg : (m₁.setTls u #[(0, b)]).tlsOf u = #[(0, b)] := by
      rw [Mem.tlsOf_setTls _ _ _ _ hut₁, if_pos rfl]
    have hk : recInstance (m₁.setTls u #[(0, b)]).threads u 0 = some b := by
      rw [← Mem.tlsInstance_eq]; unfold Mem.tlsInstance; rw [hreg]; rfl
    have ho₂ : Owned (upd (ownOf G m) u (h₁a ∪ h₁b)) (m₁.setTls u #[(0, b)]) := ho₁.setTls
    have hut₂ : u < (m₁.setTls u #[(0, b)]).threads.size := by simpa using hut₁
    have hp₂ : (u32At ⟨some b, 0⟩ A' .global 7 ∗ u32At out A .stack 0)
        (upd (ownOf G m) u (h₁a ∪ h₁b) u) := by
      rw [upd_self]
      exact ⟨h₁b, h₁a, hd₁.symm, Heap.union_comm hd₁, htls, hc₁'⟩
    -- The worker.
    refine WP.bind (WP.map (WP.liftMem_ownedIn (bumpTwice_spec hk hA' ho0 hA) ho₂ hc₁ rfl hut₂ hp₂
      fun _ m₃ h₃ _ ho₃ hq₃ hs₃ => ?_))
    have ht₃ : m₃.threads = (m₁.setTls u #[(0, b)]).threads := hs₃.threads
    have hc₃ : m₃.current = u := hs₃.current.trans hc₁
    rw [upd_upd] at ho₃
    have hR₃ : ((m₃.threads[u]?).map (·.tls)).getD #[] = #[(0, b)] := by
      rw [ht₃]; exact hreg
    -- The thread end: its instance is freed.
    refine WP.liftMem_ownedIn (TTripleIn.tlsExit_one (key := 0) hR₃ (enc_u32 9) (by decide))
      ho₃ hc₃ rfl (by rw [ht₃]; exact hut₂) (by rw [upd_self]; exact hq₃)
      fun _ m₄ h₄ _ ho₄ hq₄ hs₄ => ?_
    rw [upd_upd] at ho₄
    have ht₄ : m₄.threads = (m₁.setTls u #[(0, b)]).threads := hs₄.threads.trans ht₃
    have hjb : joinedB m₄ = joinedB m := by
      rw [joinedB_of_threads ht₄, joinedB_setTls, joinedB_of_threads ht₁]; rfl
    have hkid : ∀ v jn, KidRec m v jn → KidRec m₄ v jn := by
      intro v jn hr
      have := setTls_kidRec (m := m₁) (u := u) (ids := #[(0, b)]) (v := v) (jn := jn)
        (by obtain ⟨tls, hr⟩ := hr; exact ⟨tls, by rw [ht₁]; exact hr⟩)
      obtain ⟨tls, hr'⟩ := this
      exact ⟨tls, by rw [ht₄]; exact hr'⟩
    refine ⟨.kid h₄ out A true, ⟨?_, fun w h' o' A'' d' hw => ?_, ?_, ?_⟩, ⟨_, _, _, rfl⟩,
      fun _ => ?_⟩
    · rw [ownOf_upd hjb hj]; exact ho₄
    · by_cases hwu : w = u
      · subst hwu; rw [upd_self] at hw; cases hw
        exact sep_lift.mpr ⟨⟨ho0, hA⟩, by simpa using hq₄⟩
      · rw [upd_ne _ _ hwu] at hw; exact hi.kids w _ _ _ _ hw
    · obtain ⟨ph, hm, B, h0, hB, hma, hsh⟩ := hi.main
      refine ⟨ph, hm, B, by rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact h0, hB, hma, ?_⟩
      have hsz : m₄.threads.size = m.threads.size := by rw [ht₄]; simp [ht₁]
      have hik : ∀ w dn, IsKid B G w dn → w ≠ u ∨ dn = none →
          IsKid B (upd G u (.kid h₄ out A true)) w dn := by
        intro w dn ⟨h', d', hd', hk'⟩ hw
        by_cases hwu : w = u
        · subst hwu
          rcases hw with hw | rfl
          · exact absurd rfl hw
          · refine ⟨h₄, true, .inl rfl, ?_⟩
            rw [upd_self]
            rw [hgu] at hk'
            by_cases h1 : w = 1
            · simp only [h1, ↓reduceIte] at hk' ⊢; cases hk'; rfl
            · simp only [h1, ↓reduceIte] at hk' ⊢; cases hk'; rfl
        · exact ⟨h', d', hd', by rw [upd_ne _ _ hwu]; exact hk'⟩
      have hnone : ∀ k, (∀ w, k ≤ w → G w = .none) → ∀ w, k ≤ w →
          upd G u (.kid h₄ out A true) w = .none := by
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
    · rw [ht₄, setTls_get_ne (Ne.symm hu0), ht₁]; exact hi.t0
    · intro r hr hsp
      rw [ht₄] at hr
      obtain ⟨r', hr', hsr⟩ := mem_setTls_spawner hr
      rw [ht₁] at hr'
      rw [← hsr, spawner0 hi r' hr'] at hsp
      unfold ThreadId at *; omega

/-! ## `main` -/

theorem add7 : (Zig.add false (7 : BitVec 32) 1).run = some (.ok 8) := by decide
theorem mul9a : (Zig.mul false (9 : BitVec 32) 10000).run = some (.ok 90000) := by decide
theorem mul9b : (Zig.mul false (9 : BitVec 32) 100).run = some (.ok 900) := by decide
theorem add9 : (Zig.add false (90000 : BitVec 32) 900).run = some (.ok 90900) := by decide
theorem add8 : (Zig.add false (90900 : BitVec 32) 8).run = some (.ok 90908) := by decide

theorem ownOf_main (m : Mem) (g : Gh) :
    ownOf (upd (fun _ => .none) 0 g) m = upd (fun _ => Heap.empty) 0 g.heap := by
  funext u
  by_cases hu : u = 0
  · subst hu; simp [ownOf, joinedB, upd]
  · simp only [ownOf, upd, hu, ↓reduceIte, Gh.heap]; split <;> rfl

/-- `main`'s instance of `counter` at program start, as a heap. -/
def hcnt : Heap := fun l =>
  if l.1 = 0 ∧ l.2 < 4 then some ⟨(Enc.encode (7 : BitVec 32))[l.2]!, 4096, 4, .global⟩ else none

theorem cnt_hcnt : cnt 7 hcnt := by
  refine ⟨0, rfl, by decide, fun l => ?_⟩
  simp only [hcnt, enc_u32, Int.toNat_zero, Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero]

theorem mem0_blocks :
    (mem0 .fresh).blocks = #[Block.mk (Enc.encode (7 : BitVec 32)) 4 .global true 4096] := rfl

theorem hcnt_sub : hcnt.Sub (mem0 .fresh).heap := by
  rintro ⟨b, x⟩ c h
  simp only [hcnt] at h
  split at h
  · rename_i hc
    obtain ⟨rfl, hx⟩ := hc
    cases h
    have hx' : x < (Enc.encode (7 : BitVec 32)).size := by rw [enc_u32]; exact hx
    unfold Mem.heap
    rw [mem0_blocks]
    simp only [enc_u32] at hx'
    simp [enc_u32]
    exact ⟨hx, by rw [getElem!_pos _ x (by rw [enc_u32]; exact hx)]⟩
  · cases h

theorem mem0_t0 : (mem0 .fresh).threads[0]? = some mainRec := by
  simp [mem0, Mem.mainTls, Mem.setTls, Mem.ofGlobals, Mem.addGlobal, mainRec]

theorem mem0_size : (mem0 .fresh).threads.size = 1 := rfl

theorem ho₀ : Owned (upd (fun _ => Heap.empty) 0 hcnt) { (mem0 .fresh) with current := 0 } := by
  have := Owned.add (own := fun _ => Heap.empty) (t := 0) (m := { (mem0 .fresh) with current := 0 })
    (Owned.start (by decide) (by decide)) (by decide) hcnt_sub
    (fun u => Heap.disjoint_empty _ |>.symm |> fun h => (h.symm)) (fun e he => by
      have : ({ (mem0 .fresh) with current := 0 } : Mem).footprint = #[] := by decide
      rw [this] at he; simp at he)
  simpa using this

theorem enc_zero : writeBytes (Array.replicate 4 .undef) 0 (Enc.encode (0 : BitVec 32)) =
    Enc.encode (0 : BitVec 32) :=
  writeBytes_all (by simp [enc_u32])

theorem wr (v w : BitVec 32) : writeBytes (Enc.encode v) 0 (Enc.encode w) = Enc.encode w :=
  writeBytes_all (by rw [enc_u32, enc_u32])

/-- `free` of the first block. -/
theorem free_front {R : Assn} {p : Ptr} {A S : Nat} {bs : Array Byte} (hS : bs.size = S)
    (h0 : p.off = 0) (hpos : 0 < S) :
    TTriple (bytesAt p A S .stack bs ∗ R) (Zig.free p) (fun _ => R) :=
  (TTriple.free hS h0 hpos).frame.conseq (fun _ h => h) fun _ _ h => sep_emp.mp (sep_comm h)

/-- `main`'s `tlsPtr` finds its instance, block 0. -/
theorem main_inst {m : Mem} (hc : m.current = 0) (h0 : m.threads[0]? = some mainRec) :
    m.tlsInstance m.current 0 = some 0 := by
  rw [hc]
  apply Mem.tlsInstance_head
  unfold Mem.tlsOf; rw [h0]; rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem main_spec (d : Nat) :
    proto.WP 0 twoCounters QM (fun _ => .none) { (mem0 .fresh) with current := 0 } d := by
  unfold twoCounters
  -- `a`, `b`.
  refine WP.bind (WP.liftMem_upd (alloc_next (R := cnt 7) 4 4 (by decide)) ho₀ rfl (by decide)
    cnt_hcnt fun s0 m₁ h₁ ho₁ hq₁ hc₁ ht₁ => ?_)
  obtain ⟨Aa, ⟨ha0, hAa⟩, hq₁⟩ := sep_ex_lift hq₁
  refine WP.bind (WP.liftMem_upd (alloc_next 4 4 (by decide)) ho₁ hc₁ (by rw [ht₁]; decide) hq₁
    fun s2 m₂ h₂ ho₂ hq₂ hc₂ ht₂ => ?_)
  obtain ⟨Ab, ⟨hb0, hAb⟩, hq₂⟩ := sep_ex_lift hq₂
  have htt₂ : m₂.threads = (mem0 .fresh).threads := by rw [ht₂, ht₁]
  have F₂ := sep_assoc hq₂
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  -- `a = 0`, `b = 0`.
  refine WP.bind (WP.liftM_upd ((TTriple.storeAt (k := 0) (a := 4) (0 : BitVec 32)
    (by simp [Ptr.add]) (by decide) (by simp; decide) (by simp [ha0, hAa]) (by decide)).frame.frameL)
    ho₂ hc₂ (by rw [htt₂]; decide) F₂ fun _ m₃ h₃ ho₃ F₃ hc₃ ht₃ => ?_)
  refine WP.bind (WP.liftM_upd ((TTriple.storeAt (k := 0) (a := 4) (0 : BitVec 32)
    (by simp [Ptr.add]) (by decide) (by simp; decide) (by simp [hb0, hAb]) (by decide)).frameL.frameL)
    ho₃ hc₃ (by rw [ht₃, htt₂]; decide) F₃ fun _ m₄ h₄ ho₄ F₄ hc₄ ht₄ => ?_)
  have htt₄ : m₄.threads = (mem0 .fresh).threads := by rw [ht₄, ht₃, htt₂]
  rw [enc_zero] at F₄
  dsimp only at F₄ ⊢
  let B : Blks := ⟨s0, s2, Aa, Ab⟩
  have hB : B.Ok := ⟨ha0, hb0, hAa, hAb⟩
  have hM : MainA B .pre h₄ := F₄
  -- The first spawn: kid 1 gets `a`.
  obtain ⟨hK1, hP, hdKP, rfl, hKa, hPa⟩ := sep_left_comm hM
  refine WP.bind (WP.spawnC fun k _ => ⟨.main .pre (hK1 ∪ hP) B, ?_, fun G₁ m₅ hg₁ hi₅ =>
    ⟨.kid hK1 s0 Aa false, ⟨_, _, rfl⟩, fun child m₆ hf => ?_⟩⟩)
  · refine ⟨by rw [ownOf_main]; exact ho₄, fun u _ _ _ _ hu => ?_,
      ⟨.pre, _, B, upd_self _ _ _, hB, hM, by rw [htt₄]; exact mem0_size, fun u hu => ?_⟩,
      by rw [htt₄]; exact mem0_t0⟩
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu; cases hu
    · rw [upd_ne _ _ (by unfold ThreadId at *; omega)]
  obtain ⟨ph, hm, B', h0, -, -, hsh⟩ := hi₅.main
  rw [hg₁] at h0; cases h0
  obtain ⟨hsz₅, hn₅⟩ := hsh
  obtain ⟨rfl, hth₆⟩ := fork_threads hf
  have hown₅ : ownOf G₁ m₅ 0 = hP ∪ hK1 := by
    simp [ownOf, joinedB, hg₁, Gh.heap, Heap.union_comm hdKP]
  have ho₆ := Owned.fork (hi₅.own.current 0) (by rw [hsz₅]; decide) hown₅ hdKP.symm hf
  rw [hsz₅] at ho₆ ⊢
  dsimp only
  have hjb₆ : joinedB m₆ = joinedB m₅ := joinedB_fork hf
  have hjb1 : joinedB m₅ 1 = false := by
    simp [joinedB, Array.getElem?_eq_none (show m₅.threads.size ≤ 1 by omega)]
  have hi₆ : Inv (upd (upd G₁ 1 (.kid hK1 s0 Aa false)) 0 (.main .one hP B)) m₆ := by
    refine ⟨?_, fun u h c ac dn hu => ?_, ⟨.one, hP, B, upd_self _ _ _, hB, hPa, ?_⟩, ?_⟩
    · have e : ownOf (upd (upd G₁ 1 (.kid hK1 s0 Aa false)) 0 (.main .one hP B)) m₆ =
          upd (upd (ownOf G₁ m₅) 0 hP) 1 hK1 := by
        funext u
        unfold ownOf
        rw [hjb₆]
        by_cases h0 : u = 0
        · subst h0; simp [joinedB, upd, Gh.heap]
        · by_cases h1 : u = 1
          · subst h1; simp [hjb1, upd, Gh.heap]
          · simp [upd, h0, h1]
      rw [e]; exact ho₆
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu
        by_cases h1 : u = 1
        · subst h1; rw [upd_self] at hu; cases hu
          exact sep_lift.mpr ⟨⟨ha0, hAa⟩, by simpa using hKa⟩
        · rw [upd_ne _ _ h1, hn₅ u (by unfold ThreadId at *; omega)] at hu; cases hu
    · refine ⟨by rw [hth₆]; simp [hsz₅], ⟨#[], ?_⟩, ⟨hK1, false, .inl rfl, by simp [upd, B]⟩,
        fun u hu => ?_⟩
      · rw [hth₆, Array.getElem?_push, if_pos hsz₅.symm]
      · rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega),
          hn₅ u (by unfold ThreadId at *; omega)]
    · rw [hth₆, Array.getElem?_push, if_neg (by omega)]; exact hi₅.t0
  -- The second spawn: kid 2 gets `b`; `main` keeps its instance.
  obtain ⟨hC, hK2, hdCK, rfl, hCa, hK2a⟩ := hPa
  simp only [StateT.run_bind]
  refine WP.bind (WP.spawnC fun k _ => ⟨Gh.main .one (hC ∪ hK2) B, hi₆, fun G₂ m₇ hg₂ hi₇ =>
    ⟨Gh.kid hK2 s2 Ab false, ⟨_, _, rfl⟩, fun child m₈ hf₂ => ?_⟩⟩)
  obtain ⟨ph, hm, B', h0, -, -, hsh⟩ := hi₇.main
  rw [hg₂] at h0; cases h0
  obtain ⟨hsz₇, r1₇, k1₇, hn₇⟩ := hsh
  obtain ⟨rfl, hth₈⟩ := fork_threads hf₂
  have hown₇ : ownOf G₂ m₇ 0 = hC ∪ hK2 := by simp [ownOf, joinedB, hg₂, Gh.heap]
  have ho₈ := Owned.fork (hi₇.own.current 0) (by rw [hsz₇]; decide) hown₇ hdCK hf₂
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
  -- `counter += 1` on `main`'s own instance.
  simp only [StateT.run_bind]
  refine WP.bind (WP.liftM_tlsPtr (main_inst hc₈ ht0₈) ?_)
  refine WP.bind (WP.liftM_upd ((TTriple.loadAt (p := ⟨some 0, 0⟩) (A := 4096) (S := 4)
    (K := .global) (k := 0) (a := 4) (v := (7 : BitVec 32))
    (by simp [Ptr.add]) (by decide) (by rw [enc_u32]; decide) (by decide) (decode_u32 7)))
    ho₈ hc₈ (by rw [hth₈]; simp [hsz₇]) hCa fun r₁ m₉ h₉ ho₉ hq₉ hc₉ ht₉ => ?_)
  obtain ⟨rfl, hC₉⟩ := sep_lift.mp hq₉
  refine WP.bind (WP.callRC_ok (v := (8 : BitVec 32)) add7 ?_)
  refine WP.bind (WP.liftM_upd ((TTriple.storeAt (k := 0) (a := 4) (8 : BitVec 32)
    (by simp [Ptr.add]) (by decide) (by rw [enc_u32]; decide) (by decide) (by decide)))
    ho₉ hc₉ (by rw [ht₉, hth₈]; simp [hsz₇]) hC₉ fun _ m₁₀ h₁₀ ho₁₀ hC₁₀ hc₁₀ ht₁₀ => ?_)
  rw [wr] at hC₁₀
  have hth₁₀ : m₁₀.threads = m₈.threads := by rw [ht₁₀, ht₉]
  have hjb₁₀ : joinedB m₁₀ = joinedB m₇ := by rw [joinedB_of_threads hth₁₀, hjb₈]
  have hi₁₀ : Inv (upd (upd G₂ 2 (.kid hK2 s2 Ab false)) 0 (.main .j1 h₁₀ B)) m₁₀ := by
    refine ⟨?_, fun u h c ac dn hu => ?_, ⟨.j1, h₁₀, B, upd_self _ _ _, hB, hC₁₀, ?_⟩, ?_⟩
    · have e : ownOf (upd (upd G₂ 2 (.kid hK2 s2 Ab false)) 0 (.main .j1 h₁₀ B)) m₁₀ =
          upd (upd (ownOf G₂ m₇) 2 hK2) 0 h₁₀ := by
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
          exact sep_lift.mpr ⟨⟨hb0, hAb⟩, by simpa using hK2a⟩
        · rw [upd_ne _ _ h2] at hu; exact hi₇.kids u _ _ _ _ hu
    · refine ⟨by rw [hth₁₀, hth₈]; simp [hsz₇], ?_, ?_, ?_, ⟨hK2, false, .inl rfl, by simp [upd, B]⟩,
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
  refine WP.bind (WP.joinC fun k _ => ⟨Gh.main .j1 h₁₀ B, hi₁₀, fun G₃ m₁₁ hg₃ hi₁₁ => ?_⟩)
  obtain ⟨ph, hm, B', h0, -, hma₁₁, hsh⟩ := hi₁₁.main
  rw [hg₃] at h0; cases h0
  obtain ⟨hsz₁₁, r1₁₁, r2₁₁, k1₁₁, k2₁₁, hn₁₁⟩ := hsh
  obtain ⟨tls1, hr1⟩ := r1₁₁
  refine ⟨fun _ => ⟨by decide, by rw [hsz₁₁]; decide, ⟨_, B, .inl rfl⟩, by
    simp [Thread.joinValid, hr1]⟩,
    fun hfin => ⟨fun _ => join_run hr1 rfl rfl, fun m₁₂ hj => ?_⟩⟩
  obtain ⟨hk1, c', ac', hf1⟩ := hfin
  obtain ⟨h', d', -, hk1'⟩ := k1₁₁
  simp only [↓reduceIte] at hk1'
  rw [hf1] at hk1'; cases hk1'
  obtain ⟨-, hka1⟩ := sep_lift.mp (hi₁₁.kids 1 _ _ _ _ hf1)
  simp only [↓reduceIte] at hka1
  obtain ⟨hc₁₂, hth₁₂⟩ := join_threads hr1 hj
  have ho₁₂ := Owned.join (hi₁₁.own.current 0) (by rw [hsz₁₁]; decide) (by decide) hj
  have e0 : ownOf G₃ m₁₁ 0 = h₁₀ := by simp [ownOf, joinedB, hg₃, Gh.heap]
  have e1 : ownOf G₃ m₁₁ 1 = hk1 := by simp [ownOf, joinedB, hr1, hf1, Gh.heap]
  rw [e0, e1] at ho₁₂
  have hjb₁₂ : ∀ u, joinedB m₁₂ u = if u = 1 then true else joinedB m₁₁ u := by
    intro u
    unfold joinedB
    rw [hth₁₂]
    by_cases h1 : u = 1
    · subst h1
      rw [Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz₁₁]; decide)]; rfl
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm h1)]; simp [h1]
  have hdk : Heap.Disjoint h₁₀ hk1 := by
    have := hi₁₁.own.disj 0 1 (by decide); rwa [e0, e1] at this
  have hi₁₂ : Inv (upd G₃ 0 (.main .j2 (h₁₀ ∪ hk1) B)) m₁₂ := by
    refine ⟨?_, fun u h c ac dn hu => ?_, ⟨.j2, h₁₀ ∪ hk1, B, upd_self _ _ _, hB,
      ⟨h₁₀, hk1, hdk, rfl, hma₁₁, by simpa [B] using hka1⟩, ?_⟩, ?_⟩
    · have e : ownOf (upd G₃ 0 (.main .j2 (h₁₀ ∪ hk1) B)) m₁₂ =
          upd (upd (ownOf G₃ m₁₁) 0 (h₁₀ ∪ hk1)) 1 Heap.empty := by
        funext u
        unfold ownOf
        rw [hjb₁₂]
        by_cases h0 : u = 0
        · subst h0; simp [joinedB, upd, Gh.heap]
        · by_cases h1 : u = 1
          · subst h1; simp [upd]
          · simp [upd, h0, h1]
      rw [e, ← e0, ← e1]; rw [e0, e1]; exact ho₁₂
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu; exact hi₁₁.kids u _ _ _ _ hu
    · refine ⟨by rw [hth₁₂, Array.size_setIfInBounds, hsz₁₁], ⟨tls1, ?_⟩, ?_,
        ⟨hk1, true, .inr rfl, by rw [upd_ne _ _ (by decide)]; exact hf1⟩, ?_, fun u hu => ?_⟩
      · rw [hth₁₂, Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz₁₁]; decide)]
      · obtain ⟨tls2, hr2⟩ := r2₁₁
        exact ⟨tls2, by rw [hth₁₂, Array.getElem?_setIfInBounds_ne (by decide)]; exact hr2⟩
      · obtain ⟨h'', d'', hd'', hk⟩ := k2₁₁
        exact ⟨h'', d'', hd'', by rw [upd_ne _ _ (by decide)]; exact hk⟩
      · rw [upd_ne _ _ (by unfold ThreadId at *; omega), hn₁₁ u hu]
    · rw [hth₁₂, Array.getElem?_setIfInBounds_ne (by decide)]; exact hi₁₁.t0
  -- The join of kid 2: `main` gets `b` back, with 9.
  refine WP.bind (WP.joinC fun k _ => ⟨Gh.main .j2 (h₁₀ ∪ hk1) B, hi₁₂, fun G₄ m₁₃ hg₄ hi₁₃ => ?_⟩)
  obtain ⟨ph, hm, B', h0, -, hma₁₃, hsh⟩ := hi₁₃.main
  rw [hg₄] at h0; cases h0
  obtain ⟨hsz₁₃, r1₁₃, r2₁₃, k1₁₃, k2₁₃, hn₁₃⟩ := hsh
  obtain ⟨tls2, hr2⟩ := r2₁₃
  refine ⟨fun _ => ⟨by decide, by rw [hsz₁₃]; decide, ⟨_, B, .inr rfl⟩, by
    simp [Thread.joinValid, hr2]⟩,
    fun hfin => ⟨fun _ => join_run hr2 rfl rfl, fun m₁₄ hj₂ => ?_⟩⟩
  obtain ⟨hk2, c'', ac'', hf2⟩ := hfin
  obtain ⟨h'', d'', -, hk2'⟩ := k2₁₃
  simp only [show (2 : Nat) ≠ 1 by decide, ↓reduceIte] at hk2'
  rw [hf2] at hk2'; cases hk2'
  obtain ⟨-, hka2⟩ := sep_lift.mp (hi₁₃.kids 2 _ _ _ _ hf2)
  simp only [↓reduceIte] at hka2
  obtain ⟨hc₁₄, hth₁₄⟩ := join_threads hr2 hj₂
  have ho₁₄ := Owned.join (hi₁₃.own.current 0) (by rw [hsz₁₃]; decide) (by decide) hj₂
  have e0 : ownOf G₄ m₁₃ 0 = h₁₀ ∪ hk1 := by simp [ownOf, joinedB, hg₄, Gh.heap]
  have e2 : ownOf G₄ m₁₃ 2 = hk2 := by simp [ownOf, joinedB, hr2, hf2, Gh.heap]
  have hd12 : Heap.Disjoint (h₁₀ ∪ hk1) hk2 := by
    have := hi₁₃.own.disj 0 2 (by decide); rwa [e0, e2] at this
  rw [e0, e2, upd_comm _ _ _ (show (0 : Nat) ≠ 2 by decide)] at ho₁₄
  have hA : ((cnt 8 ∗ u32At s0 Aa .stack 9) ∗ u32At s2 Ab .stack 9) ((h₁₀ ∪ hk1) ∪ hk2) :=
    ⟨_, hk2, hd12, rfl, hma₁₃, by simpa [B] using hka2⟩
  have hja : joinedAll 0 m₁₄ := by
    intro r hr _
    rw [hth₁₄] at hr
    obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hr
    have hi' : i < 3 := by simpa [hsz₁₃] using hi
    have hget : (m₁₃.threads.setIfInBounds 2 { (⟨0, false, tls2⟩ : ThreadRec) with joined := true })[i]? = some r := by
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
  refine WP.bind (WP.liftM_upd ((TTriple.loadAt (p := s0) (A := Aa) (S := 4) (K := .stack) (k := 0)
    (a := 4) (v := (9 : BitVec 32))
    (by simp [Ptr.add]) (by decide) (by rw [enc_u32]; decide) (by simp [ha0, hAa]) (decode_u32 9)).frameL_eq.frame_eq)
    ho₁₄ hc₁₄ htl hA fun r₁ m₁₅ h₁₅ ho₁₅ hq₁₅ hc₁₅ ht₁₅ => ?_)
  obtain ⟨rfl, F₁₅⟩ := sep_lift.mp hq₁₅
  refine WP.bind (WP.callRC_ok (v := (90000 : BitVec 32)) mul9a ?_)
  refine WP.bind (WP.liftM_upd ((TTriple.loadAt (p := s2) (A := Ab) (S := 4) (K := .stack) (k := 0)
    (a := 4) (v := (9 : BitVec 32))
    (by simp [Ptr.add]) (by decide) (by rw [enc_u32]; decide) (by simp [hb0, hAb]) (decode_u32 9)).frameL_eq)
    ho₁₅ hc₁₅ (by rw [ht₁₅]; exact htl) F₁₅ fun r₂ m₁₆ h₁₆ ho₁₆ hq₁₆ hc₁₆ ht₁₆ => ?_)
  obtain ⟨rfl, F₁₆⟩ := sep_lift.mp hq₁₆
  refine WP.bind (WP.callRC_ok (v := (900 : BitVec 32)) mul9b ?_)
  refine WP.bind (WP.callRC_ok (v := (90900 : BitVec 32)) add9 ?_)
  refine WP.bind (WP.liftM_tlsPtr (main_inst hc₁₆ (by rw [ht₁₆, ht₁₅]; exact hth₁₄₀)) ?_)
  refine WP.bind (WP.liftM_upd ((TTriple.loadAt (p := ⟨some 0, 0⟩) (A := 4096) (S := 4)
    (K := .global) (k := 0) (a := 4) (v := (8 : BitVec 32))
    (by simp [Ptr.add]) (by decide) (by rw [enc_u32]; decide) (by decide) (decode_u32 8)).frame_eq.frame_eq)
    ho₁₆ hc₁₆ (by rw [ht₁₆, ht₁₅]; exact htl) F₁₆ fun r₃ m₁₇ h₁₇ ho₁₇ hq₁₇ hc₁₇ ht₁₇ => ?_)
  obtain ⟨rfl, F₁₇⟩ := sep_lift.mp hq₁₇
  refine WP.bind (WP.callRC_ok (v := (90908 : BitVec 32)) add8 ?_)
  refine WP.pure' ?_
  -- The frees.
  have htl₁₇ : 0 < m₁₇.threads.size := by rw [ht₁₇, ht₁₆, ht₁₅]; exact htl
  have F' := sep_left_comm (sep_assoc F₁₇)
  refine WP.bind (WP.liftMem_upd (free_front (R := cnt 8 ∗ u32At s2 Ab .stack 9) (enc_u32 9) ha0
    (by decide)) ho₁₇ hc₁₇ htl₁₇ F' fun _ m₁₈ h₁₈ ho₁₈ hq₁₈ hc₁₈ ht₁₈ => ?_)
  refine WP.bind (WP.liftMem_upd ((free_front (R := cnt 8) (enc_u32 9) hb0 (by decide)).conseq
    (fun _ h => sep_comm h) fun _ _ h => h) ho₁₈ hc₁₈ (by rw [ht₁₈]; exact htl₁₇) hq₁₈
    fun _ m₁₉ _ _ _ _ ht₁₉ => ?_)
  refine WP.pure' ⟨rfl, fun r hr hs => hja r ?_ hs⟩
  rwa [ht₁₉, ht₁₈, ht₁₇, ht₁₆, ht₁₅] at hr

/-! ## The results -/

/-- **`twoCounters` returns 90908 under every schedule**: each worker read 9 from its own
`counter` and `main` read 8 from its own. -/
theorem twoCounters_spec {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run dispatch fuel o twoCounters (mem0 .fresh)).run = some (.ok (v, m))) :
    v = .ok 90908 := by
  obtain ⟨_, _, hv, -⟩ := proto.run_sound dispatch (fun _ => .none) dispatch_spec
    (fun _ _ _ _ _ hq => hq.2) mem0_size main_spec h
  exact hv

/-- **No run of `twoCounters` gives an error**: the concurrent increments of the three
instances do not race. -/
theorem twoCounters_safe {fuel : Nat} {o : Nat → Nat} {e : Error} :
    (Sched.run dispatch fuel o twoCounters (mem0 .fresh)).run ≠ some (.error e) :=
  proto.run_safe dispatch (fun _ => .none) rfl dispatch_spec (fun _ _ _ _ hq => hq.2) mem0_size
    main_spec

end ThreadLocals.Counters
