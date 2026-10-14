import ZigLean.Sep.Full.LockWord
import ZigLean.Sep.Full.ThreadRest
import ZigLean.Sep.Full.Atomic

/-!
# A lock that owns a resource, over full-state resources

A lock (`Io.Mutex` of Zig 0.16.0, `Thread.Mutex` of 0.15.2, translated from their std code; the
futex under it is the model) protects a resource: a full-state resource (`Res`: bytes with their
tag constraints, knowledge, ghost state) that the lock owns while it is free. `lock` moves the
resource into the part of the thread that takes the lock (`FOwned.take`), `unlock` moves it back
into the protocol's rest (`FOwned.give`). This file is the part of a protocol
(`ZigLean/Conc/Logic.lean`) for one lock, proved once for every protocol that has it; the word's
own reasoning is `ZigLean/Sep/Full/LockWord.lean`, the lock's code
`ZigLean/Sep/Full/LockRules.lean` (`docs/sep-threads.md` §Locks).

- **The lock** (`FLock`): a word (`LockWord`) and the resource `R : (ThreadId → γ) → FAssn`. The
  protocol's ghost value tells for each thread where it is in the lock's code (`ph`), its part
  (`part : γ → Res`) and the resource while it holds the lock (`held`). A thread owns
  `rsum part held` (`FLock.own`; a joined thread owns nothing).
- **The invariant** (`FLock.Inv G rX m`): the word's invariant at the threads' places
  (`LockWord.WInv`); the threads' parts and the rest (`FOwned`), where the rest is the word's cells
  (`wordR`), the free lock's resource `rL` (with `R`, and each access to it happened before every
  thread that has not ended or before the newest release of the word: `LockWord.Owns`; `rnil`
  while a thread holds the lock) and the protocol's own rest `rX` (other sync objects, read-shared
  buffers); the holder's resource has `R`.
- **A protocol with the lock** (`FLock.Fits`): its invariant is `∃ rX, Inv G rX m ∧ U G rX m`; a step
  of the lock's code (`LockWord.Step`) keeps `U` with the same `rX`.
- **Steps outside the lock's code**: a thread's step on its own part (`Inv.wp_liftMem`, with a
  thread triple `FTTriple`), a change of a ghost value (`Inv.ghost`), a spawn (`Inv.fork`), a join
  (`Inv.join`). The steps of the lock's code change the invariant through `Inv.lstep`,
  `Inv.acq` (acquire) and `Inv.rel` (release).
-/

namespace Zig
namespace Full

open FAssn Conc Proto

theorem rsum_rnil (r : Res) : rsum r rnil = r := by
  simp [rsum, Know.union_none]

namespace LockWord

variable {L : LockWord}

/-- The word's cells, as a resource of the protocol's rest. -/
abbrev wordR (L : LockWord) (m : Mem) : Res := cellsAt L.In m

theorem wordR_some {m : Mem} (hb : L.BlkOk m) {l : Zig.Loc} (hl : L.In l) :
    (L.wordR m).heap l ≠ none := by
  obtain ⟨b, x⟩ := l
  obtain ⟨h1, h2, h3⟩ := hl
  simp only at h1 h2 h3; subst h1
  exact cellsAt_some ⟨rfl, h2, h3⟩ (hb.cell h2 h3)

/-- A heap with no byte of the word, as an erased full heap. -/
theorem off_erase {h : FHeap} : L.Off h.erase ↔ ∀ l, L.In l → h l = none := by
  constructor
  · rintro hh ⟨b, x⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3; subst h1
    have := hh x h2 h3; simpa [FHeap.erase] using this
  · intro hh x h1 h2; simp [FHeap.erase, hh (L.b, x) ⟨rfl, h1, h2⟩]

/-- The word's block after a lock step. -/
theorem BlkOk.step {t : ThreadId} {m m' : Mem} (hs : L.Step t m m') (hb : L.BlkOk m) : L.BlkOk m' := by
  obtain ⟨blk, hblk, hl, hsz, ha, hk, hlo⟩ := hb
  rcases hs.blocks with e | ⟨blk', bs, h1, -, h3, h4, h5⟩
  · exact ⟨blk, by rw [e]; exact hblk, hl, hsz, ha, hk, hlo⟩
  · rw [hblk] at h1; cases h1
    refine ⟨{ blk with bytes := writeBytes blk.bytes L.o bs }, ?_, hl, ?_, ha, hk, hlo⟩
    · rw [h5]; simp only [Mem.write]
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
        (Array.getElem?_eq_some_iff.mp hblk).1]
    · show L.o + 4 ≤ (writeBytes blk.bytes L.o bs).size
      rw [writeBytes_size _ _ _ (by omega)]; exact hsz

/-- **A lock step is a step at the word's bytes** (`RestStep`). -/
theorem Step.rest {t : ThreadId} {m m' : Mem} (hs : L.Step t m m') (hb : L.BlkOk m) :
    RestStep L.In m m' := by
  have hb' := hb.step hs
  obtain ⟨blk, hblk, hl, hsz, ha, hk, hlo⟩ := hb
  have hbl : L.b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
  have hmeta : KMono m m' ∧ KeepsExt m m' ∧ (m.LiveLayout → m'.LiveLayout) := by
    rcases hs.blocks with e | ⟨blk', bs, h1, -, h3, h4, h5⟩
    · refine ⟨KMono.of_blocks e, KeepsExt.of_blocks e, fun h => ?_⟩
      obtain ⟨hd, hbd⟩ := h
      exact ⟨fun b b' x x' hne h1 h2 => hd b b' x x' hne (e ▸ h1) (e ▸ h2),
        fun b x h1 => hbd b x (e ▸ h1)⟩
    · rw [hblk] at h1; cases h1
      have hw : m'.blocks = m.blocks.set! L.b { blk with bytes := writeBytes blk.bytes L.o bs } := by
        rw [h5]; rfl
      obtain ⟨k1, k2⟩ := kmono_write hblk hw (by omega) hk
      exact ⟨k1, k2, ld_write hblk (by omega) hw⟩
  refine ⟨hs.threads, hs.csize, hs.clocks, hs.bsize, fun l hl => hs.heap hl, fun l hl => ?_,
    hmeta.1, hmeta.2.1, hmeta.2.2, fun b x hx => ?_, fun hw => ?_, fun e he => ?_, hs.cov⟩
  · obtain ⟨b, x⟩ := l
    obtain ⟨h1, h2, h3⟩ := hl
    simp only at h1 h2 h3; subst h1
    exact hb'.cell h2 h3
  · have hc : ¬ Covers b x L.shape := fun ⟨h1, h2, h3⟩ => hx ⟨h1.symm, h2, h3⟩
    rcases hs.shapes with e | ⟨e, -⟩
    · rw [e]
    · rw [e, tagOf_append_single, if_neg hc]; simp
  · rcases hs.shapes with e | ⟨e, hap⟩
    · rw [e]; exact hw
    · rw [e]
      refine ⟨fun s hs' => ?_, List.pairwise_append.mpr ⟨hw.2, by simp, fun a ha b hb => ?_⟩⟩
      · rcases List.mem_append.mp hs' with h | h
        · exact hw.1 s h
        · simp at h; subst h; simp [LockWord.shape]
      · simp at hb; subst hb; exact hap a ha
  · rcases hs.fp e he with h | ⟨h1, h2, h3, -, -⟩
    · exact .inl h
    · refine .inr ⟨fun x hx1 hx2 => ⟨h1, by omega, by omega⟩, by rw [h1]; exact hbl⟩

end LockWord

/-- A thread's place in the code of a sync primitive, a part of the protocol's ghost value `γ`:
`set g p` is `g` at the place `p` (the event's and the condition's places extend it). -/
structure FPlace (γ Ph : Type) where
  ph : γ → Ph
  set : γ → Ph → γ
  ph_set : ∀ g p, ph (set g p) = p
  set_set : ∀ g p q, set (set g p) q = set g q
  set_self : ∀ g, set g (ph g) = g

/-- **A sync primitive next to the protocol's lock** (module doc): the data a protocol keeps for it
(`FLock.Fits`). The primitive's library builds it (`FPrim.empty` for the lock alone,
`FPrim.ofWords` for a primitive over futex words). -/
structure FPrim (γ : Type) where
  /-- Where a thread is in the primitive's code. -/
  Ph : Type
  pl : FPlace γ Ph
  /-- The place of a thread out of the primitive's code (a finished or joinable thread is there). -/
  out : Ph
  /-- The places at which a thread may run the lock's code: the protocol's `ok` does not tell
  them apart. -/
  calm : Ph → Prop
  /-- The threads' roles (which threads may wait, signal, set). -/
  Role : Type
  role : Role → γ → Prop
  /-- What the protocol's rest `rX` keeps for the primitive: its invariant, its cells. -/
  Sub : (ThreadId → γ) → Res → Mem → Prop
  /-- The primitive's memory is apart from the lock's word. -/
  Apart : Prop
  /-- A step of thread `t` in the primitive's code, from the ghost values, the rest and the memory
  before it to those after it. -/
  Step : ThreadId → (ThreadId → γ) → Res → Mem → (ThreadId → γ) → Res → Mem → Prop

/-- No primitive next to the lock (a protocol with the lock alone). -/
def FPrim.empty (γ : Type) : FPrim γ where
  Ph := Unit
  pl := { ph := fun _ => (), set := fun g _ => g, ph_set := fun _ _ => rfl,
          set_set := fun _ _ _ => rfl, set_self := fun _ => rfl }
  out := ()
  calm _ := True
  Role := Empty
  role i := nomatch i
  Sub _ _ _ := True
  Apart := True
  Step _ _ _ _ _ _ _ := False

/-- A lock (module doc). -/
structure FLock (γ : Type) extends LockWord where
  /-- The resource, with the ghost values of all threads. -/
  R : (ThreadId → γ) → FAssn
  /-- Where the thread is in the lock's code. -/
  ph : γ → LPh
  /-- The thread's part, without the resource. -/
  part : γ → Res
  /-- The resource, while the thread holds the lock. -/
  held : γ → Res
  /-- `g` with the place `p` and the resource `h`. -/
  set : γ → LPh → Res → γ
  ph_set : ∀ g p h, ph (set g p h) = p
  part_set : ∀ g p h, part (set g p h) = part g
  held_set : ∀ g p h, held (set g p h) = h
  set_self : ∀ g, set g (ph g) (held g) = g
  set_set : ∀ g p h p' h', set (set g p h) p' h' = set g p' h'
  /-- The resource does not read where a thread is in the lock's code. -/
  R_set : ∀ G t p h r, R (upd G t (set (G t) p h)) r ↔ R G r
  /-- `g` with the part `r` (a step of the thread on its own part, e.g. a stack block of a sync
  object's code: `Inv.wp_liftPart`). -/
  setPart : γ → Res → γ
  ph_setPart : ∀ g r, ph (setPart g r) = ph g
  part_setPart : ∀ g r, part (setPart g r) = r
  held_setPart : ∀ g r, held (setPart g r) = held g
  setPart_self : ∀ g, setPart g (part g) = g
  setPart_setPart : ∀ g r r', setPart (setPart g r) r' = setPart g r'
  setPart_set : ∀ g p h r, setPart (set g p h) r = set (setPart g r) p h
  /-- The resource does not read the threads' parts. -/
  R_setPart : ∀ G t r r', R (upd G t (setPart (G t) r)) r' ↔ R G r'

/-- A thread's ghost value for a lock: its place, its part, the resource it holds. -/
structure FLG where
  ph : LPh := .gone
  part : Res := rnil
  held : Res := rnil

/-- A lock whose ghost value is `FLG × X`: `X` is the rest of the protocol's ghost value. The
resource reads only `X`. -/
def FLock.prod {X : Type} (b o : Nat) (R : (ThreadId → X) → FAssn) (c : Nat := 2)
    (c_ok : c = 1 ∨ c = 2 ∨ c = 3 := by decide) : FLock (FLG × X) where
  b := b
  o := o
  c := c
  c_ok := c_ok
  R G := R fun u => (G u).2
  ph g := g.1.ph
  part g := g.1.part
  held g := g.1.held
  set g p h := ({ g.1 with ph := p, held := h }, g.2)
  ph_set _ _ _ := rfl
  part_set _ _ _ := rfl
  held_set _ _ _ := rfl
  set_self _ := rfl
  set_set _ _ _ _ _ := rfl
  R_set G t p h r := by
    have : (fun u => (upd G t ({ (G t).1 with ph := p, held := h }, (G t).2) u).2) =
        fun u => (G u).2 := by
      funext u; unfold upd; split
      · rename_i e; subst e; rfl
      · rfl
    simp only [this]
  setPart g r := ({ g.1 with part := r }, g.2)
  ph_setPart _ _ := rfl
  part_setPart _ _ := rfl
  held_setPart _ _ := rfl
  setPart_self _ := rfl
  setPart_setPart _ _ _ := rfl
  setPart_set _ _ _ _ := rfl
  R_setPart G t r r' := by
    have : (fun u => (upd G t ({ (G t).1 with part := r }, (G t).2) u).2) =
        fun u => (G u).2 := by
      funext u; unfold upd; split
      · rename_i e; subst e; rfl
      · rfl
    simp only [this]

namespace FLock

/-- The ghost values `X` of a product: `upd` of `G` is `upd` of `X`. -/
theorem snd_upd {X : Type} (G : ThreadId → FLG × X) (t : ThreadId) (g : FLG × X) :
    (fun u => (upd G t g u).2) = upd (fun u => (G u).2) t g.2 := by
  funext u; unfold upd; split <;> rfl

/-- A step of a thread in the lock's code keeps the ghost values `X`. -/
theorem snd_set {X : Type} {b o c : Nat} {R : (ThreadId → X) → FAssn} {hc : c = 1 ∨ c = 2 ∨ c = 3}
    (G : ThreadId → FLG × X) (t : ThreadId) (p : LPh) (h : Res) :
    (fun u => (upd G t ((FLock.prod b o R c hc).set (G t) p h) u).2) = fun u => (G u).2 := by
  rw [snd_upd]; funext u; unfold upd; split
  · rename_i e; subst e; rfl
  · rfl

variable {γ : Type} (L : FLock γ)

/-- The threads' places. -/
def pl (G : ThreadId → γ) : ThreadId → LPh := fun u => L.ph (G u)

/-- Thread `u`'s part, with the resource while it holds the lock; a joined thread owns nothing. -/
def own (G : ThreadId → γ) (m : Mem) (u : ThreadId) : Res :=
  if joinedB m u then rnil else rsum (L.part (G u)) (L.held (G u))

/-- No thread holds the lock. -/
def Free (G : ThreadId → γ) : Prop := LockWord.Free (L.pl G)

/-- The invariant of the lock with the protocol's own rest `rX` (module doc). -/
structure Inv (G : ThreadId → γ) (rX : Res) (m : Mem) : Prop where
  w : L.WInv (L.pl G) m
  rest : ∃ rL, FOwned (L.own G m) (rsum (L.wordR m) (rsum rL rX)) m ∧
    L.Off rL.heap.erase ∧ FHeap.Disjoint rL.heap rX.heap ∧
    (L.Free G → L.R G rL ∧ L.toLockWord.Owns (L.pl G) m rL.heap.erase) ∧ (¬ L.Free G → rL = rnil)
  xoff : L.Off rX.heap.erase
  pdisj : ∀ u, FHeap.Disjoint (L.part (G u)).heap (L.held (G u)).heap
  idle : ∀ u, L.ph (G u) ≠ .holds → L.held (G u) = rnil
  /-- The holder's resource. -/
  res : ∀ u, L.ph (G u) = .holds → L.R G (L.held (G u))

/-- **A protocol with the lock `L` keeps the primitive `K`** (module doc), where only a thread with
`ok` runs the lock's code: its invariant is `FLock.Inv` and `U`, with the same rest `rX`; `U` keeps
what the primitive needs (`FPrim.Sub`) and is stable under the steps of the lock's and the
primitive's code. A protocol with the lock alone has `K = FPrim.empty` (`Fits.ofLock`, and
`Fits.ofLockAll` for `ok = True`). -/
structure Fits (K : FPrim γ) {Tgt : Type} (P : Proto Tgt γ)
    (U : (ThreadId → γ) → Res → Mem → Prop) (ok : γ → Prop) : Prop where
  inv : ∀ G m, P.inv G m ↔ ∃ rX, L.Inv G rX m ∧ U G rX m
  fin : ∀ g, P.fin g → L.ph g = .gone
  joins : ∀ g, P.joins g → L.ph g = .out
  ok_set : ∀ g p h, ok (L.set g p h) ↔ ok g
  ok_setPart : ∀ g r, ok (L.setPart g r) ↔ ok g
  /-- A step of a thread in the lock's code keeps `U`; at a release, the thread's clock happened
  before the newest message of the word. -/
  stable : ∀ G rX m m' t p h, ok (G t) → L.ph (G t) ≠ .gone → U G rX m → L.Step t m m' →
    (L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!)) →
    U (upd G t (L.set (G t) p h)) rX m'
  /-- A stop of any thread (`current := t`) keeps `U`: a thread without `ok` (one inside another
  sync object's code, which runs no lock code) stops too. -/
  atStop : ∀ G rX m t, L.ph (G t) ≠ .gone → U G rX m → U G rX { m with current := t }
  /-- A finished or joinable thread is out of the primitive's code. -/
  kfin : ∀ g, P.fin g → K.pl.ph g = K.out
  kjoins : ∀ g, P.joins g → K.pl.ph g = K.out
  /-- The rest keeps the primitive. -/
  sub : ∀ G rX m, U G rX m → K.Sub G rX m
  apart : K.Apart
  /-- The primitive's place and the lock's are independent parts of a ghost value. -/
  lph : ∀ g p, L.ph (K.pl.set g p) = L.ph g
  lpart : ∀ g p, L.part (K.pl.set g p) = L.part g
  lheld : ∀ g p, L.held (K.pl.set g p) = L.held g
  lR : ∀ G t p r, L.R G r → L.R (upd G t (K.pl.set (G t) p)) r
  ph_l : ∀ g q h, K.pl.ph (L.set g q h) = K.pl.ph g
  set_l : ∀ g p q h, K.pl.set (L.set g q h) p = L.set (K.pl.set g p) q h
  ph_part : ∀ g r, K.pl.ph (L.setPart g r) = K.pl.ph g
  set_part : ∀ g p r, K.pl.set (L.setPart g r) p = L.setPart (K.pl.set g p) r
  role_l : ∀ i g q h, K.role i (L.set g q h) ↔ K.role i g
  role_part : ∀ i g r, K.role i (L.setPart g r) ↔ K.role i g
  /-- `ok` does not read the primitive's place among the calm ones. -/
  ok_calm : ∀ g p q, K.calm p → K.calm q → (ok (K.pl.set g p) ↔ ok (K.pl.set g q))
  /-- A step of the primitive's code keeps `U`. -/
  kstep : ∀ t G rX m G' rX' m', K.Step t G rX m G' rX' m' → U G rX m → U G' rX' m'

variable {L}

/-- The same ghost value for `t` (`set_self`). -/
theorem upd_set_self (G : ThreadId → γ) (t : ThreadId) :
    upd G t (L.set (G t) (L.ph (G t)) (L.held (G t))) = G := by
  rw [L.set_self]; funext u; unfold upd; split <;> simp_all

/-- **A protocol with the lock alone**, where only a thread with `ok` runs the lock's code. -/
theorem Fits.ofLock {Tgt : Type} {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop}
    {ok : γ → Prop} (inv : ∀ G m, P.inv G m ↔ ∃ rX, L.Inv G rX m ∧ U G rX m)
    (fin : ∀ g, P.fin g → L.ph g = .gone) (joins : ∀ g, P.joins g → L.ph g = .out)
    (ok_set : ∀ g p h, ok (L.set g p h) ↔ ok g) (ok_setPart : ∀ g r, ok (L.setPart g r) ↔ ok g)
    (stable : ∀ G rX m m' t p h, ok (G t) → L.ph (G t) ≠ .gone → U G rX m → L.Step t m m' →
      (L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!)) →
      U (upd G t (L.set (G t) p h)) rX m')
    (atStop : ∀ G rX m t, L.ph (G t) ≠ .gone → U G rX m → U G rX { m with current := t }) :
    L.Fits (FPrim.empty γ) P U ok where
  inv := inv
  fin := fin
  joins := joins
  ok_set := ok_set
  ok_setPart := ok_setPart
  stable := stable
  atStop := atStop
  kfin _ _ := rfl
  kjoins _ _ := rfl
  sub _ _ _ _ := trivial
  apart := trivial
  lph _ _ := rfl
  lpart _ _ := rfl
  lheld _ _ := rfl
  lR G t _ r h := by show L.R (upd G t (G t)) r; rwa [upd_same]
  ph_l _ _ _ := rfl
  set_l _ _ _ _ := rfl
  ph_part _ _ := rfl
  set_part _ _ _ := rfl
  role_l i := nomatch i
  role_part i := nomatch i
  ok_calm _ _ _ _ _ := Iff.rfl
  kstep _ _ _ _ _ _ _ h := nomatch h

/-- **A protocol with the lock alone**, where every thread may run the lock's code: a stop keeps
`U` as a step of the lock's code that changes nothing. -/
theorem Fits.ofLockAll {Tgt : Type} {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop}
    (inv : ∀ G m, P.inv G m ↔ ∃ rX, L.Inv G rX m ∧ U G rX m)
    (fin : ∀ g, P.fin g → L.ph g = .gone) (joins : ∀ g, P.joins g → L.ph g = .out)
    (stable : ∀ G rX m m' t p h, L.ph (G t) ≠ .gone → U G rX m → L.Step t m m' →
      (L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!)) →
      U (upd G t (L.set (G t) p h)) rX m') :
    L.Fits (FPrim.empty γ) P U fun _ => True :=
  .ofLock inv fin joins (fun _ _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    (fun G rX m m' t p h _ => stable G rX m m' t p h) fun G rX m t hph hU => by
      have := stable G rX m { m with current := t } t (L.ph (G t)) (L.held (G t)) hph hU
        (LockWord.Step.same rfl rfl rfl rfl rfl rfl (fun _ _ => Iff.rfl)) (fun h1 h2 => absurd h1 h2)
      rwa [upd_set_self] at this

/-! ## Basic facts -/

theorem pl_upd (G : ThreadId → γ) (t : ThreadId) (g : γ) :
    L.pl (upd G t g) = upd (L.pl G) t (L.ph g) := by
  funext u; unfold pl upd; split <;> rfl

theorem pl_upd_set (G : ThreadId → γ) (t : ThreadId) (p : LPh) (h : Res) :
    L.pl (upd G t (L.set (G t) p h)) = upd (L.pl G) t p := by
  rw [pl_upd, L.ph_set]

/-- A thread that was not joined owns its part and its resource. -/
theorem own_live {G : ThreadId → γ} {m : Mem} {t : ThreadId} (hj : joinedB m t = false) :
    L.own G m t = rsum (L.part (G t)) (L.held (G t)) := by
  unfold FLock.own; rw [hj]; rfl

theorem own_upd {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {g : γ}
    (hj : joinedB m' = joinedB m) (hjt : joinedB m t = false) :
    L.own (upd G t g) m' = upd (L.own G m) t (rsum (L.part g) (L.held g)) := by
  funext u
  unfold FLock.own; rw [hj]
  by_cases hu : u = t
  · subst hu; simp [hjt, upd]
  · simp only [upd, hu, ↓reduceIte]

theorem free_iff_of {G G' : ThreadId → γ} (h : ∀ u, L.ph (G' u) = .holds ↔ L.ph (G u) = .holds) :
    L.Free G' ↔ L.Free G := by
  unfold FLock.Free LockWord.Free pl; exact forall_congr' fun u => not_congr (h u)

theorem Inv.ht {G : ThreadId → γ} {rX : Res} {m : Mem} (hi : L.Inv G rX m) {t : ThreadId}
    (hg : L.ph (G t) ≠ .gone) : t < m.threads.size ∧ joinedB m t = false :=
  hi.w.live t hg

/-- No part, no free resource and not the protocol's rest has a byte of the word. -/
theorem Inv.wordFree {G : ThreadId → γ} {rY : Res} {m : Mem}
    (ho : FOwned (L.own G m) (rsum (L.wordR m) rY) m) (hb : L.BlkOk m)
    {u : ThreadId} (hu : u < m.threads.size) : L.Off (L.own G m u).heap.erase :=
  LockWord.off_erase.mpr fun l hl => ho.part_off hu (by
    simp only [FHeap.union_apply]
    cases e : (L.wordR m).heap l with
    | none => exact absurd e (LockWord.wordR_some hb hl)
    | some c => simp)

/-! ## Steps of the lock's code -/

/-- The rest's word cells and the other resources, after a lock step: the same resources. -/
theorem rest_step {rX rL : Res} {m m' : Mem} {t : ThreadId}
    {own : ThreadId → Res}
    (ho : FOwned own (rsum (L.wordR m) (rsum rL rX)) m) (hs : L.Step t m m') (hb : L.BlkOk m)
    (hLoff : L.Off rL.heap.erase) (hxoff : L.Off rX.heap.erase) :
    FOwned own (rsum (L.wordR m') (rsum rL rX)) m' :=
  ho.restStep (hs.rest hb) (fun l hl => by
      obtain ⟨b, x⟩ := l; obtain ⟨h1, h2, h3⟩ := hl; simp only at h1 h2 h3; subst h1
      exact hb.cell h2 h3)
    (fun l hl => by
      simp only [FHeap.union_apply, LockWord.off_erase.mp hLoff l hl, LockWord.off_erase.mp hxoff l hl]
      rfl)

/-- **A step of the lock's code that moves no resource**: the parts stay, the free lock's
resource stays, and the places change as the word's invariant says. -/
theorem Inv.lstep {G G' : ThreadId → γ} {rX : Res} {m m' : Mem} {t : ThreadId}
    (hi : L.Inv G rX m) (hs : L.Step t m m') (hw : L.WInv (L.pl G') m')
    (hown : L.own G' m' = L.own G m) (hfree : L.Free G' ↔ L.Free G)
    (hg : ∀ u, L.ph (G' u) ≠ .gone → L.ph (G u) ≠ .gone)
    (hR : ∀ r, L.R G r → L.R G' r)
    (hpd : ∀ u, FHeap.Disjoint (L.part (G' u)).heap (L.held (G' u)).heap)
    (hidle : ∀ u, L.ph (G' u) ≠ .holds → L.held (G' u) = rnil)
    (hres : ∀ u, L.ph (G' u) = .holds → L.R G' (L.held (G' u))) : L.Inv G' rX m' := by
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  have hbl : L.b < m.blocks.size := by
    obtain ⟨blk, hb, -⟩ := hi.w.blk; exact (Array.getElem?_eq_some_iff.mp hb).1
  refine ⟨hw, ⟨rL, hown ▸ rest_step ho hs hi.w.blk hLoff hi.xoff, hLoff, hLX, fun hF' => ?_,
    fun hnF' => hnF (fun h => hnF' (hfree.mpr h))⟩, hi.xoff, hpd, hidle, hres⟩
  obtain ⟨h1, h2⟩ := hF (hfree.mp hF')
  exact ⟨hR rL h1, h2.step hs hLoff hbl hg⟩

/-- A step of the lock's code by `t`, not the holder, to the place `p ≠ holds`. -/
theorem Inv.lstepAt {G : ThreadId → γ} {rX : Res} {m m' : Mem} {t : ThreadId} {p : LPh}
    (hi : L.Inv G rX m) (hs : L.Step t m m') (hnh : L.ph (G t) ≠ .holds) (hng : L.ph (G t) ≠ .gone)
    (hp : p ≠ .holds) (hw : L.WInv (upd (L.pl G) t p) m') :
    L.Inv (upd G t (L.set (G t) p rnil)) rX m' := by
  obtain ⟨-, hjt⟩ := hi.ht hng
  have hjb : joinedB m' = joinedB m := LockWord.joinedB_congr hs.threads
  have hheld : L.held (G t) = rnil := hi.idle t hnh
  have hphu : ∀ u, L.ph (upd G t (L.set (G t) p rnil) u) = if u = t then p else L.ph (G u) := by
    intro u; unfold upd; split
    · exact L.ph_set _ _ _
    · rfl
  have hholds : ∀ u, L.ph (upd G t (L.set (G t) p rnil) u) = .holds ↔ L.ph (G u) = .holds := by
    intro u; rw [hphu]; split
    · rename_i h; subst h; exact ⟨fun h => absurd h hp, fun h => absurd h hnh⟩
    · exact Iff.rfl
  refine hi.lstep hs (by rw [pl_upd_set]; exact hw) ?_ (free_iff_of hholds) (fun u h => ?_)
    (fun r h => (L.R_set G t p rnil r).mpr h) (fun u => ?_) (fun u hu => ?_) (fun u hu => ?_)
  · rw [own_upd hjb hjt, L.part_set, L.held_set]
    funext u; unfold upd; split
    · rename_i h; subst h; rw [own_live hjt, hheld]
    · rfl
  · rw [hphu] at h; split at h
    · rename_i e; subst e; exact hng
    · exact h
  · unfold upd; split
    · rw [L.held_set]; exact FHeap.disjoint_empty _
    · exact hi.pdisj u
  · unfold upd; split
    · exact L.held_set _ _ _
    · rename_i h; rw [hphu, if_neg h] at hu; exact hi.idle u hu
  · have hut : u ≠ t := fun e => by
      have := (hholds u).mp hu; rw [e] at this; exact hnh this
    rw [upd_ne _ _ hut, L.R_set]; exact hi.res u ((hholds u).mp hu)

/-- A step of the lock's code with the same ghost values. -/
theorem Inv.lstay {G : ThreadId → γ} {rX : Res} {m m' : Mem} {t : ThreadId}
    (hi : L.Inv G rX m) (hs : L.Step t m m') (hw : L.WInv (L.pl G) m') : L.Inv G rX m' :=
  hi.lstep hs hw (by funext u; unfold FLock.own; rw [LockWord.joinedB_congr hs.threads])
    Iff.rfl (fun _ h => h) (fun _ h => h) hi.pdisj hi.idle hi.res

/-- The same memory, but the groups' tasks (`Group.async`, `Group.await`). -/
theorem Inv.groups {G : ThreadId → γ} {rX : Res} {m : Mem} (hi : L.Inv G rX m)
    (gs : Array (Ptr × ThreadId)) : L.Inv G rX { m with groups := gs } := by
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  exact ⟨hi.w.groups gs, ⟨rL, ho.keep rfl rfl rfl rfl rfl, hLoff, hLX, hF, hnF⟩, hi.xoff, hi.pdisj,
    hi.idle, hi.res⟩

/-- **An acquire**: `t` takes the free lock; the resource moves from the rest into its part. -/
theorem Inv.acq {G : ThreadId → γ} {rX : Res} {m m' : Mem} {t : ThreadId}
    (hi : L.Inv G rX m) (hs : L.Step t m m') (hnh : L.ph (G t) ≠ .holds)
    (hng : L.ph (G t) ≠ .gone) (hF : L.Free G) (hacq : L.Acq (L.pl G) t m m')
    (hw : L.WInv (upd (L.pl G) t .holds) m') :
    ∃ rL, L.R G rL ∧ L.Inv (upd G t (L.set (G t) .holds rL)) rX m' := by
  obtain ⟨rL, ho, hLoff, hLX, hFr, -⟩ := hi.rest
  obtain ⟨hR, hLown⟩ := hFr hF
  obtain ⟨ht, hjt⟩ := hi.ht hng
  have hjb : joinedB m' = joinedB m := LockWord.joinedB_congr hs.threads
  have hheld : L.held (G t) = rnil := hi.idle t hnh
  have ho' := rest_step ho hs hi.w.blk hLoff hi.xoff
  have hb' := hi.w.blk.step hs
  -- the rest as `rL ⋆ (word ⋆ rX)`
  have hWL : FHeap.Disjoint (L.wordR m').heap rL.heap := fun l => by
    by_cases hl : L.In l
    · exact .inr (LockWord.off_erase.mp hLoff l hl)
    · exact .inl (cellsAt_none hl)
  have e1 : rsum (L.wordR m') (rsum rL rX) = rsum rL (rsum (L.wordR m') rX) := by
    rw [← rsum_assoc, rsum_comm hWL, rsum_assoc]
  rw [e1] at ho'
  have hdA : FHeap.Disjoint rL.heap (rsum (L.wordR m') rX).heap :=
    FHeap.disjoint_union_right.mpr ⟨hWL.symm, hLX⟩
  have ht' : t < m'.threads.size := by rw [hs.threads]; exact ht
  have hown : m'.Owns t rL.heap.erase := hacq _ hLown hLoff
  have ho2 := ho'.take ht' hdA hown
  have hpt : L.pl (upd G t (L.set (G t) .holds rL)) = upd (L.pl G) t .holds := pl_upd_set G t _ _
  have hphu : ∀ u, L.ph (upd G t (L.set (G t) .holds rL) u) = if u = t then .holds else L.ph (G u) := by
    intro u; unfold upd; split
    · exact L.ph_set _ _ _
    · rfl
  refine ⟨rL, hR, by rw [hpt]; exact hw, ⟨rnil, ?_, LockWord.off_erase.mpr fun _ _ => rfl,
    FHeap.Disjoint.symm (FHeap.disjoint_empty _), fun hF' =>
      absurd (show L.ph (upd G t (L.set (G t) .holds rL) t) = .holds by rw [hphu]; simp) (hF' t),
    fun _ => rfl⟩, hi.xoff, fun u => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rw [rnil_rsum, own_upd hjb hjt, L.part_set, L.held_set]
    have : rsum (L.own G m t) rL = rsum (L.part (G t)) rL := by
      rw [own_live hjt, hheld, rsum_rnil]
    rw [← this]; exact ho2
  · unfold upd; split
    · rename_i h; subst h; rw [L.part_set, L.held_set]
      have hd := ho2.disj (u := u) (v := u) ht' ht'
      -- the part and the taken resource are disjoint: both are in `t`'s new part
      obtain ⟨rR, -, -, hh⟩ := ho'.part ht'
      have := (FHeap.disjoint_union_right.mp hh.disj).2
      have h2 := (FHeap.disjoint_union_right.mp this).1
      rw [own_live hjt, hheld, rsum_rnil] at h2
      exact h2
    · exact hi.pdisj u
  · unfold upd; split
    · rename_i h; subst h; rw [hphu, if_pos rfl] at hu; exact absurd rfl hu
    · rename_i h; rw [hphu, if_neg h] at hu; exact hi.idle u hu
  · rw [hphu] at hu
    split at hu
    · rename_i h; subst h; rw [upd_self, L.held_set, L.R_set]; exact hR
    · exact absurd hu (hF u)

/-- **A release**: the holder `t` goes to `p`; its resource moves from its part into the rest. -/
theorem Inv.rel {G : ThreadId → γ} {rX : Res} {m m' : Mem} {t : ThreadId} {p : LPh}
    (hi : L.Inv G rX m) (hs : L.Step t m m') (hph : L.ph (G t) = .holds) (hp : p ≠ .holds)
    (hrel : L.Rel t (upd (L.pl G) t p) m m') (hw : L.WInv (upd (L.pl G) t p) m') :
    L.Inv (upd G t (L.set (G t) p rnil)) rX m' := by
  obtain ⟨rL, ho, -, -, -, hnF⟩ := hi.rest
  have hnF' : ¬ L.Free G := fun h => h t hph
  rw [hnF hnF', rnil_rsum] at ho
  obtain ⟨ht, hjt⟩ := hi.ht (by rw [hph]; decide)
  have hjb : joinedB m' = joinedB m := LockWord.joinedB_congr hs.threads
  have honly : ∀ u, L.ph (G u) = .holds → u = t := fun u hu => hi.w.one u t hu hph
  -- the held resource: in `t`'s part, so without the word's bytes and apart from `rX`
  have hsplit : L.own G m t = rsum (L.part (G t)) (L.held (G t)) := own_live hjt
  have hoffT := Inv.wordFree ho hi.w.blk ht
  have hHoff : L.Off (L.held (G t)).heap.erase := LockWord.off_sub hoffT fun l h => by
    rw [hsplit]; simp only [FHeap.erase, rsum, FHeap.union_apply, Option.map_eq_none_iff,
      ne_eq] at h ⊢
    cases e : (L.part (G t)).heap l <;> simp_all
  have hHX : FHeap.Disjoint (L.held (G t)).heap rX.heap := fun l => by
    cases e : (L.held (G t)).heap l with
    | none => exact .inl rfl
    | some c =>
      right
      have : (L.own G m t).heap l ≠ none := by
        rw [hsplit]; simp only [rsum, FHeap.union_apply]; cases (L.part (G t)).heap l <;> simp [e]
      have h2 := FOwned.part_off ho ht (l := l)
      cases e2 : rX.heap l with
      | none => rfl
      | some c2 =>
        exact absurd (h2 (by simp [FHeap.union_apply, e2])) this
  have ho1 := ho.give ht hsplit (hi.pdisj t)
  -- regroup the rest as `word ⋆ ((L.held (G t)) ⋆ rX)`
  have hWH : FHeap.Disjoint (L.wordR m).heap (L.held (G t)).heap := fun l => by
    by_cases hl : L.In l
    · exact .inr (LockWord.off_erase.mp hHoff l hl)
    · exact .inl (cellsAt_none hl)
  have e1 : rsum (L.held (G t)) (rsum (L.wordR m) rX) = rsum (L.wordR m) (rsum (L.held (G t)) rX) := by
    rw [← rsum_assoc, rsum_comm hWH.symm, rsum_assoc]
  rw [e1] at ho1
  have ho2 := rest_step ho1 hs hi.w.blk hHoff hi.xoff
  have hpt : L.pl (upd G t (L.set (G t) p rnil)) = upd (L.pl G) t p := pl_upd_set G t _ _
  have hphu : ∀ u, L.ph (upd G t (L.set (G t) p rnil) u) = if u = t then p else L.ph (G u) := by
    intro u; unfold upd; split
    · exact L.ph_set _ _ _
    · rfl
  have hnh : ∀ u, L.ph (upd G t (L.set (G t) p rnil) u) ≠ .holds := by
    intro u hu; rw [hphu] at hu
    split at hu
    · exact hp hu
    · rename_i h; exact h (honly u hu)
  have hown : m.OwnsC (m.clocks[t]!) (L.held (G t)).heap.erase :=
    (ho.owns t ht).sub fun l h => by
      rw [hsplit]; simp only [FHeap.erase, rsum, FHeap.union_apply, Option.map_eq_none_iff,
        ne_eq] at h ⊢
      cases e : (L.part (G t)).heap l <;> simp_all
  refine ⟨by rw [hpt]; exact hw, ⟨(L.held (G t)), ?_, hHoff, hHX, fun _ => ⟨?_, by rw [hpt]; exact hrel _ hown hHoff⟩,
    fun h => absurd (fun u => hnh u) h⟩, hi.xoff, fun u => ?_, fun u _ => ?_,
    fun u hu => absurd hu (hnh u)⟩
  · rw [own_upd hjb hjt, L.part_set, L.held_set, rsum_rnil]; exact ho2
  · rw [L.R_set]; exact hi.res t hph
  · unfold upd; split
    · rw [L.held_set]; exact FHeap.disjoint_empty _
    · exact hi.pdisj u
  · unfold upd; split
    · exact L.held_set _ _ _
    · rename_i h; exact hi.idle u (fun e => h (honly u e))

/-! ## Steps outside the lock's code -/

/-- A change of thread `t`'s ghost value outside the lock's code: `t` is `out` before, and `out`,
`gone` or `away` after; it keeps its part and holds nothing. -/
theorem Inv.ghost {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} {g : γ}
    (hi : L.Inv G rX m) (hph : L.ph (G t) = .out)
    (hg : L.ph g = .out ∨ L.ph g = .gone ∨ L.ph g = .away)
    (hpart : L.part g = L.part (G t)) (hheld : L.held g = rnil)
    (hlive : L.ph g ≠ .gone → t < m.threads.size ∧ joinedB m t = false)
    (hRk : ∀ r, L.R G r → L.R (upd G t g) r) : L.Inv (upd G t g) rX m := by
  have hnh : L.ph (G t) ≠ .holds := by rw [hph]; decide
  have hgh : L.ph g ≠ .holds := by rcases hg with h | h | h <;> rw [h] <;> decide
  have hown : L.own (upd G t g) m = L.own G m := by
    funext u; unfold FLock.own
    by_cases h : u = t
    · subst h; rw [upd_self, hpart, hheld, hi.idle u hnh]
    · rw [upd_ne _ _ h]
  have hphu : ∀ u, L.ph (upd G t g u) = if u = t then L.ph g else L.ph (G u) := fun u => by
    unfold upd; split <;> rfl
  have hholds : ∀ u, L.ph (upd G t g u) = .holds ↔ L.ph (G u) = .holds := by
    intro u; rw [hphu]; split
    · rename_i h; subst h; exact ⟨fun h => absurd h hgh, fun h => absurd h hnh⟩
    · exact Iff.rfl
  have hfree := free_iff_of (L := L) hholds
  have hgw : ∀ u, L.ph (upd G t g u) ≠ .gone → L.ph (G u) ≠ .gone := fun u h => by
    rw [hphu] at h; split at h
    · rename_i e; subst e; rw [hph]; decide
    · exact h
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  refine ⟨by rw [pl_upd]; exact hi.w.ghost hph hg hlive, ⟨rL, hown ▸ ho, hLoff, hLX, fun hF' => ?_,
    fun h => hnF (fun h' => h (hfree.mpr h'))⟩, hi.xoff, fun u => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨h1, h2⟩ := hF (hfree.mp hF')
    refine ⟨hRk rL h1, ?_⟩
    exact h2.weaken fun u h => hgw u h
  · unfold upd; split
    · rw [hheld]; exact FHeap.disjoint_empty _
    · exact hi.pdisj u
  · unfold upd; split
    · exact hheld
    · rename_i h; rw [hphu, if_neg h] at hu; exact hi.idle u hu
  · have hut : u ≠ t := fun e => by
      have := (hholds u).mp hu; rw [e] at this; exact hnh this
    rw [upd_ne _ _ hut]; exact hRk _ (hi.res u ((hholds u).mp hu))

/-- A change of thread `t`'s ghost value that keeps its place, its part and its resource in the
lock (a step of `t` in another sync object's code, also while it holds the lock). -/
theorem Inv.relabel {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} {g : γ}
    (hi : L.Inv G rX m) (hph : L.ph g = L.ph (G t)) (hpart : L.part g = L.part (G t))
    (hheld : L.held g = L.held (G t)) (hRk : ∀ r, L.R G r → L.R (upd G t g) r) :
    L.Inv (upd G t g) rX m := by
  have hphu : ∀ u, L.ph (upd G t g u) = L.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hph]
    · rw [upd_ne _ _ e]
  have hpl : L.pl (upd G t g) = L.pl G := funext hphu
  have hown : L.own (upd G t g) m = L.own G m := by
    funext u; unfold FLock.own
    by_cases e : u = t
    · subst e; rw [upd_self, hpart, hheld]
    · rw [upd_ne _ _ e]
  have hfree : L.Free (upd G t g) ↔ L.Free G := by unfold FLock.Free; rw [hpl]
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  refine ⟨by rw [hpl]; exact hi.w, ⟨rL, by rw [hown]; exact ho, hLoff, hLX, fun hF' => ?_,
    fun h => hnF (fun h' => h (hfree.mpr h'))⟩, hi.xoff, fun u => ?_, fun u hu => ?_,
    fun u hu => ?_⟩
  · obtain ⟨h1, h2⟩ := hF (hfree.mp hF'); exact ⟨hRk rL h1, by rw [hpl]; exact h2⟩
  · by_cases e : u = t
    · subst e; rw [upd_self, hpart, hheld]; exact hi.pdisj _
    · rw [upd_ne _ _ e]; exact hi.pdisj u
  · rw [hphu] at hu
    by_cases e : u = t
    · subst e; rw [upd_self, hheld]; exact hi.idle _ hu
    · rw [upd_ne _ _ e]; exact hi.idle u hu
  · rw [hphu] at hu
    by_cases e : u = t
    · subst e; rw [upd_self, hheld]; exact hRk _ (hi.res _ hu)
    · rw [upd_ne _ _ e]; exact hRk _ (hi.res u hu)

/-- **A step of thread `t` on its own part** with a thread triple (`FTTriple`): after it, a new
ghost value `g` for `t` with the same place, whose part and resource are the triple's post, gives
the invariant; the step keeps the lock's word and the protocol's rest `rX` (`FStepIn`). A `MemM`
step does not stop, so the ghost values of the `WP` (`G₀`) are any. -/
theorem Inv.wp_liftMem {Tgt α : Type} {P : Proto Tgt γ} {x : MemM α} {Pa : FAssn}
    {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop} {G G₀ : ThreadId → γ}
    {rX : Res} {m : Mem} {n : Nat} {t : ThreadId}
    (hi : L.Inv G rX m) (hc : m.current = t) (ht : t < m.threads.size) (hjt : joinedB m t = false)
    (htt : FTTriple Pa x Qa) (hp : Pa (rsum (L.part (G t)) (L.held (G t))))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → Qa a r' →
      FStepIn (rsum (L.wordR m) rX).heap.erase m m' →
      m'.current = t →
      (∀ g, L.ph g = L.ph (G t) → rsum (L.part g) (L.held g) = r' →
        FHeap.Disjoint (L.part g).heap (L.held g).heap → (L.ph g ≠ .holds → L.held g = rnil) →
        (L.ph (G t) ≠ .holds → ∀ r, L.R G r → L.R (upd G t g) r) →
        (L.ph g = .holds → L.R (upd G t g) (L.held g)) → L.Inv (upd G t g) rX m') →
      Q a G₀ m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G₀ m n := by
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  refine WP.liftMem_fownedR htt ho hc ht (by rw [own_live hjt]; exact hp)
    (fun a m' r' hr ho' hq hs => h a m' r' hr hq (hs.weaken fun l hl => ?_) (hs.current.trans hc)
      fun g hph hr' hpd hidle hRk hres => ?_) hret
  · simp only [FHeap.erase, Option.map_eq_none_iff, ne_eq, rsum, FHeap.union_apply,
      Option.or_eq_none_iff, not_and] at hl ⊢
    intro h1 _; exact hl h1
  have hjb : joinedB m' = joinedB m := LockWord.joinedB_congr hs.threads
  -- the word's cells: the same up to `Cell.norm`
  have hcells : ∀ x, L.o ≤ x → x < L.o + 4 →
      (m'.heap (L.b, x)).map Cell.norm = (m.heap (L.b, x)).map Cell.norm := by
    intro x h1 h2
    have hin : L.In (L.b, x) := ⟨rfl, h1, h2⟩
    have hc0 := hi.w.blk.cell h1 h2
    cases e : m.heap (L.b, x) with
    | none => exact absurd e hc0
    | some c =>
      have := ho'.rest_cell (l := (L.b, x)) (fc := ⟨c, none⟩) (by
        simp [FHeap.union_apply, cellsAt_of hin, e])
      rw [this]; rfl
  have hwF : ∀ x, L.o ≤ x → x < L.o + 4 →
      (rsum (L.wordR m) (rsum rL rX)).heap.erase (L.b, x) ≠ none := by
    intro x h1 h2
    have := LockWord.wordR_some hi.w.blk (l := (L.b, x)) ⟨rfl, h1, h2⟩
    simp only [FHeap.erase, rsum, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
      Option.or_eq_none_iff, not_and]
    intro h; exact absurd h this
  have hplg : L.pl (upd G t g) = L.pl G := by
    rw [pl_upd, hph]; funext u; unfold upd pl; split
    · rename_i e; subst e; rfl
    · rfl
  have hphu : ∀ u, L.ph (upd G t g u) = L.ph (G u) := fun u => by
    have := congrFun hplg u; exact this
  have hholds : ∀ u, L.ph (upd G t g u) = .holds ↔ L.ph (G u) = .holds := fun u => by rw [hphu]
  have hfree := free_iff_of (L := L) hholds
  -- the rest with the new memory's word cells
  have hsim : FHeap.Sim (rsum (L.wordR m') (rsum rL rX)).heap (rsum (L.wordR m) (rsum rL rX)).heap := by
    intro l
    by_cases hl : L.In l
    · obtain ⟨b, x⟩ := l
      obtain ⟨h1, h2, h3⟩ := hl
      simp only at h1 h2 h3; subst h1
      have := hcells x h2 h3
      simp only [rsum, FHeap.union_apply, cellsAt_of (show L.In (L.b, x) from ⟨rfl, h2, h3⟩)]
      cases e : m.heap (L.b, x) <;> cases e' : m'.heap (L.b, x) <;>
        simp_all [Option.map]
    · simp [rsum, FHeap.union_apply, cellsAt_none hl]
  have ho2 := ho'.congrRest hsim rfl rfl
  refine ⟨by rw [hplg]; exact hi.w.stepIn hs hwF hcells, ⟨rL, ?_, hLoff, hLX, fun hF' => ?_,
    fun h => hnF (fun h' => h (hfree.mpr h'))⟩, hi.xoff, fun u => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rw [own_upd hjb hjt, hr']; exact ho2
  · obtain ⟨h1, h2⟩ := hF (hfree.mp hF')
    have htn : L.ph (G t) ≠ .holds := fun e => hfree.mp hF' t e
    have hsub : ∀ l, rL.heap.erase l ≠ none →
        (rsum (L.wordR m) (rsum rL rX)).heap.erase l ≠ none := by
      intro l hl
      simp only [FHeap.erase, rsum, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
        Option.or_eq_none_iff, not_and] at hl ⊢
      intro _ hn; exact absurd hn hl
    refine ⟨hRk htn rL h1, ?_⟩
    rw [hplg]; exact h2.stepIn hs hsub hwF fun i l hl => (hi.w.loc.ok i l hl).1
  · unfold upd; split
    · exact hpd
    · exact hi.pdisj u
  · unfold upd; split
    · rename_i e; subst e; rw [hphu] at hu; exact hidle (by rw [hph]; exact hu)
    · rename_i e; rw [hphu] at hu; exact hi.idle u hu
  · by_cases hut : u = t
    · subst hut; rw [upd_self]; exact hres (by rw [hph]; rw [hphu] at hu; exact hu)
    · rw [upd_ne _ _ hut]
      rw [hphu] at hu
      have htn : L.ph (G t) ≠ .holds := fun e => hut (hi.w.one u t hu e)
      exact hRk htn _ (hi.res u hu)

/-- `Inv.wp_liftMem` for a step of generated code (`liftM`). -/
theorem Inv.wp_liftM {Tgt σ α : Type} {P : Proto Tgt γ} {x : MemM α} {s : σ} {Pa : FAssn}
    {Qa : α → FAssn} {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop} {G G₀ : ThreadId → γ}
    {rX : Res} {m : Mem} {n : Nat} {t : ThreadId}
    (hi : L.Inv G rX m) (hc : m.current = t) (ht : t < m.threads.size) (hjt : joinedB m t = false)
    (htt : FTTriple Pa x Qa) (hp : Pa (rsum (L.part (G t)) (L.held (G t))))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → Qa a r' →
      FStepIn (rsum (L.wordR m) rX).heap.erase m m' →
      m'.current = t →
      (∀ g, L.ph g = L.ph (G t) → rsum (L.part g) (L.held g) = r' →
        FHeap.Disjoint (L.part g).heap (L.held g).heap → (L.ph g ≠ .holds → L.held g = rnil) →
        (L.ph (G t) ≠ .holds → ∀ r, L.R G r → L.R (upd G t g) r) →
        (L.ph g = .holds → L.R (upd G t g) (L.held g)) → L.Inv (upd G t g) rX m') →
      Q (a, s) G₀ m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t ((liftM x : CM Tgt σ α).run s) Q G₀ m n := by
  show P.WP t (ConcM.liftMem x >>= fun a => pure (a, s)) Q G₀ m n
  exact WP.bind (hi.wp_liftMem hc ht hjt htt hp (fun a m' r' hr hq hs hc' hk =>
    WP.pure' (h a m' r' hr hq hs hc' hk)) hret)

/-- **A step of thread `t` on its own part** (`g`, out of the lock's code or holding the lock;
the held resource is framed), with a thread triple: its part becomes the triple's post
(`setPart`). -/
theorem Inv.wp_liftPart {Tgt α : Type} {P : Proto Tgt γ} {x : MemM α} {Pa : FAssn}
    {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop} {G G₀ : ThreadId → γ}
    {rX : Res} {m : Mem} {n : Nat} {t : ThreadId} {g : γ}
    (hi : L.Inv (upd G t g) rX m) (hc : m.current = t) (hgo : L.ph g = .out ∨ L.ph g = .holds)
    (htt : FTTriple Pa x Qa) (hp : Pa (L.part g))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → Qa a r' →
      FStepIn (rsum (L.wordR m) rX).heap.erase m m' →
      m'.current = t → L.Inv (upd G t (L.setPart g r')) rX m' → Q a G₀ m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G₀ m n := by
  have hgn : L.ph (upd G t g t) ≠ .gone := by
    rw [upd_self]; rcases hgo with e | e <;> rw [e] <;> decide
  obtain ⟨ht, hjt⟩ := hi.ht hgn
  have hd : FHeap.Disjoint (L.part g).heap (L.held g).heap := by
    have := hi.pdisj t; rwa [upd_self] at this
  refine hi.wp_liftMem hc ht hjt (htt.frame (R := (· = L.held g)))
    (by rw [upd_self]; exact ⟨_, _, hd, rfl, hp, rfl⟩)
    (fun a m' r'' hr hq hs hc' hk => ?_)
    (hret.imp_right fun hr => (FTTotalTriple.frame (R := (· = L.held g)) ⟨htt, hr⟩).2)
  obtain ⟨r', rH, hd', rfl, hq', rfl⟩ := hq
  refine h a m' r' hr hq' hs hc' ?_
  have hR : ∀ r, L.R (upd G t g) r → L.R (upd (upd G t g) t (L.setPart g r')) r := fun r hr => by
    have := (L.R_setPart (upd G t g) t r' r).mpr hr
    rwa [upd_self] at this
  have := hk (L.setPart g r') (by rw [L.ph_setPart, upd_self])
    (by rw [L.part_setPart, L.held_setPart])
    (by rw [L.part_setPart, L.held_setPart]; exact hd')
    (fun e => by
      rw [L.ph_setPart] at e; rw [L.held_setPart]
      have := hi.idle t (by rw [upd_self]; exact e); rwa [upd_self] at this)
    (fun _ => hR)
    (fun e => by
      rw [L.ph_setPart] at e; rw [L.held_setPart]
      have := hi.res t (by rw [upd_self]; exact e); rw [upd_self] at this; exact hR _ this)
  rwa [upd_upd] at this

/-! ## Spawn and join -/

theorem wordR_congr {m m' : Mem} (h : m'.blocks = m.blocks) : L.wordR m' = L.wordR m := by
  have : m'.heap = m.heap := by funext ⟨b, x⟩; simp only [Mem.heap, h]
  simp only [LockWord.wordR, cellsAt, this]

/-- A spawn by `t`, which is out of the lock's code: `t` keeps `part g₁`, the new thread gets
`part g₀` and starts out of the lock's code. -/
theorem Inv.fork {G : ThreadId → γ} {rX : Res} {m m' : Mem} {t c : ThreadId} {g₁ g₀ : γ}
    {gt : Bool} (hi : L.Inv G rX m) (hout : L.ph (G t) = .out)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m')))
    (hsplit : L.part (G t) = rsum (L.part g₁) (L.part g₀))
    (hd : FHeap.Disjoint (L.part g₁).heap (L.part g₀).heap)
    (h₁ : L.ph g₁ = .out) (h₁h : L.held g₁ = rnil)
    (h₀ : L.ph g₀ = .out) (h₀h : L.held g₀ = rnil)
    (hRk : ∀ r, L.R G r → L.R (upd (upd G c g₀) t g₁) r) :
    L.Inv (upd (upd G c g₀) t g₁) rX m' := by
  obtain ⟨ht, hjt⟩ := hi.ht (by rw [hout]; decide)
  have hheld : L.held (G t) = rnil := hi.idle t (by rw [hout]; decide)
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  have hownt : L.own G m t = rsum (L.part g₁) (L.part g₀) := by
    rw [own_live hjt, hheld, rsum_rnil, hsplit]
  have ho' := FOwned.fork (r₁ := L.part g₁) (r₂ := L.part g₀) (ho.current t |> fun _ => ho) ht
    hownt hd hf
  have hjb := joinedB_fork hf
  obtain ⟨hc, hw, hown⟩ := hi.w.fork (gt := gt) (by exact hout) hf
  rw [Proto.forkWith_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  have hct : m.threads.size ≠ t := fun h => by rw [h] at ht; exact Nat.lt_irrefl _ ht
  have hGc : L.ph (G m.threads.size) = .gone := by
    cases hx : L.ph (G m.threads.size) <;> first | rfl |
      exact absurd (hi.w.live _ (by simp only [pl]; rw [hx]; decide)).1 (Nat.lt_irrefl _)
  have hjc : joinedB m m.threads.size = false := by
    simp [joinedB, Array.getElem?_eq_none (Nat.le_refl _)]
  have hpl : L.pl (upd (upd G m.threads.size g₀) t g₁) = upd (L.pl G) m.threads.size .out := by
    funext u; simp only [pl, upd]
    by_cases h1 : u = t
    · simp [h1, h₁, hout, Ne.symm hct]
    · by_cases h2 : u = m.threads.size
      · simp [h1, h2, h₀, hct]
      · simp [h1, h2]
  have hphu : ∀ u, L.ph (upd (upd G m.threads.size g₀) t g₁ u) = .holds ↔ L.ph (G u) = .holds := by
    intro u
    have := congrFun hpl u; simp only [pl] at this; rw [this, LockWord.upd_apply]
    split
    · rename_i h; subst h; rw [hGc]; decide
    · exact Iff.rfl
  have hfree := free_iff_of (L := L) hphu
  refine ⟨by rw [hpl]; exact hw, ⟨rL, ?_, hLoff, hLX, fun hF' => ?_,
    fun h => hnF (fun h' => h (hfree.mpr h'))⟩, hi.xoff, fun u => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · have e : L.own (upd (upd G m.threads.size g₀) t g₁) { m with
        current := t,
        clocks := (m.clocks.set! t (VClock.bump (m.clocks[t]!) t)).push (VClock.bump (m.clocks[t]!) t),
        threads := m.threads.push { spawner := t, joined := false, gated := gt } } =
        upd (upd (L.own G m) t (L.part g₁)) m.threads.size (L.part g₀) := by
      funext u
      unfold FLock.own; rw [hjb]
      by_cases h1 : u = t
      · subst h1; simp [upd, hjt, Ne.symm hct, h₁h, rsum_rnil]
      · by_cases h2 : u = m.threads.size
        · subst h2; simp [upd, hjc, hct, h₀h, rsum_rnil]
        · simp [upd, h1, h2, FLock.own]
    rw [e]; exact ho'
  · obtain ⟨h1, h2⟩ := hF (hfree.mp hF')
    exact ⟨hRk rL h1, by rw [hpl]; exact hown _ h2⟩
  · unfold upd
    by_cases h1 : u = t
    · simp only [h1, ↓reduceIte, h₁h]; exact FHeap.disjoint_empty _
    · by_cases h2 : u = m.threads.size
      · simp only [h1, h2, hct, ↓reduceIte, h₀h]; exact FHeap.disjoint_empty _
      · simp only [h1, h2, ↓reduceIte]; exact hi.pdisj u
  · rw [ne_eq, hphu] at hu; unfold upd
    by_cases h1 : u = t
    · simp only [h1, ↓reduceIte, h₁h]
    · by_cases h2 : u = m.threads.size
      · simp only [h1, h2, hct, ↓reduceIte, h₀h]
      · simp only [h1, h2, ↓reduceIte]; exact hi.idle u hu
  · rw [hphu] at hu
    have hc' : u ≠ m.threads.size := fun e => by rw [e, hGc] at hu; cases hu
    have hut : u ≠ t := fun e => by rw [e, hout] at hu; cases hu
    rw [show upd (upd G m.threads.size g₀) t g₁ u = G u by simp [upd, hc', hut]]
    exact hRk _ (hi.res u hu)

/-- A join of `u` by `t`, both out of the lock's code: `t` takes `u`'s part. -/
theorem Inv.join {G : ThreadId → γ} {rX : Res} {m m' : Mem} {t u : ThreadId} {g : γ}
    (hi : L.Inv G rX m) (hut : u ≠ t) (hu0 : u ≠ 0) (hout : L.ph (G t) = .out)
    (huo : L.ph (G u) = .gone)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m')))
    (hg : L.part g = rsum (L.part (G t)) (L.own G m u)) (hgo : L.ph g = .out)
    (hgh : L.held g = rnil) (hRk : ∀ r, L.R G r → L.R (upd G t g) r) :
    L.Inv (upd G t g) rX m' := by
  obtain ⟨ht, hjt⟩ := hi.ht (by rw [hout]; decide)
  have hheld : L.held (G t) = rnil := hi.idle t (by rw [hout]; decide)
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  have ho' := ho.join ht hut hj
  obtain ⟨hw, hown⟩ := hi.w.join hut hu0 (by exact hout) (by exact huo) hj
  obtain ⟨rec, hr, -, rfl⟩ := Proto.join_eq hj
  have hul : u < m.threads.size := (Array.getElem?_eq_some_iff.mp hr).1
  have hjb : ∀ w, joinedB { m with
      current := t,
      clocks := m.clocks.set! t (VClock.merge (VClock.bump (m.clocks[t]!) t) (m.clocks[u]!)),
      threads := m.threads.set! u { rec with joined := true } } w =
      if w = u then true else joinedB m w := by
    intro w
    unfold joinedB
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hw : w = u
    · subst hw; simp [hu0, hul]
    · simp [hw, Ne.symm hw]
  have hpl : L.pl (upd G t g) = L.pl G := by
    rw [pl_upd, hgo, ← hout]; funext w; simp only [LockWord.upd_apply]; split
    · rename_i e; subst e; rfl
    · rfl
  have hholds : ∀ w, L.ph (upd G t g w) = .holds ↔ L.ph (G w) = .holds := fun w => by
    have := congrFun hpl w; simp only [pl] at this; rw [this]
  have hfree := free_iff_of (L := L) hholds
  refine ⟨by rw [hpl]; exact hw, ⟨rL, ?_, hLoff, hLX, fun hF' => ?_,
    fun h => hnF (fun h' => h (hfree.mpr h'))⟩, hi.xoff, fun w => ?_, fun w hw' => ?_, fun w hw' => ?_⟩
  · have e : L.own (upd G t g) { m with
        current := t,
        clocks := m.clocks.set! t (VClock.merge (VClock.bump (m.clocks[t]!) t) (m.clocks[u]!)),
        threads := m.threads.set! u { rec with joined := true } } =
        upd (upd (L.own G m) u rnil) t (rsum (L.own G m t) (L.own G m u)) := by
      funext w
      unfold FLock.own; rw [hjb]
      by_cases h1 : w = u
      · subst h1; simp [upd, hut]
      · by_cases h2 : w = t
        · subst h2; simp [upd, h1, hjt, hg, hgh, hheld, rsum_rnil, FLock.own]
        · simp [upd, h1, h2]
    rw [e]; exact ho'
  · obtain ⟨h1, h2⟩ := hF (hfree.mp hF')
    exact ⟨hRk rL h1, by rw [hpl]; exact hown _ h2⟩
  · unfold upd; split
    · rw [hgh]; exact FHeap.disjoint_empty _
    · exact hi.pdisj w
  · rw [ne_eq, hholds] at hw'; unfold upd; split
    · exact hgh
    · exact hi.idle w hw'
  · rw [hholds] at hw'
    have hwt : w ≠ t := fun e => by rw [e, hout] at hw'; cases hw'
    rw [upd_ne _ _ hwt]; exact hRk _ (hi.res w hw')

/-! ## The start and the end of the lock -/

/-- **The start of the lock**: thread `t`, whose clock is above every thread's, gives the word
`rW` (exactly the word's bytes, which hold `0`) and the resource `rL` (with `R`) of its part to the
rest `rX`. Each thread is out of the lock's code (and alive) or gone, no atomic location is in the
word's block, and no thread waits at a futex. -/
theorem Inv.make {G : ThreadId → γ} {own : ThreadId → Res} {rX rL rW : Res} {m : Mem}
    {t : ThreadId} (ho : FOwned own rX m) (hjt : joinedB m t = false) (ht : t < m.threads.size)
    (hown : ∀ u, u ≠ t → L.own G m u = own u)
    (hsplit : own t = rsum (L.part (G t)) (rsum rL rW))
    (hd : FHeap.Disjoint (L.part (G t)).heap (rsum rL rW).heap)
    (hdLW : FHeap.Disjoint rL.heap rW.heap)
    (hW : ∀ l, rW.heap l ≠ none ↔ L.In l) (hWk : rW.know = Know.none) (hWg : rW.gh = Ghost.unit)
    (hph : ∀ u, (L.ph (G u) = .out ∧ u < m.threads.size ∧ joinedB m u = false) ∨
      L.ph (G u) = .gone) (hheld : ∀ u, L.held (G u) = rnil) (hR : L.R G rL)
    (hblk : L.BlkOk m) (h0 : L.U32 m 0) (hat : ∀ l ∈ m.atomics, l.block ≠ L.b)
    (hq : m.waiters = #[]) (hall : AllLe m (m.clocks[t]!)) :
    L.Inv G rX m := by
  have hfree : L.Free G := fun u => by
    show L.ph (G u) ≠ _; rcases hph u with ⟨h, -⟩ | h <;> rw [h] <;> decide
  have hownE : L.own G m = upd own t (L.part (G t)) := by
    funext u; unfold upd
    by_cases hu : u = t
    · subst hu; simp [own_live hjt, hheld, rsum_rnil]
    · simp only [hu, ↓reduceIte]; exact hown u hu
  -- `t` owns the word and the resource: every access to them happened before every thread
  have htown := ho.owns t ht
  rw [hsplit] at htown
  have hsubT : ∀ (h : FHeap), (∀ l, h l ≠ none → (rsum rL rW).heap l ≠ none) →
      ∀ l, h.erase l ≠ none → (FHeap.erase (rsum (L.part (G t)) (rsum rL rW)).heap) l ≠ none := by
    intro h hs l hl
    have := hs l (by simpa [FHeap.erase] using hl)
    simp only [FHeap.erase, rsum, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
      Option.or_eq_none_iff, not_and] at this ⊢
    intro _; exact this
  have hle : ∀ (h : FHeap), (∀ l, h l ≠ none → (rsum rL rW).heap l ≠ none) →
      ∀ e ∈ m.footprint, (e.Touches h.erase ∨ m.blocks.size ≤ e.block) →
        ∀ u < m.threads.size, VClock.le e.clock (m.clocks[u]!) = true :=
    fun h hs e he htc u hu => VClock.le_trans (htown.sub (hsubT h hs) e he htc) (hall u hu)
  have hW' : ∀ l, rW.heap l ≠ none → (rsum rL rW).heap l ≠ none := fun l hl => by
    simp only [rsum, FHeap.union_apply]; cases rL.heap l <;> simp_all
  have hL' : ∀ l, rL.heap l ≠ none → (rsum rL rW).heap l ≠ none := fun l hl => by
    simp only [rsum, FHeap.union_apply]; cases e : rL.heap l <;> simp_all
  have hw : L.WInv (L.pl G) m :=
    LockWord.WInv.make (ho.csize) (fun u => hph u) hblk h0 hat hq fun e he hh u hu _ =>
      hle rW.heap hW' e he (.inl (LockWord.touches_word hh fun x h1 h2 => by
        simpa [FHeap.erase] using (hW (L.b, x)).mpr ⟨rfl, h1, h2⟩)) u hu
  have hLoff : L.Off rL.heap.erase := LockWord.off_erase.mpr fun l hl => by
    rcases hdLW l with e | e
    · exact e
    · exact absurd e ((hW l).mpr hl)
  -- the rest: give `rL ⋆ rW` to it, then read `rW` as the word's cells
  have ho1 := ho.give ht hsplit hd
  rw [← hownE] at ho1
  -- `t`'s part (with `rL` and `rW`) is apart from the rest
  have hTX : ∀ l, rX.heap l ≠ none → (own t).heap l = none := fun l hn => ho.part_off ht hn
  have hWX : FHeap.Disjoint rW.heap rX.heap := fun l => by
    cases e : rX.heap l with
    | none => exact .inr rfl
    | some _ =>
      have h2 := hTX l (by rw [e]; simp)
      rw [hsplit] at h2
      simp only [rsum, FHeap.union_apply, Option.or_eq_none_iff] at h2
      exact .inl h2.2.2
  have hLX : FHeap.Disjoint rL.heap rX.heap := fun l => by
    cases e : rX.heap l with
    | none => exact .inr rfl
    | some _ =>
      have h2 := hTX l (by rw [e]; simp)
      rw [hsplit] at h2
      simp only [rsum, FHeap.union_apply, Option.or_eq_none_iff] at h2
      exact .inl h2.2.1
  have hxoff : L.Off rX.heap.erase := LockWord.off_erase.mpr fun l hl => by
    rcases hWX l with e | e
    · exact absurd e ((hW l).mpr hl)
    · exact e
  refine ⟨hw, ⟨rL, ?_, hLoff, hLX, fun _ => ⟨hR, fun e he htc => .inl fun u hu _ =>
      hle rL.heap hL' e he htc u hu⟩, fun h => absurd hfree h⟩, hxoff,
    fun u => by rw [hheld]; exact FHeap.disjoint_empty _, fun u _ => hheld u,
    fun u hu => absurd hu (hfree u)⟩
  -- `rsum (rsum rL rW) rX` as `rsum (wordR m) (rsum rL rX)`
  refine ho1.congrRestU (fun l => ?_) (fun l fc' hl => ?_) ?_ ?_
  · by_cases hl : L.In l
    · have hWl := (hW l).mpr hl
      have hLl := (hdLW l).resolve_right hWl
      have hXl := (hWX l).resolve_left hWl
      simp only [rsum, FHeap.union_apply, cellsAt_of hl, hLl, hXl, Option.none_or, Option.or_none]
      obtain ⟨fc, hfc⟩ := Option.ne_none_iff_exists'.mp hWl
      rw [hfc]
      have := ho1.rest_cell (l := l) (fc := fc) (by simp [rsum, FHeap.union_apply, hLl, hfc])
      cases e : m.heap l with
      | none => rw [e] at this; cases this
      | some c => rw [e] at this; simpa [Cell.norm] using this
    · have hWl : rW.heap l = none := by
        cases e : rW.heap l with
        | none => rfl
        | some _ => exact absurd ((hW l).mp (by rw [e]; simp)) hl
      simp [rsum, FHeap.union_apply, cellsAt_none hl, hWl]
  · by_cases hl' : L.In l
    · have hWl := (hW l).mpr hl'
      have hLl := (hdLW l).resolve_right hWl
      have hXl := (hWX l).resolve_left hWl
      simp only [rsum, FHeap.union_apply, cellsAt_of hl', hLl, hXl, Option.none_or,
        Option.or_none, Option.map_eq_some_iff] at hl
      obtain ⟨c, -, rfl⟩ := hl
      exact .inl rfl
    · simp only [rsum, FHeap.union_apply, cellsAt_none hl', Option.none_or] at hl
      refine .inr ⟨fc', ?_, rfl⟩
      have hWl : rW.heap l = none := by
        cases e : rW.heap l with
        | none => rfl
        | some _ => exact absurd ((hW l).mp (by rw [e]; simp)) hl'
      simp only [rsum, FHeap.union_apply]
      cases e : rL.heap l <;> simp_all
  · simp [rsum, LockWord.wordR, cellsAt, hWk, Know.none_union, Know.union_assoc]
  · simp [rsum, LockWord.wordR, cellsAt, hWg, Ghost.add_assoc]

/-- **The end of the lock**: no thread holds it, and thread `t` (not `gone`) has a clock above every
thread's. Then `t` takes the resource `rL` (with `R`) and the word's cells into its part, apart from
its old part. -/
theorem Inv.take {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} (hi : L.Inv G rX m)
    (hF : L.Free G) (hg : L.ph (G t) ≠ .gone)
    (hall : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m.clocks[t]!) = true) :
    ∃ rL, L.R G rL ∧ ((fun r => r = L.own G m t) ⋆ ((fun r => r = rL) ⋆ fun r => r = L.wordR m))
        (rsum (L.own G m t) (rsum rL (L.wordR m))) ∧
      FOwned (upd (L.own G m) t (rsum (L.own G m t) (rsum rL (L.wordR m)))) rX m := by
  obtain ⟨ht, -⟩ := hi.ht hg
  obtain ⟨rL, ho, hLoff, hLX, hFr, -⟩ := hi.rest
  obtain ⟨hR, hLown⟩ := hFr hF
  have hWL : FHeap.Disjoint (L.wordR m).heap rL.heap := fun l => by
    by_cases hl : L.In l
    · exact .inr (LockWord.off_erase.mp hLoff l hl)
    · exact .inl (cellsAt_none hl)
  have hWX : FHeap.Disjoint (L.wordR m).heap rX.heap := fun l => by
    by_cases hl : L.In l
    · exact .inr (LockWord.off_erase.mp hi.xoff l hl)
    · exact .inl (cellsAt_none hl)
  have e1 : rsum (L.wordR m) (rsum rL rX) = rsum (rsum rL (L.wordR m)) rX := by
    rw [← rsum_assoc, rsum_comm hWL]
  rw [e1] at ho
  have hT : FHeap.Disjoint (L.own G m t).heap (rsum rL (L.wordR m)).heap := fun l => by
    cases e : (rsum rL (L.wordR m)).heap l with
    | none => exact .inr rfl
    | some _ => exact .inl (ho.part_off ht (by
        show ((rsum rL (L.wordR m)).heap ∪ rX.heap) l ≠ none
        rw [FHeap.union_apply, e]; simp))
  refine ⟨rL, hR, ⟨_, _, hT, rfl, rfl, _, _, hWL.symm, rfl, rfl, rfl⟩,
    ho.take ht (FHeap.disjoint_union_left.mpr ⟨hLX, hWX⟩) ?_⟩
  simp only [rsum, FHeap.erase_union]
  refine Mem.OwnsC.union (fun e he htc => ?_) (fun e he htc => ?_)
  · rcases hLown e he htc with h | ⟨i, l, hl, hle⟩
    · exact VClock.le_trans (h t ht hg) (VClock.le_refl _)
    · obtain ⟨⟨v, hv, hle'⟩, -⟩ := hi.w.rel i l hl
      exact VClock.le_trans hle (VClock.le_trans hle' (hall v hv))
  · rcases htc with ⟨x, h1, h2, h3⟩ | hb
    · have hin : L.In (e.block, x) := Classical.byContradiction fun hn =>
        h3 (by simp [FHeap.erase, cellsAt_none hn])
      obtain ⟨hb, hx1, hx2⟩ := hin
      rcases hi.w.wfp e he ⟨hb, x, h1, h2, hx1, hx2⟩ with ⟨-, v, hv, hle⟩ | h
      · exact VClock.le_trans hle (hall v hv)
      · exact h t ht hg
    · -- an access to a block that does not exist yet happened before `t`: `t` owns its part
      exact ho.owns t ht e he (.inr hb)

/-! ## A recorded access to bytes of the protocol's rest -/

/-- A recorded access of the current thread `t` (not a write) to `n` bytes of the protocol's own
rest `rX` (a read of a read-shared buffer): the invariant holds after it. -/
theorem Inv.recordX {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} {b : BlockId}
    {o n : Nat} {k : AccessKind} (hi : L.Inv G rX m) (hk : k ≠ .write) (hc : m.current = t)
    (ht : t < m.threads.size) (hb : b < m.blocks.size) (hn : 0 < n)
    (hX : ∀ x, o ≤ x → x < o + n → rX.heap (b, x) ≠ none) :
    L.Inv G rX (m.recordAt b o n k) := by
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  have hrest : ∀ x, o ≤ x → x < o + n → (rsum (L.wordR m) (rsum rL rX)).heap (b, x) ≠ none :=
    fun x h1 h2 => by
      have := hX x h1 h2
      simp only [rsum, FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
      intro _ _; exact this
  have hnw : b ≠ L.b ∨ o + n ≤ L.o ∨ L.o + 4 ≤ o := by
    by_cases hbb : b = L.b
    · subst hbb
      by_cases hlo : o + n ≤ L.o
      · exact .inr (.inl hlo)
      · by_cases hhi : L.o + 4 ≤ o
        · exact .inr (.inr hhi)
        · exfalso
          have x0 : ∃ x, o ≤ x ∧ x < o + n ∧ L.o ≤ x ∧ x < L.o + 4 :=
            ⟨if o ≤ L.o then L.o else o, by split <;> omega, by split <;> omega,
              by split <;> omega, by split <;> omega⟩
          obtain ⟨x, h1, h2, h3, h4⟩ := x0
          have := hX x h1 h2
          have h0 := LockWord.off_erase.mp hi.xoff (L.b, x) ⟨rfl, h3, h4⟩
          exact this h0
    · exact .inl hbb
  have hLb : ∀ x, o ≤ x → x < o + n → rL.heap.erase (b, x) = none := fun x h1 h2 => by
    have := (hLX (b, x)).resolve_right (hX x h1 h2)
    simp [FHeap.erase, this]
  have hjb : joinedB (m.recordAt b o n k) = joinedB m := rfl
  refine ⟨hi.w.readK hk hnw, ⟨rL, ?_, hLoff, hLX, fun hF' => ?_, hnF⟩, hi.xoff, hi.pdisj,
    hi.idle, hi.res⟩
  · have : L.wordR (m.recordAt b o n k) = L.wordR m := wordR_congr rfl
    rw [this]
    have e : L.own G (m.recordAt b o n k) = L.own G m := rfl
    rw [e]
    exact ho.recordRest hc ht hb fun u hu x h1 h2 => ho.part_off hu (hrest x h1 h2)
  · obtain ⟨h1, h2⟩ := hF hF'
    exact ⟨h1, h2.readK hb (fun x h1 h2 => hLb x h1 h2)⟩

end FLock

end Full
end Zig
