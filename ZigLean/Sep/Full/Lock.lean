import ZigLean.Sep.Full.LockWord
import ZigLean.Sep.Full.ThreadRest
import ZigLean.Sep.Full.Atomic
import ZigLean.Sep.Full.Tick

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
- **A protocol with the lock and a sync primitive next to it** (`FLock.Fits L K P U ok`, the one
  judgment for every sync primitive): its invariant is `∃ rX, Inv G rX m ∧ U G rX m`; a step of
  the lock's code (`LockWord.Step`) by a thread with `ok`, not `gone`, `away` or `holdsAway`, keeps
  `U`
  with the same `rX`. The primitive `K` (`FPrim`) is data: a thread's place in its code
  (`FPlace`), its roles, what the rest keeps for it (`Sub`: its invariant, its cells), and its steps (`Step`); `U` keeps `Sub`
  and every step, and the primitive's place is a part of the ghost value independent of the
  lock's (the compatibility laws `lph` … `role_part`). The lock alone is `FPrim.empty`
  (`Fits.ofLock`); a primitive over futex words (the event, the condition) is `FPrim.ofWords`
  (`ZigLean/Sep/Full/WordRules.lean`). A new primitive is a new `FPrim`, not a new judgment.
- **Steps outside the lock's code**: a thread's step on its own part (`Inv.wp_liftMem`, with a
  thread triple `FTTriple`), a change of a ghost value (`Inv.ghost`), a spawn (`Inv.fork`), a join
  (`Inv.join`). The steps of the lock's code change the invariant through `Inv.lstep`,
  `Inv.acq` (acquire) and `Inv.rel` (release).
-/

namespace Zig
namespace Full

open FAssn Conc Proto

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
  have hmeta : KMono m m' ∧ KeepsExt m m' ∧ (m.LiveLayout → m'.LiveLayout) ∧
      MemAuth.Keep m { m' with current := m.current } := by
    rcases hs.blocks with e | ⟨blk', bs, h1, -, h3, h4, h5⟩
    · refine ⟨KMono.of_blocks e, KeepsExt.of_blocks e, fun h => ?_,
        MemAuth.Keep.of_aux (m' := { m' with current := m.current }) e hs.aux⟩
      obtain ⟨hd, hbd⟩ := h
      exact ⟨fun b b' x x' hne h1 h2 => hd b b' x x' hne (e ▸ h1) (e ▸ h2),
        fun b x h1 => hbd b x (e ▸ h1)⟩
    · rw [hblk] at h1; cases h1
      have hw : m'.blocks = m.blocks.set! L.b { blk with bytes := writeBytes blk.bytes L.o bs } := by
        rw [h5]; rfl
      obtain ⟨k1, k2, k3⟩ := kmono_write (m' := { m' with current := m.current }) hblk hw
        (by omega) hk hs.aux
      exact ⟨k1, k2, ld_write hblk (by omega) hw, k3⟩
  refine ⟨hs.threads, hs.csize, hs.clocks, hs.bsize, fun l hl => hs.heap hl, fun l hl => ?_,
    hmeta.1, hmeta.2.1, hmeta.2.2.1, fun b x hx => ?_, fun hw => ?_, fun e he => ?_, hmeta.2.2.2,
    hs.cov⟩
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

/-- A step of a thread in the lock's code keeps the ghost values `X`. -/
theorem snd_set {X : Type} {b o c : Nat} {R : (ThreadId → X) → FAssn} {hc : c = 1 ∨ c = 2 ∨ c = 3}
    (G : ThreadId → FLG × X) (t : ThreadId) (p : LPh) (h : Res) :
    (fun u => (upd G t ((FLock.prod b o R c hc).set (G t) p h) u).2) = fun u => (G u).2 := by
  rw [upd_snd]; funext u; unfold upd; split
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

/-- **`rL` is the free lock's resource** in the invariant's rest (`Inv.rest`): the threads' parts
and the rest `wordR ⋆ rL ⋆ rX` (`FOwned`), `rL` off the word and apart from `rX`, with `R` and
`LockWord.Owns` while the lock is free, and `rnil` while a thread holds it (so `rL` is the lock's
resource only when the lock is free). -/
abbrev FreeRes (G : ThreadId → γ) (rX : Res) (m : Mem) (rL : Res) : Prop :=
  FOwned (L.own G m) (rsum (L.wordR m) (rsum rL rX)) m ∧
    L.Off rL.heap.erase ∧ FHeap.Disjoint rL.heap rX.heap ∧
    (L.Free G → L.R G rL ∧ L.toLockWord.OwnsRes (L.pl G) m rL) ∧ (¬ L.Free G → rL = rnil)

/-- **An acquire by `t` gathers no read share** (`docs/sep-full-state.md` §Read shares): at every
byte, `t`'s part or the lock's resource holds no partial share. Gathering two partial shares into a
whole one makes the byte exclusive, which needs every read of it ordered before `t`; the free
lock orders only the writes to its partial shares (`LockWord.OwnsRes`), so `Inv.acq` fails closed
on it (engine ledger #share-gather). A resource without partial shares never gathers
(`NoGather.of_R`). -/
def NoGather (G : ThreadId → γ) (m : Mem) (t : ThreadId) : Prop :=
  ∀ rL, L.R G rL → ∀ l, (L.own G m t).shared l = none ∨ rL.shared l = none

/-- A lock whose resource holds no partial share gathers none (`FAssn.Unshared`: `up`, `bext`,
`⋆`, `∃`, …). -/
theorem NoGather.of_R (hR : ∀ G, (L.R G).Unshared) {G : ThreadId → γ} {m : Mem}
    {t : ThreadId} : L.NoGather G m t :=
  fun rL h l => .inr (hR G rL h l)

/-- The invariant of the lock with the protocol's own rest `rX` (module doc). -/
structure Inv (G : ThreadId → γ) (rX : Res) (m : Mem) : Prop where
  w : L.WInv (L.pl G) m
  rest : ∃ rL, L.FreeRes G rX m rL
  xoff : L.Off rX.heap.erase
  pdisj : ∀ u, FHeap.Disjoint (L.part (G u)).heap (L.held (G u)).heap
  idle : ∀ u, (L.ph (G u)).held = false → L.held (G u) = rnil
  /-- The holder's resource (awake, or at another object's futex wait). -/
  res : ∀ u, (L.ph (G u)).held = true → L.R G (L.held (G u))

/-- An instrumented step on the caller's part, including while another sync object's internal
phase makes `ok` false. The existing total thread rule pays for the actual tick and fixes its
complete post-resource; the protected resource and the protocol rest are framed unchanged.
Native atomic/futex steps still use their exact `Step`/`Mem.Aux` summaries. -/
def PartTick (t : ThreadId) (G : ThreadId → γ) (rX : Res) (m : Mem)
    (G' : ThreadId → γ) (rX' : Res) (m' : Mem) : Prop :=
  m.current = t ∧ L.ph (G t) ≠ .gone ∧ L.Inv G rX m ∧ ∃ r,
    FTTotalTriple (fun rp => rp = L.part (G t)) Zig.tick (fun _ rp => rp = r) ∧
    G' = upd G t (L.setPart (G t) r) ∧ rX' = rX ∧ m' = m.ticked ∧ L.Inv G' rX' m'

/-- **The resource a step of the lock's code moves**, when `t` goes to the place `p` with the held
resource `h` (a premise of `Fits.stable`; ledger #lock-stable-inv), in four cases: without the
lock afterwards `t` holds nothing; a holder that stays one keeps its resource; at an acquire the
lock was free and `h` is its resource before the step (`Inv.acq`); at a release the free lock's
resource after the step is the one `t` held (`Inv.rel`). The rules build it with `Transfer.none`,
`stay`, `acquire` and `release` (`LockRules.lean`). -/
def Transfer (G : ThreadId → γ) (rX : Res) (m m' : Mem) (t : ThreadId) (p : LPh) (h : Res) :
    Prop :=
  (p.held = false → h = rnil) ∧
  ((L.ph (G t)).held = true → p.held = true → h = L.held (G t)) ∧
  ((L.ph (G t)).held = false → p.held = true → L.Free G ∧ L.FreeRes G rX m h) ∧
  ((L.ph (G t)).held = true → p.held = false →
    L.FreeRes (upd G t (L.set (G t) p h)) rX m' (L.held (G t)))


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
  before the newest message of the word. The thread runs the lock's code, so it has not ended
  and is not away in another object's code, without the lock (`away`) or holding it
  (`holdsAway`). A holder's nap and unnap (`holds` ↔ `holdsAway`, `LockWord.WInv.nap`/`unnap`)
  are not such steps: no lock code runs and the word does not change. Their `U`-stability is a
  hypothesis of the nap and unnap rules (`Fits.nap`/`Fits.unnap`, planned with the two-lock
  product), discharged by each nesting protocol for its own `U`; a protocol that never nests
  (empty `nest`) proves nothing for them (decision on #667). The client may use the lock's
  invariant before the step (`L.Inv G rX m`), e.g. in a two-lock product the stepping lock's
  `BlkOk`, which the other lock's invariant inside `U` needs. Every rule that applies `stable`
  has it (ledger #lock-stable-inv).

  The client also gets the resource the step moves (`Transfer`: `rnil` without the lock, the old
  one for a holder that stays one, at an acquire the free resource before the step, at a release
  the free resource after it is the one `t` held). Every rule has it: at once for a step that
  neither holds the lock before nor after it, from `Inv.idle` for a step that keeps the place,
  from `Inv.acq`/`Inv.rel` for an acquire or a release (maintainer
  decision 2026-11-05, option (a) on #693).
  Without it `h` is arbitrary, and a two-lock product's `U` cannot say where lock A's held
  resource lies in lock B's rest, which B's invariant needs after a critical-section step.
  Counterexample: at A's acquire take `h := {d ↦ w}` with `d` outside B's rest; the coupling is
  false, yet `stable` demanded `U`. Rejected: the post-step invariant (pins `h` only for precise
  `R`), a ghost free resource (changes `Inv`), fixed footprints and strict nesting only. -/
  stable : ∀ G rX m m' t p h, ok (G t) → L.ph (G t) ≠ .gone → L.ph (G t) ≠ .away →
    L.ph (G t) ≠ .holdsAway → L.Inv G rX m → U G rX m → L.Step t m m' →
    (L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!)) →
    L.Transfer G rX m m' t p h → U (upd G t (L.set (G t) p h)) rX m'
  /-- A stop of any thread (`current := t`, a thread that exists) keeps `U`: a thread without `ok`
  (one inside another sync object's code, which runs no lock code) stops too, and so does a thread
  that left the lock (`gone`) and runs other sync code. The scheduler resumes only a thread that
  exists (`Proto.Safe`), so the stop knows `t < m.threads.size`. -/
  atStop : ∀ G rX m t, t < m.threads.size → U G rX m → U G rX { m with current := t }
  /-- An acquire gathers no read share (`NoGather`, `Inv.acq`: fail closed, engine ledger
  #share-gather); a resource without partial shares discharges it (`NoGather.of_R`). -/
  noGather : ∀ G rX m t, L.Inv G rX m → U G rX m → L.NoGather G m t
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
  /-- A native primitive step or an admitted caller-part tick keeps `U`. The latter transports
  the exact memory and actual resource post through the same composite stability obligation,
  without requiring `ok` in an internal busy phase. -/
  kstep : ∀ t G rX m G' rX' m',
    K.Step t G rX m G' rX' m' ∨ L.PartTick t G rX m G' rX' m' → U G rX m → U G' rX' m'
  /-- **A holder at another object's futex wait is not in a deadlock** (`LockWord.nest`): the one
  liveness obligation of a lock order. A lock without a nest discharges it at once
  (`FLock.holdLive_none`: such a holder is never asleep); a lock whose nest is the words of inner
  locks from their `Fits` (`FLock.holdLive_inners`, `LockOrder.lean`). -/
  holdLive : ∀ G rX m v, L.Inv G rX m → U G rX m → L.ph (G v) = .holdsAway → P.Live v G m

variable {L}

/-- **The obligation for a lock without a nest** (every single-lock protocol): a holder at
`holdsAway` is never in the futex queue, so it is never in a deadlock. -/
theorem holdLive_none {Tgt : Type} {P : Proto Tgt γ} (hn : ∀ p, ¬ L.nest p) {G : ThreadId → γ}
    {rX : Res} {m : Mem} {v : ThreadId} (hi : L.Inv G rX m) (hv : L.ph (G v) = .holdsAway) :
    P.Live v G m := fun hq _ => by
  obtain ⟨-, -, -, p, hp, -⟩ := hi.w.nestQ hv hq
  exact hn p hp

/-- The same ghost value for `t` (`set_self`). -/
theorem upd_set_self (G : ThreadId → γ) (t : ThreadId) :
    upd G t (L.set (G t) (L.ph (G t)) (L.held (G t))) = G := by
  rw [L.set_self]; funext u; unfold upd; split <;> simp_all

/-- **A protocol with the lock alone**, where only a thread with `ok` runs the lock's code. -/
theorem Fits.ofLock {Tgt : Type} {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop}
    {ok : γ → Prop} (inv : ∀ G m, P.inv G m ↔ ∃ rX, L.Inv G rX m ∧ U G rX m)
    (fin : ∀ g, P.fin g → L.ph g = .gone) (joins : ∀ g, P.joins g → L.ph g = .out)
    (ok_set : ∀ g p h, ok (L.set g p h) ↔ ok g) (ok_setPart : ∀ g r, ok (L.setPart g r) ↔ ok g)
    (stable : ∀ G rX m m' t p h, ok (G t) → L.ph (G t) ≠ .gone → L.ph (G t) ≠ .away →
      L.ph (G t) ≠ .holdsAway → L.Inv G rX m → U G rX m → L.Step t m m' →
      (L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!)) →
      L.Transfer G rX m m' t p h → U (upd G t (L.set (G t) p h)) rX m')
    (atStop : ∀ G rX m t, t < m.threads.size → U G rX m → U G rX { m with current := t })
    (tick : ∀ t G rX m G' rX' m', L.PartTick t G rX m G' rX' m' → U G rX m → U G' rX' m')
    (noGather : ∀ G rX m t, L.Inv G rX m → U G rX m → L.NoGather G m t)
    (hn : ∀ p, ¬ L.nest p := by exact fun _ h => h) :
    L.Fits (FPrim.empty γ) P U ok where
  inv := inv
  fin := fin
  joins := joins
  ok_set := ok_set
  ok_setPart := ok_setPart
  stable := stable
  atStop := atStop
  noGather := noGather
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
  kstep t G rX m G' rX' m' h hU := h.elim (fun h => nomatch h)
    (fun h => tick t G rX m G' rX' m' h hU)
  holdLive _ _ _ _ hi _ hv := holdLive_none hn hi hv

/-- **A protocol with the lock alone**, where every thread may run the lock's code. -/
theorem Fits.ofLockAll {Tgt : Type} {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop}
    (inv : ∀ G m, P.inv G m ↔ ∃ rX, L.Inv G rX m ∧ U G rX m)
    (fin : ∀ g, P.fin g → L.ph g = .gone) (joins : ∀ g, P.joins g → L.ph g = .out)
    (stable : ∀ G rX m m' t p h, L.ph (G t) ≠ .gone → L.ph (G t) ≠ .holdsAway → L.Inv G rX m →
      U G rX m → L.Step t m m' → (L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!)) →
      L.Transfer G rX m m' t p h → U (upd G t (L.set (G t) p h)) rX m')
    (atStop : ∀ G rX m t, t < m.threads.size → U G rX m → U G rX { m with current := t })
    (tick : ∀ t G rX m G' rX' m', L.PartTick t G rX m G' rX' m' → U G rX m → U G' rX' m')
    (noGather : ∀ G rX m t, L.Inv G rX m → U G rX m → L.NoGather G m t)
    (hn : ∀ p, ¬ L.nest p := by exact fun _ h => h) :
    L.Fits (FPrim.empty γ) P U fun _ => True :=
  .ofLock inv fin joins (fun _ _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    (fun G rX m m' t p h _ hg _ hz => stable G rX m m' t p h hg hz) atStop tick noGather hn

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

theorem held_false_of_iff {a b : LPh} (h : a.held = true ↔ b.held = true) (ha : a.held = false) :
    b.held = false := by
  cases hb : b.held
  · rfl
  · rw [h.mpr hb] at ha; cases ha

theorem free_iff_of {G G' : ThreadId → γ}
    (h : ∀ u, (L.ph (G' u)).held = true ↔ (L.ph (G u)).held = true) :
    L.Free G' ↔ L.Free G := by
  unfold FLock.Free LockWord.Free pl
  exact forall_congr' fun u => imp_congr_left (h u)

theorem Inv.ht {G : ThreadId → γ} {rX : Res} {m : Mem} (hi : L.Inv G rX m) {t : ThreadId}
    (hg : L.ph (G t) ≠ .gone) : t < m.threads.size ∧ joinedB m t = false :=
  hi.w.live t hg

/-- **A thread outside the lock without read shares in its part owns none** (`Inv.join`'s and
`Inv.take`'s gather premise `hgat`, from a protocol's `fin` or its parts' assertions). -/
theorem Inv.own_unshared {G : ThreadId → γ} {rX : Res} {m : Mem} (hi : L.Inv G rX m)
    {u : ThreadId} (hu : (L.ph (G u)).held = false) (hp : ∀ l, (L.part (G u)).shared l = none)
    (l : Loc) : (L.own G m u).shared l = none := by
  unfold own; split
  · exact (Res.excl_eq_erase).2 l
  · rw [hi.idle u hu, rsum_rnil]; exact hp l

/-- No part, no free resource and not the protocol's rest has a byte of the word. -/
theorem Inv.wordFree {G : ThreadId → γ} {rY : Res} {m : Mem}
    (ho : FOwned (L.own G m) (rsum (L.wordR m) rY) m) (hb : L.BlkOk m)
    {u : ThreadId} (hu : u < m.threads.size) : L.Off (L.own G m u).heap.erase :=
  LockWord.off_erase.mpr fun l hl => ho.part_off hu (by
    simp only [FHeap.union_apply]
    cases e : (L.wordR m).heap l with
    | none => exact absurd e (LockWord.wordR_some hb hl)
    | some c => simp)

/-- **The free lock's resource owns no cell of the rest it lacks**: a byte the rest holds as a cell
is no share (`FOwned.rest_noShare`), so `rL` owns it only as its own cell. -/
theorem rest_owned_off {own : ThreadId → Res} {rL rX : Res} {m : Mem}
    (ho : FOwned own (rsum (L.wordR m) (rsum rL rX)) m) {l : Zig.Loc}
    (hl : (rsum (L.wordR m) (rsum rL rX)).heap l ≠ none) (hL : rL.heap l = none) :
    rL.owned l = none :=
  Classical.byContradiction fun hn => (Res.owned_ne.mp hn).elim (· hL) fun hp =>
    ho.rest_noShare hl (by
      simp only [rsum, Ghost.add_share]
      exact SCell.pos_add_iff.mpr (.inr (SCell.pos_add_iff.mpr (.inl hp))))

/-- The free lock's resource, off the word's cells, owns no byte of the word. -/
theorem off_owned {own : ThreadId → Res} {rL rX : Res} {m : Mem}
    (ho : FOwned own (rsum (L.wordR m) (rsum rL rX)) m) (hb : L.BlkOk m)
    (hL : L.Off rL.heap.erase) : L.Off rL.owned := fun x h1 h2 =>
  rest_owned_off ho (by
      simp only [rsum, FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
      exact fun h => absurd h (LockWord.wordR_some hb ⟨rfl, h1, h2⟩))
    (LockWord.off_erase.mp hL _ ⟨rfl, h1, h2⟩)

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
    (hidle : ∀ u, (L.ph (G' u)).held = false → L.held (G' u) = rnil)
    (hres : ∀ u, (L.ph (G' u)).held = true → L.R G' (L.held (G' u))) : L.Inv G' rX m' := by
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  have hbl : L.b < m.blocks.size := by
    obtain ⟨blk, hb, -⟩ := hi.w.blk; exact (Array.getElem?_eq_some_iff.mp hb).1
  refine ⟨hw, ⟨rL, hown ▸ rest_step ho hs hi.w.blk hLoff hi.xoff, hLoff, hLX, fun hF' => ?_,
    fun hnF' => hnF (fun h => hnF' (hfree.mpr h))⟩, hi.xoff, hpd, hidle, hres⟩
  obtain ⟨h1, h2⟩ := hF (hfree.mp hF')
  exact ⟨hR rL h1, h2.step hs (off_owned ho hi.w.blk hLoff) hbl hg⟩

/-- A step of the lock's code by `t`, not the holder, to a place `p` that does not hold the lock
(`p.held = false`). -/
theorem Inv.lstepAt {G : ThreadId → γ} {rX : Res} {m m' : Mem} {t : ThreadId} {p : LPh}
    (hi : L.Inv G rX m) (hs : L.Step t m m') (hnh : (L.ph (G t)).held = false)
    (hng : L.ph (G t) ≠ .gone) (hp : p.held = false) (hw : L.WInv (upd (L.pl G) t p) m') :
    L.Inv (upd G t (L.set (G t) p rnil)) rX m' := by
  obtain ⟨-, hjt⟩ := hi.ht hng
  have hjb : joinedB m' = joinedB m := LockWord.joinedB_congr hs.threads
  have hheld : L.held (G t) = rnil := hi.idle t hnh
  have hphu : ∀ u, L.ph (upd G t (L.set (G t) p rnil) u) = if u = t then p else L.ph (G u) := by
    intro u; unfold upd; split
    · exact L.ph_set _ _ _
    · rfl
  have hholds : ∀ u, (L.ph (upd G t (L.set (G t) p rnil) u)).held = true ↔
      (L.ph (G u)).held = true := by
    intro u; rw [hphu]; split
    · rename_i h; subst h; rw [hp, hnh]
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
      have := (hholds u).mp hu; rw [e, hnh] at this; cases this
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

/-- **An acquire**: `t` takes the free lock; the resource, the free one before the step
(`FreeRes`), moves from the rest into its part. -/
theorem Inv.acq {G : ThreadId → γ} {rX : Res} {m m' : Mem} {t : ThreadId}
    (hi : L.Inv G rX m) (hs : L.Step t m m') (hnh : (L.ph (G t)).held = false)
    (hng : L.ph (G t) ≠ .gone) (hF : L.Free G) (hacq : L.Acq (L.pl G) t m m')
    (hw : L.WInv (upd (L.pl G) t .holds) m') (hgat : L.NoGather G m t) :
    ∃ rL, L.FreeRes G rX m rL ∧ L.Inv (upd G t (L.set (G t) .holds rL)) rX m' := by
  obtain ⟨rL, hfr⟩ := hi.rest
  obtain ⟨ho, hLoff, hLX, hFr, -⟩ := id hfr
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
  have hown : m'.OwnsRes t (rsum (L.own G m t) rL) :=
    (ho'.owns t ht').gather (hacq.ownsRes hLown (off_owned ho hi.w.blk hLoff)) (hgat rL hR)
  have ho2 := ho'.take ht' hdA hown
  have hpt : L.pl (upd G t (L.set (G t) .holds rL)) = upd (L.pl G) t .holds := pl_upd_set G t _ _
  have hphu : ∀ u, L.ph (upd G t (L.set (G t) .holds rL) u) = if u = t then .holds else L.ph (G u) := by
    intro u; unfold upd; split
    · exact L.ph_set _ _ _
    · rfl
  refine ⟨rL, hfr, by rw [hpt]; exact hw, ⟨rnil, ?_, LockWord.off_erase.mpr fun _ _ => rfl,
    FHeap.Disjoint.symm (FHeap.disjoint_empty _), fun hF' => (by
      have h := hF'.held t; unfold pl at h; rw [hphu, if_pos rfl] at h; cases h),
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
    · rename_i h; subst h; rw [hphu, if_pos rfl] at hu; cases hu
    · rename_i h; rw [hphu, if_neg h] at hu; exact hi.idle u hu
  · rw [hphu] at hu
    split at hu
    · rename_i h; subst h; rw [upd_self, L.held_set, L.R_set]; exact hR
    · exact (hF u hu).elim

/-- **A release**: the holder `t` goes to `p`; its resource moves from its part into the rest, as
the free one after the step (`FreeRes`). -/
theorem Inv.rel {G : ThreadId → γ} {rX : Res} {m m' : Mem} {t : ThreadId} {p : LPh}
    (hi : L.Inv G rX m) (hs : L.Step t m m') (hph : L.ph (G t) = .holds) (hp : p.held = false)
    (hrel : L.Rel t (upd (L.pl G) t p) m m') (hw : L.WInv (upd (L.pl G) t p) m') :
    L.FreeRes (upd G t (L.set (G t) p rnil)) rX m' (L.held (G t)) ∧
      L.Inv (upd G t (L.set (G t) p rnil)) rX m' := by
  obtain ⟨rL, ho, -, -, -, hnF⟩ := hi.rest
  have hph₁ : (L.ph (G t)).held = true := LPh.held_of_holds hph
  have hnF' : ¬ L.Free G := fun h => h t hph₁
  rw [hnF hnF', rnil_rsum] at ho
  obtain ⟨ht, hjt⟩ := hi.ht (by rw [hph]; decide)
  have hjb : joinedB m' = joinedB m := LockWord.joinedB_congr hs.threads
  have honly : ∀ u, (L.ph (G u)).held = true → u = t := fun u hu => hi.w.one u t hu hph₁
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
  have hnh₀ : ∀ u, u ≠ t → (L.ph (G u)).held = false := fun u h => by
    cases hu : (L.ph (G u)).held
    · rfl
    · exact absurd (honly u hu) h
  have hnh : ∀ u, (L.ph (upd G t (L.set (G t) p rnil) u)).held = false := by
    intro u; rw [hphu]; split
    · exact hp
    · rename_i h; exact hnh₀ u h
  have hown : m.OwnsRes t (L.held (G t)) := by
    have := ho.owns t ht; rw [hsplit] at this; exact this.sepR rfl rfl
  have hHoff' : L.Off (L.held (G t)).owned := fun x h1 h2 => by
    have := ho.part_off_owned ht (l := (L.b, x)) (by
      simp only [rsum, FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
      exact fun h => absurd h (LockWord.wordR_some hi.w.blk ⟨rfl, h1, h2⟩))
    rw [hsplit] at this
    exact Classical.byContradiction fun hn => (Res.owned_sep rfl rfl).mpr (.inr hn) this
  have hfr : L.FreeRes (upd G t (L.set (G t) p rnil)) rX m' (L.held (G t)) :=
    ⟨by rw [own_upd hjb hjt, L.part_set, L.held_set, rsum_rnil]; exact ho2, hHoff, hHX,
      fun _ => ⟨by rw [L.R_set]; exact hi.res t hph₁, by rw [hpt]; exact hrel.ownsRes hown hHoff'⟩,
      fun h => absurd (LockWord.Free.of_held hnh) h⟩
  refine ⟨hfr, by rw [hpt]; exact hw, ⟨_, hfr⟩, hi.xoff, fun u => ?_, fun u _ => ?_,
    fun u hu => by rw [hnh u] at hu; cases hu⟩
  · unfold upd; split
    · rw [L.held_set]; exact FHeap.disjoint_empty _
    · exact hi.pdisj u
  · unfold upd; split
    · exact L.held_set _ _ _
    · rename_i h; exact hi.idle u (hnh₀ u h)

/-! ## Steps outside the lock's code -/

/-- A change of thread `t`'s ghost value outside the lock's code: `t` is `out` before, and `out`,
`gone` or `away` after; it keeps its part and holds nothing. -/
theorem Inv.ghost {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} {g : γ}
    (hi : L.Inv G rX m) (hph : L.ph (G t) = .out)
    (hg : L.ph g = .out ∨ L.ph g = .gone ∨ L.ph g = .away)
    (hpart : L.part g = L.part (G t)) (hheld : L.held g = rnil)
    (hlive : L.ph g ≠ .gone → t < m.threads.size ∧ joinedB m t = false)
    (hRk : ∀ r, L.R G r → L.R (upd G t g) r) : L.Inv (upd G t g) rX m := by
  have hnh : (L.ph (G t)).held = false := by rw [hph]; rfl
  have hgh : (L.ph g).held = false := by rcases hg with h | h | h <;> rw [h] <;> rfl
  have hown : L.own (upd G t g) m = L.own G m := by
    funext u; unfold FLock.own
    by_cases h : u = t
    · subst h; rw [upd_self, hpart, hheld, hi.idle u hnh]
    · rw [upd_ne _ _ h]
  have hphu : ∀ u, L.ph (upd G t g u) = if u = t then L.ph g else L.ph (G u) := fun u => by
    unfold upd; split <;> rfl
  have hholds : ∀ u, (L.ph (upd G t g u)).held = true ↔ (L.ph (G u)).held = true := by
    intro u; rw [hphu]; split
    · rename_i h; subst h; rw [hgh, hnh]
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
      have := (hholds u).mp hu; rw [e, hnh] at this; cases this
    rw [upd_ne _ _ hut]; exact hRk _ (hi.res u ((hholds u).mp hu))

/-- A new split of a thread's complete resource at the same lock phase. Equality of `Res`
preserves bytes, knowledge and ghost state together. A holder re-establishes the protected
assertion on its new held part; otherwise every protected assertion is preserved. -/
theorem Inv.repartition {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} {g : γ}
    (hi : L.Inv G rX m) (hph : L.ph g = L.ph (G t))
    (hsum : rsum (L.part g) (L.held g) = rsum (L.part (G t)) (L.held (G t)))
    (hdisj : FHeap.Disjoint (L.part g).heap (L.held g).heap)
    (hidle : (L.ph g).held = false → L.held g = rnil)
    (hRk : (L.ph (G t)).held = false → ∀ r, L.R G r → L.R (upd G t g) r)
    (hres : (L.ph g).held = true → L.R (upd G t g) (L.held g)) :
    L.Inv (upd G t g) rX m := by
  have hphu : ∀ u, L.ph (upd G t g u) = L.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hph]
    · rw [upd_ne _ _ e]
  have hpl : L.pl (upd G t g) = L.pl G := funext hphu
  have hown : L.own (upd G t g) m = L.own G m := by
    funext u; unfold FLock.own
    by_cases e : u = t
    · subst e; rw [upd_self, hsum]
    · rw [upd_ne _ _ e]
  have hfree : L.Free (upd G t g) ↔ L.Free G := by unfold FLock.Free; rw [hpl]
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  refine ⟨by rw [hpl]; exact hi.w, ⟨rL, by rw [hown]; exact ho, hLoff, hLX, fun hF' => ?_,
    fun h => hnF (fun h' => h (hfree.mpr h'))⟩, hi.xoff, fun u => ?_, fun u hu => ?_,
    fun u hu => ?_⟩
  · obtain ⟨h1, h2⟩ := hF (hfree.mp hF')
    exact ⟨hRk ((hfree.mp hF').held t) rL h1, by rw [hpl]; exact h2⟩
  · by_cases e : u = t
    · subst e; rw [upd_self]; exact hdisj
    · rw [upd_ne _ _ e]; exact hi.pdisj u
  · rw [hphu] at hu
    by_cases e : u = t
    · subst e; rw [upd_self]; exact hidle (by rw [hph]; exact hu)
    · rw [upd_ne _ _ e]; exact hi.idle u hu
  · rw [hphu] at hu
    by_cases e : u = t
    · subst e; rw [upd_self]; exact hres (by rw [hph]; exact hu)
    · rw [upd_ne _ _ e]
      exact hRk (hi.w.held_false_of_ne hu e) _ (hi.res u hu)

/-- Take one complete resource from protocol rest into this caller's part at the same
mutex phase. The free/held lock resource, all other callers, memory and phase map stay.
This uses actual clock ownership, without requiring this caller to hold the mutex. -/
theorem Inv.takeRest {G : ThreadId → γ} {rA rX : Res} {m : Mem} {t : ThreadId}
    (hi : L.Inv G (rsum rA rX) m) (hg : L.ph (G t) ≠ .gone)
    (hd : FHeap.Disjoint rA.heap rX.heap) (howns : m.Owns t rA.owned) :
    L.Inv (upd G t (L.setPart (G t) (rsum (L.part (G t)) rA))) rX m := by
  obtain ⟨ht, hjt⟩ := hi.ht hg
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  have hoff : ∀ l, L.In l → rA.heap l = none ∧ rX.heap l = none := by
    intro l hl
    have h := LockWord.off_erase.mp hi.xoff l hl
    simpa only [rsum, FHeap.union_apply, Option.or_eq_none_iff] using h
  have hWA : FHeap.Disjoint (L.wordR m).heap rA.heap := fun l => by
    by_cases hl : L.In l
    · exact .inr (hoff l hl).1
    · exact .inl (cellsAt_none hl)
  have hLA := (FHeap.disjoint_union_right.mp hLX).1
  have hLX' := (FHeap.disjoint_union_right.mp hLX).2
  have he : rsum (L.wordR m) (rsum rL (rsum rA rX)) =
      rsum rA (rsum (L.wordR m) (rsum rL rX)) := by
    rw [← rsum_assoc (a := rL), rsum_comm hLA, rsum_assoc,
      ← rsum_assoc (a := L.wordR m), rsum_comm hWA, rsum_assoc]
  rw [he] at ho
  have hAR : FHeap.Disjoint rA.heap (rsum (L.wordR m) (rsum rL rX)).heap :=
    FHeap.disjoint_union_right.mpr ⟨hWA.symm,
      FHeap.disjoint_union_right.mpr ⟨hLA.symm, hd⟩⟩
  have hTA : FHeap.Disjoint (L.own G m t).heap rA.heap := fun l => by
    cases ha : rA.heap l with
    | none => exact .inr rfl
    | some fc => exact .inl (ho.part_off ht (by simp [FHeap.union_apply, ha]))
  have hHA : FHeap.Disjoint (L.held (G t)).heap rA.heap := by
    rw [own_live hjt] at hTA
    exact (FHeap.disjoint_union_left.mp hTA).2
  have ho' := ho.take ht hAR ((ho.owns t ht).addOwns howns)
  let g := L.setPart (G t) (rsum (L.part (G t)) rA)
  let G' := upd G t g
  have hpl : L.pl G' = L.pl G := by
    change L.pl (upd G t (L.setPart (G t) _)) = L.pl G
    rw [pl_upd, L.ph_setPart]
    exact upd_same (L.pl G) t
  have hph : ∀ u, L.ph (G' u) = L.ph (G u) := fun u => congrFun hpl u
  have hfree : L.Free G' ↔ L.Free G := by unfold FLock.Free; rw [hpl]
  have hpart : rsum (L.part g) (L.held g) = rsum (L.own G m t) rA := by
    dsimp [g]
    rw [L.part_setPart, L.held_setPart, own_live hjt, rsum_assoc,
      rsum_comm hHA.symm, ← rsum_assoc]
  have hown : L.own G' m = upd (L.own G m) t (rsum (L.own G m t) rA) := by
    rw [own_upd rfl hjt, hpart]
  have hheld : ∀ u, L.held (G' u) = L.held (G u) := by
    intro u
    by_cases h : u = t
    · subst u
      change L.held (upd G t g t) = L.held (G t)
      rw [upd_self]
      exact L.held_setPart _ _
    · exact congrArg L.held (upd_ne _ _ h)
  refine ⟨by rw [hpl]; exact hi.w,
    ⟨rL, by rw [hown]; exact ho', hLoff, hLX', ?_, ?_⟩,
    LockWord.off_erase.mpr (fun l hl => (hoff l hl).2), ?_, ?_, ?_⟩
  · intro hf
    obtain ⟨hR, hO⟩ := hF (hfree.mp hf)
    exact ⟨(L.R_setPart G t _ rL).mpr hR, by rw [hpl]; exact hO⟩
  · intro hf
    exact hnF (fun h => hf (hfree.mpr h))
  · intro u
    by_cases h : u = t
    · subst u
      simp only [upd_self, L.part_setPart, L.held_setPart]
      exact FHeap.disjoint_union_left.mpr ⟨hi.pdisj t, hHA.symm⟩
    · simpa only [G', upd_ne _ _ h] using hi.pdisj u
  · intro u hu
    rw [hheld u]
    exact hi.idle u (by rw [← hph u]; exact hu)
  · intro u hu
    rw [hheld u]
    exact (L.R_setPart G t _ _).mpr (hi.res u (by rw [← hph u]; exact hu))

/-- Publish one complete caller-owned resource into protocol rest while retaining the
caller's mutex phase and complete held resource. No mutex release or Free is required. -/
theorem Inv.giveRest {G : ThreadId → γ} {rP rA rX : Res} {m : Mem} {t : ThreadId}
    (hi : L.Inv G rX m) (hg : L.ph (G t) ≠ .gone)
    (hpart : L.part (G t) = rsum rP rA) (hd : FHeap.Disjoint rP.heap rA.heap) :
    L.Inv (upd G t (L.setPart (G t) rP)) (rsum rA rX) m := by
  obtain ⟨ht, hjt⟩ := hi.ht hg
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  have hp := hi.pdisj t
  rw [hpart] at hp
  obtain ⟨hPH, hAH⟩ := FHeap.disjoint_union_left.mp hp
  have hAR : FHeap.Disjoint rA.heap (rsum (L.wordR m) (rsum rL rX)).heap := fun l => by
    cases he : (rsum (L.wordR m) (rsum rL rX)).heap l with
    | none => exact .inr rfl
    | some fc =>
      have hp := ho.part_off ht (by rw [he]; simp)
      rw [own_live hjt, hpart] at hp
      simp only [FHeap.union_apply, Option.or_eq_none_iff] at hp
      exact .inl hp.1.2
  have hAW := (FHeap.disjoint_union_right.mp hAR).1
  have hAL := (FHeap.disjoint_union_right.mp
    (FHeap.disjoint_union_right.mp hAR).2).1
  have hAoff : ∀ l, L.In l → rA.heap l = none := fun l hl =>
    (hAW l).resolve_right (LockWord.wordR_some hi.w.blk hl)
  have hsplit : L.own G m t = rsum (rsum rP (L.held (G t))) rA := by
    rw [own_live hjt, hpart, rsum_assoc, rsum_comm hAH, ← rsum_assoc]
  have ho' := ho.give ht hsplit (FHeap.disjoint_union_left.mpr ⟨hd, hAH.symm⟩)
  have he : rsum (L.wordR m) (rsum rL (rsum rA rX)) =
      rsum rA (rsum (L.wordR m) (rsum rL rX)) := by
    rw [← rsum_assoc (a := rL), rsum_comm hAL.symm, rsum_assoc,
      ← rsum_assoc (a := L.wordR m), rsum_comm hAW.symm, rsum_assoc]
  rw [← he] at ho'
  let g := L.setPart (G t) rP
  let G' := upd G t g
  have hpl : L.pl G' = L.pl G := by
    change L.pl (upd G t (L.setPart (G t) _)) = L.pl G
    rw [pl_upd, L.ph_setPart]
    exact upd_same (L.pl G) t
  have hph : ∀ u, L.ph (G' u) = L.ph (G u) := fun u => congrFun hpl u
  have hfree : L.Free G' ↔ L.Free G := by unfold FLock.Free; rw [hpl]
  have hown : L.own G' m = upd (L.own G m) t (rsum rP (L.held (G t))) := by
    rw [own_upd rfl hjt]
    simp only [g, L.part_setPart, L.held_setPart]
  have hheld : ∀ u, L.held (G' u) = L.held (G u) := by
    intro u
    by_cases h : u = t
    · subst u
      change L.held (upd G t g t) = L.held (G t)
      rw [upd_self]
      exact L.held_setPart _ _
    · exact congrArg L.held (upd_ne _ _ h)
  refine ⟨by rw [hpl]; exact hi.w,
    ⟨rL, by rw [hown]; exact ho', hLoff,
      FHeap.disjoint_union_right.mpr ⟨hAL.symm, hLX⟩, ?_, ?_⟩,
    LockWord.off_erase.mpr (fun l hl => by
      simp only [FHeap.union_apply, Option.or_eq_none_iff]
      exact ⟨hAoff l hl, LockWord.off_erase.mp hi.xoff l hl⟩), ?_, ?_, ?_⟩
  · intro hf
    obtain ⟨hR, hO⟩ := hF (hfree.mp hf)
    exact ⟨(L.R_setPart G t rP rL).mpr hR, by rw [hpl]; exact hO⟩
  · intro hf
    exact hnF (fun h => hf (hfree.mpr h))
  · intro u
    by_cases h : u = t
    · subst u
      simpa only [G', upd_self, g, L.part_setPart, L.held_setPart] using hPH
    · simpa only [G', upd_ne _ _ h] using hi.pdisj u
  · intro u hu
    rw [hheld u]
    exact hi.idle u (by rw [← hph u]; exact hu)
  · intro u hu
    rw [hheld u]
    exact (L.R_setPart G t rP _).mpr (hi.res u (by rw [← hph u]; exact hu))

/-- A change of thread `t`'s ghost value that keeps its place, its part and its resource in the
lock (a step of `t` in another sync object's code, also while it holds the lock). -/
theorem Inv.relabel {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} {g : γ}
    (hi : L.Inv G rX m) (hph : L.ph g = L.ph (G t)) (hpart : L.part g = L.part (G t))
    (hheld : L.held g = L.held (G t)) (hRk : ∀ r, L.R G r → L.R (upd G t g) r) :
    L.Inv (upd G t g) rX m := by
  exact hi.repartition hph (by rw [hpart, hheld]) (by rw [hpart, hheld]; exact hi.pdisj t)
    (fun hn => hheld.trans (hi.idle t (hph ▸ hn))) (fun _ => hRk)
    (fun hh => by rw [hheld]; exact hRk _ (hi.res t (hph ▸ hh)))

/-- The invariant reconstruction shared by ordinary and cur-aware local steps. The native
step protects the ACTUAL rest footprint, and its actual post ownership supplies the new part.
No execution rule or resource mode is assumed by this pure reconstruction. -/
private theorem Inv.rebuildPartStep {G : ThreadId → γ} {rX rL r' : Res} {m m' : Mem}
    {t : ThreadId} {g : γ} (hi : L.Inv G rX m) (hjt : joinedB m t = false)
    (hLoff : L.Off rL.heap.erase) (hLX : FHeap.Disjoint rL.heap rX.heap)
    (hF : L.Free G → L.R G rL ∧ L.toLockWord.OwnsRes (L.pl G) m rL)
    (hnF : ¬ L.Free G → rL = rnil)
    (ho' : FOwned (upd (L.own G m) t r') (rsum (L.wordR m) (rsum rL rX)) m')
    (hs : FStepIn (rsum (L.wordR m) (rsum rL rX)).owned m m' (rsum (L.wordR m) (rsum rL rX)).shared)
    (hph : L.ph g = L.ph (G t)) (hr' : rsum (L.part g) (L.held g) = r')
    (hpd : FHeap.Disjoint (L.part g).heap (L.held g).heap)
    (hidle : (L.ph g).held = false → L.held g = rnil)
    (hRk : (L.ph (G t)).held = false → ∀ r, L.R G r → L.R (upd G t g) r)
    (hres : (L.ph g).held = true → L.R (upd G t g) (L.held g)) :
    L.Inv (upd G t g) rX m' := by
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
      (rsum (L.wordR m) (rsum rL rX)).owned (L.b, x) ≠ none := by
    intro x h1 h2
    have := LockWord.wordR_some hi.w.blk (l := (L.b, x)) ⟨rfl, h1, h2⟩
    exact Res.owned_of_heap (by
      simp only [rsum, FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
      intro h; exact absurd h this)
  -- the word's bytes are the rest's cells, so no read share
  have hwR : ∀ x, L.o ≤ x → x < L.o + 4 →
      (rsum (L.wordR m) (rsum rL rX)).shared (L.b, x) = none := by
    intro x h1 h2
    have := LockWord.wordR_some hi.w.blk (l := (L.b, x)) ⟨rfl, h1, h2⟩
    exact Res.excl_shared_disj (Res.excl_of_heap (by
      simp only [rsum, FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
      intro h; exact absurd h this))
  have hplg : L.pl (upd G t g) = L.pl G := by
    rw [pl_upd, hph]; funext u; unfold upd pl; split
    · rename_i e; subst e; rfl
    · rfl
  have hphu : ∀ u, L.ph (upd G t g u) = L.ph (G u) := fun u => by
    have := congrFun hplg u; exact this
  have hholds : ∀ u, (L.ph (upd G t g u)).held = true ↔ (L.ph (G u)).held = true := fun u => by
    rw [hphu]
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
  refine ⟨by rw [hplg]; exact hi.w.stepIn hs hwF hwR hcells, ⟨rL, ?_, hLoff, hLX, fun hF' => ?_,
    fun h => hnF (fun h' => h (hfree.mpr h'))⟩, hi.xoff, fun u => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rw [own_upd hjb hjt, hr']; exact ho2
  · obtain ⟨h1, h2⟩ := hF (hfree.mp hF')
    have htn : (L.ph (G t)).held = false := (hfree.mp hF').held t
    have hsub : ∀ l, rL.owned l ≠ none → (rsum (L.wordR m) (rsum rL rX)).owned l ≠ none :=
      fun _ hl => (Res.owned_sep rfl rfl).mpr (.inr ((Res.owned_sep rfl rfl).mpr (.inl hl)))
    refine ⟨hRk htn rL h1, ?_⟩
    rw [hplg]
    exact h2.stepIn hs hsub hwF (fun i l hl => (hi.w.loc.ok i l hl).1) fun l hl =>
      Res.excl_shared_disj (Res.excl_sep rfl rfl (.inr (Res.excl_sep rfl rfl (.inl hl))))
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
      exact hRk (hi.w.held_false_of_ne hu hut) _ (hi.res u hu)

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
        FHeap.Disjoint (L.part g).heap (L.held g).heap → ((L.ph g).held = false → L.held g = rnil) →
        ((L.ph (G t)).held = false → ∀ r, L.R G r → L.R (upd G t g) r) →
        ((L.ph g).held = true → L.R (upd G t g) (L.held g)) → L.Inv (upd G t g) rX m') →
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
  refine WP.liftMem_fownedR htt ho hc ht (by rw [own_live hjt]; exact hp) ?_ hret
  intro a m' r' hr ho' hq hs
  have hsX : FStepIn (rsum (L.wordR m) rX).heap.erase m m' := by
    refine hs.cells.weaken fun l hl => ?_
    simp only [FHeap.erase, Option.map_eq_none_iff, ne_eq, rsum, FHeap.union_apply,
      Option.or_eq_none_iff, not_and] at hl ⊢
    intro h1 _; exact hl h1
  exact h a m' r' hr hq hsX (hs.current.trans hc)
    (fun g hph hr' hpd hidle hRk hres =>
      hi.rebuildPartStep hjt hLoff hLX hF hnF ho' hs hph hr' hpd hidle hRk hres)

/-- A local step with `cur t` supplied only for the step. The actual-rest cur-aware rule
returns its exact protected footprint; the SAME invariant reconstruction handles its post. -/
theorem Inv.wp_liftMemCur {Tgt α : Type} {P : Proto Tgt γ} {x : MemM α} {Pa : FAssn}
    {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop} {G G₀ : ThreadId → γ}
    {rX : Res} {m : Mem} {n : Nat} {t : ThreadId}
    (hi : L.Inv G rX m) (hc : m.current = t) (ht : t < m.threads.size) (hjt : joinedB m t = false)
    (htt : FTTriple (Pa ⋆ cur t) x (fun a => Qa a ⋆ cur t))
    (hp : Pa (rsum (L.part (G t)) (L.held (G t))))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → Qa a r' →
      FStepIn (rsum (L.wordR m) rX).heap.erase m m' → m'.current = t →
      (∀ g, L.ph g = L.ph (G t) → rsum (L.part g) (L.held g) = r' →
        FHeap.Disjoint (L.part g).heap (L.held g).heap → ((L.ph g).held = false → L.held g = rnil) →
        ((L.ph (G t)).held = false → ∀ r, L.R G r → L.R (upd G t g) r) →
        ((L.ph g).held = true → L.R (upd G t g) (L.held g)) → L.Inv (upd G t g) rX m') →
      Q a G₀ m' n)
    (hret : P.Partial ∨ FTTReturns (Pa ⋆ cur t) x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G₀ m n := by
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  refine WP.liftMem_fownedCurR htt ho hc ht (by rw [own_live hjt]; exact hp) ?_ hret
  intro a m' r' hr ho' hq hs
  have hsX : FStepIn (rsum (L.wordR m) rX).heap.erase m m' := by
    refine hs.cells.weaken fun l hl => ?_
    simp only [FHeap.erase, Option.map_eq_none_iff, ne_eq, rsum, FHeap.union_apply,
      Option.or_eq_none_iff, not_and] at hl ⊢
    intro h1 _; exact hl h1
  exact h a m' r' hr hq hsX (hs.current.trans hc)
    (fun g hph hr' hpd hidle hRk hres =>
      hi.rebuildPartStep hjt hLoff hLX hF hnF ho' hs hph hr' hpd hidle hRk hres)

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
        FHeap.Disjoint (L.part g).heap (L.held g).heap → ((L.ph g).held = false → L.held g = rnil) →
        ((L.ph (G t)).held = false → ∀ r, L.R G r → L.R (upd G t g) r) →
        ((L.ph g).held = true → L.R (upd G t g) (L.held g)) → L.Inv (upd G t g) rX m') →
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

/-- Finish a caller-only step while keeping the complete held resource. Both ordinary and
cur-aware lifting use this same ghost/resource reconstruction. -/
private theorem Inv.finishPartStep {G : ThreadId → γ} {g : γ} {rX r : Res} {m m' : Mem}
    {t : ThreadId} (hi : L.Inv (upd G t g) rX m)
    (hd : FHeap.Disjoint r.heap (L.held g).heap)
    (hk : ∀ g', L.ph g' = L.ph (upd G t g t) →
      rsum (L.part g') (L.held g') = rsum r (L.held g) →
      FHeap.Disjoint (L.part g').heap (L.held g').heap →
      ((L.ph g').held = false → L.held g' = rnil) →
      ((L.ph (upd G t g t)).held = false → ∀ r', L.R (upd G t g) r' →
        L.R (upd (upd G t g) t g') r') →
      ((L.ph g').held = true → L.R (upd (upd G t g) t g') (L.held g')) →
      L.Inv (upd (upd G t g) t g') rX m') :
    L.Inv (upd G t (L.setPart g r)) rX m' := by
  have hR : ∀ r', L.R (upd G t g) r' →
      L.R (upd (upd G t g) t (L.setPart g r)) r' := fun r' hr => by
    have := (L.R_setPart (upd G t g) t r r').mpr hr
    rwa [upd_self] at this
  have := hk (L.setPart g r) (by rw [L.ph_setPart, upd_self])
    (by rw [L.part_setPart, L.held_setPart])
    (by rw [L.part_setPart, L.held_setPart]; exact hd)
    (fun e => by
      rw [L.ph_setPart] at e; rw [L.held_setPart]
      have := hi.idle t (by rw [upd_self]; exact e); rwa [upd_self] at this)
    (fun _ => hR)
    (fun e => by
      rw [L.ph_setPart] at e; rw [L.held_setPart]
      have := hi.res t (by rw [upd_self]; exact e); rw [upd_self] at this; exact hR _ this)
  rwa [upd_upd] at this

/-- **A step of any live thread on its own part**, including inside composite sync code. The
whole held resource is framed, and the caller part becomes the thread triple's actual post. -/
theorem Inv.wp_liftPartLive {Tgt α : Type} {P : Proto Tgt γ} {x : MemM α} {Pa : FAssn}
    {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop} {G G₀ : ThreadId → γ}
    {rX : Res} {m : Mem} {n : Nat} {t : ThreadId} {g : γ}
    (hi : L.Inv (upd G t g) rX m) (hc : m.current = t) (hgo : L.ph g ≠ .gone)
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
    rw [upd_self]; exact hgo
  obtain ⟨ht, hjt⟩ := hi.ht hgn
  have hd : FHeap.Disjoint (L.part g).heap (L.held g).heap := by
    have := hi.pdisj t; rwa [upd_self] at this
  refine hi.wp_liftMem hc ht hjt (htt.frame (R := (· = L.held g)))
    (by rw [upd_self]; exact ⟨_, _, hd, rfl, hp, rfl⟩)
    (fun a m' r'' hr hq hs hc' hk => ?_)
    (hret.imp_right fun hr => (FTTotalTriple.frame (R := (· = L.held g)) ⟨htt, hr⟩).2)
  obtain ⟨r', rH, hd', rfl, hq', rfl⟩ := hq
  refine h a m' r' hr hq' hs hc' ?_
  exact hi.finishPartStep hd' hk

/-- A cur-aware step on the caller's part, at any live internal or public phase. The token
is provided only for this local step; the WHOLE held resource and actual rest remain framed. -/
theorem Inv.wp_liftPartLiveCur {Tgt α : Type} {P : Proto Tgt γ} {x : MemM α} {Pa : FAssn}
    {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop} {G G₀ : ThreadId → γ}
    {rX : Res} {m : Mem} {n : Nat} {t : ThreadId} {g : γ}
    (hi : L.Inv (upd G t g) rX m) (hc : m.current = t) (hgo : L.ph g ≠ .gone)
    (htt : FTTriple (Pa ⋆ cur t) x (fun a => Qa a ⋆ cur t)) (hp : Pa (L.part g))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → Qa a r' →
      FStepIn (rsum (L.wordR m) rX).heap.erase m m' →
      m'.current = t → L.Inv (upd G t (L.setPart g r')) rX m' → Q a G₀ m' n)
    (hret : P.Partial ∨ FTTReturns (Pa ⋆ cur t) x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G₀ m n := by
  have hgn : L.ph (upd G t g t) ≠ .gone := by
    rw [upd_self]; exact hgo
  obtain ⟨ht, hjt⟩ := hi.ht hgn
  have hd : FHeap.Disjoint (L.part g).heap (L.held g).heap := by
    have := hi.pdisj t; rwa [upd_self] at this
  have httF : FTTriple ((Pa ⋆ (· = L.held g)) ⋆ cur t) x
      (fun a => (Qa a ⋆ (· = L.held g)) ⋆ cur t) :=
    (htt.frame (R := (· = L.held g))).conseq
      (fun _ h => sep_assoc' (sep_mono_right (fun _ => sep_comm) (sep_assoc h)))
      (fun _ _ h => sep_assoc' (sep_mono_right (fun _ => sep_comm) (sep_assoc h)))
  have hretF : P.Partial ∨ FTTReturns ((Pa ⋆ (· = L.held g)) ⋆ cur t) x := by
    refine hret.imp_right fun hr => ?_
    have htF : FTTotalTriple ((Pa ⋆ (· = L.held g)) ⋆ cur t) x
        (fun a => (Qa a ⋆ (· = L.held g)) ⋆ cur t) :=
      (FTTotalTriple.frame (R := (· = L.held g)) ⟨htt, hr⟩).conseq
        (fun _ h => sep_assoc' (sep_mono_right (fun _ => sep_comm) (sep_assoc h)))
        (fun _ _ h => sep_assoc' (sep_mono_right (fun _ => sep_comm) (sep_assoc h)))
    exact htF.2
  refine hi.wp_liftMemCur hc ht hjt httF
    (by rw [upd_self]; exact ⟨_, _, hd, rfl, hp, rfl⟩)
    (fun a m' r'' hr hq hs hc' hk => ?_) hretF
  obtain ⟨r', rH, hd', rfl, hq', rfl⟩ := hq
  exact h a m' r' hr hq' hs hc' (hi.finishPartStep hd' hk)

/-- A same-memory caller-part update, derived from the total rule for `pure`. This is the
resource operation used to retain, duplicate or drop plain fragments at initialization, spawn
and join boundaries. The whole held resource and every other thread remain framed. -/
theorem Inv.eupdPart {Tgt : Type} (P : Proto Tgt γ) {G : ThreadId → γ} {g : γ}
    {rX : Res} {m : Mem} {t : ThreadId} {Qa : FAssn}
    (hi : L.Inv (upd G t g) rX m) (hc : m.current = t) (hg : L.ph g ≠ .gone)
    (hu : EUpd (fun r => r = L.part g) Qa) :
    ∃ r, Qa r ∧ L.Inv (upd G t (L.setPart g r)) rX m := by
  have htt : FTTotalTriple (fun r => r = L.part g) (pure () : MemM Unit) (fun _ => Qa) :=
    .ofSeq (FTotalTriple.eupd hu (FTotalTriple.ret (Q := fun _ : Unit => Qa) ())) (ThreadLocal.pure ())
  have hw : P.WP t (ConcM.liftMem (pure () : MemM Unit) : ConcM Tgt Unit)
      (fun _ _ _ _ => ∃ r, Qa r ∧ L.Inv (upd G t (L.setPart g r)) rX m) G m 0 :=
    hi.wp_liftPartLive hc hg htt.1 rfl (fun _ m' r hr hq _ _ hi' => by
      have hm : m' = m :=
        (Prod.mk.inj (Except.ok.inj (Option.some.inj hr))).2.symm
      exact ⟨r, hq, hm ▸ hi'⟩) (.inr htt.2)
  change m.threads.size = m.threads.size ∧
    (∃ r, Qa r ∧ L.Inv (upd G t (L.setPart g r)) rX m) at hw
  exact hw.2

/-- A caller-part step at a public lock place. The general rule also covers the live internal
phases of composite sync code; both frame the holder's complete resource. -/
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
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G₀ m n :=
  hi.wp_liftPartLive hc (by rcases hgo with h | h <;> rw [h] <;> decide) htt hp h hret

/-- The cur-aware caller-part lift at the public lock places. -/
theorem Inv.wp_liftPartCur {Tgt α : Type} {P : Proto Tgt γ} {x : MemM α} {Pa : FAssn}
    {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop} {G G₀ : ThreadId → γ}
    {rX : Res} {m : Mem} {n : Nat} {t : ThreadId} {g : γ}
    (hi : L.Inv (upd G t g) rX m) (hc : m.current = t) (hgo : L.ph g = .out ∨ L.ph g = .holds)
    (htt : FTTriple (Pa ⋆ cur t) x (fun a => Qa a ⋆ cur t)) (hp : Pa (L.part g))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → Qa a r' →
      FStepIn (rsum (L.wordR m) rX).heap.erase m m' →
      m'.current = t → L.Inv (upd G t (L.setPart g r')) rX m' → Q a G₀ m' n)
    (hret : P.Partial ∨ FTTReturns (Pa ⋆ cur t) x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G₀ m n :=
  hi.wp_liftPartLiveCur hc (by rcases hgo with h | h <;> rw [h] <;> decide) htt hp h hret

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
  have hphu : ∀ u, (L.ph (upd (upd G m.threads.size g₀) t g₁ u)).held = true ↔
      (L.ph (G u)).held = true := by
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
    exact ⟨hRk rL h1, by rw [hpl]; exact ⟨hown _ _ h2.1, hown _ _ h2.2⟩⟩
  · unfold upd
    by_cases h1 : u = t
    · simp only [h1, ↓reduceIte, h₁h]; exact FHeap.disjoint_empty _
    · by_cases h2 : u = m.threads.size
      · simp only [h1, h2, hct, ↓reduceIte, h₀h]; exact FHeap.disjoint_empty _
      · simp only [h1, h2, ↓reduceIte]; exact hi.pdisj u
  · replace hu := held_false_of_iff (hphu u) hu; unfold upd
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
    (hgh : L.held g = rnil) (hRk : ∀ r, L.R G r → L.R (upd G t g) r)
    (hgat : ∀ l, (L.own G m t).shared l = none ∨ (L.own G m u).shared l = none := by
      intro l; exact .inl ((Res.excl_eq_erase).2 l)) :
    L.Inv (upd G t g) rX m' := by
  obtain ⟨ht, hjt⟩ := hi.ht (by rw [hout]; decide)
  have hheld : L.held (G t) = rnil := hi.idle t (by rw [hout]; decide)
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  have ho' := ho.join ht hut hj hgat
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
  have hholds : ∀ w, (L.ph (upd G t g w)).held = true ↔ (L.ph (G w)).held = true := fun w => by
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
    exact ⟨hRk rL h1, by rw [hpl]; exact ⟨hown _ _ h2.1, hown _ _ h2.2⟩⟩
  · unfold upd; split
    · rw [hgh]; exact FHeap.disjoint_empty _
    · exact hi.pdisj w
  · replace hw' := held_false_of_iff (hholds w) hw'; unfold upd; split
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
  have hfree : L.Free G := LockWord.Free.of_held fun u => by
    show (L.ph (G u)).held = false; rcases hph u with ⟨h, -⟩ | h <;> rw [h] <;> rfl
  have hownE : L.own G m = upd own t (L.part (G t)) := by
    funext u; unfold upd
    by_cases hu : u = t
    · subst hu; simp [own_live hjt, hheld, rsum_rnil]
    · simp only [hu, ↓reduceIte]; exact hown u hu
  -- `t` owns the word and the resource: every access to them happened before every thread
  have htown := ho.owns t ht
  rw [hsplit] at htown
  -- every access to the exclusive bytes of `rL ⋆ rW`, every write to its shared bytes
  have hle : ∀ (h : Heap),
      (∀ l, h l ≠ none → (rsum (L.part (G t)) (rsum rL rW)).excl l ≠ none) →
      ∀ e ∈ m.footprint, (e.Touches h ∨ m.blocks.size ≤ e.block) →
        ∀ u < m.threads.size, VClock.le e.clock (m.clocks[u]!) = true :=
    fun h hs e he htc u hu => VClock.le_trans (htown.1.sub hs e he htc) (hall u hu)
  have hleR : ∀ (h : Heap), (∀ l, h l ≠ none → (rsum rL rW).owned l ≠ none) →
      ∀ e ∈ m.footprint, e.kind.isWrite = true → (e.Touches h ∨ m.blocks.size ≤ e.block) →
        ∀ u < m.threads.size, VClock.le e.clock (m.clocks[u]!) = true :=
    fun h hs e he hwr htc u hu => VClock.le_trans
      (htown.ownsR.sub (fun l hl => (Res.owned_sep rfl rfl).mpr (.inr (hs l hl))) e he hwr htc)
      (hall u hu)
  have hW' : ∀ l, rW.heap.erase l ≠ none → (rsum (L.part (G t)) (rsum rL rW)).excl l ≠ none :=
    fun _ hl => Res.excl_sep rfl rfl (.inr (Res.excl_sep rfl rfl (.inr (Res.excl_of_heap
      fun e => hl (by simp [FHeap.erase, e])))))
  have hLx : ∀ l, rL.excl l ≠ none → (rsum (L.part (G t)) (rsum rL rW)).excl l ≠ none :=
    fun _ hl => Res.excl_sep rfl rfl (.inr (Res.excl_sep rfl rfl (.inl hl)))
  have hLs : ∀ l, rL.shared l ≠ none → (rsum rL rW).owned l ≠ none := fun _ hl =>
    (Res.owned_sep rfl rfl).mpr (.inl (Res.owned_of_shared hl))
  have hw : L.WInv (L.pl G) m :=
    LockWord.WInv.make (ho.csize) (fun u => hph u) hblk h0 hat hq fun e he hh u hu _ =>
      hle rW.heap.erase hW' e he (.inl (LockWord.touches_word hh fun x h1 h2 => by
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
  refine ⟨hw, ⟨rL, ?_, hLoff, hLX, fun _ => ⟨hR, fun e he _ htc => .inl fun u hu _ =>
      hle rL.excl hLx e he htc u hu, fun e he hwr htc => .inl fun u hu _ =>
      hleR rL.shared hLs e he (hwr rfl) htc u hu⟩, fun h => absurd hfree h⟩, hxoff,
    fun u => by rw [hheld]; exact FHeap.disjoint_empty _, fun u _ => hheld u,
    fun u hu => (hfree u hu).elim⟩
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
    (hall : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m.clocks[t]!) = true)
    (hgat : L.NoGather G m t) :
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
  -- what the free lock owns (may read), `t` owns (may read): it is above every thread
  have hlk : ∀ (h : Heap) (w : Bool), L.toLockWord.Owns (L.pl G) m h w →
      LockWord.OwnsW w m (m.clocks[t]!) h := fun h w ho' e he hw htc => by
    rcases ho' e he hw htc with h | ⟨i, l, hl, hle⟩
    · exact VClock.le_trans (h t ht hg) (VClock.le_refl _)
    · obtain ⟨⟨v, hv, hle'⟩, -⟩ := hi.w.rel i l hl
      exact VClock.le_trans hle (VClock.le_trans hle' (hall v hv))
  -- the word has no share
  have hsh : ∀ l, rL.shared l = none → (rsum rL (L.wordR m)).shared l = none := fun l h =>
    Classical.byContradiction fun hn => by
      obtain ⟨h1, h2, h3⟩ := Res.shared_ne.mp hn
      have hg : (rsum rL (L.wordR m)).gh = rL.gh := Ghost.add_unit _
      rw [hg] at h2 h3
      simp only [rsum, FHeap.union_apply, Option.or_eq_none_iff] at h1
      exact Res.shared_ne.mpr ⟨h1.1, h2, h3⟩ h
  refine ⟨rL, hR, ⟨_, _, hT, rfl, rfl, _, _, hWL.symm, rfl, rfl, rfl⟩,
    ho.take ht (FHeap.disjoint_union_left.mpr ⟨hLX, hWX⟩) ((ho.owns t ht).gather
      (Mem.OwnsRes.gather ⟨LockWord.ownsW_false.mp (hlk _ _ hLown.1),
        LockWord.ownsW_true.mp (hlk _ _ hLown.2)⟩ (.of_owns ?_)
        fun l => .inr ((Res.excl_eq_erase).2 l))
      fun l => (hgat rL hR l).imp id (hsh l))⟩
  · intro e he htc
    rcases htc with ⟨x, h1, h2, h3⟩ | hb
    · have hin : L.In (e.block, x) := Classical.byContradiction fun hn =>
        h3 (cellsAt_owned_none hn)
      obtain ⟨hb, hx1, hx2⟩ := hin
      rcases hi.w.wfp e he ⟨hb, x, h1, h2, hx1, hx2⟩ with ⟨-, v, hv, hle⟩ | h
      · exact VClock.le_trans hle (hall v hv)
      · exact h t ht hg
    · -- an access to a block that does not exist yet happened before `t`: `t` owns its part
      exact (ho.owns t ht).1 e he (.inr hb)

/-! ## A recorded access to bytes of the protocol's rest -/

/-- A recorded access of the current thread `t` to bytes that no thread's part has (`hno`), given
the word's invariant after it (`hw`) and what the free lock owns after it (`hown`): the invariant
holds after it. -/
theorem Inv.record {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} {b : BlockId}
    {o n : Nat} {k : AccessKind} (hi : L.Inv G rX m) (hc : m.current = t)
    (ht : t < m.threads.size) (hb : b < m.blocks.size)
    (hw : L.WInv (L.pl G) (m.recordAt b o n k))
    (hno : ∀ u < m.threads.size, ∀ x, o ≤ x → x < o + n → (L.own G m u).owned (b, x) = none)
    (hown : ∀ rL : Res, (∀ l, rX.heap l ≠ none → rL.owned l = none) →
      L.OwnsRes (L.pl G) m rL → L.OwnsRes (L.pl G) (m.recordAt b o n k) rL) :
    L.Inv G rX (m.recordAt b o n k) := by
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  have hLX' : ∀ l, rX.heap l ≠ none → rL.owned l = none := fun l hl =>
    rest_owned_off ho (by
        simp only [rsum, FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
        exact fun _ _ h => absurd h hl)
      ((hLX l).resolve_right hl)
  refine ⟨hw, ⟨rL, ?_, hLoff, hLX, fun hF' => ?_, hnF⟩, hi.xoff, hi.pdisj, hi.idle, hi.res⟩
  · have : L.wordR (m.recordAt b o n k) = L.wordR m := wordR_congr rfl
    rw [this]
    have e : L.own G (m.recordAt b o n k) = L.own G m := rfl
    rw [e]
    exact ho.recordRest hc ht hb (fun u hu x h1 h2 => Classical.byContradiction fun hn =>
      Res.owned_of_excl hn (hno u hu x h1 h2)) fun _ => hno
  · obtain ⟨h1, h2⟩ := hF hF'
    exact ⟨h1, hown rL hLX' h2⟩

/-- A recorded access of the current thread `t` (not a write) to `n` bytes of the protocol's own
rest `rX` (a read of a read-shared buffer): the invariant holds after it. -/
theorem Inv.recordX {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} {b : BlockId}
    {o n : Nat} {k : AccessKind} (hi : L.Inv G rX m) (hk : k ≠ .write) (hc : m.current = t)
    (ht : t < m.threads.size) (hb : b < m.blocks.size) (hn : 0 < n)
    (hX : ∀ x, o ≤ x → x < o + n → rX.heap (b, x) ≠ none) :
    L.Inv G rX (m.recordAt b o n k) := by
  obtain ⟨rL, ho, -⟩ := hi.rest
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
  exact hi.record hc ht hb (hi.w.readK hk hnw)
    (fun u hu x h1 h2 => ho.part_off_owned hu (hrest x h1 h2))
    fun _ hLX' h2 => ⟨h2.1.readK hb fun x h1 h2 => Classical.byContradiction fun hn =>
        Res.owned_of_excl hn (hLX' _ (hX x h1 h2)),
      h2.2.readK hb fun x h1 h2 => Classical.byContradiction fun hn =>
        Res.owned_of_shared hn (hLX' _ (hX x h1 h2))⟩

/-- A plain read by the current thread `t`, when every other thread has left the lock (`gone`), of
bytes that no thread's part has (`hno`; e.g. bytes of the protocol's rest, the word's cells and the
free lock's resource): the invariant holds after it. -/
theorem Inv.recordAll {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} {b : BlockId}
    {o n : Nat} (hi : L.Inv G rX m) (hc : m.current = t) (ht : t < m.threads.size)
    (hb : b < m.blocks.size) (hsole : ∀ u < m.threads.size, u ≠ t → L.ph (G u) = .gone)
    (hno : ∀ u < m.threads.size, ∀ x, o ≤ x → x < o + n → (L.own G m u).owned (b, x) = none) :
    L.Inv G rX (m.recordAt b o n .read) := by
  have hs : ∀ u < m.threads.size, u ≠ m.current → L.pl G u = .gone := fun u hu h =>
    hsole u hu (by rw [← hc]; exact h)
  exact hi.record hc ht hb (hi.w.readAll (by rw [hc]; exact ht) hs) hno
    fun _ _ h2 => ⟨h2.1.readAll (by rw [hi.w.csize, hc]; exact ht) hs,
      h2.2.readAll (by rw [hi.w.csize, hc]; exact ht) hs⟩

/-! ## Happened before the lock's holder

A clock that a client of the lock relates to the lock's holders (`HB`): a write made while
holding the lock happened before every later holder (`HB.le`), and the fact stays over the steps
that keep the holders, the word's releases and the threads (`HB.mono`). -/

variable (L) in
/-- The clock `c` happened before the lock's holder (awake or at another object's futex wait:
`held`, so the fact survives `WInv.nap`), before the release clock of the newest message of the
lock's word, or before every thread that has not ended. -/
def HB (G : ThreadId → γ) (m : Mem) (c : VClock) : Prop :=
  (∃ u, (L.ph (G u)).held = true ∧ VClock.le c (m.clocks[u]!) = true) ∨ L.Before m c ∨
    LockWord.LiveLe (L.pl G) m c

/-- A clock that happened before the lock's holder `t` (with the word's invariant). -/
theorem HB.le {G : ThreadId → γ} {m : Mem} {c : VClock} (hw : L.WInv (L.pl G) m)
    (h : L.HB G m c) {t : ThreadId} (ht : (L.ph (G t)).held = true) :
    VClock.le c (m.clocks[t]!) = true := by
  rcases h with ⟨u, hu, hle⟩ | ⟨i, l, hl, hle⟩ | hlive
  · obtain rfl := hw.one u t hu ht; exact hle
  · exact VClock.le_trans hle ((hw.rel i l hl).2 t ht)
  · exact hlive t (hw.live t (LPh.ne_gone_of_held ht)).1 (LPh.ne_gone_of_held ht)

/-- The word's releases stay over a step that has the lock's word in its frame. -/
theorem Inv.before_fstep {G : ThreadId → γ} {rX : Res} {m m' : Mem} (hL : L.Inv G rX m)
    (hfs : FStepIn (rsum (L.wordR m) rX).heap.erase m m') :
    ∀ c, L.Before m c → L.Before m' c := by
  rintro c ⟨i, l, hl, hle⟩
  obtain ⟨i', hl'⟩ := (LockWord.loc_fstep (L := L.toLockWord) hfs
    (fun x h1 h2 => by
      have := LockWord.wordR_some hL.w.blk (L := L.toLockWord) (l := (L.b, x)) ⟨rfl, h1, h2⟩
      simp only [FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
        Option.or_eq_none_iff, not_and]
      intro h; exact absurd h this)
    (fun i l hl => (hL.w.loc.ok i l hl).1) l).mpr ⟨i, hl⟩
  exact ⟨i', l, hl', hle⟩

/-- **`HB` stays** over a step that keeps the holders (or releases with the release fact), grows
the clocks, keeps the word's newest release and the threads that have not ended. -/
theorem HB.mono {G G' : ThreadId → γ} {m m' : Mem} {c : VClock} (h : L.HB G m c)
    (hhold : ∀ u, (L.ph (G u)).held = true → (L.ph (G' u)).held = true ∨
      ∀ c, VClock.le c (m.clocks[u]!) = true → L.Before m' c)
    (hcl : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hbef : ∀ c, L.Before m c → L.Before m' c) (ht : m'.threads = m.threads)
    (hgone : ∀ u, L.ph (G' u) ≠ .gone → L.ph (G u) ≠ .gone) : L.HB G' m' c := by
  rcases h with ⟨u, hu, hle⟩ | hb | hlive
  · rcases hhold u hu with h' | hrel
    · exact .inl ⟨u, h', VClock.le_trans hle (hcl u)⟩
    · exact .inr (.inl (hrel c hle))
  · exact .inr (.inl (hbef c hb))
  · exact .inr (.inr (fun u hu hg =>
      VClock.le_trans (hlive u (ht ▸ hu) (hgone u hg)) (hcl u)))

/-- A clock that happened before thread `t`, which holds the lock. -/
theorem HB.of_holder {G : ThreadId → γ} {m : Mem} {c : VClock} {t : ThreadId}
    (ht : (L.ph (G t)).held = true) (hle : VClock.le c (m.clocks[t]!) = true) : L.HB G m c :=
  .inl ⟨t, ht, hle⟩

/-- **A holder over a step of the lock's code** by `t` (which runs the lock's code, so it is not
at `holdsAway`) to any place `q` (`Fits.stable`): it still holds, or (at a release: `t` held the
lock and `q` is not `holds`) its clock happened before the newest message of the word (`hrel`).
The `hhold` of `HB.mono`. -/
theorem lstep_hold {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {q : LPh} {h : Res}
    (hz : L.ph (G t) ≠ .holdsAway)
    (hrel : L.ph (G t) = .holds → q ≠ .holds → L.Before m' (m.clocks[t]!)) (u : ThreadId)
    (hu : (L.ph (G u)).held = true) : (L.ph (upd G t (L.set (G t) q h) u)).held = true ∨
      ∀ c, VClock.le c (m.clocks[u]!) = true → L.Before m' c := by
  by_cases e : u = t
  · subst e
    by_cases hq : q = .holds
    · exact .inl (by rw [upd_self, L.ph_set, hq]; rfl)
    · exact .inr fun c hc => L.before_le (hrel (LPh.holds_of_held hu hz) hq) hc
  · exact .inl (by rw [upd_ne _ _ e]; exact hu)

/-- **A thread that has not ended over a step of the lock's code** by `t` (not `gone`) to any
place: it had not ended before it. The `hgone` of `HB.mono`. -/
theorem lstep_live {G : ThreadId → γ} {t : ThreadId} {q : LPh} {h : Res}
    (hg : L.ph (G t) ≠ .gone) (u : ThreadId) (hu : L.ph (upd G t (L.set (G t) q h) u) ≠ .gone) :
    L.ph (G u) ≠ .gone := by
  by_cases e : u = t
  · subst e; exact hg
  · rwa [upd_ne _ _ e] at hu

/-- **`HB` stays over a step of the lock's code** by `t` to any place `q` (`Fits.stable`):
`lstep_hold`, `lstep_live`. -/
theorem HB.lstep {G : ThreadId → γ} {m m' : Mem} {c : VClock} {t : ThreadId} {q : LPh} {h : Res}
    (hc : L.HB G m c) (hg : L.ph (G t) ≠ .gone) (hz : L.ph (G t) ≠ .holdsAway) (hs : L.Step t m m')
    (hrel : L.ph (G t) = .holds → q ≠ .holds → L.Before m' (m.clocks[t]!)) :
    L.HB (upd G t (L.set (G t) q h)) m' c :=
  hc.mono (lstep_hold hz hrel) hs.clocks hs.before hs.threads (lstep_live hg)

end FLock

end Full
end Zig
