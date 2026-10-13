import Proofs.Handoff.Layout
import ZigLean.Sep.Full.Cond
import ZigLean.Sep.Full.Mutex
import ZigLean.Sep.Full.ThreadFacts
import ZigLean.Conc.Share

/-!
# The protocol of `handoff`, once for every version

`handoff` (`Proofs/Handoff/Layout.lean`): `main` spawns a producer, locks the mutex and waits on
the condition until `ready`, reads `v`, unlocks, waits on the event and joins the producer. The
producer locks the mutex, stores `v = 7` and `ready = true`, unlocks, signals the condition and
sets the event. This file is the protocol of that program for every layout (`Layout`) and every
implementation of the three sync objects (`MutexImpl`, `CondImpl`, `EventImpl`): the program's
proof uses only their contracts, and each version's file walks `main` and the producer of its
generated code with the steps here.

- **Ghost values** (`Gh = FLG × X`): the lock's part (`FLG`), and `X`: the thread's place in the
  program (`Ph`), its place in the condition's code (`CPh`) and in the event's (`EPh`). `main`
  is `run` for the whole loop of the condition (the condition's place says where it is inside
  `wait`), and `ev` in the event's `wait`.
- **The lock** (`L`, `FLock.prod`): the mutex owns `v` and `ready`, whose values follow from the
  producer's place (`vOf`, `rdyOf`).
- **The condition** (`C`) and **the event** (`E`): their words are in the protocol's rest (with
  `io` for 0.16.0: read-shared); their invariants (`FCond.Inv`, `FEvent.Inv`) are part of `U`.
  Only the producer in its `signal` signals (`FCond.sx`); only `main` waits at the event
  (`FEvent.wx`).
- **The rest `U`**: the threads (`Shape`), and what the contracts' client premises need: the
  epoch has its first write only, which `main` made, until the producer signals (`ep1`, `ep0`:
  `hhb`); while `main` is in the condition's critical code the producer is before its lock
  (`ent`: `hent`, and from it `hone`); `main`'s registration happened before the producer
  (`reg`: `hseen`, through the mutex's release and acquire); after the producer's signal a
  registered `main` is signalled (`lvc`), and after its end the event is set (`fin`): `hlive`.
-/

namespace Zig
namespace Handoff

open Conc Conc.Proto Full Full.FAssn

/-- Where a thread is in the program (module doc). -/
inductive Ph where
  | none
  /-- `main` before its spawn. -/
  | pre
  /-- `main` from its spawn to its unlock (the condition's loop). -/
  | run
  /-- `main` after its unlock, in the event's `wait`. -/
  | ev
  /-- `main` at its join. -/
  | joins
  /-- The producer before (or in) its lock. -/
  | lk
  /-- The producer holds the mutex. -/
  | hl
  /-- The producer stored `v = 7`. -/
  | v7
  /-- The producer stored `ready = true` (until it signals). -/
  | rdy
  /-- The producer in `signal`. -/
  | sg
  /-- The producer in the event's `set`. -/
  | st
  /-- The producer at its end. -/
  | fin
  deriving DecidableEq

namespace Ph

/-- `main`'s places. -/
def isMain : Ph → Bool
  | .pre | .run | .ev | .joins => true
  | _ => false

/-- The producer's places. -/
def isProd : Ph → Bool
  | .lk | .hl | .v7 | .rdy | .sg | .st | .fin => true
  | _ => false

/-- The producer stored `v`. -/
def hasV : Ph → Bool
  | .v7 | .rdy | .sg | .st | .fin => true
  | _ => false

/-- The producer stored `ready`. -/
def hasR : Ph → Bool
  | .rdy | .sg | .st | .fin => true
  | _ => false

/-- The producer is in or after its `signal`. -/
def sigd : Ph → Bool
  | .sg | .st | .fin => true
  | _ => false

end Ph

/-- A thread's places (module doc). -/
structure X where
  ph : Ph := .none
  c : CPh := .out
  e : EPh := .out

abbrev Gh := FLG × X

variable (Lo : Layout)

/-- `v`, from the producer's place. -/
def vOf (x : X) : Nat := if x.ph.hasV then 7 else 0

/-- The mutex's resource: `v` and `ready`, from the producer's place. -/
def R (Y : ThreadId → X) : FAssn :=
  up (pts (bPtr.add Lo.xo) 4 (BitVec.ofNat 32 (vOf (Y 1)))) ⋆
    up (pts (bPtr.add Lo.ro) 1 (Y 1).ph.hasR)

/-- The mutex. -/
abbrev L : FLock Gh := FLock.prod 0 Lo.mo (R Lo) Lo.c Lo.c_ok

/-- The condition: its place is `X.c`; the producer signals. -/
def C : FCond Gh where
  S := Lo.WS
  Ep := Lo.WE
  ep_b := rfl
  ep_o := rfl
  ph g := g.2.c
  set g p := (g.1, { g.2 with c := p })
  ph_set _ _ := rfl
  set_set _ _ _ := rfl
  set_self _ := rfl
  sx g := g.2.ph = .sg
  sx_set _ _ := Iff.rfl

/-- The event: its place is `X.e`; `main` waits (from its event wait on), the producer sets. -/
def E : FEvent Gh where
  W := Lo.WV
  ph g := g.2.e
  set g p := (g.1, { g.2 with e := p })
  ph_set _ _ := rfl
  set_set _ _ _ := rfl
  set_self _ := rfl
  wx g := g.2.ph = .ev ∨ g.2.ph = .joins
  wx_set _ _ := Iff.rfl
  sx g := g.2.ph = .st
  sx_set _ _ := Iff.rfl

/-- The threads that run the lock's code: out of the condition's busy code and of the event's
code, and not the producer while it holds the mutex (`Full/Cond.lean`, `CPh.busy`). -/
def ok (g : Gh) : Prop :=
  (g.2.c).busy = false ∧ g.2.e = .out ∧ g.2.ph ≠ .hl ∧ g.2.ph ≠ .v7

/-- The accesses to the bytes of `io` (`0 .. io` of the `Box`). -/
def IoR (e : FootprintEntry) : Prop := e.block = 0 ∧ e.off < Lo.io

/-- The bytes of `io` and the `Box`'s full extent, in the protocol's rest. The extent pins the
block (its size and kind) for every thread's step, so the cells of the shared words in the rest
are the memory's at every stop (`Rest`, `Word.InRest`). -/
def IoRest (r : Res) : Prop :=
  ∃ A bs, A % Lo.align = 0 ∧ bs.size = Lo.io ∧
    (up (bytesAt bPtr A Lo.size .stack bs) ⋆ bext 0 Lo.size .stack) r

/-- The protocol's rest `rX`: the cells of the condition's and the event's words, and `io`. -/
def Rest (rX : Res) (m : Mem) : Prop :=
  ∃ rIO, IoRest Lo rIO ∧ (∀ l, Lo.BoxW l → rIO.heap l = none) ∧
    rX = rsum (cellsAt Lo.BoxW m) rIO

/-- Block 0 is the live `Box`, `size` bytes on the stack. -/
def BlkOk (m : Mem) : Prop :=
  ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true ∧ blk.bytes.size = Lo.size ∧ blk.kind = .stack

/-- The threads: `main` alone before its spawn; then `main` and the producer, which `main`
spawned and did not join yet. -/
def Shape (Y : ThreadId → X) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧
  ((m.threads.size = 1 ∧ Y 0 = { ph := .pre } ∧ ∀ u, 1 ≤ u → Y u = {}) ∨
   (m.threads.size = 2 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
    (Y 0).ph.isMain ∧ (Y 0).ph ≠ .pre ∧ (Y 1).ph.isProd ∧ ∀ u, 2 ≤ u → Y u = {}))

/-- The rest of the invariant (module doc). -/
structure U (G : ThreadId → Gh) (rX : Res) (m : Mem) : Prop where
  shape : Shape (fun u => (G u).2) m
  io : ReadShared (IoR Lo) m
  rest : Rest Lo rX m
  blk : BlkOk Lo m
  ws : Lo.WS.Ok m
  we : Lo.WE.Ok m
  wv : Lo.WV.Ok m
  cinv : (C Lo).Inv (L Lo) G m
  einv : (E Lo).Inv (L Lo) G m
  /-- The producer does not wait at the condition. -/
  places : ((G 1).2.c).waits = false
  /-- Until the producer signals, the epoch has its first write, which `main` made. -/
  ep1 : (G 1).2.ph.sigd = false → (Lo.WE.hist m).size = 1
  ep0 : VClock.le (Lo.WE.hist m)[0]!.clock (m.clocks[0]!) = true
  /-- `main` in the condition's critical code: the producer is before its lock. -/
  ent : ((G 0).2.c).crit → (G 1).2.ph = .lk
  /-- The producer holds the mutex between its lock and its store of `ready`. -/
  hold : (G 1).2.ph = .hl ∨ (G 1).2.ph = .v7 → (G 1).1.ph = .holds
  /-- `main`'s registration happened before the producer, or before the mutex's release while
  the producer is before its lock. -/
  reg : ∀ i jr sn e, (G 0).2.c = .reg i jr sn e →
    VClock.le (Lo.WS.hist m)[jr]!.clock (m.clocks[1]!) = true ∨
    ((G 1).2.ph = .lk ∧ (((G 0).1.ph = .holds ∧
      VClock.le (Lo.WS.hist m)[jr]!.clock (m.clocks[0]!) = true) ∨
      (L Lo).Before m (Lo.WS.hist m)[jr]!.clock))
  /-- After the producer's signal, a registered `main` is signalled. -/
  lvc : ((G 0).2.c).waits → (G 1).2.ph = .st ∨ (G 1).2.ph = .fin → (C Lo).Signalled m
  /-- After the producer's end, the event is set. -/
  fin : (G 1).2.ph = .fin → (E Lo).IsSet m
  /-- A thread waits only at the mutex, the epoch or the event. -/
  q : ∀ w ∈ m.waiters, w.2 = (L Lo).ptr ∨ w.2 = Lo.WE.ptr ∨ w.2 = Lo.WV.ptr
  /-- A thread in the condition's code is `main` in its loop or the producer in `signal`. -/
  xc : ∀ u, (G u).2.c ≠ .out → (G u).2.ph = .run ∨ (G u).2.ph = .sg

variable {Tgt : Type}

/-- The protocol, in strict mode; `prodOf` reads the producer's argument from a spawn target. -/
def proto (prodOf : Tgt → Option Ptr) : Proto Tgt Gh where
  inv G m := ∃ rX, (L Lo).Inv G rX m ∧ U Lo G rX m
  init tgt g := prodOf tgt = some bPtr ∧ g = (⟨.out, rnil, rnil⟩, { ph := .lk })
  fin g := g.1.ph = .gone ∧ g.2 = { ph := .fin }
  strict := true
  joins g := g.1.ph = .out ∧ g.2 = { ph := .joins }

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 7 ∧ joinedAll 0 m

/-! ## The rest: the shared words' cells -/

theorem res_eq {a b : Res} (hh : a.heap = b.heap) (hk : a.know = b.know) (hg : a.gh = b.gh) :
    a = b := by
  cases a; cases b; simp only at hh hk hg; subst hh hk hg; rfl

variable {Lo}

/-- A word of the three in the rest: its cells and the others. -/
theorem Rest.split {rX : Res} {m : Mem} {W : Word 32 4} (hW : ∀ l, W.In l → Lo.BoxW l)
    (h : Rest Lo rX m) : ∃ rY, rX = rsum (W.cellsR m) rY ∧ ∀ l, W.In l → rY.heap l = none := by
  obtain ⟨rIO, -, hIO, rfl⟩ := h
  refine ⟨rsum (cellsAt (fun l => Lo.BoxW l ∧ ¬ W.In l) m) rIO, res_eq ?_ ?_ ?_, fun l hl => ?_⟩
  · funext l
    simp only [FHeap.union_apply, Word.cellsR]
    by_cases hw : W.In l
    · rw [cellsAt_of hw, cellsAt_of (hW l hw), cellsAt_none (fun h => h.2 hw), hIO l (hW l hw)]
      simp
    · rw [cellsAt_none hw]
      by_cases hb : Lo.BoxW l
      · rw [cellsAt_of hb, cellsAt_of (W := fun l => Lo.BoxW l ∧ ¬ W.In l) ⟨hb, hw⟩]; simp
      · rw [cellsAt_none hb, cellsAt_none (W := fun l => Lo.BoxW l ∧ ¬ W.In l) (fun h => hb h.1)]
        simp
  · simp [cellsAt, Word.cellsR, Know.none_union]
  · simp [cellsAt, Word.cellsR]
  · simp only [FHeap.union_apply]
    rw [cellsAt_none (W := fun l => Lo.BoxW l ∧ ¬ W.In l) (fun h => h.2 hl), hIO l (hW l hl)]; rfl

/-- After a step that changes only the bytes of the word `W` among the three (the others' cells
stay), the rest has `W`'s new cells. -/
theorem Rest.step {rX rY : Res} {m m' : Mem} {W : Word 32 4} (hW : ∀ l, W.In l → Lo.BoxW l)
    (h : Rest Lo rX m) (hX : rX = rsum (W.cellsR m) rY) (hY : ∀ l, W.In l → rY.heap l = none)
    (hm : ∀ l, Lo.BoxW l → ¬ W.In l → m'.heap l = m.heap l) :
    Rest Lo (rsum (W.cellsR m') rY) m' := by
  obtain ⟨rIO, hR, hIO, rfl⟩ := h
  have hk : rY.know = rIO.know := by
    have := congrArg Res.know hX; simpa [cellsAt, Word.cellsR, Know.none_union] using this.symm
  have hg : rY.gh = rIO.gh := by
    have := congrArg Res.gh hX; simpa [cellsAt, Word.cellsR] using this.symm
  refine ⟨rIO, hR, hIO, res_eq ?_ ?_ ?_⟩
  · funext l
    have hl := congrFun (congrArg Res.heap hX) l
    simp only [FHeap.union_apply, Word.cellsR] at hl ⊢
    by_cases hw : W.In l
    · rw [cellsAt_of hw, cellsAt_of (hW l hw), hY l hw, hIO l (hW l hw)]
    · rw [cellsAt_none hw, Option.none_or] at hl ⊢
      rw [← hl]
      by_cases hb : Lo.BoxW l
      · rw [cellsAt_of hb, cellsAt_of hb, hm l hb hw]
      · rw [cellsAt_none hb, cellsAt_none hb]
  · simp [cellsAt, Word.cellsR, Know.none_union, hk]
  · simp [cellsAt, Word.cellsR, hg]

/-- A step that keeps the cells of the three words keeps the rest. -/
theorem Rest.congr {rX : Res} {m m' : Mem} (h : Rest Lo rX m)
    (hm : ∀ l, Lo.BoxW l → m'.heap l = m.heap l) : Rest Lo rX m' := by
  obtain ⟨rIO, hR, hIO, rfl⟩ := h
  refine ⟨rIO, hR, hIO, res_eq ?_ rfl rfl⟩
  funext l
  simp only [FHeap.union_apply]
  by_cases hb : Lo.BoxW l
  · rw [cellsAt_of hb, cellsAt_of hb, hm l hb]
  · rw [cellsAt_none hb, cellsAt_none hb]

/-- **The `Box` is block 0**: live, `size` bytes on the stack (the extent in the rest). -/
theorem blk_of {G : ThreadId → Gh} {rX : Res} {m m₀ : Mem} (hi : (L Lo).Inv G rX m)
    (hr : Rest Lo rX m₀) : ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true ∧
      blk.bytes.size = Lo.size ∧ blk.kind = .stack := by
  obtain ⟨rL, ho, -⟩ := hi.rest
  obtain ⟨rT, -, hh⟩ := ho.holds
  have he := hh.swap.extTrue
  obtain ⟨rIO, ⟨A, bs, -, -, r₁, r₂, -, rfl, -, h2⟩, -, rfl⟩ := hr
  simp only [rsum] at he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [bauth_eq h2] at he
  obtain ⟨blk, h1, h2, h3, h4, -⟩ := (he 0).1 Lo.size .stack (by simp [Ghost.atExt, ECell.auth1])
  exact ⟨blk, h1, h2, h3, h4⟩

theorem heap_blk {m : Mem} {blk : Block} (hb : m.blocks[0]? = some blk) (hl : blk.live = true)
    (hk : blk.kind = .stack) {x : Nat} (hx : x < blk.bytes.size) :
    m.heap (0, x) = some ⟨blk.bytes[x], blk.addr, blk.bytes.size, blk.kind⟩ := by
  simp [Mem.heap, hb, hl, hx, hk, BlockKind.mappedLo]

/-- **A step that keeps the rest keeps the shared words' cells**: the lock's invariant after it
has them up to `Cell.norm`, and the extent in the rest pins the block. -/
theorem cells_same {G' : ThreadId → Gh} {rX : Res} {m m' : Mem} (hbk : BlkOk Lo m)
    (hi' : (L Lo).Inv G' rX m') (hr : Rest Lo rX m) : ∀ l, Lo.BoxW l → m'.heap l = m.heap l := by
  rintro ⟨b, x⟩ hl
  obtain ⟨h0, h1, h2⟩ := hl
  simp only at h0 h1 h2; subst h0
  obtain ⟨blk, hb, hlv, hs, hk⟩ := hbk
  obtain ⟨blk', hb', hlv', hs', hk'⟩ := blk_of hi' hr
  have hx : x < Lo.size := by have := Lo.ok; omega
  have e := heap_blk hb hlv hk (by omega : x < blk.bytes.size)
  have e' := heap_blk hb' hlv' hk' (by omega : x < blk'.bytes.size)
  have hrc := hi'.restCell (l := (0, x)) (fc := ⟨⟨blk.bytes[x], blk.addr, blk.bytes.size, blk.kind⟩, none⟩) (by
    obtain ⟨rIO, -, hIO, rfl⟩ := hr
    have hB : Lo.BoxW (0, x) := ⟨rfl, h1, h2⟩
    simp only [FHeap.union_apply, cellsAt_of hB, e, hIO (0, x) hB]
    rfl)
  rw [e', e]
  rw [e'] at hrc
  simp only [Option.map_some, Option.some.injEq, Cell.norm, Cell.mk.injEq] at hrc
  obtain ⟨hby, had, -⟩ := hrc
  simp only [Option.some.injEq, Cell.mk.injEq]
  exact ⟨hby, had, by omega, by rw [hk, hk']⟩

/-! ## The protocol has the lock -/

theorem apS : Lo.WS.ApartL (L Lo).toLockWord := .inr (.inl (by have := Lo.ok; simp [Layout.WS, L, FLock.prod]; omega))
theorem apE : Lo.WE.ApartL (L Lo).toLockWord := .inr (.inl (by have := Lo.ok; simp [Layout.WE, L, FLock.prod]; omega))
theorem apV : Lo.WV.ApartL (L Lo).toLockWord := .inr (.inl (by have := Lo.ok; simp [Layout.WV, L, FLock.prod]; omega))

/-- A byte of the three words is not the mutex's. -/
theorem box_notL {l : Zig.Loc} (h : Lo.BoxW l) : ¬ (L Lo).In l := fun ⟨_, h2, h3⟩ => by
  have := Lo.ok; obtain ⟨-, h5, -⟩ := h; simp [L, FLock.prod] at h2 h3; omega

/-- The access `e` of the mutex's word is not to `io`. -/
theorem io_notL {e : FootprintEntry} (h : e.off = (L Lo).o) : ¬ IoR Lo e := fun ⟨_, h2⟩ => by
  have := Lo.ok; simp [L, FLock.prod] at h; omega

/-- A step of the lock's code keeps the `Box`: it writes at most the mutex's bytes. -/
theorem BlkOk.lstep {t : ThreadId} {m m' : Mem} (hb : BlkOk Lo m) (hs : (L Lo).Step t m m') :
    BlkOk Lo m' := by
  obtain ⟨blk, hb, hl, hsz, hk⟩ := hb
  rcases hs.blocks with e | ⟨blk', bs, h1, -, h3, h4, h5⟩
  · exact ⟨blk, by rw [e]; exact hb, hl, hsz, hk⟩
  · have h1' : m.blocks[0]? = some blk' := h1
    rw [hb] at h1'; cases h1'
    refine ⟨{ blk with bytes := writeBytes blk.bytes Lo.mo bs }, ?_, hl, ?_, hk⟩
    · rw [h5]; show (m.blocks.set! 0 _)[0]? = _
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
        (Array.getElem?_eq_some_iff.mp hb).1]; rfl
    · show (writeBytes blk.bytes Lo.mo bs).size = Lo.size
      rw [writeBytes_size _ _ _ (by rw [h3]; exact h4), hsz]

/-- **A step of the lock's code keeps `U`** (`FLock.FitsOn.stable`). -/
theorem stable (G : ThreadId → Gh) (rX : Res) (m m' : Mem) (t : ThreadId) (p : LPh) (h : Res)
    (hok : ok (G t)) (_ : (L Lo).ph (G t) ≠ .gone) (hu : U Lo G rX m) (hs : (L Lo).Step t m m')
    (hrel : (L Lo).ph (G t) = .holds → p ≠ .holds → (L Lo).Before m' (m.clocks[t]!)) :
    U Lo (upd G t ((L Lo).set (G t) p h)) rX m' := by
  have hX : ∀ u, (upd G t ((L Lo).set (G t) p h) u).2 = (G u).2 := fun u => congrFun (FLock.snd_set G t p h) u
  have hhS := Word.hist_keep hu.ws (Word.keep_lockWordStep hs apS)
  have hhE := Word.hist_keep hu.we (Word.keep_lockWordStep hs apE)
  have hhV := Word.hist_keep hu.wv (Word.keep_lockWordStep hs apV)
  refine ⟨?_, fun e he hr => ?_, hu.rest.congr fun l hl => hs.heap (box_notL hl),
    hu.blk.lstep hs,
    hu.ws.keep (Word.keep_lockWordStep hs apS), hu.we.keep (Word.keep_lockWordStep hs apE),
    hu.wv.keep (Word.keep_lockWordStep hs apV),
    hu.cinv.lstep hu.ws hu.we apS apE hok.1 (fun _ _ _ => rfl) hs,
    hu.einv.lstep hu.wv apV hok.2.1 (fun _ _ _ => rfl) (fun _ _ _ => Iff.rfl)
      (fun _ _ _ => Iff.rfl) hs,
    by rw [hX]; exact hu.places, fun h1 => ?_, ?_, fun h0 => ?_, fun h1 => ?_,
    fun i jr sn e hr => ?_, fun h0 h1 => ?_, fun h1 => ?_, fun w hw => ?_,
    fun u hu' => by rw [hX] at hu' ⊢; exact hu.xc u hu'⟩
  · have : (fun u => (upd G t ((L Lo).set (G t) p h) u).2) = fun u => (G u).2 := funext hX
    rw [this]; unfold Shape at *; rw [hs.threads]; exact hu.shape
  · rcases hs.fp e he with h' | ⟨-, ho', -⟩
    · rcases hu.io e h' hr with ⟨hk, h''⟩ | h''
      · exact .inl ⟨hk, hs.someLe h''⟩
      · exact .inr (hs.allLe h'')
    · exact absurd hr (io_notL ho')
  · rw [hX] at h1; rw [hhE]; exact hu.ep1 h1
  · rw [hhE]; exact VClock.le_trans hu.ep0 (hs.clocks 0)
  · rw [hX] at h0; rw [hX]; exact hu.ent h0
  · rw [hX] at h1
    by_cases ht : t = 1
    · subst ht; rcases h1 with h1 | h1
      · exact absurd h1 hok.2.2.1
      · exact absurd h1 hok.2.2.2
    · rw [upd_ne _ _ (Ne.symm ht)]; exact hu.hold h1
  · rw [hX] at hr; rw [hX, hhS]
    rcases hu.reg i jr sn e hr with h' | ⟨hlk, h'⟩
    · exact .inl (VClock.le_trans h' (hs.clocks 1))
    · refine .inr ⟨hlk, ?_⟩
      rcases h' with ⟨hh, hle⟩ | hb
      · by_cases ht0 : t = 0
        · subst ht0
          by_cases hp : p = .holds
          · subst hp
            exact .inl ⟨by rw [upd_self]; rfl, VClock.le_trans hle (hs.clocks 0)⟩
          · exact .inr (LockWord.before_le (hrel hh hp) hle)
        · exact .inl ⟨by rw [upd_ne _ _ (Ne.symm ht0)]; exact hh, VClock.le_trans hle (hs.clocks 0)⟩
      · exact .inr (hs.before _ hb)
  · rw [hX] at h0 h1
    show ((Lo.WS.hist m')[(Lo.WS.hist m').size - 1]!).Val _; rw [hhS]; exact hu.lvc h0 h1
  · rw [hX] at h1
    show ((Lo.WV.hist m')[(Lo.WV.hist m').size - 1]!).Val _; rw [hhV]; exact hu.fin h1
  · by_cases hl : w.2 = (L Lo).ptr
    · exact .inl hl
    · exact hu.q w ((hs.waiters w hl).mp hw)

/-- A stop keeps `U`: it reads no current thread. -/
theorem atStop {G : ThreadId → Gh} {rX : Res} {m : Mem} (t : ThreadId) (hu : U Lo G rX m) :
    U Lo G rX { m with current := t } :=
  have hk := fun (W : Word 32 4) => W.keep_same m t m.seen m.nextMsg m.waiters m.woken m.groups
  ⟨hu.shape, hu.io, hu.rest, hu.blk, hu.ws.keep (hk _), hu.we.keep (hk _), hu.wv.keep (hk _),
    hu.cinv.stay t rfl rfl apE.ptr_ne (fun _ _ h => h) (fun _ => VClock.le_refl _),
    hu.einv.frame (t := t) (fun _ _ => rfl) rfl rfl rfl rfl (fun _ => VClock.le_refl _) id id,
    hu.places, hu.ep1, hu.ep0, hu.ent, hu.hold, hu.reg, hu.lvc, hu.fin, hu.q, hu.xc⟩

/-- The rest has the bytes of `io`. -/
theorem rest_io {rX : Res} {m : Mem} (hr : Rest Lo rX m) {x : Nat} (hx : x < Lo.io) :
    rX.heap (0, x) ≠ none := by
  obtain ⟨rIO, ⟨A, bs, -, hbs, r₁, r₂, -, rfl, h1, -⟩, -, rfl⟩ := hr
  have := (up_bytesAt_some h1 rfl (0, x)).mpr ⟨rfl, by simp [bPtr], by simp [bPtr, hbs]; omega⟩
  simp only [FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
  intro _ h; exact absurd h this

/-- The rest has the cells of the three words. -/
theorem rest_box {rX : Res} {m : Mem} (hr : Rest Lo rX m) (hw : ∀ l, Lo.BoxW l → m.heap l ≠ none)
    {l : Zig.Loc} (hl : Lo.BoxW l) : rX.heap.erase l ≠ none := by
  obtain ⟨rIO, -, -, rfl⟩ := hr
  have := cellsAt_some hl (hw l hl) (m := m)
  simp only [FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff, Option.or_eq_none_iff,
    not_and]
  intro h; exact absurd h this

/-- The words' cells are live. -/
theorem box_live {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U Lo G rX m) {l : Zig.Loc}
    (hl : Lo.BoxW l) : m.heap l ≠ none := by
  rcases Lo.box_cases hl with h | h | h
  · exact hu.ws.cellIn h
  · exact hu.we.cellIn h
  · exact hu.wv.cellIn h

theorem before_atomics {m m' : Mem} (ha : m'.atomics = m.atomics) {c : VClock}
    (h : (L Lo).Before m c) : (L Lo).Before m' c := by
  obtain ⟨i, l, ⟨h1, h2⟩, h3⟩ := h
  exact ⟨i, l, ⟨by rw [ha]; exact h1, by rw [ha]; exact h2⟩, h3⟩

/-- **A step of `t` on its own part keeps `U`** (a `StepIn` whose frame has `io`), with the new
rest `rX'`, the three words kept, and `t`'s new ghost value `g` at the same places (a new part or
held resource). -/
theorem U_frame {G : ThreadId → Gh} {rX rX' : Res} {m m' : Mem} {t : ThreadId} {g : Gh}
    {hF : Heap} (hu : U Lo G rX m) (hs : StepIn hF m m')
    (hio : ∀ x, x < Lo.io → hF (0, x) ≠ none) (hrest : Rest Lo rX' m') (hbk : BlkOk Lo m')
    (kS : Lo.WS.KeepK m m') (kE : Lo.WE.KeepK m m') (kV : Lo.WV.KeepK m m')
    (hX : g.2 = (G t).2) (hph : g.1.ph = (G t).1.ph) : U Lo (upd G t g) rX' m' := by
  have hX' : ∀ u, (upd G t g u).2 = (G u).2 := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hX]
    · rw [upd_ne _ _ e]
  have hP' : ∀ u, (upd G t g u).1.ph = (G u).1.ph := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hph]
    · rw [upd_ne _ _ e]
  have hhS := Word.hist_keepK hu.ws kS
  have hhE := Word.hist_keepK hu.we kE
  have hhV := Word.hist_keepK hu.wv kV
  refine ⟨?_, fun e he hr => ?_, hrest, hbk, hu.ws.keepK kS, hu.we.keepK kE,
    hu.wv.keepK kV,
    hu.cinv.frame (t := t) (g' := g) (congrArg (·.c) hX) hph
      (fun h => by show g.2.ph = .sg; rw [hX]; exact h) hhS hhE apE.ptr_ne hs.waiters hs.clock,
    hu.einv.frame (fun u hu => upd_ne _ _ hu) (by rw [upd_self]; exact congrArg (·.e) hX)
      (by rw [upd_self]; exact hph) hhV hs.waiters hs.clock
      (fun h => by rw [upd_self]; show g.2.ph = .ev ∨ g.2.ph = .joins; rw [hX]; exact h)
      (fun h => by rw [upd_self]; show g.2.ph = .st; rw [hX]; exact h),
    by rw [hX']; exact hu.places, fun h1 => ?_, ?_, fun h0 => ?_, fun h1 => ?_,
    fun i jr sn e hr => ?_, fun h0 h1 => ?_, fun h1 => ?_, fun w hw => ?_,
    fun u hu' => by rw [hX'] at hu' ⊢; exact hu.xc u hu'⟩
  · have : (fun u => (upd G t g u).2) = fun u => (G u).2 := funext hX'
    rw [this]; unfold Shape at *; rw [hs.threads]; exact hu.shape
  · rcases hs.fp e he with h' | ⟨-, hnt, -⟩
    · rcases hu.io e h' hr with ⟨hk, h''⟩ | h''
      · exact .inl ⟨hk, LockWord.someLe_mono hs.threads (fun u _ => hs.clock u) h''⟩
      · exact .inr (LockWord.allLe_mono hs.threads (fun u _ => hs.clock u) h'')
    · refine absurd ⟨e.off, Nat.le_refl _, .inr rfl, ?_⟩ hnt
      rw [hr.1]; exact hio _ hr.2
  · rw [hX'] at h1; rw [hhE]; exact hu.ep1 h1
  · rw [hhE]; exact VClock.le_trans hu.ep0 (hs.clock 0)
  · rw [hX'] at h0; rw [hX']; exact hu.ent h0
  · rw [hX'] at h1; rw [hP']; exact hu.hold h1
  · rw [hX'] at hr; rw [hX', hhS, hP']
    rcases hu.reg i jr sn e hr with h' | ⟨hlk, h'⟩
    · exact .inl (VClock.le_trans h' (hs.clock 1))
    · refine .inr ⟨hlk, ?_⟩
      rcases h' with ⟨hh, hle⟩ | hb
      · exact .inl ⟨hh, VClock.le_trans hle (hs.clock 0)⟩
      · exact .inr (before_atomics hs.atomics hb)
  · rw [hX'] at h0 h1
    show ((Lo.WS.hist m')[(Lo.WS.hist m').size - 1]!).Val _; rw [hhS]; exact hu.lvc h0 h1
  · rw [hX'] at h1
    show ((Lo.WV.hist m')[(Lo.WV.hist m').size - 1]!).Val _; rw [hhV]; exact hu.fin h1
  · rw [hs.waiters] at hw; exact hu.q w hw

/-- `blk_of` for a rest whose ghost state is `io`'s. -/
theorem blk_ofG {G : ThreadId → Gh} {rX rIO : Res} {m : Mem} (hi : (L Lo).Inv G rX m)
    (hIO : IoRest Lo rIO) (hg : rX.gh = rIO.gh) : BlkOk Lo m := by
  obtain ⟨rL, ho, -⟩ := hi.rest
  obtain ⟨rT, -, hh⟩ := ho.holds
  have he := hh.swap.extTrue
  obtain ⟨A, bs, -, -, r₁, r₂, -, rfl, -, h2⟩ := hIO
  simp only [rsum] at he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [hg, Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [bauth_eq h2] at he
  obtain ⟨blk, h1, h2, h3, h4, -⟩ := (he 0).1 Lo.size .stack (by simp [Ghost.atExt, ECell.auth1])
  exact ⟨blk, h1, h2, h3, h4⟩

/-- A byte of the `Box` that the rest after a step holds with its cell before it: the same cell
(the block is pinned). -/
theorem cell_eq {G' : ThreadId → Gh} {rX' : Res} {m m' : Mem} (hbk : BlkOk Lo m)
    (hbk' : BlkOk Lo m') (hi' : (L Lo).Inv G' rX' m') {x : Nat} (hx : x < Lo.size)
    (hr : rX'.heap (0, x) = (m.heap (0, x)).map fun c => ⟨c, none⟩) : m'.heap (0, x) = m.heap (0, x) := by
  obtain ⟨blk, hb, hlv, hs, hk⟩ := hbk
  obtain ⟨blk', hb', hlv', hs', hk'⟩ := hbk'
  have e := heap_blk hb hlv hk (by omega : x < blk.bytes.size)
  have e' := heap_blk hb' hlv' hk' (by omega : x < blk'.bytes.size)
  rw [e] at hr
  have hrc := hi'.restCell (l := (0, x)) hr
  rw [e', e]
  rw [e'] at hrc
  simp only [Option.map_some, Option.some.injEq, Cell.norm, Cell.mk.injEq] at hrc
  obtain ⟨hby, had, -⟩ := hrc
  simp only [Option.some.injEq, Cell.mk.injEq]
  exact ⟨hby, had, by omega, by rw [hk, hk']⟩

/-- The three words: their bytes are in the `Box`, and two of them are equal or apart. -/
theorem three_box {W : Word 32 4} (h : W = Lo.WS ∨ W = Lo.WE ∨ W = Lo.WV) :
    ∀ l, W.In l → Lo.BoxW l := by
  rcases h with rfl | rfl | rfl
  · exact fun _ => Lo.ws_box
  · exact fun _ => Lo.we_box
  · exact fun _ => Lo.wv_box

theorem three_apart {W W' : Word 32 4} (h : W = Lo.WS ∨ W = Lo.WE ∨ W = Lo.WV)
    (h' : W' = Lo.WS ∨ W' = Lo.WE ∨ W' = Lo.WV) : W' = W ∨ ∀ l, W'.In l → ¬ W.In l := by
  have := Lo.ok
  rcases h with rfl | rfl | rfl <;> rcases h' with rfl | rfl | rfl <;>
    first
      | exact .inl rfl
      | exact .inr fun l ⟨_, a, b⟩ ⟨_, c, d⟩ => by
          simp only [Layout.WS, Layout.WE, Layout.WV] at a b c d; omega

/-- The words' keeps after a step on a part: from the cells (`cells_same`). -/
theorem keepK_of {rX : Res} {m m' : Mem} {hF : Heap} (hr : Rest Lo rX m)
    (hw : ∀ l, Lo.BoxW l → m.heap l ≠ none) (hs : StepIn hF m m')
    (hF' : ∀ l, Lo.BoxW l → rX.heap.erase l ≠ none → hF l ≠ none) {W : Word 32 4}
    (hW : ∀ l, W.In l → Lo.BoxW l) (hcs : ∀ l, W.In l → m'.heap l = m.heap l) : W.KeepK m m' :=
  Word.keepK_stepIn hs (fun l hl => hF' l (hW l hl) (rest_box hr hw (hW l hl)))
    (fun l hl => by rw [hcs l hl])

/-- **A step of `t` on its own part keeps `U`** (a `StepIn` that keeps the rest), with `t`'s new
ghost value `g` at the same places (a new part or held resource). -/
theorem U_stepIn {G : ThreadId → Gh} {rX : Res} {m m' : Mem} {t : ThreadId} {g : Gh}
    (hu : U Lo G rX m) (hs : StepIn rX.heap.erase m m') (hi' : (L Lo).Inv (upd G t g) rX m')
    (hX : g.2 = (G t).2) (hph : g.1.ph = (G t).1.ph) : U Lo (upd G t g) rX m' := by
  have hcs := cells_same hu.blk hi' hu.rest
  have hk := fun (W : Word 32 4) (hW : ∀ l, W.In l → Lo.BoxW l) =>
    keepK_of hu.rest (fun _ => box_live hu) hs (fun _ _ h => h) hW (fun l hl => hcs l (hW l hl))
  exact U_frame hu hs (fun x hx => by simpa [FHeap.erase] using rest_io hu.rest hx)
    (hu.rest.congr hcs) (blk_of hi' hu.rest) (hk _ fun _ => Lo.ws_box)
    (hk _ fun _ => Lo.we_box) (hk _ fun _ => Lo.wv_box) hX hph

/-- **A step of `t` on its own part in the code of a sync object at the word `W`** keeps `U`
(`FCond.Fits.own`, `FEvent.Fits.own`): the rest gets `W`'s new cells, the other words' cells
stay. -/
theorem U_own {G : ThreadId → Gh} {rY : Res} {m m' : Mem} {t : ThreadId} {g : Gh}
    {W : Word 32 4} (hW3 : W = Lo.WS ∨ W = Lo.WE ∨ W = Lo.WV)
    (hu : U Lo G (rsum (W.cellsR m) rY) m) (hY : ∀ l, W.In l → rY.heap l = none)
    (hs : StepIn (rsum (W.cellsR m) rY).heap.erase m m') (hk : W.KeepK m m')
    (hi' : (L Lo).Inv (upd G t g) (rsum (W.cellsR m') rY) m')
    (hX : g.2 = (G t).2) (hph : g.1.ph = (G t).1.ph) :
    U Lo (upd G t g) (rsum (W.cellsR m') rY) m' := by
  have hWb := three_box hW3
  obtain ⟨rIO, hIO, hIOoff, hrX⟩ := hu.rest
  have hg : rY.gh = rIO.gh := by
    have := congrArg Res.gh hrX; simpa [cellsAt, Word.cellsR] using this
  have hbk' := blk_ofG hi' hIO (by simp [cellsAt, Word.cellsR, hg])
  have hcs : ∀ l, Lo.BoxW l → ¬ W.In l → m'.heap l = m.heap l := by
    rintro ⟨b, x⟩ hl hw
    obtain ⟨h0, h1, h2⟩ := hl
    simp only at h0 h1 h2; subst h0
    refine cell_eq hu.blk hbk' hi' (by have := Lo.ok; omega) ?_
    have := congrFun (congrArg Res.heap hrX) (0, x)
    simp only [FHeap.union_apply] at this ⊢
    rw [cellsAt_none hw, Option.none_or] at this ⊢
    rw [this, cellsAt_of (W := Lo.BoxW) ⟨rfl, h1, h2⟩, hIOoff _ ⟨rfl, h1, h2⟩, Option.or_none]
  have hrest := Rest.step hWb ⟨rIO, hIO, hIOoff, hrX⟩ rfl hY hcs
  have hkW : ∀ W', (W' = Lo.WS ∨ W' = Lo.WE ∨ W' = Lo.WV) → W'.KeepK m m' := fun W' hW' => by
    rcases three_apart hW3 hW' with rfl | hap
    · exact hk
    · exact keepK_of ⟨rIO, hIO, hIOoff, hrX⟩ (fun _ => box_live hu) hs (fun _ _ h => h)
        (three_box hW') (fun l hl => hcs l (three_box hW' l hl) (hap l hl))
  exact U_frame hu hs (fun x hx => by simpa [FHeap.erase] using rest_io hu.rest hx) hrest hbk'
    (hkW _ (.inl rfl)) (hkW _ (.inr (.inl rfl))) (hkW _ (.inr (.inr rfl))) hX hph

/-! ## A step of the condition's or the event's code, as the rest sees it -/

/-- Two words whose bytes are apart: the condition of `Word.keep_op`. -/
theorem apart_of {W W' : Word 32 4} (h : ∀ l, W'.In l → ¬ W.In l) :
    W.b ≠ W'.b ∨ W.o + 4 ≤ W'.o ∨ W'.o + 4 ≤ W.o := by
  by_cases hb : W.b = W'.b
  · refine .inr (Classical.byContradiction fun hc => ?_)
    by_cases h2 : W'.o ≤ W.o
    · exact h (W'.b, W.o) ⟨rfl, h2, by dsimp only; omega⟩ ⟨hb.symm, Nat.le_refl _, by dsimp only; omega⟩
    · exact h (W'.b, W'.o) ⟨rfl, Nat.le_refl _, by dsimp only; omega⟩
        ⟨hb.symm, by dsimp only; omega, by dsimp only; omega⟩
  · exact .inl hb

/-- One of the three shared words. -/
def Three (Lo : Layout) (W : Word 32 4) : Prop := W = Lo.WS ∨ W = Lo.WE ∨ W = Lo.WV

/-- What a step of the condition's or the event's code at the word `W` (one of the three; a futex
wait or wake at the word `wp`) does to the memory (`Mv.ofC`, `Mv.ofE`): the threads stay, the
clocks grow, only `W`'s bytes change, a new access is at the shared words, the `Box` and the
mutex's location stay, a new waiter is `t` at `wp`, the three words stay valid and only `W` gets a
new write. -/
structure Mv (Lo : Layout) (W : Word 32 4) (wp : Ptr) (t : ThreadId) (m m' : Mem) : Prop where
  threads : m'.threads = m.threads
  clk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true
  fp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ (e.block = 0 ∧ Lo.so ≤ e.off)
  cells : ∀ l, ¬ W.In l → m'.heap l = m.heap l
  blk : BlkOk Lo m → BlkOk Lo m'
  before : ∀ c, (L Lo).Before m c → (L Lo).Before m' c
  waiters : ∀ w ∈ m'.waiters, w ∈ m.waiters ∨ w = (t, wp)
  ok : ∀ W', Three Lo W' → W'.Ok m → W'.Ok m'
  hist : ∀ W', Three Lo W' → W'.Ok m → W'.hist m' = W'.hist m ∨ (W' = W ∧ ∃ x, W'.hist m' = (W'.hist m).push x)

theorem three_b {W : Word 32 4} (h : Three Lo W) : W.b = 0 := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem three_o {W : Word 32 4} (h : Three Lo W) : Lo.so ≤ W.o := by
  have := Lo.ok
  rcases h with rfl | rfl | rfl <;> simp [Layout.WS, Layout.WE, Layout.WV] <;> omega

theorem three_ap {W : Word 32 4} (h : Three Lo W) : W.ApartL (L Lo).toLockWord := by
  rcases h with rfl | rfl | rfl
  · exact apS
  · exact apE
  · exact apV

/-- A step that keeps the blocks, the atomic locations, the footprint, the threads and the
clocks, with a new futex queue: an `Mv`. -/
theorem Mv.requeue {W : Word 32 4} {wp : Ptr} {t : ThreadId} {m m' : Mem}
    (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics) (hf : m'.footprint = m.footprint)
    (ht : m'.threads = m.threads) (hcl : m'.clocks = m.clocks)
    (hw : ∀ w ∈ m'.waiters, w ∈ m.waiters) : Mv Lo W wp t m m' := by
  have hk : ∀ W' : Word 32 4, W'.Keep m m' := fun W' =>
    Word.keep_of hb ha hf ht fun u => by rw [hcl]; exact VClock.le_refl _
  have hh : ∀ l, m'.heap l = m.heap l := fun l => by unfold Mem.heap; rw [hb]
  refine ⟨ht, fun u => by rw [hcl]; exact VClock.le_refl _, fun e he => .inl (hf ▸ he),
    fun l _ => hh l, fun ⟨blk, h1, h2⟩ => ⟨blk, by rw [hb]; exact h1, h2⟩,
    fun c ⟨i, l, hl, hc⟩ => ⟨i, l, by unfold LockWord.Loc; rw [ha]; exact hl, hc⟩,
    fun w h => .inl (hw w h), fun W' _ h => h.keep (hk W'), fun W' _ h => .inl (Word.hist_keep h (hk W'))⟩

/-- An op of `t` at the word `W` (from its stop): an `Mv`. -/
theorem Mv.op {W : Word 32 4} {wp : Ptr} {t : ThreadId} {m m' : Mem} (hW : Three Lo W)
    (hop : W.Op t { m with current := t } m') (hok : W.Ok m')
    (hh : W.hist m' = W.hist m ∨ ∃ x, W.hist m' = (W.hist m).push x) : Mv Lo W wp t m m' := by
  have hop' := hop.of_cur
  have hb0 := three_b hW
  refine ⟨hop'.threads, hop'.clocks, fun e he => (hop'.fp e he).imp id fun ⟨h1, h2, _⟩ =>
    ⟨h1.trans hb0, h2 ▸ three_o hW⟩, fun l hl => hop'.cells l hl, fun ⟨blk, h1, h2, h3, h4⟩ => ?_,
    fun c ⟨i, l, hl, hc⟩ => ⟨i, l, (hop'.locs.same _ _ (three_ap hW).ne i l).mpr hl, hc⟩,
    fun w h => .inl (hop'.waiters ▸ h), fun W' hW' h => ?_, fun W' hW' h => ?_⟩
  · obtain ⟨blk', e1, -, e2, e3, e4, -⟩ := hop'.blocks.word blk (by rw [hb0]; exact h1)
    rw [hb0] at e1
    exact ⟨blk', e1, by rw [e2]; exact h2, by rw [e4]; exact h3, by rw [e3]; exact h4⟩
  · rcases three_apart hW hW' with rfl | hap
    · exact hok
    · exact h.keep (Word.keep_op hop' (apart_of hap))
  · rcases three_apart hW hW' with rfl | hap
    · rcases hh with hh | hh
      · exact .inl hh
      · exact .inr ⟨rfl, hh⟩
    · exact .inl (Word.hist_keep h (Word.keep_op hop' (apart_of hap)))

/-- A futex wait's sleep of `t` at the word `W'` (an op there that keeps its writes): an `Mv` for
any of the three words `W`. -/
theorem Mv.sleep {W W' : Word 32 4} {t : ThreadId} {m M : Mem} (hW' : Three Lo W')
    (hop : W'.Op t { m with current := t } M) (hh : W'.hist M = W'.hist m) (hok : W'.Ok M)
    (hbl : M.blocks = m.blocks) :
    Mv Lo W W'.ptr t m { M with waiters := M.waiters.push (t, W'.ptr) } := by
  have hop' := hop.of_cur
  have hb0 := three_b hW'
  have hhp : ∀ l, ({ M with waiters := M.waiters.push (t, W'.ptr) } : Mem).heap l = m.heap l :=
    fun l => by show M.heap l = m.heap l; unfold Mem.heap; rw [hbl]
  -- the push of the futex queue keeps every word
  have hq : ∀ W₁ : Word 32 4, W₁.Keep M { M with waiters := M.waiters.push (t, W'.ptr) } :=
    fun _ => Word.keep_of rfl rfl rfl rfl fun _ => VClock.le_refl _
  have hM : ∀ W₁, Three Lo W₁ → W₁.Ok m → W₁.Ok M ∧ W₁.hist M = W₁.hist m := fun W₁ hW₁ h => by
    rcases three_apart hW' hW₁ with rfl | hap
    · exact ⟨hok, hh⟩
    · exact ⟨h.keep (Word.keep_op hop' (apart_of hap)),
        Word.hist_keep h (Word.keep_op hop' (apart_of hap))⟩
  refine ⟨hop'.threads, hop'.clocks, fun e he => (hop'.fp e he).imp id fun ⟨h1, h2, _⟩ =>
    ⟨h1.trans hb0, h2 ▸ three_o hW'⟩, fun l _ => hhp l,
    fun ⟨blk, h1, h2⟩ => ⟨blk, by show M.blocks[0]? = _; rw [hbl]; exact h1, h2⟩,
    fun c ⟨i, l, hl, hc⟩ => ⟨i, l, (hop'.locs.same _ _ (three_ap hW').ne i l).mpr hl, hc⟩,
    fun w h => ?_, fun W₁ hW₁ h => (hM W₁ hW₁ h).1.keep (hq W₁),
    fun W₁ hW₁ h => .inl ((Word.hist_keep (hM W₁ hW₁ h).1 (hq W₁)).trans (hM W₁ hW₁ h).2)⟩
  rcases Array.mem_push.mp h with h | rfl
  · exact .inl (hop'.waiters ▸ h)
  · exact .inr rfl

/-- A futex wake of `t` at a word: an `Mv`. -/
theorem Mv.wake {W : Word 32 4} {wp p : Ptr} {t : ThreadId} {m m' : Mem} {c : Nat}
    {cs : List Nat}
    (h : ((Thread.futexWake p c cs).run { m with current := t }).run = some (.ok ((), m'))) :
    Mv Lo W wp t m m' := by
  have hm' := Proto.modify_ok h
  subst hm'
  exact Mv.requeue rfl rfl rfl rfl rfl fun w hw => (Array.mem_filter.mp hw).1

/-- **A step of the condition's code** at its word `W`: an `Mv`. -/
theorem Mv.ofC {W : Word 32 4} (hW : W = Lo.WS ∨ W = Lo.WE) {t : ThreadId} {m m' : Mem}
    (hs : (C Lo).MStep W t m m') : Mv Lo W Lo.WE.ptr t m m' := by
  have hW3 : Three Lo W := hW.imp id .inl
  cases hs with
  | same => exact Mv.requeue rfl rfl rfl rfl rfl fun _ h => h
  | op hop hok hh => exact Mv.op hW3 hop hok (hh.imp id fun ⟨_, _, h⟩ => ⟨_, h⟩)
  | sleep hop hh hok hbl => exact Mv.sleep (W' := Lo.WE) (.inr (.inl rfl)) hop hh hok hbl
  | woken => exact Mv.requeue rfl rfl rfl rfl rfl fun _ h => h
  | resume => exact Mv.requeue rfl rfl rfl rfl rfl fun _ h => h
  | wake c cs h => exact Mv.wake h

/-- **A step of the event's code**: an `Mv`. -/
theorem Mv.ofE {t : ThreadId} {m m' : Mem} (hs : (E Lo).MStep t m m') :
    Mv Lo Lo.WV Lo.WV.ptr t m m' := by
  cases hs with
  | same => exact Mv.requeue rfl rfl rfl rfl rfl fun _ h => h
  | op hop hok hh => exact Mv.op (.inr (.inr rfl)) hop hok (hh.imp id fun ⟨_, _, h⟩ => ⟨_, h⟩)
  | sleep hop hh hok hbl => exact Mv.sleep (W' := Lo.WV) (.inr (.inr rfl)) hop hh hok hbl
  | woken => exact Mv.requeue rfl rfl rfl rfl rfl fun _ h => h
  | resume => exact Mv.requeue rfl rfl rfl rfl rfl fun _ h => h
  | wake c cs h => exact Mv.wake h

/-! ## The threads' places -/

theorem ptr_EV : Lo.WE.ptr ≠ Lo.WV.ptr := fun h => by
  have h1 : (((Lo.so + 4 : Nat) : Int)) = ((Lo.vo : Nat) : Int) := congrArg Ptr.off h
  have := Lo.ok; omega

theorem ne_VS : Lo.WV ≠ Lo.WS := fun h => by
  have h1 : Lo.vo = Lo.so := congrArg Word.o h
  have := Lo.ok; omega

theorem ne_VE : Lo.WV ≠ Lo.WE := fun h => by
  have h1 : Lo.vo = Lo.so + 4 := congrArg Word.o h
  have := Lo.ok; omega

/-- The threads' shape after a step that keeps every program place and the `X` of a thread that
is not running yet (or `main` before its spawn). -/
theorem Shape.congr {Y Y' : ThreadId → X} {m m' : Mem} (h : Shape Y m)
    (hth : m'.threads = m.threads) (hph : ∀ u, (Y' u).ph = (Y u).ph)
    (hfr : ∀ u, Y u = {} ∨ Y u = { ph := .pre } → Y' u = Y u) : Shape Y' m' := by
  obtain ⟨h0, ⟨hsz, hy0, hyu⟩ | ⟨hsz, h1, hm, hnp, hp, hyu⟩⟩ := h
  · exact ⟨by rw [hth]; exact h0, .inl ⟨by rw [hth]; exact hsz, by rw [hfr 0 (.inr hy0)]; exact hy0,
      fun u hu => by rw [hfr u (.inl (hyu u hu))]; exact hyu u hu⟩⟩
  · exact ⟨by rw [hth]; exact h0, .inr ⟨by rw [hth]; exact hsz, by rw [hth]; exact h1,
      by rw [hph]; exact hm, by rw [hph]; exact hnp, by rw [hph]; exact hp,
      fun u hu => by rw [hfr u (.inl (hyu u hu))]; exact hyu u hu⟩⟩

/-- Only the producer (thread 1) is at a producer's place. -/
theorem Shape.one {Y : ThreadId → X} {m : Mem} (h : Shape Y m) {u : ThreadId}
    (hp : (Y u).ph.isProd = true) : u = 1 := by
  obtain ⟨-, ⟨-, h0, hu⟩ | ⟨-, -, hm, -, -, hu⟩⟩ := h
  · rcases u with _ | u
    · rw [h0] at hp; exact absurd hp (by decide)
    · rw [hu (u + 1) (Nat.succ_pos u)] at hp; exact absurd hp (by decide)
  · rcases u with _ | _ | u
    · revert hm hp; cases (Y 0).ph <;> decide
    · rfl
    · rw [hu (u + 2) (Nat.le_add_left 2 u)] at hp; exact absurd hp (by decide)

/-- Only `main` (thread 0) is at a place of `main`. -/
theorem Shape.zero {Y : ThreadId → X} {m : Mem} (h : Shape Y m) {u : ThreadId}
    (hp : (Y u).ph.isMain = true) : u = 0 := by
  obtain ⟨-, ⟨-, -, hu⟩ | ⟨-, -, -, -, hpr, hu⟩⟩ := h
  · rcases u with _ | u
    · rfl
    · rw [hu (u + 1) (Nat.succ_pos u)] at hp; exact absurd hp (by decide)
  · rcases u with _ | _ | u
    · rfl
    · revert hpr hp; cases (Y 1).ph <;> decide
    · rw [hu (u + 2) (Nat.le_add_left 2 u)] at hp; exact absurd hp (by decide)

/-- A thread in the condition's code is out of the event's code (`xc`, `FEvent.wx`, `FEvent.sx`). -/
theorem U.e_out {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U Lo G rX m) {u : ThreadId}
    (hc : (G u).2.c ≠ .out) : (G u).2.e = .out := by
  have hx := hu.xc u hc
  cases he : (G u).2.e with
  | out => rfl
  | w0 =>
    have h := hu.einv.wx u (Or.inl he)
    rcases h with h | h <;> rcases hx with h' | h' <;> rw [h'] at h <;> cases h
  | w1 =>
    have h := hu.einv.wx u (Or.inr he)
    rcases h with h | h <;> rcases hx with h' | h' <;> rw [h'] at h <;> cases h
  | sw =>
    have h : (G u).2.ph = .st := hu.einv.sx u he
    rcases hx with h' | h' <;> rw [h'] at h <;> cases h

theorem next_out {p : CPh} (h : CPh.Next .out p) : p = .out ∨ p = .inc := by
  cases p <;> simp_all [CPh.Next]

theorem next_reg {a : CPh} {i jr : Nat} {sn : Bool} {e : BitVec 32}
    (h : CPh.Next a (.reg i jr sn e)) : (∃ sn', a = .reg i jr sn' e) ∨ a = .ld i e := by
  cases a <;> simp_all [CPh.Next]

/-- A waiter's place out of the critical code is a registration. -/
theorem reg_of {c : CPh} (hw : c.waits = true) (hc : c.crit = false) :
    ∃ i jr sn e, c = .reg i jr sn e := by
  cases c <;> simp_all [CPh.waits, CPh.crit]

/-- **A step of the condition's code keeps `U`** (`FCond.Fits.step`). -/
theorem cstep (G : ThreadId → Gh) (rY : Res) (m m' : Mem) (t : ThreadId) (p : CPh) (q : LPh)
    (h : Res) (W : Word 32 4) (hW : W = (C Lo).S ∨ W = (C Lo).Ep)
    (hn : CPh.Next ((C Lo).ph (G t)) p)
    (hq : (q = (L Lo).ph (G t) ∧ h = (L Lo).held (G t)) ∨
      (((L Lo).ph (G t) = .out ∨ (L Lo).ph (G t) = .away) ∧
        (q = .out ∨ (q = .away ∧ p.waits = true)) ∧ h = rnil))
    (hu : U Lo G (rsum (W.cellsR m) rY) m) (hY : ∀ l, W.In l → rY.heap l = none)
    (hs : (C Lo).MStep W t m m')
    (hEp : (C Lo).Ep.hist m' = (C Lo).Ep.hist m ∨ (C Lo).ph (G t) = .inc)
    (hI : (C Lo).Inv (L Lo) (upd G t ((L Lo).set ((C Lo).set (G t) p) q h)) m') :
    U Lo (upd G t ((L Lo).set ((C Lo).set (G t) p) q h)) (rsum (W.cellsR m') rY) m' := by
  have hmv := Mv.ofC hW hs
  have hW3 : Three Lo W := hW.imp id .inl
  have hn' : CPh.Next ((G t).2.c) p := hn
  -- the new ghost values
  have hG : ∀ u, u ≠ t → upd G t ((L Lo).set ((C Lo).set (G t) p) q h) u = G u :=
    fun u hu => upd_ne _ _ hu
  have hXt : (upd G t ((L Lo).set ((C Lo).set (G t) p) q h) t).2 = { (G t).2 with c := p } := by
    rw [upd_self]; rfl
  have hLt : (upd G t ((L Lo).set ((C Lo).set (G t) p) q h) t).1.ph = q := by rw [upd_self]; rfl
  have hph : ∀ u, (upd G t ((L Lo).set ((C Lo).set (G t) p) q h) u).2.ph = (G u).2.ph ∧
      (upd G t ((L Lo).set ((C Lo).set (G t) p) q h) u).2.e = (G u).2.e := fun u => by
    by_cases e : u = t
    · subst e; rw [hXt]; exact ⟨rfl, rfl⟩
    · rw [hG u e]; exact ⟨rfl, rfl⟩
  have hcw : ∀ u, ((upd G t ((L Lo).set ((C Lo).set (G t) p) q h) u).2.c).waits = true →
      ((G u).2.c).waits = true := fun u hw => by
    by_cases e : u = t
    · subst e; rw [hXt] at hw; exact CPh.Next.waits hn hw
    · rwa [hG u e] at hw
  have hcc : ∀ u, ((upd G t ((L Lo).set ((C Lo).set (G t) p) q h) u).2.c).crit = true →
      ((G u).2.c).crit = true := fun u hw => by
    by_cases e : u = t
    · subst e; rw [hXt] at hw; exact CPh.Next.crit hn hw
    · rwa [hG u e] at hw
  have hinc : p = .inc → (G t).2.ph = .sg := fun hp => by
    have := hI.sx t (by show ((upd G t _ t).2.c).sig = true; rw [hXt, hp]; rfl)
    have h2 : (upd G t ((L Lo).set ((C Lo).set (G t) p) q h) t).2.ph = .sg := this
    rw [(hph t).1] at h2; exact h2
  -- the lock place of `t` changes only for a waiter
  have hlq : (L Lo).ph (G t) ≠ (upd G t ((L Lo).set ((C Lo).set (G t) p) q h) t).1.ph →
      ((L Lo).ph (G t) = .out ∨ (L Lo).ph (G t) = .away) ∧
        (q = .out ∨ (q = .away ∧ p.waits = true)) := fun hne => by
    rcases hq with ⟨rfl, -⟩ | ⟨h1, h2, -⟩
    · exact absurd hLt.symm hne
    · exact ⟨h1, h2⟩
  have hV : Lo.WV.hist m' = Lo.WV.hist m := by
    rcases hmv.hist _ (.inr (.inr rfl)) hu.wv with e | ⟨e, -⟩
    · exact e
    · rcases hW with rfl | rfl
      · exact absurd e ne_VS
      · exact absurd e ne_VE
  -- a new waiter in the futex queue is `t` at the epoch, registered
  have hnw : ∀ w ∈ m'.waiters, w ∈ m.waiters ∨ (w = (t, Lo.WE.ptr) ∧ ((G t).2.c).waits = true) :=
    fun w hw => by
      rcases hmv.waiters w hw with h' | rfl
      · exact .inl h'
      · obtain ⟨i, jr, e, h1, -⟩ := hI.q _ hw rfl
        refine .inr ⟨rfl, hcw t ?_⟩
        show ((upd G t _ t).2.c).waits = true
        have : (upd G t ((L Lo).set ((C Lo).set (G t) p) q h) t).2.c = _ := h1
        rw [this]; rfl
  refine ⟨?_, fun e he hr => ?_, Rest.step (three_box hW3) hu.rest rfl hY fun l _ hw => hmv.cells l hw,
    hmv.blk hu.blk, hmv.ok _ (.inl rfl) hu.ws, hmv.ok _ (.inr (.inl rfl)) hu.we,
    hmv.ok _ (.inr (.inr rfl)) hu.wv, hI, ?_, ?_, fun h1 => ?_, ?_, fun h0 => ?_, fun h1 => ?_,
    fun i jr sn e hr => ?_, fun h0 h1 => ?_, fun h1 => ?_, fun w hw => ?_, fun u hu' => ?_⟩
  · -- shape
    refine Shape.congr hu.shape hmv.threads (fun u => (hph u).1) fun u hfr => ?_
    by_cases e : u = t
    · subst e
      have hc : (G u).2.c = .out := by rcases hfr with h' | h' <;> rw [h']
      have hp : p = .out := by
        rcases next_out (hc ▸ hn') with h' | h'
        · exact h'
        · have := hinc h'
          rcases hfr with h'' | h'' <;> rw [h''] at this <;> cases this
      show (upd G u _ u).2 = (G u).2
      rw [hXt, hp, ← hc]
    · rw [hG u e]
  · -- io
    rcases hmv.fp e he with h' | ⟨hb, ho⟩
    · rcases hu.io e h' hr with ⟨hk, h''⟩ | h''
      · exact .inl ⟨hk, LockWord.someLe_mono hmv.threads (fun u _ => hmv.clk u) h''⟩
      · exact .inr (LockWord.allLe_mono hmv.threads (fun u _ => hmv.clk u) h'')
    · have := Lo.ok; have := hr.2; omega
  · -- the event's invariant
    refine hu.einv.other (fun u hu => hG u hu) (hph t).2 (fun hne => ?_) hV (fun w hw => ?_)
      hmv.clk (fun h' => by show (_ = _ ∨ _ = _); rw [(hph t).1]; exact h')
      (fun h' => by show (_ = _); rw [(hph t).1]; exact h')
    · by_cases hl : (L Lo).ph (upd G t ((L Lo).set ((C Lo).set (G t) p) q h) t) = (L Lo).ph (G t)
      · exact .inl hl
      · obtain ⟨-, hq'⟩ := hlq (Ne.symm hl)
        rcases hq' with hq' | ⟨-, hw⟩
        · exact .inr (hLt.trans hq')
        · exact absurd (hu.e_out (fun hc => by
            rcases next_out (hc ▸ hn') with h' | h' <;> rw [h'] at hw <;> cases hw)) hne
    · rcases hnw w hw with h' | ⟨rfl, hw'⟩
      · exact .inl h'
      · refine .inr ⟨rfl, ptr_EV, fun he => ?_⟩
        have := hu.e_out (u := t) (fun hc => by rw [hc] at hw'; cases hw')
        rw [show (E Lo).ph (G t) = (G t).2.e from rfl, this] at he; cases he
  · -- places
    cases hw : ((upd G t ((L Lo).set ((C Lo).set (G t) p) q h) 1).2.c).waits
    · rfl
    · have := hcw 1 hw; rw [hu.places] at this; cases this
  · -- ep1
    rw [(hph 1).1] at h1
    rcases hEp with e | e
    · show (Lo.WE.hist m').size = 1
      rw [show Lo.WE.hist m' = Lo.WE.hist m from e]; exact hu.ep1 h1
    · have h2 := hu.cinv.sx t (by show ((G t).2.c).sig = true; rw [show (G t).2.c = _ from e]; rfl)
      have h3 : (G t).2.ph = .sg := h2
      have ht := hu.shape.one (u := t) (by rw [h3]; rfl)
      subst ht; rw [h3] at h1; cases h1
  · -- ep0
    rcases hmv.hist _ (.inr (.inl rfl)) hu.we with e | ⟨-, x, e⟩
    · rw [e]; exact VClock.le_trans hu.ep0 (hmv.clk 0)
    · rw [e, FEvent.get_push_lt (FEvent.hist_pos hu.we)]; exact VClock.le_trans hu.ep0 (hmv.clk 0)
  · -- ent
    rw [(hph 1).1]; exact hu.ent (hcc 0 h0)
  · -- hold
    rw [(hph 1).1] at h1
    have hh := hu.hold h1
    by_cases e : t = 1
    · subst e
      by_cases hl : (L Lo).ph (G 1) = (upd G 1 ((L Lo).set ((C Lo).set (G 1) p) q h) 1).1.ph
      · rw [← hl]; exact hh
      · obtain ⟨h2, -⟩ := hlq hl
        rcases h2 with h2 | h2 <;> rw [show (L Lo).ph (G 1) = (G 1).1.ph from rfl, hh] at h2 <;>
          cases h2
    · rw [hG 1 (Ne.symm e)]; exact hh
  · -- reg
    have hS : ∀ k, k < (Lo.WS.hist m).size → (Lo.WS.hist m')[k]! = (Lo.WS.hist m)[k]! := fun k hk => by
      rcases hmv.hist _ (.inl rfl) hu.ws with e | ⟨-, x, e⟩
      · rw [e]
      · rw [e, FEvent.get_push_lt hk]
    have hjr : ∀ i' sn' e', (G 0).2.c = .reg i' jr sn' e' → jr < (Lo.WS.hist m).size := fun i' sn' e' h' => by
      have := (hu.cinv.era 0 i' jr sn' e' h').ssz
      rcases this with h'' | h'' <;> (show jr < (Lo.WS.hist m).size; rw [show Lo.WS.hist m = _ from rfl]) <;>
        simp only [C] at h'' <;> omega
    -- `main`'s lock place after the step, when it held the mutex
    have hold0 : (G 0).1.ph = .holds → (upd G t ((L Lo).set ((C Lo).set (G t) p) q h) 0).1.ph = .holds :=
      fun h0 => by
        by_cases e : t = 0
        · subst e
          by_cases hl : (L Lo).ph (G 0) = (upd G 0 ((L Lo).set ((C Lo).set (G 0) p) q h) 0).1.ph
          · rw [← hl]; exact h0
          · obtain ⟨h2, -⟩ := hlq hl
            rcases h2 with h2 | h2 <;> rw [show (L Lo).ph (G 0) = (G 0).1.ph from rfl, h0] at h2 <;>
              cases h2
        · rw [hG 0 (Ne.symm e)]; exact h0
    -- `main`'s place before the step
    have hb : (∃ sn', (G 0).2.c = .reg i jr sn' e) ∨ (t = 0 ∧ (G 0).2.c = .ld i e) := by
      by_cases et : t = 0
      · subst et; rw [hXt] at hr
        rcases next_reg (show CPh.Next ((G 0).2.c) (.reg i jr sn e) by rw [← hr]; exact hn) with h' | h'
        · exact .inl h'
        · exact .inr ⟨rfl, h'⟩
      · rw [hG 0 (Ne.symm et)] at hr; exact .inl ⟨sn, hr⟩
    rcases hb with ⟨sn', hb⟩ | ⟨rfl, hb⟩
    · rw [hS jr (hjr i sn' e hb), (hph 1).1]
      rcases hu.reg i jr sn' e hb with h' | ⟨hlk, h' | h'⟩
      · exact .inl (VClock.le_trans h' (hmv.clk 1))
      · exact .inr ⟨hlk, .inl ⟨hold0 h'.1, VClock.le_trans h'.2 (hmv.clk 0)⟩⟩
      · exact .inr ⟨hlk, .inr (hmv.before _ h')⟩
    · -- `main` registered in this step: it holds the mutex, the producer is before its lock
      have hcr : ((G 0).2.c).crit = true := by rw [hb]; rfl
      refine .inr ⟨by rw [(hph 1).1]; exact hu.ent hcr, .inl ⟨hold0 (hu.cinv.crit 0 hcr),
        (hI.era 0 i jr sn e (by show (upd G 0 _ 0).2.c = _; exact hr)).cs⟩⟩
  · -- lvc
    rw [(hph 1).1] at h1
    have hw0 := hcw 0 h0
    have hsig := hu.lvc hw0 h1
    have hnc : ∀ c : CPh, c.crit = true → ((G 0).2.c).crit = true → False := fun _ _ hc => by
      have := hu.ent hc; rw [this] at h1; rcases h1 with h1 | h1 <;> cases h1
    have hnc0 : ((G 0).2.c).crit = false := by
      cases hc : ((G 0).2.c).crit
      · rfl
      · exact (hnc _ hc hc).elim
    obtain ⟨i, jr, sn, e, hb⟩ := reg_of hw0 hnc0
    have hera := hu.cinv.era 0 i jr sn e hb
    have hs2 : (Lo.WS.hist m).size = jr + 2 := by
      rcases hera.last with ⟨-, h2⟩ | ⟨h2, -⟩
      · exact absurd (FEvent.val_eq h2 hsig) (by decide)
      · exact h2
    -- `main` keeps its registration
    have hnc0' : ((upd G t ((L Lo).set ((C Lo).set (G t) p) q h) 0).2.c).crit = false := by
      cases hc : ((upd G t ((L Lo).set ((C Lo).set (G t) p) q h) 0).2.c).crit
      · rfl
      · exact (hnc _ (hcc 0 hc) (hcc 0 hc)).elim
    obtain ⟨i', jr', sn', e', hb'⟩ := reg_of h0 hnc0'
    have hjr : jr' = jr := by
      by_cases et : t = 0
      · subst et; rw [hXt] at hb'
        rcases next_reg (show CPh.Next ((G 0).2.c) (.reg i' jr' sn' e') by rw [← hb']; exact hn)
          with ⟨_, h'⟩ | h'
        · rw [hb] at h'; cases h'; rfl
        · rw [hb] at h'; cases h'
      · rw [hG 0 (Ne.symm et), hb] at hb'; cases hb'; rfl
    subst hjr
    have hera' := hI.era 0 i' jr' sn' e' hb'
    have hge : jr' + 2 ≤ ((C Lo).S.hist m').size := by
      rcases hmv.hist _ (.inl rfl) hu.ws with e | ⟨-, x, e⟩
      · show jr' + 2 ≤ (Lo.WS.hist m').size; rw [e, hs2]; exact Nat.le_refl _
      · show jr' + 2 ≤ (Lo.WS.hist m').size; rw [e, Array.size_push, hs2]; omega
    rcases hera'.last with ⟨h2, -⟩ | ⟨-, h2⟩
    · omega
    · exact h2
  · -- fin
    rw [(hph 1).1] at h1
    show ((Lo.WV.hist m')[(Lo.WV.hist m').size - 1]!).Val _; rw [hV]; exact hu.fin h1
  · -- q
    rcases hmv.waiters w hw with h' | rfl
    · exact hu.q w h'
    · exact .inr (.inl rfl)
  · -- xc
    by_cases e : u = t
    · subst e
      have hp' : p ≠ .out := by rw [hXt] at hu'; exact hu'
      rw [(hph u).1]
      by_cases hc : (G u).2.c = .out
      · rcases next_out (hc ▸ hn') with h' | h'
        · exact absurd h' hp'
        · exact .inr (hinc h')
      · exact hu.xc u hc
    · rw [hG u e] at hu' ⊢; exact hu.xc u hu'

/-- **A step of the event's code keeps `U`** (`FEvent.Fits.step`). -/
theorem estep (G : ThreadId → Gh) (rY : Res) (m m' : Mem) (t : ThreadId) (p : EPh) (q : LPh)
    (hlo : (L Lo).ph (G t) = .out ∨ (L Lo).ph (G t) = .away)
    (hq : q = .out ∨ (q = .away ∧ p = .w1))
    (hu : U Lo G (rsum ((E Lo).W.cellsR m) rY) m) (hY : ∀ l, (E Lo).W.In l → rY.heap l = none)
    (hs : (E Lo).MStep t m m')
    (hI : (E Lo).Inv (L Lo) (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil)) m') :
    U Lo (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil)) (rsum ((E Lo).W.cellsR m') rY) m' := by
  have hmv := Mv.ofE hs
  have hG : ∀ u, u ≠ t → upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) u = G u :=
    fun u hu => upd_ne _ _ hu
  have hXt : (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) t).2 = { (G t).2 with e := p } := by
    rw [upd_self]; rfl
  have hph : ∀ u, (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) u).2.ph = (G u).2.ph ∧
      (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) u).2.c = (G u).2.c := fun u => by
    by_cases e : u = t
    · subst e; rw [hXt]; exact ⟨rfl, rfl⟩
    · rw [hG u e]; exact ⟨rfl, rfl⟩
  -- `t` is not `holds`
  have hnh : (G t).1.ph ≠ .holds := fun h => by
    rcases hlo with h' | h' <;> rw [show (L Lo).ph (G t) = (G t).1.ph from rfl, h] at h' <;> cases h'
  -- a waiter of the event is `main` from its event wait on
  have hEt : (E Lo).ph (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) t) = p := by
    rw [upd_self]; rfl
  have hwx : (p = .w0 ∨ p = .w1) → (G t).2.ph = .ev ∨ (G t).2.ph = .joins := fun hp => by
    have := hI.wx t (by rw [hEt]; exact hp)
    have h2 : (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) t).2.ph = .ev ∨
      (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) t).2.ph = .joins := this
    rwa [(hph t).1] at h2
  have hsw : p = .sw → (G t).2.ph = .st := fun hp => by
    have := hI.sx t (by rw [hEt]; exact hp)
    have h2 : (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) t).2.ph = .st := this
    rwa [(hph t).1] at h2
  -- a thread at the event's waiter places is out of the condition's code
  have hco : (p = .w0 ∨ p = .w1) → (G t).2.c = .out := fun hp => by
    by_cases hc : (G t).2.c = .out
    · exact hc
    · rcases hu.xc t hc with h' | h' <;> rcases hwx hp with h'' | h'' <;> rw [h'] at h'' <;>
        cases h''
  have hS : Lo.WS.hist m' = Lo.WS.hist m := by
    rcases hmv.hist _ (.inl rfl) hu.ws with e | ⟨e, -⟩
    · exact e
    · exact absurd e.symm ne_VS
  have hE : Lo.WE.hist m' = Lo.WE.hist m := by
    rcases hmv.hist _ (.inr (.inl rfl)) hu.we with e | ⟨e, -⟩
    · exact e
    · exact absurd e.symm ne_VE
  -- a new waiter in the futex queue is `t` at the event, a waiter there
  have hnw : ∀ w ∈ m'.waiters, w ∈ m.waiters ∨ (w = (t, Lo.WV.ptr) ∧ p = .w1) := fun w hw => by
    rcases hmv.waiters w hw with h' | rfl
    · exact .inl h'
    · have h1 := (hI.q _ hw rfl).1
      rw [hEt] at h1; exact .inr ⟨rfl, h1⟩
  refine ⟨?_, fun e he hr => ?_, Rest.step (fun _ => Lo.wv_box) hu.rest rfl hY
      fun l _ hw => hmv.cells l hw,
    hmv.blk hu.blk, hmv.ok _ (.inl rfl) hu.ws, hmv.ok _ (.inr (.inl rfl)) hu.we,
    hmv.ok _ (.inr (.inr rfl)) hu.wv, ?_, hI, by rw [(hph 1).2]; exact hu.places,
    fun h1 => by rw [(hph 1).1] at h1; rw [hE]; exact hu.ep1 h1,
    by rw [hE]; exact VClock.le_trans hu.ep0 (hmv.clk 0),
    fun h0 => by rw [(hph 0).2] at h0; rw [(hph 1).1]; exact hu.ent h0, fun h1 => ?_,
    fun i jr sn e hr => ?_, fun h0 h1 => ?_, fun h1 => ?_, fun w hw => ?_,
    fun u hu' => by rw [(hph u).2] at hu'; rw [(hph u).1]; exact hu.xc u hu'⟩
  · -- shape
    refine Shape.congr hu.shape hmv.threads (fun u => (hph u).1) fun u hfr => ?_
    by_cases e : u = t
    · subst e
      have hfr' : (G u).2.ph = .none ∨ (G u).2.ph = .pre := by
        rcases hfr with h' | h' <;> rw [h'] <;> simp
      have he : (G u).2.e = .out := by rcases hfr with h' | h' <;> rw [h']
      have hp : p = .out := by
        cases p with
        | out => rfl
        | w0 => rcases hwx (.inl rfl) with h' | h' <;> rcases hfr' with h'' | h'' <;>
            rw [h''] at h' <;> cases h'
        | w1 => rcases hwx (.inr rfl) with h' | h' <;> rcases hfr' with h'' | h'' <;>
            rw [h''] at h' <;> cases h'
        | sw => have h' := hsw rfl; rcases hfr' with h'' | h'' <;> rw [h''] at h' <;> cases h'
      show (upd G u _ u).2 = (G u).2
      rw [hXt, hp, ← he]
    · rw [hG u e]
  · -- io
    rcases hmv.fp e he with h' | ⟨hb, ho⟩
    · rcases hu.io e h' hr with ⟨hk, h''⟩ | h''
      · exact .inl ⟨hk, LockWord.someLe_mono hmv.threads (fun u _ => hmv.clk u) h''⟩
      · exact .inr (LockWord.allLe_mono hmv.threads (fun u _ => hmv.clk u) h'')
    · have := Lo.ok; have := hr.2; omega
  · -- the condition's invariant
    refine hu.cinv.other (fun u hu => hG u hu) (hph t).2 (fun hb => ?_) hS hE (fun w hw => ?_)
      hmv.clk (fun h' => by show (_ = _); rw [(hph t).1]; exact h') apE.ptr_ne
    · -- `t` in the condition's busy code is a signaller out of the lock, not a waiter
      have hsig : ((G t).2.c).sig = true := by
        unfold CPh.busy at hb
        cases hc : ((G t).2.c).crit
        · rw [show (C Lo).ph (G t) = (G t).2.c from rfl, hc, Bool.false_or] at hb; exact hb
        · have := hu.cinv.crit t hc; exact absurd this hnh
      have hlp : (G t).1.ph = .out := hu.cinv.lp t hsig
      have hsg : (G t).2.ph = .sg := hu.cinv.sx t hsig
      rcases hq with rfl | ⟨rfl, rfl⟩
      · rw [upd_self]; show LPh.out = (G t).1.ph; rw [hlp]
      · rcases hwx (.inr rfl) with h' | h' <;> rw [hsg] at h' <;> cases h'
    · rcases hnw w hw with h' | ⟨rfl, hp⟩
      · exact .inl h'
      · refine .inr ⟨rfl, fun h => ptr_EV h.symm, ?_⟩
        show ((G t).2.c).waits = false
        rw [hco (.inr hp)]; rfl
  · -- hold
    rw [(hph 1).1] at h1
    have hh := hu.hold h1
    by_cases e : t = 1
    · subst e; exact absurd hh hnh
    · rw [hG 1 (Ne.symm e)]; exact hh
  · -- reg
    rw [(hph 0).2] at hr
    rw [hS, (hph 1).1]
    rcases hu.reg i jr sn e hr with h' | ⟨hlk, h' | h'⟩
    · exact .inl (VClock.le_trans h' (hmv.clk 1))
    · refine .inr ⟨hlk, .inl ⟨?_, VClock.le_trans h'.2 (hmv.clk 0)⟩⟩
      by_cases et : t = 0
      · subst et; exact absurd h'.1 hnh
      · rw [hG 0 (Ne.symm et)]; exact h'.1
    · exact .inr ⟨hlk, .inr (hmv.before _ h')⟩
  · -- lvc
    rw [(hph 0).2] at h0; rw [(hph 1).1] at h1
    show ((Lo.WS.hist m')[(Lo.WS.hist m').size - 1]!).Val _; rw [hS]; exact hu.lvc h0 h1
  · -- fin: the event stays set
    rw [(hph 1).1] at h1
    have hset := hu.fin h1
    have hpos := FEvent.hist_pos hu.wv
    rcases hmv.hist _ (.inr (.inr rfl)) hu.wv with e | ⟨-, x, e⟩
    · show ((Lo.WV.hist m')[(Lo.WV.hist m').size - 1]!).Val _; rw [e]; exact hset
    · refine hI.isSet_of (j := (Lo.WV.hist m).size - 1) ?_ ?_
      · show _ < (Lo.WV.hist m').size; rw [e, Array.size_push]; omega
      · show ((Lo.WV.hist m')[(Lo.WV.hist m).size - 1]!).Val _
        rw [e, FEvent.get_push_lt (by omega)]; exact hset
  · -- q
    rcases hmv.waiters w hw with h' | rfl
    · exact hu.q w h'
    · exact .inr (.inr rfl)

/-- `R` reads the producer's program place only. -/
theorem R_congr {Y Y' : ThreadId → X} (h : (Y' 1).ph = (Y 1).ph) : R Lo Y' = R Lo Y := by
  unfold R vOf; rw [h]

variable {prodOf : Tgt → Option Ptr}

/-- **The protocol has the condition.** -/
theorem fitsC : (C Lo).Fits (L Lo) (proto Lo prodOf) (U Lo) ok where
  rS _ _ _ hu := ⟨hu.ws, Rest.split (fun _ => Lo.ws_box) hu.rest⟩
  rE _ _ _ hu := ⟨hu.we, Rest.split (fun _ => Lo.we_box) hu.rest⟩
  apS := apS
  apE := apE
  inv _ _ _ hu := hu.cinv
  fin g h := by show g.2.c = _; rw [h.2]
  joins g h := by show g.2.c = _; rw [h.2]
  lph _ _ := rfl
  lpart _ _ := rfl
  lheld _ _ := rfl
  lR G t p r hr := by
    change R Lo (fun u => (upd G t ((C Lo).set (G t) p) u).2) r
    rw [R_congr (Y := fun u => (G u).2) (by
      show (upd G t ((C Lo).set (G t) p) 1).2.ph = (G 1).2.ph
      by_cases e : t = 1
      · subst e; rw [upd_self]; rfl
      · rw [upd_ne _ _ (Ne.symm e)])]
    exact hr
  ph_l _ _ _ := rfl
  set_l _ _ _ _ := rfl
  ph_part _ _ := rfl
  set_part _ _ _ := rfl
  sx_l _ _ _ := Iff.rfl
  sx_part _ _ := Iff.rfl
  ok_c _ _ _ hp hq := ⟨fun h => ⟨hq, h.2⟩, fun h => ⟨hp, h.2⟩⟩
  own _ _ _ _ _ _ _ hW _ hu hY _ hs hk hL _ := U_own (hW.imp id .inl) hu hY hs hk hL rfl rfl
  step := cstep

/-- **The protocol has the event.** -/
theorem fitsE : (E Lo).Fits (L Lo) (proto Lo prodOf) (U Lo) where
  rest _ _ _ hu := ⟨hu.wv, Rest.split (fun _ => Lo.wv_box) hu.rest⟩
  ap := apV
  inv _ _ _ hu := hu.einv
  fin g h := by show g.2.e = _; rw [h.2]
  joins g h := by show g.2.e = _; rw [h.2]
  lph _ _ := rfl
  lpart _ _ := rfl
  lheld _ _ := rfl
  lR G t p r hr := by
    change R Lo (fun u => (upd G t ((E Lo).set (G t) p) u).2) r
    rw [R_congr (Y := fun u => (G u).2) (by
      show (upd G t ((E Lo).set (G t) p) 1).2.ph = (G 1).2.ph
      by_cases e : t = 1
      · subst e; rw [upd_self]; rfl
      · rw [upd_ne _ _ (Ne.symm e)])]
    exact hr
  ph_l _ _ _ := rfl
  set_l _ _ _ _ := rfl
  ph_part _ _ := rfl
  set_part _ _ _ := rfl
  wx_l _ _ _ := Iff.rfl
  wx_part _ _ := Iff.rfl
  sx_l _ _ _ := Iff.rfl
  sx_part _ _ := Iff.rfl
  own _ _ _ _ _ _ _ hu hY _ hs hk hL _ := U_own (.inr (.inr rfl)) hu hY hs hk hL rfl rfl
  step := estep

/-- **The protocol has the lock**, for the threads that run its code (`ok`). -/
theorem fitsL : (L Lo).FitsOn (proto Lo prodOf) (U Lo) ok :=
  ⟨fun _ _ => Iff.rfl, fun _ h => h.1, fun _ h => h.1, fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl,
    stable, fun _ _ _ t _ hu => atStop t hu⟩

end Handoff
end Zig
