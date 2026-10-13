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

/-- The event: its place is `X.e`; `main` waits. -/
def E : FEvent Gh where
  W := Lo.WV
  ph g := g.2.e
  set g p := (g.1, { g.2 with e := p })
  ph_set _ _ := rfl
  set_set _ _ _ := rfl
  set_self _ := rfl
  wx g := g.2.ph.isMain
  wx_set _ _ := Iff.rfl

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
    hu.einv.lstep hu.wv apV hok.2.1 (fun _ _ _ => rfl) (fun _ _ _ => Iff.rfl) hs,
    by rw [hX]; exact hu.places, fun h1 => ?_, ?_, fun h0 => ?_, fun h1 => ?_,
    fun i jr sn e hr => ?_, fun h0 h1 => ?_, fun h1 => ?_, fun w hw => ?_⟩
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
    hu.einv.frame (t := t) (fun _ _ => rfl) rfl rfl rfl rfl (fun _ => VClock.le_refl _) id,
    hu.places, hu.ep1, hu.ep0, hu.ent, hu.hold, hu.reg, hu.lvc, hu.fin, hu.q⟩

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
      (fun h => by rw [upd_self]; show g.2.ph.isMain; rw [hX]; exact h),
    by rw [hX']; exact hu.places, fun h1 => ?_, ?_, fun h0 => ?_, fun h1 => ?_,
    fun i jr sn e hr => ?_, fun h0 h1 => ?_, fun h1 => ?_, fun w hw => ?_⟩
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

variable {prodOf : Tgt → Option Ptr}

/-- **The protocol has the lock**, for the threads that run its code (`ok`). -/
theorem fitsL : (L Lo).FitsOn (proto Lo prodOf) (U Lo) ok :=
  ⟨fun _ _ => Iff.rfl, fun _ h => h.1, fun _ h => h.1, fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl,
    stable, fun _ _ _ t _ hu => atStop t hu⟩

end Handoff
end Zig
