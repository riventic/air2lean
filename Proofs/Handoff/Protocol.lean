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
- **The rest `U`**: the threads (`Shape`), and what the contracts need: the epoch has its first
  write only until the producer signals (`ep1`) and moves at most once, with no post possible
  after it (`ep2`, `epS`, `incE`: the window `Fits.win`); while `main` is in the condition's
  critical code the producer is before its lock (`ent`: `hent`; only `main` registers, so
  `hroom`); every registration (a state write with `waiters` from 0 to 1, `FCond.RegW`) happened
  before the producer (`reg`, through the mutex's release and acquire), a registered `main` has
  one waiter from its registration on (`w1`), and inside `signal` the producer's call snapshot
  (`X.sz`) covers every registration (`snap`): with `FCond.SigPost.one` the signal's post says
  `main` is signalled (`signal_sig`, `lvc`); after the producer's end the event is set (`fin`):
  `hlive`.
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

/-- A thread's places (module doc). `sz` is the producer's call snapshot inside its `signal`: the
number of the state's writes at the call. -/
structure X where
  ph : Ph := .none
  c : CPh := .out
  e : EPh := .out
  sz : Option Nat := none

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

/-- The event: its place is `X.e`; `main` waits (from its event wait on), the producer sets (from
its `set` on: the role stays at its end, so its end keeps the event's invariant). -/
def E : FEvent Gh where
  W := Lo.WV
  ph g := g.2.e
  set g p := (g.1, { g.2 with e := p })
  ph_set _ _ := rfl
  set_set _ _ _ := rfl
  set_self _ := rfl
  wx g := g.2.ph = .ev ∨ g.2.ph = .joins
  wx_set _ _ := Iff.rfl
  sx g := g.2.ph = .st ∨ g.2.ph = .fin
  sx_set _ _ := Iff.rfl

/-- The threads that run the lock's code: out of the condition's busy code and of the event's
code, and not the producer while it holds the mutex (`Full/Cond.lean`, `CPh.busy`). -/
def ok (g : Gh) : Prop :=
  (g.2.c).busy = false ∧ g.2.e = .out ∧ g.2.ph ≠ .hl ∧ g.2.ph ≠ .v7

/-- The accesses to the bytes of `io` (`0 .. io` of the `Box`; a zero-length access touches
none). -/
def IoR (e : FootprintEntry) : Prop := e.block = 0 ∧ 0 < e.len ∧ e.off < Lo.io

/-- The bytes of `io` and the `Box`'s full extent, in the protocol's rest. The extent pins the
block (its size and kind) for every thread's step, so the cells of the shared words in the rest
are the memory's at every stop (`Rest`, `Word.InRest`). -/
def IoRest (r : Res) : Prop :=
  ∃ A bs, A % Lo.align = 0 ∧ bs.size = Lo.io ∧ (Lo.io = Enc.size Io → Enc.decode bs = pure (⟨⟩ : Io)) ∧
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
  /-- Until the producer signals, the epoch has its first write. -/
  ep1 : (G 1).2.ph.sigd = false → (Lo.WE.hist m).size = 1
  /-- The epoch moves at most once: the producer's one `epoch += 1`, after its post, which
  leaves no room for another post (`incE`, `epS`). This gives the window (`fitsC`). -/
  ep2 : (Lo.WE.hist m).size ≤ 2
  epS : (Lo.WE.hist m).size = 2 → (C Lo).Sated m
  incE : ∀ q n h, (G 1).2.c = .inc q n h → (Lo.WE.hist m).size = 1 ∧ (C Lo).Sated m
  /-- `main` in the condition's critical code: the producer is before its lock. -/
  ent : ((G 0).2.c).crit → (G 1).2.ph = .lk
  /-- The producer holds the mutex between its lock and its store of `ready`. -/
  hold : (G 1).2.ph = .hl ∨ (G 1).2.ph = .v7 → (G 1).1.ph = .holds
  /-- A registration happened before the producer, or before the mutex's release while the
  producer is before its lock (`main` registers holding the mutex). -/
  reg : ∀ j, (C Lo).RegW m j →
    VClock.le ((C Lo).S.hist m)[j]!.clock (m.clocks[1]!) = true ∨
    ((G 1).2.ph = .lk ∧ (((G 0).1.ph = .holds ∧
      VClock.le ((C Lo).S.hist m)[j]!.clock (m.clocks[0]!) = true) ∨
      (L Lo).Before m ((C Lo).S.hist m)[j]!.clock))
  /-- A registered `main` has its registration, and one waiter from it on (the client's history
  fact of `FCond.SigPost.one`). -/
  w1 : ((G 0).2.c).isReg → ∃ j, (C Lo).RegW m j ∧
    ∀ p, j ≤ p → p < ((C Lo).S.hist m).size → FCond.wOf ((C Lo).S.hist m)[p]! = 1
  /-- Inside its `signal`, the producer's call snapshot `n` covers every registration (no
  registration while the producer is past its lock). -/
  snap : ∀ n, (G 1).2.sz = some n → (G 1).2.ph = .sg ∧ ∀ j, (C Lo).RegW m j → j < n
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
  init tgt g := prodOf tgt = some bPtr ∧ ∃ rp, plain rp ∧ g = (⟨.out, rp, rnil⟩, { ph := .lk })
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

/-! ## The state's writes -/

/-- The newest `waiters` when only `main` registers: 1 if it is registered, else 0
(`FCond.Inv.cnt`). -/
theorem wlast {G : ThreadId → Gh} {m : Mem} (hI : (C Lo).Inv (L Lo) G m)
    (h0 : ∀ u, ((G u).2.c).isReg = true → u = 0) :
    FCond.wOf ((C Lo).lastS m) = if ((G 0).2.c).isReg then 1 else 0 := by
  obtain ⟨T, hT, hw, -⟩ := hI.cnt
  rw [hw]
  unfold FCond.nreg
  rw [tsum_congr (h := fun u => if u = 0 then (if ((G 0).2.c).isReg then 1 else 0) else 0)
    (fun u _ => ?_)]
  · rcases Nat.eq_zero_or_pos T with rfl | hT0
    · have : (G 0).2.c = .out := hT 0 (Nat.le_refl _)
      rw [this]; rfl
    · exact tsum_point hT0 _
  · by_cases e : u = 0
    · subst e; rfl
    · simp only [e, ↓reduceIte]
      cases hr : ((G u).2.c).isReg
      · show (if ((G u).2.c).isReg = true then 1 else 0) = 0; rw [hr]; rfl
      · exact absurd (h0 u hr) e

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
  obtain ⟨rIO, ⟨A, bs, -, -, -, r₁, r₂, -, rfl, -, h2⟩, -, rfl⟩ := hr
  simp only at he
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
theorem io_notL {e : FootprintEntry} (h : e.off = (L Lo).o) : ¬ IoR Lo e := fun ⟨_, _, h2⟩ => by
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

/-- **`U` after a step that keeps the threads' places (`ph`, `c`, `sz`) and the state's and the
epoch's writes**: the fields that read only these carry over (`places`, `ep1`, `ep2`, `epS`,
`incE`, `ent`, `w1`, `snap`, `lvc`, `xc`). The step gives the others, with `hold`, `reg` and `fin`
at the old places and `reg` for the old registrations. -/
theorem U.congrHist {G G' : ThreadId → Gh} {rX rX' : Res} {m m' : Mem} (hu : U Lo G rX m)
    (hX : ∀ u, (G' u).2.ph = (G u).2.ph ∧ (G' u).2.c = (G u).2.c ∧ (G' u).2.sz = (G u).2.sz)
    (hhS : Lo.WS.hist m' = Lo.WS.hist m) (hhE : Lo.WE.hist m' = Lo.WE.hist m)
    (shape : Shape (fun u => (G' u).2) m') (io : ReadShared (IoR Lo) m') (rest : Rest Lo rX' m')
    (blk : BlkOk Lo m') (ws : Lo.WS.Ok m') (we : Lo.WE.Ok m') (wv : Lo.WV.Ok m')
    (cinv : (C Lo).Inv (L Lo) G' m') (einv : (E Lo).Inv (L Lo) G' m')
    (hold : (G 1).2.ph = .hl ∨ (G 1).2.ph = .v7 → (G' 1).1.ph = .holds)
    (reg : ∀ j, (C Lo).RegW m j →
      VClock.le ((C Lo).S.hist m)[j]!.clock (m'.clocks[1]!) = true ∨
      ((G 1).2.ph = .lk ∧ (((G' 0).1.ph = .holds ∧
        VClock.le ((C Lo).S.hist m)[j]!.clock (m'.clocks[0]!) = true) ∨
        (L Lo).Before m' ((C Lo).S.hist m)[j]!.clock)))
    (fin : (G 1).2.ph = .fin → (E Lo).IsSet m')
    (q : ∀ w ∈ m'.waiters, w.2 = (L Lo).ptr ∨ w.2 = Lo.WE.ptr ∨ w.2 = Lo.WV.ptr) :
    U Lo G' rX' m' := by
  have hS : (C Lo).S.hist m' = (C Lo).S.hist m := hhS
  refine ⟨shape, io, rest, blk, ws, we, wv, cinv, einv, by rw [(hX 1).2.1]; exact hu.places,
    fun h => by rw [(hX 1).1] at h; rw [hhE]; exact hu.ep1 h, by rw [hhE]; exact hu.ep2,
    fun h => (FCond.Sated.congr hS).mpr (hu.epS (by rw [← hhE]; exact h)),
    fun q' n h hq => by
      rw [(hX 1).2.1] at hq; rw [hhE]
      exact ⟨(hu.incE q' n h hq).1, (FCond.Sated.congr hS).mpr (hu.incE q' n h hq).2⟩,
    fun h => by rw [(hX 0).2.1] at h; rw [(hX 1).1]; exact hu.ent h,
    fun h => by rw [(hX 1).1] at h; exact hold h,
    fun j hj => by rw [hS, (hX 1).1]; exact reg j ((FCond.RegW.congr hS).mp hj),
    fun h => by
      rw [(hX 0).2.1] at h; obtain ⟨j, hj, hp⟩ := hu.w1 h
      exact ⟨j, (FCond.RegW.congr hS).mpr hj, by rw [hS]; exact hp⟩,
    fun n h => by
      rw [(hX 1).2.2] at h; rw [(hX 1).1]
      exact ⟨(hu.snap n h).1, fun j hj => (hu.snap n h).2 j ((FCond.RegW.congr hS).mp hj)⟩,
    fun h0 h1 => by
      rw [(hX 0).2.1] at h0; rw [(hX 1).1] at h1
      exact (FCond.Signalled.congr hS).mpr (hu.lvc h0 h1),
    fun h => by rw [(hX 1).1] at h; exact fin h, q,
    fun u h => by rw [(hX u).2.1] at h; rw [(hX u).1]; exact hu.xc u h⟩

/-- **A step of the lock's code keeps `U`** (`FLock.Fits.stable`). -/
theorem stable (G : ThreadId → Gh) (rX : Res) (m m' : Mem) (t : ThreadId) (p : LPh) (h : Res)
    (hok : ok (G t)) (_ : (L Lo).ph (G t) ≠ .gone) (hna : (L Lo).ph (G t) ≠ .away)
    (hu : U Lo G rX m) (hs : (L Lo).Step t m m')
    (hrel : (L Lo).ph (G t) = .holds → p ≠ .holds → (L Lo).Before m' (m.clocks[t]!)) :
    U Lo (upd G t ((L Lo).set (G t) p h)) rX m' := by
  have hX : ∀ u, (upd G t ((L Lo).set (G t) p h) u).2 = (G u).2 := fun u => congrFun (FLock.snd_set G t p h) u
  obtain ⟨hwS, hhS⟩ := hu.ws.lockStep hs apS
  obtain ⟨hwE, hhE⟩ := hu.we.lockStep hs apE
  obtain ⟨hwV, hhV⟩ := hu.wv.lockStep hs apV
  refine hu.congrHist (fun u => by rw [hX u]; exact ⟨rfl, rfl, rfl⟩) hhS hhE ?_
    (fun e he hr => ?_) (hu.rest.congr fun l hl => hs.heap (box_notL hl)) (hu.blk.lstep hs)
    hwS hwE hwV (hu.cinv.lstep hu.ws hu.we apS apE hok.1 hna (fun _ _ _ => rfl) hs)
    (hu.einv.lstep hu.wv apV hok.2.1 (fun _ _ _ => rfl) (fun _ _ _ => Iff.rfl)
      (fun _ _ _ => Iff.rfl) hs)
    (fun h1 => ?_) (fun j hj => ?_) (fun h1 => ?_) (fun w hw => ?_)
  · have : (fun u => (upd G t ((L Lo).set (G t) p h) u).2) = fun u => (G u).2 := funext hX
    rw [this]; unfold Shape at *; rw [hs.threads]; exact hu.shape
  · rcases hs.fp e he with h' | ⟨-, ho', -⟩
    · rcases hu.io e h' hr with ⟨hk, h''⟩ | h''
      · exact .inl ⟨hk, hs.someLe h''⟩
      · exact .inr (hs.allLe h'')
    · exact absurd hr (io_notL ho')
  · by_cases ht : t = 1
    · subst ht; rcases h1 with h1 | h1
      · exact absurd h1 hok.2.2.1
      · exact absurd h1 hok.2.2.2
    · rw [upd_ne _ _ (Ne.symm ht)]; exact hu.hold h1
  · rcases hu.reg j hj with h' | ⟨hlk, h'⟩
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
  · show ((Lo.WV.hist m')[(Lo.WV.hist m').size - 1]!).Val _; rw [hhV]; exact hu.fin h1
  · by_cases hl : w.2 = (L Lo).ptr
    · exact .inl hl
    · exact hu.q w ((hs.waiters_mem w hl).mp hw)

/-- A stop keeps `U`: it reads no current thread. -/
theorem atStop {G : ThreadId → Gh} {rX : Res} {m : Mem} (t : ThreadId) (hu : U Lo G rX m) :
    U Lo G rX { m with current := t } :=
  have wordOk : ∀ W : Word 32 4, W.Ok m → W.Ok { m with current := t } :=
    fun _ hw => (hw.fields_native (m' := { m with current := t })
      rfl rfl rfl rfl (fun _ => VClock.le_refl _)).1
  ⟨hu.shape, hu.io, hu.rest, hu.blk, wordOk _ hu.ws, wordOk _ hu.we, wordOk _ hu.wv,
    hu.cinv.stay (m' := { m with current := t }) rfl rfl rfl (fun _ hw _ => hw) (fun _ _ h => h)
      (Nat.le_refl _) (fun _ => VClock.le_refl _),
    hu.einv.frame (t := t) (fun _ _ => rfl) rfl rfl rfl rfl (fun _ => VClock.le_refl _)
      (Nat.le_refl _) id id
      hu.einv.fresh,
    hu.places, hu.ep1, hu.ep2, hu.epS, hu.incE, hu.ent, hu.hold, hu.reg, hu.w1, hu.snap, hu.lvc,
    hu.fin, hu.q, hu.xc⟩

/-- The rest has the bytes of `io`. -/
theorem rest_io {rX : Res} {m : Mem} (hr : Rest Lo rX m) {x : Nat} (hx : x < Lo.io) :
    rX.heap (0, x) ≠ none := by
  obtain ⟨rIO, ⟨A, bs, -, hbs, -, r₁, r₂, -, rfl, h1, -⟩, -, rfl⟩ := hr
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

/-- Transport the protocol invariant using a native framed step and the three words'
validity and exact history. -/
theorem U_frame_native {G : ThreadId → Gh} {rX rX' : Res} {m m' : Mem} {t : ThreadId} {g : Gh}
    {hF : Heap} (hu : U Lo G rX m) (hs : FStepIn hF m m')
    (hio : ∀ x, x < Lo.io → hF (0, x) ≠ none)
    (hwL : ∀ x, (L Lo).o ≤ x → x < (L Lo).o + 4 → hF ((L Lo).b, x) ≠ none)
    (hwB : ∀ l, Lo.BoxW l → hF l ≠ none)
    (hok : ∀ i l, (L Lo).Loc m i l → l.len = 4) (hrest : Rest Lo rX' m') (hbk : BlkOk Lo m')
    (hwS : Lo.WS.Ok m') (hwE : Lo.WE.Ok m') (hwV : Lo.WV.Ok m')
    (hhS : Lo.WS.hist m' = Lo.WS.hist m)
    (hhE : Lo.WE.hist m' = Lo.WE.hist m)
    (hhV : Lo.WV.hist m' = Lo.WV.hist m)
    (hX : g.2 = (G t).2) (hph : g.1.ph = (G t).1.ph) : U Lo (upd G t g) rX' m' := by
  have hX' : ∀ u, (upd G t g u).2 = (G u).2 := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hX]
    · rw [upd_ne _ _ e]
  have hP' : ∀ u, (upd G t g u).1.ph = (G u).1.ph := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hph]
    · rw [upd_ne _ _ e]
  refine hu.congrHist (fun u => by rw [hX' u]; exact ⟨rfl, rfl, rfl⟩) hhS hhE ?_
    (fun e he hr => ?_) hrest hbk hwS hwE hwV
    (hu.cinv.other (t := t) (g' := g) (congrArg (·.c) hX) (fun _ => hph)
      (fun _ h => by show g.1.ph = _; rw [hph]; exact h)
      (fun h => by show g.2.ph = .sg; rw [hX]; exact h) hhS hhE (by rw [hs.waiters])
      (fun w hw _ => .inl (by rw [hs.waiters] at hw; exact hw))
      (fun _ _ _ h => by rw [hs.woken]; exact h) (Nat.le_of_eq (by rw [hs.threads])) hs.clock)
    (hu.einv.frame (fun u hu => upd_ne _ _ hu) (by rw [upd_self]; exact congrArg (·.e) hX)
      (by rw [upd_self]; exact hph) hhV hs.waiters hs.clock (Nat.le_of_eq (by rw [hs.threads]))
      (fun h => by rw [upd_self]; show g.2.ph = .ev ∨ g.2.ph = .joins; rw [hX]; exact h)
      (fun h => by rw [upd_self]; show g.2.ph = .st ∨ g.2.ph = .fin; rw [hX]; exact h)
      (hu.einv.fresh.fstep hs (fun x h1 h2 => hwB _ (Lo.wv_box ⟨rfl, h1, h2⟩))
        (fun i l hl => (hu.wv.loc i l hl).1)))
    (fun h1 => by rw [hP']; exact hu.hold h1) (fun j hj => ?_) (fun h1 => ?_)
    (fun w hw => by rw [hs.waiters] at hw; exact hu.q w hw)
  · have : (fun u => (upd G t g u).2) = fun u => (G u).2 := funext hX'
    rw [this]; unfold Shape at *; rw [hs.threads]; exact hu.shape
  · rcases hs.fp e he with ⟨e₀, he₀, hn⟩ | ⟨-, hnt, -⟩
    · obtain ⟨-, hb, hk, ho, hl, hc⟩ := hn
      rcases hu.io e₀ he₀ ⟨hb.symm.trans hr.1, by have := hr.2.1; omega,
        by have := hr.2.2; omega⟩ with ⟨hk', h''⟩ | h''
      · exact .inl ⟨hk.trans hk', LockWord.someLe_mono hs.threads (fun u _ => hs.clock u)
          (LockWord.someLe_le hc h'')⟩
      · exact .inr (LockWord.allLe_mono hs.threads (fun u _ => hs.clock u)
          fun u hu => VClock.le_trans hc (h'' u hu))
    · refine absurd ⟨e.off, Nat.le_refl _, by have := hr.2.1; omega, ?_⟩ hnt
      rw [hr.1]; exact hio _ hr.2.2
  · rw [hP']
    rcases hu.reg j hj with h' | ⟨hlk, h'⟩
    · exact .inl (VClock.le_trans h' (hs.clock 1))
    · refine .inr ⟨hlk, ?_⟩
      rcases h' with ⟨hh, hle⟩ | hb
      · exact .inl ⟨hh, VClock.le_trans hle (hs.clock 0)⟩
      · obtain ⟨i, l, hl, hle⟩ := hb
        obtain ⟨j, hl'⟩ := (LockWord.loc_fstep (L := (L Lo).toLockWord) hs hwL hok l).mpr ⟨i, hl⟩
        exact .inr ⟨j, l, hl', hle⟩
  · show ((Lo.WV.hist m')[(Lo.WV.hist m').size - 1]!).Val _; rw [hhV]; exact hu.fin h1

/-- `blk_of` for a rest whose ghost state is `io`'s. -/
theorem blk_ofG {G : ThreadId → Gh} {rX rIO : Res} {m : Mem} (hi : (L Lo).Inv G rX m)
    (hIO : IoRest Lo rIO) (hg : rX.gh = rIO.gh) : BlkOk Lo m := by
  obtain ⟨rL, ho, -⟩ := hi.rest
  obtain ⟨rT, -, hh⟩ := ho.holds
  have he := hh.swap.extTrue
  obtain ⟨A, bs, -, -, -, r₁, r₂, -, rfl, -, h2⟩ := hIO
  simp only at he
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

/-- The frame of a step on a part with the mutex's word and the rest `rX` (`FLock.Inv.wp_liftM`):
it has the rest's bytes, and the mutex's. -/
theorem frame_rest {rX : Res} {m : Mem} {l : Zig.Loc} (h : rX.heap.erase l ≠ none) :
    (rsum ((L Lo).wordR m) rX).heap.erase l ≠ none := by
  simp only [rsum, FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
    Option.or_eq_none_iff, not_and] at h ⊢
  intro _; exact h

theorem frame_word {G : ThreadId → Gh} {rX : Res} {m : Mem} (hi : (L Lo).Inv G rX m) {x : Nat}
    (h1 : (L Lo).o ≤ x) (h2 : x < (L Lo).o + 4) :
    (rsum ((L Lo).wordR m) rX).heap.erase ((L Lo).b, x) ≠ none := by
  have := LockWord.wordR_some hi.w.blk (l := ((L Lo).b, x)) ⟨rfl, h1, h2⟩
  simp only [rsum, FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
    Option.or_eq_none_iff, not_and]
  intro h; exact absurd h this

/-- **A step of `t` on its own part keeps `U`** (an `FStepIn` that keeps the mutex's word and the
rest, `FLock.Inv.wp_liftM`), with `t`'s new ghost value `g` at the same places (a new part or
held resource); the lock's invariant after it (with any ghost values `G'`) pins the `Box`. -/
theorem U_stepIn {G G₀ G' : ThreadId → Gh} {rX : Res} {m m' : Mem} {t : ThreadId} {g : Gh}
    (hu : U Lo G rX m) (hi : (L Lo).Inv G₀ rX m)
    (hs : FStepIn (rsum ((L Lo).wordR m) rX).heap.erase m m') (hi' : (L Lo).Inv G' rX m')
    (hX : g.2 = (G t).2) (hph : g.1.ph = (G t).1.ph) : U Lo (upd G t g) rX m' := by
  have hcs := cells_same hu.blk hi' hu.rest
  have facts : ∀ (W : Word 32 4), (∀ l, W.In l → Lo.BoxW l) → W.Ok m →
      W.Ok m' ∧ W.hist m' = W.hist m := by
    intro W hW hw
    have hcover : ∀ l, W.In l →
        (rsum ((L Lo).wordR m) rX).heap.erase l ≠ none :=
      fun l hl => frame_rest (rest_box hu.rest (fun _ => box_live hu) (hW l hl))
    have hnorm : ∀ l, W.In l →
        (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm := by
      intro l hl
      rw [hcs l (hW l hl)]
    exact ⟨hw.fstep hs hcover hnorm, Word.hist_fstep hw hs hcover hnorm⟩
  obtain ⟨hwS, hhS⟩ := facts _ (fun _ => Lo.ws_box) hu.ws
  obtain ⟨hwE, hhE⟩ := facts _ (fun _ => Lo.we_box) hu.we
  obtain ⟨hwV, hhV⟩ := facts _ (fun _ => Lo.wv_box) hu.wv
  exact U_frame_native hu hs
    (fun x hx => frame_rest (by simpa [FHeap.erase] using rest_io hu.rest hx))
    (fun x h1 h2 => frame_word hi h1 h2)
    (fun l hl => frame_rest (rest_box hu.rest (fun _ => box_live hu) hl))
    (fun i l hl => (hi.w.loc.ok i l hl).1)
    (hu.rest.congr hcs) (blk_of hi' hu.rest) hwS hwE hwV hhS hhE hhV hX hph

/-- Transport an own-part step using native word validity and exact history. -/
theorem U_own_native {G : ThreadId → Gh} {rY : Res} {m m' : Mem} {t : ThreadId} {g : Gh}
    {W : Word 32 4} (hW3 : W = Lo.WS ∨ W = Lo.WE ∨ W = Lo.WV)
    (hu : U Lo G (rsum (W.cellsR m) rY) m) (hi : (L Lo).Inv G (rsum (W.cellsR m) rY) m)
    (hY : ∀ l, W.In l → rY.heap l = none)
    (hs : FStepIn (rsum ((L Lo).wordR m) (rsum (W.cellsR m) rY)).heap.erase m m')
    (hw' : W.Ok m') (hh : W.hist m' = W.hist m)
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
  have facts : ∀ W', (W' = Lo.WS ∨ W' = Lo.WE ∨ W' = Lo.WV) →
      W'.Ok m' ∧ W'.hist m' = W'.hist m := by
    intro W' hW'
    rcases three_apart hW3 hW' with rfl | hap
    · exact ⟨hw', hh⟩
    · have hw : W'.Ok m := by
        rcases hW' with rfl | rfl | rfl
        · exact hu.ws
        · exact hu.we
        · exact hu.wv
      have hcover : ∀ l, W'.In l →
          (rsum ((L Lo).wordR m) (rsum (W.cellsR m) rY)).heap.erase l ≠ none :=
        fun l hl => frame_rest
          (rest_box hu.rest (fun _ => box_live hu) (three_box hW' l hl))
      have hnorm : ∀ l, W'.In l →
          (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm := by
        intro l hl
        rw [hcs l (three_box hW' l hl) (hap l hl)]
      exact ⟨hw.fstep hs hcover hnorm, Word.hist_fstep hw hs hcover hnorm⟩
  obtain ⟨hwS, hhS⟩ := facts _ (.inl rfl)
  obtain ⟨hwE, hhE⟩ := facts _ (.inr (.inl rfl))
  obtain ⟨hwV, hhV⟩ := facts _ (.inr (.inr rfl))
  exact U_frame_native hu hs
    (fun x hx => frame_rest (by simpa [FHeap.erase] using rest_io hu.rest hx))
    (fun x h1 h2 => frame_word hi h1 h2)
    (fun l hl => frame_rest (rest_box hu.rest (fun _ => box_live hu) hl))
    (fun i l hl => (hi.w.loc.ok i l hl).1) hrest hbk'
    hwS hwE hwV hhS hhE hhV hX hph

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

/-- Two of the three words: the same, or apart (`FCond.MStep.word`, `FEvent.MStep.word`). -/
theorem three_word {W W' : Word 32 4} (h : Three Lo W) (h' : Three Lo W') :
    W' = W ∨ W.b ≠ W'.b ∨ W.o + 4 ≤ W'.o ∨ W'.o + 4 ≤ W.o :=
  (three_apart h h').imp_right apart_of

/-- An access at one of the three words is in the `Box` past the mutex. -/
theorem three_fp {e : FootprintEntry} {W : Word 32 4} (hW : Three Lo W)
    (h : e.block = W.b ∧ e.off = W.o) : e.block = 0 ∧ Lo.so ≤ e.off :=
  ⟨h.1.trans (three_b hW), h.2 ▸ three_o hW⟩

/-- The `Box` after a step that keeps each block as live, as large and of the same kind
(`FCond.MStep.block`, `FEvent.MStep.block`). -/
theorem BlkOk.of_block {m m' : Mem} (h : BlkOk Lo m)
    (hb : ∀ (b : BlockId) (blk : Block), m.blocks[b]? = some blk → ∃ blk', m'.blocks[b]? = some blk' ∧
      blk'.live = blk.live ∧ blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind) :
    BlkOk Lo m' := by
  obtain ⟨blk, h1, h2, h3, h4⟩ := h
  obtain ⟨blk', e1, e2, e3, e4⟩ := hb _ _ h1
  exact ⟨blk', e1, by rw [e2]; exact h2, by rw [e3]; exact h3, by rw [e4]; exact h4⟩

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
    have h : (G u).2.ph = .st ∨ (G u).2.ph = .fin := hu.einv.sx u he
    rcases h with h | h <;> rcases hx with h' | h' <;> rw [h'] at h <;> cases h
  | sd =>
    have h : (G u).2.ph = .st ∨ (G u).2.ph = .fin := hu.einv.sdx u he
    rcases h with h | h <;> rcases hx with h' | h' <;> rw [h'] at h <;> cases h

/-- Only `main` waits at the condition (`xc`, `places`). -/
theorem U.wait0 {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U Lo G rX m) {u : ThreadId}
    (h : ((G u).2.c).waits = true) : u = 0 := by
  rcases hu.xc u (fun hc => by rw [hc] at h; cases h) with h' | h'
  · exact hu.shape.zero (u := u) (by rw [h']; rfl)
  · have := hu.shape.one (u := u) (by rw [h']; rfl)
    subst this
    rw [hu.places] at h; cases h

/-- Only the producer, in its `signal`, is at a signaller's place (`FCond.Inv.sx`). -/
theorem U.sig1 {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U Lo G rX m) {u : ThreadId}
    (h : ((G u).2.c).sig = true) : u = 1 ∧ (G u).2.ph = .sg := by
  have h2 : (G u).2.ph = .sg := hu.cinv.sx u h
  exact ⟨hu.shape.one (u := u) (by rw [h2]; rfl), h2⟩

/-- **A step of the condition's code keeps `U`** (`FLock.Fits.kstep` of `FCond.prim`). -/
theorem cstep (G : ThreadId → Gh) (rY : Res) (m m' : Mem) (t : ThreadId) (p : CPh) (q : LPh)
    (h : Res) (W : Word 32 4) (hW : W = (C Lo).S ∨ W = (C Lo).Ep)
    (hn : CPh.Next ((C Lo).ph (G t)) p)
    (hq : (q = (L Lo).ph (G t) ∧ h = (L Lo).held (G t)) ∨
      (((L Lo).ph (G t) = .out ∨ ((L Lo).ph (G t) = .away ∧ ((C Lo).ph (G t)).isReg = true)) ∧
        (q = .out ∨ (q = .away ∧ p.waits = true)) ∧ h = rnil))
    (hu : U Lo G (rsum (W.cellsR m) rY) m) (hY : ∀ l, W.In l → rY.heap l = none)
    (hs : (C Lo).MStep W t m m')
    (hEp : (C Lo).Ep.hist m' = (C Lo).Ep.hist m ∨
      ∃ q n h, (C Lo).ph (G t) = .inc q n h ∧ p = .wk n q h)
    (hpost : ∀ sh c q n h, (C Lo).ph (G t) = .sl sh c → p = .inc q n h →
      ((C Lo).S.hist m').size = ((C Lo).S.hist m).size + 1)
    (hI : (C Lo).Inv (L Lo) (upd G t ((L Lo).set ((C Lo).set (G t) p) q h)) m') :
    U Lo (upd G t ((L Lo).set ((C Lo).set (G t) p) q h)) (rsum (W.cellsR m') rY) m' := by
  have hW3 : Three Lo W := hW.imp id .inl
  -- what the step does to the memory (`FCond.MStep.*`)
  have hth := hs.threads
  have hclk := hs.clocks
  have hcells : ∀ l, ¬ W.In l → m'.heap l = m.heap l := fun _ h => hs.cells h
  have hblk : BlkOk Lo m → BlkOk Lo m' := fun h => h.of_block fun _ _ hb => hs.block hb
  have hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ (e.block = 0 ∧ Lo.so ≤ e.off) := fun _ he =>
    (hs.fp he).imp_right fun h => h.elim (three_fp hW3) (three_fp (.inr (.inl rfl)))
  have hbef : ∀ c, (L Lo).Before m c → (L Lo).Before m' c := fun _ ⟨i, l, hl, hc⟩ =>
    ⟨i, l, hs.lockLoc (three_ap hW3) apE hl, hc⟩
  have hwt : ∀ w ∈ m'.waiters, w ∈ m.waiters ∨ w = (t, Lo.WE.ptr) := fun _ hw => hs.waiters hw
  have hwd := fun W' (hW' : Three Lo W') (h : W'.Ok m) =>
    hs.word h (three_word hW3 hW') (three_word (W := Lo.WE) (.inr (.inl rfl)) hW')
  have hok3 := fun W' (hW' : Three Lo W') (h : W'.Ok m) => (hwd W' hW' h).1
  have hhist := fun W' (hW' : Three Lo W') (h : W'.Ok m) => (hwd W' hW' h).2
  have hn' : CPh.Next ((G t).2.c) p := hn
  -- the new ghost values
  obtain ⟨G', hG'⟩ : ∃ G', G' = upd G t ((L Lo).set ((C Lo).set (G t) p) q h) := ⟨_, rfl⟩
  rw [← hG'] at hI ⊢
  have hG : ∀ u, u ≠ t → G' u = G u := fun u hu => by rw [hG']; exact upd_ne _ _ hu
  have hXt : (G' t).2 = { (G t).2 with c := p } := by rw [hG', upd_self]; rfl
  have hLt : (G' t).1.ph = q := by rw [hG', upd_self]; rfl
  have hph : ∀ u, (G' u).2.ph = (G u).2.ph ∧ (G' u).2.e = (G u).2.e ∧
      (G' u).2.sz = (G u).2.sz := fun u => by
    by_cases e : u = t
    · subst e; rw [hXt]; exact ⟨rfl, rfl, rfl⟩
    · rw [hG u e]; exact ⟨rfl, rfl, rfl⟩
  have hcw : ∀ u, ((G' u).2.c).waits = true → ((G u).2.c).waits = true := fun u hw => by
    by_cases e : u = t
    · subst e; rw [hXt] at hw; exact CPh.Next.waits hn hw
    · rwa [hG u e] at hw
  have hcc : ∀ u, ((G' u).2.c).crit = true → ((G u).2.c).crit = true := fun u hw => by
    by_cases e : u = t
    · subst e; rw [hXt] at hw; exact CPh.Next.crit hn hw
    · rwa [hG u e] at hw
  have hinc : p.sig = true → (G t).2.ph = .sg := fun hp => by
    have := hI.sx t (by show ((G' t).2.c).sig = true; rw [hXt]; exact hp)
    have h2 : (G' t).2.ph = .sg := this
    rw [(hph t).1] at h2; exact h2
  -- only `main` registers, from its critical code (the producer is then before its lock)
  have hr0' : ∀ u, ((G' u).2.c).isReg = true → u = 0 := fun u hr =>
    hu.wait0 (hcw u (CPh.isReg_waits hr))
  have hwl := wlast hu.cinv fun u hr => hu.wait0 (CPh.isReg_waits hr)
  have hwl' := wlast hI hr0'
  have henter : ((G' 0).2.c).isReg = true → ((G 0).2.c).isReg = false →
      t = 0 ∧ ((G 0).2.c).crit = true := fun h1 h2 => by
    by_cases et : t = 0
    · subst et; rw [hXt] at h1; exact ⟨rfl, hn'.crit_of_reg h1 h2⟩
    · rw [hG 0 (Ne.symm et)] at h1; rw [h1] at h2; cases h2
  have hnoreg : (G 1).2.ph ≠ .lk → ((G' 0).2.c).isReg = true → ((G 0).2.c).isReg = true :=
    fun hl h1 => by
      cases h2 : ((G 0).2.c).isReg
      · exact absurd (hu.ent (henter h1 h2).2) hl
      · rfl
  -- the state's writes: the same, or the stepping thread's new write
  have hpos : 0 < ((C Lo).S.hist m).size := hu.cinv.spos
  have hSh : (C Lo).S.hist m' = (C Lo).S.hist m ∨
      ∃ x : Word.Entry, x.clock = m'.clocks[t]! ∧
        (C Lo).S.hist m' = ((C Lo).S.hist m).push x := by
    rcases (hs.word_rmw hu.ws (three_word hW3 (.inl rfl))
      (three_word (W := Lo.WE) (.inr (.inl rfl)) (.inl rfl))).2 with e | ⟨-, ord, v, e⟩
    · exact .inl e
    · exact .inr ⟨_, rfl, e⟩
  have hwx : ∀ x, (C Lo).S.hist m' = ((C Lo).S.hist m).push x →
      FCond.wOf x = if ((G' 0).2.c).isReg then 1 else 0 := fun x e => by
    rw [← FCond.lastS_push e]; exact hwl'
  have hwle : (G 1).2.ph ≠ .lk → ∀ x, (C Lo).S.hist m' = ((C Lo).S.hist m).push x →
      FCond.wOf x ≤ FCond.wOf ((C Lo).lastS m) := fun hl x e => by
    rw [hwx x e, hwl]
    cases h1 : ((G' 0).2.c).isReg
    · simp
    · simp [hnoreg hl h1]
  -- `signals = waiters` stays while the producer is past its lock
  have hSW : (G 1).2.ph ≠ .lk → (C Lo).Sated m → (C Lo).Sated m' := fun hl hsw => by
    rcases hSh with e | ⟨x, -, e⟩
    · exact (FCond.Sated.congr e).mpr hsw
    · exact hI.sated_push hpos e hsw (hwle hl x e)
  -- the epoch's writes: the same, or the `epoch += 1` of a signaller at `inc`
  have hEp' : Lo.WE.hist m' = Lo.WE.hist m ∨
      ∃ q n h', (G t).2.c = .inc q n h' ∧ p = .wk n q h' := hEp
  have hEh : Lo.WE.hist m' = Lo.WE.hist m ∨ ∃ x, Lo.WE.hist m' = (Lo.WE.hist m).push x :=
    (hhist _ (.inr (.inl rfl)) hu.we).imp_right fun ⟨_, x, e⟩ => ⟨x, e⟩
  -- the lock place of `t` changes only for a waiter
  have hlq : (L Lo).ph (G t) ≠ (G' t).1.ph →
      ((L Lo).ph (G t) = .out ∨ (L Lo).ph (G t) = .away) ∧
        (q = .out ∨ (q = .away ∧ p.waits = true)) := fun hne => by
    rcases hq with ⟨rfl, -⟩ | ⟨h1, h2, -⟩
    · exact absurd hLt.symm hne
    · exact ⟨h1.imp_right And.left, h2⟩
  have hV : Lo.WV.hist m' = Lo.WV.hist m := by
    rcases hhist _ (.inr (.inr rfl)) hu.wv with e | ⟨e, -⟩
    · exact e
    · rcases hW with rfl | rfl
      · exact absurd e ne_VS
      · exact absurd e ne_VE
  have hVW : ∀ l, Lo.WV.In l → ¬ W.In l := by
    rcases three_apart hW3 (.inr (.inr rfl)) with heq | hap
    · rcases hW with rfl | rfl
      · exact False.elim (ne_VS heq)
      · exact False.elim (ne_VE heq)
    · exact hap
  have hoff : ∀ x, W.o ≤ x → x < W.o + 4 → (Lo.WV.cellsR m).heap.erase (W.b, x) = none := by
    intro x h1 h2
    have hn : ¬ Lo.WV.In (W.b, x) := fun hl => hVW _ hl ⟨rfl, h1, h2⟩
    simp [FHeap.erase, Word.cellsR, cellsAt_none hn]
  obtain ⟨σ, hA⟩ := hs.atomics (Lo.WV.cellsR m).heap.erase hoff
  have hFV : Lo.WV.Fresh m' := Word.Fresh.amap
    (m := { m with current := t }) (m' := { m' with current := t }) hu.einv.fresh hA hs.nextMsg
    (fun x h1 h2 => by
      have hcell := cellsAt_some (W := Lo.WV.In) (l := (Lo.WV.b, x)) ⟨rfl, h1, h2⟩
        (hu.wv.cellIn ⟨rfl, h1, h2⟩) (m := m)
      intro hnone
      exact hcell (Option.map_eq_none_iff.mp hnone))
    (fun i l hl => (hu.wv.loc i l hl).1)
  -- a new waiter in the futex queue is `t` at the epoch, registered
  have hnw : ∀ w ∈ m'.waiters, w ∈ m.waiters ∨ (w = (t, Lo.WE.ptr) ∧ ((G t).2.c).waits = true) :=
    fun w hw => by
      rcases hwt w hw with h' | rfl
      · exact .inl h'
      · obtain ⟨i, jr, e, h1, -⟩ := hI.q _ hw rfl
        refine .inr ⟨rfl, hcw t ?_⟩
        have : (G' t).2.c = _ := h1
        rw [this]; rfl
  refine ⟨?_, fun e he hr => ?_, Rest.step (three_box hW3) hu.rest rfl hY fun l _ hw => hcells l hw,
    hblk hu.blk, hok3 _ (.inl rfl) hu.ws, hok3 _ (.inr (.inl rfl)) hu.we,
    hok3 _ (.inr (.inr rfl)) hu.wv, hI, ?_, ?_, fun h1 => ?_, ?_, fun h2 => ?_,
    fun q' n h' hq' => ?_, fun h0 => ?_, fun h1 => ?_, fun j hj => ?_, fun h0 => ?_,
    fun n hn => ?_, fun h0 h1 => ?_, fun h1 => ?_, fun w hw => ?_, fun u hu' => ?_⟩
  · -- shape
    refine Shape.congr hu.shape hth (fun u => (hph u).1) fun u hfr => ?_
    by_cases e : u = t
    · subst e
      have hc : (G u).2.c = .out := by rcases hfr with h' | h' <;> rw [h']
      have hp : p = .out := by
        rcases CPh.Next.of_out (hc ▸ hn') with h' | h'
        · exact h'
        · have := hinc h'
          rcases hfr with h'' | h'' <;> rw [h''] at this <;> cases this
      rw [hXt, hp, ← hc]
    · rw [hG u e]
  · -- io
    rcases hfp e he with h' | ⟨hb, ho⟩
    · rcases hu.io e h' hr with ⟨hk, h''⟩ | h''
      · exact .inl ⟨hk, LockWord.someLe_mono hth (fun u _ => hclk u) h''⟩
      · exact .inr (LockWord.allLe_mono hth (fun u _ => hclk u) h'')
    · have := Lo.ok; have := hr.2.2; omega
  · -- the event's invariant
    refine hu.einv.other (fun u hu => hG u hu) (hph t).2.1 (fun hne => ?_) hV (fun w hw => ?_)
      hclk (Nat.le_of_eq (by rw [hth])) (fun h' => by show (_ = _ ∨ _ = _); rw [(hph t).1]; exact h')
      (fun h' => by show (_ = _ ∨ _ = _); rw [(hph t).1]; exact h') hFV
    · by_cases hl : (L Lo).ph (G' t) = (L Lo).ph (G t)
      · exact .inl hl
      · obtain ⟨-, hq'⟩ := hlq (Ne.symm hl)
        rcases hq' with hq' | ⟨-, hw⟩
        · exact .inr (hLt.trans hq')
        · exact absurd (hu.e_out (fun hc => by
            rcases CPh.Next.of_out (hc ▸ hn') with h' | h'
            · rw [h'] at hw; cases hw
            · rw [CPh.sig_waits h'] at hw; cases hw)) hne
    · rcases hnw w hw with h' | ⟨rfl, hw'⟩
      · exact .inl h'
      · refine .inr ⟨rfl, ptr_EV, fun he => ?_⟩
        have := hu.e_out (u := t) (fun hc => by rw [hc] at hw'; cases hw')
        rw [show (E Lo).ph (G t) = (G t).2.e from rfl, this] at he; cases he
  · -- places
    cases hw : ((G' 1).2.c).waits
    · rfl
    · have := hcw 1 hw; rw [hu.places] at this; cases this
  · -- ep1
    rw [(hph 1).1] at h1
    rcases hEp' with e | ⟨_, _, _, e, -⟩
    · rw [e]; exact hu.ep1 h1
    · obtain ⟨rfl, h3⟩ := hu.sig1 (u := t) (by rw [e]; rfl)
      rw [h3] at h1; cases h1
  · -- ep2: the epoch moves only at the producer's `inc`, with one write (`incE`)
    rcases hEp' with e | ⟨q₀, n₀, h₀, e, -⟩
    · rw [e]; exact hu.ep2
    · obtain ⟨rfl, -⟩ := hu.sig1 (u := t) (by rw [e]; rfl)
      have h1 := (hu.incE q₀ n₀ h₀ e).1
      rcases hEh with e' | ⟨x, e'⟩ <;> rw [e'] <;> simp [h1]
  · -- epS
    rcases hEp' with e | ⟨q₀, n₀, h₀, e, -⟩
    · rw [e] at h2
      have hl : (G 1).2.ph ≠ .lk := fun hl => by
        have := hu.ep1 (by rw [hl]; rfl); omega
      exact hSW hl (hu.epS h2)
    · obtain ⟨rfl, hsg⟩ := hu.sig1 (u := t) (by rw [e]; rfl)
      have hinc1 := hu.incE q₀ n₀ h₀ e
      exact hSW (by rw [hsg]; nofun) hinc1.2
  · -- incE
    by_cases et : t = 1
    · subst et
      have hp : p = .inc q' n h' := by rw [hXt] at hq'; exact hq'
      subst hp
      rcases hn'.to_inc with ⟨sh, c, hc⟩ | hc
      · -- `sl → inc`: the producer's post, the only one (`signals` reaches `waiters ≤ 1`)
        have hsz := hpost sh c q' n h' hc rfl
        obtain ⟨x, -, e⟩ := hSh.resolve_left fun e => by rw [e] at hsz; omega
        have hst := hI.step_push hpos e
        have hw0 : FCond.wOf x = FCond.wOf ((C Lo).lastS m) := by
          rw [hwx x e, hwl, hG 0 (by decide)]
        have hw1 : FCond.wOf x ≤ 1 := by rw [hwx x e]; split <;> omega
        have hE : Lo.WE.hist m' = Lo.WE.hist m := by
          rcases hEp' with e' | ⟨_, _, _, e', -⟩
          · exact e'
          · rw [hc] at e'; cases e'
        refine ⟨?_, ?_⟩
        · rw [hE]
          have h1 := FEvent.hist_pos hu.we
          have h2 := hu.ep2
          refine Classical.byContradiction fun hne => ?_
          have hsw := hu.epS (by omega)
          unfold FCond.Sated at hsw; unfold FCond.SStep at hst; omega
        · unfold FCond.Sated; rw [FCond.lastS_push e]; unfold FCond.SStep at hst; omega
      · -- `inc → inc`
        have hinc1 := hu.incE q' n h' hc
        have hE : Lo.WE.hist m' = Lo.WE.hist m := by
          rcases hEp' with e' | ⟨_, _, _, -, e'⟩
          · exact e'
          · cases e'
        rw [hE]
        exact ⟨hinc1.1, hSW (by rw [(hu.sig1 (u := 1) (by rw [hc]; rfl)).2]; nofun) hinc1.2⟩
    · rw [hG 1 (Ne.symm et)] at hq'
      have hinc1 := hu.incE q' n h' hq'
      have hsg : (G 1).2.ph = .sg := (hu.sig1 (u := 1) (by rw [hq']; rfl)).2
      have hE : Lo.WE.hist m' = Lo.WE.hist m := by
        rcases hEp' with e' | ⟨_, _, _, e', -⟩
        · exact e'
        · exact absurd (hu.sig1 (u := t) (by rw [e']; rfl)).1 et
      rw [hE]
      exact ⟨hinc1.1, hSW (by rw [hsg]; nofun) hinc1.2⟩
  · -- ent
    rw [(hph 1).1]; exact hu.ent (hcc 0 h0)
  · -- hold
    rw [(hph 1).1] at h1
    have hh := hu.hold h1
    by_cases e : t = 1
    · subst e
      by_cases hl : (L Lo).ph (G 1) = (G' 1).1.ph
      · rw [← hl]; exact hh
      · obtain ⟨h2, -⟩ := hlq hl
        rcases h2 with h2 | h2 <;> rw [show (L Lo).ph (G 1) = (G 1).1.ph from rfl, hh] at h2 <;>
          cases h2
    · rw [hG 1 (Ne.symm e)]; exact hh
  · -- reg
    -- `main`'s lock place after the step, when it held the mutex
    have hold0 : (G 0).1.ph = .holds → (G' 0).1.ph = .holds := fun h0 => by
      by_cases e : t = 0
      · subst e
        by_cases hl : (L Lo).ph (G 0) = (G' 0).1.ph
        · rw [← hl]; exact h0
        · obtain ⟨h2, -⟩ := hlq hl
          rcases h2 with h2 | h2 <;> rw [show (L Lo).ph (G 0) = (G 0).1.ph from rfl, h0] at h2 <;>
            cases h2
      · rw [hG 0 (Ne.symm e)]; exact h0
    -- a registration before the step, or `main`'s in this step (the new write)
    have hcase : ((C Lo).RegW m j ∧ ((C Lo).S.hist m')[j]! = ((C Lo).S.hist m)[j]!) ∨
        ∃ x : Word.Entry, x.clock = m'.clocks[t]! ∧ ((C Lo).S.hist m')[j]! = x ∧ t = 0 ∧
          ((G 0).2.c).crit = true := by
      rcases hSh with e | ⟨x, hx, e⟩
      · exact .inl ⟨(FCond.RegW.congr e).mp hj, by rw [e]⟩
      · rcases FCond.RegW.push e hj with hj' | ⟨rfl, hw0, hw1⟩
        · exact .inl ⟨hj', by rw [e, FEvent.get_push_lt hj'.2.1]⟩
        · have hr1 : ((G' 0).2.c).isReg = true := by
            rw [hwx x e] at hw1; revert hw1; cases ((G' 0).2.c).isReg <;> simp
          have hr0 : ((G 0).2.c).isReg = false := by
            rw [hwl] at hw0; revert hw0; cases ((G 0).2.c).isReg <;> simp
          exact .inr ⟨x, hx, by rw [e, FEvent.get_push_eq], henter hr1 hr0⟩
    rcases hcase with ⟨hj', e⟩ | ⟨x, hx, e, rfl, hcr⟩
    · rw [e, (hph 1).1]
      rcases hu.reg j hj' with h' | ⟨hlk, h' | h'⟩
      · exact .inl (VClock.le_trans h' (hclk 1))
      · exact .inr ⟨hlk, .inl ⟨hold0 h'.1, VClock.le_trans h'.2 (hclk 0)⟩⟩
      · exact .inr ⟨hlk, .inr (hbef _ h')⟩
    · -- `main` registered in this step: it holds the mutex, the producer is before its lock
      rw [e, hx]
      exact .inr ⟨by rw [(hph 1).1]; exact hu.ent hcr,
        .inl ⟨hold0 (hu.cinv.crit 0 hcr), VClock.le_refl _⟩⟩
  · -- w1
    cases hr : ((G 0).2.c).isReg
    · -- `main` registers in this step: the new state write is its registration
      rcases hSh with e | ⟨x, -, e⟩
      · have h1 := hwl'; rw [FCond.lastS_congr e, hwl, hr, h0] at h1; simp at h1
      · refine ⟨((C Lo).S.hist m).size,
          ⟨by omega, by rw [e, Array.size_push]; omega, ?_, ?_⟩, fun p hp1 hp2 => ?_⟩
        · rw [e, FEvent.get_push_lt (by omega), hwl, hr]; rfl
        · rw [e, FEvent.get_push_eq, hwx x e, h0]; rfl
        · rw [e, Array.size_push] at hp2
          obtain rfl : p = ((C Lo).S.hist m).size := by omega
          rw [e, FEvent.get_push_eq, hwx x e, h0]; rfl
    · obtain ⟨j, hj, hp⟩ := hu.w1 hr
      have hjs : j < ((C Lo).S.hist m).size := hj.2.1
      rcases hSh with e | ⟨x, -, e⟩
      · exact ⟨j, (FCond.RegW.congr e).mpr hj, by rw [e]; exact hp⟩
      · refine ⟨j, ⟨hj.1, by rw [e, Array.size_push]; omega, ?_, ?_⟩, fun p hp1 hp2 => ?_⟩
        · rw [e, FEvent.get_push_lt (by omega)]; exact hj.2.2.1
        · rw [e, FEvent.get_push_lt hj.2.1]; exact hj.2.2.2
        · rw [e, Array.size_push] at hp2
          by_cases hp3 : p < ((C Lo).S.hist m).size
          · rw [e, FEvent.get_push_lt hp3]; exact hp p hp1 hp3
          · obtain rfl : p = ((C Lo).S.hist m).size := by omega
            rw [e, FEvent.get_push_eq, hwx x e, h0]; rfl
  · -- snap: no registration while the producer is past its lock
    rw [(hph 1).2.2] at hn
    obtain ⟨hsg, hlt⟩ := hu.snap n hn
    refine ⟨by rw [(hph 1).1]; exact hsg, fun j hj => ?_⟩
    rcases hSh with e | ⟨x, -, e⟩
    · exact hlt j ((FCond.RegW.congr e).mp hj)
    · rcases FCond.RegW.push e hj with hj' | ⟨rfl, hw0, hw1⟩
      · exact hlt j hj'
      · have hr1 : ((G' 0).2.c).isReg = true := by
          rw [hwx x e] at hw1; revert hw1; cases ((G' 0).2.c).isReg <;> simp
        have hr0 : ((G 0).2.c).isReg = false := by
          rw [hwl] at hw0; revert hw0; cases ((G 0).2.c).isReg <;> simp
        have := hu.ent (henter hr1 hr0).2
        rw [hsg] at this; cases this
  · -- lvc: a registered `main` stays signalled (`signals = waiters` stays)
    rw [(hph 1).1] at h1
    have hw0 := hcw 0 h0
    have hsig := hu.lvc hw0 h1
    have hl : (G 1).2.ph ≠ .lk := fun hl => by rw [hl] at h1; rcases h1 with h1 | h1 <;> cases h1
    have hnc : ((G' 0).2.c).crit = false := by
      cases hc : ((G' 0).2.c).crit
      · rfl
      · exact absurd (hu.ent (hcc 0 hc)) hl
    have hsw := hSW hl hsig.sated
    have hw1 : FCond.wOf ((C Lo).lastS m') = 1 := by rw [hwl', CPh.isReg_of_waits h0 hnc]; rfl
    unfold FCond.Sated at hsw
    exact hI.signalled_iff.mpr ⟨hw1, by omega⟩
  · -- fin
    rw [(hph 1).1] at h1
    show ((Lo.WV.hist m')[(Lo.WV.hist m').size - 1]!).Val _; rw [hV]; exact hu.fin h1
  · -- q
    rcases hwt w hw with h' | rfl
    · exact hu.q w h'
    · exact .inr (.inl rfl)
  · -- xc
    by_cases e : u = t
    · subst e
      have hp' : p ≠ .out := by rw [hXt] at hu'; exact hu'
      rw [(hph u).1]
      by_cases hc : (G u).2.c = .out
      · rcases CPh.Next.of_out (hc ▸ hn') with h' | h'
        · exact absurd h' hp'
        · exact .inr (hinc h')
      · exact hu.xc u hc
    · rw [hG u e] at hu' ⊢; exact hu.xc u hu'

/-- **A step of the event's code keeps `U`** (`FLock.Fits.kstep` of `FEvent.prim`). -/
theorem estep (G : ThreadId → Gh) (rY : Res) (m m' : Mem) (t : ThreadId) (p : EPh) (q : LPh)
    (hlq : (((L Lo).ph (G t) = .out ∨ ((L Lo).ph (G t) = .away ∧ (E Lo).ph (G t) = .w1)) ∧
      (q = .out ∨ (q = .away ∧ p = .w1))) ∨ ((L Lo).ph (G t) = .gone ∧ q = .gone))
    (hu : U Lo G (rsum ((E Lo).W.cellsR m) rY) m) (hY : ∀ l, (E Lo).W.In l → rY.heap l = none)
    (hs : (E Lo).MStep t m m')
    (hI : (E Lo).Inv (L Lo) (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil)) m') :
    U Lo (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil)) (rsum ((E Lo).W.cellsR m') rY) m' := by
  -- what the step does to the memory (`FEvent.MStep.*`)
  have hth := hs.threads
  have hclk := hs.clocks
  have hcells : ∀ l, ¬ Lo.WV.In l → m'.heap l = m.heap l := fun _ h => hs.cells h
  have hblk : BlkOk Lo m → BlkOk Lo m' := fun h => h.of_block fun _ _ hb => hs.block hb
  have hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ (e.block = 0 ∧ Lo.so ≤ e.off) := fun _ he =>
    (hs.fp he).imp_right (three_fp (.inr (.inr rfl)))
  have hbef : ∀ c, (L Lo).Before m c → (L Lo).Before m' c := fun _ ⟨i, l, hl, hc⟩ =>
    ⟨i, l, hs.lockLoc apV hl, hc⟩
  have hwt : ∀ w ∈ m'.waiters, w ∈ m.waiters ∨ w = (t, Lo.WV.ptr) := fun _ hw => hs.waiters hw
  have hwd := fun W' (hW' : Three Lo W') (h : W'.Ok m) =>
    hs.word h (three_word (W := Lo.WV) (.inr (.inr rfl)) hW')
  have hok3 := fun W' (hW' : Three Lo W') (h : W'.Ok m) => (hwd W' hW' h).1
  have hhist := fun W' (hW' : Three Lo W') (h : W'.Ok m) => (hwd W' hW' h).2
  have hG : ∀ u, u ≠ t → upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) u = G u :=
    fun u hu => upd_ne _ _ hu
  have hXt : (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) t).2 = { (G t).2 with e := p } := by
    rw [upd_self]; rfl
  have hph : ∀ u, (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) u).2.ph = (G u).2.ph ∧
      (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) u).2.c = (G u).2.c := fun u => by
    by_cases e : u = t
    · subst e; rw [hXt]; exact ⟨rfl, rfl⟩
    · rw [hG u e]; exact ⟨rfl, rfl⟩
  have hsz : ∀ u, (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) u).2.sz = (G u).2.sz :=
    fun u => by
      by_cases e : u = t
      · subst e; rw [hXt]
      · rw [hG u e]
  -- `t` is not `holds`
  have hnh : (G t).1.ph ≠ .holds := fun h => by
    rcases hlq with ⟨h' | ⟨h', -⟩, -⟩ | ⟨h', -⟩ <;>
      rw [show (L Lo).ph (G t) = (G t).1.ph from rfl, h] at h' <;> cases h'
  -- `t` in the condition's code is out of the event's, so not in its futex wait
  have hnaw : (G t).2.c ≠ .out → (L Lo).ph (G t) ≠ .away := fun hc ha => by
    rcases hlq with ⟨h' | ⟨-, hw⟩, -⟩ | ⟨h', -⟩
    · rw [ha] at h'; cases h'
    · have he : (G t).2.e = .out := hu.e_out hc
      rw [show (E Lo).ph (G t) = (G t).2.e from rfl, he] at hw; cases hw
    · rw [ha] at h'; cases h'
  -- a waiter of the event is `main` from its event wait on
  have hEt : (E Lo).ph (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) t) = p := by
    rw [upd_self]; rfl
  have hwx : (p = .w0 ∨ p = .w1) → (G t).2.ph = .ev ∨ (G t).2.ph = .joins := fun hp => by
    have := hI.wx t (by rw [hEt]; exact hp)
    have h2 : (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) t).2.ph = .ev ∨
      (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) t).2.ph = .joins := this
    rwa [(hph t).1] at h2
  have hsw : p = .sw → (G t).2.ph = .st ∨ (G t).2.ph = .fin := fun hp => by
    have := hI.sx t (by rw [hEt]; exact hp)
    have h2 : (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) t).2.ph = .st ∨
      (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) t).2.ph = .fin := this
    rwa [(hph t).1] at h2
  have hsd : p = .sd → (G t).2.ph = .st ∨ (G t).2.ph = .fin := fun hp => by
    have := hI.sdx t (by rw [hEt]; exact hp)
    have h2 : (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) t).2.ph = .st ∨
      (upd G t ((L Lo).set ((E Lo).set (G t) p) q rnil) t).2.ph = .fin := this
    rwa [(hph t).1] at h2
  -- a thread at the event's waiter places is out of the condition's code
  have hco : (p = .w0 ∨ p = .w1) → (G t).2.c = .out := fun hp => by
    by_cases hc : (G t).2.c = .out
    · exact hc
    · rcases hu.xc t hc with h' | h' <;> rcases hwx hp with h'' | h'' <;> rw [h'] at h'' <;>
        cases h''
  have hS : Lo.WS.hist m' = Lo.WS.hist m := by
    rcases hhist _ (.inl rfl) hu.ws with e | ⟨e, -⟩
    · exact e
    · exact absurd e.symm ne_VS
  have hE : Lo.WE.hist m' = Lo.WE.hist m := by
    rcases hhist _ (.inr (.inl rfl)) hu.we with e | ⟨e, -⟩
    · exact e
    · exact absurd e.symm ne_VE
  -- a new waiter in the futex queue is `t` at the event, a waiter there
  have hnw : ∀ w ∈ m'.waiters, w ∈ m.waiters ∨ (w = (t, Lo.WV.ptr) ∧ p = .w1) := fun w hw => by
    rcases hwt w hw with h' | rfl
    · exact .inl h'
    · have h1 := (hI.q _ hw rfl).1
      rw [hEt] at h1; exact .inr ⟨rfl, h1⟩
  refine hu.congrHist (fun u => ⟨(hph u).1, (hph u).2, hsz u⟩) hS hE ?_ (fun e he hr => ?_)
    (Rest.step (fun _ => Lo.wv_box) hu.rest rfl hY fun l _ hw => hcells l hw)
    (hblk hu.blk) (hok3 _ (.inl rfl) hu.ws) (hok3 _ (.inr (.inl rfl)) hu.we)
    (hok3 _ (.inr (.inr rfl)) hu.wv) ?_ hI (fun h1 => ?_) (fun j hj => ?_) (fun h1 => ?_)
    (fun w hw => ?_)
  · -- shape
    refine Shape.congr hu.shape hth (fun u => (hph u).1) fun u hfr => ?_
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
        | sw => rcases hsw rfl with h' | h' <;> rcases hfr' with h'' | h'' <;> rw [h''] at h' <;>
            cases h'
        | sd => rcases hsd rfl with h' | h' <;> rcases hfr' with h'' | h'' <;> rw [h''] at h' <;>
            cases h'
      show (upd G u _ u).2 = (G u).2
      rw [hXt, hp, ← he]
    · rw [hG u e]
  · -- io
    rcases hfp e he with h' | ⟨hb, ho⟩
    · rcases hu.io e h' hr with ⟨hk, h''⟩ | h''
      · exact .inl ⟨hk, LockWord.someLe_mono hth (fun u _ => hclk u) h''⟩
      · exact .inr (LockWord.allLe_mono hth (fun u _ => hclk u) h'')
    · have := Lo.ok; have := hr.2.2; omega
  · -- the condition's invariant
    refine hu.cinv.other (t := t) rfl (fun hb => ?_)
      (fun hr ha => absurd ha (hnaw fun hc => by
        rw [show (C Lo).ph (G t) = (G t).2.c from rfl, hc] at hr; cases hr))
      (fun h' => h') hS hE (hs.waiters_at ptr_EV fun w hw hw2 w' hw' he hw'2 => by
        -- queued at the epoch: `main`, registered; at the event's word: at `w1`
        obtain ⟨_, _, _, hr, -⟩ := hu.cinv.q w hw hw2
        have h1 := (hu.einv.q w' hw' hw'2).1
        rw [he] at h1
        have hc : (G w.1).2.c ≠ .out := fun hc => by
          rw [show (C Lo).ph (G w.1) = (G w.1).2.c from rfl, hc] at hr; cases hr
        rw [show (E Lo).ph (G w.1) = (G w.1).2.e from rfl, hu.e_out hc] at h1; cases h1)
      (fun w hw _ => ?_)
      (fun u hr ha hw => by
        by_cases hut : u = t
        · rw [hut] at hr
          exact absurd (ha hut) (hnaw fun hc => by
            rw [show (C Lo).ph (G t) = (G t).2.c from rfl, hc] at hr; cases hr)
        · exact hs.woken_ne hut hw)
      (Nat.le_of_eq (by rw [hth])) hclk
    · -- `t` in the condition's busy code is a signaller out of the lock, not a waiter
      have hsig : ((G t).2.c).sig = true := by
        unfold CPh.busy at hb
        cases hc : ((G t).2.c).crit
        · rw [show (C Lo).ph (G t) = (G t).2.c from rfl, hc, Bool.false_or] at hb; exact hb
        · have := hu.cinv.crit t hc; exact absurd this hnh
      have hlp : (G t).1.ph = .out := (hu.cinv.lp t hsig).resolve_right hnh
      have hsg : (G t).2.ph = .sg := hu.cinv.sx t hsig
      rcases hlq with ⟨-, rfl | ⟨rfl, rfl⟩⟩ | ⟨hg', -⟩
      · show LPh.out = (G t).1.ph; rw [hlp]
      · rcases hwx (.inr rfl) with h' | h' <;> rw [hsg] at h' <;> cases h'
      · exact absurd (hlp.symm.trans hg') (by decide)
    · rcases hnw w hw with h' | ⟨rfl, hp⟩
      · exact .inl h'
      · refine .inr ⟨rfl, ?_⟩
        show ((G t).2.c).waits = false
        rw [hco (.inr hp)]; rfl
  · -- hold
    have hh := hu.hold h1
    by_cases e : t = 1
    · subst e; exact absurd hh hnh
    · rw [hG 1 (Ne.symm e)]; exact hh
  · -- reg
    rcases hu.reg j hj with h' | ⟨hlk, h' | h'⟩
    · exact .inl (VClock.le_trans h' (hclk 1))
    · refine .inr ⟨hlk, .inl ⟨?_, VClock.le_trans h'.2 (hclk 0)⟩⟩
      by_cases et : t = 0
      · subst et; exact absurd h'.1 hnh
      · rw [hG 0 (Ne.symm et)]; exact h'.1
    · exact .inr ⟨hlk, .inr (hbef _ h')⟩
  · -- fin: the event stays set
    have hset := hu.fin h1
    have hpos := FEvent.hist_pos hu.wv
    rcases hhist _ (.inr (.inr rfl)) hu.wv with e | ⟨-, x, e⟩
    · show ((Lo.WV.hist m')[(Lo.WV.hist m').size - 1]!).Val _; rw [e]; exact hset
    · refine hI.isSet_of (j := (Lo.WV.hist m).size - 1) ?_ ?_
      · show _ < (Lo.WV.hist m').size; rw [e, Array.size_push]; omega
      · show ((Lo.WV.hist m')[(Lo.WV.hist m).size - 1]!).Val _
        rw [e, FEvent.get_push_lt (by omega)]; exact hset
  · -- q
    rcases hwt w hw with h' | rfl
    · exact hu.q w h'
    · exact .inr (.inr rfl)

/-- `R` reads the producer's program place only. -/
theorem R_congr {Y Y' : ThreadId → X} (h : (Y' 1).ph = (Y 1).ph) : R Lo Y' = R Lo Y := by
  unfold R vOf; rw [h]

variable {prodOf : Tgt → Option Ptr}

/-- A same-memory change of the caller's part leaves this protocol's observations unchanged.
Its physical invariant does not constrain caller ghost fragments. -/
theorem U_part {G : ThreadId → Gh} {rX : Res} {m : Mem} {t : ThreadId} {r : Res}
    (hu : U Lo G rX m) (hi : (L Lo).Inv G rX m)
    (hi' : (L Lo).Inv (upd G t ((L Lo).setPart (G t) r)) rX m) :
    U Lo (upd G t ((L Lo).setPart (G t) r)) rX m := by
  obtain ⟨rY, hrX, hY⟩ := Rest.split (fun _ => Lo.ws_box) hu.rest
  subst rX
  exact U_own_native (.inl rfl) hu hi hY (FStepIn.refl _ _) hu.ws rfl hi' rfl rfl

/-- The composite tick obligation reuses native framed invariant transport. Ticks stay visible
in the exact memory; this proof preserves the observation because its actual fields ignore
only that counter and caller ghost fragments. -/
theorem tickStable (t : ThreadId) (G : ThreadId → Gh) (rX : Res) (m : Mem)
    (G' : ThreadId → Gh) (rX' : Res) (m' : Mem)
    (hs : (L Lo).PartTick t G rX m G' rX' m') (hu : U Lo G rX m) : U Lo G' rX' m' := by
  obtain ⟨_, _, hi, r, _, rfl, rfl, rfl, hi'⟩ := hs
  obtain ⟨rY, hrX, hY⟩ := Rest.split (fun _ => Lo.ws_box) hu.rest
  subst hrX
  exact U_own_native (.inl rfl) hu hi hY (FStepIn.ticked _ _) hu.ws.ticked rfl hi' rfl rfl

/-- **The protocol has the lock**, for the threads that run its code (`ok`). -/
theorem fitsL : (L Lo).Fits (FPrim.empty Gh) (proto Lo prodOf) (U Lo) ok :=
  .ofLock (fun _ _ => Iff.rfl) (fun _ h => h.1) (fun _ h => h.1) (fun _ _ _ => Iff.rfl)
    (fun _ _ => Iff.rfl) stable (fun _ _ _ t _ hu => atStop t hu) tickStable

/-- **The protocol has the condition** (the lock's laws as for `fitsL`); the window: the epoch
has at most two writes (`ep2`). -/
theorem fitsC : (C Lo).Fits (L Lo) (proto Lo prodOf) (U Lo) ok where
  win _ _ m hu _ _ _ _ _ _ := by
    have : ((C Lo).Ep.hist m).size ≤ 2 := hu.ep2
    omega
  toFits := { fitsL with
  kfin g h := by show g.2.c = _; rw [h.2]
  kjoins g h := by show g.2.c = _; rw [h.2]
  sub _ _ _ hu := ⟨hu.cinv, fun W hW => by
    rcases hW with rfl | rfl
    · exact ⟨hu.ws, Rest.split (fun _ => Lo.ws_box) hu.rest⟩
    · exact ⟨hu.we, Rest.split (fun _ => Lo.we_box) hu.rest⟩⟩
  apart W hW := by rcases hW with rfl | rfl <;> first | exact apS | exact apE
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
  role_l _ _ _ _ := Iff.rfl
  role_part _ _ _ := Iff.rfl
  ok_calm _ _ _ hp hq := ⟨fun h => ⟨hq, h.2⟩, fun h => ⟨hp, h.2⟩⟩
  kstep := by
    intro t G rX m G' rX' m' hs hu
    rcases hs with hs | hs
    · rcases hs with ⟨W, rY, hW, rfl, rfl, hY, hI,
      ⟨p, q, h, ⟨hn, hq, hs, hEp, hsg⟩, rfl⟩ | ⟨r, -, hi, -, hs, hcW, hw', hh, hL, rfl⟩⟩
      · refine cstep G rY m m' t p q h W hW hn hq hu hY hs hEp (fun sh c q n h' e1 e2 => ?_) hI
        rw [e1, e2] at hsg
        obtain ⟨-, x, e⟩ := hsg
        rw [e, Array.size_push]
      · exact U_own_native (hW.imp id .inl) hu hi hY hs hw' hh hL rfl rfl
    · exact tickStable t G rX m G' rX' m' hs hu }

/-- **The protocol has the event** (the lock's laws as for `fitsL`). -/
theorem fitsE : (L Lo).Fits ((E Lo).prim (L Lo)) (proto Lo prodOf) (U Lo) ok := { fitsL with
  kfin g h := by show g.2.e = _; rw [h.2]
  kjoins g h := by show g.2.e = _; rw [h.2]
  sub _ _ _ hu := ⟨hu.einv, fun _ hW => hW ▸ ⟨hu.wv, Rest.split (fun _ => Lo.wv_box) hu.rest⟩⟩
  apart _ hW := hW ▸ apV
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
  role_l _ _ _ _ := Iff.rfl
  role_part _ _ _ := Iff.rfl
  ok_calm _ _ _ h := h.elim
  kstep := by
    intro t G rX m G' rX' m' hs hu
    rcases hs with hs | hs
    · rcases hs with ⟨W, rY, rfl, rfl, rfl, hY, hI,
      ⟨p, q, h, ⟨hlq, rfl, hs, -⟩, rfl⟩ | ⟨r, -, hi, -, hs, hcW, hw', hh, hL, rfl⟩⟩
      · exact estep G rY m m' t p q hlq hu hY hs hI
      · exact U_own_native (.inr (.inr rfl)) hu hi hY hs hw' hh hL rfl rfl
    · exact tickStable t G rX m G' rX' m' hs hu }

end Handoff
end Zig
