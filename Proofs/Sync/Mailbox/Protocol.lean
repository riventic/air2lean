import Proofs.Sync.Mailbox.Code
import ZigLean.Sep.Full.LockSteps
import ZigLean.Sep.Full.ThreadFacts

/-!
# The mailbox's protocol

The protocol of the mailbox (`Proofs/Sync/Mailbox/Code.lean`) for every mutex value of its
semaphore (`Cfg`): `main` (thread 0) spawns the producer (thread 1), waits for the permit, reads the
message and joins; the producer writes the message and posts. The semaphore is used through its
contract only (`SemImpl`), so the protocol keeps the semaphore (`fitsS : (S K).Fits ...`).

- **The rest `rX`** (`Rest`): the cells of the condition's two words (bytes `12 .. 20`, `BoxW`)
  and `rP` (`PadRest`): the semaphore's padding (bytes `20 .. 24`, any contents) and the block's
  full extent, which pins the block, so the words' cells in the rest are the memory's at every stop.
- **The rest of the invariant** (`U`): the threads (`Shape`: after the spawn, `main` and the
  producer, and `main` took the permit only after the producer posted), the block, the words, the
  condition's and the semaphore's invariants, and the condition's window: a thread at the
  semaphore's wait is `main` before its take (`swt`, the waiting role `FSem.wx`), so only `main`
  registers; every epoch write happened before the mutex's holder (`hbE`), so `main` saves the
  newest epoch write at its load (`ldE`); while it is registered at most one post, and so at most
  one epoch write, follows (`regE`, `incS`): `Fits.win`. `U` reads the threads' places, the words'
  histories and the memory's cells of the words; it reads no thread's part.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

namespace Sync.Mailbox

/-! ## The program's places -/

namespace Ph

/-- `main`'s places. -/
def isMain : Ph → Bool
  | .pre | .wt | .got | .joins => true
  | _ => false

/-- The producer's places. -/
def isProd : Ph → Bool
  | .pr _ | .pd | .fin => true
  | _ => false

/-- No place is both `main`'s and the producer's. -/
theorem isMain_of_isProd {p : Ph} (h : p.isProd = true) : p.isMain = false := by
  cases p <;> simp_all [isProd, isMain]

end Ph

/-- Two updates of the same thread agree at every other thread (the ghost value's second part). -/
theorem upd_ne₂ {G : ThreadId → Gh} {t u : ThreadId} {g g' : Gh} (e : u ≠ t) :
    (upd G t g u).2 = (upd G t g' u).2 := by
  rw [upd_ne _ _ e, upd_ne _ _ e]

theorem X.eq_empty {x : X} (hp : x.ph = .none) (hc : x.c = .out) (hs : x.s = .out) : x = {} := by
  cases x; simp only at hp hc hs; subst hp hc hs; rfl

/-! ## The rest and the invariant -/

/-- The semaphore's padding (bytes `20 .. 24`, any contents) and the block's full extent. -/
def PadRest (r : Res) : Prop :=
  ∃ A bs, A % 8 = 0 ∧ bs.size = 4 ∧
    (up (bytesAt (cPtr.add 20) A 32 .stack bs) ⋆ bext 0 32 .stack) r

/-- The protocol's rest: the cells of the condition's words, and the padding with the extent. -/
def Rest (rX : Res) (m : Mem) : Prop :=
  ∃ rP, PadRest rP ∧ (∀ l, BoxW l → rP.heap l = none) ∧ rX = rsum (cellsAt BoxW m) rP

/-- Block 0 is the live mailbox, 32 bytes on the stack. -/
def BlkOk (m : Mem) : Prop :=
  ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 32 ∧ blk.kind = .stack

/-- The threads: `main` alone before its spawn; then `main` and the producer, which `main`
spawned and did not join yet; `main` took the permit only after the producer posted. -/
def Shape (Y : ThreadId → X) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧
  ((m.threads.size = 1 ∧ (Y 0).ph = .pre ∧ ∀ u, 1 ≤ u → Y u = {}) ∨
   (m.threads.size = 2 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
    (Y 0).ph.isMain ∧ (Y 0).ph ≠ .pre ∧ (Y 1).ph.isProd ∧
    ((Y 0).ph.took = true → (Y 1).ph.posted = true) ∧ ∀ u, 2 ≤ u → Y u = {}))

variable (K : Cfg)

/-- The rest of the invariant (module doc). -/
structure U (G : ThreadId → Gh) (rX : Res) (m : Mem) : Prop where
  shape : Shape (fun u => (G u).2) m
  rest : Rest rX m
  blk : BlkOk m
  ws : WS.Ok m
  we : WE.Ok m
  cinv : C.Inv (L K) G m
  sinv : (S K).Inv G m
  /-- A thread at the semaphore's wait is `main` before its take (the waiting role). -/
  swt : ∀ u, (G u).2.s = .wt → (G u).2.ph = .wt
  /-- Every epoch write happened before the mutex's holder (`FCond.ld_newest`). -/
  hbE : (L K).WordHB WE G m
  /-- A waiter at its load saved the newest epoch write. -/
  ldE : ∀ u i e, (G u).2.c = .ld i e → (WE.hist m).size = i + 1
  /-- A registered waiter: at most one epoch write after its saved one; after it the state is
  sated (no further post); while a signaller is at `inc` (its post made, its `epoch += 1` not
  yet), none. -/
  regE : ∀ u i jr sn e, (G u).2.c = .reg i jr sn e → (WE.hist m).size ≤ i + 2 ∧
    ((WE.hist m).size = i + 2 → C.Sated m) ∧
    ∀ v q n h, (G v).2.c = .inc q n h → (WE.hist m).size = i + 1
  /-- A signaller at `inc` made the only post the state has room for. -/
  incS : ∀ v q n h, (G v).2.c = .inc q n h → C.Sated m
  /-- A thread sleeps only at the mutex or at the epoch. -/
  q : ∀ w ∈ m.waiters, w.2 = (L K).ptr ∨ w.2 = WE.ptr

/-- The protocol, in strict mode: the producer starts with a plain part and the message. -/
def proto : Proto Tgt Gh where
  inv G m := ∃ rX, (L K).Inv G rX m ∧ U K G rX m
  init tgt g := match tgt with
    | .semWork p => p = cPtr ∧ ∃ rp rc, plain rp ∧ Msg 0 rc ∧ FHeap.Disjoint rp.heap rc.heap ∧
        g = (⟨.out, rsum rp rc, rnil⟩, { ph := .pr 0 })
    | _ => False
  fin g := g.1.ph = .gone ∧ g.2 = { ph := .fin }
  strict := true
  joins g := g.1.ph = .out ∧ g.2 = { ph := .joins }

variable {K}

/-! ## The layout -/

theorem res_eq {a b : Res} (hh : a.heap = b.heap) (hk : a.know = b.know) (hg : a.gh = b.gh) :
    a = b := by
  cases a; cases b; simp only at hh hk hg; subst hh hk hg; rfl

theorem apS : WS.ApartL (L K).toLockWord := .inr (.inl (by simp [WS, L, FLock.prod] <;> omega))
theorem apE : WE.ApartL (L K).toLockWord := .inr (.inl (by simp [WE, L, FLock.prod] <;> omega))

/-- A byte of the condition's words is not the mutex's. -/
theorem box_notL {l : Zig.Loc} (h : BoxW l) : ¬ (L K).In l := fun ⟨_, h2, h3⟩ => by
  obtain ⟨-, h5, -⟩ := h; simp [L, FLock.prod] at h2 h3; omega

theorem box_cases {l : Zig.Loc} (h : BoxW l) : WS.In l ∨ WE.In l := by
  obtain ⟨h1, h2, h3⟩ := h
  by_cases hx : l.2 < 16
  · exact .inl ⟨by simp [WS]; exact h1, by simp [WS]; omega, by simp [WS]; omega⟩
  · exact .inr ⟨by simp [WE]; exact h1, by simp [WE]; omega, by simp [WE]; omega⟩

theorem two_box {W : Word 32 4} (h : W = WS ∨ W = WE) : ∀ l, W.In l → BoxW l := by
  rcases h with rfl | rfl
  · exact fun _ => ws_box
  · exact fun _ => we_box

theorem two_apart {W W' : Word 32 4} (h : W = WS ∨ W = WE) (h' : W' = WS ∨ W' = WE) :
    W' = W ∨ ∀ l, W'.In l → ¬ W.In l := by
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl <;>
    first
      | exact .inl rfl
      | exact .inr fun l ⟨_, a, b⟩ ⟨_, c, d⟩ => by simp only [WS, WE] at a b c d; omega

theorem two_word {W W' : Word 32 4} (h : W = WS ∨ W = WE) (h' : W' = WS ∨ W' = WE) :
    W' = W ∨ W.b ≠ W'.b ∨ W.o + 4 ≤ W'.o ∨ W'.o + 4 ≤ W.o := by
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl <;>
    first
      | exact .inl rfl
      | exact .inr (by simp [WS, WE])

theorem two_ap {W : Word 32 4} (h : W = WS ∨ W = WE) : W.ApartL (L K).toLockWord := by
  rcases h with rfl | rfl
  · exact apS
  · exact apE

/-! ## The rest: the words' cells -/

/-- A word of the two in the rest: its cells and the others. -/
theorem Rest.split {rX : Res} {m : Mem} {W : Word 32 4} (hW : ∀ l, W.In l → BoxW l)
    (h : Rest rX m) : ∃ rY, rX = rsum (W.cellsR m) rY ∧ ∀ l, W.In l → rY.heap l = none := by
  obtain ⟨rP, -, hP, rfl⟩ := h
  refine ⟨rsum (cellsAt (fun l => BoxW l ∧ ¬ W.In l) m) rP, res_eq ?_ ?_ ?_, fun l hl => ?_⟩
  · funext l
    simp only [FHeap.union_apply, Word.cellsR]
    by_cases hw : W.In l
    · rw [cellsAt_of hw, cellsAt_of (hW l hw), cellsAt_none (fun h => h.2 hw), hP l (hW l hw)]
      simp
    · rw [cellsAt_none hw]
      by_cases hb : BoxW l
      · rw [cellsAt_of hb, cellsAt_of (W := fun l => BoxW l ∧ ¬ W.In l) ⟨hb, hw⟩]; simp
      · rw [cellsAt_none hb, cellsAt_none (W := fun l => BoxW l ∧ ¬ W.In l) (fun h => hb h.1)]
        simp
  · simp [cellsAt, Word.cellsR, Know.none_union]
  · simp [cellsAt, Word.cellsR]
  · simp only [FHeap.union_apply]
    rw [cellsAt_none (W := fun l => BoxW l ∧ ¬ W.In l) (fun h => h.2 hl), hP l (hW l hl)] <;> rfl

/-- After a step that changes only the bytes of the word `W` among the two (the other's cells
stay), the rest has `W`'s new cells. -/
theorem Rest.step {rX rY : Res} {m m' : Mem} {W : Word 32 4} (hW : ∀ l, W.In l → BoxW l)
    (h : Rest rX m) (hX : rX = rsum (W.cellsR m) rY) (hY : ∀ l, W.In l → rY.heap l = none)
    (hm : ∀ l, BoxW l → ¬ W.In l → m'.heap l = m.heap l) :
    Rest (rsum (W.cellsR m') rY) m' := by
  obtain ⟨rP, hR, hP, rfl⟩ := h
  have hk : rY.know = rP.know := by
    have := congrArg Res.know hX; simpa [cellsAt, Word.cellsR, Know.none_union] using this.symm
  have hg : rY.gh = rP.gh := by
    have := congrArg Res.gh hX; simpa [cellsAt, Word.cellsR] using this.symm
  refine ⟨rP, hR, hP, res_eq ?_ ?_ ?_⟩
  · funext l
    have hl := congrFun (congrArg Res.heap hX) l
    simp only [FHeap.union_apply, Word.cellsR] at hl ⊢
    by_cases hw : W.In l
    · rw [cellsAt_of hw, cellsAt_of (hW l hw), hY l hw, hP l (hW l hw)]
    · rw [cellsAt_none hw, Option.none_or] at hl ⊢
      rw [← hl]
      by_cases hb : BoxW l
      · rw [cellsAt_of hb, cellsAt_of hb, hm l hb hw]
      · rw [cellsAt_none hb, cellsAt_none hb]
  · simp [cellsAt, Word.cellsR, Know.none_union, hk]
  · simp [cellsAt, Word.cellsR, hg]

/-- A step that keeps the cells of the two words keeps the rest. -/
theorem Rest.congr {rX : Res} {m m' : Mem} (h : Rest rX m)
    (hm : ∀ l, BoxW l → m'.heap l = m.heap l) : Rest rX m' := by
  obtain ⟨rP, hR, hP, rfl⟩ := h
  refine ⟨rP, hR, hP, res_eq ?_ rfl rfl⟩
  funext l
  simp only [FHeap.union_apply]
  by_cases hb : BoxW l
  · rw [cellsAt_of hb, cellsAt_of hb, hm l hb]
  · rw [cellsAt_none hb, cellsAt_none hb]

/-- **The mailbox is block 0**: live, 32 bytes on the stack (the extent in the rest), whatever the
ghost values of the lock's invariant. -/
theorem blk_ofG {G : ThreadId → Gh} {rX rP : Res} {m : Mem} (hi : (L K).Inv G rX m)
    (hP : PadRest rP) (hg : rX.gh = rP.gh) : BlkOk m := by
  obtain ⟨rL, ho, -⟩ := hi.rest
  obtain ⟨rT, -, hh⟩ := ho.holds
  have he := hh.swap.extTrue
  obtain ⟨A, bs, -, -, r₁, r₂, -, rfl, -, h2⟩ := hP
  simp only at he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [hg, Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [bauth_eq h2] at he
  obtain ⟨blk, h1, h2, h3, h4, -⟩ := (he 0).1 32 .stack (by simp [Ghost.atExt, ECell.auth1])
  exact ⟨blk, h1, h2, h3, h4⟩

theorem blk_of {G : ThreadId → Gh} {rX : Res} {m m₀ : Mem} (hi : (L K).Inv G rX m)
    (hr : Rest rX m₀) : BlkOk m := by
  obtain ⟨rP, hP, -, rfl⟩ := hr
  exact blk_ofG hi hP (by simp [cellsAt])

theorem heap_blk {m : Mem} {blk : Block} (hb : m.blocks[0]? = some blk) (hl : blk.live = true)
    (hk : blk.kind = .stack) {x : Nat} (hx : x < blk.bytes.size) :
    m.heap (0, x) = some ⟨blk.bytes[x], blk.addr, blk.bytes.size, blk.kind⟩ := by
  simp [Mem.heap, hb, hl, hx, hk, BlockKind.mappedLo]

/-- A byte of the mailbox that the rest after a step holds with its cell before it: the same cell
(the block is pinned). -/
theorem cell_eq {G' : ThreadId → Gh} {rX' : Res} {m m' : Mem} (hbk : BlkOk m)
    (hbk' : BlkOk m') (hi' : (L K).Inv G' rX' m') {x : Nat} (hx : x < 32)
    (hr : rX'.heap (0, x) = (m.heap (0, x)).map fun c => ⟨c, none⟩) :
    m'.heap (0, x) = m.heap (0, x) := by
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

/-- **A step that keeps the rest keeps the words' cells**: the lock's invariant after it (at any
ghost values) has them up to `Cell.norm`, and the extent in the rest pins the block. -/
theorem cells_same {G' : ThreadId → Gh} {rX : Res} {m m' : Mem} (hbk : BlkOk m)
    (hi' : (L K).Inv G' rX m') (hr : Rest rX m) : ∀ l, BoxW l → m'.heap l = m.heap l := by
  rintro ⟨b, x⟩ hl
  obtain ⟨h0, h1, h2⟩ := hl
  simp only at h0 h1 h2; subst h0
  refine cell_eq hbk (blk_of hi' hr) hi' (by omega) ?_
  obtain ⟨rP, -, hP, rfl⟩ := hr
  have hB : BoxW (0, x) := ⟨rfl, h1, h2⟩
  simp only [FHeap.union_apply, cellsAt_of hB, hP (0, x) hB, Option.or_none]

/-- A step of the lock's code keeps the mailbox: it writes at most the mutex's bytes. -/
theorem BlkOk.lstep {t : ThreadId} {m m' : Mem} (hb : BlkOk m) (hs : (L K).Step t m m') :
    BlkOk m' := by
  obtain ⟨blk, hb, hl, hsz, hk⟩ := hb
  rcases hs.blocks with e | ⟨blk', bs, h1, -, h3, h4, h5⟩
  · exact ⟨blk, by rw [e]; exact hb, hl, hsz, hk⟩
  · have h1' : m.blocks[0]? = some blk' := h1
    rw [hb] at h1'; cases h1'
    refine ⟨{ blk with bytes := writeBytes blk.bytes 8 bs }, ?_, hl, ?_, hk⟩
    · rw [h5]; show (m.blocks.set! 0 _)[0]? = _
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
        (Array.getElem?_eq_some_iff.mp hb).1] <;> rfl
    · show (writeBytes blk.bytes 8 bs).size = 32
      rw [writeBytes_size _ _ _ (by rw [h3]; exact h4), hsz]

/-- The mailbox after a step that keeps each block as live, as large and of the same kind. -/
theorem BlkOk.of_block {m m' : Mem} (h : BlkOk m)
    (hb : ∀ (b : BlockId) (blk : Block), m.blocks[b]? = some blk → ∃ blk', m'.blocks[b]? = some blk' ∧
      blk'.live = blk.live ∧ blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind) :
    BlkOk m' := by
  obtain ⟨blk, h1, h2, h3, h4⟩ := h
  obtain ⟨blk', e1, e2, e3, e4⟩ := hb _ _ h1
  exact ⟨blk', e1, by rw [e2]; exact h2, by rw [e3]; exact h3, by rw [e4]; exact h4⟩

/-- The rest has the cells of the two words. -/
theorem rest_box {rX : Res} {m : Mem} (hr : Rest rX m) (hw : ∀ l, BoxW l → m.heap l ≠ none)
    {l : Zig.Loc} (hl : BoxW l) : rX.heap.erase l ≠ none := by
  obtain ⟨rP, -, -, rfl⟩ := hr
  have := cellsAt_some hl (hw l hl) (m := m)
  simp only [FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff, Option.or_eq_none_iff,
    not_and]
  intro h; exact absurd h this

/-- The frame of a step on a part with the mutex's word and the rest `rX`: it has the rest's
bytes, and the mutex's. -/
theorem frame_rest {rX : Res} {m : Mem} {l : Zig.Loc} (h : rX.heap.erase l ≠ none) :
    (rsum ((L K).wordR m) rX).heap.erase l ≠ none := by
  simp only [FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
    Option.or_eq_none_iff, not_and] at h ⊢
  intro _; exact h

theorem frame_word {G : ThreadId → Gh} {rX : Res} {m : Mem} (hi : (L K).Inv G rX m) {x : Nat}
    (h1 : (L K).o ≤ x) (h2 : x < (L K).o + 4) :
    (rsum ((L K).wordR m) rX).heap.erase ((L K).b, x) ≠ none := by
  have := LockWord.wordR_some hi.w.blk (l := ((L K).b, x)) ⟨rfl, h1, h2⟩
  simp only [FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
    Option.or_eq_none_iff, not_and]
  intro h; exact absurd h this

/-! ## The threads -/

/-- The threads' shape after a step that keeps the threads and every program place, with every
thread past the threads out of the condition's and the semaphore's code. -/
theorem Shape.congr {Y Y' : ThreadId → X} {m m' : Mem} (h : Shape Y m)
    (hth : m'.threads = m.threads) (hph : ∀ u, (Y' u).ph = (Y u).ph)
    (hout : ∀ u, m.threads.size ≤ u → (Y' u).c = .out ∧ (Y' u).s = .out) : Shape Y' m' := by
  have hfr : ∀ u, m.threads.size ≤ u → Y u = {} → Y' u = {} := fun u hu he => by
    obtain ⟨hc, hs⟩ := hout u hu
    exact X.eq_empty (by rw [hph, he] <;> rfl) hc hs
  obtain ⟨h0, ⟨hsz, hy0, hyu⟩ | ⟨hsz, h1, hm, hnp, hp, htk, hyu⟩⟩ := h
  · exact ⟨by rw [hth]; exact h0, .inl ⟨by rw [hth]; exact hsz, by rw [hph]; exact hy0,
      fun u hu => hfr u (by simp only [ThreadId] at *; omega) (hyu u hu)⟩⟩
  · exact ⟨by rw [hth]; exact h0, .inr ⟨by rw [hth]; exact hsz, by rw [hth]; exact h1,
      by rw [hph]; exact hm, by rw [hph]; exact hnp, by rw [hph]; exact hp,
      by rw [hph, hph]; exact htk, fun u hu => hfr u (by simp only [ThreadId] at *; omega) (hyu u hu)⟩⟩

/-- Only `main` (thread 0) is at a place of `main`. -/
theorem Shape.zero {Y : ThreadId → X} {m : Mem} (h : Shape Y m) {u : ThreadId}
    (hp : (Y u).ph.isMain = true) : u = 0 := by
  obtain ⟨-, ⟨-, -, hu⟩ | ⟨-, -, -, -, hpr, -, hu⟩⟩ := h
  · refine Classical.byContradiction fun hne => ?_
    rw [hu u (by simp only [ThreadId] at *; omega)] at hp; exact absurd hp (by decide)
  · by_cases h1 : u = 1
    · subst h1
      rw [Ph.isMain_of_isProd hpr] at hp; exact absurd hp (by decide)
    · refine Classical.byContradiction fun hne => ?_
      rw [hu u (by simp only [ThreadId] at *; omega)] at hp; exact absurd hp (by decide)

/-- A thread at the semaphore's wait is `main`. -/
theorem U.zero_of_wt {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U K G rX m) {u : ThreadId}
    (h : (G u).2.s = .wt) : u = 0 :=
  hu.shape.zero (u := u) (show (G u).2.ph.isMain = true by rw [hu.swt u h] <;> rfl)

/-- **Only `main` waits at the condition** (`FSem.Inv.wt`, `swt`). -/
theorem U.waits0 {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U K G rX m) {u : ThreadId}
    (h : ((G u).2.c).waits = true) : u = 0 :=
  hu.zero_of_wt (hu.sinv.wt u h)

/-- A signaller holds the mutex, at the semaphore's `pst`. -/
theorem U.sig_holds {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U K G rX m) {u : ThreadId}
    (h : ((G u).2.c).sig = true) : (G u).1.ph = .holds :=
  hu.sinv.pst u (hu.cinv.sx u h)

/-- No thread is in the condition's critical code while one signals (both hold the mutex). -/
theorem U.crit_sig {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U K G rX m) {u v : ThreadId}
    (hc : ((G u).2.c).crit = true) (hs : ((G v).2.c).sig = true) : False :=
  hu.sinv.cp u v hc (hu.cinv.sx v hs)

/-- The newest `waiters` when only `main` registers: 1 if it is registered, else 0. -/
theorem wlast {G : ThreadId → Gh} {m : Mem} (hI : C.Inv (L K) G m)
    (h0 : ∀ u, ((G u).2.c).isReg = true → u = 0) :
    FCond.wOf (C.lastS m) = if ((G 0).2.c).isReg then 1 else 0 := by
  obtain ⟨T, hT, hw, -⟩ := hI.cnt
  rw [hw]
  unfold FCond.nreg
  rw [tsum_congr (h := fun u => if u = 0 then (if ((G 0).2.c).isReg then 1 else 0) else 0)
    (fun u _ => ?_)]
  · rcases Nat.eq_zero_or_pos T with rfl | hT0
    · have : (G 0).2.c = .out := hT 0 (Nat.le_refl _)
      rw [this] <;> rfl
    · exact tsum_point hT0 _
  · by_cases e : u = 0
    · subst e; rfl
    · simp only [e, ↓reduceIte]
      cases hr : ((G u).2.c).isReg
      · show (if ((G u).2.c).isReg = true then 1 else 0) = 0; rw [hr] <;> rfl
      · exact absurd (h0 u hr) e

/-- **Only `main` registers**: at most one registered waiter (`SemImpl.wait_wp`'s `hroom`). -/
theorem U.nreg_le {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U K G rX m) (T : Nat) :
    C.nreg G T ≤ 1 := by
  unfold FCond.nreg
  rw [tsum_congr (h := fun u => if u = 0 then (if ((G 0).2.c).isReg then 1 else 0) else 0)
    (fun u _ => ?_)]
  · rcases Nat.eq_zero_or_pos T with rfl | hT0
    · exact Nat.zero_le _
    · rw [tsum_point hT0]; split <;> omega
  · by_cases e : u = 0
    · subst e; rfl
    · simp only [e, ↓reduceIte]
      cases hr : ((G u).2.c).isReg
      · show (if ((G u).2.c).isReg = true then 1 else 0) = 0; rw [hr] <;> rfl
      · exact absurd (hu.waits0 (CPh.isReg_waits hr)) e

/-! ## `U` over the steps -/

/-- **`U` after a step that keeps the waiters' and signallers' places and the words' writes**:
the window's fields carry over; the step gives the others. -/
theorem U.congr {G G' : ThreadId → Gh} {rX rX' : Res} {m m' : Mem} (hu : U K G rX m)
    (hld : ∀ u i e, (G' u).2.c = .ld i e → (G u).2.c = .ld i e)
    (hreg : ∀ u i jr sn e, (G' u).2.c = .reg i jr sn e → (G u).2.c = .reg i jr sn e)
    (hinc : ∀ u q n h, (G' u).2.c = .inc q n h → (G u).2.c = .inc q n h)
    (hhS : WS.hist m' = WS.hist m) (hhE : WE.hist m' = WE.hist m)
    (shape : Shape (fun u => (G' u).2) m') (rest : Rest rX' m') (blk : BlkOk m')
    (ws : WS.Ok m') (we : WE.Ok m') (cinv : C.Inv (L K) G' m') (sinv : (S K).Inv G' m')
    (swt : ∀ u, (G' u).2.s = .wt → (G' u).2.ph = .wt)
    (hmono : ∀ c, (L K).HB G m c → (L K).HB G' m' c)
    (q : ∀ w ∈ m'.waiters, w.2 = (L K).ptr ∨ w.2 = WE.ptr) : U K G' rX' m' := by
  have hS : C.S.hist m' = C.S.hist m := hhS
  refine ⟨shape, rest, blk, ws, we, cinv, sinv, swt, hu.hbE.step hmono (.inl hhE),
    fun u i e h => ?_, fun u i jr sn e h => ?_, fun v q' n h' h => ?_, q⟩
  · rw [hhE]; exact hu.ldE u i e (hld u i e h)
  · obtain ⟨h1, h2, h3⟩ := hu.regE u i jr sn e (hreg u i jr sn e h)
    refine ⟨by rw [hhE]; exact h1, fun h' => (FCond.Sated.congr hS).mpr (h2 (by rw [← hhE]; exact h')),
      fun v q' n h'' hv => by rw [hhE]; exact h3 v q' n h'' (hinc v q' n h'' hv)⟩
  · exact (FCond.Sated.congr hS).mpr (hu.incS v q' n h' (hinc v q' n h' h))

/-- **A step of the lock's code keeps `U`** (`FLock.Fits.stable`). -/
theorem stable (G : ThreadId → Gh) (rX : Res) (m m' : Mem) (t : ThreadId) (p : LPh) (h : Res)
    (hok : ok (G t)) (hng : (L K).ph (G t) ≠ .gone) (hna : (L K).ph (G t) ≠ .away)
    (hu : U K G rX m) (hs : (L K).Step t m m')
    (hrel : (L K).ph (G t) = .holds → p ≠ .holds → (L K).Before m' (m.clocks[t]!)) :
    U K (upd G t ((L K).set (G t) p h)) rX m' := by
  have hX : ∀ u, (upd G t ((L K).set (G t) p h) u).2 = (G u).2 :=
    fun u => congrFun (FLock.snd_set G t p h) u
  obtain ⟨hwS, hhS⟩ := hu.ws.lockStep hs apS
  obtain ⟨hwE, hhE⟩ := hu.we.lockStep hs apE
  have hst : ((S K).ph (G t)).isPst = false := by
    show ((G t).2.s).isPst = false
    rcases hok.2 with e | e <;> rw [e] <;> rfl
  refine hu.congr (fun u i e h' => by rwa [hX] at h') (fun u i jr sn e h' => by rwa [hX] at h')
    (fun u q n h'' h' => by rwa [hX] at h') hhS hhE ?_
    (hu.rest.congr fun l hl => hs.heap (box_notL hl)) (hu.blk.lstep hs) hwS hwE
    (hu.cinv.lstep hu.ws hu.we apS apE hok.1 hna (fun _ _ _ => rfl) hs)
    (hu.sinv.lstep hu.ws apS (fun _ _ _ => rfl) (fun _ _ _ => rfl) hst hng hs hrel)
    (fun u h' => by rw [hX] at h' ⊢; exact hu.swt u h') (fun c hc => hc.lstep hng hs hrel)
    (fun w hw => ?_)
  · have : (fun u => (upd G t ((L K).set (G t) p h) u).2) = fun u => (G u).2 := funext hX
    rw [this]; unfold Shape at *; rw [hs.threads]; exact hu.shape
  · by_cases hl : w.2 = (L K).ptr
    · exact .inl hl
    · exact hu.q w ((hs.waiters_mem w hl).mp hw)

/-- A stop keeps `U`: it reads no current thread. -/
theorem atStop {G : ThreadId → Gh} {rX : Res} {m : Mem} (t : ThreadId) (hu : U K G rX m) :
    U K G rX { m with current := t } :=
  have wordOk : ∀ W : Word 32 4, W.Ok m → W.Ok { m with current := t } :=
    fun _ hw => (hw.fields_native (m' := { m with current := t })
      rfl rfl rfl rfl (fun _ => VClock.le_refl _)).1
  ⟨hu.shape, hu.rest, hu.blk, wordOk _ hu.ws, wordOk _ hu.we,
    hu.cinv.stay (m' := { m with current := t }) rfl rfl rfl (fun _ hw _ => hw) (fun _ _ h => h)
      (Nat.le_refl _) (fun _ => VClock.le_refl _),
    hu.sinv.mono (m' := { m with current := t }) (fun _ => rfl) (fun _ => rfl) rfl
      (fun u h => hu.sinv.pst u h) (fun _ h => .inl h) (fun _ => VClock.le_refl _) (fun _ h => h)
      rfl (fun _ h => h) (fun _ hw => .inl hw) rfl,
    hu.swt, hu.hbE, hu.ldE, hu.regE, hu.incS, hu.q⟩

/-- **A framed step of `t` that keeps its places** (its part, its held resource) keeps `U`, given
both invariants after it, the rest's and the words' facts after it. -/
theorem U_frame {G : ThreadId → Gh} {rX rX' : Res} {m m' : Mem} {t : ThreadId} {g : Gh}
    {hF : Heap} (hu : U K G rX m) (hs : FStepIn hF m m')
    (hwL : ∀ x, (L K).o ≤ x → x < (L K).o + 4 → hF ((L K).b, x) ≠ none)
    (hok : ∀ i l, (L K).Loc m i l → l.len = 4) (hrest : Rest rX' m') (hbk : BlkOk m')
    (hwS : WS.Ok m') (hwE : WE.Ok m') (hhS : WS.hist m' = WS.hist m)
    (hhE : WE.hist m' = WE.hist m) (hX : g.2 = (G t).2) (hph : g.1.ph = (G t).1.ph)
    (hC : C.Inv (L K) (upd G t g) m') (hS : (S K).Inv (upd G t g) m') :
    U K (upd G t g) rX' m' := by
  have hX' : ∀ u, (upd G t g u).2 = (G u).2 := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hX]
    · rw [upd_ne _ _ e]
  have hP' : ∀ u, (upd G t g u).1.ph = (G u).1.ph := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hph]
    · rw [upd_ne _ _ e]
  refine hu.congr (fun u i e h => by rwa [hX'] at h) (fun u i jr sn e h => by rwa [hX'] at h)
    (fun u q n h' h => by rwa [hX'] at h) hhS hhE ?_ hrest hbk hwS hwE hC hS
    (fun u h => by rw [hX'] at h ⊢; exact hu.swt u h) (fun c hc => ?_)
    (fun w hw => by rw [hs.waiters] at hw; exact hu.q w hw)
  · have : (fun u => (upd G t g u).2) = fun u => (G u).2 := funext hX'
    rw [this]; unfold Shape at *; rw [hs.threads]; exact hu.shape
  · refine hc.mono (fun u h => .inl ?_) hs.clock (fun c hb => ?_) hs.threads (fun u h => ?_)
    · show (upd G t g u).1.ph = .holds; rw [hP']; exact h
    · obtain ⟨i, l, hl, hle⟩ := hb
      obtain ⟨j, hl'⟩ := (LockWord.loc_fstep (L := (L K).toLockWord) hs hwL hok l).mpr ⟨i, hl⟩
      exact ⟨j, l, hl', hle⟩
    · have h' : (upd G t g u).1.ph ≠ .gone := h
      rw [hP'] at h'; exact h'

/-- The condition's invariant over a framed step of `t` that keeps its places. -/
theorem cinv_frame {G : ThreadId → Gh} {rX : Res} {m m' : Mem} {t : ThreadId} {g : Gh}
    {hF : Heap} (hu : U K G rX m) (hs : FStepIn hF m m') (hhS : WS.hist m' = WS.hist m)
    (hhE : WE.hist m' = WE.hist m) (hX : g.2 = (G t).2) (hph : g.1.ph = (G t).1.ph) :
    C.Inv (L K) (upd G t g) m' :=
  hu.cinv.other (t := t) (g' := g) (congrArg (·.c) hX) (fun _ => hph)
    (fun _ h => by show g.1.ph = _; rw [hph]; exact h)
    (fun h => by show (g.2.s).isPst = true; rw [hX]; exact h) hhS hhE (by rw [hs.waiters])
    (fun w hw _ => .inl (by rw [hs.waiters] at hw; exact hw))
    (fun _ _ _ h => by rw [hs.woken]; exact h) (Nat.le_of_eq (by rw [hs.threads])) hs.clock

/-- **A step of `t` on its own part keeps `U`** (the condition's own-part step, a tick): the
lock's invariant after it pins the mailbox, so the words' cells stay but at the word `W`, which
the step gives. -/
theorem U_own {G : ThreadId → Gh} {rY : Res} {m m' : Mem} {t : ThreadId} {g : Gh}
    {W : Word 32 4} (hW2 : W = WS ∨ W = WE)
    (hu : U K G (rsum (W.cellsR m) rY) m) (hi : (L K).Inv G (rsum (W.cellsR m) rY) m)
    (hY : ∀ l, W.In l → rY.heap l = none)
    (hs : FStepIn (rsum ((L K).wordR m) (rsum (W.cellsR m) rY)).heap.erase m m')
    (hw' : W.Ok m') (hh : W.hist m' = W.hist m)
    (hi' : (L K).Inv (upd G t g) (rsum (W.cellsR m') rY) m')
    (hX : g.2 = (G t).2) (hph : g.1.ph = (G t).1.ph)
    (hS : (S K).Inv (upd G t g) m') :
    U K (upd G t g) (rsum (W.cellsR m') rY) m' := by
  have hWb := two_box hW2
  obtain ⟨rP, hP, hPoff, hrX⟩ := hu.rest
  have hg : rY.gh = rP.gh := by
    have := congrArg Res.gh hrX; simpa [cellsAt, Word.cellsR] using this
  have hbk' := blk_ofG hi' hP (by simp [cellsAt, Word.cellsR, hg])
  have hcs : ∀ l, BoxW l → ¬ W.In l → m'.heap l = m.heap l := by
    rintro ⟨b, x⟩ hl hw
    obtain ⟨h0, h1, h2⟩ := hl
    simp only at h0 h1 h2; subst h0
    refine cell_eq hu.blk hbk' hi' (by omega) ?_
    have := congrFun (congrArg Res.heap hrX) (0, x)
    simp only [FHeap.union_apply] at this ⊢
    rw [cellsAt_none hw, Option.none_or] at this ⊢
    rw [this, cellsAt_of (W := BoxW) ⟨rfl, h1, h2⟩, hPoff _ ⟨rfl, h1, h2⟩, Option.or_none]
  have hrest := Rest.step hWb ⟨rP, hP, hPoff, hrX⟩ rfl hY hcs
  have facts : ∀ W', (W' = WS ∨ W' = WE) → W'.Ok m' ∧ W'.hist m' = W'.hist m := by
    intro W' hW'
    rcases two_apart hW2 hW' with rfl | hap
    · exact ⟨hw', hh⟩
    · have hw : W'.Ok m := by
        rcases hW' with rfl | rfl
        · exact hu.ws
        · exact hu.we
      have hcover : ∀ l, W'.In l →
          (rsum ((L K).wordR m) (rsum (W.cellsR m) rY)).heap.erase l ≠ none :=
        fun l hl => frame_rest (rest_box hu.rest (fun _ hb => (box_cases hb).elim
          (fun h => hu.ws.cellIn h) (fun h => hu.we.cellIn h)) (two_box hW' l hl))
      have hnorm : ∀ l, W'.In l →
          (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm := by
        intro l hl
        rw [hcs l (two_box hW' l hl) (hap l hl)]
      exact ⟨hw.fstep hs hcover hnorm, Word.hist_fstep hw hs hcover hnorm⟩
  obtain ⟨hwS, hhS⟩ := facts _ (.inl rfl)
  obtain ⟨hwE, hhE⟩ := facts _ (.inr rfl)
  exact U_frame hu hs (fun x h1 h2 => frame_word hi h1 h2) (fun i l hl => (hi.w.loc.ok i l hl).1)
    hrest hbk' hwS hwE hhS hhE hX hph (cinv_frame hu hs hhS hhE hX hph) hS

/-- **A tick keeps `U`** (`FLock.PartTick`). -/
theorem tickStable (t : ThreadId) (G : ThreadId → Gh) (rX : Res) (m : Mem)
    (G' : ThreadId → Gh) (rX' : Res) (m' : Mem)
    (hs : (L K).PartTick t G rX m G' rX' m') (hu : U K G rX m) : U K G' rX' m' := by
  have hS := hu.sinv.partTick (fun _ _ => rfl) (fun _ _ => rfl) hs
  obtain ⟨_, _, hi, r, _, rfl, rfl, rfl, hi'⟩ := hs
  obtain ⟨rY, hrX, hY⟩ := Rest.split (fun _ => ws_box) hu.rest
  subst hrX
  exact U_own (.inl rfl) hu hi hY (FStepIn.ticked _ _) hu.ws.ticked rfl hi' rfl rfl hS

/-- **The waiter's entry into the condition keeps `U`** (`FSem.Move.enter`). -/
theorem enterStep {G : ThreadId → Gh} {rX : Res} {m : Mem} {t : ThreadId} (hu : U K G rX m)
    (hC : C.Inv (L K) (upd G t (C.set (G t) .en)) m)
    (hS : (S K).Inv (upd G t (C.set (G t) .en)) m) :
    U K (upd G t (C.set (G t) .en)) rX m := by
  obtain ⟨G', hG'⟩ : ∃ G', G' = upd G t (C.set (G t) .en) := ⟨_, rfl⟩
  rw [← hG'] at hC hS ⊢
  have hXt : (G' t).2 = { (G t).2 with c := .en } := by rw [hG', upd_self] <;> rfl
  have hX : ∀ u, u ≠ t → G' u = G u := fun u e => by rw [hG']; exact upd_ne _ _ e
  have hps : ∀ u, (G' u).2.ph = (G u).2.ph ∧ (G' u).2.s = (G u).2.s := fun u => by
    by_cases e : u = t
    · subst e; rw [hXt]; exact ⟨rfl, rfl⟩
    · rw [hX u e]; exact ⟨rfl, rfl⟩
  have hlp : ∀ u, (G' u).1.ph = (G u).1.ph := fun u => by
    by_cases e : u = t
    · subst e; rw [hG', upd_self] <;> rfl
    · rw [hX u e]
  -- `t` is at `en` after the step, at none of the window's places
  have hc : ∀ u (P : CPh → Prop), ¬ P .en → P (G' u).2.c → P (G u).2.c :=
    fun u P hP h => by
      by_cases e : u = t
      · subst e; rw [hXt] at h; exact absurd h hP
      · rwa [hX u e] at h
  refine hu.congr (fun u i e h => hc u (· = .ld i e) (fun h => by cases h) h)
    (fun u i jr sn e h => hc u (· = .reg i jr sn e) (fun h => by cases h) h)
    (fun u q n h' h => hc u (· = .inc q n h') (fun h => by cases h) h) rfl rfl ?_
    hu.rest hu.blk hu.ws hu.we hC hS (fun u h => ?_) (fun c hc => ?_) hu.q
  · refine Shape.congr hu.shape rfl (fun u => (hps u).1) fun u hu' => ⟨?_, ?_⟩
    · exact Classical.byContradiction fun hne => absurd (hC.ex u hne) (by simp only [ThreadId] at *; omega)
    · exact Classical.byContradiction fun hne => absurd (hS.ex u hne) (by simp only [ThreadId] at *; omega)
  · rw [(hps u).1]; exact hu.swt u (by rw [← (hps u).2]; exact h)
  · exact hc.mono (fun u h => .inl (by show (G' u).1.ph = .holds; rw [hlp]; exact h))
      (fun _ => VClock.le_refl _) (fun _ h => h) rfl
      (fun u h => by have h' : (G' u).1.ph ≠ .gone := h; rwa [hlp] at h')

/-- **The holder's step in the semaphore's code keeps `U`** (`FSem.Move.hold`): the lock's
invariant after it (at some ghost values) pins the mailbox, so the words' cells stay. -/
theorem holdStep {G : ThreadId → Gh} {rX : Res} {m m' : Mem} {t : ThreadId} {s : SPh} {h : Res}
    (hu : U K G rX m) (hh : (L K).ph (G t) = .holds) (hL : (L K).Inv G rX m)
    (hfs : FStepIn (rsum ((L K).wordR m) rX).heap.erase m m')
    (hL' : ∃ G'', (L K).Inv G'' rX m') (hgo : (S K).Go G m t s)
    (hC : C.Inv (L K) (upd G t ((S K).set ((L K).set (G t) .holds h) s)) m')
    (hS : (S K).Inv (upd G t ((S K).set ((L K).set (G t) .holds h) s)) m') :
    U K (upd G t ((S K).set ((L K).set (G t) .holds h) s)) rX m' := by
  obtain ⟨G'', hi'⟩ := hL'
  have hcs := cells_same hu.blk hi' hu.rest
  have facts : ∀ W : Word 32 4, (W = WS ∨ W = WE) → W.Ok m → W.Ok m' ∧ W.hist m' = W.hist m := by
    intro W hW hw
    have hcover : ∀ l, W.In l → (rsum ((L K).wordR m) rX).heap.erase l ≠ none :=
      fun l hl => frame_rest (rest_box hu.rest (fun _ hb => (box_cases hb).elim
        (fun h => hu.ws.cellIn h) (fun h => hu.we.cellIn h)) (two_box hW l hl))
    have hnorm : ∀ l, W.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm :=
      fun l hl => by rw [hcs l (two_box hW l hl)]
    exact ⟨hw.fstep hfs hcover hnorm, Word.hist_fstep hw hfs hcover hnorm⟩
  obtain ⟨hwS, hhS⟩ := facts _ (.inl rfl) hu.ws
  obtain ⟨hwE, hhE⟩ := facts _ (.inr rfl) hu.we
  obtain ⟨G', hG'⟩ : ∃ G', G' = upd G t ((S K).set ((L K).set (G t) .holds h) s) := ⟨_, rfl⟩
  rw [← hG'] at hC hS ⊢
  have hXt : (G' t).2 = { (G t).2 with s := s } := by rw [hG', upd_self] <;> rfl
  have hX : ∀ u, u ≠ t → G' u = G u := fun u e => by rw [hG']; exact upd_ne _ _ e
  have hpc : ∀ u, (G' u).2.ph = (G u).2.ph ∧ (G' u).2.c = (G u).2.c := fun u => by
    by_cases e : u = t
    · subst e; rw [hXt]; exact ⟨rfl, rfl⟩
    · rw [hX u e]; exact ⟨rfl, rfl⟩
  have hlp : ∀ u, (G' u).1.ph = (G u).1.ph := fun u => by
    by_cases e : u = t
    · subst e; rw [hG', upd_self]; exact hh.symm
    · rw [hX u e]
  refine hu.congr (fun u i e h' => by rwa [(hpc u).2] at h')
    (fun u i jr sn e h' => by rwa [(hpc u).2] at h') (fun u q n h'' h' => by rwa [(hpc u).2] at h')
    hhS hhE ?_ (hu.rest.congr hcs) (blk_of hi' hu.rest) hwS hwE hC hS (fun u h' => ?_)
    (fun c hc => ?_) (fun w hw => by rw [hfs.waiters] at hw; exact hu.q w hw)
  · refine Shape.congr hu.shape hfs.threads (fun u => (hpc u).1) fun u hu' => ⟨?_, ?_⟩
    · exact Classical.byContradiction fun hne => absurd (hC.ex u hne) (by rw [hfs.threads]; simp only [ThreadId] at *; omega)
    · exact Classical.byContradiction fun hne => absurd (hS.ex u hne) (by rw [hfs.threads]; simp only [ThreadId] at *; omega)
  · rw [(hpc u).1]
    by_cases e : u = t
    · subst e
      rw [hXt] at h'
      have h'' : s = .wt := h'
      subst h''
      rcases hgo with e | ⟨-, -, hwx⟩ | ⟨e, -⟩ | ⟨e, -⟩
      · exact hu.swt u e.symm
      · exact hwx
      · cases e
      · cases e
    · rw [hX u e] at h'; exact hu.swt u h'
  · exact hc.mono (fun u h => .inl (by show (G' u).1.ph = .holds; rw [hlp]; exact h)) hfs.clock
      (FLock.Inv.before_fstep hL hfs) hfs.threads
      (fun u h => by have h' : (G' u).1.ph ≠ .gone := h; rwa [hlp] at h')

/-! ## A step of the condition's code -/

theorem next_to_ld {a : CPh} {i : Nat} {e : BitVec 32} (h : CPh.Next a (.ld i e)) :
    a = .en ∨ a = .ld i e := by
  cases a with
  | en => exact .inl rfl
  | ld i' e' => exact .inr h
  | _ => simp [CPh.Next] at h

theorem next_to_reg {a : CPh} {i jr : Nat} {sn : Bool} {e : BitVec 32}
    (h : CPh.Next a (.reg i jr sn e)) :
    (∃ e', a = .ld i e') ∨ ∃ i₀ sn₀ e₀, a = .reg i₀ jr sn₀ e₀ ∧ i₀ ≤ i := by
  cases a with
  | ld i' e' => obtain ⟨h1, -, -⟩ := h; exact .inl ⟨e', by rw [h1]⟩
  | reg i₀ jr₀ sn₀ e₀ => obtain ⟨h1, h2⟩ := h; exact .inr ⟨i₀, sn₀, e₀, by rw [h1], h2⟩
  | _ => simp [CPh.Next] at h

/-- **A step of the condition's code keeps `U`** (`FLock.Fits.kstep` of `FCond.prim`, inside
`FSem.prim`). -/
theorem cstep (G : ThreadId → Gh) (rY : Res) (m m' : Mem) (t : ThreadId) (p : CPh) (q : LPh)
    (h : Res) (W : Word 32 4) (hW : W = C.S ∨ W = C.Ep)
    (hn : CPh.Next (C.ph (G t)) p)
    (hq : (q = (L K).ph (G t) ∧ h = (L K).held (G t)) ∨
      (((L K).ph (G t) = .out ∨ ((L K).ph (G t) = .away ∧ (C.ph (G t)).isReg = true)) ∧
        (q = .out ∨ (q = .away ∧ p.waits = true)) ∧ h = rnil))
    (hs : C.MStep W t m m')
    (hEp : C.Ep.hist m' = C.Ep.hist m ∨ ∃ q n h, C.ph (G t) = .inc q n h ∧ p = .wk n q h)
    (hsg : C.SigStep t (C.ph (G t)) p m m') (hwL : (L K).WInv ((L K).pl G) m)
    (hu : U K G (rsum (W.cellsR m) rY) m) (hY : ∀ l, W.In l → rY.heap l = none)
    (hI : C.Inv (L K) (upd G t ((L K).set (C.set (G t) p) q h)) m')
    (hSI : (S K).Inv (upd G t ((L K).set (C.set (G t) p) q h)) m') :
    U K (upd G t ((L K).set (C.set (G t) p) q h)) (rsum (W.cellsR m') rY) m' := by
  have hW2 : W = WS ∨ W = WE := hW
  have hth := hs.threads
  have hwd := fun W' (hW' : W' = WS ∨ W' = WE) (h : W'.Ok m) =>
    hs.word_rmw h (two_word hW2 hW') (two_word (W := WE) (.inr rfl) hW')
  have hn' : CPh.Next ((G t).2.c) p := hn
  -- the new ghost values
  obtain ⟨G', hG'⟩ : ∃ G', G' = upd G t ((L K).set (C.set (G t) p) q h) := ⟨_, rfl⟩
  rw [← hG'] at hI hSI ⊢
  have hG : ∀ u, u ≠ t → G' u = G u := fun u hu => by rw [hG']; exact upd_ne _ _ hu
  have hXt : (G' t).2 = { (G t).2 with c := p } := by rw [hG', upd_self] <;> rfl
  have hLt : (G' t).1.ph = q := by rw [hG', upd_self] <;> rfl
  have hct : (G' t).2.c = p := congrArg X.c hXt
  have hps : ∀ u, (G' u).2.ph = (G u).2.ph ∧ (G' u).2.s = (G u).2.s := fun u => by
    by_cases e : u = t
    · subst e; rw [hXt]; exact ⟨rfl, rfl⟩
    · rw [hG u e]; exact ⟨rfl, rfl⟩
  -- only `main` registers
  have h0 : ∀ u, ((G u).2.c).isReg = true → u = 0 := fun u hr => hu.waits0 (CPh.isReg_waits hr)
  have h0' : ∀ u, ((G' u).2.c).isReg = true → u = 0 := fun u hr => by
    have hw : (G' u).2.s = .wt := hSI.wt u (CPh.isReg_waits hr)
    exact hu.zero_of_wt (by rw [← (hps u).2]; exact hw)
  have hwl := wlast hu.cinv h0
  have hwl' := wlast hI h0'
  have hnew : ((G' 0).2.c).isReg = true → ((G 0).2.c).isReg = false →
      t = 0 ∧ ((G t).2.c).crit = true := fun h1 h2 => by
    by_cases et : t = 0
    · subst et; rw [hct] at h1; exact ⟨rfl, hn'.crit_of_reg h1 h2⟩
    · rw [hG 0 (Ne.symm et)] at h1; rw [h1] at h2; cases h2
  -- the state's writes: the same, or one new
  have hpos : 0 < (C.S.hist m).size := hu.cinv.spos
  have hSh : WS.hist m' = WS.hist m ∨ ∃ x : Word.Entry, WS.hist m' = (WS.hist m).push x := by
    rcases (hwd _ (.inl rfl) hu.ws).2 with e | ⟨-, _, _, e⟩
    · exact .inl e
    · exact .inr ⟨_, e⟩
  have hsat : (((G' 0).2.c).isReg = true → ((G 0).2.c).isReg = true) → C.Sated m →
      C.Sated m' := fun hr hsw => by
    rcases hSh with e | ⟨x, e⟩
    · exact (FCond.Sated.congr (C := C) e).mpr hsw
    · refine hI.sated_push hpos e hsw ?_
      rw [← FCond.lastS_push (C := C) e, hwl', hwl]
      cases h1 : ((G' 0).2.c).isReg
      · simp
      · simp [hr h1]
  -- the epoch's writes: the same, or the `epoch += 1` of `t` at `inc` (holding the mutex)
  have hEh : WE.hist m' = WE.hist m ∨ ∃ x : Word.Entry,
      WE.hist m' = (WE.hist m).push x ∧ x.clock = m'.clocks[t]! := by
    rcases (hwd _ (.inr rfl) hu.we).2 with e | ⟨-, _, _, e⟩
    · exact .inl e
    · exact .inr ⟨_, e, rfl⟩
  have hEp' : WE.hist m' = WE.hist m ∨ ∃ q n h', (G t).2.c = .inc q n h' ∧ p = .wk n q h' := hEp
  have hEs : (∀ q n h', (G t).2.c ≠ .inc q n h') → WE.hist m' = WE.hist m := fun hni =>
    hEp'.resolve_right fun ⟨q, n, h', e, _⟩ => hni q n h' e
  -- the lock place of `t` changes only out of the mutex
  have hlq : (G t).1.ph ≠ q → (G t).1.ph = .out ∨ (G t).1.ph = .away := fun hne => by
    rcases hq with ⟨rfl, -⟩ | ⟨h1, -, -⟩
    · exact absurd rfl hne
    · exact h1.imp_right And.left
  have hhold : (G t).1.ph = .holds → (G' t).1.ph = .holds := fun hh => by
    rw [hLt]
    by_cases hqe : (G t).1.ph = q
    · rw [← hqe]; exact hh
    · rcases hlq hqe with h' | h' <;> rw [hh] at h' <;> cases h'
  have hmono : ∀ c, (L K).HB G m c → (L K).HB G' m' c := fun c hc =>
    hc.mono (fun u hu' => .inl (by
        show (G' u).1.ph = .holds
        by_cases e : u = t
        · subst e; exact hhold hu'
        · rw [hG u e]; exact hu'))
      hs.clocks (fun _ ⟨i, l, hl, hc⟩ => ⟨i, l, hs.lockLoc (two_ap hW2) apE hl, hc⟩) hth
      (fun u hg => by
        show (G u).1.ph ≠ .gone
        have hg' : (G' u).1.ph ≠ .gone := hg
        by_cases e : u = t
        · subst e
          by_cases hqe : (G u).1.ph = q
          · rw [hqe]; rw [hLt] at hg'; exact hg'
          · rcases hlq hqe with h' | h' <;> rw [h'] <;> nofun
        · rwa [hG u e] at hg')
  have hEhb : WE.hist m' = WE.hist m ∨
      ∃ x : Word.Entry, WE.hist m' = (WE.hist m).push x ∧ (L K).HB G' m' x.clock := by
    rcases hEp' with e | ⟨q₀, n₀, h₀, e, -⟩
    · exact .inl e
    · rcases hEh with e' | ⟨x, e', hx⟩
      · exact .inl e'
      · refine .inr ⟨x, e', FLock.HB.of_holder (t := t) (hhold (hu.sig_holds (by rw [e] <;> rfl)))
          (by rw [hx]; exact VClock.le_refl _)⟩
  -- a post (`sl → inc`): `waiters` stays, `signals` goes up
  have hpost : ∀ sh c q₀ n₀ h₀, (G t).2.c = .sl sh c → p = .inc q₀ n₀ h₀ →
      ∃ x, WS.hist m' = (WS.hist m).push x ∧ FCond.wOf x = FCond.wOf (C.lastS m) ∧
        FCond.sOf (C.lastS m) < FCond.sOf x ∧ FCond.sOf x ≤ FCond.wOf x := by
    intro sh c q₀ n₀ h₀ hsl hp
    obtain ⟨hq', ⟨x, hx⟩, -, -, hlt⟩ := FCond.SigStep.inc_fresh (C := C) (L := L K) (G := G)
      (G' := G') (t := t) (q := q₀) (n := n₀) (h := h₀) hsl (by show (G' t).2.c = _; rw [hct, hp]) hG
      (by show C.SigStep t (C.ph (G t)) (G' t).2.c m m'; rw [hct]; exact hsg) hu.cinv hI
    have hr0 : ((G' 0).2.c).isReg = ((G 0).2.c).isReg := by
      by_cases e : t = 0
      · subst e; rw [hct, hp, hsl] <;> rfl
      · rw [hG 0 (Ne.symm e)]
    have hxq : (C.S.hist m')[q₀]! = x := by rw [hx, hq', Word.get_push_eq]
    have hxq1 : (C.S.hist m')[q₀ - 1]! = C.lastS m := by
      rw [hx, hq']; exact Word.get_push_lt (by omega)
    refine ⟨x, hx, ?_, ?_, ?_⟩
    · rw [← FCond.lastS_push (C := C) hx, hwl', hwl, hr0]
    · rw [hxq, hxq1] at hlt; exact hlt
    · have := (hI.sv q₀ (by rw [hx, Array.size_push, ← hq']; omega)).2
      rw [hxq] at this; exact this
  refine ⟨?_, Rest.step (two_box hW2) hu.rest rfl hY fun l _ hw => hs.cells hw,
    hu.blk.of_block fun _ _ hb => hs.block hb, (hwd _ (.inl rfl) hu.ws).1,
    (hwd _ (.inr rfl) hu.we).1, hI, hSI, fun u h' => ?_, hu.hbE.step hmono hEhb,
    fun u i e h' => ?_, fun u i jr sn e h' => ?_, fun v q' n h' h'' => ?_, fun w hw => ?_⟩
  · -- shape
    refine Shape.congr hu.shape hth (fun u => (hps u).1) fun u hu' => ⟨?_, ?_⟩
    · exact Classical.byContradiction fun hne => absurd (hI.ex u hne) (by rw [hth]; simp only [ThreadId] at *; omega)
    · exact Classical.byContradiction fun hne => absurd (hSI.ex u hne) (by rw [hth]; simp only [ThreadId] at *; omega)
  · -- swt
    rw [(hps u).1]; exact hu.swt u (by rw [← (hps u).2]; exact h')
  · -- ldE
    by_cases e' : u = t
    · subst e'
      rw [hct] at h'; subst h'
      rcases next_to_ld hn' with ha | ha
      · -- `en → ld`: the waiter holds the mutex and reads the newest epoch write
        have hE := hEs fun _ _ _ h'' => by rw [ha] at h''; cases h''
        have hi : i < (WE.hist m).size := by
          rw [← hE]; exact (hI.ld u i e (by show (G' u).2.c = _; rw [hct])).1
        have hfl : Word.Floor (WE.hist m) (m.clocks[u]!) i := by
          have := hsg; rw [show C.ph (G u) = .en from ha] at this; exact this
        have := hu.hbE.last hwL (hu.cinv.crit u (by show ((G u).2.c).crit = true; rw [ha] <;> rfl))
          hi hfl
        rw [hE]; omega
      · rw [hEs fun _ _ _ h'' => by rw [ha] at h''; cases h'']; exact hu.ldE u i e ha
    · rw [hG u e'] at h'
      have hE : WE.hist m' = WE.hist m := hEs fun q₀ n₀ h₀ hi =>
        hu.crit_sig (u := u) (v := t) (by rw [h'] <;> rfl) (by rw [hi] <;> rfl)
      rw [hE]; exact hu.ldE u i e h'
  · -- regE
    by_cases e' : u = t
    · subst e'
      rw [hct] at h'; subst h'
      rcases next_to_reg hn' with ⟨e₀, ha⟩ | ⟨i₀, sn₀, e₀, ha, hle⟩
      · -- the registration: the epoch has its newest write, and nobody signals
        have hE := hEs fun _ _ _ h'' => by rw [ha] at h''; cases h''
        have h1 := hu.ldE u i e₀ ha
        refine ⟨by rw [hE]; omega, fun h2 => by rw [hE] at h2; omega, fun v q' n h'' hv => ?_⟩
        have hvt : v ≠ u := fun hvu => by subst hvu; rw [hct] at hv; cases hv
        rw [hG v hvt] at hv
        exact (hu.crit_sig (u := u) (v := v) (by rw [ha] <;> rfl) (by rw [hv] <;> rfl)).elim
      · -- a registered waiter's step: its saved write is at most a later one
        have hE := hEs fun _ _ _ h'' => by rw [ha] at h''; cases h''
        obtain ⟨r1, r2, r3⟩ := hu.regE u i₀ jr sn₀ e₀ ha
        have hlt : i < (WE.hist m).size := by
          rw [← hE]; exact (hI.reg u i jr sn e (by show (G' u).2.c = _; rw [hct])).1
        refine ⟨by rw [hE]; omega, fun h2 => ?_, fun v q' n h'' hv => ?_⟩
        · rw [hE] at h2
          have hii : i₀ = i := by omega
          subst hii
          refine hsat (fun _ => ?_) (r2 h2)
          obtain rfl := h0 u (by rw [ha] <;> rfl)
          rw [ha] <;> rfl
        · have hvt : v ≠ u := fun hvu => by subst hvu; rw [hct] at hv; cases hv
          rw [hG v hvt] at hv
          have := r3 v q' n h'' hv
          rw [hE]; omega
    · rw [hG u e'] at h'
      obtain ⟨r1, r2, r3⟩ := hu.regE u i jr sn e h'
      have hu0 : u = 0 := h0 u (by rw [h'] <;> rfl)
      have ht0 : t ≠ 0 := fun ht => e' (hu0.trans ht.symm)
      have hr : ((G' 0).2.c).isReg = true → ((G 0).2.c).isReg = true := fun h1 => by
        rwa [hG 0 (Ne.symm ht0)] at h1
      have hlt : i < (WE.hist m).size := (hu.cinv.reg u i jr sn e h').1
      rcases hEh with hE | ⟨x, hE, -⟩
      · refine ⟨by rw [hE]; exact r1, fun h2 => hsat hr (r2 (by rw [← hE]; exact h2)),
          fun v q' n h'' hv => ?_⟩
        rw [hE]
        by_cases evt : v = t
        · subst evt
          rw [hct] at hv; subst hv
          rcases CPh.Next.to_inc hn' with ⟨sh, c, hsl⟩ | hsame
          · -- a post: none while the state is sated, so the epoch has one write after `i`
            obtain ⟨x, -, hw, hs1, hs2⟩ := hpost sh c q' n h'' hsl rfl
            refine Classical.byContradiction fun hne => ?_
            have hsw := r2 (by omega)
            unfold FCond.Sated at hsw
            omega
          · exact r3 v q' n h'' hsame
        · rw [hG v evt] at hv; exact r3 v q' n h'' hv
      · -- the epoch's `+= 1`: by `t` at `inc`, after its post
        obtain ⟨q₀, n₀, h₀, hinc, hpw⟩ : ∃ q₀ n₀ h₀, (G t).2.c = .inc q₀ n₀ h₀ ∧
            p = .wk n₀ q₀ h₀ := by
          rcases hEp' with e | h''
          · have := congrArg Array.size (hE.symm.trans e); simp at this
          · exact h''
        have h1 := r3 t q₀ n₀ h₀ hinc
        refine ⟨by rw [hE, Array.size_push]; omega, fun _ => hsat hr (hu.incS t q₀ n₀ h₀ hinc),
          fun v q' n h'' hv => ?_⟩
        have hvt : v ≠ t := fun hvt => by subst hvt; rw [hct, hpw] at hv; cases hv
        rw [hG v hvt] at hv
        exact absurd (hwL.one v t (hu.sig_holds (by rw [hv] <;> rfl))
          (hu.sig_holds (by rw [hinc] <;> rfl))) hvt
  · -- incS
    have hr : ¬ ((G t).2.c).crit = true →
        (((G' 0).2.c).isReg = true → ((G 0).2.c).isReg = true) := fun hnc h1 => by
      cases h2 : ((G 0).2.c).isReg
      · exact absurd (hnew h1 h2).2 hnc
      · rfl
    by_cases evt : v = t
    · subst evt
      rw [hct] at h''; subst h''
      rcases CPh.Next.to_inc hn' with ⟨sh, c, hsl⟩ | hsame
      · obtain ⟨x, hx, hw, hs1, hs2⟩ := hpost sh c q' n h' hsl rfl
        have hw1 : FCond.wOf (C.lastS m) ≤ 1 := by rw [hwl]; split <;> omega
        show FCond.sOf (C.lastS m') = FCond.wOf (C.lastS m')
        rw [FCond.lastS_push (C := C) hx]
        omega
      · exact hsat (hr (by rw [hsame]; simp [CPh.crit])) (hu.incS v q' n h' hsame)
    · rw [hG v evt] at h''
      refine hsat (hr fun hc => ?_) (hu.incS v q' n h' h'')
      exact hu.crit_sig (u := t) (v := v) hc (by rw [h''] <;> rfl)
  · -- q
    rcases hs.waiters hw with h' | rfl
    · exact hu.q w h'
    · exact .inr rfl

/-! ## The walks' ghost values -/

/-- A thread out of the lock's code with part `r` at the places `x`. -/
def gO (r : Res) (x : X) : Gh := (⟨.out, r, rnil⟩, x)

/-- No thread at the start. -/
def G0 : ThreadId → Gh := fun _ => (⟨.gone, rnil, rnil⟩, {})

/-- **`U` after a move of the program places at the same memory** (the walks' ghost moves: `main`'s
take, the producer's post): the condition's and the semaphore's places and the lock places stay;
the shape, both invariants and the waiting role after it are the move's to show. -/
theorem U.xMove {G G' : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U K G rX m)
    (hc : ∀ u, (G' u).2.c = (G u).2.c) (hl : ∀ u, (G' u).1.ph = (G u).1.ph)
    (shape : Shape (fun u => (G' u).2) m) (cinv : C.Inv (L K) G' m) (sinv : (S K).Inv G' m)
    (swt : ∀ u, (G' u).2.s = .wt → (G' u).2.ph = .wt) : U K G' rX m :=
  hu.congr (fun u i e h => by rwa [hc] at h) (fun u i jr sn e h => by rwa [hc] at h)
    (fun u q n h' h => by rwa [hc] at h) rfl rfl shape hu.rest hu.blk hu.ws hu.we cinv sinv swt
    (fun c h => h.mono (fun u h' => .inl (by show (G' u).1.ph = .holds; rw [hl]; exact h'))
      (fun _ => VClock.le_refl _) (fun _ h => h) rfl
      (fun u h' => by have h'' : (G' u).1.ph ≠ .gone := h'; rwa [hl] at h''))
    hu.q

/-! ## The protocol keeps the semaphore -/

/-- `R` reads the program places only. -/
theorem R_congr {Y Y' : ThreadId → X} (h : ∀ u, (Y' u).ph = (Y u).ph) : R Y' = R Y := by
  unfold R; rw [show (fun u => (Y' u).ph) = fun u => (Y u).ph from funext h]

/-- **The protocol has the lock**, for the threads that run its code (`ok`). -/
theorem fitsL : (L K).Fits (FPrim.empty Gh) (proto K) (U K) ok :=
  .ofLock (fun _ _ => Iff.rfl) (fun _ h => h.1) (fun _ h => h.1) (fun _ _ _ => Iff.rfl)
    (fun _ _ => Iff.rfl) stable (fun _ _ _ t _ hu => atStop t hu) tickStable

/-- **The protocol keeps the semaphore** (`FSem.Fits`): the lock's laws, the steps of the
condition's and the semaphore's code (`cstep`, `U_own`, `enterStep`, `holdStep`), the ticks, and
the window: a registered `main` has at most one epoch write after its saved one (`regE`). -/
theorem fitsS : (S K).Fits (proto K) (U K) ok where
  ok_s _ h := h.2
  win G rX m hu u i jr e hreg _ _ := by
    have := (hu.regE u i jr false e hreg).1
    show (WE.hist m).size ≤ i + 4294967296
    omega
  inv _ _ := Iff.rfl
  fin _ h := h.1
  joins _ h := h.1
  ok_set _ _ _ := Iff.rfl
  ok_setPart _ _ := Iff.rfl
  stable := stable
  atStop _ _ _ t _ hu := atStop t hu
  kfin g h := by show ((g.2.c, g.2.s) : CPh × SPh) = (.out, .out); rw [h.2]
  kjoins g h := by show ((g.2.c, g.2.s) : CPh × SPh) = (.out, .out); rw [h.2]
  sub _ _ _ hu := ⟨⟨hu.cinv, fun W hW => by
    rcases hW with rfl | rfl
    · exact ⟨hu.ws, Rest.split (fun _ => ws_box) hu.rest⟩
    · exact ⟨hu.we, Rest.split (fun _ => we_box) hu.rest⟩⟩, hu.sinv⟩
  apart W hW := by rcases hW with rfl | rfl <;> first | exact apS | exact apE
  lph _ _ := rfl
  lpart _ _ := rfl
  lheld _ _ := rfl
  lR G t p r hr := by
    change R (fun u => (upd G t ((S K).place.set (G t) p) u).2) r
    rw [R_congr (Y' := fun u => (upd G t ((S K).place.set (G t) p) u).2)
      (Y := fun u => (G u).2) fun u => by
        show (upd G t ((S K).place.set (G t) p) u).2.ph = (G u).2.ph
        by_cases e : u = t
        · subst e; rw [upd_self] <;> rfl
        · rw [upd_ne _ _ e]]
    exact hr
  ph_l _ _ _ := rfl
  set_l _ _ _ _ := rfl
  ph_part _ _ := rfl
  set_part _ _ _ := rfl
  role_l _ _ _ _ := Iff.rfl
  role_part _ _ _ := Iff.rfl
  ok_calm _ _ _ hp hq := ⟨fun _ => hq, fun _ => hp⟩
  kstep := by
    intro t G rX m G' rX' m' hs hu
    rcases hs with ⟨hSI, hs | ⟨hC, hmv⟩⟩ | hs
    · rcases hs with ⟨W, rY, hW, rfl, rfl, hY, hI,
        ⟨p, q, h, ⟨hn, hq, hms, hEp, hsg⟩, hwL, rfl⟩ | ⟨r, -, hi, -, hfs, -, hw', hh, hL, rfl⟩⟩
      · exact cstep G rY m m' t p q h W hW hn hq hms hEp hsg hwL hu hY hI hSI
      · exact U_own hW hu hi hY hfs hw' hh hL rfl rfl hSI
    · cases hmv with
      | enter _ _ _ _ _ => exact enterStep hu hC hSI
      | hold s h hh _ hL _ hfs hL' _ hgo => exact holdStep hu hh hL hfs hL' hgo hC hSI
    · exact tickStable t G rX m G' rX' m' hs hu

end Sync.Mailbox
