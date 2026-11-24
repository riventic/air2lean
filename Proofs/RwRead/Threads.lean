import Proofs.RwRead.Ops
import ZigLean.Sep.Full.RwLockThreads
import ZigLean.Sep.Full.RwLockEnds

/-!
# The threads of `rwLockRead` and `rwLockSnapshotPair`: the spawn, the writer's end, the join

The steps of the two programs at which a thread's place in the program changes outside the lock's
entry points (`Proofs/RwRead/Protocol.lean`, `Ph`), each from the library's rule for every
protocol with the reader/writer lock (`ZigLean/Sep/Full/RwLockThreads.lean`,
`ZigLean/Sep/Full/RwLockEnds.lean`); a walk of `main` and of the writer's end uses them as `fsym`
rules. The program supplies only its threads' fact (`Thr`) and that `n`'s value (`cnt`) stays.

- **The threads' fact** over each change: `Thr.spawn` (`main` `pre → run`, the writer new at
  `wr 0`, one more record), `Thr.toJoins` (`main` `run → joins`), `Thr.finish` (the writer
  `wr k → fin`), `Thr.joined` (`main` `joins → done`, the writer's record joined); what it gives
  at a place: `Thr.pre`, `Thr.joins_rec`, `spawners`, `joinedAll_done`.
- `inv_spawn`: `main`'s spawn of the writer (`FRw.Base.spawn`): the plain mode is copied for the
  child.
- `inv_joins`: `main` moves to its join (`FRw.Base.inv_ghost`), as `Proto.joins` asks before the
  join's stop.
- `inv_end`, `fin_gF`, `kid_end`: the writer's end (`FRw.Base.inv_ghost`): it is `gone` at both
  mutexes, at `fin`, and its part holds no read share (`Proto.fin`, `Proto.QKid`).
- `wp_join`: `main`'s join of the writer (`FRw.Base.wp_join`): `main` goes on at `done` with the
  writer's part in its own, every thread joined.
-/

namespace Zig

namespace Full

/-- A resource with the plain mode keeps it next to anything (`Res.plain_of_sep`, on the left).
(Should move to `ZigLean/Sep/Full/Ghost.lean`, next to `Res.plain_of_sep`.) -/
theorem Res.Plain.rsum_left {a : Res} (h : a.Plain) (b : Res) : (rsum a b).Plain := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by simp only [Ghost.add_ac, ACell.add_frag]; omega,
    by simp only [Ghost.add_ac, ACell.add_frag]; omega⟩

end Full

namespace RwRead

open Conc Conc.Proto Full Full.FAssn

variable {Tgt : Type} {wOf : Tgt → Option Ptr}

/-! ## The threads' fact over the changes of place -/

/-- Before `main`'s spawn there is one thread, and no other id has a place. -/
theorem Thr.pre {Y : ThreadId → Ph} {ts : Array ThreadRec} (h : Thr Y ts) (h0 : Y 0 = .pre) :
    ts.size = 1 ∧ ∀ u, 1 ≤ u → Y u = .none := by
  obtain ⟨-, ⟨hs, -, hn⟩ | ⟨-, -, ⟨-, h0c, -⟩ | ⟨-, h0c, -⟩⟩⟩ := h
  · exact ⟨hs, hn⟩
  · rcases h0c with e | e <;> rw [e] at h0 <;> cases h0
  · rw [h0c] at h0; cases h0

/-- **The threads after `main`'s spawn**: `main` at `run`, the writer new at `wr 0`, with its
record. -/
theorem Thr.spawn {Y Y' : ThreadId → Ph} {ts : Array ThreadRec} (h : Thr Y ts) (h0 : Y 0 = .pre)
    (h0' : Y' 0 = .run) (h1' : Y' 1 = .wr 0) (hY : ∀ u, 2 ≤ u → Y' u = Y u) :
    Thr Y' (ts.push { spawner := 0, joined := false }) := by
  obtain ⟨ht0, ⟨hs, -, hn⟩ | ⟨-, -, ⟨-, h0c, -⟩ | ⟨-, h0c, -⟩⟩⟩ := h
  · refine ⟨?_, .inr ⟨by simp [Array.size_push, hs], fun u hu => ?_,
      .inl ⟨?_, .inl h0', .inr ⟨0, by decide, h1'⟩⟩⟩⟩
    · first
        | (rw [Array.getElem?_push, hs, if_neg (by decide)]; exact ht0)
        | (obtain ⟨h0lt, e0⟩ := Array.getElem?_eq_some_iff.mp ht0
           exact Array.getElem?_eq_some_iff.mpr ⟨by rw [Array.size_push]; omega,
             by rw [Array.getElem_push_lt h0lt]; exact e0⟩)
    · rw [hY u hu]; exact hn u (Nat.le_trans (by decide : 1 ≤ 2) hu)
    · first
        | rw [Array.getElem?_push, hs, if_pos rfl]
        | (have e : (ts.push { spawner := 0, joined := false })[ts.size]? =
               some { spawner := 0, joined := false } := Array.getElem?_push_size
           rw [hs] at e; exact e)
        | (have e : (ts.push { spawner := 0, joined := false })[ts.size]? =
               some { spawner := 0, joined := false } := Array.getElem?_push_size _ _
           rw [hs] at e; exact e)
  · rcases h0c with e | e <;> rw [e] at h0 <;> cases h0
  · rw [h0c] at h0; cases h0

/-- **The threads after `main`'s move to its join.** -/
theorem Thr.toJoins {Y Y' : ThreadId → Ph} {ts : Array ThreadRec} (h : Thr Y ts)
    (h0 : Y 0 = .run) (h0' : Y' 0 = .joins) (hY : ∀ u, u ≠ 0 → Y' u = Y u) : Thr Y' ts := by
  obtain ⟨ht0, ⟨-, h0c, -⟩ | ⟨hs, hn, ⟨ht1, -, h1⟩ | ⟨-, h0c, -⟩⟩⟩ := h
  · rw [h0c] at h0; cases h0
  · exact ⟨ht0, .inr ⟨hs,
      fun u hu => by
        rw [hY u (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 0 < 2) hu))]; exact hn u hu,
      .inl ⟨ht1, .inr h0', by rw [hY 1 (by decide)]; exact h1⟩⟩⟩
  · rw [h0c] at h0; cases h0

/-- **The threads after the writer's end.** -/
theorem Thr.finish {Y Y' : ThreadId → Ph} {ts : Array ThreadRec} (h : Thr Y ts) {k : Nat}
    (h1 : Y 1 = .wr k) (h1' : Y' 1 = .fin) (hY : ∀ u, u ≠ 1 → Y' u = Y u) : Thr Y' ts := by
  obtain ⟨ht0, ⟨-, -, hn⟩ | ⟨hs, hn, ⟨ht1, h0, -⟩ | ⟨-, -, hf⟩⟩⟩ := h
  · rw [hn 1 (by decide)] at h1; cases h1
  · exact ⟨ht0, .inr ⟨hs, fun u hu => by rw [hY u (Nat.ne_of_gt hu)]; exact hn u hu,
      .inl ⟨ht1, by rw [hY 0 (by decide)]; exact h0, .inl h1'⟩⟩⟩
  · rw [hf] at h1; cases h1

/-- `main` at its join: two threads, and the writer's record is not joined. -/
theorem Thr.joins_rec {Y : ThreadId → Ph} {ts : Array ThreadRec} (h : Thr Y ts)
    (h0 : Y 0 = .joins) : ts.size = 2 ∧ ts[1]? = some { spawner := 0, joined := false } := by
  obtain ⟨-, ⟨-, h0c, -⟩ | ⟨hs, -, ⟨ht1, -, -⟩ | ⟨-, h0c, -⟩⟩⟩ := h
  · rw [h0c] at h0; cases h0
  · exact ⟨hs, ht1⟩
  · rw [h0c] at h0; cases h0

/-- **The threads after `main`'s join** of the ended writer: `main` at `done`, the writer's record
joined. -/
theorem Thr.joined {Y Y' : ThreadId → Ph} {ts : Array ThreadRec} (h : Thr Y ts)
    (h0 : Y 0 = .joins) (h1 : Y 1 = .fin) (h0' : Y' 0 = .done) (hY : ∀ u, u ≠ 0 → Y' u = Y u) :
    Thr Y' (ts.set! 1 { spawner := 0, joined := true }) := by
  obtain ⟨ht0, ⟨-, h0c, -⟩ | ⟨hs, hn, ⟨-, -, -⟩ | ⟨-, h0c, -⟩⟩⟩ := h
  · rw [h0c] at h0; cases h0
  · refine ⟨?_, .inr ⟨by rw [Array.size_set!]; exact hs, fun u hu => ?_,
      .inr ⟨?_, h0', ?_⟩⟩⟩
    · simp [Array.set!_eq_setIfInBounds, ht0]
    · rw [hY u (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 0 < 2) hu))]; exact hn u hu
    · simp [Array.set!_eq_setIfInBounds, hs]
    · rw [hY 1 (by decide)]; exact h1
  · rw [h0c] at h0; cases h0

/-- `main` spawned every thread. -/
theorem spawners {Y : ThreadId → Ph} {m : Mem} (h : Thr Y m.threads) :
    ∀ r ∈ m.threads, r.spawner = 0 :=
  spawners_of_getElem fun i hi => by
    obtain ⟨h0, ⟨hs, -⟩ | ⟨hs, -, ⟨h1, -⟩ | ⟨h1, -⟩⟩⟩ := h
    · obtain rfl : i = 0 := by omega
      rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
      · rw [Array.getElem?_eq_getElem hi] at h1; rw [Option.some.inj h1]
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
      · rw [Array.getElem?_eq_getElem hi] at h1; rw [Option.some.inj h1]

/-- **After its join `main` has joined every thread it spawned** (the program's post,
`QRead`/`QPair`), in every memory with the threads' fact and `main` at `done`. -/
theorem joinedAll_done {Y : ThreadId → Ph} {m : Mem} (h : Thr Y m.threads) (h0 : Y 0 = .done) :
    joinedAll 0 m := by
  obtain ⟨ht0, ⟨-, h0c, -⟩ | ⟨hs, -, ⟨-, h0c, -⟩ | ⟨ht1, -, -⟩⟩⟩ := h
  · rw [h0c] at h0; cases h0
  · rcases h0c with e | e <;> rw [e] at h0 <;> cases h0
  · show ∀ r ∈ m.threads, r.spawner = 0 → r.joined = true
    intro r hr _
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hr
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [Array.getElem?_eq_getElem hi] at ht0; rw [Option.some.inj ht0]
    · rw [Array.getElem?_eq_getElem hi] at ht1; rw [Option.some.inj ht1]

/-! ## The ghost values -/

/-- A thread out of the lock's code, `a` at the outer mutex and `b` at the semaphore's (`out`, or
`gone` after its end): its part `r`, its place in the program `x`. `gO r x` is
`gE .out .out r x`. -/
def gE (a b : LPh) (r : Res) (x : Ph) : Gh := (⟨a, rnil, b, rnil, r⟩, { x := x })

/-- The ended writer: `gone` at both mutexes, at `fin`; its part `r`. -/
def gF (r : Res) : Gh := gE .gone .gone r .fin

/-- `n`'s value does not read `main`'s ghost value. -/
theorem cnt_upd0 (G : ThreadId → Gh) (g : Gh) :
    cnt (fun u => (upd G 0 g u).2.x) = cnt (fun u => (G u).2.x) := by
  show ((upd G 0 g 1).2.x).count = ((G 1).2.x).count
  rw [upd_ne _ _ (by decide : (1 : ThreadId) ≠ 0)]

/-! ## The spawn -/

/-- **`main`'s spawn of the writer** (`FRw.Base.spawn`): `main` copies its duplicable plain mode,
goes on at `run` with its part, and the writer starts at `wr 0` with the copy (`Proto.init`). -/
theorem inv_spawn {G : ThreadId → Gh} {m m' : Mem} {c : ThreadId} {rM : Res}
    (hp : rM.Plain) (hi : (proto wOf).inv G m) (hg : G 0 = gO rM .pre)
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (c, m'))) :
    c = 1 ∧ m'.current = 0 ∧ ∃ rP, plain rP ∧
      (proto wOf).inv (upd (upd G 1 (gO rP (.wr 0))) 0 (gO rM .run)) m' := by
  have hthr := thr_of hi
  have hx0 : (G 0).2.x = .pre := by rw [hg] <;> rfl
  obtain ⟨hsz, hnone⟩ := hthr.pre hx0
  have h1n : (G 1).2.x = .none := hnone 1 (by decide)
  have hc : c = 1 ∧ m'.threads = m.threads.push { spawner := 0, joined := false } := by
    have h := hf
    rw [fork_run] at h
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hsz, rfl⟩
  obtain ⟨rfl, hth⟩ := hc
  have hR : ∀ r, R (fun u => (G u).2.x) r →
      R (fun u => (upd (upd G 1 (gO rnil (.wr 0))) 0 (gO rM .run) u).2.x) r := fun r hr => by
    have e : cnt (fun u => (upd (upd G 1 (gO rnil (.wr 0))) 0 (gO rM .run) u).2.x) =
        cnt (fun u => (G u).2.x) := by
      show ((upd (upd G 1 (gO rnil (.wr 0))) 0 (gO rM .run) 1).2.x).count = ((G 1).2.x).count
      rw [upd_ne _ _ (by decide : (1 : ThreadId) ≠ 0), upd_self, h1n] <;> rfl
    unfold R; rw [e]; exact hr
  have hT : Thr (fun u => (upd (upd G 1 (gO rnil (.wr 0))) 0 (gO rM .run) u).2.x)
      m'.threads := by
    rw [hth]
    refine hthr.spawn hx0 ?_ ?_ fun u hu => ?_
    · show (upd (upd G 1 _) 0 _ 0).2.x = _
      rw [upd_self] <;> rfl
    · show (upd (upd G 1 _) 0 _ 1).2.x = _
      rw [upd_ne _ _ (by decide : (1 : ThreadId) ≠ 0), upd_self] <;> rfl
    · show (upd (upd G 1 _) 0 _ u).2.x = (G u).2.x
      rw [upd_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 0 < 2) hu)),
        upd_ne _ _ (Nat.ne_of_gt hu)]
  obtain ⟨-, hcur, rP, hpP, hinv⟩ := FRw.Base.spawn (W := W) (E := E) (Sz := 64) (K := .stack)
    (P := proto wOf) (G := G) (t := 0) (g₁ := gO rM .run) (g₀ := gO rnil (.wr 0))
    (fun _ _ => Iff.rfl) (fun _ _ => rfl) (by rw [hg]; exact hp) hi
    (by rw [hg]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hf
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by rw [hg] <;> rfl)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hR hT
  exact ⟨rfl, hcur, rP, hpP, hinv⟩

/-! ## A thread's change of place outside the locks -/

/-- **A thread out of every code changes its place in the program, or ends**
(`FRw.Base.inv_ghost`): it stays `out` at each mutex or goes to `gone`, and keeps its part; the
program gives that `n`'s value stays and its threads' fact at the new place. -/
theorem inv_move {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {rp : Res} {x y : Ph} {a b : LPh}
    (hi : (proto wOf).inv (upd G t (gO rp x)) m)
    (ha : a = .out ∨ a = .gone) (hb : b = .out ∨ b = .gone)
    (hcnt : cnt (fun u => (upd G t (gE a b rp y) u).2.x) =
      cnt (fun u => (upd G t (gO rp x) u).2.x))
    (hT : Thr (fun u => (upd G t (gE a b rp y) u).2.x) m.threads) :
    (proto wOf).inv (upd G t (gE a b rp y)) m := by
  have h := FRw.Base.inv_ghost (W := W) (E := E) (Sz := 64) (K := .stack) (t := t)
    (g := gE a b rp y) hi
    (by rw [upd_self] <;> rfl) (by rw [upd_self] <;> rfl) (by rw [upd_self] <;> rfl)
    (by rw [upd_self] <;> rfl) ha rfl hb rfl
    (fun r hr => by
      show R (fun u => (upd (upd G t (gO rp x)) t (gE a b rp y) u).2.x) r
      rw [upd_upd]; unfold R; rw [hcnt]; exact hr)
    (by
      show Thr (fun u => (upd (upd G t (gO rp x)) t (gE a b rp y) u).2.x) m.threads
      rw [upd_upd]; exact hT)
  rw [upd_upd] at h
  exact h

/-- **`main` moves to its join** (`Proto.joins`, which the join's stop asks for). -/
theorem inv_joins {G : ThreadId → Gh} {m : Mem} {rp : Res}
    (hi : (proto wOf).inv (upd G 0 (gO rp .run)) m) :
    (proto wOf).inv (upd G 0 (gO rp .joins)) m :=
  inv_move (a := .out) (b := .out) (y := .joins) hi (.inl rfl) (.inl rfl)
    ((cnt_upd0 G _).trans (cnt_upd0 G _).symm)
    ((thr_of hi).toJoins (by show (upd G 0 _ 0).2.x = _; rw [upd_self] <;> rfl)
      (by show (upd G 0 _ 0).2.x = _; rw [upd_self] <;> rfl)
      fun u hu => by
        show (upd G 0 _ u).2.x = (upd G 0 _ u).2.x
        rw [upd_ne _ _ hu, upd_ne _ _ hu])

/-- **The writer's end** after its two increments: `gone` at both mutexes, at `fin`, with its
part. -/
theorem inv_end {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {rp : Res}
    (hi : (proto wOf).inv (upd G t (gO rp (.wr 2))) m) : (proto wOf).inv (upd G t (gF rp)) m := by
  obtain ⟨rfl, -⟩ := wr1 hi rfl
  exact inv_move (a := .gone) (b := .gone) (y := .fin) hi (.inr rfl) (.inr rfl)
    (by rw [cnt_upd1, cnt_upd1] <;> rfl)
    ((thr_of hi).finish (k := 2) (by show (upd G 1 _ 1).2.x = _; rw [upd_self] <;> rfl)
      (by show (upd G 1 _ 1).2.x = _; rw [upd_self] <;> rfl)
      fun u hu => by
        show (upd G 1 _ u).2.x = (upd G 1 _ u).2.x
        rw [upd_ne _ _ hu, upd_ne _ _ hu])

/-- The ended writer's ghost value is the protocol's `fin`, when its part holds no read share. -/
theorem fin_gF {r : Res} (h : ∀ l, r.shared l = none) : (proto wOf).fin (gF r) :=
  ⟨rfl, rfl, rfl, h⟩

/-- **The writer's end** (`QKid`): it is `gone` at `fin` and spawned no thread. Its part holds no
read share (`hrp`: the plain mode, `FAssn.Unshared.plain`), so `main`'s join gathers none. -/
theorem kid_end {G : ThreadId → Gh} {m : Mem} {d : Nat} {rp : Res}
    (hrp : ∀ l, rp.shared l = none) (hi : (proto wOf).inv (upd G 1 (gO rp (.wr 2))) m) :
    (proto wOf).QKid 1 () G m d := by
  have hi' := inv_end hi
  exact ⟨_, hi', fin_gF hrp, fun _ => joinedAll_of_main (spawners (thr_of hi')) (by decide)⟩

/-! ## The join -/

/-- **`main`'s join of the writer** at `joins` (`FRw.Base.wp_join`): it goes on at `done`, with
the writer's part in its own (`rp'`, which holds the plain mode); every thread is joined and
every clock is below `main`'s. With `main` at `done` the threads' fact gives `n = 2`
(`Thr.done`). -/
theorem wp_join {σ : Type} {s : σ} {G : ThreadId → Gh} {m : Mem} {n : Nat} {rp : Res}
    (hp : rp.Plain) (hi : (proto wOf).inv (upd G 0 (gO rp .joins)) m)
    {Q : Unit × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k G₁ m' rp', n = k + 1 → rp'.Plain → m'.current = 0 →
      (proto wOf).inv (upd G₁ 0 (gO rp' .done)) m' → joinedAll 0 m' → m'.ClocksLe →
      Q ((), s) G₁ m' k) :
    (proto wOf).WP 0 ((joinC 1 : CM Tgt σ Unit).run s) Q G m n := by
  refine FRw.Base.wp_join (W := W) (E := E) (Sz := 64) (K := .stack) (P := proto wOf)
    (g₀ := gO rp .joins) (fun _ _ => Iff.rfl) (fun _ hf => hf.1) (fun _ hf => hf.2.1)
    (fun g hf => ?_) hi (by decide) (by decide) rfl rfl
    (fun _ G₁ m₁ hg hi₁ => ?_) (fun k G₁ m₁ m' hk hg hi₁ hfin hj hinv => ?_)
  · show g.2.w = .out
    rw [hf.2.2.1]
  · have hx0 : (G₁ 0).2.x = .joins := by rw [hg] <;> rfl
    obtain ⟨hs2, hr1⟩ := (thr_of hi₁).joins_rec hx0
    have hr1' : m₁.threads[1]? = some { spawner := 0, joined := false } := hr1
    exact ⟨by show (0 : Nat) < 1; decide, by rw [hs2]; decide, ⟨rfl, rfl, rfl⟩,
      by simp [Thread.joinValid, Mem.isGated, hr1'],
      fun _ => join_run (m := { m₁ with current := 0 }) hr1' rfl rfl⟩
  · have hx0 : (G₁ 0).2.x = .joins := by rw [hg] <;> rfl
    obtain ⟨hs2, hr1⟩ := (thr_of hi₁).joins_rec hx0
    have hr1' : m₁.threads[1]? = some { spawner := 0, joined := false } := hr1
    obtain ⟨rX, hM, -⟩ := id hi₁
    obtain ⟨rec, hrec, -, hm'⟩ := join_eq hj
    have hrec' : m₁.threads[1]? = some rec := hrec
    rw [hr1'] at hrec'
    obtain rfl := Option.some.inj hrec'
    have hc' : m'.current = 0 := by rw [hm'] <;> rfl
    have hth : m'.threads = m₁.threads.set! 1 { spawner := 0, joined := true } := by
      rw [hm'] <;> rfl
    -- `main` takes the writer's entire part, with its copy of the plain mode
    obtain ⟨rp', hrp'⟩ : ∃ rp', rp' = rsum rp ((RwProd.M (Xc := Ph) 0 16).own G₁ m₁ 1) :=
      ⟨_, rfl⟩
    have hpl' : rp'.Plain := by rw [hrp']; exact hp.rsum_left _
    have hgone : ((RwProd.M (Xc := Ph) 0 16).ph (G₁ 1)).held = false := by
      have e : (G₁ 1).1.phA = .gone := hfin.1
      show ((G₁ 1).1.phA).held = false
      rw [e] <;> rfl
    have hd0 : (upd G₁ 0 (gO rp' .done) 0).2.x = .done := by rw [upd_self] <;> rfl
    have hinv' : (proto wOf).inv (upd G₁ 0 (gO rp' .done)) m' :=
      hinv (gO rp' .done) rfl hrp' rfl rfl rfl rfl
        (fun r hr => by
          show R (fun u => (upd G₁ 0 (gO rp' .done) u).2.x) r
          unfold R; rw [cnt_upd0]; exact hr)
        (fun l => .inr (hM.own_unshared hgone hfin.2.2.2 l))
        (by
          show Thr (fun u => (upd G₁ 0 (gO rp' .done) u).2.x) m'.threads
          rw [hth]
          exact (thr_of hi₁).joined hx0 (congrArg RwX.x hfin.2.2.1) hd0 fun u hu => by
            show (upd G₁ 0 _ u).2.x = (G₁ u).2.x
            rw [upd_ne _ _ hu])
    exact h k G₁ m' rp' hk hpl' hc' hinv' (joinedAll_done (thr_of hinv') hd0)
      (Mem.ClocksLe.join2 hj (by rw [hM.w.csize, hs2]))

end RwRead
end Zig
