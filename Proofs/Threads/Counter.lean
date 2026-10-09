import ZigLean.Conc.Unroll
import Proofs.Threads.Gen
import ZigLean.Conc.Lemmas
import ZigLean.Mem.Witness

/-!
# `parallelCounter` over all schedules

`parallelCounter n` spawns 4 threads; each one does `n` atomic `fetchAdd(1, .seq_cst)` on a
shared counter; `main` joins the 4 threads and loads the counter. The result is `4 * n` under
every schedule (`parallelCounter_spec`), and no schedule gives an error (`parallelCounter_safe`):
a proof with the program logic of
`ZigLean/Conc/Logic.lean`.

**Protocol.** A thread's ghost value (`Gh`): for a `bump` thread, how many increments it did
(and whether it ended); for `main`, how many threads it spawned and which it joined. The
invariant (`Inv`):

- The counter is one atomic location whose messages are an RMW chain (each one an RMW of the one
  before, `ALoc.Chain`); message `j` holds `j`, and the number of increments of all threads is
  the number of messages after the first. So an RMW reads the newest message only
  (`readOpts_chain`): no increment is lost.
- Each message's clock is `≤` the clock of some thread; `main` joined the threads in `J`, and a
  joined thread's clock is `≤` `main`'s clock. After the 4 joins, `main`'s clock is `≥` every
  message's clock, so its load reads the newest message only (`readOpts_floor`): `4 * n`.
- Thread `k + 1`'s context (block 0, slot `k`) holds the counter's address and `n`.

**No error** (`parallelCounter_safe`). The protocol is in strict mode (`Proto.strict`), so the
same proof also shows that no run gives an error. `Ex` adds: the three stack blocks are live with
their sizes and aligned addresses; each footprint entry is a read of a context, an atomic access
to the counter, a plain write that happened before every thread, or `main`'s access to the handles
(so no access races: `noRace_b0`, `noRace_b1`, `noRace_b2`); every thread was spawned by `main`;
handle slot `k` holds thread id `k + 1` (so every join is of a thread that `main` spawned and did
not join yet).
-/

open Zig Zig.Conc Zig.Conc.Proto Threads

namespace Threads.Counter

/-- A thread's ghost value. -/
inductive Gh where
  | none
  /-- `main`: it spawned `s` threads and joined the threads in `J`. -/
  | main (s : Nat) (J : List Nat)
  /-- A `bump` thread with the context `p`: it did `c` increments; `done`: it ended. -/
  | bump (p : Ptr) (c : Nat) (done : Bool)

/-- The increments of a thread. -/
def Gh.count : Gh → Nat
  | .bump _ c _ => c
  | _ => 0

/-- The context of thread `k + 1`: slot `k` of block 0 (`ctxs`). -/
def ctxPtr (k : Nat) : Ptr := ⟨some 0, ((16 * k : Nat) : Int)⟩

/-- The counter: block 1. -/
def counterPtr : Ptr := ⟨some 1, 0⟩

/-- The increments of threads `1 … s`. -/
def total (G : ThreadId → Gh) (s : Nat) : Nat := ((List.range s).map fun k => (G (k + 1)).count).sum

variable (n : BitVec 32)

/-- Each context slot holds the counter's address and `n`. -/
def CtxOk (m : Mem) : Prop :=
  ∀ blk, m.blocks[0]? = some blk → ∀ k < 4,
    (Enc.decode (blk.bytes.extract (16 * k) (16 * k + 8)) : Result Ptr).run = some (.ok counterPtr) ∧
    (Enc.decode (blk.bytes.extract (16 * k + 8) (16 * k + 12)) : Result (BitVec 32)).run =
      some (.ok n)

/-- The counter holds `tot` increments: no atomic location yet and the value 0, or an RMW chain
of `tot + 1` messages whose newest one comes after each plain write to the counter. Each plain
write to the counter happened before every thread. -/
def CntOk (tot : Nat) (m : Mem) : Prop :=
  (∀ l ∈ m.atomics, l.block = 1 → l.off = 0 ∧ l.len = 4) ∧
  (m.atomics.findIdx? (fun l => l.block == 1 && l.off == 0) = none →
    tot = 0 ∧ (intOfBytes 32 (Proto.curBytes m 1 0 4)).run = some (.ok 0) ∧
    ∀ l ∈ m.atomics, l.block ≠ 1) ∧
  (∀ i, m.atomics.findIdx? (fun l => l.block == 1 && l.off == 0) = some i →
    (m.atomics[i]!).msgs.size = tot + 1 ∧ (m.atomics[i]!).Chain ∧
    (∀ j (h : j < (m.atomics[i]!).msgs.size),
      (intOfBytes 32 ((m.atomics[i]!).msgs[j]).bytes).run = some (.ok (BitVec.ofNat 32 j))) ∧
    Proto.ALoc.lastBytes (m.atomics[i]!) = Proto.curBytes m 1 0 4 ∧
    (∀ j (h : j < (m.atomics[i]!).msgs.size), ∃ u < m.threads.size,
      VClock.le ((m.atomics[i]!).msgs[j]).clock (m.clocks[u]!) = true) ∧
    Proto.PlainLe m 1 0 4 (m.atomics[i]!).lastClock) ∧
  (∀ e ∈ m.footprint, plainHit 1 0 4 e = true → ∀ u < m.threads.size,
    VClock.le e.clock (m.clocks[u]!) = true)

/-- The invariant (see the module doc). -/
def Inv (G : ThreadId → Gh) (m : Mem) : Prop :=
  ∃ s J, G 0 = .main s J ∧ s ≤ 4 ∧ m.threads.size = s + 1 ∧ m.clocks.size = s + 1 ∧
    (∀ u, 1 ≤ u → u ≤ s → ∃ c d, G u = .bump (ctxPtr (u - 1)) c d) ∧
    (∀ u, s < u → G u = .none) ∧
    J.Nodup ∧
    (∀ u ∈ J, 1 ≤ u ∧ u ≤ s ∧ (∃ p, G u = .bump p n.toNat true) ∧
      VClock.le (m.clocks[u]!) (m.clocks[0]!) = true ∧
      ∃ h : u < m.threads.size, (m.threads[u]).joined = true) ∧
    (∀ u (h : u < m.threads.size), (m.threads[u]).joined = true → u = 0 ∨ u ∈ J) ∧
    (∃ h : 0 < m.threads.size, (m.threads[0]).joined = true) ∧
    CtxOk n m ∧
    CntOk (total G s) m ∧
    (∀ e ∈ m.footprint, ∃ u < m.threads.size, VClock.le e.clock (m.clocks[u]!) = true)

/-! ## Facts for "no error" (strict mode) -/

/-- Each footprint entry is a read of a context (block 0), an atomic access to the counter
(block 1), a plain write to blocks 0 or 1 that happened before every thread, or `main`'s access to
the handles (block 2). -/
def FpOk (m : Mem) : Prop := ∀ e ∈ m.footprint,
  (e.block = 0 ∧ e.kind = .read) ∨ (e.block = 1 ∧ e.kind.isAtomic = true) ∨
  ((e.block = 0 ∨ e.block = 1) ∧ e.kind = .write ∧
    ∀ u < m.threads.size, VClock.le e.clock (m.clocks[u]!) = true) ∨
  (e.block = 2 ∧ VClock.le e.clock (m.clocks[0]!) = true)

/-- The handle slots `0 … s - 1` (block 2) hold the thread ids `1 … s`. -/
def HdOk (s : Nat) (m : Mem) : Prop := ∀ blk, m.blocks[2]? = some blk → ∀ k < s,
  (Enc.decode (blk.bytes.extract (8 * k) (8 * k + 8)) : Result ThreadId).run = some (.ok (k + 1))

/-- The facts of strict mode that `Inv` does not have. -/
def Ex (G : ThreadId → Gh) (m : Mem) : Prop :=
  BlkAt m 0 64 8 ∧ BlkAt m 1 4 4 ∧ BlkAt m 2 32 8 ∧ FpOk m ∧
    (∀ r ∈ m.threads, r.spawner = 0) ∧ ∃ s J, G 0 = .main s J ∧ HdOk s m

/-- The protocol, in strict mode: `Ex` (below) has the facts for "no error". -/
def proto : Proto Tgt Gh where
  inv G m := Inv n G m ∧ Ex G m
  init tgt g := (match tgt with
      | .bump p => some (.bump p 0 false)
      | _ => none) = some g
  fin g := ∃ p, g = .bump p n.toNat true
  strict := true

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok (4 * n) ∧ joinedAll 0 m

theorem inv_current {G : ThreadId → Gh} {m : Mem} {u : ThreadId} (h : Inv n G m) :
    Inv n G { m with current := u } := h

/-! ## Helpers -/

theorem getElem!_set! {α : Type} [Inhabited α] (xs : Array α) {t u : Nat} (v : α)
    (ht : t < xs.size) : (xs.set! t v)[u]! = if u = t then v else xs[u]! := by
  simp only [Array.set!_eq_setIfInBounds]
  by_cases hu : u < xs.size
  · rw [getElem!_pos _ u (by simpa using hu), getElem!_pos xs u hu, Array.getElem_setIfInBounds hu]
    by_cases h : u = t
    · subst h; simp
    · simp [Ne.symm h, h]
  · rw [getElem!_neg _ u (by simpa using hu), getElem!_neg xs u hu]
    have : u ≠ t := by omega
    simp [this]

theorem findIdx?_set! {α : Type} [Inhabited α] {xs : Array α} {q : α → Bool} {i : Nat} {v : α}
    (hi : i < xs.size) (hq : q v = q xs[i]) : (xs.set! i v).findIdx? q = xs.findIdx? q := by
  simp only [Array.set!_eq_setIfInBounds]
  cases h : xs.findIdx? q with
  | none =>
    rw [Array.findIdx?_eq_none_iff] at h ⊢
    intro x hx
    rw [Array.mem_iff_getElem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simp only [Array.size_setIfInBounds] at hj
    rw [Array.getElem_setIfInBounds hj]
    split
    · subst_vars; rw [hq]; exact h _ (Array.getElem_mem _)
    · exact h _ (Array.getElem_mem _)
  | some k =>
    rw [Array.findIdx?_eq_some_iff_getElem] at h ⊢
    obtain ⟨hk, hqk, hlt⟩ := h
    refine ⟨by simpa using hk, ?_, fun j hj => ?_⟩
    · rw [Array.getElem_setIfInBounds hk]; split
      · subst_vars; rw [hq]; exact hqk
      · exact hqk
    · rw [Array.getElem_setIfInBounds (Nat.lt_trans hj hk)]; split
      · subst_vars; rw [hq]; exact hlt j hj
      · exact hlt j hj

/-- The increments after thread `t` (`1 ≤ t ≤ s`) did one more. -/
theorem total_upd {G : ThreadId → Gh} {s t : Nat} {g : Gh} (h1 : 1 ≤ t) (h2 : t ≤ s) :
    total (Conc.upd G t g) s + (G t).count = total G s + g.count := by
  induction s with
  | zero => omega
  | succ s ih =>
    unfold total at ih ⊢
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases hs : t = s + 1
    · subst hs
      have hmap : List.map (fun k => (Conc.upd G (s + 1) g (k + 1)).count) (List.range s) =
          List.map (fun k => (G (k + 1)).count) (List.range s) :=
        List.map_congr_left fun k hk =>
          congrArg Gh.count (Conc.upd_ne _ _ (Nat.ne_of_lt (Nat.succ_lt_succ (List.mem_range.mp hk))))
      rw [hmap, Conc.upd_self]
      exact Nat.add_right_comm _ _ _
    · have ih := ih (by omega)
      rw [Conc.upd_ne _ _ (fun h => hs h.symm)]
      omega

theorem total_congr {G G' : ThreadId → Gh} {s : Nat}
    (h : ∀ u, 1 ≤ u → u ≤ s → (G' u).count = (G u).count) : total G' s = total G s := by
  unfold total
  congr 1
  apply List.map_congr_left
  intro k hk; rw [List.mem_range] at hk; exact h _ (by omega) (by omega)

theorem getElem_of_eq {α : Type} {a b : Array α} (e : a = b) {u : Nat} (h : u < a.size) :
    a[u] = b[u]'(e ▸ h) := by subst e; rfl

/-! ## The counter's location -/

/-- The lookup of `locIdx` for the counter. -/
abbrev isCnt (l : ALoc) : Bool := l.block == 1 && l.off == 0

/-- Location `li` is the counter: an RMW chain of `tot + 1` messages, message `j` holds `j`. -/
structure CntAt (tot li : Nat) (m : Mem) : Prop where
  find : m.atomics.findIdx? isCnt = some li
  only : ∀ l ∈ m.atomics, l.block = 1 → l.off = 0 ∧ l.len = 4
  size : (m.atomics[li]!).msgs.size = tot + 1
  chain : (m.atomics[li]!).Chain
  val : ∀ j (h : j < (m.atomics[li]!).msgs.size),
    (intOfBytes 32 ((m.atomics[li]!).msgs[j]).bytes).run = some (.ok (BitVec.ofNat 32 j))
  last : Proto.ALoc.lastBytes (m.atomics[li]!) = Proto.curBytes m 1 0 4
  clk : ∀ j (h : j < (m.atomics[li]!).msgs.size), ∃ u < m.threads.size,
    VClock.le ((m.atomics[li]!).msgs[j]).clock (m.clocks[u]!) = true
  plain : Proto.PlainLe m 1 0 4 (m.atomics[li]!).lastClock
  pw : ∀ e ∈ m.footprint, plainHit 1 0 4 e = true → ∀ u < m.threads.size,
    VClock.le e.clock (m.clocks[u]!) = true

theorem cntOk_of_cntAt {tot li : Nat} {m : Mem} (h : CntAt tot li m) : CntOk tot m := by
  refine ⟨h.only, fun hn => ?_, fun i hi => ?_, h.pw⟩
  · rw [h.find] at hn; cases hn
  · rw [h.find] at hi; cases hi
    exact ⟨h.size, h.chain, h.val, h.last, h.clk, h.plain⟩

theorem cntAt_len {tot li : Nat} {m : Mem} (h : CntAt tot li m) :
    li < m.atomics.size ∧ (m.atomics[li]!).block = 1 ∧ (m.atomics[li]!).off = 0 ∧
      (m.atomics[li]!).len = 4 := by
  obtain ⟨hlt, hq, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp h.find
  simp only [isCnt, Bool.and_eq_true, beq_iff_eq] at hq
  have := h.only _ (Array.getElem_mem hlt) hq.1
  rw [getElem!_pos m.atomics li hlt]
  exact ⟨hlt, hq.1, this⟩

/-- The counter's location when an atomic op makes it: the block's bytes as its first message. -/
def loc0 (m : Mem) : ALoc :=
  { block := 1, off := 0, len := 4,
    msgs := #[{ id := m.nextMsg, bytes := Proto.curBytes m 1 0 4, clock := plainClock m 1 0 4,
                relClock := #[] }] }

/-- The lookup of an atomic op on the counter (`locIdx 1 0 4`) gives the counter's location. -/
theorem cntAt_locIdx {tot li : Nat} {m m₁ : Mem} (hc : CntOk tot m)
    (h0 : 0 < m.threads.size)
    (h : ((locIdx 1 0 4).run m).run = some (.ok (li, m₁))) :
    CntAt tot li m₁ ∧ m₁.threads = m.threads ∧ m₁.clocks = m.clocks ∧ m₁.blocks = m.blocks ∧
      m₁.footprint = m.footprint ∧ m₁.current = m.current := by
  obtain ⟨honly, hnone, hsome, hpw⟩ := hc
  cases hf : m.atomics.findIdx? isCnt with
  | none =>
    obtain ⟨htot, hdec, hno⟩ := hnone hf
    obtain ⟨rfl, rfl⟩ := Proto.locIdx_new hf h
    change CntAt tot m.atomics.size
      { m with atomics := m.atomics.push (loc0 m), nextMsg := m.nextMsg + 1 } ∧ _
    have hget : (m.atomics.push (loc0 m))[m.atomics.size]! = loc0 m := by
      rw [getElem!_pos _ _ (by simp)]; simp
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpw⟩, rfl, rfl, rfl, rfl, rfl⟩
    · simp [Array.findIdx?_push, hf, isCnt, loc0]
    · intro l hl hb
      rcases Array.mem_push.mp hl with hl | rfl
      · exact absurd hb (hno l hl)
      · exact ⟨rfl, rfl⟩
    · simp only [hget]; simp [loc0, htot]
    · intro j hj; simp only [hget] at hj; simp [loc0] at hj
    · intro j hj
      simp only [hget] at hj ⊢
      simp [loc0] at hj; subst hj; simpa [loc0] using hdec
    · simp only [hget]; rfl
    · intro j hj
      simp only [hget] at hj ⊢
      simp [loc0] at hj; subst hj
      exact ⟨0, h0, Proto.plainClock_le_of fun e he hh => hpw e he hh 0 h0⟩
    · simp only [hget]
      intro e he hh
      simpa [ALoc.lastClock, loc0] using Proto.plainLe_plainClock m 1 0 4 e he hh
  | some i =>
    obtain ⟨hsz, hch, hval, hlast, hclk, hpl⟩ := hsome i hf
    have hlt := (Array.findIdx?_eq_some_iff_getElem.mp hf).1
    have hq := (Array.findIdx?_eq_some_iff_getElem.mp hf).2.1
    simp only [isCnt, Bool.and_eq_true, beq_iff_eq] at hq
    have hlen : (m.atomics[i]!).len = 4 := by
      rw [getElem!_pos m.atomics i hlt]; exact (honly _ (Array.getElem_mem hlt) hq.1).2
    obtain ⟨rfl, rfl⟩ := Proto.locIdx_found hf hlen hlast hpl h
    exact ⟨⟨hf, honly, hsz, hch, hval, hlast, hclk, hpl, hpw⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- The counter with one more RMW message `msg`, stated field by field. -/
theorem cntAt_push {tot li : Nat} {m₁ M : Mem} {msg : Msg} {blk : Block}
    (hc : CntAt tot li m₁) (hbs : 4 ≤ blk.bytes.size)
    (hat : M.atomics = m₁.atomics.set! li
      { m₁.atomics[li]! with msgs := (m₁.atomics[li]!).msgs.push msg })
    (hbl : M.blocks[1]? = some { blk with bytes := writeBytes blk.bytes 0 msg.bytes })
    (hth : M.threads = m₁.threads)
    (hcl : ∀ u : Nat, VClock.le (m₁.clocks[u]!) (M.clocks[u]!) = true)
    (hrmw : msg.rmwOf = some ((m₁.atomics[li]!).msgs[tot]!).id)
    (hval : (intOfBytes 32 msg.bytes).run = some (.ok (BitVec.ofNat 32 (tot + 1))))
    (hms : msg.bytes.size = 4)
    (hmc : ∃ u < m₁.threads.size, VClock.le msg.clock (M.clocks[u]!) = true)
    (hmp : Proto.PlainLe M 1 0 4 msg.clock)
    (hpw : ∀ e ∈ M.footprint, plainHit 1 0 4 e = true → ∀ u < M.threads.size,
      VClock.le e.clock (M.clocks[u]!) = true) :
    CntAt (tot + 1) li M := by
  obtain ⟨hlt, hblk, hoff, hlen⟩ := cntAt_len hc
  have hsz := hc.size
  have hget : M.atomics[li]! = { m₁.atomics[li]! with msgs := (m₁.atomics[li]!).msgs.push msg } := by
    rw [hat, getElem!_set! _ _ hlt, ite_eq_left rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpw⟩
  · rw [hat, findIdx?_set! hlt]
    · exact hc.find
    · simp [isCnt, getElem!_pos m₁.atomics li hlt]
  · intro l hl hb
    rw [hat, Array.set!_eq_setIfInBounds] at hl
    rcases Array.mem_or_eq_of_mem_setIfInBounds hl with hl | rfl
    · exact hc.only l hl hb
    · exact ⟨hoff, hlen⟩
  · rw [hget]; simp [hsz]
  · intro j hj
    simp only [hget, Array.size_push] at hj ⊢
    rw [Array.getElem_push, Array.getElem_push]
    split
    · rename_i h1; rw [dite_eq_left (by omega)]; exact hc.chain j h1
    · rename_i h1
      have hj' : j = tot := by omega
      subst hj'
      rw [dite_eq_left (by omega), hrmw, getElem!_pos _ _ (by omega)]
  · intro j hj
    simp only [hget, Array.size_push] at hj ⊢
    rw [Array.getElem_push]
    split
    · rename_i h1; exact hc.val j h1
    · have hj' : j = tot + 1 := by omega
      subst hj'; exact hval
  · rw [hget]
    unfold Proto.ALoc.lastBytes Proto.curBytes
    simp only [Array.back?_push, Option.map_some, Option.getD_some, hbl]
    have := extract_writeBytes blk.bytes 0 msg.bytes (by omega)
    rw [hms] at this; simpa using this.symm
  · intro j hj
    simp only [hget, Array.size_push] at hj ⊢
    rw [Array.getElem_push]
    split
    · rename_i h1
      obtain ⟨u, hu, hle⟩ := hc.clk j h1
      exact ⟨u, hth ▸ hu, VClock.le_trans hle (hcl u)⟩
    · obtain ⟨u, hu, hle⟩ := hmc
      exact ⟨u, hth ▸ hu, hle⟩
  · rw [hget]
    intro e he hh
    simpa [ALoc.lastClock] using hmp e he hh

/-- An RMW increment at the counter: it reads the newest message (the value `tot`) and adds
message `tot + 1`. -/
theorem cntAt_rmw {tot li c pos : Nat} {m₁ : Mem} {old : BitVec 32} (hc : CntAt tot li m₁)
    (hcur : m₁.current < m₁.threads.size) (hcs : m₁.clocks.size = m₁.threads.size)
    (hb1 : ∃ blk, m₁.blocks[1]? = some blk ∧ 4 ≤ blk.bytes.size)
    (hpos : (readOpts m₁ li true)[c]? = some pos)
    (hd : (intOfBytes 32 ((m₁.atomics[li]!).msgs[pos]!).bytes).run = some (.ok old)) :
    old = BitVec.ofNat 32 tot ∧
    CntAt (tot + 1) li (Proto.rmwM m₁ li pos .seqCst ((m₁.atomics[li]!).msgs[pos]!)
      (RmwOp.add.apply false old 1)) ∧
    (Proto.rmwM m₁ li pos .seqCst ((m₁.atomics[li]!).msgs[pos]!)
      (RmwOp.add.apply false old 1)).threads = m₁.threads ∧
    (Proto.rmwM m₁ li pos .seqCst ((m₁.atomics[li]!).msgs[pos]!)
      (RmwOp.add.apply false old 1)).clocks = m₁.clocks.set! m₁.current
        (VClock.merge (m₁.clocks[m₁.current]!) ((m₁.atomics[li]!).msgs[pos]!).relClock) ∧
    (Proto.rmwM m₁ li pos .seqCst ((m₁.atomics[li]!).msgs[pos]!)
      (RmwOp.add.apply false old 1)).footprint = m₁.footprint ∧
    (∀ b : Nat, b ≠ 1 → (Proto.rmwM m₁ li pos .seqCst ((m₁.atomics[li]!).msgs[pos]!)
      (RmwOp.add.apply false old 1)).blocks[b]? = m₁.blocks[b]?) ∧
    (∀ blk', m₁.blocks[1]? = some blk' → ∃ blk'', (Proto.rmwM m₁ li pos .seqCst
      ((m₁.atomics[li]!).msgs[pos]!) (RmwOp.add.apply false old 1)).blocks[1]? = some blk'' ∧
      blk''.live = blk'.live ∧ blk''.bytes.size = blk'.bytes.size ∧ blk''.kind = blk'.kind ∧
      blk''.addr = blk'.addr) ∧
    (Proto.rmwM m₁ li pos .seqCst ((m₁.atomics[li]!).msgs[pos]!)
      (RmwOp.add.apply false old 1)).current = m₁.current := by
  obtain ⟨hlt, hblk, hoff, hlen⟩ := cntAt_len hc
  have hsz := hc.size
  rw [Proto.readOpts_chain (by omega) hc.chain] at hpos
  have hcp : c = 0 ∧ pos = tot := by
    rcases c with _ | c
    · simp at hpos; omega
    · simp at hpos
  obtain ⟨rfl, rfl⟩ := hcp
  have hpos' : pos < (m₁.atomics[li]!).msgs.size := by omega
  rw [getElem!_pos (m₁.atomics[li]!).msgs pos hpos', hc.val pos hpos'] at hd
  simp only [Option.some.injEq, Except.ok.injEq] at hd
  subst hd
  refine ⟨rfl, ?_⟩
  obtain ⟨blk, hb, hbs⟩ := hb1
  generalize hrd : (m₁.atomics[li]!).msgs[pos]! = rd
  have hrd' : rd = (m₁.atomics[li]!).msgs[pos] := by rw [← hrd, getElem!_pos (m₁.atomics[li]!).msgs pos hpos']
  -- The memory after the RMW, field by field.
  have hins := insertM_last (m := Proto.acqM m₁ rd.relClock) (li := li)
    (msg := Proto.rmwMsg (Proto.acqM m₁ rd.relClock) .seqCst rd (RmwOp.add.apply false (BitVec.ofNat 32 pos) 1))
    (blk := blk) (by simpa [Proto.acqM, hblk] using hb)
  simp only [Proto.acqM] at hins
  have hM : Proto.rmwM m₁ li pos .seqCst rd (RmwOp.add.apply false (BitVec.ofNat 32 pos) 1) =
      Proto.observeM (Proto.insertM (Proto.acqM m₁ rd.relClock) li (pos + 1)
        (Proto.rmwMsg (Proto.acqM m₁ rd.relClock) .seqCst rd
          (RmwOp.add.apply false (BitVec.ofNat 32 pos) 1))) li m₁.nextMsg := rfl
  rw [hM, ← hsz]
  simp only [Proto.acqM] at hins ⊢
  rw [hins]
  have hcl : m₁.current < m₁.clocks.size := hcs ▸ hcur
  refine ⟨?_, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · rw [hsz]
    refine cntAt_push (blk := blk) hc hbs rfl ?_ rfl (fun u => ?_) ?_ ?_ ?_ ⟨m₁.current, hcur, ?_⟩
      (fun e he hh => ?_) (fun e he hh u hu => ?_)
    · simp only [Proto.observeM, hblk, hoff, Array.set!_eq_setIfInBounds]
      rw [Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp hb).1]
    · simp only [Proto.observeM]
      rw [getElem!_set! _ _ hcl]
      split
      · subst_vars; exact VClock.le_merge_left _ _
      · exact VClock.le_refl _
    · rw [hrd]; rfl
    · simp only [Proto.rmwMsg, RmwOp.apply]
      rw [intOfBytes_rmw, BitVec.ofNat_add]; rfl
    · exact LawfulEnc.size_encode (α := BitVec 32) _
    · simp only [Proto.observeM, Proto.rmwMsg]
      exact VClock.le_refl _
    · simp only [Proto.observeM, Proto.rmwMsg]
      rw [getElem!_set! _ _ hcl, ite_eq_left rfl]
      exact VClock.le_trans (hc.pw e he hh _ hcur) (VClock.le_merge_left _ _)
    · simp only [Proto.observeM]
      rw [getElem!_set! _ _ hcl]
      split
      · subst_vars; exact VClock.le_trans (hc.pw e he hh _ hcur) (VClock.le_merge_left _ _)
      · exact hc.pw e he hh u hu
  · intro b hb'
    simp only [Proto.observeM, hblk, Array.set!_eq_setIfInBounds]
    rw [Array.getElem?_setIfInBounds_ne (Ne.symm hb')]
  · intro blk' hb'
    rw [hb, Option.some.injEq] at hb'
    subst hb'
    have hb1 : 1 < m₁.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
    simp only [Proto.observeM, hblk, hoff, Array.set!_eq_setIfInBounds]
    rw [Array.getElem?_setIfInBounds_self_of_lt hb1]
    refine ⟨_, rfl, rfl, ?_, rfl, rfl⟩
    have h4 : ∀ v : BitVec 32, (padTo (intSize 32) (intBytes v)).size = 4 :=
      fun v => LawfulEnc.size_encode (α := BitVec 32) v
    exact writeBytes_size _ _ _ (by simp only [Proto.rmwMsg, h4]; omega)

/-- A read of a context by a thread does not race. -/
theorem noRace_b0 {m : Mem} {o l : Nat} (hf : FpOk m) (hcur : m.current < m.threads.size) :
    NoRace m 0 o l .read := by
  refine Proto.noRace_of fun e he hb _ _ => ?_
  rcases hf e he with ⟨_, hk⟩ | ⟨h1, _⟩ | ⟨_, _, hc⟩ | ⟨h2, _⟩
  · exact .inr (by rw [hk]; rfl)
  · rw [hb] at h1; cases h1
  · exact .inl (hc _ hcur)
  · rw [hb] at h2; cases h2

/-- An atomic access to the counter does not race. -/
theorem noRace_b1 {m : Mem} {o l : Nat} {k : AccessKind} (hf : FpOk m)
    (hcur : m.current < m.threads.size) (hk : k.isAtomic = true) : NoRace m 1 o l k := by
  refine Proto.noRace_of fun e he hb _ _ => ?_
  rcases hf e he with ⟨h0, _⟩ | ⟨_, ha⟩ | ⟨_, _, hc⟩ | ⟨h2, _⟩
  · rw [hb] at h0; cases h0
  · exact .inr (racePair_atomic ha hk)
  · exact .inl (hc _ hcur)
  · rw [hb] at h2; cases h2

/-- `main`'s access to the handles does not race. -/
theorem noRace_b2 {m : Mem} {o l : Nat} {k : AccessKind} (hf : FpOk m) (h0 : m.current = 0) :
    NoRace m 2 o l k := by
  refine Proto.noRace_of fun e he hb _ _ => ?_
  rcases hf e he with ⟨h0', _⟩ | ⟨h1, _⟩ | ⟨h01, _, _⟩ | ⟨_, hc⟩
  · rw [hb] at h0'; cases h0'
  · rw [hb] at h1; cases h1
  · rcases h01 with h | h <;> rw [hb] at h <;> cases h
  · exact .inl (h0 ▸ hc)

/-- The clocks after a `recordAccess`: the current thread's clock is bumped. -/
theorem recordAt_clock {m : Mem} {b o l : Nat} {k : AccessKind}
    (hcl : m.current < m.clocks.size) (u : Nat) :
    (m.recordAt b o l k).clocks[u]! =
      if u = m.current then VClock.bump (m.clocks[m.current]!) m.current else m.clocks[u]! := by
  simp only [Mem.recordAt]; rw [getElem!_set! _ _ hcl]

/-- `FpOk` after a step that keeps or adds entries, grows each clock, and gives a new thread a
clock above `main`'s. -/
theorem fpOk_step {m m' : Mem} (hf : FpOk m)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ (e.block = 0 ∧ e.kind = .read) ∨
      (e.block = 1 ∧ e.kind.isAtomic = true) ∨ (e.block = 2 ∧ VClock.le e.clock (m'.clocks[0]!) = true))
    (hle : ∀ u : Nat, u < m.threads.size → VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hnew : ∀ u : Nat, m.threads.size ≤ u → u < m'.threads.size →
      VClock.le (m.clocks[0]!) (m'.clocks[u]!) = true)
    (h0 : 0 < m.threads.size) : FpOk m' := by
  intro e he
  rcases hfp e he with he | h | h | h
  · rcases hf e he with h | h | ⟨hb, hk, hc⟩ | ⟨hb, hc⟩
    · exact .inl h
    · exact .inr (.inl h)
    · refine .inr (.inr (.inl ⟨hb, hk, fun u hu => ?_⟩))
      by_cases hu' : u < m.threads.size
      · exact VClock.le_trans (hc u hu') (hle u hu')
      · exact VClock.le_trans (hc 0 h0) (hnew u (by omega) hu)
    · exact .inr (.inr (.inr ⟨hb, VClock.le_trans hc (hle 0 h0)⟩))
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inr h))

/-- A `recordAccess` of a context read, an atomic access to the counter, or `main`'s access to
the handles keeps `Ex`. -/
theorem ex_recordAt {G : ThreadId → Gh} {m : Mem} {b o l : Nat} {k : AccessKind} (he : Ex G m)
    (hk : (b = 0 ∧ k = .read) ∨ (b = 1 ∧ k.isAtomic = true) ∨ (b = 2 ∧ m.current = 0))
    (hcur : m.current < m.threads.size) (hcs : m.clocks.size = m.threads.size) :
    Ex G (m.recordAt b o l k) := by
  obtain ⟨h0, h1, h2, hf, hsp, s, J, hG, hd⟩ := he
  refine ⟨h0, h1, h2, ?_, hsp, s, J, hG, hd⟩
  have hcl : m.current < m.clocks.size := hcs ▸ hcur
  refine fpOk_step hf (fun e he' => ?_) (fun u _ => ?_)
    (fun u h1 h2 => absurd h2 (Nat.not_lt.mpr h1)) (Nat.lt_of_le_of_lt (Nat.zero_le _) hcur)
  · simp only [Mem.recordAt, Array.mem_push] at he'
    rcases he' with he' | rfl
    · exact .inl he'
    · right
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, hk⟩ | ⟨rfl, hc0⟩
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr (.inl ⟨rfl, hk⟩)
      · refine .inr (.inr ⟨rfl, ?_⟩)
        rw [recordAt_clock hcl 0, ite_eq_left hc0.symm]; exact VClock.le_refl _
  · rw [recordAt_clock hcl]; split
    · subst_vars; exact VClock.le_bump _ _
    · exact VClock.le_refl _

/-! ## The invariant under a step -/

/-- A step that keeps the threads, the contexts and the counter, and only makes the current
thread's clock larger (a load, a store to another block, `recordAccess`), keeps the invariant. The
current thread has not ended. -/
theorem inv_frame {G : ThreadId → Gh} {m m' : Mem} (hi : Inv n G m)
    (hcur : ∀ p, G m.current ≠ .bump p n.toNat true)
    (hth : m'.threads = m.threads) (hcs : m'.clocks.size = m.clocks.size)
    (hle : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hne : ∀ u : Nat, u ≠ m.current → m'.clocks[u]! = m.clocks[u]!)
    (hb0 : m'.blocks[0]? = m.blocks[0]?) (hat : m'.atomics = m.atomics)
    (hb1 : Proto.curBytes m' 1 0 4 = Proto.curBytes m 1 0 4)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨
      ∃ u < m.threads.size, VClock.le e.clock (m'.clocks[u]!) = true)
    (hpf : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ plainHit 1 0 4 e = false) :
    Inv n G m' := by
  obtain ⟨s, J, hG0, hs4, hsz, hcl, hkid, hnone, hnd, hJ, hjoined, hj0, hctx, hcnt, hfp0⟩ := hi
  refine ⟨s, J, hG0, hs4, hth ▸ hsz, hcs ▸ hcl, hkid, hnone, hnd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨h1, h2, ⟨p, hp⟩, hc, hlt, hj⟩ := hJ u hu
    refine ⟨h1, h2, ⟨p, hp⟩, ?_, hth ▸ hlt, by rw [← getElem_of_eq hth.symm hlt]; exact hj⟩
    have hu' : u ≠ m.current := fun e => hcur p (e ▸ hp)
    rw [hne u hu']
    exact VClock.le_trans hc (hle 0)
  · intro u h hj; exact hjoined u (hth ▸ h) (by simpa [hth] using hj)
  · obtain ⟨h, hj⟩ := hj0; exact ⟨hth ▸ h, by simp only [hth]; exact hj⟩
  · intro blk hb; rw [hb0] at hb; exact hctx blk hb
  · obtain ⟨hc1, hc2, hc3, hc4⟩ := hcnt
    refine ⟨hat ▸ hc1, fun h => ?_, fun i h => ?_, fun e he hh u hu => ?_⟩
    · rw [hat] at h; obtain ⟨a, b, c⟩ := hc2 h; exact ⟨a, hb1 ▸ b, hat ▸ c⟩
    · rw [hat] at h ⊢
      obtain ⟨a, b, c, d, e, f⟩ := hc3 i h
      refine ⟨a, b, c, hb1 ▸ d, fun j hj => ?_, f.of_fp hpf⟩
      obtain ⟨u, hu, hl⟩ := e j hj
      exact ⟨u, hth ▸ hu, VClock.le_trans hl (hle u)⟩
    · rcases hpf e he with he | hn
      · exact VClock.le_trans (hc4 e he hh u (hth ▸ hu)) (hle u)
      · rw [hn] at hh; cases hh
  · intro e he
    rcases hfp e he with he | ⟨u, hu, hl⟩
    · obtain ⟨u, hu, hl⟩ := hfp0 e he
      exact ⟨u, hth ▸ hu, VClock.le_trans hl (hle u)⟩
    · exact ⟨u, hth ▸ hu, hl⟩

/-- `recordAccess` by a thread that has not ended keeps the invariant. -/
theorem inv_recordAt {G : ThreadId → Gh} {m : Mem} {b o len : Nat} {k : AccessKind}
    (hi : Inv n G m) (hcur : ∀ p, G m.current ≠ .bump p n.toNat true)
    (hlt : m.current < m.threads.size) (hn1 : b = 1 → k ≠ .write) :
    Inv n G (m.recordAt b o len k) := by
  have hcl : m.clocks.size = m.threads.size := by
    obtain ⟨s, J, -, -, hsz, hcl, -⟩ := hi; rw [hsz, hcl]
  have hget : ∀ u : Nat, (m.recordAt b o len k).clocks[u]! =
      if u = m.current then VClock.bump (m.clocks[m.current]!) m.current else m.clocks[u]! := by
    intro u
    simp only [Mem.recordAt, Array.set!_eq_setIfInBounds]
    by_cases hu : u < m.clocks.size
    · have hu' : u < (m.clocks.setIfInBounds m.current
          (VClock.bump (m.clocks[m.current]!) m.current)).size := by simpa using hu
      rw [getElem!_pos _ u hu', getElem!_pos m.clocks u hu, Array.getElem_setIfInBounds hu]
      by_cases h : u = m.current
      · subst h; simp
      · simp [Ne.symm h, h]
    · have hu' : ¬ u < (m.clocks.setIfInBounds m.current
          (VClock.bump (m.clocks[m.current]!) m.current)).size := by simpa using hu
      rw [getElem!_neg _ u hu', getElem!_neg m.clocks u hu]
      have : u ≠ m.current := fun h => hu (h ▸ hcl ▸ hlt)
      simp [this]
  refine inv_frame n hi hcur rfl (by simp [Mem.recordAt]) (fun u => ?_) (fun u hu => ?_) rfl rfl
    (by simp [Proto.curBytes, Mem.recordAt]) (fun e he => ?_) (fun e he => ?_)
  · rw [hget u]; split
    · subst_vars; exact VClock.le_bump _ _
    · exact VClock.le_refl _
  · rw [hget u, ite_eq_right_iff.mpr (fun h => absurd h hu)]
  · simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · refine .inr ⟨m.current, hlt, ?_⟩
      show VClock.le _ ((m.recordAt b o len k).clocks[m.current]!) = true
      rw [hget, ite_eq_left_iff.mpr (fun h => absurd rfl h)]; exact VClock.le_refl _
  · simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · exact .inr (Proto.plainHit_false_of hn1)

/-- A `bump` thread's increment keeps the invariant, with one more increment in its ghost
value. -/
theorem inv_rmw {G : ThreadId → Gh} {m m' : Mem} {t : ThreadId} {p : Ptr} {i c : Nat}
    {old : BitVec 32} (hi : Inv n G m) (he : Ex G m) (hg : G t = .bump p i false)
    (hcur : m.current = t)
    (h : ((atomicRmwAt c .add false .seqCst 4 counterPtr (1 : BitVec 32)).run m).run =
      some (.ok (old, m'))) :
    Inv n (Conc.upd G t (.bump p (i + 1) false)) m' ∧ Ex (Conc.upd G t (.bump p (i + 1) false)) m' ∧
      m'.current = m.current := by
  have hnd : ∀ q, G m.current ≠ .bump q n.toNat true := by
    intro q hq; rw [hcur, hg] at hq; cases hq
  have hiR := inv_recordAt (b := 1) (o := 0) (len := 4) (k := .atomicWrite) (hn1 := by decide) n hi hnd (by
    obtain ⟨s, J, hG0, -, hsz, -, -, hnone, -⟩ := hi
    have : t ≤ s := Nat.le_of_not_lt fun h => by rw [hnone t h] at hg; cases hg
    rw [hcur, hsz]; exact Nat.lt_succ_of_le this)
  obtain ⟨s, J, hG0, hs4, hsz, hcs, hkid, hnone, hnd', hJ, hjoined, hj0, hctx, hcnt, hfp⟩ := hi
  have ht0 : t ≠ 0 := fun e => by subst e; rw [hG0] at hg; cases hg
  have hts : t ≤ s := Nat.le_of_not_lt fun h => by rw [hnone t h] at hg; cases hg
  obtain ⟨c0, d0, hkt⟩ := hkid t (Nat.pos_of_ne_zero ht0) hts
  rw [hg] at hkt; cases hkt
  obtain ⟨b, blk, o, li, m₁, pos, ha, -, hl, hpos, hd, rfl⟩ := Proto.atomicRmwAt_ok h
  have ha' := (Proto.accessW_pure (show (m.accessW _ _ _).run = _ from congrArg ExceptT.run ha)).1
  obtain ⟨hb, hblk, -, -, hbs, -, ho⟩ := access_eq ha'
  simp only [counterPtr, Option.some.injEq] at hb ho
  subst hb; subst ho
  obtain ⟨sR, JR, hG0R, _, hszR, hcsR, _, _, _, _, _, _, _, hcntR, hfpR⟩ := hiR
  rw [hG0] at hG0R; cases hG0R
  have hl' : ((locIdx 1 0 4).run (m.recordAt 1 0 4 .atomicWrite)).run = some (.ok (li, m₁)) := hl
  obtain ⟨hcat, hth1, hcl1, hbl1, hfp1, hcu1⟩ := cntAt_locIdx hcntR (by rw [hszR]; omega) hl'
  have hcu1' : m₁.current = t := hcu1.trans hcur
  have hth1' : m₁.threads = m.threads := hth1
  have hcur1 : m₁.current < m₁.threads.size := by
    rw [hcu1', hth1', hsz]; exact Nat.lt_succ_of_le hts
  have hcs1 : m₁.clocks.size = m₁.threads.size := by rw [hcl1, hth1]; exact hcsR.trans hszR.symm
  have h4 : intSize 32 = 4 := rfl
  have hb1 : ∃ blk', m₁.blocks[1]? = some blk' ∧ 4 ≤ blk'.bytes.size :=
    ⟨blk, by rw [hbl1]; exact hblk, by rw [h4] at hbs; simp [counterPtr] at hbs; omega⟩
  obtain ⟨-, hcat', hth', hcl', hfp', hb0', hblk1', hcu'⟩ := cntAt_rmw hcat hcur1 hcs1 hb1 hpos hd
  have hclR : ∀ u : Nat, (m.recordAt 1 0 4 .atomicWrite).clocks[u]! =
      if u = t then VClock.bump (m.clocks[t]!) t else m.clocks[u]! := by
    intro u
    simp only [Mem.recordAt, hcur]
    rw [getElem!_set! _ _ (by rw [hcs]; exact Nat.lt_succ_of_le hts)]
  have hclt : m₁.current < m₁.clocks.size := hcs1 ▸ hcur1
  have hcl'' : ∀ u : Nat, u ≠ t →
      (Proto.rmwM m₁ li pos .seqCst ((m₁.atomics[li]!).msgs[pos]!)
        (RmwOp.add.apply false old 1)).clocks[u]! = m.clocks[u]! := by
    intro u hu
    rw [hcl', getElem!_set! _ _ hclt, hcu1', ite_eq_right hu, hcl1, hclR u, ite_eq_right hu]
  have hgrow : ∀ u : Nat, VClock.le ((m.recordAt 1 0 4 .atomicWrite).clocks[u]!)
      ((Proto.rmwM m₁ li pos .seqCst ((m₁.atomics[li]!).msgs[pos]!)
        (RmwOp.add.apply false old 1)).clocks[u]!) = true := by
    intro u
    rw [hcl', getElem!_set! _ _ hclt, ← hcl1]
    split
    · rename_i hu; rw [hu]; exact VClock.le_merge_left _ _
    · exact VClock.le_refl _
  refine ⟨?_, ?_, hcu'.trans hcu1⟩
  rotate_left
  · -- `Ex` after the RMW.
    have hcurm : m.current < m.threads.size := by rw [hcur, hsz]; exact Nat.lt_succ_of_le hts
    obtain ⟨B0, B1, B2, hf, hsp, s', J', hG', hd'⟩ :=
      ex_recordAt (b := 1) (o := 0) (l := 4) (k := .atomicWrite) he (.inr (.inl ⟨rfl, rfl⟩))
        hcurm (by rw [hcs, hsz])
    have hbR : ∀ b : Nat, b ≠ 1 → (Proto.rmwM m₁ li pos .seqCst ((m₁.atomics[li]!).msgs[pos]!)
        (RmwOp.add.apply false old 1)).blocks[b]? = (m.recordAt 1 0 4 .atomicWrite).blocks[b]? :=
      fun b hb => by rw [hb0' b hb, hbl1]
    have hthM : (Proto.rmwM m₁ li pos .seqCst ((m₁.atomics[li]!).msgs[pos]!)
        (RmwOp.add.apply false old 1)).threads = (m.recordAt 1 0 4 .atomicWrite).threads := by
      rw [hth', hth1]
    refine ⟨?_, ?_, ?_, ?_, ?_, s', J', by rw [Conc.upd_ne _ _ (Ne.symm ht0)]; exact hG', ?_⟩
    · obtain ⟨blk0, hb, r⟩ := B0; exact ⟨blk0, by rw [hbR 0 (by omega)]; exact hb, r⟩
    · obtain ⟨blk1, hb, hl, hs, hk, ha⟩ := B1
      obtain ⟨blk'', hb'', hl', hs', hk', ha'⟩ := hblk1' blk1 (by rw [hbl1]; exact hb)
      exact ⟨blk'', hb'', hl' ▸ hl, hs' ▸ hs, hk' ▸ hk, ha' ▸ ha⟩
    · obtain ⟨blk2, hb, r⟩ := B2; exact ⟨blk2, by rw [hbR 2 (by omega)]; exact hb, r⟩
    · refine fpOk_step hf (fun e he' => .inl (by rw [hfp', hfp1] at he'; exact he'))
        (fun u _ => hgrow u) (fun u h1 h2 => absurd h2 (by rw [hthM]; exact Nat.not_lt.mpr h1))
        (by rw [hszR]; exact Nat.succ_pos _)
    · intro r hr; rw [hthM] at hr; exact hsp r hr
    · intro blk hb; rw [hbR 2 (by omega)] at hb; exact hd' blk hb
  have htot : total (Conc.upd G t (.bump (ctxPtr (t - 1)) (i + 1) false)) s = total G s + 1 := by
    have := total_upd (G := G) (g := .bump (ctxPtr (t - 1)) (i + 1) false)
      (Nat.pos_of_ne_zero ht0) hts
    rw [hg] at this; simp only [Gh.count] at this; omega
  refine ⟨s, J, by rw [Conc.upd_ne _ _ (Ne.symm ht0)]; exact hG0, hs4, ?_, ?_, ?_, ?_, hnd', ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [hth', hth1']; exact hsz
  · rw [hcl']; simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    rw [hcl1]; exact hcsR
  · intro u h1 h2
    by_cases hu : u = t
    · subst hu; exact ⟨i + 1, false, Conc.upd_self _ _ _⟩
    · rw [Conc.upd_ne _ _ hu]; exact hkid u h1 h2
  · intro u hu
    rw [Conc.upd_ne _ _ (Nat.ne_of_gt (Nat.lt_of_le_of_lt hts hu))]; exact hnone u hu
  · intro u hu
    obtain ⟨h1, h2, ⟨q, hq⟩, hc, hlt, hj⟩ := hJ u hu
    have hut : u ≠ t := fun e => by subst e; rw [hg] at hq; cases hq
    have e := (hth'.trans hth1').symm
    refine ⟨h1, h2, ⟨q, by rw [Conc.upd_ne _ _ hut]; exact hq⟩, ?_, e ▸ hlt,
      by rw [← getElem_of_eq e hlt]; exact hj⟩
    rw [hcl'' u hut, hcl'' 0 (Ne.symm ht0)]; exact hc
  · intro u h hj
    have e := hth'.trans hth1'
    exact hjoined u (e ▸ h) (by rw [← getElem_of_eq e h]; exact hj)
  · obtain ⟨h, hj⟩ := hj0
    have e := (hth'.trans hth1').symm
    exact ⟨e ▸ h, by rw [← getElem_of_eq e h]; exact hj⟩
  · intro blk' hb'
    rw [hb0' 0 (by omega), hbl1] at hb'
    exact hctx blk' hb'
  · rw [htot]; exact cntOk_of_cntAt hcat'
  · intro e he
    rw [hfp', hfp1] at he
    obtain ⟨u, hu, hle⟩ := hfpR e he
    exact ⟨u, by rw [hth', hth1']; exact hu, VClock.le_trans hle (hgrow u)⟩

/-- Two states of the invariant with the same `main` ghost value have the same threads. -/
theorem inv_size {G G' : ThreadId → Gh} {m m' : Mem} (hi : Inv n G m) (hi' : Inv n G' m')
    (h0 : G' 0 = G 0) : m'.threads.size = m.threads.size := by
  obtain ⟨s, J, hG0, -, hsz, -⟩ := hi
  obtain ⟨s', J', hG0', -, hsz', -⟩ := hi'
  rw [h0, hG0] at hG0'; cases hG0'
  rw [hsz, hsz']

/-- A thread with a `bump` ghost value is thread `k + 1` with context `ctxPtr k`, `k < 4`. -/
theorem inv_kid {G : ThreadId → Gh} {m : Mem} {u : ThreadId} {p : Ptr} {c : Nat} {d : Bool}
    (hi : Inv n G m) (hg : G u = .bump p c d) :
    1 ≤ u ∧ u < m.threads.size ∧ u - 1 < 4 ∧ p = ctxPtr (u - 1) := by
  obtain ⟨s, J, hG0, hs4, hsz, -, hkid, hnone, -⟩ := hi
  have hu0 : u ≠ 0 := fun e => by subst e; rw [hG0] at hg; cases hg
  have hus : u ≤ s := Nat.le_of_not_lt fun h => by rw [hnone u h] at hg; cases hg
  obtain ⟨c', d', hk⟩ := hkid u (Nat.pos_of_ne_zero hu0) hus
  rw [hg] at hk; cases hk
  exact ⟨Nat.pos_of_ne_zero hu0, by rw [hsz]; exact Nat.lt_succ_of_le hus,
    Nat.sub_one_lt_of_le (Nat.pos_of_ne_zero hu0) (Nat.le_trans hus hs4), rfl⟩

theorem ctx_off (k j : Nat) : ((ctxPtr k).add (j : Int)).off.toNat = 16 * k + j := by
  simp only [ctxPtr, Ptr.add]; omega

/-- `bump` loads `n` from its context. -/
theorem load_n {G : ThreadId → Gh} {m m₁ : Mem} {u : ThreadId} {p : Ptr} {c : Nat} {d : Bool}
    {a : BitVec 32} (hi : Inv n G m) (hg : G u = .bump p c d)
    (h : ((load (BitVec 32) 4 (p.add 8)).run m).run = some (.ok (a, m₁))) :
    a = n ∧ ∃ o, m₁ = m.recordAt 0 o 4 .read := by
  obtain ⟨-, -, hk4, rfl⟩ := inv_kid n hi hg
  obtain ⟨b, blk, o, ha, -, hd, rfl⟩ := Proto.load_ok h
  obtain ⟨hb, hblk, -, -, -, -, ho⟩ := access_eq ha
  simp only [ctxPtr, Ptr.add, Option.some.injEq] at hb
  subst hb
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hctx, _⟩ := hi
  have hv := (hctx blk hblk (u - 1) hk4).2
  have ho' : o = 16 * (u - 1) + 8 := by rw [ho]; exact ctx_off (u - 1) 8
  subst ho'
  rw [show 16 * (u - 1) + 8 + Enc.size (BitVec 32) = 16 * (u - 1) + 12 from rfl,
    decodeLoad_run_of_decode hv] at hd
  simp only [Option.some.injEq, Except.ok.injEq] at hd
  exact ⟨hd.symm, _, rfl⟩

/-- `bump` loads the counter's address from its context. -/
theorem load_cnt {G : ThreadId → Gh} {m m₁ : Mem} {u : ThreadId} {p : Ptr} {c : Nat} {d : Bool}
    {a : Ptr} (hi : Inv n G m) (hg : G u = .bump p c d)
    (h : ((load Ptr 8 (p.add 0)).run m).run = some (.ok (a, m₁))) :
    a = counterPtr ∧ ∃ o, m₁ = m.recordAt 0 o 8 .read := by
  obtain ⟨-, -, hk4, rfl⟩ := inv_kid n hi hg
  obtain ⟨b, blk, o, ha, -, hd, rfl⟩ := Proto.load_ok h
  obtain ⟨hb, hblk, -, -, -, -, ho⟩ := access_eq ha
  simp only [ctxPtr, Ptr.add, Option.some.injEq] at hb
  subst hb
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hctx, _⟩ := hi
  have hv := (hctx blk hblk (u - 1) hk4).1
  have ho' : o = 16 * (u - 1) + 0 := by rw [ho]; exact ctx_off (u - 1) 0
  subst ho'
  rw [show 16 * (u - 1) + 0 + Enc.size Ptr = 16 * (u - 1) + 8 from rfl, Nat.add_zero,
    decodeLoad_run_of_decode hv] at hd
  simp only [Option.some.injEq, Except.ok.injEq] at hd
  exact ⟨hd.symm, _, rfl⟩

/-- A kid's load from its context gives no error. -/
theorem ctx_load_noErr {T : Type} [Enc T] {G : ThreadId → Gh} {m : Mem} {u : ThreadId} {p : Ptr}
    {c : Nat} {d : Bool} {a j : Nat} {v : T} (hi : Inv n G m) (he : Ex G m)
    (hg : G u = .bump p c d) (hcur : m.current = u) (hj : j + Enc.size T ≤ 16)
    (hal : ∀ A k : Nat, A % 8 = 0 → (A + (16 * k + j)) % a = 0)
    (hv : ∀ blk, m.blocks[0]? = some blk →
      Enc.decode (blk.bytes.extract (16 * (u - 1) + j) (16 * (u - 1) + j + Enc.size T)) = pure v)
    (e : Error) : ((load T a (p.add j)).run m).run ≠ some (.error e) := by
  obtain ⟨-, hlt, hk4, rfl⟩ := inv_kid n hi hg
  obtain ⟨⟨blk, hb, hl, hs, -, hadd⟩, -, -, hf, -⟩ := he
  have hoff : ((ctxPtr (u - 1)).add j).off = ((16 * (u - 1) + j : Nat) : Int) := by
    simp [ctxPtr, Ptr.add]
  have hacc : m.access ((ctxPtr (u - 1)).add j) (Enc.size T) a =
      pure (0, blk, 16 * (u - 1) + j) := by
    have := access_of (m := m) (p := (ctxPtr (u - 1)).add j) (n := Enc.size T) (a := a)
      (by simp [ctxPtr, Ptr.add]) hb hl (by rw [hoff]; omega)
      (by rw [hoff, hs]; unfold ThreadId at *; omega)
      (by rw [ctx_off]; exact hal _ _ hadd)
    rwa [ctx_off] at this
  exact MemM.noErr_of_run (load_run hacc (hv blk hb) (noRace_b0 hf (by rw [hcur]; exact hlt))) e

/-- A kid's load of `n` gives no error. -/
theorem load_n_noErr {G : ThreadId → Gh} {m : Mem} {u : ThreadId} {p : Ptr} {c : Nat} {d : Bool}
    (hi : Inv n G m) (he : Ex G m) (hg : G u = .bump p c d) (hcur : m.current = u) (e : Error) :
    ((load (BitVec 32) 4 (p.add 8)).run m).run ≠ some (.error e) := by
  have hk4 := (inv_kid n hi hg).2.2.1
  have hctx : CtxOk n m := by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hi; exact h
  exact ctx_load_noErr (v := n) (j := 8) n hi he hg hcur (by decide) (fun A k h => by omega)
    (fun blk hb => (hctx blk hb (u - 1) hk4).2) e

/-- A kid's load of the counter's address gives no error. -/
theorem load_cnt_noErr {G : ThreadId → Gh} {m : Mem} {u : ThreadId} {p : Ptr} {c : Nat}
    {d : Bool} (hi : Inv n G m) (he : Ex G m) (hg : G u = .bump p c d) (hcur : m.current = u)
    (e : Error) : ((load Ptr 8 (p.add 0)).run m).run ≠ some (.error e) := by
  have hk4 := (inv_kid n hi hg).2.2.1
  have hctx : CtxOk n m := by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hi; exact h
  refine ctx_load_noErr (v := counterPtr) (j := 0) n hi he hg hcur (by decide)
    (fun A k h => by omega) (fun blk hb => ?_) e
  exact (hctx blk hb (u - 1) hk4).1

/-- The location of an atomic op at the counter is the counter (`cntAt_locIdx`), after the
`recordAccess` of the op. -/
theorem cnt_loc {G : ThreadId → Gh} {m m₁ : Mem} {li : Nat} {k : AccessKind}
    (hi : Inv n G m) (hnd : ∀ q, G m.current ≠ .bump q n.toNat true)
    (hcur : m.current < m.threads.size) (hk : k.isAtomic = true)
    (hl : ((locIdx 1 0 4).run (m.recordAt 1 0 4 k)).run = some (.ok (li, m₁))) :
    ∃ tot, CntAt tot li m₁ := by
  obtain ⟨_, _, _, _, hszR, _, _, _, _, _, _, _, _, hcntR, hfpR⟩ := inv_recordAt n hi hnd hcur
    (b := 1) (o := 0) (len := 4) (k := k) (hn1 := fun _ h => by subst h; cases hk)
  exact ⟨_, (cntAt_locIdx hcntR (by rw [hszR]; exact Nat.succ_pos _) hl).1⟩

/-- The preparation of an RMW at the counter reads the newest message only. -/
theorem cnt_prep {G : ThreadId → Gh} {m m₁ : Mem} {li : Nat} {opts : Array Nat}
    (hi : Inv n G m) (hnd : ∀ q, G m.current ≠ .bump q n.toNat true)
    (hcur : m.current < m.threads.size)
    (h : ((loadPrep 32 .seqCst 4 counterPtr true).run m).run = some (.ok ((li, opts), m₁))) :
    ∃ tot, CntAt tot li m₁ ∧ opts = #[(m₁.atomics[li]!).msgs.size - 1] := by
  obtain ⟨b, blk, o, ha, -, hl, rfl⟩ := Proto.loadPrep_ok h
  simp only [↓reduceIte] at ha hl
  have ha' := (Proto.accessW_pure (show (m.accessW _ _ _).run = _ from congrArg ExceptT.run ha)).1
  obtain ⟨hb, -, -, -, -, -, ho⟩ := access_eq ha'
  simp only [counterPtr, Option.some.injEq] at hb ho
  subst hb; subst ho
  obtain ⟨tot, hc⟩ := cnt_loc n hi hnd hcur rfl hl
  exact ⟨tot, hc, Proto.readOpts_chain (by rw [hc.size]; exact Nat.succ_pos _) hc.chain⟩

/-- A kid's RMW at the counter gives no error: the access, the race check and the location are
fine, and the oracle's choice is the only option. -/
theorem rmw_noErr {G : ThreadId → Gh} {m : Mem} {c : Nat} (hi : Inv n G m) (he : Ex G m)
    (hnd : ∀ q, G m.current ≠ .bump q n.toNat true) (hcur : m.current < m.threads.size)
    (hc : c < rmwCount 32 .seqCst 4 counterPtr m ∨ rmwCount 32 .seqCst 4 counterPtr m = 0 ∧ c = 0)
    (e : Error) :
    ((atomicRmwAt c .add false .seqCst 4 counterPtr (1 : BitVec 32)).run m).run ≠
      some (.error e) := by
  obtain ⟨-, ⟨blk, hb, hl, hs, hk, hadd⟩, -, hf, -⟩ := he
  have hacc : m.access counterPtr (intSize 32) 4 = pure (1, blk, 0) :=
    access_of (by rfl) hb hl (by simp [counterPtr]) (by simp [counterPtr, hs]; decide)
      (by simp [counterPtr]; omega)
  have haccW : m.accessW counterPtr (intSize 32) 4 = pure (1, blk, 0) := by
    simp [Mem.accessW, hacc, hk, pure, ExceptT.pure, ExceptT.mk, bind, ExceptT.bind,
      ExceptT.bindCont]
  have hcnt1 : rmwCount 32 .seqCst 4 counterPtr m ≤ 1 := by
    refine Proto.optCount_le_one fun a m' h => ?_
    obtain ⟨⟨li, opts⟩, hr, rfl⟩ := MemM.map_ok h
    obtain ⟨_, -, rfl⟩ := cnt_prep n hi hnd hcur hr
    simp
  have hc0 : c = 0 := by omega
  subst hc0
  refine Proto.atomicRmwAt_noErr ?_ (fun li opts m₁ h => ?_) e
  · refine Proto.loadPrep_noErr (b := 1) (o := 0) (blk := blk) (by simpa using haccW)
      (noRace_b1 hf hcur rfl) ?_
    intro e' h'
    obtain ⟨_, _, _, _, hszR, _, _, _, _, _, _, _, _, hcntR, hfpR⟩ :=
      inv_recordAt n hi hnd hcur (b := 1) (o := 0) (len := 4) (k := .atomicWrite) (hn1 := by decide)
    refine Proto.locIdx_noErr (fun i hi' => ?_) (fun hn => (hcntR.2.1 hn).2.2) e' h'
    have hlt := (Array.findIdx?_eq_some_iff_getElem.mp hi').1
    have hq := (Array.findIdx?_eq_some_iff_getElem.mp hi').2.1
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    rw [getElem!_pos (m.recordAt 1 0 4 .atomicWrite).atomics i hlt]
    exact (hcntR.1 _ (Array.getElem_mem hlt) hq.1).2
  · obtain ⟨tot, hct, rfl⟩ := cnt_prep n hi hnd hcur h
    have hsz := hct.size
    have hp : (m₁.atomics[li]!).msgs.size - 1 < (m₁.atomics[li]!).msgs.size := by omega
    refine ⟨_, rfl, BitVec.ofNat 32 ((m₁.atomics[li]!).msgs.size - 1), ?_⟩
    rw [getElem!_pos (m₁.atomics[li]!).msgs _ hp]
    exact hct.val _ hp

/-- A `bump` thread that ends: its ghost value gets `done`. -/
theorem inv_finish {G : ThreadId → Gh} {m : Mem} {u : ThreadId} {p : Ptr} {c : Nat}
    (hi : Inv n (Conc.upd G u (.bump p c false)) m) :
    Inv n (Conc.upd G u (.bump p c true)) m := by
  obtain ⟨hu1, -, -, hp⟩ := inv_kid n hi (Conc.upd_self _ _ _)
  have hu0 : (0 : Nat) ≠ u := Nat.ne_of_lt hu1
  obtain ⟨s, J, hG0, hs4, hsz, hcs, hkid, hnone, hnd, hJ, hjoined, hj0, hctx, hcnt, hfp⟩ := hi
  rw [Conc.upd_ne _ _ hu0] at hG0
  have hus : u ≤ s := Nat.le_of_not_lt fun h => by
    have := hnone u h; rw [Conc.upd_self] at this; cases this
  have htot : total (Conc.upd G u (.bump p c true)) s = total (Conc.upd G u (.bump p c false)) s :=
    total_congr fun v _ _ => by
      by_cases hv : v = u
      · subst hv; simp [Conc.upd_self, Gh.count]
      · rw [Conc.upd_ne _ _ hv, Conc.upd_ne _ _ hv]
  refine ⟨s, J, by rw [Conc.upd_ne _ _ hu0]; exact hG0, hs4, hsz, hcs, ?_, ?_, hnd, ?_, hjoined,
    hj0, hctx, htot ▸ hcnt, hfp⟩
  · intro v h1 h2
    by_cases hv : v = u
    · subst hv; rw [Conc.upd_self]; exact ⟨c, true, hp ▸ rfl⟩
    · rw [Conc.upd_ne _ _ hv]; have := hkid v h1 h2; rwa [Conc.upd_ne _ _ hv] at this
  · intro v hv
    have hvu : v ≠ u := fun e => absurd (e ▸ hv) (Nat.not_lt.mpr hus)
    rw [Conc.upd_ne _ _ hvu]; have := hnone v hv; rwa [Conc.upd_ne _ _ hvu] at this
  · intro v hv
    obtain ⟨h1, h2, ⟨q, hq⟩, hc, hj⟩ := hJ v hv
    have hvu : v ≠ u := fun e => by
      subst e; rw [Conc.upd_self] at hq; injection hq with _ _ h3; cases h3
    rw [Conc.upd_ne _ _ hvu] at hq
    exact ⟨h1, h2, ⟨q, by rw [Conc.upd_ne _ _ hvu]; exact hq⟩, hc, hj⟩

/-- `bump`'s loop invariant: at the loop head the thread did `i` increments. -/
def bumpInv (u : ThreadId) (p : Ptr) (s : bumpLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) :
    Prop :=
  m.current = u ∧ s.i.toNat ≤ n.toNat ∧ Inv n (Conc.upd G u (.bump p s.i.toNat false)) m ∧
    Ex (Conc.upd G u (.bump p s.i.toNat false)) m

/-- `bump`'s loop ends after `n` increments. -/
def bumpPost (u : ThreadId) (p : Ptr) (r : bumpExit × bumpLocals) (G : ThreadId → Gh) (m : Mem)
    (_ : Nat) : Prop :=
  r.1 = .br3 ∧ m.current = u ∧ Inv n (Conc.upd G u (.bump p n.toNat false)) m ∧
    Ex (Conc.upd G u (.bump p n.toNat false)) m

/-- One repeat of `bump`'s loop: one increment and a stop, or the end. -/
theorem bump_body (p : Ptr) (u : ThreadId) (s : bumpLocals) (G : ThreadId → Gh) (m : Mem)
    (d : Nat) (h : bumpInv n u p s G m d) :
    (proto n).WP u ((bump.loop4 p).run s) (fun r G' m' d' =>
      if bump.again4 r.1 then bumpInv n u p r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : bumpLocals) => 0) s)
      else bumpPost n u p r G' m' d') G m d := by
  obtain ⟨hcur, hle, hi, he⟩ := h
  have hg : (Conc.upd G u (.bump p s.i.toNat false)) u = .bump p s.i.toNat false :=
    Conc.upd_self _ _ _
  have hnd : ∀ q, (Conc.upd G u (.bump p s.i.toNat false)) m.current ≠ .bump q n.toNat true := by
    rw [hcur, hg]; intro q h; injection h with _ _ h3; cases h3
  have hlt₀ : m.current < m.threads.size := by rw [hcur]; exact (inv_kid n hi hg).2.1
  have hcs₀ : m.clocks.size = m.threads.size := by
    obtain ⟨_, _, _, _, h1, h2, _⟩ := hi; rw [h1, h2]
  unfold bump.loop4
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  refine WP.bind (WP.liftM (fun e h => (load_n_noErr n hi he hg hcur e h).elim)
    fun a m₁ hl => ?_)
  obtain ⟨ha, o, rfl⟩ := load_n n hi hg hl
  subst a
  have hi₁ := inv_recordAt (b := 0) (o := o) (len := 4) (k := .read) n hi hnd hlt₀ (by decide)
  have he₁ := ex_recordAt (b := 0) (o := o) (l := 4) (k := .read) he (.inl ⟨rfl, rfl⟩) hlt₀ hcs₀
  refine ⟨rfl, ?_⟩
  simp only
  split
  · rename_i hlt
    simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
    refine WP.bind (WP.liftM (fun e h => (load_cnt_noErr n hi₁ he₁ hg hcur e h).elim)
      fun a m₂ hl₂ => ?_)
    obtain ⟨ha, o₂, rfl⟩ := load_cnt n hi₁ hg hl₂
    subst a
    have hi₂ := inv_recordAt (b := 0) (o := o₂) (len := 8) (k := .read) n hi₁ hnd hlt₀ (by decide)
    have he₂ := ex_recordAt (b := 0) (o := o₂) (l := 8) (k := .read) he₁ (.inl ⟨rfl, rfl⟩) hlt₀
      (by simp [Mem.recordAt, hcs₀])
    refine ⟨rfl, ?_⟩
    simp only [atomicRmwC, StateT.run_bind, bind_assoc]
    refine WP.bind (WP.pickC fun k hk => ⟨.bump p s.i.toNat false, ⟨hi₂, he₂⟩,
      fun G₁ m₃ hg₁ hie₃ c hcr => ?_⟩)
    obtain ⟨hi₃, he₃⟩ := hie₃
    have hi₃' := inv_current (u := u) n hi₃
    have he₃' : Ex G₁ { m₃ with current := u } := he₃
    have hnd₃ : ∀ q, G₁ ({ m₃ with current := u } : Mem).current ≠ .bump q n.toNat true := by
      show ∀ q, G₁ u ≠ _; rw [hg₁]; intro q h; injection h with _ _ h3; cases h3
    have hlt₃ : ({ m₃ with current := u } : Mem).current < ({ m₃ with current := u } : Mem).threads.size :=
      (inv_kid n hi₃ hg₁).2.1
    refine WP.bind (WP.callMC (fun e h => by
      rw [ptr_add_zero] at h; exact (rmw_noErr n hi₃' he₃' hnd₃ hlt₃ hcr e h).elim)
      fun old m₄ hr => ?_)
    rw [ptr_add_zero] at hr
    obtain ⟨hi₄, he₄, hc₄⟩ := inv_rmw n hi₃' he₃' hg₁ rfl hr
    refine ⟨inv_size n hi₃' hi₄ (Conc.upd_ne _ _ (Nat.ne_of_lt (inv_kid n hi₃ hg₁).1)), ?_⟩
    have hlt' : s.i.toNat < n.toNat := by simpa [lt, BitVec.ult] using hlt
    refine WP.bind (WP.callRC (fun e h => (add_one_noErr (a := s.i) (by have := n.isLt; omega) e h).elim)
      fun i' hadd => ?_)
    have hin : i'.toNat = s.i.toNat + 1 := add_one_ok hadd (by have := n.isLt; omega)
    simp only [StateT.run_modify, StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [bump.again4, ↓reduceIte]
    refine ⟨⟨by rw [hc₄], by simp only; omega, by simp only; rw [hin]; exact hi₄,
      by simp only; rw [hin]; exact he₄⟩, .inl ?_⟩
    omega
  · rename_i hge
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    have hge' : ¬ s.i.toNat < n.toNat := by simpa [lt, BitVec.ult] using hge
    have heq : s.i.toNat = n.toNat := by omega
    simp only [bump.again4, Bool.false_eq_true, ↓reduceIte]
    exact ⟨rfl, hcur, heq ▸ hi₁, heq ▸ he₁⟩

/-! ## `main`'s steps -/

theorem fork_eq {m m' : Mem} {c : ThreadId}
    (h : (Thread.fork.run m).run = some (.ok (c, m'))) :
    c = m.threads.size ∧ m' = { m with
      clocks := (m.clocks.set! m.current (VClock.bump (m.clocks[m.current]!) m.current)).push
        (VClock.bump (m.clocks[m.current]!) m.current),
      threads := m.threads.push { spawner := m.current, joined := false } } := by
  simp [Thread.fork, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, set, StateT.set, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run,
    ExceptT.bind, ExceptT.bindCont, Option.bind] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem total_succ (G : ThreadId → Gh) (s : Nat) :
    total G (s + 1) = total G s + (G (s + 1)).count := by
  unfold total; rw [List.range_succ]; simp

/-- The counter's facts survive a step that keeps its location and bytes, adds threads, and makes
clocks larger. -/
theorem cntOk_mono {tot : Nat} {m m' : Mem} (h : CntOk tot m) (hat : m'.atomics = m.atomics)
    (hb : Proto.curBytes m' 1 0 4 = Proto.curBytes m 1 0 4)
    (hth : m.threads.size ≤ m'.threads.size)
    (hle : ∀ u, u < m.threads.size → VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hpf : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ plainHit 1 0 4 e = false)
    (hnew : ∀ u, m.threads.size ≤ u → u < m'.threads.size →
      VClock.le (m.clocks[0]!) (m'.clocks[u]!) = true)
    (h0 : 0 < m.threads.size) :
    CntOk tot m' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨hat ▸ h1, fun hn => ?_, fun i hi => ?_, fun e he hh u hu => ?_⟩
  · rw [hat] at hn; obtain ⟨a, b, c⟩ := h2 hn; exact ⟨a, hb ▸ b, hat ▸ c⟩
  · rw [hat] at hi ⊢
    obtain ⟨a, b, c, d, e, f⟩ := h3 i hi
    refine ⟨a, b, c, hb ▸ d, fun j hj => ?_, f.of_fp hpf⟩
    obtain ⟨u, hu, hl⟩ := e j hj
    exact ⟨u, Nat.lt_of_lt_of_le hu hth, VClock.le_trans hl (hle u hu)⟩
  · rcases hpf e he with he | hn
    · by_cases hu' : u < m.threads.size
      · exact VClock.le_trans (h4 e he hh u hu') (hle u hu')
      · exact VClock.le_trans (h4 e he hh 0 h0) (hnew u (by omega) hu)
    · rw [hn] at hh; cases hh

/-- A spawn of thread `k + 1` and the store of its handle keep the invariant; `main`'s ghost
value counts one more spawn. -/
theorem inv_spawn {G : ThreadId → Gh} {m m₂ m₃ : Mem} {k : Nat} {child : ThreadId} {q : Ptr}
    (hi : Inv n G m) (hG0 : G 0 = .main k []) (hk : k < 4)
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (child, m₂)))
    (hs : ((store 8 q child).run m₂).run = some (.ok ((), m₃))) (hq : q.block = some 2) :
    child = k + 1 ∧ m₃.current = 0 ∧
      Inv n (Conc.upd (Conc.upd G child (.bump (ctxPtr k) 0 false)) 0 (.main (k + 1) [])) m₃ := by
  obtain ⟨s, J, hG0', hs4, hsz, hcs, hkid, hnone, hnd, hJ, hjoined, hj0, hctx, hcnt, hfp⟩ := hi
  rw [hG0] at hG0'; cases hG0'
  obtain ⟨hc, hm₂⟩ := fork_eq hf
  obtain ⟨b, blk, o, ha, -, hm₃⟩ := Proto.store_ok hs
  obtain ⟨hb, -, -, -, -, -, -⟩ := access_eq ha
  rw [hq, Option.some.injEq] at hb
  subst hb
  have hcl0 : 0 < m.clocks.size := by rw [hcs]; omega
  -- The memory after the fork (`m₂`) and after the store of the handle (`m₃`), field by field.
  have h2c : m₂.clocks = (m.clocks.set! 0 (VClock.bump (m.clocks[0]!) 0)).push
      (VClock.bump (m.clocks[0]!) 0) := by rw [hm₂]
  have h2t : m₂.threads = m.threads.push { spawner := 0, joined := false } := by rw [hm₂]
  have h2cur : m₂.current = 0 := by rw [hm₂]
  have h3c : m₃.clocks = m₂.clocks.set! 0 (VClock.bump (m₂.clocks[0]!) 0) := by
    rw [hm₃, ← h2cur]; rfl
  have h3t : m₃.threads = m₂.threads := by rw [hm₃]; rfl
  have h3cur : m₃.current = 0 := by rw [hm₃, ← h2cur]; rfl
  have h3a : m₃.atomics = m.atomics := by rw [hm₃, hm₂]; rfl
  have h3b0 : m₃.blocks[0]? = m.blocks[0]? := by
    rw [hm₃, hm₂]; simp [Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds]
  have h3b1 : Proto.curBytes m₃ 1 0 4 = Proto.curBytes m 1 0 4 := by
    rw [hm₃, hm₂]; simp [Mem.write, Mem.recordAt, Proto.curBytes, Array.set!_eq_setIfInBounds]
  have h3f : ∀ e ∈ m₃.footprint, e ∈ m.footprint ∨ e.clock = m₃.clocks[0]! := by
    intro e he
    rw [hm₃] at he
    simp only [Mem.write, Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · left; rw [hm₂] at he; exact he
    · right
      rw [h3c, getElem!_set! _ _ (by rw [h2c]; simp <;> omega), ite_eq_left rfl, h2cur]
  have h2c0 : m₂.clocks[0]! = VClock.bump (m.clocks[0]!) 0 := by
    rw [h2c, getElem!_push, ite_eq_left (by simp; omega), getElem!_set! _ _ hcl0, ite_eq_left rfl]
  have hc3 : ∀ u : Nat, m₃.clocks[u]! =
      if u = 0 then VClock.bump (VClock.bump (m.clocks[0]!) 0) 0
      else if u < k + 1 then m.clocks[u]! else if u = k + 1 then VClock.bump (m.clocks[0]!) 0
      else default := by
    intro u
    rw [h3c, getElem!_set! _ _ (by rw [h2c]; simp <;> omega), h2c0]
    by_cases h0 : u = 0
    · simp [h0]
    · simp only [h0, ↓reduceIte]
      rw [h2c, getElem!_push, getElem!_set! _ _ hcl0]
      simp [h0, hcs]
  have hgrow : ∀ u : Nat, u < k + 1 → VClock.le (m.clocks[u]!) (m₃.clocks[u]!) = true := by
    intro u hu
    rw [hc3 u]
    by_cases h0 : u = 0
    · subst h0; simp only [↓reduceIte]
      exact VClock.le_trans (VClock.le_bump _ _) (VClock.le_bump _ _)
    · simp only [h0, hu, ↓reduceIte]; exact VClock.le_refl _
  have hchild : child = k + 1 := by rw [hc, hsz]
  subst hchild
  have hk0 : (0 : Nat) ≠ k + 1 := by omega
  have hG'0 : ∀ u : Nat, u ≠ 0 → u ≠ k + 1 →
      Conc.upd (Conc.upd G (k + 1) (.bump (ctxPtr k) 0 false)) 0 (.main (k + 1) []) u = G u :=
    fun u h0 h1 => by rw [Conc.upd_ne _ _ h0, Conc.upd_ne _ _ h1]
  have hG'k : Conc.upd (Conc.upd G (k + 1) (.bump (ctxPtr k) 0 false)) 0 (.main (k + 1) [])
      (k + 1) = .bump (ctxPtr k) 0 false := by
    rw [Conc.upd_ne _ _ hk0.symm, Conc.upd_self]
  have hth3 : m₃.threads = m.threads.push { spawner := 0, joined := false } := h3t.trans h2t
  refine ⟨rfl, h3cur, k + 1, [], Conc.upd_self _ _ _, by omega, by rw [hth3]; simp [hsz], ?_, ?_,
    ?_, List.nodup_nil, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h3c, h2c]; simp [hcs]
  · intro u h1 h2
    by_cases hu : u = k + 1
    · subst hu; exact ⟨0, false, by rw [hG'k, Nat.add_sub_cancel]⟩
    · rw [hG'0 u (by omega) hu]; exact hkid u h1 (by omega)
  · intro u hu
    rw [hG'0 u (by omega) (by omega)]; exact hnone u (by omega)
  · intro u h hj
    left
    by_cases hu : u < k + 1
    · have e : m₃.threads[u] = m.threads[u]'(hsz ▸ hu) := by
        simp only [hth3]; exact Array.getElem_push_lt _
      rw [e] at hj
      rcases hjoined u (hsz ▸ hu) hj with h0 | h0
      · exact h0
      · simp at h0
    · have hu' : u = k + 1 := by rw [hth3] at h; simp [hsz] at h; omega
      subst hu'
      have e : m₃.threads[k + 1] = { spawner := 0, joined := false } := by
        simp only [hth3]; rw [Array.getElem_push]; simp [hsz]
      rw [e] at hj; cases hj
  · obtain ⟨h, hj⟩ := hj0
    have h' : 0 < m₃.threads.size := by rw [hth3]; simp
    refine ⟨h', ?_⟩
    have e : m₃.threads[0] = m.threads[0] := by simp only [hth3]; exact Array.getElem_push_lt _
    rw [e]; exact hj
  · intro blk' hb'; rw [h3b0] at hb'; exact hctx blk' hb'
  · have htot : total (Conc.upd (Conc.upd G (k + 1) (.bump (ctxPtr k) 0 false)) 0
        (.main (k + 1) [])) (k + 1) = total G k := by
      rw [total_succ, hG'k, total_congr (G := G) fun u h1 h2 => by rw [hG'0 u (by omega) (by omega)]]
      simp [Gh.count]
    rw [htot]
    refine cntOk_mono hcnt h3a h3b1 (by rw [hth3]; simp) (fun u hu => hgrow u (hsz ▸ hu))
      (fun e he => ?_) (fun u h1 h2 => ?_) (by rw [hsz]; omega)
    · rw [hm₃] at he
      simp only [Mem.write, Mem.recordAt, Array.mem_push] at he
      rcases he with he | rfl
      · left; rw [hm₂] at he; exact he
      · right; simp [plainHit]
    · have hu : u = k + 1 := by rw [hth3] at h2; simp at h2; rw [hsz] at h1; omega
      subst hu
      rw [hc3]; simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.lt_irrefl]
      exact VClock.le_bump _ _
  · intro e he
    rcases h3f e he with he | he
    · obtain ⟨u, hu, hl⟩ := hfp e he
      exact ⟨u, by rw [hth3]; simp; omega, VClock.le_trans hl (hgrow u (hsz ▸ hu))⟩
    · exact ⟨0, by rw [hth3]; simp, by rw [he]; exact VClock.le_refl _⟩

/-- `main`'s join of a thread that ended keeps the invariant; the thread goes into `J`. -/
theorem inv_join {G : ThreadId → Gh} {m m' : Mem} {J : List Nat} {tid : ThreadId}
    (hi : Inv n G m) (hG0 : G 0 = .main 4 J) (hfin : ∃ p, G tid = .bump p n.toNat true)
    (hj : ((Thread.join tid).run { m with current := 0 }).run = some (.ok ((), m'))) :
    tid ∉ J ∧ m'.current = 0 ∧ Inv n (Conc.upd G 0 (.main 4 (tid :: J))) m' := by
  obtain ⟨s, J', hG0', hs4, hsz, hcs, hkid, hnone, hnd, hJ, hjoined, hj0, hctx, hcnt, hfp⟩ := hi
  rw [hG0] at hG0'; cases hG0'
  obtain ⟨rec, hrec, hrj, hm'⟩ := join_eq hj
  obtain ⟨htl, hre⟩ := Array.getElem?_eq_some_iff.mp hrec
  simp only at htl hre
  have ht0 : tid ≠ 0 := by
    intro e; subst e
    obtain ⟨h, hj0'⟩ := hj0
    rw [hre] at hj0'; rw [hj0'] at hrj; cases hrj
  have htJ : tid ∉ J := by
    intro hin
    obtain ⟨-, -, -, -, h, hjt⟩ := hJ tid hin
    rw [hre] at hjt; rw [hjt] at hrj; cases hrj
  have hcl0 : 0 < m.clocks.size := by rw [hcs]; omega
  have h't : m'.threads = m.threads.set! tid { rec with joined := true } := by rw [hm']
  have h'c : m'.clocks = m.clocks.set! 0
      (VClock.merge (VClock.bump (m.clocks[0]!) 0) (m.clocks[tid]!)) := by rw [hm']
  have hc' : ∀ u : Nat, m'.clocks[u]! = if u = 0 then
      VClock.merge (VClock.bump (m.clocks[0]!) 0) (m.clocks[tid]!) else m.clocks[u]! := by
    intro u; rw [h'c, getElem!_set! _ _ hcl0]
  have hgrow : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := by
    intro u; rw [hc' u]; split
    · subst_vars; exact VClock.le_trans (VClock.le_bump _ _) (VClock.le_merge_left _ _)
    · exact VClock.le_refl _
  have hsz' : m'.threads.size = m.threads.size := by rw [h't]; simp
  have hth' : ∀ u (h : u < m'.threads.size), m'.threads[u] =
      if u = tid then { rec with joined := true } else m.threads[u]'(hsz' ▸ h) := by
    intro u h
    simp only [h't, Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds (by simpa [hsz'] using h)]
    by_cases hu : u = tid
    · subst hu; simp
    · simp [Ne.symm hu, hu]
  have hG' : ∀ u : Nat, u ≠ 0 → Conc.upd G 0 (.main 4 (tid :: J)) u = G u :=
    fun u h => Conc.upd_ne _ _ h
  refine ⟨htJ, by rw [hm'], 4, tid :: J, Conc.upd_self _ _ _, hs4, hsz' ▸ hsz,
    by rw [h'c]; simp [hcs], fun u h1 h2 => ?_, fun u hu => ?_, List.nodup_cons.mpr ⟨htJ, hnd⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hG' u (by omega)]; exact hkid u h1 h2
  · rw [hG' u (by omega)]; exact hnone u hu
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · obtain ⟨p, hp⟩ := hfin
      refine ⟨Nat.pos_of_ne_zero ht0, by rw [hsz] at htl; omega, ⟨p, by rw [hG' v ht0]; exact hp⟩,
        ?_, hsz' ▸ htl, ?_⟩
      · rw [hc' v, hc' 0, ite_eq_right ht0, ite_eq_left rfl]; exact VClock.le_merge_right _ _
      · rw [hth' v (hsz' ▸ htl), ite_eq_left rfl]
    · obtain ⟨h1, h2, ⟨p, hp⟩, hc, hlt, hjv⟩ := hJ v hv
      have hv0 : v ≠ 0 := by omega
      have hvt : v ≠ tid := fun e => htJ (e ▸ hv)
      refine ⟨h1, h2, ⟨p, by rw [hG' v hv0]; exact hp⟩, ?_, hsz' ▸ hlt, ?_⟩
      · rw [hc' v, hc' 0, ite_eq_right hv0, ite_eq_left rfl]
        exact VClock.le_trans hc (VClock.le_trans (VClock.le_bump _ _) (VClock.le_merge_left _ _))
      · rw [hth' v (hsz' ▸ hlt), ite_eq_right hvt]; exact hjv
  · intro u h hju
    rw [hth' u h] at hju
    by_cases hu : u = tid
    · exact .inr (hu ▸ List.mem_cons_self)
    · rw [ite_eq_right hu] at hju
      rcases hjoined u (hsz' ▸ h) hju with h0 | h0
      · exact .inl h0
      · exact .inr (List.mem_cons_of_mem _ h0)
  · obtain ⟨h, hj0'⟩ := hj0
    refine ⟨hsz' ▸ h, ?_⟩
    rw [hth' 0 (hsz' ▸ h), ite_eq_right (Ne.symm ht0)]; exact hj0'
  · intro blk hb; rw [hm'] at hb; exact hctx blk hb
  · rw [total_congr (G := G) fun u h1 _ => by rw [hG' u (by omega)]]
    exact cntOk_mono hcnt (by rw [hm']) (by rw [hm']; rfl) (by rw [hsz']; exact Nat.le_refl _)
      (fun u _ => hgrow u) (fun e he => .inl (by rw [hm'] at he; exact he))
      (fun u h1 h2 => absurd h2 (by rw [hsz']; omega)) (by rw [hsz]; omega)
  · intro e he
    rw [hm'] at he
    obtain ⟨u, hu, hl⟩ := hfp e he
    exact ⟨u, hsz' ▸ hu, VClock.le_trans hl (hgrow u)⟩

/-- 4 distinct thread ids in `1 … 4` are all of them. -/
theorem all_joined {J : List Nat} (hnd : J.Nodup) (hl : J.length = 4)
    (hr : ∀ u ∈ J, 1 ≤ u ∧ u ≤ 4) : ∀ u, 1 ≤ u → u ≤ 4 → u ∈ J := by
  intro u h1 h2
  apply Classical.byContradiction
  intro hu
  have hsub : J ⊆ (List.range' 1 4).erase u := by
    intro v hv
    obtain ⟨a, b⟩ := hr v hv
    have hvu : v ≠ u := fun e => hu (e ▸ hv)
    exact (List.mem_erase_of_ne hvu).mpr (List.mem_range'_1.mpr ⟨a, by omega⟩)
  have := hnd.length_le_of_subset hsub
  rw [List.length_erase_of_mem (List.mem_range'_1.mpr ⟨h1, by omega⟩)] at this
  simp at this; omega

/-- `main`'s load after the 4 joins reads `4 * n`: every thread did `n` increments, and `main`'s
clock is `≥` every message's clock, so only the newest message is a read option. -/
theorem final_load {G : ThreadId → Gh} {m m' : Mem} {J : List Nat} {c : Nat} {v : BitVec 32}
    (hi : Inv n G m) (hG0 : G 0 = .main 4 J) (hJ4 : J.length = 4) (hcur : m.current = 0)
    (h : ((atomicLoadAt c .seqCst 4 counterPtr).run m).run = some (.ok (v, m'))) :
    v = BitVec.ofNat 32 (4 * n.toNat) ∧ m'.threads = m.threads ∧ m'.blocks = m.blocks := by
  have hnd' : ∀ q, G m.current ≠ .bump q n.toNat true := by
    intro q hq; rw [hcur, hG0] at hq; cases hq
  have hiR := inv_recordAt (b := 1) (o := 0) (len := 4) (k := .atomicRead) (hn1 := by decide) n hi hnd' (by
    obtain ⟨s, J, -, -, hsz, -⟩ := hi; rw [hcur, hsz]; exact Nat.succ_pos _)
  obtain ⟨s, J', hG0', hs4, hsz, hcs, hkid, hnone, hnd, hJ, hjoined, hj0, hctx, hcnt, hfp⟩ := hi
  rw [hG0] at hG0'; cases hG0'
  have hall := all_joined hnd hJ4 fun u hu => ⟨(hJ u hu).1, (hJ u hu).2.1⟩
  have htot : total G 4 = 4 * n.toNat := by
    have : ∀ k : Nat, k < 4 → (G (k + 1)).count = n.toNat := by
      intro k hk
      obtain ⟨-, -, ⟨p, hp⟩, -⟩ := hJ (k + 1) (hall (k + 1) (by omega) (by omega))
      rw [hp]; rfl
    simp only [total, List.range_succ, List.range_zero, List.map, List.sum_cons, List.sum_nil,
      List.nil_append, List.cons_append, List.map_cons]
    rw [this 0 (by omega), this 1 (by omega), this 2 (by omega), this 3 (by omega)]; omega
  have hclk : ∀ u, u < m.threads.size → VClock.le (m.clocks[u]!) (m.clocks[0]!) = true := by
    intro u hu
    by_cases h0 : u = 0
    · subst h0; exact VClock.le_refl _
    · exact (hJ u (hall u (Nat.pos_of_ne_zero h0) (by rw [hsz] at hu; omega))).2.2.2.1
  obtain ⟨b, blk, o, li, m₁, pos, ha, -, hl, hpos, hd, hm'⟩ := Proto.atomicLoadAt_ok h
  obtain ⟨hb, hblk, -, -, hbs, -, ho⟩ := access_eq ha
  simp only [counterPtr, Option.some.injEq] at hb ho
  subst hb; subst ho
  obtain ⟨_, _, hG0R, _, hszR, hcsR, _, _, _, _, _, _, _, hcntR, hfpR⟩ := hiR
  rw [hG0] at hG0R; cases hG0R
  have hl' : ((locIdx 1 0 4).run (m.recordAt 1 0 4 .atomicRead)).run = some (.ok (li, m₁)) := hl
  obtain ⟨hcat, hth1, hcl1, hbl1, -, hcu1⟩ := cntAt_locIdx hcntR (by rw [hszR]; omega) hl'
  rw [htot] at hcat
  have hsz1 := hcat.size
  -- The newest message happened before `main`'s load.
  have hle : VClock.le ((m₁.atomics[li]!).msgs[4 * n.toNat]'(by omega)).clock
      (m₁.clocks[m₁.current]!) = true := by
    obtain ⟨u, hu, hlu⟩ := hcat.clk (4 * n.toNat) (by omega)
    rw [hth1] at hu
    have hR : ∀ w : Nat, (m.recordAt 1 0 4 .atomicRead).clocks[w]! =
        if w = 0 then VClock.bump (m.clocks[0]!) 0 else m.clocks[w]! := by
      intro w; simp only [Mem.recordAt, hcur]; rw [getElem!_set! _ _ (by rw [hcs]; omega)]
    have hcR : (m.recordAt 1 0 4 .atomicRead).current = 0 := hcur
    rw [hcl1] at hlu ⊢
    rw [hcu1, hR, hcR, ite_eq_left rfl]
    rw [hR] at hlu
    split at hlu
    · subst_vars; exact hlu
    · exact VClock.le_trans hlu (VClock.le_trans (hclk u hu) (VClock.le_bump _ _))
  have hf : floorPos m₁ li = (m₁.atomics[li]!).msgs.size - 1 := by
    have h1 := Proto.le_floorPos (by omega) hle
    have h2 := Proto.floorPos_lt (m := m₁) (li := li) (by omega)
    omega
  rw [Proto.readOpts_floor (by omega) hf] at hpos
  have hcp : c = 0 ∧ pos = 4 * n.toNat := by
    rcases c with _ | c
    · simp at hpos; omega
    · simp at hpos
  obtain ⟨rfl, rfl⟩ := hcp
  rw [getElem!_pos (m₁.atomics[li]!).msgs _ (by omega), hcat.val _ (by omega)] at hd
  simp only [Option.some.injEq, Except.ok.injEq] at hd
  refine ⟨hd.symm, ?_, ?_⟩
  · rw [hm']; show m₁.threads = m.threads; rw [hth1]; rfl
  · rw [hm']
    simp only [Proto.loadM, Proto.acqM, Proto.observeM, AtomicOrder.isAcq, ↓reduceIte]
    rw [hbl1]; rfl

/-- The preparation of `main`'s load after the 4 joins: the counter holds `4 * n`, and the load
reads the newest message only. -/
theorem final_prep {G : ThreadId → Gh} {m m₁ : Mem} {J : List Nat} {li : Nat} {opts : Array Nat}
    (hi : Inv n G m) (hG0 : G 0 = .main 4 J) (hJ4 : J.length = 4) (hcur : m.current = 0)
    (h : ((loadPrep 32 .seqCst 4 counterPtr false).run m).run = some (.ok ((li, opts), m₁))) :
    CntAt (4 * n.toNat) li m₁ ∧ opts = #[(m₁.atomics[li]!).msgs.size - 1] := by
  have hnd' : ∀ q, G m.current ≠ .bump q n.toNat true := by
    intro q hq; rw [hcur, hG0] at hq; cases hq
  have hiR := inv_recordAt (b := 1) (o := 0) (len := 4) (k := .atomicRead) (hn1 := by decide) n hi hnd' (by
    obtain ⟨s, J, -, -, hsz, -⟩ := hi; rw [hcur, hsz]; exact Nat.succ_pos _)
  obtain ⟨s, J', hG0', hs4, hsz, hcs, hkid, hnone, hnd, hJ, hjoined, hj0, hctx, hcnt, hfp⟩ := hi
  rw [hG0] at hG0'; cases hG0'
  have hall := all_joined hnd hJ4 fun u hu => ⟨(hJ u hu).1, (hJ u hu).2.1⟩
  have htot : total G 4 = 4 * n.toNat := by
    have : ∀ k : Nat, k < 4 → (G (k + 1)).count = n.toNat := by
      intro k hk
      obtain ⟨-, -, ⟨p, hp⟩, -⟩ := hJ (k + 1) (hall (k + 1) (by omega) (by omega))
      rw [hp]; rfl
    simp only [total, List.range_succ, List.range_zero, List.map, List.sum_cons, List.sum_nil,
      List.nil_append, List.cons_append, List.map_cons]
    rw [this 0 (by omega), this 1 (by omega), this 2 (by omega), this 3 (by omega)]; omega
  have hclk : ∀ u, u < m.threads.size → VClock.le (m.clocks[u]!) (m.clocks[0]!) = true := by
    intro u hu
    by_cases h0 : u = 0
    · subst h0; exact VClock.le_refl _
    · exact (hJ u (hall u (Nat.pos_of_ne_zero h0) (by rw [hsz] at hu; omega))).2.2.2.1
  obtain ⟨b, blk, o, ha, -, hl, rfl⟩ := Proto.loadPrep_ok h
  simp only [Bool.false_eq_true, ↓reduceIte] at ha hl
  obtain ⟨hb, hblk, -, -, hbs, -, ho⟩ := access_eq ha
  simp only [counterPtr, Option.some.injEq] at hb ho
  subst hb; subst ho
  obtain ⟨_, _, hG0R, _, hszR, hcsR, _, _, _, _, _, _, _, hcntR, hfpR⟩ := hiR
  rw [hG0] at hG0R; cases hG0R
  have hl' : ((locIdx 1 0 4).run (m.recordAt 1 0 4 .atomicRead)).run = some (.ok (li, m₁)) := hl
  obtain ⟨hcat, hth1, hcl1, -, -, hcu1⟩ := cntAt_locIdx hcntR (by rw [hszR]; omega) hl'
  rw [htot] at hcat
  have hsz1 := hcat.size
  -- The newest message happened before `main`'s load.
  have hle : VClock.le ((m₁.atomics[li]!).msgs[4 * n.toNat]'(by omega)).clock
      (m₁.clocks[m₁.current]!) = true := by
    obtain ⟨u, hu, hlu⟩ := hcat.clk (4 * n.toNat) (by omega)
    rw [hth1] at hu
    have hR : ∀ w : Nat, (m.recordAt 1 0 4 .atomicRead).clocks[w]! =
        if w = 0 then VClock.bump (m.clocks[0]!) 0 else m.clocks[w]! := by
      intro w; simp only [Mem.recordAt, hcur]; rw [getElem!_set! _ _ (by rw [hcs]; omega)]
    have hcR : (m.recordAt 1 0 4 .atomicRead).current = 0 := hcur
    rw [hcl1] at hlu ⊢
    rw [hcu1, hR, hcR, ite_eq_left rfl]
    rw [hR] at hlu
    split at hlu
    · subst_vars; exact hlu
    · exact VClock.le_trans hlu (VClock.le_trans (hclk u hu) (VClock.le_bump _ _))
  have hf : floorPos m₁ li = (m₁.atomics[li]!).msgs.size - 1 := by
    have h1 := Proto.le_floorPos (by omega) hle
    have h2 := Proto.floorPos_lt (m := m₁) (li := li) (by omega)
    omega
  exact ⟨hcat, Proto.readOpts_floor (by omega) hf⟩

/-- `main`'s load after the 4 joins gives no error. -/
theorem final_noErr {G : ThreadId → Gh} {m : Mem} {J : List Nat} {c : Nat}
    (hi : Inv n G m) (he : Ex G m) (hG0 : G 0 = .main 4 J) (hJ4 : J.length = 4)
    (hcur : m.current = 0)
    (hc : c < loadCount 32 .seqCst 4 counterPtr m ∨ loadCount 32 .seqCst 4 counterPtr m = 0 ∧ c = 0)
    (e : Error) :
    ((atomicLoadAt (n := 32) c .seqCst 4 counterPtr).run m).run ≠ some (.error e) := by
  have hnd : ∀ q, G m.current ≠ .bump q n.toNat true := by
    intro q hq; rw [hcur, hG0] at hq; cases hq
  have hlt : m.current < m.threads.size := by
    obtain ⟨s, J', -, -, hsz, -⟩ := hi; rw [hcur, hsz]; exact Nat.succ_pos _
  obtain ⟨-, ⟨blk, hb, hl, hs, hk, hadd⟩, -, hf, -⟩ := he
  have hacc : m.access counterPtr (intSize 32) 4 = pure (1, blk, 0) :=
    access_of (by rfl) hb hl (by simp [counterPtr]) (by simp [counterPtr, hs]; decide)
      (by simp [counterPtr]; omega)
  have hcnt1 : loadCount 32 .seqCst 4 counterPtr m ≤ 1 := by
    refine Proto.optCount_le_one fun a m' h => ?_
    obtain ⟨⟨li, opts⟩, hr, rfl⟩ := MemM.map_ok h
    obtain ⟨-, rfl⟩ := final_prep n hi hG0 hJ4 hcur hr
    simp
  have hc0 : c = 0 := by omega
  subst hc0
  refine Proto.atomicLoadAt_noErr ?_ (fun li opts m₁ h => ?_) e
  · refine Proto.loadPrep_noErr (b := 1) (o := 0) (blk := blk) (by simpa using hacc)
      (noRace_b1 hf hlt rfl) ?_
    intro e' h'
    obtain ⟨_, _, _, _, hszR, _, _, _, _, _, _, _, _, hcntR, hfpR⟩ :=
      inv_recordAt n hi hnd hlt (b := 1) (o := 0) (len := 4) (k := .atomicRead) (hn1 := by decide)
    refine Proto.locIdx_noErr (fun i hi' => ?_) (fun hn => (hcntR.2.1 hn).2.2) e' h'
    have hlt' := (Array.findIdx?_eq_some_iff_getElem.mp hi').1
    have hq := (Array.findIdx?_eq_some_iff_getElem.mp hi').2.1
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    rw [getElem!_pos (m.recordAt 1 0 4 .atomicRead).atomics i hlt']
    exact (hcntR.1 _ (Array.getElem_mem hlt') hq.1).2
  · obtain ⟨hct, rfl⟩ := final_prep n hi hG0 hJ4 hcur h
    have hsz := hct.size
    have hp : (m₁.atomics[li]!).msgs.size - 1 < (m₁.atomics[li]!).msgs.size := by omega
    refine ⟨_, rfl, BitVec.ofNat 32 ((m₁.atomics[li]!).msgs.size - 1), ?_⟩
    rw [getElem!_pos (m₁.atomics[li]!).msgs _ hp]
    exact hct.val _ hp

/-- After the 4 joins, `main` joined every thread. -/
theorem joined_final {G : ThreadId → Gh} {m : Mem} {J : List Nat} (hi : Inv n G m)
    (hG0 : G 0 = .main 4 J) (hJ4 : J.length = 4) : joinedAll 0 m := by
  obtain ⟨s, J', hG0', hs4, hsz, hcs, hkid, hnone, hnd, hJ, hjoined, ⟨h0, hj0⟩, -⟩ := hi
  rw [hG0] at hG0'; cases hG0'
  have hall := all_joined hnd hJ4 fun u hu => ⟨(hJ u hu).1, (hJ u hu).2.1⟩
  intro r hr _
  obtain ⟨u, hu, rfl⟩ := Array.mem_iff_getElem.mp hr
  by_cases h : u = 0
  · subst h; exact hj0
  · obtain ⟨-, -, -, -, hu', hj⟩ := hJ u (hall u (Nat.pos_of_ne_zero h) (by omega))
    exact hj

/-! ## `main` before its first spawn -/

/-- `main` before its first spawn: one thread, no atomic location yet, and each access happened
before `main`'s clock. -/
structure PreA (m : Mem) : Prop where
  cur : m.current = 0
  th : m.threads = #[{ spawner := 0, joined := true }]
  cs : m.clocks.size = 1
  atm : m.atomics = #[]
  fp : ∀ e ∈ m.footprint, VClock.le e.clock (m.clocks[0]!) = true

theorem preA_recordAt {m : Mem} {b o l : Nat} {k : AccessKind} (h : PreA m) :
    PreA (m.recordAt b o l k) := by
  obtain ⟨hc, ht, hs, ha, hf⟩ := h
  have hget : (m.recordAt b o l k).clocks[0]! = VClock.bump (m.clocks[0]!) 0 := by
    simp only [Mem.recordAt, hc]; rw [getElem!_set! _ _ (by omega), ite_eq_left rfl]
  refine ⟨hc, ht, by simp [Mem.recordAt, hs], ha, fun e he => ?_⟩
  rw [hget]
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact VClock.le_trans (hf e he) (VClock.le_bump _ _)
  · simp only [hc]; exact VClock.le_refl _

theorem preA_write {m : Mem} {b o : Nat} {blk : Block} {bs : Array Byte} (h : PreA m) :
    PreA (m.write b blk o bs) := ⟨h.cur, h.th, h.cs, h.atm, h.fp⟩

theorem preA_alloc {m m' : Mem} {kind : BlockKind} {size align : Nat} {q : Ptr} (h : PreA m)
    (ha : ((alloc kind size align).run m).run = some (.ok (q, m'))) : PreA m' := by
  obtain ⟨-, rfl⟩ := Proto.alloc_ok ha; exact ⟨h.cur, h.th, h.cs, h.atm, h.fp⟩

/-- The counter's bytes do not change by a write to another block, or by `recordAccess`. -/
theorem curBytes_write {m : Mem} {b o : Nat} {blk : Block} {bs : Array Byte} (hb : b ≠ 1) :
    Proto.curBytes (m.write b blk o bs) 1 0 4 = Proto.curBytes m 1 0 4 := by
  simp [Proto.curBytes, Mem.write, Array.set!_eq_setIfInBounds, hb]

theorem curBytes_recordAt {m : Mem} {b o l : Nat} {k : AccessKind} :
    Proto.curBytes (m.recordAt b o l k) 1 0 4 = Proto.curBytes m 1 0 4 := rfl

/-- The facts of context slot `k`: the counter's address and `n`. -/
def SlotOk (bs : Array Byte) (k : Nat) : Prop :=
  (Enc.decode (bs.extract (16 * k) (16 * k + 8)) : Result Ptr).run = some (.ok counterPtr) ∧
  (Enc.decode (bs.extract (16 * k + 8) (16 * k + 12)) : Result (BitVec 32)).run = some (.ok n)

/-- The two stores of slot `k` keep slots `0 … k - 1` and fill slot `k`. -/
theorem slots_step {bs : Array Byte} {k : Nat} (hs : ∀ j < k, SlotOk n bs j)
    (hsz : 16 * k + 12 ≤ bs.size) :
    ∀ j < k + 1, SlotOk n (writeBytes (writeBytes bs (16 * k) (Enc.encode counterPtr))
      (16 * k + 8) (Enc.encode n)) j := by
  have h8 : (Enc.encode counterPtr).size = 8 := LawfulEnc.size_encode _
  have h4 : (Enc.encode n).size = 4 := LawfulEnc.size_encode _
  have hsz1 : (writeBytes bs (16 * k) (Enc.encode counterPtr)).size = bs.size :=
    writeBytes_size _ _ _ (by omega)
  intro j hj
  -- A read of `len` bytes at `o` that misses both writes, or hits one of them.
  have miss : ∀ o len, o + len ≤ 16 * k ∨ 16 * k + 12 ≤ o → o + len ≤ bs.size →
      (writeBytes (writeBytes bs (16 * k) (Enc.encode counterPtr)) (16 * k + 8)
        (Enc.encode n)).extract o (o + len) = bs.extract o (o + len) := by
    intro o len hd hl
    rw [extract_writeBytes_disjoint _ _ _ _ _ (by omega) (by omega) (by omega),
      extract_writeBytes_disjoint _ _ _ _ _ (by omega) (by omega) (by omega)]
  by_cases hjk : j < k
  · obtain ⟨hp, hv⟩ := hs j hjk
    refine ⟨?_, ?_⟩
    · rw [miss (16 * j) 8 (by omega) (by omega)]; exact hp
    · have := miss (16 * j + 8) 4 (by omega) (by omega)
      rw [show 16 * j + 8 + 4 = 16 * j + 12 by omega] at this
      rw [this]; exact hv
  · have hj' : j = k := by omega
    subst hj'
    refine ⟨?_, ?_⟩
    · have e1 := extract_writeBytes_disjoint (writeBytes bs (16 * j) (Enc.encode counterPtr))
        (16 * j + 8) (Enc.encode n) (16 * j) 8 (by omega) (by omega) (by omega)
      have e2 := extract_writeBytes bs (16 * j) (Enc.encode counterPtr) (by omega)
      rw [h8] at e2
      rw [e1, e2]
      exact congrArg ExceptT.run (LawfulEnc.decode_encode counterPtr)
    · have e := extract_writeBytes (writeBytes bs (16 * j) (Enc.encode counterPtr)) (16 * j + 8)
        (Enc.encode n) (by omega)
      rw [h4, show 16 * j + 8 + 4 = 16 * j + 12 by omega] at e
      rw [e]
      exact congrArg ExceptT.run (LawfulEnc.decode_encode n)

/-- `main` before its first spawn, the facts of strict mode: the three blocks, and each access is
a write to a context or the counter, or an access to the handles. -/
def PreB (m : Mem) : Prop :=
  BlkAt m 0 64 8 ∧ BlkAt m 1 4 4 ∧ BlkAt m 2 32 8 ∧
    ∀ e ∈ m.footprint, ((e.block = 0 ∨ e.block = 1) ∧ e.kind = .write) ∨ e.block = 2

/-- Before the first spawn, no access races: every access happened before. -/
theorem noRace_pre {m : Mem} {b o l : Nat} {k : AccessKind} (h : PreA m) : NoRace m b o l k :=
  Proto.noRace_of fun e he _ _ _ => .inl (by rw [h.cur]; exact h.fp e he)

/-- A write before the first spawn, to a block that it fits in, keeps `PreB`. -/
theorem preB_store {m : Mem} {b o : Nat} {blk : Block} {bs : Array Byte} (h : PreB m)
    (hb : m.blocks[b]? = some blk) (hfit : o + bs.size ≤ blk.bytes.size)
    (hk : b = 0 ∨ b = 1 ∨ b = 2) :
    PreB ((m.recordAt b o bs.size .write).write b blk o bs) := by
  obtain ⟨h0, h1, h2, hf⟩ := h
  have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have keep : ∀ b' sz a, BlkAt m b' sz a →
      BlkAt ((m.recordAt b o bs.size .write).write b blk o bs) b' sz a := by
    rintro b' sz a ⟨blk', hb', hl, hs, hkd, ha⟩
    simp only [BlkAt, Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds]
    by_cases hbb : b = b'
    · subst hbb
      rw [hb] at hb'; cases hb'
      rw [Array.getElem?_setIfInBounds_self_of_lt hlt]
      exact ⟨_, rfl, hl, by rw [writeBytes_size _ _ _ hfit]; exact hs, hkd, ha⟩
    · rw [Array.getElem?_setIfInBounds_ne hbb]
      exact ⟨blk', hb', hl, hs, hkd, ha⟩
  refine ⟨keep _ _ _ h0, keep _ _ _ h1, keep _ _ _ h2, fun e he => ?_⟩
  simp only [Mem.write, Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact hf e he
  · rcases hk with rfl | rfl | rfl
    · exact .inl ⟨.inl rfl, rfl⟩
    · exact .inl ⟨.inr rfl, rfl⟩
    · exact .inr rfl

/-- A store before the first spawn gives no error. -/
theorem store_noErr_pre {m : Mem} {p : Ptr} {a : Nat} {bs : Array Byte} {b o : Nat} {blk : Block}
    (hpa : PreA m) (hacc : m.access p bs.size a = pure (b, blk, o))
    (hk : blk.kind ≠ .constGlobal) (e : Error) :
    ((storeBytes p a bs).run m).run ≠ some (.error e) :=
  MemM.noErr_of_run (storeBytes_run hacc hk (noRace_pre hpa)) e

/-- `main` starts the spawns: the invariant holds with no thread spawned. -/
theorem inv_start {m : Mem} (h : PreA m)
    (hcnt : (intOfBytes 32 (Proto.curBytes m 1 0 4)).run = some (.ok 0))
    (hctx : ∀ blk, m.blocks[0]? = some blk → ∀ k < 4, SlotOk n blk.bytes k) :
    Inv n (fun u => if u = 0 then .main 0 [] else .none) m := by
  obtain ⟨hc, ht, hs, ha, hf⟩ := h
  have hts : m.threads.size = 1 := by rw [ht]; rfl
  refine ⟨0, [], by simp, by omega, hts, hs, fun u h1 h2 => by omega, fun u hu => ?_,
    List.nodup_nil, by simp, fun u h _ => .inl (by omega), ⟨by omega, ?_⟩, hctx, ?_,
    fun e he => ⟨0, by omega, hf e he⟩⟩
  · exact ite_eq_right (Nat.ne_of_gt hu)
  · simp only [ht]; rfl
  · refine ⟨by simp [ha], fun _ => ⟨rfl, hcnt, by simp [ha]⟩, fun i hi => ?_,
      fun e he _ u hu => ?_⟩
    · simp [ha] at hi
    · rw [hts] at hu; rw [show u = 0 by omega]; exact hf e he

/-- The ghost values at the start: `main` spawned nothing. -/
def G0 : ThreadId → Gh := fun u => if u = 0 then .main 0 [] else .none

/-- `main` starts the spawns: `Ex` holds. -/
theorem ex_start {m : Mem} (hpa : PreA m) (hpb : PreB m) : Ex G0 m := by
  obtain ⟨hc, ht, hs, ha, hf⟩ := hpa
  obtain ⟨h0, h1, h2, hk⟩ := hpb
  have hts : m.threads.size = 1 := by rw [ht]; rfl
  refine ⟨h0, h1, h2, fun e he => ?_, fun r hr => ?_, 0, [], by simp [G0], fun _ _ k hk => by omega⟩
  · rcases hk e he with ⟨hb, hw⟩ | hb
    · exact .inr (.inr (.inl ⟨hb, hw, fun u hu => by
        rw [hts] at hu; rw [show u = 0 by omega]; exact hf e he⟩))
    · exact .inr (.inr (.inr ⟨hb, hf e he⟩))
  · rw [ht] at hr
    simp [mem0, Mem.ofGlobals] at hr
    rw [hr]


/-- The invariant of `main`'s first loop: slots `0 … local6 - 1` are filled. -/
def inv9 (s : parallelCounterLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  G = G0 ∧ s.local6.toNat ≤ 4 ∧ s.handles = ⟨some 2, 0⟩ ∧ PreA m ∧ PreB m ∧
  (intOfBytes 32 (Proto.curBytes m 1 0 4)).run = some (.ok 0) ∧
  ∀ blk, m.blocks[0]? = some blk → ∀ k < s.local6.toNat, SlotOk n blk.bytes k

/-- The end of `main`'s first loop: all 4 slots are filled. -/
def post9 (r : parallelCounterExit × parallelCounterLocals) (G : ThreadId → Gh) (m : Mem)
    (_ : Nat) : Prop :=
  r.1 = .br8 ∧ G = G0 ∧ r.2.handles = ⟨some 2, 0⟩ ∧ PreA m ∧ PreB m ∧
  (intOfBytes 32 (Proto.curBytes m 1 0 4)).run = some (.ok 0) ∧
  ∀ blk, m.blocks[0]? = some blk → ∀ k < 4, SlotOk n blk.bytes k

theorem loop9_body (s : parallelCounterLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (h : inv9 n s G m d) :
    (proto n).WP 0 ((parallelCounter.loop9 n counterPtr ⟨some 0, 0⟩).run s) (fun r G' m' d' =>
      if parallelCounter.again9 r.1 then inv9 n r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun (x : parallelCounterLocals) => 4 - x.local6.toNat) r.2 <
          (fun (x : parallelCounterLocals) => 4 - x.local6.toNat) s)
      else post9 n r G' m' d') G m d := by
  obtain ⟨rfl, hle, hhd, hpa, hpb, hcnt, hsl⟩ := h
  unfold parallelCounter.loop9
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rename_i hlt
    have hlt' : s.local6.toNat < 4 := by simpa [lt, BitVec.ult] using hlt
    simp only [StateT.run_bind, bind_assoc]
    have e8 : (Enc.encode counterPtr).size = 8 := LawfulEnc.size_encode _
    have e4 : (Enc.encode n).size = 4 := LawfulEnc.size_encode _
    obtain ⟨bk1, hbk1, hk1, hsz64, hacc1⟩ := access_blk (o := 16 * s.local6.toNat)
      (len := (Enc.encode counterPtr).size) (a := 8) hpb.1 (by rw [e8]; omega)
      (fun A h => by omega) (p := ((⟨some 0, 0⟩ : Ptr).elem 16 s.local6).add 0)
      (by simp [Ptr.elem, Ptr.add])
    refine WP.bind (WP.liftM (fun e h => (store_noErr_pre hpa hacc1 hk1 e h).elim)
      fun _ m₁ hs₁ => ?_)
    obtain ⟨b, blk, o, ha, -, rfl⟩ := Proto.store_ok hs₁
    obtain ⟨hb, hblk, -, -, hsz1, -, ho⟩ := access_eq ha
    simp only [Ptr.elem, Ptr.add, Option.some.injEq] at hb
    subst hb
    have ho' : o = 16 * s.local6.toNat := by rw [ho]; simp only [Ptr.elem, Ptr.add]; omega
    subst ho'
    refine ⟨rfl, ?_⟩
    have hbe : blk = bk1 := by
      rw [ha] at hacc1
      have := congrArg ExceptT.run hacc1
      simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at this
      first | exact this | exact this.symm
    subst hbe
    have hpa1 := preA_write (b := 0) (blk := blk) (o := 16 * s.local6.toNat)
      (bs := Enc.encode counterPtr) (preA_recordAt (b := 0) (o := 16 * s.local6.toNat)
        (l := (Enc.encode counterPtr).size) (k := .write) hpa)
    have hpb1 := preB_store (o := 16 * s.local6.toNat) (bs := Enc.encode counterPtr) hpb hblk
      (by rw [e8, hsz64]; omega) (.inl rfl)
    obtain ⟨bk2, hbk2, hk2, -, hacc2⟩ := access_blk (o := 16 * s.local6.toNat + 8)
      (len := (Enc.encode n).size) (a := 4) hpb1.1 (by rw [e4]; omega)
      (fun A h => by omega) (p := ((⟨some 0, 0⟩ : Ptr).elem 16 s.local6).add 8)
      (by simp [Ptr.elem, Ptr.add] <;> omega)
    refine WP.bind (WP.liftM (fun e h => (store_noErr_pre hpa1 hacc2 hk2 e h).elim)
      fun _ m₂ hs₂ => ?_)
    obtain ⟨b2, blk2, o2, ha2, -, rfl⟩ := Proto.store_ok hs₂
    obtain ⟨hb2, hblk2, -, -, hsz2, -, ho2⟩ := access_eq ha2
    simp only [Ptr.elem, Ptr.add, Option.some.injEq] at hb2
    subst hb2
    have ho2' : o2 = 16 * s.local6.toNat + 8 := by rw [ho2]; simp only [Ptr.elem, Ptr.add]; omega
    subst ho2'
    have hb0 : 0 < m.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
    have hblk2' : blk2 = Block.mk (writeBytes blk.bytes (16 * s.local6.toNat)
        (Enc.encode counterPtr)) blk.align blk.kind blk.live blk.addr := by
      simp only [Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_self_of_lt hb0, Option.some.injEq] at hblk2
      exact hblk2.symm
    subst hblk2'
    refine ⟨rfl, ?_⟩
    simp only [StateT.run_pure, pure_bind, StateT.run_bind]
    refine WP.bind (WP.callRC (fun e h => (add_one_noErr (a := s.local6) (by omega) e h).elim)
      fun k' hadd => ?_)
    have hkn : k'.toNat = s.local6.toNat + 1 := add_one_ok hadd (by omega)
    simp only [StateT.run_modify, pure_bind]
    refine WP.pure' ?_
    simp only [parallelCounter.again9, ↓reduceIte]
    refine ⟨⟨rfl, by show k'.toNat ≤ 4; omega, hhd,
      preA_write (preA_recordAt (preA_write (preA_recordAt hpa))),
      preB_store (o := 16 * s.local6.toNat + 8) (bs := Enc.encode n) hpb1 hblk2
        (by simp only [e4]; rw [writeBytes_size _ _ _ (by rw [e8, hsz64]; omega), hsz64]; omega)
        (.inl rfl), ?_, ?_⟩,
      .inr ⟨trivial, by show 4 - k'.toNat < 4 - s.local6.toNat; omega⟩⟩
    · rw [curBytes_write (by omega), curBytes_recordAt, curBytes_write (by omega),
        curBytes_recordAt]
      exact hcnt
    · intro blk' hb' j hj
      simp only [Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds] at hb'
      rw [Array.getElem?_setIfInBounds_self_of_lt (by simpa using hb0), Option.some.injEq] at hb'
      subst hb'
      simp only [Ptr.elem, Ptr.add, e8, e4] at hsz1 hsz2
      have hsz8 : 16 * s.local6.toNat + 8 ≤ blk.bytes.size := by omega
      have hsz12 : 16 * s.local6.toNat + 12 ≤ blk.bytes.size := by
        rw [writeBytes_size _ _ _ (by rw [e8]; exact hsz8)] at hsz2; omega
      exact slots_step n (hsl blk hblk) hsz12 j (by rw [hkn] at hj; exact hj)
  · rename_i hge
    have hge' : ¬ s.local6.toNat < 4 := by simpa [lt, BitVec.ult] using hge
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [parallelCounter.again9, Bool.false_eq_true, ↓reduceIte]
    exact ⟨rfl, rfl, hhd, hpa, hpb, hcnt, fun blk hb k hk => hsl blk hb k (by omega)⟩

theorem ctxPtr_elem (i : BitVec 64) : (⟨some 0, 0⟩ : Ptr).elem 16 i = ctxPtr i.toNat := by
  simp [Ptr.elem, Ptr.add, ctxPtr]

/-- A thread id reads back. -/
theorem decode_tid (t : ThreadId) (h : t < 2 ^ 64) :
    (Enc.decode (Enc.encode t) : Result ThreadId).run = some (.ok t) := by
  have := LawfulEnc.decode_encode (α := BitVec 64) (BitVec.ofNat 64 t)
  show (do pure (← (Enc.decode (Enc.encode (BitVec.ofNat 64 t)) : Result (BitVec 64))).toNat :
    Result Nat).run = _
  rw [this]
  simp [pure, ExceptT.pure, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont, ExceptT.run,
    Nat.mod_eq_of_lt h]

/-- A spawn by `main` keeps `Ex`: the new thread's clock is `main`'s. -/
theorem ex_fork {G G' : ThreadId → Gh} {m m₂ : Mem} {child : ThreadId} (he : Ex G m)
    (hG : G' 0 = G 0) (hcs : m.clocks.size = m.threads.size) (h0 : 0 < m.threads.size)
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (child, m₂))) :
    Ex G' m₂ ∧ m₂.current = 0 ∧ m₂.clocks.size = m₂.threads.size := by
  obtain ⟨_, hm₂⟩ := fork_eq hf
  subst hm₂
  obtain ⟨B0, B1, B2, hfp, hsp, s, J, hG0, hd⟩ := he
  have hcl0 : 0 < m.clocks.size := by omega
  refine ⟨⟨B0, B1, B2, ?_, fun r hr => ?_, s, J, hG.trans hG0, hd⟩, rfl, by simp [hcs]⟩
  · refine fpOk_step hfp (fun e he => .inl he) (fun u hu => ?_) (fun u h1 h2 => ?_) h0
    · show VClock.le _ ((((m.clocks.set! 0 (VClock.bump (m.clocks[0]!) 0)).push
        (VClock.bump (m.clocks[0]!) 0)))[u]!) = true
      rw [getElem!_push, ite_eq_left (by simp; omega), getElem!_set! _ _ hcl0]
      split
      · subst_vars; exact VClock.le_bump _ _
      · exact VClock.le_refl _
    · simp only [Array.size_push] at h2
      have hu : u = m.threads.size := by omega
      show VClock.le _ ((((m.clocks.set! 0 (VClock.bump (m.clocks[0]!) 0)).push
        (VClock.bump (m.clocks[0]!) 0)))[u]!) = true
      rw [getElem!_push, ite_eq_right (by simp; omega), ite_eq_left (by simp; omega)]
      exact VClock.le_bump _ _
  · simp only [Array.mem_push] at hr
    rcases hr with hr | rfl
    · exact hsp r hr
    · rfl

/-- `main`'s store of handle `k` (thread `k + 1`) keeps `Ex`, with one more handle. -/
theorem ex_handle {G G' : ThreadId → Gh} {m m₃ : Mem} {k : Nat} {q : Ptr} (he : Ex G m)
    (hG : G 0 = .main k []) (hG' : G' 0 = .main (k + 1) []) (hk : k < 4) (hcur : m.current = 0)
    (hcs : m.clocks.size = m.threads.size) (h0 : 0 < m.threads.size)
    (hq : q = ⟨some 2, ((8 * k : Nat) : Int)⟩)
    (hs : ((store 8 q (k + 1 : ThreadId)).run m).run = some (.ok ((), m₃))) : Ex G' m₃ := by
  obtain ⟨b, blk, o, ha, -, rfl⟩ := Proto.store_ok hs
  obtain ⟨hb, hblk, -, -, -, -, ho⟩ := access_eq ha
  subst hq
  simp only [Option.some.injEq] at hb; subst hb
  simp only [Int.toNat_natCast] at ho; subst ho
  have heR := ex_recordAt (b := 2) (o := 8 * k) (l := (Enc.encode (k + 1 : ThreadId)).size)
    (k := .write) he (.inr (.inr ⟨rfl, hcur⟩)) (by rw [hcur]; exact h0) hcs
  obtain ⟨B0, B1, ⟨blk2, hb2, hl2, hs2, hk2, ha2⟩, hfp, hsp, s, J, hG0, hd⟩ := heR
  have hbe : blk2 = blk := by
    simp only [Mem.recordAt] at hb2; rw [hblk] at hb2; cases hb2; rfl
  subst hbe
  have e8 : (Enc.encode (k + 1 : ThreadId)).size = 8 :=
    LawfulEnc.size_encode (α := BitVec 64) _
  have hlt2 : 2 < m.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
  have hnb : ((m.recordAt 2 (8 * k) (Enc.encode (k + 1 : ThreadId)).size .write).write 2 blk2
      (8 * k) (Enc.encode (k + 1 : ThreadId))).blocks[2]? =
      some { blk2 with bytes := writeBytes blk2.bytes (8 * k) (Enc.encode (k + 1 : ThreadId)) } := by
    simp only [Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds]
    rw [Array.getElem?_setIfInBounds_self_of_lt hlt2]
  have hfit : 8 * k + (Enc.encode (k + 1 : ThreadId)).size ≤ blk2.bytes.size := by
    rw [e8, hs2]; omega
  have keep : ∀ b', b' ≠ 2 → ((m.recordAt 2 (8 * k) (Enc.encode (k + 1 : ThreadId)).size
      .write).write 2 blk2 (8 * k) (Enc.encode (k + 1 : ThreadId))).blocks[b']? =
      (m.recordAt 2 (8 * k) (Enc.encode (k + 1 : ThreadId)).size .write).blocks[b']? := by
    intro b' hb'
    simp only [Mem.write, Array.set!_eq_setIfInBounds]
    rw [Array.getElem?_setIfInBounds_ne (Ne.symm hb')]
  refine ⟨?_, ?_, ⟨_, hnb, hl2, by rw [writeBytes_size _ _ _ hfit, hs2], hk2, ha2⟩, hfp, hsp,
    k + 1, [], hG', ?_⟩
  · obtain ⟨b0, hb0, r⟩ := B0; exact ⟨b0, by rw [keep 0 (by omega)]; exact hb0, r⟩
  · obtain ⟨b1, hb1, r⟩ := B1; exact ⟨b1, by rw [keep 1 (by omega)]; exact hb1, r⟩
  · rw [hG0] at hG; cases hG
    intro blk' hb' j hj
    rw [hnb, Option.some.injEq] at hb'
    subst hb'
    by_cases hjk : j < k
    · have := hd blk2 hb2 j hjk
      rw [extract_writeBytes_disjoint _ _ _ _ _ hfit (by rw [hs2]; omega) (by rw [e8]; omega)]
      exact this
    · have hj' : j = k := by omega
      subst hj'
      have := extract_writeBytes blk2.bytes (8 * j) (Enc.encode (j + 1 : ThreadId)) hfit
      rw [e8] at this
      simp only
      rw [this]
      exact decode_tid _ (by unfold ThreadId at *; omega)

/-- The invariant of `main`'s spawn loop: it spawned `local29` threads, and the cleanup
counter `started` agrees with the loop index. -/
def inv32 (s : parallelCounterLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  s.started = s.local29 ∧ s.local29.toNat ≤ 4 ∧ m.current = 0 ∧
    Inv n (Conc.upd G 0 (.main s.local29.toNat [])) m ∧
    Ex (Conc.upd G 0 (.main s.local29.toNat [])) m

def post32 (r : parallelCounterExit × parallelCounterLocals) (G : ThreadId → Gh) (m : Mem)
    (_ : Nat) : Prop :=
  r.1 = .br31 ∧ m.current = 0 ∧ Inv n (Conc.upd G 0 (.main 4 [])) m ∧
    Ex (Conc.upd G 0 (.main 4 [])) m

theorem loop32_body (s : parallelCounterLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (h : inv32 n s G m d) :
    (proto n).WP 0 ((parallelCounter.loop32 ⟨some 0, 0⟩ ⟨some 2, 0⟩).run s) (fun r G' m' d' =>
      if parallelCounter.again32 r.1 then inv32 n r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun (_ : parallelCounterLocals) => 0) r.2 <
          (fun (_ : parallelCounterLocals) => 0) s)
      else post32 n r G' m' d') G m d := by
  obtain ⟨hstarted, hle, hcur, hi, he⟩ := h
  unfold parallelCounter.loop32
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rename_i hlt
    have hlt' : s.local29.toNat < 4 := by simpa [lt, BitVec.ult] using hlt
    simp only [StateT.run_bind, bind_assoc]
    refine WP.bind (WP.spawnC fun k hk => ⟨.main s.local29.toNat [], ⟨hi, he⟩,
      fun G₁ m₁ hg₁ hie₁ => ⟨_, rfl, fun child m₂ hf => ?_⟩⟩)
    obtain ⟨hi₁, he₁⟩ := hie₁
    have hsz₁ : m₁.threads.size = s.local29.toNat + 1 := by
      obtain ⟨s', J', hG', -, h, -⟩ := hi₁; rw [hg₁] at hG'; cases hG'; exact h
    have hcs₁ : m₁.clocks.size = m₁.threads.size := by
      obtain ⟨s', J', hG', -, h1, h2, -⟩ := hi₁; rw [h1, h2]
    obtain ⟨he₂, hcur₂, -⟩ := ex_fork (G' := G₁) he₁ rfl hcs₁ (by omega) hf
    have hch : child = s.local29.toNat + 1 := by rw [(fork_ok hf).1]; exact hsz₁
    obtain ⟨bk, hbk, hkk, -, hacc⟩ := access_blk (o := 8 * s.local29.toNat)
      (len := (Enc.encode child).size) (a := 8) he₂.2.2.1
      (by rw [show (Enc.encode child).size = 8 from LawfulEnc.size_encode (α := BitVec 64) _]; omega)
      (fun A h => by omega) (p := (⟨some 2, 0⟩ : Ptr).elem 8 s.local29)
      (by simp [Ptr.elem, Ptr.add])
    simp only [StateT.run_bind, bind_assoc]
    refine WP.bind (WP.liftM (fun e h => (MemM.noErr_of_run
      (storeBytes_run hacc hkk (noRace_b2 he₂.2.2.2.1 hcur₂)) e h).elim) fun _ m₃ hs₃ => ?_)
    obtain ⟨hc, hcur₃, hi₃⟩ := inv_spawn n hi₁ hg₁ hlt' hf hs₃ (by simp [Ptr.elem, Ptr.add])
    subst hc
    have he₃ := ex_handle (G := G₁)
      (G' := Conc.upd (Conc.upd G₁ (s.local29.toNat + 1) (.bump (ctxPtr s.local29.toNat) 0 false))
        0 (.main (s.local29.toNat + 1) [])) he₂ hg₁ (Conc.upd_self _ _ _) hlt' hcur₂
      (by obtain ⟨_, h⟩ := (fork_ok hf); rw [(fork_eq hf).2]; simp [hcs₁])
      (by rw [(fork_ok hf).2]; omega) (by simp [Ptr.elem, Ptr.add]) hs₃
    refine ⟨by obtain ⟨b, blk, o, -, -, rfl⟩ := Proto.store_ok hs₃; rfl, ?_⟩
    simp only [StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_get]
    refine WP.bind (WP.callRC (fun e h => (add_one_noErr (a := s.started)
      (by rw [hstarted]; omega) e h).elim) fun started' hstartedAdd => ?_)
    have hstartedNat : started'.toNat = s.local29.toNat + 1 := by
      rw [add_one_ok hstartedAdd (by rw [hstarted]; omega), hstarted]
    simp only [StateT.run_modify, StateT.run_pure, pure_bind, StateT.run_bind]
    refine WP.bind (WP.callRC (fun e h => (add_one_noErr (a := s.local29) (by omega) e h).elim)
      fun k' hadd => ?_)
    have hkn : k'.toNat = s.local29.toNat + 1 := add_one_ok hadd (by omega)
    simp only [StateT.run_modify, pure_bind]
    refine WP.pure' ?_
    simp only [parallelCounter.again32, ↓reduceIte]
    refine ⟨⟨BitVec.eq_of_toNat_eq (hstartedNat.trans hkn.symm),
      by show k'.toNat ≤ 4; omega, hcur₃, ?_, ?_⟩, .inl (by omega)⟩
    · show Inv n (Conc.upd _ 0 (.main k'.toNat [])) m₃
      rw [hkn, ctxPtr_elem]
      exact hi₃
    · show Ex (Conc.upd _ 0 (.main k'.toNat [])) m₃
      rw [hkn, ctxPtr_elem]
      exact he₃
  · rename_i hge
    have hge' : ¬ s.local29.toNat < 4 := by simpa [lt, BitVec.ult] using hge
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [parallelCounter.again32, Bool.false_eq_true, ↓reduceIte]
    have h4 : s.local29.toNat = 4 := by omega
    exact ⟨rfl, hcur, h4 ▸ hi, h4 ▸ he⟩

/-- `main`'s join keeps `Ex`. -/
theorem ex_join {G G' : ThreadId → Gh} {m m' : Mem} {tid : ThreadId} (he : Ex G m)
    (hG : G' 0 = G 0 ∨ ∃ s J J', G 0 = .main s J ∧ G' 0 = .main s J')
    (hcs : m.clocks.size = m.threads.size) (h0 : 0 < m.threads.size)
    (hj : ((Thread.join tid).run { m with current := 0 }).run = some (.ok ((), m'))) :
    Ex G' m' ∧ m'.current = 0 := by
  obtain ⟨rec, hrec, -, hm'⟩ := join_eq hj
  subst hm'
  obtain ⟨B0, B1, B2, hfp, hsp, s, J, hG0, hd⟩ := he
  have hcl0 : 0 < m.clocks.size := by omega
  have hs' : ∃ J', G' 0 = .main s J' := by
    rcases hG with h | ⟨s', J₁, J', h1, h2⟩
    · exact ⟨J, h.trans hG0⟩
    · rw [hG0] at h1; cases h1; exact ⟨J', h2⟩
  obtain ⟨J', hG'⟩ := hs'
  refine ⟨⟨B0, B1, B2, ?_, fun r hr => ?_, s, J', hG', hd⟩, rfl⟩
  · refine fpOk_step hfp (fun e he => .inl he) (fun u hu => ?_)
      (fun u h1 h2 => absurd h2 (by simp; omega)) h0
    show VClock.le _ ((m.clocks.set! 0 (VClock.merge (VClock.bump (m.clocks[0]!) 0)
      (m.clocks[tid]!)))[u]!) = true
    rw [getElem!_set! _ _ hcl0]
    split
    · subst_vars
      exact VClock.le_trans (VClock.le_bump _ _) (VClock.le_merge_left _ _)
    · exact VClock.le_refl _
  · simp only [Array.set!_eq_setIfInBounds] at hr
    rcases Array.mem_or_eq_of_mem_setIfInBounds hr with hr | rfl
    · exact hsp r hr
    · exact hsp rec (Array.mem_of_getElem? hrec)

/-- The invariant of `main`'s join loop: it joined `local85` threads (the list `J`). -/
def inv88 (s : parallelCounterLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  s.local85.toNat ≤ 4 ∧ m.current = 0 ∧
    ∃ J : List Nat, J.length = s.local85.toNat ∧ (∀ u ∈ J, u ≤ s.local85.toNat) ∧
      Inv n (Conc.upd G 0 (.main 4 J)) m ∧ Ex (Conc.upd G 0 (.main 4 J)) m

def post88 (r : parallelCounterExit × parallelCounterLocals) (G : ThreadId → Gh) (m : Mem)
    (_ : Nat) : Prop :=
  r.1 = .br87 ∧ m.current = 0 ∧ ∃ J : List Nat, J.length = 4 ∧
    Inv n (Conc.upd G 0 (.main 4 J)) m ∧ Ex (Conc.upd G 0 (.main 4 J)) m

theorem loop88_body (s : parallelCounterLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (h : inv88 n s G m d) :
    (proto n).WP 0 ((parallelCounter.loop88 ⟨some 2, 0⟩).run s) (fun r G' m' d' =>
      if parallelCounter.again88 r.1 then inv88 n r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun (_ : parallelCounterLocals) => 0) r.2 <
          (fun (_ : parallelCounterLocals) => 0) s)
      else post88 n r G' m' d') G m d := by
  obtain ⟨hle, hcur, J, hJl, hJle, hi, he⟩ := h
  have hnd : ∀ q, (Conc.upd G 0 (.main 4 J)) m.current ≠ .bump q n.toNat true := by
    rw [hcur, Conc.upd_self]; intro q h; cases h
  unfold parallelCounter.loop88
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rename_i hlt
    have hlt' : s.local85.toNat < 4 := by simpa [lt, BitVec.ult] using hlt
    simp only [StateT.run_bind, bind_assoc]
    have hsz : m.threads.size = 5 := by
      obtain ⟨s', J', hG', -, h, -⟩ := hi; rw [Conc.upd_self] at hG'; cases hG'; exact h
    have hcs : m.clocks.size = m.threads.size := by
      obtain ⟨s', J', hG', -, h1, h2, -⟩ := hi; rw [h1, h2]
    have hG4 : (Conc.upd G 0 (.main 4 J)) 0 = .main 4 J := Conc.upd_self _ _ _
    obtain ⟨-, -, B2, hfp, hsp, s', J', hG', hd⟩ := id he
    rw [hG4] at hG'; cases hG'
    obtain ⟨bk, hbk, -, hbs, hacc⟩ := access_blk (o := 8 * s.local85.toNat)
      (len := Enc.size ThreadId) (a := 8) B2 (by show _ + 8 ≤ 32; omega) (fun A h => by omega)
      (p := (⟨some 2, 0⟩ : Ptr).elem 8 s.local85) (by simp [Ptr.elem, Ptr.add])
    have hdec := hd bk hbk s.local85.toNat hlt'
    refine WP.bind (WP.callMC (fun e h => (MemM.noErr_of_run
      (load_run (v := s.local85.toNat + 1) hacc hdec (noRace_b2 hfp hcur)) e h).elim)
      fun tid m₁ hl => ?_)
    have hl' := hl
    rw [load_run (v := s.local85.toNat + 1) hacc hdec (noRace_b2 hfp hcur)] at hl'
    simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at hl'
    obtain ⟨rfl, rfl⟩ := hl'
    have hi₁ := inv_recordAt (b := 2) (o := 8 * s.local85.toNat) (len := Enc.size ThreadId)
      (k := .read) n hi hnd (by rw [hcur, hsz]; decide) (by decide)
    have he₁ := ex_recordAt (b := 2) (o := 8 * s.local85.toNat) (l := Enc.size ThreadId)
      (k := .read) (G := Conc.upd G 0 (.main 4 J)) he (.inr (.inr ⟨rfl, hcur⟩))
      (by rw [hcur, hsz]; decide) hcs
    refine ⟨rfl, ?_⟩
    refine WP.bind (WP.joinC fun k hk => ⟨.main 4 J, ⟨hi₁, he₁⟩,
      fun G₁ m₂ hg₁ hie₂ => ?_⟩)
    have hjoin : ∃ m', ((Thread.join (s.local85.toNat + 1)).run
        { m₂ with current := 0 }).run = some (.ok ((), m')) := by
      obtain ⟨hi₂, he₂⟩ := hie₂
      obtain ⟨s₂, J₂, hG₂, -, hsz₂, -, -, -, -, -, hjoined, -⟩ := hi₂
      rw [hg₁] at hG₂; cases hG₂
      have hlt₂ : s.local85.toNat + 1 < m₂.threads.size := by rw [hsz₂]; omega
      have hjf : (m₂.threads[s.local85.toNat + 1]).joined = false := by
        cases hjv : (m₂.threads[s.local85.toNat + 1]).joined
        · rfl
        · rcases hjoined _ hlt₂ hjv with h | h
          · omega
          · have := hJle _ h; omega
      exact Proto.join_run (rec := m₂.threads[s.local85.toNat + 1])
        (Array.getElem?_eq_getElem hlt₂) (he₂.2.2.2.2.1 _ (Array.getElem_mem hlt₂)) hjf
    refine ⟨fun _ => ?_, fun hfin => ⟨fun _ => hjoin, fun m' hj => ?_⟩⟩
    · obtain ⟨s₂, J₂, hG₂, -, hsz₂, -⟩ := hie₂.1
      rw [hg₁] at hG₂; cases hG₂
      obtain ⟨m', hj⟩ := hjoin
      exact ⟨Nat.succ_pos _, by rw [hsz₂]; unfold ThreadId at *; omega,
        trivial, Proto.join_valid hj⟩
    obtain ⟨hi₂, he₂⟩ := hie₂
    obtain ⟨p, hp⟩ := hfin
    obtain ⟨htJ, hcur', hi'⟩ := inv_join n hi₂ hg₁ ⟨p, hp⟩ hj
    have hcs₂ : m₂.clocks.size = m₂.threads.size := by
      obtain ⟨s₂, J₂, -, -, h1, h2, -⟩ := hi₂; rw [h1, h2]
    have hsz₂ : 0 < m₂.threads.size := by
      obtain ⟨s₂, J₂, -, -, h1, -⟩ := hi₂; rw [h1]; omega
    obtain ⟨he', -⟩ := ex_join (G' := Conc.upd G₁ 0 (.main 4 ((s.local85.toNat + 1) :: J)))
      he₂ (.inr ⟨4, J, _, hg₁, Conc.upd_self _ _ _⟩) hcs₂ hsz₂ hj
    simp only [StateT.run_pure, pure_bind, StateT.run_bind]
    refine WP.bind (WP.callRC (fun e h => (add_one_noErr (a := s.local85) (by omega) e h).elim)
      fun k' hadd => ?_)
    have hkn : k'.toNat = s.local85.toNat + 1 := add_one_ok hadd (by omega)
    simp only [StateT.run_modify, pure_bind]
    refine WP.pure' ?_
    simp only [parallelCounter.again88, ↓reduceIte]
    refine ⟨⟨by show k'.toNat ≤ 4; omega, hcur', (s.local85.toNat + 1) :: J, ?_, ?_, hi', he'⟩,
      .inl (by omega)⟩
    · show ((s.local85.toNat + 1) :: J).length = k'.toNat
      rw [hkn, List.length_cons, hJl]
    · intro u hu
      show u ≤ k'.toNat
      rw [hkn]
      rcases List.mem_cons.mp hu with rfl | hu
      · exact Nat.le_refl _
      · exact Nat.le_succ_of_le (hJle u hu)
  · rename_i hge
    have hge' : ¬ s.local85.toNat < 4 := by simpa [lt, BitVec.ult] using hge
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [parallelCounter.again88, Bool.false_eq_true, ↓reduceIte]
    exact ⟨rfl, hcur, J, by omega, hi, he⟩

/-- `Ex` depends on the ghost values only through `main`'s. -/
theorem ex_congr {G G' : ThreadId → Gh} {m : Mem} (h0 : G' 0 = G 0) (he : Ex G m) : Ex G' m := by
  obtain ⟨h0', h1, h2, hf, hsp, s, J, hG, hd⟩ := he
  exact ⟨h0', h1, h2, hf, hsp, s, J, h0.trans hG, hd⟩

/-- A kid spawned nothing: every thread was spawned by `main`. -/
theorem ex_joinedAll {G : ThreadId → Gh} {m : Mem} {u : ThreadId} (hu : u ≠ 0) (he : Ex G m) :
    joinedAll u m := by
  intro r hr hs
  have := he.2.2.2.2.1 r hr
  rw [this] at hs; exact absurd hs.symm hu

/-- A `bump` thread keeps the protocol. -/
theorem bump_spec (p : Ptr) (u : ThreadId) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hg : G u = .bump p 0 false) (hi : Inv n G m) (he : Ex G m) :
    (proto n).WP u (dispatch (.bump p)) ((proto n).QKid u) G { m with current := u } d := by
  show (proto n).WP u ((fun _ => ()) <$> bump p) _ G _ d
  refine WP.map ?_
  unfold bump
  refine WP.bind ?_
  show (proto n).WP u ((fun (r : bumpExit × bumpLocals) => r.1) <$> StateT.run _ default) _ G _ d
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_modify, pure_bind]
  have h0 : ((default : bumpLocals).i : BitVec 32) = default := rfl
  refine WP.bind (WP.mono ?_ (WP.loop (bump.loop4 p) bump.again4 (bumpInv n u p) (fun _ => 0)
    (bumpPost n u p) (fun s G m d h => bump_body n p u s G m d h) _ G _ d
    ⟨rfl, by simp, ?_⟩))
  · rintro ⟨e, s'⟩ G' m' d' ⟨hex, hc', hi', he'⟩
    simp only at hex
    subst hex
    have hu0 : u ≠ 0 := Nat.ne_of_gt (inv_kid n hi' (Conc.upd_self _ _ _)).1
    refine WP.pure' ?_
    refine WP.pure' ⟨_, ⟨inv_finish n hi',
      ex_congr (by rw [Conc.upd_ne _ _ (Ne.symm hu0), Conc.upd_ne _ _ (Ne.symm hu0)]) he'⟩,
      ⟨p, rfl⟩, fun _ => ex_joinedAll hu0 he'⟩
  · have : (Conc.upd G u (.bump p ({ (default : bumpLocals) with i := 0 } : bumpLocals).i.toNat false)) = G := by
      rw [show ({ (default : bumpLocals) with i := 0 } : bumpLocals).i.toNat = 0 from rfl, ← hg,
        upd_same]
    rw [this]; exact ⟨inv_current n hi, he⟩

/-- `main` keeps the protocol, and its result is `4 * n`. -/
theorem main_spec (σ : Placement) (d : Nat) :
    (proto n).WP 0 (parallelCounter n) (QM n) (fun u => if u = 0 then .main 0 [] else .none)
      { mem0 σ with current := 0 } d := by
  unfold parallelCounter
  have hpa0 : PreA { mem0 σ with current := 0 } := ⟨rfl, rfl, rfl, rfl, by simp [mem0, Mem.ofGlobals]⟩
  refine WP.bind (WP.liftMem (fun e h => (alloc_noErr e h).elim) fun s4 m₁ ha₁ => ?_)
  have hpa1 := preA_alloc hpa0 ha₁
  obtain ⟨rfl, hm₁⟩ := Proto.alloc_ok ha₁
  refine ⟨by rw [hm₁] <;> rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun e h => (alloc_noErr e h).elim) fun s1 m₂ ha₂ => ?_)
  have hpa2 := preA_alloc hpa1 ha₂
  obtain ⟨rfl, hm₂⟩ := Proto.alloc_ok ha₂
  refine ⟨by rw [hm₂] <;> rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun e h => (alloc_noErr e h).elim) fun s25 m₃ ha₃ => ?_)
  have hpa3 := preA_alloc hpa2 ha₃
  obtain ⟨rfl, hm₃⟩ := Proto.alloc_ok ha₃
  refine ⟨by rw [hm₃] <;> rfl, ?_⟩
  have e0 : ({ mem0 σ with current := 0 } : Mem).blocks.size = 0 := rfl
  have e1 : m₁.blocks.size = 1 := by rw [hm₁]; rfl
  have e2 : m₂.blocks.size = 2 := by rw [hm₂]; simp [Mem.afterAlloc, e1]
  -- The three blocks.
  have hpb3 : PreB m₃ := by
    subst hm₁ hm₂ hm₃
    refine ⟨by blkat_alloc, by blkat_alloc, by blkat_alloc, fun e he => ?_⟩
    simp [mem0, Mem.ofGlobals, Mem.afterAlloc] at he
  simp only [e0, e1, e2]
  refine WP.bind ?_
  show (proto n).WP 0 ((fun (r : parallelCounterExit × parallelCounterLocals) => r.1) <$>
    StateT.run _ _) _ _ _ _
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  have hinit : (atomic_Value_u32_init 0).run = some (.ok { raw := 0 }) := rfl
  refine WP.bind (WP.callRC (fun e h => by rw [hinit] at h; cases h) fun a ha => ?_)
  rw [hinit] at ha; simp only [Option.some.injEq, Except.ok.injEq] at ha; subst ha
  -- The counter's store: its bytes read 0.
  have e4 : (Enc.encode ({ raw := 0 } : atomic_Value_u32)).size = 4 := by decide +kernel
  have e4' : (Enc.encode ({ raw := 0#32 } : atomic_Value_u32)).size = 4 := e4
  obtain ⟨bk4, hbk4, hk4, hs4, hacc4⟩ := access_blk (o := 0)
    (len := (Enc.encode ({ raw := 0 } : atomic_Value_u32)).size) (a := 4) hpb3.2.1
    (by simp [e4']) (fun A h => by omega) (p := ⟨some 1, 0⟩) rfl
  refine WP.bind (WP.liftM (fun e h => (store_noErr_pre hpa3 hacc4 hk4 e h).elim)
    fun _ m₄ hs₄ => ?_)
  obtain ⟨b, blk, o, ha₄, -, hm₄⟩ := Proto.store_ok hs₄
  obtain ⟨hb, hblk, -, -, hsz, -, ho⟩ := access_eq ha₄
  simp only [Option.some.injEq] at hb; subst hb
  simp only at ho; subst ho
  have hpa4 : PreA m₄ := hm₄ ▸ preA_write (preA_recordAt hpa3)
  have hpb4 : PreB m₄ := hm₄ ▸ preB_store hpb3 hblk (by simp [e4'] at hsz; rw [e4]; omega)
    (.inr (.inl rfl))
  have hc4 : (intOfBytes 32 (Proto.curBytes m₄ 1 0 4)).run = some (.ok 0) := by
    have hv : (intOfBytes 32 (Enc.encode ({ raw := 0 } : atomic_Value_u32))).run =
        some (.ok 0) := by
      rw [show Enc.encode ({ raw := 0 } : atomic_Value_u32) = Enc.encode (0 : BitVec 32) by
        decide +kernel]
      exact congrArg ExceptT.run (LawfulEnc.decode_encode (α := BitVec 32) 0)
    have hb1 : 1 < m₃.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
    rw [hm₄]
    simp only [Proto.curBytes, Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_self_of_lt hb1, Option.map_some, Option.getD_some]
    simp only [e4] at hsz
    have := extract_writeBytes blk.bytes 0 (Enc.encode ({ raw := 0 } : atomic_Value_u32))
      (by rw [e4]; simp at hsz; omega)
    rw [e4] at this; simp only [Nat.zero_add] at this
    rw [show (0 : Int).toNat = 0 from rfl, this]; exact hv
  refine ⟨by rw [hm₄]; rfl, ?_⟩
  -- The contexts' `storeUndef`.
  have e64 : (Array.replicate (Enc.size (Vector CounterCtx 4)) Byte.undef).size = 64 := by
    simp; rfl
  obtain ⟨bk5, hbk5, hk5, -, hacc5⟩ := access_blk (o := 0)
    (len := (Array.replicate (Enc.size (Vector CounterCtx 4)) Byte.undef).size) (a := 8) hpb4.1
    (by simp [e64]) (fun A h => by omega) (p := ⟨some 0, 0⟩) rfl
  refine WP.bind (WP.liftM (fun e h => (store_noErr_pre hpa4 hacc5 hk5 e h).elim)
    fun _ m₅ hs₅ => ?_)
  obtain ⟨b5, blk5, o5, ha₅, -, hm₅⟩ := Proto.storeUndef_ok hs₅
  obtain ⟨hb5, hblk5, -, -, hsz5, -, ho5⟩ := access_eq ha₅
  simp only [Option.some.injEq] at hb5; subst hb5
  simp only at ho5; subst ho5
  have hpa5 : PreA m₅ := hm₅ ▸ preA_write (preA_recordAt hpa4)
  have hpb5 : PreB m₅ := by
    rw [hm₅]
    have := preB_store (o := 0) (bs := Array.replicate (Enc.size (Vector CounterCtx 4)) Byte.undef)
      hpb4 hblk5 (by rw [e64]; simp at hsz5 ⊢; omega) (.inl rfl)
    simpa using this
  have hc5 : (intOfBytes 32 (Proto.curBytes m₅ 1 0 4)).run = some (.ok 0) := by
    rw [hm₅, curBytes_write (by omega), curBytes_recordAt]; exact hc4
  refine ⟨by rw [hm₅]; rfl, ?_⟩
  simp only [StateT.run_modify, pure_bind]
  -- The first loop fills the 4 contexts.
  refine WP.bind (WP.mono (fun r G' m' d' hp => ?_) (WP.loop _ _ (inv9 n)
    (fun x => 4 - x.local6.toNat) (post9 n) (fun s G m d h => loop9_body n s G m d h) _ _ _ _
    ⟨rfl, by simp, rfl, hpa5, hpb5, hc5, fun blk _ k hk => by simp at hk⟩))
  obtain ⟨hr, rfl, hhd, hpa6, hpb6, hc6, hsl6⟩ := hp
  obtain ⟨e, s₁⟩ := r
  simp only at hr hhd
  subst hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hhd]
  -- The handles' `storeUndef`, then the invariant holds.
  have e32 : (Array.replicate (Enc.size (Vector ThreadId 4)) Byte.undef).size = 32 := by
    simp; rfl
  obtain ⟨bk7, hbk7, hk7, -, hacc7⟩ := access_blk (o := 0)
    (len := (Array.replicate (Enc.size (Vector ThreadId 4)) Byte.undef).size) (a := 8)
    hpb6.2.2.1 (by simp [e32]) (fun A h => by omega) (p := ⟨some 2, 0⟩) rfl
  refine WP.bind (WP.liftM (fun e h => (store_noErr_pre hpa6 hacc7 hk7 e h).elim)
    fun _ m₇ hs₇ => ?_)
  obtain ⟨b7, blk7, o7, ha₇, -, hm₇⟩ := Proto.storeUndef_ok hs₇
  obtain ⟨hb7, hblk7, -, -, hsz7, -, ho7⟩ := access_eq ha₇
  simp only [Option.some.injEq] at hb7; subst hb7
  simp only at ho7; subst ho7
  have hpa7 : PreA m₇ := hm₇ ▸ preA_write (preA_recordAt hpa6)
  have hpb7 : PreB m₇ := by
    rw [hm₇]
    have := preB_store (o := 0) (bs := Array.replicate (Enc.size (Vector ThreadId 4)) Byte.undef)
      hpb6 hblk7 (by rw [e32]; simp at hsz7 ⊢; omega) (.inr (.inr rfl))
    simpa using this
  have hi₇ : Inv n G0 m₇ := by
    refine inv_start n hpa7 ?_ ?_
    · rw [hm₇, curBytes_write (by omega), curBytes_recordAt]; exact hc6
    · intro blk hb k hk
      rw [hm₇] at hb
      simp only [Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_ne (show (2 : Nat) ≠ 0 by omega)] at hb
      exact hsl6 blk hb k hk
  have he₇ : Ex G0 m₇ := ex_start hpa7 hpb7
  refine ⟨by rw [hm₇]; rfl, ?_⟩
  simp only [StateT.run_modify, pure_bind]
  -- The spawn loop.
  have hG0 : Conc.upd G0 0 (.main 0 []) = G0 := by
    funext u; by_cases hu : u = 0
    · subst hu; simp [Conc.upd, G0]
    · simp [Conc.upd, hu]
  refine WP.bind (WP.mono (fun r G' m' d' hp => ?_) (WP.loop _ _ (inv32 n)
    (fun _ => 0) (post32 n) (fun s G m d h => loop32_body n s G m d h) _ _ _ _
    ⟨rfl, by simp, hpa7.cur, by simpa [hG0] using hi₇, by simpa [hG0] using he₇⟩))
  obtain ⟨hr, hcur8, hi₈, he₈⟩ := hp
  obtain ⟨e, s₂⟩ := r
  simp only at hr; subst hr
  simp only [StateT.run_bind, StateT.run_modify, pure_bind]
  -- The join loop.
  refine WP.bind (WP.mono (fun r G' m' d' hp => ?_) (WP.loop _ _ (inv88 n)
    (fun _ => 0) (post88 n) (fun s G m d h => loop88_body n s G m d h) _ _ _ _
    ⟨by simp, hcur8, [], rfl, by simp, hi₈, he₈⟩))
  obtain ⟨hr, hcur9, J, hJ4, hi₉, he₉⟩ := hp
  obtain ⟨e, s₃⟩ := r
  simp only at hr; subst hr
  simp only [atomicLoadC, StateT.run_bind, bind_assoc, ptr_add_zero]
  -- The load after the joins.
  refine WP.bind (WP.pickC fun k hk => ⟨.main 4 J, ⟨hi₉, he₉⟩,
    fun G₁ m₁ hg₁ hie₁ c hcr => ?_⟩)
  obtain ⟨hi₁, he₁⟩ := hie₁
  have hi₁' := inv_current (u := 0) n hi₁
  have he₁' : Ex G₁ { m₁ with current := 0 } := he₁
  refine WP.bind (WP.callMC (fun e h => (final_noErr n hi₁' he₁' hg₁ hJ4 rfl hcr e h).elim)
    fun v m₂ hl => ?_)
  obtain ⟨hv, hth₂, hbl₂⟩ := final_load n hi₁' hg₁ hJ4 rfl hl
  refine ⟨by rw [hth₂], ?_⟩
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  simp only
  -- The frees: the blocks are live; the threads do not change.
  have hjd : joinedAll 0 m₂ := by
    intro r hr; rw [hth₂] at hr; exact joined_final n hi₁' hg₁ hJ4 r hr
  obtain ⟨⟨f0, hf0, hl0, -⟩, ⟨f1, hf1, hl1, -⟩, ⟨f2, hf2, hl2, -⟩, -⟩ := he₁'
  rw [← hbl₂] at hf0 hf1 hf2
  refine WP.bind (WP.liftMem (fun e h => (free_noErr hf0 hl0 e h).elim) fun x m₃ hf => ?_)
  obtain ⟨b, blk, hb, hblk, rfl⟩ := Proto.free_ok hf
  simp only [Option.some.injEq] at hb; subst hb
  refine ⟨rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun e h => (free_noErr (blk := f1)
    (by simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, hf1]) hl1 e h).elim)
    fun x m₄ hf => ?_)
  obtain ⟨b, blk', hb, hblk', rfl⟩ := Proto.free_ok hf
  simp only [Option.some.injEq] at hb; subst hb
  refine ⟨rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun e h => (free_noErr (blk := f2)
    (by simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, hf2]) hl2 e h).elim)
    fun x m₅ hf => ?_)
  obtain ⟨b, blk'', hb, hblk'', rfl⟩ := Proto.free_ok hf
  refine ⟨rfl, ?_⟩
  refine WP.pure' ⟨?_, hjd⟩
  show Except.ok v = Except.ok (4 * n)
  rw [hv]
  congr 1

theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : (proto n).init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (_ : 0 < u) (hgu : G u = g) (hi : (proto n).inv G m) :
    (proto n).WP u (dispatch tgt) ((proto n).QKid u) G { m with current := u } d := by
  cases tgt with
  | bump p =>
    cases hg
    exact bump_spec n p u G m d hgu hi.1 hi.2
  | _ => cases hg

/-- **`parallelCounter n` gives `4 * n` under every schedule** (every oracle `o`, every
`fuel`). -/
theorem parallelCounter_spec {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)}
    {m : Mem} (h : (Sched.run dispatch fuel o (parallelCounter n) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok (4 * n) := by
  obtain ⟨_, _, hv, -⟩ := (proto n).run_sound dispatch (fun u => if u = 0 then .main 0 [] else .none)
    (dispatch_spec n) (fun _ _ _ _ _ hq => hq.2) rfl
    (main_spec n σ) h
  exact hv

/-- **No run of `parallelCounter n` gives an error**, under any schedule: no data race, no
deadlock, no overflow, no other illegal behaviour. -/
theorem parallelCounter_safe {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} :
    (Sched.run dispatch fuel o (parallelCounter n) (mem0 σ)).run ≠ some (.error e) :=
  (proto n).run_safe dispatch (fun u => if u = 0 then .main 0 [] else .none) rfl
    (dispatch_spec n) (fun _ _ _ _ hq => hq.2) rfl
    (main_spec n σ)

/-- One schedule completes: under the oracle that always picks option 0, `parallelCounter 1` returns 4 within
fuel 1000, from `mem0` with the translation's spawn policy. The kernel computes the run, with
each loop cut after 10 iterations (`unroll_sched`, `ZigLean/Conc/Unroll.lean`). -/
theorem parallelCounter_completes :
    ∃ σ, Witness.okVal (Sched.run dispatch 1000 (fun _ => 0) (parallelCounter 1) (mem0 σ)) = some 4 :=
  ⟨.fresh, by unroll_sched 10⟩

/-! ## Non-vacuity witnesses -/

/-- The counter's location with its first message, `0`, as `main` leaves it before the
spawns. -/
def cntLoc : ALoc :=
  { block := 1, off := 0, len := 4,
    msgs := #[{ id := 0, bytes := Enc.encode (0 : BitVec 32), clock := #[], relClock := #[] }] }

/-- A memory whose block 1 is the counter, `0`, with its atomic location. -/
def cntMem : Mem :=
  { blocks := #[Witness.blk #[], { Witness.blk (Enc.encode (0 : BitVec 32)) with addr := 8192 }],
    atomics := #[cntLoc] }

theorem cntAt_cntMem : CntAt 0 0 cntMem where
  find := by decide +kernel
  only := fun l hl _ => by simp [cntMem] at hl; subst hl; exact ⟨rfl, rfl⟩
  size := rfl
  chain := fun j h => by simp [cntMem, cntLoc] at h
  val := fun j h => by
    simp [cntMem, cntLoc] at h; subst h; with_unfolding_all rfl
  last := by decide +kernel
  clk := fun j h => by
    simp [cntMem, cntLoc] at h; subst h; exact ⟨0, by decide, by with_unfolding_all rfl⟩
  plain := fun e he => by simp [cntMem] at he
  pw := fun e he => by simp [cntMem] at he

nonvacuity_witness CntAt.val := ⟨0, 0, cntMem, cntAt_cntMem, 0, by decide +kernel, trivial⟩
nonvacuity_witness decode_tid := ⟨0, by decide, trivial⟩

end Threads.Counter
