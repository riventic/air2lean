import ZigLean.Conc.WeakCasLemmas
import Proofs.Atomics.MessagePassing
import ZigLean.Mem.Witness

/-!
# `stackPush` over all schedules: a lock-free stack

`stackPush` spawns two pushers. Pusher `u` (thread `u`, node `u`) reads the head with
`.monotonic`, then loops: it writes `next[u] := h` (a plain write), and a `cmpxchgWeak` (release,
failure relaxed) sets the head from `h` to `u`; on failure `h` is the value read. After both
joins `main` reads the head with `.acquire` and gives `100 * top + 10 * next[top] +
next[next[top]]`. The result is 120 or 210 under every schedule (`stackPush_spec`), and no
schedule gives an error (`stackPush_safe`).

**Protocol.** A pusher's ghost value (`Gh`): `start u`, then `cas h` at its `cmpxchg` (it wrote
`next[u] := h`), then `done`. `main`: `pre`, `mid` (between its spawns), `j1`, `j2` (at its joins),
`ld` (at the load of the head). The invariant (`Inv`):

- The head is one atomic location whose messages are an RMW chain (`ALoc.Chain`), so a
  `cmpxchg` that succeeds reads the newest message. The values of the messages are one of
  `Chains`: 0, then the nodes in the order of their push. A pusher is `done` exactly when its
  node is on the stack, and `next[v]` holds the value before `v` (`HeadLoc`).
- **No data race.** Each pusher writes only its `next[u]`; `main` reads `next` only after both
  joins, and its clock is then above both pushers' clocks (`JoinLe`). The head's messages are
  below their pusher's clock, so the acquire load after the joins reads the newest message.

The end of `main` has two translations: 0.16.0 reads `next[k]` through a pointer into the
`Stack`; 0.15.2 loads the whole `Stack` and indexes its `next`. `main_spec` has a branch for each.
-/

open Zig Zig.Conc Zig.Conc.Proto Atomics

namespace Atomics.Stack

/-- A thread's ghost value. -/
inductive Gh where
  | none
  /-- `main` before its first spawn. -/
  | pre
  /-- `main` at its second spawn. -/
  | mid
  /-- `main` at the join of pusher 1. -/
  | j1
  /-- `main` at the join of pusher 2. -/
  | j2
  /-- `main` at the load of the head. -/
  | ld
  /-- Pusher `u` at its relaxed load of the head. -/
  | start (u : Nat)
  /-- A pusher at its `cmpxchg`, which expects `h`; it wrote `next[u] := h`. -/
  | cas (h : BitVec 32)
  /-- A pusher that ended: its node is on the stack. -/
  | done
  deriving DecidableEq

/-- Thread `u` is pusher `u`. -/
def Kid (u : Nat) (g : Gh) : Prop := g = .start u ∨ (∃ h, g = .cas h) ∨ g = .done

/-- The `Stack` (block 0): the head at bytes `0..4`, `next[k]` at `4 + 4k`. -/
def sPtr : Ptr := ⟨some 0, 0⟩

/-- The `PushCtx` of pusher `u` (block `u`): `s` at bytes `0..8`, `node` at `8..12`. -/
def cPtr (u : Nat) : Ptr := ⟨some u, 0⟩

/-- The bytes `o..o+4` of block `b` hold the `u32` `v`. -/
def U32At (m : Mem) (b o : Nat) (v : BitVec 32) : Prop :=
  (intOfBytes 32 (curBytes m b o 4)).run = some (.ok v)

/-- Message `msg` holds the `u32` `v`. -/
def Val (msg : Msg) (v : BitVec 32) : Prop := (intOfBytes 32 msg.bytes).run = some (.ok v)

/-- `next[k]` holds `v`. -/
def NextAt (m : Mem) (k : Nat) (v : BitVec 32) : Prop := U32At m 0 (4 + 4 * k) v

/-- The values of the head's messages, oldest first: 0, then the nodes in the order of their
push. -/
def Chains : List (List Nat) := [[0], [0, 1], [0, 2], [0, 1, 2], [0, 2, 1]]

/-- The head's atomic location (see the module doc). -/
def HeadLoc (G : ThreadId → Gh) (m : Mem) (l : ALoc) : Prop :=
  l.block = 0 ∧ l.off = 0 ∧ l.len = 4 ∧ ALoc.lastBytes l = curBytes m 0 0 4 ∧
  PlainLe m 0 0 4 l.lastClock ∧ l.Chain ∧
  ∃ vs ∈ Chains, l.msgs.size = vs.length ∧
    (∀ j (h : j < l.msgs.size), Val l.msgs[j] (BitVec.ofNat 32 vs[j]!)) ∧
    (∀ u, (u = 1 ∨ u = 2) → (G u = .done ↔ u ∈ vs)) ∧
    (∀ j, j + 1 < vs.length → NextAt m vs[j + 1]! (BitVec.ofNat 32 vs[j]!)) ∧
    (∀ j (h : j + 1 < l.msgs.size), VClock.le l.msgs[j + 1].clock (m.clocks[vs[j + 1]!]!) = true)

/-- No atomic location yet (the head holds 0, no pusher is done), or the head's. -/
def HeadOk (G : ThreadId → Gh) (m : Mem) : Prop :=
  (m.atomics = #[] ∧ U32At m 0 0 0 ∧ ∀ u, (u = 1 ∨ u = 2) → G u ≠ .done) ∨
  ∃ l, m.atomics = #[l] ∧ HeadLoc G m l

/-- A footprint entry: a write that happened before every thread; an atomic access to the head;
pusher `u`'s write of `next[u]`; `main`'s read of the `Stack` after both joins; a read of a
`PushCtx`. -/
def FpOk (G : ThreadId → Gh) (m : Mem) (e : FootprintEntry) : Prop :=
  (e.kind = .write ∧ Before m e.clock) ∨
  (e.block = 0 ∧ e.off = 0 ∧ e.len ≤ 4 ∧ e.kind.isAtomic = true) ∨
  (e.block = 0 ∧ e.kind = .write ∧ (e.tid = 1 ∨ e.tid = 2) ∧ e.off = 4 + 4 * e.tid ∧ e.len = 4) ∨
  (e.block = 0 ∧ e.kind = .read ∧ e.tid = 0 ∧ G 0 = .ld) ∨
  ((e.block = 1 ∨ e.block = 2) ∧ e.kind = .read)

/-- The threads: `main` alone; then pusher 1; then pusher 2; `main` joins them in order. -/
def ThrOk (G : ThreadId → Gh) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧ m.clocks.size = m.threads.size ∧
  ((m.threads.size = 1 ∧ G 0 = .pre ∧ ∀ u, 1 ≤ u → G u = .none) ∨
   (m.threads.size = 2 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧ G 0 = .mid ∧
    Kid 1 (G 1) ∧ ∀ u, 2 ≤ u → G u = .none) ∨
   (m.threads.size = 3 ∧ Kid 1 (G 1) ∧ Kid 2 (G 2) ∧ (∀ u, 3 ≤ u → G u = .none) ∧
    ((G 0 = .j1 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
        m.threads[2]? = some { spawner := 0, joined := false }) ∨
     (G 0 = .j2 ∧ G 1 = .done ∧ m.threads[1]? = some { spawner := 0, joined := true } ∧
        m.threads[2]? = some { spawner := 0, joined := false }) ∨
     (G 0 = .ld ∧ G 1 = .done ∧ G 2 = .done ∧ m.threads[1]? = some { spawner := 0, joined := true } ∧
        m.threads[2]? = some { spawner := 0, joined := true }))))

/-- After a join, `main`'s clock is above the pusher's. -/
def JoinLe (G : ThreadId → Gh) (m : Mem) : Prop :=
  (G 0 = .j2 ∨ G 0 = .ld → VClock.le (m.clocks[1]!) (m.clocks[0]!) = true) ∧
  (G 0 = .ld → VClock.le (m.clocks[2]!) (m.clocks[0]!) = true)

/-- The invariant (see the module doc). -/
structure Inv (G : ThreadId → Gh) (m : Mem) : Prop where
  thr : ThrOk G m
  b0 : BlkAt m 0 16 4
  b1 : BlkAt m 1 16 8
  b2 : BlkAt m 2 16 8
  ctx : ∀ u, (u = 1 ∨ u = 2) → curBytes m u 0 8 = Enc.encode sPtr ∧ U32At m u 8 (BitVec.ofNat 32 u)
  head : HeadOk G m
  casn : ∀ u h, (u = 1 ∨ u = 2) → G u = .cas h → NextAt m u h
  n0 : NextAt m 0 0
  join : JoinLe G m
  fp : ∀ e ∈ m.footprint, FpOk G m e
  own : ∀ e ∈ m.footprint, e.tid < m.threads.size ∧ VClock.le e.clock (m.clocks[e.tid]!) = true

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv := Inv
  init tgt g := (match tgt with
      | .push p => if p = cPtr 1 then some (.start 1) else if p = cPtr 2 then some (.start 2) else none
      | _ => none) = some g
  fin g := g = .done
  strict := true
  joins g := g = .j1 ∨ g = .j2

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => (v = .ok 120 ∨ v = .ok 210) ∧ joinedAll 0 m

/-! ## Frame -/

/-- The thread that runs a step: `main`, or a pusher that is not `done`. -/
def Act (G : ThreadId → Gh) (t : ThreadId) : Prop := t = 0 ∨ ((t = 1 ∨ t = 2) ∧ G t ≠ .done)

/-- `m'` is `m` with the clock of thread `t` not smaller, and the other clocks the same. -/
structure GrowsAt (m m' : Mem) (t : ThreadId) : Prop where
  grows : Grows m m'
  same : ∀ u, u ≠ t → m'.clocks[u]! = m.clocks[u]!

theorem JoinLe.grow {G : ThreadId → Gh} {m m' : Mem} {t : ThreadId} (h : JoinLe G m)
    (hg : GrowsAt m m' t) (ht : Act G t) (hthr : ThrOk G m) : JoinLe G m' := by
  have hd : ∀ u, G u = .done → m'.clocks[u]! = m.clocks[u]! := fun u hu => by
    refine hg.same u fun hut => ?_
    subst hut
    rcases ht with rfl | ⟨-, hn⟩
    · obtain ⟨-, -, ⟨-, hp, -⟩ | ⟨-, -, hp, -⟩ | ⟨-, -, -, -, h0⟩⟩ := hthr
      · rw [hp] at hu; cases hu
      · rw [hp] at hu; cases hu
      · rcases h0 with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩ <;> rw [hp] at hu <;> cases hu
    · exact hn hu
  have h1 : G 0 = .j2 ∨ G 0 = .ld → G 1 = .done := fun h0 => by
    obtain ⟨-, -, ⟨-, hp, -⟩ | ⟨-, -, hp, -⟩ | ⟨-, -, -, -, hh⟩⟩ := hthr
    · rcases h0 with h0 | h0 <;> rw [hp] at h0 <;> cases h0
    · rcases h0 with h0 | h0 <;> rw [hp] at h0 <;> cases h0
    · rcases hh with ⟨hp, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩
      · rcases h0 with h0 | h0 <;> rw [hp] at h0 <;> cases h0
      · exact h1
      · exact h1
  have h2 : G 0 = .ld → G 2 = .done := fun h0 => by
    obtain ⟨-, -, ⟨-, hp, -⟩ | ⟨-, -, hp, -⟩ | ⟨-, -, -, -, hh⟩⟩ := hthr
    · rw [hp] at h0; cases h0
    · rw [hp] at h0; cases h0
    · rcases hh with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨-, -, h2, -⟩
      · rw [hp] at h0; cases h0
      · rw [hp] at h0; cases h0
      · exact h2
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · rw [hd 1 (h1 h0)]; exact VClock.le_trans (h.1 h0) (hg.grows.cle 0)
  · rw [hd 2 (h2 h0)]; exact VClock.le_trans (h.2 h0) (hg.grows.cle 0)

theorem Inv.grow {G : ThreadId → Gh} {m m' : Mem} {t : ThreadId} (hi : Inv G m) (hg : GrowsAt m m' t)
    (ht : Act G t) : Inv G m' where
  thr := by unfold ThrOk; rw [hg.grows.threads, hg.grows.csize]; exact hi.thr
  b0 := hi.b0.congr hg.grows.blocks
  b1 := hi.b1.congr hg.grows.blocks
  b2 := hi.b2.congr hg.grows.blocks
  ctx := by intro u hu; unfold U32At; rw [curBytes_congr hg.grows.blocks, curBytes_congr hg.grows.blocks]; exact hi.ctx u hu
  head := by
    rcases hi.head with ⟨ha, hu, hn⟩ | ⟨l, ha, hlb, hlo, hll, hlast, hpl, hc, vs, hvs, hsz, hv, hd, hnx, hcl⟩
    · exact .inl ⟨hg.grows.atomics ▸ ha, by unfold U32At; rw [curBytes_congr hg.grows.blocks]; exact hu, hn⟩
    · refine .inr ⟨l, hg.grows.atomics ▸ ha, hlb, hlo, hll, by rw [curBytes_congr hg.grows.blocks]; exact hlast,
        by unfold PlainLe; rw [hg.grows.footprint]; exact hpl, hc, vs, hvs, hsz, hv, hd, fun j hj => ?_, fun j hj => VClock.le_trans (hcl j hj) (hg.grows.cle _)⟩
      unfold NextAt U32At; rw [curBytes_congr hg.grows.blocks]; exact hnx j hj
  casn := fun u h hu hc => by unfold NextAt U32At; rw [curBytes_congr hg.grows.blocks]; exact hi.casn u h hu hc
  n0 := by unfold NextAt U32At; rw [curBytes_congr hg.grows.blocks]; exact hi.n0
  join := hi.join.grow hg ht hi.thr
  fp := by
    intro e he
    rw [hg.grows.footprint] at he
    rcases hi.fp e he with ⟨hk, hb⟩ | h | h | h | h
    · exact .inl ⟨hk, before_grow hg.grows hb⟩
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr h)))
  own := by
    intro e he
    rw [hg.grows.footprint] at he
    obtain ⟨h1, h2⟩ := hi.own e he
    exact ⟨hg.grows.threads ▸ h1, VClock.le_trans h2 (hg.grows.cle _)⟩

theorem growsAt_current (m : Mem) (u : ThreadId) : GrowsAt m { m with current := u } u :=
  ⟨grows_current m u, fun _ _ => rfl⟩

/-- A race-free access by the current thread: its clock is bumped and the entry recorded. -/
theorem Inv.record {G : ThreadId → Gh} {m : Mem} {b o len : Nat} {k : AccessKind} (hi : Inv G m)
    (ht : m.current < m.threads.size) (ha : Act G m.current) (hn0 : b = 0 → k = .write → 4 ≤ o)
    (hf : FpOk G (m.recordAt b o len k)
      { tid := m.current, clock := VClock.bump (m.clocks[m.current]!) m.current, block := b,
        off := o, len := len, kind := k }) :
    Inv G (m.recordAt b o len k) := by
  have hcs : m.current < m.clocks.size := by rw [hi.thr.2.1]; exact ht
  let m₁ : Mem := { m with clocks := m.clocks.set! m.current (VClock.bump (m.clocks[m.current]!) m.current) }
  have hg : GrowsAt m m₁ m.current := by
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, by simp [m₁], fun u => ?_⟩, fun u hu => ?_⟩
    · simp only [m₁]
      rw [getElem!_set!_ite]
      split
      · rename_i h; rw [h.1]; exact VClock.le_bump _ _
      · exact VClock.le_refl _
    · simp only [m₁]
      rw [getElem!_set!_ite]
      simp [hu]
  have hi₁ := hi.grow hg ha
  have hcur : (m.recordAt b o len k).clocks[m.current]! = VClock.bump (m.clocks[m.current]!) m.current := by
    simp only [Mem.recordAt]; rw [getElem!_set!_ite]; simp [hcs]
  have hpf : ∀ e ∈ (m.recordAt b o len k).footprint, e ∈ m₁.footprint ∨ plainHit 0 0 4 e = false := by
    intro e he
    simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · refine .inr ?_
      cases hp : plainHit 0 0 4 _
      · rfl
      · have h4 := hn0 (plainHit_block hp) (plainHit_kind hp)
        unfold plainHit at hp
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
        omega
  have hhead : HeadOk G (m.recordAt b o len k) := by
    rcases hi₁.head with h | ⟨l, ha, hlb, hlo, hll, hlast, hpl, hrest⟩
    · exact .inl h
    · exact .inr ⟨l, ha, hlb, hlo, hll, hlast, hpl.of_fp hpf, hrest⟩
  exact {
    thr := hi₁.thr, b0 := hi₁.b0, b1 := hi₁.b1, b2 := hi₁.b2, ctx := hi₁.ctx, head := hhead
    casn := hi₁.casn, n0 := hi₁.n0, join := hi₁.join
    fp := by
      intro e he
      simp only [Mem.recordAt, Array.mem_push] at he
      rcases he with he | rfl
      · exact hi₁.fp e he
      · exact hf
    own := by
      intro e he
      simp only [Mem.recordAt, Array.mem_push] at he
      rcases he with he | rfl
      · exact hi₁.own e he
      · exact ⟨ht, by rw [hcur]; exact VClock.le_refl _⟩ }

/-- The race check of an access by the current thread to block `b`: each entry of `b` is a write
before every thread, happened before the thread, or does not race by its kind. -/
theorem noRace_inv {G : ThreadId → Gh} {m : Mem} {b o len : Nat} {k : AccessKind} (hi : Inv G m)
    (ht : m.current < m.threads.size)
    (h : ∀ e ∈ m.footprint, e.block = b → o < e.off + e.len → e.off < o + len → FpOk G m e →
      (e.kind = .write ∧ Before m e.clock) ∨ VClock.le e.clock (m.clocks[m.current]!) = true ∨
        racePair e.kind k = none) :
    NoRace m b o len k :=
  noRace_of fun e he hb h1 h2 => by
    rcases h e he hb h1 h2 (hi.fp e he) with ⟨-, hle⟩ | h | h
    · exact .inl (hle _ ht)
    · exact .inl h
    · exact .inr h

/-- A pusher: thread 1 or 2, one of the threads. -/
theorem thr_kid {G : ThreadId → Gh} {m : Mem} {u : ThreadId} (h : ThrOk G m)
    (hg : G u = .done ∨ (∃ v, G u = .start v) ∨ ∃ x, G u = .cas x) :
    (u = 1 ∨ u = 2) ∧ u < m.threads.size ∧ Kid u (G u) := by
  have hnk : ∀ g : Gh, g = .none ∨ g = .pre ∨ g = .mid ∨ g = .j1 ∨ g = .j2 ∨ g = .ld →
      (g = .done ∨ (∃ v, g = .start v) ∨ ∃ x, g = .cas x) → False := by
    intro g h1 h2
    rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases h2 with h2 | ⟨_, h2⟩ | ⟨_, h2⟩ <;> cases h2
  obtain ⟨-, -, ⟨hs, h0, hn⟩ | ⟨hs, -, h0, k1, hn⟩ | ⟨hs, k1, k2, hn, h0⟩⟩ := h
  · by_cases hu : u = 0
    · subst hu; exact (hnk _ (.inr (.inl h0)) hg).elim
    · exact (hnk _ (.inl (hn u (by unfold ThreadId at *; omega))) hg).elim
  · by_cases hu : u = 0
    · subst hu; exact (hnk _ (.inr (.inr (.inl h0))) hg).elim
    · by_cases hu1 : u = 1
      · subst hu1; exact ⟨.inl rfl, by rw [hs]; decide, k1⟩
      · exact (hnk _ (.inl (hn u (by unfold ThreadId at *; omega))) hg).elim
  · by_cases hu : u = 0
    · subst hu
      rcases h0 with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact (hnk _ (.inr (.inr (.inr (.inl h0)))) hg).elim
      · exact (hnk _ (.inr (.inr (.inr (.inr (.inl h0))))) hg).elim
      · exact (hnk _ (.inr (.inr (.inr (.inr (.inr h0))))) hg).elim
    · by_cases hu1 : u = 1
      · subst hu1; exact ⟨.inl rfl, by rw [hs]; decide, k1⟩
      · by_cases hu2 : u = 2
        · subst hu2; exact ⟨.inr rfl, by rw [hs]; decide, k2⟩
        · exact (hnk _ (.inl (hn u (by unfold ThreadId at *; omega))) hg).elim

/-- A change of a pusher's ghost value keeps `ThrOk`, if it stays a pusher's and does not undo
`done`. -/
theorem thr_upd_kid {G : ThreadId → Gh} {m m' : Mem} {u : ThreadId} {g : Gh} (h : ThrOk G m)
    (ht : m'.threads = m.threads) (hc : m'.clocks.size = m.clocks.size) (hu : u = 1 ∨ u = 2)
    (hk0 : Kid u (G u)) (hk : Kid u g) (hd : G u = .done → g = .done) : ThrOk (upd G u g) m' := by
  have hnk : ¬ Kid u .none := by rintro (h | ⟨_, h⟩ | h) <;> cases h
  have h0 : upd G u g 0 = G 0 := upd_ne _ _ (by rcases hu with rfl | rfl <;> decide)
  obtain ⟨hr0, hcs, hh⟩ := h
  refine ⟨ht ▸ hr0, by rw [hc, ht]; exact hcs, ?_⟩
  rw [ht, h0]
  rcases hh with ⟨hs, hp, hn⟩ | ⟨hs, hr1, hp, k1, hn⟩ | ⟨hs, k1, k2, hn, hj⟩
  · rcases hu with rfl | rfl
    · rw [hn 1 (by decide)] at hk0; exact (hnk hk0).elim
    · rw [hn 2 (by decide)] at hk0; exact (hnk hk0).elim
  · rcases hu with rfl | rfl
    · exact .inr (.inl ⟨hs, hr1, hp, by rw [upd_self]; exact hk, fun v hv => by
        rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact hn v hv⟩)
    · rw [hn 2 (by decide)] at hk0; exact (hnk hk0).elim
  · refine .inr (.inr ⟨hs, ?_, ?_, fun v hv => ?_, ?_⟩)
    · rcases hu with rfl | rfl
      · rw [upd_self]; exact hk
      · rw [upd_ne _ _ (by decide)]; exact k1
    · rcases hu with rfl | rfl
      · rw [upd_ne _ _ (by decide)]; exact k2
      · rw [upd_self]; exact hk
    · rw [upd_ne _ _ (by rcases hu with rfl | rfl <;> unfold ThreadId at * <;> omega)]; exact hn v hv
    · have hd1 : G 1 = .done → upd G u g 1 = .done := fun h1 => by
        by_cases hu1 : u = 1
        · subst hu1; rw [upd_self]; exact hd h1
        · rw [upd_ne _ _ (Ne.symm hu1)]; exact h1
      have hd2 : G 2 = .done → upd G u g 2 = .done := fun h2 => by
        by_cases hu2 : u = 2
        · subst hu2; rw [upd_self]; exact hd h2
        · rw [upd_ne _ _ (Ne.symm hu2)]; exact h2
      rcases hj with ⟨hp, hr⟩ | ⟨hp, h1, hr⟩ | ⟨hp, h1, h2, hr⟩
      · exact .inl ⟨hp, hr⟩
      · exact .inr (.inl ⟨hp, hd1 h1, hr⟩)
      · exact .inr (.inr ⟨hp, hd1 h1, hd2 h2, hr⟩)

/-- At `ld`, both pushers ended. -/
theorem ld_done {G : ThreadId → Gh} {m : Mem} (h : ThrOk G m) (h0 : G 0 = .ld) :
    G 1 = .done ∧ G 2 = .done := by
  obtain ⟨-, -, ⟨-, hp, -⟩ | ⟨-, -, hp, -⟩ | ⟨-, -, -, -, hh⟩⟩ := h
  · rw [h0] at hp; cases hp
  · rw [h0] at hp; cases hp
  · rcases hh with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨-, h1, h2, -⟩
    · rw [h0] at hp; cases hp
    · rw [h0] at hp; cases hp
    · exact ⟨h1, h2⟩

/-! ## The head's atomic location -/

/-- The first location of the head (`firstLoc`) is a `HeadLoc`. -/
theorem headLoc_first {G : ThreadId → Gh} {m : Mem} (hu : U32At m 0 0 0)
    (hn : ∀ u, (u = 1 ∨ u = 2) → G u ≠ .done) : HeadLoc G m (firstLoc m 0 0 4) := by
  refine ⟨rfl, rfl, rfl, rfl, fun e he hh => by
      simpa [ALoc.lastClock, firstLoc, firstMsg] using plainLe_plainClock m 0 0 4 e he hh,
    fun j hj => by simp [firstLoc] at hj, [0], by simp [Chains], rfl,
    fun j hj => ?_, fun u hu => ?_, fun j hj => by simp at hj, fun j hj => by simp [firstLoc] at hj⟩
  · have : j = 0 := by simpa [firstLoc] using hj
    subst this; exact hu
  · rcases hu with rfl | rfl <;> simp [hn _ (.inl rfl), hn _ (.inr rfl)]

/-- The head's location at an atomic op (`locIdx 0 0 4`): location 0, a `HeadLoc`; the op changes
only `atomics` and `nextMsg`. -/
theorem loc_head {G : ThreadId → Gh} {m m₁ : Mem} {li : Nat} (hf : HeadOk G m)
    (h : ((locIdx 0 0 4).run m).run = some (.ok (li, m₁))) :
    li = 0 ∧ ∃ l k, HeadLoc G m l ∧ m₁ = { m with atomics := #[l], nextMsg := k } := by
  have h0 : m.atomics = #[] ∨ ∃ l, m.atomics = #[l] ∧ l.block = 0 ∧ l.off = 0 ∧ l.len = 4 ∧
      ALoc.lastBytes l = curBytes m 0 0 4 ∧ PlainLe m 0 0 4 l.lastClock := by
    rcases hf with ⟨ha, -⟩ | ⟨l, ha, hlb, hlo, hll, hlast, hpl, -⟩
    · exact .inl ha
    · exact .inr ⟨l, ha, hlb, hlo, hll, hlast, hpl⟩
  obtain ⟨rfl, l, k, rfl, ⟨ha, rfl⟩ | ha⟩ := locIdx_single h0 h
  · rcases hf with ⟨-, hu, hn⟩ | ⟨l, ha', -⟩
    · exact ⟨rfl, firstLoc m 0 0 4, k, headLoc_first hu hn, rfl⟩
    · rw [ha] at ha'; simp at ha'
  · rcases hf with ⟨ha', -⟩ | ⟨l', ha', hfl⟩
    · rw [ha] at ha'; simp at ha'
    · rw [ha] at ha'
      have : l = l' := by simpa using ha'
      subst this
      exact ⟨rfl, l, k, hfl, rfl⟩

theorem head_locIdx_noErr {G : ThreadId → Gh} {m : Mem} (hf : HeadOk G m) (e : Error) :
    ((locIdx 0 0 4).run m).run ≠ some (.error e) := by
  refine locIdx_noErr (fun i hi => ?_) (fun hn l hl => ?_) e
  · rcases hf with ⟨ha, -⟩ | ⟨l, ha, -, -, hll, -⟩
    · rw [ha] at hi; simp at hi
    · have := (Array.findIdx?_eq_some_iff_getElem.mp hi).1
      rw [ha] at this hi ⊢
      have : i = 0 := by simp at this; omega
      subst this; exact hll
  · rcases hf with ⟨ha, -⟩ | ⟨l', ha, hlb, hlo, -, -⟩
    · rw [ha] at hl; simp at hl
    · rw [ha] at hn; simp [hlb, hlo] at hn

/-- A new head location for the invariant. -/
theorem Inv.setLoc {G : ThreadId → Gh} {m : Mem} {l : ALoc} (hi : Inv G m) (hl : HeadLoc G m l)
    (k : Nat) : Inv G { m with atomics := #[l], nextMsg := k } :=
  { hi with head := .inr ⟨l, rfl, hl⟩ }

theorem HeadLoc.pos {G : ThreadId → Gh} {m : Mem} {l : ALoc} (h : HeadLoc G m l) :
    0 < l.msgs.size := by
  obtain ⟨-, -, -, -, -, -, vs, hvs, hsz, -⟩ := h
  rw [hsz]
  simp only [Chains, List.mem_cons, List.not_mem_nil, or_false] at hvs
  rcases hvs with rfl | rfl | rfl | rfl | rfl <;> decide

/-- An access to the head: block 0, offset 0. -/
theorem acc_head {m : Mem} {n a : Nat} {b : BlockId} {blk : Block} {o : Nat}
    (h : m.access sPtr n a = pure (b, blk, o)) : b = 0 ∧ o = 0 ∧ m.blocks[0]? = some blk ∧
      (0 : Int) + n ≤ blk.bytes.size := by
  obtain ⟨hpb, hblk, -, -, hn, -, ho⟩ := access_eq h
  cases hpb
  exact ⟨rfl, by simpa [sPtr] using ho, hblk, hn⟩

/-- An atomic access to the head does not race. -/
theorem noRace_head {G : ThreadId → Gh} {m : Mem} {k : AccessKind} (hk : k.isAtomic = true)
    (hi : Inv G m) (ht : m.current < m.threads.size) (hact : Act G m.current) :
    NoRace m 0 0 (intSize 32) k :=
  noRace_inv hi ht fun e he hb h1 h2 hf => by
    have h4 : intSize 32 = 4 := by decide
    rw [h4] at h2
    rcases hf with h | ⟨-, -, -, ha⟩ | ⟨-, -, -, ho, -⟩ | ⟨-, -, htid, hld⟩ | ⟨h, -⟩
    · exact .inl h
    · exact .inr (.inr (racePair_atomic ha hk))
    · omega
    · rcases hact with h0 | ⟨hu, hnd⟩
      · refine .inr (.inl ?_)
        have := (hi.own e he).2
        rw [htid] at this; rw [h0]; exact this
      · exfalso
        have hd := ld_done hi.thr hld
        rcases hu with h | h
        · exact hnd (by rw [h]; exact hd.1)
        · exact hnd (by rw [h]; exact hd.2)
    · rcases h with h | h <;> exact (blk_ne h hb (by decide)).elim

/-- The invariant depends only on the threads, the clocks, the blocks, the atomic locations and
the footprint. -/
theorem Inv.congr {G : ThreadId → Gh} {m m' : Mem} (hi : Inv G m) (ht : m'.threads = m.threads)
    (hc : m'.clocks = m.clocks) (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics)
    (hf : m'.footprint = m.footprint) : Inv G m' where
  thr := by unfold ThrOk; rw [ht, hc]; exact hi.thr
  b0 := hi.b0.congr hb
  b1 := hi.b1.congr hb
  b2 := hi.b2.congr hb
  ctx := by intro u hu; unfold U32At; rw [curBytes_congr hb, curBytes_congr hb]; exact hi.ctx u hu
  head := by unfold HeadOk HeadLoc NextAt U32At PlainLe; simp only [ha, curBytes_congr hb, hc, hf]; exact hi.head
  casn := by unfold NextAt U32At; simp only [curBytes_congr hb]; exact hi.casn
  n0 := by unfold NextAt U32At; simp only [curBytes_congr hb]; exact hi.n0
  join := by unfold JoinLe; rw [hc]; exact hi.join
  fp := by
    intro e he
    rw [hf] at he
    have := hi.fp e he
    unfold FpOk Before at this ⊢
    rw [ht, hc]
    exact this
  own := by intro e he; rw [hf] at he; rw [ht, hc]; exact hi.own e he

/-! ## A pusher -/

/-- Pusher `u` reads its `PushCtx` (block `u`, bytes `o..`). -/
theorem step_ctx {T : Type} [Enc T] {G : ThreadId → Gh} {m m' : Mem} {u o a : Nat} {v v₀ : T}
    (hi : Inv G m) (hu : u = 1 ∨ u = 2) (ht : m.current < m.threads.size) (hact : Act G m.current)
    (hfit : o + Enc.size T ≤ 16) (hal : ∀ A : Nat, A % 8 = 0 → (A + o) % a = 0)
    (hq : (Enc.decode (curBytes m u o (Enc.size T)) : Result T) = pure v₀)
    (h : ((load T a ⟨some u, (o : Int)⟩).run m).run = some (.ok (v, m'))) :
    v = v₀ ∧ m' = m.recordAt u o (Enc.size T) .read ∧ Inv G m' := by
  obtain ⟨b, blk, o', hacc, -, hdec, rfl⟩ := load_ok h
  have hbu : BlkAt m u 16 8 := by
    rcases hu with rfl | rfl
    · exact hi.b1
    · exact hi.b2
  obtain ⟨blk₂, hb₂, -, -, hacc₂⟩ := access_blk (a := a) (len := Enc.size T) (o := o) hbu hfit hal rfl
  rw [hacc₂] at hacc
  cases hacc
  have hx : blk.bytes.extract o (o + Enc.size T) = curBytes m u o (Enc.size T) := by
    unfold curBytes; rw [hb₂]; rfl
  rw [hx, hq] at hdec
  simp only [pure, ExceptT.pure, ExceptT.mk, ExceptT.run, Option.some.injEq, Except.ok.injEq] at hdec
  exact ⟨hdec.symm, rfl, hi.record ht hact (fun _ h => by cases h) (.inr (.inr (.inr (.inr ⟨hu, rfl⟩))))⟩

theorem ctx_noErr {T : Type} [Enc T] {G : ThreadId → Gh} {m : Mem} {u o a : Nat} {v₀ : T}
    (hi : Inv G m) (hu : u = 1 ∨ u = 2) (ht : m.current < m.threads.size)
    (hfit : o + Enc.size T ≤ 16) (hal : ∀ A : Nat, A % 8 = 0 → (A + o) % a = 0)
    (hq : (Enc.decode (curBytes m u o (Enc.size T)) : Result T) = pure v₀) (e : Error) :
    ((load T a ⟨some u, (o : Int)⟩).run m).run ≠ some (.error e) := by
  have hbu : BlkAt m u 16 8 := by
    rcases hu with rfl | rfl
    · exact hi.b1
    · exact hi.b2
  obtain ⟨blk₂, hb₂, -, -, hacc₂⟩ := access_blk (a := a) (len := Enc.size T) (o := o) hbu hfit hal rfl
  have hx : blk₂.bytes.extract o (o + Enc.size T) = curBytes m u o (Enc.size T) := by
    unfold curBytes; rw [hb₂]; rfl
  have hnr : NoRace m u o (Enc.size T) .read := noRace_inv hi ht fun e _ hb _ _ hf => by
    have hu0 : u ≠ 0 := by rcases hu with rfl | rfl <;> decide
    rcases hf with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hk⟩
    · exact .inl h
    · exact (hu0 (hb.symm.trans h)).elim
    · exact (hu0 (hb.symm.trans h)).elim
    · exact (hu0 (hb.symm.trans h)).elim
    · exact .inr (.inr (by rw [hk]; rfl))
  exact MemM.noErr_of_run (load_run hacc₂ (by rw [hx]; exact hq) hnr) e

/-- `next[k]` for `k < 3`: bytes `4 + 4k .. 8 + 4k` of block 0; a write to another `next` or to
the head does not change it. -/
theorem nextAt_write {m : Mem} {blk : Block} {o k : Nat} {bs : Array Byte} {v : BitVec 32}
    (hb : m.blocks[0]? = some blk) (hsz : blk.bytes.size = 16) (hfit : o + bs.size ≤ 16)
    (hk : k < 3) (hd : o + bs.size ≤ 4 + 4 * k ∨ 8 + 4 * k ≤ o) (h : NextAt m k v) :
    NextAt (m.write 0 blk o bs) k v := by
  unfold NextAt U32At
  rw [curBytes_write_other hb (by rw [hsz]; exact hfit) (.inr ⟨rfl, by rw [hsz]; omega, by omega⟩)]
  exact h

theorem mem_of_getElem! {vs : List Nat} {j : Nat} (h : j < vs.length) : vs[j]! ∈ vs := by
  rw [getElem!_pos vs j h]; exact List.getElem_mem _

/-- The nodes of a chain are 0, 1, 2. -/
theorem chains_lt {vs : List Nat} (hvs : vs ∈ Chains) {x : Nat} (hx : x ∈ vs) : x < 3 := by
  simp only [Chains, List.mem_cons, List.not_mem_nil, or_false] at hvs
  rcases hvs with rfl | rfl | rfl | rfl | rfl <;> simp at hx <;> omega

/-- Pusher `u`'s write of `h` to `next[u]`: it goes to `cas h`. -/
theorem Inv.writeNext {G : ThreadId → Gh} {M : Mem} {u : ThreadId} {blk : Block} {h : BitVec 32}
    (hi : Inv G M) (hu : u = 1 ∨ u = 2) (hk0 : Kid u (G u)) (hnd : G u ≠ .done)
    (hb : M.blocks[0]? = some blk) :
    Inv (upd G u (.cas h)) (M.write 0 blk (4 + 4 * u) (Enc.encode h)) := by
  have hsz : blk.bytes.size = 16 := by
    obtain ⟨blk', hb', -, hs, -⟩ := hi.b0; rw [hb] at hb'; cases hb'; exact hs
  have h4 : (Enc.encode h).size = 4 := size_encode_u32 h
  have hfit : 4 + 4 * u + (Enc.encode h).size ≤ blk.bytes.size := by
    rw [h4, hsz]; rcases hu with rfl | rfl <;> decide
  have hfit' : 4 + 4 * u + (Enc.encode h).size ≤ 16 := by rw [← hsz]; exact hfit
  have h0 : upd G u (.cas h) 0 = G 0 := upd_ne _ _ (by rcases hu with rfl | rfl <;> decide)
  have hne : ∀ v, v ≠ u → upd G u (.cas h) v = G v := fun v hv => upd_ne _ _ hv
  have hnx : ∀ k v, k < 3 → k ≠ u → NextAt M k v → NextAt (M.write 0 blk (4 + 4 * u) (Enc.encode h)) k v :=
    fun k v hk hku hn => nextAt_write hb hsz hfit' hk (by rw [h4]; unfold ThreadId at *; omega) hn
  exact {
    thr := thr_upd_kid hi.thr rfl rfl hu hk0 (.inr (.inl ⟨h, rfl⟩)) (fun hd => absurd hd hnd)
    b0 := BlkAt.write hb hfit hi.b0
    b1 := BlkAt.write hb hfit hi.b1
    b2 := BlkAt.write hb hfit hi.b2
    ctx := fun v hv => by
      unfold U32At
      rw [curBytes_write_other hb hfit (.inl (by rcases hv with rfl | rfl <;> decide)),
        curBytes_write_other hb hfit (.inl (by rcases hv with rfl | rfl <;> decide))]
      exact hi.ctx v hv
    head := by
      rcases hi.head with ⟨ha, hu0, hn⟩ | ⟨l, ha, hlb, hlo, hll, hlast, hpl, hc, vs, hvs, hsz', hv, hd, hnxt, hcl⟩
      · refine .inl ⟨ha, ?_, fun v hv => ?_⟩
        · unfold U32At
          rw [curBytes_write_other hb hfit (.inr ⟨rfl, by rw [hsz]; decide, .inr (by omega)⟩)]
          exact hu0
        · by_cases hvu : v = u
          · subst hvu; rw [upd_self]; exact fun h => by cases h
          · rw [hne v hvu]; exact hn v hv
      · have hnu : u ∉ vs := fun h => hnd ((hd u hu).mpr h)
        refine .inr ⟨l, ha, hlb, hlo, hll, ?_, hpl, hc, vs, hvs, hsz', hv, fun v hv => ?_, fun j hj => ?_, hcl⟩
        · rw [curBytes_write_other hb hfit (.inr ⟨rfl, by rw [hsz]; decide, .inr (by omega)⟩)]
          exact hlast
        · by_cases hvu : v = u
          · subst hvu; rw [upd_self]; exact ⟨fun h => (by cases h), fun h => absurd h hnu⟩
          · rw [hne v hvu]; exact hd v hv
        · have hm := mem_of_getElem! hj
          exact hnx _ _ (chains_lt hvs hm) (fun h => hnu (h ▸ hm)) (hnxt j hj)
    casn := fun v x hv hc => by
      by_cases hvu : v = u
      · subst hvu
        rw [upd_self] at hc
        cases hc
        unfold NextAt U32At
        have := curBytes_write_same hb hfit
        rw [h4] at this
        rw [this]
        exact intOfBytes_rmw _
      · rw [hne v hvu] at hc
        exact hnx v x (by rcases hv with rfl | rfl <;> decide) hvu (hi.casn v x hv hc)
    n0 := hnx 0 0 (by decide) (by rcases hu with rfl | rfl <;> decide) hi.n0
    join := by unfold JoinLe; rw [h0]; exact hi.join
    fp := by
      intro e he
      rcases hi.fp e he with h | h | h | ⟨h1, h2, h3, h4⟩ | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inl ⟨h1, h2, h3, by rw [h0]; exact h4⟩)))
      · exact .inr (.inr (.inr (.inr h)))
    own := hi.own }

theorem kid_lt {G : ThreadId → Gh} {m : Mem} {u : ThreadId} (hi : Inv G m) (hk : Kid u (G u)) :
    u < m.threads.size := by
  refine (thr_kid hi.thr ?_).2.1
  rcases hk with h | ⟨x, h⟩ | h
  · exact .inr (.inl ⟨u, h⟩)
  · exact .inr (.inr ⟨x, h⟩)
  · exact .inl h

/-- Pusher `u`'s write of `h` to `next[u]` (a plain store): it goes to `cas h`. -/
theorem step_next {G : ThreadId → Gh} {m m' : Mem} {u : ThreadId} {h : BitVec 32} (hi : Inv G m)
    (hu : u = 1 ∨ u = 2) (hk0 : Kid u (G u)) (hnd : G u ≠ .done) (hc : m.current = u)
    (hs : ((store (α := BitVec 32) 4 ⟨some 0, ((4 + 4 * u : Nat) : Int)⟩ h).run m).run = some (.ok ((), m'))) :
    m'.current = u ∧ m'.threads = m.threads ∧ Inv (upd G u (.cas h)) m' := by
  obtain ⟨b, blk, o, hacc, -, rfl⟩ := store_ok hs
  obtain ⟨blk₀, hb₀, -, -, hacc₀⟩ := access_blk (a := 4) (len := (Enc.encode h).size)
    (o := 4 + 4 * u) hi.b0 (by rw [size_encode_u32]; rcases hu with rfl | rfl <;> decide)
    (fun A hA => by unfold ThreadId at *; omega) rfl
  rw [hacc₀] at hacc
  cases hacc
  have ht : m.current < m.threads.size := by rw [hc]; exact kid_lt hi hk0
  have hir := hi.record (b := 0) (o := 4 + 4 * u) (len := (Enc.encode h).size) (k := .write) ht
    (.inr ⟨by rw [hc]; exact hu, by rw [hc]; exact hnd⟩) (fun _ _ => by omega)
    (.inr (.inr (.inl ⟨rfl, rfl, by rw [hc]; exact hu, by rw [hc], size_encode_u32 h⟩)))
  exact ⟨hc, rfl, hir.writeNext hu hk0 hnd hb₀⟩

theorem next_noErr {G : ThreadId → Gh} {m : Mem} {u : ThreadId} {h : BitVec 32} (hi : Inv G m)
    (hu : u = 1 ∨ u = 2) (hk0 : Kid u (G u)) (hnd : G u ≠ .done) (hc : m.current = u) (e : Error) :
    ((store (α := BitVec 32) 4 ⟨some 0, ((4 + 4 * u : Nat) : Int)⟩ h).run m).run ≠ some (.error e) := by
  obtain ⟨blk₀, -, hk, -, hacc₀⟩ := access_blk (a := 4) (len := Enc.size (BitVec 32))
    (o := 4 + 4 * u) hi.b0 (by rcases hu with rfl | rfl <;> decide)
    (fun A hA => by unfold ThreadId at *; omega) rfl
  have ht : m.current < m.threads.size := by rw [hc]; exact kid_lt hi hk0
  have hnr : NoRace m 0 (4 + 4 * u) (Enc.size (BitVec 32)) .write :=
    noRace_inv hi ht fun e he hb h1 h2 hf => by
      have h4 : Enc.size (BitVec 32) = 4 := rfl
      rw [h4] at h2
      rcases hf with h | ⟨-, ho, hl, -⟩ | ⟨-, -, -, ho, hl⟩ | ⟨-, -, -, hld⟩ | ⟨hbb, -⟩
      · exact .inl h
      · exfalso; rw [ho] at h1; unfold ThreadId at *; omega
      · refine .inr (.inl ?_)
        have htid : e.tid = u := by rw [ho, hl] at h1; rw [ho] at h2; unfold ThreadId at *; omega
        have := (hi.own e he).2
        rw [htid, ← hc] at this
        exact this
      · exfalso
        have := ld_done hi.thr hld
        rcases hu with rfl | rfl
        · exact hnd this.1
        · exact hnd this.2
      · rcases hbb with hbb | hbb <;> exact (blk_ne hbb hb (by decide)).elim
  exact MemM.noErr_of_run (store_run h hacc₀ hk hnr) e

/-- A `GrowsAt` for a read that does not acquire. -/
theorem growsAt_loadM (m : Mem) (li : Nat) (msg : Msg) (t : ThreadId) :
    GrowsAt m (loadM m li .relaxed msg) t :=
  ⟨grows_loadM m li .relaxed msg, fun _ _ => rfl⟩

/-- Pusher `u`'s relaxed load of the head. -/
theorem step_rload {G : ThreadId → Gh} {m m' : Mem} {c u : Nat} {v : BitVec 32} (hi : Inv G m)
    (hu : u = 1 ∨ u = 2) (hk0 : Kid u (G u)) (hnd : G u ≠ .done) (hc : m.current = u)
    (h : ((atomicLoadAt (n := 32) c .relaxed 4 sPtr).run m).run = some (.ok (v, m'))) :
    m'.current = u ∧ m'.threads = m.threads ∧ Inv G m' := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, -, hl, -, -, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨rfl, rfl, -, -⟩ := acc_head hacc
  have ht : m.current < m.threads.size := by rw [hc]; exact kid_lt hi hk0
  have hact : Act G m.current := .inr ⟨by rw [hc]; exact hu, by rw [hc]; exact hnd⟩
  have hir := hi.record (b := 0) (o := 0) (len := intSize 32) (k := .atomicRead) ht hact
    (fun _ h => by cases h) (.inr (.inl ⟨rfl, rfl, show intSize 32 ≤ 4 by decide, rfl⟩))
  have hcur : (m.recordAt 0 0 (intSize 32) .atomicRead).current = m.current := rfl
  have hthr : (m.recordAt 0 0 (intSize 32) .atomicRead).threads = m.threads := rfl
  generalize m.recordAt 0 0 (intSize 32) .atomicRead = mr at hir hl hcur hthr
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_head hir.head hl
  have hiM := hir.setLoc hfl k
  exact ⟨by rw [loadM_current]; exact hcur.trans hc, hthr,
    hiM.grow (growsAt_loadM _ _ _ mr.current) (by rw [hcur]; exact hact)⟩

/-- A message of the head holds a `u32`. -/
theorem HeadLoc.val {G : ThreadId → Gh} {m : Mem} {l : ALoc} (h : HeadLoc G m l) {pos : Nat}
    (hp : pos < l.msgs.size) : ∃ w, (intOfBytes 32 (l.msgs[pos]!).bytes).run = some (.ok w) := by
  obtain ⟨-, -, -, -, -, -, vs, -, -, hv, -⟩ := h
  exact ⟨_, by rw [getElem!_pos l.msgs pos hp]; exact hv pos hp⟩

theorem rload_noErr {G : ThreadId → Gh} {m : Mem} {c : Nat} {ord : AtomicOrder} (hi : Inv G m)
    (ht : m.current < m.threads.size) (hact : Act G m.current)
    (hcr : c < loadCount 32 ord 4 sPtr m ∨ loadCount 32 ord 4 sPtr m = 0 ∧ c = 0)
    (e : Error) : ((atomicLoadAt (n := 32) c ord 4 sPtr).run m).run ≠ some (.error e) := by
  obtain ⟨blk₀, -, -, -, hacc₀⟩ := access_blk (p := sPtr) (a := 4) (len := intSize 32) (o := 0)
    hi.b0 (by decide) (fun A hA => by omega) rfl
  have hir := hi.record (b := 0) (o := 0) (len := intSize 32) (k := .atomicRead) ht hact
    (fun _ h => by cases h) (.inr (.inl ⟨rfl, rfl, show intSize 32 ≤ 4 by decide, rfl⟩))
  refine atomicLoadAt_noErr (loadPrep_noErr (rmw := false) (by simpa using hacc₀)
    (by simpa using noRace_head (k := .atomicRead) rfl hi ht hact)
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact head_locIdx_noErr hir.head))
    (fun li opts m₁ hp => ?_) e
  obtain ⟨b, blk, o, hacc', -, hl, rfl⟩ := loadPrep_ok hp
  simp only [Bool.false_eq_true, ↓reduceIte] at hacc' hl
  obtain ⟨rfl, rfl, -, -⟩ := acc_head hacc'
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_head hir.head hl
  have hl0 : ({ m.recordAt 0 0 (intSize 32) .atomicRead with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
  have hcount : loadCount 32 ord 4 sPtr m = (readOpts { m.recordAt 0 0 (intSize 32) .atomicRead with
      atomics := #[l], nextMsg := k } 0 false).size := optCount_eq hp
  have hne : 0 < (readOpts { m.recordAt 0 0 (intSize 32) .atomicRead with
      atomics := #[l], nextMsg := k } 0 false).size := readOpts_ne (by rw [hl0]; exact hfl.pos)
  rw [hcount] at hcr
  have hc : c < (readOpts { m.recordAt 0 0 (intSize 32) .atomicRead with atomics := #[l], nextMsg := k } 0 false).size := by
    rcases hcr with h | ⟨h0, -⟩
    · exact h
    · exact absurd h0 (Nat.pos_iff_ne_zero.mp hne)
  refine ⟨_, Array.getElem?_eq_getElem hc, ?_⟩
  have hlt := readOpts_lt (Array.getElem?_eq_getElem hc)
  rw [hl0] at hlt ⊢
  exact hfl.val hlt

/-! ## A pusher's `cmpxchg` -/

theorem chains_push {vs : List Nat} (hvs : vs ∈ Chains) {u : Nat} (hu : u = 1 ∨ u = 2)
    (hn : u ∉ vs) : vs ++ [u] ∈ Chains := by
  simp only [Chains, List.mem_cons, List.not_mem_nil, or_false] at hvs ⊢
  rcases hu with rfl | rfl <;> rcases hvs with rfl | rfl | rfl | rfl | rfl <;> simp_all

theorem chains_pos {vs : List Nat} (hvs : vs ∈ Chains) : 0 < vs.length := by
  simp only [Chains, List.mem_cons, List.not_mem_nil, or_false] at hvs
  rcases hvs with rfl | rfl | rfl | rfl | rfl <;> decide

theorem getElem!_append_lt {vs : List Nat} {u j : Nat} (h : j < vs.length) :
    (vs ++ [u])[j]! = vs[j]! := by
  rw [getElem!_pos (vs ++ [u]) j (by simp; omega), getElem!_pos vs j h, List.getElem_append_left]

theorem getElem!_append_len (vs : List Nat) (u : Nat) : (vs ++ [u])[vs.length]! = u := by
  rw [getElem!_pos (vs ++ [u]) vs.length (by simp)]; simp

theorem val_inj {msg : Msg} {a b : BitVec 32} (ha : Val msg a) (hb : Val msg b) : a = b := by
  have := ha.symm.trans hb
  simpa using this

/-- Pusher `u`'s `cmpxchg` that succeeds: its message `u` after the newest one; it ends. -/
theorem Inv.pushHead {G : ThreadId → Gh} {M : Mem} {l : ALoc} {msg : Msg} {blk : Block}
    {u : ThreadId} {h : BitVec 32} (hi : Inv G M) (hu : u = 1 ∨ u = 2) (hg : G u = .cas h)
    (ha : M.atomics = #[l]) (hlast : Val (l.msgs[l.msgs.size - 1]!) h) (hb : M.blocks[0]? = some blk)
    (hbs : msg.bytes.size = 4) (hv : Val msg (BitVec.ofNat 32 u))
    (hr : msg.rmwOf = some (l.msgs[l.msgs.size - 1]!).id)
    (hcl : VClock.le msg.clock (M.clocks[u]!) = true) (hpl : PlainLe M 0 0 4 msg.clock) :
    Inv (upd G u .done) { M.write 0 blk 0 msg.bytes with atomics := #[{ l with msgs := l.msgs.push msg }] } := by
  obtain ⟨hlb, hlo, hll, -, -, hc, vs, hvs, hsz, hval, hd, hnxt, hclk⟩ : HeadLoc G M l := by
    rcases hi.head with ⟨ha', -⟩ | ⟨l', ha', hfl⟩
    · rw [ha] at ha'; simp at ha'
    · rw [ha] at ha'
      have : l = l' := by simpa using ha'
      subst this; exact hfl
  have hvl := chains_pos hvs
  have h0 : 0 < l.msgs.size := by rw [hsz]; exact hvl
  have hnu : u ∉ vs := fun hm => by have := (hd u hu).mpr hm; rw [hg] at this; cases this
  have hh : h = BitVec.ofNat 32 vs[vs.length - 1]! := by
    rw [hsz] at hlast
    rw [getElem!_pos l.msgs _ (by omega)] at hlast
    exact val_inj hlast (hval (vs.length - 1) (by omega))
  have hsz16 : blk.bytes.size = 16 := by
    obtain ⟨blk', hb', -, hs, -⟩ := hi.b0; rw [hb] at hb'; cases hb'; exact hs
  have hfit : 0 + msg.bytes.size ≤ blk.bytes.size := by rw [hbs, hsz16]; decide
  have hfit' : 0 + msg.bytes.size ≤ 16 := by rw [hbs]; decide
  have hnx : ∀ k v, k < 3 → NextAt M k v → NextAt (M.write 0 blk 0 msg.bytes) k v :=
    fun k v hk hn => nextAt_write hb hsz16 hfit' hk (by rw [hbs]; omega) hn
  have h0' : upd G u .done 0 = G 0 := upd_ne _ _ (by rcases hu with rfl | rfl <;> decide)
  have hlast' : ALoc.lastBytes { l with msgs := l.msgs.push msg } =
      curBytes (M.write 0 blk 0 msg.bytes) 0 0 4 := by
    have := curBytes_write_same hb hfit
    rw [hbs] at this
    rw [this]; simp [ALoc.lastBytes]
  refine {
    thr := thr_upd_kid hi.thr rfl rfl hu (.inr (.inl ⟨h, hg⟩)) (.inr (.inr rfl)) (fun _ => rfl)
    b0 := BlkAt.write hb hfit hi.b0
    b1 := BlkAt.write hb hfit hi.b1
    b2 := BlkAt.write hb hfit hi.b2
    ctx := fun v hv => by
      show curBytes (M.write 0 blk 0 msg.bytes) v 0 8 = _ ∧ U32At (M.write 0 blk 0 msg.bytes) v 8 _
      unfold U32At
      rw [curBytes_write_other hb hfit (.inl (by rcases hv with rfl | rfl <;> decide)),
        curBytes_write_other hb hfit (.inl (by rcases hv with rfl | rfl <;> decide))]
      exact hi.ctx v hv
    head := .inr ⟨_, rfl, hlb, hlo, hll, hlast',
      fun e he hh => by simpa [ALoc.lastClock] using hpl e he hh, hc.push h0 hr, vs ++ [u],
      chains_push hvs hu hnu,
      by simp [hsz], fun j hj => ?_, fun v hv => ?_, fun j hj => ?_, fun j hj => ?_⟩
    casn := fun v x hv hcx => by
      by_cases hvu : v = u
      · subst hvu; rw [upd_self] at hcx; cases hcx
      · rw [upd_ne _ _ hvu] at hcx
        exact hnx v x (by rcases hv with rfl | rfl <;> decide) (hi.casn v x hv hcx)
    n0 := hnx 0 0 (by decide) hi.n0
    join := by unfold JoinLe; rw [h0']; exact hi.join
    fp := by
      intro e he
      rcases hi.fp e he with h | h | h | ⟨h1, h2, h3, h4⟩ | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inl ⟨h1, h2, h3, by rw [h0']; exact h4⟩)))
      · exact .inr (.inr (.inr (.inr h)))
    own := hi.own }
  · simp only [Array.size_push] at hj
    simp only [Array.getElem_push]
    split
    · rename_i hj'
      rw [getElem!_append_lt (by omega)]
      exact hval j hj'
    · have : j = vs.length := by omega
      subst this
      rw [getElem!_append_len]
      exact hv
  · by_cases hvu : v = u
    · subst hvu; simp
    · rw [upd_ne _ _ hvu, hd v hv]; simp [hvu]
  · simp only [List.length_append, List.length_singleton] at hj
    by_cases hj' : j + 1 < vs.length
    · rw [getElem!_append_lt hj', getElem!_append_lt (by omega)]
      exact hnx _ _ (chains_lt hvs (mem_of_getElem! hj')) (hnxt j hj')
    · have : j + 1 = vs.length := by omega
      rw [this, getElem!_append_len, getElem!_append_lt (by omega),
        show j = vs.length - 1 by omega, ← hh]
      exact hnx _ _ (by rcases hu with rfl | rfl <;> decide) (hi.casn u h hu hg)
  · simp only [Array.size_push] at hj
    simp only [Array.getElem_push]
    split
    · rename_i hj'
      rw [getElem!_append_lt (by omega)]
      exact hclk j hj'
    · have : j + 1 = vs.length := by omega
      rw [this, getElem!_append_len]
      exact hcl

/-- Pusher `u`'s `cmpxchg(h, u)` (release, failure relaxed): on success it ends (`done`); on
failure nothing that the invariant sees changes. -/
theorem step_cas {G : ThreadId → Gh} {m m' : Mem} {c u : Nat} {h : BitVec 32}
    {r : Option (BitVec 32)} (hi : Inv G m) (hu : u = 1 ∨ u = 2) (hg : G u = .cas h)
    (hc : m.current = u)
    (hs : ((cmpxchgWeakAt c .release .relaxed 4 sPtr h (BitVec.ofNat 32 u)).run m).run = some (.ok (r, m'))) :
    m'.current = u ∧ m'.threads = m.threads ∧
      ((r = none ∧ Inv (upd G u .done) m') ∨ (∃ old, r = some old ∧ Inv G m')) := by
  obtain ⟨b, blk, o, li, m₁, pos, spurious, old, hacc, -, hl, hpos, hold, hres⟩ := cmpxchgWeakAt_ok hs
  obtain ⟨rfl, rfl, hb0, -⟩ := acc_head (accessW_pure hacc).1
  have hk0 : Kid u (G u) := .inr (.inl ⟨h, hg⟩)
  have hnd : G u ≠ .done := by rw [hg]; intro h; cases h
  have ht : m.current < m.threads.size := by rw [hc]; exact kid_lt hi hk0
  have hact : Act G m.current := .inr ⟨by rw [hc]; exact hu, by rw [hc]; exact hnd⟩
  have hir := hi.record (b := 0) (o := 0) (len := intSize 32) (k := .atomicRead) ht hact
    (fun _ h => by cases h) (.inr (.inl ⟨rfl, rfl, show intSize 32 ≤ 4 by decide, rfl⟩))
  have hcur : (m.recordAt 0 0 (intSize 32) .atomicRead).current = m.current := rfl
  have hthr : (m.recordAt 0 0 (intSize 32) .atomicRead).threads = m.threads := rfl
  have hbr : (m.recordAt 0 0 (intSize 32) .atomicRead).blocks[0]? = some blk := hb0
  generalize m.recordAt 0 0 (intSize 32) .atomicRead = mr at hir hl hcur hthr hbr
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_head hir.head hl
  have hl0 : ({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
  have hiM := hir.setLoc hfl k
  have hact' : Act G mr.current := by rw [hcur]; exact hact
  rcases hres with ⟨rfl, hsp, rfl, -, rfl⟩ | ⟨-, rfl, rfl⟩
  · -- success: the newest message, then the pusher's message
    obtain ⟨j, hstrong⟩ := weakCasOpts_strong (by simpa [hsp] using hpos)
    have hpos' := cas_chain_pos (m := { mr with atomics := #[l], nextMsg := k })
      (by rw [hl0]; exact hfl.2.2.2.2.2.1) hstrong hold
    rw [hl0] at hpos' hold
    have hbM : ({ mr with atomics := #[l], nextMsg := k } : Mem).blocks[
        (({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).block]? = some blk := by
      rw [hl0, hfl.1]; exact hbr
    let mw := ({ mr with atomics := #[l], nextMsg := k } : Mem).recordAt 0 0 (intSize 32) .atomicWrite
    have hiW : Inv G mw := hiM.record (by change mr.current < mr.threads.size; rw [hcur, hthr]; exact ht) hact'
      (fun _ h => by cases h) (.inr (.inl ⟨rfl, rfl, show intSize 32 ≤ 4 by decide, rfl⟩))
    have hlw : mw.atomics[0]! = l := rfl
    unfold rmwM
    simp only [AtomicOrder.isAcq, Bool.false_eq_true, ↓reduceIte]
    have hins := insertM_last (m := mw) (msg := rmwMsg mw .release
      (l.msgs[l.msgs.size - 1]!) (BitVec.ofNat 32 u)) hbM
    rw [hlw] at hins
    rw [hpos', Nat.sub_add_cancel hfl.pos, show (#[l] : Array ALoc)[0]! = l from rfl, hins]
    have hiN := hiW.pushHead hu hg rfl (by rw [← hpos']; exact hold) hbr
      (msg := rmwMsg mw .release (l.msgs[l.msgs.size - 1]!)
        (BitVec.ofNat 32 u))
      (LawfulEnc.size_encode (α := BitVec 32) _) (intOfBytes_rmw _) rfl
      (by show VClock.le (mw.clocks[mw.current]!) (mw.clocks[u]!) = true; rw [show mw.current = u from hcur.trans hc]; exact VClock.le_refl _)
      (fun e he hh => by
        show VClock.le e.clock (mw.clocks[mw.current]!) = true
        have hb0 := plainHit_block hh
        have hkw := plainHit_kind hh
        rcases hiW.fp e he with ⟨-, hbf⟩ | ⟨-, -, -, ha⟩ | ⟨-, -, -, ho, -⟩ | ⟨-, hk, -⟩ | ⟨hbb, -⟩
        · exact hbf _ (by change mr.current < mr.threads.size; rw [hcur, hthr]; exact ht)
        · rw [plainHit_atomic ha] at hh; cases hh
        · unfold plainHit at hh
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
          omega
        · rw [hkw] at hk; cases hk
        · rcases hbb with hbb | hbb <;> exact (blk_ne hbb hb0 (by decide)).elim)
    refine ⟨hcur.trans hc, hthr, .inl ⟨trivial, hiN.congr rfl rfl ?_ ?_ rfl⟩⟩
    · show mw.blocks.set! _ _ = mw.blocks.set! _ _
      rw [hfl.1, hfl.2.1]
    · rfl
  · -- failure: a read of a message, no acquire
    exact ⟨by rw [loadM_current]; exact hcur.trans hc, hthr,
      .inr ⟨_, rfl, hiM.grow (growsAt_loadM _ _ _ mr.current) hact'⟩⟩

theorem cas_noErr {G : ThreadId → Gh} {m : Mem} {c u : Nat} {h : BitVec 32} (hi : Inv G m)
    (hu : u = 1 ∨ u = 2) (hg : G u = .cas h) (hc : m.current = u)
    (hcr : c < weakCasCount 32 .release 4 sPtr h m ∨ weakCasCount 32 .release 4 sPtr h m = 0 ∧ c = 0)
    (e : Error) :
    ((cmpxchgWeakAt c .release .relaxed 4 sPtr h (BitVec.ofNat 32 u)).run m).run ≠ some (.error e) := by
  have hk0 : Kid u (G u) := .inr (.inl ⟨h, hg⟩)
  have hnd : G u ≠ .done := by rw [hg]; intro h; cases h
  have ht : m.current < m.threads.size := by rw [hc]; exact kid_lt hi hk0
  have hact : Act G m.current := .inr ⟨by rw [hc]; exact hu, by rw [hc]; exact hnd⟩
  obtain ⟨blk₀, -, hk, -, hacc₀⟩ := access_blk (p := sPtr) (a := 4) (len := intSize 32) (o := 0)
    hi.b0 (by decide) (fun A hA => by omega) rfl
  have hacc : m.accessW sPtr (intSize 32) 4 = pure (0, blk₀, 0) := by simp [Mem.accessW, hacc₀, hk]
  have hir := hi.record (b := 0) (o := 0) (len := intSize 32) (k := .atomicRead) ht hact
    (fun _ h => by cases h) (.inr (.inl ⟨rfl, rfl, show intSize 32 ≤ 4 by decide, rfl⟩))
  refine cmpxchgWeakAt_noErr (weakCasPrep_noErr (casPrep_noErr hacc (noRace_head rfl hi ht hact)
    (head_locIdx_noErr hir.head))) (fun li opts m₁ hp => ?_) (fun li opts m₁ hp e he => ?_) e
  · obtain ⟨b, blk, o, hacc', -, hl, rfl⟩ := weakCasPrep_ok hp
    obtain ⟨rfl, rfl, -, -⟩ := acc_head (accessW_pure hacc').1
    obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_head hir.head hl
    have hl0 : ({ m.recordAt 0 0 (intSize 32) .atomicRead with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
    let prepared : Mem := { m.recordAt 0 0 (intSize 32) .atomicRead with atomics := #[l], nextMsg := k }
    have hcount := weakOptCount_eq (succ := .release) hp
    have hne : 0 < (weakCasOpts prepared 0 h (casOpts prepared 0 h)).size := by
      have hs := casOpts_ne (e := h) (m := prepared) (li := 0) (by rw [hl0]; exact hfl.pos)
      simp only [weakCasOpts_eq, Array.size_append, Array.size_map]
      omega
    rw [hcount] at hcr
    change c < (weakCasOpts prepared 0 h (casOpts prepared 0 h)).size ∨
      (weakCasOpts prepared 0 h (casOpts prepared 0 h)).size = 0 ∧ c = 0 at hcr
    have hc' : c < (weakCasOpts prepared 0 h (casOpts prepared 0 h)).size := by omega
    let choice := (weakCasOpts prepared 0 h (casOpts prepared 0 h))[c]
    have hchoice : (weakCasOpts prepared 0 h (casOpts prepared 0 h))[c]? = some choice :=
      Array.getElem?_eq_getElem hc'
    obtain ⟨j, hread⟩ := weakCasOpts_read hchoice
    refine ⟨choice.1, choice.2, hchoice, ?_⟩
    have hlt := readOpts_lt hread
    rw [hl0] at hlt ⊢
    exact hfl.val hlt


  · obtain ⟨b, blk, o, hacc', -, hl, rfl⟩ := weakCasPrep_ok hp
    obtain ⟨rfl, rfl, -, -⟩ := acc_head (accessW_pure hacc').1
    obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_head hir.head hl
    have hiM := hir.setLoc hfl k
    have htM : ({ m.recordAt 0 0 (intSize 32) .atomicRead with
        atomics := #[l], nextMsg := k } : Mem).current < m.threads.size := ht
    let M : Mem := { m.recordAt 0 0 (intSize 32) .atomicRead with atomics := #[l], nextMsg := k }
    have haM : M.accessW sPtr (intSize 32) 4 = pure (0, blk, 0) := hacc'
    exact MemM.noErr_of_run (casMarkWrite_run haM
      (noRace_head rfl hiM htM hact)) e he


/-! ## A pusher's loop -/

/-- The loop's invariant: pusher `u` at the start of a repeat. -/
def loopInv (u : Nat) (_ : pushLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  m.current = u ∧ ∃ g, (g = .start u ∨ ∃ x, g = .cas x) ∧ Inv (upd G u g) m

/-- The loop ends when the pusher's `cmpxchg` succeeded. -/
def loopPost (u : Nat) (r : pushExit × pushLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  r.1 = .br11 ∧ m.current = u ∧ Inv (upd G u .done) m

theorem ctxS_dec {G : ThreadId → Gh} {m : Mem} {u : Nat} (hi : Inv G m) (hu : u = 1 ∨ u = 2) :
    (Enc.decode (curBytes m u 0 (Enc.size Ptr)) : Result Ptr) = pure sPtr := by
  show (Enc.decode (curBytes m u 0 8) : Result Ptr) = _
  rw [(hi.ctx u hu).1]; exact LawfulEnc.decode_encode _

theorem ctxN_dec {G : ThreadId → Gh} {m : Mem} {u : Nat} (hi : Inv G m) (hu : u = 1 ∨ u = 2) :
    (Enc.decode (curBytes m u 8 (Enc.size (BitVec 32))) : Result (BitVec 32)) = pure (BitVec.ofNat 32 u) := by
  have := (hi.ctx u hu).2
  unfold U32At at this
  show ExceptT.mk (ExceptT.run (intOfBytes 32 (curBytes m u 8 4))) = _
  rw [this]; rfl

theorem loop12_body (u : Nat) (hu : u = 1 ∨ u = 2) (s : pushLocals) (G : ThreadId → Gh) (m : Mem)
    (d : Nat) (h : loopInv u s G m d) :
    proto.WP u ((push.loop12 (cPtr u)).run s) (fun r G' m' d' =>
      if push.again12 r.1 then loopInv u r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : pushLocals) => 0) s)
      else loopPost u r G' m' d') G m d := by
  obtain ⟨hc, g, hg, hi⟩ := h
  have hk0 : Kid u (upd G u g u) := by
    rw [upd_self]; rcases hg with rfl | ⟨x, rfl⟩
    · exact .inl rfl
    · exact .inr (.inl ⟨x, rfl⟩)
  have hnd : upd G u g u ≠ .done := by rw [upd_self]; rcases hg with rfl | ⟨x, rfl⟩ <;> intro h <;> cases h
  have ht : m.current < m.threads.size := by rw [hc]; exact kid_lt hi hk0
  have hact : Act (upd G u g) m.current := .inr ⟨by rw [hc]; exact hu, by rw [hc]; exact hnd⟩
  unfold push.loop12
  simp only [StateT.run_bind, pure_bind]
  rw [show (cPtr u).add 0 = ⟨some u, ((0 : Nat) : Int)⟩ from rfl,
    show (cPtr u).add 8 = ⟨some u, ((8 : Nat) : Int)⟩ from rfl]
  -- `s.s`
  refine WP.bind (WP.liftM (fun e he => (ctx_noErr hi hu ht (by decide) (fun A hA => by omega)
    (ctxS_dec hi hu) e he).elim) fun q m₁ hl => ?_)
  obtain ⟨rfl, rfl, hi₁⟩ := step_ctx hi hu ht hact (by decide) (fun A hA => by omega) (ctxS_dec hi hu) hl
  refine ⟨rfl, ?_⟩
  -- `s.node`
  refine WP.bind (WP.liftM (fun e he => (ctx_noErr hi₁ hu ht (by decide) (fun A hA => by omega)
    (ctxN_dec hi₁ hu) e he).elim) fun n m₂ hl => ?_)
  obtain ⟨rfl, rfl, hi₂⟩ := step_ctx hi₁ hu ht hact (by decide) (fun A hA => by omega) (ctxN_dec hi₁ hu) hl
  refine ⟨rfl, ?_⟩
  -- the cast and the bounds check
  have hcast : (intCast false false 64 (BitVec.ofNat 32 u)).run = some (.ok (BitVec.ofNat 64 u)) := by
    rcases hu with rfl | rfl <;> rfl
  refine WP.bind (WP.callRC (fun e he => by
    have he' : (intCast false false 64 (BitVec.ofNat 32 u)).run = some (.error e) := he
    rw [hcast] at he'; cases he') fun i18 hi18 => ?_)
  have hi18' : (intCast false false 64 (BitVec.ofNat 32 u)).run = some (.ok i18) := hi18
  rw [hcast] at hi18'
  cases hi18'
  have hlt : lt false (BitVec.ofNat 64 u) 3 = true := by rcases hu with rfl | rfl <;> rfl
  simp only [hlt, ↓reduceIte, StateT.run_pure, pure_bind]
  -- `next[u] := h`
  rw [show (sPtr.add 4).elem 4 (BitVec.ofNat 64 u) = ⟨some 0, ((4 + 4 * u : Nat) : Int)⟩ by
    rcases hu with rfl | rfl <;> rfl]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hc₂ : ((m.recordAt u 0 (Enc.size Ptr) .read).recordAt u 8 (Enc.size (BitVec 32)) .read).current = u := hc
  refine WP.bind (WP.liftM (fun e he => (next_noErr hi₂ hu hk0 hnd hc₂ e he).elim) fun _ m₃ hs₃ => ?_)
  obtain ⟨hc₃, hth₃, hi₃⟩ := step_next hi₂ hu hk0 hnd hc₂ hs₃
  rw [upd_upd] at hi₃
  refine ⟨by rw [hth₃], ?_⟩
  have hk₃ : Kid u (upd G u (.cas s.h) u) := by rw [upd_self]; exact .inr (.inl ⟨_, rfl⟩)
  have hnd₃ : upd G u (.cas s.h) u ≠ .done := by rw [upd_self]; intro h; cases h
  have ht₃ : m₃.current < m₃.threads.size := by rw [hc₃]; exact kid_lt hi₃ hk₃
  have hact₃ : Act (upd G u (.cas s.h)) m₃.current := .inr ⟨by rw [hc₃]; exact hu, by rw [hc₃]; exact hnd₃⟩
  -- `s.s`, `s.node`
  refine WP.bind (WP.bind (WP.liftM (fun e he => (ctx_noErr hi₃ hu ht₃ (by decide) (fun A hA => by omega)
    (ctxS_dec hi₃ hu) e he).elim) fun q m₄ hl => ?_))
  obtain ⟨rfl, rfl, hi₄⟩ := step_ctx hi₃ hu ht₃ hact₃ (by decide) (fun A hA => by omega) (ctxS_dec hi₃ hu) hl
  refine ⟨rfl, ?_⟩
  refine WP.bind (WP.liftM (fun e he => (ctx_noErr hi₄ hu ht₃ (by decide) (fun A hA => by omega)
    (ctxN_dec hi₄ hu) e he).elim) fun n m₅ hl => ?_)
  obtain ⟨rfl, rfl, hi₅⟩ := step_ctx hi₄ hu ht₃ hact₃ (by decide) (fun A hA => by omega) (ctxN_dec hi₄ hu) hl
  refine ⟨rfl, ?_⟩
  -- the `cmpxchg` (a stop)
  rw [show (sPtr.add 0).add 0 = sPtr from rfl]
  simp only [cmpxchgWeakC, StateT.run_bind]
  refine WP.bind (WP.bind (WP.bind (WP.pickC fun k₁ hk₁ => ⟨Gh.cas s.h, hi₅, fun G₁ m₆ hg₁ hi₆ c hcr => ?_⟩)))
  have hi₆' : Inv G₁ { m₆ with current := u } :=
    (hi₆ : Inv G₁ m₆).grow (growsAt_current m₆ u) (.inr ⟨hu, by rw [hg₁]; intro h; cases h⟩)
  refine WP.callMC (fun e he => (cas_noErr hi₆' hu hg₁ rfl hcr e he).elim) fun r m₇ hr => ?_
  obtain ⟨hc₇, hth₇, ⟨rfl, hi₇⟩ | ⟨old, rfl, hi₇⟩⟩ := step_cas hi₆' hu hg₁ rfl hr
  · refine ⟨by rw [hth₇], ?_⟩
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
    refine WP.pure' (WP.pure' ?_)
    simp only [push.again12, Bool.false_eq_true, ↓reduceIte]
    exact ⟨rfl, hc₇, hi₇⟩
  · refine ⟨by rw [hth₇], ?_⟩
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind]
    refine WP.bind (WP.callRC (fun e he => by cases he) fun a ha => ?_)
    cases ha
    refine WP.pure' ?_
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [push.again12, ↓reduceIte]
    refine ⟨⟨hc₇, .cas s.h, .inr ⟨_, rfl⟩, by rw [← hg₁, upd_same]; exact hi₇⟩, .inl (by omega)⟩

/-- Every thread was spawned by `main`: a pusher joined its own threads (none). -/
theorem joinedAll_kid {G : ThreadId → Gh} {m : Mem} {u : ThreadId} (h : ThrOk G m) (hu : 0 < u) :
    joinedAll u m := by
  intro r hr hs
  obtain ⟨h0, -, hh⟩ := h
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  have hget : ∀ {j : Nat} {x : ThreadRec} (hj : j < m.threads.size), m.threads[j]? = some x →
      m.threads[j] = x := fun hj hx => by rw [Array.getElem?_eq_getElem hj] at hx; exact Option.some.inj hx
  have hsp : (m.threads[i]'hi').spawner = 0 := by
    rcases hh with ⟨hs1, -⟩ | ⟨hs2, hr1, -⟩ | ⟨hs3, -, -, -, hj⟩
    · have : i = 0 := by omega
      subst this; rw [hget hi' h0]
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [hget hi' h0]
      · rw [hget hi' hr1]
    · have hr12 : ∃ a b : Bool, m.threads[1]? = some { spawner := 0, joined := a } ∧
          m.threads[2]? = some { spawner := 0, joined := b } := by
        rcases hj with ⟨-, h1, h2⟩ | ⟨-, -, h1, h2⟩ | ⟨-, -, -, h1, h2⟩
        · exact ⟨_, _, h1, h2⟩
        · exact ⟨_, _, h1, h2⟩
        · exact ⟨_, _, h1, h2⟩
      obtain ⟨a, b, h1, h2⟩ := hr12
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · rw [hget hi' h0]
      · rw [hget hi' h1]
      · rw [hget hi' h2]
  rw [hsp] at hs; exact absurd hs (Nat.ne_of_lt hu)

/-- Pusher `u` (thread `u`, `PushCtx` `u`): the relaxed load of the head (a stop), then the loop. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | push p =>
    simp only [proto] at hg
    obtain ⟨n, hn, rfl, rfl⟩ : ∃ n, (n = 1 ∨ n = 2) ∧ p = cPtr n ∧ g = .start n := by
      split at hg
      · rename_i hp; cases hg; exact ⟨1, .inl rfl, hp, rfl⟩
      · split at hg
        · rename_i hp; cases hg; exact ⟨2, .inr rfl, hp, rfl⟩
        · cases hg
    have hk := thr_kid (hi : Inv G m).thr (.inr (.inl ⟨n, hgu⟩))
    have hnu : n = u := by
      rcases hk.2.2 with h | ⟨_, h⟩ | h <;> rw [hgu] at h <;> cases h; rfl
    subst hnu
    have hact : Act G n := .inr ⟨hn, by rw [hgu]; intro h; cases h⟩
    have hi₀ : Inv G { m with current := n } := (hi : Inv G m).grow (growsAt_current m n) hact
    have ht₀ : ({ m with current := n } : Mem).current < ({ m with current := n } : Mem).threads.size :=
      hk.2.1
    show proto.WP n ((fun _ => ()) <$> push (cPtr n)) _ G _ d
    refine WP.map ?_
    unfold push
    refine WP.bind ?_
    rw [StateT.run'_eq]
    refine WP.map ?_
    simp only [StateT.run_bind, StateT.run_pure, pure_bind]
    rw [show (cPtr n).add 0 = ⟨some n, ((0 : Nat) : Int)⟩ from rfl]
    -- `c.s`
    refine WP.bind (WP.liftM (fun e he => (ctx_noErr hi₀ hn ht₀ (by decide) (fun A hA => by omega)
      (ctxS_dec hi₀ hn) e he).elim) fun q m₁ hl => ?_)
    obtain ⟨rfl, rfl, hi₁⟩ := step_ctx hi₀ hn ht₀ hact (by decide) (fun A hA => by omega) (ctxS_dec hi₀ hn) hl
    refine ⟨rfl, ?_⟩
    -- the relaxed load of the head (a stop)
    rw [show (sPtr.add 0).add 0 = sPtr from rfl]
    simp only [atomicLoadC, StateT.run_bind]
    refine WP.bind (WP.bind (WP.bind (WP.pickC fun k₁ hk₁ =>
      ⟨Gh.start n, by rw [← hgu, upd_same]; exact hi₁, fun G₁ m₂ hg₁ hi₂ c hcr => ?_⟩)))
    have hact₂ : Act G₁ n := .inr ⟨hn, by rw [hg₁]; intro h; cases h⟩
    have hi₂' : Inv G₁ { m₂ with current := n } := (hi₂ : Inv G₁ m₂).grow (growsAt_current m₂ n) hact₂
    have hk₂ : Kid n (G₁ n) := by rw [hg₁]; exact .inl rfl
    have ht₂ : ({ m₂ with current := n } : Mem).current < ({ m₂ with current := n } : Mem).threads.size :=
      kid_lt hi₂' hk₂
    refine WP.callMC (fun e he => (rload_noErr hi₂' ht₂ hact₂ hcr e he).elim) fun v m₃ hl => ?_
    obtain ⟨hc₃, hth₃, hi₃⟩ := step_rload hi₂' hn hk₂ (by rw [hg₁]; intro h; cases h) rfl hl
    refine ⟨by rw [hth₃], ?_⟩
    refine WP.pure' ?_
    simp only [StateT.run_modify, StateT.run_bind, pure_bind]
    -- the loop
    refine WP.bind (WP.mono ?_ (WP.loop _ _ (loopInv n) (fun _ => 0) (loopPost n) (loop12_body n hn)
      _ G₁ m₃ k₁ ⟨hc₃, .start n, .inl rfl, by rw [← hg₁, upd_same]; exact hi₃⟩))
    rintro ⟨e, s'⟩ G' m' d' ⟨rfl, hc', hi'⟩
    dsimp only
    simp only [StateT.run_pure]
    refine WP.pure' (WP.pure' ?_)
    exact ⟨.done, hi', rfl, fun _ => joinedAll_kid hi'.thr hu⟩
  | mpWriter p => cases hg
  | mpWriterRelaxed p => cases hg
  | sb p => cases hg
  | ww p => cases hg

/-! ## `main`: spawns and joins -/

/-- A step of `main` that changes only the threads, the clocks (not smaller; a new thread above
`main`'s old clock) and ghost values (no pusher gets or leaves `done` or `cas`). -/
theorem Inv.frame {G G' : ThreadId → Gh} {m m' : Mem} (hi : Inv G m) (hthr : ThrOk G' m')
    (hjoin : JoinLe G' m')
    (hdone : ∀ u, (u = 1 ∨ u = 2) → (G' u = .done ↔ G u = .done))
    (hcas : ∀ u h, (u = 1 ∨ u = 2) → G' u = .cas h → G u = .cas h)
    (hld : G 0 = .ld → G' 0 = .ld) (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics)
    (hf : m'.footprint = m.footprint) (hsz : m.threads.size ≤ m'.threads.size)
    (hcl : ∀ k : Nat, VClock.le (m.clocks[k]!) (m'.clocks[k]!) = true)
    (hnew : ∀ u < m'.threads.size, m.threads.size ≤ u → VClock.le (m.clocks[0]!) (m'.clocks[u]!) = true) :
    Inv G' m' where
  thr := hthr
  b0 := hi.b0.congr hb
  b1 := hi.b1.congr hb
  b2 := hi.b2.congr hb
  ctx := by intro u hu; unfold U32At; rw [curBytes_congr hb, curBytes_congr hb]; exact hi.ctx u hu
  head := by
    rcases hi.head with ⟨ha', hu, hn⟩ | ⟨l, ha', hlb, hlo, hll, hlast, hpl, hc, vs, hvs, hs, hv, hd, hnx, hclk⟩
    · exact .inl ⟨ha ▸ ha', by unfold U32At; rw [curBytes_congr hb]; exact hu,
        fun u h1 h2 => hn u h1 ((hdone u h1).mp h2)⟩
    · refine .inr ⟨l, ha ▸ ha', hlb, hlo, hll, by rw [curBytes_congr hb]; exact hlast,
        by unfold PlainLe; rw [hf]; exact hpl, hc, vs, hvs, hs, hv,
        fun u h1 => (hdone u h1).trans (hd u h1), fun j hj => ?_,
        fun j hj => VClock.le_trans (hclk j hj) (hcl _)⟩
      unfold NextAt U32At; rw [curBytes_congr hb]; exact hnx j hj
  casn := fun u h hu hc => by
    unfold NextAt U32At; rw [curBytes_congr hb]; exact hi.casn u h hu (hcas u h hu hc)
  n0 := by unfold NextAt U32At; rw [curBytes_congr hb]; exact hi.n0
  join := hjoin
  fp := by
    intro e he
    rw [hf] at he
    rcases hi.fp e he with ⟨hk, hbf⟩ | h | h | ⟨h1, h2, h3, h4⟩ | h
    · refine .inl ⟨hk, fun u hu => ?_⟩
      have h0 : 0 < m.threads.size := (Array.getElem?_eq_some_iff.mp hi.thr.1).1
      by_cases hu' : u < m.threads.size
      · exact VClock.le_trans (hbf u hu') (hcl u)
      · exact VClock.le_trans (hbf 0 h0) (hnew u hu (by omega))
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl ⟨h1, h2, h3, hld h4⟩)))
    · exact .inr (.inr (.inr (.inr h)))
  own := by
    intro e he
    rw [hf] at he
    obtain ⟨h1, h2⟩ := hi.own e he
    exact ⟨Nat.lt_of_lt_of_le h1 hsz, VClock.le_trans h2 (hcl _)⟩

/-- The clocks after a fork of `main`. -/
theorem fork_cl {m : Mem} (hc : m.current = 0) (k : Nat) :
    VClock.le (m.clocks[k]!) (((m.clocks.set! m.current (VClock.bump (m.clocks[m.current]!) m.current)).push
      (VClock.bump (m.clocks[m.current]!) m.current))[k]!) = true := by
  rw [hc, getElem!_push]
  have hsz : (m.clocks.set! 0 (VClock.bump (m.clocks[0]!) 0)).size = m.clocks.size := by simp
  rw [hsz]
  by_cases hk : k < m.clocks.size
  · simp only [hk, ↓reduceIte]
    rw [getElem!_set!_ite]
    split
    · rename_i h; rw [h.1]; exact VClock.le_bump _ _
    · exact VClock.le_refl _
  · rw [getElem!_neg m.clocks k hk]; exact VClock.le_default _

theorem fork_new {m : Mem} (hc : m.current = 0) (hcs : m.clocks.size = m.threads.size) (r : ThreadRec)
    (u : Nat) (hu : u < (m.threads.push r).size) (hge : m.threads.size ≤ u) :
    VClock.le (m.clocks[0]!) (((m.clocks.set! m.current (VClock.bump (m.clocks[m.current]!) m.current)).push
      (VClock.bump (m.clocks[m.current]!) m.current))[u]!) = true := by
  simp only [Array.size_push] at hu
  have : u = m.clocks.size := by omega
  subst this
  rw [hc, getElem!_push]
  have hsz : (m.clocks.set! 0 (VClock.bump (m.clocks[0]!) 0)).size = m.clocks.size := by simp
  simp only [hsz, Nat.lt_irrefl, ↓reduceIte]
  exact VClock.le_bump _ _

/-- `main`'s first spawn: pusher 1 is thread 1. -/
theorem inv_fork1 {G : ThreadId → Gh} {m m' : Mem} {c : ThreadId} (hi : Inv G m) (hg : G 0 = .pre)
    (hc : m.current = 0) (h : (Thread.fork.run m).run = some (.ok (c, m'))) :
    c = 1 ∧ m'.current = 0 ∧ Inv (upd (upd G 1 (.start 1)) 0 .mid) m' := by
  rw [fork_run] at h
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨h0, hcs, hthr⟩ := hi.thr
  obtain ⟨hs1, -, hnone⟩ : m.threads.size = 1 ∧ G 0 = .pre ∧ ∀ u, 1 ≤ u → G u = .none := by
    rcases hthr with h | ⟨-, -, g0, -⟩ | ⟨-, -, -, -, h0'⟩
    · exact h
    · rw [hg] at g0; cases g0
    · rcases h0' with ⟨g0, -⟩ | ⟨g0, -⟩ | ⟨g0, -⟩ <;> rw [hg] at g0 <;> cases g0
  refine ⟨hs1, hc, hi.frame ?_ ?_ (fun u hu => ?_) (fun u x hu hx => ?_) (fun h => by rw [hg] at h; cases h)
    rfl rfl rfl (by simp) (fork_cl hc) (fork_new hc hcs _)⟩
  · refine ⟨by rw [Array.getElem?_push_lt (by omega), ← Array.getElem?_eq_getElem (by omega)]; exact h0,
      by simp [hcs],
      .inr (.inl ⟨by simp [hs1], ?_, by rw [upd_self], by rw [upd_ne _ _ (by decide), upd_self]; exact .inl rfl,
        fun u hu => ?_⟩)⟩
    · simp only [Array.getElem?_push, hs1]; simp [hc]
    · rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega)]
      exact hnone u (by unfold ThreadId at *; omega)
  · exact ⟨fun h => (by rw [upd_self] at h; rcases h with h | h <;> cases h),
      fun h => (by rw [upd_self] at h; cases h)⟩
  · rw [upd_ne _ _ (by rcases hu with rfl | rfl <;> decide)]
    rcases hu with rfl | rfl
    · rw [upd_self, hnone 1 (by decide)]; exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
    · rw [upd_ne _ _ (by decide), hnone 2 (by decide)]
  · rw [upd_ne _ _ (by rcases hu with rfl | rfl <;> decide)] at hx
    rcases hu with rfl | rfl
    · rw [upd_self] at hx; cases hx
    · rw [upd_ne _ _ (by decide), hnone 2 (by decide)] at hx; cases hx

/-- `main`'s second spawn: pusher 2 is thread 2. -/
theorem inv_fork2 {G : ThreadId → Gh} {m m' : Mem} {c : ThreadId} (hi : Inv G m) (hg : G 0 = .mid)
    (hc : m.current = 0) (h : (Thread.fork.run m).run = some (.ok (c, m'))) :
    c = 2 ∧ m'.current = 0 ∧ Inv (upd (upd G 2 (.start 2)) 0 .j1) m' := by
  rw [fork_run] at h
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨h0, hcs, hthr⟩ := hi.thr
  obtain ⟨hs2, hr1, k1, hnone⟩ : m.threads.size = 2 ∧
      m.threads[1]? = some { spawner := 0, joined := false } ∧ Kid 1 (G 1) ∧ ∀ u, 2 ≤ u → G u = .none := by
    rcases hthr with ⟨-, g0, -⟩ | ⟨hs, hr, -, k1, hn⟩ | ⟨-, -, -, -, h0'⟩
    · rw [hg] at g0; cases g0
    · exact ⟨hs, hr, k1, hn⟩
    · rcases h0' with ⟨g0, -⟩ | ⟨g0, -⟩ | ⟨g0, -⟩ <;> rw [hg] at g0 <;> cases g0
  have h1 : upd (upd G 2 (.start 2)) 0 .j1 1 = G 1 := by
    rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]
  have h2 : upd (upd G 2 (.start 2)) 0 .j1 2 = .start 2 := by rw [upd_ne _ _ (by decide), upd_self]
  refine ⟨hs2, hc, hi.frame ?_ ⟨fun h => ?_, fun h => ?_⟩ (fun u hu => ?_) (fun u x hu hx => ?_)
    (fun h => by rw [hg] at h; cases h) rfl rfl rfl (by simp) (fork_cl hc) (fork_new hc hcs _)⟩
  · refine ⟨by rw [Array.getElem?_push_lt (by omega), ← Array.getElem?_eq_getElem (by omega)]; exact h0,
      by simp [hcs], .inr (.inr ⟨by simp [hs2], by rw [h1]; exact k1, by rw [h2]; exact .inl rfl,
        fun u hu => ?_, .inl ⟨by rw [upd_self], ?_, ?_⟩⟩)⟩
    · rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega)]
      exact hnone u (by unfold ThreadId at *; omega)
    · rw [Array.getElem?_push_lt (by omega), ← Array.getElem?_eq_getElem (by omega)]; exact hr1
    · simp only [Array.getElem?_push, hs2]; simp [hc]
  · rw [upd_self] at h; rcases h with h | h <;> cases h
  · rw [upd_self] at h; cases h
  · rcases hu with rfl | rfl
    · rw [h1]
    · rw [h2, hnone 2 (by decide)]; exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  · rcases hu with rfl | rfl
    · rw [h1] at hx; exact hx
    · rw [h2] at hx; cases hx

/-- `main`'s join of pusher `k` is possible: thread `k`, spawned by `main`, not joined. -/
theorem join_ok {G : ThreadId → Gh} {m : Mem} {k : Nat} (hi : Inv G m)
    (hk : (G 0 = .j1 ∧ k = 1) ∨ (G 0 = .j2 ∧ k = 2)) :
    ∃ m', ((Thread.join k).run { m with current := 0 }).run = some (.ok ((), m')) := by
  obtain ⟨-, -, ⟨-, hp, -⟩ | ⟨-, -, hp, -⟩ | ⟨-, -, -, -, hj⟩⟩ := hi.thr
  · rcases hk with ⟨h0, -⟩ | ⟨h0, -⟩ <;> rw [h0] at hp <;> cases hp
  · rcases hk with ⟨h0, -⟩ | ⟨h0, -⟩ <;> rw [h0] at hp <;> cases hp
  · rcases hk with ⟨h0, rfl⟩ | ⟨h0, rfl⟩
    · rcases hj with ⟨-, hr, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩
      · exact join_run (m := { m with current := 0 }) hr rfl rfl
      · rw [h0] at hp; cases hp
      · rw [h0] at hp; cases hp
    · rcases hj with ⟨hp, -⟩ | ⟨-, -, -, hr⟩ | ⟨hp, -⟩
      · rw [h0] at hp; cases hp
      · exact join_run (m := { m with current := 0 }) hr rfl rfl
      · rw [h0] at hp; cases hp

/-- `main`'s join of pusher `k`, which ended: `main`'s clock goes above the pusher's. -/
theorem inv_join {G : ThreadId → Gh} {m m' : Mem} {k : Nat} {g : Gh} (hi : Inv G m)
    (hk : (G 0 = .j1 ∧ k = 1 ∧ g = .j2) ∨ (G 0 = .j2 ∧ k = 2 ∧ g = .ld)) (hfin : G k = .done)
    (hj : ((Thread.join k).run { m with current := 0 }).run = some (.ok ((), m'))) :
    m'.current = 0 ∧ m'.threads.size = 3 ∧ Inv (upd G 0 g) m' := by
  obtain ⟨rec, hr, hjf, rfl⟩ := join_eq hj
  obtain ⟨h00, hcs, hthr⟩ := hi.thr
  obtain ⟨hs3, k1, k2, hn, hj3⟩ : m.threads.size = 3 ∧ Kid 1 (G 1) ∧ Kid 2 (G 2) ∧
      (∀ u, 3 ≤ u → G u = .none) ∧
      ((G 0 = .j1 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
          m.threads[2]? = some { spawner := 0, joined := false }) ∨
       (G 0 = .j2 ∧ G 1 = .done ∧ m.threads[1]? = some { spawner := 0, joined := true } ∧
          m.threads[2]? = some { spawner := 0, joined := false }) ∨
       (G 0 = .ld ∧ G 1 = .done ∧ G 2 = .done ∧ m.threads[1]? = some { spawner := 0, joined := true } ∧
          m.threads[2]? = some { spawner := 0, joined := true })) := by
    rcases hthr with ⟨-, hp, -⟩ | ⟨-, -, hp, -⟩ | h
    · rcases hk with ⟨h0, -⟩ | ⟨h0, -⟩ <;> rw [h0] at hp <;> cases hp
    · rcases hk with ⟨h0, -⟩ | ⟨h0, -⟩ <;> rw [h0] at hp <;> cases hp
    · exact h
  have hk0 : k ≠ 0 := by rcases hk with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> decide
  have hkk : k = 1 ∨ k = 2 := by rcases hk with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> simp
  have hc0 : 0 < m.clocks.size := by rw [hcs, hs3]; decide
  have hup : ∀ u, u ≠ 0 → upd G 0 g u = G u := fun u hu => upd_ne _ _ hu
  have hcl : ∀ u : Nat, (m.clocks.set! 0 (VClock.merge (VClock.bump (m.clocks[0]!) 0) (m.clocks[k]!)))[u]! =
      if u = 0 then VClock.merge (VClock.bump (m.clocks[0]!) 0) (m.clocks[k]!) else m.clocks[u]! := by
    intro u; rw [getElem!_set!_ite]; by_cases hu : u = 0 <;> simp [hu, hc0]
  have hth : ∀ i, i ≠ k → (m.threads.set! k { rec with joined := true })[i]? = m.threads[i]? := by
    intro i hi
    simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getElem?_setIfInBounds_ne (Ne.symm hi)]
  have hthk : (m.threads.set! k { rec with joined := true })[k]? = some { rec with joined := true } := by
    simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getElem?_setIfInBounds_self_of_lt (by rcases hkk with rfl | rfl <;> omega)]
  refine ⟨rfl, by simp [hs3], hi.frame ?_ ?_ (fun u hu => ?_) (fun u x hu hx => ?_) (fun h => ?_) rfl rfl rfl
    (by simp) (fun u => ?_) (fun u hu hge => by simp at hu; omega)⟩
  · refine ⟨by rw [hth 0 (Ne.symm hk0)]; exact h00, by simp [hcs], .inr (.inr ⟨by simp [hs3],
      by rw [hup 1 (by decide)]; exact k1, by rw [hup 2 (by decide)]; exact k2,
      fun u hu => by rw [hup u (by unfold ThreadId at *; omega)]; exact hn u hu, ?_⟩)⟩
    rcases hk with ⟨h0, rfl, rfl⟩ | ⟨h0, rfl, rfl⟩
    · rcases hj3 with ⟨-, hr1, hr2⟩ | ⟨hp, -⟩ | ⟨hp, -⟩
      · rw [hr1] at hr; cases hr
        refine .inr (.inl ⟨upd_self _ _ _, by rw [hup 1 (by decide)]; exact hfin, hthk, ?_⟩)
        rw [hth 2 (by decide)]; exact hr2
      · rw [h0] at hp; cases hp
      · rw [h0] at hp; cases hp
    · rcases hj3 with ⟨hp, -⟩ | ⟨-, h1, hr1, hr2⟩ | ⟨hp, -⟩
      · rw [h0] at hp; cases hp
      · rw [hr2] at hr; cases hr
        refine .inr (.inr ⟨upd_self _ _ _, by rw [hup 1 (by decide)]; exact h1,
          by rw [hup 2 (by decide)]; exact hfin, ?_, hthk⟩)
        rw [hth 1 (by decide)]; exact hr1
      · rw [h0] at hp; cases hp
  · show (_ → VClock.le (Array.set! _ _ _)[1]! (Array.set! _ _ _)[0]! = true) ∧
      (_ → VClock.le (Array.set! _ _ _)[2]! (Array.set! _ _ _)[0]! = true)
    have e0 : (m.clocks.set! 0 (VClock.merge (VClock.bump (m.clocks[0]!) 0) (m.clocks[k]!)))[0]! =
        VClock.merge (VClock.bump (m.clocks[0]!) 0) (m.clocks[k]!) := by rw [hcl]; rfl
    have e1 : (m.clocks.set! 0 (VClock.merge (VClock.bump (m.clocks[0]!) 0) (m.clocks[k]!)))[1]! =
        m.clocks[1]! := by rw [hcl]; rfl
    have e2 : (m.clocks.set! 0 (VClock.merge (VClock.bump (m.clocks[0]!) 0) (m.clocks[k]!)))[2]! =
        m.clocks[2]! := by rw [hcl]; rfl
    rw [e0, e1, e2, upd_self]
    rcases hk with ⟨h0, rfl, rfl⟩ | ⟨h0, rfl, rfl⟩
    · exact ⟨fun _ => VClock.le_merge_right _ _, fun h => by cases h⟩
    · have hj2 := hi.join.1 (.inl h0)
      exact ⟨fun _ => VClock.le_trans hj2 (VClock.le_trans (VClock.le_bump _ _) (VClock.le_merge_left _ _)),
        fun _ => VClock.le_merge_right _ _⟩
  · rw [hup u (by rcases hu with rfl | rfl <;> decide)]
  · rw [hup u (by rcases hu with rfl | rfl <;> decide)] at hx; exact hx
  · rcases hk with ⟨h0, -⟩ | ⟨h0, -⟩ <;> rw [h0] at h <;> cases h
  · show VClock.le (m.clocks[u]!)
      ((m.clocks.set! 0 (VClock.merge (VClock.bump (m.clocks[0]!) 0) (m.clocks[k]!)))[u]!) = true
    rw [hcl]
    split
    · rename_i hu; subst hu
      exact VClock.le_trans (VClock.le_bump _ _) (VClock.le_merge_left _ _)
    · exact VClock.le_refl _

/-! ## `main` after the joins -/

theorem size3 {G : ThreadId → Gh} {m : Mem} (h : ThrOk G m) (h0 : G 0 = .j1 ∨ G 0 = .j2 ∨ G 0 = .ld) :
    m.threads.size = 3 := by
  obtain ⟨-, -, ⟨-, hp, -⟩ | ⟨-, -, hp, -⟩ | ⟨hs, -⟩⟩ := h
  · rcases h0 with h0 | h0 | h0 <;> rw [h0] at hp <;> cases hp
  · rcases h0 with h0 | h0 | h0 <;> rw [h0] at hp <;> cases hp
  · exact hs

theorem ld_size {G : ThreadId → Gh} {m : Mem} (h : ThrOk G m) (h0 : G 0 = .ld) : m.threads.size = 3 :=
  size3 h (.inr (.inr h0))

/-- Both nodes are on the stack. -/
theorem chains_full {vs : List Nat} (hvs : vs ∈ Chains) (h1 : 1 ∈ vs) (h2 : 2 ∈ vs) :
    vs = [0, 1, 2] ∨ vs = [0, 2, 1] := by
  simp only [Chains, List.mem_cons, List.not_mem_nil, or_false] at hvs
  rcases hvs with rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- A read changes only the reader's clock. -/
theorem growsAt_loadM' (m : Mem) (li : Nat) (ord : AtomicOrder) (msg : Msg) :
    GrowsAt m (loadM m li ord msg) m.current := by
  refine ⟨grows_loadM m li ord msg, fun u hu => ?_⟩
  unfold loadM
  split
  · show ((observeM m li msg.id).clocks.set! (observeM m li msg.id).current _)[u]! = _
    rw [getElem!_set!_ite]
    simp only [show (observeM m li msg.id).current = m.current from rfl, hu, false_and, ↓reduceIte]
    rfl
  · rfl

theorem nextAt_congr {m m' : Mem} (hb : m'.blocks = m.blocks) {k : Nat} {v : BitVec 32}
    (h : NextAt m k v) : NextAt m' k v := by
  unfold NextAt U32At; rw [curBytes_congr hb]; exact h

/-- `main`'s acquire load of the head after both joins: the newest message, the top node `b`;
under it `a`, then 0. -/
theorem step_top {G : ThreadId → Gh} {m m' : Mem} {c : Nat} {v : BitVec 32} (hi : Inv G m)
    (hg : G 0 = .ld) (hc : m.current = 0)
    (h : ((atomicLoadAt (n := 32) c .acquire 4 sPtr).run m).run = some (.ok (v, m'))) :
    m'.current = 0 ∧ m'.threads = m.threads ∧ Inv G m' ∧
      ∃ a b, ((a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)) ∧ v = BitVec.ofNat 32 b ∧
        NextAt m' b (BitVec.ofNat 32 a) ∧ NextAt m' a 0 := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, -, hl, hpos, hv, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨rfl, rfl, -, -⟩ := acc_head hacc
  have ht : m.current < m.threads.size := by rw [hc, ld_size hi.thr hg]; decide
  have hact : Act G m.current := .inl hc
  have hir := hi.record (b := 0) (o := 0) (len := intSize 32) (k := .atomicRead) ht hact
    (fun _ h => by cases h) (.inr (.inl ⟨rfl, rfl, show intSize 32 ≤ 4 by decide, rfl⟩))
  have hcur : (m.recordAt 0 0 (intSize 32) .atomicRead).current = 0 := hc
  have hthr : (m.recordAt 0 0 (intSize 32) .atomicRead).threads = m.threads := rfl
  have hcs : 0 < (m.recordAt 0 0 (intSize 32) .atomicRead).clocks.size := by
    rw [hir.thr.2.1, hthr, ld_size hi.thr hg]; decide
  generalize m.recordAt 0 0 (intSize 32) .atomicRead = mr at hir hl hcur hthr hcs
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_head hir.head hl
  have hfl' := hfl
  obtain ⟨-, -, -, -, -, -, vs, hvs, hsz, hval, hd, hnx, hclk⟩ := hfl'
  have hdn := ld_done hir.thr hg
  have h1 : 1 ∈ vs := (hd 1 (.inl rfl)).mp hdn.1
  have h2 : 2 ∈ vs := (hd 2 (.inr rfl)).mp hdn.2
  have hsz3 : l.msgs.size = 3 := by rw [hsz]; rcases chains_full hvs h1 h2 with rfl | rfl <;> rfl
  have hl0 : ({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
  -- the floor of the load is the newest message
  have hj : VClock.le (l.msgs[2]'(by omega)).clock (mr.clocks[mr.current]!) = true := by
    have := hclk 1 (by omega)
    rw [hcur]
    have hv2 : vs[2]! = 1 ∨ vs[2]! = 2 := by rcases chains_full hvs h1 h2 with rfl | rfl <;> simp
    rcases hv2 with e | e <;> rw [e] at this
    · exact VClock.le_trans this (hir.join.1 (.inr hg))
    · exact VClock.le_trans this (hir.join.2 hg)
  have hfl0 : floorPos { mr with atomics := #[l], nextMsg := k } 0 = 2 := by
    have hle := le_floorPos (m := { mr with atomics := #[l], nextMsg := k }) (li := 0) (j := 2)
      (by rw [hl0]; omega) (by simp only [hl0]; exact hj)
    have hlt := floorPos_lt (m := { mr with atomics := #[l], nextMsg := k }) (li := 0) (by rw [hl0]; omega)
    rw [hl0, hsz3] at hlt
    omega
  have hro := readOpts_floor (m := { mr with atomics := #[l], nextMsg := k }) (li := 0)
    (by rw [hl0]; omega) (by rw [hfl0, hl0, hsz3])
  rw [hro, hl0, hsz3] at hpos
  have hp2 : pos = 2 := by
    cases c with
    | zero => simp at hpos; exact hpos.symm
    | succ c => simp at hpos
  subst hp2
  rw [hl0] at hv
  have hv' : v = BitVec.ofNat 32 vs[2]! := by
    rw [getElem!_pos l.msgs 2 (by omega)] at hv
    exact val_inj hv (hval 2 (by omega))
  have hb : (loadM { mr with atomics := #[l], nextMsg := k } 0 .acquire
      ((({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).msgs[2]!)).blocks = mr.blocks :=
    (grows_loadM _ _ _ _).blocks
  refine ⟨by rw [loadM_current]; exact hcur, (grows_loadM _ _ _ _).threads.trans hthr,
    (hir.setLoc hfl k).grow (growsAt_loadM' _ _ _ _) (by show Act G mr.current; rw [hcur]; exact .inl rfl), ?_⟩
  have hn1 := nextAt_congr hb (hnx 1 (by rw [← hsz, hsz3]; decide))
  have hn0 := nextAt_congr hb (hnx 0 (by rw [← hsz, hsz3]; decide))
  rcases chains_full hvs h1 h2 with rfl | rfl
  · exact ⟨1, 2, .inl ⟨rfl, rfl⟩, hv', hn1, hn0⟩
  · exact ⟨2, 1, .inr ⟨rfl, rfl⟩, hv', hn1, hn0⟩

/-- `main`'s read of `next[k]` after both joins. -/
theorem step_rd {G : ThreadId → Gh} {m m' : Mem} {k : Nat} {v w : BitVec 32} (hi : Inv G m)
    (hg : G 0 = .ld) (hc : m.current = 0) (hk : k = 1 ∨ k = 2) (hn : NextAt m k w)
    (h : ((load (BitVec 32) 4 ⟨some 0, ((4 + 4 * k : Nat) : Int)⟩).run m).run = some (.ok (v, m'))) :
    v = w ∧ m' = m.recordAt 0 (4 + 4 * k) (Enc.size (BitVec 32)) .read ∧ Inv G m' := by
  obtain ⟨b, blk, o, hacc, -, hdec, rfl⟩ := load_ok h
  obtain ⟨blk₀, hb₀, -, -, hacc₀⟩ := access_blk (a := 4) (len := Enc.size (BitVec 32))
    (o := 4 + 4 * k) hi.b0 (by rcases hk with rfl | rfl <;> decide) (fun A hA => by omega) rfl
  rw [hacc₀] at hacc
  cases hacc
  have hx : (Enc.decode (blk.bytes.extract (4 + 4 * k) (4 + 4 * k + Enc.size (BitVec 32))) :
      Result (BitVec 32)).run = some (.ok w) := by
    have := hn; unfold NextAt U32At curBytes at this; rw [hb₀] at this; exact this
  rw [hx] at hdec
  simp only [Option.some.injEq, Except.ok.injEq] at hdec
  have ht : m.current < m.threads.size := by rw [hc, ld_size hi.thr hg]; decide
  exact ⟨hdec.symm, rfl, hi.record ht (.inl hc) (fun _ h => by cases h) (.inr (.inr (.inr (.inl ⟨rfl, rfl, hc, hg⟩))))⟩

theorem rd_noErr {G : ThreadId → Gh} {m : Mem} {k : Nat} {w : BitVec 32} (hi : Inv G m)
    (hg : G 0 = .ld) (hc : m.current = 0) (hk : k = 1 ∨ k = 2) (hn : NextAt m k w) (e : Error) :
    ((load (BitVec 32) 4 ⟨some 0, ((4 + 4 * k : Nat) : Int)⟩).run m).run ≠ some (.error e) := by
  obtain ⟨blk₀, hb₀, -, -, hacc₀⟩ := access_blk (a := 4) (len := Enc.size (BitVec 32))
    (o := 4 + 4 * k) hi.b0 (by rcases hk with rfl | rfl <;> decide) (fun A hA => by omega) rfl
  have hx : (Enc.decode (blk₀.bytes.extract (4 + 4 * k) (4 + 4 * k + Enc.size (BitVec 32))) :
      Result (BitVec 32)) = pure w := by
    have := hn; unfold NextAt U32At curBytes at this; rw [hb₀] at this
    exact ExceptT.ext this
  have ht : m.current < m.threads.size := by rw [hc, ld_size hi.thr hg]; decide
  have hnr : NoRace m 0 (4 + 4 * k) (Enc.size (BitVec 32)) .read :=
    noRace_inv hi ht fun e he hb h1 h2 hf => by
      rcases hf with h | ⟨-, ho, hl, -⟩ | ⟨-, -, htid, -⟩ | ⟨-, hk', -⟩ | ⟨hbb, -⟩
      · exact .inl h
      · exfalso; rw [ho] at h1; omega
      · refine .inr (.inl ?_)
        have hown := (hi.own e he).2
        rw [hc]
        rcases htid with h | h <;> rw [h] at hown
        · exact VClock.le_trans hown (hi.join.1 (.inr hg))
        · exact VClock.le_trans hown (hi.join.2 hg)
      · exact .inr (.inr (by rw [hk']; rfl))
      · rcases hbb with hbb | hbb <;> exact (blk_ne hbb hb (by decide)).elim
  exact MemM.noErr_of_run (load_run hacc₀ hx hnr) e

/-- After both joins, `main` joined every thread. -/
theorem joinedAll_ld {G : ThreadId → Gh} {m : Mem} (h : ThrOk G m) (h0 : G 0 = .ld) : joinedAll 0 m := by
  intro r hr _
  obtain ⟨h00, -, ⟨-, hp, -⟩ | ⟨-, -, hp, -⟩ | ⟨hs3, -, -, -, hj⟩⟩ := h
  · rw [h0] at hp; cases hp
  · rw [h0] at hp; cases hp
  obtain ⟨hr1, hr2⟩ : m.threads[1]? = some { spawner := 0, joined := true } ∧
      m.threads[2]? = some { spawner := 0, joined := true } := by
    rcases hj with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨-, -, -, hr1, hr2⟩
    · rw [h0] at hp; cases hp
    · rw [h0] at hp; cases hp
    · exact ⟨hr1, hr2⟩
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  have hget : ∀ {x : ThreadRec}, m.threads[i]? = some x → m.threads[i] = x := fun hx => by
    rw [Array.getElem?_eq_getElem hi'] at hx; exact Option.some.inj hx
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · rw [hget h00]
  · rw [hget hr1]
  · rw [hget hr2]

/-! ## `main` after the joins: a load of the whole `Stack` (Zig 0.15.2)

Zig 0.15.2 reads `s.next[top]` by a load of the whole `Stack` (16 bytes, the head too), then an
index into its `next`. After both joins every access happened before `main` (`ld_le`), so the load
does not race. -/

/-- After both joins, every access happened before `main`. -/
theorem ld_le {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) (hg : G 0 = .ld) :
    ∀ e ∈ m.footprint, VClock.le e.clock (m.clocks[0]!) = true := by
  intro e he
  obtain ⟨h1, h2⟩ := hi.own e he
  rw [ld_size hi.thr hg] at h1
  rcases (by unfold ThreadId at *; omega : e.tid = 0 ∨ e.tid = 1 ∨ e.tid = 2) with h | h | h <;>
    rw [h] at h2
  · exact h2
  · exact VClock.le_trans h2 (hi.join.1 (.inr hg))
  · exact VClock.le_trans h2 (hi.join.2 hg)

/-- The head holds a `u32`. -/
theorem head_val {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) : ∃ v, U32At m 0 0 v := by
  rcases hi.head with ⟨-, hu, -⟩ | ⟨l, -, -, -, -, hlast, -, -, vs, hvs, hsz, hv, -⟩
  · exact ⟨0, hu⟩
  · have hp : 0 < l.msgs.size := by rw [hsz]; exact chains_pos hvs
    refine ⟨BitVec.ofNat 32 vs[l.msgs.size - 1]!, ?_⟩
    unfold U32At
    rw [← hlast]
    unfold ALoc.lastBytes
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
    simp only [Option.map_some, Option.getD_some]
    exact hv _ (by omega)

/-- The bytes of a `Stack`: the head, then `next[0..3]`. -/
theorem decode_stack (B : Array Byte) {v0 v1 v2 v3 : BitVec 32}
    (h0 : intOfBytes 32 (B.extract 0 4) = pure v0) (h1 : intOfBytes 32 (B.extract 4 8) = pure v1)
    (h2 : intOfBytes 32 (B.extract 8 12) = pure v2) (h3 : intOfBytes 32 (B.extract 12 16) = pure v3) :
    (Enc.decode (B.extract 0 16) : Result Stack) = pure ⟨⟨v0⟩, #v[v1, v2, v3]⟩ := by
  have hr : Array.range 3 = #[0, 1, 2] := rfl
  have e1 : Enc.size (BitVec 32) = 4 := rfl
  have e2 : Enc.size atomic_Value_u32 = 4 := rfl
  have e3 : Enc.size (Vector (BitVec 32) 3) = 12 := rfl
  simp only [Enc.decode, Enc.decodeAt, Array.extract_extract, hr, Array.mapM_eq_mapM_toList]
  simp [e1, e2, e3, h0, h1, h2, h3]

theorem u32_blk {m : Mem} {blk : Block} {o : Nat} {v : BitVec 32} (hb : m.blocks[0]? = some blk)
    (h : U32At m 0 o v) : intOfBytes 32 (blk.bytes.extract o (o + 4)) = pure v := by
  unfold U32At curBytes at h; rw [hb] at h; exact ExceptT.ext h

/-- The decode of the `Stack` that `main` loads, from `next[0..3]`. -/
theorem whole_dec {G : ThreadId → Gh} {m : Mem} {blk : Block} {w0 w1 w2 : BitVec 32} (hi : Inv G m)
    (hb : m.blocks[0]? = some blk) (hn0 : NextAt m 0 w0) (hn1 : NextAt m 1 w1) (hn2 : NextAt m 2 w2) :
    ∃ v, (Enc.decode (blk.bytes.extract 0 (0 + Enc.size Stack)) : Result Stack) =
      pure ⟨⟨v⟩, #v[w0, w1, w2]⟩ := by
  obtain ⟨v, hv⟩ := head_val hi
  exact ⟨v, decode_stack blk.bytes (u32_blk hb hv) (u32_blk hb hn0) (u32_blk hb hn1) (u32_blk hb hn2)⟩

/-- `main`'s load of the whole `Stack` after both joins. -/
theorem step_whole {G : ThreadId → Gh} {m m' : Mem} {s : Stack} {w0 w1 w2 : BitVec 32} (hi : Inv G m)
    (hg : G 0 = .ld) (hc : m.current = 0) (hn0 : NextAt m 0 w0) (hn1 : NextAt m 1 w1)
    (hn2 : NextAt m 2 w2) (h : ((load Stack 4 sPtr).run m).run = some (.ok (s, m'))) :
    s.next = #v[w0, w1, w2] ∧ m' = m.recordAt 0 0 (Enc.size Stack) .read ∧ Inv G m' := by
  obtain ⟨b, blk, o, hacc, -, hdec, rfl⟩ := load_ok h
  obtain ⟨blk₀, hb₀, -, -, hacc₀⟩ := access_blk (p := sPtr) (a := 4) (len := Enc.size Stack) (o := 0)
    hi.b0 (by decide) (fun A hA => by omega) rfl
  rw [hacc₀] at hacc
  cases hacc
  obtain ⟨v, hd⟩ := whole_dec hi hb₀ hn0 hn1 hn2
  rw [hd] at hdec
  simp only [pure, ExceptT.pure, ExceptT.mk, ExceptT.run, Option.some.injEq, Except.ok.injEq] at hdec
  subst hdec
  have ht : m.current < m.threads.size := by rw [hc, ld_size hi.thr hg]; decide
  exact ⟨rfl, rfl, hi.record ht (.inl hc) (fun _ h => by cases h) (.inr (.inr (.inr (.inl ⟨rfl, rfl, hc, hg⟩))))⟩

theorem whole_noErr {G : ThreadId → Gh} {m : Mem} {w0 w1 w2 : BitVec 32} (hi : Inv G m)
    (hg : G 0 = .ld) (hc : m.current = 0) (hn0 : NextAt m 0 w0) (hn1 : NextAt m 1 w1)
    (hn2 : NextAt m 2 w2) (e : Error) : ((load Stack 4 sPtr).run m).run ≠ some (.error e) := by
  obtain ⟨blk₀, hb₀, -, -, hacc₀⟩ := access_blk (p := sPtr) (a := 4) (len := Enc.size Stack) (o := 0)
    hi.b0 (by decide) (fun A hA => by omega) rfl
  obtain ⟨v, hd⟩ := whole_dec hi hb₀ hn0 hn1 hn2
  have hnr : NoRace m 0 0 (Enc.size Stack) .read :=
    noRace_of fun e he _ _ _ => .inl (by rw [hc]; exact ld_le hi hg e he)
  exact MemM.noErr_of_run (load_run hacc₀ hd hnr) e

/-- `main`'s end: the frees of the three blocks; the result. -/
theorem main_end {G : ThreadId → Gh} {m : Mem} {d : Nat} {v : BitVec 32} (hi : Inv G m)
    (hg : G 0 = .ld) (hv : v = 120 ∨ v = 210) :
    proto.WP 0 (do
      Zig.free sPtr
      Zig.free (cPtr 1)
      Zig.free (cPtr 2)
      pure (Except.ok v : Except ErrName (BitVec 32)) : ConcM Tgt _) QM G m d := by
  obtain ⟨blk₀, hb₀, hl₀, -⟩ := hi.b0
  obtain ⟨blk₁, hb₁, hl₁, -⟩ := hi.b1
  obtain ⟨blk₂, hb₂, hl₂, -⟩ := hi.b2
  refine WP.bind (WP.liftMem (fun e he => (free_noErr hb₀ hl₀ e he).elim) fun _ m₁ hf₁ => ?_)
  obtain ⟨b', blk, hb', -, rfl⟩ := free_ok hf₁
  cases hb'
  refine ⟨rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun e he => (free_noErr (b := 1) (by
      simp only [Array.set!_eq_setIfInBounds]; rw [Array.getElem?_setIfInBounds_ne (by decide)]
      exact hb₁) hl₁ e he).elim) fun _ m₂ hf₂ => ?_)
  obtain ⟨b', blk', hb', -, rfl⟩ := free_ok hf₂
  cases hb'
  refine ⟨rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun e he => (free_noErr (b := 2) (by
      simp only [Array.set!_eq_setIfInBounds]
      rw [Array.getElem?_setIfInBounds_ne (by decide), Array.getElem?_setIfInBounds_ne (by decide)]
      exact hb₂) hl₂ e he).elim) fun _ m₃ hf₃ => ?_)
  obtain ⟨b', blk'', hb', -, rfl⟩ := free_ok hf₃
  cases hb'
  refine ⟨rfl, WP.pure' ⟨?_, joinedAll_ld hi.thr hg⟩⟩
  rcases hv with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl

/-! ## `main` before its spawns -/

/-- `main` before its spawns: `Solo`, with the three blocks. -/
structure Pre (m : Mem) : Prop extends Solo m where
  b0 : BlkAt m 0 16 4
  b1 : BlkAt m 1 16 8
  b2 : BlkAt m 2 16 8

/-- `main`'s store before its spawns, to block `b` at `o` (`solo_store`). -/
theorem pre_store {α : Type} [Enc α] {m m' : Mem} {b sz al o a : Nat} {v : α} (h : Pre m)
    (hb : BlkAt m b sz al) (hfit : o + (Enc.encode v).size ≤ sz)
    (hal : ∀ A : Nat, A % al = 0 → (A + o) % a = 0)
    (hs : ((store a ⟨some b, (o : Int)⟩ v).run m).run = some (.ok ((), m'))) :
    Pre m' ∧ curBytes m' b o (Enc.encode v).size = Enc.encode v ∧
      ∀ b' o' len, (b ≠ b' ∨ b' = b ∧ o' + len ≤ sz ∧ (o + (Enc.encode v).size ≤ o' ∨ o' + len ≤ o)) →
        curBytes m' b' o' len = curBytes m b' o' len := by
  obtain ⟨hs', hk, -, h1, h2⟩ := solo_store h.toSolo hb hfit hal hs
  exact ⟨{ toSolo := hs', b0 := hk _ _ _ h.b0, b1 := hk _ _ _ h.b1, b2 := hk _ _ _ h.b2 }, h1, h2⟩

theorem pre_store_noErr {α : Type} [Enc α] {m : Mem} {b sz al o a : Nat} {v : α} (h : Pre m)
    (hb : BlkAt m b sz al) (hfit : o + (Enc.encode v).size ≤ sz)
    (hal : ∀ A : Nat, A % al = 0 → (A + o) % a = 0) (e : Error) :
    ((store a ⟨some b, (o : Int)⟩ v).run m).run ≠ some (.error e) :=
  solo_store_noErr h.toSolo hb hfit hal e

/-- The start: before its spawns, `main` holds the invariant with the ghost value `pre`. -/
def G0 : ThreadId → Gh := fun u => if u = 0 then .pre else .none

theorem pre_inv {m : Mem} (h : Pre m) (hh : U32At m 0 0 0) (hn0 : NextAt m 0 0)
    (hc : ∀ u, (u = 1 ∨ u = 2) → curBytes m u 0 8 = Enc.encode sPtr ∧ U32At m u 8 (BitVec.ofNat 32 u)) :
    Inv G0 m where
  thr := by
    refine ⟨by rw [h.thr]; rfl, by rw [h.clk, h.thr]; rfl, .inl ⟨by rw [h.thr]; rfl, rfl, fun u hu => ?_⟩⟩
    unfold G0; split
    · rename_i h; unfold ThreadId at *; omega
    · rfl
  b0 := h.b0
  b1 := h.b1
  b2 := h.b2
  ctx := hc
  head := .inl ⟨h.at0, hh, fun u hu => by
    unfold G0; split
    · rename_i h0; rcases hu with rfl | rfl <;> cases h0
    · intro h; cases h⟩
  casn := fun u x hu hx => by unfold G0 at hx; split at hx <;> cases hx
  n0 := hn0
  join := ⟨fun h0 => by simp [G0] at h0, fun h0 => by simp [G0] at h0⟩
  fp := fun e he => .inl ⟨(h.fp e he).1, fun u hu => by
    have : u = 0 := by rw [h.thr] at hu; simp at hu; omega
    rw [this]; exact (h.fp e he).2.2⟩
  own := fun e he => by
    obtain ⟨-, h2, h3⟩ := h.fp e he
    rw [h2]; exact ⟨by rw [h.thr]; decide, h3⟩

/-- `next[k]`, from the index that `main` computes (`@intCast` of a `u32` to `usize`). -/
theorem next_ptr (k : Nat) (hk : k < 3) :
    (sPtr.add 4).elem 4 (BitVec.ofInt 64 (val false (BitVec.ofNat 32 k))) =
      ⟨some 0, ((4 + 4 * k : Nat) : Int)⟩ := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> rfl

theorem next_lt (k : Nat) (hk : k < 3) :
    lt false (BitVec.ofInt 64 (val false (BitVec.ofNat 32 k))) 3 = true := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> rfl

theorem main_spec (d : Nat) : proto.WP 0 stackPush QM G0 { mem0 with current := 0 } d := by
  unfold stackPush
  -- the blocks: the `Stack`, the two `PushCtx`
  refine WP.bind (WP.liftMem (fun e h => (alloc_noErr e h).elim) fun s0 m₁ ha₁ => ?_)
  obtain ⟨hq₁, hm₁⟩ := alloc_ok ha₁
  have e0 : s0 = sPtr := by rw [hq₁]; rfl
  subst e0 hm₁
  refine ⟨rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun e h => (alloc_noErr e h).elim) fun s1 m₂ ha₂ => ?_)
  obtain ⟨hq₂, hm₂⟩ := alloc_ok ha₂
  have e1 : s1 = cPtr 1 := by rw [hq₂]; rfl
  subst e1 hm₂
  refine ⟨rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun e h => (alloc_noErr e h).elim) fun s2 m₃ ha₃ => ?_)
  obtain ⟨hq₃, hm₃⟩ := alloc_ok ha₃
  have e2 : s2 = cPtr 2 := by rw [hq₃]; rfl
  subst e2
  refine ⟨by rw [hm₃], ?_⟩
  have hp₃ : Pre m₃ := by
    rw [hm₃]
    exact { toSolo := ⟨rfl, rfl, rfl, rfl, fun e he => by simp [mem0, Mem.ofGlobals] at he⟩
            b0 := ⟨_, rfl, rfl, rfl, rfl, by decide⟩
            b1 := ⟨_, rfl, rfl, rfl, rfl, by decide⟩
            b2 := ⟨_, rfl, rfl, rfl, rfl, by decide⟩ }
  clear hm₃ ha₃ hq₃
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [show sPtr.add 0 = ⟨some 0, ((0 : Nat) : Int)⟩ from rfl,
    show (sPtr.add 4).elem 4 0 = ⟨some 0, ((4 : Nat) : Int)⟩ from rfl,
    show (sPtr.add 4).elem 4 1 = ⟨some 0, ((8 : Nat) : Int)⟩ from rfl,
    show (sPtr.add 4).elem 4 2 = ⟨some 0, ((12 : Nat) : Int)⟩ from rfl]
  -- `head = .init(0)`
  refine WP.bind (WP.callRC (fun e he => by
    have he' : (atomic_Value_u32_init 0).run = some (.error e) := he
    rw [MP.init_run] at he'; cases he') fun a ha => ?_)
  have ha' : (atomic_Value_u32_init 0).run = some (.ok a) := ha
  rw [MP.init_run] at ha'
  cases ha'
  refine WP.bind (WP.liftM (fun e he => (pre_store_noErr hp₃ hp₃.b0 (by rw [MP.enc_av4]; omega)
    (fun A hA => by omega) e he).elim) fun _ m₄ hs₄ => ?_)
  obtain ⟨hp₄, hh₄, -⟩ := pre_store hp₃ hp₃.b0 (by rw [MP.enc_av4]; omega) (fun A hA => by omega) hs₄
  refine ⟨by rw [hp₄.thr, hp₃.thr], ?_⟩
  have hH₄ : U32At m₄ 0 0 0 := by
    unfold U32At; rw [MP.enc_av4] at hh₄; rw [hh₄, MP.enc_av]; exact intOfBytes_rmw 0
  -- `next = .{ 0, 0, 0 }`
  refine WP.bind (WP.liftM (fun e he => (pre_store_noErr hp₄ hp₄.b0 (by rw [size_encode_u32]; omega)
    (fun A hA => by omega) e he).elim) fun _ m₅ hs₅ => ?_)
  obtain ⟨hp₅, hz₅, hk₅⟩ := pre_store hp₄ hp₄.b0 (by rw [size_encode_u32]; omega) (fun A hA => by omega) hs₅
  have hN₅ : NextAt m₅ 0 0 := by
    unfold NextAt U32At; rw [size_encode_u32] at hz₅; rw [hz₅]; exact intOfBytes_rmw 0
  refine ⟨by rw [hp₅.thr, hp₄.thr], ?_⟩
  have hH₅ : U32At m₅ 0 0 0 := by
    unfold U32At; rw [hk₅ 0 0 4 (.inr ⟨rfl, by decide, .inr (by decide)⟩)]; exact hH₄
  refine WP.bind (WP.liftM (fun e he => (pre_store_noErr hp₅ hp₅.b0 (by rw [size_encode_u32]; omega)
    (fun A hA => by omega) e he).elim) fun _ m₆ hs₆ => ?_)
  obtain ⟨hp₆, -, hk₆⟩ := pre_store hp₅ hp₅.b0 (by rw [size_encode_u32]; omega) (fun A hA => by omega) hs₆
  refine ⟨by rw [hp₆.thr, hp₅.thr], ?_⟩
  have hH₆ : U32At m₆ 0 0 0 := by
    unfold U32At; rw [hk₆ 0 0 4 (.inr ⟨rfl, by decide, .inr (by decide)⟩)]; exact hH₅
  refine WP.bind (WP.liftM (fun e he => (pre_store_noErr hp₆ hp₆.b0 (by rw [size_encode_u32]; omega)
    (fun A hA => by omega) e he).elim) fun _ m₇ hs₇ => ?_)
  obtain ⟨hp₇, -, hk₇⟩ := pre_store hp₆ hp₆.b0 (by rw [size_encode_u32]; omega) (fun A hA => by omega) hs₇
  refine ⟨by rw [hp₇.thr, hp₆.thr], ?_⟩
  have hN₇ : NextAt m₇ 0 0 := by
    unfold NextAt U32At
    rw [hk₇ 0 4 4 (.inr ⟨rfl, by decide, .inr (by decide)⟩), hk₆ 0 4 4 (.inr ⟨rfl, by decide, .inr (by decide)⟩)]
    exact hN₅
  have hH₇ : U32At m₇ 0 0 0 := by
    unfold U32At; rw [hk₇ 0 0 4 (.inr ⟨rfl, by decide, .inr (by decide)⟩)]; exact hH₆
  -- the `PushCtx` of pusher 1
  dsimp only
  rw [show (cPtr 1).add 0 = ⟨some 1, ((0 : Nat) : Int)⟩ from rfl,
    show (cPtr 1).add 8 = ⟨some 1, ((8 : Nat) : Int)⟩ from rfl]
  refine WP.bind (WP.liftM (fun e he => (pre_store_noErr hp₇ hp₇.b1 (by rw [size_encode_ptr]; omega)
    (fun A hA => by omega) e he).elim) fun _ m₈ hs₈ => ?_)
  obtain ⟨hp₈, hs1₈, hk₈⟩ := pre_store hp₇ hp₇.b1 (by rw [size_encode_ptr]; omega) (fun A hA => by omega) hs₈
  refine ⟨by rw [hp₈.thr, hp₇.thr], ?_⟩
  refine WP.bind (WP.liftM (fun e he => (pre_store_noErr hp₈ hp₈.b1 (by rw [size_encode_u32]; omega)
    (fun A hA => by omega) e he).elim) fun _ m₉ hs₉ => ?_)
  obtain ⟨hp₉, hn1₉, hk₉⟩ := pre_store hp₈ hp₈.b1 (by rw [size_encode_u32]; omega) (fun A hA => by omega) hs₉
  refine ⟨by rw [hp₉.thr, hp₈.thr], ?_⟩
  -- the `PushCtx` of pusher 2
  dsimp only
  rw [show (cPtr 2).add 0 = ⟨some 2, ((0 : Nat) : Int)⟩ from rfl,
    show (cPtr 2).add 8 = ⟨some 2, ((8 : Nat) : Int)⟩ from rfl]
  refine WP.bind (WP.liftM (fun e he => (pre_store_noErr hp₉ hp₉.b2 (by rw [size_encode_ptr]; omega)
    (fun A hA => by omega) e he).elim) fun _ m₁₀ hs₁₀ => ?_)
  obtain ⟨hp₁₀, hs2₁₀, hk₁₀⟩ := pre_store hp₉ hp₉.b2 (by rw [size_encode_ptr]; omega) (fun A hA => by omega) hs₁₀
  refine ⟨by rw [hp₁₀.thr, hp₉.thr], ?_⟩
  refine WP.bind (WP.liftM (fun e he => (pre_store_noErr hp₁₀ hp₁₀.b2 (by rw [size_encode_u32]; omega)
    (fun A hA => by omega) e he).elim) fun _ m₁₁ hs₁₁ => ?_)
  obtain ⟨hp₁₁, hn2₁₁, hk₁₁⟩ := pre_store hp₁₀ hp₁₀.b2 (by rw [size_encode_u32]; omega) (fun A hA => by omega) hs₁₁
  refine ⟨by rw [hp₁₁.thr, hp₁₀.thr], ?_⟩
  have hi₁₁ : Inv G0 m₁₁ := by
    refine pre_inv hp₁₁ ?_ ?_ fun u hu => ?_
    · unfold U32At
      rw [hk₁₁ 0 0 4 (.inl (by decide)), hk₁₀ 0 0 4 (.inl (by decide)), hk₉ 0 0 4 (.inl (by decide)),
        hk₈ 0 0 4 (.inl (by decide))]
      exact hH₇
    · unfold NextAt U32At
      rw [hk₁₁ 0 4 4 (.inl (by decide)), hk₁₀ 0 4 4 (.inl (by decide)), hk₉ 0 4 4 (.inl (by decide)),
        hk₈ 0 4 4 (.inl (by decide))]
      exact hN₇
    · rcases hu with rfl | rfl
      · refine ⟨?_, ?_⟩
        · rw [hk₁₁ 1 0 8 (.inl (by decide)), hk₁₀ 1 0 8 (.inl (by decide)),
            hk₉ 1 0 8 (.inr ⟨rfl, by decide, .inr (by decide)⟩)]
          rw [size_encode_ptr] at hs1₈; exact hs1₈
        · unfold U32At
          rw [hk₁₁ 1 8 4 (.inl (by decide)), hk₁₀ 1 8 4 (.inl (by decide))]
          rw [size_encode_u32] at hn1₉; rw [hn1₉]; exact intOfBytes_rmw 1
      · refine ⟨?_, ?_⟩
        · rw [hk₁₁ 2 0 8 (.inr ⟨rfl, by decide, .inr (by decide)⟩)]
          rw [size_encode_ptr] at hs2₁₀; exact hs2₁₀
        · unfold U32At
          rw [size_encode_u32] at hn2₁₁; rw [hn2₁₁]; exact intOfBytes_rmw 2
  have hG0 : upd G0 0 .pre = G0 := by
    funext u; unfold upd G0; split <;> simp_all
  -- the spawns
  refine WP.bind (WP.spawnC fun k hk => ⟨.pre, by rw [hG0]; exact hi₁₁, fun G₁ m₁₂ hg₁ hi₁₂ =>
    ⟨.start 1, by simp [proto], fun child m₁₃ hf => ?_⟩⟩)
  obtain ⟨rfl, hc₁₃, hi₁₃⟩ := inv_fork1 ((hi₁₂ : Inv G₁ m₁₂).grow (growsAt_current m₁₂ 0) (.inl rfl)) hg₁ rfl hf
  dsimp only
  simp only [StateT.run_bind]
  refine WP.bind (WP.spawnC fun k₂ hk₂ => ⟨Gh.mid, hi₁₃, fun G₂ m₁₄ hg₂ hi₁₄ =>
    ⟨Gh.start 2, by simp [proto, cPtr], fun child m₁₅ hf => ?_⟩⟩)
  obtain ⟨rfl, hc₁₅, hi₁₅⟩ := inv_fork2 ((hi₁₄ : Inv G₂ m₁₄).grow (growsAt_current m₁₄ 0) (.inl rfl)) hg₂ rfl hf
  dsimp only
  simp only [StateT.run_bind]
  -- the joins
  refine WP.bind (WP.joinC fun k₃ hk₃ => ⟨Gh.j1, hi₁₅, fun G₃ m₁₆ hg₃ hi₁₆ =>
    ⟨fun _ => ⟨by decide, by rw [size3 (hi₁₆ : Inv G₃ m₁₆).thr (.inl hg₃)]; decide, .inl rfl, by
      obtain ⟨m', hj⟩ := join_ok hi₁₆ (.inl ⟨hg₃, rfl⟩)
      exact Proto.join_valid hj⟩, fun hfin =>
      ⟨fun _ => join_ok hi₁₆ (.inl ⟨hg₃, rfl⟩), fun m₁₇ hj => ?_⟩⟩⟩)
  obtain ⟨hc₁₇, hs₁₇, hi₁₇⟩ := inv_join hi₁₆ (.inl ⟨hg₃, rfl, rfl⟩) hfin hj
  refine WP.bind (WP.joinC fun k₄ hk₄ => ⟨Gh.j2, hi₁₇, fun G₄ m₁₈ hg₄ hi₁₈ =>
    ⟨fun _ => ⟨by decide, by rw [size3 (hi₁₈ : Inv G₄ m₁₈).thr (.inr (.inl hg₄))]; decide, .inr rfl, by
      obtain ⟨m', hj⟩ := join_ok hi₁₈ (.inr ⟨hg₄, rfl⟩)
      exact Proto.join_valid hj⟩, fun hfin =>
      ⟨fun _ => join_ok hi₁₈ (.inr ⟨hg₄, rfl⟩), fun m₁₉ hj => ?_⟩⟩⟩)
  obtain ⟨hc₁₉, hs₁₉, hi₁₉⟩ := inv_join hi₁₈ (.inr ⟨hg₄, rfl, rfl⟩) hfin hj
  -- the acquire load of the head (a stop)
  rw [show (⟨some 0, ((0 : Nat) : Int)⟩ : Ptr).add 0 = sPtr from rfl]
  simp only [StateT.run_bind, atomicLoadC]
  refine WP.bind (WP.bind (WP.bind (WP.pickC fun k₅ hk₅ => ⟨Gh.ld, hi₁₉, fun G₅ m₂₀ hg₅ hi₂₀ c hcr => ?_⟩)))
  have hi₂₀' : Inv G₅ { m₂₀ with current := 0 } :=
    (hi₂₀ : Inv G₅ m₂₀).grow (growsAt_current m₂₀ 0) (.inl rfl)
  have ht₂₀ : ({ m₂₀ with current := 0 } : Mem).current < ({ m₂₀ with current := 0 } : Mem).threads.size := by
    show 0 < _; rw [ld_size hi₂₀'.thr hg₅]; decide
  refine WP.callMC (fun e he => (rload_noErr hi₂₀' ht₂₀ (.inl rfl) hcr e he).elim) fun v m₂₁ hl => ?_
  obtain ⟨hc₂₁, hth₂₁, hi₂₁, a, b, hab, rfl, hnb, hna⟩ := step_top hi₂₀' hg₅ rfl hl
  refine ⟨by rw [hth₂₁], ?_⟩
  have hg₂₁ : G₅ 0 = .ld := hg₅
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind]
  have ha3 : a < 3 := by rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hb3 : b < 3 := by rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hak : a = 1 ∨ a = 2 := by rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hbk : b = 1 ∨ b = 2 := by rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  -- `100 * top`, the cast, the bounds check
  refine WP.bind (WP.callRC_ok (x := mul false 100 (BitVec.ofNat 32 b)) (v := BitVec.ofNat 32 (100 * b))
    (by rcases hbk with rfl | rfl <;> rfl) ?_)
  first
  | -- Zig 0.16.0: `next[k]` through a pointer into the `Stack`
      refine WP.bind (WP.callRC_ok (x := intCast false false 64 (BitVec.ofNat 32 b))
        (v := BitVec.ofInt 64 (val false (BitVec.ofNat 32 b))) (by rcases hbk with rfl | rfl <;> rfl) ?_)
      dsimp only
      simp only [next_lt b hb3, ↓reduceIte, StateT.run_pure, pure_bind, StateT.run_bind]
      rw [next_ptr b hb3]
      -- `next[top]`
      refine WP.bind (WP.callMC (fun e he => (rd_noErr hi₂₁ hg₂₁ hc₂₁ hbk hnb e he).elim) fun v m₂₂ hl => ?_)
      obtain ⟨rfl, rfl, hi₂₂⟩ := step_rd hi₂₁ hg₂₁ hc₂₁ hbk hnb hl
      refine ⟨rfl, ?_⟩
      -- `10 * next[top]`, the sum, the cast, the bounds check
      refine WP.bind (WP.callRC_ok (x := mul false 10 (BitVec.ofNat 32 a)) (v := BitVec.ofNat 32 (10 * a))
        (by rcases hak with rfl | rfl <;> rfl) ?_)
      refine WP.bind (WP.callRC_ok (x := add false (BitVec.ofNat 32 (100 * b)) (BitVec.ofNat 32 (10 * a)))
        (v := BitVec.ofNat 32 (100 * b + 10 * a))
        (by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl) ?_)
      refine WP.bind (WP.callRC_ok (x := intCast false false 64 (BitVec.ofNat 32 b))
        (v := BitVec.ofInt 64 (val false (BitVec.ofNat 32 b))) (by rcases hbk with rfl | rfl <;> rfl) ?_)
      dsimp only
      simp only [next_lt b hb3, ↓reduceIte, StateT.run_pure, pure_bind, StateT.run_bind]
      rw [next_ptr b hb3]
      -- `next[top]` again
      have hnb₂ := nextAt_congr (m := m₂₁) (m' := m₂₁.recordAt 0 (4 + 4 * b) (Enc.size (BitVec 32)) .read) rfl hnb
      refine WP.bind (WP.callMC (fun e he => (rd_noErr hi₂₂ hg₂₁ hc₂₁ hbk hnb₂ e he).elim) fun v m₂₃ hl => ?_)
      obtain ⟨rfl, rfl, hi₂₃⟩ := step_rd hi₂₂ hg₂₁ hc₂₁ hbk hnb₂ hl
      refine ⟨rfl, ?_⟩
      -- the cast of `next[top]`, the bounds check, `next[next[top]]`
      refine WP.bind (WP.callRC_ok (x := intCast false false 64 (BitVec.ofNat 32 a))
        (v := BitVec.ofInt 64 (val false (BitVec.ofNat 32 a))) (by rcases hak with rfl | rfl <;> rfl) ?_)
      dsimp only
      simp only [next_lt a ha3, ↓reduceIte, StateT.run_pure, pure_bind, StateT.run_bind]
      rw [next_ptr a ha3]
      have hna₃ := nextAt_congr (m := m₂₁) (m' := (m₂₁.recordAt 0 (4 + 4 * b) (Enc.size (BitVec 32)) .read).recordAt 0
        (4 + 4 * b) (Enc.size (BitVec 32)) .read) rfl hna
      refine WP.bind (WP.callMC (fun e he => (rd_noErr hi₂₃ hg₂₁ hc₂₁ hak hna₃ e he).elim) fun v m₂₄ hl => ?_)
      obtain ⟨rfl, rfl, hi₂₄⟩ := step_rd hi₂₃ hg₂₁ hc₂₁ hak hna₃ hl
      refine ⟨rfl, ?_⟩
      refine WP.bind (WP.callRC_ok (x := add false (BitVec.ofNat 32 (100 * b + 10 * a)) 0)
        (v := BitVec.ofNat 32 (100 * b + 10 * a)) (by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl) ?_)
      refine WP.pure' ?_
      exact main_end hi₂₄ hg₂₁ (by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
  | -- Zig 0.15.2: a load of the whole `Stack`, then an index into its `next`
    obtain ⟨w1, w2, hn1, hn2, hw⟩ : ∃ w1 w2 : BitVec 32, NextAt m₂₁ 1 w1 ∧ NextAt m₂₁ 2 w2 ∧
        ((a = 1 ∧ b = 2 ∧ w1 = 0 ∧ w2 = 1) ∨ (a = 2 ∧ b = 1 ∧ w1 = 2 ∧ w2 = 0)) := by
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, 1, hna, hnb, .inl ⟨rfl, rfl, rfl, rfl⟩⟩
      · exact ⟨2, 0, hnb, hna, .inr ⟨rfl, rfl, rfl, rfl⟩⟩
    refine WP.bind (WP.liftM (fun e he => (whole_noErr hi₂₁ hg₂₁ hc₂₁ hi₂₁.n0 hn1 hn2 e he).elim)
      fun s m₂₂ hl => ?_)
    obtain ⟨hs, rfl, hi₂₂⟩ := step_whole hi₂₁ hg₂₁ hc₂₁ hi₂₁.n0 hn1 hn2 hl
    refine ⟨rfl, ?_⟩
    -- the cast, the bounds check, `next[top]`, `10 * next[top]`, the sum
    refine WP.bind (WP.callRC_ok (x := intCast false false 64 (BitVec.ofNat 32 b))
      (v := BitVec.ofInt 64 (val false (BitVec.ofNat 32 b))) (by rcases hbk with rfl | rfl <;> rfl) ?_)
    dsimp only
    simp only [next_lt b hb3, ↓reduceIte, StateT.run_pure, pure_bind, StateT.run_bind]
    rw [hs]
    refine WP.bind (WP.callRC_ok (x := vindex #v[0, w1, w2] (BitVec.ofInt 64 (val false (BitVec.ofNat 32 b))))
      (v := BitVec.ofNat 32 a) (by rcases hw with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> rfl) ?_)
    refine WP.bind (WP.callRC_ok (x := mul false 10 (BitVec.ofNat 32 a)) (v := BitVec.ofNat 32 (10 * a))
      (by rcases hak with rfl | rfl <;> rfl) ?_)
    refine WP.bind (WP.callRC_ok (x := add false (BitVec.ofNat 32 (100 * b)) (BitVec.ofNat 32 (10 * a)))
      (v := BitVec.ofNat 32 (100 * b + 10 * a))
      (by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl) ?_)
    -- two more loads of the `Stack`
    have hn1' := nextAt_congr (m' := m₂₁.recordAt 0 0 (Enc.size Stack) .read) rfl hn1
    have hn2' := nextAt_congr (m' := m₂₁.recordAt 0 0 (Enc.size Stack) .read) rfl hn2
    refine WP.bind (WP.liftM (fun e he => (whole_noErr hi₂₂ hg₂₁ hc₂₁ hi₂₂.n0 hn1' hn2' e he).elim)
      fun s' m₂₃ hl => ?_)
    obtain ⟨hs', rfl, hi₂₃⟩ := step_whole hi₂₂ hg₂₁ hc₂₁ hi₂₂.n0 hn1' hn2' hl
    refine ⟨rfl, ?_⟩
    have hn1'' := nextAt_congr (m' := (m₂₁.recordAt 0 0 (Enc.size Stack) .read).recordAt 0 0 (Enc.size Stack) .read) rfl hn1
    have hn2'' := nextAt_congr (m' := (m₂₁.recordAt 0 0 (Enc.size Stack) .read).recordAt 0 0 (Enc.size Stack) .read) rfl hn2
    refine WP.bind (WP.liftM (fun e he => (whole_noErr hi₂₃ hg₂₁ hc₂₁ hi₂₃.n0 hn1'' hn2'' e he).elim)
      fun s'' m₂₄ hl => ?_)
    obtain ⟨hs'', rfl, hi₂₄⟩ := step_whole hi₂₃ hg₂₁ hc₂₁ hi₂₃.n0 hn1'' hn2'' hl
    refine ⟨rfl, ?_⟩
    -- the cast, the bounds check, `next[top]`
    refine WP.bind (WP.callRC_ok (x := intCast false false 64 (BitVec.ofNat 32 b))
      (v := BitVec.ofInt 64 (val false (BitVec.ofNat 32 b))) (by rcases hbk with rfl | rfl <;> rfl) ?_)
    dsimp only
    simp only [next_lt b hb3, ↓reduceIte, StateT.run_pure, pure_bind, StateT.run_bind]
    rw [hs'']
    refine WP.bind (WP.callRC_ok (x := vindex #v[0, w1, w2] (BitVec.ofInt 64 (val false (BitVec.ofNat 32 b))))
      (v := BitVec.ofNat 32 a) (by rcases hw with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> rfl) ?_)
    -- the cast of `next[top]`, the bounds check, `next[next[top]]`, the sum
    refine WP.bind (WP.callRC_ok (x := intCast false false 64 (BitVec.ofNat 32 a))
      (v := BitVec.ofInt 64 (val false (BitVec.ofNat 32 a))) (by rcases hak with rfl | rfl <;> rfl) ?_)
    dsimp only
    simp only [next_lt a ha3, ↓reduceIte, StateT.run_pure, pure_bind, StateT.run_bind]
    rw [hs']
    refine WP.bind (WP.callRC_ok (x := vindex #v[0, w1, w2] (BitVec.ofInt 64 (val false (BitVec.ofNat 32 a))))
      (v := 0) (by rcases hw with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> rfl) ?_)
    refine WP.bind (WP.callRC_ok (x := add false (BitVec.ofNat 32 (100 * b + 10 * a)) 0)
      (v := BitVec.ofNat 32 (100 * b + 10 * a)) (by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl) ?_)
    refine WP.pure' ?_
    exact main_end hi₂₄ hg₂₁ (by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)

/-! ## The results -/

/-- **`stackPush` gives 120 or 210 under every schedule** (every oracle `o`, every `fuel`): both
nodes are on the stack, the top one first, then the other, then 0. -/
theorem stackPush_spec {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run dispatch fuel o stackPush mem0).run = some (.ok (v, m))) :
    v = .ok 120 ∨ v = .ok 210 := by
  obtain ⟨_, _, hv, -⟩ := proto.run_sound dispatch G0 dispatch_spec
    (fun _ _ _ _ _ hq => hq.2) rfl main_spec h
  exact hv

/-- **No run of `stackPush` gives an error**: no data race on `next`, no out-of-bounds index, no
overflow, under every schedule. -/
theorem stackPush_safe {fuel : Nat} {o : Nat → Nat} {e : Error} :
    (Sched.run dispatch fuel o stackPush mem0).run ≠ some (.error e) :=
  proto.run_safe dispatch G0 rfl dispatch_spec (fun _ _ _ _ hq => hq.2) rfl main_spec

/-! ## Non-vacuity witnesses

`memW` is `main`'s memory before its spawns as `main_spec` builds it: the `Stack` (head 0,
`next[0] = 0`) and the two `PushCtx`, so `pre_inv` gives the invariant. -/

/-- A `stack` block of 16 bytes at `addr`. -/
def blkW (bs : Array Byte) (addr : Nat) : Block :=
  { bytes := bs ++ Array.replicate (16 - bs.size) .undef, align := 8, kind := .stack, live := true,
    addr }

def memW : Mem :=
  { blocks := #[blkW (Enc.encode (0 : BitVec 32) ++ Enc.encode (0 : BitVec 32)) 4096,
      blkW (Enc.encode sPtr ++ Enc.encode (1 : BitVec 32)) 8192,
      blkW (Enc.encode sPtr ++ Enc.encode (2 : BitVec 32)) 12288],
    nextAddr := 12288 + 17 }

theorem memW_inv : Inv G0 memW :=
  pre_inv ⟨⟨rfl, rfl, rfl, rfl, fun _ h => by simp [memW] at h⟩, ⟨_, rfl, rfl, by decide +kernel, rfl, rfl⟩,
      ⟨_, rfl, rfl, by decide +kernel, rfl, rfl⟩, ⟨_, rfl, rfl, by decide +kernel, rfl, rfl⟩⟩
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (fun u hu => by rcases hu with rfl | rfl <;> exact ⟨by decide +kernel, by with_unfolding_all rfl⟩)

nonvacuity_witness ctxS_dec := ⟨G0, memW, 1, memW_inv, .inl rfl, trivial⟩
nonvacuity_witness ctxN_dec := ⟨G0, memW, 1, memW_inv, .inl rfl, trivial⟩

nonvacuity_witness decode_stack :=
  ⟨Array.replicate 16 (.int 0), 0, 0, 0, 0, by with_unfolding_all rfl, by with_unfolding_all rfl,
    by with_unfolding_all rfl, by with_unfolding_all rfl, trivial⟩

nonvacuity_witness u32_blk :=
  ⟨Witness.mem1 (Enc.encode (0 : BitVec 32)), Witness.blk (Enc.encode (0 : BitVec 32)), 0, 0, rfl,
    by with_unfolding_all rfl, trivial⟩

end Atomics.Stack
