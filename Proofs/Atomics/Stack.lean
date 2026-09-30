import Proofs.Atomics.MessagePassing

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
  l.block = 0 ∧ l.off = 0 ∧ l.len = 4 ∧ ALoc.lastBytes l = curBytes m 0 0 4 ∧ l.Chain ∧
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
pusher `u`'s write of `next[u]`; `main`'s read of `next` after both joins; a read of a
`PushCtx`. -/
def FpOk (G : ThreadId → Gh) (m : Mem) (e : FootprintEntry) : Prop :=
  (e.kind = .write ∧ Before m e.clock) ∨
  (e.block = 0 ∧ e.off = 0 ∧ e.len ≤ 4 ∧ e.kind.isAtomic = true) ∨
  (e.block = 0 ∧ e.kind = .write ∧ (e.tid = 1 ∨ e.tid = 2) ∧ e.off = 4 + 4 * e.tid ∧ e.len = 4) ∨
  (e.block = 0 ∧ e.kind = .read ∧ 4 ≤ e.off ∧ G 0 = .ld) ∨
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
  join : JoinLe G m
  fp : ∀ e ∈ m.footprint, FpOk G m e
  own : ∀ e ∈ m.footprint, e.tid < m.threads.size ∧ VClock.le e.clock (m.clocks[e.tid]!) = true

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv := Inv
  init
    | .push p => if p = cPtr 1 then some (.start 1) else if p = cPtr 2 then some (.start 2) else none
    | _ => none
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
    rcases hi.head with ⟨ha, hu, hn⟩ | ⟨l, ha, hlb, hlo, hll, hlast, hc, vs, hvs, hsz, hv, hd, hnx, hcl⟩
    · exact .inl ⟨hg.grows.atomics ▸ ha, by unfold U32At; rw [curBytes_congr hg.grows.blocks]; exact hu, hn⟩
    · refine .inr ⟨l, hg.grows.atomics ▸ ha, hlb, hlo, hll, by rw [curBytes_congr hg.grows.blocks]; exact hlast,
        hc, vs, hvs, hsz, hv, hd, fun j hj => ?_, fun j hj => VClock.le_trans (hcl j hj) (hg.grows.cle _)⟩
      unfold NextAt U32At; rw [curBytes_congr hg.grows.blocks]; exact hnx j hj
  casn := fun u h hu hc => by unfold NextAt U32At; rw [curBytes_congr hg.grows.blocks]; exact hi.casn u h hu hc
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
    (ht : m.current < m.threads.size) (ha : Act G m.current)
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
  exact {
    thr := hi₁.thr, b0 := hi₁.b0, b1 := hi₁.b1, b2 := hi₁.b2, ctx := hi₁.ctx, head := hi₁.head
    casn := hi₁.casn, join := hi₁.join
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

/-! ## The head's atomic location -/

/-- The first location of the head (`firstLoc`) is a `HeadLoc`. -/
theorem headLoc_first {G : ThreadId → Gh} {m : Mem} (hu : U32At m 0 0 0)
    (hn : ∀ u, (u = 1 ∨ u = 2) → G u ≠ .done) : HeadLoc G m (firstLoc m 0 0 4) := by
  refine ⟨rfl, rfl, rfl, rfl, fun j hj => by simp [firstLoc] at hj, [0], by simp [Chains], rfl,
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
      ALoc.lastBytes l = curBytes m 0 0 4 := by
    rcases hf with ⟨ha, -⟩ | ⟨l, ha, hlb, hlo, hll, hlast, -⟩
    · exact .inl ha
    · exact .inr ⟨l, ha, hlb, hlo, hll, hlast⟩
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
  obtain ⟨-, -, -, -, -, vs, hvs, hsz, -⟩ := h
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
    (hi : Inv G m) (ht : m.current < m.threads.size) : NoRace m 0 0 (intSize 32) k :=
  noRace_inv hi ht fun e _ hb h1 h2 hf => by
    have h4 : intSize 32 = 4 := by decide
    rw [h4] at h2
    rcases hf with h | ⟨-, -, -, ha⟩ | ⟨-, -, -, ho, -⟩ | ⟨-, -, ho, -⟩ | ⟨h, -⟩
    · exact .inl h
    · exact .inr (.inr (racePair_atomic ha hk))
    · omega
    · omega
    · rcases h with h | h <;> exact (blk_ne h hb (by decide)).elim

end Atomics.Stack
