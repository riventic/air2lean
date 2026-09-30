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
  head := by unfold HeadOk HeadLoc NextAt U32At; simp only [ha, curBytes_congr hb, hc]; exact hi.head
  casn := by unfold NextAt U32At; simp only [curBytes_congr hb]; exact hi.casn
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
  exact ⟨hdec.symm, rfl, hi.record ht hact (.inr (.inr (.inr (.inr ⟨hu, rfl⟩))))⟩

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
      rcases hi.head with ⟨ha, hu0, hn⟩ | ⟨l, ha, hlb, hlo, hll, hlast, hc, vs, hvs, hsz', hv, hd, hnxt, hcl⟩
      · refine .inl ⟨ha, ?_, fun v hv => ?_⟩
        · unfold U32At
          rw [curBytes_write_other hb hfit (.inr ⟨rfl, by rw [hsz]; decide, .inr (by omega)⟩)]
          exact hu0
        · by_cases hvu : v = u
          · subst hvu; rw [upd_self]; exact fun h => by cases h
          · rw [hne v hvu]; exact hn v hv
      · have hnu : u ∉ vs := fun h => hnd ((hd u hu).mpr h)
        refine .inr ⟨l, ha, hlb, hlo, hll, ?_, hc, vs, hvs, hsz', hv, fun v hv => ?_, fun j hj => ?_, hcl⟩
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
    (.inr ⟨by rw [hc]; exact hu, by rw [hc]; exact hnd⟩)
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
    (.inr (.inl ⟨rfl, rfl, show intSize 32 ≤ 4 by decide, rfl⟩))
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
  obtain ⟨-, -, -, -, -, vs, -, -, hv, -⟩ := h
  exact ⟨_, by rw [getElem!_pos l.msgs pos hp]; exact hv pos hp⟩

theorem rload_noErr {G : ThreadId → Gh} {m : Mem} {c : Nat} {ord : AtomicOrder} (hi : Inv G m)
    (ht : m.current < m.threads.size) (hact : Act G m.current)
    (hcr : c < loadCount 32 ord 4 sPtr m ∨ loadCount 32 ord 4 sPtr m = 0 ∧ c = 0)
    (e : Error) : ((atomicLoadAt (n := 32) c ord 4 sPtr).run m).run ≠ some (.error e) := by
  obtain ⟨blk₀, -, -, -, hacc₀⟩ := access_blk (p := sPtr) (a := 4) (len := intSize 32) (o := 0)
    hi.b0 (by decide) (fun A hA => by omega) rfl
  have hir := hi.record (b := 0) (o := 0) (len := intSize 32) (k := .atomicRead) ht hact
    (.inr (.inl ⟨rfl, rfl, show intSize 32 ≤ 4 by decide, rfl⟩))
  refine atomicLoadAt_noErr (loadPrep_noErr (rmw := false) (by simpa using hacc₀)
    (by simpa using noRace_head (k := .atomicRead) rfl hi ht)
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
    (hcl : VClock.le msg.clock (M.clocks[u]!) = true) :
    Inv (upd G u .done) { M.write 0 blk 0 msg.bytes with atomics := #[{ l with msgs := l.msgs.push msg }] } := by
  obtain ⟨hlb, hlo, hll, -, hc, vs, hvs, hsz, hval, hd, hnxt, hclk⟩ : HeadLoc G M l := by
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
    head := .inr ⟨_, rfl, hlb, hlo, hll, hlast', hc.push h0 hr, vs ++ [u], chains_push hvs hu hnu,
      by simp [hsz], fun j hj => ?_, fun v hv => ?_, fun j hj => ?_, fun j hj => ?_⟩
    casn := fun v x hv hcx => by
      by_cases hvu : v = u
      · subst hvu; rw [upd_self] at hcx; cases hcx
      · rw [upd_ne _ _ hvu] at hcx
        exact hnx v x (by rcases hv with rfl | rfl <;> decide) (hi.casn v x hv hcx)
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
    (hs : ((cmpxchgAt c .release .relaxed 4 sPtr h (BitVec.ofNat 32 u)).run m).run = some (.ok (r, m'))) :
    m'.current = u ∧ m'.threads = m.threads ∧
      ((r = none ∧ Inv (upd G u .done) m') ∨ (∃ old, r = some old ∧ Inv G m')) := by
  obtain ⟨b, blk, o, li, m₁, pos, old, hacc, -, hl, hpos, hold, hres⟩ := cmpxchgAt_ok hs
  obtain ⟨rfl, rfl, hb0, -⟩ := acc_head (accessW_pure hacc).1
  have hk0 : Kid u (G u) := .inr (.inl ⟨h, hg⟩)
  have hnd : G u ≠ .done := by rw [hg]; intro h; cases h
  have ht : m.current < m.threads.size := by rw [hc]; exact kid_lt hi hk0
  have hact : Act G m.current := .inr ⟨by rw [hc]; exact hu, by rw [hc]; exact hnd⟩
  have hir := hi.record (b := 0) (o := 0) (len := intSize 32) (k := .atomicWrite) ht hact
    (.inr (.inl ⟨rfl, rfl, show intSize 32 ≤ 4 by decide, rfl⟩))
  have hcur : (m.recordAt 0 0 (intSize 32) .atomicWrite).current = m.current := rfl
  have hthr : (m.recordAt 0 0 (intSize 32) .atomicWrite).threads = m.threads := rfl
  have hbr : (m.recordAt 0 0 (intSize 32) .atomicWrite).blocks[0]? = some blk := hb0
  generalize m.recordAt 0 0 (intSize 32) .atomicWrite = mr at hir hl hcur hthr hbr
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_head hir.head hl
  have hl0 : ({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
  have hiM := hir.setLoc hfl k
  have hact' : Act G mr.current := by rw [hcur]; exact hact
  rcases hres with ⟨rfl, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
  · -- success: the newest message, then the pusher's message
    have hpos' := cas_chain_pos (m := { mr with atomics := #[l], nextMsg := k })
      (by rw [hl0]; exact hfl.2.2.2.2.1) hpos hold
    rw [hl0] at hpos' hold
    have hbM : ({ mr with atomics := #[l], nextMsg := k } : Mem).blocks[
        (({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).block]? = some blk := by
      rw [hl0, hfl.1]; exact hbr
    unfold rmwM
    simp only [AtomicOrder.isAcq, Bool.false_eq_true, ↓reduceIte]
    have hins := insertM_last (msg := rmwMsg { mr with atomics := #[l], nextMsg := k } .release
      (l.msgs[l.msgs.size - 1]!) (BitVec.ofNat 32 u)) hbM
    rw [hl0] at hins
    rw [hpos', Nat.sub_add_cancel hfl.pos, show (#[l] : Array ALoc)[0]! = l from rfl, hins]
    have hiN := hiM.pushHead hu hg rfl (by rw [← hpos']; exact hold) hbr
      (msg := rmwMsg { mr with atomics := #[l], nextMsg := k } .release (l.msgs[l.msgs.size - 1]!)
        (BitVec.ofNat 32 u))
      (LawfulEnc.size_encode (α := BitVec 32) _) (intOfBytes_rmw _) rfl
      (by show VClock.le (mr.clocks[mr.current]!) _ = true; rw [hcur, hc]; exact VClock.le_refl _)
    refine ⟨hcur.trans hc, hthr, .inl ⟨trivial, hiN.congr rfl rfl ?_ ?_ rfl⟩⟩
    · show mr.blocks.set! _ _ = mr.blocks.set! _ _
      rw [hfl.1, hfl.2.1]
    · rfl
  · -- failure: a read of a message, no acquire
    exact ⟨by rw [loadM_current]; exact hcur.trans hc, hthr,
      .inr ⟨_, rfl, hiM.grow (growsAt_loadM _ _ _ mr.current) hact'⟩⟩

theorem cas_noErr {G : ThreadId → Gh} {m : Mem} {c u : Nat} {h : BitVec 32} (hi : Inv G m)
    (hu : u = 1 ∨ u = 2) (hg : G u = .cas h) (hc : m.current = u)
    (hcr : c < casCount 32 .release 4 sPtr h m ∨ casCount 32 .release 4 sPtr h m = 0 ∧ c = 0)
    (e : Error) :
    ((cmpxchgAt c .release .relaxed 4 sPtr h (BitVec.ofNat 32 u)).run m).run ≠ some (.error e) := by
  have hk0 : Kid u (G u) := .inr (.inl ⟨h, hg⟩)
  have hnd : G u ≠ .done := by rw [hg]; intro h; cases h
  have ht : m.current < m.threads.size := by rw [hc]; exact kid_lt hi hk0
  have hact : Act G m.current := .inr ⟨by rw [hc]; exact hu, by rw [hc]; exact hnd⟩
  obtain ⟨blk₀, -, hk, -, hacc₀⟩ := access_blk (p := sPtr) (a := 4) (len := intSize 32) (o := 0)
    hi.b0 (by decide) (fun A hA => by omega) rfl
  have hacc : m.accessW sPtr (intSize 32) 4 = pure (0, blk₀, 0) := by simp [Mem.accessW, hacc₀, hk]
  have hir := hi.record (b := 0) (o := 0) (len := intSize 32) (k := .atomicWrite) ht hact
    (.inr (.inl ⟨rfl, rfl, show intSize 32 ≤ 4 by decide, rfl⟩))
  refine cmpxchgAt_noErr (casPrep_noErr hacc (noRace_head rfl hi ht)
    (head_locIdx_noErr hir.head)) (fun li opts m₁ hp => ?_) e
  obtain ⟨b, blk, o, hacc', -, hl, rfl⟩ := casPrep_ok hp
  obtain ⟨rfl, rfl, -, -⟩ := acc_head (accessW_pure hacc').1
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_head hir.head hl
  have hl0 : ({ m.recordAt 0 0 (intSize 32) .atomicWrite with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
  have hcount : casCount 32 .release 4 sPtr h m = (casOpts { m.recordAt 0 0 (intSize 32) .atomicWrite with
      atomics := #[l], nextMsg := k } 0 h).size := optCount_eq hp
  have hne : 0 < (casOpts { m.recordAt 0 0 (intSize 32) .atomicWrite with
      atomics := #[l], nextMsg := k } 0 h).size := casOpts_ne (by rw [hl0]; exact hfl.pos)
  rw [hcount] at hcr
  have hc' : c < (casOpts { m.recordAt 0 0 (intSize 32) .atomicWrite with atomics := #[l], nextMsg := k } 0 h).size := by
    rcases hcr with h | ⟨h0, -⟩
    · exact h
    · exact absurd h0 (Nat.pos_iff_ne_zero.mp hne)
  refine ⟨_, Array.getElem?_eq_getElem hc', ?_⟩
  have hlt := (casOpts_pos (Array.getElem?_eq_getElem hc')).1
  rw [hl0] at hlt ⊢
  exact hfl.val hlt

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
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
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
  simp only [cmpxchgC, StateT.run_bind]
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
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt = some g) (u : ThreadId)
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

end Atomics.Stack
