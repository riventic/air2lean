import ZigLean.Conc.Logic
import ZigLean.Mem.Lemmas

/-!
# Rules for generated concurrent code

The `WP` rules of `ZigLean/Conc/Logic.lean` for the steps that `Emit.lean` writes in a
concurrent function (`Zig.CM`): a call in `MemM` (`liftM`, `callMC`, `callRC`), the sync ops
(`pickC`, `spawnC`, `joinC`), and `run'` of a body. A proof unfolds the generated code, applies
these rules one step at a time, and uses the `*_ok` lemmas for what a `MemM` step that gave a
result did: with partial correctness a step can fail (a race is `.illegal`), so the lemmas go
from a result back to the memory. In strict mode each step also needs a proof that it does not
throw: the `*_noErr` lemmas, built from `MemM.bind_err` and the others (from an error back to the
step that threw it), `noRace_of` and `join_run`.
-/

namespace Zig
namespace Conc
namespace Proto

variable {Tgt γ : Type} {P : Proto Tgt γ}
variable {σ α β : Type} {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat}

/-! ## Steps of a concurrent body -/

theorem WP.map {x : ConcM Tgt α} {f : α → β} {Q : β → (ThreadId → γ) → Mem → Nat → Prop}
    (h : P.WP t x (fun a G m d => Q (f a) G m d) G m n) : P.WP t (f <$> x) Q G m n := by
  rw [map_eq_pure_bind]
  exact WP.bind (WP.mono (fun _ _ _ _ hq => WP.pure' hq) h)

/-- A call in `MemM`, lifted into the body: no stop. In strict mode it does not throw
(`herr`). -/
theorem WP.liftM {x : MemM α} {s : σ} {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (herr : ∀ e, (x.run m).run = some (.error e) → P.strict = false)
    (h : ∀ a m', (x.run m).run = some (.ok (a, m')) →
      m'.threads.size = m.threads.size ∧ Q (a, s) G m' n) :
    P.WP t ((liftM x : CM Tgt σ α).run s) Q G m n := by
  show P.WP t (ConcM.liftMem x >>= fun a => pure (a, s)) Q G m n
  exact WP.bind (WP.liftMem herr fun a m' hr => ⟨(h a m' hr).1, WP.pure' (h a m' hr).2⟩)

theorem WP.callMC {x : MemM α} {s : σ} {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (herr : ∀ e, (x.run m).run = some (.error e) → P.strict = false)
    (h : ∀ a m', (x.run m).run = some (.ok (a, m')) →
      m'.threads.size = m.threads.size ∧ Q (a, s) G m' n) :
    P.WP t ((callMC x : CM Tgt σ α).run s) Q G m n :=
  WP.liftM (x := x) herr h

/-- A call to a pure function: no stop, the memory does not change. -/
theorem WP.callRC {x : Result α} {s : σ} {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (herr : ∀ e, x.run = some (.error e) → P.strict = false)
    (h : ∀ a, x.run = some (.ok a) → Q (a, s) G m n) :
    P.WP t ((callRC x : CM Tgt σ α).run s) Q G m n := by
  show P.WP t (ConcM.liftMem (StateT.lift x) >>= fun a => pure (a, s)) Q G m n
  refine WP.bind (WP.liftMem (fun e he => herr e ?_) fun a m' hr => ?_)
  · have he' : ExceptT.run ((fun a => (a, m)) <$> x) = some (.error e) := he
    rw [ExceptT.run_map] at he'
    match hx : x.run, he' with
    | none, he' => simp at he'
    | some (.error e'), he' => simp [Except.map] at he'; rw [he']
    | some (.ok _), he' => simp [Except.map] at he'
  have hr' : ExceptT.run ((fun a => (a, m)) <$> x) = some (.ok (a, m')) := hr
  rw [ExceptT.run_map] at hr'
  match hx : x.run, hr' with
  | none, hr' => simp at hr'
  | some (.error _), hr' => simp [Except.map] at hr'
  | some (.ok a'), hr' =>
    simp only [Option.map_eq_map, Option.map_some, Except.map, Option.some.injEq,
      Except.ok.injEq, Prod.mk.injEq] at hr'
    obtain ⟨rfl, rfl⟩ := hr'
    exact ⟨rfl, WP.pure' (h _ hx)⟩

/-- A stop where the oracle picks one of `count m` options: the post holds for every pick. -/
theorem WP.pickC {count : Mem → Nat} {s : σ} {Q : Nat × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧ ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      ∀ c, (c < count { m₁ with current := t } ∨ count { m₁ with current := t } = 0 ∧ c = 0) →
        Q (c, s) G₁ { m₁ with current := t } k) :
    P.WP t ((pickC count : CM Tgt σ Nat).run s) Q G m n := by
  show P.WP t (ConcM.sync (.pick count) >>= fun a => pure (a, s)) Q G m n
  refine WP.bind (WP.sync fun k hk => ?_)
  obtain ⟨g, hi, hc⟩ := h k hk
  exact ⟨g, hi, fun G₁ m₁ hg hi₁ c hcr => WP.pure' (hc G₁ m₁ hg hi₁ c hcr)⟩

/-- A call to another concurrent function: its post, with the locals of the caller. -/
theorem WP.callC {r : ConcM Tgt α} {s : σ} {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : P.WP t r (fun a G m d => Q (a, s) G m d) G m n) :
    P.WP t ((callC r : CM Tgt σ α).run s) Q G m n := by
  show P.WP t (r >>= fun a => pure (a, s)) Q G m n
  exact WP.bind (WP.mono (fun _ _ _ _ hq => WP.pure' hq) h)

/-- `Thread.spawn` of `tgt`: the new thread starts with the ghost value `g₀`. -/
theorem WP.spawnC {tgt : Tgt} {s : σ} {Q : Except ErrName ThreadId × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧ ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      ∃ g₀, P.init tgt = some g₀ ∧ ∀ child m',
        (Thread.fork.run { m₁ with current := t }).run = some (.ok (child, m')) →
        Q (.ok child, s) (upd G₁ child g₀) m' k) :
    P.WP t ((spawnC tgt : CM Tgt σ (Except ErrName ThreadId)).run s) Q G m n := by
  show P.WP t ((ConcM.sync (.spawn tgt) >>= fun a => pure (a, s)) >>= fun p =>
    pure ((Except.ok p.1 : Except ErrName ThreadId), p.2)) Q G m n
  refine WP.bind (WP.bind (WP.sync fun k hk => ?_))
  obtain ⟨g, hi, hc⟩ := h k hk
  refine ⟨g, hi, fun G₁ m₁ hg hi₁ => ?_⟩
  obtain ⟨g₀, hg₀, hk'⟩ := hc G₁ m₁ hg hi₁
  exact ⟨g₀, hg₀, fun child m' hf => WP.pure' (WP.pure' (hk' child m' hf))⟩

/-- `Thread.join` of `tid`: it goes on after thread `tid` ended, so `fin (G₁ tid)` holds. In
strict mode, `tid` is a later thread and the join does not throw. -/
theorem WP.joinC {tid : ThreadId} {s : σ} {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧ ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      (P.strict = true → t < tid ∧ tid < m₁.threads.size ∧ P.joins g) ∧ (P.fin (G₁ tid) →
        (P.strict = true → ∃ m', ((Thread.join tid).run { m₁ with current := t }).run =
          some (.ok ((), m'))) ∧ ∀ m',
        ((Thread.join tid).run { m₁ with current := t }).run = some (.ok ((), m')) →
        Q ((), s) G₁ m' k)) :
    P.WP t ((joinC tid : CM Tgt σ Unit).run s) Q G m n := by
  show P.WP t (((fun _ => ()) <$> ConcM.sync (Tgt := Tgt) (.join tid)) >>= fun a =>
    pure (a, s)) Q G m n
  refine WP.bind (WP.map (WP.sync fun k hk => ?_))
  obtain ⟨g, hi, hc⟩ := h k hk
  exact ⟨g, hi, fun G₁ m₁ hg hi₁ => ⟨hg ▸ (hc G₁ m₁ hg hi₁).1, fun hf =>
    ⟨((hc G₁ m₁ hg hi₁).2 hf).1, fun m' hj => WP.pure' (((hc G₁ m₁ hg hi₁).2 hf).2 m' hj)⟩⟩⟩

/-- A futex wait (`futexWaitC`, the bits `e'` of `e`): the thread stops with the ghost value
`g`. It begins not in the queue; if it sleeps, it keeps the invariant with `g`; when it goes on,
`Q` holds. In strict mode it keeps `Live` and does not throw. -/
theorem WP.futexWaitC {ε : Type} {w : Nat} [Packed ε w] {io : Io} {p : Ptr} {e : ε} {s : σ}
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧ ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      let e' := (Packed.toBits e).setWidth 32
      (P.strict = true → P.Live t G₁ m₁) ∧ (m₁.waiters.any (·.1 == t) = false →
        (P.strict = true → ∃ b m',
          ((Thread.futexWait p e').run { m₁ with current := t }).run = some (.ok (b, m'))) ∧
        ∀ b m', ((Thread.futexWait p e').run { m₁ with current := t }).run = some (.ok (b, m')) →
          if b then P.inv G₁ m' else Q ((), s) G₁ m' k)) :
    P.WP t ((futexWaitC io p e : CM Tgt σ Unit).run s) Q G m n := by
  show P.WP t (((fun _ => ()) <$> ConcM.sync (Tgt := Tgt)
    (.wait p ((Packed.toBits e).setWidth 32))) >>= fun a => pure (a, s)) Q G m n
  refine WP.bind (WP.map (WP.sync fun k hk => ?_))
  obtain ⟨g, hi, hc⟩ := h k hk
  refine ⟨g, hi, fun G₁ m₁ hg hi₁ => ⟨(hc G₁ m₁ hg hi₁).1, fun hq =>
    ⟨((hc G₁ m₁ hg hi₁).2 hq).1, fun b m' hr => ?_⟩⟩⟩
  have := ((hc G₁ m₁ hg hi₁).2 hq).2 b m' hr
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at this ⊢
  · exact WP.pure' this
  · exact this

/-- A futex wake (`futexWakeC`): the thread stops with the ghost value `g`; `Q` holds after the
wake. -/
theorem WP.futexWakeC {io : Io} {p : Ptr} {c : BitVec 32} {s : σ}
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧ ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      ∀ m', ((Thread.futexWake p c.toNat).run { m₁ with current := t }).run =
        some (.ok ((), m')) → Q ((), s) G₁ m' k) :
    P.WP t ((futexWakeC io p c : CM Tgt σ Unit).run s) Q G m n := by
  show P.WP t (((fun _ => ()) <$> ConcM.sync (Tgt := Tgt) (.wake p c.toNat)) >>= fun a =>
    pure (a, s)) Q G m n
  refine WP.bind (WP.map (WP.sync fun k hk => ?_))
  obtain ⟨g, hi, hc⟩ := h k hk
  exact ⟨g, hi, fun G₁ m₁ hg hi₁ m' hw => WP.pure' (hc G₁ m₁ hg hi₁ m' hw)⟩


/-- A result `(b, blk, o)` of `Mem.access` is `pure`. -/
theorem access_pure {m : Mem} {p : Ptr} {n a : Nat} {r : BlockId × Block × Nat}
    (h : (m.access p n a).run = some (.ok r)) : m.access p n a = pure r := h

theorem recordAccess_ok {m m' : Mem} {b o l : Nat} {k : AccessKind} {x : Unit}
    (h : ((recordAccess b o l k).run m).run = some (.ok (x, m'))) :
    NoRace m b o l k ∧ m' = m.recordAt b o l k := by
  unfold recordAccess at h
  obtain ⟨a, m₁, hg, h₁⟩ := MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  dsimp only at h₁
  split at h₁
  · exact (MemM.throw_ok h₁).elim
  · rename_i hr
    exact ⟨hr, MemM.set_ok h₁⟩

theorem loadBytes_ok {m m' : Mem} {p : Ptr} {n a : Nat} {kind : AccessKind} {bs : Array Byte}
    (h : ((loadBytes p n a kind).run m).run = some (.ok (bs, m'))) :
    ∃ b blk o, m.access p n a = pure (b, blk, o) ∧ NoRace m b o n kind ∧
      bs = blk.bytes.extract o (o + n) ∧ m' = m.recordAt b o n kind := by
  unfold loadBytes at h
  obtain ⟨a₁, m₁, hg, h₁⟩ := MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  dsimp only at h₁
  obtain ⟨⟨b, blk, o⟩, m₂, ha, h₂⟩ := MemM.bind_ok h₁
  obtain ⟨ha, rfl⟩ := MemM.lift_ok ha
  dsimp only at h₂
  obtain ⟨_, m₃, hr, h₃⟩ := MemM.bind_ok h₂
  obtain ⟨hnr, rfl⟩ := recordAccess_ok hr
  obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₃
  exact ⟨b, blk, o, access_pure ha, hnr, rfl, rfl⟩

theorem load_ok {T : Type} [Enc T] {m m' : Mem} {p : Ptr} {a : Nat} {v : T}
    (h : ((load T a p).run m).run = some (.ok (v, m'))) :
    ∃ b blk o, m.access p (Enc.size T) a = pure (b, blk, o) ∧ NoRace m b o (Enc.size T) .read ∧
      (Enc.decode (blk.bytes.extract o (o + Enc.size T)) : Result T).run = some (.ok v) ∧
      m' = m.recordAt b o (Enc.size T) .read := by
  unfold load at h
  obtain ⟨bs, m₁, hl, h₁⟩ := MemM.bind_ok h
  obtain ⟨b, blk, o, ha, hnr, rfl, rfl⟩ := loadBytes_ok hl
  obtain ⟨hd, rfl⟩ := MemM.lift_ok h₁
  exact ⟨b, blk, o, ha, hnr, hd, rfl⟩

theorem accessW_pure {m : Mem} {p : Ptr} {n a : Nat} {r : BlockId × Block × Nat}
    (h : (m.accessW p n a).run = some (.ok r)) :
    m.access p n a = pure r ∧ r.2.1.kind ≠ .constGlobal := by
  unfold Mem.accessW at h
  rw [ExceptT.run_bind] at h
  match hr : (m.access p n a).run, h with
  | none, h => simp at h
  | some (.error _), h => simp [pure] at h
  | some (.ok r'), h =>
    simp only [bind, Option.bind_some] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.run] at h
    · rename_i hk
      simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at h
      subst h
      exact ⟨hr, hk⟩

theorem storeBytes_ok {m m' : Mem} {p : Ptr} {a : Nat} {bs : Array Byte} {kind : AccessKind}
    {x : Unit} (h : ((storeBytes p a bs kind).run m).run = some (.ok (x, m'))) :
    ∃ b blk o, m.access p bs.size a = pure (b, blk, o) ∧ blk.kind ≠ .constGlobal ∧
      NoRace m b o bs.size kind ∧ m' = (m.recordAt b o bs.size kind).write b blk o bs := by
  unfold storeBytes at h
  obtain ⟨a₁, m₁, hg, h₁⟩ := MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  dsimp only at h₁
  obtain ⟨⟨b, blk, o⟩, m₂, ha, h₂⟩ := MemM.bind_ok h₁
  obtain ⟨ha, rfl⟩ := MemM.lift_ok ha
  obtain ⟨hacc, hk⟩ := accessW_pure ha
  dsimp only at h₂
  obtain ⟨_, m₃, hr, h₃⟩ := MemM.bind_ok h₂
  obtain ⟨hnr, rfl⟩ := recordAccess_ok hr
  obtain ⟨a₄, m₄, hg, h₄⟩ := MemM.bind_ok h₃
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  exact ⟨b, blk, o, hacc, hk, hnr, MemM.set_ok h₄⟩


theorem store_ok {T : Type} [Enc T] {m m' : Mem} {p : Ptr} {a : Nat} {v : T} {x : Unit}
    (h : ((store a p v).run m).run = some (.ok (x, m'))) :
    ∃ b blk o, m.access p (Enc.encode v).size a = pure (b, blk, o) ∧ blk.kind ≠ .constGlobal ∧
      m' = (m.recordAt b o (Enc.encode v).size .write).write b blk o (Enc.encode v) := by
  obtain ⟨b, blk, o, ha, hk, -, rfl⟩ := storeBytes_ok h
  exact ⟨b, blk, o, ha, hk, rfl⟩

theorem storeUndef_ok {T : Type} [Enc T] {m m' : Mem} {p : Ptr} {a : Nat} {x : Unit}
    (h : ((storeUndef T a p).run m).run = some (.ok (x, m'))) :
    ∃ b blk o, m.access p (Enc.size T) a = pure (b, blk, o) ∧ blk.kind ≠ .constGlobal ∧
      m' = (m.recordAt b o (Enc.size T) .write).write b blk o
        (Array.replicate (Enc.size T) .undef) := by
  obtain ⟨b, blk, o, ha, hk, -, rfl⟩ := storeBytes_ok h
  simp only [Array.size_replicate] at ha ⊢
  exact ⟨b, blk, o, ha, hk, rfl⟩

theorem alloc_ok {m m' : Mem} {kind : BlockKind} {size align : Nat} {q : Ptr}
    (h : ((alloc kind size align).run m).run = some (.ok (q, m'))) :
    q = ⟨some m.blocks.size, 0⟩ ∧ m' = { m with
      blocks := m.blocks.push
        { bytes := Array.replicate size .undef, align, kind, live := true,
          addr := alignUp m.nextAddr align },
      nextAddr := alignUp m.nextAddr align + size + 1 } := by
  unfold alloc at h
  obtain ⟨a₁, m₁, hg, h₁⟩ := MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  obtain ⟨_, m₂, hs, h₂⟩ := MemM.bind_ok h₁
  have := MemM.set_ok hs
  subst this
  obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₂
  exact ⟨rfl, rfl⟩

theorem free_ok {m m' : Mem} {p : Ptr} {x : Unit}
    (h : ((free p).run m).run = some (.ok (x, m'))) :
    ∃ b blk, p.block = some b ∧ m.blocks[b]? = some blk ∧
      m' = { m with blocks := m.blocks.set! b { blk with live := false } } := by
  unfold free at h
  obtain ⟨a₁, m₁, hg, h₁⟩ := MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  split at h₁
  · exact (MemM.throw_ok h₁).elim
  · rename_i b hb
    split at h₁
    · rename_i blk hblk
      split at h₁
      · exact ⟨b, blk, hb, hblk, MemM.set_ok h₁⟩
      · exact (MemM.throw_ok h₁).elim
    · exact (MemM.throw_ok h₁).elim

/-! ## RC11 options at an RMW chain

At a location where every message after the first is an RMW of the one before it
(`ALoc.Chain`), an RMW can read only the newest message; a read whose clock is `≥` the newest
message's clock also reads only it. -/

/-- Every message after the first is an RMW of the one before it. -/
def _root_.Zig.ALoc.Chain (l : ALoc) : Prop :=
  ∀ j (h : j + 1 < l.msgs.size), l.msgs[j + 1].rmwOf = some l.msgs[j].id

theorem _root_.Zig.ALoc.hasRmwAfter_chain {l : ALoc} (hc : l.Chain) {p : Nat}
    (hp : p + 1 < l.msgs.size) : l.hasRmwAfter p = true := by
  unfold ALoc.hasRmwAfter
  rw [Array.getElem?_eq_getElem hp, Array.getElem?_eq_getElem (by omega)]
  simp [hc p hp]

theorem _root_.Zig.ALoc.hasRmwAfter_last (l : ALoc) : l.hasRmwAfter (l.msgs.size - 1) = false := by
  unfold ALoc.hasRmwAfter
  by_cases h : l.msgs.size = 0
  · simp [h]
  · rw [Array.getElem?_eq_none (by omega)]

theorem _root_.Zig.ALoc.pos_lt {l : ALoc} {id p : Nat} (h : l.pos id = some p) :
    p < l.msgs.size := by
  unfold ALoc.pos at h
  exact (Array.findIdx?_eq_some_iff_getElem.mp h).1

/-- The fold of `floorPos`: at least each index whose message satisfies `P`. -/
theorem foldl_max_ge {α : Type} (P : α → Bool) :
    ∀ (xs : List (α × Nat)) (a₀ j : Nat), (∃ x, (x, j) ∈ xs ∧ P x = true) ∨ j ≤ a₀ →
      j ≤ xs.foldl (fun a (x, i) => if P x then Nat.max a i else a) a₀
  | [], a₀, j, h => by
    rcases h with ⟨x, hx, -⟩ | h
    · simp at hx
    · exact h
  | (y, i) :: xs, a₀, j, h => by
    simp only [List.foldl_cons]
    apply foldl_max_ge P xs
    rcases h with ⟨x, hx, hp⟩ | h
    · rcases List.mem_cons.mp hx with he | hx
      · cases he; right; simp only [hp, ↓reduceIte]; exact Nat.le_max_right _ _
      · exact .inl ⟨x, hx, hp⟩
    · right; split
      · exact Nat.le_trans h (Nat.le_max_left _ _)
      · exact h

/-- The fold of `floorPos`: below a bound of every index. -/
theorem foldl_max_le {α : Type} (P : α → Bool) (N : Nat) :
    ∀ (xs : List (α × Nat)) (a₀ : Nat), a₀ ≤ N → (∀ x i, (x, i) ∈ xs → i ≤ N) →
      xs.foldl (fun a (x, i) => if P x then Nat.max a i else a) a₀ ≤ N
  | [], a₀, h, _ => h
  | (y, i) :: xs, a₀, h, hx => by
    simp only [List.foldl_cons]
    apply foldl_max_le P N xs
    · split
      · exact Nat.max_le.mpr ⟨h, hx y i (by simp)⟩
      · exact h
    · intro x j hj; exact hx x j (by simp [hj])

theorem floorPos_lt {m : Mem} {li : Nat} (h : 0 < (m.atomics[li]!).msgs.size) :
    floorPos m li < (m.atomics[li]!).msgs.size := by
  unfold floorPos
  refine Nat.max_lt.mpr ⟨?_, ?_⟩
  · rw [← Array.foldl_toList]
    have := foldl_max_le (fun x : Msg => VClock.le x.clock (m.clocks[m.current]!))
      ((m.atomics[li]!).msgs.size - 1) (m.atomics[li]!).msgs.zipIdx.toList 0 (Nat.zero_le _)
      (fun x i hx => by
        rw [Array.mem_toList_iff, Array.mem_zipIdx_iff_getElem?] at hx
        have := (Array.getElem?_eq_some_iff.mp hx).1
        omega)
    exact Nat.lt_of_le_of_lt this (Nat.sub_lt h Nat.one_pos)
  · cases hfind : m.seen.find? (fun (t, j, _) => t == m.current && j == li) with
    | none => simpa using h
    | some x =>
      cases hp : (m.atomics[li]!).pos x.2.2 with
      | none => simpa [hp] using h
      | some p => simpa [hp] using ALoc.pos_lt hp

/-- Message `j` happened before the reader: the floor is at least `j`. -/
theorem le_floorPos {m : Mem} {li j : Nat} (hj : j < (m.atomics[li]!).msgs.size)
    (hc : VClock.le ((m.atomics[li]!).msgs[j]).clock (m.clocks[m.current]!) = true) :
    j ≤ floorPos m li := by
  unfold floorPos
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  rw [← Array.foldl_toList]
  refine foldl_max_ge (fun x : Msg => VClock.le x.clock (m.clocks[m.current]!)) _ 0 j
    (.inl ⟨(m.atomics[li]!).msgs[j], ?_, hc⟩)
  rw [Array.mem_toList_iff, Array.mem_zipIdx_iff_getElem?]
  exact Array.getElem?_eq_getElem hj


/-- An RMW at a chain reads the newest message only. -/
theorem readOpts_chain {m : Mem} {li : Nat} (h : 0 < (m.atomics[li]!).msgs.size)
    (hc : (m.atomics[li]!).Chain) :
    readOpts m li true = #[(m.atomics[li]!).msgs.size - 1] := by
  have hf := floorPos_lt h
  unfold readOpts
  generalize hk : (m.atomics[li]!).msgs.size - floorPos m li = k
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  apply Array.toList_inj.mp
  simp only [Array.toList_filter, Array.toList_map, Array.toList_range]
  rw [hk, List.range_succ_eq_map, List.map_cons, List.map_map, List.filter_cons]
  simp only [Nat.sub_zero, ALoc.hasRmwAfter_last, Bool.not_false, Bool.not_true, Bool.false_or,
    ↓reduceIte, List.cons.injEq, true_and]
  simp only [List.filter_eq_nil_iff, List.mem_map, List.mem_range,
    Function.comp, Bool.not_eq_true']
  rintro _ ⟨j, hj, rfl⟩
  rw [ALoc.hasRmwAfter_chain hc (p := (m.atomics[li]!).msgs.size - 1 - j.succ) (by omega)]
  simp

/-- A read whose floor is the newest message reads it only. -/
theorem readOpts_floor {m : Mem} {li : Nat} (h : 0 < (m.atomics[li]!).msgs.size)
    (hf : floorPos m li = (m.atomics[li]!).msgs.size - 1) :
    readOpts m li false = #[(m.atomics[li]!).msgs.size - 1] := by
  unfold readOpts
  simp only [hf, show (m.atomics[li]!).msgs.size - ((m.atomics[li]!).msgs.size - 1) = 1 by omega]
  apply Array.toList_inj.mp
  simp


/-! ## The atomic location of an access (`locIdx`) -/

/-- The bytes of block `b` at `o..o+len` (`locIdx`'s `cur`). -/
def curBytes (m : Mem) (b o len : Nat) : Array Byte :=
  ((m.blocks[b]?.map (·.bytes)).getD #[]).extract o (o + len)

/-- The bytes of the newest message of `l` (`locIdx`'s `last`). -/
def ALoc.lastBytes (l : ALoc) : Array Byte := (l.msgs.back?.map (·.bytes)).getD #[]

/-- The location exists, and its newest message has the block's bytes: no change. -/
theorem locIdx_found {m m' : Mem} {b o len i r : Nat}
    (hi : m.atomics.findIdx? (fun l => l.block == b && l.off == o) = some i)
    (hlen : (m.atomics[i]!).len = len)
    (hlast : ALoc.lastBytes (m.atomics[i]!) = curBytes m b o len)
    (h : ((locIdx b o len).run m).run = some (.ok (r, m'))) : r = i ∧ m' = m := by
  have hi' := (Array.findIdx?_eq_some_iff_getElem.mp hi).1
  unfold locIdx at h
  obtain ⟨a₁, m₁, hg, h₁⟩ := MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  simp only [hi] at h₁
  split at h₁
  · rename_i hne; simp [hlen] at hne
  · unfold ALoc.lastBytes curBytes at hlast
    simp only [hlast, beq_self_eq_true, ↓reduceIte] at h₁
    obtain ⟨_, m₂, hs, h₂⟩ := MemM.bind_ok h₁
    have := MemM.set_ok hs
    subst this
    obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₂
    refine ⟨rfl, ?_⟩
    have e : m₁.atomics.setIfInBounds r
        { block := m₁.atomics[r]!.block, off := m₁.atomics[r]!.off, len := m₁.atomics[r]!.len,
          msgs := m₁.atomics[r]!.msgs } = m₁.atomics := by
      apply Array.ext (by simp)
      intro j h1 h2
      rw [Array.getElem_setIfInBounds h2]
      split
      · subst_vars; rw [getElem!_pos m₁.atomics _ h2]
      · rfl
    simp only [Array.set!_eq_setIfInBounds, e]

/-- The first atomic op at `(b, o)`: a new location, with the block's bytes as its first
message. -/
theorem locIdx_new {m m' : Mem} {b o len r : Nat}
    (hi : m.atomics.findIdx? (fun l => l.block == b && l.off == o) = none)
    (h : ((locIdx b o len).run m).run = some (.ok (r, m'))) :
    r = m.atomics.size ∧ m' = { m with
      atomics := m.atomics.push
        { block := b, off := o, len := len,
          msgs := #[{ id := m.nextMsg, bytes := curBytes m b o len,
                      clock := plainClock m b o len, relClock := #[] }] },
      nextMsg := m.nextMsg + 1 } := by
  unfold locIdx at h
  obtain ⟨a₁, m₁, hg, h₁⟩ := MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  simp only [hi] at h₁
  split at h₁
  · exact (MemM.throw_ok h₁).elim
  · obtain ⟨_, m₂, hs, h₂⟩ := MemM.bind_ok h₁
    have := MemM.set_ok hs
    subst this
    obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₂
    exact ⟨rfl, rfl⟩


/-! ## Atomic ops, from their result -/

/-- `acquireClock c` on `m`. -/
def acqM (m : Mem) (c : VClock) : Mem :=
  { m with clocks := m.clocks.set! m.current (VClock.merge (m.clocks[m.current]!) c) }

/-- `insertMsg li p msg` on `m`. -/
def insertM (m : Mem) (li p : Nat) (msg : Msg) : Mem :=
  let l := m.atomics[li]!
  let m' := { m with atomics := m.atomics.set! li { l with msgs := l.msgs.insertIdxIfInBounds p msg },
                     nextMsg := m.nextMsg + 1 }
  if p == l.msgs.size then
    match m'.blocks[l.block]? with
    | some blk => { m' with blocks := m'.blocks.set! l.block { blk with bytes := writeBytes blk.bytes l.off msg.bytes } }
    | none => m'
  else m'

/-- `observe li id` on `m`. -/
def observeM (m : Mem) (li id : Nat) : Mem :=
  { m with seen := (m.seen.filter fun (t, j, _) => !(t == m.current && j == li)).push (m.current, li, id) }

/-- The message that an RMW writes (`rmwWrite`). -/
def rmwMsg {n : Nat} (m : Mem) (ord : AtomicOrder) (rd : Msg) (new : BitVec n) : Msg :=
  let cl := m.clocks[m.current]!
  { id := m.nextMsg, bytes := padTo (intSize n) (intBytes new), clock := cl,
    relClock := (if ord.isRel then VClock.merge rd.relClock cl else rd.relClock), rmwOf := some rd.id }

/-- `rmwWrite li pos ord rd new` on `m`. -/
def rmwM {n : Nat} (m : Mem) (li pos : Nat) (ord : AtomicOrder) (rd : Msg) (new : BitVec n) : Mem :=
  let m₂ := if ord.isAcq then acqM m rd.relClock else m
  observeM (insertM m₂ li (pos + 1) (rmwMsg m₂ ord rd new)) li m₂.nextMsg

/-- An atomic read of message `msg` of location `li` on `m` (`atomicLoadAt` after `loadPrep`). -/
def loadM (m : Mem) (li : Nat) (ord : AtomicOrder) (msg : Msg) : Mem :=
  let m₂ := observeM m li msg.id
  if ord.isAcq then acqM m₂ msg.relClock else m₂

theorem insertIdxIfInBounds_size_self {α : Type} (xs : Array α) (v : α) :
    xs.insertIdxIfInBounds xs.size v = xs.push v := by
  simp [Array.insertIdxIfInBounds, Array.insertIdx_size_self]

/-- An RMW's bytes read back as its value. -/
theorem intOfBytes_rmw (v : BitVec 32) :
    (intOfBytes 32 (padTo (intSize 32) (intBytes v))).run = some (.ok v) :=
  congrArg ExceptT.run (LawfulEnc.decode_encode (α := BitVec 32) v)

theorem ptr_add_zero (p : Ptr) : p.add 0 = p := by simp [Ptr.add]

/-- An insert at the end: the location has one more message, and the block has its bytes. -/
theorem insertM_last {m : Mem} {li : Nat} {msg : Msg} {blk : Block}
    (hb : m.blocks[(m.atomics[li]!).block]? = some blk) :
    insertM m li (m.atomics[li]!).msgs.size msg = { m with
      atomics := m.atomics.set! li
        { m.atomics[li]! with msgs := (m.atomics[li]!).msgs.push msg },
      nextMsg := m.nextMsg + 1,
      blocks := m.blocks.set! (m.atomics[li]!).block
        { blk with bytes := writeBytes blk.bytes (m.atomics[li]!).off msg.bytes } } := by
  unfold insertM
  simp [insertIdxIfInBounds_size_self, hb]

theorem modify_ok {f : Mem → Mem} {m m' : Mem} {x : PUnit}
    (h : ((modify f : MemM PUnit).run m).run = some (.ok (x, m'))) : m' = f m := by
  simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run, pure,
    ExceptT.pure, ExceptT.mk, ExceptT.run] at h
  exact h.symm

theorem loadPrep_ok {n : Nat} {ord : AtomicOrder} {align : Nat} {p : Ptr} {rmw : Bool}
    {m m' : Mem} {li : Nat} {opts : Array Nat}
    (h : ((loadPrep n ord align p rmw).run m).run = some (.ok ((li, opts), m'))) :
    ∃ b blk o, (if rmw then m.accessW p (intSize n) align else m.access p (intSize n) align) =
        pure (b, blk, o) ∧
      NoRace m b o (intSize n) (if rmw then .atomicWrite else .atomicRead) ∧
      ((locIdx b o (intSize n)).run
        (m.recordAt b o (intSize n) (if rmw then .atomicWrite else .atomicRead))).run =
        some (.ok (li, m')) ∧
      opts = readOpts m' li rmw := by
  unfold loadPrep at h
  cases rmw <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢ <;>
  · obtain ⟨a₁, m₁, hg, h₁⟩ := MemM.bind_ok h
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    try dsimp only at h₁
    obtain ⟨⟨b, blk, o⟩, m₂, ha, h₂⟩ := MemM.bind_ok h₁
    obtain ⟨ha, rfl⟩ := MemM.lift_ok ha
    try dsimp only at h₂
    obtain ⟨_, m₃, hr, h₃⟩ := MemM.bind_ok h₂
    obtain ⟨hnr, rfl⟩ := recordAccess_ok hr
    obtain ⟨li', m₄, hl, h₄⟩ := MemM.bind_ok h₃
    obtain ⟨a₅, m₅, hg, h₅⟩ := MemM.bind_ok h₄
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    obtain ⟨he, rfl⟩ := MemM.pure_ok h₅
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨b, blk, o, ha, hnr, hl, rfl⟩



theorem rmwWrite_ok {n : Nat} {li pos : Nat} {ord : AtomicOrder} {rd : Msg} {new : BitVec n}
    {m m' : Mem} {x : Unit}
    (h : ((rmwWrite li pos ord rd new).run m).run = some (.ok (x, m'))) :
    m' = rmwM m li pos ord rd new := by
  unfold rmwWrite at h
  unfold rmwM
  cases hq : ord.isAcq <;> simp only [hq, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · obtain ⟨a₂, m₂, hg, h₂⟩ := MemM.bind_ok h
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    obtain ⟨_, m₃, hi, h₃⟩ := MemM.bind_ok h₂
    have := modify_ok hi
    subst this
    exact modify_ok h₃
  · obtain ⟨_, m₁, ha, h₁⟩ := MemM.bind_ok h
    have := modify_ok ha
    subst this
    obtain ⟨a₂, m₂, hg, h₂⟩ := MemM.bind_ok h₁
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    obtain ⟨_, m₃, hi, h₃⟩ := MemM.bind_ok h₂
    have := modify_ok hi
    subst this
    exact modify_ok h₃

theorem atomicRmwAt_ok {n c : Nat} {op : RmwOp} {signed : Bool} {ord : AtomicOrder} {align : Nat}
    {p : Ptr} {v old : BitVec n} {m m' : Mem}
    (h : ((atomicRmwAt c op signed ord align p v).run m).run = some (.ok (old, m'))) :
    ∃ b blk o li m₁ pos, m.accessW p (intSize n) align = pure (b, blk, o) ∧
      NoRace m b o (intSize n) .atomicWrite ∧
      ((locIdx b o (intSize n)).run (m.recordAt b o (intSize n) .atomicWrite)).run =
        some (.ok (li, m₁)) ∧
      (readOpts m₁ li true)[c]? = some pos ∧
      (intOfBytes n ((m₁.atomics[li]!).msgs[pos]!).bytes).run = some (.ok old) ∧
      m' = rmwM m₁ li pos ord ((m₁.atomics[li]!).msgs[pos]!) (op.apply signed old v) := by
  unfold atomicRmwAt at h
  obtain ⟨⟨li, opts⟩, m₁, hp, h₁⟩ := MemM.bind_ok h
  obtain ⟨b, blk, o, ha, hnr, hl, rfl⟩ := loadPrep_ok hp
  simp only [↓reduceIte] at ha hnr hl
  refine ⟨b, blk, o, li, m₁, ?_⟩
  dsimp only at h₁
  split at h₁
  · rename_i pos hpos
    obtain ⟨a₂, m₂, hg, h₂⟩ := MemM.bind_ok h₁
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    obtain ⟨old', m₃, hd, h₃⟩ := MemM.bind_ok h₂
    obtain ⟨hd, rfl⟩ := MemM.lift_ok hd
    obtain ⟨_, m₄, hw, h₄⟩ := MemM.bind_ok h₃
    obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₄
    exact ⟨pos, ha, hnr, hl, hpos, hd, rmwWrite_ok hw⟩
  · exact (MemM.throw_ok h₁).elim

theorem atomicLoadAt_ok {n c : Nat} {ord : AtomicOrder} {align : Nat} {p : Ptr} {v : BitVec n}
    {m m' : Mem} (h : ((atomicLoadAt c ord align p).run m).run = some (.ok (v, m'))) :
    ∃ b blk o li m₁ pos, m.access p (intSize n) align = pure (b, blk, o) ∧
      NoRace m b o (intSize n) .atomicRead ∧
      ((locIdx b o (intSize n)).run (m.recordAt b o (intSize n) .atomicRead)).run =
        some (.ok (li, m₁)) ∧
      (readOpts m₁ li false)[c]? = some pos ∧
      (intOfBytes n ((m₁.atomics[li]!).msgs[pos]!).bytes).run = some (.ok v) ∧
      m' = loadM m₁ li ord ((m₁.atomics[li]!).msgs[pos]!) := by
  unfold atomicLoadAt at h
  obtain ⟨⟨li, opts⟩, m₁, hp, h₁⟩ := MemM.bind_ok h
  obtain ⟨b, blk, o, ha, hnr, hl, rfl⟩ := loadPrep_ok hp
  simp only [Bool.false_eq_true, ↓reduceIte] at ha hnr hl
  refine ⟨b, blk, o, li, m₁, ?_⟩
  dsimp only at h₁
  split at h₁
  · rename_i pos hpos
    refine ⟨pos, ha, hnr, hl, hpos, ?_⟩
    obtain ⟨a₂, m₂, hg, h₂⟩ := MemM.bind_ok h₁
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    obtain ⟨_, m₃, ho, h₃⟩ := MemM.bind_ok h₂
    have := modify_ok ho
    subst this
    unfold loadM
    cases hq : ord.isAcq <;> simp only [hq, Bool.false_eq_true, ↓reduceIte] at h₃ ⊢
    · obtain ⟨hd, rfl⟩ := MemM.lift_ok h₃
      exact ⟨hd, rfl⟩
    · obtain ⟨_, m₄, hc, h₄⟩ := MemM.bind_ok h₃
      have := modify_ok hc
      subst this
      obtain ⟨hd, rfl⟩ := MemM.lift_ok h₄
      exact ⟨hd, rfl⟩
  · exact (MemM.throw_ok h₁).elim


/-- The options of a `cmpxchg` (`casPrep`): the messages that a read can read, without one that
has the value `expected` and an RMW after it. -/
def casOpts {n : Nat} (m : Mem) (li : Nat) (expected : BitVec n) : Array Nat :=
  (readOpts m li false).filter fun pos =>
    !((m.atomics[li]!).hasRmwAfter pos && match (intOfBytes n (m.atomics[li]!).msgs[pos]!.bytes).run with
      | some (.ok v) => v == expected
      | _ => false)

theorem casPrep_ok {n align : Nat} {p : Ptr} {expected : BitVec n} {m m' : Mem} {li : Nat}
    {opts : Array Nat}
    (h : ((casPrep n align p expected).run m).run = some (.ok ((li, opts), m'))) :
    ∃ b blk o, m.accessW p (intSize n) align = pure (b, blk, o) ∧
      NoRace m b o (intSize n) .atomicWrite ∧
      ((locIdx b o (intSize n)).run (m.recordAt b o (intSize n) .atomicWrite)).run =
        some (.ok (li, m')) ∧
      opts = casOpts m' li expected := by
  unfold casPrep at h
  obtain ⟨a₁, m₁, hg, h₁⟩ := MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  obtain ⟨⟨b, blk, o⟩, m₂, ha, h₂⟩ := MemM.bind_ok h₁
  obtain ⟨ha, rfl⟩ := MemM.lift_ok ha
  dsimp only at h₂
  obtain ⟨_, m₃, hr, h₃⟩ := MemM.bind_ok h₂
  obtain ⟨hnr, rfl⟩ := recordAccess_ok hr
  obtain ⟨li', m₄, hl, h₄⟩ := MemM.bind_ok h₃
  obtain ⟨a₅, m₅, hg, h₅⟩ := MemM.bind_ok h₄
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  obtain ⟨he, rfl⟩ := MemM.pure_ok h₅
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨b, blk, o, ha, hnr, hl, rfl⟩

/-- A `cmpxchg` that read message `pos` (with the value `old`) of location `li`: on success
(`old = expected`) an RMW, else a read with the failure order. -/
theorem cmpxchgAt_ok {n c : Nat} {succ fail : AtomicOrder} {align : Nat} {p : Ptr}
    {expected new : BitVec n} {r : Option (BitVec n)} {m m' : Mem}
    (h : ((cmpxchgAt c succ fail align p expected new).run m).run = some (.ok (r, m'))) :
    ∃ b blk o li m₁ pos old, m.accessW p (intSize n) align = pure (b, blk, o) ∧
      NoRace m b o (intSize n) .atomicWrite ∧
      ((locIdx b o (intSize n)).run (m.recordAt b o (intSize n) .atomicWrite)).run =
        some (.ok (li, m₁)) ∧
      (casOpts m₁ li expected)[c]? = some pos ∧
      (intOfBytes n ((m₁.atomics[li]!).msgs[pos]!).bytes).run = some (.ok old) ∧
      ((old = expected ∧ r = none ∧ m' = rmwM m₁ li pos succ ((m₁.atomics[li]!).msgs[pos]!) new) ∨
       (old ≠ expected ∧ r = some old ∧ m' = loadM m₁ li fail ((m₁.atomics[li]!).msgs[pos]!))) := by
  unfold cmpxchgAt at h
  obtain ⟨⟨li, opts⟩, m₁, hp, h₁⟩ := MemM.bind_ok h
  obtain ⟨b, blk, o, ha, hnr, hl, rfl⟩ := casPrep_ok hp
  refine ⟨b, blk, o, li, m₁, ?_⟩
  dsimp only at h₁
  split at h₁
  · rename_i pos hpos
    obtain ⟨a₂, m₂, hg, h₂⟩ := MemM.bind_ok h₁
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    obtain ⟨old, m₃, hd, h₃⟩ := MemM.bind_ok h₂
    obtain ⟨hd, rfl⟩ := MemM.lift_ok hd
    refine ⟨pos, old, ha, hnr, hl, hpos, hd, ?_⟩
    split at h₃
    · rename_i he
      obtain ⟨_, m₄, hw, h₄⟩ := MemM.bind_ok h₃
      obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₄
      exact .inl ⟨he, rfl, rmwWrite_ok hw⟩
    · rename_i he
      obtain ⟨_, m₄, ho, h₄⟩ := MemM.bind_ok h₃
      have := modify_ok ho
      subst this
      refine .inr ⟨he, ?_⟩
      unfold loadM
      cases hq : fail.isAcq <;> simp only [hq, Bool.false_eq_true, ↓reduceIte] at h₄ ⊢
      · obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₄
        exact ⟨rfl, rfl⟩
      · obtain ⟨_, m₅, hc, h₅⟩ := MemM.bind_ok h₄
        have := modify_ok hc
        subst this
        obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₅
        exact ⟨rfl, rfl⟩
  · exact (MemM.throw_ok h₁).elim

/-- A position that a read can read is a message. -/
theorem readOpts_lt {m : Mem} {li : Nat} {rmw : Bool} {c pos : Nat}
    (h : (readOpts m li rmw)[c]? = some pos) : pos < (m.atomics[li]!).msgs.size := by
  have hm := Array.mem_of_getElem? h
  unfold readOpts at hm
  simp only [Array.mem_filter, Array.mem_map, Array.mem_range] at hm
  obtain ⟨⟨k, hk, rfl⟩, -⟩ := hm
  omega

/-- An RMW at a chain reads the newest message. -/
theorem rmw_chain_pos {m : Mem} {li c pos : Nat} (h0 : 0 < (m.atomics[li]!).msgs.size)
    (hc : (m.atomics[li]!).Chain) (h : (readOpts m li true)[c]? = some pos) :
    pos = (m.atomics[li]!).msgs.size - 1 := by
  rw [readOpts_chain h0 hc] at h
  cases c with
  | zero => simp at h; exact h.symm
  | succ c => simp at h

/-- A `cmpxchg` option is a message; one with the value `expected` has no RMW after it. -/
theorem casOpts_pos {n : Nat} {m : Mem} {li : Nat} {e : BitVec n} {c pos : Nat}
    (h : (casOpts m li e)[c]? = some pos) :
    pos < (m.atomics[li]!).msgs.size ∧
      ((intOfBytes n ((m.atomics[li]!).msgs[pos]!).bytes).run = some (.ok e) →
        (m.atomics[li]!).hasRmwAfter pos = false) := by
  have hm := Array.mem_of_getElem? h
  unfold casOpts at hm
  rw [Array.mem_filter] at hm
  obtain ⟨hr, hf⟩ := hm
  obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.mp hr
  refine ⟨readOpts_lt hi, fun hv => ?_⟩
  rw [hv] at hf
  simpa using hf

/-- At a chain, a `cmpxchg` that reads the value `expected` reads the newest message. -/
theorem cas_chain_pos {n : Nat} {m : Mem} {li : Nat} {e : BitVec n} {c pos : Nat}
    (hc : (m.atomics[li]!).Chain) (h : (casOpts m li e)[c]? = some pos)
    (hv : (intOfBytes n ((m.atomics[li]!).msgs[pos]!).bytes).run = some (.ok e)) :
    pos = (m.atomics[li]!).msgs.size - 1 := by
  obtain ⟨hlt, hr⟩ := casOpts_pos h
  have := hr hv
  by_cases hne : pos + 1 < (m.atomics[li]!).msgs.size
  · rw [ALoc.hasRmwAfter_chain hc hne] at this; cases this
  · omega

/-! ## No error: from a step's error back to its cause -/

namespace MemM

theorem bind_err {x : MemM α} {f : α → MemM β} {m : Mem} {e : Error}
    (h : ((x >>= f).run m).run = some (.error e)) :
    (x.run m).run = some (.error e) ∨
      ∃ a m', (x.run m).run = some (.ok (a, m')) ∧ ((f a).run m').run = some (.error e) := by
  rw [StateT.run_bind, ExceptT.run_bind] at h
  match hx : (x.run m).run, h with
  | none, h => simp at h
  | some (.error e'), h => simp [pure] at h; exact .inl (by rw [h])
  | some (.ok (a, m')), h => exact .inr ⟨a, m', rfl, by simpa [hx] using h⟩

theorem lift_err {r : Result α} {m : Mem} {e : Error}
    (h : ((StateT.lift r : MemM α).run m).run = some (.error e)) : r.run = some (.error e) := by
  simp only [StateT.run, StateT.lift, ExceptT.run_bind] at h
  match hr : r.run, h with
  | none, h => simp at h
  | some (.error _), h => simp [pure] at h; rw [h]
  | some (.ok _), h => simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at h

theorem get_err {m : Mem} {e : Error} (h : ((get : MemM Mem).run m).run = some (.error e)) :
    False := by
  simp [get, getThe, MonadStateOf.get, StateT.get, StateT.run, pure, ExceptT.pure,
    ExceptT.mk, ExceptT.run] at h

theorem pure_err {x : α} {m : Mem} {e : Error}
    (h : ((pure x : MemM α).run m).run = some (.error e)) : False := by
  simp [StateT.run, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at h

theorem set_err {x m : Mem} {e : Error}
    (h : ((set x : MemM PUnit).run m).run = some (.error e)) : False := by
  simp [set, StateT.set, StateT.run, pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at h

theorem modify_err {f : Mem → Mem} {m : Mem} {e : Error}
    (h : ((modify f : MemM PUnit).run m).run = some (.error e)) : False := by
  simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run, pure,
    ExceptT.pure, ExceptT.mk, ExceptT.run] at h

theorem map_ok {x : MemM α} {f : α → β} {m m' : Mem} {b : β}
    (h : ((f <$> x).run m).run = some (.ok (b, m'))) :
    ∃ a, (x.run m).run = some (.ok (a, m')) ∧ b = f a := by
  rw [map_eq_pure_bind] at h
  obtain ⟨a, m₁, hx, hp⟩ := bind_ok h
  obtain ⟨rfl, rfl⟩ := pure_ok hp
  exact ⟨a, hx, rfl⟩

/-- A step whose run is `pure r` gives no error. -/
theorem noErr_of_run {x : MemM α} {m : Mem} {r : α × Mem} (h : x.run m = pure r) (e : Error) :
    (x.run m).run ≠ some (.error e) := by
  rw [h]; simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run]

end MemM

/-- No footprint entry that overlaps an access races with it: each one happened before the
access (its clock is `≤` the thread's clock), or does not race by its kind. -/
theorem noRace_of {m : Mem} {b o len : Nat} {k : AccessKind}
    (h : ∀ e ∈ m.footprint, e.block = b → o < e.off + e.len → e.off < o + len →
      VClock.le e.clock (m.clocks[m.current]!) = true ∨ racePair e.kind k = none) :
    NoRace m b o len k := by
  unfold NoRace raceAt
  rw [Array.findSome?_eq_none_iff]
  intro e he
  by_cases hb : e.block = b
  · by_cases ho : o < e.off + e.len ∧ e.off < o + len
    · rcases h e he hb ho.1 ho.2 with hl | hr
      · have hle : VClock.le e.clock (VClock.bump (m.clocks[m.current]!) m.current) = true :=
          VClock.le_trans hl (VClock.le_bump _ _)
        simp [VClock.concurrent, hle]
      · simp [hr]
    · have : ¬ (o < e.off + e.len ∧ e.off < o + len) := ho
      simp only [not_and] at this
      by_cases h1 : o < e.off + e.len
      · simp [hb, h1, this h1]
      · simp [h1]
  · simp [hb]

/-- `Thread.join` of a thread that the current thread spawned and did not join yet. -/
theorem join_run {m : Mem} {tid : ThreadId} {rec : ThreadRec} (hr : m.threads[tid]? = some rec)
    (hs : rec.spawner = m.current) (hj : rec.joined = false) :
    ∃ m', ((Thread.join tid).run m).run = some (.ok ((), m')) := by
  unfold Thread.join
  simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, ExceptT.run,
    ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure, set, StateT.set, hr, hs, hj]


theorem locIdx_noErr {m : Mem} {b o len : Nat}
    (hfound : ∀ i, m.atomics.findIdx? (fun l => l.block == b && l.off == o) = some i →
      (m.atomics[i]!).len = len)
    (hnew : m.atomics.findIdx? (fun l => l.block == b && l.off == o) = none →
      ∀ l ∈ m.atomics, l.block ≠ b) (e : Error) :
    ((locIdx b o len).run m).run ≠ some (.error e) := by
  intro h
  unfold locIdx at h
  rcases MemM.bind_err h with h₀ | ⟨a₁, m₁, hg, h₁⟩
  · exact MemM.get_err h₀
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  cases hi : m₁.atomics.findIdx? (fun l => l.block == b && l.off == o) with
  | some i =>
    simp only [hi, hfound i hi, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h₁
    split at h₁
    all_goals
      rcases MemM.bind_err h₁ with h₂ | ⟨_, m₂, hs, h₂⟩
      · exact MemM.set_err h₂
      · exact MemM.pure_err h₂
  | none =>
    have hno : (m₁.atomics.any fun l => l.block == b && o < l.off + l.len && l.off < o + len) =
        false := by
      rw [Array.any_eq_false]
      intro j hj
      have := hnew hi _ (Array.getElem_mem hj)
      simp [this]
    simp only [hi, hno, Bool.false_eq_true, ↓reduceIte] at h₁
    rcases MemM.bind_err h₁ with h₂ | ⟨_, m₂, hs, h₂⟩
    · exact MemM.set_err h₂
    · exact MemM.pure_err h₂

theorem loadPrep_noErr {n : Nat} {ord : AtomicOrder} {align : Nat} {p : Ptr} {rmw : Bool}
    {m : Mem} {b o : Nat} {blk : Block}
    (hacc : (if rmw then m.accessW p (intSize n) align else m.access p (intSize n) align) =
      pure (b, blk, o))
    (hnr : NoRace m b o (intSize n) (if rmw then .atomicWrite else .atomicRead))
    (hloc : ∀ e, ((locIdx b o (intSize n)).run
      (m.recordAt b o (intSize n) (if rmw then .atomicWrite else .atomicRead))).run ≠
        some (.error e)) (e : Error) :
    ((loadPrep n ord align p rmw).run m).run ≠ some (.error e) := by
  intro h
  unfold loadPrep at h
  cases rmw <;> simp only [Bool.false_eq_true, ↓reduceIte] at h hacc hnr hloc <;>
  · rcases MemM.bind_err h with he1 | ⟨a₁, m₁, hg, h1⟩
    · exact MemM.get_err he1
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    rcases MemM.bind_err h1 with he2 | ⟨r, m₂, ha, h2⟩
    · have := MemM.lift_err he2; rw [hacc] at this; simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at this
    obtain ⟨ha, rfl⟩ := MemM.lift_ok ha
    rw [hacc] at ha; simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at ha; subst ha
    rcases MemM.bind_err h2 with he3 | ⟨_, m₃, hr, h3⟩
    · rw [recordAccess_run hnr] at he3; simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at he3
    obtain ⟨-, rfl⟩ := recordAccess_ok hr
    rcases MemM.bind_err h3 with he4 | ⟨li, m₄, hl, h4⟩
    · exact hloc e he4
    rcases MemM.bind_err h4 with he5 | ⟨a₅, m₅, hg, h5⟩
    · exact MemM.get_err he5
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    exact MemM.pure_err h5

theorem rmwWrite_noErr {n : Nat} {li pos : Nat} {ord : AtomicOrder} {rd : Msg} {new : BitVec n}
    {m : Mem} (e : Error) : ((rmwWrite li pos ord rd new).run m).run ≠ some (.error e) := by
  intro h
  unfold rmwWrite at h
  cases hq : ord.isAcq <;> simp only [hq, Bool.false_eq_true, ↓reduceIte] at h
  · rcases MemM.bind_err h with he1 | ⟨a₂, m₂, hg, h1⟩
    · exact MemM.get_err he1
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    rcases MemM.bind_err h1 with he2 | ⟨_, m₃, hi, h2⟩
    · exact MemM.modify_err he2
    · exact MemM.modify_err h2
  · rcases MemM.bind_err h with he3 | ⟨_, m₁, ha, h3⟩
    · exact MemM.modify_err he3
    rcases MemM.bind_err h3 with he4 | ⟨a₂, m₂, hg, h4⟩
    · exact MemM.get_err he4
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    rcases MemM.bind_err h4 with he5 | ⟨_, m₃, hi, h5⟩
    · exact MemM.modify_err he5
    · exact MemM.modify_err h5

theorem atomicRmwAt_noErr {n c : Nat} {op : RmwOp} {signed : Bool} {ord : AtomicOrder}
    {align : Nat} {p : Ptr} {v : BitVec n} {m : Mem}
    (hprep : ∀ e, ((loadPrep n ord align p true).run m).run ≠ some (.error e))
    (hpos : ∀ li opts m₁, ((loadPrep n ord align p true).run m).run =
        some (.ok ((li, opts), m₁)) →
      ∃ pos, opts[c]? = some pos ∧
        ∃ w, (intOfBytes n ((m₁.atomics[li]!).msgs[pos]!).bytes).run = some (.ok w))
    (e : Error) : ((atomicRmwAt c op signed ord align p v).run m).run ≠ some (.error e) := by
  intro h
  unfold atomicRmwAt at h
  rcases MemM.bind_err h with he1 | ⟨⟨li, opts⟩, m₁, hp, h1⟩
  · exact hprep e he1
  obtain ⟨pos, hpos, w, hw⟩ := hpos li opts m₁ hp
  simp only [hpos] at h1
  rcases MemM.bind_err h1 with he2 | ⟨a₂, m₂, hg, h2⟩
  · exact MemM.get_err he2
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  rcases MemM.bind_err h2 with he3 | ⟨old, m₃, hd, h3⟩
  · have := MemM.lift_err he3
    change ExceptT.run (intOfBytes n _) = _ at this
    rw [hw] at this; cases this
  obtain ⟨-, rfl⟩ := MemM.lift_ok hd
  rcases MemM.bind_err h3 with he4 | ⟨_, m₄, hr, h4⟩
  · exact rmwWrite_noErr e he4
  · exact MemM.pure_err h4

theorem atomicLoadAt_noErr {n c : Nat} {ord : AtomicOrder} {align : Nat} {p : Ptr} {m : Mem}
    (hprep : ∀ e, ((loadPrep n ord align p false).run m).run ≠ some (.error e))
    (hpos : ∀ li opts m₁, ((loadPrep n ord align p false).run m).run =
        some (.ok ((li, opts), m₁)) →
      ∃ pos, opts[c]? = some pos ∧
        ∃ w, (intOfBytes n ((m₁.atomics[li]!).msgs[pos]!).bytes).run = some (.ok w))
    (e : Error) : ((atomicLoadAt (n := n) c ord align p).run m).run ≠ some (.error e) := by
  intro h
  unfold atomicLoadAt at h
  rcases MemM.bind_err h with he1 | ⟨⟨li, opts⟩, m₁, hp, h1⟩
  · exact hprep e he1
  obtain ⟨pos, hpos, w, hw⟩ := hpos li opts m₁ hp
  simp only [hpos] at h1
  rcases MemM.bind_err h1 with he2 | ⟨a₂, m₂, hg, h2⟩
  · exact MemM.get_err he2
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  rcases MemM.bind_err h2 with he3 | ⟨_, m₃, ho, h3⟩
  · exact MemM.modify_err he3
  have := modify_ok ho; subst this
  have hw' : (intOfBytes n ((m₂.atomics[li]!).msgs[pos]!).bytes).run = some (.ok w) := hw
  cases hq : ord.isAcq <;> simp only [hq, Bool.false_eq_true, ↓reduceIte] at h3
  · have := MemM.lift_err h3
    change ExceptT.run (intOfBytes n _) = _ at this
    rw [hw'] at this; cases this
  · rcases MemM.bind_err h3 with he4 | ⟨_, m₄, hc, h4⟩
    · exact MemM.modify_err he4
    have := modify_ok hc; subst this
    have := MemM.lift_err h4
    change ExceptT.run (intOfBytes n _) = _ at this
    rw [hw'] at this; cases this

/-- The number of options of an op is at most 1 if every result of its preparation has at most
1. -/
theorem optCount_le_one {x : MemM (Array Nat)} {m : Mem}
    (h : ∀ a m', (x.run m).run = some (.ok (a, m')) → a.size ≤ 1) : optCount x m ≤ 1 := by
  unfold optCount
  split
  · rename_i a m' hr; exact h a m' hr
  · exact Nat.le_refl _

/-- An RMW on an enum or a `bool` (`atomicRmwAs`): the integer RMW, then the decode. -/
theorem atomicRmwAs_ok {α : Type} {n : Nat} [Packed α n] {c : Nat} {op : RmwOp} {ord : AtomicOrder}
    {align : Nat} {p : Ptr} {v r : α} {m m' : Mem}
    (h : ((atomicRmwAs c op ord align p v).run m).run = some (.ok (r, m'))) :
    ∃ b, ((atomicRmwAt c op false ord align p (Packed.toBits v)).run m).run = some (.ok (b, m')) ∧
      (Packed.ofBits? (α := α) b).run = some (.ok r) := by
  unfold atomicRmwAs at h
  obtain ⟨b, m₁, hb, h₁⟩ := MemM.bind_ok h
  obtain ⟨hd, rfl⟩ := MemM.lift_ok h₁
  exact ⟨b, hb, hd⟩

/-- A `cmpxchg` on an enum or a `bool` (`cmpxchgAs`): the integer `cmpxchg`, then the decode of
the value read on failure. -/
theorem cmpxchgAs_ok {α : Type} {n : Nat} [Packed α n] {c : Nat} {succ fail : AtomicOrder}
    {align : Nat} {p : Ptr} {expected new : α} {r : Option α} {m m' : Mem}
    (h : ((cmpxchgAs c succ fail align p expected new).run m).run = some (.ok (r, m'))) :
    (r = none ∧ ((cmpxchgAt c succ fail align p (Packed.toBits expected) (Packed.toBits new)).run
      m).run = some (.ok (none, m'))) ∨
    ∃ b v, r = some v ∧ ((cmpxchgAt c succ fail align p (Packed.toBits expected)
      (Packed.toBits new)).run m).run = some (.ok (some b, m')) ∧
      (Packed.ofBits? (α := α) b).run = some (.ok v) := by
  unfold cmpxchgAs at h
  obtain ⟨o, m₁, ho, h₁⟩ := MemM.bind_ok h
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₁
    exact .inl ⟨rfl, ho⟩
  | some b =>
    obtain ⟨v, h₂, rfl⟩ := MemM.map_ok h₁
    obtain ⟨hd, rfl⟩ := MemM.lift_ok h₂
    exact .inr ⟨b, v, rfl, ho, hd⟩

end Proto
end Conc
end Zig
