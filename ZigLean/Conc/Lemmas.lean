import ZigLean.Conc.Logic
import ZigLean.Mem.Lemmas

/-!
# Rules for generated concurrent code

The `WP` rules of `ZigLean/Conc/Logic.lean` for the steps that `Emit.lean` writes in a
concurrent function (`Zig.CM`): a call in `MemM` (`liftM`, `callMC`, `callRC`), the sync ops
(`pickC`, `spawnC`, `joinC`), and `run'` of a body. A proof unfolds the generated code, applies
these rules one step at a time, and uses the `*_ok` lemmas for what a `MemM` step that gave a
result did: with partial correctness a step can fail (a race is `.illegal`), so the lemmas go
from a result back to the memory.
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

/-- A call in `MemM`, lifted into the body: no stop. -/
theorem WP.liftM {x : MemM α} {s : σ} {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ a m', (x.run m).run = some (.ok (a, m')) →
      m'.threads.size = m.threads.size ∧ Q (a, s) G m' n) :
    P.WP t ((liftM x : CM Tgt σ α).run s) Q G m n := by
  show P.WP t (ConcM.liftMem x >>= fun a => pure (a, s)) Q G m n
  exact WP.bind (WP.liftMem fun a m' hr => ⟨(h a m' hr).1, WP.pure' (h a m' hr).2⟩)

theorem WP.callMC {x : MemM α} {s : σ} {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ a m', (x.run m).run = some (.ok (a, m')) →
      m'.threads.size = m.threads.size ∧ Q (a, s) G m' n) :
    P.WP t ((callMC x : CM Tgt σ α).run s) Q G m n :=
  WP.liftM (x := x) h

/-- A call to a pure function: no stop, the memory does not change. -/
theorem WP.callRC {x : Result α} {s : σ} {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ a, x.run = some (.ok a) → Q (a, s) G m n) :
    P.WP t ((callRC x : CM Tgt σ α).run s) Q G m n := by
  show P.WP t (ConcM.liftMem (StateT.lift x) >>= fun a => pure (a, s)) Q G m n
  refine WP.bind (WP.liftMem fun a m' hr => ?_)
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
      ∀ c, Q (c, s) G₁ { m₁ with current := t } k) :
    P.WP t ((pickC count : CM Tgt σ Nat).run s) Q G m n := by
  show P.WP t (ConcM.sync (.pick count) >>= fun a => pure (a, s)) Q G m n
  refine WP.bind (WP.sync fun k hk => ?_)
  obtain ⟨g, hi, hc⟩ := h k hk
  exact ⟨g, hi, fun G₁ m₁ hg hi₁ c => WP.pure' (hc G₁ m₁ hg hi₁ c)⟩

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

/-- `Thread.join` of `tid`: it goes on after thread `tid` ended, so `fin (G₁ tid)` holds. -/
theorem WP.joinC {tid : ThreadId} {s : σ} {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧ ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      P.fin (G₁ tid) → ∀ m',
        ((Thread.join tid).run { m₁ with current := t }).run = some (.ok ((), m')) →
        Q ((), s) G₁ m' k) :
    P.WP t ((joinC tid : CM Tgt σ Unit).run s) Q G m n := by
  show P.WP t (((fun _ => ()) <$> ConcM.sync (Tgt := Tgt) (.join tid)) >>= fun a =>
    pure (a, s)) Q G m n
  refine WP.bind (WP.map (WP.sync fun k hk => ?_))
  obtain ⟨g, hi, hc⟩ := h k hk
  exact ⟨g, hi, fun G₁ m₁ hg hi₁ hf m' hj => WP.pure' (hc G₁ m₁ hg hi₁ hf m' hj)⟩


/-! ## What a step in `MemM` did, from its result -/

namespace MemM

theorem bind_ok {x : MemM α} {f : α → MemM β} {m m'' : Mem} {b : β}
    (h : ((x >>= f).run m).run = some (.ok (b, m''))) :
    ∃ a m', (x.run m).run = some (.ok (a, m')) ∧ ((f a).run m').run = some (.ok (b, m'')) := by
  rw [StateT.run_bind, ExceptT.run_bind] at h
  match hx : (x.run m).run, h with
  | none, h => simp at h
  | some (.error _), h => simp [pure] at h
  | some (.ok (a, m')), h => exact ⟨a, m', rfl, by simpa [hx] using h⟩

theorem lift_ok {r : Result α} {m m' : Mem} {a : α}
    (h : ((StateT.lift r : MemM α).run m).run = some (.ok (a, m'))) :
    r.run = some (.ok a) ∧ m' = m := by
  simp only [StateT.run, StateT.lift, ExceptT.run_bind] at h
  match hr : r.run, h with
  | none, h => simp at h
  | some (.error _), h => simp [pure] at h
  | some (.ok a'), h =>
    simp [pure, ExceptT.pure, ExceptT.mk] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem get_ok {m m' : Mem} {a : Mem} (h : ((get : MemM Mem).run m).run = some (.ok (a, m'))) :
    a = m ∧ m' = m := by
  simp [get, getThe, MonadStateOf.get, StateT.get, StateT.run, pure, ExceptT.pure,
    ExceptT.mk, ExceptT.run] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem pure_ok {x : α} {m m' : Mem} {a : α}
    (h : ((pure x : MemM α).run m).run = some (.ok (a, m'))) : a = x ∧ m' = m := by
  simp [StateT.run, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem throw_ok {e : Error} {m m' : Mem} {a : α}
    (h : ((throw e : MemM α).run m).run = some (.ok (a, m'))) : False := by
  simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, StateT.run, ExceptT.run,
    ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont] at h

theorem set_ok {x : Mem} {m m' : Mem} {a : PUnit}
    (h : ((set x : MemM PUnit).run m).run = some (.ok (a, m'))) : m' = x := by
  simp [set, StateT.set, StateT.run, pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at h
  exact h.symm

end MemM

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

end Proto
end Conc
end Zig
