import ZigLean.Conc.Lemmas
import ZigLean.Conc.Future

/-!
# Rules for `Io.Future` (`ZigLean/Conc/Future.lean`, C08)

Proof-only (it imports `ZigLean.Mem.Lemmas`), so it stays out of `ZigLean.lean`.

- **Result cells** (`Future.Holds slot r m`): every successful access of the result cells of the
  runtime record at `slot` reads bytes that decode to `r`. Only `blocks` matter
  (`Holds.of_blocks`): joins, forks, cancelation requests and reads keep it.
- **Completion** (`complete_holds`): the task's last step establishes `Holds` for the value it
  wrote; **take** (`take_eq`): a successful read of the result cells after the join returns it.
- **The future value**: a pending future reads back as itself (`decode_pending`), and so does a
  consumed one (`decode_consumed`), so a second `await` returns the stored result
  (`awaitC_consumed`) without a sync op.
- **The future protocol** (`futureProto`): a rely-guarantee protocol (`Zig.Conc.Proto`) for one
  task and its spawner. A task's ghost value records its runtime record and whether it has
  completed; the spawner's records the record and the task's thread. The invariant says that a
  completed task's record holds a result satisfying `R`. `task_wp` is the task side: a body
  whose results satisfy `R`, followed by `Future.complete`, ends with the protocol's `QKid`.
  The spawner's side is in the client proofs (`tests/roadmap/futures/Futures/Proofs.lean`).
-/

namespace Zig

namespace Future

variable {α : Type} [Enc α]

/-- Every successful access of the result cells of the runtime record at `slot` reads `r`. -/
def Holds (slot : Ptr) (r : α) (m : Mem) : Prop :=
  ∀ b blk o, m.access (slot.add (resultOff α)) (Enc.size α) (Enc.align α) = pure (b, blk, o) →
    Enc.decode (blk.bytes.extract o (o + Enc.size α)) = pure r

theorem access_congr {m m' : Mem} (hb : m'.blocks = m.blocks) (p : Ptr) (n a : Nat) :
    m'.access p n a = m.access p n a := by
  unfold Mem.access; rw [hb]

theorem Holds.of_blocks {slot : Ptr} {r : α} {m m' : Mem} (h : Holds slot r m)
    (hb : m'.blocks = m.blocks) : Holds slot r m' := by
  intro b blk o ha
  exact h b blk o (by rw [← access_congr hb]; exact ha)

/-- The value that a successful read of the result cells gives. -/
theorem load_eq {slot : Ptr} {r v : α} {m m' : Mem} (h : Holds slot r m)
    (hl : ((load α (Enc.align α) (slot.add (resultOff α))).run m).run = some (.ok (v, m'))) :
    v = r := by
  obtain ⟨b, blk, o, ha, -, hd, -⟩ := Conc.Proto.load_ok hl
  have := h b blk o ha
  rw [this] at hd
  simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at hd
  exact hd.symm

/-- `take`: the value read is the one that the result cells hold. -/
theorem take_eq {slot : Ptr} {r v : α} {m m' : Mem} (h : Holds slot r m)
    (ht : ((take α slot).run m).run = some (.ok (v, m'))) : v = r := by
  unfold take at ht
  obtain ⟨v', m₁, hl, h₁⟩ := Conc.Proto.MemM.bind_ok ht
  obtain ⟨_, m₂, -, h₂⟩ := Conc.Proto.MemM.bind_ok h₁
  obtain ⟨rfl, -⟩ := Conc.Proto.MemM.pure_ok h₂
  exact load_eq h hl

/-- The task's last step: after `complete slot r`, the result cells hold `r`. `r` must read
back as itself (`LawfulEnc` at `r`; a finite error domain is lawful only on its names). -/
theorem complete_holds {slot : Ptr} {r : α} {m m' : Mem}
    (hs : (Enc.encode r).size = Enc.size α) (hd : Enc.decode (Enc.encode r) = (pure r : Result α))
    (h : ((complete slot r).run m).run = some (.ok ((), m'))) : Holds slot r m' := by
  obtain ⟨b, blk, o, ha, -, rfl⟩ := Conc.Proto.store_ok h
  intro b' blk' o' ha'
  rw [hs] at ha ha'
  have hp : (m.recordAt b o (Enc.size α) .write).access (slot.add (resultOff α))
      (Enc.encode r).size (Enc.align α) = pure (b, blk, o) := by
    rw [access_recordAt, hs]; exact ha
  have hq : (m.recordAt b o (Enc.size α) .write).access (slot.add (resultOff α))
      (Enc.size α) (Enc.align α) = pure (b, blk, o) := by
    rw [access_recordAt]; exact ha
  have hw := access_write_same hp hq
  rw [ha'] at hw
  simp only [pure, ExceptT.pure, ExceptT.mk] at hw
  obtain ⟨rfl, rfl, rfl⟩ := hw
  obtain ⟨-, -, -, h0, hn, -, ho⟩ := access_eq ha
  have hx := extract_writeBytes blk.bytes o (Enc.encode r) (by omega)
  simp only
  rw [← hs, hx, hd]

/-- A successful load right after a successful store at the same pointer and alignment decodes
the stored bytes. -/
theorem load_after_store {β : Type} [Enc β] {q : Ptr} {a : Nat} {v w : β} {m m' m'' : Mem}
    {x : Unit} (hs : (Enc.encode v).size = Enc.size β)
    (h : ((store a q v).run m).run = some (.ok (x, m')))
    (hl : ((load β a q).run m').run = some (.ok (w, m''))) :
    (Enc.decode (Enc.encode v) : Result β).run = some (.ok w) := by
  obtain ⟨b, blk, o, ha, -, rfl⟩ := Conc.Proto.store_ok h
  obtain ⟨b', blk', o', ha', -, hd, -⟩ := Conc.Proto.load_ok hl
  rw [hs] at ha ha'
  have hp : (m.recordAt b o (Enc.size β) .write).access q (Enc.encode v).size a =
      pure (b, blk, o) := by
    rw [access_recordAt, hs]; exact ha
  have hq : (m.recordAt b o (Enc.size β) .write).access q (Enc.size β) a = pure (b, blk, o) := by
    rw [access_recordAt]; exact ha
  have hw := access_write_same hp hq
  rw [ha'] at hw
  simp only [pure, ExceptT.pure, ExceptT.mk] at hw
  obtain ⟨rfl, rfl, rfl⟩ := hw
  obtain ⟨-, -, -, h0, hn, -, ho⟩ := access_eq ha
  have hx := extract_writeBytes blk.bytes o (Enc.encode v) (by omega)
  simp only at hd
  rwa [← hs, hx] at hd

theorem complete_blocks_threads {slot : Ptr} {r : α} {m m' : Mem}
    (h : ((complete slot r).run m).run = some (.ok ((), m'))) : m'.threads = m.threads := by
  obtain ⟨b, blk, o, -, -, rfl⟩ := Conc.Proto.store_ok h
  rfl

theorem take_threads {slot : Ptr} {v : α} {m m' : Mem}
    (ht : ((take α slot).run m).run = some (.ok (v, m'))) : m'.threads = m.threads := by
  unfold take at ht
  obtain ⟨_, m₁, hl, h₁⟩ := Conc.Proto.MemM.bind_ok ht
  obtain ⟨_, m₂, hf, h₂⟩ := Conc.Proto.MemM.bind_ok h₁
  obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h₂
  obtain ⟨_, _, _, -, -, -, rfl⟩ := Conc.Proto.load_ok hl
  obtain ⟨_, _, -, -, rfl⟩ := Conc.Proto.free_ok hf
  rfl

theorem requestCancel_eq {tid : ThreadId} {m m' : Mem} {x : Unit}
    (h : ((requestCancel tid).run m).run = some (.ok (x, m'))) :
    m'.blocks = m.blocks ∧ m'.threads = m.threads := by
  have := Conc.Proto.modify_ok h
  subst this
  split <;> exact ⟨rfl, rfl⟩

theorem dropCancel_eq {tid : ThreadId} {m m' : Mem} {x : Unit}
    (h : ((dropCancel tid).run m).run = some (.ok (x, m'))) :
    m'.blocks = m.blocks ∧ m'.threads = m.threads := by
  have := Conc.Proto.modify_ok h
  subst this
  exact ⟨rfl, rfl⟩

theorem takeCancel_eq {m m' : Mem} {c : Except ErrName Unit}
    (h : (takeCancel.run m).run = some (.ok (c, m'))) :
    m'.blocks = m.blocks ∧ m'.threads = m.threads ∧ (c = .ok () ∨ c = .error "Canceled") := by
  unfold takeCancel at h
  obtain ⟨a, m₁, hg, h₁⟩ := Conc.Proto.MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok hg
  split at h₁
  · obtain ⟨_, m₂, hs, h₂⟩ := Conc.Proto.MemM.bind_ok h₁
    have := Conc.Proto.MemM.set_ok hs
    subst this
    obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.pure_ok h₂
    exact ⟨rfl, rfl, .inr rfl⟩
  · obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.pure_ok h₁
    exact ⟨rfl, rfl, .inl rfl⟩

/-! ## The bytes of a future -/

theorem eight_le_resultOff : 8 ≤ resultOff α := le_alignUp 8 _

theorem size_optPtr : Enc.size (Option Ptr) = 8 := rfl

theorem resultOff_add_le_size : resultOff α + Enc.size α ≤ size α := le_alignUp _ _

theorem extract_replicate (n o k : Nat) (h : o + k ≤ n) :
    (Array.replicate n Byte.undef).extract o (o + k) = Array.replicate k Byte.undef := by
  apply Array.ext
  · simp; omega
  · intro i _ _; simp

theorem task_bytes (task : Option Ptr) :
    (writeBytes (Array.replicate (size α) .undef) 0 (Enc.encode task)).size = size α ∧
      (writeBytes (Array.replicate (size α) .undef) 0 (Enc.encode task)).extract 0 8 =
        Enc.encode task := by
  have h8 : (Enc.encode task).size = 8 := LawfulEnc.size_encode task
  have hS : 8 ≤ size α := by
    have := eight_le_resultOff (α := α); have := resultOff_add_le_size (α := α); omega
  refine ⟨by rw [writeBytes_size _ _ _ (by rw [h8]; simp; omega)]; simp, ?_⟩
  have := extract_writeBytes (Array.replicate (size α) Byte.undef) 0 (Enc.encode task)
    (by rw [h8]; simp; omega)
  rwa [h8, Nat.zero_add] at this

/-- A pending future reads back as itself (a nonempty result type: its undefined bytes are
`none`). -/
theorem decode_pending (slot : Ptr) (hs : Enc.size α ≠ 0) :
    (Enc.decode (Enc.encode ({ task := some slot, result := none } : Future α)) :
      Result (Future α)) = pure { task := some slot, result := none } := by
  show (do
    let task ← (Enc.decode ((bytes ({ task := some slot, result := none } : Future α)).extract 0 8) :
      Result (Option Ptr))
    let result ← decodeResult ((bytes ({ task := some slot, result := none } : Future α)).extract
      (resultOff α) (resultOff α + Enc.size α))
    pure ({ task, result } : Future α)) = _
  obtain ⟨hsz, hx⟩ := task_bytes (α := α) (some slot)
  have h8 := eight_le_resultOff (α := α)
  have hle := resultOff_add_le_size (α := α)
  have hr : (writeBytes (Array.replicate (size α) .undef) 0 (Enc.encode (some slot))).extract
      (resultOff α) (resultOff α + Enc.size α) = Array.replicate (Enc.size α) .undef := by
    rw [extract_writeBytes_disjoint _ _ _ _ _ (by rw [LawfulEnc.size_encode, size_optPtr]; simp; omega)
      (by simp; omega) (by rw [LawfulEnc.size_encode, size_optPtr]; omega)]
    exact extract_replicate _ _ _ hle
  simp only [bytes, hx, hr, LawfulEnc.decode_encode, decodeResult]
  have hall : (Array.replicate (Enc.size α) Byte.undef).all (· == .undef) = true := by
    rw [Array.all_eq_true]; intro i hi; simp
  simp only [bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont, hall, hs,
    ne_eq, not_false_eq_true, and_self, ↓reduceIte, Option.bind_some]

/-- A consumed future reads back as itself, for a result that reads back and whose bytes are not
all undefined. -/
theorem decode_consumed {r : α} (hs : (Enc.encode r).size = Enc.size α)
    (hd : Enc.decode (Enc.encode r) = (pure r : Result α))
    (hdef : (Enc.encode r).all (· == .undef) = false) :
    (Enc.decode (Enc.encode ({ task := none, result := some r } : Future α)) :
      Result (Future α)) = pure { task := none, result := some r } := by
  show (do
    let task ← (Enc.decode ((bytes ({ task := none, result := some r } : Future α)).extract 0 8) :
      Result (Option Ptr))
    let result ← decodeResult ((bytes ({ task := none, result := some r } : Future α)).extract
      (resultOff α) (resultOff α + Enc.size α))
    pure ({ task, result } : Future α)) = _
  obtain ⟨hsz, hx⟩ := task_bytes (α := α) none
  have h8 := eight_le_resultOff (α := α)
  have hle := resultOff_add_le_size (α := α)
  have hn : (Enc.encode (none : Option Ptr)).size = 8 := LawfulEnc.size_encode _
  have hw := extract_writeBytes (writeBytes (Array.replicate (size α) .undef) 0
    (Enc.encode (none : Option Ptr))) (resultOff α) (Enc.encode r) (by rw [hsz, hs]; omega)
  have ht := extract_writeBytes_disjoint (writeBytes (Array.replicate (size α) .undef) 0
    (Enc.encode (none : Option Ptr))) (resultOff α) (Enc.encode r) 0 8 (by rw [hsz, hs]; omega)
    (by rw [hsz]; omega) (by rw [hs]; omega)
  rw [hs] at hw
  simp only [Nat.zero_add] at ht
  simp only [bytes, ht, hx, hw, LawfulEnc.decode_encode, decodeResult, hdef, hd]
  simp [bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont, Functor.map,
    ExceptT.map]

variable {Tgt σ : Type}

/-- **Idempotence.** `await` and `cancel` of a consumed future read it and return the stored
result: no sync op, no join, no change besides the read. -/
theorem awaitC_consumed {io : Io} {p : Ptr} {r : α} {s : σ} {m m' : Mem} (n : Nat)
    (hl : (load (Future α) (align α) p).run m = pure ({ task := none, result := some r }, m')) :
    ((awaitC io p : CM Tgt σ α).run s) n m = .leaf (some (.ok ((r, s), m'))) := by
  have e : (ConcM.liftMem (load (Future α) (align α) p) : ConcM Tgt (Future α)) n m =
      .leaf (some (.ok ({ task := none, result := some r }, m'))) := by
    simp only [ConcM.liftMem, hl]; rfl
  simp only [awaitC, callMC, callRC, StateT.run_bind, StateT.run_lift]
  simp only [bind, e, CoN.bind]
  rfl

theorem cancelC_consumed {io : Io} {p : Ptr} {r : α} {s : σ} {m m' : Mem} (n : Nat)
    (hl : (load (Future α) (align α) p).run m = pure ({ task := none, result := some r }, m')) :
    ((cancelC io p : CM Tgt σ α).run s) n m = .leaf (some (.ok ((r, s), m'))) := by
  have e : (ConcM.liftMem (load (Future α) (align α) p) : ConcM Tgt (Future α)) n m =
      .leaf (some (.ok ({ task := none, result := some r }, m'))) := by
    simp only [ConcM.liftMem, hl]; rfl
  simp only [cancelC, callMC, callRC, StateT.run_bind, StateT.run_lift]
  simp only [bind, e, CoN.bind]
  rfl

end Future

/-! ## The future protocol -/

namespace Conc

/-- Ghost values: the spawner knows the record and the task's thread; a task knows its record
and whether it has completed. -/
inductive FGh where
  | none
  | main (slot : Ptr) (task : ThreadId)
  | task (slot : Ptr) (done : Bool)

/-- The protocol of one `Io.async` task whose results satisfy `R`. `slotOf` reads the runtime
record out of a spawn target (the generated `Tgt.<worker>_future` constructors). -/
def futureProto {Tgt α : Type} [Enc α] (slotOf : Tgt → Option Ptr) (R : α → Prop) :
    Proto Tgt FGh where
  inv G m := ∀ u slot d, G u = .task slot d →
    G 0 = .main slot u ∧ (d = true → ∃ r, R r ∧ Future.Holds slot r m)
  init tgt g := ∃ slot, slotOf tgt = some slot ∧ g = .task slot false
  fin g := ∃ slot, g = .task slot true

namespace FutureProto

variable {Tgt α : Type} [Enc α] {slotOf : Tgt → Option Ptr} {R : α → Prop}

theorem strict_false : (futureProto slotOf R).strict = false := rfl

theorem not_strict {φ : Prop} : (futureProto slotOf R).strict = true → φ := fun h => by
  rw [strict_false] at h; cases h

theorem inv_of_blocks {G : ThreadId → FGh} {m m' : Mem} (hi : (futureProto slotOf R).inv G m)
    (hb : m'.blocks = m.blocks) : (futureProto slotOf R).inv G m' := by
  intro u slot d hu
  obtain ⟨h0, hd⟩ := hi u slot d hu
  exact ⟨h0, fun e => let ⟨r, hr, hh⟩ := hd e; ⟨r, hr, hh.of_blocks hb⟩⟩

/-- The spawner's ghost value is not a task's. -/
theorem inv_main {G : ThreadId → FGh} {m : Mem} {slot : Ptr} {c : ThreadId}
    (hi : (futureProto slotOf R).inv G m) (h0 : G 0 = .main slot c) {u : ThreadId} {s : Ptr}
    {d : Bool} (hu : G u = .task s d) : s = slot ∧ u = c := by
  obtain ⟨h, -⟩ := hi u s d hu
  rw [h0] at h; cases h; exact ⟨rfl, rfl⟩

/-- After the join of the task `c` (`fin`), the record of the spawner's ghost value holds a
result that satisfies `R`. -/
theorem joined_holds {G : ThreadId → FGh} {m : Mem} {slot : Ptr} {c : ThreadId}
    (hi : (futureProto slotOf R).inv G m) (h0 : G 0 = .main slot c)
    {tid : ThreadId} (hf : (futureProto slotOf R).fin (G tid)) :
    tid = c ∧ ∃ r, R r ∧ Future.Holds slot r m := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨rfl, rfl⟩ := inv_main hi h0 hs
  exact ⟨rfl, (hi tid s true hs).2 rfl⟩

/-- The task side: a body whose every result satisfies `R` and that keeps the task's ghost
value and the invariant, followed by `Future.complete`, ends as the protocol requires
(`QKid`). -/
theorem task_wp {u : ThreadId} {slot : Ptr} {body : ConcM Tgt α} {G : ThreadId → FGh} {m : Mem}
    {n : Nat} (hu : 0 < u)
    (hlaw : ∀ r, R r → (Enc.encode r).size = Enc.size α ∧
      Enc.decode (Enc.encode r) = (pure r : Result α))
    (hbody : (futureProto slotOf R).WP u body (fun r G' m' _ => R r ∧ G' u = .task slot false ∧
      (futureProto slotOf R).inv G' m') G m n) :
    (futureProto slotOf R).WP u (body >>= fun r => ConcM.liftMem (Future.complete slot r))
      ((futureProto slotOf R).QKid u) G m n := by
  refine Proto.WP.bind (Proto.WP.mono (fun r G' m' d ⟨hr, hgu, hi⟩ => ?_) hbody)
  refine Proto.WP.liftMem (fun _ _ => rfl) fun _ m'' hc => ?_
  obtain ⟨hs, hd⟩ := hlaw r hr
  refine ⟨by rw [Future.complete_blocks_threads hc], .task slot true, ?_, ⟨slot, rfl⟩,
    fun h => by cases h⟩
  have h0 := (hi u slot false hgu).1
  intro w s dd hw
  by_cases hwu : w = u
  · subst hwu
    rw [upd_self] at hw
    cases hw
    refine ⟨by rw [upd_ne _ _ (show (0 : ThreadId) ≠ w from Nat.ne_of_lt hu)]; exact h0, fun _ => ⟨r, hr, ?_⟩⟩
    exact Future.complete_holds hs hd hc
  · rw [upd_ne _ _ hwu] at hw
    obtain ⟨-, rfl⟩ := inv_main hi h0 hw
    exact absurd rfl hwu

variable {σ : Type}

theorem load_threads {β : Type} [Enc β] {a : Nat} {q : Ptr} {v : β} {m m' : Mem}
    (h : ((load β a q).run m).run = some (.ok (v, m'))) : m'.threads = m.threads := by
  obtain ⟨_, _, _, -, -, -, rfl⟩ := Proto.load_ok h
  rfl

theorem store_threads {β : Type} [Enc β] {a : Nat} {q : Ptr} {v : β} {m m' : Mem} {x : Unit}
    (h : ((store a q v).run m).run = some (.ok (x, m'))) : m'.threads = m.threads := by
  obtain ⟨_, _, _, -, -, rfl⟩ := Proto.store_ok h
  rfl

/-- `Io.async` in the spawner `t`: a runtime record, a stop at the spawn (the task starts with a
ghost value of `init`), then the spawner writes the task's id into the record. -/
theorem wp_asyncC {γ : Type} {P : Proto Tgt γ} {t : ThreadId} {mk : Ptr → Tgt} {s : σ}
    {G : ThreadId → γ} {m : Mem} {n : Nat}
    {Q : Future α × σ → (ThreadId → γ) → Mem → Nat → Prop} (hns : P.strict = false)
    (h : ∀ slot m₁, ((Future.slotAlloc α).run m).run = some (.ok (slot, m₁)) →
      ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m₁ ∧ ∀ G₁ m₂, G₁ t = g → P.inv G₁ m₂ →
        ∃ g₀, P.init (mk slot) g₀ ∧ ∀ child m₃,
          (Thread.fork.run { m₂ with current := t }).run = some (.ok (child, m₃)) →
          ∀ m₄, ((store 8 slot child).run m₃).run = some (.ok ((), m₄)) →
            Q ({ task := some slot, result := none }, s) (upd G₁ child g₀) m₄ k) :
    P.WP t ((asyncC mk : CM Tgt σ (Future α)).run s) Q G m n := by
  unfold asyncC
  simp only [StateT.run_bind, StateT.run_lift]
  refine Proto.WP.bind (Proto.WP.callMC (fun _ _ => hns) fun slot m₁ ha => ⟨?_, ?_⟩)
  · obtain ⟨-, rfl⟩ := Proto.alloc_ok ha; rfl
  refine Proto.WP.bind (Proto.WP.bind (Proto.WP.sync fun k hk => ?_))
  obtain ⟨g, hi, hc⟩ := h slot m₁ ha k hk
  refine ⟨g, hi, fun G₁ m₂ hg hi₂ => ?_⟩
  obtain ⟨g₀, hg₀, hk'⟩ := hc G₁ m₂ hg hi₂
  refine ⟨g₀, hg₀, fun child m₃ hf => Proto.WP.pure' ?_⟩
  refine Proto.WP.bind (Proto.WP.callMC (fun _ _ => hns) fun x m₄ hs => ⟨?_, ?_⟩)
  · rw [store_threads hs]
  · exact Proto.WP.pure' (hk' child m₃ hf m₄ hs)

/-- `Io.checkCancel` in thread `t`: a stop, then the cancelation point. -/
theorem wp_checkCancelC {γ : Type} {P : Proto Tgt γ} {t : ThreadId} {io : Io} {s : σ}
    {G : ThreadId → γ} {m : Mem} {n : Nat}
    {Q : Except ErrName Unit × σ → (ThreadId → γ) → Mem → Nat → Prop} (hns : P.strict = false)
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧ ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      ∀ c m₂, (Future.takeCancel.run { m₁ with current := t }).run = some (.ok (c, m₂)) →
        Q (c, s) G₁ m₂ k) :
    P.WP t ((checkCancelC io : CM Tgt σ (Except ErrName Unit)).run s) Q G m n := by
  unfold checkCancelC
  simp only [StateT.run_bind, StateT.run_lift]
  refine Proto.WP.bind (Proto.WP.bind (Proto.WP.map (Proto.WP.sync fun k hk => ?_)))
  obtain ⟨g, hi, hc⟩ := h k hk
  refine ⟨g, hi, fun G₁ m₁ hg hi₁ => Proto.WP.pure' ?_⟩
  refine Proto.WP.callMC (fun _ _ => hns) fun c m₂ ht => ⟨?_, hc G₁ m₁ hg hi₁ c m₂ ht⟩
  rw [(Future.takeCancel_eq ht).2.1]

/-- The spawner's `await` of its pending future at `p`, with record `slot` and task `child`, in
the future protocol. Before the join the task has not run (`htasks`); after it, the record
holds a result satisfying `R`, which `await` returns. -/
theorem await_wp {io : Io} {p slot : Ptr} {child : ThreadId} {s : σ} {G : ThreadId → FGh}
    {m : Mem} {n : Nat} {Q : α × σ → (ThreadId → FGh) → Mem → Nat → Prop}
    (hp : ∀ f m', ((load (Future α) (Future.align α) p).run m).run = some (.ok (f, m')) →
      f = { task := some slot, result := none })
    (htasks : ∀ u sl d, G u = .task sl d → u = child ∧ sl = slot ∧ d = false)
    (hQ : ∀ r G' m' d, R r → Q (r, s) G' m' d) :
    (futureProto slotOf R).WP 0 ((awaitC io p : CM Tgt σ α).run s) Q G m n := by
  unfold awaitC consumeC
  simp only [StateT.run_bind]
  refine Proto.WP.bind (Proto.WP.callMC (fun _ _ => rfl) fun f m₁ hl => ⟨by rw [load_threads hl], ?_⟩)
  obtain rfl := hp f m₁ hl
  simp only [StateT.run_bind]
  refine Proto.WP.bind (Proto.WP.callMC (fun _ _ => rfl) fun tid m₂ ht => ⟨by rw [load_threads ht], ?_⟩)
  simp only [StateT.run_bind]
  refine Proto.WP.bind ?_
  refine Proto.WP.joinC ?_
  intro k _
  refine ⟨.main slot child, ?_, fun G₁ m₃ hg hi₃ =>
    ⟨not_strict, fun hf => ⟨not_strict, fun m₄ hj => ?_⟩⟩⟩
  · intro u sl d hu
    by_cases hu0 : u = 0
    · subst hu0; rw [upd_self] at hu; cases hu
    · rw [upd_ne _ _ hu0] at hu
      obtain ⟨rfl, rfl, rfl⟩ := htasks u sl d hu
      exact ⟨upd_self _ _ _, fun h => by cases h⟩
  obtain ⟨-, r, hr, hh⟩ := joined_holds hi₃ hg hf
  have hh₄ : Future.Holds slot r m₄ := by
    obtain ⟨_, -, -, rfl⟩ := Proto.join_eq hj
    exact hh.of_blocks rfl
  simp only [StateT.run_bind]
  refine Proto.WP.bind (Proto.WP.callMC (fun _ _ => rfl) fun v m₅ htk => ⟨by rw [Future.take_threads htk], ?_⟩)
  obtain rfl := Future.take_eq hh₄ htk
  simp only [StateT.run_bind]
  refine Proto.WP.bind (Proto.WP.callMC (fun _ _ => rfl) fun _ m₆ hs => ⟨by rw [store_threads hs], ?_⟩)
  exact Proto.WP.pure' (hQ v _ _ _ hr)

/-- The spawner's `cancel` of its pending future: as `await_wp`, with a stop before the
cancelation request, after which the task may already have completed. -/
theorem cancel_wp {io : Io} {p slot : Ptr} {child : ThreadId} {s : σ} {G : ThreadId → FGh}
    {m : Mem} {n : Nat} {Q : α × σ → (ThreadId → FGh) → Mem → Nat → Prop}
    (hp : ∀ f m', ((load (Future α) (Future.align α) p).run m).run = some (.ok (f, m')) →
      f = { task := some slot, result := none })
    (htasks : ∀ u sl d, G u = .task sl d → u = child ∧ sl = slot ∧ d = false)
    (hQ : ∀ r G' m' d, R r → Q (r, s) G' m' d) :
    (futureProto slotOf R).WP 0 ((cancelC io p : CM Tgt σ α).run s) Q G m n := by
  unfold cancelC consumeC
  simp only [StateT.run_bind]
  refine Proto.WP.bind (Proto.WP.callMC (fun _ _ => rfl) fun f m₁ hl => ⟨by rw [load_threads hl], ?_⟩)
  obtain rfl := hp f m₁ hl
  simp only [StateT.run_bind]
  refine Proto.WP.bind (Proto.WP.callMC (fun _ _ => rfl) fun tid m₂ ht => ⟨by rw [load_threads ht], ?_⟩)
  simp only [StateT.run_bind, StateT.run_lift]
  have hstop : (futureProto slotOf R).inv (upd G 0 (.main slot child)) m₂ := by
    intro u sl d hu
    by_cases hu0 : u = 0
    · subst hu0; rw [upd_self] at hu; cases hu
    · rw [upd_ne _ _ hu0] at hu
      obtain ⟨rfl, rfl, rfl⟩ := htasks u sl d hu
      exact ⟨upd_self _ _ _, fun h => by cases h⟩
  refine Proto.WP.bind (Proto.WP.bind (Proto.WP.map (Proto.WP.sync fun k _ =>
    ⟨.main slot child, hstop, fun G₁ m₃ hg hi₃ => ?_⟩)))
  refine Proto.WP.pure' (Proto.WP.bind (Proto.WP.callMC (fun _ _ => rfl) fun _ m₄ hc => ?_))
  obtain ⟨hb₄, ht₄⟩ := Future.requestCancel_eq hc
  refine ⟨by rw [ht₄], ?_⟩
  have hi₄ := inv_of_blocks hi₃ hb₄
  simp only [StateT.run_bind]
  refine Proto.WP.bind (Proto.WP.bind ?_)
  refine Proto.WP.joinC ?_
  intro k' _
  refine ⟨.main slot child, ?_,
    fun G₂ m₅ hg₂ hi₅ => ⟨not_strict, fun hf => ⟨not_strict, fun m₆ hj => ?_⟩⟩⟩
  · rw [show upd G₁ 0 (.main slot child) = G₁ by rw [← hg]; exact Proto.upd_same _ _]
    exact hi₄
  obtain ⟨-, r, hr, hh⟩ := joined_holds hi₅ hg₂ hf
  have hh₆ : Future.Holds slot r m₆ := by
    obtain ⟨_, -, -, rfl⟩ := Proto.join_eq hj
    exact hh.of_blocks rfl
  simp only [StateT.run_bind]
  refine Proto.WP.bind (Proto.WP.callMC (fun _ _ => rfl) fun v m₇ htk => ⟨by rw [Future.take_threads htk], ?_⟩)
  obtain rfl := Future.take_eq hh₆ htk
  simp only [StateT.run_bind]
  refine Proto.WP.bind (Proto.WP.callMC (fun _ _ => rfl) fun _ m₈ hs => ⟨by rw [store_threads hs], ?_⟩)
  refine Proto.WP.pure' ?_
  refine Proto.WP.bind (Proto.WP.callMC (fun _ _ => rfl) fun _ m₉ hd => ⟨?_, ?_⟩)
  · rw [(Future.dropCancel_eq hd).2]
  · exact Proto.WP.pure' (hQ v _ _ _ hr)

end FutureProto

end Conc

end Zig
