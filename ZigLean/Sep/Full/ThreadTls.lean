import ZigLean.Sep.Full.ThreadOwned
import ZigLean.Sep.Full.Local
import ZigLean.Sep.Full.Init
import ZigLean.Conc.TlsLemmas
import ZigLean.Sep.Full.AutoThread

/-!
# Thread-local storage in the full-state thread logic

Rules for a thread with `threadlocal` globals (`ZigLean/Mem/Tls.lean`, `ConcM.tlsThread`) over the
threads' parts (`FOwned`, `ZigLean/Sep/Full/ThreadOwned.lean`); `docs/sep-threads.md` §TLS.

- **An instance is a block of its thread**: a `.global` block with its bytes and its full extent
  (`gblk`). `tlsOwn inits ids` is the thread's instances after its start: one new block per
  `threadlocal` global of `inits`, in order, keyed as in `inits`, holding the initial bytes at an
  aligned address. `tlsDying bids` is the instances at the thread's end, with any bytes.
- **Thread start** (`tlsEnter`): the allocations are a thread triple (`FTTriple.tlsAllocs`); the
  registration changes only the thread's record (`FOwned.setTls`). Together:
  `WP.liftMem_tlsEnter_fowned`.
- **Thread end** (`tlsExit`): it frees the instances that the thread's record lists
  (`WP.liftMem_tlsExit_fowned`, from `FTTriple.freeBlocks`).
- **`tlsPtr`** reads only the thread records, which are facts of the protocol, not resources of a
  thread: in a step of generated code it is resolved against the current memory
  (`WP.liftMem_tlsPtr_bind`, from `WP.liftMem_congr`: a `MemM` step is read only at the memory
  it runs in), and the rest of the step is a thread triple again.
- **`main`'s instances** are blocks of the start memory: `FOwned.one` gives `main` any resource
  that the start memory holds (`initRes_holds`, `ZigLean/Sep/Full/Init.lean`).
-/

namespace Zig
namespace Full

open FAssn Conc Proto

/-! ## Instances -/

/-- A `.global` block `b` at address `A` with the bytes `bs` and its full extent. -/
abbrev gblk (b : BlockId) (A : Nat) (bs : Array Byte) : FAssn :=
  up (bytesAt ⟨some b, 0⟩ A bs.size .global bs) ⋆ bext b bs.size .global

/-- A new instance of a `threadlocal` global with the initial bytes `bs` and the alignment `a`. -/
abbrev tlsInst (b : BlockId) (bs : Array Byte) (a : Nat) : FAssn :=
  FAssn.ex fun A => ⟪A % a = 0⟫ ⋆ gblk b A bs

/-- The instances `ids` (key, block) of the `threadlocal` globals `inits` (key, initial bytes,
alignment) after a thread start. -/
def tlsOwn : List (BlockId × Array Byte × Nat) → List (BlockId × BlockId) → FAssn
  | [], [] => emp
  | (k, bs, a) :: rest, (k', b) :: ids => ⟪k' = k⟫ ⋆ (tlsInst b bs a ⋆ tlsOwn rest ids)
  | _, _ => fun _ => False

/-- The instance blocks `bids` at a thread's end: whole `.global` blocks, with any bytes. -/
def tlsDying : List BlockId → FAssn
  | [] => emp
  | b :: bids =>
    (FAssn.ex fun A => FAssn.ex fun bs : Array Byte => ⟪0 < bs.size⟫ ⋆ gblk b A bs) ⋆ tlsDying bids

/-- The instances of one `threadlocal` global. -/
theorem tlsOwn_one {k : BlockId} {bs : Array Byte} {a : Nat} {l : List (BlockId × BlockId)}
    {r : Res} (h : tlsOwn [(k, bs, a)] l r) : ∃ b, l = [(k, b)] ∧ tlsInst b bs a r := by
  match l, h with
  | [(k', b)], h =>
    have h' : (⟪k' = k⟫ ⋆ (tlsInst b bs a ⋆ emp)) r := h
    obtain ⟨e, hi⟩ := sep_lift.mp h'
    subst e
    exact ⟨b, rfl, sep_emp.mp hi⟩
  | [], h => exact h.elim
  | _ :: _ :: _, h =>
    obtain ⟨-, h⟩ := sep_lift.mp h
    obtain ⟨_, _, -, -, -, h⟩ := h
    exact h.elim

/-! ## Thread triples -/

namespace FTTriple

/-- A pure step with a known result (`StateT.lift` of a `Result`: wrapping arithmetic, checks). -/
theorem liftR_ok {α : Type} {r : Result α} {x : α} {P : FAssn} (hr : r.run = some (.ok x)) :
    FTTriple P (StateT.lift r : MemM α) (fun y => ⟪y = x⟫ ⋆ P) :=
  FTTriple.of_run fun m r' _ hh hp hc ho =>
    ⟨x, m, r', by rw [show r = pure x from hr]; rfl, hh, sep_lift.mpr ⟨rfl, hp⟩, hc, ho,
      FStepIn.refl m _⟩

/-- One new instance (`tlsAlloc`): a new `.global` block with the initial bytes. -/
theorem tlsAlloc {bs : Array Byte} {a : Nat} (ha : 0 < a) (hn : 0 < bs.size) :
    FTTriple emp (Zig.tlsAlloc bs a)
      (fun p => FAssn.ex fun b => ⟪p = ⟨some b, 0⟩⟫ ⋆ tlsInst b bs a) := by
  unfold Zig.tlsAlloc
  refine (FTTriple.ofSeq (FTriple.alloc' .global bs.size a ha hn (by decide))
    (ThreadLocal.alloc .global bs.size a)).bind fun p =>
    FTTriple.ex fun A => FTTriple.ex fun b => FTTriple.lift fun ⟨hpb, h0, hA⟩ => ?_
  have hp : p = ⟨some b, 0⟩ := by cases p; simp_all
  subst hp
  refine (FTTriple.storeBytesAt (k := 0) (a := a) bs hpb (by simp [Ptr.add]) hn (by simp)
    (by simp [hA]) (by decide)).bind fun _ => ?_
  rw [writeBytes_all (by simp)]
  exact FTTriple.ret' _ fun _ h => ⟨b, sep_lift.mpr ⟨rfl, A, sep_lift.mpr ⟨hA, h⟩⟩⟩

/-- **The instances of a thread start** (`tlsAllocs`), for every list of `threadlocal` globals. -/
theorem tlsAllocs : ∀ (inits : List (BlockId × Array Byte × Nat)),
    (∀ x ∈ inits, 0 < x.2.2 ∧ 0 < x.2.1.size) →
    FTTriple emp (Zig.tlsAllocs inits) (fun ids => tlsOwn inits ids.toList)
  | [], _ => by
    simp only [Zig.tlsAllocs]
    exact FTTriple.ret' _ fun _ h => by simpa [tlsOwn] using h
  | (key, bs, a) :: rest, h => by
    obtain ⟨ha, hn⟩ := h _ List.mem_cons_self
    simp only [Zig.tlsAllocs]
    refine (tlsAlloc ha hn).bind fun p => FTTriple.ex fun b => FTTriple.lift fun hp => ?_
    subst hp
    refine (((tlsAllocs rest fun x hx => h x (List.mem_cons_of_mem _ hx)).frameL
      (R := tlsInst b bs a)).pre fun _ h => sep_emp.mpr h).bind fun ids => ?_
    refine FTTriple.ret' _ fun _ h => ?_
    have e : (#[(key, (some b : Option BlockId).getD 0)] ++ ids).toList = (key, b) :: ids.toList := by
      simp
    show tlsOwn _ (#[(key, (some b : Option BlockId).getD 0)] ++ ids).toList _
    rw [e]
    exact sep_lift.mpr ⟨rfl, h⟩

/-- **The thread end's frees** (`freeBlocks`) of whole instance blocks. -/
theorem freeBlocks : ∀ (bids : List BlockId) {R : FAssn},
    FTTriple (tlsDying bids ⋆ R) (Zig.freeBlocks bids) (fun _ => R)
  | [], R => by
    simp only [Zig.freeBlocks]
    exact FTTriple.ret' _ fun _ h => sep_emp.mp (sep_comm h)
  | b :: bids, R => by
    simp only [Zig.freeBlocks]
    refine FTTriple.pre (P := FAssn.ex fun A => FAssn.ex fun bs : Array Byte =>
      ⟪0 < bs.size⟫ ⋆ (gblk b A bs ⋆ (tlsDying bids ⋆ R))) ?_ fun _ h => ?_
    · refine FTTriple.ex fun A => FTTriple.ex fun bs => FTTriple.lift fun hn => ?_
      have hf := FTTotalTriple.ofSeq
        (FTotalTriple.free (p := ⟨some b, 0⟩) (A := A) (K := .global) (bs := bs) rfl rfl rfl hn
          (by decide))
        (ThreadLocal.free_of (Within.refl _).sepL (Within.refl _).sepR rfl rfl rfl)
      exact (hf.toPartial.frame).bind
        fun _ => (freeBlocks bids).pre fun _ h => sep_emp.mp (sep_comm h)
    · obtain ⟨A, h⟩ := sep_ex.mp (sep_assoc h)
      obtain ⟨bs, h⟩ := sep_ex.mp h
      exact ⟨A, bs, sep_assoc h⟩

end FTTriple

/-! ## The threads' parts -/

namespace FOwned

variable {own : ThreadId → Res} {rO : Res} {m : Mem}

/-- The registration of a thread start changes only a thread's record: the parts stay. -/
theorem setTls (ho : FOwned own rO m) (u : ThreadId) (ids : Array (BlockId × BlockId)) :
    FOwned own rO (m.setTls u ids) := by
  have hs : (m.setTls u ids).threads.size = m.threads.size := by simp
  exact ⟨by
      rw [hs]; obtain ⟨rT, h1, h2⟩ := ho.holds
      exact ⟨rT, h1, Holds.congrMem (m := m) rfl rfl h2⟩,
    fun v hv => ho.owns v (by rw [hs] at hv; exact hv),
    fun v hv => ho.outside v (by rw [hs] at hv; exact hv), by rw [hs]; exact ho.csize, ho.conc,
    ho.noCur⟩

/-- **One thread owns `r`**: in a memory with one thread and no recorded access, any resource it
holds next to `rO` is thread `0`'s part (`main`'s globals at program start, `initRes_holds`).
Neither holds the running thread's token (`FOwned.noCur`). -/
theorem one {r : Res} (hh : Holds m r rO) (h1 : m.threads.size = 1) (hc : m.clocks.size = 1)
    (hf : m.footprint = #[]) (hw : ShapesWF (shapes m)) (hl : m.LiveLayout) (hmc : m.MsgCov)
    (hnr : r.NoCur) (hnO : rO.NoCur) :
    FOwned (upd (fun _ => rnil) 0 r) rO m where
  noCur := ⟨fun u => by
    by_cases e : u = 0
    · subst e; rw [upd_self]; exact hnr
    · rw [upd_ne _ _ e]; exact fun _ => rfl, hnO⟩
  holds := by
    refine ⟨r, ?_, hh⟩
    rw [h1]
    refine ⟨r, rnil, FHeap.disjoint_empty _, ?_, by simp [partOf], ⟨rfl, rfl, rfl⟩⟩
    rw [res_eta r]; simp [FHeap.union_empty, Know.union_none, Ghost.add_unit]
  owns _ _ e he := by rw [hf] at he; simp at he
  outside u hu := by
    rw [h1] at hu; rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact ⟨rfl, rfl, rfl⟩
  csize := by rw [hc, h1]
  conc := ⟨hw, hl, hmc⟩

end FOwned

end Full

/-! ## Steps of a thread with `threadlocal` globals -/

namespace Conc
namespace Proto

open Full

variable {Tgt γ α β : Type} {P : Proto Tgt γ} {t : ThreadId} {G : ThreadId → γ} {m : Mem}
  {n : Nat} {own : ThreadId → Res} {rO : Res}

/-- A `MemM` step is read only at the memory it runs in. -/
theorem WP.liftMem_congr {x y : MemM α} {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
    (h : x.run m = y.run m) (hy : P.WP t (ConcM.liftMem y : ConcM Tgt α) Q G m n) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n := by
  unfold WP at hy ⊢
  show P.Safe t Q m.threads.size G (.leaf (x.run m))
  rw [h]; exact hy

/-- **A step of thread `t` followed by more of the same `MemM` step** (`x >>= f`): `x` by its thread
triple on `t`'s part, then `f` from the memory and the part after `x`. -/
theorem WP.liftMem_fowned_bind {x : MemM β} {f : β → MemM α} {Pa : FAssn} {Qa : β → FAssn}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop} (ht : FTTriple Pa x Qa) (ho : FOwned own rO m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' r', FOwned (upd own t r') rO m' → Qa a r' → m'.current = t →
      m'.threads = m.threads → P.WP t (ConcM.liftMem (f a) : ConcM Tgt α) Q G m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t (ConcM.liftMem (x >>= f) : ConcM Tgt α) Q G m n := by
  rw [liftMem_bind]
  exact WP.bind (WP.liftMem_fowned ht ho hc htl hp (fun a m' r' _ ho' hq hc' ht' =>
    h a m' r' ho' hq hc' ht') hret)

/-- A first step that, in the current memory, returns `v` and changes nothing. -/
theorem WP.liftMem_bind_pure {x : MemM β} {v : β} {f : β → MemM α}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop} (hx : x.run m = pure (v, m))
    (h : P.WP t (ConcM.liftMem (f v) : ConcM Tgt α) Q G m n) :
    P.WP t (ConcM.liftMem (x >>= f) : ConcM Tgt α) Q G m n :=
  WP.liftMem_congr (by rw [StateT.run_bind, hx]; rfl) h

/-- **`tlsPtr` in a step of generated code**: the current thread's instance, from its record. -/
theorem WP.liftMem_tlsPtr_bind {key b : BlockId} {f : Ptr → MemM α}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop} (hk : m.tlsInstance m.current key = some b)
    (h : P.WP t (ConcM.liftMem (f ⟨some b, 0⟩) : ConcM Tgt α) Q G m n) :
    P.WP t (ConcM.liftMem (tlsPtr key >>= f) : ConcM Tgt α) Q G m n :=
  WP.liftMem_bind_pure (tlsPtr_run hk) h

/-- **A thread start** (`tlsEnter inits`) of thread `t` with the part `R`: afterwards the part also
holds the new instances `ids` (`tlsOwn`), and `t`'s record lists them. -/
theorem WP.liftMem_tlsEnter_fowned {inits : List (BlockId × Array Byte × Nat)} {R : FAssn}
    {Q : Unit → (ThreadId → γ) → Mem → Nat → Prop}
    (hinit : ∀ x ∈ inits, 0 < x.2.2 ∧ 0 < x.2.1.size) (ho : FOwned own rO m) (hc : m.current = t)
    (htl : t < m.threads.size) (hp : R (own t))
    (h : ∀ (ids : Array (BlockId × BlockId)) (m₁ : Mem) (r' : Res), FOwned (upd own t r') rO (m₁.setTls t ids) →
      (R ⋆ tlsOwn inits ids.toList) r' → m₁.current = t → m₁.threads = m.threads →
      Q () G (m₁.setTls t ids) n)
    (hpart : P.Partial := by first | exact .inl rfl | exact .inr rfl | assumption) :
    P.WP t (ConcM.liftMem (tlsEnter inits) : ConcM Tgt Unit) Q G m n := by
  unfold tlsEnter
  rw [liftMem_bind]
  refine WP.bind (WP.liftMem_fowned ((FTTriple.tlsAllocs inits hinit).frameL (R := R)
    |>.pre fun _ h => Full.sep_emp.mpr h) ho hc htl hp (fun ids m₁ r' _ ho₁ hq hc₁ ht₁ => ?_)
    (.inl hpart))
  refine WP.liftMem_setTls ?_
  rw [hc₁]
  exact h ids m₁ r' (ho₁.setTls t ids) hq hc₁ ht₁

/-- **A thread end** (`tlsExit`) of thread `t` whose part holds the instance blocks that its
record lists (`tlsDying`) next to `R`: afterwards the part is `R`. -/
theorem WP.liftMem_tlsExit_fowned {R : FAssn} {Q : Unit → (ThreadId → γ) → Mem → Nat → Prop}
    (ho : FOwned own rO m) (hc : m.current = t) (htl : t < m.threads.size)
    (hp : (tlsDying ((m.tlsOf t).toList.map (·.2)) ⋆ R) (own t))
    (h : ∀ m' r', FOwned (upd own t r') rO m' → R r' → m'.current = t → m'.threads = m.threads →
      Q () G m' n)
    (hpart : P.Partial := by first | exact .inl rfl | exact .inr rfl | assumption) :
    P.WP t (ConcM.liftMem tlsExit : ConcM Tgt Unit) Q G m n := by
  refine WP.liftMem_congr (y := Zig.freeBlocks ((m.tlsOf t).toList.map (·.2)))
    (by simp only [tlsExit, StateT.run_bind, StateT.run_get, pure_bind, hc]) ?_
  exact WP.liftMem_fowned (FTTriple.freeBlocks _) ho hc htl hp (fun _ m' r' _ ho' hq hc' ht' =>
    h m' r' ho' hq hc' ht') (.inl hpart)

/-! ### Errors of the thread-local steps (audit soundness-2026-10-14 S4)

Thread entry and exit and the instance pointer throw only `.illegal` or `.stackOverflow`, errors
at which the native program stops (`Error.nativeStops`), so a partial-correctness proof meets their
error premise with `ErrOk.of_run`. -/

theorem tlsPtr_native {key : BlockId} :
    ∀ e, ((tlsPtr key).run m).run = some (.error e) → e.nativeStops := by
  unfold tlsPtr
  refine MemM.native_bind MemM.native_get fun _ _ _ => ?_
  split
  · exact MemM.native_pure
  · exact MemM.native_throw rfl

theorem tlsAllocs_native : ∀ {inits : List (BlockId × Array Byte × Nat)} {m : Mem},
    ∀ e, ((tlsAllocs inits).run m).run = some (.error e) → e.nativeStops
  | [], _ => MemM.native_pure
  | (_, _, _) :: _, _ => by
    unfold tlsAllocs tlsAlloc
    exact MemM.native_bind (MemM.native_bind alloc_native fun _ _ _ =>
      MemM.native_bind storeBytes_native fun _ _ _ => MemM.native_pure) fun _ _ _ =>
      MemM.native_bind tlsAllocs_native fun _ _ _ => MemM.native_pure

theorem tlsEnter_native {inits : List (BlockId × Array Byte × Nat)} :
    ∀ e, ((tlsEnter inits).run m).run = some (.error e) → e.nativeStops :=
  MemM.native_bind tlsAllocs_native fun _ _ _ => MemM.native_modify

theorem freeBlocks_native : ∀ {bs : List BlockId} {m : Mem},
    ∀ e, ((freeBlocks bs).run m).run = some (.error e) → e.nativeStops
  | [], _ => MemM.native_pure
  | _ :: _, _ => by
    unfold freeBlocks
    exact MemM.native_bind free_native fun _ _ _ => freeBlocks_native

theorem tlsExit_native : ∀ e, ((tlsExit).run m).run = some (.error e) → e.nativeStops :=
  MemM.native_bind MemM.native_get fun _ _ _ => freeBlocks_native

/-- A load through a pointer into a dead block throws `.illegal` before it reads anything. -/
theorem load_dead_native {T : Type} [Enc T] {p : Ptr} {b : BlockId} {a : Nat}
    (hd : m.Dead b) (hp : p.block = some b) :
    ∀ e, ((load T a p).run m).run = some (.error e) → e.nativeStops :=
  load_native_of_read fun _ _ hl => by
    obtain ⟨b', blk, o, hacc, -, -, -⟩ := loadBytes_ok hl
    obtain ⟨hpb, hblk, hl, -⟩ := access_eq hacc
    obtain ⟨blk', hb', hl'⟩ := hd
    rw [hp, Option.some.injEq] at hpb
    subst hpb
    rw [hb', Option.some.injEq] at hblk
    subst hblk
    rw [hl'] at hl
    cases hl

end Proto
end Conc

end Zig
