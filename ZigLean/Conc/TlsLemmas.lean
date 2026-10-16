import ZigLean.Conc.Csl
import ZigLean.Conc.Base.Tls

/-!
# Thread-local storage: identity, initialization, lifetime

Lemmas about `ZigLean/Mem/Tls.lean` and the rules a proof over all schedules uses for a
spawned thread with thread-local storage (`ConcM.tlsThread`). A proof-only module: it imports
`ZigLean.Mem.Lemmas`, so it stays out of the `ZigLean` umbrella.

- **No aliasing** (`TlsWF`, `TlsWF.no_alias`): every registered instance is a block of the
  memory, and no block is the instance of two threads. So the same key (the same `threadlocal`
  name) in two different threads gives two different blocks. `TlsWF` holds at program start
  (`TlsWF.mainTls`) and every memory step keeps it: a step that keeps the thread records and
  does not remove blocks (`TlsWF.of_threads`: every load, store, allocation, free and atomic
  op), a spawn (`TlsWF.fork`), a join (`TlsWF.join`) and a thread start (`TlsWF.tlsEnter`).
- **Initialization** (`tlsEnter_init`): after a thread start, each instance of the thread is a
  new, live block holding exactly the initial bytes of its global, whatever the other threads
  did to their instances.
- **Lifetime** (`tlsExit_dead`): after a thread end, every instance of the thread is dead, so
  any later access through a pointer to it throws `.illegal` (`load_dead`).
- **Rules for proofs** (`TTripleIn`): a thread triple that may also read the thread records
  (which every thread triple keeps): `tlsPtr` is a step that reads only them (`TTripleIn.tlsPtr`).
  `WP.liftMem_ownedIn` uses such a triple in a thread, `WP.liftM_tlsPtr` is the step in a
  concurrent body, and `Owned.setTls` and `liftMem_bind`
  handle the registration of a thread start.
-/

namespace Zig

open Assn Conc Conc.Proto

/-! ## Rules for proofs -/

/-- Thread `t`'s instance of `key` in the thread records `R` (`Mem.tlsInstance` reads only
them). -/
def recInstance (R : Array ThreadRec) (t : ThreadId) (key : BlockId) : Option BlockId :=
  (((((R[t]?).map (·.tls)).getD #[]).find? (·.1 == key))).map (·.2)

theorem Mem.tlsInstance_eq (m : Mem) (t : ThreadId) (key : BlockId) :
    m.tlsInstance t key = recInstance m.threads t key := rfl

/-- A lifted pure step with a known result. -/
theorem TTriple.liftR_ok {α : Type} {r : Result α} {x : α} {P : Assn} (hr : r.run = some (.ok x)) :
    TTriple P (StateT.lift r : MemM α) (fun y => ⌜y = x⌝ ∗ P) :=
  TTriple.of_run fun m hP hF hd hm hp _ ho => by
    refine ⟨x, m, hP, ?_, hd, hm, sep_lift.mpr ⟨rfl, hp⟩, ho, StepIn.refl m _⟩
    rw [show r = pure x from hr]; rfl

/-- `TTriple` for a step that may read the thread records: run by thread `t` with the records
`R`. Every thread triple keeps both (`StepIn.current`, `StepIn.threads`), so a sequence of
them, with `tlsPtr` among them, has one `t` and one `R`. -/
def TTripleIn {α : Type} (t : ThreadId) (R : Array ThreadRec) (P : Assn) (c : MemM α)
    (Q : α → Assn) : Prop :=
  ∀ m hP hF, m.current = t → m.threads = R → Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP →
    m.current < m.clocks.size → m.Owns m.current hP →
    match (c.run m).run with
    | none => True
    | some (.error e) => e = .stackOverflow
    | some (.ok (v, m')) =>
      ∃ hQ, Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ Q v hQ ∧ m'.Owns m'.current hQ ∧
        StepIn hF m m'

namespace TTripleIn

variable {α β : Type} {t : ThreadId} {R : Array ThreadRec} {P P' : Assn} {Q Q' : α → Assn}
  {c : MemM α}

theorem of (h : TTriple P c Q) : TTripleIn t R P c Q :=
  fun m hP hF _ _ hd hm hp hc ho => h m hP hF hd hm hp hc ho

theorem conseq (ht : TTripleIn t R P c Q) (hp : ∀ h, P' h → P h) (hq : ∀ v h, Q v h → Q' v h) :
    TTripleIn t R P' c Q' := by
  intro m hP hF hct hR hd hm hp' hc ho
  have := ht m hP hF hct hR hd hm (hp _ hp') hc ho
  split at this
  · trivial
  · exact this
  · obtain ⟨hQ, a, b, c, d, e⟩ := this; exact ⟨hQ, a, b, hq _ _ c, d, e⟩

theorem bind {S : β → Assn} {f : α → MemM β} (hc : TTripleIn t R P c Q)
    (hf : ∀ v, TTripleIn t R (Q v) (f v) S) : TTripleIn t R P (c >>= f) S := by
  intro m hP hF hct hR hd hm hp hcl ho
  have h1 := hc m hP hF hct hR hd hm hp hcl ho
  simp only [StateT.run_bind, ExceptT.run_bind]
  revert h1
  cases (c.run m).run with
  | none => intro; trivial
  | some r =>
    cases r with
    | error e => intro h1; exact h1
    | ok r =>
      obtain ⟨v, m'⟩ := r
      rintro ⟨hQ, hd', hm', hq, ho', hs⟩
      have hcl' : m'.current < m'.clocks.size := by rw [hs.current, hs.size]; exact hcl
      have h2 := hf v m' hQ hF (hs.current.trans hct) (hs.threads.trans hR) hd' hm' hq hcl' ho'
      dsimp only [Bind.bind, Option.bind]
      split at h2
      · trivial
      · exact h2
      · obtain ⟨hS, a, b, c, d, hs'⟩ := h2
        exact ⟨hS, a, b, c, d, hs.trans hs'⟩

theorem lift {φ : Prop} (h : φ → TTripleIn t R P c Q) : TTripleIn t R (⌜φ⌝ ∗ P) c Q := by
  intro m hP hF hct hR hd hm hp hc ho
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact h hφ m hP hF hct hR hd hm hp hc ho

/-- A step whose post names its result `v`, then the rest. -/
theorem bind_eq {v : α} {P' : Assn} {f : α → MemM β} {S : β → Assn}
    (hc : TTripleIn t R P c (fun r => ⌜r = v⌝ ∗ P')) (hf : TTripleIn t R P' (f v) S) :
    TTripleIn t R P (c >>= f) S :=
  hc.bind fun _ => TTripleIn.lift fun hr => hr ▸ hf

theorem ret (v : α) : TTripleIn t R (Q v) (pure v : MemM α) Q := of (TTriple.ret v)

/-- `tlsPtr` reads only the thread records: the thread's own instance. -/
theorem tlsPtr {key b : BlockId} (hk : recInstance R t key = some b) :
    TTripleIn t R P (Zig.tlsPtr key) (fun r => ⌜r = ⟨some b, 0⟩⌝ ∗ P) := by
  intro m hP hF hct hR hd hm hp _ ho
  have hi : m.tlsInstance m.current key = some b := by
    rw [Mem.tlsInstance_eq, hR, hct]; exact hk
  rw [tlsPtr_run hi]
  exact ⟨hP, hd, hm, sep_lift.mpr ⟨rfl, hp⟩, ho, StepIn.refl m _⟩

end TTripleIn

/-- One new instance: the thread owns a new writable block with the initial bytes. -/
theorem TTriple.tlsAlloc {bs : Array Byte} {a : Nat} (ha : 0 < a) (hn : 0 < bs.size) :
    TTriple emp (tlsAlloc bs a) (fun p => Assn.ex fun A =>
      ⌜p.off = 0 ∧ A % a = 0⌝ ∗ bytesAt p A bs.size .global bs) := by
  unfold Zig.tlsAlloc
  refine (TTriple.alloc .global bs.size a ha).bind fun p =>
    TTriple.ex fun A => TTriple.lift fun ⟨h0, hA⟩ => ?_
  refine (TTriple.storeBytesAt (k := 0) (a := a) bs (by simp [Ptr.add]) hn (by simp)
    (by simp [h0, hA]) (by decide)).bind fun _ => ?_
  rw [writeBytes_all (by simp)]
  exact (TTriple.ret p).conseq (fun h hb => ⟨A, sep_lift.mpr ⟨⟨h0, hA⟩, hb⟩⟩) (fun _ _ h => h)

/-- The instances of a program with one `threadlocal` global. -/
theorem TTriple.tlsAllocs_one {key : BlockId} {bs : Array Byte} {a : Nat} (ha : 0 < a)
    (hn : 0 < bs.size) :
    TTriple emp (tlsAllocs [(key, bs, a)]) (fun ids => Assn.ex fun b => Assn.ex fun A =>
      ⌜ids = #[(key, b)] ∧ A % a = 0⌝ ∗ bytesAt ⟨some b, 0⟩ A bs.size .global bs) := by
  unfold tlsAllocs
  refine (TTriple.tlsAlloc ha hn).bind fun p => TTriple.ex fun A => TTriple.lift fun ⟨h0, hA⟩ => ?_
  simp only [tlsAllocs, pure_bind]
  refine (TTriple.ret _).conseq (fun h hb => ?_) (fun _ _ h => h)
  obtain ⟨b, hpb, -, -⟩ := id hb
  have hp : p = ⟨some b, 0⟩ := by cases p; simp_all
  subst hp
  exact ⟨b, A, sep_lift.mpr ⟨by simp [hA], hb⟩⟩

theorem tlsExit_run_one {m : Mem} {key b : BlockId} (h : m.tlsOf m.current = #[(key, b)]) :
    tlsExit.run m = (free ⟨some b, 0⟩ >>= fun _ => (pure () : MemM Unit)).run m := by
  simp [tlsExit, h, freeBlocks, StateT.run_bind, StateT.run_get]

/-- Thread end with one instance: the thread gives up its block. -/
theorem TTripleIn.tlsExit_one {t : ThreadId} {R : Array ThreadRec} {key b : BlockId} {A S : Nat}
    {K : BlockKind} {bs : Array Byte} {Q : Assn}
    (hR : ((R[t]?).map (·.tls)).getD #[] = #[(key, b)]) (hS : bs.size = S) (hpos : 0 < S)
    (hK : K ≠ .constGlobal := by decide) :
    TTripleIn t R (bytesAt ⟨some b, 0⟩ A S K bs ∗ Q) tlsExit (fun _ => Q) := by
  intro m hP hF hct hR' hd hm hp hc ho
  have hreg : m.tlsOf m.current = #[(key, b)] := by
    unfold Mem.tlsOf; rw [hR', hct]; exact hR
  rw [tlsExit_run_one hreg]
  have ht : TTriple (bytesAt ⟨some b, 0⟩ A S K bs ∗ Q)
      (free ⟨some b, 0⟩ >>= fun _ => (pure () : MemM Unit)) (fun _ => Q) :=
    ((TTriple.free hS rfl hpos hK).frame.conseq (fun _ h => h)
      fun _ _ h => sep_emp.mp (sep_comm h)).bind fun _ => TTriple.ret (Q := fun _ => Q) ()
  exact ht m hP hF hd hm hp hc ho

namespace Conc.Proto

variable {Tgt γ σ α : Type} {P : Proto Tgt γ} {t : ThreadId} {G : ThreadId → γ} {m : Mem}
  {n : Nat} {own : ThreadId → Heap}

/-- `WP.liftMem_owned` for a `TTripleIn`: a step of thread `t` with the thread records `R`. -/
theorem WP.liftMem_ownedIn {x : MemM α} {R : Array ThreadRec} {Pa : Assn} {Qa : α → Assn}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop} (ht : TTripleIn t R Pa x Qa) (ho : Owned own m)
    (hc : m.current = t) (hR : m.threads = R) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' hQ, (x.run m).run = some (.ok (a, m')) → Owned (upd own t hQ) m' → Qa a hQ →
      StepIn (m.heap.diff (own t)) m m' → Q a G m' n)
    (hpart : P.Partial := by
      first
        | exact .inl rfl
        | exact .inr rfl
        | assumption
        | exact .inr (by assumption)
        | exact .inl (by assumption)) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n := by
  obtain ⟨hm, hd⟩ := Heap.diff_split (ho.sub t)
  have hcs : m.current < m.clocks.size := by rw [hc, ho.csize]; exact htl
  have hx := ht m (own t) _ hc hR hd hm hp hcs (hc ▸ ho.owns t htl)
  refine WP.liftMem' (fun e he => ?_) fun a m' hr => ?_
  · rw [he] at hx; exact .inr hx
  · rw [hr] at hx
    obtain ⟨hQ, hd', hm', hq, ho', hs⟩ := hx
    have ho'' : m'.Owns t hQ := by rw [hs.current, hc] at ho'; exact ho'
    exact ⟨by rw [hs.threads], h a m' hQ hr (ho.step hc htl hs hm' hd' ho'') hq hs⟩

/-- `tlsPtr` in a concurrent body: the thread's own instance, no memory change. -/
theorem WP.liftM_tlsPtr {key b : BlockId} {s : σ} {Q : Ptr × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (hk : m.tlsInstance m.current key = some b) (h : Q (⟨some b, 0⟩, s) G m n) :
    P.WP t ((_root_.liftM (tlsPtr key) : CM Tgt σ Ptr).run s) Q G m n :=
  WP.liftM (fun e he => by rw [tlsPtr_run hk] at he; cases he) (fun a m' hr => by
    rw [tlsPtr_run hk] at hr
    simp only [pure, StateT.pure, ExceptT.run, ExceptT.pure, ExceptT.mk, Option.some.injEq,
      Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨rfl, h⟩) fun hn => by rw [tlsPtr_run hk] at hn; cases hn

/-- The registration of a thread start keeps the threads' parts. -/
theorem _root_.Zig.Owned.setTls {u : ThreadId} {ids : Array (BlockId × BlockId)} (ho : Owned own m) :
    Owned own (m.setTls u ids) :=
  ⟨ho.sub, ho.disj, fun v hv => ho.owns v (by simpa using hv), fun v hv => ho.outside v
    (by simpa using hv), by simpa using ho.csize⟩

end Conc.Proto

end Zig
