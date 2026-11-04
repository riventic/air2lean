import ZigLean.Sep.Full.Word
import ZigLean.Sep.Full.ThreadFacts
import ZigLean.Conc.Share

/-!
# A thread's plain steps in a protocol with a lock

Plain steps that every protocol with a lock (`FLock.Fits`, `ZigLean/Sep/Full/Lock.lean`) has, stated
once for every protocol, lock and primitive; a protocol discharges only its own obligations.

- **A read of read-shared bytes of the protocol's rest** (`Fits.wp_readRest`: the `io` prefix of a
  program's shared object, which every thread reads and no thread owns): the bytes are in the
  rest (`hrest`), the region is read-shared (`hsh`, `hcov`: no race, `ReadShared.noRace_read`),
  and the protocol's `U` is kept by the read's record (`hrec`). The lock's invariant is kept by
  `Inv.recordX`.
- **A read by the only thread that has not left the lock** (`Fits.wp_readAll`: a whole struct
  with the lock's word and the counter it protects, read after every other thread finished with
  the lock): the bytes may lie in the protocol's rest, the word's cells and the free lock's
  resource. The lock's invariant is kept by `Inv.recordAll`.
- **A step that redistributes the holder's resource** (`Fits.wp_holdParts`): a thread triple on
  the caller's part together with the protected resource. Its separating post gives a new caller
  part and protected resource, whose complete sum is the triple's post-resource, including
  knowledge and ghost state. The protocol supplies its new ghost value and pure invariant facts;
  its rest's move (`hU`) gets the post's facts on the new split (a resource that moved into the
  caller's part, a value read).
- **A step of the lock's holder on the lock's resource** (`Fits.wp_hold`: a load or a store of the
  counter that the lock protects), a thread triple on the held resource: the holder's part is
  framed, its new ghost value `g'` (the rule's ghost argument: the transition of its place, ledger
  #52) keeps the lock's resource (`hR`) and the protocol's `U` (`hU`). The lock's invariant is
  kept by `Inv.wp_liftMem`.

`fsym`'s `WP` backend applies them as caller rules: a read with the protocol's obligations as
arguments (`fsym [hF.wp_readRest …]`, `fsym [hF.wp_readAll …]`, as the lock's contract rules `MutexImpl.lock_wp`), the
holder's step with the holder's next place (`fsym [hF.wp_hold (g' := gH x'), …]`, one term per
place a walk reaches): the walk takes the segment's precondition from `hpa`, infers its post,
proves `hR` from the post and `hU` by the protocol's lemmas given as terms
(`docs/proof-automation.md` §WP).
-/

namespace Zig
namespace Full
namespace FLock

open FAssn Conc Proto

variable {γ : Type} {L : FLock γ} {K : FPrim γ} {Tgt : Type} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-- **A plain load from invariant rest by a race-free reader.** The bytes occur once in `rX`;
the caller's admission need only justify its own `NoRace` fact. In particular, no prior write
has to precede an unrelated live thread. The exact load run and its read record preserve the
same full-state lock invariant and resource, without a protocol/implementation contract. -/
theorem Inv.loadRest {T : Type} [Enc T] {p : Ptr} {b : BlockId} {a : Nat} {v : T}
    {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} (hi : L.Inv G rX m)
    (hpb : p.block = some b) (hn : 0 < Enc.size T)
    (hrest : ∃ r A S K' bs, up (bytesAt p A S K' bs) r ∧
      (∀ l fc, r.heap l = some fc → rX.heap l = some fc) ∧ bs.size = Enc.size T ∧
      Enc.decode bs = pure v ∧ (A + p.off.toNat) % a = 0 ∧ K' ≠ .constGlobal)
    (hc : m.current = t) (hg : L.ph (G t) ≠ .gone)
    (hread : NoRace m b p.off.toNat (Enc.size T) .read) :
    (load T a p).run m = pure (v, m.recordAt b p.off.toNat (Enc.size T) .read) ∧
      L.Inv G rX (m.recordAt b p.off.toNat (Enc.size T) .read) := by
  obtain ⟨ht, _⟩ := hi.ht hg
  obtain ⟨r, A, S, K', bs, hr, hsub, hbs, hdec, ha, hK⟩ := hrest
  obtain ⟨rL, ho, hin⟩ := hi.restIn
  obtain ⟨hrun, hb, hcov⟩ :=
    ho.loadRun hpb hn hr (fun l fc h => hin l fc (hsub l fc h)) hbs hdec ha hK hread
  refine ⟨hrun, hi.recordX (k := .read) (by decide) hc ht hb hn fun x h1 h2 => ?_⟩
  obtain ⟨fc', hfc'⟩ := Option.ne_none_iff_exists'.mp (hcov x h1 h2)
  rw [hsub _ _ hfc']; simp

/-- **A plain load by the only thread that has not left the lock** (every other thread is
`gone`): the bytes are in the lock's complete rest (the protocol's rest `rX`, the word's cells and
the free lock's resource `rL`), so the read may span the word and what the lock protects. The
caller shows the bytes for every `rL` the invariant allows (with `R` when the lock is free,
`rnil` when it is held, apart from the word and from `rX`), and that the read does not race. -/
theorem Inv.loadAll {T : Type} [Enc T] {p : Ptr} {b : BlockId} {a : Nat} {v : T}
    {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} (hi : L.Inv G rX m)
    (hpb : p.block = some b) (hn : 0 < Enc.size T)
    (hrest : ∀ rL, (L.Free G → L.R G rL) → (¬ L.Free G → rL = rnil) → L.Off rL.heap.erase →
      FHeap.Disjoint rL.heap rX.heap → ∃ r A S K' bs, up (bytesAt p A S K' bs) r ∧
      (∀ l fc, r.heap l = some fc → (rsum (L.wordR m) (rsum rL rX)).heap l = some fc) ∧
      bs.size = Enc.size T ∧ Enc.decode bs = pure v ∧ (A + p.off.toNat) % a = 0 ∧
      K' ≠ .constGlobal)
    (hc : m.current = t) (hg : L.ph (G t) ≠ .gone)
    (hsole : ∀ u < m.threads.size, u ≠ t → L.ph (G u) = .gone)
    (hread : NoRace m b p.off.toNat (Enc.size T) .read) :
    (load T a p).run m = pure (v, m.recordAt b p.off.toNat (Enc.size T) .read) ∧
      L.Inv G rX (m.recordAt b p.off.toNat (Enc.size T) .read) := by
  obtain ⟨ht, _⟩ := hi.ht hg
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  obtain ⟨r, A, S, K', bs, hr, hsub, hbs, hdec, ha, hK⟩ :=
    hrest rL (fun h => (hF h).1) hnF hLoff hLX
  obtain ⟨hrun, hb, hcov⟩ := ho.loadRun hpb hn hr hsub hbs hdec ha hK hread
  refine ⟨hrun, hi.recordAll hc ht hb hsole fun u hu x h1 h2 => ho.part_off hu ?_⟩
  obtain ⟨fc', hfc'⟩ := Option.ne_none_iff_exists'.mp (hcov x h1 h2)
  rw [hsub _ _ hfc']; simp

/-- Reads by other admitted readers need no clock ordering. Every conflicting write
must precede this reader through the publication clock or through AllLe. -/
theorem _root_.Zig.Full.noRace_read_of_publication {m : Mem} {b o n : Nat}
    {Rg : FootprintEntry → Prop} {c : VClock} (ht : m.current < m.threads.size)
    (hcov : Conc.Covers Rg b o n)
    (hpub : ∀ e ∈ m.footprint, Rg e → e.kind = .read ∨
      VClock.le e.clock c = true ∨ AllLe m e.clock)
    (ha : VClock.le c (m.clocks[m.current]!) = true) : NoRace m b o n .read := by
  refine noRace_of_pos fun e he hb hn h1 h2 => ?_
  rcases hpub e he (hcov e hb hn h1 h2) with hr | hp | hall
  · exact .inr (by rw [hr]; rfl)
  · exact .inl (VClock.le_trans hp ha)
  · exact .inl (hall _ ht)

/-- A plain load by a thread `t` that is not `gone`, whose run (`hload`) reads `v`, records the
read and keeps the lock's invariant, and whose record keeps `U` (`hrec`): the read rules' common
step. -/
theorem Fits.wp_loadWith (hF : L.Fits K P U ok) {T : Type} [Enc T] {p : Ptr} {b : BlockId}
    {o n a : Nat} {v : T} {G G' : ThreadId → γ} {t : ThreadId} {m : Mem} {d : Nat}
    {Q : T → (ThreadId → γ) → Mem → Nat → Prop}
    (hload : ∀ rX, L.Inv G' rX m → U G' rX m → t < m.threads.size →
      (load T a p).run m = pure (v, m.recordAt b o n .read) ∧
        L.Inv G' rX (m.recordAt b o n .read))
    (hrec : ∀ rX, U G' rX m → t < m.threads.size → joinedB m t = false →
      m.clocks.size = m.threads.size → U G' rX (m.recordAt b o n .read))
    (hi : P.inv G' m) (hc : m.current = t) (hg : L.ph (G' t) ≠ .gone)
    (h : ∀ m', m'.current = t → m'.threads = m.threads → P.inv G' m' → Q v G m' d) :
    P.WP t (ConcM.liftMem (load T a p) : ConcM Tgt T) Q G m d := by
  obtain ⟨rX, hiL, hU⟩ := (hF.inv G' m).mp hi
  obtain ⟨ht, hjt⟩ := hiL.ht hg
  obtain ⟨hrun, hiL'⟩ := hload rX hiL hU ht
  refine WP.liftMem (fun e he => (MemM.noErr_of_run hrun e he).elim) (fun v' m' hr' => ?_)
    fun hnone => by rw [hrun] at hnone; cases hnone
  rw [hrun] at hr'
  simp only [pure, ExceptT.pure, ExceptT.mk, ExceptT.run, Option.some.injEq, Except.ok.injEq,
    Prod.mk.injEq] at hr'
  obtain ⟨rfl, rfl⟩ := hr'
  exact ⟨rfl, h _ hc rfl ((hF.inv G' _).mpr ⟨rX, hiL', hrec rX hU ht hjt hiL.w.csize⟩)⟩

/-- The reader's admission justifies its projection, actual NoRace and preservation
of U by this read record. It does not require an unrelated live reader's clock. -/
theorem Fits.wp_readRestOf (hF : L.Fits K P U ok) {T : Type} [Enc T] {p : Ptr} {b : BlockId}
    {a : Nat} {v : T} {A : ThreadId → γ → Prop} (hpb : p.block = some b)
    (hn : 0 < Enc.size T)
    (hrest : ∀ G rX m u, U G rX m → A u (G u) → ∃ r B S K' bs, up (bytesAt p B S K' bs) r ∧
      (∀ l fc, r.heap l = some fc → rX.heap l = some fc) ∧ bs.size = Enc.size T ∧
      Enc.decode bs = pure v ∧ (B + p.off.toNat) % a = 0 ∧ K' ≠ .constGlobal)
    (hread : ∀ G rX m u, U G rX m → A u (G u) → m.current = u →
      u < m.threads.size → NoRace m b p.off.toNat (Enc.size T) .read)
    (hrec : ∀ G rX m u, U G rX m → A u (G u) → m.current = u →
      u < m.threads.size → joinedB m u = false → m.clocks.size = m.threads.size →
      U G rX (m.recordAt b p.off.toNat (Enc.size T) .read))
    {G G' : ThreadId → γ} {t : ThreadId} {m : Mem} {d : Nat}
    {Q : T → (ThreadId → γ) → Mem → Nat → Prop}
    (hi : P.inv G' m) (hc : m.current = t) (hg : L.ph (G' t) ≠ .gone)
    (ha : A t (G' t))
    (h : ∀ m', m'.current = t → m'.threads = m.threads → P.inv G' m' → Q v G m' d) :
    P.WP t (ConcM.liftMem (load T a p) : ConcM Tgt T) Q G m d := by
  exact hF.wp_loadWith (fun rX hiL hU ht => hiL.loadRest hpb hn (hrest G' rX m t hU ha) hc hg
    (hread G' rX m t hU ha hc ht)) (fun rX hU => hrec G' rX m t hU ha hc) hi hc hg h

/-- **A read by the only thread that has not left the lock** (`Inv.loadAll`): the bytes are in the
lock's complete rest, the protocol's rest with the word's cells and the free lock's resource, so
the read may span the word and what the lock protects (a whole struct read after every other
thread finished with the lock). The reader's admission `A` gives that every other thread is `gone`
(`hsole`), the bytes for every lock resource the invariant allows (`hrest`), no race (`hread`) and
`U` after the read's record (`hrec`). -/
theorem Fits.wp_readAll (hF : L.Fits K P U ok) {T : Type} [Enc T] {p : Ptr} {b : BlockId}
    {a : Nat} {v : T} {A : ThreadId → γ → Prop} (hpb : p.block = some b)
    (hn : 0 < Enc.size T)
    (hsole : ∀ G rX m u, U G rX m → A u (G u) → ∀ w < m.threads.size, w ≠ u → L.ph (G w) = .gone)
    (hrest : ∀ G rX m u rL, L.Inv G rX m → U G rX m → A u (G u) → (L.Free G → L.R G rL) →
      (¬ L.Free G → rL = rnil) → L.Off rL.heap.erase → FHeap.Disjoint rL.heap rX.heap →
      ∃ r B S K' bs, up (bytesAt p B S K' bs) r ∧
      (∀ l fc, r.heap l = some fc → (rsum (L.wordR m) (rsum rL rX)).heap l = some fc) ∧
      bs.size = Enc.size T ∧ Enc.decode bs = pure v ∧ (B + p.off.toNat) % a = 0 ∧
      K' ≠ .constGlobal)
    (hread : ∀ G rX m u, U G rX m → A u (G u) → m.current = u →
      u < m.threads.size → NoRace m b p.off.toNat (Enc.size T) .read)
    (hrec : ∀ G rX m u, U G rX m → A u (G u) → m.current = u →
      u < m.threads.size → joinedB m u = false → m.clocks.size = m.threads.size →
      U G rX (m.recordAt b p.off.toNat (Enc.size T) .read))
    {G G' : ThreadId → γ} {t : ThreadId} {m : Mem} {d : Nat}
    {Q : T → (ThreadId → γ) → Mem → Nat → Prop}
    (hi : P.inv G' m) (hc : m.current = t) (hg : L.ph (G' t) ≠ .gone)
    (ha : A t (G' t))
    (h : ∀ m', m'.current = t → m'.threads = m.threads → P.inv G' m' → Q v G m' d) :
    P.WP t (ConcM.liftMem (load T a p) : ConcM Tgt T) Q G m d := by
  exact hF.wp_loadWith (fun rX hiL hU ht => hiL.loadAll hpb hn (hrest G' rX m t · hiL hU ha) hc
    hg (hsole G' rX m t hU ha) (hread G' rX m t hU ha hc ht))
    (fun rX hU => hrec G' rX m t hU ha hc) hi hc hg h

/-- **A read of read-shared bytes of the protocol's rest** (module doc) by a live thread `t`:
`T`'s `Enc.size T` bytes at `p` (block `b`) are bytes `bs` of the rest that decode to `v`, at an
address aligned for the load; the region `Rg` that covers them is read-shared, and a read's
record keeps `U`. The invariant's ghost values `G'` stay. -/
theorem Fits.wp_readRest (hF : L.Fits K P U ok) {T : Type} [Enc T] {p : Ptr} {b : BlockId}
    {a : Nat} {v : T} {Rg : FootprintEntry → Prop} (hpb : p.block = some b)
    (hn : 0 < Enc.size T)
    (hrest : ∀ G rX m, U G rX m → ∃ r A S K' bs, up (bytesAt p A S K' bs) r ∧
      (∀ l fc, r.heap l = some fc → rX.heap l = some fc) ∧ bs.size = Enc.size T ∧
      Enc.decode bs = pure v ∧ (A + p.off.toNat) % a = 0 ∧ K' ≠ .constGlobal)
    (hsh : ∀ G rX m, U G rX m → ReadShared Rg m)
    (hcov : Conc.Covers Rg b p.off.toNat (Enc.size T))
    (hrec : ∀ G rX m, U G rX m → m.current < m.threads.size → joinedB m m.current = false →
      m.clocks.size = m.threads.size → U G rX (m.recordAt b p.off.toNat (Enc.size T) .read))
    {G G' : ThreadId → γ} {t : ThreadId} {m : Mem} {d : Nat}
    {Q : T → (ThreadId → γ) → Mem → Nat → Prop}
    (hi : P.inv G' m) (hc : m.current = t) (hg : L.ph (G' t) ≠ .gone)
    (h : ∀ m', m'.current = t → m'.threads = m.threads → P.inv G' m' → Q v G m' d) :
    P.WP t (ConcM.liftMem (load T a p) : ConcM Tgt T) Q G m d := by
  exact hF.wp_readRestOf (A := fun _ _ => True) hpb hn
    (fun G rX m _ hU _ => hrest G rX m hU)
    (fun G rX m u hU _ hc ht => (hsh G rX m hU).noRace_read (hc ▸ ht) hcov)
    (fun G rX m u hU _ hc ht hj hcs => hrec G rX m hU (hc ▸ ht) (hc ▸ hj) hcs)
    hi hc hg trivial h

/-- A step that keeps the protocol's rest with the lock's word keeps the rest alone (for a
protocol's `U` step under `Fits.wp_hold`'s `hU`, which gets the step with the word). -/
theorem _root_.Zig.FStepIn.restX {rX : Res} {m m' : Mem}
    (hs : FStepIn (rsum (L.wordR m) rX).heap.erase m m') : FStepIn rX.heap.erase m m' :=
  hs.weaken fun l hl => by
    simp only [FHeap.erase, rsum, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
      Option.or_eq_none_iff, not_and] at hl ⊢
    exact fun _ => hl

/-- **A holder step with a new split of the complete resource.** The thread triple operates on
the caller's part and held resource together; its separating post supplies their new split.
The two parts reconstruct the complete post-resource of the existing thread rule, without
assuming that the caller part stays fixed. The new ghost value realizes that split and re-establishes the
protected assertion. The rest's move (`hU`) gets the post's facts `Qp a rp` and `Qh a rh` on the
new split. The ordinary `wp_hold` rule is the fixed-caller instance below. -/
theorem Fits.wp_holdParts (hF : L.Fits K P U ok) {α : Type} {x : MemM α}
    {G G' : ThreadId → γ} {Pa : FAssn} {Qp Qh : α → FAssn}
    {t : ThreadId} {m : Mem} {d : Nat} {g' : Res → Res → γ}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
    (hi : P.inv G' m) (hc : m.current = t) (hh : L.ph (G' t) = .holds)
    (htt : FTTriple Pa x (fun a => Qp a ⋆ Qh a))
    (hpa : ∀ r, L.R G' r → FHeap.Disjoint (L.part (G' t)).heap r.heap →
      Pa (rsum (L.part (G' t)) r))
    (hR : ∀ a rp rh, Qp a rp → Qh a rh → L.R (upd G' t (g' rp rh)) rh)
    (hg' : ∀ a rp rh, Qp a rp → Qh a rh →
      L.ph (g' rp rh) = .holds ∧ L.part (g' rp rh) = rp ∧ L.held (g' rp rh) = rh)
    (hU : ∀ a rX m' rp rh, Qp a rp → Qh a rh → L.Inv G' rX m → U G' rX m →
      joinedB m t = false → FStepIn (rsum (L.wordR m) rX).heap.erase m m' →
      m'.threads = m.threads → L.Inv (upd G' t (g' rp rh)) rX m' →
      U (upd G' t (g' rp rh)) rX m')
    (h : ∀ a m' rp rh, m'.current = t → m'.threads = m.threads → Qp a rp → Qh a rh →
      P.inv (upd G' t (g' rp rh)) m' → Q a G m' d)
    (hpart : P.Partial := by
      first
        | exact .inl rfl
        | exact .inr rfl
        | assumption) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m d := by
  obtain ⟨rX, hiL, hU₀⟩ := (hF.inv G' m).mp hi
  obtain ⟨ht, hjt⟩ := hiL.ht (by rw [hh]; decide)
  refine hiL.wp_liftMem hc ht hjt htt (hpa _ (hiL.res t hh) (hiL.pdisj t))
    (fun a m' r' _ hq hs hc' hk => ?_) (.inl hpart)
  obtain ⟨rp, rh, hd, rfl, hqp, hqh⟩ := hq
  obtain ⟨hph, hpt, hhd⟩ := hg' a rp rh hqp hqh
  have hl := hk (g' rp rh) (by rw [hph, hh]) (by rw [hpt, hhd])
    (by rw [hpt, hhd]; exact hd) (fun h => absurd hph h) (fun h => absurd hh h)
    (fun _ => by rw [hhd]; exact hR a rp rh hqp hqh)
  exact h a m' rp rh hc' hs.threads hqp hqh
    ((hF.inv _ _).mpr ⟨rX, hl, hU a rX m' rp rh hqp hqh hiL hU₀ hjt hs hs.threads hl⟩)

/-- **A step of the lock's holder `t` on the lock's resource** (module doc): a thread triple from
what the resource `L.R G'` gives (`hpa`; the holder's part framed); after it, the holder's new
ghost value `g' r` (holding, the same part, the new resource `r`) gives the resource (`hR`) and
keeps `U` (`hU`). (The premises in the order `fsym` proves them: `hR`, which the post of the
step decides, before `hg'` and `hU`; ledger #70.) -/
theorem Fits.wp_hold (hF : L.Fits K P U ok) {α : Type} {x : MemM α} {G G' : ThreadId → γ}
    {Pa : FAssn} {Qa : α → FAssn} {t : ThreadId} {m : Mem} {d : Nat} {g' : Res → γ}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
    (hi : P.inv G' m) (hc : m.current = t) (hh : L.ph (G' t) = .holds)
    (htt : FTTriple Pa x Qa) (hpa : ∀ r, L.R G' r → Pa r)
    (hR : ∀ a r, Qa a r → L.R (upd G' t (g' r)) r)
    (hg' : ∀ r, L.ph (g' r) = .holds ∧ L.part (g' r) = L.part (G' t) ∧
      L.held (g' r) = r)
    (hU : ∀ rX m' r, L.Inv G' rX m → U G' rX m → joinedB m t = false →
      FStepIn (rsum (L.wordR m) rX).heap.erase m m' → m'.threads = m.threads →
      L.Inv (upd G' t (g' r)) rX m' → U (upd G' t (g' r)) rX m')
    (h : ∀ a m' r, m'.current = t → m'.threads = m.threads → Qa a r →
      P.inv (upd G' t (g' r)) m' → Q a G m' d)
    (hpart : P.Partial := by
      first
        | exact .inl rfl
        | exact .inr rfl
        | assumption) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m d := by
  refine hF.wp_holdParts (Qp := fun _ r => r = L.part (G' t)) (Qh := Qa)
    (g' := fun _ rh => g' rh) hi hc hh (htt.frameL (R := fun r => r = L.part (G' t)))
    (fun r hr hd => ⟨_, _, hd, rfl, rfl, hpa r hr⟩)
    (fun a _ rh _ hq => hR a rh hq) (fun a rp rh hp _ => ?_)
    (fun _ rX m' _ rh _ _ => hU rX m' rh) (fun a m' _ rh hc' ht' _ hq => h a m' rh hc' ht' hq)
    hpart
  subst rp
  exact hg' rh

end FLock
end Full
end Zig
