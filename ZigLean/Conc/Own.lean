import ZigLean.Conc.Clock
import ZigLean.Sep.Block

/-!
# Ownership in threads

The separation logic of `ZigLean/Sep/` for a thread of a concurrent run (legacy: the full-state
thread triples `FTTriple` of `ZigLean/Sep/Full/Thread.lean` replace it).

- **Ownership** (`Mem.Owns`) and **a step of the owner** (`StepIn hF`): `ZigLean/Conc/Clock.lean`.
  A spawn gives ownership to the child, and a join gives it back (`Owned.fork`, `Owned.join` in
  `ZigLean/Conc/Csl.lean`).
- **Thread triples** (`TTriple`). `Triple` with ownership in place of `SingleThread`: if the
  current thread owns the part `P` holds of, `c` does not throw, `Q` holds of the part after it,
  the thread owns that part, and the step is a `StepIn` of the frame. The rules are those of
  `Triple`: `conseq`, `frame`, `ret`, `bind`, `ex`, `lift`, `load`, `store`, `alloc`, `free`.
- **In a thread.** `ZigLean/Conc/Csl.lean` keeps the threads' parts in a proof's invariant and
  has the `WP` rules for a step with a thread triple.
-/

namespace Zig

open Assn

theorem sep_left_comm {P Q R : Assn} {h : Heap} (hh : (P ∗ (Q ∗ R)) h) : (Q ∗ (P ∗ R)) h :=
  sep_assoc (sep_mono (fun _ h => sep_comm h) (fun _ h => h) (sep_assoc' hh))

/-! ## Thread triples -/

/-- `Triple` for a thread (module doc). -/
def TTriple {α : Type} (P : Assn) (c : MemM α) (Q : α → Assn) : Prop :=
  ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.current < m.clocks.size →
    m.Owns m.current hP →
    match (c.run m).run with
    | none => True
    | some (.error e) => e = .stackOverflow
    | some (.ok (v, m')) =>
      ∃ hQ, Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ Q v hQ ∧ m'.Owns m'.current hQ ∧
        StepIn hF m m'

namespace TTriple

variable {α β : Type} {P P' R : Assn} {Q Q' : α → Assn} {c : MemM α}

theorem of_run
    (h : ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.current < m.clocks.size →
      m.Owns m.current hP →
      ∃ v m' hQ, c.run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ Q v hQ ∧
        m'.Owns m'.current hQ ∧ StepIn hF m m') :
    TTriple P c Q := by
  intro m hP hF hd hm hp hc ho
  obtain ⟨v, m', hQ, hr, hd', hm', hq, ho', hs⟩ := h m hP hF hd hm hp hc ho
  rw [hr]; exact ⟨hQ, hd', hm', hq, ho', hs⟩

theorem conseq (ht : TTriple P c Q) (hp : ∀ h, P' h → P h) (hq : ∀ v h, Q v h → Q' v h) :
    TTriple P' c Q' := by
  intro m hP hF hd hm hp' hc ho
  have := ht m hP hF hd hm (hp _ hp') hc ho
  split at this
  · trivial
  · exact this
  · obtain ⟨hQ, a, b, c, d, e⟩ := this; exact ⟨hQ, a, b, hq _ _ c, d, e⟩

/-- The frame rule: a part of the memory that `c` does not own stays unchanged, and the thread
keeps it. -/
theorem frame (ht : TTriple P c Q) : TTriple (P ∗ R) c (fun v => Q v ∗ R) := by
  intro m hPR hF hd hm ⟨hP, hR, hPd, hPR', hp, hr⟩ hc ho
  subst hPR'
  obtain ⟨hPF, hRF⟩ := Heap.disjoint_union_left.mp hd
  have hd' : Heap.Disjoint hP (hR ∪ hF) := Heap.disjoint_union_right.mpr ⟨hPd, hPF⟩
  have hm' : m.heap = hP ∪ (hR ∪ hF) := by rw [hm, Heap.union_assoc]
  have := ht m hP (hR ∪ hF) hd' hm' hp hc (Mem.OwnsC.left ho)
  split at this
  · trivial
  · exact this
  · obtain ⟨hQ, hQd, hmQ, hq, ho', hs⟩ := this
    obtain ⟨hQR, hQF⟩ := Heap.disjoint_union_right.mp hQd
    have hsubR : ∀ l, hR l ≠ none → (hR ∪ hF) l ≠ none := fun l hl => by
      rw [Heap.union_apply]; cases e : hR l <;> simp_all
    refine ⟨hQ ∪ hR, Heap.disjoint_union_left.mpr ⟨hQF, hRF⟩, by rw [hmQ, Heap.union_assoc],
      ⟨hQ, hR, hQR, rfl, hq, hr⟩, Mem.OwnsC.union ho' (Mem.Owns.frameSelf hs (Mem.OwnsC.right ho) hsubR),
      hs.weaken fun l hl => ?_⟩
    simp only [Heap.union_apply]; cases e : hR l <;> simp_all

theorem ret (v : α) : TTriple (Q v) (pure v : MemM α) Q :=
  of_run fun m hP _ hd hm hq _ ho => ⟨v, m, hP, rfl, hd, hm, hq, ho, StepIn.refl m _⟩

theorem bind {R : β → Assn} {f : α → MemM β} (hc : TTriple P c Q) (hf : ∀ v, TTriple (Q v) (f v) R) :
    TTriple P (c >>= f) R := by
  intro m hP hF hd hm hp hcl ho
  have h1 := hc m hP hF hd hm hp hcl ho
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
      have h2 := hf v m' hQ hF hd' hm' hq hcl' ho'
      dsimp only [Bind.bind, Option.bind]
      split at h2
      · trivial
      · exact h2
      · obtain ⟨hR, a, b, c, d, hs'⟩ := h2
        exact ⟨hR, a, b, c, d, hs.trans hs'⟩

theorem ex {γ : Type} {P : γ → Assn} (h : ∀ x, TTriple (P x) c Q) : TTriple (Assn.ex P) c Q := by
  intro m hP hF hd hm ⟨x, hp⟩ hc ho
  exact h x m hP hF hd hm hp hc ho

theorem lift {φ : Prop} (h : φ → TTriple P c Q) : TTriple (⌜φ⌝ ∗ P) c Q := by
  intro m hP hF hd hm hp hc ho
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact h hφ m hP hF hd hm hp hc ho

/-- A load's result fact stays in front of the frame. -/
theorem frame_eq {v : α} {P' : Assn} (ht : TTriple P c (fun r => ⌜r = v⌝ ∗ P')) :
    TTriple (P ∗ R) c (fun r => ⌜r = v⌝ ∗ (P' ∗ R)) :=
  ht.frame.conseq (fun _ h => h) fun _ _ h => sep_assoc h

/-- The frame rule with the frame on the left. -/
theorem frameL (ht : TTriple P c Q) : TTriple (R ∗ P) c (fun v => R ∗ Q v) :=
  ht.frame.conseq (fun _ h => sep_comm h) (fun _ _ h => sep_comm h)

theorem frameL_eq {v : α} {P' : Assn} (ht : TTriple P c (fun r => ⌜r = v⌝ ∗ P')) :
    TTriple (R ∗ P) c (fun r => ⌜r = v⌝ ∗ (R ∗ P')) :=
  ht.frameL.conseq (fun _ h => h) fun _ _ h => sep_left_comm h

/-- A step whose post names its result `v` (a load), then the rest. -/
theorem bind_eq {v : α} {P' : Assn} {f : α → MemM β} {R : β → Assn}
    (hc : TTriple P c (fun r => ⌜r = v⌝ ∗ P')) (hf : TTriple P' (f v) R) : TTriple P (c >>= f) R :=
  hc.bind fun _ => TTriple.lift fun hr => hr ▸ hf

end TTriple

section Rules

variable {T : Type} [Enc T] {m : Mem} {h hF : Heap}

/-- The bytes of `bytesAt` are in the heap. -/
theorem bytesAt_in {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    (hb : bytesAt p A S K bs h) {b : BlockId} (hpb : p.block = some b) {x : Nat}
    (h1 : p.off.toNat ≤ x) (h2 : x < p.off.toNat + bs.size) : h (b, x) ≠ none := by
  obtain ⟨b', hb', -, hl⟩ := hb
  rw [hpb] at hb'; cases hb'
  rw [hl]; simp [h1, h2]

/-- `std.Io` (one value, 16 bytes): a store of it is a store of an encoding. -/
instance : LawfulEnc Io where
  size_encode _ := by simp [Enc.encode, Enc.size]
  decode_encode _ := rfl

/-- Owned bytes are the block's bytes at `p`, in a live block with the address `A`, the size `S`
and the kind `K`. -/
theorem bytesAt_blk {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    (hb : bytesAt p A S K bs h) (hs : ∀ l c, h l = some c → m.heap l = some c) {b : BlockId}
    (hpb : p.block = some b) (hn : 0 < bs.size) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧ blk.addr = A ∧ blk.bytes.size = S ∧
      blk.kind = K ∧ blk.bytes.extract p.off.toNat (p.off.toNat + bs.size) = bs := by
  have hm : m.heap = h ∪ fun l => if h l = none then m.heap l else none := by
    funext l
    cases e : h l with
    | none => simp [e]
    | some c => rw [Heap.union_apply, e, hs l c e]; rfl
  obtain ⟨b', blk, hacc, hblk, hA, hS, hx⟩ := bytesAt_access (q := p.add 0) (k := 0) (n := bs.size)
    (a := 1) hb hm (by simp [Ptr.add]) hn (by omega) (Nat.mod_one _)
  obtain ⟨hqb, -⟩ := access_eq hacc
  have : b' = b := by simp [Ptr.add] at hqb; rw [hpb] at hqb; cases hqb; rfl
  subst this
  have c0 := bytesAt_cell hb hm hpb (j := 0) hn
  obtain ⟨blk', hblk', hl, hlt, hc⟩ := Mem.heap_some c0
  rw [hblk] at hblk'; cases hblk'
  simp only [Cell.mk.injEq] at hc
  refine ⟨blk, hblk, by simpa using hl, hA, hS, hc.2.2.2.symm, ?_⟩
  simp only [Nat.add_zero] at hx
  rw [hx]; simp

/-- A load of the `T` at byte `k` of owned bytes. -/
theorem TTriple.loadAt {p q : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {k a : Nat}
    {v : T} (hq : q = p.add k) (hn : 0 < Enc.size T) (hk : k + Enc.size T ≤ bs.size)
    (ha : (A + p.off.toNat + k) % a = 0) (hv : Enc.decode (bs.extract k (k + Enc.size T)) = pure v) :
    TTriple (bytesAt p A S K bs) (Zig.load T a q) (fun r => ⌜r = v⌝ ∗ bytesAt p A S K bs) :=
  TTriple.of_run fun m hP hF hd hm hb hc ho => by
    obtain ⟨b, blk, hacc, hblk, -, -, hx⟩ := bytesAt_access hb hm hq hn hk ha
    obtain ⟨hqb, -⟩ := access_eq hacc
    have hpb : p.block = some b := by rw [hq] at hqb; exact hqb
    have hv' : Enc.decode (blk.bytes.extract (p.off.toNat + k)
        (p.off.toNat + k + Enc.size T)) = pure v := by rw [hx]; exact hv
    have hin : ∀ x, p.off.toNat + k ≤ x → x < p.off.toNat + k + Enc.size T → hP (b, x) ≠ none :=
      fun x h1 h2 => bytesAt_in hb hpb (by omega) (by omega)
    have hbs : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
    refine ⟨v, _, hP, load_read hacc hv' (ho.noRace hin), hd, ?_, sep_lift.mpr ⟨rfl, hb⟩,
      Mem.Owns.readAt hc ho, StepIn.readAt hc hd hin hbs⟩
    funext l; rw [Mem.heap_readAt]; exact congrFun hm l

/-- Forming a pointer `k` bytes into owned bytes (one past the end included; `ptrProject`,
MM-3): no access, the memory does not change. -/
theorem TTriple.ptrProjectAt {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {k : Nat}
    (hk : k ≤ bs.size) (hpos : 0 < bs.size) :
    TTriple (bytesAt p A S K bs) (ptrProject p (·.add k))
      (fun r => ⌜r = p.add k⌝ ∗ bytesAt p A S K bs) :=
  TTriple.of_run fun m hP _ hd hm hb _ ho =>
    ⟨p.add k, m, hP, bytesAt_ptrProject_run hb hm hk hpos, hd, hm, sep_lift.mpr ⟨rfl, hb⟩, ho,
      StepIn.refl m _⟩

/-- A store of the bytes `bs'` at byte `k` of owned bytes. -/
theorem TTriple.storeBytesAt {p q : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {k a : Nat} (bs' : Array Byte) (hq : q = p.add k) (hn : 0 < bs'.size)
    (hk : k + bs'.size ≤ bs.size) (ha : (A + p.off.toNat + k) % a = 0) (hK : K ≠ .constGlobal) :
    TTriple (bytesAt p A S K bs) (Zig.storeBytes q a bs')
      (fun _ => bytesAt p A S K (writeBytes bs k bs')) :=
  TTriple.of_run fun m hP hF hd hm hb hc ho => by
    have hin : ∀ b, p.block = some b →
        ∀ x, p.off.toNat + k ≤ x → x < p.off.toNat + k + bs'.size → hP (b, x) ≠ none :=
      fun b hpb x h1 h2 => bytesAt_in hb hpb (by omega) (by omega)
    obtain ⟨b, blk, hpb, hr, h', hd', hm', hb'⟩ :=
      bytesAt_store_core (bs' := bs') hb hm hd hq (by omega) (by omega) ha
        (fun b hpb => ho.noRace (hin b hpb)) hK
    have hbs : b < m.blocks.size := by
      have c0 := bytesAt_cell (j := 0) hb hm hpb (by omega)
      obtain ⟨blk', hblk', -⟩ := Mem.heap_some c0
      exact (Array.getElem?_eq_some_iff.mp hblk').1
    have hs1 := StepIn.recordAt (kind := .write) hc hd (hin b hpb) hbs
    refine ⟨(), _, h', hr, hd', hm', hb', Mem.Owns.write ?_, hs1.trans (StepIn.write _ _ _ _ _ _)⟩
    -- The bytes of `h'` are those of `hP`.
    have ho1 := Mem.Owns.recordAt (b := b) (off := p.off.toNat + k) (len := bs'.size)
      (kind := .write) hc ho
    intro e he ht
    apply ho1 e he
    rcases ht with ⟨x, h1, h2, h3⟩ | hb2
    · refine .inl ⟨x, h1, h2, ?_⟩
      obtain ⟨b'', hpb'', -, hl'⟩ := id hb'
      rw [hpb] at hpb''; cases hpb''
      rw [hl', writeBytes_size _ _ _ (by omega)] at h3
      split at h3
      · rename_i hc'
        obtain ⟨hbe, hx1, hx2⟩ := hc'
        simp only at hbe hx1 hx2
        rw [hbe]; exact bytesAt_in hb hpb hx1 hx2
      · exact absurd rfl h3
    · exact .inr (by simpa [Mem.write] using hb2)

/-- A store of `w`, whose encoding has the size of `T`, at byte `k` of owned bytes. -/
theorem TTriple.storeAt' {p q : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {k a : Nat} (w : T) (hw : (Enc.encode w).size = Enc.size T) (hq : q = p.add k)
    (hn : 0 < Enc.size T) (hk : k + Enc.size T ≤ bs.size)
    (ha : (A + p.off.toNat + k) % a = 0) (hK : K ≠ .constGlobal) :
    TTriple (bytesAt p A S K bs) (Zig.store a q w)
      (fun _ => bytesAt p A S K (writeBytes bs k (Enc.encode w))) :=
  TTriple.storeBytesAt (Enc.encode w) hq (by omega) (by omega) ha hK

/-- A store of `w` at byte `k` of owned bytes. -/
theorem TTriple.storeAt [LawfulEnc T] {p q : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {k a : Nat} (w : T) (hq : q = p.add k) (hn : 0 < Enc.size T) (hk : k + Enc.size T ≤ bs.size)
    (ha : (A + p.off.toNat + k) % a = 0) (hK : K ≠ .constGlobal) :
    TTriple (bytesAt p A S K bs) (Zig.store a q w)
      (fun _ => bytesAt p A S K (writeBytes bs k (Enc.encode w))) :=
  TTriple.storeAt' w (LawfulEnc.size_encode w) hq hn hk ha hK

theorem TTriple.load {p : Ptr} {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    TTriple (pts p a v) (Zig.load T a p) (fun r => ⌜r = v⌝ ∗ pts p a v) := by
  intro m hP hF hd hm hp
  obtain ⟨A, S, K, bs, ha, hs, hv, hb, hK⟩ := hp
  refine (TTriple.loadAt (k := 0) (a := a) (v := v) (by simp [Ptr.add]) hn (by omega)
    (by simpa using ha) ?_ |>.conseq (fun _ h => h) fun r h hq => ?_) m hP hF hd hm hb
  · rw [show bs.extract 0 (0 + Enc.size T) = bs by rw [← hs]; simp]; exact hv
  · obtain ⟨hr, hb'⟩ := sep_lift.mp hq
    exact sep_lift.mpr ⟨hr, A, S, K, bs, ha, hs, hv, hb', hK⟩

theorem TTriple.store [LawfulEnc T] {p : Ptr} {a : Nat} {v : T} (hn : 0 < Enc.size T) (w : T) :
    TTriple (pts p a v) (Zig.store a p w) (fun _ => pts p a w) := by
  intro m hP hF hd hm hp
  obtain ⟨A, S, K, bs, ha, hs, -, hb, hK⟩ := hp
  have hw := LawfulEnc.size_encode w
  refine (TTriple.storeAt (k := 0) (a := a) w (by simp [Ptr.add]) hn (by omega)
    (by simpa using ha) hK |>.conseq (fun _ h => h) fun _ h hq => ?_) m hP hF hd hm hb
  refine ⟨A, S, K, _, ha, ?_, ?_, hq, hK⟩
  · rw [writeBytes_all (by omega)]; exact hw
  · rw [writeBytes_all (by omega)]; exact LawfulEnc.decode_encode w

end Rules

section Blocks

variable {m : Mem} {h hF : Heap}

/-- A byte of `bytesAt p …` is in the block of `p`. -/
theorem bytesAt_block {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    (hb : bytesAt p A S K bs h) {b : BlockId} (hpb : p.block = some b) {l : Loc}
    (hl : h l ≠ none) : l.1 = b := by
  obtain ⟨b', hb', -, hown⟩ := hb
  rw [hpb] at hb'; cases hb'
  rw [hown] at hl
  split at hl
  · rename_i hc; exact hc.1
  · exact absurd rfl hl

/-- A step that changes only the blocks. -/
theorem StepIn.sameThreads {m' : Mem} (hs : m.SameThreads m') (hb : m.blocks.size ≤ m'.blocks.size) :
    StepIn hF m m' where
  current := hs.current
  threads := hs.threads
  atomics := hs.atomics
  seen := hs.seen
  nextMsg := hs.nextMsg
  waiters := hs.waiters
  woken := hs.woken
  groups := hs.groups
  size := by rw [hs.clocks]
  others u _ := by rw [hs.clocks]
  mine := by rw [hs.clocks]; exact VClock.le_refl _
  blocks := hb
  fp e he := .inl (hs.footprint ▸ he)
  fpc e he := .inl (hs.footprint ▸ he)

theorem TTriple.alloc (kind : BlockKind) (size align : Nat) (ha : 0 < align)
    (hk : kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    TTriple emp (Zig.alloc kind size align) (fun p => Assn.ex fun A =>
      ⌜p.off = 0 ∧ A % align = 0⌝ ∗ bytesAt p A size kind (Array.replicate size .undef)) :=
  fun m hP hF hd hm hp hc ho => by
    have hP0 : hP = Heap.empty := hp
    subst hP0
    cases hroom : m.allocOk kind size align
    · rw [alloc_run_noRoom m hroom]; try trivial
    obtain ⟨p, m', h', hr, h0, hpb, hsz, hd', hm', -, hs, A, -, hA, hb⟩ :=
      alloc_run_core hd hm kind size align ha hroom hk
    simp only [Heap.empty_union] at hd' hm'
    rw [hr]
    refine ⟨h', hd', hm', ⟨A, sep_lift.mpr ⟨⟨h0, hA⟩, hb⟩⟩, ?_,
      StepIn.sameThreads hs (by omega)⟩
    intro e he ht
    rw [hs.footprint] at he
    unfold Mem.Owns at ho
    rw [hs.current, hs.clocks]
    apply ho e he (.inr ?_)
    rcases ht with ⟨x, -, -, hx⟩ | hb'
    · have := bytesAt_block hb hpb hx; simp only at this; rw [this]; exact Nat.le_refl _
    · omega

/-- An allocation next to the heap `R` that the thread owns. -/
theorem alloc_next {R : Assn} (size align : Nat) (ha : 0 < align) :
    TTriple R (Zig.alloc .stack size align) (fun p => R ∗ Assn.ex fun A =>
      ⌜p.off = 0 ∧ A % align = 0⌝ ∗ bytesAt p A size .stack (Array.replicate size .undef)) :=
  (TTriple.alloc .stack size align ha).frameL.conseq (fun _ h => sep_emp.mpr h) fun _ _ h => h

theorem sep_ex_lift {R : Assn} {φ : Nat → Prop} {P : Nat → Assn} {h : Heap}
    (hh : (R ∗ Assn.ex fun A => ⌜φ A⌝ ∗ P A) h) : ∃ A, φ A ∧ (R ∗ P A) h := by
  obtain ⟨h₁, h₂, hd, rfl, hr, A, hp⟩ := hh
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact ⟨A, hφ, h₁, h₂, hd, rfl, hr, hp⟩

theorem TTriple.free {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} (hS : bs.size = S)
    (h0 : p.off = 0) (hpos : 0 < S) (hK : K ≠ .constGlobal := by decide) :
    TTriple (bytesAt p A S K bs) (Zig.free p) (fun _ => emp) :=
  TTriple.of_run fun m _ hF hd hm hb _ ho => by
    obtain ⟨m', hr, hm', hsz, hs⟩ := free_run_core hb hm hd hS h0 hpos (fun b hpb =>
      freeRaces_of_clock fun e he heb hl ho' => by
        obtain ⟨b', hpb', -, hown⟩ := id hb
        rw [hpb] at hpb'; cases hpb'
        refine ho e he (.inl ⟨e.off, Nat.le_refl _, by omega, ?_⟩)
        rw [hown, heb]; simp [h0, hS, ho']) hK
    refine ⟨(), m', Heap.empty, hr, (Heap.disjoint_empty hF).symm, hm', rfl, ?_,
      StepIn.sameThreads hs (by omega)⟩
    intro e he ht
    rw [hs.footprint] at he
    unfold Mem.Owns at ho
    rw [hs.current, hs.clocks]
    apply ho e he (.inr ?_)
    rcases ht with ⟨x, -, -, hx⟩ | hb'
    · exact absurd rfl hx
    · omega

end Blocks

end Zig
