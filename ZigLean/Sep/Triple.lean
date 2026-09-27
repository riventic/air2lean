import ZigLean.Sep.Assert

/-!
# Typed assertions and triples

`pts p a v`: `p` points to the value `v`, which a load or store with alignment `a` can access.
`arr p vs`: `p` points to the items `vs`, one after the other.

`Triple P c Q` is partial correctness without a panic: if `P` holds of a part of
the memory, `c` does not throw; if it returns `v`, `Q v` holds of that part after it, and the
rest of the memory (the frame) is unchanged. A program that does not terminate satisfies every
triple. The frame is in the definition, so the frame rule (`Triple.frame`) holds for every
program.

The `*_run` lemmas state what one memory operation does to a heap that owns the bytes it
accesses. A proof about generated code unfolds the code (`zig_unfold`) and uses them.
-/

namespace Zig

open Assn

/-- `p` points to `v`, and an access with alignment `a` to it is aligned. -/
def pts {T : Type} [Enc T] (p : Ptr) (a : Nat) (v : T) : Assn := fun h =>
  ∃ A S K bs, (A + p.off.toNat) % a = 0 ∧ bs.size = Enc.size T ∧ Enc.decode bs = pure v ∧
    bytesAt p A S K bs h

/-- `p` points to the items `vs`, each `Enc.size T` bytes, the first aligned to `Enc.align T`. -/
def arr {T : Type} [Enc T] (p : Ptr) (vs : List T) : Assn := fun h =>
  ∃ A S K bs, (A + p.off.toNat) % Enc.align T = 0 ∧ bs.size = Enc.size T * vs.length ∧
    (∀ i (hi : i < vs.length),
      Enc.decode (bs.extract (Enc.size T * i) (Enc.size T * i + Enc.size T)) = pure vs[i]) ∧
    bytesAt p A S K bs h

section Lemmas

variable {m : Mem} {h hF : Heap} {T : Type} [Enc T]

theorem writeBytes_all {a bs : Array Byte} (h : bs.size = a.size) : writeBytes a 0 bs = bs := by
  simp [writeBytes, h]

/-- The bytes at `x` of a write, inside the written range, are the written ones. -/
theorem extract_writeBytes_in (a bs : Array Byte) (o x n : Nat) (h : o + bs.size ≤ a.size)
    (hx : o ≤ x) (hn : x + n ≤ o + bs.size) :
    (writeBytes a o bs).extract x (x + n) = bs.extract (x - o) (x - o + n) := by
  have hs := writeBytes_size a o bs h
  apply Array.ext
  · simp; omega
  · intro i h1 _
    simp only [Array.size_extract] at h1
    simp only [Array.getElem_extract]
    rw [writeBytes_getElem a o bs h _ (by omega)]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), getElem!_pos bs _ (by omega)]
    congr 1; omega

/-- `Ptr.elem` as `Ptr.add`. -/
theorem Ptr.elem_eq (p : Ptr) (size : Nat) (i : BitVec 64) :
    p.elem size i = p.add ((size * i.toNat : Nat) : Int) := by
  simp [Ptr.elem, Ptr.add]

theorem pts_load_run {p : Ptr} {a : Nat} {v : T} (hp : pts p a v h) (hm : m.heap = h ∪ hF)
    (hn : 0 < Enc.size T) : (load T a p).run m = pure (v, m) := by
  obtain ⟨A, S, K, bs, ha, hs, hv, hb⟩ := hp
  obtain ⟨b, blk, hacc, -, -, -, hx⟩ :=
    bytesAt_access (q := p) (k := 0) (n := Enc.size T) (a := a) hb hm (by simp [Ptr.add])
      hn (by omega) (by simpa using ha)
  apply load_run (by simpa using hacc)
  simp only [Nat.add_zero] at hx
  rw [hx, show bs.extract 0 (0 + Enc.size T) = bs by rw [← hs]; simp]
  exact hv

theorem pts_store_run [LawfulEnc T] {p : Ptr} {a : Nat} {v : T} (hp : pts p a v h)
    (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hn : 0 < Enc.size T) (w : T) :
    ∃ m', (store a p w).run m = pure ((), m') ∧
      ∃ h', Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ pts p a w h' := by
  obtain ⟨A, S, K, bs, ha, hs, -, hb⟩ := hp
  have hw := LawfulEnc.size_encode w
  obtain ⟨m', hrun, h', hd', hm', hb'⟩ :=
    bytesAt_store (q := p) (k := 0) (a := a) (bs' := Enc.encode w) hb hm hd (by simp [Ptr.add])
      (by omega) (by omega) (by simpa using ha)
  refine ⟨m', hrun, h', hd', hm', A, S, K, _, ha, ?_, ?_, hb'⟩
  · rw [writeBytes_all (by omega)]; exact hw
  · rw [writeBytes_all (by omega)]; exact LawfulEnc.decode_encode w

/-- The alignment of item `i`: a multiple of `a` if `a` divides the item alignment, and that
divides the item size. -/
theorem item_aligned {A o a i : Nat} (hA : (A + o) % Enc.align T = 0) (ha : a ∣ Enc.align T)
    (hs : Enc.align T ∣ Enc.size T) : (A + o + Enc.size T * i) % a = 0 := by
  apply Nat.mod_eq_zero_of_dvd
  apply Nat.dvd_trans ha
  exact Nat.dvd_add (Nat.dvd_of_mod_eq_zero hA) (Nat.dvd_trans hs (Nat.dvd_mul_right _ _))

theorem arr_load_run {p : Ptr} {vs : List T} {a : Nat} {i : BitVec 64} (hp : arr p vs h)
    (hm : m.heap = h ∪ hF) (hn : 0 < Enc.size T) (ha : a ∣ Enc.align T)
    (hs : Enc.align T ∣ Enc.size T) (hi : i.toNat < vs.length) :
    (load T a (p.elem (Enc.size T) i)).run m = pure (vs[i.toNat], m) := by
  obtain ⟨A, S, K, bs, hA, hsz, hv, hb⟩ := hp
  have hk : Enc.size T * i.toNat + Enc.size T ≤ bs.size := by
    rw [hsz, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  obtain ⟨b, blk, hacc, -, -, -, hx⟩ :=
    bytesAt_access (k := Enc.size T * i.toNat) (n := Enc.size T) (a := a) hb hm
      (Ptr.elem_eq p _ i) hn hk (item_aligned hA ha hs)
  apply load_run hacc
  rw [hx]; exact hv _ hi

theorem arr_store_run [LawfulEnc T] {p : Ptr} {vs : List T} {a : Nat} {i : BitVec 64}
    (hp : arr p vs h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hn : 0 < Enc.size T)
    (ha : a ∣ Enc.align T) (hs : Enc.align T ∣ Enc.size T) (hi : i.toNat < vs.length) (w : T) :
    ∃ m', (store a (p.elem (Enc.size T) i) w).run m = pure ((), m') ∧
      ∃ h', Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ arr p (vs.set i.toNat w) h' := by
  obtain ⟨A, S, K, bs, hA, hsz, hv, hb⟩ := hp
  have hw := LawfulEnc.size_encode w
  have hk : Enc.size T * i.toNat + (Enc.encode w).size ≤ bs.size := by
    rw [hsz, hw, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  obtain ⟨m', hrun, h', hd', hm', hb'⟩ :=
    bytesAt_store (k := Enc.size T * i.toNat) (a := a) (bs' := Enc.encode w) hb hm hd
      (Ptr.elem_eq p _ i) (by omega) hk (item_aligned hA ha hs)
  refine ⟨m', hrun, h', hd', hm', A, S, K, _, hA, ?_, ?_, hb'⟩
  · rw [writeBytes_size _ _ _ hk, hsz, List.length_set]
  · intro j hj
    rw [List.length_set] at hj
    have hjk : Enc.size T * j + Enc.size T ≤ bs.size := by
      rw [hsz, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
    by_cases hij : j = i.toNat
    · subst hij
      rw [extract_writeBytes_in _ _ _ _ _ hk (Nat.le_refl _) (by omega)]
      simp only [Nat.sub_self, Nat.zero_add, List.getElem_set_self]
      rw [← hw, Array.extract_size]; exact LawfulEnc.decode_encode w
    · rw [extract_writeBytes_disjoint _ _ _ _ _ hk hjk ?_, List.getElem_set_ne (Ne.symm hij)]
      · exact hv j hj
      · have hsj := Nat.mul_succ (Enc.size T) j
        have hsi := Nat.mul_succ (Enc.size T) i.toNat
        rw [hw]
        rcases Nat.lt_or_gt_of_ne hij with h | h
        · right; have := Nat.mul_le_mul_left (Enc.size T) (Nat.succ_le_of_lt h); omega
        · left; have := Nat.mul_le_mul_left (Enc.size T) (Nat.succ_le_of_lt h); omega

theorem Array.size_flatten_replicate {α : Type} (x : Array α) (n : Nat) : ((Array.replicate n x).flatten).size = n * x.size := by
  induction n with
  | zero => simp
  | succ k ih => simp [Array.replicate_succ, Array.flatten_push, ih, Nat.succ_mul]

theorem Array.extract_flatten_replicate {α : Type} (x : Array α) (n j : Nat) (hj : j < n) :
    ((Array.replicate n x).flatten).extract (x.size * j) (x.size * j + x.size) = x := by
  induction n generalizing j with
  | zero => omega
  | succ k ih =>
    rw [Array.replicate_succ, Array.flatten_push]
    have hs := Array.size_flatten_replicate x k
    rw [Array.extract_append, hs]
    by_cases hjk : j < k
    · have h1 := Nat.mul_le_mul_left x.size (Nat.succ_le_of_lt hjk)
      rw [Nat.mul_succ] at h1
      rw [ih j hjk]
      have : x.size * j + x.size - k * x.size = 0 := by rw [Nat.mul_comm k]; omega
      rw [this]; simp
    · have : j = k := by omega
      subst this
      have e : x.size * j - j * x.size = 0 := by rw [Nat.mul_comm]; omega
      have e' : x.size * j + x.size - j * x.size = x.size := by rw [Nat.mul_comm]; omega
      rw [e, e']
      simp [hs, Nat.mul_comm]

theorem arr_memset_run [LawfulEnc T] {p : Ptr} {vs : List T} {a : Nat} {n : BitVec 64}
    (hp : arr p vs h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hn : 0 < Enc.size T)
    (ha : a ∣ Enc.align T) (hn' : n.toNat = vs.length) (w : T) :
    ∃ m', (memset a p n (some w)).run m = pure ((), m') ∧
      ∃ h', Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ arr p (List.replicate vs.length w) h' := by
  by_cases h0 : n.toNat = 0
  · refine ⟨m, ?_, h, hd, hm, ?_⟩
    · simp [memset, h0, StateT.run, pure, StateT.pure, ExceptT.pure, ExceptT.mk]
    · have : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; exact hp
  obtain ⟨A, S, K, bs, hA, hsz, -, hb⟩ := hp
  have hw := LawfulEnc.size_encode w
  let bs' := (Array.replicate n.toNat (Enc.encode w)).flatten
  have hs' : bs'.size = Enc.size T * vs.length := by
    simp only [bs', Array.size_flatten_replicate, hw, hn']; exact Nat.mul_comm _ _
  have ha0 : (A + p.off.toNat + 0) % a = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans ha (Nat.dvd_of_mod_eq_zero (by simpa using hA)))
  have hpos : 0 < bs'.size := by rw [hs']; exact Nat.mul_pos hn (by omega)
  have hp0 : p = p.add ((0 : Nat) : Int) := by simp [Ptr.add]
  obtain ⟨b, blk, hacc, -, -, -, -⟩ := bytesAt_access (q := p) (k := 0) (n := bs'.size) (a := a)
    hb hm hp0 hpos (by omega) ha0
  obtain ⟨m', hrun, h', hd', hm', hb'⟩ := bytesAt_store (q := p) (k := 0) (a := a) (bs' := bs') hb
    hm hd hp0 hpos (by omega) ha0
  rw [writeBytes_all (by omega)] at hb'
  refine ⟨m', ?_, h', hd', hm', A, S, K, bs', hA, by simp [hs'], ?_, hb'⟩
  · have e : n.toNat * Enc.size T = bs'.size := by rw [hs', hn', Nat.mul_comm]
    simp only [StateT.run] at hrun
    simp only [memset, h0, ↓reduceIte, zig_unfold, e, hacc, ExceptT.bindCont]
    exact hrun
  · intro j hj
    simp only [List.length_replicate] at hj
    rw [List.getElem_replicate, ← hw, Array.extract_flatten_replicate _ _ _ (by omega)]
    exact LawfulEnc.decode_encode w

/-- `vs` with the `len` items from `d` on replaced by the `len` items from `s` on (the items
before the copy: `@memmove`). -/
def copyItems {T : Type} (vs : List T) (d s len : Nat) : List T :=
  vs.mapIdx fun j x => if d ≤ j ∧ j < d + len then vs.getD (j - d + s) x else x

theorem arr_memmove_run {p : Ptr} {vs : List T} {a : Nat} {d s n : BitVec 64} (hp : arr p vs h)
    (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hn : 0 < Enc.size T)
    (ha : a ∣ Enc.align T) (hs : Enc.align T ∣ Enc.size T)
    (hdn : d.toNat + n.toNat ≤ vs.length) (hsn : s.toNat + n.toNat ≤ vs.length) :
    ∃ m', (memmove (Enc.size T) a a (p.elem (Enc.size T) d) (p.elem (Enc.size T) s) n).run m =
        pure ((), m') ∧
      ∃ h', Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧
        arr p (copyItems vs d.toNat s.toNat n.toNat) h' := by
  have hlen : (copyItems vs d.toNat s.toNat n.toNat).length = vs.length := by simp [copyItems]
  by_cases h0 : n.toNat = 0
  · refine ⟨m, ?_, h, hd, hm, ?_⟩
    · simp [memmove, h0, StateT.run, pure, StateT.pure, ExceptT.pure, ExceptT.mk]
    · have : copyItems vs d.toNat s.toNat n.toNat = vs := by
        apply List.ext_getElem hlen; intro j _ _; simp [copyItems, h0]; omega
      rw [this]; exact hp
  obtain ⟨A, S, K, bs, hA, hsz, hv, hb⟩ := hp
  have hdk : (Enc.size T) * d.toNat + (Enc.size T) * n.toNat ≤ bs.size := by
    rw [hsz, ← Nat.mul_add]; exact Nat.mul_le_mul_left _ hdn
  have hsk : (Enc.size T) * s.toNat + (Enc.size T) * n.toNat ≤ bs.size := by
    rw [hsz, ← Nat.mul_add]; exact Nat.mul_le_mul_left _ hsn
  have hpos : 0 < (Enc.size T) * n.toNat := Nat.mul_pos hn (by omega)
  obtain ⟨b, blk, hacc, -, -, -, -⟩ := bytesAt_access (k := (Enc.size T) * d.toNat) (n := (Enc.size T) * n.toNat)
    (a := a) hb hm (Ptr.elem_eq p _ d) hpos hdk (item_aligned hA ha hs)
  obtain ⟨b₂, blk₂, hacc₂, -, -, -, hx₂⟩ := bytesAt_access (k := (Enc.size T) * s.toNat)
    (n := (Enc.size T) * n.toNat) (a := a) hb hm (Ptr.elem_eq p _ s) hpos hsk (item_aligned hA ha hs)
  let src := bs.extract ((Enc.size T) * s.toNat) ((Enc.size T) * s.toNat + (Enc.size T) * n.toNat)
  have hsrc : src.size = (Enc.size T) * n.toNat := by simp [src]; omega
  obtain ⟨m', hrun, h', hd', hm', hb'⟩ := bytesAt_store (k := (Enc.size T) * d.toNat) (a := a) (bs' := src)
    hb hm hd (Ptr.elem_eq p _ d) (by omega) (by omega) (item_aligned hA ha hs)
  refine ⟨m', ?_, h', hd', hm', A, S, K, _, hA, ?_, ?_, hb'⟩
  · have hl := loadBytes_run hacc₂
    rw [hx₂] at hl
    simp only [StateT.run] at hl hrun
    simp only [memmove, h0, ↓reduceIte, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, liftM, monadLift, MonadLift.monadLift, StateT.lift, ExceptT.bind, ExceptT.mk,
      ExceptT.bindCont, Nat.mul_comm n.toNat (Enc.size T), hacc, hl, pure, ExceptT.pure,
      Option.bind_some]
    exact hrun
  · rw [writeBytes_size _ _ _ (by omega), hsz, hlen]
  · intro j hj
    rw [hlen] at hj
    have hjk : (Enc.size T) * j + (Enc.size T) ≤ bs.size := by rw [hsz, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
    simp only [copyItems, List.getElem_mapIdx]
    by_cases hin : d.toNat ≤ j ∧ j < d.toNat + n.toNat
    · have hlt : j - d.toNat + s.toNat < vs.length := by omega
      simp only [hin, and_self, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
        Option.getD_some]
      have h1 := Nat.mul_le_mul_left (Enc.size T) hin.1
      have h2 := Nat.mul_le_mul_left (Enc.size T) (Nat.succ_le_of_lt hin.2)
      rw [Nat.mul_succ] at h2
      rw [extract_writeBytes_in _ _ _ _ _ (by omega) h1 (by rw [hsrc, ← Nat.mul_add]; omega)]
      have e1 := Nat.mul_sub (Enc.size T) j d.toNat
      have e2 := Nat.mul_add (Enc.size T) (j - d.toNat) s.toNat
      have e3 := Nat.mul_succ (Enc.size T) (j - d.toNat + s.toNat)
      have h3 := Nat.mul_le_mul_left (Enc.size T) (show j - d.toNat + 1 ≤ n.toNat by omega)
      rw [Nat.mul_succ] at h3
      rw [Array.extract_extract, show Enc.size T * s.toNat + (Enc.size T * j - Enc.size T * d.toNat)
          = Enc.size T * (j - d.toNat + s.toNat) by omega,
        Nat.min_eq_left (by omega)]
      rw [show Enc.size T * s.toNat + (Enc.size T * j - Enc.size T * d.toNat + Enc.size T)
          = Enc.size T * (j - d.toNat + s.toNat) + Enc.size T by omega]
      exact hv _ hlt
    · simp only [hin, ↓reduceIte]
      rw [extract_writeBytes_disjoint _ _ _ _ _ (by omega) hjk ?_]
      · exact hv j hj
      · rw [hsrc]
        rcases Nat.lt_or_ge j d.toNat with h | h
        · right; have := Nat.mul_le_mul_left (Enc.size T) (Nat.succ_le_of_lt h); rw [Nat.mul_succ] at this
          omega
        · left; have : d.toNat + n.toNat ≤ j := by omega
          have := Nat.mul_le_mul_left (Enc.size T) this; rw [Nat.mul_add] at this; omega

end Lemmas

/-! ## Triples -/

/-- `Triple P c Q` (module doc). -/
def Triple {α : Type} (P : Assn) (c : MemM α) (Q : α → Assn) : Prop :=
  ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP →
    match (c.run m).run with
    | none => True
    | some (.error _) => False
    | some (.ok (v, m')) => ∃ hQ, Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ Q v hQ


namespace Triple

variable {α β : Type} {P P' R : Assn} {Q Q' : α → Assn} {c : MemM α}

/-- A triple from the run: `c` returns, and the post-condition holds. -/
theorem of_run
    (h : ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP →
      ∃ v m' hQ, c.run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ Q v hQ) :
    Triple P c Q := by
  intro m hP hF hd hm hp
  obtain ⟨v, m', hQ, hr, hd', hm', hq⟩ := h m hP hF hd hm hp
  rw [hr]; exact ⟨hQ, hd', hm', hq⟩

theorem conseq (ht : Triple P c Q) (hp : ∀ h, P' h → P h) (hq : ∀ v h, Q v h → Q' v h) :
    Triple P' c Q' := by
  intro m hP hF hd hm hp'
  have := ht m hP hF hd hm (hp _ hp')
  split at this
  · trivial
  · exact this
  · obtain ⟨hQ, a, b, c⟩ := this; exact ⟨hQ, a, b, hq _ _ c⟩

/-- The frame rule: a part of the memory that `c` does not own stays unchanged. -/
theorem frame (ht : Triple P c Q) : Triple (P ∗ R) c (fun v => Q v ∗ R) := by
  intro m hPR hF hd hm ⟨hP, hR, hPd, hPR', hp, hr⟩
  subst hPR'
  obtain ⟨hPF, hRF⟩ := Heap.disjoint_union_left.mp hd
  have hd' : Heap.Disjoint hP (hR ∪ hF) := Heap.disjoint_union_right.mpr ⟨hPd, hPF⟩
  have hm' : m.heap = hP ∪ (hR ∪ hF) := by rw [hm, Heap.union_assoc]
  have := ht m hP (hR ∪ hF) hd' hm' hp
  split at this
  · trivial
  · exact this
  · obtain ⟨hQ, hQd, hmQ, hq⟩ := this
    obtain ⟨hQR, hQF⟩ := Heap.disjoint_union_right.mp hQd
    exact ⟨hQ ∪ hR, Heap.disjoint_union_left.mpr ⟨hQF, hRF⟩, by rw [hmQ, Heap.union_assoc],
      hQ, hR, hQR, rfl, hq, hr⟩

theorem ret (v : α) : Triple (Q v) (pure v : MemM α) (Q) :=
  of_run fun m hP _ hd hm hq => ⟨v, m, hP, rfl, hd, hm, hq⟩

theorem bind {R : β → Assn} {f : α → MemM β} (hc : Triple P c Q) (hf : ∀ v, Triple (Q v) (f v) R) :
    Triple (P) (c >>= f) (R) := by
  intro m hP hF hd hm hp
  have h1 := hc m hP hF hd hm hp
  simp only [StateT.run_bind, ExceptT.run_bind]
  revert h1
  cases (c.run m).run with
  | none => intro; trivial
  | some r =>
    cases r with
    | error e => intro h1; exact h1.elim
    | ok r =>
      obtain ⟨v, m'⟩ := r
      rintro ⟨hQ, hd', hm', hq⟩
      exact hf v m' hQ hF hd' hm' hq

theorem ex {γ : Type} {P : γ → Assn} (h : ∀ x, Triple (P x) c Q) : Triple (Assn.ex P) c Q := by
  intro m hP hF hd hm ⟨x, hp⟩
  exact h x m hP hF hd hm hp

theorem lift {φ : Prop} (h : φ → Triple P c Q) : Triple (⌜φ⌝ ∗ P) c Q := by
  intro m hP hF hd hm hp
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact h hφ m hP hF hd hm hp

end Triple

section Rules

variable {T : Type} [Enc T]

theorem Triple.load {p : Ptr} {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    Triple (pts p a v) (load T a p) (fun r => ⌜r = v⌝ ∗ pts p a v) :=
  Triple.of_run fun _ hP _ hd hm hp =>
    ⟨v, _, hP, pts_load_run hp hm hn, hd, hm, sep_lift.mpr ⟨rfl, hp⟩⟩

theorem Triple.store [LawfulEnc T] {p : Ptr} {a : Nat} {v : T} (hn : 0 < Enc.size T) (w : T) :
    Triple (pts p a v) (store a p w) (fun _ => pts p a w) :=
  Triple.of_run fun _ _ _ hd hm hp => by
    obtain ⟨m', hr, h', hd', hm', hp'⟩ := pts_store_run hp hm hd hn w
    exact ⟨(), m', h', hr, hd', hm', hp'⟩

end Rules

end Zig
