import AllocFba.Fba

/-!
# The proved client of a translated `FixedBufferAllocator` (`client.zig`, `fba_client`)

`Client.client_spec`: from the `buffer` global (16 bytes) and the allocator's vtable constant,
the generated `fba_client v` returns, without any error (no `.illegal`, no panic), one of the
out-of-memory codes `1`–`4` or `v + v + (v +% 1)`: the bytes written before the `realloc` are
still there after it (`keepsPrefix`), and the byte written after it too.

The proof uses only the generic contracts: the wrapper contracts (`Wrap.*_spec`) for the
`AllocSpec` of the allocator behind the `Allocator` value, which is `dispatch_allocSpec` of
`FBA.allocSpec`; the bridge equalities (`Bridge.lean`); and the fixed buffer allocator's own API
around the vtable (`own_init`, `own_state`, `reset_spec`, `grantSep`). It does not unfold the
allocator. The client keeps the buffer's last 3 bytes for itself (`guard`); they keep the
buffer's block alive across the allocator calls, which is how the client knows, at `reset`, that
every buffer byte is back (`Covers`).
-/

namespace AllocFba.Client

open Zig Gen Assn FBA

/-- The buffer pointer, the pin and the client's bytes: `buffer[0..12]`, `buffer[12]`,
`buffer[13..16]`. -/
abbrev bufp : Ptr := ⟨some 0, 0⟩
abbrev pinp : Ptr := ⟨some 0, 12⟩
abbrev guardp : Ptr := ⟨some 0, 13⟩
abbrev vtp : Ptr := ⟨some 5, 0⟩

/-- The fixed buffer allocator of the client: its struct at `s1` (block address `Ac`). -/
def buf (A₀ Ac : Nat) : Buf where
  ptr := bufp
  cap := 12
  A := A₀
  S := 16
  K := .global
  pin := pinp
  cA := Ac
  cS := 24
  cK := .stack

/-- The `Allocator` value `fba.allocator()`. -/
abbrev alc (s1 : Ptr) : mem_Allocator := ⟨s1, vtp⟩

/-- The allocator invariant behind the `Allocator` value: the fixed buffer and the vtable. -/
abbrev I (s1 : Ptr) (A₀ Ac : Nat) : AllocInv := (inv s1 (buf A₀ Ac)).withVTable vtp fns

theorem spec (s1 : Ptr) (A₀ Ac : Nat) : AllocSpec Logic.total (vt (alc s1)) s1 (I s1 A₀ Ac) :=
  dispatch_allocSpec (allocSpec s1 (buf A₀ Ac)) (by simp [vtp])

theorem grantSep' (s1 : Ptr) (A₀ Ac : Nat) (k : Nat) : GrantSep (I s1 A₀ Ac) k :=
  grantSep s1 (buf A₀ Ac) k

/-- The bytes the client keeps. -/
def guard (A₀ : Nat) (g : Array Byte) : Assn := regionIn guardp A₀ 16 .global 1 g

/-- The coverage that `reset` needs: every byte of `buffer[0..12]`. -/
def cov : Heap → Prop := Covers 0 0 12

/-- The results of `fba_client v`. -/
def expected (v : BitVec 8) : BitVec 32 := BitVec.ofNat 32 (v.toNat + v.toNat + (v + 1).toNat)

def Res (v : BitVec 8) (r : BitVec 32) : Prop :=
  r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = expected v

/-! ## Steps that keep the coverage -/

section Steps

variable {A₀ : Nat} {g : Array Byte}

/-- A step of the session between `init` and `reset`: a triple `P c Q` for a part `P ∗ F` of the
current assertion, with the guard and the coverage carried over. -/
theorem tc_bind {α β : Type} {Cur P F : Assn} {c : MemM α} {Q : α → Assn} {f : α → MemM β}
    {Post : β → Assn} (hg : 0 < g.size) (ht : TotalTriple P c Q) (hpre : ∀ h, Cur h → (P ∗ F) h)
    (hk : ∀ v, TotalTriple (fun h => ((Q v ∗ F) ∗ guard A₀ g) h ∧ cov h) (f v) Post) :
    TotalTriple (fun h => (Cur ∗ guard A₀ g) h ∧ cov h) (c >>= f) Post := by
  refine TotalTriple.bind (TotalTriple.conseq (TotalTriple.covers (G := guard A₀ g) (b := 0)
    (S := 16) (lo := 0) (hi := 12) (TotalTriple.frame (R := F) ht)
    (fun h hr => regionIn_pins hr rfl hg) (by decide) (by simp)) (fun h ⟨hp, hc⟩ =>
      ⟨sep_mono hpre (fun _ x => x) hp, hc⟩) (fun _ _ x => x)) hk

theorem tc_pre {α : Type} {Cur Cur' : Assn} {c : MemM α} {Post : α → Assn}
    (hcur : ∀ h, Cur h → Cur' h)
    (ht : TotalTriple (fun h => (Cur' ∗ guard A₀ g) h ∧ cov h) c Post) :
    TotalTriple (fun h => (Cur ∗ guard A₀ g) h ∧ cov h) c Post :=
  TotalTriple.conseq ht (fun h ⟨hp, hc⟩ => ⟨sep_mono hcur (fun _ x => x) hp, hc⟩) (fun _ _ x => x)

theorem tc_pure {α : Type} {Cur : Assn} {c : MemM α} {Post : α → Assn} {φ : Prop}
    (hφ : ∀ h, Cur h → φ) (ht : φ → TotalTriple (fun h => (Cur ∗ guard A₀ g) h ∧ cov h) c Post) :
    TotalTriple (fun h => (Cur ∗ guard A₀ g) h ∧ cov h) c Post :=
  TotalTriple.of_pure (fun _ ⟨⟨h₁, _, _, _, hp, _⟩, _⟩ => hφ h₁ hp) ht

/-- Leave the session: drop the coverage. -/
theorem tc_exit {α : Type} {Cur : Assn} {c : MemM α} {Post : α → Assn}
    (ht : TotalTriple (Cur ∗ guard A₀ g) c Post) :
    TotalTriple (fun h => (Cur ∗ guard A₀ g) h ∧ cov h) c Post :=
  TotalTriple.conseq ht (fun _ ⟨hp, _⟩ => hp) (fun _ _ x => x)

end Steps

/-! ## Entry and exit -/

/-- The stack block of `fba`: a fresh block, so not the buffer's. -/
theorem alloc_fresh {P : Assn} (hP0 : ∀ h, P h → ∃ o c, h (0, o) = some c) :
    TotalTriple P (allocStack 24 8) (fun p => ⌜p.off = 0 ∧ p.block ≠ some 0⌝ ∗
      (P ∗ Assn.ex fun Ac => ⌜Ac % 8 = 0⌝ ∗ bytesAt p Ac 24 .stack (Array.replicate 24 .undef))) := by
  intro m hP hF hd hm hp hst
  obtain ⟨p, m', h', hr, h0, hd', hm', hdd, hst', -, A, hA, hb, -⟩ :=
    alloc_run hd hm .stack 24 8 (by decide) hst
  have hpe : p = ⟨some m.blocks.size, 0⟩ := by
    have e := hr.symm.trans (alloc_run_eq m .stack 24 8)
    simp only [pure, ExceptT.pure, ExceptT.mk] at e
    exact (Prod.mk.inj (Except.ok.inj (Option.some.inj e))).1
  obtain ⟨o, c, hc⟩ := hP0 hP hp
  have : m.heap (0, o) = some c := by rw [hm]; simp [hc]
  obtain ⟨blk, hblk, -⟩ := Mem.heap_some this
  have hpos : 0 < m.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
  have hne : m.blocks.size ≠ 0 := by omega
  refine ⟨p, m', hP ∪ h', hr, hd', hm', sep_lift.mpr ⟨⟨h0, ?_⟩, hP, h', hdd, rfl, hp, A,
    sep_lift.mpr ⟨hA, hb⟩⟩, hst'⟩
  rw [hpe]; intro e; exact hne (Option.some.inj e)

/-- The struct value `FixedBufferAllocator.init(buffer[0..12])`. -/
abbrev sv : heap_FixedBufferAllocator := ⟨0, ⟨bufp, 12⟩⟩

theorem slice_decode_encode (s : Slice) : Enc.decode (Enc.encode s) = (pure s : Result Slice) := by
  have hp : (Enc.encode s.ptr).size = 8 := LawfulEnc.size_encode s.ptr
  have hl : (Enc.encode s.len).size = 8 := LawfulEnc.size_encode s.len
  change (do pure ⟨← Enc.decode ((Enc.encode s.ptr ++ Enc.encode s.len).extract 0 8),
    ← Enc.decode ((Enc.encode s.ptr ++ Enc.encode s.len).extract 8 16)⟩ : Result Slice) = pure s
  have e1 : (Enc.encode s.ptr ++ Enc.encode s.len).extract 0 8 = Enc.encode s.ptr := by
    rw [← hp]; exact Region.extract_append_left _ _
  have e2 : (Enc.encode s.ptr ++ Enc.encode s.len).extract 8 16 = Enc.encode s.len := by
    have := Region.extract_append_right (Enc.encode s.ptr) (Enc.encode s.len)
    simpa [hp, hl] using this
  rw [e1, e2, LawfulEnc.decode_encode, LawfulEnc.decode_encode]
  rfl

theorem extract_writeBytes_lt (a bs : Array Byte) {o x n : Nat} (hn : x + n ≤ o)
    (h : o + bs.size ≤ a.size) : (writeBytes a o bs).extract x (x + n) = a.extract x (x + n) := by
  have hs := writeBytes_size a o bs h
  apply Array.ext
  · simp [hs]
  · intro i h1 h2
    simp only [Array.size_extract] at h1
    simp only [Array.getElem_extract]
    rw [writeBytes_getElem a o bs h _ (by omega), if_neg (by omega), getElem!_pos a _ (by omega)]

theorem enc_sv_eq : Enc.encode sv = writeBytes (writeBytes (Array.replicate 24 .undef) 0
    (Enc.encode (0 : BitVec 64))) 8 (Enc.encode (⟨bufp, 12⟩ : Slice)) := rfl

theorem enc_e_size : (Enc.encode (0 : BitVec 64)).size = 8 := LawfulEnc.size_encode _

theorem enc_s_size : (Enc.encode (⟨bufp, 12⟩ : Slice)).size = 16 := by
  show (Enc.encode bufp ++ Enc.encode (12 : BitVec 64)).size = 16
  rw [Array.size_append, LawfulEnc.size_encode, LawfulEnc.size_encode]; rfl

theorem enc_w1_size : (writeBytes (Array.replicate 24 .undef) 0 (Enc.encode (0 : BitVec 64))).size = 24 := by
  rw [writeBytes_size _ _ _ (by rw [enc_e_size] <;> simp)]; simp

theorem enc_sv_size : (Enc.encode sv).size = 24 := by
  rw [enc_sv_eq, writeBytes_size _ _ _ (by rw [enc_w1_size, enc_s_size] <;> omega), enc_w1_size]

theorem enc_sv_end : Enc.decode ((Enc.encode sv).extract 0 8) =
    (pure (BitVec.ofNat 64 0) : Result (BitVec 64)) := by
  rw [enc_sv_eq, show (8 : Nat) = 0 + 8 from rfl,
    extract_writeBytes_lt _ _ (Nat.le_refl _) (by rw [enc_w1_size, enc_s_size] <;> omega)]
  have := extract_writeBytes_in (Array.replicate 24 .undef) (Enc.encode (0 : BitVec 64)) 0 0 8
    (by rw [enc_e_size] <;> simp) (Nat.le_refl 0) (by rw [enc_e_size] <;> omega)
  simp only [Nat.zero_add, Nat.sub_self] at this
  rw [this, show (8 : Nat) = (Enc.encode (0 : BitVec 64)).size from enc_e_size.symm, Array.extract_size,
    LawfulEnc.decode_encode]
  rfl

theorem enc_sv_buf : Enc.decode ((Enc.encode sv).extract 8 24) =
    (pure (⟨bufp, BitVec.ofNat 64 12⟩ : Slice) : Result Slice) := by
  rw [enc_sv_eq]
  have := extract_writeBytes_in (writeBytes (Array.replicate 24 .undef) 0
    (Enc.encode (0 : BitVec 64))) (Enc.encode (⟨bufp, 12⟩ : Slice)) 8 8 16
    (by rw [enc_w1_size, enc_s_size] <;> omega) (Nat.le_refl 8) (by rw [enc_s_size] <;> omega)
  simp only [Nat.sub_self, Nat.zero_add, show (8 : Nat) + 16 = 24 from rfl] at this
  rw [this, show (16 : Nat) = (Enc.encode (⟨bufp, 12⟩ : Slice)).size from enc_s_size.symm,
    Array.extract_size, slice_decode_encode]
  rfl

/-- `fba = .init(buffer[0..12])`: the struct. -/
theorem store_struct {s1 : Ptr} {A₀ Ac : Nat} (h0 : s1.off = 0) (hAc : Ac % 8 = 0) :
    TotalTriple (bytesAt s1 Ac 24 .stack (Array.replicate 24 .undef)) (store 8 s1 sv)
      (fun _ => state s1 (buf A₀ Ac) 0) := by
  intro m hP hF hd hm hp hst
  obtain ⟨m', hrun, hst', h', hd', hm', hb'⟩ := bytesAt_store (q := s1) (k := 0) (a := 8)
    (bs' := Enc.encode sv) hp hm hd (by simp [Ptr.add]) (by rw [enc_sv_size]; decide)
    (by rw [enc_sv_size]; simp) (by rw [h0]; simpa using hAc) hst (by decide)
  rw [writeBytes_all (by rw [enc_sv_size]; simp)] at hb'
  refine ⟨(), m', h', hrun, hd', hm', ?_, hst'⟩
  have hsp := bytesAt_split hb' (k := 8) (by rw [enc_sv_size]; decide)
  rw [enc_sv_size] at hsp
  obtain ⟨g₁, g₂, hdg, rfl, hb₁, hb₂⟩ := hsp
  refine ⟨g₁, g₂, hdg, rfl, ⟨by simp [buf, h0, hAc], by simp [buf], _,
    by rw [Array.size_extract, enc_sv_size]; rfl, enc_sv_end, by simpa [buf] using hb₁⟩,
    ⟨?_, by simp [buf], _, by rw [Array.size_extract, enc_sv_size]; rfl, enc_sv_buf, ?_⟩⟩
  · simp [buf, Ptr.add, h0]; omega
  · simpa [Ptr.add, buf] using hb₂

/-- The buffer: `buffer[0..12]` for the allocator, `buffer[12]` its pin, `buffer[13..16]` the
client's. -/
theorem split_buffer {A₀ : Nat} {bs : Array Byte} {h : Heap} (hs : bs.size = 16)
    (hr : regionIn bufp A₀ 16 .global 1 bs h) :
    (regionIn bufp A₀ 16 .global 1 (bs.extract 0 12) ∗
      (regionIn pinp A₀ 16 .global 1 ((bs.extract 12 16).extract 0 1) ∗
        guard A₀ ((bs.extract 12 16).extract 1 ((bs.extract 12 16).size)))) h := by
  have h1 := Region.regionIn_split hr (k := 12) (a' := 1) (by omega) (Nat.mod_one _)
  rw [hs] at h1
  have e12 : bufp.add ((12 : Nat) : Int) = pinp := rfl
  rw [e12] at h1
  refine sep_mono (fun _ x => x) (fun _ x => ?_) h1
  have h2 := Region.regionIn_split x (k := 1) (a' := 1) (by simp [hs]) (Nat.mod_one _)
  have e13 : pinp.add ((1 : Nat) : Int) = guardp := rfl
  rw [e13] at h2
  exact h2

/-- Every buffer byte is in a heap that has the allocator's bytes `buffer[0..12]`. -/
theorem cov_of {A₀ : Nat} {bs : Array Byte} {R : Assn} {h : Heap} (hs : bs.size = 12)
    (hr : (regionIn bufp A₀ 16 .global 1 bs ∗ R) h) : cov h := by
  obtain ⟨h₁, h₂, -, rfl, ⟨-, -, b, hb, -, hl⟩, -⟩ := hr
  cases hb
  intro i _ hi
  have : h₁ (0, i) ≠ none := by rw [hl]; simp [hs]; omega
  simp only [Heap.union_apply]
  intro e
  rw [Option.or_eq_none_iff] at e
  exact this e.1

/-- Leave: free the struct's stack block and return `k`. -/
theorem exit_free {s1 : Ptr} {A₀ Ac : Nat} {X : Assn} {v : BitVec 8} (h0 : s1.off = 0) (k : BitVec 32)
    (hk : Res v k) :
    TotalTriple ((I s1 A₀ Ac).own ∗ X) (free s1 >>= fun _ => pure k)
      (fun r => ⌜Res v r⌝ ∗ junk) := by
  refine TotalTriple.conseq (P := Assn.ex fun bs : Array Byte => ⌜bs.size = 24⌝ ∗
    (bytesAt s1 Ac 24 .stack bs ∗ junk)) ?_ ?_ (fun _ _ x => x)
  · refine TotalTriple.ex fun bs => TotalTriple.lift fun hs => ?_
    refine TotalTriple.bind (free_whole hs h0 (by decide)) fun _ => ?_
    exact TotalTriple.conseq (TotalTriple.ret (Q := fun r => ⌜Res v r⌝ ∗ junk) k)
      (fun h _ => sep_lift.mpr ⟨hk, trivial⟩) (fun _ _ x => x)
  · intro h hp
    have hp0 : ((own s1 (buf A₀ Ac) ∗ vtR vtp fns) ∗ X) h := hp
    have hp' : ((((Assn.ex fun e => state s1 (buf A₀ Ac) e) ∗ junk) ∗ vtR vtp fns) ∗ X) h :=
      sep_mono (fun _ y => sep_mono (fun _ x => own_state x) (fun _ x => x) y) (fun _ x => x) hp0
    have hp'' : ((Assn.ex fun e => state s1 (buf A₀ Ac) e) ∗ junk) h :=
      sep_mono (fun _ x => x) (fun _ _ => trivial) (sep_assoc (sep_assoc hp'))
    obtain ⟨h₁, h₂, hd, rfl, ⟨e, hst⟩, -⟩ := hp''
    obtain ⟨bs, hs, hb⟩ := state_bytes hst
    exact ⟨bs, sep_lift.mpr ⟨hs, h₁, h₂, hd, rfl, hb, trivial⟩⟩

/-! ## Memory steps on granted regions -/

section Granted

variable {J : AllocInv} {p : Ptr} {k : Nat} {bs : Array Byte}

/-- `@memset` of a granted region with a defined byte. -/
theorem granted_memset (v : BitVec 8) {n : BitVec 64} (hn : n.toNat = bs.size) :
    TotalTriple (granted J p k bs) (memset (α := BitVec 8) 1 p n (some v))
      (fun _ => granted J p k (Array.replicate n.toNat (Enc.encode v)).flatten) := by
  have hs : ((Array.replicate n.toNat (Enc.encode v)).flatten).size = bs.size := by
    rw [Array.size_flatten_replicate, LawfulEnc.size_encode, show Enc.size (BitVec 8) = 1 from rfl,
      Nat.mul_one, hn]
  refine TotalTriple.ex fun A => TotalTriple.ex fun S => TotalTriple.ex fun K => ?_
  refine TotalTriple.conseq (TotalTriple.frame (R := J.tok p bs.size k A S K)
    (Region.memsetIn (some v) hn))
    (fun _ x => x) (fun _ h x => ⟨A, S, K, by rw [hs]; exact x⟩)

/-- The pointer to an item at most one past a nonempty granted region is formed (MM-3). -/
theorem granted_project (i : BitVec 64) (hpos : 0 < bs.size) (hi : i.toNat ≤ bs.size) :
    TotalTriple (granted J p k bs) (ptrProject p (·.elem 1 i))
      (fun q => ⌜q = p.elem 1 i⌝ ∗ granted J p k bs) := by
  refine TotalTriple.ex fun A => TotalTriple.ex fun S => TotalTriple.ex fun K => ?_
  refine TotalTriple.conseq (TotalTriple.frame (R := J.tok p bs.size k A S K)
    (ptrProject_elem_region (p := p) (A := A) (S := S) (K := K) (a := 2 ^ k) (size := 1) (i := i)
      hpos (by omega))) (fun _ x => x) (fun _ h x => ?_)
  obtain ⟨hr, x⟩ := sep_lift.mp (sep_assoc x)
  exact sep_lift.mpr ⟨hr, A, S, K, x⟩

/-- A store of an item into a granted region. -/
theorem granted_store {T : Type} [Enc T] [LawfulEnc T] {al : Nat} (w : T) (i : BitVec 64)
    (hpos : 0 < Enc.size T) (ho : i.toNat + Enc.size T ≤ bs.size) (hal : al ∣ 2 ^ k)
    (halo : al ∣ i.toNat) :
    TotalTriple (granted J p k bs) (store al (p.elem 1 i) w)
      (fun _ => granted J p k (writeBytes bs i.toNat (Enc.encode w))) := by
  have hs : (writeBytes bs i.toNat (Enc.encode w)).size = bs.size :=
    writeBytes_size _ _ _ (by rw [LawfulEnc.size_encode]; exact ho)
  rw [Ptr.elem_eq, Nat.one_mul]
  refine TotalTriple.ex fun A => TotalTriple.ex fun S => TotalTriple.ex fun K => ?_
  refine TotalTriple.conseq (TotalTriple.frame (R := J.tok p bs.size k A S K)
    (Region.storeItemIn (p := p) (A := A) (S := S) (K := K) (o := i.toNat) w hpos ho hal halo))
    (fun _ x => x) (fun _ h x => ⟨A, S, K, by rw [hs]; exact x⟩)

/-- A load of an item from a granted region. -/
theorem granted_load {T : Type} [Enc T] {al : Nat} {w : T} (i : BitVec 64)
    (hpos : 0 < Enc.size T) (ho : i.toNat + Enc.size T ≤ bs.size) (hal : al ∣ 2 ^ k)
    (halo : al ∣ i.toNat) (hv : Enc.decode (bs.extract i.toNat (i.toNat + Enc.size T)) = pure w) :
    TotalTriple (granted J p k bs) (load T al (p.elem 1 i)) (fun r => ⌜r = w⌝ ∗ granted J p k bs) := by
  rw [Ptr.elem_eq, Nat.one_mul]
  refine TotalTriple.ex fun A => TotalTriple.ex fun S => TotalTriple.ex fun K => ?_
  refine TotalTriple.conseq (TotalTriple.frame (R := J.tok p bs.size k A S K)
    (loadItemIn (p := p) (A := A) (S := S) (K := K) (o := i.toNat) hpos ho hal halo hv))
    (fun _ x => x) (fun _ h x => ?_)
  obtain ⟨hr, x⟩ := sep_lift.mp (sep_assoc x)
  exact sep_lift.mpr ⟨hr, A, S, K, x⟩

theorem granted_load0 {T : Type} [Enc T] {al : Nat} {w : T}
    (hpos : 0 < Enc.size T) (ho : Enc.size T ≤ bs.size) (hal : al ∣ 2 ^ k)
    (hv : Enc.decode (bs.extract 0 (Enc.size T)) = pure w) :
    TotalTriple (granted J p k bs) (load T al p) (fun r => ⌜r = w⌝ ∗ granted J p k bs) := by
  have t := granted_load (J := J) (p := p) (k := k) (bs := bs) (al := al) (w := w) 0 hpos
    (by simpa using ho) hal (Nat.dvd_zero _) (by simpa using hv)
  simpa [Ptr.elem, Ptr.add] using t

end Granted

/-! ## `reset` in the client -/

/-- At `reset`, the allocator's part of the heap has every byte of `buffer[0..12]`: the vtable is
another block and the client's bytes are `buffer[13..16]`. -/
theorem reset_step {s1 : Ptr} {A₀ Ac : Nat} {g : Array Byte} (hblk : s1.block ≠ some 0) :
    TotalTriple (fun h => ((I s1 A₀ Ac).own ∗ guard A₀ g) h ∧ cov h)
      (heap_FixedBufferAllocator_reset s1) (fun _ => (I s1 A₀ Ac).own ∗ guard A₀ g) := by
  have hr := TotalTriple.frame (R := vtR vtp fns ∗ guard A₀ g)
    (reset_spec s1 (buf A₀ Ac) (b := 0) rfl (by simpa [buf] using hblk))
  refine TotalTriple.conseq hr (fun h ⟨hp, hc⟩ => ?_) (fun _ h x => by
    show ((own s1 (buf A₀ Ac) ∗ vtR vtp fns) ∗ guard A₀ g) h; sep_from x)
  have hp' : (own s1 (buf A₀ Ac) ∗ (vtR vtp fns ∗ guard A₀ g)) h := by
    have : ((own s1 (buf A₀ Ac) ∗ vtR vtp fns) ∗ guard A₀ g) h := hp
    sep_from this
  obtain ⟨h₁, h₂, hd, rfl, ho, hrest⟩ := hp'
  refine ⟨h₁, h₂, hd, rfl, ⟨ho, fun i hlo hhi => ?_⟩, hrest⟩
  -- the rest has no cell of `buffer[0..12]`
  have hn : h₂ (0, i) = none := by
    obtain ⟨g₁, g₂, -, rfl, hv, ⟨-, -, b, hb, -, hl⟩⟩ := hrest
    cases hb
    have pn : ∀ {q : Ptr} {T : Type} [Enc T] {a : Nat} {w : T} {h : Heap}, ptsR q a w h →
        q.block = some 5 → h (0, i) = none := by
      intro q T _ a w h hq hb
      obtain ⟨_, _, _, _, _, _, _, b, hb', _, hl⟩ := hq
      rw [hb] at hb'; cases hb'; rw [hl]; simp
    have h1 : g₁ (0, i) = none := by
      unfold vtR at hv
      obtain ⟨v₁, v₂, -, rfl, p₁, v₃, v₄, -, rfl, p₂, v₅, v₆, -, rfl, p₃, p₄⟩ := hv
      simp [Heap.union_apply, pn p₁ rfl, pn p₂ rfl, pn p₃ rfl, pn p₄ rfl]
    have hhi' : i < 12 := by simpa [buf] using hhi
    have h2 : g₂ (0, i) = none := by rw [hl]; simp; omega
    simp [h1, h2]
  have := hc i hlo hhi
  simp only [Heap.union_apply, hn, Option.or_none] at this
  exact this

/-! ## Bytes and values -/

theorem decode_byte (v : BitVec 8) : Enc.decode (Enc.encode v) = (pure v : Result (BitVec 8)) :=
  LawfulEnc.decode_encode v

theorem byte_at (v : BitVec 8) (n j : Nat) (hj : j < n) :
    ((Array.replicate n (Enc.encode v)).flatten).extract j (j + 1) = Enc.encode v := by
  have := Array.extract_flatten_replicate (Enc.encode v) n j hj
  rwa [LawfulEnc.size_encode, show Enc.size (BitVec 8) = 1 from rfl, Nat.one_mul] at this

theorem intCast_byte (x : BitVec 8) : Zig.intCast false false 32 x = pure (BitVec.ofNat 32 x.toNat) := by
  have := x.isLt
  simp only [Zig.intCast, Zig.val, Bool.false_eq_true, ↓reduceIte]
  rw [if_pos (by constructor <;> simp <;> omega), BitVec.ofInt_natCast]

theorem add32 {a b : Nat} (ha : a < 512) (hb : b < 256) :
    Zig.add false (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = pure (BitVec.ofNat 32 (a + b)) := by
  simp only [Zig.add, BitVec.uaddOverflow, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by simp; omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega)]

/-! ## The client -/

theorem tc_ex {α γ : Type} {A₀ : Nat} {g : Array Byte} {P : γ → Assn} {c : MemM α}
    {Post : α → Assn}
    (ht : ∀ a, TotalTriple (fun h => (P a ∗ guard A₀ g) h ∧ cov h) c Post) :
    TotalTriple (fun h => (Assn.ex P ∗ guard A₀ g) h ∧ cov h) c Post := by
  rintro m hP hF hd hm ⟨⟨h₁, h₂, hd₁, rfl, ⟨a, hp⟩, hg⟩, hc⟩ hst
  exact ht a m _ hF hd hm ⟨⟨h₁, h₂, hd₁, rfl, hp, hg⟩, hc⟩ hst

theorem flat_size (n : Nat) (v : BitVec 8) : ((Array.replicate n (Enc.encode v)).flatten).size = n := by
  rw [Array.size_flatten_replicate, LawfulEnc.size_encode, show Enc.size (BitVec 8) = 1 from rfl,
    Nat.mul_one]

theorem fitsI {s1 : Ptr} {A₀ Ac n : Nat} (hn : n ≤ 64) : Wrap.Fits (I s1 A₀ Ac) n 0 := by
  intro _ _
  show 12 + 2 ^ 0 + n ≤ 2 ^ 64
  omega

/-- Leave with the code `k`: the client's other bytes are given up. -/
theorem leave {s1 : Ptr} {A₀ Ac : Nat} {g : Array Byte} {Cur : Assn} {v : BitVec 8} (h0 : s1.off = 0)
    (k : BitVec 32) (hk : Res v k) (hcur : ∀ h, Cur h → ((I s1 A₀ Ac).own ∗ junk) h) :
    TotalTriple (fun h => (Cur ∗ guard A₀ g) h ∧ cov h) (free s1 >>= fun _ => pure k)
      (fun r => ⌜Res v r⌝ ∗ junk) :=
  tc_exit (TotalTriple.conseq (exit_free (X := junk ∗ guard A₀ g) h0 k hk)
    (fun h hp => sep_assoc (sep_mono hcur (fun _ x => x) hp)) (fun _ _ x => x))

theorem prefix_byte {bs' bs4 : Array Byte} {j : Nat} (h : bs'.extract 0 4 = bs4) (hj : j + 1 ≤ 4) :
    bs'.extract j (j + 1) = bs4.extract j (j + 1) := by
  rw [← h, Array.extract_extract]; simp [Nat.min_eq_left hj]

theorem own_junk {J : AllocInv} {X : Assn} {h : Heap} (hp : (J.own ∗ X) h) : (J.own ∗ junk) h :=
  sep_mono (fun _ x => x) (fun _ _ => trivial) hp

abbrev g3 (bs : Array Byte) : Array Byte := (bs.extract 12 16).extract 1 ((bs.extract 12 16).size)

/-- Entry: the allocator is set up on `buffer[0..12]`, the client keeps `buffer[13..16]`, and
every byte of `buffer[0..12]` is in the heap. -/
theorem entry {s1 : Ptr} {A₀ Ac : Nat} {bs : Array Byte} {h : Heap} (hs : bs.size = 16)
    (hA : A₀ + 16 ≤ 2 ^ 64) (hblk : s1.block ≠ some 0)
    (hh : (state s1 (buf A₀ Ac) 0 ∗ (regionIn bufp A₀ 16 .global 1 bs ∗ vtR vtp fns)) h) :
    ((I s1 A₀ Ac).own ∗ guard A₀ (g3 bs)) h ∧ cov h := by
  have hsplit := sep_mono (fun _ x => x) (fun _ y => sep_mono (fun _ z => split_buffer hs z)
    (fun _ z => z) y) hh
  refine ⟨?_, ?_⟩
  · have h2 : ((state s1 (buf A₀ Ac) 0 ∗ (regionIn bufp A₀ 16 .global 1 (bs.extract 0 12) ∗
        regionIn pinp A₀ 16 .global 1 ((bs.extract 12 16).extract 0 1))) ∗
        (vtR vtp fns ∗ guard A₀ (g3 bs))) h := by sep_from hsplit
    have h3 := sep_mono (fun _ x => own_init (ctx := s1) (B := buf A₀ Ac) (by simp [hs, buf])
      (by simp [hs]) (by simp [buf]; omega) (by simp [buf]) rfl (by right; simp [buf])
      (by simp [buf]) x) (fun _ x => x) h2
    show ((own s1 (buf A₀ Ac) ∗ vtR vtp fns) ∗ guard A₀ (g3 bs)) h
    sep_from h3
  · have h2 : (regionIn bufp A₀ 16 .global 1 (bs.extract 0 12) ∗
        (state s1 (buf A₀ Ac) 0 ∗ (regionIn pinp A₀ 16 .global 1 ((bs.extract 12 16).extract 0 1) ∗
          (vtR vtp fns ∗ guard A₀ (g3 bs))))) h := by sep_from hsplit
    exact cov_of (by simp [hs]) h2

set_option maxHeartbeats 4000000 in
/-- **The client theorem.** -/
theorem client_spec (v : BitVec 8) (A₀ : Nat) (bs : Array Byte) (hs : bs.size = 16)
    (hA : A₀ + 16 ≤ 2 ^ 64) :
    TotalTriple (regionIn bufp A₀ 16 .global 1 bs ∗ vtR vtp fns) (fba_client v)
      (fun r => ⌜Res v r⌝ ∗ junk) := by
  simp only [fba_client, heap_FixedBufferAllocator_init, heap_FixedBufferAllocator_allocator,
    alloc_eq, realloc_eq, free_eq]
  gen_norm
  refine TotalTriple.bind (alloc_fresh fun h hp => ?_) fun s1 => ?_
  · obtain ⟨h₁, -, -, rfl, ⟨-, -, b, hb, -, hl⟩, -⟩ := hp
    cases hb
    exact ⟨0, ⟨bs[0]!, A₀, 16, .global⟩, by simp [hl, hs]⟩
  refine TotalTriple.lift fun ⟨h0, hblk⟩ => ?_
  refine TotalTriple.conseq (P := Assn.ex fun Ac => ⌜Ac % 8 = 0⌝ ∗
    (bytesAt s1 Ac 24 .stack (Array.replicate 24 .undef) ∗
      (regionIn bufp A₀ 16 .global 1 bs ∗ vtR vtp fns))) ?_ (fun h hp => ?_) (fun _ _ x => x)
  rotate_left
  · obtain ⟨h₁, h₂, hd, rfl, hp₁, Ac, hp₂⟩ := hp
    obtain ⟨hAc, hb⟩ := sep_lift.mp hp₂
    exact ⟨Ac, sep_lift.mpr ⟨hAc, h₂, h₁, hd.symm, Heap.union_comm hd, hb, hp₁⟩⟩
  refine TotalTriple.ex fun Ac => TotalTriple.lift fun hAc => ?_
  refine TotalTriple.bind (TotalTriple.frame (store_struct (A₀ := A₀) h0 hAc)) fun _ => ?_
  refine TotalTriple.conseq (P := fun h => ((I s1 A₀ Ac).own ∗ guard A₀ (g3 bs)) h ∧ cov h) ?_
    (fun h hp => entry hs hA hblk hp) (fun _ _ x => x)
  have hg : 0 < (g3 bs).size := by simp [g3, hs]
  -- `a.alloc(u8, 4)`
  refine tc_bind (Cur := (I s1 A₀ Ac).own) (F := emp) hg
    (Wrap.allocSlice_spec (spec s1 A₀ Ac) 1 0 4 (by decide) (by decide) (fitsI (by decide)))
    (fun h hp => sep_emp.mpr hp) fun r => ?_
  cases r with
  | error e =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Zig.unwrapErr, Norm.lift_pure,
      pure_bind]
    exact leave h0 1 (by simp [Res]) fun h hp => by
      simp only [Wrap.sliceResult] at hp
      obtain ⟨-, hp⟩ := sep_lift.mp (sep_assoc hp)
      exact own_junk (sep_mono (fun _ x => x) (fun _ _ => trivial) hp)
  | ok x =>
  simp only [Bool.not_false, ↓reduceIte, Zig.unwrapPayload, Norm.lift_pure, pure_bind]
  simp only [Wrap.sliceResult, Nat.one_mul]
  refine tc_pure (fun h hp => (sep_lift.mp (sep_assoc hp)).1) fun hx4 => ?_
  rw [Wrap.owned_pos (by simp)]
  -- `@memset(s, v)`
  refine tc_bind (P := granted (I s1 A₀ Ac) x.ptr 0 (Array.replicate 4 .undef))
    (F := (I s1 A₀ Ac).own) hg (granted_memset v (by rw [hx4]; simp))
    (fun h hp => by obtain ⟨-, hp⟩ := sep_lift.mp (sep_assoc hp); sep_from hp) fun _ => ?_
  rw [hx4]
  -- `a.realloc(s, 8)`
  refine tc_bind (P := (I s1 A₀ Ac).own ∗ Wrap.owned (I s1 A₀ Ac) 0 x.ptr
      (Array.replicate 4 (Enc.encode v)).flatten) (F := emp) hg
    (Wrap.realloc_spec (spec s1 A₀ Ac) 1 0 x 8 _ (by decide) (by decide) (by decide)
      (by rw [flat_size, hx4]; rfl) (by rw [flat_size]; decide) (fitsI (by decide))
      (grantSep' s1 A₀ Ac 0))
    (fun h hp => by
      rw [Wrap.owned_pos (by rw [flat_size]; decide)]
      refine sep_emp.mpr ?_
      simpa using (show ((I s1 A₀ Ac).own ∗ granted (I s1 A₀ Ac) x.ptr 0
        (Array.replicate (BitVec.toNat (4 : BitVec 64)) (Enc.encode v)).flatten) h by sep_from hp)) fun r => ?_
  cases r with
  | error e =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Zig.unwrapErr, Norm.lift_pure,
      pure_bind]
    exact leave h0 2 (by simp [Res]) fun h hp => by
      simp only [Wrap.reallocResult] at hp
      obtain ⟨-, hp⟩ := sep_lift.mp (sep_assoc hp)
      exact own_junk (sep_mono (fun _ x => x) (fun _ _ => trivial) (sep_assoc hp))
  | ok t =>
  simp only [Bool.not_false, ↓reduceIte, Zig.unwrapPayload, Norm.lift_pure, pure_bind]
  let J := I s1 A₀ Ac
  let bs4 := (Array.replicate 4 (Enc.encode v)).flatten
  simp only [Wrap.reallocResult, Nat.one_mul]
  refine tc_pure (fun h hp => (sep_lift.mp (sep_assoc hp)).1) fun ht8 => ?_
  refine tc_pre (Cur' := Assn.ex fun bs' : Array Byte => ⌜bs'.size = 8 ∧ keepsPrefix bs4 bs'⌝ ∗
      (J.own ∗ granted J t.ptr 0 bs')) (fun h hp => ?_) ?_
  · obtain ⟨-, hp⟩ := sep_lift.mp (sep_assoc hp)
    obtain ⟨bs', hp⟩ := sep_ex_right.mp (sep_emp.mp hp)
    obtain ⟨hf, hp⟩ := sep_lift_right.mp hp
    refine ⟨bs', sep_lift.mpr ⟨hf, ?_⟩⟩
    rw [Wrap.owned_pos (by have := hf.1; simp at this; omega)] at hp
    exact hp
  refine tc_ex fun bs' => tc_pure (fun h hp => (sep_lift.mp hp).1) fun ⟨hb8, hkp⟩ => ?_
  refine tc_pre (Cur' := J.own ∗ granted J t.ptr 0 bs') (fun h hp => (sep_lift.mp hp).2) ?_
  have hpre4 : bs'.extract 0 4 = bs4 := by
    have := hkp; unfold keepsPrefix at this
    rw [flat_size, hb8] at this
    rw [this]; exact Array.extract_eq_self_of_le (by show bs4.size ≤ 8; simp only [bs4, flat_size]; decide)
  rw [ht8, if_pos (by decide)]
  -- `t[7] = v +% 1`
  refine tc_bind (P := granted J t.ptr 0 bs') (F := J.own) hg
    (granted_project 7 (by rw [hb8]; decide) (by rw [hb8]; decide))
    (fun h hp => sep_comm hp) fun q => tc_pure (fun h hp => (sep_lift.mp (sep_assoc hp)).1) fun hq => ?_
  subst hq
  refine tc_bind (P := granted J t.ptr 0 bs') (F := J.own) hg
    (granted_store (Zig.addWrap v 1) 7 (by decide) (by rw [hb8]; decide) (Nat.one_dvd _)
      (Nat.one_dvd _)) (fun h hp => by obtain ⟨-, hp⟩ := sep_lift.mp (sep_assoc hp); exact hp)
    fun _ => ?_
  rw [show (7 : BitVec 64).toNat = 7 from rfl]
  have hw : (Enc.encode (Zig.addWrap v 1)).size = 1 := LawfulEnc.size_encode (Zig.addWrap v 1)
  have hb2 : (writeBytes bs' 7 (Enc.encode (Zig.addWrap v 1))).size = 8 := by
    rw [writeBytes_size _ _ _ (by rw [hw, hb8] <;> omega), hb8]
  have hv0 : (writeBytes bs' 7 (Enc.encode (Zig.addWrap v 1))).extract 0 1 = Enc.encode v := by
    rw [show (1 : Nat) = 0 + 1 from rfl, extract_writeBytes_lt _ _ (by decide) (by rw [hw, hb8] <;> omega),
      prefix_byte hpre4 (by decide)]
    exact byte_at v 4 0 (by decide)
  have hv3 : (writeBytes bs' 7 (Enc.encode (Zig.addWrap v 1))).extract 3 4 = Enc.encode v := by
    rw [show (4 : Nat) = 3 + 1 from rfl, extract_writeBytes_lt _ _ (by decide) (by rw [hw, hb8] <;> omega),
      prefix_byte hpre4 (by decide)]
    exact byte_at v 4 3 (by decide)
  have hv7 : (writeBytes bs' 7 (Enc.encode (Zig.addWrap v 1))).extract 7 8 =
      Enc.encode (Zig.addWrap v 1) := by
    have := extract_writeBytes_in bs' (Enc.encode (Zig.addWrap v 1)) 7 7 1
      (by rw [hw, hb8] <;> omega) (Nat.le_refl 7) (by rw [hw] <;> omega)
    rw [show (7 : Nat) + 1 = 8 from rfl, Nat.sub_self, Nat.zero_add] at this
    rw [this, show (1 : Nat) = (Enc.encode (Zig.addWrap v 1)).size from hw.symm, Array.extract_size]
  generalize writeBytes bs' 7 (Enc.encode (Zig.addWrap v 1)) = b2 at hb2 hv0 hv3 hv7 ⊢
  -- `a.alloc(u8, 64)`: out of memory for this buffer, but the specification allows both
  refine tc_bind (P := J.own) (F := granted J t.ptr 0 b2) hg
    (Wrap.allocSlice_spec (spec s1 A₀ Ac) 1 0 64 (by decide) (by decide) (fitsI (by decide)))
    (fun h hp => sep_comm hp) fun r => ?_
  cases r with
  | ok big =>
    simp only [Bool.not_false, ↓reduceIte, Norm.lift_pure, pure_bind]
    simp only [Wrap.sliceResult, Nat.one_mul]
    refine tc_pure (fun h hp => (sep_lift.mp (sep_assoc hp)).1) fun hbig => ?_
    refine tc_bind (P := J.own ∗ Wrap.owned J 0 big.ptr (Array.replicate 64 .undef))
      (F := granted J t.ptr 0 b2) hg
      (Wrap.free_spec (spec s1 A₀ Ac) 1 0 big _ (by decide) (by rw [hbig]; rfl) (by decide))
      (fun h hp => (sep_lift.mp (sep_assoc hp)).2) fun _ => ?_
    exact leave h0 3 (by simp [Res]) fun h hp => own_junk (sep_mono (fun _ x => x)
      (fun _ _ => trivial) hp)
  | error e =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Zig.unwrapErr, Norm.lift_pure,
    pure_bind]
  refine tc_pre (Cur' := J.own ∗ granted J t.ptr 0 b2) (fun h hp => by
    simp only [Wrap.sliceResult] at hp
    obtain ⟨-, hp⟩ := sep_lift.mp (sep_assoc hp)
    exact hp) ?_
  rw [if_pos (by decide), checkIndex_bind_of_lt (by rw [ht8]; decide)]
  refine tc_bind (P := granted J t.ptr 0 b2) (F := J.own) hg
    (granted_load0 (w := v) (al := 1) (by decide) (by rw [hb2]; decide) (Nat.one_dvd _)
      (by rw [show Enc.size (BitVec 8) = 1 from rfl, hv0]; exact decode_byte v))
    (fun h hp => sep_comm hp) fun x₀ => tc_pure (fun h hp => (sep_lift.mp (sep_assoc hp)).1)
      fun hx₀ => ?_
  subst x₀
  rw [intCast_byte, Norm.lift_pure, pure_bind, if_pos (by decide), checkIndex_bind_of_lt (by rw [ht8]; decide)]
  refine tc_bind (P := granted J t.ptr 0 b2) (F := J.own) hg
    (granted_load (w := v) (al := 1) 3 (by decide) (by rw [hb2]; decide) (Nat.one_dvd _)
      (Nat.one_dvd _) (by rw [show Enc.size (BitVec 8) = 1 from rfl]; exact hv3 ▸ decode_byte v))
    (fun h hp => by obtain ⟨-, hp⟩ := sep_lift.mp (sep_assoc hp); exact hp) fun x₃ =>
      tc_pure (fun h hp => (sep_lift.mp (sep_assoc hp)).1) fun hx₃ => ?_
  subst x₃
  rw [intCast_byte, Norm.lift_pure, pure_bind, add32 (by have := v.isLt; omega) v.isLt,
    Norm.lift_pure, pure_bind, if_pos (by decide), checkIndex_bind_of_lt (by rw [ht8]; decide)]
  refine tc_bind (P := granted J t.ptr 0 b2) (F := J.own) hg
    (granted_load (w := Zig.addWrap v 1) (al := 1) 7 (by decide) (by rw [hb2]; decide)
      (Nat.one_dvd _) (Nat.one_dvd _)
      (by rw [show Enc.size (BitVec 8) = 1 from rfl]; exact hv7 ▸ decode_byte _))
    (fun h hp => by obtain ⟨-, hp⟩ := sep_lift.mp (sep_assoc hp); exact hp) fun x₇ =>
      tc_pure (fun h hp => (sep_lift.mp (sep_assoc hp)).1) fun hx₇ => ?_
  subst x₇
  rw [intCast_byte, Norm.lift_pure, pure_bind,
    add32 (by have := v.isLt; omega) (Zig.addWrap v 1).isLt, Norm.lift_pure, pure_bind]
  -- `a.free(t)`
  refine tc_bind (P := J.own ∗ Wrap.owned J 0 t.ptr b2) (F := emp) hg
    (Wrap.free_spec (spec s1 A₀ Ac) 1 0 t b2 (by decide) (by rw [hb2, ht8]; rfl)
      (by rw [hb2]; decide))
    (fun h hp => by
      obtain ⟨-, hp⟩ := sep_lift.mp (sep_assoc hp)
      rw [Wrap.owned_pos (by rw [hb2]; decide)]
      exact sep_emp.mpr (sep_comm hp)) fun _ => ?_
  -- `fba.reset()`
  refine TotalTriple.bind (TotalTriple.conseq (reset_step (A₀ := A₀) (Ac := Ac) (g := g3 bs) hblk)
    (fun h ⟨hp, hc⟩ => ⟨sep_mono (fun _ x => sep_emp.mp x) (fun _ x => x) hp, hc⟩)
    (fun _ _ x => x)) fun _ => ?_
  -- `a.alloc(u8, 12)` after the reset
  refine TotalTriple.bind (TotalTriple.frame (R := guard A₀ (g3 bs))
    (Wrap.allocSlice_spec (spec s1 A₀ Ac) 1 0 12 (by decide) (by decide) (fitsI (by decide))))
    fun r => ?_
  have hexit : ∀ (k : BitVec 32), Res v k → ∀ X : Assn,
      TotalTriple ((J.own ∗ X) ∗ guard A₀ (g3 bs)) (free s1 >>= fun _ => pure k)
        (fun r => ⌜Res v r⌝ ∗ junk) := fun k hk X =>
    TotalTriple.conseq (exit_free (X := junk) h0 k hk) (fun h hp => own_junk (sep_assoc hp))
      (fun _ _ x => x)
  cases r with
  | error e =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Norm.lift_pure, pure_bind]
    refine TotalTriple.conseq (hexit 4 (by simp [Res]) emp) (fun h hp => ?_) (fun _ _ x => x)
    simp only [Wrap.sliceResult] at hp
    obtain ⟨h₁, h₂, hd, rfl, hp₁, hg'⟩ := hp
    exact ⟨h₁, h₂, hd, rfl, sep_emp.mpr (sep_lift.mp hp₁).2, hg'⟩
  | ok u =>
  simp only [Bool.not_false, ↓reduceIte, Norm.lift_pure, pure_bind]
  simp only [Wrap.sliceResult, Nat.one_mul]
  refine TotalTriple.of_pure (fun h hp => by
    obtain ⟨h₁, -, -, -, hp₁, -⟩ := hp; exact (sep_lift.mp hp₁).1) fun hu => ?_
  rw [hu, if_pos (by decide), Wrap.owned_pos (by simp)]
  refine TotalTriple.conseq (P := granted J u.ptr 0 (Array.replicate 12 .undef) ∗
    (J.own ∗ guard A₀ (g3 bs))) ?_ (fun h hp => by
      obtain ⟨h₁, h₂, hd, rfl, hp₁, hg'⟩ := hp
      have hp₂ : ((J.own ∗ granted J u.ptr 0 (Array.replicate 12 .undef)) ∗ guard A₀ (g3 bs))
          (h₁ ∪ h₂) := ⟨h₁, h₂, hd, rfl, (sep_lift.mp hp₁).2, hg'⟩
      sep_from hp₂) (fun _ _ x => x)
  refine TotalTriple.bind (TotalTriple.frame (granted_project (J := J) (p := u.ptr) (k := 0) 11
    (by simp) (by simp))) fun q => ?_
  refine TotalTriple.conseq (P := ⌜q = u.ptr.elem 1 11⌝ ∗ (granted J u.ptr 0 (Array.replicate 12 .undef) ∗
    (J.own ∗ guard A₀ (g3 bs)))) ?_ (fun h hp => sep_assoc hp) (fun _ _ x => x)
  refine TotalTriple.lift fun hq => ?_
  subst hq
  refine TotalTriple.bind (TotalTriple.frame (granted_store (J := J) v 11 (by decide)
    (by rw [Array.size_replicate]; decide) (Nat.one_dvd _) (Nat.one_dvd _))) fun _ => ?_
  rw [if_pos (by decide), show (11 : BitVec 64).toNat = 11 from rfl, checkIndex_bind_of_lt (by rw [hu]; decide)]
  have hw : (Enc.encode v).size = 1 := LawfulEnc.size_encode v
  have hv11 : (writeBytes (Array.replicate 12 .undef) 11 (Enc.encode v)).extract 11 12 =
      Enc.encode v := by
    have := extract_writeBytes_in (Array.replicate 12 .undef) (Enc.encode v) 11 11 1
      (by rw [hw] <;> simp) (Nat.le_refl 11) (by rw [hw] <;> omega)
    rw [show (11 : Nat) + 1 = 12 from rfl, Nat.sub_self, Nat.zero_add] at this
    rw [this, show (1 : Nat) = (Enc.encode v).size from hw.symm, Array.extract_size]
  have hsz : (writeBytes (Array.replicate 12 .undef) 11 (Enc.encode v)).size = 12 := by
    rw [writeBytes_size _ _ _ (by rw [hw] <;> simp)]; simp
  generalize writeBytes (Array.replicate 12 .undef) 11 (Enc.encode v) = b3 at hv11 hsz ⊢
  refine TotalTriple.bind (TotalTriple.frame (granted_load (J := J) (w := v) (al := 1) 11
    (by decide) (by rw [hsz]; decide) (Nat.one_dvd _) (Nat.one_dvd _)
    (by rw [show Enc.size (BitVec 8) = 1 from rfl]; exact hv11 ▸ decode_byte v))) fun x₁₁ => ?_
  refine TotalTriple.conseq (P := ⌜x₁₁ = v⌝ ∗ (granted J u.ptr 0 b3 ∗ (J.own ∗ guard A₀ (g3 bs))))
    ?_ (fun h hp => sep_assoc hp) (fun _ _ x => x)
  refine TotalTriple.lift fun hx => ?_
  subst x₁₁
  -- `buffer[15] = u[11]`: the client's own byte
  have hgs : (g3 bs).size = 3 := by simp [g3, hs]
  rw [show (⟨some 0, 15⟩ : Ptr) = guardp.add ((2 : Nat) : Int) from rfl]
  refine TotalTriple.bind (TotalTriple.conseq (TotalTriple.frame
      (R := granted J u.ptr 0 b3 ∗ J.own)
      (Region.storeItemIn (p := guardp) (A := A₀) (S := 16) (K := .global) (a := 1)
        (bs := g3 bs) (o := 2) (al := 1) v (by decide) (by rw [hgs]; decide) (Nat.one_dvd _)
        (Nat.one_dvd _)))
    (fun h hp => by unfold guard at hp; sep_from hp) (fun _ _ x => x)) fun _ => ?_
  -- `a.free(u)`
  refine TotalTriple.bind (TotalTriple.conseq (TotalTriple.frame
      (R := regionIn guardp A₀ 16 .global 1 (writeBytes (g3 bs) 2 (Enc.encode v)))
      (Wrap.free_spec (spec s1 A₀ Ac) 1 0 u b3 (by decide) (by rw [hsz, hu]; rfl)
        (by rw [hsz]; decide)))
    (fun h hp => by rw [Wrap.owned_pos (by rw [hsz]; decide)]; sep_from hp)
    (fun _ _ x => x)) fun _ => ?_
  have hres : Res v (BitVec.ofNat 32 (v.toNat + v.toNat + (Zig.addWrap v 1).toNat)) := by
    right; right; right; right; rfl
  exact TotalTriple.conseq (exit_free (X := junk) h0 _ hres) (fun h hp => own_junk hp)
    (fun _ _ x => x)

end AllocFba.Client
