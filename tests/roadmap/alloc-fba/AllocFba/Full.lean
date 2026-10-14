import AllocFba.Fba
import ZigLean.Sep.Full.AutoClaims
import ZigLean.Sep.Full.ResetLedger

/-!
# The translated `FixedBufferAllocator` satisfies the full-state `FAllocSpec`

`FBA.fallocSpec`: the four vtable entries of the translated `FixedBufferAllocator` (`Gen.lean`)
satisfy `FAllocSpec FLogic.total impl ctx (finv ctx B γ e)` for every allocator struct `ctx`, every
buffer `B` and every epoch `e` of a ledger `γ`, proved natively in the full-state logic
(`ZigLean/Sep/Full`) from the generated code; `FBA.reset_spec`: `reset` takes the whole epoch token
and gives the next epoch's back. The fixed buffer is the second instance of the reset ledger
(`ZigLean/Sep/Full/ResetLedger.lean`, `FBA.ledger`; the arena is the first): `reset` makes the whole
buffer free again, so a client that kept a grant would get its bytes twice, and the whole epoch
token, which every outstanding grant holds a part of, is the evidence that none is out.

* The invariant `fown ctx B γ e` owns the struct (`end_index = ei` and the buffer slice, as two
  typed words), the free tail `[ei, cap)` of the buffer, the junk (padding and the bytes of non-last
  frees) as the heap `jh` (`JunkAt`), the knowledge of the addresses of the buffer's and the
  struct's blocks, and a share `bshare b q (ptr.off + cap)` of the buffer block's extent: the block
  reaches the buffer's end even when every byte of the buffer is lent out, so `buffer.ptr +
  end_index` is formed (`ptrProject`, MM-3). A share, not the full extent: the buffer may itself lie
  in a grant of another allocator.
* The ledger: the authority `gauthP γ e M none` over the grant map `M` and the receipts with the
  grants' fees (`LedgerRcpts`). A grant's share is half of the invariant's, lent at the grant's end
  and tagged with the epoch (`ledger_issue`); `free` gives it back against its receipt
  (`ledger_return`), `resize` shrinks or re-lends it (`ledger_shrink`, `ledger_regrow`).
* Claims: the buffer's claim was lent at the epoch's start (the receipt `frcpt`); the invariant
  holds the tagged claim on the free tail `[ei, cap)` (`fclaim`); a grant gets the claim on its bytes
  carved from it, a `free` or shrink of the last grant joins it back, other frees drop it.
* Coverage (`fcov`, kept opaque by `fsym`): every byte of `[0, ei)` of the buffer is junk or a
  grant's, and the junk's cells have the buffer's labels. With no grant (the whole epoch token) the
  junk is the whole used part, and `reset` turns it back into the buffer (`EUpd.junkRegionLab`).
* The token of a grant names it in the ledger (`ledgerTok`) and says that it lies in the buffer,
  with the buffer's address and its cells' labels `S`, `K` (a full-state cell's size is a label:
  `FMatch` ignores it).

`fits n k := cap + 2^k + n ≤ 2^64`, as in the legacy proof.

**The proofs are the invariant, the general symbolic executor `fsym`**
(`ZigLean/Sep/Full/Auto.lean`, `docs/proof-automation.md`) **and the updates of the state at the
returns** (`fsym [u]`): each entry is `fsym` on its `FAllocSpec` field, which walks the generated
code with the library's step rules and plans the returns (carving and joining regions and claims);
a return that changes the ledger or the junk is closed by the update of its branch
(`alloc_upd`, `free_last_upd`, …), plain lemmas over the invariant built from the library's ledger
updates. `resize` is the refined field (`FAllocInv.held`/`relBytes`/`rresizePost`); `remap` is
`resize`'s whole-region form (`FAllocInv.resize_granted_of`) and a pointer.
-/

namespace AllocFba

open Zig Zig.Full Zig.Full.FAssn Gen

namespace FBA

/-! ## The invariant -/

/-- The buffer: its pointer and length, the address of its block, the size and kind labels of
its region cells, and the address of the struct's block. -/
structure FBuf where
  ptr : Ptr
  cap : Nat
  A : Nat
  S : Nat
  K : BlockKind
  cA : Nat

/-- The struct word `end_index = ei`. -/
def wEnd (ctx : Ptr) (ei : Nat) : FAssn := up (pts ctx 8 (BitVec.ofNat 64 ei))

/-- The struct's buffer slice. -/
def wBuf (ctx : Ptr) (B : FBuf) : FAssn := up (pts (ctx.add 8) 8 (⟨B.ptr, BitVec.ofNat 64 B.cap⟩ : Slice))

/-- The buffer's bound: its block reaches the buffer's end. -/
def bnd (B : FBuf) : Nat := B.ptr.off.toNat + B.cap

def FOk (ctx : Ptr) (B : FBuf) (ei : Nat) (tail : Array Byte) : Prop :=
  ei ≤ B.cap ∧ tail.size = B.cap - ei ∧ B.A + B.ptr.off.toNat + B.cap < 2 ^ 64 ∧ 0 ≤ B.ptr.off ∧
    (B.cA + ctx.off.toNat) % 8 = 0 ∧ 0 ≤ ctx.off

/-- The parts of the invariant that no entry changes: the buffer slice, the knowledge of the two
blocks' addresses, the extent share of the buffer's block. -/
def fparts (ctx : Ptr) (B : FBuf) (q : Frac) (b cb : BlockId) : FAssn :=
  wBuf ctx B ⋆ (known cb B.cA ⋆ (known b B.A ⋆ bshare b q (bnd B)))

/-- The free tail `[ei, cap)` of the buffer. -/
def ftail (B : FBuf) (ei : Nat) (tail : Array Byte) : FAssn :=
  up (regionIn (B.ptr.add (ei : Int)) B.A B.S B.K 1 tail)

/-- The claim on the free tail, tagged with the epoch: a grant carved from the tail gets the claim
on its bytes. -/
def fclaim (B : FBuf) (ei : Nat) (b : BlockId) (γ e : Nat) : FAssn :=
  bclaim b (B.ptr.off.toNat + ei) (bnd B) (some (γ, e))

/-- The receipt for the buffer's claim, lent at the epoch's start. -/
def frcpt (B : FBuf) (b : BlockId) (γ e : Nat) : FAssn :=
  bcrcpt b B.ptr.off.toNat (bnd B) γ e

/-- **Coverage**: the grant ids from `mN` on are unused, every byte of the used part `[0, ei)`
of the buffer is junk or a grant's, and the junk's cells record the buffer's address and kind. -/
structure FCov (B : FBuf) (b : BlockId) (ei mN : Nat) (M : GMap) (jh : Heap) : Prop where
  bound : ∀ i, mN ≤ i → M i = none
  cov : ∀ x, B.ptr.off.toNat ≤ x → x < B.ptr.off.toNat + ei → jh (b, x) ≠ none ∨ ∃ i, GrantHas b x (M i)
  lab : ∀ l c, jh l = some c → c.addr = B.A ∧ c.kind.norm = B.K.norm

/-- The coverage as an assertion, which `fsym` keeps opaque: the updates of the returns read and
re-establish it. -/
def fcov (B : FBuf) (b : BlockId) (ei mN : Nat) (M : GMap) (jh : Heap) : FAssn := ⟪FCov B b ei mN M jh⟫

-- an atom of `fsym` (not unfolded into a fact of the walk's context)
attribute [fsym_atom] fcov

/-- The facts of the variables. -/
def FFacts (ctx : Ptr) (B : FBuf) (ei : Nat) (tail : Array Byte) (b cb : BlockId) : Prop :=
  FOk ctx B ei tail ∧ B.ptr.block = some b ∧ ctx.block = some cb

/-- The allocator's state at epoch `e` of the ledger `γ` (module doc): the ledger, the struct with
`end_index = ei`, the parts no entry changes, the tail and its claim, the receipt of the buffer's
claim, the junk and the coverage. (The parts are written out here, not behind a definition: an
update that produces one of them, `fparts`, closes it in the postcondition as it stands.) -/
def fown (ctx : Ptr) (B : FBuf) (γ e : Nat) : FAssn :=
  FAssn.ex fun ei => FAssn.ex fun tail => FAssn.ex fun q => FAssn.ex fun b => FAssn.ex fun cb =>
    FAssn.ex fun mN => FAssn.ex fun M => FAssn.ex fun jh =>
      ⟪FFacts ctx B ei tail b cb⟫ ⋆
        ((gauthP γ e M none ⋆ LedgerRcpts γ e M) ⋆ ((wEnd ctx ei ⋆ fparts ctx B q b cb) ⋆
          ((ftail B ei tail ⋆ fclaim B ei b γ e) ⋆ (frcpt B b γ e ⋆ (JunkAt jh ⋆ fcov B b ei mN M jh)))))

/-- What a grant's token says besides naming the grant: it lies in the buffer, with the buffer's
address and labels. -/
def FTok (B : FBuf) (p : Ptr) (n _k A S : Nat) (K : BlockKind) (_q _φ : Frac) : Prop :=
  p.block = B.ptr.block ∧ A = B.A ∧ S = B.S ∧ K = B.K ∧ B.ptr.off ≤ p.off ∧
    p.off + n ≤ B.ptr.off + B.cap

def ffits (B : FBuf) (n k : Nat) : Prop := B.cap + 2 ^ k + n ≤ 2 ^ 64

/-- The fixed buffer's invariant at epoch `e` of the ledger `γ`: the token of a grant names it in
the ledger (`ledgerTok`) with `FTok`, the fee is a nonzero part of the epoch token (`epFee`), the
grants' shares are tagged with the epoch, and the state holds the ledger, so it witnesses the tag
(`act`; the ledger has no parent: the buffer's own share is untagged). -/
def finv (ctx : Ptr) (B : FBuf) (γ e : Nat) : FAllocInv where
  own := fown ctx B γ e
  tok p n k A S K q φ := ledgerTok γ e p n k A S K q φ ⋆ ⟪FTok B p n k A S K q φ⟫
  fee := epFee γ e
  fits := ffits B
  tag := some (γ, e)
  act r h := by
    obtain ⟨_, _, _, _, _, _, _, _, h⟩ := h
    obtain ⟨-, h⟩ := sep_lift.mp h
    exact act_gauthP (by within) h Act.root
  fee_add _ _ ha hb := epFee_add γ e ha hb

@[simp] theorem finv_tag (ctx : Ptr) (B : FBuf) (γ e : Nat) : (finv ctx B γ e).tag = some (γ, e) := rfl

@[simp] theorem finv_fee (ctx : Ptr) (B : FBuf) (γ e : Nat) (φ : Frac) :
    (finv ctx B γ e).fee φ = epFee γ e φ := rfl

/-- A fixed buffer takes every request up to `n` bytes when its capacity leaves room for them
(`FAllocInv.FitsUpTo`; the arena's child at `n = 2 ^ 63`, `k = 3`: `cap ≤ 2 ^ 63 - 8`). -/
theorem finv_fitsUpTo {ctx : Ptr} {B : FBuf} {γ e n k : Nat} (h : B.cap + 2 ^ k + n ≤ 2 ^ 64) :
    (finv ctx B γ e).FitsUpTo n k :=
  fun m hm => show B.cap + 2 ^ k + m ≤ 2 ^ 64 by omega

/-! ## The updates of the returns -/

/-- The coverage after a grant `g` of the bytes `[w - n, w)` under the fresh id `mN`, with the
padding `[ei, w - n)` in the junk. -/
theorem FCov.alloc {B : FBuf} {b : BlockId} {ei mN w n : Nat} {M : GMap} {jh jh' : Heap}
    {g : GRegion} (hc : FCov B b ei mN M jh) (hb : B.ptr.block = some b)
    (hg : JunkGrew B.ptr ei (w - n) jh jh') (hf : JunkFrom B.A B.K jh jh')
    (hG : ∀ x, B.ptr.off.toNat + (w - n) ≤ x → x < B.ptr.off.toNat + w → GrantHas b x (some g)) :
    FCov B b w (mN + 1) (M.set mN (some g)) jh' where
  bound i hi := by rw [GMap.set_ne _ _ (by omega)]; exact hc.bound i (by omega)
  cov x h1 h2 := by
    by_cases hx : x < B.ptr.off.toNat + ei
    · rcases hc.cov x h1 hx with hj | ⟨i, hi⟩
      · exact Or.inl (hg.1 _ hj)
      · have hne : i ≠ mN := fun e => by subst e; rw [hc.bound _ (Nat.le_refl _)] at hi; exact hi
        exact Or.inr ⟨i, by rwa [GMap.set_ne _ _ hne]⟩
    · by_cases hx2 : x < B.ptr.off.toNat + (w - n)
      · exact Or.inl (hg.2 b x hb (by omega) hx2)
      · exact Or.inr ⟨mN, by rw [GMap.set_same]; exact hG x (by omega) h2⟩
  lab l c h := by
    rcases hf l c h with h | ⟨h1, h2⟩
    · exact hc.lab l c h
    · exact ⟨h1, by rw [h2]⟩

/-- The coverage after the grant `i` (`g`) is retired (`v = none`) or re-pointed (`v = some g'`)
and the used part ends at `w`: a byte of the old grant below `w` is junk now or the new grant's,
and the bytes past the old end `ei` are the new grant's. -/
theorem FCov.set {B : FBuf} {b : BlockId} {ei w mN i : Nat} {M : GMap} {jh jh' : Heap} {g : GRegion}
    {v : Option GRegion} (hc : FCov B b ei mN M jh) (hM : M i = some g)
    (hjh : ∀ l, jh l ≠ none → jh' l ≠ none) (hf : JunkFrom B.A B.K jh jh')
    (hold : ∀ x, x < B.ptr.off.toNat + w → GrantHas b x (some g) → jh' (b, x) ≠ none ∨ GrantHas b x v)
    (hnew : ∀ x, B.ptr.off.toNat + ei ≤ x → x < B.ptr.off.toNat + w → GrantHas b x v) :
    FCov B b w mN (M.set i v) jh' where
  bound j hj := by
    have hne : j ≠ i := fun e => by subst e; rw [hc.bound _ hj] at hM; cases hM
    rw [GMap.set_ne _ _ hne]; exact hc.bound j hj
  cov x h1 h2 := by
    by_cases hx : x < B.ptr.off.toNat + ei
    · rcases hc.cov x h1 hx with hj | ⟨j, hj⟩
      · exact Or.inl (hjh _ hj)
      · by_cases e : j = i
        · subst e; rw [hM] at hj
          rcases hold x h2 hj with h | h
          · exact Or.inl h
          · exact Or.inr ⟨j, by rw [GMap.set_same]; exact h⟩
        · exact Or.inr ⟨j, by rwa [GMap.set_ne _ _ e]⟩
    · exact Or.inr ⟨i, by rw [GMap.set_same]; exact hnew x (by omega) h2⟩
  lab l c h := by
    rcases hf l c h with h | ⟨h1, h2⟩
    · exact hc.lab l c h
    · exact ⟨h1, by rw [h2]⟩

/-- The first `k` bytes of a region keep its alignment; the rest is a region of alignment `a'`
when its start is `a'`-aligned. -/
theorem up_region_split' {p : Ptr} {A S : Nat} {K : BlockKind} {a a' k : Nat} {bs : Array Byte}
    {r : Res} (hk : k ≤ bs.size) (ha : (A + p.off.toNat + k) % a' = 0)
    (h : up (regionIn p A S K a bs) r) :
    (up (regionIn p A S K a (bs.extract 0 k)) ⋆ up (regionIn (p.add k) A S K a' (bs.extract k bs.size))) r :=
  up_sep ⟨Region.regionIn_split h.1 hk ha, h.2⟩

section Upd

variable (ctx : Ptr) (B : FBuf) (γ e : Nat)

/-- **`alloc`'s ledger part**: `end_index` was set to `w`, the end of the grant `[w - n, w)`; the
padding `[ei, w - n)` joins the junk, half of the invariant's share is lent to the grant
(`ledger_issue`) under the fresh id `mN` with the client's fee, and the grant's bytes are the
grant's in the coverage. (The planner carves the grant's bytes and claim from the tail.) -/
theorem alloc_upd (n k : Nat) (φ : Frac) {ei mN : Nat} {tail : Array Byte} {q : Frac} {b cb : BlockId}
    {M : GMap} {jh : Heap} {w : BitVec 64}
    (hb : B.ptr.block = some b) (hp0 : 0 ≤ B.ptr.off) (hn : 0 < n) (hlo : ei + n ≤ w.toNat)
    (hhi : w.toNat ≤ B.cap) (ht : tail.size = B.cap - ei)
    (hal : (B.A + B.ptr.off.toNat + (w.toNat - n)) % 2 ^ k = 0) :
    EUpd (ftail B ei tail ⋆ (JunkAt jh ⋆ (fcov B b ei mN M jh ⋆ ((gauthP γ e M none ⋆ LedgerRcpts γ e M) ⋆
        (fparts ctx B q b cb ⋆ (epFee γ e φ ⋆ up (pts ctx 8 w)))))))
      (fparts ctx B q.half b cb ⋆ ftail B w.toNat (tail.extract (w.toNat - ei) tail.size) ⋆
        up (regionIn (B.ptr.add ((w.toNat - n : Nat) : Int)) B.A B.S B.K (2 ^ k)
          (tail.extract (w.toNat - n - ei) (w.toNat - ei))) ⋆
        FAssn.ex fun jh' => JunkAt jh' ⋆
        (fcov B b w.toNat (mN + 1) (M.set mN (some (B.ptr.add ((w.toNat - n : Nat) : Int), n, q.half, B.A, B.K, φ))) jh' ⋆
          ((gauthP γ e (M.set mN (some (B.ptr.add ((w.toNat - n : Nat) : Int), n, q.half, B.A, B.K, φ))) none ⋆
            LedgerRcpts γ e (M.set mN (some (B.ptr.add ((w.toNat - n : Nat) : Int), n, q.half, B.A, B.K, φ)))) ⋆
          (gfrag γ e mN (B.ptr.add ((w.toNat - n : Nat) : Int), n, q.half, B.A, B.K, φ) ⋆
            (bshare b q.half (B.ptr.off.toNat + w.toNat) (some (γ, e)) ⋆ up (pts ctx 8 w)))))) := by
  have hpo : (B.ptr.add ((w.toNat - n : Nat) : Int)).off.toNat = B.ptr.off.toNat + (w.toNat - n) := by
    simp only [Ptr.add]; omega
  have hpb : (B.ptr.add ((w.toNat - n : Nat) : Int)).block = some b := by simpa [Ptr.add] using hb
  have heo : (B.ptr.add (ei : Int)).off.toNat = B.ptr.off.toNat + ei := by simp only [Ptr.add]; omega
  -- the tail: the padding, the grant's bytes, the rest
  let u := tail.extract 0 (w.toNat - ei)
  have hu : u.size = w.toNat - ei := by simp only [u, Array.size_extract]; omega
  let pad := u.extract 0 (w.toNat - n - ei)
  have hpad : ei + pad.size = w.toNat - n := by simp only [pad, Array.size_extract]; omega
  let GR := up (regionIn (B.ptr.add ((w.toNat - n : Nat) : Int)) B.A B.S B.K (2 ^ k)
    (tail.extract (w.toNat - n - ei) (w.toNat - ei)))
  let RT := ftail B w.toNat (tail.extract (w.toNat - ei) tail.size)
  have hsplit : ∀ r, ftail B ei tail r →
      ((up (regionIn (B.ptr.add (ei : Int)) B.A B.S B.K 1 pad) ⋆ GR) ⋆ RT) r := fun r hr => by
    have h := up_region_split' (k := w.toNat - ei) (a' := 1) (by omega) (Nat.mod_one _) hr
    have e1 : (B.ptr.add (ei : Int)).add ((w.toNat - ei : Nat) : Int) = B.ptr.add ((w.toNat : Nat) : Int) := by
      simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega
    rw [e1] at h
    refine sep_mono_left (fun r x => ?_) h
    have ha : (B.A + (B.ptr.add (ei : Int)).off.toNat + (w.toNat - n - ei)) % 2 ^ k = 0 := by
      rw [heo, show B.A + (B.ptr.off.toNat + ei) + (w.toNat - n - ei) = B.A + B.ptr.off.toNat + (w.toNat - n)
        by omega]; exact hal
    have h := up_region_split' (k := w.toNat - n - ei) (a' := 2 ^ k)
      (by simp only [Array.size_extract]; omega) ha x
    have e2 : (B.ptr.add (ei : Int)).add ((w.toNat - n - ei : Nat) : Int) = B.ptr.add ((w.toNat - n : Nat) : Int) := by
      simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega
    have e3 : u.extract (w.toNat - n - ei) u.size = tail.extract (w.toNat - n - ei) (w.toNat - ei) := by
      simp only [u, Array.extract_extract, Nat.zero_add, hu]; congr 1; omega
    rw [e2, e3] at h
    exact h
  -- the padding joins the junk
  refine EUpd.trans (EUpd.of_imp (P' := FAssn.ex fun jh' =>
      ⟪JunkGrew B.ptr ei (w.toNat - n) jh jh' ∧ JunkFrom B.A B.K jh jh' ∧ FCov B b ei mN M jh⟫ ⋆
      ((gauthP γ e M none ⋆ (pshare B.ptr q (bnd B) none ⋆ (LedgerRcpts γ e M ⋆ epFee γ e φ))) ⋆
        (GR ⋆ (RT ⋆ (JunkAt jh' ⋆ (wBuf ctx B ⋆ (known cb B.cA ⋆ (known b B.A ⋆ up (pts ctx 8 w)))))))))
    fun r h => ?_) ?_
  · have h := sep_mono_left (hsplit) h
    have h := of_eq (Q := (up (regionIn (B.ptr.add (ei : Int)) B.A B.S B.K 1 pad) ⋆ JunkAt jh) ⋆
      (⟪FCov B b ei mN M jh⟫ ⋆ (bshare b q (bnd B) ⋆ (gauthP γ e M none ⋆ LedgerRcpts γ e M ⋆ epFee γ e φ ⋆
        GR ⋆ RT ⋆ wBuf ctx B ⋆ known cb B.cA ⋆ known b B.A ⋆ up (pts ctx 8 w)))))
      (by simp only [fcov, fparts]; ac_rfl) h
    obtain ⟨jh', hg, hf, h⟩ := junk_grew (p := B.ptr) (lo := ei) hp0 (by simp [Ptr.add])
      (by simp [Ptr.add]) h
    rw [hpad] at hg
    have h := sep_mono_left (Q := pshare B.ptr q (bnd B) none) (fun _ y => (pshare_iff hb).mpr y)
      (of_eq (Q := bshare b q (bnd B) ⋆ (⟪FCov B b ei mN M jh⟫ ⋆ (JunkAt jh' ⋆
        (gauthP γ e M none ⋆ LedgerRcpts γ e M ⋆ epFee γ e φ ⋆ GR ⋆ RT ⋆ wBuf ctx B ⋆ known cb B.cA ⋆
          known b B.A ⋆ up (pts ctx 8 w))))) (by ac_rfl) h)
    obtain ⟨hc, h⟩ := sep_lift.mp (of_eq (Q := ⟪FCov B b ei mN M jh⟫ ⋆ (pshare B.ptr q (bnd B) none ⋆
      (JunkAt jh' ⋆ (gauthP γ e M none ⋆ LedgerRcpts γ e M ⋆ epFee γ e φ ⋆ GR ⋆ RT ⋆ wBuf ctx B ⋆
        known cb B.cA ⋆ known b B.A ⋆ up (pts ctx 8 w))))) (by ac_rfl) h)
    exact ⟨jh', sep_lift.mpr ⟨⟨hg, hf, hc⟩, of_eq (by ac_rfl) h⟩⟩
  refine EUpd.exAll fun jh' => EUpd.lift fun ⟨hg, hf, hc⟩ => ?_
  refine EUpd.trans (EUpd.frame (ledger_issue (i := mN) (A := B.A) (K := B.K) (φ := φ) (n := n)
    (p := B.ptr.add ((w.toNat - n : Nat) : Int)) (hc.bound _ (Nat.le_refl _)) hb hpb
    (by unfold bnd; omega))) ?_
  refine EUpd.of_imp fun r h => ?_
  have hc' := FCov.alloc (w := w.toNat) (n := n)
    (g := (B.ptr.add ((w.toNat - n : Nat) : Int), n, q.half, B.A, B.K, φ)) hc hb hg hf
    fun x h1 h2 => ⟨hpb, by omega, by omega⟩
  have h := of_eq (Q := pshare (B.ptr.add ((w.toNat - n : Nat) : Int)) q.half
      ((B.ptr.add ((w.toNat - n : Nat) : Int)).off.toNat + n) (some (γ, e)) ⋆
    (pshare B.ptr q.half (bnd B) none ⋆ (gauthP γ e (M.set mN (some (B.ptr.add ((w.toNat - n : Nat) : Int), n,
      q.half, B.A, B.K, φ))) none ⋆ gfrag γ e mN (B.ptr.add ((w.toNat - n : Nat) : Int), n, q.half, B.A, B.K, φ) ⋆
      LedgerRcpts γ e (M.set mN (some (B.ptr.add ((w.toNat - n : Nat) : Int), n, q.half, B.A, B.K, φ))) ⋆
      GR ⋆ RT ⋆ JunkAt jh' ⋆ wBuf ctx B ⋆ known cb B.cA ⋆ known b B.A ⋆ up (pts ctx 8 w))))
    (by ac_rfl) h
  have h := sep_mono_left (Q := bshare b q.half ((B.ptr.add ((w.toNat - n : Nat) : Int)).off.toNat + n)
    (some (γ, e))) (fun _ x => (pshare_iff hpb).mp x) h
  have h := sep_mono_left (Q := bshare b q.half (bnd B) none) (fun _ y => (pshare_iff hb).mp y)
    (of_eq (Q := pshare B.ptr q.half (bnd B) none ⋆ (bshare b q.half
      ((B.ptr.add ((w.toNat - n : Nat) : Int)).off.toNat + n) (some (γ, e)) ⋆
      (gauthP γ e (M.set mN (some (B.ptr.add ((w.toNat - n : Nat) : Int), n,
      q.half, B.A, B.K, φ))) none ⋆ gfrag γ e mN (B.ptr.add ((w.toNat - n : Nat) : Int), n, q.half, B.A, B.K, φ) ⋆
      LedgerRcpts γ e (M.set mN (some (B.ptr.add ((w.toNat - n : Nat) : Int), n, q.half, B.A, B.K, φ))) ⋆
      GR ⋆ RT ⋆ JunkAt jh' ⋆ wBuf ctx B ⋆ known cb B.cA ⋆ known b B.A ⋆ up (pts ctx 8 w)))) (by ac_rfl) h)
  rw [hpo, show B.ptr.off.toNat + (w.toNat - n) + n = B.ptr.off.toNat + w.toNat by omega] at h
  refine sep_mono_right (fun _ x => sep_mono_right (fun _ y => sep_mono_right (fun _ z => ⟨jh', z⟩) y) x) ?_
  exact of_eq (by simp only [fparts, fcov, GR, RT]; ac_rfl) (sep_lift.mpr ⟨hc', h⟩)

/-- **`free` of the last grant**: `end_index` was set back to `w`, the grant's start; its share
goes back against its receipt and joins the invariant's (`ledger_return`), the grant is retired, its
fee comes back. (The planner joins its bytes and claim to the tail.) -/
theorem free_last_upd {ei mN i len : Nat} {qb q φ : Frac} {b b' cb : BlockId} {M : GMap} {jh : Heap}
    {p : Ptr} {w : BitVec 64}
    (hb : B.ptr.block = some b) (hpb : p.block = some b') (hpB : p.block = B.ptr.block)
    (hlo : B.ptr.off ≤ p.off) (hlast : p.off.toNat + len = B.ptr.off.toNat + ei)
    (hw : w.toNat + len = ei) :
    EUpd (gauthP γ e M none ⋆ (gfrag γ e i (p, len, q, B.A, B.K, φ) ⋆
        (bshare b' q (p.off.toNat + len) (some (γ, e)) ⋆ (LedgerRcpts γ e M ⋆
          (fparts ctx B qb b cb ⋆ (fcov B b ei mN M jh ⋆ up (pts ctx 8 w)))))))
      (fparts ctx B (qb.add q) b cb ⋆ ((gauthP γ e (M.set i none) none ⋆ LedgerRcpts γ e (M.set i none)) ⋆
        (fcov B b w.toNat mN (M.set i none) jh ⋆ (up (pts ctx 8 w) ⋆ (epTok γ e φ ⋆ ⟪0 < φ.val⟫))))) := by
  have hbb : b' = b := by rw [hpB, hb] at hpb; exact (Option.some.inj hpb).symm
  subst hbb
  refine EUpd.withFact ledger_grant_fact fun hM => ?_
  -- the grant goes back (`ledger_return`)
  refine EUpd.trans (EUpd.of_imp (P' := ⟪FCov B b' ei mN M jh⟫ ⋆
      ((gauthP γ e M none ⋆ (gfrag γ e i (p, len, q, B.A, B.K, φ) ⋆
        (pshare p q (p.off.toNat + len) (some (γ, e)) ⋆ LedgerRcpts γ e M))) ⋆
      (bshare b' qb (bnd B) ⋆ (wBuf ctx B ⋆ (known cb B.cA ⋆ (known b' B.A ⋆ up (pts ctx 8 w)))))))
    fun _ h => ?_) ?_
  · have h := sep_mono_left (Q := pshare p q (p.off.toNat + len) (some (γ, e)))
      (fun _ x => (pshare_iff hpb).mpr x)
      (of_eq (Q := bshare b' q (p.off.toNat + len) (some (γ, e)) ⋆ (gauthP γ e M none ⋆
        gfrag γ e i (p, len, q, B.A, B.K, φ) ⋆ LedgerRcpts γ e M ⋆ ⟪FCov B b' ei mN M jh⟫ ⋆
        bshare b' qb (bnd B) ⋆ wBuf ctx B ⋆ known cb B.cA ⋆ known b' B.A ⋆ up (pts ctx 8 w)))
        (by simp only [fparts, fcov]; ac_rfl) h)
    exact of_eq (by ac_rfl) h
  refine EUpd.lift fun hc => ?_
  refine EUpd.trans (EUpd.frame ledger_return) ?_
  refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc h) (EUpd.ex fun b₂ => EUpd.ex fun k => ?_)
  refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc h) (EUpd.lift fun hb₂ => ?_)
  rw [hpb] at hb₂; cases hb₂
  -- its share joins the invariant's
  refine EUpd.trans (EUpd.of_imp (P' := (bshare b' qb (bnd B) ⋆ bshare b' q k) ⋆
      (gauthP γ e (M.set i none) none ⋆ LedgerRcpts γ e (M.set i none) ⋆ epFee γ e φ ⋆ wBuf ctx B ⋆
        known cb B.cA ⋆ known b' B.A ⋆ up (pts ctx 8 w)))
    fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame EUpd.join) (EUpd.trans (EUpd.frame (EUpd.weaken (Nat.le_max_left _ _))) ?_)
  refine EUpd.of_imp fun _ h => ?_
  have hc' : FCov B b' w.toNat mN (M.set i none) jh :=
    FCov.set hc hM (fun _ h => h) (fun _ _ h => Or.inl h)
      (fun x h2 hx => absurd hx.2.1 (by omega)) (fun x h1 h2 => absurd h2 (by omega))
  exact of_eq (by simp only [fparts, fcov, epFee]; ac_rfl) (sep_lift.mpr ⟨hc', h⟩)

/-- **`free` of a grant that is not the last**: its bytes join the junk (with the buffer's labels),
its share goes back against its receipt and joins the invariant's (`ledger_return`), the grant is
retired, its fee comes back. (The planner forgets its claim.) -/
theorem free_other_upd {ei mN i k : Nat} {qb q φ : Frac} {b b' cb : BlockId} {M : GMap} {jh : Heap}
    {p : Ptr} {bs : Array Byte}
    (hb : B.ptr.block = some b) (hpb : p.block = some b') (hpB : p.block = B.ptr.block) (hp0 : 0 ≤ p.off) :
    EUpd (up (regionIn p B.A B.S B.K (2 ^ k) bs) ⋆ (JunkAt jh ⋆ (gauthP γ e M none ⋆
        (gfrag γ e i (p, bs.size, q, B.A, B.K, φ) ⋆ (bshare b' q (p.off.toNat + bs.size) (some (γ, e)) ⋆
          (LedgerRcpts γ e M ⋆ (fparts ctx B qb b cb ⋆ fcov B b ei mN M jh)))))))
      (fparts ctx B (qb.add q) b cb ⋆ FAssn.ex fun jh' => JunkAt jh' ⋆
        ((gauthP γ e (M.set i none) none ⋆ LedgerRcpts γ e (M.set i none)) ⋆
          (fcov B b ei mN (M.set i none) jh' ⋆ (epTok γ e φ ⋆ ⟪0 < φ.val⟫)))) := by
  have hbb : b' = b := by rw [hpB, hb] at hpb; exact (Option.some.inj hpb).symm
  subst hbb
  -- the grant's bytes join the junk
  refine EUpd.trans (EUpd.of_imp (P' := FAssn.ex fun jh' =>
      ⟪JunkGrew p 0 bs.size jh jh' ∧ JunkFrom B.A B.K jh jh' ∧ FCov B b' ei mN M jh⟫ ⋆
      ((gauthP γ e M none ⋆ (gfrag γ e i (p, bs.size, q, B.A, B.K, φ) ⋆
        (pshare p q (p.off.toNat + bs.size) (some (γ, e)) ⋆ LedgerRcpts γ e M))) ⋆
      (JunkAt jh' ⋆ (bshare b' qb (bnd B) ⋆ (wBuf ctx B ⋆ (known cb B.cA ⋆ known b' B.A))))))
    fun r h => ?_) ?_
  · have h := of_eq (Q := (up (regionIn p B.A B.S B.K (2 ^ k) bs) ⋆ JunkAt jh) ⋆
      (⟪FCov B b' ei mN M jh⟫ ⋆ (bshare b' q (p.off.toNat + bs.size) (some (γ, e)) ⋆ (gauthP γ e M none ⋆
        gfrag γ e i (p, bs.size, q, B.A, B.K, φ) ⋆ LedgerRcpts γ e M ⋆ bshare b' qb (bnd B) ⋆ wBuf ctx B ⋆
        known cb B.cA ⋆ known b' B.A))))
      (by simp only [fcov, fparts]; ac_rfl) h
    obtain ⟨jh', hg, hf, h⟩ := junk_grew (p := p) (lo := 0) hp0 rfl (by simp) h
    rw [Nat.zero_add] at hg
    obtain ⟨hc, h⟩ := sep_lift.mp (of_eq (Q := ⟪FCov B b' ei mN M jh⟫ ⋆
      (bshare b' q (p.off.toNat + bs.size) (some (γ, e)) ⋆ (JunkAt jh' ⋆ (gauthP γ e M none ⋆
        gfrag γ e i (p, bs.size, q, B.A, B.K, φ) ⋆ LedgerRcpts γ e M ⋆ bshare b' qb (bnd B) ⋆ wBuf ctx B ⋆
        known cb B.cA ⋆ known b' B.A)))) (by ac_rfl) h)
    have h := sep_mono_left (Q := pshare p q (p.off.toNat + bs.size) (some (γ, e)))
      (fun _ x => (pshare_iff hpb).mpr x) h
    exact ⟨jh', sep_lift.mpr ⟨⟨hg, hf, hc⟩, of_eq (by ac_rfl) h⟩⟩
  refine EUpd.exAll fun jh' => EUpd.lift fun ⟨hg, hf, hc⟩ => ?_
  refine EUpd.withFact (fun m r rF hh hp hs =>
    ledger_grant_fact m r rF hh (sep_mono_right (fun _ x => sep_assoc x) (sep_assoc hp)) hs) fun hM => ?_
  -- the grant goes back (`ledger_return`), its share joins the invariant's
  refine EUpd.trans (EUpd.frame ledger_return) ?_
  refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc h) (EUpd.ex fun b₂ => EUpd.ex fun k => ?_)
  refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc h) (EUpd.lift fun hb₂ => ?_)
  rw [hpb] at hb₂; cases hb₂
  refine EUpd.trans (EUpd.of_imp (P' := (bshare b' qb (bnd B) ⋆ bshare b' q k) ⋆
      (gauthP γ e (M.set i none) none ⋆ LedgerRcpts γ e (M.set i none) ⋆ epFee γ e φ ⋆ JunkAt jh' ⋆
        wBuf ctx B ⋆ known cb B.cA ⋆ known b' B.A))
    fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame EUpd.join) (EUpd.trans (EUpd.frame (EUpd.weaken (Nat.le_max_left _ _))) ?_)
  refine EUpd.of_imp fun _ h => ?_
  have hc' : FCov B b' ei mN (M.set i none) jh' :=
    FCov.set (w := ei) hc hM hg.1 hf
      (fun x _ hx => Or.inl (hg.2 b' x hx.1 (by have := hx.2.1; omega) (by have := hx.2.2; omega)))
      (fun x h1 h2 => absurd h2 (by omega))
  refine sep_mono_right (fun _ x => ⟨jh', x⟩) ?_
  exact of_eq (by simp only [fparts, fcov, epFee]; ac_rfl) (sep_lift.mpr ⟨hc', h⟩)

/-- **`resize` of a grant that is not the last to `n ≤ len`**: the released bytes (`relBytes`)
join the junk and their claim is forgotten, the grant's share comes down to its new end
(`ledger_shrink`), the grant is re-pointed. -/
theorem resize_other_upd (n len : Nat) (q' : Frac) (tl : Array Byte) {ei mN i : Nat} {qb q φ : Frac}
    {b b' cb : BlockId} {M : GMap} {jh : Heap} {p : Ptr}
    (hb : B.ptr.block = some b) (hpb : p.block = some b') (hpB : p.block = B.ptr.block) (hp0 : 0 ≤ p.off)
    (hn : n ≤ len) :
    EUpd ((finv ctx B γ e).relBytes p B.A B.S B.K n len tl ⋆ (JunkAt jh ⋆ (gauthP γ e M none ⋆
        (gfrag γ e i (p, len, q, B.A, B.K, φ) ⋆ (bshare b' q' (p.off.toNat + len) (some (γ, e)) ⋆
          (LedgerRcpts γ e M ⋆ (fparts ctx B qb b cb ⋆ fcov B b ei mN M jh)))))))
      (fparts ctx B qb b cb ⋆ FAssn.ex fun jh' => JunkAt jh' ⋆
        ((gauthP γ e (M.set i (some (p, n, q, B.A, B.K, φ))) none ⋆
          LedgerRcpts γ e (M.set i (some (p, n, q, B.A, B.K, φ)))) ⋆
          (gfrag γ e i (p, n, q, B.A, B.K, φ) ⋆ (bshare b' q' (p.off.toNat + n) (some (γ, e)) ⋆
            fcov B b ei mN (M.set i (some (p, n, q, B.A, B.K, φ))) jh')))) := by
  have hbb : b' = b := by rw [hpB, hb] at hpb; exact (Option.some.inj hpb).symm
  subst hbb
  let LG : FAssn := gauthP γ e M none ⋆ (gfrag γ e i (p, len, q, B.A, B.K, φ) ⋆
    (pshare p q' (p.off.toNat + len) (some (γ, e)) ⋆ LedgerRcpts γ e M))
  refine EUpd.trans (EUpd.of_imp (P' := ⟪FCov B b' ei mN M jh⟫ ⋆
      ((finv ctx B γ e).relBytes p B.A B.S B.K n len tl ⋆ (JunkAt jh ⋆ (LG ⋆ fparts ctx B qb b' cb))))
    fun _ h => ?_) ?_
  · have h := sep_mono_left (Q := pshare p q' (p.off.toNat + len) (some (γ, e)))
      (fun _ x => (pshare_iff hpb).mpr x)
      (of_eq (Q := bshare b' q' (p.off.toNat + len) (some (γ, e)) ⋆ (⟪FCov B b' ei mN M jh⟫ ⋆
        (finv ctx B γ e).relBytes p B.A B.S B.K n len tl ⋆ JunkAt jh ⋆ gauthP γ e M none ⋆
        gfrag γ e i (p, len, q, B.A, B.K, φ) ⋆ LedgerRcpts γ e M ⋆ fparts ctx B qb b' cb))
        (by simp only [fcov]; ac_rfl) h)
    exact of_eq (by simp only [LG]; ac_rfl) h
  refine EUpd.lift fun hc => ?_
  -- the ledger part, once the released bytes are junk
  suffices H : ∀ jh', (∀ x, p.off.toNat + n ≤ x → x < p.off.toNat + len → jh' (b', x) ≠ none) →
      (∀ l, jh l ≠ none → jh' l ≠ none) → JunkFrom B.A B.K jh jh' →
      EUpd (LG ⋆ (JunkAt jh' ⋆ fparts ctx B qb b' cb))
        (fparts ctx B qb b' cb ⋆ FAssn.ex fun jh' => JunkAt jh' ⋆
          ((gauthP γ e (M.set i (some (p, n, q, B.A, B.K, φ))) none ⋆
            LedgerRcpts γ e (M.set i (some (p, n, q, B.A, B.K, φ)))) ⋆
            (gfrag γ e i (p, n, q, B.A, B.K, φ) ⋆ (bshare b' q' (p.off.toNat + n) (some (γ, e)) ⋆
              fcov B b' ei mN (M.set i (some (p, n, q, B.A, B.K, φ))) jh')))) by
    simp only [FAllocInv.relBytes, finv_tag]
    by_cases hlt : n < len
    · rw [if_pos hlt]
      refine EUpd.trans (EUpd.of_imp (P' := (FAssn.ex fun jh' =>
          ⟪(∀ x, p.off.toNat + n ≤ x → x < p.off.toNat + len → jh' (b', x) ≠ none) ∧
            (∀ l, jh l ≠ none → jh' l ≠ none) ∧ JunkFrom B.A B.K jh jh'⟫ ⋆
          (LG ⋆ (JunkAt jh' ⋆ fparts ctx B qb b' cb))) ⋆
          pclaim p (p.off.toNat + n) (p.off.toNat + len) (some (γ, e))) fun _ h => ?_)
        (EUpd.trans (EUpd.drop fun _ h => pclaim_ghost h)
          (EUpd.exAll fun jh' => EUpd.lift fun ⟨h1, h2, h3⟩ => H jh' h1 h2 h3))
      obtain ⟨htl, h⟩ := sep_lift.mp (sep_assoc h)
      have h := of_eq (Q := (up (regionIn (p.add (n : Int)) B.A B.S B.K 1 tl) ⋆ JunkAt jh) ⋆
        (pclaim p (p.off.toNat + n) (p.off.toNat + len) (some (γ, e)) ⋆ (LG ⋆ fparts ctx B qb b' cb)))
        (by ac_rfl) h
      obtain ⟨jh', hg, hf, h⟩ := junk_grew (p := p) (lo := n) hp0 (by simp [Ptr.add])
        (by simp [Ptr.add]) h
      refine sep_mono_left (fun _ x => ⟨jh', sep_lift.mpr ⟨⟨fun x h1 h2 => hg.2 b' x hpb h1 (by omega),
        hg.1, hf⟩, x⟩⟩) (of_eq (Q := (LG ⋆ (JunkAt jh' ⋆ fparts ctx B qb b' cb)) ⋆
          pclaim p (p.off.toNat + n) (p.off.toNat + len) (some (γ, e))) (by ac_rfl) h)
    · rw [if_neg hlt]
      exact EUpd.trans (EUpd.of_imp fun _ h => of_eq (by rw [Full.emp_sep_eq]; ac_rfl) h)
        (H jh (fun x h1 h2 => absurd h2 (by omega)) (fun _ h => h) (fun _ _ h => Or.inl h))
  intro jh' hrel hjh hf
  refine EUpd.withFact (fun m r rF hh hp hs =>
    ledger_grant_fact m r rF hh (sep_mono_right (fun _ x => sep_assoc x) (sep_assoc hp)) hs) fun hM => ?_
  refine EUpd.trans (EUpd.frame (ledger_shrink (t := none) hn)) (EUpd.of_imp fun _ h => ?_)
  have hc' : FCov B b' ei mN (M.set i (some (p, n, q, B.A, B.K, φ))) jh' :=
    FCov.set (w := ei) hc hM hjh hf
      (fun x _ hx => by
        by_cases h2 : x < p.off.toNat + n
        · exact Or.inr ⟨hpb, hx.2.1, h2⟩
        · exact Or.inl (hrel x (by omega) hx.2.2))
      (fun x h1 h2 => absurd h2 (by omega))
  have h := sep_mono_left (Q := bshare b' q' (p.off.toNat + n) (some (γ, e)))
    (fun _ x => (pshare_iff hpb).mp x)
    (of_eq (Q := pshare p q' (p.off.toNat + n) (some (γ, e)) ⋆
      (gauthP γ e (M.set i (some (p, n, q, B.A, B.K, φ))) none ⋆ gfrag γ e i (p, n, q, B.A, B.K, φ) ⋆
        LedgerRcpts γ e (M.set i (some (p, n, q, B.A, B.K, φ))) ⋆ JunkAt jh' ⋆ fparts ctx B qb b' cb))
      (by ac_rfl) h)
  refine sep_mono_right (fun _ x => ⟨jh', x⟩) ?_
  exact of_eq (by simp only [fcov]; ac_rfl) (sep_lift.mpr ⟨hc', h⟩)

/-- **`resize` of the last grant to `n`** (shrink or growth into the tail): `end_index` was set
to `w`, the grant's new end; the client's part `q'` of the grant's share is re-lent at the new end
(`ledger_regrow`), the grant is re-pointed. (The planner moves the bytes and claims between the
grant and the tail.) -/
theorem resize_last_upd {ei mN i len n : Nat} {qb q q' φ : Frac} {b b' cb : BlockId} {M : GMap}
    {jh : Heap} {p : Ptr} {w : BitVec 64}
    (hb : B.ptr.block = some b) (hpb : p.block = some b') (hpB : p.block = B.ptr.block)
    (hlo : B.ptr.off ≤ p.off) (hlast : p.off.toNat + len = B.ptr.off.toNat + ei)
    (hw : B.ptr.off.toNat + w.toNat = p.off.toNat + n) (hfit : w.toNat ≤ B.cap) (hq : q'.val ≤ q.val) :
    EUpd (gauthP γ e M none ⋆ (gfrag γ e i (p, len, q, B.A, B.K, φ) ⋆
        (bshare b' q' (p.off.toNat + len) (some (γ, e)) ⋆ (LedgerRcpts γ e M ⋆
          (fparts ctx B qb b cb ⋆ (fcov B b ei mN M jh ⋆ up (pts ctx 8 w)))))))
      (fparts ctx B qb b cb ⋆ ((gauthP γ e (M.set i (some (p, n, q, B.A, B.K, φ))) none ⋆
          LedgerRcpts γ e (M.set i (some (p, n, q, B.A, B.K, φ)))) ⋆
        (gfrag γ e i (p, n, q, B.A, B.K, φ) ⋆ (bshare b' q' (p.off.toNat + n) (some (γ, e)) ⋆
          (fcov B b w.toNat mN (M.set i (some (p, n, q, B.A, B.K, φ))) jh ⋆ up (pts ctx 8 w)))))) := by
  have hbb : b' = b := by rw [hpB, hb] at hpb; exact (Option.some.inj hpb).symm
  subst hbb
  refine EUpd.withFact ledger_grant_fact fun hM => ?_
  refine EUpd.trans (EUpd.of_imp (P' := ⟪FCov B b' ei mN M jh⟫ ⋆
      ((gauthP γ e M none ⋆ (gfrag γ e i (p, len, q, B.A, B.K, φ) ⋆
        (pshare p q' (p.off.toNat + len) (some (γ, e)) ⋆ (LedgerRcpts γ e M ⋆ pshare B.ptr qb (bnd B) none)))) ⋆
      (wBuf ctx B ⋆ (known cb B.cA ⋆ (known b' B.A ⋆ up (pts ctx 8 w))))))
    fun _ h => ?_) ?_
  · have h := sep_mono_left (Q := pshare p q' (p.off.toNat + len) (some (γ, e)))
      (fun _ x => (pshare_iff hpb).mpr x)
      (of_eq (Q := bshare b' q' (p.off.toNat + len) (some (γ, e)) ⋆ (bshare b' qb (bnd B) ⋆
        (⟪FCov B b' ei mN M jh⟫ ⋆ gauthP γ e M none ⋆ gfrag γ e i (p, len, q, B.A, B.K, φ) ⋆
          LedgerRcpts γ e M ⋆ wBuf ctx B ⋆ known cb B.cA ⋆ known b' B.A ⋆ up (pts ctx 8 w))))
        (by simp only [fparts, fcov]; ac_rfl) h)
    have h := sep_mono_left (Q := pshare B.ptr qb (bnd B) none) (fun _ y => (pshare_iff hb).mpr y)
      (of_eq (Q := bshare b' qb (bnd B) ⋆ (pshare p q' (p.off.toNat + len) (some (γ, e)) ⋆
        (⟪FCov B b' ei mN M jh⟫ ⋆ gauthP γ e M none ⋆ gfrag γ e i (p, len, q, B.A, B.K, φ) ⋆
          LedgerRcpts γ e M ⋆ wBuf ctx B ⋆ known cb B.cA ⋆ known b' B.A ⋆ up (pts ctx 8 w))))
        (by ac_rfl) h)
    exact of_eq (by ac_rfl) h
  refine EUpd.lift fun hc => ?_
  refine EUpd.trans (EUpd.frame (ledger_regrow (K' := B.K) (n' := n) (N := B.ptr) hq (hpB) (by unfold bnd; omega)))
    (EUpd.of_imp fun _ h => ?_)
  have hc' : FCov B b' w.toNat mN (M.set i (some (p, n, q, B.A, B.K, φ))) jh :=
    FCov.set hc hM (fun _ h => h) (fun _ _ h => Or.inl h)
      (fun x h2 hx => Or.inr ⟨hpb, hx.2.1, by omega⟩)
      (fun x h1 h2 => ⟨hpb, by omega, by omega⟩)
  have h := of_eq (Q := pshare p q' (p.off.toNat + n) (some (γ, e)) ⋆ (pshare B.ptr qb (bnd B) none ⋆
      (gauthP γ e (M.set i (some (p, n, q, B.A, B.K, φ))) none ⋆ gfrag γ e i (p, n, q, B.A, B.K, φ) ⋆
        LedgerRcpts γ e (M.set i (some (p, n, q, B.A, B.K, φ))) ⋆ wBuf ctx B ⋆ known cb B.cA ⋆
        known b' B.A ⋆ up (pts ctx 8 w)))) (by ac_rfl) h
  have h := sep_mono_left (Q := bshare b' q' (p.off.toNat + n) (some (γ, e)))
    (fun _ x => (pshare_iff hpb).mp x) h
  have h := sep_mono_left (Q := bshare b' qb (bnd B) none) (fun _ y => (pshare_iff hb).mp y)
    (of_eq (Q := pshare B.ptr qb (bnd B) none ⋆ (bshare b' q' (p.off.toNat + n) (some (γ, e)) ⋆
      (gauthP γ e (M.set i (some (p, n, q, B.A, B.K, φ))) none ⋆ gfrag γ e i (p, n, q, B.A, B.K, φ) ⋆
        LedgerRcpts γ e (M.set i (some (p, n, q, B.A, B.K, φ))) ⋆ wBuf ctx B ⋆ known cb B.cA ⋆
        known b' B.A ⋆ up (pts ctx 8 w)))) (by ac_rfl) h)
  exact of_eq (by simp only [fparts, fcov]; ac_rfl) (sep_lift.mpr ⟨hc', h⟩)

end Upd

/-! ## The entries -/

theorem falloc_spec (ctx : Ptr) (B : FBuf) (γ e : Nat) (n : BitVec 64) (k : Nat) (ra : BitVec 64)
    (φ : Frac) (hn : 0 < n.toNat) (hk : k < 64) (hfit : (finv ctx B γ e).fits n.toNat k) :
    FTotalTriple ((finv ctx B γ e).own ⋆ (finv ctx B γ e).fee φ) (impl.alloc ctx n k ra)
      ((finv ctx B γ e).allocPost n.toNat k φ) := by
  fsym [alloc_upd ctx B γ e n.toNat k φ]

theorem fresize_spec (ctx : Ptr) (B : FBuf) (γ e : Nat) (s : Slice) (k : Nat) (n ra : BitVec 64)
    (A S : Nat) (K : BlockKind) (q q' φ : Frac) (tl : Array Byte) (hk : k < 64) (hn : 0 < n.toNat)
    (hfit : (finv ctx B γ e).fits n.toNat k) (hpos : 0 < s.len.toNat) (hq : q'.val ≤ q.val) :
    FTotalTriple ((finv ctx B γ e).own ⋆ ((finv ctx B γ e).held s.ptr s.len.toNat k A S K q q' φ ⋆
      (finv ctx B γ e).relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (impl.resize ctx s k n ra)
      ((finv ctx B γ e).rresizePost s.ptr k s.len.toNat n.toNat A S K q q' φ tl) := by
  -- (WORKAROUND fsym-engine ledger #64: the released bytes' `if` is decided before the walk; an
  -- update at a return is planned against a state with an undecided `if` in both branches at once)
  by_cases hc : n.toNat < s.len.toNat <;>
  fsym [resize_other_upd ctx B γ e n.toNat s.len.toNat q' tl,
    resize_last_upd ctx B γ e (n := n.toNat) (q := q) (q' := q')]

theorem fremap_spec (ctx : Ptr) (B : FBuf) (γ e : Nat) (s : Slice) (k : Nat) (n ra : BitVec 64)
    (φ : Frac) (bs : Array Byte) (hk : k < 64) (hn : 0 < n.toNat) (hfit : (finv ctx B γ e).fits n.toNat k)
    (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FTotalTriple ((finv ctx B γ e).own ⋆ (finv ctx B γ e).granted s.ptr k φ bs) (impl.remap ctx s k n ra)
      ((finv ctx B γ e).remapPost s.ptr k φ bs n.toNat) := by
  have hr : FTotalTriple ((finv ctx B γ e).own ⋆ (finv ctx B γ e).granted s.ptr k φ bs)
      (heap_FixedBufferAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((finv ctx B γ e).resizePost s.ptr k φ bs n.toNat) :=
    (finv ctx B γ e).resize_granted_of (L := FLogic.total) (c := impl.resize ctx s k n ra)
      (fun A S K q q' tl hq _ => fresize_spec ctx B γ e s k n ra A S K q q' φ tl hk hn hfit
        (by omega) hq) hlen
  set_option trace.fsym.total true in
  fsym [hr]

theorem ffree_spec (ctx : Ptr) (B : FBuf) (γ e : Nat) (s : Slice) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FTotalTriple ((finv ctx B γ e).own ⋆ (finv ctx B γ e).granted s.ptr k φ bs) (impl.free ctx s k ra)
      (fun _ => (finv ctx B γ e).own ⋆ (finv ctx B γ e).fee φ) := by
  set_option trace.fsym.total true in
  fsym [free_last_upd ctx B γ e, free_other_upd ctx B γ e]

end FBA

end AllocFba
