import AllocFba.Impl
import ZigLean.Sep.Full.AutoClaims
import ZigLean.Sep.Full.AutoThread
import ZigLean.Sep.Full.ResetLedger
import ZigLean.Sep.Full.WitnessStart
import ZigLean.Witness

/-!
# The translated `FixedBufferAllocator` satisfies the full-state `FAllocSpec`

`FBA.fallocSpec`: the four vtable entries of the translated `FixedBufferAllocator` (`Gen.lean`)
satisfy `FAllocSpec FLogic.total impl ctx (finv ctx B γ e)` for every allocator struct `ctx`, every
buffer `B` and every epoch `e` of a ledger `γ`, proved natively in the full-state logic
(`ZigLean/Sep/Full`) from the generated code; `FBA.freset_spec`: `reset` takes the whole epoch token
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
returns** (`fsym [u]`): each entry is `fsym` on its `FAllocSpec` field as a thread triple
(`fthread_*`; the sequential field is its reading in one thread), which walks the generated
code with the library's step rules and plans the returns (carving and joining regions and claims);
a return that changes the ledger or the junk is closed by the update of its branch
(`alloc_upd`, `free_last_upd`, …), plain lemmas over the invariant built from the library's ledger
updates. `resize` is the refined field (`FAllocInv.held`/`relBytes`/`rresizePost`); `remap` is
`resize`'s whole-region form (`FAllocInv.resize_granted_gen`) and a pointer.
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

/-- Every physically bounded buffer accepts a real positive request, including capacity zero.
Accepting a request permits an allocation failure; it does not promise spare capacity. -/
theorem ffits_usable (B : FBuf) (hcap : B.cap ≤ 2 ^ 63) :
    ∃ len : BitVec 64, ∃ k, 0 < len.toNat ∧ k < 64 ∧ ffits B len.toNat k := by
  refine ⟨1, 0, by decide, by decide, ?_⟩
  change B.cap + 1 + 1 ≤ 2 ^ 64
  omega

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
    have h := up_regionIn_split (k := w.toNat - ei) (a' := 1) (by omega) (Nat.mod_one _) hr
    have e1 : (B.ptr.add (ei : Int)).add ((w.toNat - ei : Nat) : Int) = B.ptr.add ((w.toNat : Nat) : Int) := by
      simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega
    rw [e1] at h
    refine sep_mono_left (fun r x => ?_) h
    have ha : (B.A + (B.ptr.add (ei : Int)).off.toNat + (w.toNat - n - ei)) % 2 ^ k = 0 := by
      rw [heo, show B.A + (B.ptr.off.toNat + ei) + (w.toNat - n - ei) = B.A + B.ptr.off.toNat + (w.toNat - n)
        by omega]; exact hal
    have h := up_regionIn_split (k := w.toNat - n - ei) (a' := 2 ^ k)
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

/-- **`reset`'s ghost part**: `end_index` was set to `0`. The whole epoch token shows that no grant
is out (`ledgerRcpts_epTok_empty`); the ledger moves to the next epoch (`ledger_bump`); the
buffer's claim comes back from the past epoch (`EUpd.revokeC`) and is lent again in the new one
(`EUpd.lendC`), the old tail claim is dropped; with no grant the used part is junk (`fcov`), which
becomes a region with the buffer's labels again (`EUpd.junkRegionLab`) and joins the tail. -/
theorem reset_upd {ei mN : Nat} {tail : Array Byte} {q : Frac} {b cb : BlockId} {M : GMap} {jh : Heap}
    (hei : ei ≤ B.cap) (ht : tail.size = B.cap - ei) (hA : B.A + B.ptr.off.toNat + B.cap < 2 ^ 64)
    (hp0 : 0 ≤ B.ptr.off) (hal : (B.cA + ctx.off.toNat) % 8 = 0) (hc0 : 0 ≤ ctx.off)
    (hb : B.ptr.block = some b) (hcb : ctx.block = some cb) :
    EUpd ((gauthP γ e M none ⋆ LedgerRcpts γ e M) ⋆ (epTok γ e Frac.one ⋆
        (up (pts ctx 8 (0 : BitVec 64)) ⋆ (fparts ctx B q b cb ⋆ (ftail B ei tail ⋆ (fclaim B ei b γ e ⋆
          (frcpt B b γ e ⋆ (JunkAt jh ⋆ fcov B b ei mN M jh))))))))
      (fown ctx B γ (e + 1) ⋆ epTok γ (e + 1) Frac.one) := by
  let X : FAssn := frcpt B b γ e ⋆ (JunkAt jh ⋆ (ftail B ei tail ⋆ (fclaim B ei b γ e ⋆
    (up (pts ctx 8 (0 : BitVec 64)) ⋆ fparts ctx B q b cb))))
  refine EUpd.trans (EUpd.of_imp (P' := ⟪B.K ≠ .constGlobal ∧ FCov B b ei mN M jh⟫ ⋆
      (((gauthP γ e M none ⋆ LedgerRcpts γ e M) ⋆ epTok γ e Frac.one) ⋆ X)) fun _ h => ?_) ?_
  · have h := of_eq (Q := ftail B ei tail ⋆ (⟪FCov B b ei mN M jh⟫ ⋆
      (((gauthP γ e M none ⋆ LedgerRcpts γ e M) ⋆ epTok γ e Frac.one) ⋆ (frcpt B b γ e ⋆ (JunkAt jh ⋆
        (fclaim B ei b γ e ⋆ (up (pts ctx 8 (0 : BitVec 64)) ⋆ fparts ctx B q b cb)))))))
      (by simp only [fcov]; ac_rfl) h
    have hK : B.K ≠ .constGlobal := by obtain ⟨_, _, _, _, hft, _⟩ := h; exact hft.1.2.1
    obtain ⟨hc, h⟩ := sep_lift.mp (of_eq (Q := ⟪FCov B b ei mN M jh⟫ ⋆ (ftail B ei tail ⋆
      (((gauthP γ e M none ⋆ LedgerRcpts γ e M) ⋆ epTok γ e Frac.one) ⋆ (frcpt B b γ e ⋆ (JunkAt jh ⋆
        (fclaim B ei b γ e ⋆ (up (pts ctx 8 (0 : BitVec 64)) ⋆ fparts ctx B q b cb)))))))
      (by ac_rfl) h)
    exact sep_lift.mpr ⟨⟨hK, hc⟩, of_eq (by simp only [X]; ac_rfl) h⟩
  refine EUpd.lift fun ⟨hK, hc⟩ => ?_
  -- no grant is out; the ledger moves to the next epoch
  refine EUpd.withFact (φ := M = GMap.empty) (fun m r rF hh hp hs =>
    ledgerRcpts_epTok_empty m r rF hh hp hs) fun hM => ?_
  subst hM
  refine EUpd.trans (EUpd.frame ledger_bump) ?_
  -- the buffer's claim, back and lent again; the old tail claim is dropped
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ (e + 1) GMap.empty none ⋆
      bcrcpt b B.ptr.off.toNat (bnd B) γ e) ⋆ (LedgerRcpts γ (e + 1) GMap.empty ⋆ epTok γ (e + 1) Frac.one ⋆
        JunkAt jh ⋆ ftail B ei tail ⋆ fclaim B ei b γ e ⋆ up (pts ctx 8 (0 : BitVec 64)) ⋆
        fparts ctx B q b cb))
    fun _ h => of_eq (by simp only [X, frcpt]; ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame (EUpd.revokeC (by omega))) (EUpd.trans (EUpd.frame EUpd.lendC) ?_)
  refine EUpd.trans (EUpd.of_imp (P' := fclaim B ei b γ e ⋆ (JunkAt jh ⋆
      ((gauthP γ (e + 1) GMap.empty none ⋆ (bclaim b B.ptr.off.toNat (bnd B) (some (γ, e + 1)) ⋆
        bcrcpt b B.ptr.off.toNat (bnd B) γ (e + 1))) ⋆ (LedgerRcpts γ (e + 1) GMap.empty ⋆
        epTok γ (e + 1) Frac.one ⋆ ftail B ei tail ⋆ up (pts ctx 8 (0 : BitVec 64)) ⋆ fparts ctx B q b cb))))
    fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (by unfold fclaim; exact claim_drop) ?_
  -- the junk of the used part is a region again and joins the tail
  refine EUpd.trans (EUpd.frame (EUpd.junkRegionLab (p := B.ptr) (n := ei) (A := B.A) (S := B.S)
    (K := B.K) hb hp0 hK (fun x c _ _ hx => hc.lab _ c hx) fun x h1 h2 => ?_)) ?_
  · rcases hc.cov x h1 h2 with h | ⟨i, h⟩
    · exact h
    · exact h.elim
  refine EUpd.of_imp fun _ h => ?_
  obtain ⟨bs, h⟩ := sep_ex.mp (sep_assoc h)
  obtain ⟨hbs, h⟩ := sep_lift.mp (sep_assoc h)
  have h := of_eq (Q := (up (regionIn B.ptr B.A B.S B.K 1 bs) ⋆ ftail B ei tail) ⋆
      (JunkAt (jh.cut b B.ptr.off.toNat (B.ptr.off.toNat + ei)) ⋆
        (gauthP γ (e + 1) GMap.empty none ⋆ LedgerRcpts γ (e + 1) GMap.empty) ⋆
        bclaim b B.ptr.off.toNat (bnd B) (some (γ, e + 1)) ⋆ bcrcpt b B.ptr.off.toNat (bnd B) γ (e + 1) ⋆
        epTok γ (e + 1) Frac.one ⋆ up (pts ctx 8 (0 : BitVec 64)) ⋆ fparts ctx B q b cb))
    (by ac_rfl) h
  have e0 : B.ptr.add ((0 : Nat) : Int) = B.ptr := by
    obtain ⟨blk, o⟩ := B.ptr; simp [Ptr.add]
  have h := sep_mono_left (Q := ftail B 0 (bs ++ tail)) (fun _ x => by
    unfold ftail; rw [e0]
    exact up_regionIn_join (by rw [hbs]) x) h
  have hc' : FCov B b 0 0 GMap.empty (jh.cut b B.ptr.off.toNat (B.ptr.off.toNat + ei)) :=
    ⟨fun _ _ => rfl, fun x h1 h2 => absurd h2 (by omega), fun l c hl => hc.lab l c (by
      simp only [Heap.cut] at hl; split at hl
      · cases hl
      · exact hl)⟩
  let jc := jh.cut b B.ptr.off.toNat (B.ptr.off.toNat + ei)
  have H : ((⟪FFacts ctx B 0 (bs ++ tail) b cb⟫ ⋆
      ((gauthP γ (e + 1) GMap.empty none ⋆ LedgerRcpts γ (e + 1) GMap.empty) ⋆
        ((up (pts ctx 8 (0 : BitVec 64)) ⋆ fparts ctx B q b cb) ⋆
          ((ftail B 0 (bs ++ tail) ⋆ fclaim B 0 b γ (e + 1)) ⋆
          (frcpt B b γ (e + 1) ⋆ (JunkAt jc ⋆ fcov B b 0 0 GMap.empty jc)))))) ⋆
      epTok γ (e + 1) Frac.one) _ :=
    of_eq (by simp only [fcov, fclaim, frcpt, jc, Nat.add_zero]; ac_rfl)
      (sep_lift.mpr ⟨(show FFacts ctx B 0 (bs ++ tail) b cb from
          ⟨⟨Nat.zero_le _, by simp only [Array.size_append]; omega, hA, hp0, hal, hc0⟩, hb, hcb⟩),
        sep_lift.mpr ⟨hc', h⟩⟩)
  exact sep_mono_left (fun _ x => ⟨0, bs ++ tail, q, b, cb, 0, GMap.empty, jc, x⟩) H

end Upd

/-! ## The entries

Each entry is proved once, as a **total thread triple** (`FTTotalTriple`): each step of its code
is local to the thread that owns the invariant and the grant (`ThreadLocal`, discharged by
`fsym`'s locality providers), so a thread may call it while other threads run
(`CAllocSpec.ofRaw`, `ZigLean/Sep/Full/AllocBridge.lean`). The sequential triples are their
readings in one thread (`FTTotalTriple.toFTotalTriple`). -/

theorem fthread_alloc (ctx : Ptr) (B : FBuf) (γ e : Nat) (n : BitVec 64) (k : Nat) (ra : BitVec 64)
    (φ : Frac) (hn : 0 < n.toNat) (hk : k < 64) (hfit : (finv ctx B γ e).fits n.toNat k) :
    FTTotalTriple ((finv ctx B γ e).own ⋆ (finv ctx B γ e).fee φ) (impl.alloc ctx n k ra)
      ((finv ctx B γ e).allocPost n.toNat k φ) := by
  fsym [alloc_upd ctx B γ e n.toNat k φ]

theorem fthread_resize (ctx : Ptr) (B : FBuf) (γ e : Nat) (s : Slice) (k : Nat) (n ra : BitVec 64)
    (A S : Nat) (K : BlockKind) (q q' φ : Frac) (tl : Array Byte) (hk : k < 64) (hn : 0 < n.toNat)
    (hfit : (finv ctx B γ e).fits n.toNat k) (hpos : 0 < s.len.toNat) (hq : q'.val ≤ q.val) :
    FTTotalTriple ((finv ctx B γ e).own ⋆ ((finv ctx B γ e).held s.ptr s.len.toNat k A S K q q' φ ⋆
      (finv ctx B γ e).relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (impl.resize ctx s k n ra)
      ((finv ctx B γ e).rresizePost s.ptr k s.len.toNat n.toNat A S K q q' φ tl) := by
  -- (WORKAROUND fsym-engine ledger #64: the released bytes' `if` is decided before the walk; an
  -- update at a return is planned against a state with an undecided `if` in both branches at once)
  by_cases hc : n.toNat < s.len.toNat <;>
  fsym [resize_other_upd ctx B γ e n.toNat s.len.toNat q' tl,
    resize_last_upd ctx B γ e (n := n.toNat) (q := q) (q' := q')]

theorem fthread_remap (ctx : Ptr) (B : FBuf) (γ e : Nat) (s : Slice) (k : Nat) (n ra : BitVec 64)
    (φ : Frac) (bs : Array Byte) (hk : k < 64) (hn : 0 < n.toNat) (hfit : (finv ctx B γ e).fits n.toNat k)
    (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FTTotalTriple ((finv ctx B γ e).own ⋆ (finv ctx B γ e).granted s.ptr k φ bs) (impl.remap ctx s k n ra)
      ((finv ctx B γ e).remapPost s.ptr k φ bs n.toNat) := by
  have hr : FTTotalTriple ((finv ctx B γ e).own ⋆ (finv ctx B γ e).granted s.ptr k φ bs)
      (heap_FixedBufferAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((finv ctx B γ e).resizePost s.ptr k φ bs n.toNat) :=
    (finv ctx B γ e).resize_granted_gen (T := FTTotalTriple) (c := impl.resize ctx s k n ra)
      (fun h hp => h.conseq hp fun _ _ x => x) FTTotalTriple.frame FTTotalTriple.ex
      (fun h hu => h.eupd_post hu)
      (fun A S K q q' tl hq _ => fthread_resize ctx B γ e s k n ra A S K q q' φ tl hk hn hfit
        (by omega) hq) hlen
  fsym [hr]

theorem fthread_free (ctx : Ptr) (B : FBuf) (γ e : Nat) (s : Slice) (k : Nat) (ra : BitVec 64)
    (φ : Frac) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FTTotalTriple ((finv ctx B γ e).own ⋆ (finv ctx B γ e).granted s.ptr k φ bs) (impl.free ctx s k ra)
      (fun _ => (finv ctx B γ e).own ⋆ (finv ctx B γ e).fee φ) := by
  fsym [free_last_upd ctx B γ e, free_other_upd ctx B γ e]

/-- **The translated `FixedBufferAllocator` satisfies the full-state allocator specification**,
in the total logic, for every allocator struct `ctx`, every buffer `B` and every epoch `e` of a
ledger `γ`: its entries' thread triples read in one thread. -/
theorem fallocSpec (ctx : Ptr) (B : FBuf) (γ e : Nat) :
    FAllocSpec FLogic.total impl ctx (finv ctx B γ e) where
  alloc len k ra φ hl hk hfit := (fthread_alloc ctx B γ e len k ra φ hl hk hfit).toFTotalTriple
  resize s k n ra A S K q q' φ tl hk hn hfit hpos hq _ :=
    (fthread_resize ctx B γ e s k n ra A S K q q' φ tl hk hn hfit hpos hq).toFTotalTriple
  remap s k n ra φ bs hk hn hfit hlen hpos :=
    (fthread_remap ctx B γ e s k n ra φ bs hk hn hfit hlen hpos).toFTotalTriple
  free s k ra φ bs _ hlen hpos := FAllocInv.free_of_emp (L := FLogic.total) (fun _ => rfl)
    (fthread_free ctx B γ e s k ra φ bs hlen hpos).toFTotalTriple

/-! ## The reset ledger: `reset` and `init` -/

/-- **A grant goes back without running code** (`ResetLedger.ret`): `free_other_upd` at the
return of `pure ()`. -/
theorem fret (ctx : Ptr) (B : FBuf) (γ e : Nat) (s : Slice) (k : Nat) (φ : Frac) (bs : Array Byte)
    (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    EUpd ((finv ctx B γ e).own ⋆ (finv ctx B γ e).granted s.ptr k φ bs)
      ((finv ctx B γ e).own ⋆ (finv ctx B γ e).fee φ) :=
  FTotalTriple.toEUpd (v := ()) (P := (finv ctx B γ e).own ⋆ (finv ctx B γ e).granted s.ptr k φ bs)
    (Q := fun _ => (finv ctx B γ e).own ⋆ (finv ctx B γ e).fee φ) (by fsym [free_other_upd ctx B γ e])

/-- The fixed buffer's variables. -/
structure FW where
  ei : Nat
  tail : Array Byte
  q : Frac
  b : BlockId
  cb : BlockId
  mN : Nat
  M : GMap
  jh : Heap

/-- **The fixed buffer is a reset ledger** (`ZigLean/Sep/Full/ResetLedger.lean`; the arena is the
other instance): its state is the ledger's authority and receipts next to its other resources,
its token names a grant of the ledger and says that the grant lies in the buffer (`FTok`), its fee
is a part of the epoch token, and a grant goes back by `fret`. -/
def ledger (ctx : Ptr) (B : FBuf) (γ e : Nat) : ResetLedger (finv ctx B γ e) γ e where
  W := FW
  M := FW.M
  F w := FFacts ctx B w.ei w.tail w.b w.cb
  B w := (wEnd ctx w.ei ⋆ fparts ctx B w.q w.b w.cb) ⋆ ((ftail B w.ei w.tail ⋆ fclaim B w.ei w.b γ e) ⋆
    (frcpt B w.b γ e ⋆ (JunkAt w.jh ⋆ fcov B w.b w.ei w.mN w.M w.jh)))
  t := none
  TF := FTok B
  own_eq := funext fun _ => propext
    ⟨fun ⟨ei, tail, q, b, cb, mN, M, jh, h⟩ => ⟨⟨ei, tail, q, b, cb, mN, M, jh⟩, h⟩,
     fun ⟨w, h⟩ => ⟨w.ei, w.tail, w.q, w.b, w.cb, w.mN, w.M, w.jh, h⟩⟩
  tok_eq := rfl
  fee_eq := rfl
  ret := fret ctx B γ e

/-- **`reset`**: from the state of epoch `e` and the whole epoch token (no grant is out) to the
state of epoch `e + 1` and its whole token, the whole buffer free again (`reset_upd`). -/
theorem freset_spec (ctx : Ptr) (B : FBuf) (γ e : Nat) :
    FTotalTriple ((finv ctx B γ e).own ⋆ epTok γ e Frac.one) (heap_FixedBufferAllocator_reset ctx)
      (fun _ => (finv ctx B γ (e + 1)).own ⋆ epTok γ (e + 1) Frac.one) := by
  fsym [reset_upd ctx B γ e]

/-- **A fixed buffer's start** (the client's ghost step after `init` stored the struct): from the
struct's words with `end_index = 0`, the parts no entry changes, the whole buffer as a region and
the untagged claim on it, a new ledger (`Upd.alloc`) whose epoch `0` holds the buffer's claim
(`EUpd.lendC`), with that epoch's whole token. -/
theorem fown_init {ctx : Ptr} {B : FBuf} {q : Frac} {b cb : BlockId} {bs : Array Byte}
    (hs : bs.size = B.cap) (hA : B.A + B.ptr.off.toNat + B.cap < 2 ^ 64) (hp0 : 0 ≤ B.ptr.off)
    (hal : (B.cA + ctx.off.toNat) % 8 = 0) (hc0 : 0 ≤ ctx.off) (hb : B.ptr.block = some b)
    (hcb : ctx.block = some cb) :
    EUpd (wEnd ctx 0 ⋆ (fparts ctx B q b cb ⋆ (up (regionIn B.ptr B.A B.S B.K 1 bs) ⋆
        bclaim b B.ptr.off.toNat (bnd B) none)))
      (FAssn.ex fun γ => fown ctx B γ 0 ⋆ epTok γ 0 Frac.one) := by
  let P := wEnd ctx 0 ⋆ (fparts ctx B q b cb ⋆ (up (regionIn B.ptr B.A B.S B.K 1 bs) ⋆
    bclaim b B.ptr.off.toNat (bnd B) none))
  refine EUpd.trans (EUpd.trans (EUpd.of_imp fun _ h => sep_comm (sep_emp.mpr h))
    (EUpd.of_upd (Upd.frame (R := P) (Upd.alloc none)))) (EUpd.ex fun γ => ?_)
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ 0 GMap.empty none ⋆ bclaim b B.ptr.off.toNat (bnd B) none) ⋆
      (epTok γ 0 Frac.one ⋆ (wEnd ctx 0 ⋆ (fparts ctx B q b cb ⋆ up (regionIn B.ptr B.A B.S B.K 1 bs)))))
    fun _ h => of_eq (by simp only [P]; ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame EUpd.lendC) (EUpd.of_imp fun r h => ⟨γ, ?_⟩)
  have e0 : B.ptr.add ((0 : Nat) : Int) = B.ptr := by
    obtain ⟨blk, o⟩ := B.ptr; simp [Ptr.add]
  have hc : FCov B b 0 0 GMap.empty (fun _ => none) :=
    ⟨fun _ _ => rfl, fun x h1 h2 => absurd h2 (by omega), fun _ _ h => by cases h⟩
  -- the junk is empty
  have h := sep_mono_right (Q := FAssn.emp) (R := JunkAt (fun _ => none))
    (fun _ x => ⟨by rw [x.1]; rfl, x.2.1, x.2.2⟩) (sep_emp.mpr h)
  have H : ((⟪FFacts ctx B 0 bs b cb⟫ ⋆ ((gauthP γ 0 GMap.empty none ⋆ LedgerRcpts γ 0 GMap.empty) ⋆
      ((wEnd ctx 0 ⋆ fparts ctx B q b cb) ⋆ ((ftail B 0 bs ⋆ fclaim B 0 b γ 0) ⋆
        (frcpt B b γ 0 ⋆ (JunkAt (fun _ => none) ⋆ fcov B b 0 0 GMap.empty (fun _ => none))))))) ⋆
      epTok γ 0 Frac.one) r :=
    of_eq (by
        simp only [fcov, fclaim, frcpt, ftail, e0, ledgerRcpts_empty, Nat.add_zero, Full.sep_emp_eq]
        ac_rfl)
      (sep_lift.mpr ⟨(show FFacts ctx B 0 bs b cb from
        ⟨⟨Nat.zero_le _, by omega, hA, hp0, hal, hc0⟩, hb, hcb⟩), sep_lift.mpr ⟨hc, h⟩⟩)
  exact sep_mono_left (fun _ x => ⟨0, bs, q, b, cb, 0, GMap.empty, fun _ => none, x⟩) H

/-! ## Creation: raw initialized storage, then the generic ghost-ledger initialization -/

/-- The hand-stated raw resources after Zig's `init` has stored the two struct words. No
allocator invariant or fee is assumed: creation allocates the ledger and establishes both. -/
def creationPre (ctx : Ptr) (B : FBuf) : FAssn :=
  FAssn.ex fun q =>
    FAssn.ex fun b => FAssn.ex fun cb => FAssn.ex fun bs : Array Byte =>
      ⟪bs.size = B.cap ∧ B.A + B.ptr.off.toNat + B.cap < 2 ^ 64 ∧ 0 ≤ B.ptr.off ∧
        (B.cA + ctx.off.toNat) % 8 = 0 ∧ 0 ≤ ctx.off ∧ B.ptr.block = some b ∧ ctx.block = some cb ∧
        (∃ len : BitVec 64, ∃ k, 0 < len.toNat ∧ k < 64 ∧ ffits B len.toNat k)⟫ ⋆
      (wEnd ctx 0 ⋆ (fparts ctx B q b cb ⋆ (up (regionIn B.ptr B.A B.S B.K 1 bs) ⋆
        bclaim b B.ptr.off.toNat (bnd B) none)))

/-- The creation post ranges over exactly the invariant family of `fallocSpec`; the ledger
name is fresh and the initial epoch is zero. `creationPost` includes the available whole fee. -/
def creationResult (ctx : Ptr) (B : FBuf) : FAssn :=
  FAssn.ex fun γ => FAssn.ex fun e =>
    (finv ctx B γ e).creationPost

/-- **Creation companion of the translated FBA contract**, for every raw initialized buffer.
The native value is already initialized; the pure return performs only the proof's ghost update. -/
def fallocSpec.creationParameters : FAllocCreationParameters := ⟨[0, 1], [2, 3]⟩

theorem fallocSpec.creation (ctx : Ptr) (B : FBuf) :
    FTotalTriple (creationPre ctx B) (pure ()) (fun _ => creationResult ctx B) := by
  unfold creationPre creationResult
  fsym [fown_init, FAllocInv.creationPost_intro]

def seedCtx : Ptr := ⟨some 0, 0⟩
def seedBuf : Ptr := ⟨some 1, 0⟩
def seedBytes : Array Byte := Enc.encode (0 : BitVec 64) ++ Enc.encode (⟨seedBuf, 16⟩ : Slice)
private def seedGlobals : List (Array Byte × Nat × BlockKind) :=
  [(seedBytes, 8, .global), (Array.replicate 16 .undef, 8, .global)]
def seedB (A1 A0 : Nat) : FBuf := ⟨seedBuf, 16, A1, 16, .global, A0⟩

theorem seedBytes_size : seedBytes.size = 24 := by decide +kernel
theorem seedDecodeEnd : Enc.decode (seedBytes.extract 0 8) = pure (0 : BitVec 64) := by
  decide +kernel
theorem seedDecodeBuf : Enc.decode (seedBytes.extract 8 24) = pure (⟨seedBuf, 16⟩ : Slice) := by
  decide +kernel

theorem seedStruct (A1 A0 : Nat) (ha : A0 % 8 = 0) {r : Res}
    (h : up (bytesAt seedCtx A0 24 .global seedBytes) r) :
    (wEnd seedCtx 0 ⋆ wBuf seedCtx (seedB A1 A0)) r := by
  refine up_sep (up_imp (fun _ hb => ?_) h)
  obtain ⟨h₁, h₂, hd, he, hb₁, hb₂⟩ := bytesAt_split (k := 8) hb (by rw [seedBytes_size]; omega)
  rw [seedBytes_size] at hb₂
  refine ⟨h₁, h₂, hd, he, ⟨A0, 24, .global, _, by simpa [seedCtx] using ha,
    by decide +kernel, seedDecodeEnd, hb₁, by decide⟩,
    ⟨A0, 24, .global, _, ?_, by decide +kernel, seedDecodeBuf, hb₂, by decide⟩⟩
  simp only [seedCtx, Ptr.add]; omega

attribute [local fsym_facts] MemFacts.bytesAt_bound MemFacts.regionIn_bound in
theorem seedBuffer (A1 A0 : Nat) :
    EUpd (up (bytesAt seedBuf A1 16 .global (Array.replicate 16 .undef)) ⋆
        (bext 1 16 .global ⋆ bclaim 1 0 16))
      (⟪A1 + 16 ≤ 2 ^ 63⟫ ⋆
        ((up (regionIn seedBuf A1 16 .global 1 (Array.replicate 16 .undef)) ⋆ bclaim 1 0 16) ⋆
        (bshare 1 Frac.one.half (bnd (seedB A1 A0)) ⋆ bauth 1 16 .global Frac.one.half))) := by
  fsym_entail

/-- The raw creation precondition holds at an actual global-memory start. This concrete start
only witnesses existence; the creation theorem above remains generic over every raw buffer. -/
theorem creationPre_admit :
    Zig.Witness.FAdmit (FAssn.ex fun ctx => FAssn.ex fun B => creationPre ctx B) := by
  have h := (Zig.Witness.FAdmit.init_claims Placement.fresh seedGlobals
    (by unfold Mem.GlobalsFit; simp [seedGlobals, seedBytes_size])
    (by simp [seedGlobals, BlockKind.mappedLo]))
  simp only [globals, gclaims, seedGlobals, List.length_cons, List.length_nil, sepN, gblock, gext,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Nat.reduceAdd, seedBytes_size,
    Array.size_replicate, Zig.Full.sep_ex_eq, Zig.Full.sep_ex_eq_right] at h
  simp only [Nat.reduceLT, ↓reduceIte, true_implies, Full.sep_emp_eq] at h
  obtain ⟨A0, h⟩ := Zig.Witness.FAdmit.ex h
  obtain ⟨A1, h⟩ := Zig.Witness.FAdmit.ex h
  let rest := bauth 1 16 .global Frac.one.half ⋆ (bext 0 24 .global ⋆ bclaim 0 0 24)
  let pre := FAssn.ex fun ctx => FAssn.ex fun B => creationPre ctx B
  suffices hh : Zig.Witness.FAdmit (pre ⋆ rest) from Zig.Witness.FAdmit.frame hh
  refine h.eupd ?_
  refine EUpd.trans (EUpd.of_imp fun _ h => ac_cast h
    (Q := ⟪A1 % 8 = 0⟫ ⋆ (⟪A0 % 8 = 0⟫ ⋆
      ((up (bytesAt seedBuf A1 16 .global (Array.replicate 16 .undef)) ⋆
          (bext 1 16 .global ⋆ bclaim 1 0 16)) ⋆
        (up (bytesAt seedCtx A0 24 .global seedBytes) ⋆
          (known 0 A0 ⋆ (known 1 A1 ⋆ (bext 0 24 .global ⋆ bclaim 0 0 24))))))) (by ac_rfl)) ?_
  refine EUpd.lift fun _ => EUpd.lift fun h0 => ?_
  refine EUpd.trans (EUpd.frame (seedBuffer A1 A0)) ?_
  refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc h) (EUpd.lift fun hbound => ?_)
  refine EUpd.of_imp fun r h => ?_
  have h := ac_cast h (Q := up (bytesAt seedCtx A0 24 .global seedBytes) ⋆
    ((up (regionIn seedBuf A1 16 .global 1 (Array.replicate 16 .undef)) ⋆ bclaim 1 0 16) ⋆
      ((known 0 A0 ⋆ (known 1 A1 ⋆ bshare 1 Frac.one.half (bnd (seedB A1 A0)))) ⋆ rest))) (by ac_rfl)
  have h := sep_mono_left (fun _ hp => seedStruct A1 A0 h0 hp) h
  have h := ac_cast h (Q := (wEnd seedCtx 0 ⋆ (fparts seedCtx (seedB A1 A0) Frac.one.half 1 0 ⋆
    (up (regionIn seedBuf A1 16 .global 1 (Array.replicate 16 .undef)) ⋆ bclaim 1 0 16))) ⋆ rest)
    (by simp only [fparts, seedB]; ac_rfl)
  refine sep_mono_left (fun _ hp => ?_) h
  refine ⟨seedCtx, seedB A1 A0, Frac.one.half, 1, 0, Array.replicate 16 .undef, sep_lift.mpr ⟨?_, hp⟩⟩
  simp only [seedB, seedCtx, seedBuf, Array.size_replicate, bnd]
  exact ⟨rfl, by omega, by decide, by simpa using h0, by decide, rfl, rfl,
    1, 0, by decide, by decide, by decide⟩

nonvacuity_witness fallocSpec.creation := by
  obtain ⟨ctx, h⟩ := Zig.Witness.FAdmit.ex creationPre_admit
  obtain ⟨B, h⟩ := Zig.Witness.FAdmit.ex h
  exact ⟨ctx, B, h⟩

end FBA

end AllocFba
