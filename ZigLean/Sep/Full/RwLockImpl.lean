import ZigLean.Sep.Full.RwLock
import ZigLean.Sep.Full.Sem
import ZigLean.Sep.Full.Share
import ZigLean.Sep.Full.LockPair

/-!
# The reader/writer lock contract, over full-state resources

What a client of `std.Io.RwLock` may assume, for every implementation proved against it (CLAUDE.md
"Build generic, prove individual items against it", `docs/interfaces.md`): `RwLockImpl Tgt` is the
code of the four uncancelable entry points `lockUncancelable`, `unlock`, `lockSharedUncancelable`
and `unlockShared` in a program's generated code, with the four rules a client uses. It is built
like `MutexImpl` (`ZigLean/Sep/Full/Mutex.lean`) and `SemImpl` (`ZigLean/Sep/Full/Sem.lean`): the
component `FRw` and the protocol `FRw.Fits` are stated once for the `Io.RwLock` family; a client
relies only on the rules; an implementation (a Zig version and target) proves them by walking its
code with the rules of its outer mutex (`MutexImpl`), its semaphore (`SemImpl`) and the atomic
rules, with the state word's value equations of `RwState.Family` (`ZigLean/Sep/Full/RwLock.lean`).

## The component (`FRw γ X Y M L C S`)

- **Layout.** The state word (`u64`, `RwState`'s ABI64 encoding: readers at bits 32..62, pending
  writers at bits 1..31, writing at bit 0) is at `p`; the semaphore `S` at `p + 8` (its mutex `L`
  and condition `C` inside it); the outer mutex `M` at `p + 32`. `M` and `L` are one two-lock pair
  over the protocol's ghost value (`FLock.Pair`, `ZigLean/Sep/Full/LockPair.lean`): they see the
  same part of a thread. `M` protects nothing (`M.R = emp`): it only serialises writers and slow
  readers.
- **Places** (`RwPh`). A client sees `out`, `rd q H` (a reader holding the share `q` of the heap
  `H`) and `wr` (the writer, holding the protected resource exclusively and the outer mutex). The
  implementation's places are `wi` (a writer's intent counted, `+2`, until its `-1`), `ww`
  (writing set, readers draining; the writer holds `M` and may sleep at the semaphore) and `rp`
  (the last reader, posting the whole resource to the waiting writer).
- **The protected resource** `R : (ThreadId → X) → FAssn` reads the client parts `x` only. Its
  heaps carry no knowledge and no ghost state (`R_plain`, the premise of `EUpd.share_whole`) and
  have one domain (`R_fixed`, the premise of `EUpd.shared_join`). A reader's share is a part
  `share H q` that joins the caller's part (`M.part`, which is `L.part`); the writer's `r` joins it
  too. The client reads the share's bytes with the share load rule (`sload`, `load_sbytesAt`).
- **The semaphore's count and pool.** The count is `1` exactly when the resource is posted
  (`RwPosted`: a writer at `ww`, no reader at `rd` and none at `rp`), and then the pool is the whole
  resource (`R`); else the count is `0` and the pool empty (`cnt_posted`, `cnt_idle`,
  `pool_posted`, `pool_idle`). So the last reader hands the resource to the sleeping writer through
  the semaphore (`SemImpl.post_wp`, `SemImpl.wait_wp`), which orders its reads before the writer.
  Only a writer at `ww` waits at the semaphore (`wx_iff`).

## The invariant (`FRw.Inv G rX m`, in the outer mutex's rest `rX`)

- The word is `Ok` and its newest message is `RwState.encode nrd nwi writing` of the threads'
  places (`nrd`: at `rd`; `nwi`: at `wi`; `writing`: a thread at `ww` or `wr`), both counts below
  `RwState.countBound`.
- At most one thread is at `ww` or `wr`, and it holds the outer mutex. A writer at `wr` has no
  reader; a last reader at `rp` has a writer at `ww` and no other reader.
- `rX` is the word's cells, the free resource `rF` and the rest of the rest. While a writer holds
  the resource, the last reader carries it or it is posted (`Busy`), `rF` is `rnil`. Else with no
  reader `rF` has `R`; with readers `rF` is the share `1 - Σ q` of the one heap `H` with `R` that
  every reader's share is of (`Σ q < 1`, so a new reader can take a half of it).
- **Ownership** (`Owns`): each access to `rF`'s bytes happened before every thread that has not
  ended or before the release clock of the word's newest message (the word's RMW chain), or is a
  read of a shared byte below the clock of a reader still at `rd` (its own reads, which its
  `unlockShared`'s release RMW orders before the word). With no reader left, every access is
  ordered: the writer's acquire RMW takes `rF` exclusively (`docs/sep-full-state.md` §Read shares).

## The protocol (`FRw.Fits P UM US okM okS`)

The protocol keeps the outer mutex with the rwlock as its primitive (`M.Fits W.prim P UM okM`: the
rwlock's and the semaphore's places next to `M`, the rwlock's own steps `Step` keep `UM`) and the
semaphore next to its mutex (`S.Fits P US okS`). Both views are views of one invariant `P.inv`
(`FLock.Fits.inv`, `FSem.Fits`'s): building both for one protocol is the two-lock product of `M`
and `L` (ledger `two-lock-product`, item (5)), which this contract takes as its interface and does
not construct. The client also shows that a writer asleep at the semaphore is not in a deadlock
(`wlive`, the semaphore's `hlive`; the outer mutex's `holdLive` covers it at `M`'s `holdsAway`),
and that `UM` is stable over the writer's nap and unnap at `M` around its semaphore wait (`mnap`,
`munnap`: a holder in the futex queue is at `holdsAway`; decision on #667, a nesting protocol
proves the nap's stability for its own `U`).

## Facts for every implementation

`Fits.inRest` (the state word in the outer mutex's rest, for the generic word rules at `M`),
`Fits.napW` / `Fits.unnapW` (the writer's nap and unnap) and `Fits.wstep` (a step of the
rwlock's own code keeps the protocol: `FLock.Fits.kstep` at `Step`), with the counts over one
thread's change (`nrd_upd`, `nwi_upd` over `cnt_upd`; `writing_upd`, `fsum_upd`, `xs_set` over
`upd_map`), are stated once
here; an instance walks its code with them.

## The rules (`RwLockImpl`)

For every protocol with the component that counts no turns (`P.cost = none`), a caller out of
every component's code with a part that has a positive unmetered fragment (it pays the code's
ticks, as `MutexImpl.lock_wp`; a Plain part has one, `Res.Plain.unmetered`):

- `lockShared_wp`: the caller gets a positive share `q` of a heap `H` with `R`, in its part, at
  `rd q H`. **Room** (`hroom`, ledger `rwlock-reader-admission-room`, maintainer decision
  2026-11-06): fewer than `2^31 - 1` other readers. Without it the `2^31`-th reader's add sets
  bit 63, the word decodes no readers, and a writer holds `R` exclusively while the readers hold
  shares of it (`tests/roadmap/sync-contracts/RwLockState.lean`, `drain_overflow`).
- `unlockShared_wp`: the reader at `rd q H` with the share in its part is back `out` without it.
- `lock_wp`: the caller gets `r` with `R` in its part, at `wr`, holding the outer mutex. **Room**:
  fewer than `2^31 - 1` other pending writers (`encode 0 (2^31-1) false + 2` carries into the
  readers).
- `unlock_wp`: the writer at `wr` whose part holds `r` with `R` at its current client part (a
  writer changes the protected value by changing `x` before `unlock`) is back `out` without it and
  without the outer mutex.

A client with a fixed set of threads discharges both `hroom` premises from its thread count.

## Scope (fail closed)

`tryLock`, `tryLockShared` and the cancelable `lock` / `lockShared` have no rule here, so a client
that calls them cannot be walked and its proof fails closed (`ZigLean/Sep/Full/RwLock.lean`, module
doc: their two open protocol obligations). The proof that a version's `Io.RwLock` code satisfies
`RwLockImpl` is the instance's (it needs the two-lock product; ledger `two-lock-product`); no
instance and no client is in this module.
-/

namespace Zig
namespace Full

open FAssn Conc Proto

/-- Where a thread is in the reader/writer lock's own code (module doc). -/
inductive RwPh where
  | out
  /-- A reader holding the share `q` of the heap `H`. -/
  | rd (q : Frac) (H : FHeap)
  /-- The last reader, carrying the whole resource to the waiting writer. -/
  | rp
  /-- A writer whose intent is counted (`+2`), before its `-1`. -/
  | wi
  /-- The writer with writing set, readers draining. -/
  | ww
  /-- The writer, holding the resource. -/
  | wr

namespace RwPh

/-- At `rd`. -/
def isRd : RwPh → Bool
  | .rd _ _ => true
  | _ => false

/-- At `ww` or `wr`: the writing bit's holder. -/
def isW : RwPh → Bool
  | .ww | .wr => true
  | _ => false

/-- At `wi`. -/
def isWi : RwPh → Bool
  | .wi => true
  | _ => false

/-- A reader's fraction (`Frac.zero` elsewhere). -/
def frac : RwPh → Frac
  | .rd q _ => q
  | _ => Frac.zero

end RwPh

/-- The resource is posted to the waiting writer (module doc): a writer at `ww`, no reader at
`rd` and none at `rp`. -/
def RwPosted {γ : Type} (ph : γ → RwPh) (G : ThreadId → γ) : Prop :=
  (∃ u, ph (G u) = .ww) ∧ (∀ u, (ph (G u)).isRd = false) ∧ ∀ u, ph (G u) ≠ .rp

/-- **A reader/writer lock** (module doc) with the outer mutex `M`, the semaphore `S` (its mutex
`L`, its condition `C`), the client parts `x` and the protected resource `R`. -/
structure FRw (γ X Y : Type) (M L : FLock γ) (C : FCond γ) (S : FSem γ Y L C)
    extends FPlace γ RwPh where
  p : Ptr
  /-- The state word. -/
  st : Word 64 8
  ptr_st : st.ptr = p
  ptr_s : S.p = p.add 8
  ptr_m : M.ptr = p.add 32
  /-- The outer mutex and the semaphore's mutex are one pair over the ghost value. -/
  pair : M.Pair L
  /-- The outer mutex protects nothing. -/
  mR : ∀ G, M.R G = emp
  /-- The client's part of a ghost value, which the resource reads. -/
  x : γ → X
  R : (ThreadId → X) → FAssn
  R_plain : ∀ xs r, R xs r → r.know = Know.none ∧ r.gh = Ghost.unit
  R_fixed : ∀ xs, (R xs).FixedDom
  /-- The client's part is not a place or a part. -/
  x_set : ∀ g a, x (set g a) = x g
  x_m : ∀ g q h, x (M.set g q h) = x g
  x_part : ∀ g r, x (M.setPart g r) = x g
  x_l : ∀ g q h, x (L.set g q h) = x g
  x_c : ∀ g c, x (C.set g c) = x g
  x_s : ∀ g s, x (S.set g s) = x g
  /-- The rwlock's place is independent of the semaphore's mutex, condition and own place (its
  independence of the outer mutex is `M.Fits W.prim`'s). -/
  lph : ∀ g a, L.ph (set g a) = L.ph g
  lheld : ∀ g a, L.held (set g a) = L.held g
  ph_l : ∀ g q h, ph (L.set g q h) = ph g
  set_l : ∀ g a q h, set (L.set g q h) a = L.set (set g a) q h
  ph_sp : ∀ g q, ph (S.place.set g q) = ph g
  sp_ph : ∀ g a, S.place.ph (set g a) = S.place.ph g
  set_sp : ∀ g a q, S.place.set (set g a) q = set (S.place.set g q) a
  /-- The semaphore's count and pool (module doc). -/
  cnt_posted : ∀ G, RwPosted ph G → S.cnt G = 1
  cnt_idle : ∀ G, ¬ RwPosted ph G → S.cnt G = 0
  pool_posted : ∀ G, RwPosted ph G → S.Pool (S.xs G) = R fun u => x (G u)
  pool_idle : ∀ G, ¬ RwPosted ph G → S.Pool (S.xs G) = emp
  /-- Only the writer at `ww` waits at the semaphore. -/
  wx_iff : ∀ g, S.wx g ↔ ph g = .ww

namespace FRw

variable {γ X Y : Type} {M L : FLock γ} {C : FCond γ} {S : FSem γ Y L C} (W : FRw γ X Y M L C S)

/-- The client parts of the ghost values. -/
def xs (G : ThreadId → γ) : ThreadId → X := fun u => W.x (G u)

/-- The readers among the threads of `m`. -/
def nrd (G : ThreadId → γ) (m : Mem) : Nat :=
  tsum m.threads.size fun u => if (W.ph (G u)).isRd then 1 else 0

/-- The pending writers among the threads of `m`. -/
def nwi (G : ThreadId → γ) (m : Mem) : Nat :=
  tsum m.threads.size fun u => if (W.ph (G u)).isWi then 1 else 0

/-- A thread of `m` holds the writing bit. -/
def writing (G : ThreadId → γ) (m : Mem) : Bool :=
  (List.range m.threads.size).any fun u => (W.ph (G u)).isW

/-- The readers' fractions. -/
def fsum (G : ThreadId → γ) (m : Mem) : Rat :=
  ftot (fun u => (W.ph (G u)).frac) m.threads.size

/-- The resource is away from the rest: the writer holds it, the last reader carries it, or it is
posted. -/
def Busy (G : ThreadId → γ) : Prop :=
  (∃ u, W.ph (G u) = .wr) ∨ (∃ u, W.ph (G u) = .rp) ∨ RwPosted W.ph G

/-- **The free resource** `rF` in the rest (module doc). -/
def FreeRes (G : ThreadId → γ) (m : Mem) (rF : Res) : Prop :=
  (W.Busy G → rF = rnil) ∧
  (¬ W.Busy G → W.nrd G m = 0 → W.R (W.xs G) rF) ∧
  (¬ W.Busy G → W.nrd G m ≠ 0 → ∃ H f, W.R (W.xs G) ⟨H, Know.none, Ghost.unit⟩ ∧
    0 < f.val ∧ f.val + W.fsum G m = 1 ∧ rF = shareRes H f ∧
    ∀ u q H', W.ph (G u) = .rd q H' → H' = H ∧ 0 < q.val)

/-- **The free resource is owned through the word** (module doc). -/
def Owns (G : ThreadId → γ) (m : Mem) (r : Res) : Prop :=
  ∀ e ∈ m.footprint, (e.Touches r.excl ∨ e.Touches r.shared ∨ m.blocks.size ≤ e.block) →
    LockWord.LiveLe (M.pl G) m e.clock ∨
    VClock.le e.clock ((W.st.hist m).back!).relClock = true ∨
    (e.kind.isWrite = false ∧ e.Touches r.shared ∧
      ∃ u, (W.ph (G u)).isRd = true ∧ VClock.le e.clock (m.clocks[u]!) = true)

/-- **The reader/writer invariant** in the outer mutex's rest `rX` (module doc). -/
structure Inv (G : ThreadId → γ) (rX : Res) (m : Mem) : Prop where
  ok : W.st.Ok m fun u => M.ph (G u) ≠ .gone
  /-- A thread in the rwlock's code exists. -/
  ex : ∀ u, W.ph (G u) ≠ .out → u < m.threads.size
  room : W.nrd G m < RwState.countBound ∧ W.nwi G m < RwState.countBound
  /-- The word's newest message encodes the places. -/
  word : ∃ e, (W.st.hist m).back? = some e ∧
    e.Val (RwState.encode (W.nrd G m) (W.nwi G m) (W.writing G m))
  /-- At most one thread holds the writing bit, and it holds the outer mutex. -/
  one : ∀ u v, (W.ph (G u)).isW → (W.ph (G v)).isW → u = v
  wm : ∀ u, (W.ph (G u)).isW → (M.ph (G u)).held = true
  /-- The writer at `wr` has no reader. -/
  wr : ∀ u, W.ph (G u) = .wr → W.nrd G m = 0
  /-- The last reader at `rp` is the only one in the readers' code, with a writer at `ww`. -/
  rp : ∀ u, W.ph (G u) = .rp → W.nrd G m = 0 ∧ (∃ w, W.ph (G w) = .ww) ∧
    ∀ v, W.ph (G v) = .rp → v = u
  /-- The rest: the word's cells, the free resource, the rest of the rest. -/
  rest : ∃ rF rO, rX = rsum (W.st.cellsR m) (rsum rF rO) ∧
    (∀ l, W.st.In l → rF.heap l = none ∧ rO.heap l = none) ∧
    FHeap.Disjoint rF.heap rO.heap ∧ W.FreeRes G m rF ∧ W.Owns G m rF

/-- The rwlock's and the semaphore's places of a thread. -/
def place : FPlace γ (RwPh × (CPh × SPh)) where
  ph g := (W.ph g, S.place.ph g)
  set g q := W.set (S.place.set g q.2) q.1
  ph_set g q := by
    show (W.ph (W.set (S.place.set g q.2) q.1), S.place.ph (W.set (S.place.set g q.2) q.1)) = q
    rw [W.ph_set, W.sp_ph, S.place.ph_set]
  set_set g q q' := by
    show W.set (S.place.set (W.set (S.place.set g q.2) q.1) q'.2) q'.1 =
      W.set (S.place.set g q'.2) q'.1
    rw [W.set_sp, W.set_set, S.place.set_set]
  set_self g := by
    show W.set (S.place.set g (S.place.ph g)) (W.ph g) = g
    rw [S.place.set_self, W.set_self]

/-- **The rwlock's own steps** by thread `t` (module doc): an atomic step at the state word (or no
memory step), which may move the free resource between the rest and `t`'s part and change `t`'s
place in the rwlock's code; `t`'s places in the mutexes' and the semaphore's code, the client parts
and the other threads stay, the rest of the rest stays, and both the outer mutex's invariant and
the rwlock's hold before and after it. -/
def Step (t : ThreadId) (G : ThreadId → γ) (rX : Res) (m : Mem) (G' : ThreadId → γ) (rX' : Res)
    (m' : Mem) : Prop :=
  M.Inv G rX m ∧ W.Inv G rX m ∧ M.Inv G' rX' m' ∧ W.Inv G' rX' m' ∧ m.current = t ∧
  (m' = m ∨ RestStep W.st.In m m') ∧
  (∀ u, u ≠ t → G' u = G u) ∧ (∀ u, W.x (G' u) = W.x (G u)) ∧
  M.ph (G' t) = M.ph (G t) ∧ M.held (G' t) = M.held (G t) ∧
  L.ph (G' t) = L.ph (G t) ∧ L.held (G' t) = L.held (G t) ∧
  S.place.ph (G' t) = S.place.ph (G t) ∧
  ∃ rF rF' rO, rX = rsum (W.st.cellsR m) (rsum rF rO) ∧ rX' = rsum (W.st.cellsR m') (rsum rF' rO)

/-- **The rwlock as a primitive next to its outer mutex** `M` (module doc): its places with the
semaphore's; a thread runs `M`'s code at `out` (a slow reader's lock, a writer's unlock tail), `wi`
(a writer's lock) or `rd` (a slow reader's unlock), out of the semaphore's code; no role; the rest
keeps the rwlock's invariant; a step is the rwlock's own (`Step`). -/
abbrev prim : FPrim γ where
  Ph := RwPh × (CPh × SPh)
  pl := W.place
  out := (.out, (.out, .out))
  calm q := (q.1 = .out ∨ q.1 = .wi ∨ q.1.isRd = true) ∧ q.2 = (.out, .out)
  Role := Empty
  role i := nomatch i
  Sub G rX m := W.Inv G rX m
  Apart := W.st.ApartL M.toLockWord
  Step := W.Step

/-- A thread out of the rwlock's code and of its components' code, holding nothing. -/
def Out (g : γ) : Prop :=
  W.ph g = .out ∧ M.ph g = .out ∧ M.held g = rnil ∧ L.ph g = .out ∧ L.held g = rnil ∧
    C.ph g = .out ∧ S.ph g = .out

/-- **A protocol with the reader/writer lock** (module doc): the outer mutex with the rwlock as
its primitive, the semaphore next to its mutex (the two-lock product's interface), and the
writer's liveness at the semaphore. -/
structure Fits {Tgt : Type} (P : Proto Tgt γ) (UM US : (ThreadId → γ) → Res → Mem → Prop)
    (okM okS : γ → Prop) : Prop where
  m : M.Fits W.prim P UM okM
  s : S.Fits P US okS
  /-- The rwlock's place is read by neither `ok`: a thread runs either mutex's code at any of
  them (`M.Fits.ok_calm` covers only the calm places, and the writer moves `wr → out` before its
  outer unlock and `ww → wr` before it returns from `lock`). -/
  okM_set : ∀ g a, okM (W.set g a) ↔ okM g
  okS_set : ∀ g a, okS (W.set g a) ↔ okS g
  /-- Neither lock's code is `ok` of the other's view: a thread's place, held resource and part in
  one lock do not change whether it may run the other's code. -/
  okS_m : ∀ g q h, okS (M.set g q h) ↔ okS g
  okS_part : ∀ g r, okS (M.setPart g r) ↔ okS g
  okM_l : ∀ g q h, okM (L.set g q h) ↔ okM g
  /-- **The writer's nap and unnap around its semaphore wait** (`FLock.Fits.nap`/`unnap`'s `hU`
  at the outer mutex): the writer at `ww` holds the outer mutex while it may sleep in the
  semaphore's code, and a holder in the futex queue is at `holdsAway` (`LockWord.WInv.notQ`,
  `WInv.nap`). `UM`'s stability over this relabel is the nesting protocol's obligation (decision
  on #667): `FLock.Fits.stable` does not give it, since a nap is no step of the outer mutex's
  code and meets no release premise. The unnap's other premise (the writer is not in the futex
  queue) follows from the semaphore's mutex's view (`Fits.unnapW`). -/
  mnap : ∀ G rX m t g, W.ph g = .ww → L.ph g = .out → M.ph g = .holds →
    UM (upd G t g) rX m → M.Inv (upd G t g) rX m →
    UM (upd G t (M.set g .holdsAway (M.held g))) rX m
  munnap : ∀ G rX m t g, W.ph g = .ww → L.ph g = .out → M.ph g = .holdsAway →
    UM (upd G t g) rX m → M.Inv (upd G t g) rX m →
    UM (upd G t (M.set g .holds (M.held g))) rX m
  /-- **The writer asleep at the semaphore is not in a deadlock** (`SemImpl.wait_wp`'s `hlive` for
  the writer at `ww`). -/
  wlive : ∀ t G₁ m₁, W.ph (G₁ t) = .ww → (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) →
    L.ph (G₁ t) = .away → P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 →
    (∀ v, (C.ph (G₁ v)).sig = false) → S.cnt G₁ = 0 → P.Live t G₁ m₁

/-! ## Facts of the invariant -/

variable {W}

/-- With every thread out of the rwlock's code there is no reader. -/
theorem nrd_out {G : ThreadId → γ} {m : Mem} (h : ∀ u, W.ph (G u) = .out) : W.nrd G m = 0 :=
  tsum_eq_zero fun u _ => by simp [h u, RwPh.isRd]

/-- With every thread out of the rwlock's code there is no pending writer. -/
theorem nwi_out {G : ThreadId → γ} {m : Mem} (h : ∀ u, W.ph (G u) = .out) : W.nwi G m = 0 :=
  tsum_eq_zero fun u _ => by simp [h u, RwPh.isWi]

/-- With every thread out of the rwlock's code no thread is writing. -/
theorem writing_out {G : ThreadId → γ} {m : Mem} (h : ∀ u, W.ph (G u) = .out) :
    W.writing G m = false := by
  simp [writing, h, RwPh.isW]

/-- With every thread out of the rwlock's code the resource is not away from the rest. -/
theorem not_busy_out {G : ThreadId → γ} (h : ∀ u, W.ph (G u) = .out) : ¬ W.Busy G := by
  rintro (⟨u, hu⟩ | ⟨u, hu⟩ | ⟨⟨u, hu⟩, -, -⟩) <;> rw [h u] at hu <;> cases hu

/-- **A fresh lock** (non-vacuity of the invariant): every thread out of its code, the word's
newest message `RwState.encode 0 0 false` (the value `0`), and the free resource with `R`, owned through
the word, in the rest. -/
theorem Inv.start {G : ThreadId → γ} {m : Mem} {rF rO : Res}
    (hok : W.st.Ok m fun u => M.ph (G u) ≠ .gone) (hout : ∀ u, W.ph (G u) = .out)
    (hw : ∃ e, (W.st.hist m).back? = some e ∧ e.Val (RwState.encode 0 0 false))
    (hR : W.R (W.xs G) rF) (hoff : ∀ l, W.st.In l → rF.heap l = none ∧ rO.heap l = none)
    (hd : FHeap.Disjoint rF.heap rO.heap) (hown : W.Owns G m rF) :
    W.Inv G (rsum (W.st.cellsR m) (rsum rF rO)) m where
  ok := hok
  ex u hu := absurd (hout u) hu
  room := by rw [nrd_out hout, nwi_out hout]; exact ⟨Nat.two_pow_pos _, Nat.two_pow_pos _⟩
  word := by
    rw [nrd_out hout, nwi_out hout, writing_out hout]
    exact hw
  one u _ hu := by rw [hout u] at hu; cases hu
  wm u hu := by rw [hout u] at hu; cases hu
  wr u hu := by rw [hout u] at hu; cases hu
  rp u hu := by rw [hout u] at hu; cases hu
  rest := ⟨rF, rO, rfl, hoff, hd,
    ⟨fun hb => absurd hb (not_busy_out hout), fun _ _ => hR,
      fun _ hn => absurd (nrd_out hout) hn⟩, hown⟩

/-! ## Counts over one thread's change -/

/-- The client parts do not read the rwlock's place. -/
theorem xs_set (G : ThreadId → γ) (t : ThreadId) (g : γ) (a : RwPh) :
    W.xs (upd G t (W.set g a)) = W.xs (upd G t g) :=
  upd_map W.x G t (W.x_set g a)

/-- One thread's change moves a count of the places with `p` by its own (`tsum_upd`). -/
theorem cnt_upd (p : RwPh → Bool) (G : ThreadId → γ) {N t : Nat} (ht : t < N) (g g' : γ) :
    tsum N (fun u => if p (W.ph (upd G t g' u)) then 1 else 0) + (if p (W.ph g) then 1 else 0) =
      tsum N (fun u => if p (W.ph (upd G t g u)) then 1 else 0) +
        (if p (W.ph g') then 1 else 0) := by
  have h := tsum_upd (g := fun u => if p (W.ph (upd G t g u)) then 1 else 0)
    (g' := fun u => if p (W.ph (upd G t g' u)) then 1 else 0) ht fun u e => by
      show (if p (W.ph (upd G t g' u)) then 1 else 0) = (if p (W.ph (upd G t g u)) then 1 else 0)
      rw [upd_ne _ _ e, upd_ne _ _ e]
  simpa only [upd_self] using h

/-- One thread's change moves the readers' count by its own. -/
theorem nrd_upd (G : ThreadId → γ) {m : Mem} {t : ThreadId} (ht : t < m.threads.size)
    (g g' : γ) :
    W.nrd (upd G t g') m + (if (W.ph g).isRd then 1 else 0) =
      W.nrd (upd G t g) m + (if (W.ph g').isRd then 1 else 0) :=
  cnt_upd (W := W) RwPh.isRd G ht g g'

/-- One thread's change moves the pending writers' count by its own. -/
theorem nwi_upd (G : ThreadId → γ) {m : Mem} {t : ThreadId} (ht : t < m.threads.size)
    (g g' : γ) :
    W.nwi (upd G t g') m + (if (W.ph g).isWi then 1 else 0) =
      W.nwi (upd G t g) m + (if (W.ph g').isWi then 1 else 0) :=
  cnt_upd (W := W) RwPh.isWi G ht g g'

/-- A change that keeps whether the thread holds the writing bit keeps `writing`. -/
theorem writing_upd (G : ThreadId → γ) (m : Mem) (t : ThreadId) {g g' : γ}
    (h : (W.ph g').isW = (W.ph g).isW) : W.writing (upd G t g') m = W.writing (upd G t g) m :=
  congrArg (fun F => (List.range m.threads.size).any F) (upd_map (fun g => (W.ph g).isW) G t h)

/-- A change that keeps the thread's fraction keeps the readers' fractions. -/
theorem fsum_upd (G : ThreadId → γ) (m : Mem) (t : ThreadId) {g g' : γ}
    (h : (W.ph g').frac = (W.ph g).frac) : W.fsum (upd G t g') m = W.fsum (upd G t g) m :=
  congrArg (ftot · m.threads.size) (upd_map (fun g => (W.ph g).frac) G t h)

/-! ## Ownership over a step at the state word -/

/-- **Ownership survives a release write at the state word** (`Owns`): an old access keeps its
clause (the threads' clocks and the newest release clock grow, `hcl`, `hrel`; a reader that leaves
`rd` is one the new release clock covers, `hrd`), and a new access is the writer's, before its new
clock (`hfp`: `Word.atomicRmw_fpNew`), which the new message's release clock covers (`hnew`:
`Word.rmwEnt` of a release RMW merges the writer's clock). -/
theorem Owns.step {G G' : ThreadId → γ} {m m' : Mem} {r : Res} {t : ThreadId}
    (ho : W.Owns G m r)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ VClock.le e.clock (m'.clocks[t]!) = true)
    (hth : m'.threads = m.threads)
    (hcl : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hbs : m.blocks.size ≤ m'.blocks.size)
    (hrel : VClock.le ((W.st.hist m).back!).relClock ((W.st.hist m').back!).relClock = true)
    (hnew : VClock.le (m'.clocks[t]!) ((W.st.hist m').back!).relClock = true)
    (hM : ∀ u, M.ph (G' u) ≠ .gone → M.ph (G u) ≠ .gone)
    (hrd : ∀ u, (W.ph (G u)).isRd = true → (W.ph (G' u)).isRd = true ∨
      VClock.le (m.clocks[u]!) ((W.st.hist m').back!).relClock = true) :
    W.Owns G' m' r := by
  intro e he hT
  rcases hfp e he with he₀ | hc
  · have hT₀ : e.Touches r.excl ∨ e.Touches r.shared ∨ m.blocks.size ≤ e.block :=
      hT.imp_right (Or.imp_right fun h => Nat.le_trans hbs h)
    rcases ho e he₀ hT₀ with h | h | ⟨hw, hs, u, hu, hcu⟩
    · exact .inl (LockWord.LiveLe.weaken hM (LockWord.LiveLe.mono hth (fun u _ => hcl u) h))
    · exact .inr (.inl (VClock.le_trans h hrel))
    · rcases hrd u hu with hu' | hu'
      · exact .inr (.inr ⟨hw, hs, u, hu', VClock.le_trans hcu (hcl u)⟩)
      · exact .inr (.inl (VClock.le_trans hcu hu'))
  · exact .inr (.inl (VClock.le_trans hc hnew))

/-! ## The protocol's facts for every implementation -/

section Proto

variable {Tgt : Type} {P : Proto Tgt γ} {UM US : (ThreadId → γ) → Res → Mem → Prop}
  {okM okS : γ → Prop}

/-- **The state word lies in the outer mutex's rest** (`Word.InRest`, for the generic word rules
at `M`: `FLock.wp_wordLoad`, `wp_wordRmw`, `wp_wordWeakCas`), live for the threads not gone from
`M` (`Inv.ok`, `Inv.rest`). -/
theorem Fits.inRest (hW : W.Fits P UM US okM okS) :
    W.st.InRest UM fun g => M.ph g ≠ .gone := by
  intro G rX m hU
  have hI : W.Inv G rX m := hW.m.sub G rX m hU
  obtain ⟨rF, rO, he, hoff, -⟩ := hI.rest
  refine ⟨hI.ok, rsum rF rO, he, fun l hl => ?_⟩
  show (rF.heap ∪ rO.heap) l = none
  rw [FHeap.union_apply, (hoff l hl).1, (hoff l hl).2]
  rfl

/-- **The writer's nap** before its semaphore wait (`FLock.Fits.nap` at the outer mutex, with
`mnap`). -/
theorem Fits.napW (hW : W.Fits P UM US okM okS) {G : ThreadId → γ} {m : Mem} {t : ThreadId}
    {g : γ} (hw : W.ph g = .ww) (hl : L.ph g = .out) (hg : M.ph g = .holds)
    (hi : P.inv (upd G t g) m) : P.inv (upd G t (M.set g .holdsAway (M.held g))) m :=
  FLock.Fits.nap hW.m hg hi fun rX hU hI => hW.mnap G rX m t g hw hl hg hU hI

/-- **The writer's unnap** after its semaphore wait (`FLock.Fits.unnap` at the outer mutex, with
`munnap`): out of the semaphore's mutex's code, the writer is not in the futex queue
(`LockWord.WInv.notQ` in the semaphore's mutex's view of the same invariant). -/
theorem Fits.unnapW (hW : W.Fits P UM US okM okS) {G : ThreadId → γ} {m : Mem} {t : ThreadId}
    {g : γ} (hw : W.ph g = .ww) (hl : L.ph g = .out) (hg : M.ph g = .holdsAway)
    (hi : P.inv (upd G t g) m) : P.inv (upd G t (M.set g .holds (M.held g))) m := by
  obtain ⟨rX, hL, -⟩ := (hW.s.inv _ _).mp hi
  have hp : L.pl (upd G t g) t = .out := by
    show L.ph (upd G t g t) = .out
    rw [upd_self, hl]
  exact FLock.Fits.unnap hW.m hg hi
    (hL.w.notQ (by rw [hp]; decide) (by rw [hp]; decide) (by rw [hp]; decide))
    fun rX hU hI => hW.munnap G rX m t g hw hl hg hU hI

/-- **A step of the rwlock's own code keeps the protocol** (`FLock.Fits.kstep` at `Step`): the
step's facts, given the rwlock's invariant before it (`Fits.sub`). -/
theorem Fits.wstep (hW : W.Fits P UM US okM okS) {t : ThreadId} {G G' : ThreadId → γ}
    {rX rX' : Res} {m m' : Mem} (hU : UM G rX m)
    (hs : W.Inv G rX m → W.Step t G rX m G' rX' m') : P.inv G' m' :=
  have hst := hs (hW.m.sub G rX m hU)
  (hW.m.inv G' m').mpr ⟨rX', hst.2.2.1, hW.m.kstep t G rX m G' rX' m' (.inl hst) hU⟩

end Proto

end FRw

/-- **A reader/writer lock implementation** in generated code with the contended value `c` of
its two mutexes (module doc): the four uncancelable entry points and their rules, for every
protocol with the component (`FRw.Fits`) that counts no turns. -/
structure RwLockImpl (Tgt : Type) where
  /-- `lockUncancelable(p, io)`. -/
  lock : Ptr → Io → ConcM Tgt Unit
  /-- `unlock(p, io)`. -/
  unlock : Ptr → Io → ConcM Tgt Unit
  /-- `lockSharedUncancelable(p, io)`. -/
  lockShared : Ptr → Io → ConcM Tgt Unit
  /-- `unlockShared(p, io)`. -/
  unlockShared : Ptr → Io → ConcM Tgt Unit
  /-- The contended value of the outer mutex and of the semaphore's mutex (`LockWord.c`). -/
  c : Nat
  lockShared_wp : ∀ {γ X Y : Type} {M L : FLock γ} {C : FCond γ} {S : FSem γ Y L C}
    {W : FRw γ X Y M L C S} {P : Proto Tgt γ} {UM US : (ThreadId → γ) → Res → Mem → Prop}
    {okM okS : γ → Prop}, W.Fits P UM US okM okS → P.cost = none → M.c = c → L.c = c →
    ∀ {p : Ptr}, p = W.p → ∀ (t : ThreadId) (g : γ), W.Out g → okM g → okS g →
    0 < (M.part g).gh.ac.frag .unmetered →
    -- room (`rwlock-reader-admission-room`): fewer than `2^31 - 1` other readers
    (∀ G m, P.inv G m → W.ph (G t) = .out → W.nrd G m + 1 < RwState.countBound) →
    ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat), P.inv (upd G t g) m → m.current = t →
    P.WP t (lockShared p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ (q : Frac) (H : FHeap), 0 < q.val ∧ W.R (W.xs (upd G' t g)) ⟨H, Know.none, Ghost.unit⟩ ∧
        P.inv (upd G' t (W.set (M.setPart g (rsum (M.part g) (shareRes H q))) (.rd q H))) m')
      G m d
  unlockShared_wp : ∀ {γ X Y : Type} {M L : FLock γ} {C : FCond γ} {S : FSem γ Y L C}
    {W : FRw γ X Y M L C S} {P : Proto Tgt γ} {UM US : (ThreadId → γ) → Res → Mem → Prop}
    {okM okS : γ → Prop}, W.Fits P UM US okM okS → P.cost = none → M.c = c → L.c = c →
    ∀ {p : Ptr}, p = W.p → ∀ (t : ThreadId) (g : γ) (r₀ : Res) (q : Frac) (H : FHeap),
    W.ph g = .rd q H → M.ph g = .out → M.held g = rnil → L.ph g = .out → L.held g = rnil →
    C.ph g = .out → S.ph g = .out → M.part g = rsum r₀ (shareRes H q) → okM g → okS g →
    0 < r₀.gh.ac.frag .unmetered →
    ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat), P.inv (upd G t g) m → m.current = t →
    P.WP t (unlockShared p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (W.set (M.setPart g r₀) .out)) m') G m d
  lock_wp : ∀ {γ X Y : Type} {M L : FLock γ} {C : FCond γ} {S : FSem γ Y L C}
    {W : FRw γ X Y M L C S} {P : Proto Tgt γ} {UM US : (ThreadId → γ) → Res → Mem → Prop}
    {okM okS : γ → Prop}, W.Fits P UM US okM okS → P.cost = none → M.c = c → L.c = c →
    ∀ {p : Ptr}, p = W.p → ∀ (t : ThreadId) (g : γ), W.Out g → okM g → okS g →
    0 < (M.part g).gh.ac.frag .unmetered →
    -- room (`rwlock-reader-admission-room`): fewer than `2^31 - 1` other pending writers
    (∀ G m, P.inv G m → W.ph (G t) = .out → W.nwi G m + 1 < RwState.countBound) →
    ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat), P.inv (upd G t g) m → m.current = t →
    P.WP t (lock p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ r rM, W.R (W.xs (upd G' t g)) r ∧ FHeap.Disjoint (M.part g).heap r.heap ∧
        P.inv (upd G' t (M.set (W.set (M.setPart g (rsum (M.part g) r)) .wr) .holds rM)) m')
      G m d
  unlock_wp : ∀ {γ X Y : Type} {M L : FLock γ} {C : FCond γ} {S : FSem γ Y L C}
    {W : FRw γ X Y M L C S} {P : Proto Tgt γ} {UM US : (ThreadId → γ) → Res → Mem → Prop}
    {okM okS : γ → Prop}, W.Fits P UM US okM okS → P.cost = none → M.c = c → L.c = c →
    ∀ {p : Ptr}, p = W.p → ∀ (t : ThreadId) (g : γ) (r₀ r : Res),
    W.ph g = .wr → M.ph g = .holds → L.ph g = .out → L.held g = rnil → C.ph g = .out →
    S.ph g = .out → M.part g = rsum r₀ r → FHeap.Disjoint r₀.heap r.heap → okM g → okS g →
    0 < r₀.gh.ac.frag .unmetered →
    (∀ G, W.R (W.xs (upd G t g)) r) →
    ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat), P.inv (upd G t g) m → m.current = t →
    P.WP t (unlock p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (M.set (W.set (M.setPart g r₀) .out) .out rnil)) m') G m d

end Full
end Zig
