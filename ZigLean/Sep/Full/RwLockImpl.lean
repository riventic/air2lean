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
  `RwState.countBound`. Every message encodes counts below it (`msgs`: a reader's fast path adds
  to a value it read, which may be older than the newest).
- At most one thread is at `ww` or `wr`, and it holds the outer mutex. A writer at `wr` has no
  reader; a last reader at `rp` has a writer at `ww` and no other reader.
- `rX` is the word's cells, the free resource `rF` (which owns no byte of the word, not even by a
  share, so a read of the word touches none of its bytes: `Inv.load`) and the rest of the rest.
  While a writer holds the resource, the last reader carries it or it is posted (`Busy`), `rF` is
  `rnil`. Else with no reader `rF` has `R`; with readers `rF` is the share `1 - Σ q` of the one
  heap `H` with `R` that every reader's share is of (`Σ q < 1`, so a new reader can take a part
  of it: `Inv.addR`).
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
  /-- Every message encodes counts below the bound (a reader's fast path adds to a value it read,
  which may be older than the newest). -/
  msgs : ∀ j < (W.st.hist m).size, ∃ r w a, r < RwState.countBound ∧ w < RwState.countBound ∧
    (W.st.hist m)[j]!.Val (RwState.encode r w a)
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
    (∀ l, W.st.In l → rF.owned l = none ∧ rO.heap l = none) ∧
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

/-- The newest write, as the last index. -/
theorem last_of_back {a : Array Word.Entry} {e : Word.Entry} (h : a.back? = some e) :
    a[a.size - 1]! = e := by
  simp only [Array.back?] at h
  simp [getElem!_def, h]

/-- The newest write after a push. -/
theorem back_push (a : Array Word.Entry) (x : Word.Entry) : (a.push x).back! = x := by
  rw [Array.back!, getElem!_pos _ _ (by simp)]
  simp

/-- A resource without ghost state owns exactly its cells. -/
theorem _root_.Zig.Full.Res.owned_plain {r : Res} (hg : r.gh = Ghost.unit) {l : Loc}
    (h : r.heap l = none) : r.owned l = none := by
  obtain ⟨H, k, g⟩ := r
  dsimp only at hg h
  subst hg
  exact Classical.byContradiction fun hn =>
    (Res.owned_ne.mp hn).elim (· h) fun ⟨_, hc⟩ => absurd hc Rat.lt_irrefl

/-- A resource without ghost state has no shared byte. -/
theorem _root_.Zig.Full.Res.shared_plain {r : Res} (hg : r.gh = Ghost.unit) (l : Loc) :
    r.shared l = none := by
  obtain ⟨H, k, g⟩ := r
  dsimp only at hg
  subst hg
  exact Classical.byContradiction fun hn =>
    absurd (Res.shared_ne.mp hn).2.2.choose_spec Rat.lt_irrefl

/-- A byte a resource does not own is not in its heap. -/
theorem _root_.Zig.Full.Res.heap_of_owned {r : Res} {l : Loc} (h : r.owned l = none) :
    r.heap l = none :=
  Classical.byContradiction fun e => Res.owned_of_heap e h

/-- **A fresh lock** (non-vacuity of the invariant): every thread out of its code, the word's one
message `RwState.encode 0 0 false` (the value `0`), and the free resource with `R`, owned through
the word, in the rest. -/
theorem Inv.start {G : ThreadId → γ} {m : Mem} {rF rO : Res}
    (hok : W.st.Ok m fun u => M.ph (G u) ≠ .gone) (hout : ∀ u, W.ph (G u) = .out)
    (hW : (W.st.hist m).size = 1) (hW0 : (W.st.hist m)[0]!.Val (RwState.encode 0 0 false))
    (hR : W.R (W.xs G) rF) (hoff : ∀ l, W.st.In l → rF.heap l = none ∧ rO.heap l = none)
    (hd : FHeap.Disjoint rF.heap rO.heap) (hown : W.Owns G m rF) :
    W.Inv G (rsum (W.st.cellsR m) (rsum rF rO)) m where
  ok := hok
  ex u hu := absurd (hout u) hu
  room := by rw [nrd_out hout, nwi_out hout]; exact ⟨Nat.two_pow_pos _, Nat.two_pow_pos _⟩
  word := by
    rw [nrd_out hout, nwi_out hout, writing_out hout]
    cases e : (W.st.hist m).back? with
    | none => simp [Array.back?, hW] at e
    | some x => exact ⟨x, rfl, by rw [← last_of_back e, hW]; exact hW0⟩
  msgs j hj := by
    obtain rfl : j = 0 := by omega
    exact ⟨0, 0, false, Nat.two_pow_pos _, Nat.two_pow_pos _, hW0⟩
  one u _ hu := by rw [hout u] at hu; cases hu
  wm u hu := by rw [hout u] at hu; cases hu
  wr u hu := by rw [hout u] at hu; cases hu
  rp u hu := by rw [hout u] at hu; cases hu
  rest := ⟨rF, rO, rfl,
    fun l hl => ⟨Res.owned_plain (W.R_plain _ _ hR).2 (hoff l hl).1, (hoff l hl).2⟩, hd,
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

/-- Two fraction functions that agree below `n` have one sum below `n`. -/
theorem _root_.Zig.Full.ftot_eq_lt {f g : Nat → Frac} :
    ∀ {n}, (∀ k, k < n → f k = g k) → ftot f n = ftot g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [ftot]
    rw [ftot_eq_lt fun k hk => h k (by omega), h n (by omega)]

/-- **One point changes** (`tsum_upd` for fractions): the sum moves by the difference there. -/
theorem _root_.Zig.Full.ftot_upd {f g : Nat → Frac} {t : Nat} (h : ∀ u, u ≠ t → f u = g u) :
    ∀ {N}, t < N → ftot f N + (g t).val = ftot g N + (f t).val
  | 0, ht => absurd ht (Nat.not_lt_zero _)
  | N + 1, ht => by
    simp only [ftot]
    by_cases e : N = t
    · subst e
      rw [ftot_eq_lt fun k hk => h k (by omega)]
      grind
    · have := ftot_upd h (N := N) (by omega)
      rw [h N e]
      grind

/-- One thread's change moves the readers' fractions by its own. -/
theorem fsum_upd (G : ThreadId → γ) {m : Mem} {t : ThreadId} (ht : t < m.threads.size)
    (g g' : γ) :
    W.fsum (upd G t g') m + (W.ph g).frac.val = W.fsum (upd G t g) m + (W.ph g').frac.val := by
  have h := ftot_upd (f := fun u => (W.ph (upd G t g' u)).frac)
    (g := fun u => (W.ph (upd G t g u)).frac) (fun u e => by simp only [upd_ne _ _ e]) ht
  simp only [upd_self] at h
  exact h

/-- **`t` moves to `b`**: the readers' count by its old and new place (`nrd_upd`). -/
theorem nrd_mv (G : ThreadId → γ) {m : Mem} {t : ThreadId} (ht : t < m.threads.size) (b : RwPh) :
    W.nrd (upd G t (W.set (G t) b)) m + (if (W.ph (G t)).isRd then 1 else 0) =
      W.nrd G m + (if b.isRd then 1 else 0) := by
  have h := nrd_upd (W := W) G ht (G t) (W.set (G t) b)
  rwa [upd_same, W.ph_set] at h

/-- The pending writers' count after `t` moves to `b` (`nwi_upd`). -/
theorem nwi_mv (G : ThreadId → γ) {m : Mem} {t : ThreadId} (ht : t < m.threads.size) (b : RwPh) :
    W.nwi (upd G t (W.set (G t) b)) m + (if (W.ph (G t)).isWi then 1 else 0) =
      W.nwi G m + (if b.isWi then 1 else 0) := by
  have h := nwi_upd (W := W) G ht (G t) (W.set (G t) b)
  rwa [upd_same, W.ph_set] at h

/-- The readers' fractions after `t` moves to `b` (`fsum_upd`). -/
theorem fsum_mv (G : ThreadId → γ) {m : Mem} {t : ThreadId} (ht : t < m.threads.size)
    (b : RwPh) :
    W.fsum (upd G t (W.set (G t) b)) m + (W.ph (G t)).frac.val = W.fsum G m + b.frac.val := by
  have h := fsum_upd (W := W) G ht (G t) (W.set (G t) b)
  rwa [upd_same, W.ph_set] at h

/-- A move of `t` that keeps its fraction keeps the readers' fractions. -/
theorem fsum_keep (G : ThreadId → γ) (m : Mem) {t : ThreadId} {b : RwPh}
    (h : b.frac = (W.ph (G t)).frac) : W.fsum (upd G t (W.set (G t) b)) m = W.fsum G m := by
  rw [show W.fsum (upd G t (W.set (G t) b)) m = W.fsum (upd G t (G t)) m from
    congrArg (ftot · m.threads.size) (upd_map (fun g => (W.ph g).frac) G t
      (by simp only [W.ph_set]; exact h)), upd_same]

/-- A move of `t` that keeps whether it holds the writing bit keeps `writing`. -/
theorem writing_mv (G : ThreadId → γ) (m : Mem) {t : ThreadId} {b : RwPh}
    (h : b.isW = (W.ph (G t)).isW) : W.writing (upd G t (W.set (G t) b)) m = W.writing G m := by
  rw [writing_upd (W := W) G m t (g := G t) (g' := W.set (G t) b) (by rw [W.ph_set]; exact h),
    upd_same]

/-- A place property after `t` moves to `b`, which `b` lacks, is another thread's before. -/
theorem ph_mv {G : ThreadId → γ} {t u : ThreadId} {b : RwPh} (p : RwPh → Prop)
    (h : p (W.ph (upd G t (W.set (G t) b) u))) (hb : ¬ p b := by rintro ⟨⟩) :
    u ≠ t ∧ p (W.ph (G u)) := by
  by_cases e : u = t
  · subst e; rw [upd_self, W.ph_set] at h; exact absurd h hb
  · rw [upd_ne _ _ e] at h; exact ⟨e, h⟩

/-- A thread in the rwlock's code exists, after `t` (which exists) moves. -/
theorem ex_mv {G : ThreadId → γ} {m : Mem} {t : ThreadId} {b : RwPh} (ht : t < m.threads.size)
    (hex : ∀ u, W.ph (G u) ≠ .out → u < m.threads.size) :
    ∀ u, W.ph (upd G t (W.set (G t) b) u) ≠ .out → u < m.threads.size := fun u hu => by
  by_cases e : u = t
  · subst e; exact ht
  · rw [upd_ne _ _ e] at hu; exact hex u hu

/-- A reader of `m` is counted. -/
theorem nrd_pos {G : ThreadId → γ} {m : Mem} {u : ThreadId} (hu : u < m.threads.size)
    (h : (W.ph (G u)).isRd = true) : W.nrd G m ≠ 0 := by
  have h1 : (fun v => if (W.ph (G v)).isRd then 1 else 0) u ≤ W.nrd G m :=
    le_tsum (fun v => if (W.ph (G v)).isRd then 1 else 0) hu
  simp [h] at h1
  omega

/-- With no reader counted, no thread is at `rd` (each thread in the code exists). -/
theorem noRd_of {G : ThreadId → γ} {m : Mem} (hex : ∀ u, W.ph (G u) ≠ .out → u < m.threads.size)
    (h0 : W.nrd G m = 0) : ∀ u, (W.ph (G u)).isRd = false := fun u => by
  cases e : (W.ph (G u)).isRd
  · rfl
  · exact absurd h0 (nrd_pos (hex u fun h => by rw [h] at e; cases e) e)

/-- With no thread at `rd`, the readers' fractions are zero. -/
theorem fsum_noRd {G : ThreadId → γ} {m : Mem} (h : ∀ u, (W.ph (G u)).isRd = false) :
    W.fsum G m = 0 :=
  ftot_zero (fun u => by
    have hu := h u
    cases e : W.ph (G u) <;> first | rfl | (rw [e] at hu; cases hu)) _

/-- A reader's fraction is below the readers' fractions. -/
theorem frac_le_fsum {G : ThreadId → γ} {m : Mem} {u : ThreadId} (hu : u < m.threads.size) :
    (W.ph (G u)).frac.val ≤ W.fsum G m :=
  le_ftot (fun v => (W.ph (G v)).frac) hu

/-- The counts read the threads only. -/
theorem nrd_threads {G : ThreadId → γ} {m m' : Mem} (h : m'.threads = m.threads) :
    W.nrd G m' = W.nrd G m := by unfold nrd; rw [h]

theorem nwi_threads {G : ThreadId → γ} {m m' : Mem} (h : m'.threads = m.threads) :
    W.nwi G m' = W.nwi G m := by unfold nwi; rw [h]

theorem writing_threads {G : ThreadId → γ} {m m' : Mem} (h : m'.threads = m.threads) :
    W.writing G m' = W.writing G m := by unfold writing; rw [h]

theorem fsum_threads {G : ThreadId → γ} {m m' : Mem} (h : m'.threads = m.threads) :
    W.fsum G m' = W.fsum G m := by unfold fsum; rw [h]

/-- A move of `t` between places in the writers' entry (`out`, `wi`) keeps whether some thread is
at a place outside them. -/
theorem ex_calm {G : ThreadId → γ} {t : ThreadId} {a : RwPh} (p : RwPh → Prop)
    (hp : ∀ b, b = .out ∨ b = .wi → ¬ p b) (ha : a = .out ∨ a = .wi)
    (h₀ : W.ph (G t) = .out ∨ W.ph (G t) = .wi) :
    (∃ u, p (W.ph (upd G t (W.set (G t) a) u))) ↔ ∃ u, p (W.ph (G u)) := by
  constructor
  · rintro ⟨u, hu⟩
    by_cases e : u = t
    · subst e; rw [upd_self, W.ph_set] at hu; exact absurd hu (hp a ha)
    · rw [upd_ne _ _ e] at hu; exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    by_cases e : u = t
    · subst e; exact absurd hu (hp _ h₀)
    · exact ⟨u, by rw [upd_ne _ _ e]; exact hu⟩

/-- The same for a property of every thread that holds at `out` and `wi`. -/
theorem all_calm {G : ThreadId → γ} {t : ThreadId} {a : RwPh} (p : RwPh → Prop)
    (hp : ∀ b, b = .out ∨ b = .wi → p b) (ha : a = .out ∨ a = .wi)
    (h₀ : W.ph (G t) = .out ∨ W.ph (G t) = .wi) :
    (∀ u, p (W.ph (upd G t (W.set (G t) a) u))) ↔ ∀ u, p (W.ph (G u)) := by
  constructor
  · intro h u
    by_cases e : u = t
    · subst e; exact hp _ h₀
    · have := h u; rwa [upd_ne _ _ e] at this
  · intro h u
    by_cases e : u = t
    · subst e; rw [upd_self, W.ph_set]; exact hp a ha
    · rw [upd_ne _ _ e]; exact h u

/-- A move of `t` between `out` and `wi` keeps whether the resource is away and posted. -/
theorem busy_calm {G : ThreadId → γ} {t : ThreadId} {a : RwPh} (ha : a = .out ∨ a = .wi)
    (h₀ : W.ph (G t) = .out ∨ W.ph (G t) = .wi) :
    (W.Busy (upd G t (W.set (G t) a)) ↔ W.Busy G) ∧
      (RwPosted W.ph (upd G t (W.set (G t) a)) ↔ RwPosted W.ph G) := by
  have hpost : RwPosted W.ph (upd G t (W.set (G t) a)) ↔ RwPosted W.ph G :=
    and_congr (ex_calm (W := W) (· = .ww) (by rintro b (rfl | rfl) <;> nofun) ha h₀)
      (and_congr (all_calm (W := W) (fun b => b.isRd = false)
          (by rintro b (rfl | rfl) <;> rfl) ha h₀)
        (all_calm (W := W) (· ≠ .rp) (by rintro b (rfl | rfl) <;> nofun) ha h₀))
  exact ⟨or_congr (ex_calm (W := W) (· = .wr) (by rintro b (rfl | rfl) <;> nofun) ha h₀)
    (or_congr (ex_calm (W := W) (· = .rp) (by rintro b (rfl | rfl) <;> nofun) ha h₀) hpost),
    hpost⟩

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

/-- A byte a resource owns is exclusive or shared. -/
theorem _root_.Zig.Full.Res.owned_split {r : Res} {l : Loc} (h : r.owned l ≠ none) :
    r.excl l ≠ none ∨ r.shared l ≠ none := by
  by_cases hc : r.heap l ≠ none ∨ (r.gh.share l).Whole
  · exact .inl (Res.excl_ne.mpr hc)
  · refine .inr (Res.shared_ne.mpr ⟨Classical.byContradiction fun e => hc (.inl e),
      fun hw => hc (.inr hw), ?_⟩)
    rcases Res.owned_ne.mp h with h' | h'
    · exact absurd (.inl h') hc
    · exact h'

/-- **Ownership of a resource with fewer bytes** (`Owns`): each byte `r'` owns, `r` owns; while a
reader is in its code, each shared byte of `r` is shared in `r'`. -/
theorem Owns.mono {G : ThreadId → γ} {m : Mem} {r r' : Res} (ho : W.Owns G m r)
    (hT : ∀ l, r'.owned l ≠ none → r.owned l ≠ none)
    (hS : (∃ u, (W.ph (G u)).isRd = true) → ∀ l, r.shared l ≠ none → r'.shared l ≠ none) :
    W.Owns G m r' := by
  intro e he hT'
  have hsplit : ∀ x, r'.owned (e.block, x) ≠ none → e.off ≤ x → x < e.off + e.len →
      e.Touches r.excl ∨ e.Touches r.shared ∨ m.blocks.size ≤ e.block := fun x h h1 h2 =>
    (Res.owned_split (hT _ h)).elim (fun h => .inl ⟨x, h1, h2, h⟩)
      (fun h => .inr (.inl ⟨x, h1, h2, h⟩))
  have hT₀ : e.Touches r.excl ∨ e.Touches r.shared ∨ m.blocks.size ≤ e.block := by
    rcases hT' with ⟨x, h1, h2, h3⟩ | ⟨x, h1, h2, h3⟩ | h
    · exact hsplit x (Res.owned_of_excl h3) h1 h2
    · exact hsplit x (Res.owned_of_shared h3) h1 h2
    · exact .inr (.inr h)
  rcases ho e he hT₀ with h | h | ⟨hw, ⟨x, h1, h2, h3⟩, u, hu, hc⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨hw, ⟨x, h1, h2, hS ⟨u, hu⟩ _ h3⟩, u, hu, hc⟩)

/-- **A resource `t` owns, given to the rest by a release RMW of `t`** (`unlock`'s `and ~1`): its
accesses happened before `t`'s clock (`Mem.Owns`), which the RMW's release clock covers. A part
with `R` has no shared byte (`R_plain`). -/
theorem Owns.ofThread {G : ThreadId → γ} {m m' : Mem} {r : Res} {t : ThreadId}
    (ho : m.Owns t r.excl) (hsh : ∀ l, r.shared l = none)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ VClock.le e.clock (m'.clocks[t]!) = true)
    (hcl : VClock.le (m.clocks[t]!) (m'.clocks[t]!) = true)
    (hbs : m.blocks.size ≤ m'.blocks.size)
    (hnew : VClock.le (m'.clocks[t]!) ((W.st.hist m').back!).relClock = true) :
    W.Owns G m' r := by
  intro e he hT
  refine .inr (.inl ?_)
  rcases hfp e he with he₀ | hc
  · have hT' : e.Touches r.excl ∨ m.blocks.size ≤ e.block := by
      rcases hT with h | ⟨x, -, -, h3⟩ | h
      · exact .inl h
      · exact absurd (hsh _) h3
      · exact .inr (Nat.le_trans hbs h)
    exact VClock.le_trans (VClock.le_trans (ho e he₀ hT') hcl) hnew
  · exact VClock.le_trans hc hnew

/-- **The free resource, taken by `t` with an acquire RMW while no other reader is left** (the
writer's `-1` with no reader, the last reader's `-2^32` before a writer): an access is before every
live thread, before the word's release clock (which the acquire brings to `t`), or `t`'s own, so
`t` owns it (`FLock.Inv.takeRest`'s premise). -/
theorem Owns.toThread {G : ThreadId → γ} {m m' : Mem} {r : Res} {t : ThreadId}
    (ho : W.Owns G m r) (hnr : ∀ u, (W.ph (G u)).isRd = true → u = t)
    (ht : t < m.threads.size) (hg : M.ph (G t) ≠ .gone)
    (hacq : VClock.le ((W.st.hist m).back!).relClock (m'.clocks[t]!) = true)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ VClock.le e.clock (m'.clocks[t]!) = true)
    (hcl : VClock.le (m.clocks[t]!) (m'.clocks[t]!) = true)
    (hbs : m.blocks.size ≤ m'.blocks.size) :
    m'.Owns t r.owned := by
  intro e he hT
  rcases hfp e he with he₀ | hc
  · have hT' : e.Touches r.excl ∨ e.Touches r.shared ∨ m.blocks.size ≤ e.block := by
      rcases hT with ⟨x, h1, h2, h3⟩ | h
      · exact (Res.owned_split h3).elim (fun h => .inl ⟨x, h1, h2, h⟩)
          (fun h => .inr (.inl ⟨x, h1, h2, h⟩))
      · exact .inr (.inr (Nat.le_trans hbs h))
    rcases ho e he₀ hT' with h | h | ⟨-, -, u, hu, hc⟩
    · exact VClock.le_trans (h t ht hg) hcl
    · exact VClock.le_trans h hacq
    · rw [hnr u hu] at hc; exact VClock.le_trans hc hcl
  · exact hc

/-! ## The invariant after the rwlock's own ops

Each op at the state word is one of the atomic word rules at the outer mutex (`wp_wordRmw`,
`wp_wordWeakCas`): its continuation has the rest as the word's cells and a rest `rY` without the
word's bytes, which the invariant splits (`Inv.restY`); the lemmas below give the rwlock's
invariant after the op, the `hI` of `Fits.atWord`. -/

/-- **The rest beside the word's cells** is the free resource and the rest of the rest. -/
theorem Inv.restY {G : ThreadId → γ} {rY : Res} {m : Mem}
    (hI : W.Inv G (rsum (W.st.cellsR m) rY) m) (hY : ∀ l, W.st.In l → rY.heap l = none) :
    ∃ rF rO, rY = rsum rF rO ∧ (∀ l, W.st.In l → rF.owned l = none ∧ rO.heap l = none) ∧
      FHeap.Disjoint rF.heap rO.heap ∧ W.FreeRes G m rF ∧ W.Owns G m rF := by
  obtain ⟨rF, rO, he, hoff, hd, hfr, how⟩ := hI.rest
  refine ⟨rF, rO, cellsAt_cancel he hY fun l hl => ?_, hoff, hd, hfr, how⟩
  show (rF.heap ∪ rO.heap) l = none
  rw [FHeap.union_apply, Res.heap_of_owned (hoff l hl).1, (hoff l hl).2]
  rfl

/-- The value of the word's newest write, from the invariant. -/
theorem Inv.old {G : ThreadId → γ} {rX : Res} {m : Mem} {old : BitVec 64} (hI : W.Inv G rX m)
    (hv : (W.st.hist m)[(W.st.hist m).size - 1]!.Val old) :
    old = RwState.encode (W.nrd G m) (W.nwi G m) (W.writing G m) := by
  obtain ⟨e, hb, hev⟩ := hI.word
  rw [last_of_back hb] at hv
  unfold Word.Entry.Val at hv hev
  rw [hv] at hev
  cases hev; rfl

/-- The free resource reads the threads only. -/
theorem FreeRes.threads {G : ThreadId → γ} {m m' : Mem} {rF : Res} (h : m'.threads = m.threads)
    (hf : W.FreeRes G m rF) : W.FreeRes G m' rF := by
  unfold FreeRes at hf ⊢
  rw [nrd_threads h, fsum_threads h]
  exact hf

/-- **The invariant after a release RMW of `t` at the state word that moves `t` to `b`** (the
shared part of the op lemmas): the op's word facts (`wp_wordRmw`, `Word.atomicRmw_fpNew`), the
new value as the encoding of the new places, the room, the writer and last-reader facts, and the
free resource for the new places (all at the threads of `m`). The rest of the rest `rO` stays; the
free resource `rF` (the invariant's, `Inv.restY`) may become `rF'` (moved to or from `t`'s part, a
share split or joined), given its ownership after the op from the old one's (`Owns.step`: a
thread leaving `rd` is the RMW's, which its release clock covers; then `Owns.mono`,
`Owns.ofThread`). A successful weak CAS pushes the same entry (`wp_wordWeakCas`). -/
theorem Inv.ofRmwMv {G : ThreadId → γ} {rF rO rF' : Res} {m m' : Mem} {t : ThreadId}
    {b : RwPh} {ord : AtomicOrder} {new : BitVec 64}
    (hI : W.Inv G (rsum (W.st.cellsR m) (rsum rF rO)) m) (ht : t < m.threads.size)
    (hmph : ∀ a, M.ph (W.set (G t) a) = M.ph (G t))
    (hrest : RestStep W.st.In m m') (hok : W.st.Ok m' fun u => M.ph (G u) ≠ .gone)
    (hh : W.st.hist m' = (W.st.hist m).push
      (Word.rmwEnt m' t ord (W.st.hist m)[(W.st.hist m).size - 1]! new))
    (hrel : ord.isRel = true)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ VClock.le e.clock (m'.clocks[t]!) = true)
    (hroom : W.nrd (upd G t (W.set (G t) b)) m < RwState.countBound ∧
      W.nwi (upd G t (W.set (G t) b)) m < RwState.countBound)
    (hval : new = RwState.encode (W.nrd (upd G t (W.set (G t) b)) m)
      (W.nwi (upd G t (W.set (G t) b)) m) (W.writing (upd G t (W.set (G t) b)) m))
    (hone : ∀ u v, (W.ph (upd G t (W.set (G t) b) u)).isW → (W.ph (upd G t (W.set (G t) b) v)).isW →
      u = v)
    (hwm : ∀ u, (W.ph (upd G t (W.set (G t) b) u)).isW →
      (M.ph (upd G t (W.set (G t) b) u)).held = true)
    (hwr : ∀ u, W.ph (upd G t (W.set (G t) b) u) = .wr → W.nrd (upd G t (W.set (G t) b)) m = 0)
    (hrp : ∀ u, W.ph (upd G t (W.set (G t) b) u) = .rp →
      W.nrd (upd G t (W.set (G t) b)) m = 0 ∧ (∃ w, W.ph (upd G t (W.set (G t) b) w) = .ww) ∧
      ∀ v, W.ph (upd G t (W.set (G t) b) v) = .rp → v = u)
    (hoff : ∀ l, W.st.In l → rO.heap l = none) (how : W.Owns G m rF)
    (hoff' : ∀ l, W.st.In l → rF'.owned l = none) (hd' : FHeap.Disjoint rF'.heap rO.heap)
    (hfr' : W.FreeRes (upd G t (W.set (G t) b)) m rF')
    (hown : W.Owns (upd G t (W.set (G t) b)) m' rF → W.Owns (upd G t (W.set (G t) b)) m' rF') :
    W.Inv (upd G t (W.set (G t) b)) (rsum (W.st.cellsR m') (rsum rF' rO)) m' := by
  have hth := hrest.threads
  have hne : ∀ u, u ≠ t → upd G t (W.set (G t) b) u = G u := fun u hu => upd_ne _ _ hu
  have hMph : ∀ u, M.ph (upd G t (W.set (G t) b) u) = M.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hmph]
    · rw [hne u e]
  refine ⟨?_, fun u hu => by rw [hth]; exact ex_mv ht hI.ex u hu,
    by rw [nrd_threads hth, nwi_threads hth]; exact hroom, ?_, ?_, hone,
    hwm, fun u hu => by rw [nrd_threads hth]; exact hwr u hu,
    fun u hu => by rw [nrd_threads hth]; exact hrp u hu,
    ⟨rF', rO, rfl, fun l hl => ⟨hoff' l hl, hoff l hl⟩, hd', hfr'.threads hth, hown ?_⟩⟩
  · have : (fun u => M.ph (upd G t (W.set (G t) b) u) ≠ .gone) = fun u => M.ph (G u) ≠ .gone :=
      funext fun u => by rw [hMph]
    rw [this]; exact hok
  · refine ⟨Word.rmwEnt m' t ord (W.st.hist m)[(W.st.hist m).size - 1]! new, by rw [hh]; simp, ?_⟩
    rw [nrd_threads hth, nwi_threads hth, writing_threads hth, ← hval]
    exact W.st.enc_val new
  · intro j hj
    rw [hh, Array.size_push] at hj
    rw [hh]
    rcases Nat.lt_or_ge j (W.st.hist m).size with hj' | hj'
    · rw [Word.get_push_lt hj']; exact hI.msgs j hj'
    · obtain rfl : j = (W.st.hist m).size := by omega
      rw [Word.get_push_eq]
      exact ⟨_, _, W.writing (upd G t (W.set (G t) b)) m, hroom.1, hroom.2,
        by rw [← hval]; exact W.st.enc_val new⟩
  · have hnew : VClock.le (m'.clocks[t]!) ((W.st.hist m').back!).relClock = true := by
      rw [hh, back_push]; exact Word.rmwEnt_rel hrel
    refine Owns.step how hfp hth hrest.clocks (Nat.le_of_eq hrest.bsize.symm)
      (by rw [hh, back_push]; exact Word.rmwEnt_relLe) hnew
      (fun u hu => by rwa [hMph] at hu) (fun u hu => ?_)
    by_cases e : u = t
    · subst e; exact .inr (VClock.le_trans (hrest.clocks u) hnew)
    · rw [hne u e]; exact .inl hu

/-- `Inv.ofRmwMv` with the free resource kept. -/
theorem Inv.ofRmw {G : ThreadId → γ} {rY : Res} {m m' : Mem} {t : ThreadId} {b : RwPh}
    {ord : AtomicOrder} {new : BitVec 64}
    (hI : W.Inv G (rsum (W.st.cellsR m) rY) m) (hY : ∀ l, W.st.In l → rY.heap l = none)
    (ht : t < m.threads.size) (hmph : ∀ a, M.ph (W.set (G t) a) = M.ph (G t))
    (hrest : RestStep W.st.In m m') (hok : W.st.Ok m' fun u => M.ph (G u) ≠ .gone)
    (hh : W.st.hist m' = (W.st.hist m).push
      (Word.rmwEnt m' t ord (W.st.hist m)[(W.st.hist m).size - 1]! new))
    (hrel : ord.isRel = true)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ VClock.le e.clock (m'.clocks[t]!) = true)
    (hroom : W.nrd (upd G t (W.set (G t) b)) m < RwState.countBound ∧
      W.nwi (upd G t (W.set (G t) b)) m < RwState.countBound)
    (hval : new = RwState.encode (W.nrd (upd G t (W.set (G t) b)) m)
      (W.nwi (upd G t (W.set (G t) b)) m) (W.writing (upd G t (W.set (G t) b)) m))
    (hone : ∀ u v, (W.ph (upd G t (W.set (G t) b) u)).isW → (W.ph (upd G t (W.set (G t) b) v)).isW →
      u = v)
    (hwm : ∀ u, (W.ph (upd G t (W.set (G t) b) u)).isW →
      (M.ph (upd G t (W.set (G t) b) u)).held = true)
    (hwr : ∀ u, W.ph (upd G t (W.set (G t) b) u) = .wr → W.nrd (upd G t (W.set (G t) b)) m = 0)
    (hrp : ∀ u, W.ph (upd G t (W.set (G t) b) u) = .rp →
      W.nrd (upd G t (W.set (G t) b)) m = 0 ∧ (∃ w, W.ph (upd G t (W.set (G t) b) w) = .ww) ∧
      ∀ v, W.ph (upd G t (W.set (G t) b) v) = .rp → v = u)
    (hfr : ∀ rF, W.FreeRes G m rF → W.FreeRes (upd G t (W.set (G t) b)) m rF) :
    W.Inv (upd G t (W.set (G t) b)) (rsum (W.st.cellsR m') rY) m' := by
  obtain ⟨rF, rO, rfl, hoff, hd, hfr₀, how⟩ := hI.restY hY
  exact hI.ofRmwMv ht hmph hrest hok hh hrel hfp hroom hval hone hwm hwr hrp
    (fun l hl => (hoff l hl).2) how (fun l hl => (hoff l hl).1) hd (hfr rF hfr₀) id

/-- **A writer's intent** (`lockUncancelable`'s `+2`, `out → wi`): the word counts one more pending
writer; the readers, the writing bit, the free resource and its ownership stay. The room is
`lock_wp`'s. -/
theorem Inv.addW {G : ThreadId → γ} {rY : Res} {m m' : Mem} {t : ThreadId}
    {ord : AtomicOrder} {old : BitVec 64}
    (hI : W.Inv G (rsum (W.st.cellsR m) rY) m) (hY : ∀ l, W.st.In l → rY.heap l = none)
    (hout : W.ph (G t) = .out) (ht : t < m.threads.size)
    (hmph : ∀ a, M.ph (W.set (G t) a) = M.ph (G t))
    (hroom : W.nwi G m + 1 < RwState.countBound)
    (hrest : RestStep W.st.In m m') (hok : W.st.Ok m' fun u => M.ph (G u) ≠ .gone)
    (hv : (W.st.hist m)[(W.st.hist m).size - 1]!.Val old)
    (hh : W.st.hist m' = (W.st.hist m).push
      (Word.rmwEnt m' t ord (W.st.hist m)[(W.st.hist m).size - 1]! (old + 2)))
    (hrel : ord.isRel = true)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ VClock.le e.clock (m'.clocks[t]!) = true) :
    W.Inv (upd G t (W.set (G t) .wi)) (rsum (W.st.cellsR m') rY) m' := by
  have hnrd : W.nrd (upd G t (W.set (G t) .wi)) m = W.nrd G m := by
    simpa [hout, RwPh.isRd] using nrd_mv (W := W) G ht .wi
  have hnwi : W.nwi (upd G t (W.set (G t) .wi)) m = W.nwi G m + 1 := by
    simpa [hout, RwPh.isWi] using nwi_mv (W := W) G ht .wi
  have hwr := writing_mv (W := W) G m (t := t) (b := .wi) (by rw [hout]; rfl)
  have hfs := fsum_keep (W := W) G m (t := t) (b := .wi) (by rw [hout]; rfl)
  have hxs : W.xs (upd G t (W.set (G t) .wi)) = W.xs G := by rw [xs_set, upd_same]
  obtain ⟨hbusy, -⟩ := busy_calm (W := W) (G := G) (t := t) (.inr rfl) (.inl hout)
  refine hI.ofRmw hY ht hmph hrest hok hh hrel hfp
    ⟨by rw [hnrd]; exact hI.room.1, by rw [hnwi]; exact hroom⟩
    (by rw [hnrd, hnwi, hwr, hI.old hv]; exact RwState.Family.add_writer 31 1 _ _ _)
    (fun u v hu hv => hI.one u v (ph_mv (·.isW = true) hu).2
      (ph_mv (·.isW = true) hv).2)
    (fun u hu => ?_) (fun u hu => ?_) (fun u hu => ?_) (fun rF hfr => ?_)
  · obtain ⟨hu', hu⟩ := ph_mv (·.isW = true) hu
    rw [upd_ne _ _ hu']; exact hI.wm u hu
  · rw [hnrd]; exact hI.wr u (ph_mv (· = .wr) hu).2
  · obtain ⟨h0, ⟨w, hw⟩, hone⟩ := hI.rp u (ph_mv (· = .rp) hu).2
    have hw' : w ≠ t := fun e => by subst e; rw [hout] at hw; cases hw
    exact ⟨by rw [hnrd]; exact h0, ⟨w, by rw [upd_ne _ _ hw']; exact hw⟩,
      fun v hv => hone v (ph_mv (· = .rp) hv).2⟩
  · refine ⟨fun hb => hfr.1 (hbusy.mp hb), fun hb hn => ?_, fun hb hn => ?_⟩
    · rw [hxs]; exact hfr.2.1 (fun h => hb (hbusy.mpr h)) (by rwa [hnrd] at hn)
    · obtain ⟨H, f, hR, hf, hsum, hrF, hall⟩ :=
        hfr.2.2 (fun h => hb (hbusy.mpr h)) (by rwa [hnrd] at hn)
      exact ⟨H, f, by rw [hxs]; exact hR, hf, by rw [hfs]; exact hsum, hrF,
        fun u q H' hu => hall u q H' (ph_mv (· = .rd q H') hu).2⟩

/-- With no thread at `wr` or `rp` and readers present, the resource is not away. -/
theorem not_busy_rd {G : ThreadId → γ} {m : Mem} (hwr : ∀ u, W.ph (G u) ≠ .wr)
    (hrp : ∀ u, W.ph (G u) ≠ .rp) (hnr : W.nrd G m ≠ 0) : ¬ W.Busy G := by
  rintro (⟨u, hu⟩ | ⟨u, hu⟩ | ⟨-, hall, -⟩)
  · exact hwr u hu
  · exact hrp u hu
  · exact hnr (tsum_eq_zero fun u _ => by simp [hall u])

/-- With no thread holding the writing bit there is no writer at `wr`, no last reader at `rp`
(`Inv.rp`: it has a writer at `ww`), the writing bit is clear and the resource is not away. -/
theorem Inv.noW {G : ThreadId → γ} {rX : Res} {m : Mem} (hI : W.Inv G rX m)
    (hnoW : ∀ u, (W.ph (G u)).isW = false) :
    (∀ u, W.ph (G u) ≠ .wr) ∧ (∀ u, W.ph (G u) ≠ .rp) ∧ W.writing G m = false ∧ ¬ W.Busy G := by
  have hnowr : ∀ u, W.ph (G u) ≠ .wr := fun u hu => by
    have := hnoW u; rw [hu] at this; cases this
  have hnorp : ∀ u, W.ph (G u) ≠ .rp := fun u hu => by
    obtain ⟨-, ⟨w, hw⟩, -⟩ := hI.rp u hu
    have := hnoW w; rw [hw] at this; cases this
  refine ⟨hnowr, hnorp, by simp [writing, hnoW], ?_⟩
  rintro (⟨u, hu⟩ | ⟨u, hu⟩ | ⟨⟨u, hu⟩, -, -⟩)
  · exact hnowr u hu
  · exact hnorp u hu
  · have := hnoW u; rw [hu] at this; cases this

/-- With no thread holding the writing bit, only `t` holds it after it moves. -/
theorem isW_mv {G : ThreadId → γ} {t : ThreadId} {b : RwPh}
    (hnoW : ∀ u, (W.ph (G u)).isW = false) :
    ∀ u, (W.ph (upd G t (W.set (G t) b) u)).isW = true → u = t := fun u hu =>
  Classical.byContradiction fun e => by rw [upd_ne _ _ e, hnoW u] at hu; cases hu

/-- **A writer enters with readers present** (`lockUncancelable`'s `-1` holding the outer mutex,
`wi → ww`, when the old value has readers): the pending writers drop by one, the writing bit is
set, and the free resource stays with the readers. No thread held the writing bit (`hnoW`: the
outer mutex's holder is `t`, `Inv.wm`). -/
theorem Inv.enterW {G : ThreadId → γ} {rY : Res} {m m' : Mem} {t : ThreadId}
    {ord : AtomicOrder} {old : BitVec 64}
    (hI : W.Inv G (rsum (W.st.cellsR m) rY) m) (hY : ∀ l, W.st.In l → rY.heap l = none)
    (hwi : W.ph (G t) = .wi) (ht : t < m.threads.size)
    (hmph : ∀ a, M.ph (W.set (G t) a) = M.ph (G t)) (hMt : (M.ph (G t)).held = true)
    (hnoW : ∀ u, (W.ph (G u)).isW = false) (hnr : W.nrd G m ≠ 0)
    (hrest : RestStep W.st.In m m') (hok : W.st.Ok m' fun u => M.ph (G u) ≠ .gone)
    (hv : (W.st.hist m)[(W.st.hist m).size - 1]!.Val old)
    (hh : W.st.hist m' = (W.st.hist m).push
      (Word.rmwEnt m' t ord (W.st.hist m)[(W.st.hist m).size - 1]! (old + -1)))
    (hrel : ord.isRel = true)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ VClock.le e.clock (m'.clocks[t]!) = true) :
    W.Inv (upd G t (W.set (G t) .ww)) (rsum (W.st.cellsR m') rY) m' := by
  have hGt : W.ph (upd G t (W.set (G t) .ww) t) = .ww := by rw [upd_self, W.ph_set]
  have hW := isW_mv (W := W) (t := t) (b := .ww) hnoW
  obtain ⟨hnowr, hnorp, hwr₀, hnb⟩ := hI.noW hnoW
  have hnrd : W.nrd (upd G t (W.set (G t) .ww)) m = W.nrd G m := by
    simpa [hwi, RwPh.isRd] using nrd_mv (W := W) G ht .ww
  have hnwi : W.nwi (upd G t (W.set (G t) .ww)) m + 1 = W.nwi G m := by
    simpa [hwi, RwPh.isWi] using nwi_mv (W := W) G ht .ww
  have hwr : W.writing (upd G t (W.set (G t) .ww)) m = true :=
    List.any_eq_true.mpr ⟨t, List.mem_range.mpr ht, by rw [hGt]; rfl⟩
  have hfs := fsum_keep (W := W) G m (t := t) (b := .ww) (by rw [hwi]; rfl)
  have hxs : W.xs (upd G t (W.set (G t) .ww)) = W.xs G := by rw [xs_set, upd_same]
  have hnowr' : ∀ u, W.ph (upd G t (W.set (G t) .ww) u) ≠ .wr := fun u hu =>
    hnowr u (ph_mv (· = .wr) hu).2
  have hnorp' : ∀ u, W.ph (upd G t (W.set (G t) .ww) u) ≠ .rp := fun u hu =>
    hnorp u (ph_mv (· = .rp) hu).2
  refine hI.ofRmw hY ht hmph hrest hok hh hrel hfp
    ⟨by rw [hnrd]; exact hI.room.1, by have := hI.room.2; omega⟩
    (by rw [hnrd, hwr, hI.old hv, hwr₀, ← hnwi]; exact RwState.Family.enter_writer 31 1 _ _)
    (fun u v hu hv => by rw [hW u hu, hW v hv]) (fun u hu => ?_) (fun u hu => ?_)
    (fun u hu => ?_) (fun rF hfr => ?_)
  · rw [hW u hu, upd_self, hmph]; exact hMt
  · exact absurd hu (hnowr' u)
  · exact absurd hu (hnorp' u)
  · obtain ⟨H, f, hR, hf, hsum, hrF, hall⟩ := hfr.2.2 hnb hnr
    exact ⟨fun hb => absurd hb (not_busy_rd hnowr' hnorp' (by rw [hnrd]; exact hnr)),
      fun _ hn => absurd (by rwa [hnrd] at hn) hnr,
      fun _ _ => ⟨H, f, by rw [hxs]; exact hR, hf, by rw [hfs]; exact hsum, hrF,
        fun u q H' hu => hall u q H' (ph_mv (· = .rd q H') hu).2⟩⟩

/-- The empty resource owns no byte. -/
theorem rnil_owned (l : Loc) : rnil.owned l = none := Res.owned_plain rfl rfl

/-- With no reader counted, no thread is at `rd` (`Inv.ex`: a thread in the code exists). -/
theorem Inv.noRd {G : ThreadId → γ} {rX : Res} {m : Mem} (hI : W.Inv G rX m)
    (h0 : W.nrd G m = 0) : ∀ u, (W.ph (G u)).isRd = false := noRd_of hI.ex h0

/-- **A writer enters with no reader** (`lockUncancelable`'s `-1` holding the outer mutex,
`wi → wr`, when the old value has no reader): the writing bit is set and the free resource `rF`,
which has `R`, goes to `t`, which owns it after the acquire (`Owns.toThread`, the premise of
`FLock.Inv.takeRest`); the rest keeps the rest of the rest `rO`. -/
theorem Inv.takeW {G : ThreadId → γ} {rY : Res} {m m' : Mem} {t : ThreadId}
    {ord : AtomicOrder} {old : BitVec 64}
    (hI : W.Inv G (rsum (W.st.cellsR m) rY) m) (hY : ∀ l, W.st.In l → rY.heap l = none)
    (hwi : W.ph (G t) = .wi) (ht : t < m.threads.size)
    (hmph : ∀ a, M.ph (W.set (G t) a) = M.ph (G t)) (hMt : (M.ph (G t)).held = true)
    (hg : M.ph (G t) ≠ .gone) (hnoW : ∀ u, (W.ph (G u)).isW = false) (hnr : W.nrd G m = 0)
    (hrest : RestStep W.st.In m m') (hok : W.st.Ok m' fun u => M.ph (G u) ≠ .gone)
    (hv : (W.st.hist m)[(W.st.hist m).size - 1]!.Val old)
    (hh : W.st.hist m' = (W.st.hist m).push
      (Word.rmwEnt m' t ord (W.st.hist m)[(W.st.hist m).size - 1]! (old + -1)))
    (hrel : ord.isRel = true)
    (hacq : VClock.le ((W.st.hist m).back!).relClock (m'.clocks[t]!) = true)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ VClock.le e.clock (m'.clocks[t]!) = true) :
    ∃ rF rO, rY = rsum rF rO ∧ W.R (W.xs G) rF ∧ m'.Owns t rF.owned ∧
      FHeap.Disjoint rF.heap rO.heap ∧
      W.Inv (upd G t (W.set (G t) .wr)) (rsum (W.st.cellsR m') rO) m' := by
  have hGt : W.ph (upd G t (W.set (G t) .wr) t) = .wr := by rw [upd_self, W.ph_set]
  have hW := isW_mv (W := W) (t := t) (b := .wr) hnoW
  obtain ⟨-, hnorp, hwr₀, hnb⟩ := hI.noW hnoW
  have hnrd : W.nrd (upd G t (W.set (G t) .wr)) m = W.nrd G m := by
    simpa [hwi, RwPh.isRd] using nrd_mv (W := W) G ht .wr
  have hnwi : W.nwi (upd G t (W.set (G t) .wr)) m + 1 = W.nwi G m := by
    simpa [hwi, RwPh.isWi] using nwi_mv (W := W) G ht .wr
  have hwr : W.writing (upd G t (W.set (G t) .wr)) m = true :=
    List.any_eq_true.mpr ⟨t, List.mem_range.mpr ht, by rw [hGt]; rfl⟩
  have hrd := hI.noRd hnr
  obtain ⟨rF, rO, rfl, hoff, hd, hfr₀, how⟩ := hI.restY hY
  refine ⟨rF, rO, rfl, hfr₀.2.1 hnb hnr,
    how.toThread (fun u hu => by rw [hrd u] at hu; cases hu) ht hg hacq hfp (hrest.clocks t)
      (Nat.le_of_eq hrest.bsize.symm), hd, ?_⟩
  have := hI.ofRmwMv (rF' := rnil) (b := .wr) ht hmph hrest hok hh hrel hfp
    ⟨by rw [hnrd]; exact hI.room.1, by have := hI.room.2; omega⟩
    (by rw [hnrd, hwr, hI.old hv, hwr₀, ← hnwi]; exact RwState.Family.enter_writer 31 1 _ _)
    (fun u v hu hv => by rw [hW u hu, hW v hv])
    (fun u hu => by rw [hW u hu, upd_self, hmph]; exact hMt)
    (fun _ _ => by rw [hnrd]; exact hnr)
    (fun u hu => absurd (ph_mv (· = .rp) hu).2 (hnorp u))
    (fun l hl => (hoff l hl).2) how (fun l _ => rnil_owned l) (fun _ => .inl rfl)
    ⟨fun _ => rfl, fun hb _ => absurd (.inl ⟨t, hGt⟩) hb, fun hb _ => absurd (.inl ⟨t, hGt⟩) hb⟩
    (fun ho => ho.mono (fun l h => absurd (rnil_owned l) h)
      (fun ⟨u, hu⟩ _ _ => by
        have := (ph_mv (·.isRd = true) hu).2
        rw [hrd u] at this; cases this))
  rwa [rnil_rsum] at this

/-- **The writer leaves** (`unlock`'s `and ~1`, `wr → out`): the writing bit is cleared and the
resource `r` with `R` (at the current client parts) that `t` owns goes back to the rest
(`Owns.ofThread`); the free resource was empty (`Busy`). `r` is apart from the rest and the word
(the outer mutex's invariant, `FLock.Inv.giveRest`). -/
theorem Inv.giveW {G : ThreadId → γ} {rY r : Res} {m m' : Mem} {t : ThreadId}
    {ord : AtomicOrder} {old : BitVec 64}
    (hI : W.Inv G (rsum (W.st.cellsR m) rY) m) (hY : ∀ l, W.st.In l → rY.heap l = none)
    (hwr : W.ph (G t) = .wr) (ht : t < m.threads.size)
    (hmph : ∀ a, M.ph (W.set (G t) a) = M.ph (G t))
    (hR : W.R (W.xs G) r) (hown : m.Owns t r.excl) (hsh : ∀ l, r.shared l = none)
    (hoffr : ∀ l, W.st.In l → r.heap l = none) (hdr : FHeap.Disjoint r.heap rY.heap)
    (hrest : RestStep W.st.In m m') (hok : W.st.Ok m' fun u => M.ph (G u) ≠ .gone)
    (hv : (W.st.hist m)[(W.st.hist m).size - 1]!.Val old)
    (hh : W.st.hist m' = (W.st.hist m).push
      (Word.rmwEnt m' t ord (W.st.hist m)[(W.st.hist m).size - 1]! (old &&& RwState.clearWriting)))
    (hrel : ord.isRel = true)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ VClock.le e.clock (m'.clocks[t]!) = true) :
    W.Inv (upd G t (W.set (G t) .out)) (rsum (W.st.cellsR m') (rsum r rY)) m' := by
  have hGt : W.ph (upd G t (W.set (G t) .out) t) = .out := by rw [upd_self, W.ph_set]
  have hW : ∀ u, (W.ph (G u)).isW = true → u = t := fun u hu =>
    hI.one u t hu (by rw [hwr]; rfl)
  have hW' : ∀ u, (W.ph (upd G t (W.set (G t) .out) u)).isW = false := fun u => by
    cases h : (W.ph (upd G t (W.set (G t) .out) u)).isW
    · rfl
    · obtain ⟨e, hu⟩ := ph_mv (·.isW = true) h; exact absurd (hW u hu) e
  have hnrd : W.nrd (upd G t (W.set (G t) .out)) m = W.nrd G m := by
    simpa [hwr, RwPh.isRd] using nrd_mv (W := W) G ht .out
  have hnwi : W.nwi (upd G t (W.set (G t) .out)) m = W.nwi G m := by
    simpa [hwr, RwPh.isWi] using nwi_mv (W := W) G ht .out
  have hwr₀ : W.writing G m = true :=
    List.any_eq_true.mpr ⟨t, List.mem_range.mpr ht, by rw [hwr]; rfl⟩
  have hwr' : W.writing (upd G t (W.set (G t) .out)) m = false := by simp [writing, hW']
  have hxs : W.xs (upd G t (W.set (G t) .out)) = W.xs G := by rw [xs_set, upd_same]
  have hnorp : ∀ u, W.ph (G u) ≠ .rp := fun u hu => by
    obtain ⟨-, ⟨w, hw⟩, -⟩ := hI.rp u hu
    have := hW w (by rw [hw]; rfl)
    subst this; rw [hwr] at hw; cases hw
  have hnorp' : ∀ u, W.ph (upd G t (W.set (G t) .out) u) ≠ .rp := fun u hu =>
    hnorp u (ph_mv (· = .rp) hu).2
  have hnb' : ¬ W.Busy (upd G t (W.set (G t) .out)) := by
    rintro (⟨u, hu⟩ | ⟨u, hu⟩ | ⟨⟨u, hu⟩, -, -⟩)
    · have := hW' u; rw [hu] at this; cases this
    · exact hnorp' u hu
    · have := hW' u; rw [hu] at this; cases this
  have h0 : W.nrd G m = 0 := hI.wr t hwr
  obtain ⟨rF, rO, rfl, hoff, hd, hfr₀, how⟩ := hI.restY hY
  have hrF : rF = rnil := hfr₀.1 (.inl ⟨t, hwr⟩)
  subst hrF
  have hnew : VClock.le (m'.clocks[t]!) ((W.st.hist m').back!).relClock = true := by
    rw [hh, back_push]; exact Word.rmwEnt_rel hrel
  rw [rnil_rsum] at hdr ⊢
  refine hI.ofRmwMv (rF' := r) ht hmph hrest hok hh hrel hfp
    ⟨by rw [hnrd]; exact hI.room.1, by rw [hnwi]; exact hI.room.2⟩
    (by rw [hnrd, hnwi, hwr', hI.old hv, hwr₀]; exact RwState.Family.clear_writer 31 1 _ _)
    (fun u _ hu => by rw [hW' u] at hu; cases hu) (fun u hu => by rw [hW' u] at hu; cases hu)
    (fun u hu => by have := hW' u; rw [hu] at this; cases this)
    (fun u hu => absurd hu (hnorp' u))
    (fun l hl => (hoff l hl).2) how
    (fun l hl => Res.owned_plain (W.R_plain _ _ hR).2 (hoffr l hl)) hdr
    ⟨fun hb => absurd hb hnb', fun _ _ => by rw [hxs]; exact hR,
      fun _ hn => absurd (by rw [hnrd]; exact h0) hn⟩
    (fun _ => Owns.ofThread hown hsh hfp (hrest.clocks t) (Nat.le_of_eq hrest.bsize.symm) hnew)

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
  rw [FHeap.union_apply, Res.heap_of_owned (hoff l hl).1, (hoff l hl).2]
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

/-- The rwlock's place is set by the primitive's place, the semaphore's kept. -/
theorem prim_set (g : γ) (a : RwPh) : W.prim.pl.set g (a, S.place.ph g) = W.set g a := by
  show W.set (S.place.set g (S.place.ph g)) a = W.set g a
  rw [S.place.set_self]

/-- The rwlock's place is not the outer mutex's. -/
theorem Fits.mph (hW : W.Fits P UM US okM okS) (g : γ) (a : RwPh) : M.ph (W.set g a) = M.ph g := by
  rw [← prim_set, hW.m.lph]

/-- **An atomic op at the state word moves `t` to `a`** (`Fits.wstep` with the facts of the word
rules at `M`, `FLock.wp_wordRmw`, `wp_wordWeakCas`, `wp_wordLoad`): the outer mutex's invariant
before (the stop's) and after the op, the op's rest step, and the rwlock's invariant after it with
`t` at `a`. The op may move the free resource between the rest (`rF` to `rF'`, the rest of the
rest `rO` kept) and `t`'s part (`g` to `g₁`, which keeps `t`'s client part and its places and held
resources in the locks' code: `M.setPart`); the outer mutex's invariant after it is at `g₁`
(`FLock.Inv.takeRest`, `giveRest`). The other facts of `Step` hold at once. -/
theorem Fits.atWord (hW : W.Fits P UM US okM okS) {t : ThreadId} {G₁ : ThreadId → γ} {g g₁ : γ}
    {a : RwPh} {rY rY' : Res} {m₁ m' : Mem} (hg₁ : G₁ t = g) (hc₁ : m₁.current = t)
    (hU : UM G₁ (rsum (W.st.cellsR m₁) rY) m₁) (hiL : M.Inv G₁ (rsum (W.st.cellsR m₁) rY) m₁)
    (hrest : RestStep W.st.In m₁ m') (hL : M.Inv (upd G₁ t g₁) (rsum (W.st.cellsR m') rY') m')
    (hg : W.x g₁ = W.x g ∧ M.ph g₁ = M.ph g ∧ M.held g₁ = M.held g ∧ L.ph g₁ = L.ph g ∧
      L.held g₁ = L.held g ∧ S.place.ph g₁ = S.place.ph g)
    (hY : ∃ rF rF' rO, rY = rsum rF rO ∧ rY' = rsum rF' rO)
    (hI : W.Inv G₁ (rsum (W.st.cellsR m₁) rY) m₁ →
      W.Inv (upd G₁ t (W.set g₁ a)) (rsum (W.st.cellsR m') rY') m') :
    P.inv (upd G₁ t (W.set g₁ a)) m' := by
  obtain ⟨hx, hmp, hmh, hlp, hlh, hsp⟩ := hg
  obtain ⟨rF, rF', rO, rfl, rfl⟩ := hY
  have hM : M.Inv (upd G₁ t (W.set g₁ a)) (rsum (W.st.cellsR m') (rsum rF' rO)) m' := by
    have := hW.m.relabelK (G := G₁) (t := t) (g := g₁) (a, S.place.ph g₁) hL
    rwa [prim_set] at this
  refine hW.wstep hU fun hI₁ => ⟨hiL, hI₁, hM, hI hI₁, hc₁, .inr hrest,
    fun u hu => upd_ne _ _ hu, fun u => ?_, ?_, ?_, ?_, ?_, ?_,
    rF, rF', rO, rfl, rfl⟩
  · by_cases e : u = t
    · subst e; rw [upd_self, W.x_set, hg₁, hx]
    · rw [upd_ne _ _ e]
  · rw [upd_self, hg₁, ← prim_set, hW.m.lph, hmp]
  · rw [upd_self, hg₁, ← prim_set, hW.m.lheld, hmh]
  · rw [upd_self, hg₁, W.lph, hlp]
  · rw [upd_self, hg₁, W.lheld, hlh]
  · rw [upd_self, hg₁, W.sp_ph, hsp]

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
