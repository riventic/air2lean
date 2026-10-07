/-!
# Selected environment-operation interface (E03)

An opt-in boundary for handle-based reads/writes, partial success, enumerated errors,
cleanup and two distinct clocks. It is absent from the runtime umbrella and no translated
Zig call targets it. Every environment-dependent result is a field of `Ops` over an
arbitrary state `σ`; `σ` may hold an oracle stream, so the model fixes no host behavior.
`Contract` is the only knowledge a client gets about those results. No correspondence to
an operating system, CPython or browser host import is claimed; see
`docs/env-boundaries.md`.
-/
namespace Zig.Env

abbrev Handle := Nat

/-- The enumerated environment error cases. A contract selects an allowed subset. -/
inductive IoError where
  | wouldBlock
  | brokenPipe
  | noSpaceLeft
  | accessDenied
  | inputOutput
  | connectionReset
  deriving DecidableEq, Repr

/-- Environment operations. Results depend only on the supplied state, which is arbitrary.
`monotonicNow` and `wallNow` are distinct observations (nanoseconds); only the monotonic
clock carries an ordering contract. -/
structure Ops (σ : Type) where
  monotonicNow : σ → Nat
  wallNow : σ → Int
  isOpen : σ → Handle → Bool
  /-- `.ok []` for a positive request means end of input. -/
  read : σ → Handle → Nat → Except IoError (List UInt8) × σ
  /-- `.ok n` reports that the first `n` bytes were accepted. -/
  write : σ → Handle → List UInt8 → Except IoError Nat × σ
  close : σ → Handle → σ

/-- The selected contract on an open handle. Behavior on closed handles is unconstrained;
the `World` wrappers below turn such uses into faults instead. -/
structure Contract {σ : Type} (ops : Ops σ) (errors : List IoError) : Prop where
  readBound : ∀ s h max bytes s', ops.isOpen s h = true →
    ops.read s h max = (.ok bytes, s') → bytes.length ≤ max
  readError : ∀ s h max e s', ops.isOpen s h = true →
    ops.read s h max = (.error e, s') → e ∈ errors
  readFrame : ∀ s h max h', ops.isOpen s h = true →
    ops.isOpen (ops.read s h max).2 h' = ops.isOpen s h'
  writeProgress : ∀ s h buf n s', ops.isOpen s h = true → buf ≠ [] →
    ops.write s h buf = (.ok n, s') → 0 < n ∧ n ≤ buf.length
  writeError : ∀ s h buf e s', ops.isOpen s h = true →
    ops.write s h buf = (.error e, s') → e ∈ errors
  writeFrame : ∀ s h buf h', ops.isOpen s h = true →
    ops.isOpen (ops.write s h buf).2 h' = ops.isOpen s h'
  closeReleases : ∀ s h, ops.isOpen s h = true → ops.isOpen (ops.close s h) h = false
  closeFrame : ∀ s h h', h' ≠ h → ops.isOpen (ops.close s h) h' = ops.isOpen s h'
  readMonotone : ∀ s h max, ops.monotonicNow s ≤ ops.monotonicNow (ops.read s h max).2
  writeMonotone : ∀ s h buf, ops.monotonicNow s ≤ ops.monotonicNow (ops.write s h buf).2
  closeMonotone : ∀ s h, ops.monotonicNow s ≤ ops.monotonicNow (ops.close s h)

/-- Observable boundary events, in order. -/
inductive Event where
  | wrote (h : Handle) (bytes : List UInt8)
  | failed (h : Handle) (e : IoError)
  | closed (h : Handle)
  deriving DecidableEq, Repr

/-- Client-side faults: a use or second close of a non-open handle, or a write result
outside the contract (Zig's `writeAll` would loop forever or slice out of bounds). -/
inductive Fault where
  | closedHandle (h : Handle)
  | contractBreach (h : Handle)
  deriving DecidableEq, Repr

structure World (σ : Type) where
  env : σ
  log : List Event

/-- The bytes recorded by `wrote` events. -/
def written : List Event → List UInt8
  | [] => []
  | .wrote _ b :: rest => b ++ written rest
  | _ :: rest => written rest

/-- Retry partial writes until every byte is accepted; stop at the first error. -/
def writeAll {σ : Type} (ops : Ops σ) (h : Handle) (buf : List UInt8) (w : World σ) :
    Except Fault (Except IoError Unit × World σ) :=
  if buf.isEmpty then .ok (.ok (), w)
  else if ops.isOpen w.env h then
    match ops.write w.env h buf with
    | (.error e, s) => .ok (.error e, ⟨s, w.log ++ [.failed h e]⟩)
    | (.ok n, s) =>
      if hn : 0 < n ∧ n ≤ buf.length then
        writeAll ops h (buf.drop n) ⟨s, w.log ++ [.wrote h (buf.take n)]⟩
      else .error (.contractBreach h)
  else .error (.closedHandle h)
termination_by buf.length
decreasing_by simp only [List.length_drop]; omega

/-- Release a handle; closing a non-open handle is a fault. -/
def closeOnce {σ : Type} (ops : Ops σ) (h : Handle) (w : World σ) : Except Fault (World σ) :=
  if ops.isOpen w.env h then .ok ⟨ops.close w.env h, w.log ++ [.closed h]⟩
  else .error (.closedHandle h)

/-- The client: write everything, then clean up the handle on success and on error. -/
def writeAllClose {σ : Type} (ops : Ops σ) (h : Handle) (buf : List UInt8) (w : World σ) :
    Except Fault (Except IoError Unit × World σ) :=
  match writeAll ops h buf w with
  | .error f => .error f
  | .ok (r, w') =>
    match closeOnce ops h w' with
    | .error f => .error f
    | .ok w'' => .ok (r, w'')

end Zig.Env
