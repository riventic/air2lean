import ZigLean

/-!
C11 message precision: modification order holds write events, not values, and atomic accesses
of mixed sizes are rejected. Each check reduces the model's actual memory transitions in the
kernel (`decide +kernel`); `main` repeats them at runtime with the C11 assertion marker.
-/

open Zig

deriving instance DecidableEq for Except

private def value (x : MemM α) : Option (Except Error α) :=
  (x.run {}).run.map (·.map Prod.fst)

private def assertC11 (ok : Bool) (message : String) : IO Unit :=
  unless ok do
    IO.eprintln s!"C11_ASSERTION: {message}"
    IO.Process.exit 85

private def ok (x : MemM Bool) : Bool := value x == some (.ok true)

private def switch (t : ThreadId) : MemM Unit := modify fun m => { m with current := t }

/-! ## Repeated equal values (ABA) -/

/-- `x` starts at 0 (a plain write before the fork); the child stores 1 (relaxed), 0 (relaxed)
and 1 (release). `main` has no happens-before edge to any of the child's stores. -/
private def aba : MemM (Ptr × ThreadId) := do
  let p ← alloc .heap 4 4
  store 4 p (0#32)
  let child ← Thread.fork
  switch child
  atomicStoreAt 0 .relaxed 4 p (1#32)
  atomicStoreAt 0 .relaxed 4 p (0#32)
  atomicStoreAt 0 .release 4 p (1#32)
  switch 0
  pure (p, child)

private def valueAt (m : Mem) (j : Nat) : Option (BitVec 32) :=
  match (intOfBytes 32 (m.atomics[0]!.msgs[j]!).bytes).run with
  | some (.ok v) => some v
  | _ => none

/-- Four distinct write events (two of them equal to 1, two equal to 0), in program order. -/
private def abaEvents : MemM Bool := do
  let _ ← aba
  let m ← get
  let msgs := m.atomics[0]!.msgs
  let ids := msgs.map (·.id)
  pure (msgs.size == 4 && (List.range 4).map (valueAt m) == [some 0#32, some 1#32, some 0#32, some 1#32] &&
    ids.toList.eraseDups.length == 4)

example : ok abaEvents = true := by decide +kernel

/-- An acquire read of each message: its value, and whether `main` synchronized with the child.
Only the newest 1 (the release store) synchronizes; the older 1 (relaxed) does not. -/
private def abaAcquire (c : Nat) : MemM (BitVec 32 × Bool) := do
  let (p, child) ← aba
  let v ← atomicLoadAt (n := 32) c .acquire 4 p
  pure (v, (← get).clocks[0]!.get child > 0)

example : (List.range 4).map (fun c => value (abaAcquire c)) =
    [some (.ok (1#32, true)), some (.ok (0#32, false)), some (.ok (1#32, false)),
     some (.ok (0#32, false))] := by decide +kernel

/-- Two relaxed reads by `main`: every pair of choices; the positions read (oldest = 0). -/
private def twoReads (c₁ c₂ : Nat) : MemM (Option (Nat × Nat)) := do
  let (p, _) ← aba
  let n₁ := loadCount 32 .relaxed 4 p (← get)
  if c₁ ≥ n₁ then return none
  let _ ← atomicLoadAt (n := 32) c₁ .relaxed 4 p
  let n₂ := loadCount 32 .relaxed 4 p (← get)
  if c₂ ≥ n₂ then return none
  let _ ← atomicLoadAt (n := 32) c₂ .relaxed 4 p
  let m ← get
  let pos (id : Nat) := (m.atomics[0]!.pos id).getD 99
  match m.seen.find? (fun (t, _, _) => t == 0) with
  | some (_, _, id) =>
    -- `seen` keeps the second read; recompute the first from its choice (newest first).
    pure (some (3 - c₁, pos id))
  | none => pure none

/-- The read pairs that the model allows are exactly the coherent ones (RC11 read-read
coherence): the second read is not older in modification order than the first. So 1, 0, 1 is
the value sequence of positions 1, 2, 3, while 1 (the newest), 0 is impossible. -/
private def coherentPairs : List (Nat × Nat) :=
  (List.range 4).flatMap fun i => ((List.range 4).filter (i ≤ ·)).map fun j => (i, j)

private def allowedPairs : List (Nat × Nat) :=
  (List.range 4).flatMap fun c₁ => (List.range 4).filterMap fun c₂ =>
    match value (twoReads c₁ c₂) with
    | some (.ok (some pr)) => some pr
    | _ => none

/-- The same pairs, each once (`mergeSort` does not reduce in the kernel). -/
private def samePairs : Bool :=
  allowedPairs.length == coherentPairs.length && coherentPairs.all (allowedPairs.contains ·)

example : samePairs = true := by decide +kernel

/-- A strong `cmpxchg(1 → 2)` by `main`: one option per readable message. Success on either 1
is permitted (RC11 only requires the RMW to follow the message it read in modification order);
success on the older 1 inserts the RMW between it and the next write. -/
private def casOlder : MemM Bool := do
  let (p, _) ← aba
  let options := casCount 32 .relaxed 4 p (1#32) (← get)
  let weakOptions := weakCasCount 32 .relaxed 4 p (1#32) (← get)
  -- option order: newest first; option 2 reads the older 1 (position 1).
  let r ← cmpxchgAt 2 .relaxed .relaxed 4 p (1#32) (2#32)
  let m ← get
  let msgs := m.atomics[0]!.msgs
  pure (options == 4 && weakOptions == 6 && r == none &&
    (List.range 5).map (valueAt m) == [some 0#32, some 1#32, some 2#32, some 0#32, some 1#32] &&
    msgs[2]!.rmwOf == some msgs[1]!.id)

example : ok casOlder = true := by decide +kernel

/-! ## A release sequence through equal values -/

/-- Thread A writes `data` and releases `x := 1`; thread B's relaxed RMW `xchg(x, 1)` reads it
(the same value); thread C stores `x := 1` relaxed. `main` acquires message `c` (newest first)
and then reads `data`: the release store and the RMW in its release sequence synchronize, C's
equal-valued store does not, and neither does the initial value. -/
private def relSeq (c : Nat) : MemM (BitVec 32 × BitVec 32) := do
  let d ← alloc .heap 4 4
  let x ← alloc .heap 4 4
  store 4 x (0#32)
  let a ← Thread.fork
  let b ← Thread.fork
  let cT ← Thread.fork
  switch a
  store 4 d (42#32)
  atomicStoreAt 0 .release 4 x (1#32)
  switch b
  let _ ← atomicRmwAt (n := 32) 0 .xchg false .relaxed 4 x (1#32)
  switch cT
  atomicStoreAt 0 .relaxed 4 x (1#32)
  switch 0
  let v ← atomicLoadAt (n := 32) c .acquire 4 x
  pure (v, ← load (BitVec 32) 4 d)

example : (List.range 4).map (fun c => value (relSeq c)) =
    [some (.error .illegal), some (.ok (1#32, 42#32)), some (.ok (1#32, 42#32)),
     some (.error .illegal)] := by decide +kernel

/-! ## Plain writes of an equal value are write events -/

/-- A child releases `x := 1`; `main` joins it, writes `x := 1` (plain, the same value) and then
does a relaxed RMW. The plain write becomes its own message (no release clock), so the RMW reads
it and its release sequence no longer carries the child's clock. Without a plain write, an atomic
op adds no message. -/
private def plainEqual (plainWrite : Bool) : MemM (Nat × Nat × Bool) := do
  let x ← alloc .heap 4 4
  store 4 x (0#32)
  let child ← Thread.fork
  switch child
  atomicStoreAt 0 .release 4 x (1#32)
  switch 0
  Thread.join child
  let _ ← atomicLoadAt (n := 32) 0 .relaxed 4 x
  let before := (← get).atomics[0]!.msgs.size
  if plainWrite then store 4 x (1#32)
  let _ ← atomicRmwAt (n := 32) 0 .add false .relaxed 4 x (0#32)
  let msgs := (← get).atomics[0]!.msgs
  pure (before, msgs.size, msgs.back!.relClock.isEmpty)

example : value (plainEqual true) = some (.ok (2, 4, true)) := by decide +kernel
example : value (plainEqual false) = some (.ok (2, 3, false)) := by decide +kernel

/-! ## Mixed-size atomic accesses -/

/-- An atomic `u32` at offset 0 of an 8-byte block, then `second`. -/
private def mixed (second : Ptr → MemM Unit) : MemM Nat := do
  let p ← alloc .heap 8 8
  store 8 p (0#64)
  atomicStoreAt 0 .relaxed 4 p (7#32)
  second p
  return (← get).atomics.size

private def at' (p : Ptr) (o : Int) : Ptr := { p with off := o }

example : value (mixed fun p => do let _ ← atomicLoadAt (n := 8) 0 .relaxed 1 p) =
    some (.error .unspecified) := by decide +kernel
example : value (mixed fun p => do let _ ← atomicLoadAt (n := 16) 0 .relaxed 2 (at' p 2)) =
    some (.error .unspecified) := by decide +kernel
example : value (mixed fun p => do let _ ← atomicLoadAt (n := 64) 0 .relaxed 8 p) =
    some (.error .unspecified) := by decide +kernel
example : value (mixed fun p => do let _ ← cmpxchgAt 0 .relaxed .relaxed 2 p (7#16) (1#16)) =
    some (.error .unspecified) := by decide +kernel
example : value (mixed fun p => do let _ ← atomicRmwAt (n := 8) 0 .add false .relaxed 1 (at' p 3) (1#8)) =
    some (.error .unspecified) := by decide +kernel
-- Adjacent, non-overlapping atomic words are two locations.
example : value (mixed fun p => atomicStoreAt 0 .relaxed 4 (at' p 4) (1#32)) =
    some (.ok 2) := by decide +kernel

/-- The smaller access first: a later overlapping larger one is rejected too. -/
private def smallFirst : MemM Unit := do
  let p ← alloc .heap 8 8
  store 8 p (0#64)
  atomicStoreAt 0 .relaxed 2 (at' p 2) (1#16)
  let _ ← atomicLoadAt (n := 32) 0 .relaxed 4 p

example : value smallFirst = some (.error .unspecified) := by decide +kernel

/-- A plain access of another size is not an atomic access: it is a write event of the location,
and the next atomic op reads the combined bytes. -/
private def plainByte : MemM (BitVec 32) := do
  let p ← alloc .heap 4 4
  store 4 p (0#32)
  atomicStoreAt 0 .relaxed 4 p (0x0101#32)
  store 1 (at' p 1) (0x02#8)
  atomicLoadAt (n := 32) 0 .relaxed 4 p

example : value plainByte = some (.ok 0x0201#32) := by decide +kernel

def main : IO Unit := do
  assertC11 (ok abaEvents) "equal values remain distinct write events"
  assertC11 ((List.range 4).map (fun c => value (abaAcquire c)) ==
    [some (.ok (1#32, true)), some (.ok (0#32, false)), some (.ok (1#32, false)),
     some (.ok (0#32, false))]) "only the release message of an equal value synchronizes"
  assertC11 samePairs "read pairs are exactly the coherent ones"
  assertC11 (ok casOlder) "CAS may succeed on an older equal message, adjacent in mo"
  assertC11 ((List.range 4).map (fun c => value (relSeq c)) ==
    [some (.error .illegal), some (.ok (1#32, 42#32)), some (.ok (1#32, 42#32)),
     some (.error .illegal)]) "release sequence follows RMWs, not equal values"
  assertC11 (value (plainEqual true) == some (.ok (2, 4, true)))
    "an equal-valued plain write is a write event"
  assertC11 (value (plainEqual false) == some (.ok (2, 3, false)))
    "no message without a write event"
  assertC11 (value (mixed fun p => do let _ ← atomicLoadAt (n := 8) 0 .relaxed 1 p) ==
    some (.error .unspecified)) "a narrower atomic access is rejected"
  assertC11 (value smallFirst == some (.error .unspecified)) "a wider atomic access is rejected"
  assertC11 (value (mixed fun p => atomicStoreAt 0 .relaxed 4 (at' p 4) (1#32)) == some (.ok 2))
    "adjacent atomic words stay separate"
  assertC11 (value plainByte == some (.ok 0x0201#32)) "plain mixed-size writes stay events"
  IO.println "C11 message precision regressions passed"
