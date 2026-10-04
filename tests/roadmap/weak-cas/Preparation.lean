import ZigLean
open Zig

-- Pre-refactor preparation retained as a regression oracle. It records the access once,
-- computes strong choices, then computes the full read choices again for weak failure.
private def legacyStrongPrep (n align : Nat) (p : Ptr) (expected : BitVec n) :
    MemM (Nat × Array Nat) := do
  let (b, _, o) ← (← get).accessW p (intSize n) align
  recordAccess b o (intSize n) .atomicRead
  let li ← locIdx b o (intSize n)
  let m ← get
  let l := m.atomics[li]!
  let opts := (readOpts m li false).filter fun pos =>
    !(l.hasRmwAfter pos && match (intOfBytes n l.msgs[pos]!.bytes).run with
      | some (.ok v) => v == expected
      | _ => false)
  pure (li, opts)

private def legacyWeakPrep (n align : Nat) (p : Ptr) (expected : BitVec n) :
    MemM (Nat × Array (Nat × Bool)) := do
  let (li, strong) ← legacyStrongPrep n align p expected
  pure (li, weakCasOpts (← get) li expected strong)

private def arraySame (same : α → α → Bool) (a b : Array α) : Bool :=
  a.size == b.size && (a.zip b).all fun (x, y) => same x y

-- Compare each field that preparation may alter, including the entire byte/message and
-- footprint records. The shared preparation theorem determines all other fields unchanged.
private def samePreparedMem (a b : Mem) : Bool :=
  a.clocks == b.clocks && a.nextMsg == b.nextMsg &&
  arraySame (fun (x y : Block) => x.bytes == y.bytes && x.align == y.align &&
    decide (x.kind = y.kind) && x.live == y.live && x.addr == y.addr) a.blocks b.blocks &&
  arraySame (fun (x y : FootprintEntry) => x.tid == y.tid && x.clock == y.clock && x.block == y.block &&
    x.off == y.off && x.len == y.len && decide (x.kind = y.kind)) a.footprint b.footprint &&
  arraySame (fun (x y : ALoc) => x.block == y.block && x.off == y.off && x.len == y.len &&
    arraySame (fun (r s : Msg) => r.id == s.id && r.bytes == s.bytes && r.clock == s.clock &&
      r.relClock == s.relClock && r.rmwOf == s.rmwOf) x.msgs y.msgs) a.atomics b.atomics

private def samePrep [BEq α] (new old : MemM (Nat × Array α)) (m : Mem) : Bool :=
  match (new.run m).run, (old.run m).run with
  | some (.ok ((li, xs), a)), some (.ok ((lj, ys), b)) =>
    li == lj && xs == ys && samePreparedMem a b &&
      (a.footprint.filter fun e => e.kind == .atomicRead).size ==
        (m.footprint.filter fun e => e.kind == .atomicRead).size + 1
  | some (.error e), some (.error f) => decide (e = f)
  | none, none => true
  | _, _ => false

private def setup (consumed : Bool) : MemM Ptr := do
  let p ← alloc .heap 1 1
  store 1 p (42#8)
  if consumed then
    let child ← Thread.fork
    modify fun m => { m with current := child }
    let _ ← cmpxchgAt 0 .relaxed .relaxed 1 p (42#8) (7#8)
    modify fun m => { m with current := 0 }
  pure p

private def equivalent (consumed : Bool) (expected : BitVec 8) : Bool :=
  match ((setup consumed).run {}).run with
  | some (.ok (p, m)) =>
    samePrep (casPrep 8 1 p expected) (legacyStrongPrep 8 1 p expected) m &&
    samePrep (weakCasPrep 8 1 p expected) (legacyWeakPrep 8 1 p expected) m
  | _ => false

private def errorEquivalent : Bool :=
  let p : Ptr := { block := some 0, off := 0 }
  let m : Mem := { blocks := #[{ bytes := #[.int (42#8)], align := 1, kind := .constGlobal,
    live := true, addr := 4096 }] }
  samePrep (casPrep 8 1 p (42#8)) (legacyStrongPrep 8 1 p (42#8)) m &&
  samePrep (weakCasPrep 8 1 p (42#8)) (legacyWeakPrep 8 1 p (42#8)) m &&
  casCount 8 .relaxed 1 p (42#8) m == 1 && weakCasCount 8 .relaxed 1 p (42#8) m == 1

private def genericCounts : Bool :=
  optCount (pure #[(0, false), (0, true)] : MemM (Array (Nat × Bool))) {} == 2 &&
  optCount (pure #[] : MemM (Array (Nat × Bool))) {} == 0 &&
  optCount (throw .illegal : MemM (Array (Nat × Bool))) {} == 1 &&
  optCount (fun _ => ExceptT.mk none : MemM (Array (Nat × Bool))) {} == 1

example : equivalent false (42#8) = true := by decide +kernel
example : equivalent false (99#8) = true := by decide +kernel
example : equivalent true (42#8) = true := by decide +kernel
example : equivalent true (99#8) = true := by decide +kernel
example : errorEquivalent = true := by decide +kernel
example : genericCounts = true := by decide +kernel

def main : IO Unit := do
  for consumed in [false, true] do
    for expected in [42#8, 99#8] do
      unless equivalent consumed expected do
        IO.eprintln "C11_ASSERTION: preparation changed choices or memory events"
        IO.Process.exit 85
  unless errorEquivalent && genericCounts do
    IO.eprintln "C11_ASSERTION: preparation error behavior or option-count fallback changed"
    IO.Process.exit 85
  IO.println "Weak CAS preparation equivalence regressions passed"
