-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace Noalias

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure bumpThenReadLocals where
  deriving Inhabited

inductive bumpThenReadExit where
  | ret (v : BitVec 32)

def bumpThenRead (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  Zig.naEnter
  let e ← ((do
    let i2 ← Zig.load (BitVec 32) 4 p0
    Zig.naMark (some 0) none
    let i3 ← Zig.add false i2 (1 : BitVec 32)
    Zig.store (α := BitVec 32) 4 p0 i3
    Zig.naMark (some 0) (some 0)
    let i5 ← Zig.load (BitVec 32) 4 p1
    Zig.naMark none none
    pure (.ret i5)) : Zig.MM bumpThenReadLocals bumpThenReadExit).run' (default : bumpThenReadLocals)
  Zig.naExit
  match e with
  | .ret v => pure v

structure bumpOtherLocals where
  x : Zig.Ptr
  y : Zig.Ptr
  deriving Inhabited

inductive bumpOtherExit where
  | ret (v : BitVec 32)
  | br5 (v : Zig.Ptr)

def bumpOther (p0 : Bool) : Zig.MemM (BitVec 32) := do
  let s1 ← Zig.allocStack 4 4
  let s3 ← Zig.allocStack 4 4
  let e ← ((do
    let i1 ← pure (← get).x
    Zig.store (α := BitVec 32) 4 i1 (5 : BitVec 32)
    let i3 ← pure (← get).y
    Zig.store (α := BitVec 32) 4 i3 (7 : BitVec 32)
    match ← ((do
      if p0 then (do
        let i7 ← pure (i1)
        pure (.br5 i7))
      else (do
        let i9 ← pure (i3)
        pure (.br5 i9))) : Zig.MM bumpOtherLocals bumpOtherExit) with
    | .br5 v5 => (do
      let i11 ← Zig.callM (bumpThenRead i1 v5)
      pure (.ret i11))
    | e => pure e) : Zig.MM bumpOtherLocals bumpOtherExit).run' { (default : bumpOtherLocals) with x := s1, y := s3 }
  Zig.free s1
  Zig.free s3
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure copyLocals where
  local3 : BitVec 64
  deriving Inhabited

inductive copyExit where
  | ret
  | br8
  | br5
  | rep6

def copy.again6 : copyExit → Bool
  | .rep6 => true
  | _ => false

def copy.loop6 (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : BitVec 64) : Zig.MM copyLocals copyExit := do
  let i7 ← pure ((← get).local3)
  match ← ((do
    let i9 ← pure (i7)
    let i10 ← pure (p2)
    let i11 ← pure (Zig.lt false i9 i10)
    if i11 then (do
      let i13 ← Zig.callM (Zig.ptrProject p0 (·.elem 1 i7))
      Zig.naMark none none
      let i14 ← Zig.callM (Zig.load (BitVec 8) 1 (p1.elem 1 i7))
      Zig.naMark (some 1) none
      Zig.store (α := BitVec 8) 1 i13 i14
      Zig.naMark (some 0) (some 0)
      pure .br8)
    else (do
      pure .br5)) : Zig.MM copyLocals copyExit) with
  | .br8 => (do
    let i18 ← Zig.add false i7 (1 : BitVec 64)
    modify (fun s => { s with local3 := i18 })
    pure .rep6)
  | e => pure e

def copy (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : BitVec 64) : Zig.MemM (Unit) := do
  Zig.naEnter
  let e ← ((do
    modify (fun s => { s with local3 := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (copy.loop6 p0 p1 p2) copy.again6) : Zig.MM copyLocals copyExit) with
    | .br5 => (do
      pure .ret)
    | e => pure e) : Zig.MM copyLocals copyExit).run' (default : copyLocals)
  Zig.naExit
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure readThenOverflowLocals where
  deriving Inhabited

inductive readThenOverflowExit where
  | ret (v : BitVec 8)

def readThenOverflow (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (BitVec 8) := do
  Zig.naEnter
  let e ← ((do
    Zig.store (α := BitVec 8) 1 p0 (200 : BitVec 8)
    Zig.naMark (some 0) (some 0)
    let i3 ← Zig.load (BitVec 8) 1 p1
    Zig.naMark none none
    let i4 ← Zig.add false i3 (100 : BitVec 8)
    pure (.ret i4)) : Zig.MM readThenOverflowLocals readThenOverflowExit).run' (default : readThenOverflowLocals)
  Zig.naExit
  match e with
  | .ret v => pure v

structure overflowAfterOverlapLocals where
  x : Zig.Ptr
  y : Zig.Ptr
  deriving Inhabited

inductive overflowAfterOverlapExit where
  | ret (v : BitVec 8)
  | br5 (v : Zig.Ptr)

def overflowAfterOverlap (p0 : Bool) : Zig.MemM (BitVec 8) := do
  let s1 ← Zig.allocStack 1 1
  let s3 ← Zig.allocStack 1 1
  let e ← ((do
    let i1 ← pure (← get).x
    Zig.store (α := BitVec 8) 1 i1 (0 : BitVec 8)
    let i3 ← pure (← get).y
    Zig.store (α := BitVec 8) 1 i3 (200 : BitVec 8)
    match ← ((do
      if p0 then (do
        let i7 ← pure (i1)
        pure (.br5 i7))
      else (do
        let i9 ← pure (i3)
        pure (.br5 i9))) : Zig.MM overflowAfterOverlapLocals overflowAfterOverlapExit) with
    | .br5 v5 => (do
      let i11 ← Zig.callM (readThenOverflow i1 v5)
      pure (.ret i11))
    | e => pure e) : Zig.MM overflowAfterOverlapLocals overflowAfterOverlapExit).run' { (default : overflowAfterOverlapLocals) with x := s1, y := s3 }
  Zig.free s1
  Zig.free s3
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure readCheckedLocals where
  deriving Inhabited

inductive readCheckedExit where
  | ret (v : BitVec 8)
  | br2

def readChecked (p0 : Zig.Ptr) : Zig.MemM (BitVec 8) := do
  let e ← ((do
    let i1 ← Zig.load (BitVec 8) 1 p0
    Zig.naMark none none
    match ← ((do
      let i3 ← pure (i1 == (200 : BitVec 8))
      if i3 then (do
        throw .unreachable)
      else (do
        pure .br2)) : Zig.MM readCheckedLocals readCheckedExit) with
    | .br2 => (do
      pure (.ret i1))
    | e => pure e) : Zig.MM readCheckedLocals readCheckedExit).run' (default : readCheckedLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure writeThenCallLocals where
  deriving Inhabited

inductive writeThenCallExit where
  | ret (v : BitVec 8)

def writeThenCall (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (BitVec 8) := do
  Zig.naEnter
  let e ← ((do
    Zig.store (α := BitVec 8) 1 p0 (200 : BitVec 8)
    Zig.naMark (some 0) (some 0)
    let i3 ← Zig.callM (readChecked p1)
    Zig.naMark none none
    pure (.ret i3)) : Zig.MM writeThenCallLocals writeThenCallExit).run' (default : writeThenCallLocals)
  Zig.naExit
  match e with
  | .ret v => pure v

structure panicAfterOverlapLocals where
  x : Zig.Ptr
  y : Zig.Ptr
  deriving Inhabited

inductive panicAfterOverlapExit where
  | ret (v : BitVec 8)
  | br5 (v : Zig.Ptr)

def panicAfterOverlap (p0 : Bool) : Zig.MemM (BitVec 8) := do
  let s1 ← Zig.allocStack 1 1
  let s3 ← Zig.allocStack 1 1
  let e ← ((do
    let i1 ← pure (← get).x
    Zig.store (α := BitVec 8) 1 i1 (0 : BitVec 8)
    let i3 ← pure (← get).y
    Zig.store (α := BitVec 8) 1 i3 (200 : BitVec 8)
    match ← ((do
      if p0 then (do
        let i7 ← pure (i1)
        pure (.br5 i7))
      else (do
        let i9 ← pure (i3)
        pure (.br5 i9))) : Zig.MM panicAfterOverlapLocals panicAfterOverlapExit) with
    | .br5 v5 => (do
      let i11 ← Zig.callM (writeThenCall i1 v5)
      pure (.ret i11))
    | e => pure e) : Zig.MM panicAfterOverlapLocals panicAfterOverlapExit).run' { (default : panicAfterOverlapLocals) with x := s1, y := s3 }
  Zig.free s1
  Zig.free s3
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure shiftCopyLocals where
  buf : Zig.Ptr
  local20 : Zig.Slice
  deriving Inhabited

inductive shiftCopyExit where
  | ret (v : BitVec 8)
  | br7
  | br14

def shiftCopy (p0 : BitVec 64) (p1 : BitVec 64) : Zig.MemM (BitVec 8) := do
  let s2 ← Zig.allocStack 16 1
  let e ← ((do
    let i2 ← pure (← get).buf
    Zig.store (α := Vector (BitVec 8) 16) 1 i2 (#v[(1 : BitVec 8), (2 : BitVec 8), (3 : BitVec 8), (4 : BitVec 8), (5 : BitVec 8), (6 : BitVec 8), (7 : BitVec 8), (8 : BitVec 8), (9 : BitVec 8), (10 : BitVec 8), (11 : BitVec 8), (12 : BitVec 8), (13 : BitVec 8), (14 : BitVec 8), (15 : BitVec 8), (16 : BitVec 8)] : Vector (BitVec 8) 16)
    let i4 ← pure (i2)
    let i5 ← Zig.callM (Zig.ptrProject i4 (·.elem 1 p0))
    let i6 ← pure (Zig.le false p0 (16 : BitVec 64))
    match ← ((do
      if i6 then (do
        pure .br7)
      else (do
        throw .outOfBounds)) : Zig.MM shiftCopyLocals shiftCopyExit) with
    | .br7 => (do
      let i12 ← Zig.sub false (16 : BitVec 64) p0
      let i13 ← pure (Zig.le false (16 : BitVec 64) (16 : BitVec 64))
      match ← ((do
        if i13 then (do
          pure .br14)
        else (do
          throw .outOfBounds)) : Zig.MM shiftCopyLocals shiftCopyExit) with
      | .br14 => (do
        let i19 ← Zig.callM (Zig.checkSliceEnd (16 : BitVec 64) p0 i12 0 >>= fun _ => pure (⟨i5, i12⟩ : Zig.Slice))
        modify (fun s => { s with local20 := i19 })
        let i24 ← pure (((← get).local20).ptr)
        let i25 ← pure (i2)
        let _i26 ← Zig.callM (copy i24 i25 p1)
        let i27 ← Zig.callM (Zig.load (BitVec 8) 1 (i2.elem 1 (15 : BitVec 64)))
        pure (.ret i27))
      | e => pure e)
    | e => pure e) : Zig.MM shiftCopyLocals shiftCopyExit).run' { (default : shiftCopyLocals) with buf := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure sinkLocals where
  deriving Inhabited

inductive sinkExit where
  | ret

def sink (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    Zig.store (α := BitVec 32) 4 p0 (0 : BitVec 32)
    pure .ret) : Zig.MM sinkLocals sinkExit).run' (default : sinkLocals)
  match e with
  | .ret => pure ()

structure sumLocals where
  deriving Inhabited

inductive sumExit where
  | ret (v : BitVec 32)

def sum (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  Zig.naEnter
  let e ← ((do
    let i2 ← Zig.load (BitVec 32) 4 p0
    Zig.naMark (some 0) none
    let i3 ← Zig.load (BitVec 32) 4 p1
    Zig.naMark (some 1) none
    let i4 ← Zig.add false i2 i3
    pure (.ret i4)) : Zig.MM sumLocals sumExit).run' (default : sumLocals)
  Zig.naExit
  match e with
  | .ret v => pure v

structure sumSelfLocals where
  x : Zig.Ptr
  deriving Inhabited

inductive sumSelfExit where
  | ret (v : BitVec 32)

def sumSelf  : Zig.MemM (BitVec 32) := do
  let s0 ← Zig.allocStack 4 4
  let e ← ((do
    let i0 ← pure (← get).x
    Zig.store (α := BitVec 32) 4 i0 (21 : BitVec 32)
    let i2 ← pure (i0)
    let i3 ← pure (i0)
    let i4 ← Zig.callM (sum i2 i3)
    pure (.ret i4)) : Zig.MM sumSelfLocals sumSelfExit).run' { (default : sumSelfLocals) with x := s0 }
  Zig.free s0
  match e with
  | .ret v => pure v

structure swapLocals where
  deriving Inhabited

inductive swapExit where
  | ret

def swap (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (Unit) := do
  Zig.naEnter
  let e ← ((do
    let i2 ← Zig.load (BitVec 32) 4 p0
    Zig.naMark (some 0) none
    let i3 ← Zig.load (BitVec 32) 4 p1
    Zig.naMark (some 1) none
    Zig.store (α := BitVec 32) 4 p0 i3
    Zig.naMark (some 0) (some 0)
    Zig.store (α := BitVec 32) 4 p1 i2
    Zig.naMark (some 1) (some 1)
    pure .ret) : Zig.MM swapLocals swapExit).run' (default : swapLocals)
  Zig.naExit
  match e with
  | .ret => pure ()

structure swapSelfLocals where
  x : Zig.Ptr
  y : Zig.Ptr
  deriving Inhabited

inductive swapSelfExit where
  | ret (v : BitVec 32)
  | br5 (v : Zig.Ptr)

def swapSelf (p0 : Bool) : Zig.MemM (BitVec 32) := do
  let s1 ← Zig.allocStack 4 4
  let s3 ← Zig.allocStack 4 4
  let e ← ((do
    let i1 ← pure (← get).x
    Zig.store (α := BitVec 32) 4 i1 (1 : BitVec 32)
    let i3 ← pure (← get).y
    Zig.store (α := BitVec 32) 4 i3 (2 : BitVec 32)
    match ← ((do
      if p0 then (do
        pure (.br5 i1))
      else (do
        pure (.br5 i3))) : Zig.MM swapSelfLocals swapSelfExit) with
    | .br5 v5 => (do
      let _i9 ← Zig.callM (swap i1 v5)
      let i10 ← Zig.load (BitVec 32) 4 i1
      let i11 ← Zig.mul false i10 (10 : BitVec 32)
      let i12 ← Zig.load (BitVec 32) 4 i3
      let i13 ← Zig.add false i11 i12
      pure (.ret i13))
    | e => pure e) : Zig.MM swapSelfLocals swapSelfExit).run' { (default : swapSelfLocals) with x := s1, y := s3 }
  Zig.free s1
  Zig.free s3
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure twoBuffersLocals where
  a : Zig.Ptr
  b : Zig.Ptr
  deriving Inhabited

inductive twoBuffersExit where
  | ret (v : BitVec 8)

def twoBuffers (p0 : BitVec 64) : Zig.MemM (BitVec 8) := do
  let s3 ← Zig.allocStack 4 1
  let s1 ← Zig.allocStack 4 1
  let e ← ((do
    let i1 ← pure (← get).a
    Zig.store (α := Vector (BitVec 8) 4) 1 i1 (#v[(1 : BitVec 8), (2 : BitVec 8), (3 : BitVec 8), (4 : BitVec 8)] : Vector (BitVec 8) 4)
    let i3 ← pure (← get).b
    Zig.store (α := Vector (BitVec 8) 4) 1 i3 (#v[(0 : BitVec 8), (0 : BitVec 8), (0 : BitVec 8), (0 : BitVec 8)] : Vector (BitVec 8) 4)
    let i5 ← pure (i3)
    let i6 ← pure (i1)
    let _i7 ← Zig.callM (copy i5 i6 p0)
    let i8 ← Zig.callM (Zig.load (BitVec 8) 1 (i3.elem 1 (3 : BitVec 64)))
    pure (.ret i8)) : Zig.MM twoBuffersLocals twoBuffersExit).run' { (default : twoBuffersLocals) with b := s3, a := s1 }
  Zig.free s3
  Zig.free s1
  match e with
  | .ret v => pure v

end Noalias