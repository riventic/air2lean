import ZigLean


namespace Pointers

structure Job where
  duration : BitVec 32
  due : BitVec 32
  weight : BitVec 8
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Job where
  size := 12
  align := 4
  encode v := Zig.Enc.fields 12 [(0, Zig.Enc.encode v.duration), (4, Zig.Enc.encode v.due), (8, Zig.Enc.encode v.weight)]
  decode bs := do pure { duration := ← Zig.Enc.decodeAt bs 0, due := ← Zig.Enc.decodeAt bs 4, weight := ← Zig.Enc.decodeAt bs 8 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure addDownLocals where
  deriving Inhabited

inductive addDownExit where
  | ret
  | br2

mutual

def addDown (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Unit) := do
  Zig.enterFrame 0
  let e ← ((do
    match ← ((do
      let i3 ← pure (p1 == (0 : BitVec 32))
      if i3 then (do
        pure .ret)
      else (do
        pure .br2)) : Zig.MM addDownLocals addDownExit) with
    | .br2 => (do
      let i7 ← Zig.load (BitVec 64) 8 p0
      let i8 ← Zig.intCast false false 64 p1
      let i9 ← Zig.add false i7 i8
      Zig.store (α := BitVec 64) 8 p0 i9
      let i11 ← Zig.sub false p1 (1 : BitVec 32)
      let _i12 ← Zig.callM (addDown p0 i11)
      pure .ret)
    | e => pure e) : Zig.MM addDownLocals addDownExit).run' (default : addDownLocals)
  Zig.leaveFrame 0
  match e with
  | .ret => pure ()
  | _ => throw .panic
partial_fixpoint

end

structure addToLocals where
  deriving Inhabited

inductive addToExit where
  | ret

def addTo (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← Zig.load (BitVec 64) 8 p0
    let i3 ← Zig.intCast false false 64 p1
    let i4 ← Zig.add false i2 i3
    Zig.store (α := BitVec 64) 8 p0 i4
    pure .ret) : Zig.MM addToLocals addToExit).run' (default : addToLocals)
  match e with
  | .ret => pure ()

structure bumpOptLocals where
  deriving Inhabited

inductive bumpOptExit where
  | ret
  | br1

def bumpOpt (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    match ← ((do
      let i2 ← Zig.optIsSome (BitVec 32) p0
      if i2 then (do
        let i4 ← pure p0
        let i5 ← Zig.load (BitVec 32) 4 i4
        let i6 ← Zig.add false i5 (1 : BitVec 32)
        Zig.store (α := BitVec 32) 4 i4 i6
        pure .br1)
      else (do
        pure .br1)) : Zig.MM bumpOptLocals bumpOptExit) with
    | .br1 => (do
      pure .ret)
    | e => pure e) : Zig.MM bumpOptLocals bumpOptExit).run' (default : bumpOptLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure copyJobLocals where
  deriving Inhabited

inductive copyJobExit where
  | ret

def copyJob (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← Zig.load (Job) 4 p1
    Zig.store (α := Job) 4 p0 i2
    pure .ret) : Zig.MM copyJobLocals copyJobExit).run' (default : copyJobLocals)
  match e with
  | .ret => pure ()

structure delayLocals where
  deriving Inhabited

inductive delayExit where
  | ret

def delay (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.load (BitVec 32) 4 i2
    let i4 ← Zig.add false i3 p1
    Zig.store (α := BitVec 32) 4 i2 i4
    pure .ret) : Zig.MM delayLocals delayExit).run' (default : delayLocals)
  match e with
  | .ret => pure ()

structure dueOfLocals where
  deriving Inhabited

inductive dueOfExit where
  | ret (v : Zig.Ptr)

def dueOf (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← Zig.callM (Zig.ptrProject p0 (·.add 4))
    pure (.ret i1)) : Zig.MM dueOfLocals dueOfExit).run' (default : dueOfLocals)
  match e with
  | .ret v => pure v

structure maxPtrLocals where
  deriving Inhabited

inductive maxPtrExit where
  | ret (v : Option (Zig.Ptr))
  | br2 (v : Zig.Ptr)
  | br8 (v : Zig.Ptr)
  | br14 (v : Option (Zig.Ptr))

def maxPtr (p0 : Option (Zig.Ptr)) (p1 : Option (Zig.Ptr)) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure ((p0).isSome)
      if i3 then (do
        let i5 ← Zig.optPayload p0
        pure (.br2 i5))
      else (do
        pure (.ret p1))) : Zig.MM maxPtrLocals maxPtrExit) with
    | .br2 v2 => (do
      match ← ((do
        let i9 ← pure ((p1).isSome)
        if i9 then (do
          let i11 ← Zig.optPayload p1
          pure (.br8 i11))
        else (do
          pure (.ret p0))) : Zig.MM maxPtrLocals maxPtrExit) with
      | .br8 v8 => (do
        match ← ((do
          let i15 ← Zig.load (BitVec 32) 4 v2
          let i16 ← Zig.load (BitVec 32) 4 v8
          let i17 ← pure (Zig.ge false i15 i16)
          if i17 then (do
            let i19 ← pure (v2)
            pure (.br14 i19))
          else (do
            let i21 ← pure (v8)
            pure (.br14 i21))) : Zig.MM maxPtrLocals maxPtrExit) with
        | .br14 v14 => (do
          pure (.ret v14))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM maxPtrLocals maxPtrExit).run' (default : maxPtrLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure sameLocals where
  deriving Inhabited

inductive sameExit where
  | ret (v : Bool)

def same (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (Bool) := do
  let e ← ((do
    let i2 ← Zig.callM (Zig.ptrEqAddr p0 p1)
    pure (.ret i2)) : Zig.MM sameLocals sameExit).run' (default : sameLocals)
  match e with
  | .ret v => pure v

structure setOptLocals where
  deriving Inhabited

inductive setOptExit where
  | ret

def setOpt (p0 : Zig.Ptr) (p1 : Option (BitVec 32)) : Zig.MemM (Unit) := do
  let e ← ((do
    Zig.store (α := Option (BitVec 32)) 4 p0 p1
    pure .ret) : Zig.MM setOptLocals setOptExit).run' (default : setOptLocals)
  match e with
  | .ret => pure ()

structure setOptJobLocals where
  deriving Inhabited

inductive setOptJobExit where
  | ret

def setOptJob (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← Zig.optSetSome (Job) p0
    let i3 ← pure i2
    Zig.store (α := BitVec 32) 4 i3 p1
    let i5 ← Zig.callM (Zig.ptrProject i2 (·.add 4))
    Zig.store (α := BitVec 32) 4 i5 (2 : BitVec 32)
    let i7 ← Zig.callM (Zig.ptrProject i2 (·.add 8))
    Zig.store (α := BitVec 8) 1 i7 (3 : BitVec 8)
    pure .ret) : Zig.MM setOptJobLocals setOptJobExit).run' (default : setOptJobLocals)
  match e with
  | .ret => pure ()

structure sumToLocals where
  acc : Zig.Ptr
  i : BitVec 32
  deriving Inhabited

inductive sumToExit where
  | ret (v : BitVec 64)
  | br7
  | br5
  | rep6

def sumTo.again6 : sumToExit → Bool
  | .rep6 => true
  | _ => false

def sumTo.loop6 (p0 : BitVec 32) (i1 : Zig.Ptr) : Zig.MM sumToLocals sumToExit := do
  match ← ((do
    let i8 ← pure ((← get).i)
    let i9 ← pure (Zig.lt false i8 p0)
    if i9 then (do
      let i11 ← pure ((← get).i)
      let _i12 ← Zig.callM (addTo i1 i11)
      let i13 ← pure ((← get).i)
      let i14 ← Zig.add false i13 (1 : BitVec 32)
      modify (fun s => { s with i := i14 })
      pure .br7)
    else (do
      pure .br5)) : Zig.MM sumToLocals sumToExit) with
  | .br7 => (do
    pure .rep6)
  | e => pure e

def sumTo (p0 : BitVec 32) : Zig.MemM (BitVec 64) := do
  let s1 ← Zig.allocStack 8 8
  let e ← ((do
    let i1 ← pure (← get).acc
    Zig.store (α := BitVec 64) 8 i1 (0 : BitVec 64)
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (sumTo.loop6 p0 i1) sumTo.again6) : Zig.MM sumToLocals sumToExit) with
    | .br5 => (do
      let i19 ← Zig.load (BitVec 64) 8 i1
      pure (.ret i19))
    | e => pure e) : Zig.MM sumToLocals sumToExit).run' { (default : sumToLocals) with acc := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure swapLocals where
  deriving Inhabited

inductive swapExit where
  | ret

def swap (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← Zig.load (BitVec 32) 4 p0
    let i3 ← Zig.load (BitVec 32) 4 p1
    Zig.store (α := BitVec 32) 4 p0 i3
    Zig.store (α := BitVec 32) 4 p1 i2
    pure .ret) : Zig.MM swapLocals swapExit).run' (default : swapLocals)
  match e with
  | .ret => pure ()

end Pointers