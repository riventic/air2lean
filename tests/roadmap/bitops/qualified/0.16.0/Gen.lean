import ZigLean


namespace Bitops

structure cardinalityLocals where
  deriving Inhabited

inductive cardinalityExit where
  | ret (v : BitVec 32)

def cardinality (p0 : BitVec 64) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (Zig.popcount 7 p0)
    let i2 ← Zig.intCast false false 32 i1
    pure (.ret i2)) : Zig.M cardinalityLocals cardinalityExit).run' (default : cardinalityLocals)
  match e with
  | .ret v => pure v

structure clearLowestLocals where
  deriving Inhabited

inductive clearLowestExit where
  | ret (v : BitVec 64)

def clearLowest (p0 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← pure (Zig.subWrap p0 (1 : BitVec 64))
    let i2 ← pure (p0 &&& i1)
    pure (.ret i2)) : Zig.M clearLowestLocals clearLowestExit).run' (default : clearLowestLocals)
  match e with
  | .ret v => pure v

structure counts8Locals where
  deriving Inhabited

inductive counts8Exit where
  | ret (v : BitVec 32)

def counts8 (p0 : BitVec 8) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (Zig.clz 4 p0)
    let i2 ← Zig.intCast false false 32 i1
    let i3 ← pure (Zig.ctz 4 p0)
    let i4 ← Zig.intCast false false 32 i3
    let i5 ← pure (Zig.shl i4 (8 : BitVec 5))
    let i6 ← pure (i2 ||| i5)
    let i7 ← pure (Zig.popcount 4 p0)
    let i8 ← Zig.intCast false false 32 i7
    let i9 ← pure (Zig.shl i8 (16 : BitVec 5))
    let i10 ← pure (i6 ||| i9)
    pure (.ret i10)) : Zig.M counts8Locals counts8Exit).run' (default : counts8Locals)
  match e with
  | .ret v => pure v

structure countsNarrowLocals where
  deriving Inhabited

inductive countsNarrowExit where
  | ret (v : BitVec 32)

def countsNarrow (p0 : BitVec 8) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (Zig.trunc 3 p0)
    let i2 ← pure (Zig.clz 2 i1)
    let i3 ← Zig.intCast false false 32 i2
    let i4 ← pure (Zig.ctz 2 i1)
    let i5 ← Zig.intCast false false 32 i4
    let i6 ← pure (Zig.shl i5 (8 : BitVec 5))
    let i7 ← pure (i3 ||| i6)
    let i8 ← pure (Zig.popcount 2 i1)
    let i9 ← Zig.intCast false false 32 i8
    let i10 ← pure (Zig.shl i9 (16 : BitVec 5))
    let i11 ← pure (i7 ||| i10)
    pure (.ret i11)) : Zig.M countsNarrowLocals countsNarrowExit).run' (default : countsNarrowLocals)
  match e with
  | .ret v => pure v

structure countsOneLocals where
  deriving Inhabited

inductive countsOneExit where
  | ret (v : BitVec 32)

def countsOne (p0 : BitVec 8) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (Zig.trunc 1 p0)
    let i2 ← pure (Zig.clz 1 i1)
    let i3 ← Zig.intCast false false 32 i2
    let i4 ← pure (Zig.ctz 1 i1)
    let i5 ← Zig.intCast false false 32 i4
    let i6 ← pure (Zig.shl i5 (8 : BitVec 5))
    let i7 ← pure (i3 ||| i6)
    let i8 ← pure (Zig.popcount 1 i1)
    let i9 ← Zig.intCast false false 32 i8
    let i10 ← pure (Zig.shl i9 (16 : BitVec 5))
    let i11 ← pure (i7 ||| i10)
    pure (.ret i11)) : Zig.M countsOneLocals countsOneExit).run' (default : countsOneLocals)
  match e with
  | .ret v => pure v

structure countsSigned8Locals where
  deriving Inhabited

inductive countsSigned8Exit where
  | ret (v : BitVec 32)

def countsSigned8 (p0 : BitVec 8) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (Zig.clz 4 p0)
    let i2 ← Zig.intCast false false 32 i1
    let i3 ← pure (Zig.ctz 4 p0)
    let i4 ← Zig.intCast false false 32 i3
    let i5 ← pure (Zig.shl i4 (8 : BitVec 5))
    let i6 ← pure (i2 ||| i5)
    let i7 ← pure (Zig.popcount 4 p0)
    let i8 ← Zig.intCast false false 32 i7
    let i9 ← pure (Zig.shl i8 (16 : BitVec 5))
    let i10 ← pure (i6 ||| i9)
    pure (.ret i10)) : Zig.M countsSigned8Locals countsSigned8Exit).run' (default : countsSigned8Locals)
  match e with
  | .ret v => pure v

structure firstSetLocals where
  deriving Inhabited

inductive firstSetExit where
  | ret (v : BitVec 32)
  | br1

def firstSet (p0 : BitVec 64) : Zig.Result (BitVec 32) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure (p0 == (0 : BitVec 64))
      if i2 then (do
        pure (.ret (64 : BitVec 32)))
      else (do
        pure .br1)) : Zig.M firstSetLocals firstSetExit) with
    | .br1 => (do
      let i6 ← pure (Zig.ctz 7 p0)
      let i7 ← Zig.intCast false false 32 i6
      pure (.ret i7))
    | e => pure e) : Zig.M firstSetLocals firstSetExit).run' (default : firstSetLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure leadingLanesLocals where
  deriving Inhabited

inductive leadingLanesExit where
  | ret (v : Zig.Vec (BitVec 8) 4)

def leadingLanes (p0 : Zig.Vec (BitVec 8) 4) : Zig.Result (Zig.Vec (BitVec 8) 4) := do
  let e ← ((do
    let i1 ← Zig.Vec.mapM (fun x0 => pure (Zig.clz 4 x0)) p0
    let i2 ← Zig.Vec.mapM (fun x0 => Zig.intCast false false 8 x0) i1
    pure (.ret i2)) : Zig.M leadingLanesLocals leadingLanesExit).run' (default : leadingLanesLocals)
  match e with
  | .ret v => pure v

structure populationLanesLocals where
  deriving Inhabited

inductive populationLanesExit where
  | ret (v : Zig.Vec (BitVec 8) 4)

def populationLanes (p0 : Zig.Vec (BitVec 8) 4) : Zig.Result (Zig.Vec (BitVec 8) 4) := do
  let e ← ((do
    let i1 ← Zig.Vec.mapM (fun x0 => pure (Zig.popcount 4 x0)) p0
    let i2 ← Zig.Vec.mapM (fun x0 => Zig.intCast false false 8 x0) i1
    pure (.ret i2)) : Zig.M populationLanesLocals populationLanesExit).run' (default : populationLanesLocals)
  match e with
  | .ret v => pure v

structure shiftLanesLocals where
  deriving Inhabited

inductive shiftLanesExit where
  | ret (v : Zig.Vec (BitVec 16) 4)

def shiftLanes (p0 : Zig.Vec (BitVec 8) 4) (p1 : Zig.Vec (BitVec 8) 4) : Zig.Result (Zig.Vec (BitVec 16) 4) := do
  let e ← ((do
    let i2 ← Zig.Vec.mapM (fun x0 => pure (Zig.trunc 3 x0)) p1
    let i3 ← (Zig.Vec.unzip <$> Zig.Vec.map2M (fun x0 x1 => Zig.shlWithOverflow false x0 x1) p0 i2)
    let i4 ← pure ((i3).1)
    let i5 ← Zig.Vec.mapM (fun x0 => Zig.intCast false false 16 x0) i4
    let i6 ← pure ((i3).2)
    let i7 ← Zig.Vec.mapM (fun x0 => Zig.intCast false false 16 x0) i6
    let i8 ← Zig.Vec.map2M (fun x0 x1 => pure (Zig.shl x0 x1)) i7 ((⟨#v[(8 : BitVec 4), (8 : BitVec 4), (8 : BitVec 4), (8 : BitVec 4)]⟩) : Zig.Vec (BitVec 4) 4)
    let i9 ← Zig.Vec.map2M (fun x0 x1 => pure (x0 ||| x1)) i5 i8
    pure (.ret i9)) : Zig.M shiftLanesLocals shiftLanesExit).run' (default : shiftLanesLocals)
  match e with
  | .ret v => pure v

structure shiftNarrowLocals where
  deriving Inhabited

inductive shiftNarrowExit where
  | ret (v : BitVec 8)

def shiftNarrow (p0 : BitVec 8) (p1 : BitVec 8) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i2 ← pure (Zig.trunc 3 p0)
    let i3 ← pure (Zig.trunc 2 p1)
    let i4 ← Zig.shlWithOverflow false i2 i3
    let i5 ← pure ((i4).1)
    let i6 ← Zig.intCast false false 8 i5
    let i7 ← pure ((i4).2)
    let i8 ← Zig.intCast false false 8 i7
    let i9 ← pure (Zig.shl i8 (3 : BitVec 3))
    let i10 ← pure (i6 ||| i9)
    pure (.ret i10)) : Zig.M shiftNarrowLocals shiftNarrowExit).run' (default : shiftNarrowLocals)
  match e with
  | .ret v => pure v

structure shiftSigned8Locals where
  deriving Inhabited

inductive shiftSigned8Exit where
  | ret (v : BitVec 16)

def shiftSigned8 (p0 : BitVec 8) (p1 : BitVec 8) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i2 ← pure (Zig.trunc 3 p1)
    let i3 ← Zig.shlWithOverflow true p0 i2
    let i4 ← pure ((i3).1)
    let i5 ← pure (i4)
    let i6 ← Zig.intCast false false 16 i5
    let i7 ← pure ((i3).2)
    let i8 ← Zig.intCast false false 16 i7
    let i9 ← pure (Zig.shl i8 (8 : BitVec 4))
    let i10 ← pure (i6 ||| i9)
    pure (.ret i10)) : Zig.M shiftSigned8Locals shiftSigned8Exit).run' (default : shiftSigned8Locals)
  match e with
  | .ret v => pure v

structure shiftSignedLanesLocals where
  deriving Inhabited

inductive shiftSignedLanesExit where
  | ret (v : Zig.Vec (BitVec 16) 4)

def shiftSignedLanes (p0 : Zig.Vec (BitVec 8) 4) (p1 : Zig.Vec (BitVec 8) 4) : Zig.Result (Zig.Vec (BitVec 16) 4) := do
  let e ← ((do
    let i2 ← Zig.Vec.mapM (fun x0 => pure (Zig.trunc 3 x0)) p1
    let i3 ← (Zig.Vec.unzip <$> Zig.Vec.map2M (fun x0 x1 => Zig.shlWithOverflow true x0 x1) p0 i2)
    let i4 ← pure ((i3).1)
    let i5 ← Zig.Vec.mapM (fun x0 => Zig.intCast true true 16 x0) i4
    let i6 ← Zig.Vec.map2M (fun x0 x1 => pure (x0 &&& x1)) i5 ((⟨#v[(255 : BitVec 16), (255 : BitVec 16), (255 : BitVec 16), (255 : BitVec 16)]⟩) : Zig.Vec (BitVec 16) 4)
    let i7 ← pure ((i3).2)
    let i8 ← Zig.Vec.mapM (fun x0 => Zig.intCast false true 16 x0) i7
    let i9 ← Zig.Vec.map2M (fun x0 x1 => pure (Zig.shl x0 x1)) i8 ((⟨#v[(8 : BitVec 4), (8 : BitVec 4), (8 : BitVec 4), (8 : BitVec 4)]⟩) : Zig.Vec (BitVec 4) 4)
    let i10 ← Zig.Vec.map2M (fun x0 x1 => pure (x0 ||| x1)) i6 i9
    pure (.ret i10)) : Zig.M shiftSignedLanesLocals shiftSignedLanesExit).run' (default : shiftSignedLanesLocals)
  match e with
  | .ret v => pure v

structure shiftSignedNarrowLocals where
  deriving Inhabited

inductive shiftSignedNarrowExit where
  | ret (v : BitVec 8)

def shiftSignedNarrow (p0 : BitVec 8) (p1 : BitVec 8) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i2 ← pure (Zig.trunc 3 p0)
    let i3 ← pure (Zig.trunc 2 p1)
    let i4 ← Zig.shlWithOverflow true i2 i3
    let i5 ← pure ((i4).1)
    let i6 ← pure (i5)
    let i7 ← Zig.intCast false false 8 i6
    let i8 ← pure ((i4).2)
    let i9 ← Zig.intCast false false 8 i8
    let i10 ← pure (Zig.shl i9 (3 : BitVec 3))
    let i11 ← pure (i7 ||| i10)
    pure (.ret i11)) : Zig.M shiftSignedNarrowLocals shiftSignedNarrowExit).run' (default : shiftSignedNarrowLocals)
  match e with
  | .ret v => pure v

structure shiftUnsigned8Locals where
  deriving Inhabited

inductive shiftUnsigned8Exit where
  | ret (v : BitVec 16)

def shiftUnsigned8 (p0 : BitVec 8) (p1 : BitVec 8) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i2 ← pure (Zig.trunc 3 p1)
    let i3 ← Zig.shlWithOverflow false p0 i2
    let i4 ← pure ((i3).1)
    let i5 ← Zig.intCast false false 16 i4
    let i6 ← pure ((i3).2)
    let i7 ← Zig.intCast false false 16 i6
    let i8 ← pure (Zig.shl i7 (8 : BitVec 4))
    let i9 ← pure (i5 ||| i8)
    pure (.ret i9)) : Zig.M shiftUnsigned8Locals shiftUnsigned8Exit).run' (default : shiftUnsigned8Locals)
  match e with
  | .ret v => pure v

structure trailingLanesLocals where
  deriving Inhabited

inductive trailingLanesExit where
  | ret (v : Zig.Vec (BitVec 8) 4)

def trailingLanes (p0 : Zig.Vec (BitVec 8) 4) : Zig.Result (Zig.Vec (BitVec 8) 4) := do
  let e ← ((do
    let i1 ← Zig.Vec.mapM (fun x0 => pure (Zig.ctz 4 x0)) p0
    let i2 ← Zig.Vec.mapM (fun x0 => Zig.intCast false false 8 x0) i1
    pure (.ret i2)) : Zig.M trailingLanesLocals trailingLanesExit).run' (default : trailingLanesLocals)
  match e with
  | .ret v => pure v

end Bitops