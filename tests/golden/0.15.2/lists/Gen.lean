import ZigLean


namespace Lists

structure Node where
  val : BitVec 32
  next : Option (Zig.Ptr)
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Node where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(8, Zig.Enc.encode v.val), (0, Zig.Enc.encode v.next)]
  decode bs := do pure { val := ← Zig.Enc.decodeAt bs 8, next := ← Zig.Enc.decodeAt bs 0 }

structure array_list_Aligned_u32_null where
  items : Zig.Slice
  capacity : BitVec 64
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc array_list_Aligned_u32_null where
  size := 24
  align := 8
  encode v := Zig.Enc.fields 24 [(0, Zig.Enc.encode v.items), (16, Zig.Enc.encode v.capacity)]
  decode bs := do pure { items := ← Zig.Enc.decodeAt bs 0, capacity := ← Zig.Enc.decodeAt bs 16 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: a constant
  (Zig.Enc.encode ((#v[] : Vector (BitVec 32) 0) : Vector (BitVec 32) 0), 4, .constGlobal)]

structure array_list_Aligned_u32_null_growCapacityLocals where
  new : BitVec 64
  deriving Inhabited

inductive array_list_Aligned_u32_null_growCapacityExit where
  | ret (v : BitVec 64)
  | br11
  | rep4

def array_list_Aligned_u32_null_growCapacity.again4 : array_list_Aligned_u32_null_growCapacityExit → Bool
  | .rep4 => true
  | _ => false

def array_list_Aligned_u32_null_growCapacity.loop4 (p1 : BitVec 64) : Zig.M array_list_Aligned_u32_null_growCapacityLocals array_list_Aligned_u32_null_growCapacityExit := do
  let i5 ← pure ((← get).new)
  let i6 ← pure ((← get).new)
  let i7 ← Zig.divTrunc false i6 (2 : BitVec 64)
  let i8 ← Zig.add false i7 (32 : BitVec 64)
  let i9 ← pure (Zig.addSat false i5 i8)
  modify (fun s => { s with new := i9 })
  match ← ((do
    let i12 ← pure ((← get).new)
    let i13 ← pure (i12)
    let i14 ← pure (p1)
    let i15 ← pure (Zig.ge false i13 i14)
    if i15 then (do
      let i17 ← pure ((← get).new)
      pure (.ret i17))
    else (do
      pure .br11)) : Zig.M array_list_Aligned_u32_null_growCapacityLocals array_list_Aligned_u32_null_growCapacityExit) with
  | .br11 => (do
    pure .rep4)
  | e => pure e

def array_list_Aligned_u32_null_growCapacity (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with new := p0 })
    Zig.loop (array_list_Aligned_u32_null_growCapacity.loop4 p1) array_list_Aligned_u32_null_growCapacity.again4) : Zig.M array_list_Aligned_u32_null_growCapacityLocals array_list_Aligned_u32_null_growCapacityExit).run' (default : array_list_Aligned_u32_null_growCapacityLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure array_list_Aligned_u32_null_allocatedSliceLocals where
  local1 : array_list_Aligned_u32_null
  deriving Inhabited

inductive array_list_Aligned_u32_null_allocatedSliceExit where
  | ret (v : Zig.Slice)

def array_list_Aligned_u32_null_allocatedSlice (p0 : array_list_Aligned_u32_null) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    modify (fun s => { s with local1 := p0 })
    let i6 ← pure ((p0).capacity)
    let i7 ← pure ((((← get).local1).items).ptr)
    let i8 ← pure i7
    let i9 ← Zig.sub false i6 (0 : BitVec 64)
    let i10 ← pure (⟨i8, i9⟩ : Zig.Slice)
    pure (.ret i10)) : Zig.MM array_list_Aligned_u32_null_allocatedSliceLocals array_list_Aligned_u32_null_allocatedSliceExit).run' (default : array_list_Aligned_u32_null_allocatedSliceLocals)
  match e with
  | .ret v => pure v

structure array_list_Aligned_u32_null_ensureTotalCapacityPreciseLocals where
  deriving Inhabited

inductive array_list_Aligned_u32_null_ensureTotalCapacityPreciseExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br3
  | br14
  | br40
  | br51
  | br63

-- air2lean-premises: {"ALC-09":[1]}
def array_list_Aligned_u32_null_ensureTotalCapacityPrecise (p0 : Zig.Ptr) (p1 : Zig.Allocator) (p2 : BitVec 64) : Zig.MemM (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.callM (Zig.ptrProject p0 (·.add 16))
      let i5 ← Zig.load (BitVec 64) 8 i4
      let i6 ← pure (i5)
      let i7 ← pure (p2)
      let i8 ← pure (Zig.ge false i6 i7)
      if i8 then (do
        pure (.ret (.ok () : Except Zig.ErrName (Unit))))
      else (do
        pure .br3)) : Zig.MM array_list_Aligned_u32_null_ensureTotalCapacityPreciseLocals array_list_Aligned_u32_null_ensureTotalCapacityPreciseExit) with
    | .br3 => (do
      let i12 ← Zig.load (array_list_Aligned_u32_null) 8 p0
      let i13 ← Zig.callM (array_list_Aligned_u32_null_allocatedSlice i12)
      match ← ((do
        let i15 ← Zig.callM (Zig.Allocator.remap p1 4 i13 p2)
        let i16 ← pure ((i15).isSome)
        if i16 then (do
          let i18 ← Zig.optPayload i15
          let i19 ← pure p0
          let i20 ← pure i19
          let i21 ← pure i18.ptr
          Zig.store (α := Zig.Ptr) 8 i20 i21
          let i23 ← Zig.callM (Zig.ptrProject p0 (·.add 16))
          let i24 ← pure i18.len
          Zig.store (α := BitVec 64) 8 i23 i24
          pure .br14)
        else (do
          let i27 ← Zig.callM (Zig.Allocator.alloc p1 4 4 p2)
          match i27 with
          | .error _ => (do
            let i29 ← Zig.callR (Zig.unwrapErr i27)
            let i30 ← pure ((.error i29) : Except Zig.ErrName (Unit))
            pure (.ret i30))
          | .ok v28 => (do
            let i32 ← pure p0
            let i33 ← Zig.load (Zig.Slice) 8 i32
            let i34 ← pure i33.len
            let i35 ← pure v28.ptr
            let i36 ← pure i35
            let i37 ← Zig.sub false i34 (0 : BitVec 64)
            let i38 ← pure v28.len
            let i39 ← pure (Zig.le false i34 i38)
            match ← ((do
              if i39 then (do
                pure .br40)
              else (do
                throw .outOfBounds)) : Zig.MM array_list_Aligned_u32_null_ensureTotalCapacityPreciseLocals array_list_Aligned_u32_null_ensureTotalCapacityPreciseExit) with
            | .br40 => (do
              let i45 ← Zig.callM (Zig.checkSliceEnd v28.len (0 : BitVec 64) i37 0 >>= fun _ => pure (⟨i36, i37⟩ : Zig.Slice))
              let i46 ← pure p0
              let i47 ← Zig.load (Zig.Slice) 8 i46
              let i48 ← pure i45.len
              let i49 ← pure i47.len
              let i50 ← pure (i48 == i49)
              match ← ((do
                if i50 then (do
                  pure .br51)
                else (do
                  throw .panic)) : Zig.MM array_list_Aligned_u32_null_ensureTotalCapacityPreciseLocals array_list_Aligned_u32_null_ensureTotalCapacityPreciseExit) with
              | .br51 => (do
                let i56 ← pure i47.ptr
                let i57 ← pure i45.ptr
                let i58 ← Zig.callM (Zig.ptrProject i56 (·.elem 4 i48))
                let i59 ← Zig.callM (Zig.ptrProject i57 (·.elem 4 i48))
                let i60 ← Zig.callM (Zig.ptrLe i58 i57)
                let i61 ← Zig.callM (Zig.ptrLe i59 i56)
                let i62 ← pure (i60 || i61)
                match ← ((do
                  if i62 then (do
                    pure .br63)
                  else (do
                    throw .panic)) : Zig.MM array_list_Aligned_u32_null_ensureTotalCapacityPreciseLocals array_list_Aligned_u32_null_ensureTotalCapacityPreciseExit) with
                | .br63 => (do
                  Zig.callM (Zig.memcpy 4 4 4 i45.ptr i56 i45.len i47.len)
                  let _i69 ← Zig.callM (Zig.Allocator.free p1 4 i13)
                  let i70 ← pure p0
                  let i71 ← pure i70
                  let i72 ← pure v28.ptr
                  Zig.store (α := Zig.Ptr) 8 i71 i72
                  let i74 ← Zig.callM (Zig.ptrProject p0 (·.add 16))
                  let i75 ← pure v28.len
                  Zig.store (α := BitVec 64) 8 i74 i75
                  pure .br14)
                | e => pure e)
              | e => pure e)
            | e => pure e))) : Zig.MM array_list_Aligned_u32_null_ensureTotalCapacityPreciseLocals array_list_Aligned_u32_null_ensureTotalCapacityPreciseExit) with
      | .br14 => (do
        pure (.ret (.ok () : Except Zig.ErrName (Unit))))
      | e => pure e)
    | e => pure e) : Zig.MM array_list_Aligned_u32_null_ensureTotalCapacityPreciseLocals array_list_Aligned_u32_null_ensureTotalCapacityPreciseExit).run' (default : array_list_Aligned_u32_null_ensureTotalCapacityPreciseLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure array_list_Aligned_u32_null_ensureTotalCapacityLocals where
  deriving Inhabited

inductive array_list_Aligned_u32_null_ensureTotalCapacityExit where
  | ret (v : Except Zig.ErrName (Unit))
  | br3

-- air2lean-premises: {"ALC-09":[1]}
def array_list_Aligned_u32_null_ensureTotalCapacity (p0 : Zig.Ptr) (p1 : Zig.Allocator) (p2 : BitVec 64) : Zig.MemM (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.callM (Zig.ptrProject p0 (·.add 16))
      let i5 ← Zig.load (BitVec 64) 8 i4
      let i6 ← pure (i5)
      let i7 ← pure (p2)
      let i8 ← pure (Zig.ge false i6 i7)
      if i8 then (do
        pure (.ret (.ok () : Except Zig.ErrName (Unit))))
      else (do
        pure .br3)) : Zig.MM array_list_Aligned_u32_null_ensureTotalCapacityLocals array_list_Aligned_u32_null_ensureTotalCapacityExit) with
    | .br3 => (do
      let i12 ← Zig.callM (Zig.ptrProject p0 (·.add 16))
      let i13 ← Zig.load (BitVec 64) 8 i12
      let i14 ← Zig.callR (array_list_Aligned_u32_null_growCapacity i13 p2)
      let i15 ← Zig.callM (array_list_Aligned_u32_null_ensureTotalCapacityPrecise p0 p1 i14)
      pure (.ret i15))
    | e => pure e) : Zig.MM array_list_Aligned_u32_null_ensureTotalCapacityLocals array_list_Aligned_u32_null_ensureTotalCapacityExit).run' (default : array_list_Aligned_u32_null_ensureTotalCapacityLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure debug_assertLocals where
  deriving Inhabited

inductive debug_assertExit where
  | ret
  | br1

def debug_assert (p0 : Bool) : Zig.Result (Unit) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure (!p0)
      if i2 then (do
        throw .unreachable)
      else (do
        pure .br1)) : Zig.M debug_assertLocals debug_assertExit) with
    | .br1 => (do
      pure .ret)
    | e => pure e) : Zig.M debug_assertLocals debug_assertExit).run' (default : debug_assertLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure array_list_Aligned_u32_null_addOneAssumeCapacityLocals where
  deriving Inhabited

inductive array_list_Aligned_u32_null_addOneAssumeCapacityExit where
  | ret (v : Zig.Ptr)
  | br23

def array_list_Aligned_u32_null_addOneAssumeCapacity (p0 : Zig.Ptr) : Zig.MemM (Zig.Ptr) := do
  let e ← ((do
    let i1 ← pure p0
    let i2 ← Zig.load (Zig.Slice) 8 i1
    let i3 ← pure i2.len
    let i4 ← Zig.callM (Zig.ptrProject p0 (·.add 16))
    let i5 ← Zig.load (BitVec 64) 8 i4
    let i6 ← pure (i3)
    let i7 ← pure (i5)
    let i8 ← pure (Zig.lt false i6 i7)
    let _i9 ← Zig.callR (debug_assert i8)
    let i10 ← pure p0
    let i11 ← Zig.callM (Zig.ptrProject i10 (·.add 8))
    let i12 ← Zig.load (BitVec 64) 8 i11
    let i13 ← Zig.add false i12 (1 : BitVec 64)
    Zig.store (α := BitVec 64) 8 i11 i13
    let i15 ← pure p0
    let i16 ← pure p0
    let i17 ← Zig.load (Zig.Slice) 8 i16
    let i18 ← pure i17.len
    let i19 ← Zig.sub false i18 (1 : BitVec 64)
    let i20 ← Zig.load (Zig.Slice) 8 i15
    let i21 ← pure i20.len
    let i22 ← pure (Zig.lt false i19 i21)
    match ← ((do
      if i22 then (do
        pure .br23)
      else (do
        throw .outOfBounds)) : Zig.MM array_list_Aligned_u32_null_addOneAssumeCapacityLocals array_list_Aligned_u32_null_addOneAssumeCapacityExit) with
    | .br23 => (do
      let i28 ← Zig.callM (Zig.ptrProject i20.ptr (·.elem 4 i19))
      pure (.ret i28))
    | e => pure e) : Zig.MM array_list_Aligned_u32_null_addOneAssumeCapacityLocals array_list_Aligned_u32_null_addOneAssumeCapacityExit).run' (default : array_list_Aligned_u32_null_addOneAssumeCapacityLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure array_list_Aligned_u32_null_addOneLocals where
  deriving Inhabited

inductive array_list_Aligned_u32_null_addOneExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

-- air2lean-premises: {"ALC-09":[1]}
def array_list_Aligned_u32_null_addOne (p0 : Zig.Ptr) (p1 : Zig.Allocator) : Zig.MemM (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    let i2 ← pure p0
    let i3 ← Zig.load (Zig.Slice) 8 i2
    let i4 ← pure i3.len
    let i5 ← Zig.add false i4 (1 : BitVec 64)
    let i6 ← Zig.callM (array_list_Aligned_u32_null_ensureTotalCapacity p0 p1 i5)
    match i6 with
    | .error _ => (do
      let i8 ← Zig.callR (Zig.unwrapErr i6)
      let i9 ← pure ((.error i8) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i9))
    | .ok _v7 => (do
      let i11 ← Zig.callM (array_list_Aligned_u32_null_addOneAssumeCapacity p0)
      let i12 ← pure ((.ok i11) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i12))) : Zig.MM array_list_Aligned_u32_null_addOneLocals array_list_Aligned_u32_null_addOneExit).run' (default : array_list_Aligned_u32_null_addOneLocals)
  match e with
  | .ret v => pure v

structure array_list_Aligned_u32_null_appendLocals where
  deriving Inhabited

inductive array_list_Aligned_u32_null_appendExit where
  | ret (v : Except Zig.ErrName (Unit))

-- air2lean-premises: {"ALC-09":[1]}
def array_list_Aligned_u32_null_append (p0 : Zig.Ptr) (p1 : Zig.Allocator) (p2 : BitVec 32) : Zig.MemM (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    let i3 ← Zig.callM (array_list_Aligned_u32_null_addOne p0 p1)
    match i3 with
    | .error _ => (do
      let i5 ← Zig.callR (Zig.unwrapErr i3)
      let i6 ← pure ((.error i5) : Except Zig.ErrName (Unit))
      pure (.ret i6))
    | .ok v4 => (do
      Zig.store (α := BitVec 32) 4 v4 p2
      pure (.ret (.ok () : Except Zig.ErrName (Unit))))) : Zig.MM array_list_Aligned_u32_null_appendLocals array_list_Aligned_u32_null_appendExit).run' (default : array_list_Aligned_u32_null_appendLocals)
  match e with
  | .ret v => pure v

structure array_list_Aligned_u32_null_clearAndFreeLocals where
  deriving Inhabited

inductive array_list_Aligned_u32_null_clearAndFreeExit where
  | ret

-- air2lean-premises: {"ALC-09":[1]}
def array_list_Aligned_u32_null_clearAndFree (p0 : Zig.Ptr) (p1 : Zig.Allocator) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← Zig.load (array_list_Aligned_u32_null) 8 p0
    let i3 ← Zig.callM (array_list_Aligned_u32_null_allocatedSlice i2)
    let _i4 ← Zig.callM (Zig.Allocator.free p1 4 i3)
    let i5 ← pure p0
    let i6 ← Zig.callM (Zig.ptrProject i5 (·.add 8))
    Zig.store (α := BitVec 64) 8 i6 (0 : BitVec 64)
    let i8 ← Zig.callM (Zig.ptrProject p0 (·.add 16))
    Zig.store (α := BitVec 64) 8 i8 (0 : BitVec 64)
    pure .ret) : Zig.MM array_list_Aligned_u32_null_clearAndFreeLocals array_list_Aligned_u32_null_clearAndFreeExit).run' (default : array_list_Aligned_u32_null_clearAndFreeLocals)
  match e with
  | .ret => pure ()

structure array_list_Aligned_u32_null_deinitLocals where
  deriving Inhabited

inductive array_list_Aligned_u32_null_deinitExit where
  | ret

-- air2lean-premises: {"ALC-09":[1]}
def array_list_Aligned_u32_null_deinit (p0 : Zig.Ptr) (p1 : Zig.Allocator) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← Zig.load (array_list_Aligned_u32_null) 8 p0
    let i3 ← Zig.callM (array_list_Aligned_u32_null_allocatedSlice i2)
    let _i4 ← Zig.callM (Zig.Allocator.free p1 4 i3)
    Zig.storeUndef (array_list_Aligned_u32_null) 8 p0
    pure .ret) : Zig.MM array_list_Aligned_u32_null_deinitLocals array_list_Aligned_u32_null_deinitExit).run' (default : array_list_Aligned_u32_null_deinitLocals)
  match e with
  | .ret => pure ()

structure array_list_Aligned_u32_null_toOwnedSliceLocals where
  deriving Inhabited

inductive array_list_Aligned_u32_null_toOwnedSliceExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br4
  | br29
  | br41

-- air2lean-premises: {"ALC-09":[1]}
def array_list_Aligned_u32_null_toOwnedSlice (p0 : Zig.Ptr) (p1 : Zig.Allocator) : Zig.MemM (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.load (array_list_Aligned_u32_null) 8 p0
    let i3 ← Zig.callM (array_list_Aligned_u32_null_allocatedSlice i2)
    match ← ((do
      let i5 ← pure p0
      let i6 ← Zig.load (Zig.Slice) 8 i5
      let i7 ← pure i6.len
      let i8 ← Zig.callM (Zig.Allocator.remap p1 4 i3 i7)
      let i9 ← pure ((i8).isSome)
      if i9 then (do
        let i11 ← Zig.optPayload i8
        Zig.store (α := array_list_Aligned_u32_null) 8 p0 ({ items := (⟨(⟨some 0, 0⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice), capacity := (0 : BitVec 64) } : array_list_Aligned_u32_null)
        let i13 ← pure ((.ok i11) : Except Zig.ErrName (Zig.Slice))
        pure (.ret i13))
      else (do
        pure .br4)) : Zig.MM array_list_Aligned_u32_null_toOwnedSliceLocals array_list_Aligned_u32_null_toOwnedSliceExit) with
    | .br4 => (do
      let i16 ← pure p0
      let i17 ← Zig.load (Zig.Slice) 8 i16
      let i18 ← pure i17.len
      let i19 ← Zig.callM (Zig.Allocator.alloc p1 4 4 i18)
      match i19 with
      | .error _ => (do
        let i21 ← Zig.callR (Zig.unwrapErr i19)
        let i22 ← pure ((.error i21) : Except Zig.ErrName (Zig.Slice))
        pure (.ret i22))
      | .ok v20 => (do
        let i24 ← pure p0
        let i25 ← Zig.load (Zig.Slice) 8 i24
        let i26 ← pure v20.len
        let i27 ← pure i25.len
        let i28 ← pure (i26 == i27)
        match ← ((do
          if i28 then (do
            pure .br29)
          else (do
            throw .panic)) : Zig.MM array_list_Aligned_u32_null_toOwnedSliceLocals array_list_Aligned_u32_null_toOwnedSliceExit) with
        | .br29 => (do
          let i34 ← pure i25.ptr
          let i35 ← pure v20.ptr
          let i36 ← Zig.callM (Zig.ptrProject i34 (·.elem 4 i26))
          let i37 ← Zig.callM (Zig.ptrProject i35 (·.elem 4 i26))
          let i38 ← Zig.callM (Zig.ptrLe i36 i35)
          let i39 ← Zig.callM (Zig.ptrLe i37 i34)
          let i40 ← pure (i38 || i39)
          match ← ((do
            if i40 then (do
              pure .br41)
            else (do
              throw .panic)) : Zig.MM array_list_Aligned_u32_null_toOwnedSliceLocals array_list_Aligned_u32_null_toOwnedSliceExit) with
          | .br41 => (do
            Zig.callM (Zig.memcpy 4 4 4 v20.ptr i34 v20.len i25.len)
            let _i47 ← Zig.callM (array_list_Aligned_u32_null_clearAndFree p0 p1)
            let i48 ← pure ((.ok v20) : Except Zig.ErrName (Zig.Slice))
            pure (.ret i48))
          | e => pure e)
        | e => pure e))
    | e => pure e) : Zig.MM array_list_Aligned_u32_null_toOwnedSliceLocals array_list_Aligned_u32_null_toOwnedSliceExit).run' (default : array_list_Aligned_u32_null_toOwnedSliceLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure dupeLocals where
  deriving Inhabited

inductive dupeExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))

-- air2lean-premises: {"ALC-09":[0]}
def dupe (p0 : Zig.Allocator) (p1 : Zig.Slice) : Zig.MemM (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.callM (Zig.Allocator.dupe p0 1 1 1 p1)
    let i3 ← pure (i2)
    pure (.ret i3)) : Zig.MM dupeLocals dupeExit).run' (default : dupeLocals)
  match e with
  | .ret v => pure v

structure mem_Allocator_dupeZ__anon_ad013b83a643Locals where
  deriving Inhabited

inductive mem_Allocator_dupeZ__anon_ad013b83a643Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br15
  | br24
  | br36
  | br45
  | br59
  | br67

-- air2lean-premises: {"ALC-09":[0]}
def mem_Allocator_dupeZ__anon_ad013b83a643 (p0 : Zig.Allocator) (p1 : Zig.Slice) : Zig.MemM (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← pure p1.len
    let i3 ← Zig.add false i2 (1 : BitVec 64)
    let i4 ← Zig.callM (Zig.Allocator.alloc p0 1 1 i3)
    match i4 with
    | .error _ => (do
      let i6 ← Zig.callR (Zig.unwrapErr i4)
      let i7 ← pure ((.error i6) : Except Zig.ErrName (Zig.Slice))
      pure (.ret i7))
    | .ok v5 => (do
      let i9 ← pure p1.len
      let i10 ← pure v5.ptr
      let i11 ← pure i10
      let i12 ← Zig.sub false i9 (0 : BitVec 64)
      let i13 ← pure v5.len
      let i14 ← pure (Zig.le false i9 i13)
      match ← ((do
        if i14 then (do
          pure .br15)
        else (do
          throw .outOfBounds)) : Zig.MM mem_Allocator_dupeZ__anon_ad013b83a643Locals mem_Allocator_dupeZ__anon_ad013b83a643Exit) with
      | .br15 => (do
        let i20 ← Zig.callM (Zig.checkSliceEnd v5.len (0 : BitVec 64) i12 0 >>= fun _ => pure (⟨i11, i12⟩ : Zig.Slice))
        let i21 ← pure i20.len
        let i22 ← pure p1.len
        let i23 ← pure (i21 == i22)
        match ← ((do
          if i23 then (do
            pure .br24)
          else (do
            throw .panic)) : Zig.MM mem_Allocator_dupeZ__anon_ad013b83a643Locals mem_Allocator_dupeZ__anon_ad013b83a643Exit) with
        | .br24 => (do
          let i29 ← pure p1.ptr
          let i30 ← pure i20.ptr
          let i31 ← Zig.callM (Zig.ptrProject i29 (·.elem 1 i21))
          let i32 ← Zig.callM (Zig.ptrProject i30 (·.elem 1 i21))
          let i33 ← Zig.callM (Zig.ptrLe i31 i30)
          let i34 ← Zig.callM (Zig.ptrLe i32 i29)
          let i35 ← pure (i33 || i34)
          match ← ((do
            if i35 then (do
              pure .br36)
            else (do
              throw .panic)) : Zig.MM mem_Allocator_dupeZ__anon_ad013b83a643Locals mem_Allocator_dupeZ__anon_ad013b83a643Exit) with
          | .br36 => (do
            Zig.callM (Zig.memcpy 1 1 1 i20.ptr i29 i20.len p1.len)
            let i42 ← pure p1.len
            let i43 ← pure v5.len
            let i44 ← pure (Zig.lt false i42 i43)
            match ← ((do
              if i44 then (do
                pure .br45)
              else (do
                throw .outOfBounds)) : Zig.MM mem_Allocator_dupeZ__anon_ad013b83a643Locals mem_Allocator_dupeZ__anon_ad013b83a643Exit) with
            | .br45 => (do
              let i50 ← Zig.callM (Zig.ptrProject v5.ptr (·.elem 1 i42))
              Zig.store (α := BitVec 8) 1 i50 (0 : BitVec 8)
              let i52 ← pure p1.len
              let i53 ← pure v5.ptr
              let i54 ← pure i53
              let i55 ← Zig.sub false i52 (0 : BitVec 64)
              let i56 ← pure v5.len
              let i57 ← Zig.add false i52 (1 : BitVec 64)
              let i58 ← pure (Zig.le false i57 i56)
              match ← ((do
                if i58 then (do
                  pure .br59)
                else (do
                  throw .outOfBounds)) : Zig.MM mem_Allocator_dupeZ__anon_ad013b83a643Locals mem_Allocator_dupeZ__anon_ad013b83a643Exit) with
              | .br59 => (do
                let i64 ← Zig.callM (Zig.checkSliceEnd v5.len (0 : BitVec 64) i55 1 >>= fun _ => pure (⟨i54, i55⟩ : Zig.Slice))
                let i65 ← Zig.callM (Zig.checkSentinelIndex i64 i55 >>= fun _ => Zig.load (BitVec 8) 1 (i64.ptr.elem 1 i55))
                let i66 ← pure ((0 : BitVec 8) == i65)
                match ← ((do
                  if i66 then (do
                    pure .br67)
                  else (do
                    throw .panic)) : Zig.MM mem_Allocator_dupeZ__anon_ad013b83a643Locals mem_Allocator_dupeZ__anon_ad013b83a643Exit) with
                | .br67 => (do
                  let i72 ← pure ((.ok i64) : Except Zig.ErrName (Zig.Slice))
                  pure (.ret i72))
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)) : Zig.MM mem_Allocator_dupeZ__anon_ad013b83a643Locals mem_Allocator_dupeZ__anon_ad013b83a643Exit).run' (default : mem_Allocator_dupeZ__anon_ad013b83a643Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure dupeZLenLocals where
  n : BitVec 64
  deriving Inhabited

inductive dupeZLenExit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br16
  | br12
  | br10
  | rep11

def dupeZLen.again11 : dupeZLenExit → Bool
  | .rep11 => true
  | _ => false

def dupeZLen.loop11 (i3 : Zig.Slice) : Zig.MM dupeZLenLocals dupeZLenExit := do
  match ← ((do
    let i13 ← pure ((← get).n)
    let i14 ← pure i3.len
    let i15 ← pure (Zig.le false i13 i14)
    match ← ((do
      if i15 then (do
        pure .br16)
      else (do
        throw .outOfBounds)) : Zig.MM dupeZLenLocals dupeZLenExit) with
    | .br16 => (do
      let i21 ← Zig.callM (Zig.checkSentinelIndex i3 i13 >>= fun _ => Zig.load (BitVec 8) 1 (i3.ptr.elem 1 i13))
      let i22 ← pure (i21 != (0 : BitVec 8))
      if i22 then (do
        let i24 ← pure ((← get).n)
        let i25 ← Zig.add false i24 (1 : BitVec 64)
        modify (fun s => { s with n := i25 })
        pure .br12)
      else (do
        pure .br10))
    | e => pure e) : Zig.MM dupeZLenLocals dupeZLenExit) with
  | .br12 => (do
    pure .rep11)
  | e => pure e

-- air2lean-premises: {"ALC-09":[0]}
def dupeZLen (p0 : Zig.Allocator) (p1 : Zig.Slice) : Zig.MemM (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← Zig.callM (mem_Allocator_dupeZ__anon_ad013b83a643 p0 p1)
    match i2 with
    | .error _ => (do
      let i4 ← Zig.callR (Zig.unwrapErr i2)
      let i5 ← pure (i4)
      let i6 ← pure ((.error i5) : Except Zig.ErrName (BitVec 64))
      pure (.ret i6))
    | .ok v3 => (do
      modify (fun s => { s with n := (0 : BitVec 64) })
      match ← ((do
        Zig.loop (dupeZLen.loop11 v3) dupeZLen.again11) : Zig.MM dupeZLenLocals dupeZLenExit) with
      | .br10 => (do
        let i30 ← pure ((← get).n)
        let _i31 ← Zig.callM (Zig.Allocator.freeSentinel p0 1 v3)
        let i32 ← pure ((.ok i30) : Except Zig.ErrName (BitVec 64))
        pure (.ret i32))
      | e => pure e)) : Zig.MM dupeZLenLocals dupeZLenExit).run' (default : dupeZLenLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure evensLocals where
  list : Zig.Ptr
  local4 : BitVec 64
  deriving Inhabited

inductive evensExit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br16
  | br10
  | br7
  | rep8

def evens.again8 : evensExit → Bool
  | .rep8 => true
  | _ => false

def evens.loop8 (p0 : Zig.Allocator) (p1 : Zig.Slice) (i2 : Zig.Ptr) (i6 : BitVec 64) : Zig.MM evensLocals evensExit := do
  let i9 ← pure ((← get).local4)
  match ← ((do
    let i11 ← pure (i9)
    let i12 ← pure (i6)
    let i13 ← pure (Zig.lt false i11 i12)
    if i13 then (do
      let i15 ← Zig.callM (Zig.checkIndex p1 i9 >>= fun _ => Zig.load (BitVec 32) 4 (p1.ptr.elem 4 i9))
      match ← ((do
        let i17 ← Zig.rem false i15 (2 : BitVec 32)
        let i18 ← pure (i17 == (0 : BitVec 32))
        if i18 then (do
          let i20 ← Zig.callM (array_list_Aligned_u32_null_append i2 p0 i15)
          match i20 with
          | .error _ => (do
            let i22 ← Zig.callR (Zig.unwrapErr i20)
            let _i23 ← Zig.callM (array_list_Aligned_u32_null_deinit i2 p0)
            let i24 ← pure (i22)
            let i25 ← pure ((.error i24) : Except Zig.ErrName (Zig.Slice))
            pure (.ret i25))
          | .ok _v21 => (do
            pure .br16))
        else (do
          pure .br16)) : Zig.MM evensLocals evensExit) with
      | .br16 => (do
        pure .br10)
      | e => pure e)
    else (do
      pure .br7)) : Zig.MM evensLocals evensExit) with
  | .br10 => (do
    let i31 ← Zig.add false i9 (1 : BitVec 64)
    modify (fun s => { s with local4 := i31 })
    pure .rep8)
  | e => pure e

-- air2lean-premises: {"ALC-09":[0]}
def evens (p0 : Zig.Allocator) (p1 : Zig.Slice) : Zig.MemM (Except Zig.ErrName (Zig.Slice)) := do
  let s2 ← Zig.allocStack 24 8
  let e ← ((do
    let i2 ← pure (← get).list
    Zig.store (α := array_list_Aligned_u32_null) 8 i2 ({ items := (⟨(⟨some 0, 0⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice), capacity := (0 : BitVec 64) } : array_list_Aligned_u32_null)
    modify (fun s => { s with local4 := (0 : BitVec 64) })
    let i6 ← pure p1.len
    match ← ((do
      Zig.loop (evens.loop8 p0 p1 i2 i6) evens.again8) : Zig.MM evensLocals evensExit) with
    | .br7 => (do
      let i34 ← Zig.callM (array_list_Aligned_u32_null_toOwnedSlice i2 p0)
      let i35 ← pure (Zig.isNonErr i34)
      if i35 then (do
        let i37 ← pure (i34)
        pure (.ret i37))
      else (do
        let _i39 ← Zig.callM (array_list_Aligned_u32_null_deinit i2 p0)
        let i40 ← pure (i34)
        pure (.ret i40)))
    | e => pure e) : Zig.MM evensLocals evensExit).run' { (default : evensLocals) with list := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure freeAllLocals where
  p : Option (Zig.Ptr)
  deriving Inhabited

inductive freeAllExit where
  | ret
  | br6
  | br4
  | rep5

def freeAll.again5 : freeAllExit → Bool
  | .rep5 => true
  | _ => false

def freeAll.loop5 (p0 : Zig.Allocator) : Zig.MM freeAllLocals freeAllExit := do
  match ← ((do
    let i7 ← pure ((← get).p)
    let i8 ← pure ((i7).isSome)
    if i8 then (do
      let i10 ← Zig.optPayload i7
      let i11 ← pure i10
      let i12 ← Zig.load (Option (Zig.Ptr)) 8 i11
      modify (fun s => { s with p := i12 })
      let _i14 ← Zig.callM (Zig.Allocator.destroy p0 16 i10)
      pure .br6)
    else (do
      pure .br4)) : Zig.MM freeAllLocals freeAllExit) with
  | .br6 => (do
    pure .rep5)
  | e => pure e

-- air2lean-premises: {"ALC-09":[0]}
def freeAll (p0 : Zig.Allocator) (p1 : Option (Zig.Ptr)) : Zig.MemM (Unit) := do
  let e ← ((do
    modify (fun s => { s with p := p1 })
    match ← ((do
      Zig.loop (freeAll.loop5 p0) freeAll.again5) : Zig.MM freeAllLocals freeAllExit) with
    | .br4 => (do
      pure .ret)
    | e => pure e) : Zig.MM freeAllLocals freeAllExit).run' (default : freeAllLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure pushLocals where
  deriving Inhabited

inductive pushExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

-- air2lean-premises: {"ALC-09":[0]}
def push (p0 : Zig.Allocator) (p1 : Option (Zig.Ptr)) (p2 : BitVec 32) : Zig.MemM (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    let i3 ← Zig.callM (Zig.Allocator.create p0 16 8)
    match i3 with
    | .error _ => (do
      let i5 ← Zig.callR (Zig.unwrapErr i3)
      let i6 ← pure (i5)
      let i7 ← pure ((.error i6) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i7))
    | .ok v4 => (do
      let i9 ← Zig.callM (Zig.ptrProject v4 (·.add 8))
      Zig.store (α := BitVec 32) 4 i9 p2
      let i11 ← pure v4
      Zig.store (α := Option (Zig.Ptr)) 8 i11 p1
      let i13 ← pure ((.ok v4) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i13))) : Zig.MM pushLocals pushExit).run' (default : pushLocals)
  match e with
  | .ret v => pure v

structure reverseLocals where
  prev : Option (Zig.Ptr)
  cur : Option (Zig.Ptr)
  deriving Inhabited

inductive reverseExit where
  | ret (v : Option (Zig.Ptr))
  | br7
  | br5
  | rep6

def reverse.again6 : reverseExit → Bool
  | .rep6 => true
  | _ => false

def reverse.loop6  : Zig.MM reverseLocals reverseExit := do
  match ← ((do
    let i8 ← pure ((← get).cur)
    let i9 ← pure ((i8).isSome)
    if i9 then (do
      let i11 ← Zig.optPayload i8
      let i12 ← pure i11
      let i13 ← Zig.load (Option (Zig.Ptr)) 8 i12
      modify (fun s => { s with cur := i13 })
      let i15 ← pure i11
      let i16 ← pure ((← get).prev)
      Zig.store (α := Option (Zig.Ptr)) 8 i15 i16
      let i18 ← pure (i11)
      modify (fun s => { s with prev := i18 })
      pure .br7)
    else (do
      pure .br5)) : Zig.MM reverseLocals reverseExit) with
  | .br7 => (do
    pure .rep6)
  | e => pure e

def reverse (p0 : Option (Zig.Ptr)) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    modify (fun s => { s with prev := none })
    modify (fun s => { s with cur := p0 })
    match ← ((do
      Zig.loop (reverse.loop6 ) reverse.again6) : Zig.MM reverseLocals reverseExit) with
    | .br5 => (do
      let i23 ← pure ((← get).prev)
      pure (.ret i23))
    | e => pure e) : Zig.MM reverseLocals reverseExit).run' (default : reverseLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure sumLocals where
  s : BitVec 64
  p : Option (Zig.Ptr)
  deriving Inhabited

inductive sumExit where
  | ret (v : BitVec 64)
  | br7
  | br5
  | rep6

def sum.again6 : sumExit → Bool
  | .rep6 => true
  | _ => false

def sum.loop6  : Zig.MM sumLocals sumExit := do
  match ← ((do
    let i8 ← pure ((← get).p)
    let i9 ← pure ((i8).isSome)
    if i9 then (do
      let i11 ← Zig.optPayload i8
      let i12 ← pure ((← get).s)
      let i13 ← Zig.callM (Zig.ptrProject i11 (·.add 8))
      let i14 ← Zig.load (BitVec 32) 4 i13
      let i15 ← Zig.intCast false false 64 i14
      let i16 ← Zig.add false i12 i15
      modify (fun s => { s with s := i16 })
      let i18 ← pure i11
      let i19 ← Zig.load (Option (Zig.Ptr)) 8 i18
      let i20 ← pure (i19)
      modify (fun s => { s with p := i20 })
      pure .br7)
    else (do
      pure .br5)) : Zig.MM sumLocals sumExit) with
  | .br7 => (do
    pure .rep6)
  | e => pure e

def sum (p0 : Option (Zig.Ptr)) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with s := (0 : BitVec 64) })
    modify (fun s => { s with p := p0 })
    match ← ((do
      Zig.loop (sum.loop6 ) sum.again6) : Zig.MM sumLocals sumExit) with
    | .br5 => (do
      let i25 ← pure ((← get).s)
      pure (.ret i25))
    | e => pure e) : Zig.MM sumLocals sumExit).run' (default : sumLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure listSumLocals where
  head : Option (Zig.Ptr)
  local4 : BitVec 64
  deriving Inhabited

inductive listSumExit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br10
  | br7
  | br35 (v : BitVec 64)
  | rep8

def listSum.again8 : listSumExit → Bool
  | .rep8 => true
  | _ => false

def listSum.loop8 (p0 : Zig.Allocator) (p1 : Zig.Slice) (i6 : BitVec 64) : Zig.MM listSumLocals listSumExit := do
  let i9 ← pure ((← get).local4)
  match ← ((do
    let i11 ← pure (i9)
    let i12 ← pure (i6)
    let i13 ← pure (Zig.lt false i11 i12)
    if i13 then (do
      let i15 ← Zig.callM (Zig.checkIndex p1 i9 >>= fun _ => Zig.load (BitVec 32) 4 (p1.ptr.elem 4 i9))
      let i16 ← pure ((← get).head)
      let i17 ← Zig.callM (push p0 i16 i15)
      match i17 with
      | .error _ => (do
        let i19 ← Zig.callR (Zig.unwrapErr i17)
        let i20 ← pure ((← get).head)
        let _i21 ← Zig.callM (freeAll p0 i20)
        let i22 ← pure (i19)
        let i23 ← pure ((.error i22) : Except Zig.ErrName (BitVec 64))
        pure (.ret i23))
      | .ok v18 => (do
        let i25 ← pure (v18)
        modify (fun s => { s with head := i25 })
        pure .br10))
    else (do
      pure .br7)) : Zig.MM listSumLocals listSumExit) with
  | .br10 => (do
    let i29 ← Zig.add false i9 (1 : BitVec 64)
    modify (fun s => { s with local4 := i29 })
    pure .rep8)
  | e => pure e

-- air2lean-premises: {"ALC-09":[0]}
def listSum (p0 : Zig.Allocator) (p1 : Zig.Slice) : Zig.MemM (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    modify (fun s => { s with head := none })
    modify (fun s => { s with local4 := (0 : BitVec 64) })
    let i6 ← pure p1.len
    match ← ((do
      Zig.loop (listSum.loop8 p0 p1 i6) listSum.again8) : Zig.MM listSumLocals listSumExit) with
    | .br7 => (do
      let i32 ← pure ((← get).head)
      let i33 ← Zig.callM (reverse i32)
      modify (fun s => { s with head := i33 })
      match ← ((do
        let i36 ← pure ((← get).head)
        let i37 ← pure ((i36).isSome)
        if i37 then (do
          let i39 ← Zig.optPayload i36
          let i40 ← Zig.callM (Zig.ptrProject i39 (·.add 8))
          let i41 ← Zig.load (BitVec 32) 4 i40
          let i42 ← Zig.intCast false false 64 i41
          pure (.br35 i42))
        else (do
          pure (.br35 (0 : BitVec 64)))) : Zig.MM listSumLocals listSumExit) with
      | .br35 v35 => (do
        let i45 ← pure (Zig.shl v35 (32 : BitVec 6))
        let i46 ← pure ((← get).head)
        let i47 ← pure (i46)
        let i48 ← Zig.callM (sum i47)
        let i49 ← Zig.add false i45 i48
        let i50 ← pure ((← get).head)
        let _i51 ← Zig.callM (freeAll p0 i50)
        let i52 ← pure ((.ok i49) : Except Zig.ErrName (BitVec 64))
        pure (.ret i52))
      | e => pure e)
    | e => pure e) : Zig.MM listSumLocals listSumExit).run' (default : listSumLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure sumRangeLocals where
  local8 : BitVec 64
  s : BitVec 64
  local29 : BitVec 64
  deriving Inhabited

inductive sumRangeExit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br14
  | br11
  | br35
  | br32
  | rep12
  | rep33

def sumRange.again33 : sumRangeExit → Bool
  | .rep33 => true
  | _ => false

def sumRange.again12 : sumRangeExit → Bool
  | .rep12 => true
  | _ => false

def sumRange.loop33 (i3 : Zig.Slice) (i31 : BitVec 64) : Zig.MM sumRangeLocals sumRangeExit := do
  let i34 ← pure ((← get).local29)
  match ← ((do
    let i36 ← pure (i34)
    let i37 ← pure (i31)
    let i38 ← pure (Zig.lt false i36 i37)
    if i38 then (do
      let i40 ← Zig.callM (Zig.checkIndex i3 i34 >>= fun _ => Zig.load (BitVec 32) 4 (i3.ptr.elem 4 i34))
      let i41 ← pure ((← get).s)
      let i42 ← Zig.intCast false false 64 i40
      let i43 ← Zig.add false i41 i42
      modify (fun s => { s with s := i43 })
      pure .br35)
    else (do
      pure .br32)) : Zig.MM sumRangeLocals sumRangeExit) with
  | .br35 => (do
    let i47 ← Zig.add false i34 (1 : BitVec 64)
    modify (fun s => { s with local29 := i47 })
    pure .rep33)
  | e => pure e

def sumRange.loop12 (i3 : Zig.Slice) (i10 : BitVec 64) : Zig.MM sumRangeLocals sumRangeExit := do
  let i13 ← pure ((← get).local8)
  match ← ((do
    let i15 ← pure (i13)
    let i16 ← pure (i10)
    let i17 ← pure (Zig.lt false i15 i16)
    if i17 then (do
      let i19 ← Zig.callM (Zig.ptrProject i3.ptr (·.elem 4 i13))
      let i20 ← pure (Zig.trunc 32 i13)
      Zig.store (α := BitVec 32) 4 i19 i20
      pure .br14)
    else (do
      pure .br11)) : Zig.MM sumRangeLocals sumRangeExit) with
  | .br14 => (do
    let i24 ← Zig.add false i13 (1 : BitVec 64)
    modify (fun s => { s with local8 := i24 })
    pure .rep12)
  | e => pure e

-- air2lean-premises: {"ALC-09":[0]}
def sumRange (p0 : Zig.Allocator) (p1 : BitVec 64) : Zig.MemM (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← Zig.callM (Zig.Allocator.alloc p0 4 4 p1)
    match i2 with
    | .error _ => (do
      let i4 ← Zig.callR (Zig.unwrapErr i2)
      let i5 ← pure (i4)
      let i6 ← pure ((.error i5) : Except Zig.ErrName (BitVec 64))
      pure (.ret i6))
    | .ok v3 => (do
      modify (fun s => { s with local8 := (0 : BitVec 64) })
      let i10 ← pure v3.len
      match ← ((do
        Zig.loop (sumRange.loop12 v3 i10) sumRange.again12) : Zig.MM sumRangeLocals sumRangeExit) with
      | .br11 => (do
        modify (fun s => { s with s := (0 : BitVec 64) })
        modify (fun s => { s with local29 := (0 : BitVec 64) })
        let i31 ← pure v3.len
        match ← ((do
          Zig.loop (sumRange.loop33 v3 i31) sumRange.again33) : Zig.MM sumRangeLocals sumRangeExit) with
        | .br32 => (do
          let i50 ← pure ((← get).s)
          let _i51 ← Zig.callM (Zig.Allocator.free p0 4 v3)
          let i52 ← pure ((.ok i50) : Except Zig.ErrName (BitVec 64))
          pure (.ret i52))
        | e => pure e)
      | e => pure e)) : Zig.MM sumRangeLocals sumRangeExit).run' (default : sumRangeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end Lists