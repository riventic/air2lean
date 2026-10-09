-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"none","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"apple_m1","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["aes","aggressive_fma","alternate_sextload_cvt_f32_pattern","altnzcv","am","arith_bcc_fusion","arith_cbz_fusion","ccdp","ccidx","ccpp","complxnum","contextidr_el2","crc","disable_latency_sched_heuristic","dit","dotprod","el2vmsa","el3","flagm","fp16fml","fp_armv8","fptoint","fullfp16","fuse_address","fuse_aes","fuse_arith_logic","fuse_crypto_eor","fuse_csel","fuse_literals","jsconv","lor","lse","lse2","mpam","neon","nv","pan","pan_rwv","pauth","perfmon","predres","ras","rcpc","rcpc_immo","rdm","sb","sel2","sha2","sha3","specrestrict","ssbs","store_pair_suppress","tlb_rmi","tracev8_4","uaops","v8_1a","v8_2a","v8_3a","v8_4a","v8a","vh","zcm_fpr64","zcm_gpr64","zcz","zcz_gp"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"aarch64-macos.13.0...15.6-none","zig_version":"0.16.0"}}
import ZigLean


namespace AllocTranslated.PageMacos

structure mem_Allocator_VTable where
  alloc : Zig.Ptr
  resize : Zig.Ptr
  remap : Zig.Ptr
  free : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc mem_Allocator_VTable where
  size := 32
  align := 8
  encode v := Zig.Enc.fields 32 [(0, Zig.Enc.encode v.alloc), (8, Zig.Enc.encode v.resize), (16, Zig.Enc.encode v.remap), (24, Zig.Enc.encode v.free)]
  decode bs := do pure { alloc := ← Zig.Enc.decodeAt bs 0, resize := ← Zig.Enc.decodeAt bs 8, remap := ← Zig.Enc.decodeAt bs 16, free := ← Zig.Enc.decodeAt bs 24 }

structure mem_Allocator where
  ptr : Zig.Ptr
  vtable : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc mem_Allocator where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.ptr), (8, Zig.Enc.encode v.vtable)]
  decode bs := do pure { ptr := ← Zig.Enc.decodeAt bs 0, vtable := ← Zig.Enc.decodeAt bs 8 }

structure mem_Alignment where
  bits : BitVec 6
  deriving Repr, Inhabited, DecidableEq

def mem_Alignment.«1» : mem_Alignment := ⟨(0 : BitVec 6)⟩
def mem_Alignment.«2» : mem_Alignment := ⟨(1 : BitVec 6)⟩
def mem_Alignment.«4» : mem_Alignment := ⟨(2 : BitVec 6)⟩
def mem_Alignment.«8» : mem_Alignment := ⟨(3 : BitVec 6)⟩
def mem_Alignment.«16» : mem_Alignment := ⟨(4 : BitVec 6)⟩
def mem_Alignment.«32» : mem_Alignment := ⟨(5 : BitVec 6)⟩
def mem_Alignment.«64» : mem_Alignment := ⟨(6 : BitVec 6)⟩

def mem_Alignment.toBits (e : mem_Alignment) : BitVec 6 := e.bits

def mem_Alignment.ofInt? (v : Int) : Option mem_Alignment :=
  if 0 ≤ v ∧ v ≤ 63 then Option.some ⟨BitVec.ofInt 6 v⟩ else Option.none

def mem_Alignment.isNamed (e : mem_Alignment) : Bool := e.bits == (0 : BitVec 6) || e.bits == (1 : BitVec 6) || e.bits == (2 : BitVec 6) || e.bits == (3 : BitVec 6) || e.bits == (4 : BitVec 6) || e.bits == (5 : BitVec 6) || e.bits == (6 : BitVec 6)

instance : Zig.Packed mem_Alignment 6 where
  toBits := mem_Alignment.toBits
  ofBits b := ⟨b⟩

instance : Zig.Enc mem_Alignment where
  size := 1
  align := 1
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 6 ← Zig.Enc.decode bs
    pure ⟨b⟩

structure macho_vm_prot_t where
  READ : Bool
  WRITE : Bool
  EXEC : Bool
  «_» : BitVec 1
  COPY : Bool
  __ : BitVec 27
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed macho_vm_prot_t 32 where
  toBits v := ((Zig.Packed.toBits v.READ).setWidth 32 <<< 0) ||| ((Zig.Packed.toBits v.WRITE).setWidth 32 <<< 1) ||| ((Zig.Packed.toBits v.EXEC).setWidth 32 <<< 2) ||| ((Zig.Packed.toBits v.«_»).setWidth 32 <<< 3) ||| ((Zig.Packed.toBits v.COPY).setWidth 32 <<< 4) ||| ((Zig.Packed.toBits v.__).setWidth 32 <<< 5)
  ofBits b := { READ := Zig.Packed.get b 0, WRITE := Zig.Packed.get b 1, EXEC := Zig.Packed.get b 2, «_» := Zig.Packed.get b 3, COPY := Zig.Packed.get b 4, __ := Zig.Packed.get b 5 }

inductive c_MAP__struct_1__enum_1 where
  | SHARED
  | PRIVATE
  deriving Repr, Inhabited, DecidableEq

def c_MAP__struct_1__enum_1.toBits : c_MAP__struct_1__enum_1 → BitVec 4
  | .SHARED => (1 : BitVec 4)
  | .PRIVATE => (2 : BitVec 4)

def c_MAP__struct_1__enum_1.ofInt? (v : Int) : Option c_MAP__struct_1__enum_1 :=
  if v = 1 then Option.some .SHARED else if v = 2 then Option.some .PRIVATE else Option.none

def c_MAP__struct_1__enum_1.isNamed (_ : c_MAP__struct_1__enum_1) : Bool := true

instance : Zig.Packed c_MAP__struct_1__enum_1 4 where
  toBits := c_MAP__struct_1__enum_1.toBits
  ofBits b := (c_MAP__struct_1__enum_1.ofInt? (Zig.val false b)).getD default
  valid b := (c_MAP__struct_1__enum_1.ofInt? (Zig.val false b)).isSome

structure c_MAP__struct_1 where
  TYPE : c_MAP__struct_1__enum_1
  FIXED : Bool
  _5 : BitVec 1
  NORESERVE : Bool
  _7 : BitVec 2
  HASSEMAPHORE : Bool
  NOCACHE : Bool
  JIT : Bool
  ANONYMOUS : Bool
  «_» : BitVec 19
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed c_MAP__struct_1 32 where
  toBits v := ((Zig.Packed.toBits v.TYPE).setWidth 32 <<< 0) ||| ((Zig.Packed.toBits v.FIXED).setWidth 32 <<< 4) ||| ((Zig.Packed.toBits v._5).setWidth 32 <<< 5) ||| ((Zig.Packed.toBits v.NORESERVE).setWidth 32 <<< 6) ||| ((Zig.Packed.toBits v._7).setWidth 32 <<< 7) ||| ((Zig.Packed.toBits v.HASSEMAPHORE).setWidth 32 <<< 9) ||| ((Zig.Packed.toBits v.NOCACHE).setWidth 32 <<< 10) ||| ((Zig.Packed.toBits v.JIT).setWidth 32 <<< 11) ||| ((Zig.Packed.toBits v.ANONYMOUS).setWidth 32 <<< 12) ||| ((Zig.Packed.toBits v.«_»).setWidth 32 <<< 13)
  ofBits b := { TYPE := Zig.Packed.get b 0, FIXED := Zig.Packed.get b 4, _5 := Zig.Packed.get b 5, NORESERVE := Zig.Packed.get b 6, _7 := Zig.Packed.get b 7, HASSEMAPHORE := Zig.Packed.get b 9, NOCACHE := Zig.Packed.get b 10, JIT := Zig.Packed.get b 11, ANONYMOUS := Zig.Packed.get b 12, «_» := Zig.Packed.get b 13 }
  valid b := Zig.Packed.validAt (c_MAP__struct_1__enum_1) b 0

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals [
  -- 0: heap.PageAllocator.addr_hint
  (Zig.Enc.encode (none : Option (Zig.Ptr)), 8, .global),
  -- 1: heap.PageAllocator.vtable
  (Zig.Enc.encode (({ alloc := (⟨some 2, 0⟩ : Zig.Ptr), resize := (⟨some 3, 0⟩ : Zig.Ptr), remap := (⟨some 4, 0⟩ : Zig.Ptr), free := (⟨some 5, 0⟩ : Zig.Ptr) } : mem_Allocator_VTable) : mem_Allocator_VTable), 8, .constGlobal),
  -- 2: heap.PageAllocator.alloc
  (#[.undef], 1, .constGlobal),
  -- 3: heap.PageAllocator.resize
  (#[.undef], 1, .constGlobal),
  -- 4: heap.PageAllocator.remap
  (#[.undef], 1, .constGlobal),
  -- 5: heap.PageAllocator.free
  (#[.undef], 1, .constGlobal)]

/-- The spawn targets of the program. -/
inductive Tgt where

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

structure mem_Alignment_toByteUnitsLocals where
  deriving Inhabited

inductive mem_Alignment_toByteUnitsExit where
  | ret (v : BitVec 64)

def mem_Alignment_toByteUnits (p0 : mem_Alignment) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← pure (mem_Alignment.toBits p0)
    let i2 ← pure (Zig.shl (1 : BitVec 64) i1)
    pure (.ret i2)) : Zig.M mem_Alignment_toByteUnitsLocals mem_Alignment_toByteUnitsExit).run' (default : mem_Alignment_toByteUnitsLocals)
  match e with
  | .ret v => pure v

structure math_isPowerOfTwo__anon_1Locals where
  deriving Inhabited

inductive math_isPowerOfTwo__anon_1Exit where
  | ret (v : Bool)

def math_isPowerOfTwo__anon_1 (p0 : BitVec 64) : Zig.Result (Bool) := do
  let e ← ((do
    let i1 ← pure (p0)
    let i2 ← pure (Zig.gt false i1 (0 : BitVec 64))
    let _i3 ← Zig.call (debug_assert i2)
    let i4 ← Zig.sub false p0 (1 : BitVec 64)
    let i5 ← pure (p0 &&& i4)
    let i6 ← pure (i5)
    let i7 ← pure (i6 == (0 : BitVec 64))
    pure (.ret i7)) : Zig.M math_isPowerOfTwo__anon_1Locals math_isPowerOfTwo__anon_1Exit).run' (default : math_isPowerOfTwo__anon_1Locals)
  match e with
  | .ret v => pure v

structure mem_isValidAlignGeneric__anon_1Locals where
  deriving Inhabited

inductive mem_isValidAlignGeneric__anon_1Exit where
  | ret (v : Bool)
  | br3 (v : Bool)

def mem_isValidAlignGeneric__anon_1 (p0 : BitVec 64) : Zig.Result (Bool) := do
  let e ← ((do
    let i1 ← pure (p0)
    let i2 ← pure (Zig.gt false i1 (0 : BitVec 64))
    match ← ((do
      if i2 then (do
        let i5 ← Zig.call (math_isPowerOfTwo__anon_1 p0)
        pure (.br3 i5))
      else (do
        pure (.br3 false))) : Zig.M mem_isValidAlignGeneric__anon_1Locals mem_isValidAlignGeneric__anon_1Exit) with
    | .br3 v3 => (do
      pure (.ret v3))
    | e => pure e) : Zig.M mem_isValidAlignGeneric__anon_1Locals mem_isValidAlignGeneric__anon_1Exit).run' (default : mem_isValidAlignGeneric__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_alignBackward__anon_1Locals where
  deriving Inhabited

inductive mem_alignBackward__anon_1Exit where
  | ret (v : BitVec 64)

def mem_alignBackward__anon_1 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← Zig.call (mem_isValidAlignGeneric__anon_1 p1)
    let _i3 ← Zig.call (debug_assert i2)
    let i4 ← Zig.sub false p1 (1 : BitVec 64)
    let i5 ← pure (~~~i4)
    let i6 ← pure (p0 &&& i5)
    pure (.ret i6)) : Zig.M mem_alignBackward__anon_1Locals mem_alignBackward__anon_1Exit).run' (default : mem_alignBackward__anon_1Locals)
  match e with
  | .ret v => pure v

structure mem_alignForward__anon_1Locals where
  deriving Inhabited

inductive mem_alignForward__anon_1Exit where
  | ret (v : BitVec 64)

def mem_alignForward__anon_1 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← Zig.call (mem_isValidAlignGeneric__anon_1 p1)
    let _i3 ← Zig.call (debug_assert i2)
    let i4 ← Zig.sub false p1 (1 : BitVec 64)
    let i5 ← Zig.add false p0 i4
    let i6 ← Zig.call (mem_alignBackward__anon_1 i5 p1)
    pure (.ret i6)) : Zig.M mem_alignForward__anon_1Locals mem_alignForward__anon_1Exit).run' (default : mem_alignForward__anon_1Locals)
  match e with
  | .ret v => pure v

structure mem_isValidAlignLocals where
  deriving Inhabited

inductive mem_isValidAlignExit where
  | ret (v : Bool)

def mem_isValidAlign (p0 : BitVec 64) : Zig.Result (Bool) := do
  let e ← ((do
    let i1 ← Zig.call (mem_isValidAlignGeneric__anon_1 p0)
    pure (.ret i1)) : Zig.M mem_isValidAlignLocals mem_isValidAlignExit).run' (default : mem_isValidAlignLocals)
  match e with
  | .ret v => pure v

structure mem_alignPointerOffset__anon_1Locals where
  ov : BitVec 64 × BitVec 1
  deriving Inhabited

inductive mem_alignPointerOffset__anon_1Exit where
  | ret (v : Option (BitVec 64))
  | br4
  | br15
  | br31

def mem_alignPointerOffset__anon_1 (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (Option (BitVec 64)) := do
  let e ← ((do
    let i2 ← Zig.callR (mem_isValidAlign p1)
    let _i3 ← Zig.callR (debug_assert i2)
    match ← ((do
      let i5 ← pure (p1)
      let i6 ← pure (Zig.le false i5 (16384 : BitVec 64))
      if i6 then (do
        pure (.ret (some (0 : BitVec 64))))
      else (do
        pure .br4)) : Zig.MM mem_alignPointerOffset__anon_1Locals mem_alignPointerOffset__anon_1Exit) with
    | .br4 => (do
      let i10 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr p0)))
      let i12 ← Zig.sub false p1 (1 : BitVec 64)
      let i13 ← pure (Zig.addWithOverflow false i10 i12)
      modify (fun s => { s with ov := i13 })
      match ← ((do
        let i17 ← pure (((← get).ov).snd)
        let i18 ← pure (i17 != (0 : BitVec 1))
        if i18 then (do
          pure (.ret none))
        else (do
          pure .br15)) : Zig.MM mem_alignPointerOffset__anon_1Locals mem_alignPointerOffset__anon_1Exit) with
      | .br15 => (do
        let i23 ← pure (((← get).ov).fst)
        let i24 ← Zig.sub false p1 (1 : BitVec 64)
        let i25 ← pure (~~~i24)
        let i26 ← pure (i23 &&& i25)
        modify (fun s => { s with ov := { s.ov with fst := i26 } })
        let i29 ← pure (((← get).ov).fst)
        let i30 ← Zig.sub false i29 i10
        match ← ((do
          let i32 ← Zig.rem false i30 (1 : BitVec 64)
          let i33 ← pure (i32)
          let i34 ← pure (i33 != (0 : BitVec 64))
          if i34 then (do
            pure (.ret none))
          else (do
            pure .br31)) : Zig.MM mem_alignPointerOffset__anon_1Locals mem_alignPointerOffset__anon_1Exit) with
        | .br31 => (do
          let i38 ← Zig.divTrunc false i30 (1 : BitVec 64)
          let i39 ← pure (some i38)
          pure (.ret i39))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM mem_alignPointerOffset__anon_1Locals mem_alignPointerOffset__anon_1Exit).run' (default : mem_alignPointerOffset__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_alignPointer__anon_1Locals where
  deriving Inhabited

inductive mem_alignPointer__anon_1Exit where
  | ret (v : Option (Zig.Ptr))
  | br2 (v : BitVec 64)
  | br13

def mem_alignPointer__anon_1 (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i3 ← Zig.callM (mem_alignPointerOffset__anon_1 p0 p1)
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        pure (.br2 i6))
      else (do
        pure (.ret none))) : Zig.MM mem_alignPointer__anon_1Locals mem_alignPointer__anon_1Exit) with
    | .br2 v2 => (do
      let i9 ← pure (p0.elem 1 v2)
      let i10 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i9)))
      let i11 ← pure (i10 &&& (16383 : BitVec 64))
      let i12 ← pure (i11 == (0 : BitVec 64))
      match ← ((do
        if i12 then (do
          pure .br13)
        else (do
          throw .panic)) : Zig.MM mem_alignPointer__anon_1Locals mem_alignPointer__anon_1Exit) with
      | .br13 => (do
        let i18 ← pure (i9)
        pure (.ret i18))
      | e => pure e)
    | e => pure e) : Zig.MM mem_alignPointer__anon_1Locals mem_alignPointer__anon_1Exit).run' (default : mem_alignPointer__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heap_PageAllocator_mapLocals where
  local14 : Option (Zig.Ptr)
  local15 : Option (Zig.Ptr)
  local53 : Zig.Slice
  deriving Inhabited

inductive heap_PageAllocator_mapExit where
  | ret (v : Option (Zig.Ptr))
  | br2
  | br4
  | br16
  | br18
  | br33
  | br44 (v : Zig.Slice)
  | br60
  | br82
  | br72
  | br100
  | br114
  | br93
  | br123

def heap_PageAllocator_map (p0 : BitVec 64) (p1 : mem_Alignment) : Zig.ConcM Tgt (Option (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      pure .br2) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
    | .br2 => (do
      match ← ((do
        let i5 ← pure (p0)
        let i6 ← pure (Zig.ge false i5 (18446744073709535231 : BitVec 64))
        if i6 then (do
          pure (.ret none))
        else (do
          pure .br4)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
      | .br4 => (do
        let i10 ← Zig.callRC (mem_Alignment_toByteUnits p1)
        let i11 ← Zig.callRC (mem_alignForward__anon_1 p0 (16384 : BitVec 64))
        let i12 ← pure (Zig.subSat false i10 (16384 : BitVec 64))
        let i13 ← Zig.add false i11 i12
        match ← ((do
          let i17 ← Zig.atomicLoadUnorderedEncC (Option (Zig.Ptr)) 8 (⟨some 0, 0⟩ : Zig.Ptr)
          match ← ((do
            let i19 ← pure ((i17).isNone)
            if i19 then (do
              modify (fun s => { s with local14 := none })
              modify (fun s => { s with local15 := none })
              pure .br16)
            else (do
              pure .br18)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
          | .br18 => (do
            let i25 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.optPtrAddr i17)))
            let i26 ← pure (Zig.subWrap i25 i11)
            let i27 ← Zig.sub false i10 (1 : BitVec 64)
            let i28 ← pure (~~~i27)
            let i29 ← pure (i26 &&& i28)
            let i30 ← pure (Zig.subWrap i29 i12)
            let i31 ← pure (i30 &&& (16383 : BitVec 64))
            let i32 ← pure (i31 == (0 : BitVec 64))
            match ← ((do
              if i32 then (do
                pure .br33)
              else (do
                throw .panic)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
            | .br33 => (do
              let i38 ← Zig.callMC (Zig.optPtrFromAddr (i30).toNat)
              modify (fun s => { s with local14 := i17 })
              modify (fun s => { s with local15 := i38 })
              pure .br16)
            | e => pure e)
          | e => pure e) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
        | .br16 => (do
          match ← ((do
            let i45 ← pure ((← get).local15)
            let i46 ← Zig.callMC (Zig.Os.mmap Zig.Os.Target.macos i45 i13 (Zig.Packed.toBits (Zig.Packed.ofBits (3 : BitVec 32) : macho_vm_prot_t)) (Zig.Packed.toBits (Zig.Packed.ofBits (4098 : BitVec 32) : c_MAP__struct_1)) (-(1 : BitVec 32)) (0 : BitVec 64))
            let i47 ← pure (Zig.isNonErr i46)
            if i47 then (do
              let i49 ← Zig.callRC (Zig.unwrapPayload i46)
              pure (.br44 i49))
            else (do
              let _i51 ← Zig.callRC (Zig.unwrapErr i46)
              pure (.ret none))) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
          | .br44 v44 => (do
            modify (fun s => { s with local53 := v44 })
            let i57 ← pure (((← get).local53).ptr)
            let i58 ← Zig.callMC (mem_alignPointer__anon_1 i57 i10)
            let i59 ← pure ((i58).isSome)
            match ← ((do
              if i59 then (do
                pure .br60)
              else (do
                throw .panic)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
            | .br60 => (do
              let i65 ← Zig.optPayload i58
              let i67 ← pure (((← get).local53).ptr)
              let i68 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i65)))
              let i69 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i67)))
              let i70 ← pure (Zig.subWrap i68 i69)
              let i71 ← Zig.divExact false i70 (1 : BitVec 64)
              match ← ((do
                let i73 ← pure (i71)
                let i74 ← pure (i73 != (0 : BitVec 64))
                if i74 then (do
                  let i76 ← pure ((← get).local53)
                  let i77 ← pure i76.ptr
                  let i78 ← pure (i77.elem 1 (0 : BitVec 64))
                  let i79 ← Zig.sub false i71 (0 : BitVec 64)
                  let i80 ← pure i76.len
                  let i81 ← pure (Zig.le false i71 i80)
                  match ← ((do
                    if i81 then (do
                      pure .br82)
                    else (do
                      throw .outOfBounds)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
                  | .br82 => (do
                    let i87 ← pure (⟨i78, i79⟩ : Zig.Slice)
                    let i88 ← pure (i87)
                    let _i89 ← Zig.callMC (Zig.Os.munmap Zig.Os.Target.macos i88)
                    pure .br72)
                  | e => pure e)
                else (do
                  pure .br72)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
              | .br72 => (do
                let i92 ← Zig.sub false i13 i71
                match ← ((do
                  let i94 ← pure (i92)
                  let i95 ← pure (i11)
                  let i96 ← pure (Zig.gt false i94 i95)
                  if i96 then (do
                    let i98 ← pure (i65.elem 1 i11)
                    let i99 ← pure (Zig.le false i11 i92)
                    match ← ((do
                      if i99 then (do
                        pure .br100)
                      else (do
                        throw .outOfBounds)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
                    | .br100 => (do
                      let i105 ← Zig.sub false i92 i11
                      let i106 ← pure (⟨i98, i105⟩ : Zig.Slice)
                      let i107 ← pure i106.ptr
                      let i108 ← pure i106.len
                      let i109 ← pure (i108 == (0 : BitVec 64))
                      let i110 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i107)))
                      let i111 ← pure (i110 &&& (16383 : BitVec 64))
                      let i112 ← pure (i111 == (0 : BitVec 64))
                      let i113 ← pure (i109 || i112)
                      match ← ((do
                        if i113 then (do
                          pure .br114)
                        else (do
                          throw .panic)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
                      | .br114 => (do
                        let i119 ← pure (i106)
                        let _i120 ← Zig.callMC (Zig.Os.munmap Zig.Os.Target.macos i119)
                        pure .br93)
                      | e => pure e)
                    | e => pure e)
                  else (do
                    pure .br93)) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
                | .br93 => (do
                  match ← ((do
                    let i124 ← pure (i65.elem 1 (0 : BitVec 64))
                    let i125 ← pure ((← get).local14)
                    let i126 ← pure (i124)
                    let _i127 ← Zig.cmpxchgPtrC (α := Option (Zig.Ptr)) Zig.AtomicOrder.relaxed Zig.AtomicOrder.relaxed 8 (⟨some 0, 0⟩ : Zig.Ptr) i125 i126
                    pure .br123) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit) with
                  | .br123 => (do
                    let i129 ← pure (i65)
                    pure (.ret i129))
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt heap_PageAllocator_mapLocals heap_PageAllocator_mapExit).run' (default : heap_PageAllocator_mapLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heap_PageAllocator_allocLocals where
  deriving Inhabited

inductive heap_PageAllocator_allocExit where
  | ret (v : Option (Zig.Ptr))

def heap_PageAllocator_alloc (p0 : Zig.Ptr) (p1 : BitVec 64) (p2 : mem_Alignment) (p3 : BitVec 64) : Zig.ConcM Tgt (Option (Zig.Ptr)) := do
  let e ← ((do
    let i4 ← pure (p1)
    let i5 ← pure (Zig.gt false i4 (0 : BitVec 64))
    let _i6 ← Zig.callRC (debug_assert i5)
    let i7 ← Zig.callC (heap_PageAllocator_map p1 p2)
    pure (.ret i7)) : Zig.CM Tgt heap_PageAllocator_allocLocals heap_PageAllocator_allocExit).run' (default : heap_PageAllocator_allocLocals)
  match e with
  | .ret v => pure v

structure heap_PageAllocator_unmapLocals where
  local1 : Zig.Slice
  deriving Inhabited

inductive heap_PageAllocator_unmapExit where
  | ret
  | br7
  | br4

def heap_PageAllocator_unmap (p0 : Zig.Slice) : Zig.MemM (Unit) := do
  let e ← ((do
    modify (fun s => { s with local1 := p0 })
    match ← ((do
      let i6 ← pure (((← get).local1).len)
      match ← ((do
        pure .br7) : Zig.MM heap_PageAllocator_unmapLocals heap_PageAllocator_unmapExit) with
      | .br7 => (do
        let i9 ← Zig.callR (mem_alignForward__anon_1 i6 (16384 : BitVec 64))
        let i11 ← pure (((← get).local1).ptr)
        let i12 ← pure (i11.elem 1 (0 : BitVec 64))
        let i13 ← Zig.sub false i9 (0 : BitVec 64)
        let i14 ← pure (⟨i12, i13⟩ : Zig.Slice)
        let i15 ← pure (i14)
        let _i16 ← Zig.callM (Zig.Os.munmap Zig.Os.Target.macos i15)
        pure .br4)
      | e => pure e) : Zig.MM heap_PageAllocator_unmapLocals heap_PageAllocator_unmapExit) with
    | .br4 => (do
      pure .ret)
    | e => pure e) : Zig.MM heap_PageAllocator_unmapLocals heap_PageAllocator_unmapExit).run' (default : heap_PageAllocator_unmapLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure heap_PageAllocator_freeLocals where
  deriving Inhabited

inductive heap_PageAllocator_freeExit where
  | ret
  | br11

def heap_PageAllocator_free (p0 : Zig.Ptr) (p1 : Zig.Slice) (p2 : mem_Alignment) (p3 : BitVec 64) : Zig.MemM (Unit) := do
  let e ← ((do
    let i4 ← pure p1.ptr
    let i5 ← pure p1.len
    let i6 ← pure (i5 == (0 : BitVec 64))
    let i7 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i4)))
    let i8 ← pure (i7 &&& (16383 : BitVec 64))
    let i9 ← pure (i8 == (0 : BitVec 64))
    let i10 ← pure (i6 || i9)
    match ← ((do
      if i10 then (do
        pure .br11)
      else (do
        throw .panic)) : Zig.MM heap_PageAllocator_freeLocals heap_PageAllocator_freeExit) with
    | .br11 => (do
      let i16 ← pure (p1)
      let _i17 ← Zig.callM (heap_PageAllocator_unmap i16)
      pure .ret)
    | e => pure e) : Zig.MM heap_PageAllocator_freeLocals heap_PageAllocator_freeExit).run' (default : heap_PageAllocator_freeLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure heap_PageAllocator_reallocLocals where
  local17 : Zig.Slice
  deriving Inhabited

inductive heap_PageAllocator_reallocExit where
  | ret (v : Option (Zig.Ptr))
  | br11
  | br20
  | br22
  | br33
  | br62
  | br43

def heap_PageAllocator_realloc (p0 : Zig.Slice) (p1 : mem_Alignment) (p2 : BitVec 64) (p3 : Bool) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    let i4 ← pure p0.ptr
    let i5 ← pure p0.len
    let i6 ← pure (i5 == (0 : BitVec 64))
    let i7 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i4)))
    let i8 ← pure (i7 &&& (16383 : BitVec 64))
    let i9 ← pure (i8 == (0 : BitVec 64))
    let i10 ← pure (i6 || i9)
    match ← ((do
      if i10 then (do
        pure .br11)
      else (do
        throw .panic)) : Zig.MM heap_PageAllocator_reallocLocals heap_PageAllocator_reallocExit) with
    | .br11 => (do
      let i16 ← pure (p0)
      modify (fun s => { s with local17 := i16 })
      match ← ((do
        pure .br20) : Zig.MM heap_PageAllocator_reallocLocals heap_PageAllocator_reallocExit) with
      | .br20 => (do
        match ← ((do
          let i23 ← Zig.callR (mem_Alignment_toByteUnits p1)
          let i24 ← pure (i23)
          let i25 ← pure (Zig.gt false i24 (16384 : BitVec 64))
          if i25 then (do
            pure (.ret none))
          else (do
            pure .br22)) : Zig.MM heap_PageAllocator_reallocLocals heap_PageAllocator_reallocExit) with
        | .br22 => (do
          let i29 ← Zig.callR (mem_alignForward__anon_1 p2 (16384 : BitVec 64))
          let i31 ← pure (((← get).local17).len)
          let i32 ← Zig.callR (mem_alignForward__anon_1 i31 (16384 : BitVec 64))
          match ← ((do
            let i34 ← pure (i29)
            let i35 ← pure (i32)
            let i36 ← pure (i34 == i35)
            if i36 then (do
              let i39 ← pure (((← get).local17).ptr)
              let i40 ← pure (i39)
              pure (.ret i40))
            else (do
              pure .br33)) : Zig.MM heap_PageAllocator_reallocLocals heap_PageAllocator_reallocExit) with
          | .br33 => (do
            match ← ((do
              let i44 ← pure (i29)
              let i45 ← pure (i32)
              let i46 ← pure (Zig.lt false i44 i45)
              if i46 then (do
                let i49 ← pure (((← get).local17).ptr)
                let i50 ← pure (i49.elem 1 i29)
                let i51 ← Zig.sub false i32 i29
                let i52 ← pure (i50.elem 1 (0 : BitVec 64))
                let i53 ← Zig.sub false i51 (0 : BitVec 64)
                let i54 ← pure (⟨i52, i53⟩ : Zig.Slice)
                let i55 ← pure i54.ptr
                let i56 ← pure i54.len
                let i57 ← pure (i56 == (0 : BitVec 64))
                let i58 ← Zig.callM (do pure (BitVec.ofInt 64 (← Zig.ptrAddr i55)))
                let i59 ← pure (i58 &&& (16383 : BitVec 64))
                let i60 ← pure (i59 == (0 : BitVec 64))
                let i61 ← pure (i57 || i60)
                match ← ((do
                  if i61 then (do
                    pure .br62)
                  else (do
                    throw .panic)) : Zig.MM heap_PageAllocator_reallocLocals heap_PageAllocator_reallocExit) with
                | .br62 => (do
                  let i67 ← pure (i54)
                  let _i68 ← Zig.callM (Zig.Os.munmap Zig.Os.Target.macos i67)
                  let i70 ← pure (((← get).local17).ptr)
                  let i71 ← pure (i70)
                  pure (.ret i71))
                | e => pure e)
              else (do
                pure .br43)) : Zig.MM heap_PageAllocator_reallocLocals heap_PageAllocator_reallocExit) with
            | .br43 => (do
              pure (.ret none))
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM heap_PageAllocator_reallocLocals heap_PageAllocator_reallocExit).run' (default : heap_PageAllocator_reallocLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure heap_PageAllocator_remapLocals where
  deriving Inhabited

inductive heap_PageAllocator_remapExit where
  | ret (v : Option (Zig.Ptr))

def heap_PageAllocator_remap (p0 : Zig.Ptr) (p1 : Zig.Slice) (p2 : mem_Alignment) (p3 : BitVec 64) (p4 : BitVec 64) : Zig.MemM (Option (Zig.Ptr)) := do
  let e ← ((do
    let i5 ← Zig.callM (heap_PageAllocator_realloc p1 p2 p3 true)
    pure (.ret i5)) : Zig.MM heap_PageAllocator_remapLocals heap_PageAllocator_remapExit).run' (default : heap_PageAllocator_remapLocals)
  match e with
  | .ret v => pure v

structure heap_PageAllocator_resizeLocals where
  deriving Inhabited

inductive heap_PageAllocator_resizeExit where
  | ret (v : Bool)

def heap_PageAllocator_resize (p0 : Zig.Ptr) (p1 : Zig.Slice) (p2 : mem_Alignment) (p3 : BitVec 64) (p4 : BitVec 64) : Zig.MemM (Bool) := do
  let e ← ((do
    let i5 ← Zig.callM (heap_PageAllocator_realloc p1 p2 p3 false)
    let i6 ← pure ((i5).isSome)
    pure (.ret i6)) : Zig.MM heap_PageAllocator_resizeLocals heap_PageAllocator_resizeExit).run' (default : heap_PageAllocator_resizeLocals)
  match e with
  | .ret v => pure v

structure math_mul__anon_1Locals where
  deriving Inhabited

inductive math_mul__anon_1Exit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br3

def math_mul__anon_1 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← pure (Zig.mulWithOverflow false p0 p1)
    match ← ((do
      let i4 ← pure ((i2).2)
      let i5 ← pure (i4 != (0 : BitVec 1))
      if i5 then (do
        pure (.ret (.error "Overflow" : Except Zig.ErrName (BitVec 64))))
      else (do
        pure .br3)) : Zig.M math_mul__anon_1Locals math_mul__anon_1Exit) with
    | .br3 => (do
      let i9 ← pure ((i2).1)
      let i10 ← pure ((.ok i9) : Except Zig.ErrName (BitVec 64))
      pure (.ret i10))
    | e => pure e) : Zig.M math_mul__anon_1Locals math_mul__anon_1Exit).run' (default : math_mul__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Alignment_fromByteUnitsLocals where
  deriving Inhabited

inductive mem_Alignment_fromByteUnitsExit where
  | ret (v : mem_Alignment)

def mem_Alignment_fromByteUnits (p0 : BitVec 64) : Zig.Result (mem_Alignment) := do
  let e ← ((do
    let i1 ← Zig.call (math_isPowerOfTwo__anon_1 p0)
    let _i2 ← Zig.call (debug_assert i1)
    let i3 ← pure (Zig.ctz 7 p0)
    let i4 ← Zig.enumOf (mem_Alignment.ofInt? (Zig.val false i3))
    pure (.ret i4)) : Zig.M mem_Alignment_fromByteUnitsLocals mem_Alignment_fromByteUnitsExit).run' (default : mem_Alignment_fromByteUnitsLocals)
  match e with
  | .ret v => pure v

structure mem_Allocator_allocBytesWithAlignment__anon_2Locals where
  deriving Inhabited

inductive mem_Allocator_allocBytesWithAlignment__anon_2Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3
  | br10 (v : Option (Zig.Ptr))
  | br9 (v : Zig.Ptr)

def mem_Allocator_allocBytesWithAlignment__anon_2 (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (⟨none, 18446744073709551615⟩ : Zig.Ptr) : Except Zig.ErrName (Zig.Ptr))))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_2Locals mem_Allocator_allocBytesWithAlignment__anon_2Exit) with
    | .br3 => (do
      match ← ((do
        match ← ((do
          let i11 ← pure ((p0).vtable)
          let i12 ← pure (i11.add 0)
          let i13 ← Zig.load (Zig.Ptr) 8 i12
          let i14 ← pure ((p0).ptr)
          let i15 ← (if i13 == (⟨some 2, 0⟩ : Zig.Ptr) then Zig.callC (heap_PageAllocator_alloc i14 p1 mem_Alignment.«1» p2) else throw .illegal)
          pure (.br10 i15)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_2Locals mem_Allocator_allocBytesWithAlignment__anon_2Exit) with
        | .br10 v10 => (do
          let i17 ← pure ((v10).isSome)
          if i17 then (do
            let i19 ← Zig.optPayload v10
            pure (.br9 i19))
          else (do
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr)))))
        | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_2Locals mem_Allocator_allocBytesWithAlignment__anon_2Exit) with
      | .br9 v9 => (do
        let i22 ← pure (v9.elem 1 (0 : BitVec 64))
        let i23 ← Zig.sub false p1 (0 : BitVec 64)
        let i24 ← pure (⟨i22, i23⟩ : Zig.Slice)
        let _i25 ← pure i24.len
        Zig.callMC (Zig.memset (α := BitVec 8) 1 i24.ptr i24.len none)
        let i27 ← pure (v9)
        let i28 ← pure ((.ok i27) : Except Zig.ErrName (Zig.Ptr))
        pure (.ret i28))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_2Locals mem_Allocator_allocBytesWithAlignment__anon_2Exit).run' (default : mem_Allocator_allocBytesWithAlignment__anon_2Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_allocBytesWithAlignment__anon_1Locals where
  deriving Inhabited

inductive mem_Allocator_allocBytesWithAlignment__anon_1Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3
  | br10 (v : Option (Zig.Ptr))
  | br9 (v : Zig.Ptr)
  | br30

def mem_Allocator_allocBytesWithAlignment__anon_1 (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        pure (.ret (.ok (⟨none, 18446744073709551612⟩ : Zig.Ptr) : Except Zig.ErrName (Zig.Ptr))))
      else (do
        pure .br3)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_1Locals mem_Allocator_allocBytesWithAlignment__anon_1Exit) with
    | .br3 => (do
      match ← ((do
        match ← ((do
          let i11 ← pure ((p0).vtable)
          let i12 ← pure (i11.add 0)
          let i13 ← Zig.load (Zig.Ptr) 8 i12
          let i14 ← pure ((p0).ptr)
          let i15 ← (if i13 == (⟨some 2, 0⟩ : Zig.Ptr) then Zig.callC (heap_PageAllocator_alloc i14 p1 mem_Alignment.«4» p2) else throw .illegal)
          pure (.br10 i15)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_1Locals mem_Allocator_allocBytesWithAlignment__anon_1Exit) with
        | .br10 v10 => (do
          let i17 ← pure ((v10).isSome)
          if i17 then (do
            let i19 ← Zig.optPayload v10
            pure (.br9 i19))
          else (do
            pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr)))))
        | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_1Locals mem_Allocator_allocBytesWithAlignment__anon_1Exit) with
      | .br9 v9 => (do
        let i22 ← pure (v9.elem 1 (0 : BitVec 64))
        let i23 ← Zig.sub false p1 (0 : BitVec 64)
        let i24 ← pure (⟨i22, i23⟩ : Zig.Slice)
        let _i25 ← pure i24.len
        Zig.callMC (Zig.memset (α := BitVec 8) 1 i24.ptr i24.len none)
        let i27 ← Zig.callMC (do pure (BitVec.ofInt 64 (← Zig.ptrAddr v9)))
        let i28 ← pure (i27 &&& (3 : BitVec 64))
        let i29 ← pure (i28 == (0 : BitVec 64))
        match ← ((do
          if i29 then (do
            pure .br30)
          else (do
            throw .panic)) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_1Locals mem_Allocator_allocBytesWithAlignment__anon_1Exit) with
        | .br30 => (do
          let i35 ← pure (v9)
          let i36 ← pure ((.ok i35) : Except Zig.ErrName (Zig.Ptr))
          pure (.ret i36))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocBytesWithAlignment__anon_1Locals mem_Allocator_allocBytesWithAlignment__anon_1Exit).run' (default : mem_Allocator_allocBytesWithAlignment__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_allocWithSizeAndAlignment__anon_1Locals where
  deriving Inhabited

inductive mem_Allocator_allocWithSizeAndAlignment__anon_1Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))
  | br3 (v : BitVec 64)

def mem_Allocator_allocWithSizeAndAlignment__anon_1 (p0 : mem_Allocator) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.callRC (math_mul__anon_1 (1 : BitVec 64) p1)
      let i5 ← pure (Zig.isNonErr i4)
      if i5 then (do
        let i7 ← Zig.callRC (Zig.unwrapPayload i4)
        pure (.br3 i7))
      else (do
        let _i9 ← Zig.callRC (Zig.unwrapErr i4)
        pure (.ret (.error "OutOfMemory" : Except Zig.ErrName (Zig.Ptr))))) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_1Locals mem_Allocator_allocWithSizeAndAlignment__anon_1Exit) with
    | .br3 v3 => (do
      let i11 ← Zig.callC (mem_Allocator_allocBytesWithAlignment__anon_2 p0 v3 p2)
      pure (.ret i11))
    | e => pure e) : Zig.CM Tgt mem_Allocator_allocWithSizeAndAlignment__anon_1Locals mem_Allocator_allocWithSizeAndAlignment__anon_1Exit).run' (default : mem_Allocator_allocWithSizeAndAlignment__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_alloc__anon_1Locals where
  deriving Inhabited

inductive mem_Allocator_alloc__anon_1Exit where
  | ret (v : Except Zig.ErrName (Zig.Slice))
  | br3 (v : Except Zig.ErrName (Zig.Slice))

def mem_Allocator_alloc__anon_1 (p0 : mem_Allocator) (p1 : BitVec 64) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Slice)) := do
  let e ← ((do
    let i2 ← Zig.callMC Zig.returnAddress
    match ← ((do
      let i4 ← Zig.callC (mem_Allocator_allocWithSizeAndAlignment__anon_1 p0 p1 i2)
      match i4 with
      | .error _ => (do
        let i6 ← Zig.callRC (Zig.unwrapErr i4)
        let i7 ← pure ((.error i6) : Except Zig.ErrName (Zig.Slice))
        pure (.br3 i7))
      | .ok v5 => (do
        let i9 ← pure (v5.elem 1 (0 : BitVec 64))
        let i10 ← Zig.sub false p1 (0 : BitVec 64)
        let i11 ← pure (⟨i9, i10⟩ : Zig.Slice)
        let i12 ← pure ((.ok i11) : Except Zig.ErrName (Zig.Slice))
        pure (.br3 i12))) : Zig.CM Tgt mem_Allocator_alloc__anon_1Locals mem_Allocator_alloc__anon_1Exit) with
    | .br3 v3 => (do
      let i14 ← pure (v3)
      pure (.ret i14))
    | e => pure e) : Zig.CM Tgt mem_Allocator_alloc__anon_1Locals mem_Allocator_alloc__anon_1Exit).run' (default : mem_Allocator_alloc__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_Allocator_create__anon_1Locals where
  deriving Inhabited

inductive mem_Allocator_create__anon_1Exit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

def mem_Allocator_create__anon_1 (p0 : mem_Allocator) : Zig.ConcM Tgt (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    let i1 ← Zig.callMC Zig.returnAddress
    let i2 ← Zig.callC (mem_Allocator_allocBytesWithAlignment__anon_1 p0 (4 : BitVec 64) i1)
    match i2 with
    | .error _ => (do
      let i4 ← Zig.callRC (Zig.unwrapErr i2)
      let i5 ← pure ((.error i4) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i5))
    | .ok v3 => (do
      let i7 ← pure (v3)
      let i8 ← pure ((.ok i7) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i8))) : Zig.CM Tgt mem_Allocator_create__anon_1Locals mem_Allocator_create__anon_1Exit).run' (default : mem_Allocator_create__anon_1Locals)
  match e with
  | .ret v => pure v

structure mem_Allocator_destroy__anon_1Locals where
  deriving Inhabited

inductive mem_Allocator_destroy__anon_1Exit where
  | ret
  | br8

def mem_Allocator_destroy__anon_1 (p0 : mem_Allocator) (p1 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← pure (p1)
    let i3 ← pure (i2.elem 1 (0 : BitVec 64))
    let i4 ← pure (i3)
    let i5 ← pure (⟨i4, (4 : BitVec 64)⟩ : Zig.Slice)
    let i6 ← Zig.callR (mem_Alignment_fromByteUnits (4 : BitVec 64))
    let i7 ← Zig.callM Zig.returnAddress
    match ← ((do
      let i9 ← pure ((p0).vtable)
      let i10 ← pure (i9.add 24)
      let i11 ← Zig.load (Zig.Ptr) 8 i10
      let i12 ← pure ((p0).ptr)
      let _i13 ← (if i11 == (⟨some 5, 0⟩ : Zig.Ptr) then Zig.callM (heap_PageAllocator_free i12 i5 i6 i7) else throw .illegal)
      pure .br8) : Zig.MM mem_Allocator_destroy__anon_1Locals mem_Allocator_destroy__anon_1Exit) with
    | .br8 => (do
      pure .ret)
    | e => pure e) : Zig.MM mem_Allocator_destroy__anon_1Locals mem_Allocator_destroy__anon_1Exit).run' (default : mem_Allocator_destroy__anon_1Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure mem_absorbSentinel__anon_1Locals where
  deriving Inhabited

inductive mem_absorbSentinel__anon_1Exit where
  | ret (v : Zig.Slice)

def mem_absorbSentinel__anon_1 (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    pure (.ret p0)) : Zig.MM mem_absorbSentinel__anon_1Locals mem_absorbSentinel__anon_1Exit).run' (default : mem_absorbSentinel__anon_1Locals)
  match e with
  | .ret v => pure v

structure mem_Allocator_free__anon_1Locals where
  deriving Inhabited

inductive mem_Allocator_free__anon_1Exit where
  | ret
  | br4
  | br15

def mem_Allocator_free__anon_1 (p0 : mem_Allocator) (p1 : Zig.Slice) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← Zig.callM (mem_absorbSentinel__anon_1 p1)
    let i3 ← pure (i2)
    match ← ((do
      let i5 ← pure i3.len
      let i6 ← pure (i5)
      let i7 ← pure (i6 == (0 : BitVec 64))
      if i7 then (do
        pure .ret)
      else (do
        pure .br4)) : Zig.MM mem_Allocator_free__anon_1Locals mem_Allocator_free__anon_1Exit) with
    | .br4 => (do
      let _i11 ← pure i3.len
      Zig.callM (Zig.memset (α := BitVec 8) 1 i3.ptr i3.len none)
      let i13 ← Zig.callR (mem_Alignment_fromByteUnits (1 : BitVec 64))
      let i14 ← Zig.callM Zig.returnAddress
      match ← ((do
        let i16 ← pure ((p0).vtable)
        let i17 ← pure (i16.add 24)
        let i18 ← Zig.load (Zig.Ptr) 8 i17
        let i19 ← pure ((p0).ptr)
        let _i20 ← (if i18 == (⟨some 5, 0⟩ : Zig.Ptr) then Zig.callM (heap_PageAllocator_free i19 i3 i13 i14) else throw .illegal)
        pure .br15) : Zig.MM mem_Allocator_free__anon_1Locals mem_Allocator_free__anon_1Exit) with
      | .br15 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.MM mem_Allocator_free__anon_1Locals mem_Allocator_free__anon_1Exit).run' (default : mem_Allocator_free__anon_1Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure mem_Allocator_resize__anon_1Locals where
  deriving Inhabited

inductive mem_Allocator_resize__anon_1Exit where
  | ret (v : Bool)
  | br3
  | br10
  | br19 (v : BitVec 64)
  | br29 (v : Bool)

def mem_Allocator_resize__anon_1 (p0 : mem_Allocator) (p1 : Zig.Slice) (p2 : BitVec 64) : Zig.MemM (Bool) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p2)
      let i5 ← pure (i4 == (0 : BitVec 64))
      if i5 then (do
        let _i7 ← Zig.callM (mem_Allocator_free__anon_1 p0 p1)
        pure (.ret true))
      else (do
        pure .br3)) : Zig.MM mem_Allocator_resize__anon_1Locals mem_Allocator_resize__anon_1Exit) with
    | .br3 => (do
      match ← ((do
        let i11 ← pure p1.len
        let i12 ← pure (i11)
        let i13 ← pure (i12 == (0 : BitVec 64))
        if i13 then (do
          pure (.ret false))
        else (do
          pure .br10)) : Zig.MM mem_Allocator_resize__anon_1Locals mem_Allocator_resize__anon_1Exit) with
      | .br10 => (do
        let i17 ← Zig.callM (mem_absorbSentinel__anon_1 p1)
        let i18 ← pure (i17)
        match ← ((do
          let i20 ← Zig.callR (math_mul__anon_1 (1 : BitVec 64) p2)
          let i21 ← pure (Zig.isNonErr i20)
          if i21 then (do
            let i23 ← Zig.callR (Zig.unwrapPayload i20)
            pure (.br19 i23))
          else (do
            let _i25 ← Zig.callR (Zig.unwrapErr i20)
            pure (.ret false))) : Zig.MM mem_Allocator_resize__anon_1Locals mem_Allocator_resize__anon_1Exit) with
        | .br19 v19 => (do
          let i27 ← Zig.callR (mem_Alignment_fromByteUnits (1 : BitVec 64))
          let i28 ← Zig.callM Zig.returnAddress
          match ← ((do
            let i30 ← pure ((p0).vtable)
            let i31 ← pure (i30.add 8)
            let i32 ← Zig.load (Zig.Ptr) 8 i31
            let i33 ← pure ((p0).ptr)
            let i34 ← (if i32 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callM (heap_PageAllocator_resize i33 i18 i27 v19 i28) else throw .illegal)
            pure (.br29 i34)) : Zig.MM mem_Allocator_resize__anon_1Locals mem_Allocator_resize__anon_1Exit) with
          | .br29 v29 => (do
            pure (.ret v29))
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM mem_Allocator_resize__anon_1Locals mem_Allocator_resize__anon_1Exit).run' (default : mem_Allocator_resize__anon_1Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure page_createLocals where
  deriving Inhabited

inductive page_createExit where
  | ret (v : BitVec 32)
  | br1 (v : Zig.Ptr)

def page_create (p0 : BitVec 32) : Zig.ConcM Tgt (BitVec 32) := do
  let e ← ((do
    match ← ((do
      let i2 ← Zig.callC (mem_Allocator_create__anon_1 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator))
      let i3 ← pure (Zig.isNonErr i2)
      if i3 then (do
        let i5 ← Zig.callRC (Zig.unwrapPayload i2)
        pure (.br1 i5))
      else (do
        let _i7 ← Zig.callRC (Zig.unwrapErr i2)
        pure (.ret (0 : BitVec 32)))) : Zig.CM Tgt page_createLocals page_createExit) with
    | .br1 v1 => (do
      Zig.store (α := BitVec 32) 4 v1 p0
      let i10 ← Zig.load (BitVec 32) 4 v1
      let _i11 ← Zig.callMC (mem_Allocator_destroy__anon_1 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) v1)
      pure (.ret i10))
    | e => pure e) : Zig.CM Tgt page_createLocals page_createExit).run' (default : page_createLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure page_resizeLocals where
  local10 : Zig.Slice
  deriving Inhabited

inductive page_resizeExit where
  | ret (v : Bool)
  | br2 (v : Zig.Slice)
  | br14

def page_resize (p0 : BitVec 64) (p1 : BitVec 64) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    match ← ((do
      let i3 ← Zig.callC (mem_Allocator_alloc__anon_1 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) p0)
      let i4 ← pure (Zig.isNonErr i3)
      if i4 then (do
        let i6 ← Zig.callRC (Zig.unwrapPayload i3)
        pure (.br2 i6))
      else (do
        let _i8 ← Zig.callRC (Zig.unwrapErr i3)
        pure (.ret false))) : Zig.CM Tgt page_resizeLocals page_resizeExit) with
    | .br2 v2 => (do
      modify (fun s => { s with local10 := v2 })
      let i13 ← Zig.callMC (mem_Allocator_resize__anon_1 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) v2 p1)
      match ← ((do
        if i13 then (do
          let i17 ← pure (((← get).local10).ptr)
          let i18 ← pure (i17.elem 1 (0 : BitVec 64))
          let i19 ← Zig.sub false p1 (0 : BitVec 64)
          let i20 ← pure (⟨i18, i19⟩ : Zig.Slice)
          let _i21 ← Zig.callMC (mem_Allocator_free__anon_1 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) i20)
          pure .br14)
        else (do
          let _i23 ← Zig.callMC (mem_Allocator_free__anon_1 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) v2)
          pure .br14)) : Zig.CM Tgt page_resizeLocals page_resizeExit) with
      | .br14 => (do
        pure (.ret i13))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt page_resizeLocals page_resizeExit).run' (default : page_resizeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure page_sumLocals where
  sum : BitVec 64
  local13 : BitVec 64
  deriving Inhabited

inductive page_sumExit where
  | ret (v : BitVec 64)
  | br1 (v : Zig.Slice)
  | br19
  | br16
  | rep17

def page_sum.again17 : page_sumExit → Bool
  | .rep17 => true
  | _ => false

def page_sum.loop17 (i1 : Zig.Slice) (i15 : BitVec 64) : Zig.CM Tgt page_sumLocals page_sumExit := do
  let i18 ← pure ((← get).local13)
  match ← ((do
    let i20 ← pure (i18)
    let i21 ← pure (i15)
    let i22 ← pure (Zig.lt false i20 i21)
    if i22 then (do
      let i24 ← Zig.callMC (Zig.load (BitVec 8) 1 (i1.ptr.elem 1 i18))
      let i25 ← pure ((← get).sum)
      let i26 ← Zig.intCast false false 64 i24
      let i27 ← Zig.add false i25 i26
      modify (fun s => { s with sum := i27 })
      pure .br19)
    else (do
      pure .br16)) : Zig.CM Tgt page_sumLocals page_sumExit) with
  | .br19 => (do
    let i31 ← Zig.add false i18 (1 : BitVec 64)
    modify (fun s => { s with local13 := i31 })
    pure .rep17)
  | e => pure e

def page_sum (p0 : BitVec 64) : Zig.ConcM Tgt (BitVec 64) := do
  let e ← ((do
    match ← ((do
      let i2 ← Zig.callC (mem_Allocator_alloc__anon_1 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) p0)
      let i3 ← pure (Zig.isNonErr i2)
      if i3 then (do
        let i5 ← Zig.callRC (Zig.unwrapPayload i2)
        pure (.br1 i5))
      else (do
        let _i7 ← Zig.callRC (Zig.unwrapErr i2)
        pure (.ret (0 : BitVec 64)))) : Zig.CM Tgt page_sumLocals page_sumExit) with
    | .br1 v1 => (do
      let _i9 ← pure v1.len
      Zig.callMC (Zig.memset (α := BitVec 8) 1 v1.ptr v1.len (some (1 : BitVec 8)))
      modify (fun s => { s with sum := (0 : BitVec 64) })
      modify (fun s => { s with local13 := (0 : BitVec 64) })
      let i15 ← pure v1.len
      match ← ((do
        Zig.loop (page_sum.loop17 v1 i15) page_sum.again17) : Zig.CM Tgt page_sumLocals page_sumExit) with
      | .br16 => (do
        let i34 ← pure ((← get).sum)
        let _i35 ← Zig.callMC (mem_Allocator_free__anon_1 ({ ptr := (← Zig.callMC Zig.undefPtr), vtable := (⟨some 1, 0⟩ : Zig.Ptr) } : mem_Allocator) v1)
        pure (.ret i34))
      | e => pure e)
    | e => pure e) : Zig.CM Tgt page_sumLocals page_sumExit).run' (default : page_sumLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit :=
  fun t => nomatch t

end AllocTranslated.PageMacos