-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"none","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"apple_m1","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["aes","aggressive_fma","alternate_sextload_cvt_f32_pattern","altnzcv","am","arith_bcc_fusion","arith_cbz_fusion","ccdp","ccidx","ccpp","complxnum","contextidr_el2","crc","disable_latency_sched_heuristic","dit","dotprod","el2vmsa","el3","flagm","fp16fml","fp_armv8","fptoint","fullfp16","fuse_address","fuse_aes","fuse_arith_logic","fuse_crypto_eor","fuse_csel","fuse_literals","jsconv","lor","lse","lse2","mpam","neon","nv","pan","pan_rwv","pauth","perfmon","predres","ras","rcpc","rcpc_immo","rdm","sb","sel2","sha2","sha3","specrestrict","ssbs","store_pair_suppress","tlb_rmi","tracev8_4","uaops","v8_1a","v8_2a","v8_3a","v8_4a","v8a","vh","zcm_fpr64","zcm_gpr64","zcz","zcz_gp"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"aarch64-macos.13.0...15.6-none","zig_version":"0.16.0"}}
import ZigLean


namespace ProvenanceGap

structure gapLocals where
  deriving Inhabited

inductive gapExit where
  | ret (v : BitVec 32)
  | br2 (v : BitVec 32)

def gap (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (Zig.gt false p0 p1)
      if i3 then (do
        let i5 ← Zig.sub false p0 p1
        pure (.br2 i5))
      else (do
        let i7 ← Zig.sub false p1 p0
        pure (.br2 i7))) : Zig.M gapLocals gapExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M gapLocals gapExit).run' (default : gapLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure withinLocals where
  deriving Inhabited

inductive withinExit where
  | ret (v : Bool)

def within (p0 : BitVec 32) (p1 : BitVec 32) (p2 : BitVec 32) : Zig.Result (Bool) := do
  let e ← ((do
    let i3 ← Zig.call (gap p0 p1)
    let i4 ← pure (Zig.le false i3 p2)
    pure (.ret i4)) : Zig.M withinLocals withinExit).run' (default : withinLocals)
  match e with
  | .ret v => pure v

end ProvenanceGap