-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
-- air2lean-device: {"asm":[{"clobbers":["cc","rdx"],"constraints":["={rax}"],"template":"rdtsc\n\u0009shlq $32, %%rdx\n\u0009orq %%rdx, %%rax"}],"device":"cpu","registers":[],"schema":1,"semantics":"trace-oracle-v1"}
import ZigLean


namespace DeviceAsm

/-- The declared device `cpu` (`--device-contract`, docs/volatile-effects.md, premise DEV-01): every volatile access is `Zig.vload`/`Zig.vstore` on this register map, and every declared `asm volatile` is `Zig.vasm`. -/
def air2lean_device : Zig.Device := { name := "cpu", regs := [], asms := ["rdtsc\n\tshlq $32, %%rdx\n\torq %%rdx, %%rax"] }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure elapsedLocals where
  deriving Inhabited

inductive elapsedExit where
  | ret (v : BitVec 64)

def elapsed  : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i0 ← Zig.vasm air2lean_device "rdtsc\n\tshlq $32, %%rdx\n\torq %%rdx, %%rax" [] 64
    let i1 ← Zig.vasm air2lean_device "rdtsc\n\tshlq $32, %%rdx\n\torq %%rdx, %%rax" [] 64
    let i2 ← pure (Zig.subWrap i1 i0)
    pure (.ret i2)) : Zig.MM elapsedLocals elapsedExit).run' (default : elapsedLocals)
  match e with
  | .ret v => pure v

end DeviceAsm