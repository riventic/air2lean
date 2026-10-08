# Inline asm effect contract (A01)

The translator accepts read-write and memory asm operands only through an explicit effect
contract (`docs/generated-code.md` §Inline asm, `Air2Lean/AsmContract.lean`, `ZigLean/Asm.lean`,
premise ASM-03). The opaque `airAsmFx_<hash>` is a pure function of the register inputs and the
old values of the read-write outputs. The generated wrapper holds every memory effect: the alias
guard, the read-write loads, the call, then one store per lvalue output.

The fixture is hand-written AIR in the exporter's schema (`air/0.16.0`, Zig 0.16.0, x86_64):

```zig
// The output operand of Zig source names a variable; the AIR `ref` of incm/setm/swapm is the
// pointer argument itself, which only hand-written AIR (or an escaping local) reaches.
export fn incm(p: *u32) void       // asm volatile ("incl %[x]" : [x] "+m" (p.*) :: .{ .cc = true })
export fn setm(p: *u64, v: u64) void // asm ("movq %[v], %[x]" : [x] "=m" (p.*) : [v] "r" (v))
export fn swapm(p: *u32, q: *u32) void // "+m" a, "+m" b; xchg through eax; clobber rax
export fn addr(x: u64, v: u64) u64 { var y = x; asm ("addq %[v], %[y]" : [y] "+r" (y) : [v] "r" (v) : .{ .cc = true }); return y; }
export fn incLocal(x: u32) u32 { var y = x; asm volatile ("incl %[y]" : [y] "+m" (y) :: .{ .cc = true }); return y; }
export fn barrier() void { asm volatile ("" ::: .{ .memory = true }); } // the registry entry
```

`AsmEffects/Gen.lean` is its retained translation. `AsmEffects/Proofs.lean` proves, from the
generated text alone:

| Theorem | Statement |
|---|---|
| `incm_frame`, `setm_frame`, `swapm_frame` | any successful run changes only the bytes of the declared operands (`Zig.Asm.Frame`, `Proofs/Asm/Effects.lean`) |
| `incm_spec` | the `+m` operand holds the opaque's value of its old contents |
| `swapm_alias` | one pointer for both `+m` operands is `.unspecified` |
| `swapm_disjoint` | a successful run had disjoint operands |
| `addr_spec`, `incLocal_spec` | `+r`/`+m` on a local, from an ASM-02 hypothesis on the opaque |
| `barrier_spec` | the registry block has no effect |

`test_cli.py` checks the translation byte for byte, that `Proofs/Asm/Gen.lean` (register-only)
is unchanged, and 24 rejections through the CLI and `--diagnostics-json`: a `"memory"` clobber
outside the registry, a read-write or memory result output, `=&m`/`+&r`/`=rm`/`=g`/`&r`
outputs, `m`/`i`/`rm`/`+r` inputs, a 24-bit memory operand, a write through a const pointer,
two outputs writing one pointer or one local, a clobber naming a pinned operand's register
(`+{eax}` with `rax`, `{rcx}` with `cl`), two pins of one register, an input pinned to an
early-clobber output's register, and a matching input tied to a read-write or memory output.

`harness.py` runs the generated wrappers unchanged under A03's test-only interpretation
(`tests/roadmap/asm-wrappers/Interp.lean`, extended with `+r`/`+m`/`=m` operands and the
`inc`, `add`, `mov`, `xchg` instructions). It binds each opaque by the translator's hash.
`Runner.lean` runs the memory wrappers on a 32-byte block and compares the whole block, so a
write outside the declared location fails. The alias case must be `.unspecified`. Each mutant
must elaborate and fail with a `MISMATCH wrapper` line:

| Mutant | Change |
|---|---|
| `store_wrong_location` | `incm` stores to `p0.add 4` |
| `rw_read_dropped` | `incm` passes `0` instead of the old value |
| `swap_targets` | `swapm` stores each output to the other operand |
| `rw_order` | `swapm` passes the old values in the wrong order |
| `guard_dropped` | `swapm` drops `Zig.Asm.guard` (the alias case then returns) |
| `local_store_dropped` | `incLocal` drops the store of the `+m` result |

Harness assumptions are A03's AH-01..05, and AH-02 (flags unmodelled) covers `inc`/`add`. A
memory operand is a slot of the interpreter, not an address: the interpretation cannot express
an access outside the declared operands, so the frame evidence for real instructions is ASM-03
itself. An `=m` slot starts with junk that differs between allocations, so a template that reads
it first is rejected.

```sh
lake build air2lean ZigLean Proofs.Asm.Effects
bash tests/roadmap/asm-effects/check.sh
```

Scope: x86_64 GPR families for clobber/pin aliasing; one registry entry; no `m`/immediate
inputs. Zig 0.16.0's LLVM backend fails module verification on `+m` (the self-hosted x86_64
backend compiles it); the translator's contract concerns the AIR, not a backend.
