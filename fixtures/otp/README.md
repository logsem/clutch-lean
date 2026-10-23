# Compiled one-byte OTP input

`otp.c` calls `randombytes(pad,1)` and returns the message XOR the sampled byte. The proof's calling
precondition restricts the uint64 message to [0,256). The caller supplies one private owned byte.
The security game releases only the returned ciphertext and samples a fresh pad for each execution.

`otp.compiler.s` is the complete output of Zig 0.13.0 / Clang 18.1.6:

```sh
zig cc -target riscv64-linux-musl -mcpu=baseline_rv64-c-a-f-d -mabi=lp64 \
  -mno-relax -fPIC -g0 -fno-asynchronous-unwind-tables -fno-stack-protector \
  -fno-builtin -Os -S fixtures/otp/otp.c -o fixtures/otp/otp.compiler.s
```

The emitted architecture tag is RV64I/M/Zicsr. `otp.s` retains the original `.text` directive and the
entire `.globl` through `.size` function block verbatim. The remaining metadata/footer is excluded.
`generate.py` verifies those characters and the hashes in `provenance.json`, then quotes them into
`MetrologyAsm/Examples/OTP/Source.lean`. It reads local data and invokes no compiler or build system.

```sh
python3 -I fixtures/otp/generate.py --check
lake build MetrologyAsm.Examples.OTP.Decode MetrologyAsm.Examples.OTP.Byte
```

The assembler expands the call and its trampoline to twenty 32-bit instructions: 80 text bytes,
88 total image bytes and one randombytes address slot at offset 80. The function reserves 32 stack
bytes and saves ra/s0/s1. Decoder certificates connect every emitted word to the official Sail AST.
These input and arithmetic facts are foundations; the complete execution/security proof is being
implemented according to `docs/asm-ffi/OTP-PLAN.md`.
