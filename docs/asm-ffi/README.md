# Assembly FFI in Metrology

Sail-backed assembly FFI examples integrated into Metrology, on Lean 4.35.0.
All source paths and commands below are relative to the Metrology repository root.
There is no sibling-package dependency. The original Lean module names are preserved.

- `MetrologyAsm/Sail.lean`: official `try_step` wrapper and terminating execution to the
  first program counter outside the image.
- `MetrologyAsm/Initial.lean`: concrete user-mode configuration for instruction spikes.
- `RiscvZkvm/Sail/`: pinned official Sail extraction; see `docs/asm-ffi/PROVENANCE.md` for platform
  hook instantiation and the runtime parser compatibility shim.
- `sail-import/PROVENANCE.toml`: upstream extraction/compiler/configuration pins.

Commands:

```sh
lake build
python3 -I scripts/check-sail-pin.py
bash scripts/regen-sail-model.sh --plan
```

The prototype uses uncompressed RV64IM instructions. It does not provide floating-point,
atomic, compressed, terminal-I/O, or hardware-entropy execution. Unsupported platform
operations fail through Sail's error result. Randomness belongs in a ProbLang import.

`Tests/SailSpike.lean` observes one ADDI and the five-instruction swap through the
full fetch/decode/execute `try_step` wrapper. The extraction's explicit
`noncomputable` markers prevent direct `#eval`. The test creates executable aliases
of the original declaration values and proves their equality to the original
wrapper by kernel `rfl`; guarded compiler observations check the concrete outputs.
These observations are smoke checks. Universal assembly correctness requires the
separate plain-Lean specification proof.

The completed proofs are `MetrologyAsm/SwapMicrometer.lean` and
`MetrologyAsm/ImportCorrectness.lean`; the original evaluation is in
[REPORT.md](REPORT.md). The package migration preserves generated sources, theorem statements and
proof bodies. `runtime/lean-sail` is the pinned local runtime; `sail-import` holds hashes/configuration.

[INTEGRATION.md](INTEGRATION.md) describes the root build and directory layout.
[TCB.md](TCB.md) lists the classified statement dependencies; `audit/` contains fresh receipts.
