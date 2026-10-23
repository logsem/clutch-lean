# Integration into Metrology

The assembly FFI prototype is part of the Metrology repository on branch `risc`.
It was imported from sibling commit `042e17d`; the original sibling checkout is no longer required.
At the initial integration, all 182 imported Lean source files were byte-identical to that checkpoint.
The later file organization groups modules by responsibility and extracts shared example helpers;
final theorem names and statements are preserved. See `MetrologyAsm/README.md`. The theorem statements,
proof bodies, generated architecture, runtime compatibility shim and strict binder checks are preserved.

Repository layout:

- `MetrologyAsm/` and `MetrologyAsm.lean`: Sail adapter, ABI, plain specs and final example proofs.
- `RiscvZkvm/Sail/`: pinned generated architecture and explicitly owned platform hooks.
- `runtime/lean-sail/`: pinned local runtime, including the documented compatibility suffix.
- `sail-import/`: source/config/runtime hashes and strict binder metadata.
- `Tests/`: Sail observations, source-equivalence checks and executable keypair metadata check.
- `fixtures/keypair/`: linked assembly, helpers, notices and reproducible quotation generator.
- `docs/asm-ffi/`: evaluation, keypair frontier, regeneration and provenance reports.

Run from the Metrology root:

```sh
lake build
python3 -I scripts/check-sail-pin.py
python3 -I fixtures/keypair/generate.py --check
```

The default build includes the existing Metrology/widget targets, `MetrologyAsm`, and the Sail,
strict-binder and keypair regression targets. `lake build MetrologyAsm` builds only the assembly
library and its dependencies. Lean clients use `import MetrologyAsm`, or import individual examples.
No path dependency points outside this repository, and the existing git dependency pins are unchanged.
Both `autoImplicit` and `relaxedAutoImplicit` remain false. The legacy do option remains restricted to
`RiscvZkvm.Sail.RvfiDii`. Only the imported libraries use the prototype's larger Lean stack limit.

The evaluation reports retain historical sibling branch/checkpoint and build measurements.
They describe the same proof sources; current source paths are relative to the Metrology root.
The runtime's dependency-free Lake manifest is generated locally to make fresh root updates clean;
it does not modify upstream runtime source. Architectural and runtime pin checks continue to pass.

Validation in the integrated repository:

- Complete root `lake build`: **7126 jobs passed**; receipt in `audit/BUILD.txt`.
- Source/config/runtime pin checker and fixture quotation/hash check: passed.
- Existing git dependency manifest entries unchanged; module search path has no sibling checkout.
- At initial integration, all imported Lean files were byte-identical to the sibling checkpoint.
- Seven top theorem axiom checks and complete statement-dependency receipts are in `audit/`.
- The only build warnings are the existing unrelated RandomWalk admission and preserved upstream
  Sail ambiguous-open warning. Neither affects the final example theorem axiom closures.
- Whitespace findings in imported generated files and the original authorship notice are preserved
  verbatim. Integration-owned config/docs/scripts are whitespace-clean.

## Module organization

The later organization groups the machine rules under `MetrologyAsm/Sail/` and `Profile/`,
the foreign-call interpretation under `ABI/`, and the programs under `Examples/{Swap,Callback,Keypair}/`.
`Diagnostics/` contains the executable spike and the small instruction-body experiment. The literal
swap source moved from `Metrology/ProbLang/Asm/Examples.lean` into `Examples/Swap/Source.lean`.

Shared decoder effects, return decoding, instruction-state helpers and concrete witness fixtures
were extracted from swap-specific modules. The callback example no longer imports swap proof files.
The decoder helper is now `decode_ret`; shared concrete fixture helpers are `witnessPlacement`,
`witnessRegisters` and `witnessRegisters_config`. Final theorem names and statements are unchanged.
Focused imports are `MetrologyAsm.Examples.Swap` and `MetrologyAsm.Examples.Callback`.

The reorganized complete default build passes **7132 jobs**. Both refreshed statement receipts
retain exactly the previous counts (M1 831/2023/41; M2 832/2031/42), with no missing bodies/ranges;
all seven top theorem axiom closures remain the standard three. Source hashes and file pointers
in the receipts now refer to the organized modules. `audit/BUILD.txt` is the current build receipt.
