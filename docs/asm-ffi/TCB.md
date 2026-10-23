# WS10 / M4: statement dependency audit

The M1/M2 sources are integrated on Metrology branch `risc`, imported from sibling checkpoint
`042e17d`. The receipts in `docs/asm-ffi/audit/` are regenerated against this repository.
Both are complete: no unavailable owned bodies or unresolved source ranges. Axiom closures are
exactly `[propext, Classical.choice, Quot.sound]`; see `audit/AXIOMS.txt`.

`Metrology/Meta/TCB.lean` starts at a theorem's type, follows declaration types and non-theorem
bodies (including inductive constructors), and excludes theorem proof bodies. The Python driver
loads private data in legacy import mode and resolves generated declarations to their owning source
ranges. Counts below are referenced non-proof declarations/types and unions of source lines per
module, including comments within declaration ranges. They are not total file sizes or proof LOC.
Core/Std/Mathlib/iris-lean/lean-sail/generated architecture are excluded from this owned-layer table.
Handwritten Sail platform hooks are explicitly included. Full declaration names, paths and SHA256s
are in the JSON receipts; this is the compact per-module list.

| Class | M1 modules/decls/lines | M2 modules/decls/lines |
|---|---:|---:|
| Shared language/logic | 27/403/953 | 27/402/950 |
| Assembler/source | 4/213/448 | 4/212/450 |
| FFI semantics | 5/149/325 | 5/149/325 |
| RV adapter/facets | 4/59/290 | 4/59/290 |
| Platform hooks | 1/7/7 | 1/7/7 |
| Callback/statement | 0/0/0 | 1/3/9 |
| **Total** | **41/831/2023** | **42/832/2031** |

The shared class combines pre-existing ProbLang/Iris resources with additions to shared syntax and
WP; these are mixed files, so this classification does not invent a clean historical LOC split.
The five FFI modules are new semantics/boundary/dispatch/capture/replay. RV covers the actual step,
RunsTo, decode, facets, open UserConfig and memory helper definitions. Assembler/source includes
label resolution, pseudo expansion, placement/import slots and literal source statement values.
The actual M2 callback/environment/expression definitions add nine lines. `randombytes` is absent
from both top statements; there is no M3 theorem to audit. Its implementation and safety theorem
are separately identified in WS9 and REPORT-KEYPAIR.md, not presented as a keypair dependency cone.

| Module | Class | M1 declarations/lines | M2 declarations/lines |
|---|---|---:|---:|
| `Metrology.Couplings.BindLaw` | Shared language/logic | 4/32 | 4/32 |
| `Metrology.Couplings.Lifting` | Shared language/logic | 4/35 | 4/35 |
| `Metrology.Couplings.Measure` | Shared language/logic | 1/3 | 1/3 |
| `Metrology.Couplings.SubProbability` | Shared language/logic | 2/8 | 2/8 |
| `Metrology.Iris.AgreeHeap` | Shared language/logic | 1/3 | 1/3 |
| `Metrology.Iris.AppProgram` | Shared language/logic | 13/27 | 12/24 |
| `Metrology.Iris.SpecProgram` | Shared language/logic | 23/44 | 23/44 |
| `Metrology.Iris.SpecUpdate` | Shared language/logic | 4/9 | 4/9 |
| `Metrology.Micrometer.KernelWp` | Shared language/logic | 3/15 | 3/15 |
| `Metrology.Micrometer.MicrometerWpGS` | Shared language/logic | 11/20 | 11/20 |
| `Metrology.Micrometer.PrimitiveLaws` | Shared language/logic | 7/20 | 7/20 |
| `Metrology.Micrometer.ProgramKernel` | Shared language/logic | 1/14 | 1/14 |
| `Metrology.Micrometer.SpecCoupl` | Shared language/logic | 6/25 | 6/25 |
| `Metrology.ProbLang.Asm.Assembler` | Assembler/source | 72/325 | 72/325 |
| `Metrology.ProbLang.Asm.Boundary` | FFI semantics | 58/126 | 58/126 |
| `Metrology.ProbLang.Asm.Capture` | FFI semantics | 1/6 | 1/6 |
| `Metrology.ProbLang.Asm.Examples` | Assembler/source | 3/14 | — |
| `Metrology.ProbLang.Asm.Execution` | FFI semantics | 33/85 | 33/85 |
| `Metrology.ProbLang.Asm.Parser` | Assembler/source | 2/5 | 2/5 |
| `Metrology.ProbLang.Asm.Semantics` | FFI semantics | 41/70 | 41/70 |
| `Metrology.ProbLang.Asm.Step` | FFI semantics | 16/38 | 16/38 |
| `Metrology.ProbLang.Asm.Syntax` | Assembler/source | 136/104 | 136/104 |
| `Metrology.ProbLang.CoreMeasures.BaseLit` | Shared language/logic | 13/1 | 13/1 |
| `Metrology.ProbLang.CoreMeasures.Cfg` | Shared language/logic | 3/8 | 3/8 |
| `Metrology.ProbLang.CoreMeasures.Discrete` | Shared language/logic | 1/1 | 1/1 |
| `Metrology.ProbLang.CoreMeasures.Exp` | Shared language/logic | 32/1 | 32/1 |
| `Metrology.ProbLang.CoreMeasures.Pat` | Shared language/logic | 11/1 | 11/1 |
| `Metrology.ProbLang.CoreMeasures.State` | Shared language/logic | 1/3 | 1/3 |
| `Metrology.ProbLang.CoreMeasures.Val` | Shared language/logic | 1/3 | 1/3 |
| `Metrology.ProbLang.CtxStep` | Shared language/logic | 3/7 | 3/7 |
| `Metrology.ProbLang.Erasure.ErasableExpr` | Shared language/logic | 1/4 | 1/4 |
| `Metrology.ProbLang.Erasure.Lifting` | Shared language/logic | 2/10 | 2/10 |
| `Metrology.ProbLang.Exec` | Shared language/logic | 10/22 | 10/22 |
| `Metrology.ProbLang.HeadStep` | Shared language/logic | 23/82 | 23/82 |
| `Metrology.ProbLang.Syntax.HeapArray` | Shared language/logic | 3/4 | 3/4 |
| `Metrology.ProbLang.Syntax.Syntax` | Shared language/logic | 219/551 | 219/551 |
| `MetrologyAsm.Config` | RV adapter/facets | 6/58 | 6/58 |
| `MetrologyAsm.ImportMicrometer` | Callback/statement | — | 3/9 |
| `MetrologyAsm.ImportToy` | Assembler/source | — | 2/16 |
| `MetrologyAsm.MemoryRules` | RV adapter/facets | 1/3 | 1/3 |
| `MetrologyAsm.RV` | RV adapter/facets | 43/207 | 43/207 |
| `MetrologyAsm.Sail` | RV adapter/facets | 9/22 | 9/22 |
| `RiscvZkvm.Sail.RiscvExtras` | Platform hooks | 7/7 | 7/7 |

The FFI plus RV class is 208 definitions/types and 615 referenced lines in nine modules for either
result. Seven platform-hook definitions add seven lines. This is the demonstrated semantic review
surface, not a claim that fewer lines are impossible. Centralizing encoding/placement policy and
checked generation of routine ABI projections could reduce duplication; no smaller implementation
was proved here. Syntax-generated constructors account for many declarations.

Separately, the pinned extraction/support tree has 121 files and 60,211 lines, with 3,215 `def` and
172 `abbrev` source declarations under the original anchored scan (not a kernel declaration census).
This includes the original Extras inventory entry, whose installed replacement is hand-owned.
The architectural digest is `559bb257093328400e5b47722b0bb8dd004396a8b8c45e32ecaefaa79256d992`.
Runtime, release revisions, exact source certificates and the unpatched effectful short-circuit
backend defect are documented in REPORT-REGENERATION.md. Neither C/compiler correctness nor
quotation/source-intent correctness follows from this statement audit.

Comparison: xv6iris `tools/tcb/Tcb.lean` and `expected.json` at
`0f273147820d8ea41b56b8dec6164895292c5e6e` also start from statement types, ignore proof bodies,
attribute generated declarations to source owners, and union ranges per module. Their native audit
pins module sets/axioms/opaques in CI; ours emits complete receipts without a pinned CI baseline.
Ours conservatively follows definition types and non-theorem values, including Prop-valued defs,
and can inspect opaque bodies; MachCSL excludes proof-valued definitions and treats opaques by type
only. Its counts therefore cannot be compared numerically without aligning policies. Our missing
range checks are stricter: unresolved owners make the receipt incomplete rather than silently adding
zero lines. A CI baseline for module-set/axiom changes is a useful next hardening step.

Reproduce from the root (Python reads run isolated):

```
python3 -I scripts/audit-asm-tcb.py MetrologyAsm.SwapMicrometer MetrologyAsm.wp_swap_spec \
  --project . --output /tmp/swap-tcb.json
python3 -I scripts/audit-asm-tcb.py MetrologyAsm.ImportCorrectness MetrologyAsm.wp_importToy_spec \
  --project . --output /tmp/import-tcb.json
```
