# Assembly FFI prototype — evaluation report

**Integrated into Metrology on 2026-10-23.** The Sail layer, examples, tests, pinned runtime,
fixtures and audit scripts now live in `/home/agent/Metrology` on branch `risc`. All source paths
below are relative to that repository root. No sibling checkout is required. Companion reports
are in `docs/asm-ffi/`. The original proof-development checkpoints/build measurements below are
historical; the current integration commands and checks are in [README.md](README.md).

The combined Metrology root build passes **7,132 jobs**. Source/runtime pins and fixture checks pass;
current theorem axiom and statement-dependency receipts are in `docs/asm-ffi/audit/`.
See [INTEGRATION.md](INTEGRATION.md) for the migration and validation details.

## 1. Summary

- M0: Lean 4.35 foundations and scoped Sail builds pass; pinned regeneration is byte-identical.
- M1: **proved**: `MetrologyAsm/Examples/Swap/Correctness.lean:95`, `wp_swap_spec`, has no execution/evaluator premise.
- M2: **proved**: `MetrologyAsm/Examples/Callback/Correctness.lean:26`, `wp_importToy_spec`, executes a Sail callback round trip.
- M3: callback implementation and byte safety/law exist; keypair correctness and product uniformity do not.
- M4: complete statement audits: M1 831 definitions/types, 2,023 lines, 41 modules; M2 832/2,031/42.
- Audited M1/M2/core/callback proof closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
- Scope is the pinned **RV64IM** extraction/profile, not RV64GC or compiler correctness.

## 2. Key prototype question: interaction trees over Sail and the review surface

The generated architecture is not given an FFI instruction or an interaction-tree monad.
`MetrologyAsm/Sail/Execution.lean:19–38` runs the original `try_step 0 false` and inductively executes while PC
lies inside the assembled text. On the first PC outside that text, `MetrologyAsm/ABI/Interface.lean:200` decodes either a return
address or an imported function address. Other exits cannot satisfy the observation contract.
Imports are implemented in ProbLang; Sail never executes their external addresses. `RVResume`
(`MetrologyAsm/ABI/Interface.lean:231`) relates a paused state to a resumed state with the reply register, return PC, footprint
bytes, profile and frame requirements. It is not an added Sail transition or hook.

The inductively defined interaction tree specifies these stopping runs. `FollowsFrom` retains
the original entry machine throughout callbacks. The evaluator selects a unique canonical tree only
when a compatible entry exists. The ProbLang dispatcher snapshots the entry, invokes the ordinary
callback inside `Exp.asmResume`, then re-evaluates and replays the archive to select the continuation
using the callback's **current** footprint. The actual foreign kernel is `primStepWith env`;
`wpFor (primStepWith env)` is the shared guarded Micrometer WP, not a second unguarded logic.

M1 connects the actual GNU source, assembler words, official Sail decoder, arbitrary compatible raw
states, plain `RVSpec`, nonvacuous evaluation, and ordinary points-to ownership. Its public statement is:

```
l ↦ old(l) ∗ k ↦ old(k)
  ⊢ wpFor (primStepWith env) L E (asm swapCode [loc l, loc k])
       (fun result => result = unit ∗ l ↦ old(k) ∗ k ↦ old(l))
```

The pure hypotheses are `env.machine = rv`, distinct logical cells, and signed-64 representability of
the two values. Compatibility quantifies physical code/data bases, initial frame contents, unused
registers and unrelated permitted CSR values. `MetrologyAsm/Examples/Swap/Witness.lean:238` proves compatible entries exist;
this is not merely a specification over an empty set of machines or one initialized test state.

The generic one-import fixture (`Metrology/Micrometer/AsmImports.lean:258`) exchanges one logical
byte cell from 11 to 22 and returns seven. It is an abstract machine fixture using the real dispatcher.
The separate **actual Sail** toy preserves ra on a 16-byte stack frame, calls `cb`, and returns its
signed-64 reply. It has no arguments and an empty logical footprint, so it does not exercise a Sail
callback exchanging an array. Raw seven-step entry and arbitrary-resumed-state three-step return,
image/layout bridges, and universal `importToy_rvspec` are proved. `MetrologyAsm/Examples/Callback/Witness.lean:170`
supplies a compatible entry; `MetrologyAsm/Examples/Callback/Evaluation.lean:12` closes unique evaluator selection.
`MetrologyAsm/Examples/Callback/Correctness.lean:26`, `wp_importToy_spec`, proves return of seven under the shared WP with
no remaining evaluator, transition, specification or continuation premise. Every valid signed-64
response and arbitrary allowed resumption is covered by the plain specification, restoring the
original ABI frame. The particular ProbLang callback returns seven. Both final top theorems are
exported by `MetrologyAsm.lean`; the primary default build passed 3,605 jobs.

### Answers to the six Sail questions

1. **Undefined values and determinism.** `Sail/ConcurrencyInterfaceV1.lean:9–25,101–110,132–157`
   supplies a configurable `ChoiceSource` in an `EStateM` state. The selected `trivialChoiceSource`
   deterministically returns false/zero/empty defaults. `Mach` is `SequentialState RegisterType
   trivialChoiceSource`; registers are an `ExtDHashMap`, byte memory an `ExtHashMap Nat (BitVec 8)`.
   `runSail` returns `Option (value × Mach)` and discards errors. `rvStep` is a function: it accepts
   `some (false,s')` from `try_step` and rejects errors/waiting results. `RunsTo.agree/unique` prove
   common/unique terminal states for terminating runs. No nondeterministic successor relation is assumed.

2. **Initial user configuration.** `MetrologyAsm/Profile/Config.lean:41–70` defines an open `UserConfig` with every register
   present, active hart, User privilege, RV64 I/M/U/S bits, C disabled, SXL/UXL=64, MPRV=0, bare satp,
   disabled pointer masking/CFI, mie=0, and inhibited retirement counting. The first PMP TOR entry
   grants rwx below 4 GiB. A first PMA main-memory region covers `[0x80000000,0x100000000)` and traps
   misaligned loads/stores. Trap vectors are direct and separated from code/return/import stops by F12.
   Other policy-allowed values remain open. `MetrologyAsm/Profile/Witness.lean` constructs a 176-register witness;
   `UserRules`, `GuardRules`, `FetchRules`, and `MemoryRules` discharge actual generated checks.
   This answers the scoped RV64IM question; no RV64GC/FP profile theorem is supplied.

3. **Lean/runtime compatibility and cost.** Lean is 4.35.0; upstream lean-sail is pinned to
   `079463134b9c50450b8393e1566a09fc492a34d9` (upstream toolchain 4.33.1). The supported 85-module
   extraction root closure builds strictly with both implicit-binder options false. A historical first
   model build took 1m49s/1.53 GiB; regenerating and freshly strict-compiling the supported candidate
   took a 57.48s first pass followed by 2m53.59s for the remaining closure, peak 1,673,304 KiB.
   Compatibility is scoped: 22 of the 36 dormant files fail the stronger all121 scan (47 omitted-binder
   declarations in 21 files, plus DeviceTree's reserved `prefix` binder). No all121 success is claimed.
   See [REPORT-REGENERATION.md](REPORT-REGENERATION.md) for the exact inventory.

4. **Proof automation.** An ADDI-body equation is `rfl`; legacy `mvcgen` proves a small body triple
   after primitive unfolds. The newer `vcgen` did not determine the SailM type in that experiment.
   Full `try_step` proofs required reusable register, profile, interrupt, translation, PMP/PMA, byte
   memory, fetch and decoder lemmas, then instruction composition. `SwapSteps` and `InstructionRules`
   cover the five swap steps with no remaining execution-equation premises. Extensional map/bit proofs
   were material work; executable `#eval` observations were useful tests, not universal proofs.

5. **Size of the layer above Sail.** The complete M1 receipt is
   `docs/asm-ffi/audit/TCB-swap_problang.json` in Metrology. The audit starts from
   `wp_swap_spec`'s **type**, follows definition bodies and declaration types, and excludes proof bodies,
   core/Mathlib/iris-lean/runtime/generated architecture. Private bodies and source ranges are resolved;
   the receipt reports no unavailable bodies or missing ranges. Its classification is:

   | Statement dependency class | Modules | Definitions/types | Referenced source lines |
   |---|---:|---:|---:|
   | Shared language, Iris and WP machinery, existing and new | 27 | 403 | 953 |
   | Assembly syntax, assembler, parser types and source example | 4 | 213 | 448 |
   | FFI semantics, boundary checks, capture, dispatch and replay | 5 | 149 | 325 |
   | RV adapter, facets/profile and memory helper definitions | 4 | 59 | 290 |
   | Handwritten platform hooks | 1 | 7 | 7 |
   | Total | 41 | 831 | 2023 |

   Thus the referenced adapter/facet/FFI surface corresponding to Sail-layer items 3–5 is 615 lines,
   208 definitions/types, nine modules. These are source-range unions per module, not total file sizes
   or a proof-code census; generated constructors/matchers are included in declaration counts.
   The installed extraction/support tree separately has 121 Lean files and 60,211 lines; a modifier-aware anchored
   source scan finds 3,215 `def` and 172 `abbrev` declarations, not a kernel declaration census.
   Lean/compiler correctness, C compilation, quotation/elaboration and source intent are outside this
   statement-closure audit. Concrete LLVM byte comparisons and Sail decoder proofs do not establish a
   general verified parser/assembler. No M3 theorem exists to audit. Actual M2's complete receipt is `TCB-sail-import.json`:
   832 definitions/types, 2,031 lines, 42 modules. Its corresponding classes are shared language/WP
   402/950 (27 modules), assembler/source 212/450 (four), FFI 149/325 (five), RV adapter
   59/290 (four), hooks 7/7 (one), and callback/environment statement definitions 3/9 (one).
   `docs/asm-ffi/TCB.md` lists every module and compares the traversal with MachCSL's audit.

   A credible further reduction is to centralize encoding/placement policy and generate routine ABI
   projections with checked equalities. Generated syntax constructors already account for much of
   the declaration count. No smaller adapter/facet/replay implementation has been demonstrated here;
   proof-script size and this semantic review surface are different measurements.

6. **Regeneration and short-circuiting.** Actual generation succeeded using the verified official Sail
   0.20.3 aarch64 binary, not opam or downloaded build scripts. Sail revision is
   `60695b1ea377048f0adc39c62671cd099b2ed9f6`; sail-riscv 0.13.1 is
   `27224ccb2290f022e46213c05b3e72e8a9ea635e`. Manual compiler invocation took 5m56.03s,
   peak 496,248 KiB. Existing audited normalization and supplied hand-owned adapters produce a candidate
   byte-identical to the installed tree. The pinned backend lacks `short_circuit_to_if`; the known
   effectful Boolean RHS fix is **unpatched**. Independent Lean tests execute RHS effects in both
   `false && (← side())` and `true || (← side())`. No reachable ISA counterexample is claimed proved,
   but byte identity does not repair or discharge this compiler defect. Exact pins, command, hashes,
   warnings, candidate build and original-type/body certificate results are in the regeneration report.

## 3. Design deviations and statement changes

These are explicit limits or corrections, not implicit weakenings of advertised results:

| Decision or change | Actual implementation and reason |
|---|---|
| Package layout | The original D16 sibling package is now integrated into Metrology at the owner's request; Lean module names and proof sources are unchanged. |
| RV64GC target narrowed | The pinned extraction and proofs support the RV64IM integer path with Zicsr-related configuration; C/A/F/D instruction coverage is absent. No GC claim. |
| Explicit FFI kernel beside the base kernel | Base `headStep/primStep` leave foreign redexes stuck. `headStepWith/primStepWith env` and the same guarded `wpFor` supply FFI behavior; existing `wp` remains its exact base specialization. No opaque global environment. |
| First-order code/archive representation | Code is countable syntax; `Replay` stores scalar args, integer snapshots and completed responses. Function-valued trees/Val payloads are not inserted into Exp. Snapshots sort logical locations without ordering physical addresses. |
| Import signatures | Imports use first-order `CallSig`, not recursively nested signature/import tables; duplicate import names are rejected. |
| Offset and block typing | `+ₗ` is operationally defined but untyped: the old reference type and arbitrary location bijections do not justify arithmetic. General allocN is untyped because nonpositive lengths are stuck. The original fundamental theorem is retained. |
| Unowned memory | F11 preserves it but does not allocate it. Absent bytes can fault; an always-readable over-read premise was not added. |
| fflags/FP | The current configuration frame preserves all of fcsr, rather than leaving fflags open. This is sufficient only for the current non-FP scope. |
| Pointer results | Footprint candidates are tried first, followed by one-past endpoints. This deterministic policy can be ambiguous across adjacent physical regions; a general inverse/renaming result is not proved. |
| Origin-preserving callbacks | `FollowsFrom` retains the original ABI entry across resumptions. Resetting the frame anchor at each callback was a semantic bug and was corrected before the final M1 gate. |
| Global lawfulness | No global `rvLawful.resume_nonempty` is supplied. Return-only and one-call evaluator lemmas use the proved run/exit laws and only the local resumption existence needed by their statements. |
| GNU syntax scope | Supported fragments parse verbatim; arbitrary GNU syntax, GOT/writable relocations, numeric local-label references and C/F/D/atomic encodings are not supported. LLVM comparison is a test, not compiler correctness. |
| Model/runtime boundary | Generated architectural source is unchanged. The original three-line runtime-root import prefix is preserved with an appended 132-line hand-owned compatibility suffix. Platform-hook implementations are separately owned and audited. |
| Logic coverage | No arbitrary-tree `wp_asm_tree`, TotalEris FFI rule, generic FFI adequacy theorem or logical-renaming theorem is claimed. |
| Keypair precondition | Public and secret 32-byte regions must be disjoint: the signature's permitted identical-region alias would otherwise overwrite the promised unchanged secret. Two fresh allocations suffice. |

The keypair function `f : Bytes32 → Bytes32` must be selected before physical placements/raw states and
callback responses; choosing a fresh f separately per physical execution would evade the intended goal.
The proposed reusable statement chooses f independently of unrelated logical heaps too. Neither that
shape theorem nor identification with TweetNaCl scalar multiplication is proved.

The runtime suffix is an exact closed module/declaration/kind whitelist, not free-variable inference:
82 frozen original type/body certificates prove equality by `rfl`. Unknown declarations still use
strict elaboration. Only RvfiDii uses the supported legacy-do option for its pathological print routine.
`check-sail-pin.py` checks the untouched runtime prefix and exact appended suffix separately. The
architectural digest is `559bb257093328400e5b47722b0bb8dd004396a8b8c45e32ecaefaa79256d992`,
using preserved `sail-import/RiscvExtras.upstream.lean.txt` for the original hand-owned Extras entry.
Installed `RiscvExtras.lean` deliberately supplies explicit platform definitions: I/O, entropy and
reservations reject/return false, cancellation is a no-op, experimental extensions are false.
It is not silently counted as unchanged upstream architectural semantics.

## 4. The fourteen open questions

1. **Regeneration:** performed successfully with the pinned binary and original release source. Opam
   was unnecessary and not run. RV64GC and the unpatched short-circuit defect remain limitations.
2. **Unowned memory readable:** not guaranteed. Memory is partial; only required code/owned/stack bytes
   are allocated by compatibility. Masked libc over-reads need an additional allocation/readability
   argument before their universal specs are justified.
3. **Code-dependent pointers:** no code-pointer boundary value was added. A vtable/code address outside
   the footprint/endpoints cannot be decoded as a logical pointer; such a claimed return has no valid stop.
4. **Logical renaming:** unproved, as allowed outside M1–M3. Sorted snapshot enumeration is not an order
   condition on physical embeddings, but neither it nor the offset operator proves equivariance.
5. **Divergence versus stuck:** terminating `RunsTo` is inductive; nontermination has no finite tree.
   A failed valid-call evaluator yields a stuck zero kernel. Invalid boundary checks instead reduce to
   `fail`; neither produces a returned output. Adequacy for the FFI kernel remains separate work.
6. **Reals:** excluded structurally by `BoundaryValue = int | loc | unit`; closures likewise do not cross.
7. **Function-valued tree uniqueness:** resolved generically by canonical invalid branches, functional
   extensionality and nonvacuity; the local one-call extension avoids an unproved global RV resume law.
8. **Aliasing:** identical compatible regions are permitted and partial overlaps rejected. Keypair needs
   the stronger explicit disjointness condition above. The proved swap requires distinct cells.
9. **Stack bound:** `Sig.stackBound : Nat` is implemented; F8 reserves aligned allocated stack bytes.
   The import toy declares 16; the statically computed keypair depth is 2,080, not yet proved safe.
10. **Signedness:** both `int w` and `uint w` exist, as do signed/unsigned array element kinds; widths
    are bits. The randombytes array has 32 logical eight-bit cells, not 32 machine words.
11. **Where the environment enters:** explicit `FfiEnv rT = {machine, impls}` in the new kernel,
    carried into shared `wpFor`. Existing base examples keep their old APIs and compile.
12. **fflags at exit:** unchanged with all fcsr in the current frame; opening flags and proving FP
    compatibility is future RV64GC work, not already implemented.
13. **Compressed instructions:** none are emitted. Compiler comparisons use Zig/LLVM with
    `-mcpu=baseline_rv64-c -mno-relax`; all current emitted instruction words are 32-bit.
14. **One-past pointers:** accepted and represented as logical `base + length`. Physical decoding uses
    footprint-first/endpoints-second lookup and may have multiple logical candidates. General
    placement-independent pointer-result correctness needs a sharper ambiguity policy or premise.

## 5. Uniqueness in practice

Without canonical invalid branches, two continuation functions can agree on every valid response yet
differ elsewhere. Extensional equality of entire interaction trees then fails. Canonicalization fixes
all invalid responses to the same invalid tree; `Spec` alone still does not imply unique evaluation
when compatibility is empty, so `Evaluates` explicitly includes a compatible-entry witness.

The global uniqueness theorem uses run agreement, exit determinism and resumption existence. M1
does not need a callback law: `eval_ret_eq_some` uses only the return-specific laws. The one-call
theorem in `Metrology/ProbLang/Asm/OneCall.lean` aligns a common pause, chooses a common resumed
state for each valid reply, identifies return branches, and uses canonicality for invalid replies.
It needs local resumption nonemptiness only for that code and observed callback, not a global axiom.

The original entry also matters independently of extensionality. `FollowsFrom origin current`
(`Semantics.lean:103`) holds origin fixed through every callback so exit frames are compared with the
original ABI entry. The earlier current-entry recursion would have lost this guarantee. A regression
fixture pauses inside a frame and returns against its original anchor; the full M1 build was rerun
after this correction. General arbitrary-tree RV evaluation remains beyond these proved local cases.

## 6. Proof effort and measured limits

The table reports selected **current source lines**, including comments/statements/proofs, not a net
diff, additive work accounting or person-hours. Historical cached build timings are identified;
no isolated timer is invented for a workstream that was not measured separately.

| WS | Selected source/review scope | Measured check or frontier |
|---|---|---|
| 0 | Toolchain/config/lockfiles; no isolated proof LOC | Lean 4.35; final root strict/export build passed 6,976 jobs. |
| 1 | Sail/Config/ConfigWitness: 281 lines | First model build 1m49s/1.53 GiB; concrete ADDI/swap observations checked. |
| 2 | HeapArray/Array/array tests: 176 lines; integrated change 682 insertions/45 deletions in 24 files | Full array-stage library build 3,884 jobs/2m50s; both interpreters exercised. |
| 3 | Syntax/Parser/Assembler/Notation/Examples: 803 lines | Swap and AES linked bytes match LLVM; whole TweetNaCl quotation/assembly accepts 2,894 instructions/11,576 text bytes. |
| 4 | Semantics/Boundary/Execution/Capture/Step/Measurable/Fragments/OneCall: 1,344 lines | Fallout gate 3,888 jobs/1m20.331s; final integrated strict root gate 6,976 jobs. |
| 5 | Sail/Config/RV/RVProofs/RVResume: 628 lines | Universal facets, run/exit laws and local resume construction; no separate total timer. |
| 6 | Ten register/profile/memory/fetch/instruction helper modules: 1,657 lines | Memory target 97 jobs/3.4s; complete generated swap steps proved. |
| 7 | ProgramKernel/KernelWp/Asm/AsmImports/HeapFragment: 1,038 lines | Generic one-import target 3,451 jobs; actual-Sail conditional import module 176 lines/~5.8s scoped compile; closed callback WP 34 lines. |
| 8 | Swap/Bridge/Specification/Witness/Evaluation/Micrometer: 1,006 lines | Actual M1 target 3,574 jobs and default package 3,585 jobs passed; elapsed totals not separately retained. |
| 9 | Callback plus durable tests: 231 lines | 80 dual-interpreter array/frame cases + three empty-heap cases, six standard-axiom guards. No curve/product theorem. |
| 10 | TCB metaprogram + source audit script: 189 lines | Complete M1 and M2 JSON receipts; 831/2,023 and 832/2,031 declarations/referenced lines. |
| 11 | Three regeneration scripts, 3,567-line equality fixture, 135-line runtime root: 3,962 lines | Generation 5m56.03s; supported85 strict closure; all121 failure inventory completed. |

Actual M2 additionally has 843 source lines across Specification/Evaluation/Correctness/Frames/
Observation/Boundary/Image/Placement/Witness (including comments and proofs). Its final correctness
target passed 3,586 jobs; the coherent primary default gate passed 3,605. These are job counts,
not wall-time measurements or additive proof-effort estimates.

The required upstream alternative was actually inspected at riscv-zkvm revision
`6810fc14d9c40373101321cefaec59df8d82e3e7`: 51 primary instruction equivalences, plus separate step
and presence wrappers. `sailStep_run_sim` executes a supplied decoded instruction plus PC/tick;
its Machine-mode/PMP-off RunInv and toy AST code stream do **not** simulate actual user `try_step`
fetch/interrupt/decode. Its bounded-loop logic is useful design material but not a ready-made bridge
to this RVSpec. [REPORT-SAIL-EQUIV.md](REPORT-SAIL-EQUIV.md) gives exact premises and source lines.

The proof cost per instruction is dominated initially by shared profile/fetch/memory infrastructure;
the five-step swap does not justify multiplying a constant per-instruction estimate for larger code.
No loop RVSpec was completed, so there is no measured universal per-loop elaboration cost.
Early SAT `bv_decide` experiments introduced custom native axioms on this toolchain; final proofs use
kernel-checked extensional bit/map lemmas and `bv_normalize` preprocessing instead.

For keypair, actual static linkage and quotation were attempted: eight reachable functions, 847 source
instructions, 882 emitted instructions, 3,528 text bytes, 30 backedges and one external `randombytes`.
The 32-byte secret/public result requires all compatible placements and resumed states, owned-array
loop invariants, stack/internal-call contracts and layout-independent output. Source counts imply
3,057 field-multiply calls and 782,592 limb products; one eight-instruction inner loop accounts for
6,260,736 executions under naive unrolling. These are diagnostics, not a certified dynamic counter.
An actual MUL-body control proof took 5.75ms elaboration + 5.19ms checking, 3.11s whole process; its
arithmetic helper remains explicit. No full field arithmetic or curve proof is claimed.

The ProbLang `randombytesValue` exists (`Examples/RandomBytes.lean:33`), with actual primitive uniform
byte law and singleton mass `1/256`, and owned-array byte-safety WP. The WP uses base `primStep`;
transport to `primStepWith env`, the full array product law, arbitrary callback-tree WP/adequacy,
and the keypair shape/functional theorem remain open. The committed `MetrologyAsm/Examples/Keypair/Source.lean` retains the literal linked source, declared signature
and two-allocation game returning `(sk, pk)`; `fixtures/keypair/` contains helpers, hashes, metrics,
notices and a quotation generator. `Tests/Keypair.lean` checks image metadata by execution,
not a kernel execution theorem. Full assembly/image hashes, exact signatures,
the disjointness correction, experiments and failed arithmetic diagnostic are in
[REPORT-KEYPAIR.md](REPORT-KEYPAIR.md). No fake uniform-keypair theorem is substituted.

## 7. Branches and commits

No branch was merged to main. Only explicit owned paths were staged; handoff notes stay uncommitted.

| Original repository/worktree | Branch/checkpoint | Historical meaning |
|---|---|---|
| `/home/agent/Metrology` | `risc`, `d468b15` | Core/FFI/shared WP, origin fix, callback and final strict exports. |
| `/home/agent/MetrologyAsm` | `asm-ffi/prototype`, proof checkpoint `73078e7` | Authoritative integrated M1/M2; source/fixture/default-build checkpoint `9a2cbf9` follows. |
| `/home/agent/MetrologyAsm-rv` | `asm-ffi/rv`, `649d336` | Matching M1/M2 source/proof checkpoint, before final documentation/input synchronization. |

Useful root commits: `c595199` arrays; `03437fa`/`986d5c5` shared kernel/WP; `49bee2b` foundations;
`763cc83` retained-origin fix; `235f2d1` local one-call uniqueness; `4d4b899` randombytes;
`d468b15` strict/export gate. The M1 RV chain is `swap_rvspec → swap_compat_exists → swap_eval →
wp_swap_spec`, with final WP `f001cfe` and exports `0b7c0ef` on the RV branch.
Raw callback source/execution is `c838001` there (source `f18c64a`); image/layout/frame bridges and
`4557de6` boundary characterization follow. Conditional WP is `17bda5d` (source `a102fe7`).
Commit hashes differ across cherry-picks; the cited branch/source must be used together.

M2's universal specification/evaluation/WP are `82e6cdb`/`fb4e40d`/`649d336` on the RV branch;
primary equivalents are `a679380`/`29929fe`/`73078e7`. Input/default-target integration is `35b452e`/`9a2cbf9` on the primary branch. The latter is the
final source/build checkpoint; subsequent report-only commits do not alter it. The RV worker branch
retains its proof checkpoint. These are historical development branches; the authoritative current
checkout is Metrology/risc, with these source trees integrated directly.

Measured artifacts are retained at `/home/agent/asm-ffi-ws9-ws11`; root strict build log is
`/tmp/ffi-final-strict-root.log`. Companion reports pin detailed commands/hashes. The final primary build receipt is
`/tmp/ffi-primary-final-with-keypair.log` (3,605 jobs); final statement/axiom receipts are copied to
`docs/asm-ffi/audit/`. The pin checker and strict source-equivalence checks pass.
Only preserved upstream Sail ambiguous-open warnings occur in the sibling gate; root also retains
the pre-existing unrelated RandomWalk admission. Neither top result depends on that admission.

## 8. Recommended next steps and production cost

1. **Extend the demonstrated callback boundary to arrays.** The actual Sail toy uses an empty
   footprint; the separate abstract callback fixture exchanges a cell. Prove a Sail callback with an
   owned byte array and an ordinary sampler implementation before tackling the full keypair closure.
2. **Settle the architecture/adequacy boundary.** Add a general finite-tree WP rule and an adequacy
   theorem for the explicit kernel, then port sampler/heap rules or prove a justified ordinary-code
   transport. Prove only needed local resume existence or finish a genuinely global law. Resolve
   pointer ambiguity and the allocation policy for permitted libc over-reads before extending claims.
3. **Repair and review the compiler backend.** Regenerate an isolated candidate with the effectful
   short-circuit fix, inspect differences, update provenance deliberately, and rerun proofs. Do not
   silently replace the pinned model. Keep exact whitelist/type/body checks; dormant generated modules
   should be fixed only when expanding the supported closure.
4. **Build loop/procedure arithmetic contracts for keypair.** Prove bounded limb-array access,
   carry/packing/inversion/ladder invariants and libc contracts, then output independence from placement
   and frame. Prove the randombytes product distribution and finally compose the game. Decoding and
   printing the whole source do not replace these obligations.
5. **Broaden only after the scoped pipeline is sound.** Add logical-renaming results, automated
   instruction/CFG verification and CI matrices, then separately budget RV64GC/FP/compressed/atomic
   semantics and ABI support. Timing, constant-time security and C compiler correctness remain outside
   the present mission.

Planning estimates, not measured labor: hardening the RV64IM tree/adequacy/profile/automation boundary is roughly
2–6 engineer-weeks; the keypair loop/field layer another 4–12 specialist engineer-weeks, and sampler/game
composition 1–3 weeks once that infrastructure exists. These overlap and are uncertain; a production
quality verified RV64IM keypair pipeline is plausibly a 3–6 engineer-month project. RV64GC/general-C
coverage has no justified fixed upper bound from this five-instruction experiment. These planning
estimates have not been calibrated against measured human labor.

## 9. Five files to inspect first

1. `Metrology/ProbLang/Asm/Semantics.lean:36,103,125,164` — the interface, original-entry recursion,
   nonvacuous evaluator and law assumptions; inspect `OneCall.lean` alongside its local uniqueness rule.
2. `MetrologyAsm/ABI/Interface.lean:120–256` — code range, ABI/profile/frame facets, deterministic observation and
   resumption; `Sail.lean:19–38` is the short actual-model execution adapter.
3. `MetrologyAsm/Examples/Swap/Correctness.lean:95` — the final ordinary two-cell M1 WP; follow its evaluator,
   witness and plain specification rather than the concrete smoke fixture.
4. `Metrology/Micrometer/Asm.lean:28,67` — the actual guarded finite-fragment exchange and shared-WP
   bridge, including the distinction between exact evaluation and globally lawful semantics.
5. `MetrologyAsm/Examples/Callback/Correctness.lean:26` — the unconditional actual-Sail callback WP; follow
   `MetrologyAsm/Examples/Callback/Evaluation.lean` and `MetrologyAsm/Examples/Callback/Specification.lean` for evaluator selection and arbitrary resumes.
