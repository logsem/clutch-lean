# Durable TweetNaCl keypair input

This is a statically linked **assembly input**, not a verified crypto implementation.
There is no keypair RVSpec, shape/functional theorem, stack-safety proof, product-uniformity
theorem, or game WP in this fixture.

keypair-linked.s retains the reachable TweetNaCl keypair/scalarmult/field functions and the
_9/_121665 constants. It statically includes the separately compiled musl memcpy/memset
bodies. Only randombytes remains external. Helper-local .L labels are alpha-renamed
with their helper name to avoid collisions; other retained function instructions are unchanged.
Functions receive four-byte alignment and constants eight-byte alignment.

The source is canonical here. generate.py escapes it into a multiline riscv_asm! quotation
in MetrologyAsm/Keypair.lean, with one physical Lean line per GNU line. It reads local data
only and invokes no compiler, downloaded script, build system, network client, or shell.

From the sibling package root:

    python3 -I fixtures/keypair/generate.py --check
    lake build MetrologyAsm.Keypair
    lake env lean Tests/Keypair.lean

To regenerate only the quotation/module after a deliberate fixture edit:

    python3 -I fixtures/keypair/generate.py

The generator verifies the pinned fixture hashes before writing or checking the module.
The .s file SHA-256 is
747626b938c4a387551c517ca8ba7a531927b1ac3293ef220aab20b12d3e527c.
provenance.json records original C/assembly hashes, helper compiler arguments, extraction
steps, expected image metadata, and notice origins. metrics.json contains the original data-only
call-graph/frame/backedge assessment; its source_sha256 refers to the whole surveyed TweetNaCl
assembly, not the extracted linked file. No upstream downloads or compiler builds were repeated
when promoting these already measured artifacts.

## Declared contract and measurements

The code entry is crypto_box_curve25519xsalsa20poly1305_tweet_keypair. Arguments are public
key first and secret key second:

    [array 8 (const 32), array 8 (const 32)] -> int 32
    randombytes : [array 8 (arg 1), uint 64] -> unit

The import length index is zero-based and refers to its second argument. Widths are bits.
The declared stackBound = 2080 is a measured maximum of statically summed frame sizes,
excluding execution of the external import. **It is an unproved contract**, not a theorem
that every path is stack-safe. Fresh public/secret allocations avoid the identical-region
alias permitted by the general signature.

The executable regression in Tests/Keypair.lean checks successful assembly, 882 emitted
instructions, 3,528 text bytes, read-only offset 3,528, entry zero, 3,696 total bytes, and exactly
one import slot ("randombytes", 3688). This is a compiler-evaluated diagnostic, not a kernel
theorem or an execution proof. A full closed-image kernel reduction exceeded a 180-second
experiment cap; it is not included in the default build. The surveyed source has 847 instructions in eight functions,
30 syntactic backedges, and 160 constant bytes.

keypairGame is the planned ProbLang skeleton: allocate two 32-cell zeroed arrays, call
keypair with (pk, (sk, ())), discard the C return code, and return (sk, pk). It requires
an explicit FFI environment; its assembly correctness and probabilistic postcondition are
not proved. The existing ProbLang.RandomBytes.randombytesValue is the intended callback,
whose owned-array safety proof currently uses the base kernel.

## Notices

- TweetNaCl's public-domain authorship notice is preserved in AUTHORS-tweetnacl.md, copied
  from the already available Monocypher external-test notice. The original official URL
  and exact surveyed C hash are in provenance.json.
- helpers/memcpy-Os.s and helpers/memset-Os.s are the already compiled musl helper outputs.
  The full available musl COPYRIGHT/MIT notice from Zig 0.13.0 is preserved unchanged as
  LICENSE-musl.txt. No new license is assigned to that code.
- Generated architectural Sail source and runtime code are untouched.
