# Uniform sections and clock-birth injectivity for Rule30 positive words

This bundle contains two reusable structural lemmas for the literal
older-first Rule30 automaton, with products acting right to left and sections
indexed by input:

* `common_sections`: positive words of the same length n have literally equal
  section words on every input of length at least2n.
* `birth_sections_injective`: if equal-length positive words both flip the
  root, equivalence of the zero-sections of their squares forces the words
  themselves to be equal.

The supporting `run_drop_common` theorem proves equality of output tails
after2n input bits. The proofs use symbolic list induction, the two-bit
memory reset, and the existing positive-word freeness theorem. The exact
definitions and `act_memory` bridge to the Rule30 xor/OR scan are preserved.

**Neither single-response faithfulness nor full-white-orbit faithfulness is
proved. No physical Problem1 bridge is supplied.** The hypotheses in the
birth theorem require equivalence on ALL finite inputs, not just equal
outputs or equal orbits from white. Genuine least-clock coalescence and
finite-white plateau cancellation are not formalized in this bundle.

## Sources and evidence

The five included sources are the two official Ruliology dependencies at
commit`7d665044b904117af9e82328aeb90a30692b2b85`, the two unchanged positive
automaton modules, and the new Rule30PositiveSectionsResearch module.
`SOURCE-MAP.json` and `INPUTS.json` record exact hashes and roles.

The current validation freshly compiled all five sources into an empty
library directory, then ran the unchanged official checker on all three
research modules:

| Research module | Constants replayed | Headlines |
|---|---:|---:|
| Rule30PositiveAutomaton |153|5|
| Rule30PositiveAutomatonBounds |16|3|
| Rule30PositiveSectionsResearch |27|3|
| Total |196|11|

The new module contains13 source theorems and one helper definition; the
27-constant count includes generated constants. All source builds had zero
warnings. All full replays and printed type comparisons passed, with no new
axioms. The unchanged checker's own `Lean.Environment.replay` deprecation
warning is preserved in its raw stdout; checker logs are not warning-free.

`evidence/current7d` contains the fresh current-pin receipts.
`evidence/author5473` separately preserves the earlier author's successful
5473 replay; it is not relabeled as current-pin evidence. Current raw checker
logs, author raw mathematical JSON lines, and all type logs are unchanged.
Author stdout copies replace only the private absolute filename prefix at
the checker warning; they are explicitly named and labeled as redacted,
preserve all warning text, and record the original raw stdout hash.
Resource-only guard extracts identify their omitted private command field
and the SHA256 of the original raw receipt. No binary, account, credential,
or remote-execution data is included.

## Reproduction

Requires Lean4.35.0 and the Mathlib libraries pinned by the included Lake
metadata, already available. The verifier does not install dependencies or
access a network service. With a prepared Lake environment, run:

```text
lake env python verify.py
```

Alternatively, use existing compatible libraries directly:

```text
python verify.py --lean /path/to/lean --library-path /path/to/built/libraries
```

Repeat `--library-path` for multiple library directories if necessary.
The script validates input hashes, creates a fresh owned library, compiles
all five sources, checks all196 research constants and11 headline types,
and compares the printed types with the author receipts. It writes a new
receipt directory under `verification-output` without overwriting supplied
evidence. The validated run reused existing pinned Mathlib/toolchain
libraries; it was not a cold dependency-package rebuild.

`Check.lean` is unchanged, with SHA256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
`.gitattributes` preserves exact source and receipt bytes in Git.

Prepared for Troy Lowry with AI assistance. This is a research helper bundle,
not a prize submission or a claimed solution to a Rule30 Prize problem.
