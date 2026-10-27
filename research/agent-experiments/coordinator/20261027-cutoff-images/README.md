# Exact cutoff images and primitive-front finite ambiguity

This research bundle proves the complete first and second physical Rule30
images of the catalog's two cutoff examples. It also strengthens the known
all-horizons finite ambiguity construction by requiring both initial rows
to have primitive right front100.

For every cutoff N>=2, including site N, put

    kL = N - ((N+1) mod3),     kR = N - ((N+2) mod3).

The complete first rows are `[-4<=p<=k+1 and p!=-2]`. The complete second
rows are the fixed black set `{-5,-4,-1}` together with one isolated black
at `k+2`. The precise second-image sites are:

| N mod3 | Left example | Right example |
|---|---|---|
| 0 | N+1 | N |
| 1 | N | N+2 |
| 2 | N+2 | N+1 |

All coordinates are physical integer sites. These are function equalities
on the entire row, not finite-window calculations.

For every horizon H, the construction gives two finite rows with the
same left edge -3, different initial cells at -1, primitive front100, and
equal center observations for every t<H. The explicit second-image rows
agree at the center whenever t+2<=N. The cutoff depends on H. **No fixed
finite pair with equal complete infinite traces is proved.** The result
does not refute EdgeObservable, prove a prize problem, or concern only
the single-seed genealogy.

The new source is `Rule30CutoffImagesResearch.lean`. `PAPER.md` preserves
the mathematical input and its caveats. The official `TraceMerge` and
`TraceAmbiguity` modules supply the existing infinite examples, first
images, finite cutoff definition, and causality facts. This contribution
is their exact finite-cutoff image analysis and primitive-front refinement.

## Reproduce

Use Lean4.35.0 and Python3 with Lean already available. No installation,
network service, machine-specific command, or private compiled object is
required. From this directory run:

```text
python verify.py --lean /path/to/lean
```

Or, with the pinned project dependencies already prepared:

```text
lake env python verify.py
```

The actual proof closure is core Lean: it has no Mathlib imports. The
official project's Mathlib pin and package lock are retained for exact
environment provenance; the recorded fresh run used no Mathlib objects.
The checker and all19 source files are bundled. The script creates a new
empty contribution library for each invocation, compiles all18 official
modules and the new leaf in dependency order, replays the entire new
module with the unchanged checker, and compares all nine printed types
and axiom lists against the author receipt. New runs write only under
`.verification-build/` and `verification-output/`.

The official source pin is
`7d665044b904117af9e82328aeb90a30692b2b85`. The unchanged `Check.lean` hash is
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
`INPUTS.json` contains every source hash, topological build order, and all
checker arguments. The nine headlines are:

- `last_sites_mod_zero`
- `last_sites_mod_one`
- `last_sites_mod_two`
- `capped_second_image`
- `cutoff_first_images`
- `cutoff_second_images`
- `cutoff_fronts`
- `arbitrarily_long_primitive_finite_ambiguity`
- `isolated_images_finite_agreement`

Each is qualified by the namespace `Rule30CutoffImagesResearch`.

## Evidence and scope of validation

`evidence/fresh19/` contains the new complete19-source build, raw unchanged
checker output, printed types, and the machine-readable result. The checker
replays all94 new-module constants, including generated constants, and all
nine headlines. The source has16 explicit theorems and five definitions.
No new axioms are admitted; the headlines use the standard `propext`,
`Classical.choice`, and `Quot.sound` axioms.

The19 source builds have zero warnings. The raw checker log deliberately
retains the official checker's `Lean.Environment.replay` deprecation
warning; this bundle does not claim globally warning-free checker output.
The existing pinned toolchain was reused. This is a fresh contribution
source build, not a new compiler or package build.

`evidence/author-targeted/` is distinct earlier evidence: one fresh research
leaf, three missing official modules compiled, and15 exact official objects
reused. Its mathematical JSON and type receipts are byte-preserved. Its
checker stdout has one explicitly labelled filename-only path redaction;
`PROVENANCE.json` records the original hash and precise replacement.
The original warning and mathematical JSON remain unchanged. Both resource
guard extracts omit the private command field and record the original raw
receipt hash. No private paths, account information, execution service
details, or compiled binaries are included.

The preserved author provenance explains three earlier failures: a missing
dependency object, a namespace-overlay setup error, and four integer
arithmetic elaboration goals. No mathematical statement was weakened to
obtain the passing proof. The sealed author bundle was not edited.

Prepared for Troy Lowry with AI-assisted derivation, implementation, and
review. This is a reusable research helper bundle, not a prize submission.
