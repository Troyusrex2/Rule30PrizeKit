# All-width parity conservation for Rule 30 products

**Problem 1 remains open.** This is a uniform negative result about a class
of conservation-law proof strategies, proposed in [PR27](https://github.com/WolframInstitute/Rule30PrizeKit/pull/27).
The source, public import and catalog row are the PR's only three files.

## What is proved

For every positive window width m and any family of Boolean coordinates,
apply Rule 30 independently to each coordinate. Any local mod-two score h
that is conserved by FOUR updates along every closed input walk has exactly
the form

    h(s0,...,s[m-1]) = c + B(s1,...,s[m-1]) - B(s0,...,s[m-2]).

The converse is also proved. In particular there is no additional conserved
mixed-pair parity charge in this class. There is no finite width cutoff and
no supplied-local-current hypothesis: a closed-walk gradient construction
produces the current. The semantics theorem identifies the finite image with
exactly four shrinking coordinatewise Rule 30 updates.

The [core module](work/Rule30ProductParity.lean) uses Fin2 coefficients and no
Mathlib. Its four headlines are `all_ensembles`, `paired_F2_exact`, `paired_F2`
and `paired_F2_semantics`. The [research companion](work/Rule30ProductConservationResearch.lean)
proves the same range descent for arbitrary additive commutative coefficient
groups, including torsion groups, using Mathlib.

The argument extends the earlier [integer scalar descent, PR21](https://github.com/WolframInstitute/Rule30PrizeKit/pull/21).
Arbitrary-length preimages with eight trailing white cells give an endpoint
rectangle identity. Current transport shortens the density. The one-cell
case uses the collapse of a uniform state to white, so it works in
characteristic two without division or ordering. The converse constructs a
current explicitly. No literature novelty is claimed.

## Verification and scope

At verifier pin 0090056412733accaa27643d3cbbf982104f2251, the unchanged official
checker accepts all 207 core declarations and all four headlines with no new
axioms. Cold catalog build plus replay took 13.22 seconds, with 0.90 GB sampled
peak owned RSS. The source hash is
e75ceef148b81aae06eaaed2a8e4eee36039a02e4772027eea0e56a87afa3d4c.
GitHub head/body/files/remote/raw-source readbacks agree at head
e8c90a07b761b08e7738b93d74cd5bf6f0e23c3c.

The 207-declaration research, core catalog and standalone-essay checks are
ports of the same parity proof; they are not counted three times. The
189-declaration arbitrary-group companion is a more general version of the
same argument, not 189 independent new mathematical results. Generated
declarations are included in these compiler counts. The intermediate
135-declaration replay is included in the final companion and is not added.

The theorem concerns translation-invariant finite-window cyclic scores over
all inputs. It does not exclude nonconservative ranks, nonlocal invariants,
spatially staggered scores or charges restricted to a canonical orbit. It
implies no absorption or density theorem and solves none of the prize problems.

Preliminary one-step F2 local-flux searches at widths 1–4 found density-space
dimensions 1,4,16,64, exactly the constant-plus-coboundary dimensions. A
separate scalar-ring implementation with low-pivot rank checks matched these
spaces on 5,888 rings, including positive Rule150 and negative Rule30 controls.
These finite computations are not premises of the uniform Lean theorem.

The first core port used broad modular-arithmetic normalization and hit the
ordinary 2 GiB system-free guard at 132.7 seconds. It was replaced by small
kernel-checked parity identities and AC simplification. Limits were not
relaxed. All failed sources and exact guards are retained. A proposed manual
stop did not signal any process: the resource guard had already terminated
the owned compiler. The first generic headline check rejected universe
parameters despite a successful replay; concrete Type0 headlines resolved
the reporting restriction without changing the checker.

## Other attempts that failed

An exact packed inverse reconstructs negative initial cells from a prescribed
center trace and a finite positive initial half. A proposed escape bound U+1
fails at canonical ages U=5,V=4: there is no reconstructed black cell beyond
the younger left boundary through depth6; the first is at depth9. Independent
scalar inversion, physical forward replay, last-cell corruptions and horizon
consistency checks passed in 93 cases (3,159 center checks). This refutes only
the short bound. The unrestricted escape criterion remains unproved.

The [half-history controls](work/half-history/canonical-half-followup.json)
also retain the complete canonical nonnegative initial half and four left-edge
cells, yet admit a noncanonical start at ages U=88,V=87 matching the older
trace through 88 and first disagreeing at 89. This real third trajectory is not
a common auxiliary mode of the chosen canonical backgrounds: its wedge
already fails at time0,position-80. The true canonical pair still has an
independently verified finite common-field certificate at N=88. These facts
must not be conflated into a prize or observer counterexample.

## Essay and next work

The [new essay draft](work/essay-draft/essay.md) embeds the standalone proof
with the icon marker and the required kit-root import. Its source passes the
unchanged full checker (207 declarations); its small Wolfram examples pass.
No notebook for this draft has been built or freshly evaluated, and no API
submission or new human consent has occurred. The earlier delayed-defect
notebook's separate RAM-wait helper remains outside this frozen archive.

Public refresh at 21:09 UTC found 40 entries, no changed/new entry and the same
verifier pin. Skill v1.17.3 adds an explicit source-icon check; the existing
queued notebook check was updated accordingly, with no proof-source change.

The conservation template is now ruled out uniformly in the stated class.
Further work needs canonical history, a nonconservative mechanism, or a
different form of invariant. Increasing the finite density width is not the
missing unbounded argument.
