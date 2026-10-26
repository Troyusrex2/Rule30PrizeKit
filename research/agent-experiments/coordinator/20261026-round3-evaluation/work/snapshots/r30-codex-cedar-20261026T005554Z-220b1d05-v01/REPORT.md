# One experiment: decode Rule 30's hidden logical bit

For Wolfram/coordinator, from codex-cedar at Troy's request.
Status: **EXPERIMENT — proposal, not run.** No proof or prize claim.

**Try borrowing the idea of logical-operator cleaning from error-correcting
codes: move the initial left-edge bit through the spacetime constraints until
it can be read entirely from the center column. Search for a recursive rule
that moves the certificate, rather than another predictor of the cells.**

The coin connection is provenance. A convincing-looking result is insufficient;
we want a chain of exact transformations back to the original input. Here the
output would be a short recipe that expands into a checkable XOR certificate.

## What makes this a different experiment

The current observer work already constructs finite linear certificates. That
reformulation is not my proposed discovery. The experiment is to take those
certificates apart at dyadic time seams, and look for an exact **lifting rule
for the certificates themselves**. Think of decoding an encoded bit by moving
its representative, while preserving what it means on every legal history.

This replaces my earlier surviving-path/ancestry approach. We permit enormous
path cancellation and work with equivalence classes of linear functionals.
It needs no quantum hardware, quantum simulation, or customer coin data.

## Exact interface

Use the coordinator's current canonical observer problem, with all arithmetic
over F2. For U > V >= 0, let A(t,p)=cell(U+t,p), B(t,p)=cell(V+t,p), and
delta=A+B, from the same single black seed under
f(l,c,r)=l XOR (c OR r). Define the constraint functionals

```
D[t,p] = h(t+1,p) + h(t,p-1)
         + (1+B(t,p+1))*h(t,p) + (1+A(t,p))*h(t,p+1)
W[t,p] = delta(t,p+1)*h(t,p) + delta(t,p)*h(t,p+1)
S[p]   = h(0,p), only where delta(0,p)=0
O[t]   = h(t,0)
E      = h(0,-U).
```

For fixed canonical backgrounds these are linear in h; Rule 30 itself has
not become linear. The hoped-for output for each U,V is a finite, exact identity

```
E = XOR(selected D) + XOR(selected W)
    + XOR(selected S) + XOR(selected O).
```

Every coefficient is either zero or one, with explicit finite coordinates.
Then D=W=S=0 and an all-time zero center force E=0. The actual difference
under an alleged eventual period has E=1, giving the required contradiction.
This is the existing sufficient observer target in certificate form, not a
new implication claimed as proved by this response.

"Cleaning" has a precise elementary meaning here: adding a D, W or S row to
a functional changes its support while leaving its value unchanged on fields
satisfying those constraints. Center observations are the allowed final readout.
Do not quotient out E, impose it as zero, or assume away an exterior variable.

## The one experiment I want you to try

1. Reuse existing canonical finite certificates. Retain XOR provenance for
   every elimination step. Draw the *certificate support*, not the CA image.
2. Cut it into spacetime blocks at canonical dyadic return seams. Eliminate
   each block's interior over F2, keeping its complete boundary relation,
   the distinguished E contribution, and the original-check provenance.
   Glue blocks by matching seam variables exactly. A pivot-only summary loses
   constraints; a truncated boundary can invent a certificate.
3. Search for a parameterized rewrite that lifts a cleaned block to the next
   dyadic scale. Keep U, V, coordinate offsets and canonical background data
   as parameters. An optional symbolic learner proposes rewrite templates;
   exact algebra accepts or rejects each instance. Train on certificates and
   failed rewrites, not future center bits.
4. Demand one explicit rewrite identity and an induction measure before
   expanding the search. The desired object is a finite description producing
   finite certificates for **every** U>V, with a proved terminating recursion.
   Certificate size, support and boundary state may grow without bound.

The new fixed-band escape theorem makes dyadic seams worth inspecting. It
does **not** supply the lifting rule, a center hit, or a bounded-width decoder.
In particular, do not identify arbitrary canonical interiors with repeated
copies of one block just because their boundary phases match.

## Fastest serious falsification

Start with a CPU-only pilot, capped at 60 seconds and 256 MiB, on existing
certificate data. Stop with the exact failed template or resource-limit status.

- Replay every assembled certificate by XORing its original rows: the result
  must be exactly E, with every unwanted coordinate canceled, including seams
  and both exterior boundaries. Never zero-fill an unproved exterior.
- Test each proposed local rewrite on all boundary assignments of a small
  block. If the rewrite uses canonical ancestry, include and check that premise;
  a finite block census does not establish its arbitrary-size instance.
- Hold out entire binary-age families, especially long carries such as
  U=2^k+1 and V=2^k-1. Retain exact absolute ages rather than only low bits.
- Use the published finite-look-ahead pulse obstruction to reject any rewrite
  that silently replaces all-time compatibility with H steps. It lacks the
  required canonical left-edge premise; the decoder must record that distinction.
- Use known noncanonical invisible modes as rejection controls. A purported
  universal cleaning rule that certifies them is unsound. Their existence does
  not refute the canonical target.

A new numerical rank, a larger batch of certificates, or good compression
ratios alone is not success. The useful return is **one exact lifting identity
with its missing induction premise**, or a counterexample to that identity.
If complete interface information defeats the proposed compression, report
that failure; do not discard the inconvenient interface to restore the pattern.

## Why it might work, and the actual gap

The speculative bet is that certificate construction has a simpler recursive
structure than the visibly irregular cells. We need not compress the entire
Rule 30 history or obtain a fixed finite-state observer. A symbolic certificate
family can grow while retaining a short recursive description.

This lies outside the already-refuted additive prefix scores and fixed finite
look-ahead assumptions. It can still fail completely. No bounded interface,
dyadic closure, termination measure or uniform certificate construction has
been discovered here. Generic error-correcting-code theorems do not establish
any of these Rule-30-specific facts.

## Sources, scope and handoff

Read-only coordinator snapshot: `e4daf9ab8af66cff090fc232946dd8fdc60ffbd6`.
The exact files read and their hashes are in `provenance.json`:

- `20261025-trace-followup/BRIEF.md`: exact D/W observer and canonical premises.
- `20261025-canonical-preimages/BRIEF.md`: finite look-ahead obstruction.
- `20261026-band-escape/BRIEF.md`: reported all-width escape and remaining gap.
- Parent handoff and response format; earlier Cedar submissions remain intact.

Conceptual inspiration: Kalachev and Sadov,
[On the Cleaning Lemma of Quantum Coding Theory](https://arxiv.org/abs/2204.04699),
which treats cleaning through linear algebra. This is an analogy and a search
direction, not an application of that paper's theorem to Rule 30. No quantum
code structure, commuting checks, or distance bound is assumed here.

No CA experiment, solver search, model training, Lean build, kernel replay or
external prize submission was performed for this proposal. Packaging/schema
and SHA-256 checks establish delivery integrity only. Before formal work, use
the coordinator's current official checker instructions and independently
replay any required theorem; no verifier pin is claimed as used here.

**Next action:** try exact dyadic block cleaning on the existing observer
certificates, and return the first nontrivial lifting rule or its counterexample.
