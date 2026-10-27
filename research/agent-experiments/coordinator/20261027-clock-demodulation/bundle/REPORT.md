# Recovering older observations across a clock birth

The literal finite-word CA observer now has a uniform reconstruction theorem:
when an appended penultimate bit flips after a whole return of the older word,
the two newest output streams recover both older output streams exactly.
A finite OR of those observed differences detects that flip. This is a positive
two-cell reduction, including comparisons of older words of different lengths.

Use the existing definitions T=C after A, r=last bit, and s=last bit after A.
For a nonempty older word u, appended bits g,h, and T^P(u)=u, define
eta=r(T^P(u++[g])) XOR g. With D_P f(t)=f(t+P) XOR f(t), the new theorem is

    D_P(r+s) = eta AND NOT r_old
    D_P(s+U r) = eta AND NOT s_old.

If eta=1, complement these differences to recover the older outputs. For P>0,
eta equals the OR of the two differences at times0 through P-1. The detector
reads observations only through time2P. A supplied whole older return is
essential; P need not be the least return. The flag may vanish when an oversized
P is supplied, and is not an intrinsic label of a plateau. A flip only of the
newest bit does not suffice. The eta=0 case reconstructs nothing.

The helper proves that in the genuine sheared recurrence a permanently black
first column excludes any later constant column. Applied through the existing
CA adapter, the older output channels cannot both remain black forever. This
supplies the finite detector witness without assuming observer completeness.

The same bundle proves a complementary limitation. For every width m>=8,
no two arbitrary scalar Boolean output functions admit affine F2 full-state
decoders using finitely many fixed time shifts. This excludes an entire linear
decoding method, while leaving nonlinear decoding and trace injectivity open.
It uses an all-width conserved prefix polynomial, valid already at width>=6:

    I=(1+x2)[x5+x4(1+x1+x0*x1)+(x0+x1)(1+x3)].

At width>=8 the source proves an exact sixteen-term coordinate-stream identity
for I. Together with the invariant functions1 and x2, this gives three
independent fixed functions. Full affine coordinate recovery would force all
three into a two-generated observation module, whose fixed space has dimension
at most two. The generic argument uses rank-nullity, not invertibility or
nilpotence. The polynomial identities are verified by kernel coefficient
equality and a proved evaluation theorem, not a zero-tail slice assumption.
The obstruction does not say I alone is unobservable.

Main sources are Rule30CAClockDemodulationResearch, Rule30AnchoredConstantResearch,
Rule30CAInvariantResearch, and Rule30CALinearBarrier. The polynomial evaluator,
symbolic certificate, and generic linear module are included, as are all six
previously published reader dependencies. The seven new modules contain413
kernel-replayed constants and25 headlines; all thirteen total1117 constants
and43 headlines. Constants include generated declarations.

All thirteen exact sources passed independent full replay through the unchanged
official checker. The twelve-module closure was rebuilt from source, then the
demodulation leaf was rebuilt using only that independently replayed closure.
No worker object files were used. Exact headline type transcripts, source hashes,
checker receipts, and both guards are included. The official dependency library
was reused; this is not a cold Mathlib build. Partial checker typeMatches is not
an external expected-proposition comparison; source and type review establish
the stated scope. No new axioms, sorry, native_decide, or bv_decide are used.

Reader completeness, phase separation, unrestricted plateau reconstruction, the
separate physical-center bridge, and Prize Problem1 all remain open. Nothing
here establishes closeness to a full prize solution. No Wolfram essay was sent.

Verify files and recorded receipts without invoking Lean:

    python replay.py --verify-only

Rebuild all thirteen sources with the pinned official environment:

    python replay.py --lean /path/to/lean --official-lib /path/to/pinned/lib/lean --checker /path/to/pinned/Check.lean --output /new/separate/output

The output directory must be new and outside the bundle, tools, and official
library. The official library must already be built at the pin in summary.json.
No private research objects are needed. MANIFEST.json seals every bundle file
except itself. A reproducibility receipt from this exact command is included
in the enclosing archive when that replay is complete.
