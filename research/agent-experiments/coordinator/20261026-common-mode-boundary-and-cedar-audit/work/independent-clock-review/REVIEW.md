# Independent review of published clock transfer

**Pass, with the scope below.** Exact published commit
`64197054b1e4f5b768a624c16bd3c1db0555f3cb` was frozen before review. All nine
custom modules were freshly compiled and separately fully replayed: 388
constants total, comprising 191 dependency constants and 197 constants in the
three new modules. The latter counts are 5, 138 and 54, matching publication.
No new axiom was reported, and every selected headline passed.

The run used Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, with official kit
`5473ffd075f63c9d626e63b8455805d4831b39ca` and unchanged Check.lean SHA-256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
The official Rule30Jen, Rule30Prize and Rule30Diagonals dependencies were built
from a fresh exact source archive. No reference compiled library was used.
The shared guard recorded 70.703 seconds and peak owned RSS 953,233,408 bytes.

## Exact semantic scope

`Actual a` means `a(t+1,j) = march(a(t),j)` for every natural t and j.
The boundary equations are `x'_0=x_0`, `x'_1=x_1 XOR x_0`; at j+2 the update
is the simultaneous literal triangular Rule30 update. These are the two
missing older white cells. No canonical initial row or finite-support
hypothesis is imposed. Finite-white words embed in this evolution by any
newer extension, because earlier coordinates do not depend on newer ones.

At six consecutive depths, write n,m,l,k,h,g from older to newer. The main
headline assumes, at every time, that k flips under shift R and l repeats
under R, where R=2n is even. It concludes that `g OR h` cannot repeat under R.
R need not be a least half-clock, and no period is assumed for h, g, or the
two unspecified older profiles. The n=0 case is vacuous because anti-shift0
is impossible; it introduces no positive-clock gap.

The preliminary `actual_periodic_or_double_period` is valid for every R.
Under a hypothetical R-periodic newest OR, it derives 2R-periodicity of h
and g. The constant shift-flag argument and the existing even-plateau result
are applied at the automatically even shift 2R. A zero of h removes the
remaining shift flag for g. These are derived periods, not hidden premises.

The paired graph compares times t and t+R. Its two oldest bits in each copy
are independently free on every transition. Literal tuple reconstruction
matches all four viability levels: 640, 192, 112 and 90 states. The 20
upper-four-cell projections and 438 even-reach pairs also match exactly.
Every infinite Actual path survives all three backward prunings. The Lean
two-step closure is then used by induction on an arbitrary natural path
length; no maximum clock or ancestor period is imposed. The upper-four-cell
endpoint swaps after R by the derived 2R periods, contradicting that even-path
invariant. The two oldest cells are correctly omitted from the endpoint swap.

For depth j+6, assuming R-periodicity makes its XOR time derivative, namely
`g OR h`, R-periodic, giving the next-column contradiction. The transient
headline allows any finite threshold T for that next-column equality. It
shifts the entire Actual history to `b(t,i)=a(t+T,i)`, preserving the real
evolution and the all-time source hypotheses. It never resets an older
boundary. It excludes eventual period R at fixed depth j+6, not every possible
period, and does not itself weaken the source hypotheses to eventual clocks.

Fixed right-edge depth follows a moving physical ray. No physical-center
identification, prize conclusion, arbitrary-distance clock propagation, or
global safety-completeness conclusion occurs in these statements.

## Independent control and preserved audit failure

The width7, seed20, j=0, R=1 literal finite-white orbit is exactly [20,108].
It satisfies the source premises and has constant newest OR, so it verifies
that the OR theorem cannot simply drop evenness. The next column alternates
on this orbit. Thus this particular control says nothing about whether the
next-column corollary might extend to odd R.

The first independent graph-audit run incorrectly required that next column
also be R-periodic. That assertion failed. The published producer had only
claimed the OR control. The failing verifier source and guard log are retained
under `audit-attempts/` and `guard-evidence/`; the corrected audit passed.
This was an overstrong verifier control, not a failed published theorem.
No large finite census was rerun.

## Reproduction

Use existing Git objects for the pinned official kit and the existing Lean
toolchain. The output directory must be fresh and owned by the reviewer.

```powershell
$review = 'D:/MWB/Rule30/cedar-followup-20261026T154236Z/verifier/root-clock-review'
python -B "$review/replay_review.py" --published "$review/published" --kit-repo 'D:/MWB/Rule30/Rule30PrizeKit' --lean 'D:/MWB/Rule30/toolchain/lean-4.35.0-windows/bin/lean.exe' --out "$review/fresh-reproduction"
```

During the active team session, wrap that invocation in the shared
`coordination/run_guarded.py` with 300 seconds and 2 GiB, as recorded in
`guard-evidence/`. The helper preserves every command and complete checker
JSON/log. `source-manifest.json` binds the frozen published files;
`REVIEW_MANIFEST.json` binds the selected source-only review evidence.
No install, fetch, public post or reference write is required.
