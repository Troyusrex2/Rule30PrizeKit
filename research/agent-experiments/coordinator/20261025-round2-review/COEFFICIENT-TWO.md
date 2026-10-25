# The actual finite-right coefficient-two counterexample is proved

The wiki response `r30-coinailyzer-wiki-20261025T124335Z-f16dc412-v01#F001`
proposed W1 as a finite counterexample candidate. It is black precisely at
positions **3, 7, 11**. The finite experiment is now an all-time proof.

For this actual finite right half R, and every natural additive allowance B,
the inequality

```
5*zeros(free R,n) <= n+B+2*blackCount(Psi R,2*n+1)
```

fails at some n. Any natural coefficient satisfying the bound for this R
must be at least three. This says nothing about the sufficiency of three,
variable coefficients, ScaleCharges, CQ01 or the prize statement.

## The missing infinite step

The original response observed the stream for 20,000 steps but had no proof
it continued. The coordinator found entry to the official ether-and-wall
invariant at **physical time 59**, ether width 6, spatial offset 3 and global
phase offset 3. The wall code is 5284, with its first cell at bit zero.

`Rule30RoundTwoDrivenPrefixResearch.trace_sound` proves a generic Boolean
light-cone certificate sound for the exact official `drv` recursion. The
concrete certificate contains 60 shrinking rows and 2,970 Boolean cells,
initial width 79. Its transition and initial-condition checks are reduced
by the Lean kernel. At time 59 it certifies the first 20 cells, including
the six ether cells and thirteen wall cells.

The official `Rule30Ether.trap_invariant` then fixes the first column forever.
Combined with the certified earlier free bits, it proves

```
free R = 0,1,1,0,1,0,1,0,...
```

More precisely, s<2 gives `s==1`, and s>=2 gives `s%2==0`. This is actual
coupling to the finite R, not an assumed or hand-built driver.

## Reconstruction and exact counts

A finite table represents the sideways reconstruction at every depth and
time. Time has a four-cell prefix followed by period four; depth has a
twelve-cell prefix followed by period fourteen. All table transitions are
kernel checked, and induction on depth proves equality to the official
`recon`, `Theta` and `Psi`. No observed spatial period is extrapolated.

The all-scale counts are, for every natural k,

```
n = 14*k+6,
zeros(free R,n)         = 7*k+3,
blackCount(Psi R,2*n+1) = 10*k+7.
```

Thus the proposed coefficient-two inequality requires

```
35*k+15 <= 34*k+20+B.
```

Taking k=B+6 contradicts it. The result covers **every B**, not just the
zero allowance or the simulated horizon. The earlier count convention is
unchanged: `blackCount L K` counts depths 0 through K-1.

## Verification, attribution and limits

The five new charge/certificate modules replayed 157 owned declarations
(10+41+68+33+5), including generated declarations, against the unchanged
official checker at kit `3eca23c0a9fa6b153313655e6d51835406c2d06e`, Lean 4.35.0.
Every full replay passed with no new axioms. The bridge proves this is the
same `Rule30GoldenCriticalDriftResearch.CriticalCharge` as before.

The final headline is
`Rule30RoundTwoChargeTwoBridgeResearch.coefficient_two_false`.
Supporting sources and raw reports are in `work/` and `work/evidence/`.
The previous checked `Rule30CriticalChargeOneCoreResearch` and its bridge
are unchanged dependencies, archived in the earlier release.

Credit: the wiki agent supplied W1, its empirical stream and charging idea.
The coordinator supplied the finite entry search, certificate soundness,
all-time trap proof, reconstruction table proof, counts and bridge. The
second proposed witness W2 was reproduced finitely and has a candidate
entry at time 47, but is not separately formalized here.

The witness's sideways support is infinite, fully consistent with CQ01.
No full prize solution, new Wolfram verification status or new essay
submission is claimed.
