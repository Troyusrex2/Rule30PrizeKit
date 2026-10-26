# Full-support one-step Subset variants: both fail

Status: paper audit of the exact finite-state witnesses supplied by the
structural worker. This note proves no all-time preservation result and
claims no new Lean replay. No separate search or horizon sweep was run by
this worker. All coordinates are older-first, with the genuine white
boundary; integers encode coordinate0 in the least significant bit.

## Predicates and exact difference dynamics

For backgrounds A,B and mode H, let D=A XOR B. Actual backgrounds evolve
by F and the mode evolves by

    H'_0=H_0, H'_1=H_1 XOR H_0,
    H'_j=H_j XOR ((NOT B_(j-2)) AND H_(j-1))
                 XOR ((NOT A_(j-1)) AND H_(j-2)), j>=2.

Common is the adjacent identity D_j H_(j+1)=H_j D_(j+1); Subset means
H_j D_j=H_j. The same linear mode update applies exactly to D. The
interior identity follows by expanding Boolean OR over GF(2):

    (A_(j-1) OR A_(j-2)) XOR (B_(j-1) OR B_(j-2))
      = ((NOT B_(j-2)) AND D_(j-1))
          XOR ((NOT A_(j-1)) AND D_(j-2)).

These are the formulas in Rule30CommonPastResearch, with no right wrap.

## Forward implication fails on complete zero-padded rows

The supplied five-cell input, extended by zeros at every newer coordinate,
is

    A=25 (10011), B=2 (01000), H=24 (00011).

Literal actual/mode updates on the entire half-line give

    A'=111, B'=14, H'=104.

The corresponding seven-cell displayed output rows are1111011,0111000,
0001011. Input D=27 supports H=24, so input Subset holds globally. Output
D'=97 has support{0,5,6}, whereas H' has support{3,5,6}; output Subset
fails exactly at3. Common holds globally on both input and output rows.
For the input, the only adjacent nonzero H pair is3,4, where D is11.
At the output, the common supported pair5,6 has D=H=11; the extra H at3
has D=0 at2,3,4. Every remaining adjacent equation is0=0.

All outputs vanish after coordinate6, so this checks the two newer output
cells as well as the whole zero tail. It is not the earlier width-four
truncation artifact.

Thus global Common at the input and output rows, genuine white Actual/Mode,
and global input Subset do not imply global output Subset, even when all
three input rows have finite support.

## Backward implication also fails on complete zero-padded rows

The supplied six-cell input is

    A=33, B=34, H=24.

The complete outputs are

    A'=231, B'=238, H'=8.

Input D=3 misses both H positions3,4, so input Subset fails. Output D'=9
contains H'=8, so output Subset holds globally. Common holds globally in
both rows: input D has support{0,1} and H has support{3,4}, separated by
zero at2; output D has support{0,3} and H support{3}, with separating
zeros. Outputs beyond coordinate7 vanish.

The common input black cell at5 matters to the mode coefficient:
H'_6=H_4 AND NOT A_5=0. Hence a newest unsupported mode bit need not leave
an unsupported mode bit farther to the newer side. A right-tail survival
argument without the full coefficient constraints would be invalid.

## Finite-cut reduction for an arbitrary common background

This semantic reduction is sound, although neither candidate theorem is.
Suppose only D and H have finite support: choose N such that D_j=H_j=0
for every j>=N. The actual backgrounds A,B may have an arbitrary common
infinite tail. Keep A and B unchanged through coordinateN+1, and replace
both by0 at coordinates>=N+2; keep H (already zero there) unchanged.

Input D and H are identical before and after this cut. Actual and Mode
updates at coordinates<=N+1 use only coordinates<=N+1, so their output
D,H agree there. At every j>=N+2 the three older/current D and H inputs
in their triangular update vanish. Thus output D_j=H_j=0 on both sides
of the cut, regardless of the common background coefficients. Therefore
all global input/output Common and Subset predicates are preserved.

Consequently any one-step counterexample with finite D,H and arbitrary
common background can be represented by finite-support A,B,H, after
retaining two common-tail cells. This does not prove a preservation law;
the explicit finite-support controls above already refute both directions.

## What the proposed bridges would and would not prove

Had the global forward lemma held, finite initial D,H and all-time global
Common would permit direct time induction: D,H remain finitely supported,
their support growing by at most two cells per step, and the lemma would
preserve Subset at each step. No global recurrence premise would be needed.
The displayed forward counterexample invalidates this particular lemma.

A global backward lemma would still not combine automatically with
fixed-prefix recurrence to supply whole-half-line future Subset. This
separate logical gap is explained in recurrent-subset-note.md. The stronger
backward one-step premise itself is now also refuted.

The witnesses assert Common only at the two displayed times. They are not
counterexamples to initial-Subset preservation under Common at every
natural time, to FrontStable, to finite-white safety completeness, or to a
physical-center conjecture. No claim about an all-time Common completion
is made. After these failures, no further candidate is proposed here.

## Audit provenance

The structural worker supplied the witnesses from one exact closed graph
over input symbols(A,B,H), retaining both Subset flags and checking the
complete newer output tail. This worker independently calculated the
displayed full-row updates, differences, predicate equations and finite-cut
argument on paper. The structural worker owns the independent literal
transition audit and graph certificate; no new graph was generated here.
The completed audit is ../structural/full-support-backward/audit.json,
with source audit.py and producer probe.py in that directory. It reports
PASS on all364 reachable states,2912 transitions and the literal complete
finite-support witnesses. The certificate SHA256 is
14c37330ac6122d7b71d278a49cb06a15402e3a92b774b377c498579657e5cac.
