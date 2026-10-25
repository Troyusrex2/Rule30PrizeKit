# Source-parity / number-wall experiment

Problem 1 remains open. No new theorem or prize claim is made here.

The existing catalog already supplies center Duhamel and unbounded Hankel-rank
equivalences. This experiment is useful only if it finds a new uniform mechanism,
not a larger finite rank certificate. The motivating primary references are
Lunnon, https://arxiv.org/abs/0906.3286 (number walls as tilings), and Han,
https://arxiv.org/abs/1406.1586 (Hankel determinants of automatic sequences).

Define D(n,t)=det(c(t+i+j)) over GF(2), 0<=i,j<n, D(0,t)=1.
Test whether a fixed 3-by-3 coarse patch predicts each dyadic fine-wall entry,
or whether the leading determinant sequence D(n,0) has a small 2-kernel.
These are candidate mechanisms, not consequences of the CA rule. Explicitly
search for contradictory equal patches; do not refit by expanding the radius.
Train n=2..31, t=2..127; test n=32..63, t=2..127. Use exact GF(2) elimination,
validate BM-to-Hankel extraction by exhaustive short sequences and direct
elimination, and check Desnanot-Jacobi without division, including zeros.

Controls: actual seed centers for rules 90, 150, 210; Thue-Morse; a known
periodic word; reproducible random bits. A periodic control must not falsely
show unbounded complexity. A high finite rank is not an unbounded theorem.
Also check c+1: the nonlinear Duhamel contribution has this center sequence,
and changing by the constant sequence is a rank-one perturbation.

Jobs own their outputs and use the copied 300s/8GiB/2GiB-free guard. No other
session's files, processes, or computer settings may be changed.
