# Critical drift and a complete two-state reader experiment

Problem 1 and `CQ01` remain open. The new theorem below weakens an unproved
counting target; it does not establish that target. The accompanying reader
search found no useful candidate. No new Wolfram submission was made.

## A kernel-checked critical-density argument

Let `z(s,n)` count zeros in the first `n` free bits. A Golden stream has no
`00` or `11111`, and therefore at least roughly one zero in every five bits.
`Rule30GoldenCriticalDriftResearch` proves:

```text
Golden(s) and (for every n, 5*z(s,n) <= n+B)
    ==> s is eventually periodic with period five.
```

This is a statement for arbitrary streams and all depths. The proof tracks
the trailing run of ones and a nondecreasing defect count. Exactly,

```text
5*z(s,n) + trailingOnes(s,n) = n + defects(s,n).
```

A zero following fewer than four ones increases `defects`; a zero following
four ones leaves it unchanged. The counting hypothesis bounds the defects.
A bounded nondecreasing natural sequence eventually stabilizes, after which
every zero follows four ones. The no-five-ones constraint then forces period
five. In particular every aperiodic Golden stream satisfies

```text
for every B, there exists n with n+B < 5*z(s,n).
```

Unbounded excess does not imply a positive asymptotic gap above density
`1/5`; the excess may grow sublinearly.

The kit already proves that a finitely supported constrained left start has
aperiodic free bits. Combining that theorem with the new argument gives a
weaker sufficient target for `CQ01`. With `b(L,K)` counting all black spatial
cells at depths `0,...,K-1`, it suffices to prove

```text
5*z(free(R),n) <= n + B + C*b(Psi(R),2*n+1), for every n,
```

where natural constants `B,C` may depend on the finite right half `R`.
If `Psi(R)` were finite, the right-side excess term would be bounded, forcing
periodic free bits and contradicting the kit theorem. This critical case is
useful: a drift exactly `n/5` can suffice; a strict density margin is not
required. **The displayed spatial counting inequality remains unproved.**

The complete new module passed the unchanged official checker: **74 owned
declarations, six headlines, full kernel replay**. Its statements explicitly
retain the missing counting premise. This establishes a uniform reduction,
not `CQ01` or a complete prize solution.

## Searching inequalities that cover arbitrary lengths

Previous readers fitted finitely many transitions. The new model instead
uses finite product graphs to encode a fixed reader's inequalities at all
word lengths in a specified column model.

Write a temporal triple as `w(t) = A(t)+2*B(t)+4*D(t)`. The column relation is

```text
A(t) = B(t+1) XOR (B(t) OR D(t)).
```

One inverse spatial step gives the word of triples `(C,A,B)`, where
`C(t) = A(t+1) XOR (A(t) OR B(t))`, shortening the word by one. A reader has
signed transition costs and a signed terminal cost, with empty-word energy
zero. We seek an energy `V` satisfying

```text
V(w) - V(inverseStep(w)) <= gamma*A(0).
```

A second graph requires the initial boundary energy to dominate starts of
free-zero runs. A finite spatial telescope would then charge those runs
against the black cells of the reconstructed initial row. Unlike a time
ranking argument, this telescope does not require nonnegative intermediate
energies. Graph potentials encode all paths, including cycles; no fixed word
length is used as a substitute for a universal inequality.

The finite graph constraints and their relation to the official spacetime
definitions have not been proved in Lean. An LP candidate would need exact
rational checking and that formal bridge before becoming a mathematical
claim. Independent controls checked 10,912 spatial path identities and 1,016
boundary path identities using signed random reader costs.

## Results and limitations

- All **65,536 two-state transition tables** on the eight-symbol alphabet
  were tested, in four disjoint ranges. The implemented universal LP allowed
  arbitrary signed costs and an unbounded nonnegative `gamma`. Every solver
  result was `infeasible`; there were no unknown statuses or candidates.
  These are numerical infeasibility results, not 65,536 kernel-checked
  impossibility certificates. They do not exclude larger or nonlinear
  readers, or another column invariant.
- The initial 32 constant, parity, last-symbol and random readers also found
  no feasible zero-drift candidate.
- A relaxed model allowed `zeros <= epsilon*n + gamma*spatialBlack`, using
  the Golden constraints and the two already checked coupled guard words.
  With `gamma <= 64`, 64 readers and a further 260 readers with an explicit
  transient initial state achieved no useful drift. The best exact checked
  value was `epsilon=1/2`; the critical reduction needs at most `1/5`.
- A separate positive control recovers the known black-run mass bound with
  exact `gamma=2` using a four-state prefix reader. The corresponding
  impossible all-white-column mass claim is rejected. This is a validation
  control, not a new prize result or a formalized graph-to-CA proof.

The graph search ran on the isolated 64 GB worker using Python 3.13.13,
NumPy 2.4.6 and SciPy 1.18.0. Four processes each had a 300-second, 4 GiB
process-tree cap and a 16 GiB system-free guard. Actual shard RSS stayed
below 0.08 GiB. Unlike the earlier large Lean probe, this numerical search
was not memory intensive.

One first-run checkpoint replacement hit a Windows file-sharing lock. Three
ranges completed and the fourth retained a valid checkpoint after 9,408
cases: 58,560 cases were preserved altogether. A separate V2 workspace added
bounded replacement retries and explicit, hash-bound predecessor provenance.
It completed the remaining cases. Original checkpoints and source hashes
remain intact. No computer settings or permissions were changed.

The evidence folder preserves the byte-exact original and repaired wrappers,
the unchanged synthesis source, seed hashes, final range records and guard
reports. A scoped `.gitattributes` preserves those source bytes, including
their original line endings. Earlier published manifests remain unchanged.

The next mathematical step is a proof or counterexample for the critical
counting inequality, or a different global argument. The tested reader
families have not supplied it. A larger finite simulation alone would not
settle the missing premise.
