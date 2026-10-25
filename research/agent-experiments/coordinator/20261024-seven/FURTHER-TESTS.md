# Further tests of the coupled counting route

**The full prize problem and the factor-three counting inequality remain
open.** The new work in this record is numerical investigation, not a new
Lean proof. The two uniform word exclusions, population certificate and
conditional CQ01 reduction remain the checked results of
[COUPLED-LANGUAGE.md](COUPLED-LANGUAGE.md), published in commit
`c141fc9b515b8bd49b806f11bb0cb18d693d37bc`.

## A stronger bounded check, with a separate encoding

For coupled free bits `s_R(k)=!u R k`, write `z(n)` for the number of free
zeros and `e(n)` for the black even initial coordinates among the first `n`.
The candidate is `z(n) <= 3*e(n)` for every finite right half and all `n`.
Its proof would imply CQ01 by the already checked reduction. It would not
settle the other periods of Prize Problem 1.

The earlier Z3 all-prefix-through-48 query timed out. A new Boolean CNF
encoding with Glucose 4 excludes a counterexample at **every prefix through
64**, enforcing the actual driven right half and the left reconstruction.
The length-48 all-prefix check takes about 1.5 seconds and length 64 about
40.8 seconds on this machine. These are solver results, **not Lean theorems**.

The CNF independently encodes XOR/OR gates. At a fixed length `n`, charge
failure is `ones(s)+3*ones(E) <= n-1`. The all-prefix version instead builds
an exact unary running counter and asks whether any prefix violates its
threshold. The filename's `seqcounter` parameter is relevant to point
queries; the all-prefix implementation uses this explicit running counter.

Controls cover all Boolean inputs to the gates, a known actual coupled
factor-two counterexample, and a prefix that fails at length 11 but recovers
at 12. The latter prevents a final-length test from being mistaken for an
all-prefix test. Every satisfying test model is independently checked by
exact physical evolution and sideways decoding.

The first point and all-prefix tests at length 96 timed out. Alternative
engine/encoding results are included in the appended result table. A
timeout is inconclusive. The guard-only query imposing the two proved word
exclusions, rather than actual right dynamics, also timed out at 96. It
correctly recognizes the known 197-bit counterexample when only the
six-word exclusion is imposed and excludes that word when the seven-word
exclusion is added.

## Complete sparse-input trees

The tree enumerates both next even input bits while retaining a population
budget. It rejects a prefix only when its free bits leave a finite window
language. No beam pruning is used. A cap leaves an explicit unknown result.

| Guard window | Black-even budget | Outcome |
| --- | ---: | --- |
| 7 | 12 | Complete extinction at depth 93 |
| 7 | 14 | Complete extinction at depth 111 |
| 30 | 12 | Complete extinction at depth 56 |
| 30 | 24 | Complete extinction at depth 117 |
| 30 | 48 | State cap; last complete depth 57, unknown |

The seven-bit guard permits exactly 25 words. It has the same forbidden
patterns as Golden plus the two kernel-proved exclusions `010110` and
`1011010`. The 30-bit guard is a stronger numerical overapproximation from
the complete finite right-image census; its longer exclusions have not been
kernel checked. Neither numerical tree is claimed as a kernel certificate.

For the complete budget-14, window-7 tree, the maximum free-zero counts at
exact black-even costs `0,...,14` are:

```text
cost:  0 1 2 3  4  5  6  7  8  9 10 11 12 13 14
zeros: 0 3 4 8 10 13 14 18 22 24 25 27 30 33 35
```

Every value satisfies factor three. The stored maximizing prefixes were
independently re-encoded with scalar anti-diagonals and physical decoding.
This is evidence for a counting invariant, not an induction over all
budgets. Increasing a finite budget repeatedly cannot establish that
induction by itself.

## Wider searches and unsuccessful learned ranks

A beam of width 2048, avoiding the two proved words and Golden violations,
reaches 5308 free bits before its self-imposed time limit. Its best retained
state has 609 black even inputs and 1742 free zeros, giving deficit
`3*609-1742=85`. No counterexample was found; beam pruning makes that
absence heuristic. The final prefix passes independent scalar re-encoding.

All 457 primitive periodic phases of periods at most 14 admitted by those
short-word guards were checked through 2048 bits. No factor-three violation
was found. Their first 64 bits were also checked by independent physical
decoding. This covers that finite periodic experiment, not arbitrary
periodic words or aperiodic streams.

Further ranking attempts use the stronger two-word guard:

- Positive-semidefinite quadratic forms in letter counts and signed
  position-parity counts, conditioned on the recent free-bit context,
  fit the shorter training widths but fail wider held-out widths. Depending
  on the variant, 148--462 held-out constraints fail.
- Removing the constant feature makes all four tested homogeneous
  quadratic templates numerically infeasible on the training constraints.
  That numerical status is not a formal impossibility theorem.
- A bias-free ReLU network with a squared, hence nonnegative, output was
  also trained as a homogeneous rank. It failed to fit 1458 of 1688
  training inequalities and failed 472 of 817 fresh held-out inequalities.
  It produced no candidate for extraction or proof. This is a failed
  optimization attempt, not a theorem excluding every neural rank.

The training widths were 16--256 and held-out widths 512--1024. The neural
held-out seed is independent of the earlier quadratic experiments. The
constant-free models avoid explaining finite data by a fixed width ceiling.

## Why finite word guards do not establish periodicity

The length-30 window graph has 3098 vertices and 3578 edges. Its largest
strongly connected component has 1293 vertices and 210 branching vertices.
Thus this finite guard alone admits nonperiodic infinite words; it does not
force every admitted stream to become periodic. Its numerical spectral
radius is about 1.16353.

This graph is an **overapproximation**. Its nonperiodic words have not been
identified with traces of actual right halves. Neither a positive-entropy
claim about the true image nor a counterexample to eventual periodicity of
an actual right trace follows from the graph.

## Two tempting simplifications fail

A local version of the charging argument is already false. For actual right
initial row `0x843c2243dda4964`, the free word's interval `[17,30)` contains
four zeros while the last black even input is at index 17 and inputs
18,...,29 are all white. Thus one cannot simply assign at most three later
free zeros to the latest black even input. A proof of factor three would
need an amortized argument that can retain credit from earlier inputs.

The empty driven right half also briefly suggests a self-similarity: its
states at times 1,3,7 are single front cells. That pattern fails at time 15,
when there are seven black cells. The longer power-time probe records the
failure rather than extrapolating the first three cases.

## Reproduction and remaining gap

[further-tests-artifacts.json](further-tests-artifacts.json) hashes the
scripts and records. Numerical scripts import the earlier campaign helpers.
SAT uses workspace-local `python-sat 1.9.dev17`; quadratic experiments use
workspace-local CVXPY, and the neural experiment uses PyTorch. No solver
binary or model credential is committed. All jobs retain the 300-second,
8-GiB RSS and 2-GiB-free-RAM guard. A wrapper's command-completion status
does not change an inner solver's `unknown` or a failed held-out result.

The next substantive step is a genuinely unbounded invariant or an actual
coupled counterexample to the proposed counting bound. A longer finite
census, a fitted model or a cycle in the guard graph cannot fill that gap.
Independent agents should return results with the
[shared response format](../../RESPONSE_FORMAT.md), clearly separating
actual right traces, guard-only examples and kernel-checked proofs.

## CNF result table

| Length | Engine | Query | Encoding | Result | Seconds |
| ---: | --- | --- | --- | --- | ---: |
| 48 | g4 | final length | seqcounter | unsat | 1.141 |
| 48 | g4 | every prefix | exact unary prefix counter | unsat | 1.469 |
| 64 | g4 | every prefix | exact unary prefix counter | unsat | 40.781 |
| 96 | g4 | final length | seqcounter | unknown_timeout | 90.406 |
| 96 | g4 | every prefix | exact unary prefix counter | unknown_timeout | 90.61 |
| 96 | m22 | every prefix | exact unary prefix counter | unknown_timeout | 90.515 |
| 96 | g4 | final length | totalizer | unknown_timeout | 90.39 |
