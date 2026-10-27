# Full gate preimages and two precise embedding barriers

Paper assessment plus one named scalar counterexample. No automaton-size,
width, period, or state sweep; no new Lean build or certificate. Regularity
of the full gate language and uniform gate halving remain OPEN.

## Exact language and finite preimages

Read finite words low-head-first, with white cells beyond the older end.
Let D(n)=n XOR((n>>1) OR(n>>2)) and F=D^2. Define G by

    head=NOT neighbor, next-older<=neighbor.

These are exactly the even head-OR gate and the following odd head gate.
The full finite-word safety language in THIS paper is

    S=intersection_(j>=0) F^(-j)(G).

This S is the alternating-gate language, not the older report's different
Safe condition forbidding consecutive zero head values.

For N>=0 put K_N=intersection_(0<=j<=N) F^(-j)(G). Since one D step reads
two positions farther toward the older end, K_N depends only on the first
4N+3 initial bits. A finite automaton can remember that prefix, ignore
the rest, and pad missing bits white at end of word. Thus each K_N is
regular, by an explicit finite-prefix description. No automaton was built.
This says nothing by itself about regularity of the infinite intersection.

The exact recursion is K_(N+1)=G intersection F^(-1)(K_N). If equality
K_(N+1)=K_N were proved for some N, K_N would be forward invariant and
would equal S. An accelerated invariant could avoid such literal finite-
stage equality, but would need a sound independent closure argument.

## What the existing barriers do and do not exclude

The previously formalized infinite orbit-signalizer concerns exact least-
return MAPS on finite tails. It rejects a finite closure representing all
those maps exactly. It does not reject a finite automaton recognizing a
particular property, a relational abstraction, or a regular invariant.

The marker/carry four-fiber results reject deterministic next-view
prediction from those particular observations. Their projected97 cycle
also rejects sound progress inferred from switched existential view
representatives. It is not an actual safe nonreturning trajectory and
does not rule out full-word regular-language reasoning.

The unusual-reader three-edge cancellation refutes specified additive
feature/moment ranks, even with its named boundary and phase features.
The clock-background ordinal counterexample refutes its agreement-count
ordinal; the full intrinsic clock vector is static along time. Neither
is a theorem against every regular or ordinal certificate. The earlier
canonical and block-clock rank UNSAT/timeouts likewise have their stated
template scope. Canonical normalization and its regular DFA are genuine
all-width results, but their missing observer condition is still open.

These distinctions leave regular model checking logically possible.
They do not provide its missing simulation or acceleration theorem.

## Four-white-cell insertion: explicit analytic failure

The prospective candidate in PROTOCOL.md was insertion behind an unchanged
gate prefix:

    E_i(n)=(n mod2^i)+2^(i+4)*(n>>i),  i>=3.

It inserts four white cells, preserves the first three bits, and preserves
every retained older position modulo4. This spatial phase agreement is
not a dynamical preservation theorem.

Take n=10, whose literal D orbit is10,13,10. Both selected gates hold in
this two-cycle, so10 belongs to S. At i=3 the embedded row is130. Its
eight updates are exactly

    130,227,154,245,138,237,146,255,128.

The selected gates are1 through time7 and0 at time8:128 has head and
neighbor both zero. Hence E_3 does NOT preserve S. This is a genuine
finite-white counterexample to the stated embedding, not a free driver,
projected path, or counterexample to regularity of S.

There is also no lockstep monotonicity for the order generated only by
these zero insertions. Such an order preserves the number of black bits,
but F(10)=10 has two black bits and F(130)=154 has four. Thus the original
related pair has macro images that cannot be related by zero insertions
in either direction. This does not exclude a differently oriented or
augmented simulation with separately proved observation conditions.

Independently, zero-insertion-only order is not a well-quasi-order on the
full initial gate domain. The words010 followed by k black bits, k>=0,
all satisfy the initial gate and have distinct black counts. None can
be obtained from another by only inserting whites, so they form an
infinite antichain. Additional operations would be required before a
well-quasi-order argument of this kind could begin; their preservation
would then need proof. No claim here excludes all possible embeddings.

check_embedding.py verifies only the displayed two-cycle and eight-step
counterexample, using both packed and literal per-bit updates.

## Already-proved sound terminal growth does not give a full WQO

There are genuine observation-preserving word expansions in the pinned
official Rule30ControlledResponse source. Its tail_011_response and
tail_101_response, with any shared newer prefix w, give

    w011 ~ w01,   w101 ~ w11.

Here the strings are low-head-first and TERMINAL at the older white end.
The theorem sameResponse_iff_diagonal identifies this relation with equal
head AND adjacent-OR observations at every D time. Therefore either
replacement preserves membership in S. This is an existing proved fact,
not a new embedding result of this phase. It does not permit inserting
the replacement inside an arbitrary additional older context.

The order generated by just the inverse terminal reductions still has an
infinite antichain. Deleting011->01 or101->11 is deterministic at the
older end and strictly shortens the word, so it has a unique terminal
normal form. Each inverse expansion preserves that normal form. The
distinct words

    w_k=010 ++ 1^k ++ 001,  k>=0,

are in the initial G language and are all irreducible, since their final
three bits are001. They therefore belong to distinct expansion classes
and are pairwise incomparable under these terminal expansions. This
does not identify their complete dynamical traces or prove they are all
outside S. It only shows why the existing sound expansions alone do not
supply the desired order on all initial gate words.

## Why finite preimage saturation cannot reach the stripe core

This is a reformulation of the KNOWN nonwhite-ancestry/finite-causal-cone
barrier, not a newly discovered torus. Use the inherited period-eight
actual infinite history with low-to-older temporal profiles

    234,21,154,149,86,89,101,149,86,...,

where the four-cycle149,86,89,101 repeats from position3. It satisfies
all selected gates at every time. A profile's bit t is its value at
time t modulo8, as in the earlier sealed control.

For any N choose W=max(4N+3,9), keep its first W initial bits and set all
older bits white. This is a genuine finite initial n_N. Locality gives
n_N in K_N, since every gate through D time2N+1 reads only indices below
4N+3. Its first nine bits are234. These already determine coordinate4
after two D steps; the exact scalar calculation is

    D(234)=149, D(149)=250.

Coordinate4 changes from0 to1, so F(n_N)!=n_N, regardless of all older
kept bits. We have therefore proved, with arbitrary N and no census,

    K_N is not a subset of Fix(F).

In particular no finite unaccelerated preimage stage equals the desired
two-periodic stripe core. If the intended conclusion S subset Fix(F) is
true, the sequence K_N cannot stabilize at a finite N. This conditional
does NOT assume the intended conclusion as a proof premise elsewhere.
It does NOT prove that S is nonregular: a regular language can still be
the nonstationary intersection of these finite-prefix approximations.

The finite truncations are not known from this argument to fail a later
gate, and are not claimed to be all-time gated counterexamples. The whole
small-period return premise of the halving theorem is also not inferred
from finite observation agreement.

## Stopping point

The full-language route is not excluded by the older exact-map/feature
barriers. Its simple four-white embedding fails analytically, and both
that order and the available terminal expansions have explicit antichains.
The known torus barrier rules out reaching the desired stripe core at a
single finite preimage stage. A successful acceleration would therefore
need a different actual-history-preserving comparison or an independently
proved unbounded progress certificate. No such certificate is supplied
by this phase, and no larger automaton or width search is proposed.
