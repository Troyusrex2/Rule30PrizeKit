# A single physical column does not determine the global clock up to doubling

Both proposed assertions are false. An official ether already refutes the P bound. Root's newly saved 84-column physical cycle refutes the 2P bound, with least global temporal period 6 and one nonconstant column of least period 2. This phase independently validated that single saved cycle by its literal scalar stencils. It did not search for cycles, evolve a trajectory, or run Lean.

## 1. Exact assertion and existing results

Let X(t,j) be Boolean for all integers t,j and satisfy

    X(t+1,j) = X(t,j-1) XOR (X(t,j) OR X(t,j+1)).

Assume a positive COMMON global period K: X(t+K,j)=X(t,j) for every t,j. Suppose one column, translated to j=0, is nonconstant and has positive period P. The proposed conclusion is X(t+2P,j)=X(t,j) for every t,j. In terms of the LEAST global period L it says L divides 2P. A supplied oversized period K need not itself divide 2P even if that conclusion holds. The stronger proposal replaces 2P by P.

This is physical nearest-neighbor Rule 30. It assumes neither finite support nor a single-seed origin. Temporal periodicity allows equivalent formulation with natural time and extension by residues to all integer times.

The current official catalog and the separately published, fully replayed PR40 candidate distinguish this question from two established results:

* Rule30Equivalents.PeriodicPoints.evol_add_factorial proves that any globally K-periodic full configuration is spatially periodic, with a supplied period (4^K)!. It does not recover K from one column.
* The published PR40 candidate's Rule30PeriodicHalfline.common_period_head_rigidity propagates a temporal symmetry of TWO adjacent head columns through a right half when a common positive clock is supplied. The literal left reconstruction propagates the same pair symmetry to the left. It does not remove the second-column premise. Publication and prior kernel replay are not a claim that PR40 has merged or received new human/backend approval.

The inspected catalog and targeted local reports contained no theorem establishing the proposed one-column bound. Rule30PeriodicProfileCounter has a different short-head/full-state example in diagonal coordinates; it must not be read as a physical vertical-column counterexample. The inherited time-eight diagonal torus is likewise not used here without a coordinate conversion.

## 2. Existing exact counterexample to the P bound

Rule30Ether.etherTable has the seven chronological column words

    0011, 0110, 1101, 0101, 0011, 0001, 0001.

Rule30Ether.ether_rule proves the physical local rule with spatial wrap modulo 7; ether_period proves temporal period 4. Extend the table by both residues to all integer space and time. The fourth column has least period 2, while the first has least period 4. Hence the whole orbit has least period 4. This is a genuine full bi-infinite physical orbit and already refutes the stronger L|P assertion.

It does not refute L|2P. That distinction motivated the separate root calculation below.

## 3. Exact counterexample to the 2P bound

The input is the saved candidate in ../physical-ring-column-period-20261027T0730/INVERSE-RESULT.json, SHA256

    9abfc6d07e64474a11f3111064f213c22ae37592daa4dea90b5dc6e6a06cc444.

Root obtained it from a cycle of the backward temporal-profile pair map. This review did not rerun that search and does not certify its exhaustive coverage claims. Let C be its list of 84 distinct packed pairs, each packed as 64*a+b, where a is a physical column and b its right neighbor. Each profile's bit t is its value at physical time t modulo 6. The saved list advances toward the physical LEFT.

Define, for every integer j and t,

    p(j) = floor(C[(8-j) mod 84] / 64),
    X(t,j) = bit_(t mod 6)(p(j)).

There is no time-dependent spatial shift in this definition. The sign in 8-j is essential: advancing the backward pair list moves left, whereas increasing physical j moves right.

The independent audit checks all 84 pair overlaps and all 6*84=504 scalar equations

    bit_(t+1 mod 6)(p(j))
      = bit_t(p(j-1)) XOR (bit_t(p(j)) OR bit_t(p(j+1))).

Every check passes. Reducing arbitrary t,j to these residues proves that the displayed X satisfies the literal physical rule at every integer time and site. This is a finite exact certificate of an all-time periodic spacetime, not an extrapolation from a long simulated prefix. The script uses direct scalar bits and the local rule, independently of the root search's packed rotation formula.

The three columns at -1,0,1 have packed profiles 59,42,44 and chronological words

    left:    110111,
    center:  010101,
    right:   001101.

The center has least period P=2. Every column is 6-periodic by construction. The right column has no period 1,2,or3, so it has least period 6 and proves that the global least temporal period is L=6. In particular shift 2P=4 fails already at one named cell:

    X(1,1)=0,     X(5,1)=1.

Thus L does not divide 2P. Static comparison of the single initial 84-bit word also confirms least spatial period 84; that minimality is unnecessary for the counterexample, but the supplied spatial period 84 is essential to its definition.

The initial configuration is nonzero and repeats every 84 sites. It has infinitely many black cells in BOTH spatial directions. It is not a finite initial row, a single-seed evolution, or a driven finite-right witness. No prize conclusion follows.

## 4. Why pair rigidity remains valid

In this example the center/right adjacent pair has least joint period 6, not 2 or 4. Consequently common_period_head_rigidity has no 2- or 4-period premise for that pair. Its hypotheses are not contradicted.

The exact local obstruction can also be seen without changing frames. If c(t)=X(t,0) is P-periodic, and l,r are its neighbors, the center recurrence gives

    l(t) = c(t+1) XOR (c(t) OR r(t)).

Writing Delta_P f(t)=f(t+P) XOR f(t), this yields

    Delta_P l = (1+c) Delta_P r.

Differences on the right can remain at the white phases of c; a single periodic column does not supply the second adjacent periodic profile. Applying Delta_P again merely yields the same identity for Delta_(2P), because c is P-periodic. It does not force that difference to vanish. The saved full physical cycle shows that imposing global periodicity and every omitted stencil still does not repair this inference.

For comparison, a constant column DOES force a globally time-periodic full history to be fixed. If c=1, its left neighbor is constantly 0, giving a constant adjacent pair. If c=0, the two neighbors agree; the right one obeys r(t+1)=r(t) OR X(t,2), hence is nondecreasing and, by temporal periodicity, constant. Again there is a constant pair. Pair rigidity to the right and literal reconstruction to the left finish. This paper corollary uses the full common-clock premise and does not extend to the nonconstant-column claim refuted above.

## 5. Evidence and limits

CYCLE-AUDIT.json records the direct 504-stencil verification, period witnesses, orientation, and exact saved-input hash. audit_saved_cycle.py is a checker of that one fixed candidate, with no graph traversal or trajectory evolution. Source references and hashes are retained separately.

The ether construction is supplied by current official Lean source. The new 84-column counterexample has an exact independently checked arithmetic certificate and the residue proof above; it has NOT been kernel checked in this phase. Root owns the original search and any separate coherent-birth calculation. This audit does not adopt additional claims about birth frequencies, finite support, arbitrary prescribed boundaries, or single-seed ancestry.
