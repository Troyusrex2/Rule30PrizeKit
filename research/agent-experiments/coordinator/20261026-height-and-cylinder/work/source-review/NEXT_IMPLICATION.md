# An unbounded consequence that survives the saved strip controls

This is a proposed next formalization with a complete elementary paper argument. It is not Lean-verified and is not a D3*/ancestry claim.

## Sharp zero-count versus one-run tradeoff

Let b be a nonconstant cyclic Boolean trace of any positive returning period P. Assume Safe (no cyclic00) and No11011 (including cyclic wrap). Let Z be its number of zero phases and R its longest cyclic run of ones. Then

    2 P <= (R+3) Z.

The bound is uniform in P and has no finite-strip width. Nonconstancy is essential: the constant-one Safe trace has Z=0 and no finite cyclic one-run bound.

Proof: Safe isolates the zeros. Connect consecutive zeros when their cyclic separation is2. If every gap is2, the trace alternates, so R=1, P=2Z, and equality holds. Otherwise these links form C finite zero clusters. No11011 forbids a singleton cluster: the zero would have ones at both offsets2, producing11011. Thus Z>=2C. A cluster with r zeros contains r-1 internal ones. Between clusters lie C one-runs of lengths L_i, each between2 and R. Therefore

    P = 2Z - C + sum_i L_i
      <= 2Z + (R-1)C
      <= (R+3)Z/2.

The last step is valid because R>=1. Multiplying by2 avoids division.

This is a global cyclic counting consequence, not an inference that every locally admissible trace comes from a finite-white history. It can be paired with a genuinely finite-white bound on constant-run length. For example, Cedar's separate paper white-cone bound R<=ceil(d/2), at positive depth d beyond the first black column, would give

    2 P <= (ceil(d/2)+3) Z.

That width-dependent version remains conditional on independently proving and correctly transporting the white-cone bound. It is a necessary quantitative restriction, not a proof of return8. It avoids treating a free strip as a white-boundary model and does not duplicate the carry/D3 investigations.

## Existing controls are compatible

Only the two already saved profiles in `integration/free_strip_safety.json` were read. Both are Safe and avoid11011 across wrap:

| Saved period | Z | R | Zero-cluster sizes | 2P | (R+3)Z |
|---:|---:|---:|---|---:|---:|
| 17 | 8 | 2 | 8 | 34 | 40 |
| 32 | 9 | 13 | 3,2,4 | 64 | 144 |

Thus neither is a counterexample to the proposed tradeoff. They remain countercontrols to deriving period8 from Safe plus local shared-OR constraints alone. This check did not repeat their internal OR-update audit or establish finite-white ancestry.

## An unbounded limitation to retain

For any P>=5, take a P-periodic trace whose only zeros are at residues0 and2. It is Safe and avoids11011: each zero has the other zero exactly two steps away. Its longest one-run is P-3 and Z=2, so the bound is sharp. Its least period is P: a nontrivial shift preserving the two-zero set would have to swap the zeros, forcing P to divide4, impossible for P>=5.

Choosing P=2^k for k>=3 gives arbitrarily large dyadic least periods satisfying Safe and No11011. Applying `normalized_tc_chain` separately supplies a TC chain to each such terminal profile. This does not claim that the older chain profiles all avoid11011 or satisfy shared OR equations. It does show that terminal Safe/No11011 plus a TC-only ancestry chain cannot force return8.

This explicit family prevents overpromising the proposed counting lemma. Its value is a sharp all-period restriction that can be combined with a real white-boundary invariant, not another finite-clock acceptance certificate.
