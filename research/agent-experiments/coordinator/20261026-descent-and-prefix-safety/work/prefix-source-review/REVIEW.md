# Independent source and scope review

Reviewed frozen root sources in `returning-prefix-safety-20261026T2029`.
No mathematical or scope gap was found. This is an independent source
review plus exact hash/receipt checks, not a second kernel replay.

## Returning-prefix extension

`RootReturningPrefixSafety.returning_prefix_safe_extension` requires:
whole-word return8 of `u`, length at most three for `v`, and all-time
Safe of `u ++ v`. It concludes whole-word return8 of `u ++ v`.
It DOES NOT require `Safe u`.

The finite certificate is the complete Cartesian product `Fin 36 × Fin 15`.
The 15 words include the empty suffix and all binary suffixes of lengths
one, two and three. Completeness is proved by length/case analysis, not
assumed from the enumeration. All 36 states are used without an accepted
DFA-state filter. Each case gives either exact driven-suffix return8 or an
explicit consecutive-zero witness in the actual driven evolution.
The boundary profiles alone are repeated modulo eight; no period is
assumed for a nonreturning extension. Witness times beyond eight therefore
do not create a finite-window/all-time substitution.

The arbitrary-width bridge `extension_aux` inducts through `u`, preserving
whole `run8` return. Its head equality supplies the needed return bit to
the exact 36-state transition certificate; the returned state has both
correct boundary profiles. `history_lift8` is used only after that return
bit is established, so every removed prefix column is genuinely periodic
under the already-periodic incoming drivers. `safe_cons` transports safety
of the entire remaining word, with the correct last-bit default when the
suffix is empty. No original-prefix safety enters this induction.
State zero and `run8_white`/`driven_white` then give literal finite-white
semantics for the stated theorem.

## Minimum-width consequence

`RootMinimalCounterexample.near_prefix_both_events` assumes an actual
Safe/nonreturn word `u ++ v`, with `0 < |v| ≤ 3`, and safety completeness
for ALL words strictly shorter than `u ++ v`. This last hypothesis is the
correct minimum-width condition; it is not restricted to prefixes of the
chosen word.

The short-extension theorem first forces whole nonreturn of `u`, requiring
no Safe condition on `u`. Since `u` is strictly shorter, minimality rules
out Safe `u`. If `u` were CoSafe (no temporal 11), flipping its newest
initial leaf would make a genuine Safe word of the SAME width as `u`,
still strictly shorter than `u ++ v`. Minimality then returns this flipped
word; exact leaf-flip return equivalence returns `u`, a contradiction.
The empty-prefix branch of this lemma is handled separately by direct
return. Classical negation finally gives separate existential times for
00 and 11 in `u`. The theorem does not assert those events occur together,
within a bounded observation window, or at the same phase in different
prefixes.

The requirement `|v| > 0` is essential and is present: it justifies using
strictly-smaller-width completeness both for `u` and its flipped word.
No existence of a counterexample, unconditional descent, D3, or Prize P1
is inferred. Combining this result with the new height-one whole-word
descent would additionally rule out height span at most one at these
near prefixes, but that combination is not part of either reviewed source.

`RECEIPTS.json` records exact source hashes and the prior successful full
kernel counts (85 and 8). `review.py` also checks all ten dependency source
hashes against the recorded root manifest, the unchanged official pin and
checker hash, headline success, and absence of new axioms in the receipts.
