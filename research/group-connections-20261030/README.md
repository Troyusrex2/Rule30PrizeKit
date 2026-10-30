# Local group connections and the finite-white-boundary distinction

By Troy Lowry with OpenAI Codex, 2026-10-30. Partial results. The prize remains open.

The catalog contribution is [PR58](https://github.com/WolframInstitute/Rule30PrizeKit/pull/58).
For every finite width and any group, the displayed one-step local zero-curvature connection
is a vertex gauge of two commuting vacuum constants. No finite-group, abelian, or
identity-vacuum assumption is made. Ordered cyclic spatial products telescope to a
conjugate of the vacuum power. The exact transport halo is part of the statement.
The full module docstring, `full_background_connection`, and the explicit statement
guard specify the quantifiers. This is an obstruction to a class of methods, not a
prize proof or a classification of all invariants.

An additional research module checks a 13-state presentation of two infinite spatial
profile pasts. They have the same final period8 profile, not periods1,2,4, and different
immediate predecessors. Every depth satisfies the literal sideways Rule30 recurrence.
No profile in these chosen pasts is white. Thus omitting finite white ancestry from a
predecessor-decoder argument is unsound. This does not refute the white-root conjecture;
the absence of a white profile in a chosen history is not a proof that no other white
ancestry could exist. It is not offered as another catalog PR.

## Reproduction

With Python and Lean4.35.0, no Mathlib or external Python package is needed:

    python verify.py --lean C:/path/to/lean.exe --out D:/new-empty-validation

The script copies only source into a new output directory, builds the four-source
closure and explicit rule/type guard, and runs the unchanged official `Check.lean`
on both owned modules. All declarations are replayed; all selected headlines and
their standard axioms are checked. A partial verdict is not a prize implication.
There is a60-second guard per process and120-second overall guard. The full catalog
is not built. `evidence/RESULT.json` and complete logs record the actual run.

The official Jen and Prize sources are frozen from kit932cf8d. The checker is
byte-identical to the official checker used in our previous checks. SHA256SUMS.json
binds every file in this archive except itself. No compiled owned object is an input.

## Exploration: what did not become a proof

`discovery/` contains fixed-limit experiments and their exact scopes. Negative matrix
group searches were replaced by the uniform proof. Singular matrix traces do escape
the group argument, but the first found example only recognizes alternating rings.
The sparse-dyadic restart and apparent period7 in the alternating empty-right driver
failed at times16 and at sample147/154 respectively. No eventual-period claim follows.
Boolean certificates for small widths grew in complexity; no width induction emerged.
Simple dyadic survivor-code identities failed. Generic finite preimage existence is
not a replacement for the prescribed gate inverse.

The old white-root q<=32 profile graph was analyzed without extending it. Bounded
local decoding needs more context as the clock grows. Boundary-free decoding fails
already at q8; finite prefixes must not be required to have bounded-clock spatial
futures, since the next clock may double. Newton-degree monotonicity also fails in
the actual white-root q32 graph, including degree31-to26 drops; only the dyadic clock
was retained in the old certificate. These are not new unbounded positive results.

A new moving-frame candidate, absence of genuinely dyadic periodic backgrounds
above period8, survived rings<=24 at periods16/32. This is finite evidence only.
Two independent Wolfram SAT formulations of the16x32 instance hit their25-second
caps; neither is an UNSAT result. No larger census or speculative patch was adopted.

Some discovery scripts refer to the prior immutable q32 graph archive. They are
research receipts, not inputs to the source-only proof verifier. No historical
priority is claimed. Private account responses, credentials, and machine
configuration files are deliberately absent.

## Final receipts and publication status

Fresh replay passed: 180 declarations in GroupCocycle and 37 in the countermodel, with seven selected headlines and explicit official-rule/type guards. Runtime 15.219s. No new axioms or owned-source warnings. The whole catalog was not rebuilt.

The independent Wolfram GL2(F2) positive control passed all32 local equations and cyclic conjugacy. Its saved seed figure is under `essay-draft/`. The standalone root-import source also passed all four headlines. The computational notebook hit its memory/free-physical guards, so **no new formal portal submission was made**. The prose and source are labelled draft; failed notebooks are absent. The core-only portable replay is complete.

A separate bounded renewal-reader test checked whether the empty-right echo gap code was a shifted/decimated self-code or one of the seed columns-4..4. No128-bit training match occurred among77100 fixed candidates; this rejects that specific family, not every return-map renormalization.

Raw compiler logs preserve original bytes and are exempt from whitespace lint. The core-only owned sources compiled without warnings; the separate root-import draft has a nonfatal Mathlib style suggestion about letI.
