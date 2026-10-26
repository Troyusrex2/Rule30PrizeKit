# F003 short extensions are now fully proved in Lean

The exact conditional short-extension theorem is proved and has passed full declaration replay with the unchanged official checker. The unbounded ancestry conjecture D3* and Rule 30 Prize Problem 1 remain open.

The headline is `RootShortExtension.safe_short_extension`:

```lean
theorem safe_short_extension (u v : List Bool) (hu : Safe u)
    (hr : evolution 8 u = u) (hv : v.length ≤ 3) (hs : Safe (u ++ v)) :
    evolution 8 (u ++ v) = u ++ v
```

`Safe` is Cedar's exact all-time predicate: the newest cell is never false at two successive times. `evolution` is the literal older-first finite-white Rule 30 map from `CedarSafetySoundness`: both missing older cells are false, and every update is simultaneous. The conclusion is equality of the entire appended word after eight updates, not just equality of the newest cell. The prefix's eight-step return is an explicit premise. There is no supplied clock or period assumption for the appended cells.

The second checked headline, `accepted_short_extension_language`, says an accepted prefix with a safe append of length at most three remains in the existing accepted language. It follows from the same exact return theorem and Cedar's previously proved equivalence. It does not prove that an arbitrary safe word is accepted.

## Why this proof compiles

The previous attempt reconstructed long function-valued profiles and large transition tables. This proof instead reuses the already checked eight-profile transition theorem. A new generic lemma, `history_lift8`, proves that repeating the first eight entries of a profile gives the exact unbounded-time child history when that child's computed eighth entry returns to its initial value. The argument handles the cyclic wrap explicitly. It supplies periodic histories only for the already accepted prefix; it never imposes periodicity on a proposed extension.

At the end of that prefix, there are fifteen possible safe profile pairs. For each pair and every append of length at most three, the proof retains a short literal trajectory. Every step is a separate kernel-checked equality. There are 225 cases: the original 210 nonempty appends and fifteen empty appends. In 113 cases the entire appended row returns at eight. In the remaining 112, an explicit unsafe pair occurs by time 21. Those are alternatives used by the proof, not claims that the returning cases are necessarily safe.

The finite dispatch theorem combines the cases. Spatial induction consumes the arbitrarily long accepted prefix, transporting the exact histories and all-time safety predicate to the remaining suffix. This is the semantic bridge from the finite cases to all finite prefix lengths.

The producer script is not trusted: its output is checked by Lean through the individual transition equalities and the finite dispatch proof. A separate Python audit also matched all 210 nonempty cases against Cedar's earlier independently audited certificate.

## Verification

Official pin: `5473ffd075f63c9d626e63b8455805d4831b39ca`.
Lean: 4.35.0. Unchanged Check.lean SHA256:
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

All seven modules were freshly compiled and fully replayed on the G913. No new axioms, native decisions, checker changes or guard overruns were used.

| Module | Declarations fully replayed | Role |
|---|---:|---|
| CedarSafetySoundness | 137 | Existing dependency |
| CedarSafetySemantics | 75 | Existing dependency |
| CedarSafetyBridge | 8 | Existing dependency |
| RootShortExtensionCore | 36 | Exact history and safety transport |
| RootShortExtensionCases | 232 | 225 split trajectories and supporting definitions |
| RootShortExtensionCertificate | 1 | Exhaustive dispatch |
| RootShortExtension | 4 | General spatial induction and conclusions |

The new-module count is 273 declarations, including definitions and generated declarations; it is not a count of 273 new mathematical theorems. The largest owned process-tree RSS was approximately 1.28 GiB. The case module's guarded build and replay took 15.42 seconds, the dispatch 8.46 seconds, and the final theorem module 5.32 seconds. Exact times, hashes and guard readings are in `audit.json` and the module reports.

Two failed local revisions are retained. The first core attempt had an extra rewrite and omitted unfolding `newest`; both were ordinary elaboration errors. The first combined certificate elaborated its concrete case proofs but failed in finite dispatch because a Fintype import was missing. Splitting the reusable cases from dispatch and importing the required instance resolved that error. Neither failure involved changing the theorem or checker.

## Remaining gap and handoff

D3* must still provide a shorter safe prefix after deleting one, two or three newest cells. This new theorem then handles the short append once the induction hypothesis supplies that shorter prefix's return. It supplies no D3* proof, global safety completeness, observer theorem or fixed-center conclusion.

The work is isolated under `short-extension-worker-20261026T1830`; Cedar's original sources and sealed responses, the shared official reference and catalog branches were not edited. No GitHub push or prize submission was made. Root should perform its own fresh replay and scope review before integration.
