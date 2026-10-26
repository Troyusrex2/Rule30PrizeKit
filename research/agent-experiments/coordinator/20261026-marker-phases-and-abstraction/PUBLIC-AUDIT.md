# Public-source audit at 2026-10-26 21:00 UTC

Three new official receipts report full kernel verification at kit5473, Lean4.35.0, with standard axioms only and no new axioms. Root independently inspected their exact downloaded sources and receipt provenance; it did not rerun these large external certificates. None of the receipts marks an official prize target solved or human verification complete.

| Verified submission | Scope | Official replay |
| --- | --- | ---: |
| [8cca17](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261026-8cca17) | Arbitrary Boolean blocks of length at most9 followed by at least102 whites; additional isolated-black mixtures. | 4339 declarations |
| [196859](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261026-196859) | Arbitrary finite mixtures of black runs followed by at least17 whites, and other explicitly constrained mixtures. | 2078 |
| [d611aa](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261026-d611aa) | Arbitrary finite mixtures from four specified black/white run categories. | 2075 |

Exact source hashes, respectively:

```
6449c1731beffffe999f77c2d09fe174bda82f842ca9a2800091e4dd606d3bd4
67a0390c96d1149cecf7c3e48db3e7dc96ff3017fac263c6fddcc491eb09468a
a8ce65bd7ab488eb38b6fa5f9963dcf99b847dcf4ca9e3dec857f1f7d9358b21
```

These are genuine unbounded families: run lengths, finite block counts, and transients range without a fixed bound. The conclusions exclude eventual repetition of the stated finite words at the literal physical center. They do not exclude arbitrary nonperiodic streams or all periodic words. The separate later superseding entry4d375d was unverified in this snapshot and was not substituted for8cca17.

The most useful generic interface is `Rule30RankedWords.ranked_append` / `no_word_ranked`: nonincreasing ranks allow response laws to compose across arbitrary block lists. The proof still requires capture and a deterministic physical OR response when rank is unchanged. It constructs no rank for an arbitrary driver. The pinned kit already contains rank-stabilization soundness. All fifteen FastImage core declarations duplicate the already independently replayed PR31 source, rather than providing a new inverse/reachability argument.

The short-block graph explicitly retains depth9. Its physical capture uses a24-cell window, followed by14-cell certificates. No width-independent construction, arbitrary-depth capture, or bridge to finite-white Safe/F8, clock plateaus, or full reader completeness follows. A separate research task is assessing symbolic physical-front bounds; these unproved extensions are not part of the verified submissions.

Credit belongs to the original submission authors listed on the linked official records. This is an audit of their work, not a claim of authorship or fresh root replay.
