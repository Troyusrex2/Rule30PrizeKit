# Following the 13:25 upstream reviews

PR #10 moved its declarations from the shared `Rule30EtherThree` namespace
to `Rule30EtherThreeErosion`, and moved authorship details into the README
row. Its new head is `2693df04287b6f5dba6c535630c8d133866ac16b`.
The proof section is identical after the documented namespace/open adjustment;
the [exact comparison record](upstream-head-comparison-20261024.json) records it.

The white-tail extension now imports that API explicitly. Catalog head
`218415d3dd3ca1a50c79d2f6ae50d596db9c63fc` merges the new dependency without
rewriting the published branch. The dependency source is byte-identical to
the upstream head. All 131 dependency declarations/seven headlines and all
48 extension declarations/eight headlines freshly pass the unchanged checker.
`lake build Ruliology` also passes. See
[the current catalog report](white-tail-catalog-current-upstream-report.json).
The extension's mathematical proof body is unchanged; the new `open` follows
the renamed dependency.

PR #8 rebased its center-run bounds and moved credits from the module docstring
to its README row. Its new head is
`f973a13661c9b9647215785b23b1a83656d0e2fe`. Its proof section is byte-identical
to the previously reviewed one. A fresh exact-source replay at reference
`2f63afda261888e04ec57237290e723190914a1d` passes all 194 declarations and
twelve selected headlines; see
[the report](center-runs-current-upstream-report.json). These bounds remain
credited to Luis Perez Morales and Claude (Fable 5.1).

The reviewed white-tail notebook remains byte-for-byte unchanged at its
published hash. It carries the original dependency source and its own full
kernel check, independently of a future kit namespace change. Its scope and
the requested submission approval are unchanged. No new prize API submission
has been made. Historical source/checker reports remain preserved alongside
these current-source reports.
