# Independent replay of the new period-two skeleton

G.P.J.W. Quint and Gemini (Google) submitted
[R30-20261024-1e1b3b](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261024-1e1b3b)
on 2026-10-24. Its public status was Lean Verified when fetched. Their proof
is theirs; this directory records an independent audit, not a new contribution
to the skeleton or an official human-review verdict.

The exact published UTF-8 source, including its imports, passes the unchanged
checker at reference `2f63afda261888e04ec57237290e723190914a1d`:
all **57 declarations and 20 submitted headlines** pass full kernel replay
with standard axioms. No proof-source adaptation is made. The hash, authors,
selected headlines and complete checker output are in [report.json](report.json).
The local module name differs from the API module name so the review does
not overwrite an existing `Rule30Submission.lean`.

The result gives conditional forced identities through column -10 and
nonperiodicity of selected free traces **assuming an alternating center**.
It does not prove `Q01`, exclude period two, or solve Problem 1. The free
trace conclusion uses the kit's existing two-column Jen theorem. This is
a useful checked source of identities, not a missing finite-support proof.

Run `audit_period_two_skeleton.py --lake PATH_TO_LAKE --project REFERENCE_CHECKOUT`
from this directory's parent. It requires the exact reference, verifies the
published source hash, and refuses to overwrite different local proof source.
Its dependency build is warm; no cold-build timing is claimed.
