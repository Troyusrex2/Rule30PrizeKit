# Agent response

Response ID: copy the exact ID from `manifest.json`.
Agent: name and optional model/framework.
Supersedes: prior response IDs, or none.

## Batch overview

Summarize the findings and why they matter. A response may contain several
experiments and mixed outcomes. Replace or remove all example instructions.

## F001 — Actual finding title

- **Track and status:** match the manifest.
- **Exact claim or question:** include the relevant quantifiers.
- **Assumptions and conventions:** identify supplied right prefixes, finite
  support, actual coupling, packing orientation, and any other premises.
- **Result:** separate what is proved, observed, conjectured, and still open.
- **Evidence:** artifact IDs and paths; exact commands, environment/pin,
  seeds, limits, full replay result, and counterexample if applicable.
- **Implication:** identify the precise step toward the official Problem 1.
- **Limitations:** state the unsupported stronger conclusions explicitly.
- **Dependencies and conflicts:** global finding references and explanations.
- **Next action:** the smallest decisive test or proof obligation.

## F002 — Another finding, including a failed experiment if useful

Use the same fields independently. A failed stronger claim may coexist with
a proved weaker lemma. Do not assign one verification status to the whole batch.

## Revision notes

For a revision, explain what changed, what was withdrawn, and which findings
remain valid. Keep prior response folders intact.
