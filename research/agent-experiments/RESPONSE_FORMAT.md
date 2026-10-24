# Response format for multiple agents and experiments

Campaign ID: **`rule30-20261024`**. The unit of review is a **finding**, not an
entire agent or batch. One response can contain several findings with different
statuses, and an agent can send as many independent responses as needed.

## IDs and folder layout

Create your own ID without waiting for a coordinator:

```text
r30-<agent-slug>-<run-start-UTC>-<8-random-hex-digits>-v01
r30-agent-a-20261024T213000Z-7f3a2c91-v01
```

The timestamp plus random suffix prevents collisions between simultaneous
runs. Use a stable lowercase agent slug. Independent runs get new IDs.
Revisions retain the run's stem and increment `v01` to `v02`, etc.

```text
<response_id>/
  manifest.json
  REPORT.md
  src/                         optional Lean, Wolfram, Python, or other source
  evidence/                    checker JSON, data, derivations, counterexamples
  logs/                        relevant build and replay output
  READY                        empty file written last
```

Copy the [manifest template](templates/manifest.json) and
[report template](templates/REPORT.md), replace their example content, and
delete unused example findings. The [JSON schema](manifest.schema.json)
describes the manifest. Templates are examples, not real submissions.

The directory name must equal `response_id`. Complete the report, artifacts,
hashes, and manifest before creating `READY`. The coordinator ignores local
folders without that marker. Git commits and PRs should contain complete
response folders, including `READY`.

## Where to send it

**Remote:** open a PR to
[`Troyusrex2/Rule30PrizeKit`](https://github.com/Troyusrex2/Rule30PrizeKit),
base **`research/unbounded-sparse-20261024`**, adding your directory at
**`research/agent-experiments/responses/<response_id>/`**. Use a separate
fork/branch and send Troy the PR link. A PR may add several distinct response
directories. Do not target the official upstream kit for routine intake.

**Local:** use **`D:\MWB\Rule30\agent-inbox\<response_id>\`**. This inbox is
outside the working checkout. Each agent writes only its own directory.

**Fallback:** send Troy the complete folder/archive and its response ID. The
coordinator can import it. A report in chat can summarize a finding, but keep
source and evidence files with the response for reproduction.

Do not edit a shared response file or another agent's folder. Do not update
the [coordinator's index](responses/INDEX.md); unique directories let several
PRs and local deliveries coexist without contending over that file.

## Multiple findings and mixed outcomes

`manifest.findings` is an array. Assign local IDs `F001`, `F002`, etc., unique
within that response. Their global references are

```text
<response_id>#F001
```

A single batch can contain, for example, `F001` with an experimental invariant,
`F002` with a failed strengthening, and `F003` with a kernel-checked lemma.
Each has its own exact claim, scope, evidence, limitations, and next action.
**One proved lemma does not verify the other findings in the batch.**

Use these statuses:

| Status | Meaning |
|---|---|
| `EXPERIMENT` | A computation, derivation, or idea awaiting formal verification. |
| `FAILED` | A proposed claim or method failed; explain precisely how and over what scope. |
| `COUNTEREXAMPLE_CANDIDATE` | A purported counterexample whose exact scope or infinite validity still needs review. |
| `PARTIAL_KERNEL_CHECKED` | A partial theorem passed rebuild and full replay against the unchanged checker; include the evidence. |
| `FULL_SOLUTION_CANDIDATE` | The exact official full statement passed the required local checks; independent reproduction and prize review remain separate. |

The `verification` object belongs to each finding, so batches can include
different modules or checker pins. `full_kernel_replay` requires the actual
module, headlines, pin, commands, full checker-report artifact, and an unchanged
checker. `finite_computation` must state its limits in the report. Never use
a local status to imply Wolfram human review or a prize award.

Use `depends_on` and `conflicts_with` for global finding references. Explain
the exact dependency or conflict in `REPORT.md`. A result can conflict with
another agent's finding without overwriting or closing that response.

## Revisions and supersession

Keep earlier records. A revised response is a **new complete directory** with
a new version ID and `supersedes: ["<prior_response_id>"]`. Include the unchanged
findings as well as the corrected ones, and describe the changes. A combined
revision may supersede several responses. An unrelated new experiment should
not supersede old work merely because it is newer.

For example, these can all be present simultaneously:

```text
r30-agent-a-20261024T213000Z-7f3a2c91-v01/
r30-agent-b-20261024T213100Z-91d2aef0-v01/
r30-agent-a-20261024T214500Z-cf54b8a2-v01/   another independent run
r30-agent-a-20261024T213000Z-7f3a2c91-v02/   supersedes the first response
```

The index keeps historical rows and marks supersession. It can record separate
dispositions for each finding: received, reproducing, verified, rejected,
integrated, or superseded. The submitted status is the agent's report; the
coordinator's disposition is a separate review decision.

## Evidence required for a useful finding

In `REPORT.md`, state the exact proposition or experiment, assumptions, what
was observed/proved, what it implies, what remains unproved, and the next
action. Include failed tests that materially change the conclusion.

List artifacts once in `manifest.artifacts`; findings refer to their IDs in
`evidence_artifact_ids`. This lets several findings share a source or dataset
without duplicating it. Use paths relative to the response directory and
SHA-256 hashes of the actual files. Include all custom Lean dependencies and
their provenance. Do not include private machine settings, credentials,
authentication output, or unrelated personal files.

An infinite counterexample needs an invariant, induction, coinductive argument,
or finite-state cycle with a proved semantic bridge. A long prefix is not an
infinite witness. State whether it refutes Problem 1 itself, Q01, a stronger
sufficient condition, a recovery bound, or only a proposed implementation.

For a negative result, preserve enough detail to avoid rerunning the same
failed idea. For a positive result, identify the precise missing implication
it supplies. If no unbounded argument emerged, say so directly.

The schema checks structure, not mathematical correctness. During intake the
coordinator additionally checks unique response/finding/artifact IDs, folder
names, relative paths, actual file hashes, dependency references, exact theorem
types, and the reported verification scope. Code is reviewed before execution.
