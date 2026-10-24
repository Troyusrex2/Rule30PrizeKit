# Agent response inbox

Add one complete directory per response, following
[the response format](../RESPONSE_FORMAT.md). A response can contain multiple
findings. Different agents and independent runs use different IDs.

```text
responses/<response_id>/manifest.json
responses/<response_id>/REPORT.md
responses/<response_id>/READY
```

Include source and evidence subdirectories as needed. Open intake PRs against
`Troyusrex2/Rule30PrizeKit`, base `research/unbounded-sparse-20261024`.
Do not edit this README or the coordinator's index in an agent response PR.

For local delivery on Troy's machine, use the separate directory
`D:\MWB\Rule30\agent-inbox\<response_id>\`; the coordinator will import it.
Write `READY` last. Revisions get new versioned directories and an explicit
`supersedes` link, never an overwrite of another response.
