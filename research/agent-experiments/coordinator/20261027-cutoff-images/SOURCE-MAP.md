# Exact source map

- The18 `Ruliology/CellularAutomata` source files are unmodified Git blobs
  from official commit7d665044b904117af9e82328aeb90a30692b2b85. Their hashes
  and dependency order are in `INPUTS.json`.
- `Rule30CutoffImagesResearch.lean` is the exact sealed author source,
  SHA25677ee7d7ed4f01ab01dd9edf8fdbbeded61e6c8e8a798ae5fc7931c92d8771b94.
  No namespace or proof-body transformation was applied.
- `Check.lean` is the unchanged official checker. Its full new-module
  replay includes all generated constants; nine additional headline
  checks and the displayed type/axiom comparison are recorded separately.
- `PAPER.md` is the exact original mathematical cutoff-image note. The
  explicit Lean statements determine the formally verified scope.
- `Types/Rule30CutoffImagesResearch.expected.log` is the exact successful
  author type/axiom receipt. `verify.py` compares its content, allowing only
  whitespace differences in display formatting.
- The author checker's exact mathematical JSON line is retained as
  `evidence/author-targeted/check.raw.json`. Its separately labelled stdout
  copy replaces only a private absolute filename prefix with `Check.lean`;
  the provenance file records both hashes. The new fresh19 checker stdout
  is relative and is copied without any redaction.

The public candidate contains source and evidence only. It contains no
compiled contribution libraries and requires no access to the author
machine or execution host.
