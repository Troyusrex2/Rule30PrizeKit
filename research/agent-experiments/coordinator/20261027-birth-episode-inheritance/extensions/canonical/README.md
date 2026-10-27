# Canonical episode-inheritance evidence

This extension records the catalog version of the parent archive's checked episode-inheritance result. It adds one canonical module, `Ruliology.CellularAutomata.Rule30BirthEpisodeInheritance`, and reuses the parent's six exact official dependency sources and unchanged checker. No dependency source is duplicated here.

The only proof-source changes are the opening and closing namespace declarations: `Rule30BirthEpisodeInheritanceResearch` becomes `Rule30BirthEpisodeInheritance`. [RENAME-DIFF.patch](RENAME-DIFF.patch) records them. All six theorem types and axiom lists, and the entire checker JSON, agree after this exact renaming; see [FINAL-COMPARISON.json](FINAL-COMPARISON.json).

The result is unchanged: during a finite interval of continuous column-two mismatch and equal center readings, there are at most two column-one mismatch births. A second birth must occur at the final source tick and forces column-two agreement at the next reading. Explicit corollaries compare two ages of the same official single-seed orbit. This does not bound the number of parent episodes or establish a global upper birth budget. See the [parent proof](../../PROOF.md) for details.

## Fresh canonical validation

All seven sources were freshly built with core Lean/Lake 4.35.0, with no reference objects or inherited `LEAN_PATH`. The unchanged official checker replayed **37 owned constants and six headlines**, with no new axioms and no source-build warnings. Exact mathematical receipts are in [evidence/fresh7](evidence/fresh7/RESULT.json); all types and axioms are in [Types.log](evidence/fresh7/Types.log). The checker retains its own deprecation warning.

The fresh source build took 8.524 seconds. A three-import compatibility smoke was subsequently attempted in the same guarded process; that smoke failed because two separate library roots sharing the `Ruliology` prefix did not merge missing modules. Thus the original guard exited 1 **after** the successful fresh build and full checker. Both its resource receipt and failed diagnostic are retained; this setup failure is not labelled a successful whole-job run.

A smoke-only retry merged exact hash-checked fresh and historical objects into one owned library. It passed, importing the new module alongside the unchanged `Rule30PeriodicBirthCounterexample` and `Rule30LocalBirthPotential` modules. The retry guard took 0.882 seconds and peaked at 286,261,248 bytes RSS. No source changed or module was recompiled. This is a separate cached-object compatibility check, **not** a fresh combined replay of all three modules. Its [result](evidence/smoke02/RESULT.json), [printed types](evidence/smoke02/ThreeImports.log), and [referenced historical source/object hashes](evidence/smoke02/REFERENCED-OBJECTS.json) are provided without binaries.

[AUDIT.md](AUDIT.md) is an independent static source/type/provenance audit; its reviewer did not run a duplicate build. `PROVENANCE.json` records exact copies and the narrowly documented normalization of private diagnostic prefixes and guard commands.

## Reproduce the canonical seven-source proof

Place this directory at `extensions/canonical` within the parent archive. With Python 3 and an existing Lean/Lake 4.35.0 toolchain:

```text
python verify.py --audit-only
python verify.py --lean /path/to/lean --lake /path/to/lake
```

If the parent archive is elsewhere, pass `--archive /path/to/archive`. The verifier checks the extension manifest, the parent's source metadata, each of the six official files, the canonical file, and the unchanged checker. It creates a unique fresh `runs/<timestamp>/project`, rebuilds exactly seven sources, replays all 37 owned constants with six headlines, and compares printed types and axioms. Existing output directories are rejected. No toolchain installation or contribution-object reuse occurs.

The portable verifier deliberately does not rerun the historical three-import smoke: its two older module closures are outside this focused archive. Their exact source/object references and successful check are historical evidence, clearly separated from the reproducible fresh seven-source proof. No new Lean run was performed merely to package this extension.

Official pin: `7d665044b904117af9e82328aeb90a30692b2b85`. Canonical source SHA-256: `0f145167770fc8f75dffd170f174319363535061c4ace5f97b82fb5b4abb29f0`. The parent research archive was published at commit `6745ed78785dca4f4f8b2c7ca55dfc7012ff3e53`. This is supporting proof evidence, not a Wolfram submission or prize verdict.
