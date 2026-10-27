# Physical mismatch episode inheritance

This core Lean project proves a uniform restriction on mismatch births between two actual Rule 30 histories. During a continuous column-two mismatch interval with equal center readings, at most two column-one mismatch births can occur. If two occur, the second is at the last tick of the interval and the column-two mismatch is absent at the next reading.

The module also proves these statements for two ages of the **same official single-seed orbit**, using `cell(Q+t,i) XOR cell(t,i)`. Center equality is required only on the stated finite interval. No center periodicity, global upper birth budget, or prize solution is claimed.

## The checked statements

`Rule30BirthEpisodeInheritanceResearch.lean` uses the official `Rule30Ether.IsR30` recurrence. Its six headline theorems are:

* `death_termination`: if column one dies at source tick `d` while column two differs at both `d` and `d+1`, and the centers agree at `d`, then column two agrees at `d+2`.
* `terminal_second_birth`: under common center readings and continuous column-two mismatch on closed `[A,Z]`, two birth sources `A <= a < b <= Z` force `b=Z` and agreement at column two at `Z+1`.
* `no_ordered_three_births`: three ordered birth sources in that interval are impossible.
* `actual_lag_death`, `actual_terminal_second_birth`, and `actual_no_ordered_three_births`: the corresponding literal single-seed age-pair statements.

The full namespace is `Ruliology.CellularAutomata.Rule30BirthEpisodeInheritanceResearch`. Exact types and axiom lists are in [Types.log](evidence/root-full-lake/Types.log). [PROOF.md](PROOF.md) explains the argument and its limitation.

## Validation

An independent fresh Lake project built **all seven sources**: six official dependencies plus this research module. The unchanged official checker replayed **all 37 owned constants** and accepted **all six headline types**, with no new axioms. All printed headline axiom lists are `propext` and `Quot.sound`. The independent checker JSON equals the successful author result, and printed types and axioms are byte-identical.

The fresh build took 8.512 seconds. The complete guarded job took 10.331 seconds, with 838,643,712 bytes peak owned RSS and no guard stop. Source build logs have zero warnings. The unchanged checker's own deprecation warning remains visible in checker logs. The author run reused six checked dependency objects; the independent run rebuilt every source with no reference objects or inherited `LEAN_PATH`.

See [fresh result](evidence/root-full-lake/RESULT.json), [comparison](evidence/root-full-lake/AUTHOR-COMPARISON.json), and [resource extract](evidence/root-full-lake/RESOURCE-EXTRACT.json). `PROVENANCE.json` distinguishes exact copies from path-normalized diagnostics and resource-only extracts, retaining original hashes. The failed initial proof-script attempt is preserved separately and is not a verification result. No trajectory experiment was rerun for this archive.

## Reproduce

Use Python 3 and Lean/Lake **4.35.0**. No Mathlib or other external Lean package is needed.

```text
python verify.py --audit-only
python verify.py --lean /path/to/lean --lake /path/to/lake
```

The verifier checks the archive hashes, creates a unique fresh `runs/<timestamp>/project`, clears external `LEAN_PATH`, builds the seven sources with Lake, invokes unchanged `Check.lean` for all six names, and compares printed types and axioms with the recorded result. It does not install a toolchain or reuse contribution objects. Supply `--run-name NAME` for an explicit new output directory; an existing directory is rejected.

Official dependency source pin: `7d665044b904117af9e82328aeb90a30692b2b85`. Exact source/configuration hashes, build order, and headline names are in `SOURCES.json`. The checker SHA-256 is `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

This package records a prepared research contribution. `ARCHIVE-STATUS.json` describes its preparation-time status; it is not evidence of a Wolfram backend submission or prize adjudication.
