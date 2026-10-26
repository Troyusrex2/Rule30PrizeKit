# Reproduce

Run `python -B verify_artifacts.py` from this archive first. It checks hashes
and recorded full-kernel reports; it does not rerun Lean or the census.
`--staged` reads the actual Git index when preparing a commit.

The four Lean files in `work` require the official Rule30PrizeKit at
`0090056412733accaa27643d3cbbf982104f2251`, Lean 4.35.0, and its built core.
Compile in dependency order: CommonPast, ColumnReader, ReaderEquivalence,
ReaderCanonical. `work/replay.py` records the exact isolated-project commands
and all headline names used. Adapt its owner/project paths to a separate
scratch project. Do not edit the official checker. Build each module then
run the pinned `Check.lean MODULE --claim partial --headline ...`.
The checker replays every declaration, not just the headlines.

Python controls: `reader_equivalence_audit.py`, `canonical_audit.py`,
`audit_canonical.py`. `generate_equivalence.py` and `generate_canonical.py`
produce the Lean modules from their templates and certificates; preserve
UTF-8 bytes. The checked source hashes are in the formal reports.

For the exact finite census, install NumPy and Numba in an isolated Python
environment and run `orbit_partition.py` (widths 1..24). Run `audit_orbits.py`
afterwards for the independent literal and rotation controls. The generated
`orbit_partition_large.py` repeats width 8 then runs widths 25..30; it needs
several GB of free memory. All matches are exact despite hash indexing.
The original machine versions are recorded in `work/versions*.json`.

`canonical_rank.py` requires Z3; adapt its dependency search path. Its 18
UNSAT outcomes are diagnostics for that template, not Lean proofs. The
source has a 140-second overall deadline and a six-second solver timeout.

The Wolfram control runs with a locally activated Engine, using
`wolframscript -file wolfram_control.wls`; no sign-in, cloud, or submission
is required. `wl_control.py` only supplies the local executable path and
checks the output.

All executed research jobs used the unchanged `guard.py`: 300 seconds,
8 GiB owned-tree RSS, and a 2 GiB minimum free-memory floor. Guard logs
record observed usage. Do not increase limits to reproduce a result
without first checking available resources. None of these scripts changes
PowerToys or either computer's real Mouse Without Borders settings.
