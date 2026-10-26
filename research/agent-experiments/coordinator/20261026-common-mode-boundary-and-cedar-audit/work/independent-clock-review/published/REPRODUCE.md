# Reproduction

Use Lean4.35.0 and the reference kit at
5473ffd075f63c9d626e63b8455805d4831b39ca. Keep Check.lean unchanged;
its SHA-256 is b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905.
Build the kit's normal dependencies, then copy work/*.lean and
work/dependencies/*.lean into the checkout's lean/ directory.

Compile in order: Rule30CommonPastResearch, Rule30OrClockObserverResearch,
Rule30ClockJetResearch, Rule30ClockModeResearch,
Rule30EvenModeRigidityResearch, Rule30SaturatedOrPeriodResearch,
Rule30PeriodicOrPeriodResearch, Rule30PeriodicOrPairCertificate,
Rule30TwoPlateauClockResearch.

For each M: `lake env lean -o .lake/build/lib/lean/M.olean lean/M.lean`.
Fully replay each of the final three modules with
`lake env lean --run Check.lean M --claim partial`, adding the
`--headline Fully.Qualified.Name` options listed in work/formal/M/report.json.
Compilation or an axiom-only audit is not a full kernel replay.

The original Windows runner targets private owned paths and an existing
read-only reference cache. The source-order instructions above are portable.
All Python experiments here use the standard library; the historical
resource guard uses an existing psutil installation. Run generators and
controls in a fresh copy because they write source or JSON result files.
`python -B verify_artifacts.py` checks hashes, provenance, reports, guards
and scope; add `--staged` to read the staged Git bytes. This audit does not
replace rerunning Lean. No new prize submission is included.
