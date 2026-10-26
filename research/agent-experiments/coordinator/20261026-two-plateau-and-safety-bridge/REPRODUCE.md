# Reproduce at the unchanged official pin

Use an existing Lean4.35.0 installation and a fresh checkout of
5473ffd075f63c9d626e63b8455805d4831b39ca.
Use the kit's normal dependency build. No reference-source edit is needed.

Copy work/dependencies/*.lean and work/*.lean into that checkout's lean/
directory. These five historical dependencies have exactly the source
hashes used in the current reference build; provenance.json records them.
Compile in this order:

1. Rule30CommonPastResearch
2. Rule30OrClockObserverResearch
3. Rule30ClockJetResearch
4. Rule30ClockModeResearch
5. Rule30EvenModeRigidityResearch
6. Rule30SaturatedOrPeriodResearch
7. Rule30PlateauPairCertificate
8. Rule30TwoPlateauRigidityResearch
9. CedarSafetySoundness
10. CedarSafetySemantics
11. CedarSafetyBridge
12. CedarWhiteTransport

From the checkout root, for each module M compile with
`lake env lean -o .lake/build/lib/lean/M.olean lean/M.lean`.
Then fully replay each of the seven new modules6..12 with
`lake env lean --run Check.lean M --claim partial`.
Select headlines with repeated `--headline Fully.Qualified.Name` options;
the exact names and complete checker JSON are in work/formal/.
An axiom audit or ordinary compile alone is not the recorded full replay.

The original Windows runners in work/ and work/evidence/ preserve the
historical execution and path setup; they target isolated owned workspaces,
not generic installations. The source-order procedure above is portable.
All non-solver Python controls use the standard library. The two SAT scripts
also use an existing Z3 installation; no install is part of reproduction.
Run controls in a fresh copy because they write their result JSON.

All source/checker/report and artifact hashes are independently auditable
with verify_artifacts.py. Resource records describe sampled process-tree
memory, with unchanged300s/8GiB-owned/2GiB-free guards. Private agent usage
planning and coordination logs are deliberately excluded from this archive.
