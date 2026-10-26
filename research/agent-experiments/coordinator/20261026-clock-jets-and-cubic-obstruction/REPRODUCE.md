# Reproduce this checkpoint

Use Lean v4.35.0 and the unchanged reference kit at
`0090056412733accaa27643d3cbbf982104f2251`. `Check.lean` must have SHA-256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
The evidence was produced in an isolated project on G913; no installed
PowerToys configuration was touched.

First run `python verify_artifacts.py`. The same script supports `--staged`
for checking actual staged Git bytes.

Copy the Lean files from `work` into a disposable reference project and
build these dependencies in order:

```
Rule30CommonPastResearch
Rule30ColumnReaderResearch
Rule30ReaderEquivalenceResearch
Rule30ReaderCanonicalResearch
Rule30OrClockObserverResearch
Rule30ReaderObserverReductionResearch
Rule30ClockJetResearch
Rule30CubicCertificateData
```

Build the 26 modules in `work/certificate-check-modules.json`, then
`Rule30CubicPackedSemanticsV2`, `Rule30CubicOrbitSemantics`,
`Rule30CubicCertificateChecked`, and `Rule30CubicPhaseSemantics`.
For each module, use the normal `lake build <module>` followed by
`lake env lean --run Check.lean <module> --claim partial --headline <name>`.
The exact headlines and commands are in its saved `work/formal` logs and
`work/replay.py`. That wrapper uses an owned G913 project path; adapt paths
for a fresh machine rather than overwriting an existing project.

Every new module built and replayed in under one minute and below 2 GB
owned RSS in the recorded runs. The research guard remains 300 seconds,
8 GiB owned RSS and 2 GiB system available; it kills only its owned tree.
No native proof shortcuts, new axioms or checker changes are used.

For the independent literal audit, Python needs NumPy. From `work`, run
`python guard.py audit_orbit_witness.py`. It reconstructs all width-105
initial rows, checks literal rule-30 cells for 128 steps and checks every
head monomial through degree three. It does not rerun the larger search.

`clock_cubic_large.py` additionally needs Numba. Its full packed matrix
uses about 939 MB before working storage. The original search and
minimization are reproducible from the included sources; the literal audit
does not depend on their GF(2) implementation.

The WL control requires a locally activated Wolfram Engine. `wl_control.py`
invokes the included `wolfram_control.wls`. It performs no cloud sign-in,
installation or submission. Adjust the executable path if necessary.

Failed list/tactic benchmarks are preserved as failures. They are not
part of the passing build order. The complete cubic impossibility theorem
and the prize problem are not asserted by these modules.
