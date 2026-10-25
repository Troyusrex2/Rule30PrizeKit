# Reproduction

Run `python -B verify_artifacts.py` for a read-only saved-artifact audit;
`--staged` audits actual staged Git blobs. Do not rerun writing jobs inside
the immutable archive. Use a disposable copy and adjust the Windows paths.

Proof: Lean 4.35.0, current verifier kit0090056412733accaa27643d3cbbf982104f2251.
The historical five-module replay order is TailClasses, PeriodicReconstruction,
DelayedDefect, DelayedPeriods, QuantitativeDelayed (all names prefixed Rule30
and suffixed Research); their reports record the earlier 3eca pin. The merged
catalog is core-only and independent of PR24. Apply the three-file PR25 diff
to the current pin; run check_catalog_current.py with adjusted paths. It runs
lake build then the unchanged official full kernel checker, with the headline
names in its report. The standalone Rule30Submission source can instead use
replay_current.py. Require successful full replay, all headlines and no new
axioms, not only a build or axiom list.

Finite searches use Python3.12 and psutil5.9. cyclic_preimages.py checks small
rings then searches depth97. cyclic_depth.py searches deeper until the node
cap. derive_cycles.py independently checks every saved edge and produces the
selected ancestor path. Decompress cyclic-depth.json.gz before running it.
golden_density.py and delayed_defects.py are deterministic falsification
experiments; none certifies actual finite-right realizability. Use
`python -B guard.py SCRIPT.py` for each job. Guard limits are 300 seconds,
8 GiB owned process-tree RSS and 2 GiB minimum system available memory.

Essay: Wolfram Engine15 and LeanLink with matching Lean4.35 runtime. Run
build_essay.py then check_essay.py in fresh processes, under guard.py. On
Windows the saved wrappers use the already-existing official-source local
bridge build and process-only ELAN_HOME; elsewhere use your matching installed
LeanLink and remove that local PacletDirectoryLoad wrapper. The notebook's
own cells use only Needs, RULE30PRIZE_KIT and embedded source. No cloud sign-in
or API submission is needed for local build/check. preview_controls.py checks
the extracted UTF-8 bytes, notebook hashes and805 independent plotted cells.
Do not submit this draft without showing it to the human and obtaining fresh
explicit consent. Prior GitHub publication authorization is separate.
