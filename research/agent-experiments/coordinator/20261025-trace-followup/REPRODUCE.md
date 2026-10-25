# Reproduce without editing the archive

`python -B verify_artifacts.py` reads the byte manifest and scope evidence.
`--staged` reads actual index blobs before a commit. The audit references the
earlier frozen standalone proof report in 20261025-product-parity.

Copy work to a scratch directory for runs. Python 3.12 / psutil are used by
guard.py; unrestricted_right_probe.py also needs z3-solver 5.3.1.0. Adapt the
recorded workspace dependency path or provide the normal z3 package. Neither
SAT nor UNSAT is a Lean proof. Run the two mathematical probes via guard.py.

The existing conditional bridge can be independently rebuilt and checked via
audit_trace_bridge.py with the recorded verifier pin and unchanged Check.lean.
Adapt the local paths for your machine; do not change the checker or theorem.

The Wolfram launchers record this Windows machine's engine, toolchain and
LeanLink paclet paths. Adapt those launcher paths in the scratch copy. The
notebook itself obtains the kit from RULE30PRIZE_KIT and carries the proof;
it does not depend on the local source file. `workflow_canary.py` builds and
checks a small tool-test notebook in two separate plain kernels. It is not
validation of the large proof notebook.

`package_product_preview.py` uses Evaluate -> False and checks the actual
large embedded string without executing the proof. The preview's filename
and metadata say unevaluated. Only build_product_essay.py followed by
fresh_product_essay.py, each under guard.py, can complete the large workflow.
The full launch threshold is 10,500,000,000 available bytes; the runtime
guards remain 300 s, 8 GiB owned-tree RSS and 2 GiB minimum available RAM.
Do not treat a launch skip, wait timeout, old report or canary pass as a full
fresh notebook pass. No submission is performed by these scripts.
