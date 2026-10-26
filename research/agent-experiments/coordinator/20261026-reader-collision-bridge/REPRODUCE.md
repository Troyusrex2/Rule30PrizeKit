# Reproduction

The formal sources use Lean 4.35.0 at official kit commit
0090056412733accaa27643d3cbbf982104f2251. Copy the five Lean files from
`work/` to that project, set LEAN_PATH to its `.lake/build/lib/lean`, and
compile and run the unchanged Check.lean on each module in this order:

1. Rule30CommonPastResearch
2. Rule30FrontReductionResearch
3. Rule30ColumnReaderResearch
4. Rule30ReaderSeparationResearch
5. Rule30ReaderCollisionBridgeResearch

For each module M, run `lean -o .lake/build/lib/lean/M.olean M.lean`, then
`lean --run Check.lean M --claim partial` with the headlines listed in
`work/replay.py`. That Python driver records the exact commands, checker
hash, source hash, build and full replay output. Its project paths identify
our isolated G913 checkout; adjust only those paths for another installation.
Do not change the checker or bypass imported-module kernel verification.

Run `python -B guard.py independent_audit.py` in `work/` for the independent
literal controls. The script reads the included `learned-reader.json`.
The five case records and exact output are also included for direct
inspection. Run `wolframscript -file wolfram_control.wls` there with an already activated local Engine for the
built-in CA controls. No cloud connection is required.

The search folder includes the input graphs, accumulated ICE samples,
candidate data, outputs and guard logs. Python 3.12 and python-sat 1.9.dev17
with Minisat22 were used. The learners additionally try our private
`toolchain/sat-research` import path, then fall back to installed packages.
Run their guarded scripts in the order `ice_invariant.py`, `ice_safe.py`,
`ice_tree.py`, `ice_dyadic.py`, `ice_dyadic_sym.py`, `ice_typed.py`.
The later scripts warm-start from the included earlier sample files.
`audit_protocol.py` independently validates all six sample sets.
`exact_backward.py` and `audit_backward.py` need only Python's standard
library and the included graphs. The exact run is capped, not a converged
invariant computation.

The unchanged outer `guard.py` needs psutil. It caps one owned process tree
at 300 seconds and 8 GiB, and stops below 2 GiB available system memory.
Searches have additional documented internal limits. Exit code zero with
an output stop reason such as `time_cap` or `composition_state_cap` means
the bounded experiment ended normally, not that its mathematical goal passed.
