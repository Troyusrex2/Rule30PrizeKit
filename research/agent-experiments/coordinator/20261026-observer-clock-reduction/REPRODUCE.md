# Reproduce

Run `python -B verify_artifacts.py` here to check selected bytes and recorded
claims. It does not rerun Lean. `--staged` checks the Git index.

The six Lean sources in `work` build against Rule30PrizeKit commit
`0090056412733accaa27643d3cbbf982104f2251` and Lean 4.35.0. Build and fully
replay them in the order in `replay_dependencies.py`. Adapt the fixed owner
and scratch-project paths in `replay.py`, keeping the official checker
unchanged. All headlines and exact commands are recorded there. Dependencies
have byte-identical hashes to the previous published modules.

For the extension proof, run `extension_audit.py` then
`generate_extension.py`. The latter uses `observer_reduction_template.lean`
and writes the 250-state certificate in five chunks. UTF-8 source bytes must
match the formal report. The mathematical reductions are in the template,
not synthesized or assumed by the Python generator.

The local inverse controls are `plateau_probe.py` (Z3, adapt the dependency
search path) and `independent_control.py` (Python standard library). The
formal plateau witness is fixed in the Lean source; a different Z3 version
may find a different valid witness for its separate diagnostic.

`wolfram_control.wls` runs with an activated local Engine using
`wolframscript -file wolfram_control.wls`. No cloud or sign-in is needed.

`work/diagnostics` is self-contained for the algebra experiments. Use NumPy
and Numba for `nonlinear_decoder_fast.py`; it first checks common-layer ranks
and targets against `nonlinear-decoder-probe.json`, then tests width 14.
`nonlinear_decoder_probe.py` is the slower independent Python implementation
and overwrites its own result JSON when rerun. Both use exhaustive truth
tables, constants and a complete polynomial-span layer, not sampled states.

`extract_newton_decoder.py` regenerates the explicit finite filters and
independently validates them with literal Rule 30 trajectories and the
bit-subset definition of each difference coefficient. `audit_linear_decoder.py`
checks code-coordinate 1; `audit_penultimate_linear.py` runs it for coordinate
2, the penultimate bit at width five. The four-row certificates rule out
affine parity-only filters over all times because the full periods return.

`mealy_probe.py` checks the bounded closed composition automaton and its
literal section controls. It does not prove unbounded semigroup freeness.

All jobs ran through the unchanged `guard.py` with 300 seconds, 8 GiB owned
RSS, and a 2 GiB free-memory floor. Replay reports, guard logs, and artifact
hashes are included. No script changes the computers' real PowerToys settings
or copies activation/authentication material.
