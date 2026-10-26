# Reproduction

Use the official kit at commit 0090056412733accaa27643d3cbbf982104f2251,
Lean 4.35.0 and the unchanged Check.lean. Copy the two Lean sources in
work to that project. Build and fully replay CommonPast first, then
BlockClock. Each is named with prefix Rule30 and suffix Research.

For module M, run `lean -o .lake/build/lib/lean/M.olean M.lean`, followed
by `lean --run Check.lean M --claim partial` and each `--headline` listed
in work/replay.py. Set LEAN_PATH to that project's .lake/build/lib/lean.
The driver records exact commands and checker/source hashes. Adjust its
isolated G913 project paths if using another machine; do not change the
checker, proof statements, proof terms or kernel-replay requirements.

Run `python -B guard.py independent_control.py` in work. The Wolfram
control runs with `wolframscript -file wolfram_control.wls` and an already
activated local Engine; it requires no cloud sign-in. `wl_control.py`
records its exact CLI output on our installation.

The diagnostics directory contains self-contained fixed-clock graph
probes. `audit_profiles.py` uses their adjacent JSON output directly and
independently rebuilds all six complete clock graphs with a literal CA rule.

The searches directory has generated, directly executable NFA and rank
scripts plus all input sample/graph files. NFA scripts require python-sat
with Minisat22; rank scripts require z3-solver. Their optional private
import paths fall back to installed packages. Run learn_nfa.py,
learn_reverse_nfa.py and learn_hinted_reverse_nfa.py, then audit_nfa.py.
The audit forces a known model only in its explicitly separate encoding
control, not in the actual searches. The rank scripts are
context_lex_rank.py and prefix_lex_rank.py. Solver timeouts and internal
caps do not establish mathematical impossibility.

Python guards require psutil and retain the original 300-second/8-GiB/
2-GiB limits. The full formal replay belongs on a machine with at least
4 GiB available for the process and adequate system headroom. Our final
replay runs on G913 with the same guards. No external Lean file is imported
or presumed verified by the new proof.
