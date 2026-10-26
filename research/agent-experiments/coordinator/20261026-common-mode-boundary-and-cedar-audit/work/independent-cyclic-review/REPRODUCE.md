# Reproduce this review

Use the selected `mode-transient-review` directory as the current working directory. Existing Python, Git, the pinned kit repository, and Lean 4.35.0 are required; this workflow installs nothing. Supply a fresh, owned output directory. The helper extracts the exact kit commit, verifies the unchanged checker hash and supplied module hash, builds official dependencies privately, and runs a complete Check replay.

The actual reviewed command was externally guarded for 300 seconds, 2 GiB process-tree memory, and at least 2 GiB free memory:

```powershell
python -B 'D:/MWB/Rule30/cedar-followup-20261026T154236Z/coordination/run_guarded.py' --cwd 'D:/MWB/Rule30/cedar-followup-20261026T154236Z/verifier/mode-transient-review' --label verifier-mode-transient-replay --seconds 300 --gib 2 -- python -B 'D:/MWB/Rule30/cedar-followup-20261026T154236Z/verifier/mode-transient-review/replay_review.py' --kit-repo 'D:/MWB/Rule30/Rule30PrizeKit' --lean 'D:/MWB/Rule30/toolchain/lean-4.35.0-windows/bin/lean.exe' --out 'D:/MWB/Rule30/cedar-followup-20261026T154236Z/verifier/mode-transient-review/reproduction'
```

The recorded output directory already exists. For a new run choose a different fresh output path. On another machine, replace all paths and use an equivalent external guard; `replay_review.py` has per-subprocess timeouts but does not itself enforce total time, process-tree memory, or minimum free memory. The portable inner command, to be launched under that guard from this directory, is:

```powershell
python -B ./replay_review.py --kit-repo 'PATH/TO/EXISTING/Rule30PrizeKit' --lean 'PATH/TO/lean-4.35.0/bin/lean.exe' --out 'PATH/TO/FRESH/OWNED/OUTPUT'
```

The supplied-cone scalar audit is `python -B ./audit_supplied_cones.py`; it consumes only frozen JSON and never invokes SAT. Its outputs can overwrite the existing audit JSON, so run it in a fresh copy when preserving the evidence package. `freeze_review.py` records how live inputs were captured and the helper was derived; it is provenance, not a required reproduction step.

The exact all-time spatial trajectory audit is `audit_transient.py`; its original run references the prior frozen CommonPast source. The already supplied copy `Rule30CommonPastResearch.frozen.lean` has the required SHA256 `17eb07047e8b1780b25de532e72dcb73385f20eaffa91db366e92c210b394ec3`. When reproducing that auxiliary audit outside the original layout, change its source path to this supplied copy. This path adjustment does not affect the Lean replay or cone audit.
