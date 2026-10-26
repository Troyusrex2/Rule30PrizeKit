# Reproduce

First check the archived bytes and validation receipts:

```sh
python verify_artifacts.py
```

For an independent Lean replay, prepare the official repository at commit
`5473ffd075f63c9d626e63b8455805d4831b39ca` with its Lean 4.35.0 toolchain and
compiled official Ruliology dependencies. Use the unchanged root `Check.lean`
(SHA-256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`).
Then run:

```sh
python replay.py --lean /path/to/lean --official-lib /path/to/official/compiled/lib/lean --checker /path/to/Check.lean --output /new/empty/replay-directory
```

The script creates a new output directory, compiles all six included source
modules in dependency order, and runs the official checker for each module and
the same recorded headlines. It never writes into the official checkout or
reuses worker binaries. It fails on source/checker hash changes, a nonpassing
checker verdict, or new axioms. Per-command timeout is 300 seconds. Its output
directory preserves each build log, checker log, and a final receipt.

The included coordinator resource receipts record the original bounded jobs;
the portable reproduction script uses a timeout but does not impose the original
Windows process-tree memory guard. The original jobs stayed below 8 GiB owned
RSS and kept at least 2 GiB available system memory.
