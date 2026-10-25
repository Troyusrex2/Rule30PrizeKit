# Reproducing the owned worker checks

Use a separate workspace on a Windows x64 host. Python needs `psutil`;
numerical research additionally uses the campaign's documented NumPy,
SciPy, Python-SAT and optional CVXPY environments. The proof checker uses
Lean 4.35.0 and the exact recorded kit commit, not Python numerical results.

The archive/toolchain cache and compiled objects are deliberately not in Git.
All mathematical sources and complete checker JSON reports are published.
The report `MEMORY-AND-NEW-TARGET.md` describes measured resource use and
distinguishes successful checks from resource stops.

1. Prepare the campaign's official reference checkout and compiled official
   `Ruliology` imports at the recorded pin. `prepare.py` explicitly selects
   the ten owned sources and required Lean files, writes a public-kit Git
   bundle, and creates a hashed payload under `_cache`. Its workspace layout
   is inherited from the campaign's `core.py`; adjust the two workspace
   locations for a fresh installation rather than copying personal files.
2. Create an isolated worker root (the scripts default to
   `Path.home() / 'Rule30-offload'`) with `_cache`, `README.md` and an
   `OWNER.txt` containing `Rule30 research worker; created 2026-10-25`.
   Transfer only the generated payload archive, its transfer manifest and
   `bootstrap.py`. Run `python bootstrap.py --archive-sha <recorded-sha>`.
   Bootstrap checks the archive, clones the bundled kit without line-ending
   conversion, checks the official checker hash and runs the dependency and
   probe checks. It does not configure SSH, activation or application settings.
3. The initial probe replay may hit the 16 GiB guard after compilation has
   passed. On a host with sufficient free RAM, `replay_probe.py` retries only
   that already-built probe under the separately recorded 24 GiB cap and
   16 GiB system-free guard. This is optional for the partitioned certificate.
4. On the source host, run `prepare_budget8.py` followed by
   `prepare_budget8_v2.py`. The second script creates a new control directory
   and checks the exact corrected root source hash. Keep the V1 directory
   as provenance; use the **V2** directory for the actual complete run.
   Transfer that directory into the isolated worker's `_cache` and run its
   `budget8_worker.py`. It checks all input hashes, builds and independently
   replays the helper and 404 leaves, then builds and replays the V2 root.
   The three concurrent jobs each have a 300-second, 8 GiB process-tree cap
   and a 16 GiB system-free guard. Do not run multiple copies over the same
   reference build directory.
5. Exact resume requires matching report/source/object hashes. A compilation
   success alone is insufficient. Check the final root's complete official
   JSON, each leaf's full replay, every headline and the unchanged checker
   hash. The prototype join's `change` resource stop is not a certificate.

The actual first run started with the V1 leaf batch, while the separate
`complete_budget8_v2.py` waited for all 404 checked leaves and checked the
corrected root. The fresh V2 control directory reproduces the same mathematical
sources without running the slow prototype root. `collect_budget8.py` checks
the actual run's source and import-object hashes before collecting its reports;
it expects the actual run's V1 control-directory name.

For the two small new local modules, copy their exact sources to the prepared
official reference checkout and use the existing campaign verifier. For the
coupled bridge, install the checked partition imports first, or rebuild them
from the published `budget8-partition/formal` sources. All checks are ordinary
`Check.lean --claim partial` checks with the published headline names. They do
not ask the checker to recognize a complete prize solution.
