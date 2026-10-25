# Tail-13 integration after kit review

[PR #16](https://github.com/WolframInstitute/Rule30PrizeKit/pull/16) now contains
the consolidated method and its infinite-family application at commit
[`ad62be4`](https://github.com/Troyusrex2/Rule30PrizeKit/tree/ad62be4ddb5559e5f0a6d921963463c41f9d2e3f).
PR #15 is closed as superseded. The older reports in this directory retain
their original sources and verification records for reproduction.

The change responds to the kit contributor's actual
[review](https://github.com/WolframInstitute/Rule30PrizeKit/pull/16#issuecomment-6391541123):
one method module, one data module, an actual infinite-family use of the
checker, credits in README rows, measured build costs, build-script entries,
and the updated module count. Upstream sandbox verification and merge remain
pending. No prize solution or new prize API essay is claimed.

## Result and method

For every odd `m`, `row4 m 13` has a white depth-1 cell at an even time
`t <= m + 45`. The theorem `stripe_four_tail_complete` then covers all sixteen
four-bit stripe tails, with the precise arrival-relative bound in its type.
This completes the previously omitted tail-13 class; it does not prove Q01
or Prize Problem 1.

There are three catalog modules:

| Module | Checked declarations | Role |
|---|---:|---|
| `Rule30ZeroBoundaryStripeFrontLift` | 225 | Width projection, universal return periods, parallel semantics and general sparse return-map lifting |
| `Rule30Certificates/StripeTail13Completion` | 70 | Punctured lower cycle, parallel endpoint checks, return cycle and exceptional-residue tests |
| `Rule30ZeroBoundaryStripeFourComplete` | 31 | Infinite-family proof in its own namespace |

The parallel certificate uses the 32 upper states actually visited by the
return orbit. The general `run_correct` lemma supports arbitrary initial
lane values, so no all-4096-input table is needed for this particular cycle.
`return_map_cycle_lift` combines the checked 65,536-step return, the 32-step
index cycle and the exceptional-residue witnesses into a width-46 cycle of
period 2,097,152. This theorem is a return certificate, not a claim of least
period or an arbitrary-tail result.

The lower punctured width-34 cycle is by G.P.J.W. Quint and Gemini,
[R30-20261024-f177ae](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261024-f177ae).
Its needed segment checks and lemmas are included and replayed in the data
module. The catalog README credits that work and Ying Yin/Codex's stripe-front
method. The new parallel completion and integration are by Troy Lowry with
OpenAI Codex.

## Validation and costs

All **326 declarations** pass the unchanged official checker's complete
kernel replay at base `3eca23c0a9fa6b153313655e6d51835406c2d06e`, with standard
axioms only. Each normal module build passes. The complete `Ruliology` build
also passes, 124 jobs; the shell build script parses, and the actual module
count is 121. The staged bytes were checked against the replayed source
hashes before commit.

Measured on Windows x64 with Lean 4.35.0, each module alone with imports
compiled. Peak memory is summed process RSS, sampled every 50 ms:

| Module | Build time | Peak RSS |
|---|---:|---:|
| Method | 7.203 s | 0.725 GB |
| Data | 68.938 s | 1.992 GB |
| Family | 6.031 s | 0.663 GB |
| Original 256-segment data, merged into one module | 146.797 s | 0.990 GB |

The new data also beats the review's 86-second reference. Its higher memory
use remains below the catalog's 4-GB data limit. The earlier 4096-lane version
took 70.703 seconds on this host; reducing it to 32 lanes mainly shrinks the
source, rather than producing a proportional runtime gain.

The successful JSON reports retain the original standalone measurements.
Cached build logs are excluded from the timing evidence. Resume validation
checks the compiled objects in the nested `lean` package.

## Reproduce

Check out catalog commit `ad62be4ddb5559e5f0a6d921963463c41f9d2e3f` with the
pinned toolchain and dependencies. Build the baseline imports sequentially
as described in the kit README. From this research directory, run:

```text
python verify_reviewed_front_catalog.py --project PATH_TO_CATALOG --lake PATH_TO_LAKE --output PATH_TO_FRESH_REPORTS
```

The script verifies the reference checker, the allowed source changes and
the exact source/metadata hashes, then normally builds and fully replays all
three modules in dependency order. It retains the 300-second, 8-GiB RSS and
2-GiB-free guard. `--resume` requires matching successful reports and existing
compiled objects. To check the umbrella, run `lake build Ruliology` in the
reviewed checkout.

For cold timing, the target must not already be built, and its imports must
be compiled. A cached `lake build` measures cache validation, not compilation.
The original monolithic benchmark source and its source hash are retained
separately; its normal compiler run used the same pinned baseline imports.

The final catalog sources, manifest and proof reports are listed in
[reviewed-catalog-artifacts.json](reviewed-catalog-artifacts.json). Preparation
scripts describe the original workspace layout; verification of the final
catalog does not require regenerating the proposed constants.
