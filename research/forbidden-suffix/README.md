# Forbidden suffixes: tails of unrestricted length

For every Boolean word `v`, no column of a configuration with a leftmost black cell
eventually repeats any of the following words:

| Word | Sufficient bound |
|---|---:|
| `0^r v 011` | `r >= 10*length(v)+41` |
| `0^r v 001001` | `r >= 10*length(v)+71` |
| `0^r v 111001` | `r >= 10*length(v)+71` |

The word `v` has no length restriction. The transient and column are unrestricted.
The result includes every nonzero finite initial pattern and the single seed.
For example `0^r (10)^k 011` is excluded when `r >= 20*k+41`, for every `k`.

This is an arbitrary-prefix corollary of the earlier white-pulse reduction, using
three small vacuum-free full-set images. It extends the supplied essay beyond
bounded-length tail families. Small instances overlap known results; global
novelty has not been established. It does not solve period two or any full prize
problem.

Proof and formalization: OpenAI Codex through GitHub account `Troyusrex2`, building
on the earlier research branch and the kit's uniform Jen and black-shield results.

## Files

- [Essay addendum](Rule30-Forbidden-Suffix-Addendum.md): prose, exact claims, and
  embedded self-contained proof in unevaluated LeanLink cells.
- [Generic criterion](../../lean/Ruliology/CellularAutomata/Rule30ForbiddenSuffixResearch.lean).
- [Families](../../lean/Ruliology/CellularAutomata/Rule30SuffixFamiliesResearch.lean).
- [Finite certificates](../../lean/Ruliology/CellularAutomata/Rule30Certificates/ForbiddenSuffixResearch.lean).
- [Standalone catalog proof](Rule30SuffixStandalone.lean), including all research
  dependencies, using only official modules available at the pinned kit commit.
- [Catalog evidence](evidence/catalog/summary.json) and
  [pinned evidence](evidence/pinned/summary.json), with full checker reports beside
  them; [independent computations](evidence/independent-checks.json).

## Reproduce

From the repository root, with Lean 4.35.0 available:

```sh
python tests/check_forbidden_suffix_research.py
python research/forbidden-suffix/verify.py --lake /absolute/path/to/lake
```

The verifier script builds the target and runs unchanged `Check.lean` on every
research module in its dependency chain, not just the final theorem. Core Lean
suffices; these catalog checks do not require Mathlib.

To check against the verifier's pinned commit, create a **separate worktree**:

```sh
git worktree add --detach ../rule30-suffix-pinned cc1e0e0e7c1ae8c971aec5c14aaabb47c7b8c554
python research/forbidden-suffix/verify.py --kit ../rule30-suffix-pinned --prepare-pinned --lake /absolute/path/to/lake
```

`--prepare-pinned` copies only the seven proof modules into that worktree, removes
`module` and `@[expose] public section`, and replaces `public import` with `import`.
The older pinned kit predates that module-system conversion. Proof bodies stay
unchanged. Different existing files are never overwritten. The evidence records
the exact source hashes, kit commit, toolchain, and unmodified checker hash.

Run `python research/forbidden-suffix/bundle.py` to regenerate the standalone proof
and essay from the catalog sources. To replay the standalone proof, copy it into
the pinned worktree as
`lean/Ruliology/CellularAutomata/Rule30SuffixStandaloneResearch.lean`, then run from
that worktree's `lean` directory:

```sh
lake build Ruliology.CellularAutomata.Rule30SuffixStandaloneResearch
lake env lean --run ../Check.lean Ruliology.CellularAutomata.Rule30SuffixStandaloneResearch --claim partial --headline Rule30Submission.no_padding_suffix011 --headline Rule30Submission.no_padding_suffix001001 --headline Rule30Submission.no_padding_suffix111001
```

## Local validation and limits

All seven modules passed complete kernel replay on both kit versions, with only
standard axioms. The three finite certificates were also checked by a separate
cellwise implementation over all 8,448 initial-strip/right-boundary trajectories.
Four negative controls produce actual vacuum witnesses.

The standalone catalog proof is checked separately. The essay's exact embedded
source, including the required `import Rule30PrizeKit`, also passes a root-project
build and unchanged-checker replay at the pinned commit: 252 local declarations
and all three headlines. See `evidence/notebook-source/summary.json`. The earlier
standalone-only check reports 253 declarations because the root import already
provides one helper declaration.

The [built notebook](Rule30-Forbidden-Suffix-Addendum.nb) now passes actual local
Wolfram/LeanLink evaluation and kernel replay: 252 declarations, all three
headline axioms standard. Its saved input preserves the exact checked source,
and its saved outputs contain the successful replay with zero message cells.
See `evidence/wolfram-notebook/`. Submission [R30-20261023-8fe04c](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261023-8fe04c) is now **Lean Verified** by the prize system, with standard axioms only. The signed-in submitter and reviewers can open that page. The sanitized verifier report is `evidence/wolfram-notebook/submission.json`. Human review remains pending. The original downloaded essay is untouched.

## Build the Wolfram notebook

`build-notebook.wl` verifies the exact embedded source, evaluates with caching
disabled, and validates the notebook's own saved module replay, theorem kinds,
and permitted headline axioms. One replay checks every declaration of the module.
It never calls the prize submission API. The optional
`RULE30_MARKDOWN_CONVERTER_SOURCE` selects the converter's local public `.wl`
source. See [Windows build notes](../windows-notebook/README.md) for the tested
LeanLink workaround and starter validation.

Start a fresh kernel with Lean 4.35.0's `bin` directory on `PATH`, then evaluate:

```wl
SetEnvironment["RULE30PRIZE_KIT" -> "/absolute/path/to/prepared/pinned/kit"];
Get["/absolute/path/to/research/forbidden-suffix/build-notebook.wl",
  CharacterEncoding -> "UTF-8"]
```

The default output is beside the essay. `RULE30_NOTEBOOK_OUTPUT` can specify a
different output path. A successful run writes a `.verification.json` sidecar.
Troy Lowry supplied the author name and explicit consent; the completed submission is linked above.
