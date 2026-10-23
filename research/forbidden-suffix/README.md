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

The standalone catalog proof is checked separately. The essay's notebook source
adds the required `import Rule30PrizeKit`, beyond that catalog proof. No Wolfram
kernel or LeanLink evaluation was performed, no notebook was built, and no prize
API submission was made. The exact final notebook environment must still be
evaluated and checked. The earlier downloaded essay is untouched.

## Build the Wolfram notebook

`build-notebook.wl` performs a LeanLink preflight of the exact notebook source,
builds the notebook with caching disabled, and checks the notebook's own
`rule30Submission` environment. It never calls the prize submission API.
Its syntax has been checked by Wolfram's remote evaluator; local execution still
requires an installed, activated Wolfram Engine or Mathematica, version 14.3 or later.

Start a fresh kernel with Lean 4.35.0's `bin` directory on `PATH`, then evaluate:

```wl
SetEnvironment["RULE30PRIZE_KIT" -> "/absolute/path/to/prepared/pinned/kit"];
Get["/absolute/path/to/research/forbidden-suffix/build-notebook.wl",
  CharacterEncoding -> "UTF-8"]
```

The default output is beside the essay. `RULE30_NOTEBOOK_OUTPUT` can specify a
different output path. A successful run writes a `.verification.json` sidecar.
Human authorship and explicit consent remain required before any prize submission.
