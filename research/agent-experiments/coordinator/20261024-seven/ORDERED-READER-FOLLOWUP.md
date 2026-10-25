# Two checked obstructions and a failed neural rank experiment

Problem 1 and the coupled period-two question remain open. This follow-up
retires the unrestricted zero-run charging conjecture, identifies a defect
in the first recurrent reader, and records the failure of a repaired reader
on longer, untouched tests. It does not claim a uniform rank.

The source and byte hashes are in
[`ordered-reader-artifacts.json`](ordered-reader-artifacts.json). Earlier
reports and manifests are retained unchanged; this report supersedes their
suggestion that the unrestricted zero-run charge might be useful.

## The unrestricted zero-run charge is false

The earlier proposal was

```
zeroRuns s n <= blackCount (Theta s) (2*n+1)
```

for every free stream `s`. Exhaustive length-16 and random longer tests did
not refute it. An adversarial beam found a counterexample at `n=28`:
the chronological free prefix is `0110100100101001010110101010`, followed
by ones in the formal witness. There are **12 zero runs and 11 black cells**
in the counted spatial prefix.

`blackCount L K` counts depths `0..K-1`; depth zero is the white wall.
Thus `blackCount (Theta s) 57` counts the actual spatial depths `1..56`.
There is no missing depth-57 cell in this statement. The additional cell
would be black in this example and would repair that different inequality.

[`Rule30ZeroRunChargeCounterexampleResearch.lean`](Rule30ZeroRunChargeCounterexampleResearch.lean)
links each of 56 computed anti-diagonals to the official reconstruction
using `Rule30ZeroBoundaryLanes.level`, then proves:

- `zero_run_count`: the count is 12;
- `spatial_black_count`: the official `Theta` count is 11;
- `unrestricted_charge_false`: the proposed `ZeroRunSpatialCharge` is false;
- `witness_has_adjacent_zeros`: the witness contains adjacent zeros.

The last fact matters: this does **not** refute `No00SpatialCharge`, the
Golden-language target, the actual coupled target, or the newer critical
drift charge. Those statements remain unproved. The full unchanged checker
replayed all **292 owned declarations**, not just the headline theorem.
See [`zero-run-charge-counterexample-evidence/report.json`](zero-run-charge-counterexample-evidence/report.json).

## Why the first neural reader could not work

The first model read a word left to right and assigned a squared phase
constant plus a sum of nonnegative squared prefix readouts. For a fixed
phase, appending tokens can never decrease this energy.

An exact graph audit found two actual coupled transitions for the finite
mathematical right seed `0x3496`, at depths 8 and 9. Both new spatial bits
are white at both transitions. The phases are `42 -> 21 -> 42`, with
required decreases `1, 0`. The final length-20 word is the original
length-16 word followed by **`[2,1,0,0]`**. Consequently:

```
E42(short) <= E42(long) <= E21(middle) <= E42(short)-1
```

This rules out the whole prefix-monotone rank family, irrespective of
network size or training time. It is not merely an optimization failure.
The Python controls independently reconstruct the driven right dynamics,
the inverse left dynamics and the entire physical left prefix.

[`Rule30PrefixMonotoneRankObstructionResearch.lean`](Rule30PrefixMonotoneRankObstructionResearch.lean)
checks the exact word extension and integer order contradiction;
[`Rule30PrefixMonotoneOrderObstructionResearch.lean`](Rule30PrefixMonotoneOrderObstructionResearch.lean)
states the obstruction for any value type with the explicit order laws,
covering real-valued models as well. Both passed full kernel replay.
The Python-to-official-right-evolution bridge for these two examples is
**not formalized**. This distinction does not apply to the separate
zero-run counterexample above, whose official `Theta` bridge is formal.

## Architectural repair and independent longer tests

V2 adds a squared, word-dependent terminal readout of the last active
hidden state. Energy remains nonnegative but can decrease under extension.
Constructed controls demonstrate that decrease and check padding invariance
for both ReLU RNN and GRU models, including empty words. The old baseline
sources and results were not edited.

All runs use the raw ordered four-letter words, 16 phase contexts, 32 hidden
units and a sum over prefix readouts. There is no width normalization.
Checkpoint selection in V2 and V3 uses training constraints only.

| Model | Training violations | Longer validation violations | Untouched deeper test violations |
|---|---:|---:|---:|
| Forward prefix-only baseline | 1681 / 2030 | 428 / 693 | not run |
| V2 ReLU, terminal correction | 0 / 2030 | 14 / 693 | not run |
| V2 GRU, terminal correction | 0 / 2030 | 113 / 693 | not run |
| V3 ReLU, refined on old validation | 0 / 2723 | 53 / 1983 | **541 / 2073** |

These are CPU double-precision checks with violation threshold `1e-6`.
The baseline's checkpoint selection used its longer set too, so that set
was never an unbiased test. V3 puts all old validation into training, uses
fresh validation seeds at depths `512..1023`, and reserves separate fresh
seeds at depths `1024..2047` for the test. Training never reads the test set.
The independent audit reports every failing index and residual. Maximum V3
test residual is approximately `2.917`; this is not a rounding discrepancy.

Order matters to the fitted V2 ReLU model: reversing the active tokens
increases its longer-set failures from 14 to 432. That does not rescue it:
even the original order fails, and V3's deeper test exposes substantial
generalization failure. Neither trained model is accepted as a rank.

G913 completed all runs with process guards, keeping more than 43 GiB of
system RAM free. V2 training peaks were below 1.9 GiB process RSS, and the
ReLU model used about 0.17 GiB of allocated GPU memory. Extra RAM fixed the
earlier Lean proof bottleneck; these neural failures are mathematical or
modeling limitations, not out-of-memory errors.

## Reproduction and scope

[`ordered-reader-followup/`](ordered-reader-followup/) preserves the raw
sources, mathematical datasets, manifests, source and weight hashes,
architecture controls, complete training records and independent test
audit. The small saved weight files are included to permit exact inspection
and warm-start reproduction; load them with `weights_only=True`. Generator
dependencies retain their original bytes. Dependencies are Python, NumPy,
SciPy and PyTorch with CUDA for training; final audits run on CPU.

Run `train_ordered_rank_reader.py --architecture relu --seconds 165` in V2
or V3 after checking `sources.json`. V3's `warmstart/` carries the checked V2
weight and provenance. Run `audit_ordered_reader_v3.py --architecture relu`
in V3 to recheck all three sets without training. Hardware-dependent GPU
optimization may produce different weights; the published weight audit is
an exact check of the recorded model. Training is bounded by time and epoch
limits, not a proof search guarantee.

The three Lean sources were checked with Lean 4.35.0 against reference kit
`3eca23c0a9fa6b153313655e6d51835406c2d06e`. The official `Check.lean` was
unchanged, with SHA-256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
Use the existing research-module replay procedure with the dependencies
already listed by the preceding manifests. No extra axiom or skipped kernel
check was introduced. These are local full-check results, not a new Wolfram
review status or prize submission.

No new Wolfram essay was submitted and no new pull request was opened.
The next question is whether a reader in the opposite causal direction or
an explicitly unbounded algebraic invariant can survive the deeper tests
and yield a uniform proof. The current forward networks do not do so.
