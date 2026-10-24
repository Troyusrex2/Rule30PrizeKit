# Seven independent proposals: reproducible first experiments

Troy Lowry and Codex, 24 October 2026. **Problem 1 remains open.** These are
experiments and an exact obstruction to one proposed reader, not a prize claim.

All seven incoming responses were preserved byte-for-byte before evaluation.
The intake recorded no declared hash mismatch. Two responses had schema notes;
their mathematical proposals were still evaluated. Original reports are retained
privately; the response IDs, mathematical findings and source hashes are public.

| Response / F001 | Actual experiment | Result and scope |
|---|---|---|
| `r30-coinailyzer-backend-20261024T214457Z-6932e764-v01` | Fixed-frame trace readers; parity features; two larger width-known benchmarks; exhaustive short-width collisions | Simple readers did not learn a new discriminator. The proposed generic four-width prefix reader is **refuted**, even at a fixed known width and observation index. Unbounded or seed-coupled separation is not refuted. |
| `r30-photograde-20261024T214729Z-bffceeb4-v01` | Depth-two trees and at-most-five-feature logistic models, whole-time-range holdout, same-width stripe twins, matched-top control | Apparent 80–90% scores use known low grammar or the seed's structured top edge. With top 16 bits matched and low features removed, both models score exactly 50%. |
| `r30-codex-sanity-20261024T214837Z-5d3c83fc-v01` | 100,000 sampled ordered five-matrix assignments, exact integer products, 23 guarded canonical constraints | Zero survivors. The best sampled tuple passes ten constraints before an explicit failure. This does not exhaust the coefficient box or refute other matrix ranks. |
| `r30-codex-cedar-20261024T214749Z-ea604829-v01` | Exhaustive paired-neighborhood identity; exact active-DAG path counts on canonical and delayed controls | The local identity is correct and kernel checked. Merely having a path does not force disagreement: canonical `(T,P)=(0,1)` has two cancelling paths at time 3. A structural pairing with an odd remainder remains open. |
| `r30-coinailyzer-swarm-20261024T214719Z-1bf7da5f-v01` | Reproduced the submitted moving-edge probe; checked the proposed right-column inference | The reported moving-edge asymmetry reproduces. It concerns moving windows. A center and its next value do not determine the right neighbor without the left neighbor; periodic inheritance was not established. |
| `r30-coinailyzer-swarm-20261024T214738Z-655f7a15-v01` | One million seed steps, centered spatial windows of widths 20–24; exhaustive exterior-bit closure at widths 1–10 | Catalogs continue growing. Sound closure that permits arbitrary exterior bits fills every word, already from zero. Finite absence is not an all-time exclusion. |
| `r30-coinailyzer-wiki-20261024T214827Z-f1e1a394-v01` | Reproduced 400,000-step entropy run; exact local successor sets; every binary center word of periods 1–12; exhaustive uniform-neighborhood history controls | The reported entropy gap is explained by the local rule. The proposed witness-matrix spectral-radius threshold is automatic for this relaxation. It does not exclude any center period. |

## The exact reader obstruction

Use the official moving frame `Phi(a) = a XOR ((a << 1) OR (a << 2))`;
at time `t`, observation `c` reads bit `c+t`. `SeedLow(a)` means bit zero
is black and bits one and two agree.

Rows **48 and 49** both have exact width six. Row 48 is positive and even;
49 is SeedLow. At the same known index **c=3**, their traces agree for every
`t<27` and differ at `t=27`. Thus a reader receiving the proposed observations
`0..4*width` (25 bits) cannot classify both. The Lean theorem
`Rule30ReaderObstructionResearch.no_four_width_generic_reader` quantifies over
every Boolean reader of that prefix, not just the fitted model architectures.

The module imports the official `Rule30StripeMeeting.Phi` and `phiRows`.
The unchanged official checker at
`3eca23c0a9fa6b153313655e6d51835406c2d06e` replayed **16 declarations** and
accepted all **seven headlines**, with no new axioms. An independent physical
`CellularAutomaton[30]` computation in Wolfram also confirmed the collision and
its first difference. See `lean-evidence/report.json` and `wolfram-controls.json`.

These two rows have the same highest black bit. They do **not** refute the open
edge-separation sufficient condition or canonical seed-pair separation. A changed
reader, a longer observation length, or use of the coupled seed ancestry remains
a separate question.

The original reader also omitted a frame issue: `trace(2,1)=trace(1,0)` at every
time because these encode the same physical start. A trace-only class reader
without a known frame cannot infer bit zero. All fitted readers here use a known
fixed observation index; no unknown-frame ambiguity was used to reject them.

## What the learned readers actually learned

The first pilot used 6,000 training rows, 1,600 IID holdout rows and 1,800
held-out-width rows; exact widths were balanced by label and row values were
disjoint. Separate models used c=1,4,8 and the same 256 trace observations.
Training widths were 16,20,24,28; unseen widths were 32,48,64. Logistic regression,
depth-six trees, forests and small multilayer perceptrons on raw bits were near
chance. Shuffled-label controls were retained.

Parity features expose an already known c=1 rule: SeedLow implies the first two
observations differ. This predicts about 75% on a balanced random sample because
half of the even rows violate that condition. The fitted parity tree selects
exactly this first-two-bit XOR. On the remaining ambiguous subset, held-out
balanced accuracy stays near 50%.

To avoid hiding useful width information, two further benchmarks fixed the known
width to **32**, supplied the proposed **128-bit** trace, and separately fixed
c=1 and c=16. Each used **40,000 training**, **8,000 validation**, and **12,000
test** rows, disjoint by initial row value. At c=16 the forest scored 97.7% on
training rows and 50.8% on test rows; raw and parity MLPs scored 50.4% and 49.7%
on test rows. At c=1 the networks recovered the known ~74% overall signal while
their ambiguous-subset test accuracy was 49.9–50.0%. This is overfitting or known
structure, not an extracted new invariant. Finite experiments do not rule out
larger or different learners.

The separate photograde experiment used seed times 12–95 for training and
96–191 for testing, shifts 0–7, and explicit same-width stripe twins. It also
included a hard control matching every negative row's top 16 bits to its paired
positive. The strong-looking top-edge classifier collapses to 50% under that
control; low-bit classification is the already known grammar distinction.

## Why the witness entropy gap is not a new seed invariant

Given a witness `(l,c,r)`, the next center is determined. The next left bit can
vary with the unseen outer-left bit. If r=1, the next right bit is fixed; if r=0,
it has two possibilities. Thus the witness has two or four possible successors.
Uniform independent five-cell neighborhoods give conditional entropy **1.5 bits**
exactly. The reproduced single-seed estimate was **1.5001**.

Longer history does not rescue the measured signal in these tests:

| Previous witnesses | Uniform-neighborhood exact expectation | Single-seed estimate, 400,000 steps |
|---|---:|---:|
| 1 | 1.500000 | 1.5001 |
| 2 | 1.327820 | 1.3267 |
| 3 | 1.295009 | 1.2941 |
| 4 | 1.272318 | 1.2719 |

The exact expectation enumerates all relevant initial neighborhoods, not a random
simulation. Agreement with these expectations is not a proof of an invariant
measure or of seed randomness; it shows that this proposed signal is already
accounted for by local constraints on arbitrary initial data.

For a hypothesized periodic center, the local witness transition reduces to
right-bit matrices `M0=[[1,1],[0,1]]` and `M1=[[1,1],[1,0]]`. With
`v=(golden_ratio,1)`, both satisfy `M_i v <= golden_ratio*v`. Hence the proposed
per-step spectral-radius threshold `<2` is automatically met, for every center
word. Every one of the 8,190 tested words of lengths 1–12 has a nonempty local
cycle graph. A finite-seed reachability obstruction is still needed.

## Remaining directions

The coupled disagreement identity survives, but a graph pairing must use common
seed ancestry and force an odd residue without reading the desired disagreement
as its premise. The matrix search supplies explicit counterexamples for fitted
candidates; a new algebraic identity would matter more than more random sampling.
Finite-prefix class collisions demonstrate that an exact reader needs a proved
horizon or additional structure. The open highest-edge separation route remains
unaffected by the same-edge counterexample.

The latest public Lean-verified Quint/Gemini five-tail contribution
`R30-20261024-f177ae` was also fetched for an independent audit and further front
analysis. Its separate numerical follow-up and replay evidence are not part of
the seven-response findings and will be reported with their own scope.

## Reproduce

Python dependencies are listed with the versions used in `versions.json`.
Numerical scripts need NumPy, scikit-learn, PyTorch and psutil; `front_lifts.py`
additionally uses Numba. From this directory, run:

```
python run_job.py reader.py
python run_job.py reader_features.py
python run_job.py reader_large.py --center 16
python run_job.py reader_large.py --center 1
python run_job.py photo_reader.py
python run_job.py matrix_rank.py
python run_job.py local_mechanisms.py
python run_job.py witness_uniform.py
python run_job.py prefix_collision.py
python run_job.py orbit_catalog.py
```

`run_job.py` uses the repository's existing guard: 300 seconds, 8 GiB owned-tree
RSS, and at least 2 GiB system memory available. Incomplete or killed jobs do not
count as passes. For the formal obstruction, use a kit checkout at the exact pin:

```
python verify_obstruction.py --project /path/to/pinned-kit --lake /path/to/lake
python run_wolfram.py --wolframscript /path/to/wolframscript
```

No host configuration, authentication or settings are changed. No prize essay
was submitted by this campaign. All numerical claims have finite domains;
only the explicitly reported Lean theorems have kernel replay evidence.
