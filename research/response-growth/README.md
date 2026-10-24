# A limit of terminal response normalization

**Problem 1 remains open.** This package rules out a proposed shortcut through
bounded normalized right-half states. It concerns the two existing sound
terminal rewrites, not completeness of response equivalence or the actual
center column. Developed by Troy Lowry with OpenAI Codex; no priority claim
is made for the elementary tail calculation.

For the kit's controlled right half, with physical right-hand cells stored
from low to high bits, put

```text
Q(a) = a XOR ((a >> 1) OR (a >> 2))
step(b,a) = 2*Q(a) + (b XOR (a[0] OR a[1])).
```

The known terminal rewrites `011 -> 01` and `101 -> 11` apply when the highest
three packed bits are respectively `110` and `101` (values `6` and `5`).
They preserve responses under every future boundary input; that soundness is
already in the kit. Repeated forward rewriting is the candidate normalizer
studied in the earlier [controlled-response investigation](../overnight/README.md#exact-controlled-right-half-responses).

The alternative high triples `100` and `111` alternate under `Q`, since
`Q(4)=7` and `Q(7)=4`. The new boundary bit goes at the low end. Consequently,
if `a >> n` is `4` or `7`, then for **every input sequence and every time**:

- `run(a,t) >> (n+t)` is `4` or `7`;
- no instance of either terminal rewrite applies;
- `log2(run(a,t)) = n+t+2`, so the word has exactly `n+t+3` bits.

`packedRun_cap`, `run_irreducible` and `run_log2` prove these statements
without bounds on the initial prefix, time or input. `cap_irreducible`
excludes a rewrite at every possible terminal cut, rather than testing only
a chosen cut. The packed update and run are proved equal, bit for bit, to
the catalog's `Rule30ControlledResponse.step` and `run`.

There is a particularly useful counterexample to interpreting normalizer
size as observed complexity. Start at `7` (`111`) and prescribe the constant
zero boundary input. The first observed bit is **always one**, yet at time
`t` the irreducible state has **exactly `t+3` bits**. The theorem
`constant_output_unbounded_states` combines the unbounded growth with the
kit's existing zero-driver head lemma. Thus periodic input, or even a constant
observed output, does not make these normalized states bounded.

This does not show that the observed output is nonperiodic; the example's
output is constant. It does not exclude smaller representatives through some
other response relation or establish completeness of these forward rewrites.
Nor does it assert that the prescribed boundary extends to a finite whole-row
Rule 30 history. An eventual-periodicity proof using a quotient must address
the actual prescribed driver and justify its own boundedness argument.

All **45 generated declarations and eight selected headlines** pass full
kernel replay at the verifier's `3eca23c0a9fa6b153313655e6d51835406c2d06e`
commit, with the unchanged checker and standard axioms only. See
[the report](report.json) and [the source](Rule30ResponseGrowthResearch.lean).
Independent physical truth-table controls pass 60 cases and 174850 cell
comparisons through time 64, including five periodic drivers and 65 constant
head observations. Those finite controls are separate from the all-time
Lean proof; see [their report](controls.json).

```text
python research/response-growth/verify.py --project /path/to/3eca23c-kit --lake /path/to/lake
python research/response-growth/controls.py
```

The reproducer rebuilds the exact source, fully replays every declaration,
checks all headlines and source hashes, and keeps the existing 8 GiB owned
memory, 2 GiB available memory and 300-second per-job guards.
