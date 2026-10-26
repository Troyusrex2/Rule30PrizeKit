# All-future common constraints lift uniquely into the past

**P1, Q01, CQ01 and the fixed-center observer remain open.** This is a
positive unbounded compatibility result, with an explicit support limitation.
It does not establish the backward closure required by the original observer.
No new prize essay or API submission was made.

## What is now proved

[Rule30CommonPastResearch.lean](work/Rule30CommonPastResearch.lean) uses right-edge
coordinates: index j is j cells to the left of a boundary moving right at
speed one. Arbitrary rows a,b obey the exact triangular Rule30 recurrence;
h obeys their divided-difference linear recurrence. The right exterior is
white. Rows may have infinite left tails.

The module proves four uniform facts:

1. For every depth j, **a, b and h are periodic from the start with period
   dividing 2^j**. Both coefficient histories evolve physically. The proof
   generalizes the official diagonal argument and reuses its
   `xor_accum_periodic` lemma.
2. Any common-field wedge constraint holding at every time after T already
   holds at every earlier time. Each local constraint sees finitely many
   right-edge coordinates and therefore has a power-of-two temporal period.
3. A given all-future common mode has a **unique past lift** in these
   right-bounded coordinates. The inverse is defined recursively from the
   right. The common constraint remains valid at the added past time.
4. If h lies inside a XOR b **at every future time**, the past lift also
   satisfies that condition at every time. If the given past backgrounds
   have finite support, the lifted past mode consequently has finite support.

The strengthened all-time subset condition also removes the exact quadratic
curvature term: a XOR h is then an actual Rule30 history, proved in
`actual_recombination`. The earlier curvature identity warned that an arbitrary
auxiliary mode need not be physical. We do not identify the two classes.

The source includes exact ordinary-coordinate bridges, `physical_actual` and
`physical_mode`, rather than replacing Rule30 by an unrelated recurrence.
The mode equation is

```text
h_next(p) = h(p-1) XOR ((NOT b(p+1)) AND h(p))
                     XOR ((NOT a(p)) AND h(p+1)).
```

## What this does not prove

The original observer assumes subset only at its initial time. **No theorem
here upgrades that premise to all-time subset.** The strengthened theorem
must not be applied to an initial-only subset field without a separate proof.
The statement that such an upgrade holds for finite backgrounds remains open.

Likewise, a fixed physical center is a moving depth in right-edge coordinates.
Local temporal periodicity does not extend a zero trace on that diagonal into
the past. The center extension and the canonical non-cancellation argument
remain missing. The finite-horizon backward-closure obstruction from the
[earlier checkpoint](../20261026-sensor-backward-closure/REPORT.md) is unchanged.

Without subset, finite future support does not ensure a finite past. The
module proves a sharp example: over two vacuum backgrounds, the unique past
of a single linear-mode pulse has the infinite depth pattern 110110110... .
`vacuum_pulse_no_finite_past` excludes every finite predecessor. This example
violates the subset premise and is not a counterexample to the strengthened
lift or the original observer.

These results give an exact part of the desired ancestry bridge. They leave
two substantive tasks: justify the stronger support property from the real
observer hypotheses, and preserve the fixed-center sensor when going backward.

## Evidence and finite falsification attempts

Before the proof, exact finite tests tried to falsify backward recombination
and subset preservation. They did not supply the unbounded result:

- All 32,640 pairs of width-eight starts were checked for future recombination
  collisions through 128 steps. No surviving collision violated the tested
  past partition. A width-nine horizon test has counterexamples at short
  horizons, so one or a few future rows are insufficient.
- A finite-image test checked 130,816 width-nine pairs through 96 steps; no
  tested permanent-looking recombination changed the finite-preimage class.
  Equality through 96 steps is not a proof of permanence.
- Among 774,400 nontrivial initially supported width-eight linear modes,
  6,792 survived the common constraints through 128. None of those survivors
  left the subset. This is evidence for further investigation, not the missing
  initial-only preservation theorem.
- An exact cyclic-prefix SMT search found no violating closed example at
  periods 2,4,8,16. Period32 **timed out** and remains unknown. These solver
  results are finite diagnostics and are not Lean verified.

An independent audit checks 4,680 complete prefix triples and their inverses,
826 recombination controls, 38,880 literal physical cells, 256 packed-coordinate
controls and all 512 finite-image membership cases at width nine. A physical
inverse control caught a packing-direction error in an early prototype. The
affected scripts were corrected and rerun; the independent literal-cell and
image-membership controls pass. No failed prototype is counted as evidence.

## Kernel validation and reproduction

The final 397-line source has SHA-256
`17eb07047e8b1780b25de532e72dcb73385f20eaffa91db366e92c210b394ec3`.
At kit `0090056412733accaa27643d3cbbf982104f2251`, Lean 4.35.0, the
unchanged official checker fully replays **all 100 module declarations** and
accepts all seven headlines, with no new axioms or kernel shortcuts. The count
includes generated declarations, not 100 independent new theorems.

Build plus full replay took 2.064 seconds on the Windows offload machine,
peaked at 779,046,912 bytes of owned RSS, and left at least 46,458,105,856 bytes
free. The existing 300-second / 8-GiB owned-tree / 2-GiB minimum-free guard was
unchanged. The checker hash is
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
Earlier function-inference, coordinate-cast, import and simplification errors
were repaired before the reported final pass. The final build log is empty.

Run `python verify_artifacts.py` to check exact archived bytes and evidence
scope. For formal reproduction, build the pinned kit, copy the work/*.lean
module into lean/, and run there:

```text
lake env lean -o .lake/build/lib/lean/Rule30CommonPastResearch.olean Rule30CommonPastResearch.lean
lake env lean --run Check.lean Rule30CommonPastResearch --claim partial
```

The included check_formal.py lists the seven headline arguments. Most numerical
scripts use Python's standard library; cycle_subset.py additionally uses Z3
5.3.1 at a workspace-specific dependency path. Z3 is not used by the Lean proof.
The public refresh at 2026-10-26T02:01:35Z found the same verifier pin, 40 listed
contributions, no changed entries, and unchanged skill1.17.3. No external
unchecked theorem was adopted. No historical-priority claim is made here.
