# Finite backward closure fails even with the left edge and zero sensor retained

Problem 1 and the all-time canonical observer remain open. This is a research
checkpoint ruling out a particular finite backward argument. It is not a new
prize submission or an all-time counterexample.

The preceding all-width band-escape theorem remains valid, but does not force
an observation at the moving center depth. This experiment tests whether a
finite backward step could supply that missing bridge.

## Exact formal result

Let A(t,p)=cell(256+t,p), B(t,p)=cell(237+t,p), and delta=A XOR B. There is an
auxiliary field h with all of the following properties:

- h initially vanishes outside [-256,256] and is a subset of delta(0).
- Its exact left edge is -256-t through time 6.
- h(t,0)=0 for every t from 0 through 6, inclusive.
- The common-field identity W holds at every physical position through time 6.
- The frozen divided-difference evolution D holds for every time, including
  after the finite observation window.
- No previous field g contained in cell(255) XOR cell(236) can evolve by the
  preceding D step to h(0). This impossibility does not require previous W.

The definitions, general lemmas and existential statement are in
`work/Rule30SensorClosureResearch.lean`, namespace `Rule30SensorClosureResearch`.
The headline is `finite_sensor_nonlift`. The construction starts with

    h(0,p) = cell(256,p) XOR cell(237,p) XOR [p=256]

and continues by D for all time. Through the required window it equals the
actual difference plus the ordinary Rule 30 evolution of the removed pulse.
Locality inside the older row's right white gap proves D and W there. The
official integer-row recurrence, checked by kernel computation, proves the
white gap and the seven equal center samples. The common center word is
1101101, with black represented by 1.

## Why backward lifting fails

The current field's rightmost black cell is at position 237. In an auxiliary
D evolution, the rightmost black cell of an upper-bounded field advances by
one. This fact is independent of W and of the coefficient backgrounds'
evolution. The general backward form is `preimage_right_edge`.

A hypothetical previous subset field is upper bounded, so it must have a
black cell at position 236. But cell(255,236)=cell(236,236)=1, so the previous
actual difference is zero there. The required black bit violates the subset
condition. `field_nonlift` proves a parameterized version of this argument.

This example retains the sensor and left-edge conditions simultaneously.
The earlier uniform pulse obstruction lacked the left edge; the earlier
left-edge family generally had nonzero center observations. Neither earlier
scope issue is used to weaken the conditions in this example.

## Validation and limits

The unchanged official checker at kit commit
0090056412733accaa27643d3cbbf982104f2251 replayed all 134 generated module
declarations and accepted all three headlines, with no new axioms. This count
includes reused helpers, finite-row checkpoints and generated declarations;
it is not a count of 134 new independent mathematical results.

The source SHA256 is
8e26936951616c0d40246fcc397a91eddddc2dc98928b10d9820d7a4e90bc0b8.
The checker SHA256 is
b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905.
G913 built and checked it in 6.102 seconds under the unchanged 300-second,
8-GiB-owned-tree, 2-GiB-free guard. Peak owned RSS was 1,428,860,928 bytes.
`work/sensor-kernel-check.json` and the archived logs record the full result.

A separate verifier evolves sets of physical positions, imports no search
implementation, and reconstructs the full previous field from the right.
It confirms every required finite property and rejects two corrupted controls.
The initial bit-packed search also found longer finite sensor windows; those
larger examples are diagnostics and are not included in the Lean theorem.

The independent set evolution checks the continuation through time 64. Its
center first becomes nonzero at time 7. W first fails at time 9, position 246.
These last two numerical facts are independent computational controls, not
additional Lean headline theorems. In particular, the construction is neither
invisible for all time nor common for all time.

It disproves the proposed finite one-step closure with these premises. It
does not disprove closure under all-time W and all-time zero observations,
nor a theorem with a sufficiently stronger lookahead premise. No unbounded
family retaining both the left edge and zero sensor is proved here.

To replay the formal result, copy the single final Lean source into a built
checkout at the pinned kit commit and run the following there. The checker
and official statements are left unchanged.

```sh
lake env lean -o .lake/build/lib/lean/Rule30SensorClosureResearch.olean Rule30SensorClosureResearch.lean
lake env lean --run Check.lean Rule30SensorClosureResearch --claim partial --headline Rule30SensorClosureResearch.preimage_right_edge --headline Rule30SensorClosureResearch.field_nonlift --headline Rule30SensorClosureResearch.finite_sensor_nonlift
```

The independent controls need only Python: run `work/independent_sensor_check.py`
and `work/beyond_window.py`. The assembly helper can reconstruct the final
source from this archive's body and the two earlier immutable research archives;
the complete assembled source is included directly, so assembly is optional.

## Next work and incoming responses

The center-observation bridge is still the target. A proof must control the
entire canonical history or establish a different unbounded invariant;
finite backward closure as stated above cannot provide that bridge.

The public submission list and verifier pin were unchanged at this refresh.
The seven previously reviewed round-two responses in the shared inbox were
byte-unchanged; no new ready folder had arrived at the recorded scan. New
agent ideas should keep theorem, finite evidence and conjecture separate,
and identify exactly how the moving-center step would follow.

The high-RAM G913 worker is operational for Lean. The current 164-declaration
standalone essay proof also passed there, and all 24,272 notebook dependency
files verified. Engine installation on G913 is awaiting the separate approval;
full fresh notebook evaluation and a new prize API submission remain pending.
