# Marker/carry state: exact ambiguity, reconstruction, and phase coherence

Three modules, 165 declarations total, passed unchanged official full
kernel replay. They assess a proposed state for the anchored marker-front
problem; they do not prove unbounded unsafe propagation, D3, or Prize P1.

| Module | Declarations | Source SHA256 |
|---|---:|---|
| MarkerCarryAmbiguity | 110 | 1d3948b75a39bf64b3618fb562f7f994746acd309b50bc895a5559862631cada |
| MarkerCarryReconstruction | 37 | b174ee12e8bb641dfecf2c64e34334a33339857a6b4a15d03649893bf0c6f5df |
| MarkerCarryProjectedCycle | 18 | 042605504f45fac9987bdb6d795f7b7ac4582f3200d746bbd87972f40972c78f |

The root independently replayed the frozen first two modules (147
declarations) and passed their source/scope review. The last control is
available for its independent review. Counts include generated structure
declarations. Worker replay receipts and exact source snapshots are under
`formal/`; successful process-guard receipts are under `evidence/`.

## Observation definitions

For an older-first finite-white word x, `marked x` is the exact delayed100
stream from CedarMarkerReturnTwo. Its first three bits vanish and entry
k+3 records x_k AND NOT x_(k+1) AND NOT x_(k+2).

The complete carry row emits the OR of the preceding three spatial bits
at each scan position, with white missing bits. It INCLUDES the terminal
top carry, so its length is |x|+1. `View x` retains marked(x), marked(Fx),
carryRow(x), and carryRow(Fx). `ShortView` omits the internal second carry
row but retains its top bit. These are exact observations of genuine
finite words, not freely assigned temporal strips.

## 1. Deterministic closure fails, including with both full carry rows

The genuine Safe words 111100 and111110 are four phases apart in the same
verified return8 orbit of100001. Their ShortViews agree, but their next
marker rows differ. Thus `no_short_view_marker_update` refutes any function
of ShortView that predicts the following marker row even on all-time Safe
words. This does not refute a Safe/F8 versus nonreturn separator: both
witnesses are already Safe and F8-returning.

The stronger all-width family is

    x(v,n) = 1001 ++ alternating(v,n).

For both phases v, F maps its prefix to1111 and complements the entire
alternating suffix. F² maps the prefix to1000 and restores the suffix.
Induction proves that the TWO complete marker rows and TWO complete carry
rows are independent of v, at every suffix length. After F², however, the
internal carry at index5 is v whenever the suffix is nonempty.

Thus `full_view_family_equal` and `future_carry_exposes_phase` exhibit an
anchored hidden phase that becomes observable when the earliest two-step
defect reaches it. The n=3 words both fail whole F8; they give the formal
`no_full_view_update_on_nonreturn`. This is a deterministic-update
obstruction. It does NOT prohibit invariants or sound relational
abstractions using the observation.

## 2. The view is nevertheless almost reconstructive

`view_and_last_two_injective` proves for ALL finite widths:

    View(x)=View(y), and equal final two initial bits, imply x=y.

The low-width cases use default-white indexing and are included. Hence
each observation has at most four word preimages; there is no claim that
four are always realized.

The proof recovers the adjacent-OR driver row by carry XOR marker at each
position. Equality of current and next OR rows prevents a bit disagreement
from disappearing before the penultimate coordinate. If the next newer
bits agreed, the current OR equality would force that common bit to1;
next-row OR equality would force its successor to1, while the common
driver equals1 and flips it. A local Boolean certificate and backward
induction then recover the whole word from the last two bits.

Adding those bits therefore restores essentially the entire original
state. The result is useful for coherent relational tracking but supplies
no new forward marker-height potential or width reduction by itself.

## 3. Existential projected transitions can switch phase spuriously

The fixed projected cycle was constructed analytically from the preserved
Safe prefix100001's literal eight-cycle. Its prefix integer states are

    [33,39,57,15,49,23,41,31].

Append leaf bits [1,1,0,1,1,0,1,0]. The resulting seven-bit node integers
(little-endian older-first encoding) are

    [97,103,57,79,113,23,105,31].

For every node x_i, View(F(x_i))=View(x_(i+1 mod8)). Both top carries in
each observed edge equal1. Every node fails whole F8. Every node is also
ACTUALLY UNSAFE: the kernel checks an explicit consecutive-zero time below
16 for each one. Hence this is not an actual Safe nonreturning trajectory.

Only edge0 switches a hidden phase: actual F(97)=39, whereas the next
selected node is103. Their full Views agree because the older pair remains
nonzero through the relevant next two times. All other edges are literal
F transitions. `unique_phase_switch` verifies that distinction.

Consequently the straightforward existential projected transition graph
has a closed, all-observed-top-carry-one path inside the nonreturn label.
An argument using that graph must preserve the SAME hidden phase between
edges; merely bounding each observation's fiber by four does not preserve
cross-time compatibility. This control does not rule out more restrictive
relational invariants that retain that compatibility.

## What remains open

The existing Cedar identities already make whole F8 status a static
property of the two delayed marker rows: truncate by three newest entries
and require both truncated streams to be allzero, using prefix autonomy.
Thus deterministic-closure failure must not be misreported as a failure
to distinguish return from nonreturn. That good/bad label is conserved
along genuine F trajectories.

The missing assertion is that no COHERENT genuine trajectory can stay at
top carry1 forever in the nonreturn label. The persistent earliest union
marker and its first F2/F4/F8 disagreement locations are known, but no
invariant here propagates a temporal00 event to every later actual column.
The projected cycle isolates why phase switching cannot replace that
argument. Moving defect/carry information is not identified with a fixed
physical-center observer.

No new width census, strip search, higher-clock table, or growing-state
search was used. The uniform family and projected cycle were derived
analytically, and the stated exact finite instances were kernel checked.

## Pin, dependencies, and reproduction

Official pin5473ffd075f63c9d626e63b8455805d4831b39ca and checker SHA256
b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905
were unchanged. No proof placeholders, new axioms, native decision methods,
checker weakening, or shared-reference writes were used. Each final leaf
took under1.86 seconds and under0.74GiB owned RSS under unchanged guards
(300seconds /8GiB /minimum2GiB free).

Four frozen dependency sources and prior replay receipts are copied under
`dependencies/` and `dependency-receipts/`: CedarSafetySoundness,
CedarSafetySemantics, CedarSafetyBridge (root1840 phase), and
CedarMarkerReturnTwo (root1942 phase). `sources.json` records exact source
and compiled hashes. `prepare.py` checks those and prepares the unchanged
checker replay. Build MarkerCarryAmbiguity first, then either remaining
module, using `python guard.py replay.py <module>` in the owned G913 phase.
`verify_artifacts.py` verifies the local seal and every source, receipt,
headline and guard match without launching Lean.

No publication, PR, or submission API action was performed by this worker.
