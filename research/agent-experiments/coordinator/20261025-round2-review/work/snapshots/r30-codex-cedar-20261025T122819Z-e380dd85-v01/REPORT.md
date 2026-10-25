# R2-04: Noncrossing ancestry after cancellation, and the missing front-escape lemma

Response ID: `r30-codex-cedar-20261025T122819Z-e380dd85-v01`.
Agent: codex-cedar. Campaign: `rule30-20261024`. Task: R2-04.
Original response: `r30-codex-cedar-20261024T214749Z-ea604829-v01`.
Supersedes: none; this is a new experiment.
Research base: `102d5b8e938b031a6d4df53541d9da2c50ffb859`.
Brief read at: `e8b3475582739991911bc0444d2d1689d513a27b`.
Verifier: `3eca23c0a9fa6b153313655e6d51835406c2d06e`, Lean 4.35.0.

## Batch overview

**There is a constructive way to pair cancellations and give every surviving
disagreement an ordered initial ancestor. There is still no proof that a
survivor reaches the center.** These are different obligations.

The round-one fixed-factorization benchmark reproduces exactly: canonical
`(T,P)=(0,1)` has two paths to the center at future time 3 and zero disagreement.
I replaced positive path counting with a locally chosen factorization, an
explicit path-pairing construction, and a residual ancestry forest.

| Finding | Status | Scope |
|---|---|---|
| F001 | PARTIAL_KERNEL_CHECKED | Local pairing certificate, valid initial ancestors, and noncrossing ancestor order at every time, for any two Rule 30 histories. Literal path involutions were also tested finitely. |
| F002 | PARTIAL_KERNEL_CHECKED | The same new ancestry structure holds for nonlinear Rule 210, but its actual single-seed comparison `T=P=1` agrees at the center forever. Thus this structure alone cannot prove Problem 1. |
| F003 | FAILED | The candidate claim that the leftmost source's right frontier never retreats fails already at `(T,P)=(1,1)`, times 1 to 2. A weaker front-escape lemma remains open. |

The unchanged checker replayed all **44 declarations** of `CedarAncestry`, with
12 passing headlines and no new axioms. This is a partial module, not a
Problem 1 submission. The actual path-involution data structure, the frontier
recurrence, the retreat example, and the front-escape conjecture are **not**
claimed as Lean theorems.

## Conventions and boundary conditions

All coordinates are physical integers, increasing to the right. Rule 30 is
`f(l,c,r)=l XOR(c OR r)`. Outside finite supports the rows are white; no
truncation, wrapping, periodic boundary, or arbitrary exterior is used.
For canonical seed comparisons:

```
A_t(x) = cell(T+t,x)
B_t(x) = cell(T+P+t,x),       T >= 0, P >= 1
D_t(x) = A_t(x) XOR B_t(x).
```

Packed experiments use bit 0 at the physical right end:
`Phi(a)=a XOR((a<<1) OR(a<<2))`, initial `a=Phi^T(1)<<P`,
`b=Phi^(T+P)(1)`, and frame `c=T+P`. At future time `t`, bit `i`
means physical coordinate `c+t-i`; the center is bit `c+t`.

## F001: Choose the leftmost differing parent after cancellation

**Track/status:** H / PARTIAL_KERNEL_CHECKED, with the formal scope below.

### Exact local claim and smallest pairing lemma

For every pair of Boolean neighborhoods write `d_l=a_l XOR b_l`, and likewise
for `d_c,d_r`. Both expansions of the output difference are exact:

```
E0 = d_l XOR ((!a_r) AND d_c) XOR ((!b_c) AND d_r)
E1 = d_l XOR ((!b_r) AND d_c) XOR ((!a_c) AND d_r).
```

Choose E1 precisely when `!d_l AND d_c AND d_r AND a_r`; otherwise choose E0.
This rule is also defined at zero-output vertices. At a true output
disagreement, retain the **leftmost differing parent** in `(x-1,x,x+1)`.
It is an active term of the chosen expansion. The remaining active terms
are either absent or are exactly two, which can be paired.

This is the small falsifiable lemma: at every one of the 64 paired local
neighborhoods, the chosen terms have the right parity, and at every true
output the specified parent is active and the other two contributions have
even parity. `CedarAncestry.rule30_normalizes` proves all of this by kernel
reduction. It asserts more than the round-one XOR identity: it fixes which
parent survives the local cancellation.

Why the choice works: if `d_l=1`, preserve it and the other terms must cancel.
If only one of `d_c,d_r` is nonzero, the output equation forces its term to be
active. When both are nonzero and `d_l=0`, switching expansions toggles both
OR-derivative coefficients, allowing the center parent to be preserved.

### The unbounded conditional ancestry result

Define `p_t(x)` as the leftmost differing neighbor; the implementation chooses
`x+1` if the first two neighbors agree. At an actual next-time disagreement,
that chosen parent really differs. For all masks, `p_t` is nondecreasing in
`x`: two parent edges cannot cross. Define initial ancestor labels recursively:

```
rho_0(x) = x
rho_(t+1)(x) = rho_t(p_t(x)).
```

The checked theorems establish, for every `t`, without width or time bounds:

1. `D_t(x)=1` implies `D_0(rho_t(x))=1` for any two Rule 30 histories.
2. `x<=y` implies `rho_t(x)<=rho_t(y)`.

The histories need not be finite or single-seed for these two results.
Root labels on the surviving disagreements therefore occur in order; each
root's descendants form a consecutive group in that ordered list, possibly
with white spatial gaps. Paths can branch forward and share an ancestor;
“noncrossing” does not mean disjoint.

Relevant headlines: `rule30_normalizes`, `parent_monotone`,
`ancestor_monotone`, `ancestor_valid`, `parent_valid30`, `rule30_ancestry`,
`seed_shift_evolves`, and `canonical_ancestry`. The last two explicitly bridge
to the official `Rule30Jen.cell` and specialize the ancestry theorem to
`cell(T+t,x)` versus `cell(T+P+t,x)` for all natural T, P, and t.
The source uses the official statement module and no replacement `Ruliology`
definitions. `rule30_ancestry` has explicit evolution hypotheses; it does not
silently assume the output difference exists.

### Literal path pairing: construction and finite check

At each active outgoing edge, copy the pairing already constructed on paths
to its parent. Copy even path families too, including through vertices with
zero disagreement. Of the parent's unpaired representatives, pair the two
nonselected contributions, or pair both if the new output is zero. At a true
output leave the representative from `p_t(x)` unpaired. Induction gives zero
or one residual according to the actual output parity, with exactly the
ancestor label above.

This is a written inductive construction; the literal path-set involution
has **not** been formalized in Lean. `paths.py` implements it explicitly on
path tuples, checking involution symmetry, no self-pairs, exact residual
count, root order, and the frontier recurrence below. It retains even path
families instead of quietly deleting them.

Finite results: all 16 canonical pairs `0<=T<=3, 1<=P<=4` through time 10
passed. The largest tested layer contained 17,124 paths, with up to 2,025
at one vertex. There were 136 local factorization switches. Separate controls
checked both XOR identities in all 64 local cases, adjacent parent order in
all 256 paired four-cell cases, and 800 full-row comparisons between the
physical truth-table simulation and packed evolution.

### Barrier check, evidence, limitations, next action

This construction retains the full histories and is neither a fixed-width
reader nor an additive prefix rank. It does not use the false unit inverse
charge, change the Golden domain, or claim a positive density gap. However,
F002 demonstrates that it still lacks a decisive Rule-30-specific ingredient.

Evidence: `CedarAncestry.lean`, `evidence/kernel_report.json`, the raw checker
log, `experiment.py`, `paths.py`, and their JSON/log/guard records. Artifact
IDs and byte hashes are in `manifest.json`. No prior response is a formal
dependency: the local facts are reproved here. The round-one response is the
intellectual starting point, not an imported certificate.

Crucial limitation: the factorization is allowed to depend on the two actual
rows. This changes the path DAG from the original fixed E0 DAG. The result is
a normal form for cancellations, **not** a promise of an odd residual at a
chosen target. It proves “a survivor has this ancestor,” not “the center has
a survivor.” The next decisive obligation is the front-escape lemma in F003.

## F002: A nonlinear periodic control also has this ancestry structure

**Track/status:** H / PARTIAL_KERNEL_CHECKED.

**Exact claim:** for `f210(l,c,r)=l XOR((NOT c) AND r)`, the analogous
derivative-factorization switch has the same leftmost-parent pairing
certificate. Every surviving difference has an ordered initial ancestor.
Nevertheless, for its actual one-black-cell seed,

```
run210(t+1,0) = run210(t+2,0) = 0       for every t >= 0.
```

Thus canonical `T=P=1` has no center disagreement at any future time, despite
finite support, common-seed ancestry, left permutivity, nonlinear gates,
moving boundaries, and the new noncrossing residual structure.

**Mechanism/proof:** `rule210_normalizes`, `parent_valid210`,
`rule210_ancestry`, and `rule210_coupled_center_agrees` all passed kernel
replay. The final theorem uses `Rule30Realization.center210` from the exact
pinned official catalog. Its source was checked against the pin and rebuilt
in the isolated verifier. That existing center result is credited to the
catalog; the new observation is that our proposed normalization also holds
for it. No public contribution or abstract is a proof dependency.

For intuition, the Rule 210 single-seed rows agree with Rule 90's rows. Their
black cells have parity `x=t (mod 2)`, so adjacent cells cannot both be black;
on those neighborhoods `(!c AND r)=r`. Reflection symmetry then makes the
next center zero. The pinned catalog proves the all-time statement; this
paragraph is not being offered as a substitute for that dependency.

**Falsification/control:** `fronts.py` checked all 64 local cases for each of
rules 30, 90, 150, and 210. The leftmost-active-parent selection passed for
30, 150, and 210, and failed in 8 cases for 90. It also checked 257 seed rows
for Rule 210/90 equality, parity support, and reflection, plus 257 layers of
the Rule 210 coupled ancestry forest. Its left-source frontier stayed left
of zero, as required by the all-time center-agreement theorem.

**Scope and barrier:** this is an exact countercontrol to deducing center
reach from the newly proved structural package alone. It is not a
counterexample to Rule 30's prize conjecture or to the Rule-30-specific
front-escape conjecture. Nor does it prove that the dynamics of all possible
label masks are identical across rules. The actual OR gate must still enter
the progress argument, beyond selecting and ordering parents.

**Evidence/dependencies:** the shared Lean source and full replay report,
plus `fronts.py` and `evidence/fronts.json`. F002 has its own named headlines;
its status does not rely on inheriting F001's label. The pinned catalog is
the only non-core proof dependency for the center comparison.

**Next action:** reject any proposed ancestry proof that also applies to
this Rule 210 comparison. Identify an OR-specific obstruction to perpetual
blocking of the left-source frontier.

## F003: A tiny retreat refutes monotone progress; front escape remains open

**Track/status:** H / FAILED. The failed claim is monotonicity of the
frontier, not the front-escape conjecture.

### Frontier definition and explicit recurrence

For canonical Rule 30 comparisons the leftmost initial disagreement is
`r=-(T+P)`. Let `N_t` be the positions of surviving disagreements with
ancestor `r`, under F001's prescribed normalization. The ordering of root
labels gives the following recurrence:

```
N_0 = {-(T+P)}
N_(t+1) = D_(t+1) intersect (N_t + {-1,0,1}).
R_t = max N_t.
```

Reason: if any differing neighbor has the least initial root, the leftmost
differing neighbor has that root too; conversely the selected parent is a
neighbor. This recurrence is justified here on paper and checked against
explicit residual paths; it is not a headline of the Lean module.

The expanding left boundary of B is always outside A's support, so its
disagreement keeps the same initial root. Hence each `N_t` is finite and
nonempty. `R_(t+1)<=R_t+1`, but its lower movement is not constrained to one
cell. These support observations are mathematical derivations, not separately
claimed kernel-checked statements in this response.

In packed coordinates, propagation costs a few exact integer operations:

```
next_root = (Phi(a) XOR Phi(b)) AND (root OR (root<<1) OR (root<<2)).
```

This tracks a particular residual source, not a count of all possible paths.

### The monotonicity counterexample

Take `T=P=1`. The initial source is physical position -2.

| Future time t | a | b | root mask | frame | R_t |
|---:|---:|---:|---:|---:|---:|
| 0 | 0xe | 0x19 | 0x10 | 2 | -2 |
| 1 | 0x32 | 0x6f | 0x50 | 3 | -1 |
| 2 | 0xde | 0x191 | 0x140 | 4 | -2 |
| 3 | 0x322 | 0x6f7 | 0x5c0 | 5 | -1 |
| 4 | 0xdee | 0x1909 | 0x14c0 | 6 | 0 |

At time 1 the least-root descendants are `{-3,-1}`; at time 2 they are
`{-4,-2}`. Thus the right frontier retreats from -1 to -2. At time 4 this
particular root does reach the center. The witness was independently
recomputed using physical truth-table rows and selected parents, not just
the packed recurrence. This is a finite counterexample, with no claim that
it is the globally earliest retreat over unbounded time.

### The smallest remaining sufficient escape obligation

For the exact canonical rows and the recurrence above, prove:

```
forall T>=0, forall P>=1, exists t>=0, R_(T,P,t) >= 0.
```

Since `R_0<0` and the right frontier advances at most one cell per step, its
first nonnegative value must be zero. Therefore `0 in N_t`, implying
`cell(T+t,0) != cell(T+P+t,0)`. This would exclude every eventual period
with every onset and give official Problem 1.

This is a **stronger sufficient, still unproved lemma**, because it requires
the least initial root specifically to reach the center. It is not merely
renaming an arbitrary center mismatch, and no equivalence with Problem 1 is
asserted. It remains a growth problem; defining it does not solve it.

### Finite stress tests and limitations

The prescribed root reached the center in all 4,096 pairs
`0<=T<=63, 1<=P<=64` and in 32 held-out pairs sampled independently with
`T in [64,8192]`, `P in [65,8192]`, RNG seed `30720261025`.
Each was followed through `4*(T+P)+128` steps, including after its first hit.
There was no fitted model and no training. These tests concern root ancestry,
not a new bounded-period exclusion theorem.

Retreats remain substantial: `(6117,6886)` has a one-step retreat of 18
cells in the recorded horizon, and `(4459,7596)` has 1,339 steps between
successive strict advances of its running maximum. The latter is a
high-water interval, not a claim that the instantaneous front stays fixed
for 1,339 steps. These are finite observations, not evidence of a uniform
time bound or positive asymptotic velocity.

The early 272-pair pilot in `experiment.json` is a subset, not an additional
independent batch. It tested a possible extinction-before-hit failure; none
occurred. The later support argument explains why extinction of the least
root itself is impossible. The difficulty is reaching the center.

**Barrier check:** no larger fixed-state catalog or additive geometric rank
is proposed. An attempt to charge every cancellation to one initial source
without accounting for branching would be invalid: that source can have
arbitrarily many descendant paths. Rule 210 supplies an all-time control
against the claim that ordered ancestry alone removes this problem. The
existing critical C=1 charge and Golden defect-clock results are unaffected.

**Evidence/dependency:** `fronts.py`, `evidence/fronts.json`, and the physical
and explicit-path controls. The frontier interpretation uses F001, referenced
as this response's `#F001`; the counterexample itself is finite computation.

**Next action:** investigate an OR-specific cancellation debt or blocking
constraint on this one source's full frontier, allowing retreats. First
falsify it at the example above and at Rule 210 `T=P=1`. Do not assume a
bounded delay, a monotone position, or a finite initial-source budget.

## Reproduction, public review, and delivery

All custom Lean/Python sources and raw outcomes are included. Sources are at
the response root; JSON and logs are in `evidence/`. The manifest gives each
artifact's ID and actual SHA-256. Use a **copy** of this response for reruns,
so its immutable evidence and hashes remain intact.

Python 3.12.3; psutil 5.9.8 for the guard; jsonschema 4.22.0 for validation.
Experiments use only Python's standard library. Requests 2.32.3 was used only
to read the public environment and submissions feed. No ML model or solver
was used.

```
python -B guard.py experiment.py
python -B guard.py paths.py
python -B guard.py fronts.py
python -B guard.py replay.py --project <separate-checkout-at-verifier-pin> --lean <Lean-4.35.0-executable>
python -B validate_response.py <response-directory>
```

The replay script checks the checkout commit, compiler version, unchanged
checker hash, and exact pinned bytes of each official imported module. It
builds only `Rule30Jen`, `Rule30Prize`, `Rule30Realization`, and the custom
module in that checkout's `cedar-build`, then invokes the official checker
with `--claim partial` and all 12 headline names. No Mathlib download or
shared build cache is required. Exact executed commands, imported-source
hashes, headline types, axioms and the raw replay verdict are recorded.

Checker SHA-256:
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
The first compilation failed on a redundant tactic after all goals had been
discharged; the rejected log and source hash are preserved. Removing that
tactic produced the successful full replay. There was no timeout, resource
kill, numerical error, `sorry`, new axiom, `native_decide`, `bv_decide`, or
disabled kernel checking.

Each owned job was guarded at 300 seconds, 8 GiB process-tree RSS, and a
2 GiB minimum of system-available RAM. The guard records actual sampled peaks
and durations, polls every 0.1 seconds, and can kill only its owned tree.
The successful jobs stayed below 1 GiB owned RSS and 30 seconds each. Tool
output and JSON timings are finite-run measurements, not proof premises.

The public environment snapshot confirms the requested verifier pin. The
public submissions snapshot was updated `2026-10-25T12:30:48Z`, with 45
entries. Its abstracts were screened for ancestry, cancellation, pairing,
planarity and rank; no contributed source was adopted as a proof dependency.
The kit catalog was inspected, including its existing Rule 90/150/210
barrier. Public tags and abstracts are discovery metadata, not independent
verification of their claims. Snapshots and retrieval metadata are included.

Local delivery uses the fresh response folder in
`D:/MWB/Rule30/agent-inbox/`, with `READY` created only after schema, cross-
references and every artifact hash validate. No previous response or
coordinator index is overwritten. No official prize essay is submitted.
