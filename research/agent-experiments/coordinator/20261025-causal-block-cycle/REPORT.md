# A checked strict cycle in one causal block-rank template

Troy Lowry and Codex, 25 October2026. **Problem1, Q01 and CQ01 remain open.**
This tests the multiset/ordinal idea left incomplete in swarm response
`r30-coinailyzer-swarm-20261025T123207Z-d3e5f6e4-v01#F003`. The earlier
[review](../20261025-round2-review/REPORT.md) identified its missing block
ordinal and the unsupported claim that merges are automatically safe.

The universe-polymorphic theorem is fully replayed; the unchanged checker
accepts fixed-universe wrappers as headlines (including Type1 for ordinals).

The new theorem rules out a precise causal implementation of that idea,
including unbounded ordinal-valued ranks. It does **not** rule out arbitrary
multiset ranks, alternative block decompositions or global credit sharing.
The affine fitting experiment led to the obstruction, but the final Lean
theorem does not depend on the solver, affine weights or a finite rank bound.

## Exact scope

Use the canonical lag16 pair at onset n:

```
A(n) = a(n) << 16; B(n) = a(n+16),
a(0)=1; a(t+1)=a(t) XOR ((2*a(t)) OR (4*a(t))).
```

The current frame is n+16, so physical position p is packed bit n+16-p.
`IntegerRows.testBit_a` and `center_eq_testBit` connect these integers to the
official seed evolution. The guard is agreement of the two center traces
at all three times n,n+1,n+2 against their lag16 partners.

A block is a **maximal contiguous run of disagreement cells**. Its descriptor
contains time phase n mod16, its entire paired-cell word, and one paired cell
on each side. Pair codes are0=00,1=10,2=01,3=11, with the A-bit first. Thus
word letters are1 or2 and halo letters are0 or3. There is no bound on the
block length or on the rank values. Translation, onset beyond its phase,
distance from the center, other blocks and earlier history are absent from
this descriptor.

`Event` checks actual maximal parent/child blocks, the guard, their phases
and all old disagreement blocks in the child's two-step causal interval
[lo-4,hi]. Every listed parent intersects that interval; the list is nonempty.
These finite Boolean checks are evaluated by the Lean kernel on actual rows.

The tested template imposes two universal conditions:

1. **WeakCausal:** if all causal parents have the same descriptor d, the
   child's rank is at most rank(d). This includes a single parent and a merge
   of identically described parents.
2. **StrictSplit:** if two separated child blocks each have the same sole
   causal parent, each child's rank is strictly smaller than the parent's.

`no_causal_block_rank` proves that no function from these descriptors into
**any preorder** satisfies both conditions. In particular this excludes
natural-valued or ordinal-valued ranks of this form. The function may inspect
the full unbounded block word; it is not restricted to a finite-state reader,
a length score, linear weights or a bounded range.

These causal conditions are deliberate restrictions. An arbitrary global
multiset comparison need not assign each child only its geometric parents'
credit. A parent may also be connected to other parents through another
child. Consequently the theorem is **not** a proof that every multiset
construction fails. Larger halos, location, history, other segmentations,
more selective strictness and cross-block credit remain outside its scope.

## Eight actual events force a strict cycle

The descriptors below give phase, left halo, full word, right halo:

| Label | Descriptor |
|---|---|
| d0 | (5,3,[1],3) |
| d1 | (7,3,[2],0) |
| d2 | (9,0,[2],0) |
| d3 | (11,3,[2,1,1],3) |
| d4 | (13,3,[2],3) |
| d5 | (15,3,[2,1],3) |
| d6 | (1,3,[1],3) |
| d7 | (3,3,[2],3) |

| Onset | Parent bit interval(s) | Child interval | Required inequality |
|---:|---|---|---|
|37|[45,45]|[47,47]|r(d1)<=r(d0)|
|887|[1312,1312] and[1316,1316], both d1|[1316,1316]|r(d2)<=r(d1)|
|89|[42,42]|[42,44]|r(d3)<=r(d2)|
|507|[22,24]|[22,22], with separate pure sibling[24,24]|r(d4)<r(d3)|
|301|[237,237]|[237,238]|r(d5)<=r(d4)|
|911|[1024,1025]|[1027,1027]|r(d6)<=r(d5)|
|737|[443,443]|[444,444]|r(d7)<=r(d6)|
|1011|[728,728]|[730,730]|r(d0)<=r(d7)|

The inequalities compose to r(d0)<r(d0). This is impossible independently
of well-foundedness or any finite bound. The exact three-letter interior of
d3 matches at both occurrences; endpoint/length matching alone was not
assumed sufficient. All center guards, maximality, halos and causal covers
are included in the kernel-checked event theorems, including the split sibling.

## Experiment, correction and verification

The first scan found an actual guarded lag16 split reproducing an unchanged
raw disagreement word. Adding phase and a halo avoided the first coarse
obstruction, so we tested an unbounded candidate block rank
`alpha(type)*length+beta(type)`, with nonnegative integer coefficients. The
type contains phase, one-cell halo and first/last paired letters.

An early prototype split data by onset T and elapsed time t. For canonical
pairs the state depends only on T+t, so those sets overlap. Its held-out
figures must not be treated as independent validation. The corrected script
uses distinct onsets n in0..4095, and all256 possible boundary types from the
start. Only the corrected distinct-onset figures below are used.

- Training on n<256 supplied23 distinct guarded onsets and1881 deduplicated
  constraints. A fitted table also strictly decreased the actual global
  multiset on all23 training transitions.
- The458 distinct guarded held-out onsets had122 failures of global multiset
  decrease. The first is n=269. Local pure-child/merge failures are recorded
  separately, not counted as independent transitions.
- Refinement through n<1024 supplied106 guarded onsets and17934 constraints.
  Z3 reported UNSAT and supplied an eight-constraint core.
- We reconstructed the actual block words and positions independently from
  the solver core. Its full-word strict cycle became the generic Lean theorem.
  The final theorem uses neither the UNSAT claim nor the fitted coefficients.

The raw full-word scan, prototype, corrected search and extracted witnesses
are preserved. The prototype's overlap is explicitly marked, not silently
used as evidence. Larger-halo negative scans do not prove that a rank exists.

Two modules passed the full unchanged checker at pin
`3eca23c0a9fa6b153313655e6d51835406c2d06e`, Lean4.35.0:

| Module | Owned declarations replayed | Role |
|---|---:|---|
|Rule30BlockRowsResearch|168|32-step checked jumps and48 exact canonical rows through time1029; generic jump soundness.|
|Rule30CausalBlockRankResearch|90|Transparent event checks, exact cycle and no-rank theorem for every preorder.|

The258 declarations include generated/internal declarations and are not258
discoveries. All source builds are warning-free, headlines pass, imports
contain the official statements, and there are no new axioms. Every supplied
integer row jump uses `decide +kernel`. The unchanged checker SHA-256 is
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
It retains its existing deprecation warning. The final proof guard completed
in22.66 seconds with a sampled1.54GB peak owned RSS. No solver is a proof
dependency. See [REPRODUCE.md](REPRODUCE.md) and [proof-summary.json](proof-summary.json).

The14:28UTC public refresh found45 entries and no new Lean-verified result
to adopt. The new two-cell absorption entry R30-20261025-483a37 is unverified
and its notebook compilation failed; it is not a proof premise here. Earlier
archives, official statements/checker and external agents' inboxes were not
edited. No new prize essay or PR was submitted.

The multiset direction now needs a mechanism outside these causal descriptor
rules, rather than an unspecified per-block ordinal. Other open approaches
remain actual least-source escape and unbounded odd-source/minor growth.
None is proved by this obstruction.
