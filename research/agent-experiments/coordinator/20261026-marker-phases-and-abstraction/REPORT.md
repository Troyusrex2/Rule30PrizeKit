# Marker phases, exact reconstruction, and two abstraction failures

Two rows of delayed `100` markers and full carry data determine a genuine finite white-anchored word once its final two bits are specified. More precisely, any internal disagreement between words with equal observations continues through the penultimate bit as a complementary alternating suffix. However, discarding those hidden bits admits a false safe cycle, even when every represented state is a genuine finite-white word. This checkpoint also certifies why a separate pointwise half-clock abstraction cannot reject the earlier mixed-height control.

These are structural results and explicit limitations of specified abstractions. They do not prove Prize Problem 1, `ReturnComplete`, or actual reachability of the mixed strip. There is no actual Safe/nonreturn counterexample here.

## What the marker observation retains

Use the literal list evolution `CedarSafetySoundness.F`, ordered from the white boundary toward the newest cell. `marked xs` records delayed spatial `100` occurrences. `fullCarry xs` records the OR of three preceding bits, including the terminal carry. The view contains both of these rows for `xs` and `F xs`.

The all-width theorem [`view_and_last_two_injective`](sources/MarkerCarryReconstruction.lean) proves that equal views and equal final two initial bits imply identical words. Equal views force equal lengths, so the result covers empty and one-bit words as well. Consequently a view has at most four finite-word preimages. This is a mathematical consequence of injectivity; the module does not separately formalize a cardinality bound.

The proof recovers the adjacent OR driver as carry XOR marker. Equality of its current and next rows prevents a bit disagreement from disappearing before the penultimate coordinate. [`hidden_suffix_structure`](sources/MarkerTailStructure.lean) makes the geometry explicit: starting at any internal disagreement, the two words remain complementary through the penultimate bit, and both suffixes alternate. Taking the first disagreement gives the corresponding suffix description. The newest bit is deliberately unclassified. Adding the missing bits therefore restores essentially the full finite state; it does not by itself give a compressed safety invariant.

## Why deterministic and existential updates both need care

[`MarkerCarryAmbiguity`](sources/MarkerCarryAmbiguity.lean) proves two distinct failures. A smaller view, containing two marker rows, one full carry row, and both terminal carries, fails to predict the next marker row even for two phases of the same genuine Safe orbit. The complete two-marker/two-carry view also fails to predict its own next value: for every suffix length, the genuine words `1001 ++ alternating(v,n)` have equal views for both phases `v`; whenever the suffix is nonempty, a later internal carry exposes the phase. The fixed length-three suffix pair consists of whole-F8-nonreturn words. This is an obstruction to deterministic closure, not to every separator or invariant.

[`MarkerCarryProjectedCycle`](sources/MarkerCarryProjectedCycle.lean) gives a sharper relational control. Its eight seven-bit words have little-endian codes

```
97, 103, 57, 79, 113, 23, 105, 31.
```

Their views form a closed path under the relation that admits an edge whenever some representative has that next view. Both observed terminal carries are one at every edge, and every node is whole-F8-nonreturn. Yet every node is actually unsafe: the kernel checks an explicit consecutive-zero event before time16. Exactly one edge switches representatives: actual `F(97)=39`, while the following listed node is103; their views agree. The remaining seven edges are literal updates.

Thus the apparent safe cycle is created by changing a hidden phase between edges. It is not an actual orbit. Retaining one coherent representative through time is essential. This control does not prohibit stronger relational invariants. Existing return-two marker and return-eight prefix theorems also make the whole-F8 label constant on these view fibers; loss of deterministic evolution must not be confused with loss of that static label.

## Why the pointwise anchored-defect abstraction saturates

[`AnchoredDefectAbstraction`](sources/AnchoredDefectAbstraction.lean) starts from a genuine first clock jump: word `110110010` returns at16; adding a final zero gives first failure at16, return at32, and an anti16 newest trace. All shorter prefixes return at16.

The abstraction observes adjacent traces at `t,t+1,t+16,t+17`, together with time parity. It enforces the two one-step recurrences but independently chooses the new bits at `t` and `t+16`. A finite predecessor certificate proves that all100 locally valid states lie in the closure of actual seed observations. Therefore any predicate true at those seeds and inductive under this particular overapproximate step accepts all observed pairs of the previously certified mixed-height strip.

The limitation is precise: different time positions may use different abstract paths. The abstraction forgets the complete16-step XOR compatibility relation and consistency across time. The theorem does not show that the mixed strip has a genuine finite-white ancestor, nor that all invariants on actual dynamics fail. Simply retaining the first clock-birth flag did not repair the loss of temporal correlation.

## Verification and remaining work

Five exact source modules were independently rebuilt and fully replayed by the root agent against unchanged kit commit `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean4.35.0, and checker SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`. All238 declarations, including generated declarations, passed; all recorded headline types matched and no new axioms were introduced. The thirteen older dependencies comprise656 declarations previously root-replayed and hash-checked here, not freshly rebuilt. No worker binaries were used.

The five root runs took approximately1.7–13.6seconds each, below300-second/8-GiB guards. The largest used about2.05GiB. Sources, full checker receipts, guard receipts, and two sealed worker bundles are preserved. All120 worker artifact hashes and all4609 prior hashes across49 owned archives matched before packaging. The new suffix theorem also received an independent source/scope review checking both terminal-coordinate bounds.

The next proof obligations retain genuine ancestry and coherent temporal phase: rule out a real all-time safe trajectory in the nonreturn region, or derive a genuinely shorter counterexample. A pointwise closure or an existential cycle cannot substitute for either. Separate work continues on whole-word clock lifting, the finite-white mixed-height case, and the physical-center observation bridge. See [reproduction instructions](REPRODUCE.md) and [verification metadata](summary.json).

The contemporaneous [public-source audit](PUBLIC-AUDIT.md) found three newly officially verified exclusion families. None supplies these missing premises.
