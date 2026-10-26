# Independent cyclic-mode review

PASS for the exact supplied source and its stated cyclic scope. The main finite-white safety conjecture remains open.

`Rule30CyclicSubsetObstructionResearch.lean` has SHA256 `4c7afb6a97daeb6c0305a07cc0a6b54f3a74f2dc65e387d9b5026333c760b45e`. The fresh private build replayed all 48 constants and all three headlines with the unchanged official checker. No custom module dependency is imported: only the freshly built official Rule30Jen and Rule30Prize dependencies are needed. The independently read CommonPast source is comparison evidence, not an import or an extra replay dependency.

The guard recorded 11.390 seconds and 779,096,064 bytes peak process-tree RSS. Lean is 4.35.0, compiler commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; kit pin `5473ffd075f63c9d626e63b8455805d4831b39ca`; unchanged Check.lean SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`. The checker reports no new axioms, passing full replay, and all three headline types matched. The check uses `--claim partial`; it does not verify an official prize target.

## Statement and semantic audit

The domain is `Fin 6`, with older neighbors `j+5` and `j+4` and newer neighbor `j+1`, all modulo 6. Its actual update is the exact Rule30 interior XOR/OR update. Its mixed mode and adjacent Common formulas match the frozen CommonPast definitions at interior sites. They do not impose the special white equations at positions 0 and 1.

Each number encodes a spatial row with bit 0 at position 0. The temporal trajectories are:

| time | A | B | H | A xor B |
|---:|---:|---:|---:|---:|
| 0 | 58 | 23 | 12 | 45 |
| 1 | 5 | 40 | 12 | 45 |
| 2 | 27 | 27 | 36 | 0 |
| 3 | 36 | 36 | 36 | 0 |
| 4 | 63 | 63 | 63 | 0 |
| 5 onward | 0 | 0 | 63 | 0 |

The Lean proof checks all five transitions and separately checks that the final joint state is fixed. A split at time 5 covers every natural time, so the all-time claim is proved rather than extrapolated. Subset holds initially and at time 1, then fails at residues 2 and 5 at time 2. From time 2 the backgrounds coincide, making Common automatic while the mode remains nonzero. A temporal-cycle search requiring the initial state to return excludes this transient mechanism.

The three headline theorems have precisely the reported scope: cyclic dynamics with initial Subset and failure at time 2; background equality from time 2; and failure of the oldest white-boundary equation. In fact A(0,0)=false and A(1,0)=true. Thus this is not a counterexample to full white-boundary Actual, the white Actual/Mode/Common problem, FrontStable, finite-white safety, or a fixed-center claim.

Repeating the six sites periodically in space gives a mathematical extension to every integer site, or to every natural interior site j>=2. All equations are local and reduce to the six residue checks. This spatial extension is an audited semantic argument; the supplied Lean theorem itself has domain Fin 6.

## Separate finite-cone evidence

`audit_supplied_cones.py` independently evaluates Wolfram's supplied witnesses at horizons 1,2,3,4,6,8,12, without importing or running SAT. Every stored bit is checked, all initial Subset constraints pass, all interior actual and mode updates pass, Common holds throughout each specified shrinking triangle, and the target j=2H+2 loses Subset at time 1. Both Rule30 lookup and XOR/OR formulations agree. The scalar audit passed in 0.156 seconds at 12,136,448 bytes peak RSS.

These seven witnesses have width 4H+6 and constrain time-t sites only from j=2t onward (Common also needs the next site). They do not impose the older white equations after initialization, supply an all-time continuation, or establish satisfiability at every horizon. They are exact finite controls, not kernel-checked theorems.

The verifier also made a distinct explicit horizon-12 control from repeated six-cycle initial rows, width 31, evolved using genuine white equations. Its fixed core j=24..29 agrees with the periodic trajectory through time 12 and loses Subset at time 2. Common fails outside that core already at time 1, j=1. This separate construction does not strengthen Wolfram's cone witnesses into a global white-boundary result. Its data are in `audit.json`.

## Evidence and limitations

`REVIEW_MANIFEST.json` selects the frozen supplied source and reports, independent scalar audit sources/data, full checker JSON and logs, exact official source hashes, commands, and guard evidence. Private `.olean` files, the extracted kit, and source tar are excluded from the portable selection. Prior sealed Cedar snapshots remain unchanged.

No proof or replay failure occurred. One read attempted the reported underscore filename `common_subset_cone_probe.json`; the producer actually writes `common-subset-cone-probe.json`. The corrected filename was frozen before audit. The producer's SAT script was read for scope but never executed by this review.
