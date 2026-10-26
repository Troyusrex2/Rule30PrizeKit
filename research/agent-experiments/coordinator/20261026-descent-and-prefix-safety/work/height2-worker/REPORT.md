# Height-two near-return obstruction and conditional descent

The two final modules passed full declaration replay with the unchanged official checker. They make Cedar v05's conditional height-two reduction exact for literal finite-white Rule 30 histories. They do not prove that one of the two actual parents is coSafe.

## Proved statements

`HeightTwoNearReturn.height_two_short_extension` holds at every spatial width. If the entire older-first prefix `u` returns after eight applications of the white-boundary map `F`, `v.length <= 2`, and the actual newest trace of `u ++ v` has signed WHITE-height in one integer interval `[lo, lo+2] for all time`, then the entire word `u ++ v` returns after eight steps. There is no Safe hypothesis on `u` or `u ++ v`, no supplied clock for the child, and no assumption that the newest column determines the prefix clock. Empty prefixes/suffixes are included.

The white-height is exactly `sum_{0 <= t < T} (-1)^t * [b(t)=false]`. The file proves equality to the previously verified integer `RootEventHeight.height` definition. Its interval includes every `T : Nat`, including zero.

The proof uses the existing 36 return8 boundary-profile categories and all seven suffixes of length at most two. Each of the 252 cases proves either whole-suffix return8 or an explicit height difference greater than two. The independent Python control found 124 returning and 128 nonreturning cases; every nonreturning witness is within 32 steps. All finite cases are independently recomputed by Lean `decide +kernel`, split into 36 entries. An arbitrary-prefix induction transports these categories through actual evolving prefix cells, using the proved repeating-boundary history bridge. The finite certificate alone is not the theorem.

`HeightTwoDescent.coSafe_nonreturn_descent` strengthens the requested column-clock version: if an actual word `xs ++ [a] ++ tail` fails whole-word return8, its newest trace has all-time height span at most two, `1 <= tail.length <= 2`, and the actual prefix `xs ++ [a]` is coSafe (its newest trace never has temporal `11`), then `xs ++ [!a]` is strictly shorter, Safe for all time, and fails whole-word return8. Only the newest initial bit of that ancestor is flipped. Leaf complement transport is exact; the tail is not silently retained after this flip.

`coSafe_parent_descent` specializes this to a newest column that is not eight-periodic. `closed_period_coSafe_descent` supplies the same conclusion from an arbitrary positive even column period, zero signed drift over that period, and height span at most two throughout the period. `span_two_of_closed_period` proves the passage from this closed finite-period condition to an all-time band. The supplied period need not be least and is never treated as the whole-prefix period.

`height_two_nonreturn_nearby_ancestors` and `minimal_counterexample_parents` state the remaining obstruction precisely. Under the explicit hypothesis that every strictly shorter Safe word returns8, both nonempty immediate ancestor prefixes of such a height-two counterexample have a temporal `11` pair. This Safe-word minimality hypothesis is NOT inferred from minimal width among height-two words. The theorem covers words with at least three cells; the general one/two-cell ancestor theorem handles any actual nonempty ancestor.

## Exact final source identities

| File | SHA-256 | Replayed declarations |
|---|---|---:|
| HeightTwoNearReturn.lean | 3375fba87435aec88b8bfa62a0dad4f7380317757b770fc511bf203d265a7677 | 104 |
| HeightTwoDescent.lean | 2986e94319763ae4597bcc37dcc65cf00cfc724e462933d9568260aa3ae50af4 | 23 |

`dependencies.json` SHA-256: `4597567fbb9036bde182e5d914d6b9571d7d69d36657ae09f7c17d120ef0713b`. It records the nine exact source origins and hashes. All nine dependencies were rebuilt and fully replayed in this owned phase: CedarSafetySoundness 137, CedarSafetySemantics 75, CedarSafetyBridge 8, CedarWhiteTransport 18, RootShortExtensionCore 36, CedarNo11011 31, RootEventHeight 43, HeightOneLogic 30, HeightOneSemantics 67: 445 existing declarations. Peer compiled artifacts were not reused.

## Validation and failed attempts

Reference: official commit `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean 4.35.0, unchanged `Check.lean` SHA-256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`. No sorry, new axiom, native decision procedure, checker changes, or read-only reference changes.

Both final successful runs are `formal/<module>/attempt03/`. Each contains exact source bytes, build log, full checker log, and parsed report. NearReturn took 7.12 seconds and Descent 5.59 seconds. Each peaked near 1.28 GiB owned RSS, with more than 39 GiB system memory available. Every job was guarded by 300 seconds, 8 GiB owned process-tree RSS, and a 2 GiB system-free floor. No guard fired and no unrelated process was signalled.

All failed and intermediate attempts are retained. The first dependency job replayed CedarSafetySemantics successfully but requested a headline under the wrong namespace; the corrected namespace is CedarSafety. The first two NearReturn builds failed only at the final state-zero/white-boundary elaboration. Descent attempt01 failed on Bool-negation parsing and unapplied list-append simplifications; attempt02 passed the earlier 19-declaration version, and attempt03 passed the final stronger 23-declaration version. A remote PowerShell command using unsupported `&&` was rejected before running a job; it was replaced by absolute script invocation.

To independently replay, copy the exact `.lean` files, `dependencies.json`, `guard.py`, and `replay.py` into a fresh owned folder under `C:/Users/troyu/Rule30-offload/research/`, with no previous `lib/` or `formal/`. On G913 run these sequential commands with that fresh absolute guard path:

```powershell
C:/Users/troyu/Miniconda3/python.exe <fresh>/guard.py replay.py dependencies
C:/Users/troyu/Miniconda3/python.exe <fresh>/guard.py replay.py HeightTwoNearReturn fresh
C:/Users/troyu/Miniconda3/python.exe <fresh>/guard.py replay.py HeightTwoDescent fresh
```

The runner checks exact dependency/checker hashes, compiles into its private `lib/`, and invokes unchanged full declaration replay. The reference project and toolchain paths are explicit in `replay.py`. `generate_certificate.py` is preserved as discovery evidence; it emits only the initial generated certificate and would overwrite the final semantic proof if rerun in place. Run that generator only in a disposable copy, never over these final sources.

## Open problem and scope

The mixed derivative-block case is still open. The proved reduction needs at least one actual coSafe parent; Cedar's local length-four mixed block allows both parents to contain `11`. The known unanchored periodic strip remains a countercontrol against replacing the finite-white anchor by arbitrarily deep local ancestry. No clock/width sweep, new prize claim, or publication was performed by this worker. A separate follow-up theory note examines pure concatenations of the mixed block; it is not part of these frozen proofs.
