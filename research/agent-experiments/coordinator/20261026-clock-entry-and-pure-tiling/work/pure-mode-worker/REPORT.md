# Pure mixed-block height-two descent

`HeightTwoPureMode.lean` passed full unchanged-checker replay: 25 declarations. It proves a uniform tiling height bound and applies it to an actual finite-white ancestor. This is separate from the previously sealed 104+23-declaration height-two delivery.

## Exact formal result

Let `b : Nat -> Bool`. `Tiled b cut len` means `cut 0 = 0`; every `len n` is 5 or 7; `cut (n+1) = cut n + len n`; and on each such interval, b is respectively `10110` or `1011000`. The intervals concatenate without gaps or overlap and cover every natural time. There is no periodicity hypothesis or finite sampling premise.

`tiled_span_two` proves that signed white-height of b belongs to `[-1,1]` at every time. The proof first shows height is zero at every block boundary, proves coverage at every natural time, and then transports the two finite block identities with their actual time-parity sign. The finite block identities are checked by `decide +kernel`; the arbitrary concatenation theorem is an induction, not a finite sweep.

`actual_parent_descent` takes an actual finite-white word `xs ++ [a,b]` with newest-column height span at most two and failure of whole-word return8. If its actual immediate parent trace `tr(xs ++ [a])` is Tiled, then that literal shorter prefix also has height span at most two and fails whole-word return8. Nonreturn follows from the frozen, independently replayed `height_two_short_extension` theorem: parent return would force child return. No newest-column clock is substituted for a whole-prefix clock.

`minimal_height_two_not_tiled` excludes this explicit parent tiling in a minimum-width height-two/nonreturn word. Its minimum is over ALL height-two/nonreturn words. The parent's derivative grammar need not remain pure, because the minimum ranges over the whole class. This is different from the Safe-word minimum used in the earlier conditional coSafe descent; neither minimum is silently substituted for the other.

## Connection to Cedar's pure mixed-block case

Cedar v05's `artifacts/theory/theory-height/HEIGHT_STAGE.md` gives the mixed length-four derivative block with actual older-column patterns `A=1011`, `u=1101`. In the pure concatenation case, permitted gaps 1 or 3 give

| Gap | A | u | A heights from an even start | u heights from an even start |
|---|---|---|---|---|
| 1 | 10110 | 11010 | 0,0,-1,-1,-1,0 | 0,0,0,1,1,2 |
| 3 | 1011000 | 1101000 | 0,0,-1,-1,-1,0,-1,0 | 0,0,0,1,1,2,1,2 |

Each A block has zero increment and excursion `[-1,0]` at even starts, `[0,1]` at odd starts. Thus the whole A trace stays in `[-1,1]`, independent of block choices. The u blocks each add twice the starting sign and have excursion between zero and that increment. Since both block lengths are odd, those signs alternate; u also has span at most two. Only the A statement is needed and formally proved here.

The formal theorem keeps the actual-parent identity in its hypothesis: Tiled applies to `tr(xs ++ [a])`, not to an independently supplied temporal strip. It does NOT formalize Cedar's local block classification, the proof that all relevant gaps are 1 or 3, or the conversion of an arbitrarily phased periodic pure-mode child into this boundary-aligned tiling. Those are separate semantic bridges. In particular, `cut 0=0` is explicit. A phase-shift application must retain literal finite-white evolution, all-time height, and whole-word nonreturn; it cannot be justified by rotating a free strip alone.

The one-step descent does not preserve the pure grammar: A's derivative contributions are `11011` for gap1 and `1101001` for gap3. The latter creates length-one and length-three derivative pieces at joins. Therefore this is not a repeated pure-mode descent algorithm. It does exclude a boundary-aligned pure mode at a global minimum of the height-two/nonreturn class. Mixed length1/3/4 modes remain unresolved, and this result alone does not create a shorter Safe word.

## Validation and reproducibility

Final source SHA-256: `1b31d5b44996335f23c6efcefb6104cba22a4900239ecc54d76332c98d566da5`.

Dependency manifest SHA-256: `0eb28c0f069ddc67929534d1aacf76fd798ff0cdda3156cd12fc51a18f70074e`. Eleven exact source dependencies were freshly built and fully replayed in this new owned phase, 572 existing declarations total. Their source origins and hashes are in `dependencies.json`; no peer compiled artifacts were used.

Official pin `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean 4.35.0, unchanged checker SHA-256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`. Successful leaf output is `formal/HeightTwoPureMode/attempt02/`. It took 5.51 seconds, approximately 1.28 GiB peak owned RSS, and more than 40 GiB free system memory. Fresh dependencies took 39.58 seconds with the same memory scale. Every job used 300-second / 8-GiB owned-tree / 2-GiB-free guards; none fired.

Attempt01 failed only because `omega` did not unfold a `Fin` projection in the bound certificate. An explicit `change` aligned the identical arithmetic expression; attempt02 passed. Both exact source attempts and logs are retained. No sorry, new axiom, native decision procedure, checker alteration, or reference modification was used.

The separate Python control checks only the two block identities, not orbit lengths or widths. It passed in 0.17 seconds, 11 MiB owned RSS. Its output corroborates the symbolic table but is not the basis of the Lean theorem.

For a fresh independent replay, copy the `.lean` sources, dependencies.json, guard.py, and replay.py to a new G913 research folder with no lib or formal outputs, then run:

```powershell
C:/Users/troyu/Miniconda3/python.exe <fresh>/guard.py replay.py dependencies
C:/Users/troyu/Miniconda3/python.exe <fresh>/guard.py replay.py HeightTwoPureMode fresh
```

All jobs are terminal. No publication or prize submission was made by this worker.
