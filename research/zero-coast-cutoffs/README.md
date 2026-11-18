# Reset counts after the last seed bit

This note concerns `q01Gap_and_massDiverges_iff_reset_iterVoidMacro_crash` in [Rule30ZeroCoastBridge](https://github.com/WolframInstitute/Rule30PrizeKit/blob/ac3d1440c6dbce52a45aa404e4d614ce85d4b8d1/lean/Ruliology/CellularAutomata/Rule30ZeroCoastBridge.lean). The question is whether one can bound the number of successful zero-input returns from a reachable reset. Each return takes six or ten ticks.

Let $A$ and $B$ be the latest and preceding antidiagonals at a reset. Read them at the same depth, with white padding through the last index occupied by either. Let $h$ count pairs in the order 00, 01, 10, 11. Here are two paths that each complete two returns using no further set seed bits.

| Original seed | Seed width | Reset ticks | Change in $h$ |
|---|---:|---|---|
| 2440786724530854946624415088918 | 101 | 100, 106, 116 | (−1, 6, 6, −3) |
| 348215574720768951329435505750294 | 109 | 108, 114, 120 | (7, −5, −2, 6) |

The first reset in each row has already consumed the highest set bit. The two changes sum to $(6,1,4,3)$. Every fixed nonnegative weighting has nonnegative dot product with that sum. Consequently a weighted count cannot strictly decrease on both of these two-return paths. The witnesses concern aligned pairs and this particular grouping of returns.

An ordered quantity does count down during a single rhythm. For a nonzero current row $x$ of width $W$, let $L_d(x)$ be the first mismatch with the periodic wall trace that has zeros at multiples of $d$, starting at the current reset. The widths of $x$ and $F^d(x)$ differ. If $k$ is their first differing bit from the wall, their traces first differ at tick $k$ by the kit's inward wavefront theorem. Therefore $L_d(x)\le d+k\le W+2d-1$. After a successful $d$-return, $L_d$ decreases by exactly $d$. At tick 100 of the first seed, however, the pair $(L_6,L_{10})$ goes from $(12,6)$ to $(6,12)$ on a legal return. Bounding switches between the two rhythms remains open.

Run `python check.py` with Python 3. The verifier uses the literal Rule 30 truth table to reconstruct the accepted traces, both diagonal pairs, the histograms and the countdown example. The general inequalities above are paper arguments. These examples address a proposed termination method for the period-two reduction.
