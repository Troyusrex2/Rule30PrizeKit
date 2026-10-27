# Independent cut-31 local event-map audit

The corrected four local formulas pass an independent language and scalar-rule audit. The six/five forcing-position consequence follows algebraically. This is a finite exhaustive scalar check with a paper language/locality argument, not a Lean proof, an actual empty-gate trajectory calculation, or closure of a transformed boundary class.

Inputs are the exact `PROTOCOL.md`, `probe.py` and `RESULT.json` in `cut31-local-event-map-20261027T0840`; their hashes are recorded in this audit's `RESULT.json`. The author's script was read but not executed. A separate event-position enumerator produced 26 words, and 13,702 inversions of the literal physical Rule 30 table independently checked every saved output and residual. The run took 0.0086985 seconds. No larger word, horizon, trajectory, build or publication was attempted.

## Exact language coverage

Let `G: Z -> {0,1}` have black positions cofinal in both directions. Assume every consecutive black gap is 3 or 5, and no two consecutive gaps are both 3. At time `t`, let `b>=t` be the next black position, let `a<b` be its preceding black position, and put

`g=b-a`, `d=b-t`.

This gives one of the eight states `(d,g)` with `g in {3,5}`, `0<=d<g`. Its output is black exactly when `d=0`. When `d>0`, the next state is `(d-1,g)`. At a black event, the next chosen gap `h` is 3 or 5, with `(g,h)!=(3,3)`, and the next state is `(h-1,h)`. Thus every such bi-infinite gate supplies a path in the stated automaton with exactly its output.

Conversely, any bi-infinite automaton path has black events within five steps in either direction. Following a black state to the next black state produces exactly the chosen gap `h`; the transition restriction forbids adjacent 3-gaps. Hence its output satisfies exactly the stated gap language.

The graph is strongly connected without relying on a numerical sample: decrement to `(0,g)`, choose gap 5 and decrement to `(0,5)`. From `(0,5)`, either gap may be chosen and decremented to any specified `(d,g)`. Every finite path therefore extends in both directions, by attaching cycles. There is no extra inaccessible-state class in the enumerated words.

The independent enumeration uses event positions rather than the author's packed automaton recursion. The first nonnegative black position is `f in {0,...,4}`; its incoming gap is `g in {3,5}` with `f<g`. Starting from that event, append all allowed 3/5 gaps through the first event beyond position 16. Every resulting prefix extends to a bi-infinite gate by using gap 5 outside it. Every legal 17-bit fragment has this form. Deduplication gives exactly the author's 26 words. Extension witnesses for each are saved in `RESULT.json`.

For a natural-time gate, this argument has a prefix condition. If the consecutive black gaps satisfy these laws from a black event `S` onward and black events remain cofinal to the right, every window starting at `s>=S` is legal: choose an artificial incoming gap 5 at `S` to extend to the left. An arbitrarily long leading zero prefix before the first certified black event need not be an automaton word. This audit does not independently prove the actual empty-driven gate's phase or onset hypotheses.

## Physical recurrence and formulas

Set `X_0(t)=0`, `X_1(2s)=1-G(s)`, and `X_1(2s+1)=1`. Here `X_k` is physical column `-k`. The inverse reconstruction is

`X_(k+2)(t) = X_(k+1)(t+1) XOR (X_(k+1)(t) OR X_k(t))`.

It is obtained by solving the physical stencil for its left neighbor. The independent program instead inverts the physical truth table `(0,1,1,1,1,0,0,0)`, indexed by `4*left+2*center+right`, at each individual cell. It never uses the author's packed-word recurrence.

At depth `k`, time `t`, the recurrence depends only on boundary times `t,...,t+k-1`, by induction; this is also the official `Rule30ZeroBoundary.recon_local` statement. Therefore the 17 gate bits `G(s),...,G(s+16)` suffice for `X_32(2s)` and `X_32(2s+1)`, and for the corresponding depth-31 values. Indeed the boundary block has 33 physical bits; the deepest odd-time cone ends at time `2s+32`.

Define `B(t)=X_32(t)`, `L(t)=X_31(t)*(1-X_32(t))`, and `K_i=G(s+i)*G(s+i+3)`. All additions below are in F2:

```
B(2s)   = 1 + G(s+1) + K1 + K5 + K7 + K8 + K12
B(2s+1) = 1 + K3 + K4 + K7 + K8 + K11 + K13 + K4*K12
L(2s)   = K6 + K7 + K12
L(2s+1) = K7 + K8 + K13 + K5*K13
```

All four equations agree with literal scalar reconstruction on all 26 words. The isolated formulas fail on exactly two saved words: word 37008 needs the `B` odd correction, and word 74017 needs the `L` odd correction. Every saved residual and feature class agrees with the independent calculation. Translating the boundary by the even amount `2s` proves the displayed formulas at every legal window; this is not extrapolation from a finite trajectory.

`L` is the masked older-column forcing, not the full value of `X_31` when `B=1`. The equations do not discard that distinction or assert an unforced white-wall reset.

## Exact six/five forcing-position consequence

Write `E={e: G(e)=G(e+3)=1}` for short-gap starts. Minimum gap 3 makes these black events consecutive. If `e<e'` are consecutive members of `E`, the intervening gaps consist of the short gap 3 followed by `q>=1` long gaps 5, so

`e'-e = 3+5q >= 8`.

Thus physical short-start locations `2e` are separated by at least 16. The three linear terms in each parity of `L` give each start `e` the six positions

`S_e = 2e + {-25,-24,-15,-14,-13,-12}`.

These supports have diameter 13, hence distinct `S_e` are disjoint. Their XOR is therefore their ordinary union; no linear cancellation between different short starts is hidden.

The only nonlinear term is `K_(s+5)*K_(s+13)`. It is nonzero exactly for short starts `e=s+5` and `e+8=s+13`. The associated physical position is

`2s+1 = 2e-9 = 2(e+8)-25`.

It cancels precisely the leading odd position of the *later* packet `S_(e+8)`. At distance 8 the two short starts are consecutive, and `q=1`. No different preceding start produces a second cancellation at this same position. Therefore the support of `L` is exactly the disjoint union of the sets `S_e`, with the leading odd position removed if and only if `e-8` is also a short start. Each packet contains five or six positions accordingly. This statement concerns `L`; the separate odd correction in `B` has not been conflated with it.

For bi-infinite gates there is no endpoint qualification. For a natural-time gate whose formulas are valid only at windows starting `s>=S`, the complete five/six count applies to each short start `e>=S+13`. Earlier packets may be clipped by the initial time boundary or lie outside the certified language onset; they are not assigned a six/five count without additional prefix information.

## Remaining scope

The formulas retain the forcing term and are uniform over the stated language. They do not prove that the transformed forcing/boundary pair belongs to the same class, that finite left support decreases, that actual empty-driven gates realize any chosen finite fragment, or that a prize problem is solved. No Lean verification is claimed for this local-function table or its paper corollary.
