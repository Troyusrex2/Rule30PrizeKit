# CedarPaddingExclusion independent source and quantifier audit

**Verdict: source/scope PASS. No semantic or quantifier blocker found.** This audit does not repeat the worker's build or the coordinator's independent kernel replay. The exact reviewed main source is SHA-256 `223d11f428e174264b5979347caae13ad006aeecb7f69b6467622a88ea6bd42a`; its new `PhysicalCapture` dependency is `2a6bc724ccd06669d7c6a19604c71002b03f5d84b4e8c855293096d24f62d1cb`.

## Exact theorem and imported meaning

For every Boolean list u containing a black cell and every q>=Q(length u), `not_eventually_padded_word` proves the negation of the **official** `Rule30StripCertificates.EventuallyWord (u ++ replicate q false)`. No private replacement of that notion is defined. At pin5473, it means there exists a natural T such that, at **every** t>=T, the literal single-seed center cell equals the word entry indexed by `(t-T) % word.length`.

Write n=length u, B=bound n, W=warmup n, K=n+B, and P=n+q. The threshold is exactly

`Q(n) = max(W(n), B(n)+9*(n+B(n)))`.

The black-position hypothesis supplies n>=1 and hence P>0. No separate maximum length, arrangement restriction, least-period assumption, fixed finite width, mask condition, conditional capture property, or certificate table appears in the headline. Black cells may occur anywhere in u, and u may end in white cells. The previously audited physical witness theorem and the new capture lemmas are proved dependencies, not remaining headline hypotheses.

## Period and warmup accounting

The official eventual-word premise gives both exact center P-periodicity from T and the exact value at every block phase `T+m*P+s`, s<P. Choose the last black phase ell<n. Every center phase strictly after ell and below P is white, including trailing whites within u and the appended q whites.

For every period number m>=1, the warmup begins at `T+(m-1)*P+(P-W)`. Since W<=q, its W ticks lie entirely inside the preceding period's appended white padding and at times >=T. Its endpoint is exactly `T+m*P`. The physical witness theorem therefore supplies a white physical cell within distance B at the last black time `T+m*P+ell`. There is no unsupported appeal to white ticks before T.

The remaining white tail has length `L=P-ell-1`. Since ell<n, it contains at least q ticks, so `L>=B+9K`. That exact minus-one is correct: the tail starts immediately after the last black time and ends immediately before the next period start.

## Capture and closed endpoints

`PhysicalCapture.black_step` is uniform in B. At a black center tick, choose the nearest white position p<=B. Its preceding position is black, so the next row contains a black either at p or p+1. Thus a black lies within B+1; this conclusion does not assume one was already present.

During a white-center run, `near_white_run` moves a nearest available black inward by at least one position per tick until column1 is black. After B white ticks it has reached column1. `black_stays` then keeps column1 black through the **closed** endpoint of the L-tick white run. No center value at that endpoint is needed: it affects the next row, not the current one.

In block phases the arrival time is at most `ell+1+B <= n+B = K`. Therefore column1 is black at every phase s with K<=s<=P. The last 9K column1 ticks before phase P are black, and the closed endpoint supplies the final column1 bit. `stripe_after_black_run` combines these with the pinned `black_shield`, giving the complete fixed stripe on positive positions1 through2K+1 at the next period start. This holds at all period starts numbered m>=2. The explicit endpoint bit is retained; the argument does not silently infer it from a half-open run.

## All times, not only period starts

For adjacent period starts numbered m and m+1, m>=2, the positive prefixes agree because both are that same stripe. Their center drivers agree for every future time by the already proved center period. The exact pinned `Rule30BlackRuns.cone_agree` therefore makes column1 agree at all phases s<K; its requirement `1+s<=2K+1` holds. For K<=s<P both column1 values are black by capture. These two cases cover every phase of the period without a gap.

`phase_periodic` then decomposes every t>=T+2P as `T+(k+2)*P+s`, with s<P, using quotient and remainder. It proves `cell (t+P) 1 = cell t 1` at **every such time**, not merely on a sampled subsequence. The eventual column1 onset is T+2P; the proof does not claim column1 periodicity from T or from time zero.

The final call is the exact pinned `Rule30Jen.not_adjacent 0`. Its two witnesses are center eventual periodicity `(T,P)` and column1 eventual periodicity `(T+2P,P)`, with P>0. Both refer to `Rule30Jen.cell`, the actual single-black-seed evolution. The theorem does not require equal onset times or least periods, so these supplied witnesses meet its hypotheses directly.

## Proven scope and remaining limitation

The result excludes an unbounded family of arbitrary black-containing blocks with sufficiently long white padding. It does not exclude every possible eventual period: periods without a white run meeting this length-dependent threshold remain outside the theorem. The all-white and empty u cases are not in this headline because its black-position premise is explicit. No inference that arbitrary repetitions can be rewritten with arbitrarily enlarged white gaps is valid or used. No whole finite-word return, Safe-to-F8 conclusion, or Prize Problem1 proof follows here.

The copied `FrontBlackInterval`, `PhysicalEarlyCases`, and `CedarPhysicalAgeBridge` sources match the three hashes already independently audited. All five sources match the sealed v03 package. The pinned definitions and theorem signatures were read directly and their file bytes compared against git objects at the official pin. `review.json` records exact source hashes and the sealed-package hash audit. No sources were edited and no experiment or build was run. The prospective generalization beyond long white gaps is not adopted by this receipt.
