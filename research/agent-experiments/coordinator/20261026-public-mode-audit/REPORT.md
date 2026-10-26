# Independent verification of the public mode-certificate method

This is an audit of AIOvernight's existing work in [PR31](https://github.com/WolframInstitute/Rule30PrizeKit/pull/31), not a new result by Troy Lowry's research team. Rule 30 Prize Problem 1 and our observer criterion remain open.

We retrieved the exact two new Lean sources at `AIOvernight/Rule30PrizeKit` commit `16250824c5e80964495ca5ba6bb82fa69394a35a`. We rebuilt them on the G913 and replayed every declaration with the unchanged official `Check.lean`, at pinned kit `5473ffd075f63c9d626e63b8455805d4831b39ca` and Lean 4.35.0. Both modules passed, with no new axioms. These are independent local checks; no Wolfram backend, human-review, merge or prize status is asserted.

| Exact public module | Declarations fully replayed | Selected headlines | Total guarded time |
|---|---:|---:|---:|
| Rule30Certificates.WhiteEndNineChecks | 38 | 4 | 85.60 seconds |
| Rule30WhiteEndNine | 29 | 3 | About 2 seconds |

The first module includes all 17 finite certificate checks. The counts include definitions and generated declarations, and are not counts of new theorems. The certificate run peaked at 3,964,047,360 bytes of owned process-tree RSS. Both runs respected the 300-second, 8-GiB-owned and 2-GiB-free guards. A private import overlay contains 26 compiled files from seven official modules whose sources were matched to the pinned Git objects. The reference project was not modified. The reports and source hashes are retained.

## What the method actually proves

`modeCert` describes a finite strip relaxation for an arbitrary nonempty proposed eventual center word w. A warm-up image must enter a closed strip set S0. At every white phase except one distinguished phase, the next column must be constant over the relevant set. At the distinguished phase, two covering strip sets E0 and E1 encode its bit. The checked transitions imply that a 1 label is followed by 0, and two 0 labels are followed by another 0.

The soundness theorem `not_eventually_word_mode` proves that these labels are eventually constant zero or alternating. Thus the adjacent OR column eventually repeats with period twice the word length. Together with the presumed periodic center column, this contradicts the kit's masked-Jen theorem. The temporal argument is unbounded; existence of an appropriate finite certificate is a separate hypothesis.

The concrete new certificate excludes the word `1 0^9`. The final q>=9 statement combines that instance with the already existing q>=10 theorem. It does not furnish one new pumping argument for every q>=9. The maintainer explicitly asks for such a uniform improvement in the [review comment](https://github.com/WolframInstitute/Rule30PrizeKit/pull/31#issuecomment-6422351013).

## Relevance and limitations for our research

The useful idea is to allow a small temporal label system whose outputs become periodic, rather than demanding a constant output at each phase. It may help design a stronger abstraction for safety ancestry or collision clocks.

It does not presently prove that every rejected finite-white prefix produces an unsafe newest column; it does not provide the normalized D3* ancestry implication; and it does not prove our Common-field observer criterion. No translation between those problems and this finite strip certificate is assumed. In particular, its phase label is not the auxiliary divided-difference mode used in our work: the shared word "mode" does not identify their equations.

Root therefore adopts the verified theorem only at its stated scope. We will not duplicate the q=9 certificate or present the external result as our own. The next mathematical use, if any, must supply an actual semantic bridge and a uniform existence or ancestry argument.

No new PR or prize submission accompanies this audit. A fresh parallel Codex assignment targets D3*; root continues the independent Common/observer track.
