# A proved short-extension theorem and an explicit ancestry target

**The short-extension gap is closed. D3*, global safety completeness and the Rule 30 Prize remain open.**

For any genuine finite-white prefix u whose newest cell is safe for all time and whose whole word returns after eight updates, every safe append v of at most three cells also returns as a whole word after eight updates:

```lean
theorem safe_short_extension (u v : List Bool) (hu : Safe u)
    (hr : evolution 8 u = u) (hv : v.length <= 3) (hs : Safe (u ++ v)) :
    evolution 8 (u ++ v) = u ++ v
```

Here Safe means that the newest cell is never white at two successive times. Evolution is the literal simultaneous older-first Rule 30 map with both missing older cells white. The prefix's eight-step return is an explicit premise. No clock or periodicity premise is imposed on the appended cells. These are moving-diagonal coordinates; no fixed-center observation follows from this result alone.

The root parallel worker proved the result in four modules. A general history-transport lemma justifies repeating the already checked eight profiles of an accepted prefix. It handles the wrap from phase seven to phase zero explicitly. Spatial induction transports the actual history and safety predicate through an arbitrarily long accepted prefix. At its endpoint, 225 individually proved trajectories cover fifteen possible safe profile pairs and all appends of lengths zero through three. The 210 nonempty cases match Cedar's prior audited certificate. Each case either returns the whole extension at eight or supplies an explicit unsafe pair. The generator is not trusted: Lean checks every trajectory step and the exhaustive dispatch.

This replaces the previous certificate-plus-paper status of F003 with a full kernel-checked theorem. The retained worker report explains the implementation and failed revisions in detail. The concrete returning cases are not assumed safe; they are one side of a disjunction used by the proof.

## The remaining ancestry statement is now literal Lean

`RootD3Reduction.D3Star` states that every safe word beginning with its first black cell, of effective length at least four, has a safe prefix after deleting one, two or three newest cells. It has no return-period premise:

```lean
def D3Star : Prop := forall ys : List Bool,
  3 <= ys.length -> Safe (true :: ys) ->
  exists u v : List Bool,
    true :: ys = u ++ v /\ Safe u /\ 1 <= v.length /\ v.length <= 3
```

Root proved `return_complete_of_d3`: this hypothesis implies that every finite safe word returns as a whole after eight updates. Strong induction decreases the actual word length. A leading white cell is removed using Cedar's exact white-padding lemmas; a normalized longer word uses D3* and the new short-extension theorem. Every word of length at most three is checked as a base case. The existing exact language bridge then proves `language_complete_of_d3`, conditional completeness of the thirteen-state accepted language.

**No theorem asserts D3Star.** The ancestry implication is the remaining open hypothesis on this route. The conditional reduction does not establish the fixed-center observer or Prize Problem 1. Cedar's parallel ancestry and adversarial work targets this literal hypothesis. Its cyclic-gap paper reformulation is not used as a proved premise here and is not counted as new scalar mathematics.

## Independent validation

The worker fully rebuilt and replayed its seven modules, including the three previously proved dependencies. Root then froze those exact source bytes and independently compiled and replayed all seven in a fresh private G913 directory, without reusing the worker's binaries. Root also freshly replayed CedarWhiteTransport and the new D3 reduction.

| Modules | Root-replayed declarations | Role |
|---|---:|---|
| RootShortExtensionCore, Cases, Certificate, final theorem | 273 | New short-extension development |
| RootD3Reduction | 10 | New conditional ancestry reduction |
| CedarSafetySoundness, Semantics, Bridge, WhiteTransport | 238 | Existing dependencies |

The total of 283 new-module declarations includes definitions, generated declarations and the 225 individual cases. It is not a count of 283 distinct new mathematical theorems. The root replay totals 521 declarations. Every selected headline passed with no new axioms. All checks use Lean 4.35.0, kit pin `5473ffd075f63c9d626e63b8455805d4831b39ca`, and unchanged checker SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

All worker and root runs respected the 300-second, 8-GiB-owned and 2-GiB-free guards. Exact timing and memory evidence is retained. The reference project stayed read-only. An independent worker source/scope review of the D3 reduction found no defect; that review did not rerun the kernel. The worker's immutable delivery has 56 verified hashes; the complete delivery and both sets of replay reports are retained.

No new catalog PR, prize essay/API submission, backend verification, maintainer acceptance or full-solution claim accompanies this research checkpoint.
