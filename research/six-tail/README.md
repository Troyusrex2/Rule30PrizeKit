# Backward vacuum obstructions

The generic `Rule30BackwardVacuumResearch.no_padding_of_backward_certificate`
theorem is kernel-checked in the catalog checkout and the pinned reference kit.
It excludes an eventual word `0^r u` whenever a finite predecessor chain from the
vacuum along `0^N u` ends in the empty set, and

```
r >= max(N, 10*length(u)+11, K+9*(length(u)+1)).
```

It applies to every column of every configuration with a leftmost black cell.
Unlike the forward pumping method, this criterion does not require a stabilized
reachable set. It uses the existing analytic white-pulse reduction.

## Six-bit investigation: verification in progress

Exact backward obstructions were found for all sixteen six-bit words beginning
and ending in black. Their widest strip has width fourteen. Combined with the
prior five-tail result and rotation, they suggest the uniform extension to all
tails of length at most six with `r >= 77`. **The complete Lean assembly is still
under verification; that headline is not yet claimed as kernel verified here.**

The computational facts below have already been checked independently:

- Every predecessor set in [certificates.json](certificates.json) was reconstructed
  by a cellwise Boolean implementation, covering 889,216 transition cases.
- Three negative controls retain vacuum predecessors: removing one needed white
  step, decreasing the width, and using the earlier exceptional tail `10101`.
- Wolfram's free remote evaluator, version 15.0.1, independently encoded the finite
  transition histories as Boolean satisfiability problems. All sixteen positive
  cases were unsatisfiable; the one-shorter white run was satisfiable. Exact code
  and returned results are in [evidence/wolfram](evidence/wolfram/).

These remote Wolfram computations are exploratory cross-checks. They are not a
Wolfram prize-verifier verdict, an evaluated LeanLink notebook, or an API submission.

![Backward predecessor sets for 110001 at width fourteen](backward-obstruction.png)

The graph starts at the vacuum and runs backward through the six pulse bits and
then fourteen white steps. The predecessor sets become empty at the last step.
The largest stored set has 68 states. The finite completeness checks nevertheless
consider all 16,384 strips and both possible right inputs.

## Reproduce the computations

From the repository root:

```sh
python tests/check_six_tail_backward_research.py
python research/six-tail/generate.py
python research/six-tail/wolfram-crosscheck.py --width 14 --padding 14 --word 110001
python research/six-tail/wolfram-crosscheck.py --width 14 --padding 13 --word 110001
```

The generator writes Lean data modules whose predecessor implications are checked
with `decide +kernel`. It is a search/data-export tool, not a proof oracle. The
Wolfram script sends only this public mathematical model to the free remote
service; it uses no Wolfram ID and performs no prize submission.

Research and formalization: OpenAI Codex through `Troyusrex2`, building on the
earlier white-pulse, strip, and uniform Jen results. All results remain partial;
period two and the full prize questions are unresolved.
