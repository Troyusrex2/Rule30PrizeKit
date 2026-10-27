# Independent source, type and scope audit

Audit PASS for exact final `Rule30GatedDepthTwoResearch.lean`, SHA-256 `40320f742db353ee238fddd6d909c42cc15a74d4a4ce47ecb705bd98bff87362`. The auditor read the complete passed core source, the final bridge diff, all final printed headline types, both depth-two papers, the prior-result comparison, the complete prior TwoPlateauClock source and its report, and the relevant official ControlledResponse definitions. No new Lean replay was performed by the auditor or packager. Formal verification evidence is the author's unchanged-checker attempt03, which passed 70 module-owned constants and 11 headlines.

## Exact mathematical interface

Coordinates are newest-first, with the literal one-step recurrence

    x_i(t+1) = x_i(t) XOR (x_(i+1)(t) OR x_(i+2)(t)).

The profile function is indexed as `x i t`. Define h_i(t)=x_i(t) XOR x_i(t+P), and E(t)=true exactly when t is even. The supplied all-time observer relation is

    h_0(t) = E(t) AND h_1(t), for every t≥0.             D0

For even P this is equivalent, by Boolean algebra, to P-periodicity of the staggered scalar observation Y(t)=x_0(t) XOR (E(t) AND x_1(t)). That equivalence is an explanatory identity; it is not a separately exported Lean theorem here. The actual exported hypotheses are the displayed D0 relations in `prior-types/Rule30GatedDepthTwoResearch.log`.

The main local exclusion additionally requires P>0 even, anti-P trace x2 and P-periodic x3. It does not require periods of x0 or x1, an entire-output clock, a least period, or finite support. The exported `depth_two_impossible` type assumes the complete predicate `Actual x`; its proof uses only recurrences 0 through 5. The paper's eight-profile strip with x6,x7 as free oldest inputs is a justified reading of the argument, but that restricted-recursion interface is not the exact exported theorem type. The exported auxiliary theorem explicitly states four local recurrences plus the derived marked relation for q.

The finite-word conclusion is exact:

    P>0, P even,
    iterate (word u) P = word u,
    D0 for the actual orbit of word ([a,b,c] ++ u)
      ⇒ iterate (word ([a,b,c] ++ u)) P = word ([a,b,c] ++ u).

Here a,b,c are arbitrary Booleans; u is any finite Boolean list, including the empty list. The official `word` is newest-first `getD` with false default, so the older continuation is literally white. The statement concerns exactly three prepended newer coordinates. The general state theorem also allows arbitrary infinite older data whose tail from coordinate 3 has the supplied return. No black anchor, canonical form, or nonempty-word premise is hidden.

## Proof and boundary checks

The auxiliary q is never identified with a genuine Rule 30 column. Its odd one propagates forward under the shared recurrences, forcing an eventually constant drive for anti-P trace x2, which is impossible. Hence q vanishes on odd times. Genuine predecessor recurrences yield g=k only from time 1; no equality at time zero is used. An even q=1 from time 2 propagates, giving eventual q=E or q=0 and again an eventually constant drive. The evenness of P makes this contradict anti-periodicity. No eventual statement is silently transported backward, and q is not assumed periodic.

The actual finite-word bridge supplies the missing unit defect correctly. `tail_period_from_return` inducts on time using the autonomous older half-line. `oldest_failure_unit` derives a constant true P-defect at a coordinate that initially fails while every older coordinate returns. `staggered_tail_return` applies this at indices 2, 1, then 0. It assumes no 2P return of the extended trajectory and no finite observation window.

`iterate_tail` matches the official diagonal recursion by induction. `orbit_actual` is definitional equality for that recursion. `word_staggered_three_return` then uses the literal list-tail equality at index k+3. All indices read older coordinates i+1,i+2, including at i=0; no subtraction/default-boundary convention is smuggled into the recurrence. The all-time D0 condition uses E anchored at time zero; the export is not an eventual-observer or arbitrary-phase-onset theorem.

## Prior result and novelty boundary

The prior exact headline is `Rule30TwoPlateauClockResearch.actual_even_two_plateau_or_clock_rigidity`. At even shift 2n, it excludes periodic newest OR when the third-newest column flips and the next older column repeats. Its proof uses a six-column local paired-strip certificate and assumes no output clock. That result already yields the full-gated three-cell return corollary, together with the two short cases. This package does not claim that corollary as new.

D0 is a different observer premise. Under D0 the OR defect is

    h_1(t) * (1 + x_0(t) + E(t)*x_1(t))
      = h_1(t) * (1 + Y(t)),

in Boolean-ring notation. The shorter factor h_1(t)*(1+x_0(t)) applies only at odd times. Thus replacing D0 silently by periodic newest OR is not justified. This comparison concerns the observer hypotheses; it is not a claimed actual counterexample satisfying the impossible birth hypotheses. The new argument uses eight local columns versus the prior six, so it is not a blanket strict generalization of the earlier theorem.

The author report v1 omitted the parity qualification on that shorter formula. The auditor identified this prose error after the v1 seal. The author preserved v1 and supplied `AUTHOR-REPORT-v02.md` and `AUTHOR-ERRATUM.json`; both are included with their original provenance. The corrected global formula agrees with the already frozen comparison paper. No Lean source, theorem type, proof, or kernel result changed.

## Verification and remaining gap

Author attempt03 passed 70 own constants: 24 non-internal declarations and 46 internal generated constants, with 11 headlines, zero source warnings and no new axioms. The recorded guard used 3.051 seconds, peaked at 782,721,024 bytes owned RSS, and retained at least 44,613,693,440 bytes free. Limits were 300 seconds / 8 GiB owned / minimum 2 GiB free. This is fresh-leaf verification using eight previously compiled official modules, not a cold dependency build or a new Wolfram backend verdict.

The packager independently verified all 42 files in the author's original seal, the separate correction seal, the exact final source/receipt match, and all eight official source hashes at pins 5473 and 7d665. The recursive import closure is complete and has no Mathlib or research import. Portable manifest verification ran without invoking Lean. A new replay is available through the bundled helper but was not redundantly performed.

The result still requires D0 at every time and a supplied return of the older tail. It does not transfer the observer condition to successively older pairs, control births at arbitrary distance, identify the physical center, or prove any Rule 30 Prize problem. No publication or source editing occurred during this audit/preparation.
