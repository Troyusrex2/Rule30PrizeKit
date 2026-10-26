# Periodic OR cannot hide an even source clock across two cells

The previous constant-OR obstruction now holds for any OR trace repeating
after the source half-clock. The proof covers every even half-clock and
does not assume a period for the two newer columns or unspecified older
columns. **Problem 1, safety completeness and the physical-center bridge
remain open.** These are local full-kernel checks, not new Wolfram backend
or human verification verdicts.

For an Actual triangular history, write six consecutive columns as
n,m,l,k,h,g, from older to newer. The update of each column from l onward
is `x' = x XOR (previous OR older)`. If R is even, k flips after R, and l
repeats after R, then `g OR h` cannot repeat after R. This strictly
strengthens the earlier exclusion of `g OR h = 1` at every time.

The exact headline is
`Rule30TwoPlateauClockResearch.actual_even_two_plateau_or_clock_rigidity`.
Its two corollaries prove that the next column, x at position j+6, cannot
repeat after R, even after an arbitrary finite transient. If x repeated,
its time derivative would make g OR h repeat, contradicting the theorem.
Time shifting the Actual history proves the transient version. This is a
statement about fixed right-edge depths, which follow moving physical
rays; it does not assert nonperiodicity of the physical center.

## Why the stronger argument works

Assume for contradiction that g OR h repeats after R. The new preliminary
theorem `actual_periodic_or_double_period` forces BOTH h and g to repeat
after 2R. Its proof covers all R. Since k,l have period 2R, the XOR update
gives h a constant 2R shift flag. A nonzero flag would make h anti-2R;
the earlier even-clock OR rigidity theorem then contradicts the assumed
OR period. Thus h is 2R-periodic. A black k forces a zero of h. At that
zero, OR periodicity kills g's 2R shift flag as well.

Compare the six-cell strip at times t and t+R. The paired graph now
requires equal newest OR values, allowing both zero and one. It requires
opposite k values and equal l values. The two oldest inputs of EACH copy
are free at every step. Three exact backward viability steps reduce the
640 possible paired states to 192,112,90. The old saturated-OR graph had
only 70 live states, so reusing its tables would not prove this result.

There are 20 upper-four-cell projections and 438 projected even-reach
pairs. Kernel-checked initialization, two-step closure and swapped-endpoint
exclusion give an invariant for every even path length. The derived 2R
periods require the upper-four-cell projection to swap after R, impossible
when R is even. There is no bound on R in the path induction, and no
assumption that the free older profiles share R or 2R.

## Verification and controls

At official pin5473ffd075f63c9d626e63b8455805d4831b39ca, the unchanged
Check.lean replayed all constants in all three modules:

| Module | Constants | Compile and replay | Peak owned RSS |
|---|---:|---:|---:|
| Rule30PeriodicOrPeriodResearch | 5 | 1.56s | 743 MiB |
| Rule30PeriodicOrPairCertificate | 138 | 6.27s | 909 MiB |
| Rule30TwoPlateauClockResearch | 54 | 3.13s | 866 MiB |

Counts include definitions and generated declarations. There are no new
axioms or native decisions. All jobs retained the 300-second, 8-GiB owned
process-tree, 2-GiB free-system-memory guards. The first main elaboration
failed because a shell text conversion left the older constant-OR premise
and damaged a quantifier; its exact source and failure logs are retained.
The corrected statement and both corollaries were fully replayed.

An independent finite control uses the literal rule table and two white
older boundary cells. It checks complete permutation orbits of all 8,064
words at widths7..12, including 514 source-premise instances. All expected
even-clock OR and next-column exclusions hold. Odd R really must be
excluded: width7, seed20 (least significant bit is oldest), j=0 and R=1
give a genuine finite-white counterexample to the unrestricted-R claim.
No counterexample to dropping the older-period premise was found in this
small control; that does not establish that the premise is dispensable.

The separate relaxed graph probe audits every local edge. Width5 admits
a swapped-projection path; widths6 and7 do not. Such a path with arbitrary
older inputs is not asserted to be a finite-white history. These bounded
controls are not premises of the Lean theorem.

The next missing step is a global clock or observer argument. This result
does not prove preservation across arbitrarily many newer columns, the
complete safety classification, or observation at the moving depth that
represents the fixed center. Cedar continues the separate safety target.
