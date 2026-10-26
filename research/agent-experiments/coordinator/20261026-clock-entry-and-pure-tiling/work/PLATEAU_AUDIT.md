# Remaining finite-white plateau problem

This is a paper audit following the sealed 60-declaration proof package
`safe-to-height-two-20261026T2042`. No additional Lean theorem or finite
strip search is claimed here.

Let x be a minimum-width genuine Safe word failing WHOLE return8, and
write x = u ++ [c,d]. Root's short-extension theorem forces u, and the
one-cell intermediate prefix, to fail whole return8. Minimum width also
forces both temporal00 and11 in each of those prefixes. The previously
verified height-one descent rules out all-time white-height span≤1 there.

The new intrinsic dichotomy either already supplies the desired genuine
height-two/nonreturn ancestor u, or leaves

    evenClock(x) = evenClock(u ++ [c]) = evenClock(u).

The first equality is unconditional for a Safe last cell. The second is
the unresolved alternative. These clocks are least positive EVEN returns
of the entire finite words; the argument does not know that the newest
column attains them.

## What half-clock shifting really supplies

When a genuine prefix returns at R and its one-cell extension does not,
the added leaf is anti-R. This is now formally proved by actual evolution,
restart, and leaf-flip transport. Thus a temporal shift can identify the
first column where a selected older-prefix return fails.

It does not relocate that first changed column to the immediate parent of
the Safe endpoint. There can be a spatial interval after the first change
in which the WHOLE-prefix clock is unchanged. On that interval the shift
of each individual column need not be its complement or itself; its
shift difference can be a nonconstant temporal profile. Therefore one
cannot apply the paired anti-period height identity at the endpoint merely
because some older column was anti-periodic.

The same issue remains if an arbitrary common dyadic return clock is used:
having a returning parent at a deliberately oversized clock produces no
anti-periodic leaf. One needs a failed return of the extension at exactly
that parent clock. Conversely, using the least clock of a single column
does not establish return of all its older coordinates.

## Legitimate shortening and its limitation

A repeated adjacent pair of complete temporal profiles does permit exact
spatial deletion. If histories(u) = histories(u ++ v), then the recursive
history transport makes u ++ w and u ++ v ++ w have identical endpoint
traces for every time. If u itself already fails whole F8, both words
remain whole nonreturns by prefix autonomy. With nonempty v, deleting v
would contradict minimum width whenever the longer endpoint is Safe.
This paper deduction follows from the already verified histories_append,
trace/evolution transport, and prefix autonomy.

However, equal whole-return clocks are not equal temporal profile pairs.
A plateau may follow a path of distinct pairs, and its state space grows
with the temporal clock. No width-independent bound, forced repetition,
or short path to the white boundary has been proved. Treating clock
equality as a removable spatial repetition would be a new error.

## Precise missing reduction

It would suffice to prove that a minimum-width genuine Safe/nonF8 word
cannot have the displayed two-cell whole-clock plateau, or to extract a
genuine height-two/nonreturn word from such a plateau by another operation.
That assertion is NOT proved here. It is more specific than asking for an
unspecified periodic/anti-periodic triple: the adjacent clock-jump case is
already covered, and the only remaining case is the exact intrinsic
clock equality above.

The separately kernel-checked period16 free-boundary control shows that
four shared recurrences, Safe at the endpoint, no11011/no00100 throughout,
and temporal00/11 in all older traces do not alone force a height-two near
parent. A solution of this remaining case must use finite-white ancestry
or an additional invariant that survives the plateau. No finite-window
observation, added clock premise, or unproved no-period-drop assumption
has been substituted for that missing argument.
