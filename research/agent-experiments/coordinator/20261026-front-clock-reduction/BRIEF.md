# A sharper subset target: the collision clock

P1/Q01/CQ01, unconditional subset preservation and the fixed-center past
condition remain open. [New source and evidence](REPORT.md) pass full kernel
replay: 81 declarations, six headlines, unchanged pin 009005 checker.

We proved that for finite initial delta, preserving every initially supported
common mode inside delta is equivalent to this first-source property: delta
stays black at the first nonzero depth of every such mode. The proof peels
common suffixes of delta and terminates using the finite initial support.

The period-two first-source case is also proved. This leaves a concrete
background-only conjecture, `CollisionClock` in the source. For arbitrary
actual right-bounded histories a,b, delta=a XOR b, and every n, assume
delta(t,n+1)=0 for all t and delta(0,n+2)=1. Prove either:

- delta(t,n+2)=1 for all t; or
- a(t+1,n+1)=NOT a(t,n+1) for all t, and delta(t+2,n)=delta(t,n) for all t.

An exhaustive exact-temporal-prefix test through depth 14 found 2,288 varying
source candidates. Every one satisfies the second clock case, which the new
mode theorem excludes. This finite result does not prove CollisionClock at
arbitrary depth. A counterexample outside these cases would be equally useful.

`preservation_of_collision_clock` is conditional on that unproved statement.
Do not describe it as unconditional subset preservation. The fixed physical
center moves through right-edge coordinates, so even subset preservation does
not supply its missing past observation.

Possible approach: characterize equality of one temporal column for two
finite right prefixes. The tested nonalternating shared columns always share
their adjacent right column too. An exact automaton or rewrite system for that
relation may expose an inductive invariant. A finite learned classifier is not
a proof; seek a sound transition invariant or an explicit failure.

Continue returning unique response/version folders to
`D:\MWB\Rule30\agent-inbox`, preserving the existing REPORT.md/manifest.json
finding schema, source, provenance, resource records and READY written last.
Do not overwrite an earlier response. Multiple replies per agent are supported.
