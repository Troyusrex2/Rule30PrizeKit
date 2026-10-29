# Is predecessor uniqueness already false for actual finite seeds?

The small complete profile graphs suggest every nonalternating profile determines its preceding profile uniquely, even across different seed depths. This is stronger than period nonloss. Before asking for an unbounded decoder proof, test it on all exact finite T-map cycles at width24. Different depths<=23 are included by inserting leading zero bits, since T commutes with left shift.

For every cycle extract the two highest bit profiles, reduce the newer profile to its least dyadic period, verify the older profile shares that period, then use a canonical cyclic rotation of the newer word to align its older word. Any conflicting older word is an actual finite-seed counterexample to uniqueness, not necessarily to period nonloss. Period1/2 profiles are explicitly exempt. Retain a complete aligned witness; do not publish a conjecture as a theorem.

Booth canonical rotation is checked against exhaustive direct rotations for all510 binary words of lengths1..8. All2^24 finite states are fixed before execution. One60-second/1GiB owned/2GiB available G913 job, no larger width, no automatic cap increase. The previous finite census measured period decreases only; this is a different stronger hypothesis, not a wider repeat of that search.
