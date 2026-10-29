# Exact finite-past strip synchronization

Same overnight grant (14% total used target,13% new-research cutoff, no reset).

For each n in3,4,5,6,7,8, enumerate legal future gate prefixes by their exact length8 SFT windows. For each prefix, enumerate ALL legal n-bit pasts. Reconstruct the triangular spacetime strip symbolically as packed bits of its temporal boundary, retaining every one of the2n past time slices. When the past slices agree across every past choice at TWO adjacent spatial columns, prune the future-prefix branch: all later spatial columns agree because the future at time2n is common and Rule30 is left-permutive. A singleton past is trivially synchronized. No periodic completion is assumed.

Start with exactly the10 legal8-bit words. Each extension preserves the last7-bit state and requires the new8-window in S. Every such state must have a legal infinite continuation (check explicitly). At most64 future bits,200000 processed prefixes,90seconds,1GiB RSS per n,2GiB system headroom. A nonempty frontier at any cap is UNKNOWN. An empty frontier is a computational finite cover, not yet a Lean theorem. Preserve the terminal leaves and synchronization positions for independent literal replay and possible Lean formalization. Control n3 against the already kernel-proved arbitrary-future three-past theorem. Do not extrapolate a uniform bound to arbitrary n.
