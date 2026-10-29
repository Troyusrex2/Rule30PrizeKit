# Fixed periodic-profile graph experiment

Construct the complete forward closure of pairs of q-periodic right-diagonal profiles from the white pair (0,0), for q=2,4,8,16,32 only. Integrating the Boolean OR forcing gives exactly two candidate next profiles, selected by their initial bit; an odd full-period forcing parity gives no periodic successor. Independently check every candidate against all q literal cyclic equations. Test whether every reachable pair has period(previous) <= period(current).

This is not a width-limited seed census: a closed graph could yield an invariant at every spatial depth, under the explicit whole-prefix period<=32 hypothesis. It does not by itself cover a first drop from period64 or larger, nor does it imply generic nonloss.

One G913 run,60-second wall cap,1GiB owned RSS,2GiB minimum available. Hard5000-node cap for each graph, no q64 attempt or automatic cap growth. No theorem adoption until a generic reconstruction bridge, graph closure, and period inheritance are proved and replayed in core Lean. Existing training pools q16/q32 supply comparison counts only; regenerate and check all transitions independently here.

Lean promotion uses the fixed q16 graph first (68 states), then the fixed q32 graph (2116 states); each fresh build/replay attempt has the standing300-second/8GiB owned/2GiB available guard. No q64 promotion, cap extension, or larger graph on failure. Boundary and all-spatial-depth reconstruction premises must be discharged before claiming an actual-seed result.
