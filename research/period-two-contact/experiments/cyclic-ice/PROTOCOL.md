# One capped global cyclic-language invariant experiment

Target: a sufficient DFA invariant for no return to temporal period2, using the exact all-word-length validator in dfa_validator.py. This is a different target and domain from prior causal Mealy decoders and Gate-future RPNI attempts. Inputs here are already periodic temporal profile-pair words; no arbitrary Gate future is periodized or replaced by a lasso.

The DFA must accept every nonempty00-pair word; be closed under the cyclic running-XOR transduction (a,b)->(b,c), c(t+1)=c(t) XOR(a(t) OR b(t)); and exclude every accepted OR-cover word whose b-coordinate lacks cyclic period2. Exact finite product-graph reachability checks all word lengths for each candidate. A passing Python candidate is only a proposed certificate: a separate Lean soundness proof and kernel replay are required before any unbounded Rule30 claim.

Before execution, fix DFA sizes2,3,4 only; eight ICE refinement rounds per size; one second per native Cadical call; at most5000 training-prefix nodes;60-second/1GiB owned-tree/2GiB-available guard. Proceed to a larger registered size only after UNSAT at the smaller size. Stop the whole experiment at first UNKNOWN, timeout, iteration cap, node cap, or passing candidate. No larger sizes/caps or second attempt tonight.

Training positives are rotations of the previously computed complete q2/4/8 graphs. Initial negatives are OR-cover/nonperiod2 words of lengths3/4. A closure counterexample is added as an implication accepted(input)->accepted(output), not as an unconditional positive output: this avoids accidentally forcing unreachable words. Root counterexamples add positives; separation counterexamples add negatives. Labels are discovery hints only; exact candidate validation is independent. Retain all candidates and exact validation witnesses.

Controls: positive constant-forcing period2 recognizer, negative Rule30 closure control, and universal/root-only acceptors already pass510 scalar recognizer tests. Recheck those controls before learning. No installations/paid workers. No proof claim unless a positive Rule30 certificate is independently formalized.
