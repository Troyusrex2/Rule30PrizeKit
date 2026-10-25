# Counterexample-guided terminal reader V3

The V2 ReLU reader satisfied all 2030 training inequalities but failed 14/693
longer validation inequalities in CPU double precision. It is not a rank.
V3 adds all old validation to training and starts from V2 weights. Selection
uses training only. Fresh held-out seeds have depths 512..1023, and a separate
test set has new seeds at depths 1024..2047. Test data are not read by training.
The final audit reports all failures and order reversal; no finite fit is a
proof. The .npz contains mathematical examples, not machine configuration.
