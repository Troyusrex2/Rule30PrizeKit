# Signed prefix-peak policy synthesis on complete finite configurations
+
+The rank is max(0, signed scores of all center-out word prefixes). It is
+nonnegative and permits cancellation. A local policy matches each output
+prefix to the current input prefix or its predecessor, chosen by reader
+state and last input token. All consistent reader predecessor states are
+checked. This is a sufficient all-length product-graph strategy, not a
+complete decision procedure for peak ranks. During final zero padding,
+the same choice may select the last or penultimate entire input prefix.
+
+Calibration includes an explicitly synthetic prefix deletion [3,1]->[3]
+positive control, an actual-graph zero-energy negative control, and 109312
+independent matched-prefix identities. The underlying exact two-step
+physical transducer passed 4096 canonical configurations and 1024 accepted
+updates. No finite numerical optimum is a Lean theorem. A positive rate
+must pass every rational inequality, then all CA/graph/rank bridges would
+need formal proof before any CQ01 claim. All-zero native optima are not
+formal impossibility proofs. Unknown statuses are preserved.
+
+Four owned shards cover seven reader templates and 1552 local policies.
+Each shard self-stops at210s and checkpoints with bounded replace retries;
+300s/4GiB RSS/16GiB free guards apply. No machine settings are changed.
+