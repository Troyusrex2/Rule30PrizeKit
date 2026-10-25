# Terminal-aware ordered rank reader V2

The baseline nonnegative prefix sum is impossible: the independently
reconstructed R=0x3496 example has two actual white-spatial transitions with
total reward 1, and the resulting same-phase word extends the original word.
The exact extension is [2,1,0,0]. Lean checks the word extension and the
algebraic contradiction; Python checks physical evolution independently.

V2 adds a squared readout of the last ACTIVE hidden state. Energy remains
nonnegative, but it need not increase under word extension. Padding must not
affect energy. The old source/results are unchanged. This is an architectural
repair, not a claimed universal rank. Training-only checkpoint selection;
the longer selection set from the baseline is now used only for reporting.
Neither finite training nor longer validation can prove an all-length claim.
No Wolfram submission or machine configuration changes are made.
