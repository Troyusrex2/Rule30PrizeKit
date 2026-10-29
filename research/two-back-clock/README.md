# A period-two return needs a large clock two diagonals earlier

Partial result by Troy Lowry with OpenAI Codex. For an ordinary initial configuration white to the right of R, write D_n(t)=evol x t(t-(-R+n)).

If the whole prefix through D_n has period32 and D_(n+2) has period2, then D_(n+1) has period2. Consequently, a return-to-two counterexample with a non-period-two predecessor requires prefix clock at least64 already at D_n, TWO diagonals before the returned profile. This strengthens the previous one-diagonal clock condition. The general no-return/common-zero claim and the Prize remain open.

The proof uses the new isolated-zero constraint: a counterexample's predecessor has no temporal00; if non-period-two, it cannot introduce a new prefix period. Thus period32 at D_n propagates to D_(n+1). Period2 of D_(n+2) then extends the prefix period32, and the checked profile graph forces its predecessor to have period2, a contradiction.

The two retained headline theorems are `two_back_period_two` and `counter_two_back_clock64`. A draft absolute-depth corollary based on B(8)<=5 was removed after kernel evaluation disproved that numerical premise. No absolute depth11 claim is made. Explicit Int-index normalization avoids expensive failed definitional conversion; no resource cap was raised.

The final unit check passed a fresh13-source closure, all15 owned declarations and2 headline types, with no warnings/new axioms/reused objects,49.72seconds/peak843,608,064bytes. Counts include helper declarations. The full catalog integration is independently recorded in the companion prefix-clock archive. This is a focused closure build, not a whole-catalog build or Wolfram reviewer approval.

```
python replay/verify.py --lean /absolute/path/to/lean.exe --out /new/empty/output
```

All source/checker inputs are frozen, and the pinned Windows Lean4.35.0 executable hash is checked. Another platform needs a separately validated executable hash. No Mathlib, downloads, cached objects, native evaluation bypass, solver premise, sorry, or new axiom is needed. Actual build/check/type/axiom/guard receipts are in evidence/. MANIFEST.json hashes all payloads; `.gitattributes` preserves exact checked bytes.
