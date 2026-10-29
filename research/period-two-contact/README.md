# Isolated-zero profiles and the remaining no-return-to-two claim

Partial results by Troy Lowry with OpenAI Codex. The unbounded no-return claim, general individual period nonloss, arbitrary Gate-future closing, Q01, and the Prize remain open.

## Proved

`No00 f` means `(f t || f (t+1))=true` for every time t. If f has an antiperiod p and No00, then f alternates and has period2. Combined with the actual prefix-clock growth theorem, this proves an unbounded structural constraint: if a newly added actual right diagonal has No00 and is not period2, it preserves every whole-prefix period p of its preceding prefix. Such a profile cannot introduce a new prefix clock. No finite bound on p is assumed.

For an actual right-diagonal array P, no return to period2 is equivalent to a common-zero assertion: whenever P(n+1) is not period2, P(n) and P(n+1) are simultaneously white at some time. This is an equivalence of two OPEN claims, not a proof of either. A return-to-two counterexample, if one exists, must have a non-period-two predecessor with No00. The generic recurrence and actual ordinary evolution are linked explicitly.

The new module passed a fresh6-source build and unchanged official checker: all25 owned declarations and14 selected headline types, no source warnings/new axioms/reused objects,5.68seconds. These counts include framework helpers. Full catalog integration is recorded in the companion prefix-clock archive; this unit receipt is independent.

```
python replay/verify.py --lean /absolute/path/to/lean.exe --out /new/empty/output
```

The exact pinned Windows Lean4.35.0 executable and unchanged checker hashes are verified. Other platforms require separately validated executable hashes. No Mathlib, downloads, solver premises, native evaluation bypass, sorry, or new axioms are needed. This is a focused closure build, not a whole-catalog build.

## Numerical evidence, separate from proofs

- The stronger shortcut No00=>period2 is FALSE. Seed33, with black cells at0 and-5, has actual diagonal5 with little-endian8-bit profile87. It has No00 and least period8. A closed eight-tick finite-prefix orbit and a separate ordinary literal Rule30 simulation match. This is an exact numerical witness, not an additional Lean certificate.
- A new complete width24 census inspected all16,777,216 states/23,144 cycles. Every No00 profile had dyadic exponent0,1,or3. Thus No00=>period8 survived this fixed test, but remains an unbounded conjecture. The detector had positive/negative synthetic controls and256 scalar-oracle controls; runtime7.97s, peak owned tree about34MiB. No larger width was tried.
- A separate SAT falsifier required an actual closed64-tick right-moving prefix, a period2 last profile, and a non-period2 predecessor. Widths25/26 returned solver-UNSAT; width27 hit its fixed two-second timeout and stopped. These are bounded solver results, not Lean proofs. Widths28..32 were not run.
- A new global cyclic-language invariant experiment tried DFA sizes2,3,4 only. All were UNSAT already on the registered training labels; no Rule30 certificate was found. This does not exclude larger automata or nonregular methods. The supplied exact Python validator checks root inclusion, cyclic transduction closure, and exclusion of OR-cover/nonperiod2 words at EVERY finite word length using product-graph reachability. It does not replace arbitrary Gate futures by periodic ones: its objects are the already periodic temporal profiles. A positive candidate would still require a Lean soundness proof. Validator controls include510 recognizer cases and a genuine positive constant-forcing control; an independent exhaustive encoder audit checked3072 small-DFA assignments, including conditional closure implications.

Each experiment includes its pre-registered caps, source, actual receipts and scope. No cap was raised after failure. The period8 conjecture alone has not been shown to imply the common-zero claim: hidden earlier clocks would still have to be controlled. Finite-window imitation barriers in PR48 prevent treating a short forbidden-window fit as an unbounded proof.

`MANIFEST.json` hashes all payloads. The table-analysis script has only its input path adapted for portability, recorded in `PROVENANCE.json`. Mathematical/checker source bytes and original experiment sources are preserved. The exact unresolved next claim is `ContactProgress (actualProfiles x)` for a start with rightmost black cell0 and a white right side; the file defines it precisely.
