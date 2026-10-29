# Prefix clocks for every right-bounded Rule30 configuration

The new prefix-clock bridge discharges the finite-seed interpretation missing from ghywel's PR51. A prefix period is shared by **every** diagonal up to the current one. It can only stay or double; when it doubles, the newest diagonal complements under a shift by the old prefix period. Individual diagonal periods may drop, and no claim of individual period nonloss is assumed.

`Rule30RightPrefixClock.actual_no_11011` excludes the prefix-clock word `11011` once its base exponent is at least2, on actual `Rule30Realization.evol`. The middle plateau is explicit. `exists_prefix_exponent` proves the clocks exist for every right-bounded initial configuration, including every finite seed. General dyadic periodicity for such configurations already existed in `Rule30FiniteDiagonals`; that fact is not claimed as new here.

The second module reuses the official single-cell difference-order/record-charge half-rate proof. Its new step is to supply that argument from prefix periods, so its conclusion holds for **every right-bounded configuration**, with arbitrary contents to the left. If the configuration is white right of R, diagonal n left of R+t repeats from time zero with period `2^B(n)`, where the existing `B(n)=ceil(n/2)+Q(0,floor(n/2))` has an iterated-logarithm correction. The literal evolution statement is `evol_right_diagonal_half`; the whole-prefix statement is `right_bounded_prefix_half`.

The 101 shift law is ghywel's, and the half-rate accounting is reused from the official kit. These modules extend the applicability of those results. They do not prove generic individual period nonloss, unbounded legal-past closing, or any Rule30 Prize statement.

## Validation

- Exact PR51 head: `5d4cc975534cb09cd424646696de2488838afb52`; imported source SHA256 `014be30fa094111eb9bdd9d457ccb82c9c46220c908cdf7eaa5fe74951889ac1`. Independently replayed earlier before use.
- Official pin: `932cf8dde039b89b1dcbe9636867bb1b2057fef0`, Lean4.35.0, unchanged official `Check.lean`.
- Clock module: fresh five-source closure and full replay,57 declarations/six headline type checks, source `2b74c47ffc22f6f7cf8ad9c912ab389cffb182db4137ca2571590c961c35a2c6`.
- Bound module: fresh eight-source closure and full replay,79 declarations/six headline type checks, source `67cf1bb230eaf01631d757ce05c88a44473ebbe4ba1d5f6dc5e4ac6efe408c4e`.
- No objects reused, source warnings, or new axioms. These are focused closures, not whole-catalog builds. Exact statement and axiom logs are included.
- Python sanity checks are explicitly separate from Lean proofs. All512 width-ten seeds with a black rightmost bit passed the 24-diagonal/64-tick literal comparison. There were567 guarded `1101` occurrences, no guarded `11011` continuation, and512 small-clock exceptions at base exponent1. Full finite triangular-map cycle decompositions through width22 cover all4,194,304 states at that width and satisfy the universal bound.

Each replay directory has a portable `verify.py`; use `--lean <official-Lean4.35.0-Windows-lean.exe> --out <new-directory>`. Run both to replay both new modules. Payload hashes and scoped Git attributes preserve exactly the tested source bytes.
