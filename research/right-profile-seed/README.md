# The contributed 101 shift law on the actual single-cell orbit

The new `Rule30RightProfileSeed` module specializes ghywel's PR51 shift law to the kit's **actual single-cell right diagonals** `Rule30Diagonals.R`. It uses official `Rule30RightPeriods.antiperiod`, `no_three`, and period monotonicity to discharge the abstract profile hypotheses.

For j>=1 and E>=2, suppose the least period exponents at j,j+1,j+2,j+4 are E,E+1,E+2,E+3. Then the exponent at j+5 is E+3. The intervening j+3 plateau follows from the existing `no_three` theorem. Thus the actual single-cell doubling word 11011 is excluded under these guards. The public headlines are `no_11011_period`, `exponent_1101_forces_stay`, and `no_11011_exponents`.

This is a single-cell specialization, not a theorem for arbitrary finite initial codes. It does not improve the existing asymptotic period bound or prove a Rule30 Prize statement. The underlying shift law and its mod-4 forms belong to ghywel; this archive is an independent replay plus an application bridge, not a claim of authorship of those results.

## Exact inputs and verification

* Official kit pin: 932cf8dde039b89b1dcbe9636867bb1b2057fef0, Lean 4.35.0, unchanged Check.lean.
* External PR51 head: 5d4cc975534cb09cd424646696de2488838afb52, module SHA256: 014be30fa094111eb9bdd9d457ccb82c9c46220c908cdf7eaa5fe74951889ac1. Its fresh independent replay passed 67 declarations/eight headline checks.
* External PR50 head: 9a458c5bc3444a70d17f2b5994780ba1519c2176, module SHA256: 7997c71027eb67e37a982d6de0eb70169935da721d62f6408f79f307b8bf1781. Its fresh independent replay passed 159 declarations/nine headlines. This left-profile module is not a premise of the new bridge.
* New bridge source SHA256: e3f30d05550184aa4f3878625f8004580726976c8e5ca3d422ee5f8e5f4084bb. A fresh ten-source dependency build and unchanged-checker replay passed 13 declarations/three headlines, without source warnings or new axioms.

No objects were reused. These are focused source closures, not whole-catalog builds. `Types.log` and checker JSON record exact statements and axiom sets. The external modules were replayed before using PR51 as a premise.

## Reproduce

    python seed-bridge-replay/verify.py --lean <official-Lean 4.35.0-Windows-lean.exe> --out <new-directory>

The original PR50/51 independent replay is analogous under external-pr-replay/. The verifiers check binary/source hashes, build from the supplied sources, and run the unchanged official checker. MANIFEST.json hashes all payloads, and scoped Git attributes preserve the validated bytes.
