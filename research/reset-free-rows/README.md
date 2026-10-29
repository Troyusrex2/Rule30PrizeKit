# Reset-free Rule 30 tails and sharp finite-row reset production

Two new statements, both on the actual literal recurrence:

1. If five consecutive rows have spatial tails avoiding every word `0 1^(3m+1) 0`, the first row has an eventually five-periodic spatial tail. Arbitrary finite prefixes are allowed. On the official zero-wall evolution, unless the current tail is already five-periodic, one of the next five rows contains these words arbitrarily far out.
2. Every nonzero finitely supported zero-wall row contains such a word at times 0, 1, or 2. This is sharp: two adjacent black cells and their first image both avoid all such words. The corresponding headline is `finite_nonzero_reset_in_three`, with `sharpness_two_rows`.

The words reset the three-state inverse quotient; one additional spatial cell completes coalescence of the full four inverse states. The proved statements here explicitly concern the displayed spatial words. They do not assert that a particular prescribed inverse is finitely supported.

The finite graph is not an extra hypothesis. `Rule30ResetFreeRuns` proves existence of run-modulo-three colorings for ordinary reset-free rows. `Rule30ResetFreeStrip` proves the base-six encoding and all transitions symbolically, then discharges the coloring and encoding premises. The five-row certificate checks all 7,776 vertices/two transitions, with dead ranks<=8, live transient ranks<=7 and a nine-state core. The finite three-row proof uses a separately checked 20-state reachable set from the zero wall; no nonzero reachable state can return to zero. Finite support supplies the actual terminal zero state.

## Scope and open problems

The five-row result proves eventual spatial period five, not a complete classification of all possible tail words. Finite rows already have a zero tail and lie in that periodic alternative. The sharp three-row result produces some reset in a short temporal block; it does not put that reset at the particular inverse layer needed for finite-predecessor closure. Odd-black extinction (`Q01`), the legal-gate finite class, arbitrary-future past closing, and the Rule 30 Prize remain open.

The discovered spatial-period-five travelling background `11100` refutes unqualified reset production for cyclic infinite backgrounds. It is motivation, not claimed novel. The two-row adjacent-pair sharpness witness is also proved in Lean, not just numerically checked.

## Verification

Official pin: 932cf8dde039b89b1dcbe9636867bb1b2057fef0, Lean 4.35.0. A fresh 13-source build, no reused objects, followed by the unchanged official Check.lean replayed every declaration in all five added modules: 335 declarations/40 headline type checks, no source warnings or new axioms. Combined imports/type/axiom smoke passed. The whole catalog was not rebuilt. The five sources are normalized to LF only, and PROVENANCE.json records exact original/canonical hashes.

Modules: Rule30ResetFreeCore (80/eight), Rule30ResetFreeRuns (38/five), Rule30ResetFreeStrip (103/twelve), Rule30ResetFreeBoundary (11/six), Rule30ResetFreeThree (103/nine), where the numbers count replayed declarations/headline checks, not separate mathematical discoveries.

Reproduce both the exact proof and the independent numerical certificate regeneration:

    python replay/verify.py --lean <Lean-4.35.0-Windows-lean.exe> --out <new-directory>
    python regenerate_data.py

The proof verifier intentionally pins the exact Windows Lean binary and unchanged checker hashes used for these receipts. The Lean source itself is ordinary core Lean. The numerical regeneration is standard-library Python, checks the packed rank data and 20-state set against a separate finite-graph generator, and literal-replays the sharpness example. Its result is not substituted for kernel replay.

An early attempted exhaustive dependent-function transition table exceeded the registered 8 GiB process guard and was stopped. The final proof replaces that table with a symbolic five-step transition proof; the memory cap was not increased. Data discovery used small controlled exact graphs. All finite numerical certificates used by the actual theorem are checked through the Lean kernel, with no solver premise or native-evaluation bypass.

Contributed by Troy Lowry with OpenAI Codex. The official Rule 30 definitions and existing kit results are credited as prior work.
