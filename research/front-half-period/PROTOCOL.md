# Bounded protocol

One owned G913 job at a time; no heavy local computation. Each fresh Lean attempt is capped at 300 seconds, 8 GiB owned RSS, and 2 GiB minimum system-available memory. One Lean worker thread. Stop only owned processes if a guard fires. No automatic cap expansion.

Before the first proof build: test the three-bit anchor on all W < 1024 in both phases, compare the finite update against the literal Boolean rule at widths 1,3,7,10, and decompose all finite front states at widths 1..18. Numerical controls have a fixed 60-second self-deadline. An arithmetic Q implementation was added for explicit bound comparison before the final replay; the Lean theorem uses the official Q definition.

The first three proof attempts failed on elaboration / simplification details, not counterexamples. Attempt04 proved the new front module, replaying 59 declarations. Attempt05 freshly replayed all three prefix/front modules, 195 declarations. The subsequent growth lemma is an independent elementary moving-edge argument, tested by fresh Lean builds and full checker replay. No failed conjecture is treated as a proved fact.

All adopted source bytes, unchanged checker, toolchain hash, fresh build logs, declaration replay, type/axiom smoke check, numerical receipt, and resource guard receipt are retained. Never infer a full Prize solution from a finite-window front return.
