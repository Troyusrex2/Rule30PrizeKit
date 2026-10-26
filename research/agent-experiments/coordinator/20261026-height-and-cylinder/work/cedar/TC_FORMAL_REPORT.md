# Verified all-clock obstruction to transition cover alone

`CedarTCObstruction.normalized_tc_chain` passed the unchanged official full-replay checker at pin `5473ffd075f63c9d626e63b8455805d4831b39ca`:37 new declarations,1.547 seconds build plus replay,772,788,224 bytes peak owned RSS.

The verified theorem concerns Boolean temporal profiles on Nat. For every k and every nonzero profile b returning after2^k steps, it constructs m<2^k and profiles x_0 through x_m with:

* x_0 constantly1 and x_m=b;
* every profile returning after2^k steps;
* Delta(x_(i+1))=x_i at each adjacent pair;
* the pointwise cover relation x_i<=Delta(x_(i+1))<=x_i OR shift(x_i).

The module also verifies compatibility of the constant-white pair and the white-to-constant-black pair, so arbitrary leading-white padding is a paper consequence. It does not assert the actual shared two-predecessor OR recurrence. It does not construct a finite-white Rule30 orbit or prove a D3 counterexample.

The proof uses a direct derivative iteration identity and Boolean cancellation:

    Delta^(2^k)b(t) = b(t) XOR b(t+2^k).

Periodicity annihilates this derivative. Finite descent finds a preceding nonzero derivative with zero derivative; on Nat such a profile is constant, hence constantly1. Reversing the derivative sequence gives the chain. This includes k=0 and the single-profile m=0 case. No large reductions, new axioms or native decisions were used.

The source-level theorem on Z in `adversarial/TC_ALL_CLOCK_OBSTRUCTION.md` independently passes paper review. Periodic Nat profiles and their derivative chains extend to Z by residues; that extension is not formalized here. The note's explicit one-zero-per-period Safe profiles also pass paper review: for2^k>=8, the first five positive derivatives vanish at phase1, giving all three preceding spatial triple000 events, while the terminal triple000 set is empty. For periods greater than8 this also defeats a cover-only Safe=>return8 inference. Those explicit corollaries remain paper results and concern the cover relaxation only.

Source: `CedarTCObstruction.lean`, SHA256 `2137d6db0e2890e59d49f2bf75dc9c32c62271bef354c35e2dbf7f8d91dd83ca`.

Evidence: `tc-final/report.json`, `tc-final/check.log`, `tc-final/build.log`, `tc-final/guard.json`. The failed initial source and logs remain in `CedarTCObstruction.attempt1.lean` and `tc-attempt1/`; three elementary elaboration issues were corrected, with no change to the theorem statements. `build/tc-source-freeze.json` records the source, dependency and runner hashes.

Reproduce in a private G913 copy using the existing unchanged pinned project and toolchain described in `REPRODUCE.md`: first build/replay CedarSafetySoundness, then run `python -B guard.py replay_tc.py CedarTCObstruction`. This run reused only this auditor's own freshly compiled and fully replayed CedarSafetySoundness dependency from the earlier isolated run, not another worker's binaries. The new job retained the300-second/8GiB/minimum2GiB guards. No live jobs remain.
