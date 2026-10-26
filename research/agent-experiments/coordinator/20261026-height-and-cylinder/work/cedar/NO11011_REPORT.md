# Verified forbidden temporal word11011

`CedarNo11011.finite_white_no11011` proves that for every finite older-first Boolean word xs and every nonnegative time t, the newest column under the exact literal finite-white evolution cannot take values11011 at times t through t+4. There is no safety, return-period, width, normalization or eventuality premise. Prefix autonomy gives the corresponding statement for every spatial column. These are the existing moving-diagonal coordinates, not a fixed physical-center claim.

The unchanged official checker at pin `5473ffd075f63c9d626e63b8455805d4831b39ca` fully replayed31 new declarations. Build plus replay took1.626 seconds, with778,358,784 bytes peak owned RSS and over43GiB available system memory. No new axioms, native decisions, unchecked proof gaps or official-target claims were introduced.

The local theorem `local_no11011` concerns arbitrary temporal profiles B,A,u,v,w,z satisfying four shared OR equations on phases0 through3:

    Delta B=A OR u,
    Delta A=u OR v,
    Delta u=v OR w,
    Delta v=w OR z.

It rules out11011 in B by the two branches A(1)=0/1. No boundary or period assumptions are needed for this local result. The proof uses shared predecessor equations explicitly, so it does not silently replace them with transition cover alone.

`four_profile_no11011` applies the local result to four generated columns after arbitrary older profiles. Spatial induction extends this to words of effective length at least4. The15 initial words of lengths0 through3 are handled by small kernel decisions. The previously verified exact `profileTrace`/literal-evolution bridge then gives the finite-white theorem, and evolution composition shifts it to arbitrary starting time. This is an unbounded theorem, not a finite-word census or512-case cone enumeration.

The theorem is a local trace restriction. It does not prove D3, Safe=>return8, a bound on complete prefix clocks, or the prize target.

Files: `CedarNo11011.lean`, source SHA256 `951a3da95ec9e2b11a58ea3aa677e405e4666277acaf8fda5dd52fd27a059d9e`; `no11011-final/{report.json,check.log,build.log,guard.json}`; and `build/no11011-source-freeze.json`. The first failed source and logs are retained in `CedarNo11011.attempt1.lean` and `no11011-attempt1/`; failures were an overactive simplification in one three-Boolean lemma, a missing decidability instance for the five-bit pattern, and a missing t+0 simplification. Correcting those proof details did not change theorem statements.

Reproduce in a private G913 copy with the unchanged pinned project and compiler described in `REPRODUCE.md`: freshly build/replay CedarSafetySoundness and CedarSafetySemantics, then run `python -B guard.py replay_no11011.py CedarNo11011`. This run used this auditor's previously fresh, fully replayed private dependencies (137+75 declarations). All meaningful compilation/replay stayed on G913 with300-second,8GiB owned RSS and minimum2GiB free-memory guards. No live jobs remain.
