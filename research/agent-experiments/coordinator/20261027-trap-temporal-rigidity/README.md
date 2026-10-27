# Prove arbitrarily late pair differences in the 001 trap

An actual Rule30 right-half history with an eventual prescribed `001` boundary that enters any correctly aligned `t001` state has different adjacent-pair values at arbitrarily late times at any two distinct spatial positions. The theorem assumes **no temporal period for the exterior** and no finite-support condition.

Precisely, for every `j < k` and every time bound `B`,

```text
there exists t >= B such that
  (F t j, F t (j+1)) != (F t k, F t (k+1)).
```

The boundary must follow the prescribed `001` driver from an onset `T`. At some `t1 >= T`, the actual finite prefix must equal one of the existing `t001` states, with its label aligned to `(t1-T) % 3`. The full Rule30 recurrence is retained throughout the right half. This conclusion says “arbitrarily late,” not “at every sufficiently late time,” and distinguishes pairs rather than necessarily each individual column.

The family also proves that **no positive common eventual temporal period exists**: there is no `p > 0` for which every column is eventually `p`-periodic, even if each column has a different, unbounded onset. The new generic half-line module supplies periodic representatives and head-symmetry propagation for any positive common period.

These results do not prove `AbsorptionT t001`, establish trap entry from arbitrary finite starts, exclude unbounded individual column periods, or solve Rule30 Problem 1. They do not claim that the entire 47-column certified strip repeats after 21 ticks.

## Source organization

All four modules use the catalog's public-import and `Ruliology.CellularAutomata` namespace conventions.

| Module | Role |
| --- | --- |
| [Rule30Period21Profiles](Ruliology/CellularAutomata/Rule30Period21Profiles.lean) | Generic inverse-chain collision argument and exact numeric profile predecessor. Unchanged from the earlier contribution. |
| [Rule30Certificates.TrapPeriod21](Ruliology/CellularAutomata/Rule30Certificates/TrapPeriod21.lean) | Checked path to a closed cycle excluding the normalized head. Unchanged numeric certificate. |
| [Rule30PeriodicHalfline](Ruliology/CellularAutomata/Rule30PeriodicHalfline.lean) | Columnwise eventual-period representative, finitely coded inverse-chain rigidity, and propagation of head temporal symmetries. No trap-family dependency. |
| [Rule30TrapPeriod21](Ruliology/CellularAutomata/Rule30TrapPeriod21.lean) | Literal physical and trap bridges, arbitrary common-period exclusion, and arbitrarily late pair differences. Original proof bodies retained; verified new proofs appended. |

Eight unchanged official dependencies come from commit `7d665044b904117af9e82328aeb90a30692b2b85`. The complete twelve-source closure uses core Lean 4.35.0, without Mathlib or downloaded packages. [BODY-MAP.json](BODY-MAP.json) records the namespace integration and the headline rename to `trapped_pairs_differ_arbitrarily_late`. The exact statements and proof terms were preserved.

## Reproduce

From this directory, with Lean 4.35.0 available:

```text
python verify.py --lean lean
```

The actual optional arguments are `--lean PATH` and `--run-name NAME`. A supplied run name must be unused and contain only letters, digits, underscores, or hyphens. For example:

```text
python verify.py --lean lean --run-name review01
```

The script checks source and checker hashes, builds all twelve sources into a new empty library, clears inherited `LEAN_PATH`, replays every declaration of the four contribution modules, checks all 32 named headline types, and prints their axioms. It writes raw logs and `RESULT.json` beneath a fresh `runs/` directory. No SSH, reference checkout, or compiled contribution cache is required.

The separate catalog commands are:

```text
lake build Ruliology.CellularAutomata.Rule30TrapPeriod21
lake env lean --run Check.lean Ruliology.CellularAutomata.Rule30TrapPeriod21 --claim partial --headline Ruliology.CellularAutomata.Rule30TrapPeriod21.trapped_pairs_differ_arbitrarily_late
```

The unchanged checker has SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

## Validation

Fresh full-closure validation passed: **814 contribution constants and 32 headline types**, with no new axioms. The per-module counts are 58/3, 624/4, 52/11, and 80/14 in the table's order. All twelve sources were freshly compiled with external `LEAN_PATH` cleared; no reference objects or Mathlib were used. All source-build logs contain no warnings. Raw checker logs retain the unchanged checker's deprecation warning.

The complete guarded job took 27.4896 seconds and peaked at 823,373,824 bytes (about 0.767 GiB), with no guard stop. These are measurements on one machine, not runtime guarantees. They cover source compilation, full replay, and printed types.

The [fresh full-replay receipt](evidence/fresh12/RESULT.json) records those results. The separate [targeted Lake receipt](evidence/lake-smoke/RESULT.json) also passed: the actual build took 14.6863 seconds, and the named-head checker invocation took 1.7385 seconds, replaying the family's 80 constants and checking the strongest headline. That complete guarded run took 16.5145 seconds and peaked at 840,314,880 bytes, with no guard stop. The single named-head Lake check supplements, rather than replaces, the full four-module replay.

Preparation metadata is preserved unchanged as provenance, including historical lines that said the canonical build was pending. [ARCHIVE-STATUS.json](ARCHIVE-STATUS.json) records that the fresh twelve-source replay and separate Lake check supersede those preparation statuses. The raw mathematical receipts remain the evidence for each result.

[SOURCES.json](SOURCES.json) lists the exact source closure. [PROOF.md](PROOF.md) explains the argument and limits. [MANIFEST.json](MANIFEST.json) seals the portable payload, including sources, checker, reproduction script, and evidence.

Contributed by Troy Lowry with OpenAI Codex. The official `t001` certificate and invariant, Rule30 definitions, Jen pigeonhole theorem, and other imported results are credited as prior work. This is a partial mathematical contribution, not a prize solution.
