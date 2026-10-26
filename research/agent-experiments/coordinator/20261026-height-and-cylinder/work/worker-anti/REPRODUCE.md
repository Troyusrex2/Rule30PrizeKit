# Fresh replay

Use Lean 4.35.0, Mathlib 56a005855e and kit commit `5473ffd075f63c9d626e63b8455805d4831b39ca`. Verify unchanged Check.lean SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`. Copy this immutable delivery to a new writable private directory.

Compile RootEventHeight first, then RootAntiPeriodHeight. The former is the only custom dependency and exactly matches the prior immutable delivery. Its imports are the official Rule30Prize module and Mathlib's finite-sum basics and ring tactic.

In a private Lake project, build both modules and run the unchanged checker against both. The exact headline lists are in replay.py. For the new main theorem:

```text
lake env lean --run Check.lean RootAntiPeriodHeight --claim partial --headline RootAntiPeriodHeight.paired_height_identity --headline RootAntiPeriodHeight.safe_complement_height_difference --headline RootAntiPeriodHeight.height_three_periods --headline RootAntiPeriodHeight.safe_complement_zero_drift --headline RootAntiPeriodHeight.anti_period_safe_necessary --headline RootAntiPeriodHeight.not_safe_of_height_obstruction
```

For the retained G913 layout, in a writable copy under `C:/Users/troyu/Rule30-offload/research/`, run:

```powershell
C:/Users/troyu/Miniconda3/python.exe -B guard.py replay.py RootEventHeight
C:/Users/troyu/Miniconda3/python.exe -B guard.py replay.py RootAntiPeriodHeight
```

Adjust only historical environment paths for another private machine. Preserve all proof and checker bytes. The scripts write to their private lib directory and leave the reference project read-only. Guards are 300 seconds, 8 GiB owned process-tree RSS and 2 GiB minimum free memory.

`python -B verify_bundle.py` checks the retained evidence and source hashes; it does not replace a new full kernel replay. No compiled binary cache is included.
