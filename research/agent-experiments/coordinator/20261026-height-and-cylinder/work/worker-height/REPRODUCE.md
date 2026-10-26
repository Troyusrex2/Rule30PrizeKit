# Reproduction

Copy this immutable delivery to a new writable private directory. Use Lean 4.35.0, Mathlib 56a005855e and kit commit `5473ffd075f63c9d626e63b8455805d4831b39ca`. Verify unchanged Check.lean SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

There are no custom module dependencies. The source imports the pinned official Rule30Prize module, Mathlib's finite-sum basics, and Mathlib's ring tactic.

In a private Lake project, compile RootEventHeight.lean, then run:

```text
lake env lean --run Check.lean RootEventHeight --claim partial --headline RootEventHeight.signed_height_identity --headline RootEventHeight.even_return_signed_sums --headline RootEventHeight.even_period_signed_sums --headline RootEventHeight.marked_correction_range --headline RootEventHeight.event_iff_zero_pair --headline RootEventHeight.safe_marked_height_range --headline RootEventHeight.safe_height_white_initial --headline RootEventHeight.safe_height_black_initial
```

The retained Windows/G913 runner uses a private lib directory and a read-only pinned reference project. From a writable copy under `C:/Users/troyu/Rule30-offload/research/`, run:

```powershell
C:/Users/troyu/Miniconda3/python.exe -B guard.py replay.py
```

The historical paths in replay.py can be adjusted for another private environment. Preserve the checker and proof bytes. The guard limits are 300 seconds, 8 GiB owned process-tree RSS and 2 GiB minimum free memory.

`python -B verify_bundle.py` checks the archived evidence and source hashes. It does not substitute for a fresh full kernel replay. No binary caches are included.
