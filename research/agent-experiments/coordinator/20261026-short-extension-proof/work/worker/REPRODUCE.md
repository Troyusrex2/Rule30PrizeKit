# Fresh replay

Use a private project with Lean 4.35.0, Mathlib 56a005855e and the official kit at `5473ffd075f63c9d626e63b8455805d4831b39ca`. Verify Check.lean against SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

Copy the immutable bundle to a new writable work directory before executing anything. Preserve the archived copy. The exact compile order is:

1. CedarSafetySoundness
2. CedarSafetySemantics
3. CedarSafetyBridge
4. RootShortExtensionCore
5. RootShortExtensionCases
6. RootShortExtensionCertificate
7. RootShortExtension

The three Cedar sources are exact copies of `verifier/*.lean` from response `r30-codex-cedar-followup-20261026T154236Z-b768c9a6-v02`. Their hashes and origins are in `dependencies.json`. No other custom proof dependency is required. The Mathlib FinCases and Fintype Fin imports are supplied by the pinned environment.

For the retained Windows/G913 layout, copy the writable replay directory under `C:/Users/troyu/Rule30-offload/research/`, then run for each module:

```powershell
C:/Users/troyu/Miniconda3/python.exe -B guard.py replay.py MODULE
```

`replay.py` compiles the exact source to its private lib directory, invokes the unchanged checker on every declaration in that module, checks the specified headlines, and records source/checker/compiled hashes. `guard.py` enforces 300 seconds, 8 GiB owned process-tree RSS and 2 GiB minimum free memory. The scripts' reference paths are historical; adjust only those paths for another private environment, preserving the pinned sources, checker and proof files.

For a regular private Lake project, compile each module, then run:

```text
lake env lean --run Check.lean RootShortExtension --claim partial --headline RootShortExtension.safe_short_extension --headline RootShortExtension.accepted_short_extension_language
```

Repeat the checker for every dependency module using the exact headline list in `replay.py`. Checking only the final axiom list is insufficient.

`python -B verify_bundle.py` checks retained evidence hashes and source/report correspondence. It does not rerun Lean. `generate_certificate.py` reproduces the split sources and case descriptions in a writable copy; the produced certificates are not accepted until Lean checks them.
