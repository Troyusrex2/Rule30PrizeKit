# Synchronizing carriers and all pasts of a second periodic Gate family

This is a partial result. The Rule30 Prize, arbitrary legal Gate futures, and the unbounded finite-cover hypothesis remain open.

`Rule30SynchronizingCarrier` abstracts the proved gap-five mechanism. A carrier consists of spatially periodic rows, a preceding-time phase map, the ordinary inverse recurrence, and a certificate that one complete spatial cycle sends every inverse input pair to the reference pair. The generic theorem retains an arbitrary finite prefix: one inverse head costs at most two cycles, and every n-bit Gate past costs at most four cycles times n. The phase type is arbitrary. The original gap-five bound is recovered as a checked instance.

`Rule30PeriodicThreeFive` supplies a second instance. Its Gate future has black cells at residues0 and3 modulo8, with little-endian physical boundary word65470 of temporal period16. The actual spatial reconstruction has39 transient profile-pair states and a325-column cycle beginning at spatial column40. Both the transient and the cycle are connected to the official `recon`/`lam`; no near-wall periodicity is assumed. Its eight Gate windows lie in the required ten-word set.

Any two n-bit pasts of this future reconstruct rows equal at every spatial position k>=40+1300*n, for every n and every past bit. Admissibility of the pasts is unnecessary. The phase and finite-prefix extension covers all cyclic Gate phases and an arbitrary m-bit prefix, with cutoff40+1300*(m+n). This cutoff depends on m. No density argument from eventual periodicity to arbitrary futures is asserted.

The mathematical contribution is a reusable all-length criterion and its second concrete family, rather than a larger fixed-n census. The finite input data were previously computed in the gap-five archive; these new Lean modules discharge their missing reconstruction and arbitrary-n proof obligations. The original R5-03 assignment had no acknowledged receipt; root worked in a separate folder without modifying another agent's files.

## Replay

```
python replay/verify.py --lean /absolute/path/to/lean.exe --out /new/empty/output
python -B audit.py
```

The fresh11-source check passed all131 declarations owned by the two new modules and24 headline types, without source warnings or new axioms. Counts include certificate and framework helpers. It took26.22seconds, peaking at1,874,853,888 owned RSS bytes, within the fixed300-second/8GiB guard. The verifier freezes the complete dependency closure and unchanged official checker, builds from fresh sources, and checks exact headline types and axioms. See `evidence/RESULT.json`, `evidence/Types.log`, and the guard receipt. This is a focused closure build, not a whole-catalog build. The pinned Windows Lean executable is required; another platform needs a separately validated executable hash. No Mathlib, cached objects, downloads, solver premises, native evaluation bypass, sorry, or new axioms are needed.

The Python audit independently evaluates the literal eight-entry Rule30 truth table for5200 carrier recurrence cells,640 transient cells,64 inverse-block maps, and all8 Gate windows. It also checks that the exact packed Lean constants equal the raw data. These numerical controls are distinguished from the all-length Lean theorem.

Dependencies include the original gap-five/zero-boundary sources from PR47; their exact bytes and unchanged checker are frozen in `replay/INPUTS.json`. All new sources use the same project conventions. `.gitattributes` preserves validated bytes on checkout. `MANIFEST.json` hashes all payloads except itself. Earlier archived evidence is retained as a historical snapshot.
