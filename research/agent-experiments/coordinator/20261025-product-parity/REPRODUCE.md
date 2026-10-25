# Reproduce

Use Lean 4.35.0 at the saved verifier pin. Apply the three-file PR27 diff,
then from lean/ run:

    lake build Ruliology.CellularAutomata.Rule30ProductParity
    lake env lean --run ../Check.lean Ruliology.CellularAutomata.Rule30ProductParity --claim partial --headline Ruliology.CellularAutomata.Rule30ProductParity.all_ensembles --headline Ruliology.CellularAutomata.Rule30ProductParity.paired_F2_exact --headline Ruliology.CellularAutomata.Rule30ProductParity.paired_F2 --headline Ruliology.CellularAutomata.Rule30ProductParity.paired_F2_semantics

The core module needs no Mathlib. The arbitrary-group research companion
uses the pinned kit's Mathlib. Exact commands, source hashes and full replay
records are in work/evidence and work/catalog-evidence. The copied command
wrappers use machine-specific paths; adjust them for a different checkout.

For finite controls, copy work/ to scratch and run Python 3.12 plus psutil:

    python -B guard.py probe_seam.py
    python -B guard.py verify_seam.py
    python -B guard.py paired_charge.py
    python -B guard.py audit_paired_charge.py

They rewrite their own result files. No GPU, login or network is needed for
these mathematical checks. The independent scalar inverse and ring-rank
calculations do not use producer recurrences for their mathematical checks.
The seam harness calls the packed implementation only to obtain outputs to
compare with the independent result. Supplemental half-history scripts
are self-contained in their subdirectory, except that guard.py can be copied
from the parent. All research guards keep 300 seconds / 8 GiB owned RSS /
2 GiB minimum system available memory.

The essay is a draft. Its source and small Wolfram computations were checked;
notebook generation and fresh evaluation remain required. A notebook should
be built with the current MarkdownToNotebook and UseCache False, then checked
for an IconizedObject and evaluated cell-by-cell in a fresh plain kernel.
No submission or Wolfram Cloud consent is part of reproduction.

`python -B verify_artifacts.py` from this archive is read-only. It verifies
hashes, syntax, exact saved checks, scope, guards and source equivalence.
`--staged` reads the actual Git index blobs. This audit complements, and does
not replace, the unchanged official full kernel checker.
