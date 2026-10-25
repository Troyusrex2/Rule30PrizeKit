# Reproduce

The catalog module uses core Lean4.35.0. At the saved verifier pin, apply the
three-file PR26 diff and run, from lean/:

    lake build Ruliology.CellularAutomata.Rule30DividedDifference
    lake env lean --run ../Check.lean Ruliology.CellularAutomata.Rule30DividedDifference --claim partial --headline Ruliology.CellularAutomata.Rule30DividedDifference.unobservable --headline Ruliology.CellularAutomata.Rule30DividedDifference.Front.actual_difference --headline Ruliology.CellularAutomata.Rule30DividedDifference.Front.mode_left_edge

The saved catalog-evidence/report.json lists the full11-headline command.
Require full successful kernel replay and no new axioms. The research source
has the same proof in a separate namespace. No Rule30PrizeKit root import is
needed for a core catalog module; this is not a prize essay submission.

Finite controls: Python3.12, psutil5.9.8, and Matplotlib/NumPy only for the
figure. In a COPY of work/ run `python -B guard.py SCRIPT.py` for
curvature_control.py, merging_backgrounds.py, parity_conservation.py,
audit_parity.py or plot_barrier.py. Their files are rewritten. Absolute local
paths in the Lean build/GitHub preparation wrappers must be adjusted for a
different checkout. The proof itself has no local-file or network dependency.

From this archive, `python -B verify_artifacts.py` is read-only. It checks
hashes, source equivalence, exact checker results, guards and scope. With
--staged it reads the actual Git index blobs. No API submission or Wolfram
sign-in is part of these checks.
