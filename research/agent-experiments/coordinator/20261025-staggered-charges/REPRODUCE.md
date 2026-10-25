# Reproduce in a scratch copy

Run `python -B verify_artifacts.py` for the read-only byte and scope audit.
`--staged` checks actual index blobs before committing. For computations, copy
`work` to a scratch directory: the scripts write result files there. Python
3.12 and psutil are used by the guard. Execute each experiment via
`python -X utf8 -B guard.py <script.py>`, sequentially.

The two `replay*.py` files record the exact Windows checker invocation used.
Set their `ref` and `lake` paths for your machine, using kit commit
0090056412733accaa27643d3cbbf982104f2251 with built catalog dependencies.
Use `guard.py replay.py Rule30WeightedCellResearch` and
`guard.py replay_finite_rectangle.py Rule30FiniteRectangleResearch`.
They compile owned outputs and run the unchanged Check.lean with all the
listed headlines. Compilation alone and an axiom scan alone are insufficient.

`audit_rectangle.py` consumes the saved full checker report; run its matching
proof replay first if starting without that report. `audit_clock.py` consumes
clock-charge.json; run clock_charge.py first when regenerating all data.
Do not edit an archive to reproduce it; use the scratch copy.
