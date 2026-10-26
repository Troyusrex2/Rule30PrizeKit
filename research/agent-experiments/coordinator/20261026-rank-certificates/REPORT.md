# Exact certificates for three more failed rank templates

The [unbounded nonsink theorem and checked delayed example](../20261026-reader-separation/REPORT.md)
remain the latest Lean results. Reader sink separation and Problem 1 are
**open**. This follow-up adds exact rational certificates for three specific
finite rank systems; these certificates are Python checked, **not Lean
verified**. There is no new prize submission or claimed full solution.

The previous search timed out on five sufficient graph-potential templates.
Their variables are unrestricted signed weights and potentials. Every
constraint except a target lower bound of one is homogeneous, so a rational
solution can be multiplied by a positive common denominator to obtain an
integer solution. Replacing integer SMT with exact rational SMT preserves
feasibility in these templates. All five rational SMT cases still reach their
20-second process caps; they remain unknown by that method. The inherited
`original_job_guard_stop` JSON field refers to the earlier integer job. The
rational driver itself finishes normally inside the original outer guard.

A separate sparse LP finds numerical infeasibility for context two with a
first spatial moment, and context three with and without that moment. Raw
floating-point dual rays fail exact checking. Sparse integer elimination on
their positive supports reconstructs exact rational null vectors. An
independent script then verifies, using fractions only, nonnegative weights
y, **y*A=0** in every column and **y*b>0**, for the recorded systems A*x>=b.
Taking their weighted sum gives 0>=y*b>0, a contradiction. The result is
about these sufficient linear systems; it does not exclude every rank with
the same context, every ranking method, or sink separation itself.

| Context | First moment | Nonzero Farkas weights | Columns checked | Positive margin |
|---:|---|---:|---:|---|
| 2 | yes | 314 | 676 | 574612/574731 |
| 3 | no | 597 | 974 | 599131888408/599180477283 |
| 3 | yes | 1066 | 1948 | 81614327132451/81585183475334 |

The raw sparse systems, floating rays, reconstructed certificates and exact
audit are included. Changed target weights and negative weights are rejected.
The audit trusts neither LP output nor the elimination implementation. The
graph/potential construction defining each system remains explicit in
`graph_lp.py`; the arithmetic certificate proves infeasibility of precisely
that recorded system. This is not a new Lean theorem about the automaton.

The four-symbol context cases remain unknown: rational SMT reaches both
process caps, the LP without a moment returns numerical Unknown, and the LP
with a moment reaches its 15-second limit. Neither has an exact certificate.
The earlier three UNSAT cases in the combined JSON are inherited integer-SMT
results, not new rational runs or kernel proofs.

The exact elimination takes 3.891 seconds with 19,574,784 bytes peak owned RSS;
the independent audit takes 0.266 seconds with 16,486,400 bytes. Every final
job is terminal. The 300-second / 8-GiB owned-tree / 2-GiB minimum-free guards
are unchanged. Internal case caps are recorded separately from proof results.

Run `python verify_artifacts.py` for byte/scope checks, and from work/ run
`python independent_audit.py` to recheck all exact certificates using only the
standard library. Regeneration uses z3-solver, NumPy/HiGHS for discovery and
psutil for guards; adjust the explicit local dependency paths in graph_lp.py.
No numerical solver is needed to audit the published Farkas arithmetic.

No unchecked external theorem was adopted. The latest official refresh at
04:01:45 UTC still names pin 0090056412733accaa27643d3cbbf982104f2251,
40 unchanged entries and skill 1.17.3. The agent inbox has no new ready reply.
The substantive open target remains the invariant sink, followed by the
separate CollisionClock and fixed-center bridges. Do not infer proximity to
the prize from these finite template exclusions.
