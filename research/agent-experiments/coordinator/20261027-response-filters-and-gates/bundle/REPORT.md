# Two-cell response filters and gated whole returns

Two new Lean modules sharpen the finite-word observation problem. They apply
to actual finite-word scans of Rule30, with the previously published
definitions T=C after A, r=the last bit, and s=the last bit after A.

`Rule30CAResponseFilterResearch` gives an exact information-loss criterion.
Fix any nonempty older prefix u and compare two choices of appended initial
bits (g,h),(g',h'). Let a,b be the differences of their r,s observation streams,
q=g XOR g', f=r_old and chi=r_old XOR s_old. At every time:

    a(t) XOR b(t) = q AND NOT f(t)
    b(t) XOR a(t+1) = q AND NOT s_old(t).

For D(v)(t)=v(t+1) XOR v(t) and any n>=0, the complete response is

    D^(n+1)a = q AND D^n chi
    D^(n+1)b = q AND (D^n chi XOR D^(n+1)f).

Consequently both order-(n+1) filtered outputs are independent of ALL four
appended initial pairs iff D^n chi=0 and D^(n+1)f=0 as complete time streams.
There is no period premise or minimum prefix length beyond nonemptiness.
This compares different configurations; a single observed orbit need not
supply the intervention. Spatial inheritance of the filter condition is open.

`Rule30CAGateReturnResearch` uses the clock-birth reconstruction to exclude
a new clock birth at a gated two-cell extension. Its explicit predicate is

    outR(u++[g,h],t)=NOT giter(u,g,t), outS(u++[g,h],t)=true for every t.

If nonempty u has a whole return T^P(u)=u, then this gated extension also
returns after P. No positive or least-period hypothesis is needed for that
statement. The proof first excludes both older output streams being constantly
the same color, then applies the exact masked clock-displacement identities.
The predicate is NOT transferred to u; this does not justify iterating the
two-cell deletion or prove the general gate-halving conjecture.

The two new leaves contain46 full-kernel-replayed constants and6 selected
headlines. Thirteen included dependencies contribute1117 constants and43
headlines; the complete portable bundle has15 modules,1163 constants and49
headlines. Constants include generated declarations. The checker and source
reference are pinned to5473, Lean4.35.0. Source/type audits independently
checked the quantified scope; partial checker typeMatches is not comparison
with an externally supplied expected proposition. No new axioms or native
proof shortcuts are used. The official dependency library is reused.

The surrounding archive separately contains paper derivations and named
counterexamples about guarded returns, even-run markers, global extrema and
the exact odd-cover defect. Those notes are NOT Lean-verified theorems.
They identify failed shortcuts and the unresolved boundary-to-tail step.

Reader completeness, phase separation, general plateau reconstruction,
the separate physical-center bridge and Prize Problem1 remain open.

Verify bundle files and stored receipts:

    python replay.py --verify-only

Rebuild every bundled module into a NEW separate output directory:

    python replay.py --lean /path/to/lean --official-lib /path/to/pinned/lib/lean --checker /path/to/pinned/Check.lean --output /new/separate/output

No private compiled artifacts are required. The supplied official library
must be built at the pin recorded in summary.json. The enclosing archive
contains the receipt from running this exact portable command.
