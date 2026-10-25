from pathlib import Path
root=Path(__file__).resolve().parent
repo=Path(r'D:\MWB\Rule30\dyadic-source-catalog-20261025')
src=(root/'Rule30DyadicSourceResearch.lean').read_text(encoding='utf-8')
old='''/-! Actual seed run-boundary sources vanish on the low-depth support of a
dyadic Rule90 parity kernel. This is a pointwise source statement, not a
non-cancellation or nonperiodicity theorem. The unbounded-depth remainder is
unrestricted. No Duhamel/Green-function bridge is asserted in this module. -/'''
new='''/-!
# Actual Rule30 run-boundary sources on a dyadic binary support

The source `source d s` is exactly the black-to-white run boundary
`cell s (s-d) AND NOT cell s (s-d+1)` (`source_physical`). The local update
is Rule90 plus this source (`rule90_source_identity`).

Put H=2^e. Among depths d<=e and times s<2H-1, `SelectedEvent` requires d
even, `(H-1-d/2) AND (2H-2-s)=H-1-d/2`, and a nonzero actual source.
`selected_event_iff_outer` proves, for all e,d,s in that growing strip,
that exactly one event meets these requirements: d=0 and s=H-1.

The proof uses right-diagonal periodicity and the finite seed cone. At
phase H-1 every diagonal bit up to e is black; just after H the prefix
agrees with the early seed orbit. A positive-depth run-boundary source
vanishes at every phase selected by the binary support condition.

This core module states the mask explicitly. Its interpretation through
Lucas coefficients and the complete Rule90 Duhamel sum is supplied by
separate research proofs using Mathlib. No source deeper than e is
restricted here, no full source-sum noncancellation is asserted, and no
prize problem is solved. The standard diagonal periodicity and local
Boolean decomposition are not claimed as new historical results.

Contributed by Troy Lowry with OpenAI Codex, 2026-10-25.
-/'''
assert src.count(old)==1
src=src.replace(old,new).replace('namespace Rule30DyadicSourceResearch',
    'namespace Ruliology.CellularAutomata.Rule30RunBoundarySources').replace(
    'end Rule30DyadicSourceResearch','end Ruliology.CellularAutomata.Rule30RunBoundarySources')
target=repo/'lean/Ruliology/CellularAutomata/Rule30RunBoundarySources.lean'
assert not target.exists();target.write_text(src,encoding='utf-8',newline='\n')
p=repo/'lean/Ruliology.lean';text=p.read_text(encoding='utf-8')
anchor='public import Ruliology.CellularAutomata.Rule30Diagonals\n'
assert text.count(anchor)==1
p.write_text(text.replace(anchor,anchor+'public import Ruliology.CellularAutomata.Rule30RunBoundarySources\n'),encoding='utf-8',newline='\n')
p=repo/'lean/README.md';text=p.read_text(encoding='utf-8')
i=text.index('## Added in the kit');t=text.index('\n|---',i);end=text.index('\n',t+1)
row='\n| `Rule30RunBoundarySources` | 2026-10-25 | For every dyadic scale H=2^e, among actual black-to-white seed sources at depths d<=e and times s<2H-1, exactly one passes the explicit even-depth binary support mask: the outer source d=0, s=H-1. The deeper remainder is unrestricted; no prize solution is claimed. Contributed by Troy Lowry with OpenAI Codex. | `source_physical`, `source_dyadic_kernel_zero`, `selected_event_iff_outer` |'
p.write_text(text[:end]+row+text[end:],encoding='utf-8',newline='\n')
print(str(target))
