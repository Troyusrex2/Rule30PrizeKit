from pathlib import Path
root=Path(__file__).resolve().parent
repo=Path(r'D:\MWB\Rule30\delayed-period-catalog-20261025')
names=['Rule30TailClassesResearch','Rule30PeriodicReconstructionResearch','Rule30DelayedDefectResearch','Rule30DelayedPeriodsResearch','Rule30QuantitativeDelayedResearch']
parts=[]
for name in names:
    s=(root/(name+'.lean')).read_text(encoding='utf-8')
    s=s.split('namespace '+name+'\n',1)[1].rsplit('end '+name,1)[0]
    for old in names:
        s=s.replace(old+'.','Ruliology.CellularAutomata.Rule30DelayedDefectPeriods.')
        s=s.replace(' '+old,'')
    s=s.replace('open\n','')
    parts.append(s)
header='''module

public import Ruliology.CellularAutomata.Rule30ZeroBoundary
public import Ruliology.CellularAutomata.Rule30StripCertificates

/-!
# Delayed temporal defects force unbounded spatial tail periods

Let `pure t = decide (t % 4 ≠ 1)`, the column whose even entries are black
and whose free odd entries alternate 0,1. The family `input j` changes
only time `8*j+5` from white to black. Equivalently, its free sequence is
alternating except for a black bit at index `4*j+2`, giving one run 111.
The free sequence avoids 00,11111,010110 and 1011010, for every j.

Every `Theta (free j)` is a valid constrained start and is eventually
periodic in *space*. Nevertheless every eventual spatial period P>0
satisfies `j < 2^P` (`theta_delay_lt_pow_period`). Thus the explicit
choice j=2^M has no eventual period at most M, even with an arbitrary
spatial transient (`theta_explicit_large_periods`).

Proof: a 312-cell table establishes the base defect's recurrent spatial
tail, different from the pure background. Outer locality and temporal
shift equivariance show that different delays have different tails modulo
finite prefixes. A P-periodic tail has at most 2^P residue words. Periods
are inherited by earlier delays, so j>=2^P would force a tail collision.
Temporal periodicity gives eventual spatial periodicity by a separate
finite-profile argument, uniformly in the temporal preperiod.

These are synthetic temporal inputs, not proved finite-right responses or
the canonical single-seed center column. Each spatial member is periodic;
the periods across the family are unbounded. The result supplies no
density bound, does not solve Q01 or CQ01, and solves no prize problem.

Contributed by Troy Lowry with OpenAI Codex, 2026-10-25.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30DelayedDefectPeriods
'''
source=header+'\n'.join(parts)+'\nend Ruliology.CellularAutomata.Rule30DelayedDefectPeriods\n'
target=repo/'lean/Ruliology/CellularAutomata/Rule30DelayedDefectPeriods.lean'
assert not target.exists();target.write_text(source,encoding='utf-8',newline='\n')
p=repo/'lean/Ruliology.lean';s=p.read_text(encoding='utf-8');anchor='public import Ruliology.CellularAutomata.Rule30ZeroBoundary\n';assert s.count(anchor)==1
p.write_text(s.replace(anchor,anchor+'public import Ruliology.CellularAutomata.Rule30DelayedDefectPeriods\n'),encoding='utf-8',newline='\n')
p=repo/'lean/README.md';s=p.read_text(encoding='utf-8');i=s.index('## Added in the kit');t=s.index('\n|---',i);end=s.index('\n',t+1)
row='\n| `Rule30DelayedDefectPeriods` | 2026-10-25 | A single white-to-black temporal defect at time 8j+5 gives a constrained Theta start with an eventual spatial period, but every such period P satisfies j < 2^P. Choosing j=2^M forces every eventual period above M. The free input avoids four finite forbidden words; actual finite-right realizability and density are not claimed. Contributed by Troy Lowry with OpenAI Codex. | `theta_delay_lt_pow_period`, `theta_explicit_large_periods`, `theta_spatial_periodic` |'
p.write_text(s[:end]+row+s[end:],encoding='utf-8',newline='\n')
old=(root.parent/'finite-feedback-20261025T1702/check_catalog.py').read_text()
old=old.replace('spatial-lifting-catalog-20261025','delayed-period-catalog-20261025').replace('Rule30SpatialPeriodLifting','Rule30DelayedDefectPeriods').replace("['word_power','stateAt_period','recon_period_lift']","['theta_delay_lt_pow_period','theta_explicit_large_periods','theta_spatial_periodic','free_no_010110','free_no_1011010']")
(root/'check_catalog.py').write_text(old,encoding='utf-8')
print({'source':str(target),'lines':len(source.splitlines())})
