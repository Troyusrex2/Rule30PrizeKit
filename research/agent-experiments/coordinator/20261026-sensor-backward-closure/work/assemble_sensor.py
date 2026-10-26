from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
prior=ROOT.parent/'canonical-preimage-20261025T2303'
if not prior.exists():
 prior=ROOT.parent.parent/'20261025-canonical-preimages/work'
pre=(prior/'Rule30PreimageResearch.lean').read_text(encoding='utf-8')
pulse=(prior/'Rule30CanonicalPulseResearch.lean').read_text(encoding='utf-8')
rowfile=ROOT.parent/'counter-compatibility-20261025T1430/Rule30BlockRowsResearch.lean'
if not rowfile.exists():
 rowfile=ROOT.parent.parent/'20261025-causal-block-cycle/work/Rule30BlockRowsResearch.lean'
rows=rowfile.read_text(encoding='utf-8')
defs=pre[pre.index('def step'):pre.index('theorem recombination_local')]
helpers=''
for start,end in [('evol_local','physical_local'),('physical_local','canonical_gap'),('restart','gap_agreement')]:
 helpers+=pulse[pulse.index('theorem '+start):pulse.index('theorem '+end)]+'\n'
checkpoints=rows[rows.index('def step'):rows.index('theorem checkpoint_288')]
checkpoints=checkpoints.replace('step (','rowStep (')
body=(ROOT/'sensor_body.lean').read_text(encoding='utf-8').replace('-- CHECKPOINTS_INSERTED_HERE',checkpoints)
header='''module
public import Rule30Equivalents.IntegerRows
public import Rule30Equivalents.TFunction
public import Ruliology.CellularAutomata.Rule30Prize

/-! Physical finite-horizon counterexample retaining canonical backgrounds,
left edge, initial subset and zero center. P1 and all-time observability remain
open. Prior pulse/locality and integer-row checkpoint arguments are reused
from Troy Lowry's earlier verified research; no new axiom or native decision.
-/
@[expose] public section
namespace Rule30SensorClosureResearch
open Ruliology.CellularAutomata
open Rule30Jen (rule cell)
open Rule30Realization (evol)
open Rule30Equivalents.IntegerRows
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

'''
source=header+defs+helpers+body
target=ROOT/'Rule30SensorClosureResearch.lean'
target.write_text(source,encoding='utf-8',newline='\n')
print(json.dumps({'source_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'lines':len(source.splitlines())}))
