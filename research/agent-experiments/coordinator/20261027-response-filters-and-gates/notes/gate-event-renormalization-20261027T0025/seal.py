import hashlib
import json
from pathlib import Path

p=Path(__file__).resolve().parent
def sha(f):
    return hashlib.sha256(f.read_bytes()).hexdigest()

sources=[
    p.parent/'uniform-gate-halving-20261027T0010'/'PAPER.md',
    p.parent/'predecessor-periodicity-paper-20261026T2305'/'PAPER.md',
    p.parent/'gate-half-defect-20261027T0015'/'PAPER.md',
]
result={
    'status':'exact paper return relation; uniform halving OPEN',
    'official_pin':'5473ffd075f63c9d626e63b8455805d4831b39ca',
    'new_lean_build':False,
    'new_kernel_claim':False,
    'new_state_period_gap_sweep':False,
    'new_public_write':False,
    'positive_results':[
        'D^t(1+2^(4q)m)=1 XOR 2^(4q-2t)Phi^t(m), for t<=2q',
        'q>1 decreases by one every two steps, retaining tail Phi^2(m)',
        'exact five-register cocycle over actual R=D^2 tail',
        'guarded normalized return N(m)=Phi^(2s)(R^J(m)/16^s)',
        'whole 2P return guarantees J+s<=P',
        'finite positive tail bit length is conserved by N',
    ],
    'control':'one prespecified inherited infinite-tail return PASS',
    'independent_paper_audit':'prize_bridge_audit PASS; not Lean replay',
    'remaining_obligation':'exclude a recurrent guarded actual-tail path using finite whiteness',
    'prior_sources':[{'path':str(f),'sha256':sha(f)} for f in sources],
}
(p/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
files=sorted(f for f in p.iterdir() if f.is_file() and not f.name.startswith('MANIFEST'))
manifest={'version':1,'files':[{'path':f.name,'bytes':f.stat().st_size,'sha256':sha(f)} for f in files]}
(p/'MANIFEST-v1.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'paper_sha256':sha(p/'PAPER.md'),
                  'manifest_sha256':sha(p/'MANIFEST-v1.json'),
                  'files':len(files)}))
