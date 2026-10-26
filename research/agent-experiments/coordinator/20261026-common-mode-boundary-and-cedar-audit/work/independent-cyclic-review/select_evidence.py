"""Select source and review evidence, excluding private build caches."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
JOBS=ROOT.parents[1]/'coordination/jobs'
evidence=ROOT/'guard-evidence';evidence.mkdir(exist_ok=True)
for prefix in ['verifier-mode-transient-audit-','verifier-mode-transient-replay-','verifier-mode-supplied-cones-']:
    for src in JOBS.glob(prefix+'*'):
        assert src.suffix in ('.json','.log')
        dst=evidence/src.name
        if dst.exists():assert dst.read_bytes()==src.read_bytes()
        else:dst.write_bytes(src.read_bytes())
selected=[]
for p in sorted(ROOT.rglob('*')):
    if not p.is_file():continue
    rel=p.relative_to(ROOT)
    if rel.parts[0]=='reproduction' and (len(rel.parts)>1 and rel.parts[1] in ('kit','kit-source.tar')):continue
    if p.name=='REVIEW_MANIFEST.json' or p.suffix in ('.olean','.pyc'):continue
    selected.append(dict(path=rel.as_posix(),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
assert any(x['path']=='reproduction/Rule30CyclicSubsetObstructionResearch.json' for x in selected)
manifest=dict(status='PARTIAL_KERNEL_CHECKED',module='Rule30CyclicSubsetObstructionResearch',constants=48,
    headlines=3,kit_pin='5473ffd075f63c9d626e63b8455805d4831b39ca',
    checker_sha256='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905',
    main_conjecture_solved=False,files=selected)
p=ROOT/'REVIEW_MANIFEST.json';p.write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(files=len(selected),bytes=sum(x['bytes'] for x in selected),manifest_sha256=hashlib.sha256(p.read_bytes()).hexdigest())))
