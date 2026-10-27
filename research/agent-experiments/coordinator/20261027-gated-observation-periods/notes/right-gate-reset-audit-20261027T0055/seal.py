from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
p=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
refs=[p.parent/'forward-reset-onset-20261027T0045/PAPER.md',p.parent/'forward-reset-onset-20261027T0045/Rule30ForwardResetResearch.lean',p.parent/'gate-coefficient-audit-20261027T0020/PAPER.md',p.parent/'global-temporal-marker-20261027T0030/PAPER.md',p.parent/'gate-return-source-audit-20261027T0020/REPORT.md',p.parent/'gated-observation-reset-formal-20261027T0100/Rule30GatedObservationResetResearch.lean']
(p/'SOURCE-REFERENCES.json').write_text(json.dumps([{'path':str(f),'sha256':sha(f)} for f in refs],indent=2)+'\n',encoding='utf-8')
files=[{'path':str(f.relative_to(p)).replace('\\','/'),'bytes':f.stat().st_size,'sha256':sha(f)} for f in sorted(p.rglob('*')) if f.is_file() and '__pycache__' not in f.parts and f.name!='MANIFEST.json']
raw=(json.dumps({'sealed_utc':datetime.now(timezone.utc).isoformat(),'files':files},indent=2)+'\n').encode()
with (p/'MANIFEST.json').open('xb') as f:f.write(raw)
assert all(sha(p/x['path'])==x['sha256'] for x in files)
print(json.dumps({'phase':p.name,'files':len(files),'manifest_sha256':hashlib.sha256(raw).hexdigest(),'paper_sha256':sha(p/'PAPER.md')}))
