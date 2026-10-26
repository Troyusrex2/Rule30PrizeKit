"""Select source-only review evidence and verify frozen/replayed source hashes."""
from pathlib import Path
import datetime,hashlib,json
ROOT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
frozen=json.loads((ROOT/'source-manifest.json').read_bytes())
for name,item in frozen['files'].items():
    p=ROOT/'published'/name
    assert sha(p)==item['sha256'] and p.stat().st_size==item['bytes']
report=json.loads((ROOT/'reproduction/report.json').read_bytes())
assert report['passed'] and report['all_custom_constants']==388 and len(report['modules'])==9
for module in report['modules']:
    name=module['module']+'.lean'
    source=next(p for p in [ROOT/'published/work'/name,ROOT/'published/work/dependencies'/name] if p.exists())
    assert sha(source)==module['source_sha256']
assert json.loads((ROOT/'graph-audit.json').read_bytes())['passed']
guard=ROOT/'guard-evidence';guard.mkdir(exist_ok=True)
for p in (ROOT.parent.parent/'coordination/jobs').glob('verifier-clock-*'):
    if p.is_file():(guard/p.name).write_bytes(p.read_bytes())
selected={p for p in (ROOT/'published').rglob('*') if p.is_file()}
selected.update(p for p in (ROOT/'guard-evidence').rglob('*') if p.is_file())
selected.update(p for p in (ROOT/'audit-attempts').rglob('*') if p.is_file())
selected.update(p for p in (ROOT/'reproduction/logs').rglob('*') if p.is_file())
selected.update(p for p in (ROOT/'reproduction').glob('*.json'))
selected.update(ROOT/name for name in ['freeze_sources.py','source-manifest.json','replay_review.py','audit_graph.py','graph-audit.json','REVIEW.md','select_review.py'])
files={p.relative_to(ROOT).as_posix():dict(sha256=sha(p),bytes=p.stat().st_size) for p in sorted(selected)}
manifest=dict(created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    status='PARTIAL_KERNEL_CHECKED',review='Independent source/hypothesis audit and full unchanged-checker replay passed',
    published_commit=frozen['commit'],kit_pin=report['kit_pin'],checker_sha256=report['checker_sha256'],
    modules=report['modules'],all_custom_constants=388,files=files,total_bytes=sum(v['bytes'] for v in files.values()),
    scope='Even source half-clock cannot be hidden in the OR across two newer cells, nor eventually in the next fixed-depth column. No physical-center, prize, or safety-completeness claim.',
    preserved_failure='First literal audit overrequired odd-R next-column periodicity; corrected without changing published source.',
    excludes='No compiled libraries, source archives, caches, or private kit copy selected.')
(ROOT/'REVIEW_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(files=len(files),total_bytes=manifest['total_bytes'],manifest_sha256=sha(ROOT/'REVIEW_MANIFEST.json'),custom_constants=388),indent=2))
