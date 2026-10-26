"""Create one immutable selected evidence snapshot; refuse replacement."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import shutil

root = Path(__file__).resolve().parent
dest = root / 'frozen'
assert not dest.exists(), 'Never overwrite a frozen snapshot'
dest.mkdir()
for name in ('probe.py', 'certificate.json', 'audit.py', 'audit.json', 'REPORT.md', 'freeze.py'):
    shutil.copy2(root / name, dest / name)
jobs = root.parents[1] / 'coordination/jobs'
(dest / 'evidence').mkdir()
for stem in ('global-support-common-subset-502f0ee0', 'global-support-independent-audit-1817e863'):
    for extension in ('.json', '.log'):
        shutil.copy2(jobs / (stem + extension), dest / 'evidence' / (stem + extension))
files = []
for p in sorted(dest.rglob('*')):
    if p.is_file():
        files.append({'path': p.relative_to(dest).as_posix(), 'bytes': p.stat().st_size,
                      'sha256': hashlib.sha256(p.read_bytes()).hexdigest()})
manifest = {'status': 'Frozen exact one-step global finite-support counterexamples; no all-time claim',
            'created_utc': datetime.now(timezone.utc).isoformat(), 'files': files}
(dest / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8')
for f in files:
    assert hashlib.sha256((dest / f['path']).read_bytes()).hexdigest() == f['sha256']
print(json.dumps({'path': str(dest / 'manifest.json'), 'files': len(files),
                  'bytes': sum(f['bytes'] for f in files),
                  'sha256': hashlib.sha256((dest / 'manifest.json').read_bytes()).hexdigest()}))
