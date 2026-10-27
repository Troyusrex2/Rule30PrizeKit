from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
files={str(p.relative_to(root)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in sorted(root.rglob('*')) if p.is_file() and p.name!='MANIFEST.json'}
(root/'MANIFEST.json').write_text(json.dumps(files,indent=2)+'\n')
print(json.dumps({'files':len(files),'manifest':hashlib.sha256((root/'MANIFEST.json').read_bytes()).hexdigest()}))
