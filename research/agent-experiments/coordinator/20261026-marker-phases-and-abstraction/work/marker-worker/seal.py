from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
manifest={p.relative_to(root).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
          for p in sorted(root.rglob('*')) if p.is_file() and p.name not in ['MANIFEST.json','VERIFIED.json'] and '__pycache__' not in p.parts}
(root/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
