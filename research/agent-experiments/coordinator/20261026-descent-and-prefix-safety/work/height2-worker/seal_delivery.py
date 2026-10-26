from pathlib import Path
import hashlib,json,shutil
root=Path(__file__).resolve().parent
out=root/'delivery-v01'
assert not out.exists()
out.mkdir()
names=['HeightTwoNearReturn.lean','HeightTwoDescent.lean','dependencies.json','REPORT.md','guard.py','replay.py','prepare_sources.py','generate_certificate.py','certificate-controls.json','seal_delivery.py']
names += [m+'.lean' for m in json.loads((root/'dependencies.json').read_bytes())]
for name in names: shutil.copy2(root/name,out/name)
for name in ['formal','evidence']:shutil.copytree(root/name,out/name)
entries={str(p.relative_to(out)).replace('\\','/'):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.rglob('*')) if p.is_file()}
(out/'SHA256SUMS.json').write_text(json.dumps(entries,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'files':len(entries),'manifest_sha256':hashlib.sha256((out/'SHA256SUMS.json').read_bytes()).hexdigest()}))
