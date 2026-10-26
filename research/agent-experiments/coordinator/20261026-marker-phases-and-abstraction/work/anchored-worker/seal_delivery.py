from pathlib import Path
import hashlib,json,shutil
root=Path(__file__).resolve().parent;out=root/'delivery-v01'
assert not out.exists();out.mkdir()
assert hashlib.sha256((root/'AnchoredDefectAbstraction.lean').read_bytes()).hexdigest()=='b3668ec09138e22bb3f0139ecc711833750c19882ea51bbfbdb6bdd7edc08bdf'
assert hashlib.sha256((root/'input-mixed-strip.json').read_bytes()).hexdigest()=='ffac62754060e677233413fb617df244282b68e2d7b4984ffa056111fb9d6839'
names=['AnchoredDefectAbstraction.lean','AnchoredDefect.template.lean','dependencies.json','REPORT.md','guard.py','replay.py','prepare.py','abstract_closure.py','abstract-closure.json','generate_source.py','input-mixed-strip.json','seal_delivery.py']
names += [m+'.lean' for m in json.loads((root/'dependencies.json').read_bytes())]
for name in names:shutil.copy2(root/name,out/name)
for name in ['formal','evidence']:shutil.copytree(root/name,out/name)
entries={str(p.relative_to(out)).replace('\\','/'):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.rglob('*')) if p.is_file()}
(out/'SHA256SUMS.json').write_text(json.dumps(entries,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'files':len(entries),'manifest_sha256':hashlib.sha256((out/'SHA256SUMS.json').read_bytes()).hexdigest()}))
