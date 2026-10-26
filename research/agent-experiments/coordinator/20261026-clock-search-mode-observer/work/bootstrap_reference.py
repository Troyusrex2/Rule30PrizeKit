"""Create an isolated new-pin source project, copying caches without hardlinks."""
from pathlib import Path
import zipfile,json,hashlib,shutil,os,time
r=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload'
assert owner.resolve() in r.resolve().parents
p=r/'project';assert not p.exists(), 'Never overwrite an existing project'
manifest=json.loads((r/'source-manifest.json').read_bytes())
assert hashlib.sha256((r/'kit-source.zip').read_bytes()).hexdigest()==manifest['zip_sha256']
p.mkdir()
with zipfile.ZipFile(r/'kit-source.zip') as z:
    for name in manifest['files']:
        target=(p/name).resolve();assert p.resolve() in target.parents
        target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(z.read(name))
for name,h in manifest['files'].items():assert hashlib.sha256((p/name).read_bytes()).hexdigest()==h,name
old=owner/'research/notebook-offload-20261026/notebook/project/.lake/build/lib/lean'
lib=p/'.lake/build/lib/lean';lib.mkdir(parents=True)
copied=total=0
# These roots changed, and must be rebuilt. WhitePadding's proof also changed.
excluded={'Rule30PrizeKit','Ruliology','Rule30Equivalents','Rule30WhitePadding'}
start=time.monotonic()
for src in old.rglob('*'):
    if not src.is_file():continue
    rel=src.relative_to(old)
    if len(rel.parts)==1:
        stem=src.name.split('.')[0]
        if stem.startswith('Rule30') or stem in excluded:continue
    elif rel.parts[0] not in ['Aesop','Batteries','ImportGraph','LeanSearchClient','Mathlib',
                              'Plausible','ProofWidgets','Qq','Rule30Equivalents','Ruliology']:continue
    if src.name.split('.')[0] in ['Rule30WhitePadding']:continue
    target=lib/rel;target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(src,target);copied+=1;total+=src.stat().st_size
assert not (lib/'Ruliology/CellularAutomata/Rule30WhitePadding.olean').exists()
assert not (lib/'Rule30PrizeKit.olean').exists()
out={'source_pin':manifest['pin'],'source_files_verified':len(manifest['files']),
     'cached_files_copied':copied,'cached_bytes_copied':total,'hardlinks_used':False,
     'changed_modules_excluded':True,'old_project_mutated':False,'seconds':round(time.monotonic()-start,3)}
(r/'bootstrap-report.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)
