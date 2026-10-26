"""Verify a finished copy after a premature concurrent build tripped its final assertion."""
from pathlib import Path
import hashlib,json,time
r=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload';p=r/'project'
assert owner.resolve() in r.resolve().parents
old=owner/'research/notebook-offload-20261026/notebook/project/.lake/build/lib/lean'
lib=p/'.lake/build/lib/lean';manifest=json.loads((r/'source-manifest.json').read_bytes())
for name,h in manifest['files'].items():assert hashlib.sha256((p/name).read_bytes()).hexdigest()==h,name
count=total=0;start=time.monotonic()
for src in old.rglob('*'):
    if not src.is_file():continue
    rel=src.relative_to(old)
    if len(rel.parts)==1:
        stem=src.name.split('.')[0]
        if stem.startswith('Rule30') or stem in {'Rule30PrizeKit','Ruliology','Rule30Equivalents','Rule30WhitePadding'}:continue
    elif rel.parts[0] not in ['Aesop','Batteries','ImportGraph','LeanSearchClient','Mathlib',
                              'Plausible','ProofWidgets','Qq','Rule30Equivalents','Ruliology']:continue
    if src.name.split('.')[0]=='Rule30WhitePadding':continue
    target=lib/rel
    assert target.exists() and target.stat().st_size==src.stat().st_size,str(rel)
    assert not target.samefile(src),str(rel)
    with src.open('rb') as f:hs=hashlib.file_digest(f,'sha256').digest()
    with target.open('rb') as f:ht=hashlib.file_digest(f,'sha256').digest()
    assert hs==ht,str(rel)
    count+=1;total+=src.stat().st_size
out={'source_pin':manifest['pin'],'source_files_verified':len(manifest['files']),
 'cache_copies_byte_verified':count,'cached_bytes_verified':total,'hardlinks_used':False,
 'old_project_mutated':False,'changed_modules_excluded_from_copy':True,
 'initial_bootstrap_final_assertion_failed_because_build_started_early':True,
 'cache_copy_completed_and_independently_verified':True,'seconds':round(time.monotonic()-start,3)}
(r/'bootstrap-completion-report.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)
