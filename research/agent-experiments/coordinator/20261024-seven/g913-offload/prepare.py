"""Build a narrowly selected, hashed remote Lean payload; never copy user config."""
import hashlib,json,subprocess,sys,time,zipfile
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from core import HERE,BASE
from verification_context import PIN

ROOT=Path(__file__).resolve().parent
MODULES=['Rule30GoldenDFAResearch','Rule30GoldenEvenSupportResearch','Rule30GoldenBudgetResearch',
 'Rule30GoldenBudgetDFSResearch','Rule30GoldenPackedBitsResearch','Rule30GoldenPackedBudgetResearch',
 'Rule30GoldenCompactCodecResearch','Rule30GoldenCompactBudgetResearch','Rule30GoldenCompactSmokeResearch',
 'Rule30GoldenCompactLeafProbeResearch']

def digest(path):
    with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()

def main():
    start=time.monotonic();ref=BASE/'current-reference-3eca-20261024';lean=BASE/'toolchain/lean-4.35.0-windows'
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ref,text=True).strip()==PIN
    checker=subprocess.check_output(['git','show',PIN+':Check.lean'],cwd=ref)
    assert (ref/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    cache=ROOT/'_cache';cache.mkdir(exist_ok=True);bundle=cache/'kit.bundle'
    if not bundle.exists():subprocess.run(['git','bundle','create',str(bundle),'HEAD'],cwd=ref,check=True)
    subprocess.run(['git','bundle','verify',str(bundle)],cwd=ref,check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    pairs=[(bundle,'kit.bundle'),(ROOT/'worker.py','worker.py'),(ROOT/'README.md','README.md')]
    pairs += [(p,'toolchain/bin/'+p.name) for p in (lean/'bin').iterdir() if p.is_file()]
    for p in (lean/'lib/lean').rglob('*'):
        if p.is_file() and ('.olean' in p.name or p.suffix=='.ir' or p.name.endswith('.ir.sig')):
            pairs.append((p,'toolchain/lib/lean/'+p.relative_to(lean/'lib/lean').as_posix()))
    lib=ref/'lean/.lake/build/lib/lean'
    for p in lib.rglob('*'):
        if p.is_file() and ('.olean' in p.name or p.suffix=='.ir' or p.name.endswith('.ir.sig')):
            pairs.append((p,'compiled/'+p.relative_to(lib).as_posix()))
    for m in MODULES:pairs.append((HERE/(m+'.lean'),'sources/'+m+'.lean'))
    files={};archive=cache/'g913-lean-payload.zip'
    with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=1,allowZip64=True) as z:
        for src,name in pairs:
            assert src.is_file() and not src.is_symlink() and '..' not in Path(name).parts
            assert name not in files
            z.write(src,name);files[name]=digest(src)
        manifest={'kit_commit':PIN,'checker_sha256':hashlib.sha256(checker).hexdigest(),'lean_version':'4.35.0',
            'files':files,'modules':MODULES,'probe':'Rule30GoldenCompactLeafProbeResearch',
            'remote_guard':{'seconds':300,'rss_gib':16,'minimum_free_gib':16},'full_problem_solved':False}
        z.writestr('payload-manifest.json',json.dumps(manifest,indent=2)+'\n')
    record={'archive_sha256':digest(archive),'archive_bytes':archive.stat().st_size,'files':len(files),
        'kit_commit':PIN,'seconds':round(time.monotonic()-start,3)}
    (cache/'transfer-manifest.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(record,flush=True)

if __name__=='__main__':main()
