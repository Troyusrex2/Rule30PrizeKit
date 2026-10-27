"""Compile all19 sources into an empty library and replay the entire research leaf.

No installation, network access, SSH, or prior contribution objects are used.
Run with pinned Lean4.35 under lake env, or supply an existing Lean executable.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,shutil,subprocess
ROOT=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--lean',default=shutil.which('lean'))
    parser.add_argument('--library-path',action='append',default=[])
    args=parser.parse_args()
    if not args.lean:raise SystemExit('Pinned Lean4.35 is required; no installation is attempted.')
    meta=json.loads((ROOT/'INPUTS.json').read_text())
    for rel,digest in meta['files'].items():assert sha(ROOT/rel)==digest,rel
    assert sha(ROOT/'Check.lean')=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    work=ROOT/'.verification-build'/stamp;lib=work/'lib';lib.mkdir(parents=True,exist_ok=False)
    out=ROOT/'verification-output'/stamp;out.mkdir(parents=True,exist_ok=False)
    inherited=[s for s in os.environ.get('LEAN_PATH','').split(os.pathsep) if s]
    external=args.library_path or inherited
    env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(lib),*external]),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
    def run(label,command):
        log=out/(label+'.log')
        with log.open('wb') as f:
            subprocess.run(command,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=300)
        return log.read_text(encoding='utf-8')
    version=run('lean-version',[args.lean,'--version'])
    assert 'version 4.35.0,' in version,version
    imported=[]
    for name in meta['required_mathlib_modules']:
        rel=Path(*name.split('.')).with_suffix('.olean')
        p=next((Path(base)/rel for base in external if (Path(base)/rel).exists()),None)
        if p is None:raise SystemExit('An already prepared pinned dependency is required: '+name)
        imported.append({'module':name,'relative_object':rel.as_posix(),'sha256':sha(p)})
    for name in meta['build_order']:
        target=lib/Path(*name.split('.')).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
        build=run(name+'.build',[args.lean,'-o',str(target),meta['module_paths'][name]])
        assert 'warning:' not in build.lower(),name
    results=[]
    for name in meta['research_modules']:
        command=[args.lean,'--run','Check.lean',name,'--claim','partial']
        for head in meta['headlines'][name]:command+=['--headline',head]
        text=run(name+'.check',command)
        c=json.loads(next(l for l in reversed(text.splitlines()) if l.startswith('{')))
        assert c['verdict']=='pass' and c['replay']=={'constants':meta['expected_constants'][name],'ok':True}
        assert not c['newAxioms'] and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
        assert [h['name'] for h in c['headlines']]==meta['headlines'][name]
        types=run(name+'.types',[args.lean,'Types/'+name+'.lean'])
        expected=(ROOT/'Types'/(name+'.expected.log')).read_text(encoding='utf-8')
        assert re.sub(r'\s+','',types)==re.sub(r'\s+','',expected),name
        results.append({'module':name,'constants':c['replay']['constants'],'headlines':len(c['headlines']),
            'source_sha256':sha(ROOT/meta['module_paths'][name]),'full_replay':True,'types_match_author_receipt':True})
    for rel,digest in meta['files'].items():assert sha(ROOT/rel)==digest,rel
    executable=Path(args.lean) if Path(args.lean).exists() else Path(shutil.which(args.lean))
    receipt={'passed':True,'official_pin':meta['official_pin'],'mathlib_pin':meta['mathlib_pin'],
      'fresh_sources':len(meta['build_order']),'fresh_Ruliology_sources':18,'fresh_research_sources':1,
      'research_results':results,'total_research_constants':94,'total_headlines':9,'source_warnings':0,
      'new_axioms':[],'checker_sha256':sha(ROOT/'Check.lean'),'lean_version':version.strip(),
      'lean_executable_sha256':sha(executable),'reused_mathlib_entry_hashes':imported,
      'cached_contribution_objects_used':False,
      'validation_kind':'Fresh19-source standalone Lean build and complete new-leaf replay; existing pinned toolchain only, not a toolchain rebuild.'}
    (out/'RESULT.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'passed':True,'fresh_sources':len(meta['build_order']),'research_constants':94,
        'headlines':9,'receipt_directory':out.relative_to(ROOT).as_posix()}))

if __name__=='__main__':main()
