"""Freshly compile the exact research closure and fully kernel-replay each module.

Supply Lean4.35.0, the unchanged official checker, and an already built official
library. No private compiled object is loaded or copied. The output must be new.
Stored receipts are provenance only; all reported counts come from this run.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,time
ROOT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(c,msg):
    if not c:raise RuntimeError(msg)
def verify():
    manifest=json.loads((ROOT/'MANIFEST.json').read_bytes())
    for d in manifest['files']:
        rel=Path(d['path']);p=(ROOT/rel).resolve()
        require(not rel.is_absolute() and '..' not in rel.parts and p.is_relative_to(ROOT),'Unsafe path')
        require(p.is_file() and sha(p)==d['sha256'],'Bundle hash mismatch: '+str(rel))
    summary=json.loads((ROOT/'summary.json').read_bytes())
    require(summary['reference_pin']=='5473ffd075f63c9d626e63b8455805d4831b39ca','Unexpected reference')
    require(summary['current_compatible_pin']=='7d665044b904117af9e82328aeb90a30692b2b85','Unexpected current pin')
    require(summary['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905','Unexpected checker')
    require(summary['build_order']==json.loads((ROOT/'build-order.json').read_bytes()),'Build order mismatch')
    official={m['module'] for m in summary['official_modules']};seen=set()
    for m in summary['modules']:
        n=m['module'];require(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',n),'Invalid module name')
        require(n not in seen and set(m['research_imports'])<=seen,'Dependency order error')
        require(set(m['official_imports'])<=official,'Unexpected official import')
        f=ROOT/'sources'/(n+'.lean');require(sha(f)==m['source_sha256'],'Source mismatch')
        imports=re.findall(r'^(?:public )?import (\S+)',f.read_text(encoding='utf-8'),re.M)
        require(set(imports)==set(m['research_imports']+m['official_imports']),'Import manifest mismatch')
        old=json.loads((ROOT/'prior-receipts'/(n+'.json')).read_bytes())
        require(old['passed'] and old['source_sha256']==m['source_sha256'],'Prior source receipt mismatch')
        require(old['checker']['verdict']=='pass' and not old['checker']['newAxioms'],'Prior checker receipt mismatch')
        require([h['name'] for h in old['checker']['headlines']]==m['headlines'],'Headline manifest mismatch')
        seen.add(n)
    require([m['module'] for m in summary['modules']]==summary['build_order'],'Module order mismatch')
    for m in summary['official_modules']:
        require(sha(ROOT/m['source_path'])==m['source_sha256'],'Official source snapshot mismatch')
    return summary
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--verify-only',action='store_true')
    for n in ['lean','official-lib','checker','output']:ap.add_argument('--'+n,type=Path)
    a=ap.parse_args();s=verify()
    if a.verify_only:
        print(json.dumps({'verified':True,'research_sources':len(s['modules']),'official_source_references':len(s['official_modules']),'lean_invoked':False}));return
    require(all([a.lean,a.official_lib,a.checker,a.output]),'All replay paths are required')
    lean=a.lean.resolve();checker=a.checker.resolve();official=a.official_lib.resolve();out=a.output.resolve()
    require(lean.is_file() and checker.is_file() and official.is_dir(),'Missing tool or official library')
    require(sha(checker)==s['checker_sha256'],'Checker hash mismatch')
    version=subprocess.check_output([str(lean),'--version'],text=True,timeout=30).strip()
    require(re.search(r'\bversion 4\.35\.0\b',version),'Lean version mismatch')
    for protected in [ROOT,official,checker.parent,lean.parent]:require(not out.is_relative_to(protected),'Unsafe output location')
    refs={}
    for m in s['official_modules']:
        f=official/(m['module'].replace('.','/')+'.olean');require(f.is_file(),'Missing official object: '+m['module'])
        refs[m['module']]={'path':str(f),'sha256':sha(f)}
    out.mkdir(parents=True,exist_ok=False);lib=out/'lib';lib.mkdir()
    (out/'reference-objects.json').write_text(json.dumps(refs,indent=2)+'\n',encoding='utf-8')
    env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(lib),str(official)]),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
    results=[]
    for m in s['modules']:
        n=m['module'];source=ROOT/'sources'/(n+'.lean');require(sha(source)==m['source_sha256'],'Source changed')
        raw=source.read_bytes();require(not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',raw,re.M),'Unsafe proof token')
        local=out/source.name;shutil.copyfile(source,local)
        commands=[[str(lean),'-o',str(lib/(n+'.olean')),str(local)],[str(lean),'--run',str(checker),n,'--claim','partial']]
        for h in m['headlines']:commands[1]+=['--headline',h]
        start=time.monotonic()
        for cmd,suffix in zip(commands,['build','check']):
            with (out/(n+'.'+suffix+'.log')).open('wb') as stream:
                subprocess.run(cmd,cwd=out,env=env,stdout=stream,stderr=subprocess.STDOUT,check=True,timeout=300)
        lines=(out/(n+'.check.log')).read_text(encoding='utf-8').splitlines()
        c=json.loads(next(x for x in reversed(lines) if x.startswith('{')))
        require(c['module']==n and c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms'],'Checker failed')
        require([h['name'] for h in c['headlines']]==m['headlines'],'Headline names changed')
        require(all(h['ok'] and h['typeMatches'] for h in c['headlines']),'Headline failed')
        r={'module':n,'source_sha256':sha(source),'compiled_sha256':sha(lib/(n+'.olean')),'checker':c,'seconds':time.monotonic()-start,'build_warning_count':(out/(n+'.build.log')).read_text(encoding='utf-8').count('warning:')}
        results.append(r)
        (out/'progress.json').write_text(json.dumps({'completed':results},indent=2)+'\n',encoding='utf-8')
        print(json.dumps({'module':n,'passed':True,'constants':c['replay']['constants']}),flush=True)
    for d in refs.values():require(sha(Path(d['path']))==d['sha256'],'Official object changed')
    require(sha(checker)==s['checker_sha256'],'Checker changed');verify()
    totals={'research_modules':len(results),'module_owned_constants':sum(r['checker']['replay']['constants'] for r in results),'noninternal_declarations':sum(len(r['checker']['declared']) for r in results),'accepted_headlines':sum(len(r['checker']['headlines']) for r in results),'build_warnings':sum(r['build_warning_count'] for r in results)}
    receipt={'passed':True,'lean_version':version,'compiled_reference_pin':s['reference_pin'],'current_source_compatible_pin':s['current_compatible_pin'],'checker_sha256':s['checker_sha256'],'fresh_research_objects_only':True,'official_library_reused':True,'new_axioms':[],'prize_solved':False,'totals':totals,'results':results}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'passed':True,**totals,'prize_solved':False}))
if __name__=='__main__':main()
