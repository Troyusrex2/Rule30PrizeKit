"""Reproduce the exact core-Lean catalog build and unchanged full checks.

Requires Python 3.9+ and the pinned Lake/Lean on PATH. Installs nothing.
"""
from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess

ROOT=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    summary=json.loads((ROOT/'SUMMARY.json').read_bytes())
    manifest=json.loads((ROOT/'MANIFEST.json').read_bytes())['files']
    for rel,expected in manifest.items():
        path=(ROOT/rel).resolve()
        assert path.is_relative_to(ROOT),rel
        assert sha(path)==expected,rel
    assert sha(ROOT/'Check.lean')==summary['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    lake=shutil.which('lake')
    if not lake:raise SystemExit('Lake must be available on PATH; no installation is performed.')
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    out=ROOT/'verification-output'/stamp;out.mkdir(parents=True,exist_ok=False)
    fresh=not (ROOT/'.lake/build').exists()
    env=dict(os.environ,LEAN_PATH='',LEAN_NUM_THREADS='1')
    def run(label,args):
        with (out/(label+'.log')).open('wb') as f:
            subprocess.run(args,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,check=True)
        return (out/(label+'.log')).read_text(encoding='utf-8')
    version=run('lean-version',[lake,'--no-cache','env','lean','--version'])
    assert 'version 4.35.0,' in version,version
    build=run('lake-build',[lake,'--no-cache','build',*[m['module'] for m in summary['new_modules']]])
    assert 'warning:' not in build.lower()
    results=[]
    for module in summary['new_modules']:
        name=module['module'];tag=name.rsplit('.',1)[-1]
        command=[lake,'--no-cache','env','lean','--run','Check.lean',name,'--claim','partial']
        for head in module['headlines']:command+=['--headline',head]
        text=run(tag+'-full-check',command)
        checked=json.loads(next(line for line in reversed(text.splitlines()) if line.startswith('{')))
        assert checked['verdict']=='pass' and checked['replay']['ok']
        assert checked['replay']['constants']==module['constants']
        assert not checked['newAxioms']
        assert [h['name'] for h in checked['headlines']]==module['headlines']
        assert all(h['ok'] and h['typeMatches'] for h in checked['headlines'])
        results.append({'module':name,'constants':checked['replay']['constants'],'headlines':len(checked['headlines'])})
    types=run('headline-types',[lake,'--no-cache','env','lean','Types.lean'])
    assert re.sub(r'\s+','',types)==re.sub(r'\s+','',(ROOT/'Types.expected.log').read_text(encoding='utf-8'))
    for rel,expected in manifest.items():assert sha(ROOT/rel)==expected,rel
    result={'passed':True,'modules':results,'all_types_match_expected':True,'fresh_build_directory_at_start':fresh,'checker_sha256':sha(ROOT/'Check.lean'),'new_axioms':[],'source_warnings':0}
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2));print('Evidence:',out)

if __name__=='__main__':main()
