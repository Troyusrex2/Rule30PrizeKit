"""Reproduce the core Lake build and all 18 unchanged-checker headlines.

Requires Python3 and Lake/Lean4.35 on PATH. No SSH, private libraries, Mathlib,
package installation or network service is used by this script.
"""
from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess

ROOT=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    summary=json.loads((ROOT/'SUMMARY.json').read_bytes())
    manifest=json.loads((ROOT/'MANIFEST.json').read_bytes())
    for item in manifest['files']:
        path=(ROOT/item['path']).resolve()
        assert path.is_relative_to(ROOT),item['path']
        assert path.stat().st_size==item['bytes'] and sha(path)==item['sha256'],item['path']
    assert sha(ROOT/'Check.lean')==summary['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    heads=json.loads((ROOT/'headlines.json').read_bytes())
    assert heads==summary['headlines'] and len(heads)==18
    lake=shutil.which('lake')
    if not lake:raise SystemExit('Lake is required on PATH; this script does not install it.')
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    out=ROOT/'verification-output'/stamp;out.mkdir(parents=True,exist_ok=False)
    fresh=not (ROOT/'.lake/build').exists()
    env=dict(os.environ,LEAN_PATH='',LEAN_NUM_THREADS='1')
    def run(label,args):
        with (out/(label+'.log')).open('wb') as stream:
            subprocess.run(args,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT,check=True)
        return (out/(label+'.log')).read_text(encoding='utf-8')
    version=run('lean-version',[lake,'--no-cache','env','lean','--version'])
    assert 'version 4.35.0,' in version,version
    build=run('lake-build',[lake,'--no-cache','build',summary['module']])
    assert 'warning:' not in build.lower()
    command=[lake,'--no-cache','env','lean','--run','Check.lean',summary['module'],'--claim','partial']
    for head in heads:command+=['--headline',head]
    text=run('full-check',command)
    result=json.loads(next(line for line in reversed(text.splitlines()) if line.startswith('{')))
    assert result['verdict']=='pass' and result['replay']=={'constants':106,'ok':True}
    assert not result['newAxioms']
    assert [h['name'] for h in result['headlines']]==heads
    assert all(h['ok'] and h['typeMatches'] for h in result['headlines'])
    types=run('headline-types',[lake,'--no-cache','env','lean','Types.lean'])
    expected=(ROOT/'Types.expected.log').read_text(encoding='utf-8')
    assert re.sub(r'\s+','',types)==re.sub(r'\s+','',expected)
    for item in manifest['files']:assert sha(ROOT/item['path'])==item['sha256']
    receipt={'passed':True,'module_constants':106,'headline_types':18,'types_match_expected':True,'source_warnings':0,'new_axioms':[],'project_build_directory_absent_at_start':fresh,'checker_sha256':sha(ROOT/'Check.lean'),'module_source_sha256':summary['source_sha256']}
    (out/'result.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(receipt,indent=2))
    print('Evidence:',out)

if __name__=='__main__':main()
