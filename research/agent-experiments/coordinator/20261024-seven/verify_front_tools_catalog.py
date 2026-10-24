"""Normal Lake builds and unchanged full kernel replay for the catalog ports."""
import hashlib,importlib.util,json,subprocess
from core import HERE,BASE,REPO

def main():
    project=BASE/'front-tools-catalog-20261024';lake=BASE/'toolchain/lean-4.35.0-windows/bin/lake.exe'
    manifest=json.loads((HERE/'front-tools-catalog-manifest.json').read_text(encoding='utf-8'))
    pin=manifest['base_commit'];assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()==pin
    checker=subprocess.check_output(['git','show',pin+':Check.lean'],cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    out=HERE/'front-tools-catalog-evidence';out.mkdir(exist_ok=True);reports=[]
    for entry in manifest['entries']:
        mod=entry['module'];stem=mod.split('.')[-1];source=project/entry['source'];raw=source.read_bytes()
        assert hashlib.sha256(raw).hexdigest()==entry['source_sha256']
        print({'stage':'normal_lake_build','module':stem},flush=True)
        build=guard.guarded([str(lake),'build',mod],project,out/(stem+'.build.log'))
        argv=[str(lake),'env','lean','--run','Check.lean',mod,'--claim','partial']
        for h in entry['headlines']:argv+=['--headline',mod+'.'+h]
        print({'stage':'kernel_replay','module':stem,'build_seconds':build},flush=True)
        replay=guard.guarded(argv,project,out/(stem+'.check.log'))
        checked=json.loads([s for s in (out/(stem+'.check.log')).read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
        assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
        assert all(h['ok'] for h in checked['headlines']) and source.read_bytes()==raw
        assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
        report={'module':mod,'source_sha256':entry['source_sha256'],'base_commit':pin,
                'checker_unchanged':True,'checker_sha256':hashlib.sha256(checker).hexdigest(),
                'normal_build_seconds':build,'replay_seconds':replay,'check':checked,'full_problem_solved':False}
        (out/(stem+'.json')).write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n');reports.append(report)
        print({'module':stem,'stage':'pass','constants':checked['replay']['constants']},flush=True)
    result={'verdict':'pass','modules':len(reports),'replayed_declarations':sum(r['check']['replay']['constants'] for r in reports),
            'base_commit':pin,'checker_unchanged':True,'full_problem_solved':False,'Q01_proved':False}
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(result,flush=True)

if __name__=='__main__':main()
