"""Guarded kernel checks of the parallel return-map endpoints."""
import argparse,hashlib,importlib.util,json,shutil,subprocess
from core import HERE,BASE,REPO
from verification_context import add_reference_options,reference,unchanged,identity

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--all',action='store_true');parser.add_argument('--resume',action='store_true')
    add_reference_options(parser)
    args=parser.parse_args();src=HERE/'front-jump';out=src/'evidence';out.mkdir(exist_ok=True)
    project,lake,checker=reference(args)
    pin='3eca23c0a9fa6b153313655e6d51835406c2d06e'
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()==pin
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    parent=json.loads((HERE/'front-lanes-evidence/report.json').read_text(encoding='utf-8'))
    assert parent['check']['verdict']=='pass' and parent['check']['replay']['ok']
    assert hashlib.sha256((project/'Rule30FrontLanesResearch.lean').read_bytes()).hexdigest()==parent['source_sha256']
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    data=json.loads((src/'generation.json').read_text(encoding='utf-8'));reports=[]
    entries=data['entries'] if args.all else data['entries'][:2]
    for entry in entries:
        module=entry['module'];source=src/(module+'.lean');raw=source.read_bytes();sha=hashlib.sha256(raw).hexdigest()
        assert sha==data['source_hashes'][source.name]
        target=project/source.name;obj=project/'.lake/build/lib/lean'/(module+'.olean');rfile=out/(module+'.json')
        if args.resume and rfile.exists():
            old=json.loads(rfile.read_text(encoding='utf-8'))
            assert old['source_sha256']==sha and old['check']['verdict']=='pass' and old['check']['replay']['ok']
            assert not old['check']['newAxioms'] and target.read_bytes()==raw and obj.exists()
            assert old['kit_commit']==pin and all(h['ok'] for h in old['check']['headlines'])
            reports.append(old);print({'module':module,'stage':'retained_exact_pass'},flush=True);continue
        if target.exists() and target.read_bytes()!=raw:raise RuntimeError('Different owned source exists')
        shutil.copyfile(source,target)
        print({'module':module,'stage':'compile'},flush=True)
        build=guard.guarded([str(lake),'env','lean','-o',str(obj),str(target)],project,out/(module+'.build.log'))
        argv=[str(lake),'env','lean','--run','Check.lean',module,'--claim','partial']
        for h in entry['heads']:argv+=['--headline','Rule30FrontJumpResearch.'+h]
        print({'module':module,'stage':'replay','build_seconds':build},flush=True)
        log=out/(module+'.check.log');replay=guard.guarded(argv,project,log)
        checked=json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
        assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
        assert all(h['ok'] for h in checked['headlines']) and target.read_bytes()==raw
        assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
        result={'module':module,'source_sha256':sha,'kit_commit':pin,'checker_unchanged':True,
                'build_seconds':build,'replay_seconds':replay,'check':checked,'full_problem_solved':False}
        unchanged(project,checker);result.update(identity(checker))
        rfile.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n');reports.append(result)
        print({'module':module,'stage':'pass','constants':checked['replay']['constants']},flush=True)
    summary={'verdict':'pass','all_requested_modules':len(entries),'all_generated_modules':len(data['entries']),
             'full_execution_certified':args.all,'full_problem_solved':False}
    unchanged(project,checker);summary.update(identity(checker))
    (out/('report.json' if args.all else 'pilot.json')).write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(summary,flush=True)

if __name__=='__main__':main()
