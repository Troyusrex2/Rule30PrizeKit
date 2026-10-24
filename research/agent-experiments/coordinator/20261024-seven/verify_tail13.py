"""Build/replay each independent certificate module under owned-job guards."""
import argparse,concurrent.futures,hashlib,importlib.util,json,shutil,subprocess,time
from pathlib import Path
from core import HERE,BASE,REPO

PIN='3eca23c0a9fa6b153313655e6d51835406c2d06e'

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--resume',action='store_true')
    parser.add_argument('--project',type=Path,default=BASE/'current-reference-3eca-20261024')
    parser.add_argument('--lake',type=Path,default=BASE/'toolchain/lean-4.35.0-windows/bin/lake.exe')
    parser.add_argument('--workers',type=int,default=2,choices=[1,2])
    args=parser.parse_args();project=args.project.resolve();lake=args.lake.resolve()
    src=HERE/'tail13-completion';out=src/'evidence';out.mkdir(exist_ok=True)
    data=json.loads((src/'generation.json').read_text(encoding='utf-8'))
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()==PIN
    checker=subprocess.check_output(['git','show','HEAD:Check.lean'],cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    dep=guard.guarded([str(lake),'build','Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFour'],project,out/'dependencies.log')
    started=time.monotonic()
    def verify(module):
        source=src/(module+'.lean');raw=source.read_bytes();sha=hashlib.sha256(raw).hexdigest()
        assert sha==data['source_hashes'][source.name]
        target=project/source.name;artifact=project/'.lake/build/lib/lean'/(module+'.olean')
        reportfile=out/(module+'.json')
        if args.resume and reportfile.exists():
            old=json.loads(reportfile.read_text(encoding='utf-8'))
            assert old['kit_commit']==PIN and old['source_sha256']==sha
            assert old['checker_sha256']==hashlib.sha256(checker).hexdigest()
            assert old['check']['verdict']=='pass' and old['check']['replay']['ok']
            assert not old['check']['newAxioms'] and all(h['ok'] for h in old['check']['headlines'])
            assert target.read_bytes()==raw and artifact.exists()
            print({'module':module,'stage':'retained_exact_pass'},flush=True);return old
        if target.exists() and target.read_bytes()!=raw:raise RuntimeError('Different owned module: '+str(target))
        shutil.copyfile(source,target)
        print({'module':module,'stage':'compile'},flush=True)
        build=guard.guarded([str(lake),'env','lean','-o',str(artifact),str(target)],project,out/(module+'.build.log'))
        heads=['complete_path','cycle13_complete','row4_13_all_odd','stripe_four_tail_complete'] if module=='Rule30Tail13Complete' else ['path_chunk_'+module[-2:]]
        argv=[str(lake),'env','lean','--run','Check.lean',module,'--claim','partial']
        for head in heads:argv+=['--headline','Ruliology.CellularAutomata.Rule30Tail13Completion.'+head]
        print({'module':module,'stage':'full_kernel_replay','build_seconds':build},flush=True)
        log=out/(module+'.check.log');replay=guard.guarded(argv,project,log)
        checked=json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
        assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
        assert all(h['ok'] for h in checked['headlines']) and len(checked['headlines'])==len(heads)
        assert target.read_bytes()==raw
        report={'module':module,'kit_commit':PIN,'source_sha256':sha,'checker_unchanged':True,
                'checker_sha256':hashlib.sha256(checker).hexdigest(),'build_seconds':build,
                'replay_seconds':replay,'check':checked,'full_problem_solved':False}
        reportfile.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
        print({'module':module,'stage':'pass','constants':checked['replay']['constants']},flush=True)
        return report
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        reports=list(pool.map(verify,data['modules'][:-1]))
    root=verify(data['modules'][-1]);reports.append(root)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    result={'verdict':'pass','kit_commit':PIN,'checker_unchanged':True,'all_modules':len(reports),
            'all_replayed_declarations':sum(r['check']['replay']['constants'] for r in reports),
            'dependency_seconds':dep,'total_seconds':round(time.monotonic()-started,3),
            'modules':[{'module':r['module'],'source_sha256':r['source_sha256'],
                        'constants':r['check']['replay']['constants']} for r in reports],
            'full_problem_solved':False,'Q01_proved':False}
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(result,flush=True)

if __name__=='__main__':main()
