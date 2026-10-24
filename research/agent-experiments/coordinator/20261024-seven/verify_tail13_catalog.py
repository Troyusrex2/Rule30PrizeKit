"""Fresh compile and full kernel replay of every catalog-format module."""
import argparse,concurrent.futures,hashlib,importlib.util,json,subprocess,time
from core import HERE,BASE,REPO

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--resume',action='store_true');args=parser.parse_args()
    project=BASE/'stripe13-completion-catalog';lake=BASE/'toolchain/lean-4.35.0-windows/bin/lake.exe'
    data=json.loads((HERE/'catalog-tail13-manifest.json').read_text(encoding='utf-8'))
    pin=data['kit_commit'];assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()==pin
    checker=subprocess.check_output(['git','show','HEAD:Check.lean'],cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    out=HERE/'tail13-catalog-evidence';out.mkdir(exist_ok=True);start=time.monotonic()
    def verify(entry):
        module=entry['module'];stem=module.split('.')[-1];source=project/entry['source']
        raw=source.read_bytes();sha=hashlib.sha256(raw).hexdigest();assert sha==entry['source_sha256']
        artifact=project/'lean/.lake/build/lib/lean'/('/'.join(module.split('.'))+'.olean')
        artifact.parent.mkdir(parents=True,exist_ok=True);reportfile=out/(stem+'.json')
        if args.resume and reportfile.exists():
            old=json.loads(reportfile.read_text(encoding='utf-8'))
            assert old['kit_commit']==pin and old['source_sha256']==sha and old['check']['verdict']=='pass'
            assert old['check']['replay']['ok'] and not old['check']['newAxioms']
            assert all(h['ok'] for h in old['check']['headlines']) and artifact.exists()
            print({'module':stem,'stage':'retained_exact_pass'},flush=True);return old
        print({'module':stem,'stage':'compile'},flush=True)
        build=guard.guarded([str(lake),'env','lean','-o',str(artifact),str(source)],project,out/(stem+'.build.log'))
        argv=[str(lake),'env','lean','--run','Check.lean',module,'--claim','partial']
        for h in entry['headlines']:argv+=['--headline','Ruliology.CellularAutomata.Rule30Tail13Completion.'+h]
        print({'module':stem,'stage':'full_kernel_replay'},flush=True)
        log=out/(stem+'.check.log');replay=guard.guarded(argv,project,log)
        checked=json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
        assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
        assert all(h['ok'] for h in checked['headlines']) and len(checked['headlines'])==len(entry['headlines'])
        assert source.read_bytes()==raw
        result={'module':module,'source_sha256':sha,'kit_commit':pin,'checker_unchanged':True,
                'checker_sha256':hashlib.sha256(checker).hexdigest(),'build_seconds':build,
                'replay_seconds':replay,'check':checked,'full_problem_solved':False}
        reportfile.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
        print({'module':stem,'stage':'pass','constants':checked['replay']['constants']},flush=True);return result
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        results=list(pool.map(verify,data['entries'][:-1]))
    results.append(verify(data['entries'][-1]))
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    result={'verdict':'pass','kit_commit':pin,'checker_unchanged':True,'modules':len(results),
            'replayed_declarations':sum(r['check']['replay']['constants'] for r in results),
            'seconds':round(time.monotonic()-start,3),'full_problem_solved':False,'Q01_proved':False}
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(result,flush=True)

if __name__=='__main__':main()
