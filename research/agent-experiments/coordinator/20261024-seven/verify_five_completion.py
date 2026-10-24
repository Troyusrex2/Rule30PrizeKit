"""Replay the five-tail bridge after both exact dependencies have passed."""
import argparse,hashlib,importlib.util,json,shutil,subprocess
from pathlib import Path
from core import HERE,REPO,BASE

def main():
    here=HERE/'tail13-completion';out=here/'five-evidence';out.mkdir(exist_ok=True)
    four=json.loads((here/'evidence/report.json').read_text(encoding='utf-8'))
    external=json.loads((HERE/'external/f177ae-evidence/report.json').read_text(encoding='utf-8'))
    assert four['verdict']=='pass' and external['check']['verdict']=='pass'
    parser=argparse.ArgumentParser()
    parser.add_argument('--project',type=Path,default=BASE/'current-reference-3eca-20261024')
    parser.add_argument('--lake',type=Path,default=BASE/'toolchain/lean-4.35.0-windows/bin/lake.exe')
    args=parser.parse_args();project=args.project.resolve();lake=args.lake.resolve()
    pin='3eca23c0a9fa6b153313655e6d51835406c2d06e'
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()==pin
    checker=subprocess.check_output(['git','show','HEAD:Check.lean'],cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    for entry in four['modules']:
        assert hashlib.sha256((project/(entry['module']+'.lean')).read_bytes()).hexdigest()==entry['source_sha256']
    assert hashlib.sha256((project/'Rule30ExternalFiveTailAudit.lean').read_bytes()).hexdigest()==external['source_sha256']
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    mod='Rule30TailFiveCompleteResearch';source=here/(mod+'.lean');raw=source.read_bytes();target=project/source.name
    if target.exists() and target.read_bytes()!=raw:raise RuntimeError('Different owned bridge exists')
    shutil.copyfile(source,target);obj=project/'.lake/build/lib/lean'/(mod+'.olean')
    build=guard.guarded([str(lake),'env','lean','-o',str(obj),str(target)],project,out/'build.log')
    heads=['tail5_13_eq_tail4','row5_13_eq_row4','tail5_27_shift','row5_27_eq_row4','stripe_five_tail_complete']
    argv=[str(lake),'env','lean','--run','Check.lean',mod,'--claim','partial']
    for h in heads:argv+=['--headline','Rule30TailFiveCompletionResearch.'+h]
    replay=guard.guarded(argv,project,out/'check.log')
    checked=json.loads([s for s in (out/'check.log').read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
    assert all(h['ok'] for h in checked['headlines'])
    assert target.read_bytes()==raw and (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    result={'kit_commit':pin,'checker_unchanged':True,'source_sha256':hashlib.sha256(raw).hexdigest(),
            'four_tail_dependency':four,'external_dependency_source_sha256':external['source_sha256'],
            'external_dependency_replay':external['check']['replay'],'build_seconds':build,
            'replay_seconds':replay,'check':checked,'Q01_proved':False,'full_problem_solved':False}
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print({'status':'pass','constants':checked['replay']['constants'],'headlines':len(heads)},flush=True)

if __name__=='__main__':main()
