import argparse,hashlib,importlib.util,json,shutil,subprocess
from core import HERE,BASE,REPO
from verification_context import add_reference_options,reference,unchanged,identity

def main():
    parser=argparse.ArgumentParser();add_reference_options(parser)
    project,lake,checker=reference(parser.parse_args())
    endpoint=json.loads((HERE/'front-jump/evidence/report.json').read_text(encoding='utf-8'))
    maps=json.loads((HERE/'front-jump/map-evidence/report.json').read_text(encoding='utf-8'))
    assert endpoint['verdict']=='pass' and endpoint['full_execution_certified'] and maps['check']['verdict']=='pass'
    external=json.loads((HERE/'external/f177ae-evidence/report.json').read_text(encoding='utf-8'))
    assert external['check']['replay']=={'constants':363,'ok':True}
    assert hashlib.sha256((project/'Rule30ExternalFiveTailAudit.lean').read_bytes()).hexdigest()==external['source_sha256']
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    out=HERE/'front-jump/cycle-evidence';out.mkdir(exist_ok=True)
    mod='Rule30FrontJumpCycleResearch';source=HERE/'front-jump'/(mod+'.lean');target=project/source.name;raw=source.read_bytes()
    if target.exists() and target.read_bytes()!=raw:raise RuntimeError('Different owned source')
    shutil.copyfile(source,target);obj=project/'.lake/build/lib/lean'/(mod+'.olean')
    build=guard.guarded([str(lake),'env','lean','-o',str(obj),str(target)],project,out/'build.log')
    heads=['full_jump','prefix_jump','block_orbit','period_return','all_rare','compressed_cycle','compressed_row4_13']
    argv=[str(lake),'env','lean','--run','Check.lean',mod,'--claim','partial']
    for h in heads:argv+=['--headline','Rule30FrontJumpResearch.'+h]
    replay=guard.guarded(argv,project,out/'check.log')
    checked=json.loads([s for s in (out/'check.log').read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
    assert all(h['ok'] for h in checked['headlines']) and target.read_bytes()==raw
    result={'source_sha256':hashlib.sha256(raw).hexdigest(),'build_seconds':build,'replay_seconds':replay,
            'check':checked,'imports_old_complete_cycle':False,'lower_external_source_sha256':external['source_sha256'],
            'full_problem_solved':False,'Q01_proved':False}
    unchanged(project,checker);result.update(identity(checker))
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print({'verdict':'pass','constants':checked['replay']['constants'],'headlines':len(heads)},flush=True)

if __name__=='__main__':main()
