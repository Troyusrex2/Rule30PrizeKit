import argparse,hashlib,importlib.util,json,shutil,subprocess
from core import HERE,BASE,REPO
from verification_context import add_reference_options,reference,unchanged,identity

def main():
    parser=argparse.ArgumentParser();add_reference_options(parser)
    project,lake,checker=reference(parser.parse_args())
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    out=HERE/'front-jump/map-evidence';out.mkdir(exist_ok=True)
    mod='Rule30FrontJumpMapResearch';source=HERE/'front-jump'/(mod+'.lean');target=project/source.name;raw=source.read_bytes()
    if target.exists() and target.read_bytes()!=raw:raise RuntimeError('Different owned source')
    shutil.copyfile(source,target);obj=project/'.lake/build/lib/lean'/(mod+'.olean')
    build=guard.guarded([str(lake),'env','lean','-o',str(obj),str(target)],project,out/'build.log')
    heads=['jump_lt','jrun_lt','endpoint_word','return_cycle','rare_table','rare_table_sound']
    argv=[str(lake),'env','lean','--run','Check.lean',mod,'--claim','partial']
    for h in heads:argv+=['--headline','Rule30FrontJumpResearch.'+h]
    replay=guard.guarded(argv,project,out/'check.log')
    checked=json.loads([s for s in (out/'check.log').read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
    assert all(h['ok'] for h in checked['headlines']) and target.read_bytes()==raw
    result={'source_sha256':hashlib.sha256(raw).hexdigest(),'build_seconds':build,'replay_seconds':replay,
            'check':checked,'full_problem_solved':False}
    unchanged(project,checker);result.update(identity(checker))
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print({'verdict':'pass','constants':checked['replay']['constants'],'headlines':len(heads)},flush=True)

if __name__=='__main__':main()
