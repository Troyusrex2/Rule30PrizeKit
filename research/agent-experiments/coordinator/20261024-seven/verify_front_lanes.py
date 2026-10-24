"""Compile/replay generic lane semantics; no Python table is trusted."""
import argparse,hashlib,importlib.util,json,shutil,subprocess
from core import HERE,BASE,REPO
from verification_context import add_reference_options,reference,unchanged,identity

def main():
    parser=argparse.ArgumentParser(description=__doc__);add_reference_options(parser)
    project,lake,checker=reference(parser.parse_args())
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    out=HERE/'front-lanes-evidence';out.mkdir(exist_ok=True)
    guard.guarded([str(lake),'build','Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes'],project,out/'dependencies.log')
    mod='Rule30FrontLanesResearch';source=HERE/(mod+'.lean');target=project/source.name;raw=source.read_bytes()
    if target.exists() and target.read_bytes()!=raw:raise RuntimeError('Different owned module exists')
    shutil.copyfile(source,target);obj=project/'.lake/build/lib/lean'/(mod+'.olean')
    build=guard.guarded([str(lake),'env','lean','-o',str(obj),str(target)],project,out/'build.log')
    heads=['scan_length','bscan_length','map_bit_scan','bitMask_bit','project_next','project_run','bscan_getD','represents_next','brun_length','brun_represents','run_represents','word_bound','word_represents','represents_unique','brun_lo_bound','run_correct','allMask_bit','pk_pats','initial_word','initial_run_correct','run_add','run_chain']
    argv=[str(lake),'env','lean','--run','Check.lean',mod,'--claim','partial']
    for h in heads:argv+=['--headline',mod+'.'+h]
    replay=guard.guarded(argv,project,out/'check.log')
    checked=json.loads([s for s in (out/'check.log').read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
    assert all(h['ok'] for h in checked['headlines'])
    assert target.read_bytes()==raw
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    result={'source_sha256':hashlib.sha256(raw).hexdigest(),'kit_commit':'3eca23c0a9fa6b153313655e6d51835406c2d06e',
            'build_seconds':build,'replay_seconds':replay,'check':checked,'full_problem_solved':False}
    unchanged(project,checker);result.update(identity(checker))
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print({'verdict':'pass','constants':checked['replay']['constants'],'headlines':len(heads)},flush=True)

if __name__=='__main__':main()
