"""Compile and fully replay the group identities and short-period obstruction."""
import argparse,hashlib,importlib.util,json,shutil
from core import HERE,REPO
from verification_context import add_reference_options,reference,unchanged,identity

def main():
    parser=argparse.ArgumentParser(description=__doc__);add_reference_options(parser)
    project,lake,checker=reference(parser.parse_args())
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    out=HERE/'group-primitives-evidence';out.mkdir(exist_ok=True)
    mod='Rule30GroupPrimitivesResearch';source=HERE/(mod+'.lean');raw=source.read_bytes();target=project/source.name
    if target.exists() and target.read_bytes()!=raw:raise RuntimeError('Different owned module exists')
    shutil.copyfile(source,target);obj=project/'.lake/build/lib/lean'/(mod+'.olean')
    build=guard.guarded([str(lake),'env','lean','-o',str(obj),str(target)],project,out/'build.log')
    heads=['g0_involution','g1_bit0','g1_bit1','g1_high','g1_involution','phi_flip_high',
           'phi_intertwines_flip','h_square','h_fourth','flips_do_not_commute',
           'phi90_intertwines_flip','linear_flips_commute',
           'short_period_return32','short_period_no_return','short_period_minimal']
    argv=[str(lake),'env','lean','--run','Check.lean',mod,'--claim','partial']
    for h in heads:argv+=['--headline',mod+'.'+h]
    replay=guard.guarded(argv,project,out/'check.log')
    checked=json.loads([s for s in (out/'check.log').read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
    assert all(h['ok'] for h in checked['headlines']) and target.read_bytes()==raw
    unchanged(project,checker)
    result={**identity(checker),'source_sha256':hashlib.sha256(raw).hexdigest(),
            'build_seconds':build,'replay_seconds':replay,'check':checked,'full_problem_solved':False}
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print({'verdict':'pass','constants':checked['replay']['constants'],'headlines':len(heads)},flush=True)

if __name__=='__main__':main()
