"""Replay the general front-width projection lemmas, without finite certificates."""
import argparse,hashlib,importlib.util,json,shutil,subprocess
from core import HERE,BASE,REPO
from verification_context import add_reference_options,reference,unchanged,identity

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--period',action='store_true');add_reference_options(parser)
    args=parser.parse_args();project,lake,checker=reference(args)
    pin='3eca23c0a9fa6b153313655e6d51835406c2d06e'
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()==pin
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    out=HERE/('front-period-lift-evidence' if args.period else 'front-lift-evidence');out.mkdir(exist_ok=True)
    mod='Rule30FrontPeriodLiftResearch' if args.period else 'Rule30FrontLiftResearch'
    source=HERE/(mod+'.lean');raw=source.read_bytes();target=project/source.name
    if target.exists() and target.read_bytes()!=raw:raise RuntimeError('Different owned module exists; review before replacing')
    shutil.copyfile(source,target);obj=project/'.lake/build/lib/lean'/(mod+'.olean')
    build=guard.guarded([str(lake),'env','lean','-o',str(obj),str(target)],project,out/'build.log')
    heads=['parity_of_bit0','pstep_low','sig_congr','sig_mono','fstep_low','orbit_low','punctured_cycle_lift']
    if args.period:heads=['fstep_top_flip','orbit_phase_lt','orbit_top_flip','fstep_bound','orbit_bound','low_two_choices','double_period','universal_front_period']
    argv=[str(lake),'env','lean','--run','Check.lean',mod,'--claim','partial']
    for h in heads:argv+=['--headline',mod+'.'+h]
    replay=guard.guarded(argv,project,out/'check.log')
    checked=json.loads([s for s in (out/'check.log').read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
    assert all(h['ok'] for h in checked['headlines'])
    result={'kit_commit':pin,'checker_unchanged':True,'source_sha256':hashlib.sha256(raw).hexdigest(),
            'build_seconds':build,'replay_seconds':replay,'check':checked,'full_problem_solved':False}
    assert target.read_bytes()==raw;unchanged(project,checker);result.update(identity(checker))
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print({'status':'pass','constants':checked['replay']['constants'],'headlines':len(heads)},flush=True)

if __name__=='__main__':main()
