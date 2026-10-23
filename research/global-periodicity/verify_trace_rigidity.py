"""Replay an unconditional limitation theorem; no full prize claim."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
PROJECT=HERE.parents[1]
spec=importlib.util.spec_from_file_location('verify_edge',HERE/'verify_trace_edge.py')
verify=importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)
MODULE='Ruliology.CellularAutomata.Rule30TraceRigidityResearch'
HEADLINE=MODULE+'.no_left_recovery_from_eventual_finiteness'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake',default='lake')
    parser.add_argument('--pinned-project',type=Path)
    parser.add_argument('--ambiguity',action='store_true',
                        help='Check the all-horizons theorem with finite initial witnesses')
    args=parser.parse_args()
    module=('Ruliology.CellularAutomata.Rule30TraceAmbiguityResearch' if args.ambiguity else MODULE)
    headline=(module+'.arbitrarily_long_finite_left_ambiguity' if args.ambiguity else HEADLINE)
    project=args.pinned_project.resolve() if args.pinned_project else PROJECT
    tag=('ambiguity' if args.ambiguity else 'rigidity')+('-pinned' if args.pinned_project else '-catalog')
    files=[Path('lean/Ruliology/CellularAutomata')/(name+'.lean')
           for name in ['Rule30TraceEdgeResearch','Rule30TraceRigidityResearch']]
    if args.ambiguity:
        files.append(Path('lean/Ruliology/CellularAutomata/Rule30TraceAmbiguityResearch.lean'))
    if args.pinned_project:
        for relative in files:
            source=(PROJECT/relative).read_text(encoding='utf-8')
            adapted=source.removeprefix('module\n').replace('public import ','import ')
            adapted=adapted.replace('@[expose] public section','')
            target=project/relative
            if target.exists() and target.read_text(encoding='utf-8') != adapted:
                raise RuntimeError('Refusing to overwrite a different pinned research file')
            target.write_text(adapted,encoding='utf-8',newline='\n')
    build=verify.run([args.lake,'build',module],project)
    (HERE/f'{tag}-build.log').write_text(build.stdout,encoding='utf-8',newline='\n')
    if build.returncode:
        raise RuntimeError(build.stdout)
    check=verify.run([args.lake,'env','lean','--run','Check.lean',module,
                      '--claim','partial','--headline',headline],project)
    (HERE/f'{tag}-check.log').write_text(check.stdout,encoding='utf-8',newline='\n')
    data=json.loads([s for s in check.stdout.splitlines() if s.startswith('{')][-1])
    assert check.returncode==0 and data['verdict']=='pass' and data['replay']['ok']
    assert not data['newAxioms'] and all(h['ok'] for h in data['headlines'])
    (HERE/f'{tag}-kernel-check.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
    report={'headline_unconditional':True,'full_problem_claim':False,'prize_submission':False,
            'module':module,'headline':headline,'project_commit':verify.run(['git','rev-parse','HEAD'],project).stdout.strip(),
            'source_sha256':{p.as_posix():hashlib.sha256((project/p).read_bytes()).hexdigest() for p in files},
            'proof_bodies_unchanged':True,'kernel_replay':data['replay'],'new_axioms':data['newAxioms'],
            'verdict':data['verdict'],'not_a_counterexample_to_edge_observability':True,
            'initial_rows_infinite':not args.ambiguity,'left_edges_equal':True}
    if args.ambiguity:
        report.update(all_observation_horizons=True,initial_rows_finite=True,
                      equal_infinite_traces_claimed=False,fixed_left_edge=-3)
    (HERE/f'{tag}-verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(report))


if __name__=='__main__':
    main()
