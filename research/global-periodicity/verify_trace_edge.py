"""Compile and replay the CONDITIONAL global trace reduction, unchanged checker."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

HERE=Path(__file__).resolve().parent
PROJECT=HERE.parents[1]
MODULE='Ruliology.CellularAutomata.Rule30TraceEdgeResearch'
RELATIVE=Path('lean/Ruliology/CellularAutomata/Rule30TraceEdgeResearch.lean')
HEADLINE=MODULE+'.problem1_of_edgeObservable'


def run(args,cwd):
    return subprocess.run(args,cwd=cwd,encoding='utf-8',errors='replace',
                          stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake',default='lake')
    parser.add_argument('--pinned-project',type=Path)
    args=parser.parse_args()
    source=(PROJECT/RELATIVE).read_text(encoding='utf-8')
    project=args.pinned_project.resolve() if args.pinned_project else PROJECT
    tag='pinned' if args.pinned_project else 'catalog'
    if args.pinned_project:
        adapted=source.removeprefix('module\n').replace('public import ','import ')
        adapted=adapted.replace('@[expose] public section','')
        target=project/RELATIVE
        if target.exists() and target.read_text(encoding='utf-8') != adapted:
            raise RuntimeError('Refusing to overwrite a different file in the pinned worktree')
        target.write_text(adapted,encoding='utf-8',newline='\n')
    build=run([args.lake,'build',MODULE],project)
    (HERE/f'{tag}-build.log').write_text(build.stdout,encoding='utf-8',newline='\n')
    if build.returncode:
        raise RuntimeError(build.stdout)
    checked=run([args.lake,'env','lean','--run','Check.lean',MODULE,
                 '--claim','partial','--headline',HEADLINE],project)
    (HERE/f'{tag}-check.log').write_text(checked.stdout,encoding='utf-8',newline='\n')
    lines=[line for line in checked.stdout.splitlines() if line.startswith('{')]
    verdict=json.loads(lines[-1])
    assert checked.returncode==0 and verdict['verdict']=='pass'
    assert verdict['replay']['ok'] and not verdict['newAxioms']
    assert all(h['ok'] for h in verdict['headlines'])
    (HERE/f'{tag}-kernel-check.json').write_text(json.dumps(verdict,indent=2)+'\n',encoding='utf-8')
    head=run(['git','rev-parse','HEAD'],project).stdout.strip()
    report={'conditional_only':True,'full_problem_claim':False,'prize_submission':False,
            'open_hypothesis':MODULE+'.EdgeObservable', 'project_commit':head,
            'module':MODULE,'headline':HEADLINE,
            'source_sha256':hashlib.sha256((project/RELATIVE).read_bytes()).hexdigest(),
            'proof_body_unchanged':True,'kernel_replay':verdict['replay'],
            'new_axioms':verdict['newAxioms'],'verdict':verdict['verdict']}
    (HERE/f'{tag}-verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report))


if __name__=='__main__':
    main()
