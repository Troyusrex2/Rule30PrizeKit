"""Replay the unbounded single-seed column separation theorem."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE=Path(__file__).resolve().parent
PROJECT=HERE.parents[1]
spec=importlib.util.spec_from_file_location('verify',HERE/'verify_trace_separation.py')
verify=importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)
MODULE='Ruliology.CellularAutomata.Rule30ColumnSeparationResearch'
REL=Path('lean/Ruliology/CellularAutomata/Rule30ColumnSeparationResearch.lean')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lake',default='lake')
    p.add_argument('--pinned-project',type=Path)
    args=p.parse_args()
    project=args.pinned_project.resolve() if args.pinned_project else PROJECT
    tag='pinned' if args.pinned_project else 'catalog'
    if args.pinned_project:
        source=(PROJECT/REL).read_text(encoding='utf-8')
        adapted=source.removeprefix('module\n').replace('public import ','import ').replace('@[expose] public section','')
        target=project/REL
        if target.exists() and target.read_text(encoding='utf-8')!=adapted:
            raise RuntimeError('Refusing to overwrite a different pinned column-separation source')
        target.write_text(adapted,encoding='utf-8',newline='\n')
    evidence=HERE/'columns-evidence'/tag
    evidence.mkdir(parents=True,exist_ok=True)
    result=verify.verify_module(args.lake,project,evidence,MODULE,MODULE+'.columns_distinguishable')
    report={'verdict':'pass','headline_unconditional':True,'all_spatial_positions':True,
            'single_seed_only':True,'temporal_nonperiodicity_claim':False,'full_problem_claim':False,
            'eventual_equality_excluded':False,'mirror_lag_bound':18,
            'source_sha256':hashlib.sha256((project/REL).read_bytes()).hexdigest(),
            'module':MODULE,'replay':result,'proof_body_unchanged':True,
            'project_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()}
    (HERE/f'columns-{tag}-verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(report))


if __name__=='__main__':main()
