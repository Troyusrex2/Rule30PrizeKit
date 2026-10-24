"""Replay the explicit open reduction and the disproved strict factor-two bound."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
MODULE='Ruliology.CellularAutomata.Rule30VariationWeightResearch'
REL=Path('lean')/Path(MODULE.replace('.','/')).with_suffix('.lean')
sp=importlib.util.spec_from_file_location('audit',HERE/'audit_contributions.py')
audit=importlib.util.module_from_spec(sp);sp.loader.exec_module(audit)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lake',required=True)
    ap.add_argument('--project',type=Path,default=ROOT)
    args=ap.parse_args();project=args.project.resolve()
    tag='catalog' if project==ROOT else 'pinned'
    evidence=HERE/'variation-evidence'/tag;evidence.mkdir(parents=True,exist_ok=True)
    source=(ROOT/REL).read_text(encoding='utf-8')
    if tag=='pinned':
        source=source.removeprefix('module\n').replace('public import ','import ').replace('@[expose] public section','')
        target=project/REL
        if target.exists() and target.read_text(encoding='utf-8')!=source:
            raise RuntimeError('Different pinned research source')
        target.write_text(source,encoding='utf-8',newline='\n')
    expected=subprocess.check_output(['git','show','HEAD:Check.lean'],cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==expected
    audit.run([args.lake,'build',MODULE],project,evidence/'build.log')
    argv=[args.lake,'env','lean','--run','Check.lean',MODULE,'--claim','partial']
    for h in ['bounded_variation_periodic','q01_of_variation_estimate',
              'no_period_two_of_variation_estimate','strict_factor_two_false']:
        argv+=['--headline',MODULE+'.'+h]
    log=evidence/'check.log';audit.run(argv,project,log)
    data=json.loads([l for l in log.read_text(encoding='utf-8').splitlines() if l.startswith('{')][-1])
    assert data['verdict']=='pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    report={'verdict':'pass','variation_estimate_proved':False,'Q01_proved':False,
            'full_problem_claim':False,'reduction_conditional_only':True,
            'strict_factor_two_refuted':True,'source_sha256':hashlib.sha256((project/REL).read_bytes()).hexdigest(),
            'project_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip(),
            'check':data}
    (evidence/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'environment':tag,'verdict':'pass','constants':data['replay']['constants'],
                      'estimate_still_open':True}))


if __name__=='__main__':main()
