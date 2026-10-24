"""Verify the exact shifted-row link and an explicitly conditional cost reduction."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

import audit_contributions as audit


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lake',required=True)
    ap.add_argument('--project',type=Path,default=audit.ROOT)
    args=ap.parse_args();project=args.project.resolve()
    stem='Rule30EmptyGateReductionResearch';module=audit.PREFIX+stem
    rel=Path('lean')/Path(module.replace('.','/')).with_suffix('.lean')
    source=(audit.ROOT/rel).read_text(encoding='utf-8')
    tag='catalog' if project==audit.ROOT else 'pinned'
    if tag=='pinned':
        source=source.removeprefix('module\n').replace('public import ','import ')
        source=source.replace('@[expose] public section','')
        target=project/rel
        if target.exists() and target.read_text(encoding='utf-8')!=source:
            raise RuntimeError('Different research proof source')
        target.write_text(source,encoding='utf-8',newline='\n')
    expected=subprocess.check_output(['git','show','HEAD:Check.lean'],cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==expected
    evidence=audit.HERE/'empty-reduction-evidence'/tag;evidence.mkdir(parents=True,exist_ok=True)
    audit.run([args.lake,'build',module],project,evidence/'build.log')
    argv=[args.lake,'env','lean','--run','Check.lean',module,'--claim','partial']
    for h in ['shifted_eq','finite_shifted_of_finite','CQ01Empty_of_cost_estimate']:
        argv+=['--headline',module+'.'+h]
    log=evidence/'check.log';audit.run(argv,project,log)
    data=json.loads([l for l in log.read_text(encoding='utf-8').splitlines() if l.startswith('{')][-1])
    assert data['verdict']=='pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    report={'verdict':'pass','CQ01Empty_proved':False,'cost_estimate_proved':False,
            'full_problem_claim':False,'unconditional_shift_equality_proved':True,
            'cost_reduction_conditional_only':True,'checker_modified':False,
            'source_sha256':hashlib.sha256((project/rel).read_bytes()).hexdigest(),
            'project_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip(),
            'check':data}
    (evidence/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'environment':tag,'verdict':'pass','constants':data['replay']['constants'],
                      'cost_estimate_still_open':True}))


if __name__=='__main__':main()
