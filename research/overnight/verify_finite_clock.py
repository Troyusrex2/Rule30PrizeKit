"""Fully replay the arbitrary-width profile checker and clock-sixteen instance."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

import audit_contributions as audit

MODULES={
    'Rule30FiniteClockCertificateResearch': [
        'covered_predecessor','covers_finite_family','finite_family_clock_detected',
        'finite_state_clock_detected','finite_state_eventual_clock_detected','eventual_period_is_period'],
    'Rule30FiniteClockSixteenResearch': [
        'pool16_checked','detection16_checked','detection16_all_head_clocks','period_detected','period8_detected',
        'period4_detected','period2_detected','period1_detected',
        'eventual_period_detected','period_loss_requires_infinite_tail']}


def adapt(source):
    return source.removeprefix('module\n').replace('public import ','import ').replace('@[expose] public section','')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--lake',required=True)
    ap.add_argument('--project',type=Path,default=audit.ROOT)
    ap.add_argument('--refresh-generated',action='store_true')
    args=ap.parse_args();project=args.project.resolve()
    tag='catalog' if project==audit.ROOT else 'pinned'
    checker=subprocess.check_output(['git','show','HEAD:Check.lean'],cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    if tag=='pinned':
        dep=Path('lean/Ruliology/CellularAutomata/Rule30ControlledResponseResearch.lean')
        assert (project/dep).read_text(encoding='utf-8')==adapt((audit.ROOT/dep).read_text(encoding='utf-8'))
    evidence=audit.HERE/'finite-clock-evidence'/tag;evidence.mkdir(parents=True,exist_ok=True)
    previous_path=evidence/'report.json'
    previous=json.loads(previous_path.read_text(encoding='utf-8')) if previous_path.exists() else None
    report={'verdict':'running','checker_modified':False,'full_problem_claim':False,
            'full_clock_of_instance':16,'spatial_width_bound':None,'new_center_period_excluded':False,
            'arbitrary_clock_induction_proved':False,'modules':[],
            'project_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()}
    for stem,heads in MODULES.items():
        module=audit.PREFIX+stem;rel=Path('lean')/Path(module.replace('.','/')).with_suffix('.lean')
        source=(audit.ROOT/rel).read_text(encoding='utf-8')
        if tag=='pinned':
            source=adapt(source);target=project/rel
            if target.exists() and target.read_text(encoding='utf-8')!=source:
                if not args.refresh_generated or previous is None or previous['verdict']!='pass':
                    raise RuntimeError('Refusing to overwrite different pinned proof source')
                old=next((m for m in previous['modules'] if m['module']==module),None)
                if old is None or hashlib.sha256(target.read_bytes()).hexdigest()!=old['source_sha256']:
                    raise RuntimeError('Pinned source does not match its previously verified hash')
            target.write_text(source,encoding='utf-8',newline='\n')
        checked=(project/rel).read_bytes()
        audit.run([args.lake,'build',module],project,evidence/(stem+'.build.log'))
        argv=[args.lake,'env','lean','--run','Check.lean',module,'--claim','partial']
        for h in heads:argv+=['--headline',module+'.'+h]
        log=evidence/(stem+'.check.log');audit.run(argv,project,log)
        data=json.loads([line for line in log.read_text(encoding='utf-8').splitlines() if line.startswith('{')][-1])
        assert data['verdict']=='pass' and data['replay']['ok'] and not data['newAxioms']
        assert all(h['ok'] for h in data['headlines']) and (project/rel).read_bytes()==checked
        report['modules'].append({'module':module,'source_sha256':hashlib.sha256(checked).hexdigest(),'check':data})
        (evidence/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
        print(json.dumps({'environment':tag,'module':stem,'constants':data['replay']['constants'],'verdict':'pass'}),flush=True)
    report['verdict']='pass'
    (evidence/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')


if __name__=='__main__':main()
