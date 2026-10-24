"""Replay the two unconditional spatial-relation exclusions, not Problem 1."""
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
    args=ap.parse_args(); project=args.project.resolve()
    module=audit.PREFIX+'Rule30EventualColumnRelationsResearch'
    rel=Path('lean')/Path(module.replace('.','/')).with_suffix('.lean')
    source=(audit.ROOT/rel).read_text(encoding='utf-8')
    tag='catalog' if project==audit.ROOT else 'pinned'
    if tag=='pinned':
        source=source.removeprefix('module\n').replace('public import ','import ')
        source=source.replace('@[expose] public section','')
        target=project/rel
        if target.exists() and target.read_text(encoding='utf-8')!=source:
            raise RuntimeError('Refusing to overwrite different research source')
        target.write_text(source,encoding='utf-8',newline='\n')
    checker=subprocess.check_output(['git','show','HEAD:Check.lean'],cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    evidence=audit.HERE/'eventual-relations-evidence'/tag
    evidence.mkdir(parents=True,exist_ok=True)
    audit.run([args.lake,'build',module],project,evidence/'build.log')
    argv=[args.lake,'env','lean','--run','Check.lean',module,'--claim','partial']
    for h in ['middle_eventually_constant','distance_two_infinitely_different',
              'adjacent_not_complement']:
        argv+=['--headline',module+'.'+h]
    log=evidence/'check.log'; audit.run(argv,project,log)
    data=json.loads([l for l in log.read_text(encoding='utf-8').splitlines() if l.startswith('{')][-1])
    assert data['verdict']=='pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    report={'verdict':'pass','full_problem_claim':False,'temporal_period_excluded':False,
            'all_spatial_distances_covered':False,'checker_modified':False,
            'source_sha256':hashlib.sha256((project/rel).read_bytes()).hexdigest(),
            'project_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip(),
            'check':data}
    (evidence/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'environment':tag,'verdict':'pass','constants':data['replay']['constants']}))


if __name__=='__main__':main()
