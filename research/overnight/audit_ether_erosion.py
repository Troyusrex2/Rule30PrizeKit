"""Audit PR 10's all-width ether erosion on its exact source and pinned checker."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

import audit_contributions as audit


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lake', required=True)
    ap.add_argument('--project', type=Path, required=True)
    args = ap.parse_args()
    project = args.project.resolve()
    ref = 'origin/pr10-ether-erosion'
    revision = subprocess.check_output(['git','rev-parse',ref],cwd=audit.ROOT,text=True).strip()
    module = audit.PREFIX+'Rule30EtherThreeErosion'
    rel = Path('lean')/Path(module.replace('.', '/')).with_suffix('.lean')
    raw = subprocess.check_output(['git','show',ref+':'+rel.as_posix()],cwd=audit.ROOT)
    source = raw.decode().removeprefix('module\n').replace('public import ','import ').replace('@[expose] public section','')
    target = project/rel
    if target.exists() and target.read_text(encoding='utf-8') != source:
        raise RuntimeError('Refusing to overwrite different proof source')
    target.write_text(source,encoding='utf-8',newline='\n')
    checked = target.read_bytes()
    checker = subprocess.check_output(['git','show','HEAD:Check.lean'],cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n') == checker
    evidence = audit.HERE/'ether-erosion-audit'
    evidence.mkdir(exist_ok=True)
    audit.run([args.lake,'build',module],project,evidence/'build.log')
    argv = [args.lake,'env','lean','--run','Check.lean',module,'--claim','partial']
    for h in ['erosion3_fin','no_wall','wake_good','front_step','run_bad','cert_all','redge_step']:
        argv += ['--headline',audit.PREFIX+'Rule30EtherThree.'+h]
    log = evidence/'check.log'
    audit.run(argv,project,log)
    data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert data['verdict']=='pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines']) and target.read_bytes()==checked
    report = {'verdict':'pass','pull_request':10,'head_commit':revision,
        'author':'Luis Perez Morales; Claude (Fable 5.1)',
        'checker_modified':False,'proof_bodies_unchanged':True,'full_problem_claim':False,
        'original_source_sha256':hashlib.sha256(raw).hexdigest(),
        'adapted_source_sha256':hashlib.sha256(checked).hexdigest(),
        'pinned_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip(),
        'check':data}
    (evidence/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'verdict':'pass','pull_request':10,'constants':data['replay']['constants']}))


if __name__=='__main__':
    main()
