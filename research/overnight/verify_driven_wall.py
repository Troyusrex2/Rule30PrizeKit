"""Full replay of the packed engine, every certificate leaf, and infinite induction."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

import audit_contributions as audit

MODULES=[
 ('Rule30DrivenPrefixResearch',['packed_sound','double_prefix','iterate_mod_bit']),
 ('Rule30Certificates.DrivenEmptyWall',['good_all','entry']),
 ('Rule30EmptyGateSpacingResearch',['empty_windows','empty_spaced','empty_next_gap',
   'empty_black_after','empty_reconstruction_translate','transformed_empty_not_spaced']),
]
CORE_MODULES=[
 ('Rule30Certificates.DrivenEmptyCore',['observe_trim','good_all','entry']),
 ('Rule30EmptyGateLanguageResearch',['refined_spaced','refined_next_gap',
   'no_successive_short_gaps','windowWord_allowed']),
]


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lake',required=True)
    ap.add_argument('--project',type=Path,default=audit.ROOT)
    ap.add_argument('--language-core',action='store_true',help='Verify the stronger eight-bit gate-language certificate')
    args=ap.parse_args();project=args.project.resolve()
    tag='catalog' if project==audit.ROOT else 'pinned'
    folder='empty-language-evidence' if args.language_core else 'driven-wall-evidence'
    evidence=audit.HERE/folder/tag;evidence.mkdir(parents=True,exist_ok=True)
    checker=subprocess.check_output(['git','show','HEAD:Check.lean'],cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    report={'verdict':'incomplete','checker_modified':False,'full_problem_claim':False,
            'CQ01Empty_proved':False,'Q01_proved':False,'gate_spacing_only':True,
            'isolated_short_gaps':args.language_core,
            'project_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip(),
            'modules':[]}
    for stem,headlines in (CORE_MODULES if args.language_core else MODULES):
        module=audit.PREFIX+stem
        rel=Path('lean')/Path(module.replace('.','/')).with_suffix('.lean')
        source=(audit.ROOT/rel).read_text(encoding='utf-8')
        if tag=='pinned':
            source=source.removeprefix('module\n').replace('public import ','import ')
            source=source.replace('@[expose] public section','')
            target=project/rel
            if target.exists() and target.read_text(encoding='utf-8')!=source:
                raise RuntimeError('Refusing to overwrite different proof source: '+str(target))
            target.parent.mkdir(parents=True,exist_ok=True)
            target.write_text(source,encoding='utf-8',newline='\n')
        print(json.dumps({'environment':tag,'stage':'build','module':module}),flush=True)
        build=audit.run([args.lake,'build',module],project,evidence/(stem+'.build.log'))
        argv=[args.lake,'env','lean','--run','Check.lean',module,'--claim','partial']
        for h in headlines:argv+=['--headline',module+'.'+h]
        log=evidence/(stem+'.check.log')
        seconds=audit.run(argv,project,log)
        data=json.loads([l for l in log.read_text(encoding='utf-8').splitlines() if l.startswith('{')][-1])
        assert data['verdict']=='pass' and data['replay']['ok'] and not data['newAxioms']
        assert all(h['ok'] for h in data['headlines'])
        report['modules'].append({'module':module,'build_seconds':build,'check_seconds':seconds,
            'source_sha256':hashlib.sha256((project/rel).read_bytes()).hexdigest(),'check':data})
        (evidence/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
        print(json.dumps({'environment':tag,'stage':'passed','module':module,
                          'constants':data['replay']['constants']}),flush=True)
    report['verdict']='pass'
    (evidence/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')


if __name__=='__main__':main()
