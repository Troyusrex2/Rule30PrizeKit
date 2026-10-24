"""Build and fully replay the two exact research-to-catalog adaptations."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import catalog_adaptation
from replay import guarded, KIT

NS = catalog_adaptation.NEW+'.'
ITEMS = [
    ('Rule30Certificates.StripeMeeting',['checked','preservesTwo_pool']),
    ('Rule30StripeMeeting',['Phi_testBit','tailRun_accept_iff','two_step_stripe_related',
                           'stripe_meeting_is_early','stripe_related_preserves_two',
                           'stripe_related_same_trace','no_delayed_stripe_meeting',
                           'eventually_stripe_iff_early']),
]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project',type=Path,required=True)
    parser.add_argument('--lake',required=True)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    root = args.project.resolve()
    args.output.mkdir(parents=True,exist_ok=True)
    logs = args.output/'logs'
    logs.mkdir(exist_ok=True)
    checker = subprocess.check_output(['git','show',KIT+':Check.lean'],cwd=root)
    assert (root/'Check.lean').read_bytes().replace(b'\r\n',b'\n') == checker
    sources = catalog_adaptation.build()
    for relative,expected in sources.items():
        assert (root/'lean/Ruliology/CellularAutomata'/relative).read_text(encoding='utf-8')==expected
    records = []
    for stem,heads in ITEMS:
        module = 'Ruliology.CellularAutomata.'+stem
        source = root/'lean'/Path(module.replace('.','/')).with_suffix('.lean')
        raw = source.read_bytes()
        print(json.dumps({'module':module,'stage':'build'}),flush=True)
        seconds = guarded([args.lake,'build',module],root,logs/(stem+'.build.log'))
        argv = [args.lake,'env','lean','--run','Check.lean',module,'--claim','partial']
        for head in heads:
            argv += ['--headline',NS+head]
        print(json.dumps({'module':module,'stage':'full_kernel_replay'}),flush=True)
        log = logs/(stem+'.check.log')
        check_seconds = guarded(argv,root,log)
        data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines()
                           if s.startswith('{')][-1])
        assert data['verdict']=='pass' and data['replay']['ok'] and not data['newAxioms']
        assert all(h['ok'] for h in data['headlines'])
        assert source.read_bytes()==raw
        records.append({'module':module,'source_sha256':hashlib.sha256(raw).hexdigest(),
                        'build_seconds':seconds,'replay_seconds':check_seconds,'check':data})
        print(json.dumps({'module':module,'stage':'pass',
                          'constants':data['replay']['constants']}),flush=True)
    print(json.dumps({'stage':'whole_catalog_build'}),flush=True)
    seconds = guarded([args.lake,'build','Ruliology'],root,logs/'Ruliology.build.log')
    report = {'verdict':'pass','base_commit':KIT,'checker_unchanged':True,
              'checker_sha256':hashlib.sha256(checker).hexdigest(),
              'adaptation':'import/export wrappers, namespace qualification and module boundaries only',
              'modules':records,'warm_whole_catalog_build_seconds':seconds,
              'infinite_trace_completeness_proved':False,'full_problem_solved':False}
    (args.output/'report.json').write_text(json.dumps(report,indent=2)+'\n',
                                         encoding='utf-8',newline='\n')

if __name__=='__main__':
    main()
